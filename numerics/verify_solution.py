"""独立核验 short-CORPSE：直接 2×2 指数、Frechet 导数和误差积分。

浮点计算用于复核规范与实现，不承担原问题的严格最优性证明。
"""
from pathlib import Path
import json
import math
import numpy as np
from scipy.linalg import expm, expm_frechet
from numpy.polynomial.legendre import leggauss

HERE = Path(__file__).resolve().parent
SX = np.array([[0, 1], [1, 0]], dtype=complex)
SY = np.array([[0, -1j], [1j, 0]], dtype=complex)
SZ = np.diag([1, -1]).astype(complex)
PAULI = (SX, SY, SZ)
DURATIONS = np.array([math.pi/3, 5*math.pi/3, math.pi/3])
SIGNS = np.array([1, -1, 1])


def propagate(delta):
    """按原方程逐段左乘；不使用四元数或已有传播代码。"""
    U = np.eye(2, dtype=complex)
    for duration, sign in zip(DURATIONS, SIGNS):
        U = expm(-0.5j*duration*(sign*SX + delta*SZ)) @ U
    return U


def derivative_at_zero():
    """矩阵指数 Frechet 导数给出常段失谐导数，再用乘积法则。"""
    U = np.eye(2, dtype=complex)
    D = np.zeros((2, 2), dtype=complex)
    for duration, sign in zip(DURATIONS, SIGNS):
        P, dP = expm_frechet(-0.5j*duration*sign*SX, -0.5j*duration*SZ)
        D, U = dP @ U + P @ D, P @ U
    return U, D


def analytic_error_integral():
    """同轴控制的积分原函数；坐标次序为 x,y,z。"""
    phase = 0.
    error = np.zeros(3)
    endpoints = [error.tolist()]
    for duration, sign in zip(DURATIONS, SIGNS):
        end = phase + sign*duration
        error += [0., (math.cos(phase)-math.cos(end))/sign,
                   (math.sin(end)-math.sin(phase))/sign]
        phase = end
        endpoints.append(error.tolist())
    return error, phase, endpoints


def quadrature_error_integral():
    """直接求积 U†σzU，与解析原函数使用不同计算路径。"""
    nodes, weights = leggauss(32)
    U = np.eye(2, dtype=complex)
    error = np.zeros(3)
    for duration, sign in zip(DURATIONS, SIGNS):
        for node, weight in zip(nodes, weights):
            V = expm(-0.5j*duration*(node+1)/2*sign*SX) @ U
            N = V.conj().T @ SZ @ V
            error += duration*weight/2*np.array([np.trace(P@N).real/2 for P in PAULI])
        U = expm(-0.5j*duration*sign*SX) @ U
    return error


def main():
    U0 = propagate(0.)
    Uf, derivative = derivative_at_zero()
    target = -expm(-0.5j*math.pi*SX)
    analytic, phase, endpoints = analytic_error_integral()
    quadrature = quadrature_error_integral()
    integral_derivative = -0.5j*U0 @ sum(e*P for e, P in zip(quadrature, PAULI))
    samples = []
    previous = None
    for delta in [0.08, 0.04, 0.02, 0.01, 0.005, 0.0025]:
        plus = float(np.linalg.norm(propagate(delta)-U0, ord='fro'))
        minus = float(np.linalg.norm(propagate(-delta)-U0, ord='fro'))
        error = (plus+minus)/2
        samples.append({'delta':delta, 'symmetric_gate_error_fro':error,
                        'error_over_delta_squared':error/delta**2,
                        'previous_error_over_current':None if previous is None else previous/error})
        previous = error
    result = {
        'scope':'Floating-point consistency checks, not a proof of global optimality.',
        'normalization':'Omega=1, H_delta=(ux sigma_x+uy sigma_y+delta sigma_z)/2',
        'segments':[{'ux':int(s),'uy':0,'duration':float(d)} for s,d in zip(SIGNS,DURATIONS)],
        'total_time':float(sum(DURATIONS)), 'total_time_over_pi':float(sum(DURATIONS)/math.pi),
        'target':'-R_x(pi)', 'signed_rotation_angle':phase,
        'gate_error_fro':float(np.linalg.norm(U0-target)),
        'unitarity_error_fro':float(np.linalg.norm(U0.conj().T@U0-np.eye(2))),
        'frechet_nominal_agreement_fro':float(np.linalg.norm(Uf-U0)),
        'detuning_derivative_fro':float(np.linalg.norm(derivative)),
        'analytic_error_vector':analytic.tolist(),
        'quadrature_error_vector':quadrature.tolist(),
        'derivative_integral_identity_error_fro':float(np.linalg.norm(derivative-integral_derivative)),
        'curve_join_coordinates_xyz':endpoints,
        'initial_tangent_xyz':[0.,0.,1.],
        'final_tangent_xyz':[0.,math.sin(phase),math.cos(phase)],
        'small_detuning_scaling':samples,
    }
    assert result['gate_error_fro'] < 1e-12
    assert result['detuning_derivative_fro'] < 1e-12
    assert max(abs(analytic)) < 1e-12 and max(abs(quadrature)) < 1e-12
    assert result['derivative_integral_identity_error_fro'] < 1e-12
    assert all(abs(row['previous_error_over_current']-4)<.02 for row in samples[-4:])
    result['checks_passed'] = True
    (HERE/'verification.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
