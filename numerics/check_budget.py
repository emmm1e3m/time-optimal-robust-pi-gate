"""独立核查领头阶误差预算；仅使用 Python 标准库。"""

import json
import math
from pathlib import Path


def bisect_root(fun, lo, hi):
    """给定异号端点，以二分法计算唯一根。"""
    flo, fhi = fun(lo), fun(hi)
    assert flo * fhi < 0
    for _ in range(80):
        mid = (lo + hi) / 2
        fm = fun(mid)
        if mid == lo or mid == hi or fm == 0:
            return mid
        if flo * fm < 0:
            hi = mid
        else:
            lo, flo = mid, fm
    return (lo + hi) / 2


def chi(a):
    return (4 * math.cos(a) - 2) ** 2 / 6


def q(a):
    return (4 * math.cos(a) - 2) * math.sin(a) / 3


def crossing(a):
    return chi(a) + 4 * a * q(a) - 2 / 3


a_peak = math.acos((1 + math.sqrt(33)) / 8)
a_end = math.pi / 3
lambda_equal_endpoints = 1 / (2 * math.pi)
a_gain_max = bisect_root(lambda a: q(a) - lambda_equal_endpoints, a_peak, a_end)
L_gain_max = math.pi + 4 * a_gain_max
J_gain_max = chi(a_gain_max) + lambda_equal_endpoints * L_gain_max
a_transition = bisect_root(crossing, a_peak, a_end)
lambda_transition = q(a_transition)
L_transition = math.pi + 4 * a_transition

results = {
    "a_peak": a_peak,
    "lambda_peak": q(a_peak),
    "lambda_equal_endpoints": lambda_equal_endpoints,
    "a_gain_max": a_gain_max,
    "L_gain_max": L_gain_max,
    "L_gain_max_over_pi": L_gain_max / math.pi,
    "chi_gain_max": chi(a_gain_max),
    "J_gain_max": J_gain_max,
    "endpoint_budget_at_gain_max": 7 / 6,
    "relative_gain_max": 1 - J_gain_max / (7 / 6),
    "relative_gain_max_percent": 100 * (1 - J_gain_max / (7 / 6)),
    "stationarity_residual_at_gain_max": q(a_gain_max) - lambda_equal_endpoints,
    "a_transition": a_transition,
    "lambda_transition": lambda_transition,
    "L_transition": L_transition,
    "L_transition_over_pi": L_transition / math.pi,
    "crossing_residual_at_transition": crossing(a_transition),
    "J_transition_rectangular": 2 / 3 + lambda_transition * math.pi,
    "J_transition_partial": chi(a_transition) + lambda_transition * L_transition,
}

print(json.dumps(results, indent=2))
Path(__file__).with_name("numbers.json").write_bytes(
    (json.dumps(results, indent=2) + "\n").encode("utf-8")
)
