"""从解析圆弧生成科学矢量图；PDF/SVG 无栅格图像。"""
from pathlib import Path
import math
import html
import pymupdf

HERE = Path(__file__).resolve().parent
ASSETS = HERE/'assets'
ASSETS.mkdir(exist_ok=True)
C1, C2, C3 = '#087F8C', '#D87928', '#7357A5'
INK, GRAY, LIGHT = '#17212B', '#73808B', '#D7DDE1'
parts = ['<svg xmlns="http://www.w3.org/2000/svg" width="980" height="400" viewBox="0 0 980 400">',
         '<rect width="980" height="400" fill="white"/>']

def line(x1,y1,x2,y2,color=INK,width=1.2,dash=None):
    extra='' if dash is None else f' stroke-dasharray="{dash}"'
    parts.append(f'<line x1="{x1:.6f}" y1="{y1:.6f}" x2="{x2:.6f}" y2="{y2:.6f}" stroke="{color}" stroke-width="{width}"{extra}/>')

def text(x,y,value,size=17,anchor='start',color=INK,weight='normal'):
    parts.append(f'<text x="{x}" y="{y}" font-family="Arial, sans-serif" font-size="{size}" text-anchor="{anchor}" fill="{color}" font-weight="{weight}">{html.escape(value)}</text>')

def arrow(x1,y1,x2,y2,color,width=2.0,head=7):
    dx,dy=x2-x1,y2-y1
    norm=math.hypot(dx,dy); dx/=norm;dy/=norm
    line(x1,y1,x2-dx*head*.55,y2-dy*head*.55,color,width)
    bx,by=x2-dx*head,y2-dy*head
    coords=[(x2,y2),(bx-dy*head*.42,by+dx*head*.42),(bx+dy*head*.42,by-dx*head*.42)]
    parts.append('<polygon points="'+' '.join(f'{x:.6f},{y:.6f}' for x,y in coords)+f'" fill="{color}"/>')

def point(x,y,r=3,color=INK):
    parts.append(f'<circle cx="{x:.6f}" cy="{y:.6f}" r="{r}" fill="{color}"/>')

text(42,32,'(a)  Short-CORPSE control',19,weight='bold')
text(555,32,'(b)  Closed error curve',19,weight='bold')
# 控制图：横坐标为无量纲时间 Ωt。
x0,x1=71.,491.
y0,yp,ym=189.,105.,273.
T=7*math.pi/3
xt=lambda t:x0+(x1-x0)*t/T
ticks=[0,math.pi/3,2*math.pi,T]
labels=['0','π/3','2π','7π/3']
line(x0,80,x0,294,GRAY)
line(x0,y0,x1+14,y0,GRAY)
text(41,69,'uₓ/Ω',18)
text(x1+16,y0+7,'Ωt',18)
for y,lab in [(yp,'+1'),(ym,'−1')]:
    line(x0-5,y,x0,y,GRAY)
    text(x0-12,y+6,lab,16,'end')
    line(x0,y,x1,y,LIGHT,1,'3 4')
for t,lab in zip(ticks,labels):
    x=xt(t)
    line(x,y0-5,x,y0+5,GRAY)
    text(x,321,lab,17,'middle')
for t in ticks[1:]:
    line(xt(t),86,xt(t),295,LIGHT,1,'3 4')
line(xt(ticks[1]),yp,xt(ticks[1]),ym,GRAY,1.4)
line(xt(ticks[2]),ym,xt(ticks[2]),yp,GRAY,1.4)
for a,b,y,color in [(ticks[0],ticks[1],yp,C1),(ticks[1],ticks[2],ym,C2),(ticks[2],ticks[3],yp,C3)]:
    line(xt(a),y,xt(b),y,color,4.3)
text(276,361,'uᵧ = 0     |uₓ| = Ω',17,'middle',GRAY)

# 误差曲线：坐标由逐段原函数精确给出，三段均为半径1的圆弧。
scale=88.
cx,cy=773.,319.
xy=lambda ry,rz:(cx+scale*ry,cy-scale*rz)
left,right=652.,905.
line(left,cy,right,cy,GRAY)
line(left,cy,left,59,GRAY)
for value in [0,1,2]:
    yy=cy-scale*value
    line(left-4,yy,left,yy,GRAY)
    text(left-10,yy+5,str(value),15,'end',GRAY)
for value in [-1,1]:
    xx=cx+scale*value
    line(xx,cy,xx,cy+5,GRAY)
    text(xx,cy+25,str(value).replace('-','−'),15,'middle',GRAY)
parts.append('<text x="634" y="60" font-family="Arial, sans-serif" font-size="18" fill="#17212B">Ωr<tspan dy="5" font-size="12">z</tspan></text>')
parts.append('<text x="914" y="325" font-family="Arial, sans-serif" font-size="18" fill="#17212B">Ωr<tspan dy="5" font-size="12">y</tspan></text>')
text(565,84,'rₓ = 0',16,color=GRAY)
start=xy(0,0)
join1=xy(.5,math.sqrt(3)/2)
join2=xy(-.5,math.sqrt(3)/2)
for a,b,large,sweep,color in [(start,join1,0,1,C1),(join1,join2,1,0,C2),(join2,start,0,1,C3)]:
    parts.append(f'<path d="M {a[0]:.8f},{a[1]:.8f} A {scale},{scale} 0 {large} {sweep} {b[0]:.8f},{b[1]:.8f}" fill="none" stroke="{color}" stroke-width="3.4"/>')
# 各段的方向箭头按 n=(sin φ,cos φ) 放置。
for ry,rz,phase,color in [(1-math.cos(math.pi/6),.5,math.pi/6,C1),
                           (0,math.sqrt(3)+1,-math.pi/2,C2),
                           (-1-math.cos(-7*math.pi/6),.5,-7*math.pi/6,C3)]:
    xx,yy=xy(ry,rz)
    dx,dy=math.sin(phase),-math.cos(phase)
    arrow(xx-6*dx,yy-6*dy,xx+6*dx,yy+6*dy,color,2.5,8)
for x,y in [join1,join2]:point(x,y,3.1)
point(*start,3.4)
# 同一点的首末单位切向量，一上一下。
arrow(cx,cy,cx,cy-38,C1,1.9,7)
arrow(cx,cy,cx,cy+38,C3,1.9,7)
text(cx+11,cy-34,'n(0)',16,color=C1)
text(cx+11,cy+40,'n(T)',16,color=C3)
text(cx-14,cy+23,'0',15,'end',GRAY)
text(773,385,'r(0) = r(T) = 0',17,'middle')
parts.append('</svg>')
svg='\n'.join(parts)
(ASSETS/'short_corpse_geometry.svg').write_text(svg,encoding='utf-8')
doc=pymupdf.open(stream=svg.encode(),filetype='svg')
pdf=pymupdf.open('pdf',doc.convert_to_pdf())
pdf.save(ASSETS/'short_corpse_geometry.pdf',deflate=True)
pdf[0].get_pixmap(matrix=pymupdf.Matrix(1.6,1.6),alpha=False).save(ASSETS/'short_corpse_geometry.png')
print('created SVG, PDF, PNG in',ASSETS)
