"""Independent recomputation of ALL 33 certify_base margins from candidate_base.json.
Stdlib decimal only (prec 60 digits ~ 200 bits). No flint, no shared code with certify_base.py.
pi via Machin; sin/cos via Taylor; exp/ln/sqrt/arctan via decimal module.
"""
import json, sys
from decimal import Decimal as D, getcontext
getcontext().prec = 60

def atand(x):
    # Taylor atan: |x|<1, terms decay by x^2 per term
    x2 = x*x; s, term = D(0), x
    for n in range(200):
        s = s + term if n % 2 == 0 else s - term
        term = term * x2 * (2*n+1)/(2*n+3)
        if term < D(10)**-59: break
    return s
PI = 16*atand(D(1)/5) - 4*atand(D(1)/239)
LN2 = D(2).ln()
def cos_t(x):
    x = x % (2*PI)
    if x > PI: x = 2*PI - x
    s, term = D(1), D(1)
    for n in range(80):
        term = term * x*x / ((2*n+1)*(2*n+2))
        if term < D(10)**-59: break
        s = s - term if n % 2 == 0 else s + term
    return s
def sin_t(x):
    x = x % (2*PI)
    if x > PI: x = 2*PI - x; sgn = -1
    else: sgn = 1
    s, term = D(0), x
    for n in range(0, 80):
        s = s + term if n % 2 == 0 else s - term
        term = term * x*x / ((2*n+2)*(2*n+3))
        if term < D(10)**-59: break
    return sgn * s
def log2d(x): return x.ln()/LN2
H2 = lambda x: -(x*log2d(x) + (1-x)*log2d(1-x))
coshd = lambda x: (x.exp() + (-x).exp())/2

cand = json.load(open(sys.argv[1]))
D0 = {k: D(cand[k]) for k in ('tau0','eta','mu','a','gamma','l','kappa','p','q_m','epsilon','zeta','input_guard_coefficient')}
t, eta, mu, a, g, l = D0['tau0'], D0['eta'], D0['mu'], D0['a'], D0['gamma'], D0['l']
kap, p, q = D0['kappa'], D0['p'], D0['q_m']
eps, zeta, guard = D0['epsilon'], D0['zeta'], D0['input_guard_coefficient']
r = 1 - mu - l
Dl = eta - t; G = 2*t - eta; aG = Dl/G
ncos = cand['n_terms']; rc = [D(x) for x in cand['rc']]; sc = [D(x) for x in cand['sc']]

# --- grid (N_in=256, c=32 defaults) ---
N_in, c = 256, 32
beta, sig = D('0.1'), D('0.3')
N = N_in*c
dth = 2*PI/N
cosd, sind = cos_t(dth), sin_t(dth)
cosk = [D(1)]*N; sink = [D(0)]*N
for k in range(1, N):
    cosk[k] = cosk[k-1]*cosd - sink[k-1]*sind
    sink[k] = sink[k-1]*cosd + cosk[k-1]*sind
# Chebyshev recurrence for cos(j*theta_k), sin(j*theta_k), j=1..16
C = [[D(1)]*N, list(cosk)]; Sg = [[D(0)]*N, list(sink)]
for j in range(2, ncos+1):
    C.append([2*cosk[k]*C[j-1][k] - C[j-2][k] for k in range(N)])
    Sg.append([2*cosk[k]*Sg[j-1][k] - Sg[j-2][k] for k in range(N)])
def trig(co, k):
    return sum((co[j]*C[j+1][k] for j in range(ncos)), D(0)) + sum((co[ncos+j]*Sg[j+1][k] for j in range(ncos)), D(0))
rk = [trig(rc, k) for k in range(N)]; sk = [trig(sc, k) for k in range(N)]
F = [(t_*LN2).exp() for t_ in rk]; Gv = [(t_*LN2).exp() for t_ in sk]
Zf = sum(F)/N; Zg = sum(Gv)/N
Zfk = sum(((kap*t_)*LN2).exp() for t_ in rk)/N; Zgk = sum(((kap*t_)*LN2).exp() for t_ in sk)/N
LZ = log2d(Zf*Zg); H_ = log2d(Zfk) + log2d(Zgk) - kap*LZ
Gs = [Gv[c*m] for m in range(N_in)]
GSs = [Gv[c*m]*sk[c*m] for m in range(N_in)]
FR = [F[k]*rk[k] for k in range(N)]
u, v = [], []
for k in range(N):
    Pk, Yk = D(0), D(0)
    for m in range(N_in):
        i = (k + c*m) % N
        Pk += F[i]*Gs[m]; Yk += FR[i]*Gs[m] + F[i]*GSs[m]
    Pk /= N_in; Yk /= N_in
    L = log2d(Pk) - LZ; B = Yk/Pk - LZ
    u.append(L + (kap-1)*B - H_); v.append((2-kap)*B - 2*L + H_)
# strip bounds (q0, U*, W*) -- quadrature errors e^{-sigma*N} ~ 1e-1067, omitted (documented)
def Sstrip(co, y): return sum(abs(co[j])*coshd((j+1 if j < ncos else j-ncos+1)*y) for j in range(len(co)))
def trig_mod(co, k):  # coefficients pre-weighted by cosh(freq*beta) as in certify_c5 line 50-51
    return sum((co[j]*coshd((j+1 if j < ncos else j-ncos+1)*beta)*C[j+1][k] for j in range(ncos)), D(0)) \
         + sum((co[j]*coshd((j-ncos+1)*beta)*Sg[(j-ncos)+1][k] for j in range(ncos, len(co))), D(0))
rb = rc; sb = sc
nf = sum(((2*trig_mod(rb, k)*LN2).exp() for k in range(N)))/N/(Zf*Zf)
ng = sum(((2*trig_mod(sb, k)*LN2).exp() for k in range(N)))/N/(Zg*Zg)
q0 = ((nf-1)*(ng-1)).sqrt()
Bmax = ((nf*ng).sqrt()*(Sstrip(rc, beta) + Sstrip(sc, beta)) + (1+q0)*abs(LZ))/(1-q0)
lam = -log2d(1-q0)
U = lam + abs(kap-1)*Bmax + abs(H_); W = 2*lam + abs(2-kap)*Bmax + abs(H_)
# --- moments ---
rho_f = eta - D('1.5e-6'); rho_c = rho_f - D('1e-6')
I1 = sum(((2 + 2*cosk[k]) * (p*(Dl - u[k])*LN2).exp() for k in range(N)))/N
I2 = sum(((2 + 2*cosk[k]) * (q*(aG*v[k] - u[k])*LN2).exp() for k in range(N)))/N
# --- margins (lower-bound comparison; decimal treated as exact recompute, radii < 1e-45 at prec 60) ---
res = {
 'C1 gamma < h(2a)/2': H2(2*a)/2 - g,
 'C2 left list': t - (l + (H2(a) - g)*mu),
 'C3 right classes': t - (r + (1 - g)*mu),
 'C4 pairs': t - (1 - mu + (H2(a) + H2(D('0.5') - a) - g)*mu - eta),
 'C5 right masks': t - (H2(D('0.5') - a)*mu + D('0.5') - t),
 'C5L left masks (implied)': t - (H2(a)*mu + D('0.5') - t),
 'C6 r > 0': r, 'C6 r < tau0': t - r, 'C6 l < tau0': t - l,
 'C7 mu(1-2a) < l': l - mu*(1 - 2*a),
 'C8 (mu/2)log3 < eta': eta - mu/2*log2d(D(3)),
}
e0 = min(res.values())
res.update({
 'eps0 > zeta + 1/guard': e0 - (zeta + 1/guard),
 'mu < tau0 - eps0': t - e0 - mu,
 'A5': (eta - mu/2*log2d(D(3)))/2 - (D('0.5') - t + zeta),
 'S1: 4a < 1': 1 - 4*a,
 'S3': (1 - 2*a) - (H2(2*a)/2 + H2(a)),
 'Delta > 0': Dl, 'Gamma > 0': G,
 'A7.1 l': t - e0 - l, 'A7.1 r': t - e0 - r, 'A7.1 mu(1-2a)': t - e0 - mu*(1-2*a),
 'A7.3': (t - e0 + zeta) - (D('0.5') - t + zeta + g*mu/2),
 'A7.4': (t - e0 + zeta) - (r + D('0.5') - t + zeta),
 'S2': D('0.5') - mu*(1 - 2*a),
 'S5': H2(D('0.5') - a) - H2(a),
 'prime draw': t - eta/2,
 'B2 aG<=3/4': D('0.75') - aG,
 'rho0 p>=1': p - 1, 'rho1..9 q>=1': q - 1,
 'sum z <= 418.36': D('418.36') - max(p, q),
 'B3': (eta - rho_f) - (18 + 6*max(p, q))*eps,
 'B1 rho_f-rho_c': rho_f - rho_c,
 'M1': rho_c - log2d(I1), 'M2': rho_c - log2d(I2),
})
print(json.dumps({k: str(val) for k, val in res.items()}, indent=1))
print('q0_d=%.15f Ustar_d=%.12f Wstar_d=%.12f' % (q0, U, W))
print('log2M1_d=%s' % log2d(I1))
print('log2M2_d=%s' % log2d(I2))
print('T_d=%s' % (t + 20*eps))
print('all_pass_d=%s' % all(val > 0 for val in res.values()))
