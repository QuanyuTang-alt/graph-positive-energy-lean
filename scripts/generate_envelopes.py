#!/usr/bin/env python3
"""Construct exact positive Bernstein decompositions of Appendix A inequalities.
Python emits coefficients; Lean verifies identities and all nonnegativity claims.
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path

def add(a,b):
    c=[F(0)]*max(len(a),len(b))
    for i,v in enumerate(a): c[i]+=v
    for i,v in enumerate(b): c[i]+=v
    return c

def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c

def scale(a,b): return [x*b for x in a]
def power(a,n):
    c=[F(1)]
    for _ in range(n): c=mul(c,a)
    return c

def rat(x):
    return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator} : ℝ)'
def poly(c,var='t'):
    return ' + '.join(f'({rat(v)})'+(f'*{var}^{i}' if i else '') for i,v in enumerate(c) if v) or '0'
A=[F(2140),0,0,0,F(-7)]; B=[F(4414),0,0,0,F(-4)]; K=[F(625),F(125),F(25),F(5)]
L=add(scale(mul(power(A,2),power(B,2)),F(1,2)),scale(power(A,3),F(1000)))
BK=mul(power(B,3),K); av=[F(49,8),F(-7,2),F(1,2)]
rows=[]
for r,a,b in [(3,F(2),F(12,5)),(5,F(12,5),F(14,5)),(8,F(14,5),F(3))]:
    M=F(comb(2*r+2,r+1),r+1)*F((r-1)**(r-1),r**r)
    rows.append((add([F(0)]*(r-1)+av,[-M]),a,b))
for r,a,b in [(10,F(3),F(7,2)),(30,F(7,2),F(58,15))]:
    M=F(comb(2*r+2,r+1),r+1)*F((r-1)**(r-1),r**r)
    rows.append((add([F(0)]*(r-1)+L,scale(BK,-M)),a,b))
rows.append((add(L,scale(mul([F(4),F(-1)],BK),-F(comb(62,31),31*4**30))),F(58,15),F(4)))
s=['module','public import Mathlib','public import GraphPositiveEnergy.ScalarChecks','','/-! Exact Bernstein certificates for the six Appendix A scalar inequalities.','These certificates do not supply spectral moment estimates or any principal theorem. -/','@[expose] public noncomputable section','namespace GraphPositiveEnergy','']
for k,(p,a,b) in enumerate(rows):
    n=len(p)-1
    c=[F(0)]*(n+1)
    for j,x in enumerate(p): c=add(c,scale(power([a,b-a],j),x))
    coeff=[sum(c[j]*F(comb(i,j),comb(n,j)) for j in range(i+1))*comb(n,i) for i in range(n+1)]
    assert all(x>0 for x in coeff)
    s += [f'def envelopePoly{k} (t : ℝ) : ℝ := {poly(p)}',
          f'def envelopeCoeffs{k} : Fin {n+1} → ℝ := !['+', '.join(rat(v) for v in coeff)+']',
          f'theorem envelope_identity_{k} (u : ℝ) :',
          f'    envelopePoly{k} ({rat(a)}+({rat(b-a)})*u) =',
          f'      ∑ i : Fin {n+1}, envelopeCoeffs{k} i*u^i.val*(1-u)^({n}-i.val) := by',
          f'  norm_num [envelopePoly{k}, envelopeCoeffs{k}, Fin.sum_univ_succ]',
          '  ring',
          f'theorem envelope_nonneg_{k} {{t : ℝ}} (ha : {rat(a)} ≤ t) (hb : t ≤ {rat(b)}) :',
          f'    0 ≤ envelopePoly{k} t := by',
          f'  let u : ℝ := (t-{rat(a)})/({rat(b-a)})',
          '  have hu : 0 ≤ u := by dsimp [u]; linarith',
          '  have hv : 0 ≤ 1-u := by dsimp [u]; linarith',
          f'  have heq : t = {rat(a)}+({rat(b-a)})*u := by dsimp [u]; ring',
          f'  rw [heq, envelope_identity_{k}]',
          '  apply Finset.sum_nonneg', '  intro i _',
          f'  have hc : 0 ≤ envelopeCoeffs{k} i := by fin_cases i <;> norm_num [envelopeCoeffs{k}]',
          '  exact mul_nonneg (mul_nonneg hc (pow_nonneg hu _)) (pow_nonneg hv _)','']
    if k < 3:
        r=[3,5,8][k]
        constant=F(comb(2*r+2,r+1),r+1)*F((r-1)**(r-1),r**r)
        form=f't^{r-1}*((1/2 : ℝ)*((7/2 : ℝ)-t)^2)-{rat(constant)}'
    elif k < 5:
        r=[10,30][k-3]
        constant=F(comb(2*r+2,r+1),r+1)*F((r-1)**(r-1),r**r)
        form=f't^{r-1}*((1/2 : ℝ)*(Astar t)^2*(Bstar t)^2+1000*(Astar t)^3)-{rat(constant)}*(Bstar t)^3*Kstar t'
    else:
        constant=F(comb(62,31),31*4**30)
        form=f'((1/2 : ℝ)*(Astar t)^2*(Bstar t)^2+1000*(Astar t)^3)-{rat(constant)}*(4-t)*(Bstar t)^3*Kstar t'
    s += [f'theorem envelope_source_form_{k} (t : ℝ) :',
          f'    envelopePoly{k} t = {form} := by',
          f'  unfold envelopePoly{k}'+(' Astar Bstar Kstar' if k>=3 else ''),
          '  ring','']
s += ['end GraphPositiveEnergy','']
root=Path(__file__).resolve().parents[1]
(root/'GraphPositiveEnergy/EnvelopeCertificates.lean').write_text('\n'.join(s),encoding='utf-8')
print('Emitted six rational Bernstein identities and interval nonnegativity proofs.')
