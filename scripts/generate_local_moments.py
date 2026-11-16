#!/usr/bin/env python3
"""Emit exact Lean ring certificates for Appendix A local moments.
Generated lemmas are checked by Lean ring/positivity, not trusted Python output.
"""
from pathlib import Path

def add(a,b):
    c=[0]*max(len(a),len(b))
    for i,v in enumerate(a): c[i]+=v
    for i,v in enumerate(b): c[i]+=v
    return c

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c

def dot(a,b):
    c=[0]
    for x,y in zip(a,b): c=add(c,mul(x,y))
    return c

def model(L):
    n=L+2
    edges=[]
    prev=1
    for k in range(L-1):
        v=2+k
        edges.append((prev,v)); prev=v
    edges += [(prev,0),(0,n-1)]
    q=[[[0] for _ in range(n)] for _ in range(n)]
    for i,j in edges:
        for a,b in [(i,i),(j,j),(i,j),(j,i)]: q[a][b][0]+=1
    for i in (0,1):
        for j in (0,1): q[i][j]=add(q[i][j],[0,1])
    b=[[1] if i in (0,1) else [0] for i in range(n)]
    v=b
    vectors=[v]
    for _ in range(5):
        v=[dot(row,v) for row in q]
        vectors.append(v)
    return q,dot(b,v),vectors

def polynomial(c):
    terms=[]
    for i,v in enumerate(c):
        if v:
            terms.append(str(v) if i==0 else f'{v}*x'+(f'^{i}' if i>1 else ''))
    return ' + '.join(terms) or '0'

root=Path(__file__).resolve().parents[1]
s=['module','public import Mathlib','public import GraphPositiveEnergy.GraphMatrices','','/-! Exact finite local path-plus-leaf fifth moments.','All matrix equalities replay via kernel-checked ring normalization.','The infinite length stability and principal spectral comparison remain unproved. -/',
   '@[expose] public section','namespace GraphPositiveEnergy','open Matrix','']
base=[249,512,603,472,240,64]
for L in range(2,7):
    q,p,vectors=model(L); n=L+2
    rows=['!['+', '.join(polynomial(c) for c in row)+']' for row in q]
    s += [f'def localMatrix{L} (x : ℝ) : Matrix (Fin {n}) (Fin {n}) ℝ :=',
          '  !['+',\n    '.join(rows)+']',
          f'def localVector{L} : Fin {n} → ℝ := !['+', '.join('1' if i in (0,1) else '0' for i in range(n))+']']
    for k,v in enumerate(vectors[1:],1):
        prev=f'localVector{L}' if k==1 else f'localIter{L}_{k-1} x'
        s += [f'def localIter{L}_{k} (x : ℝ) : Fin {n} → ℝ := !['+', '.join(polynomial(c) for c in v)+']',
              f'theorem local_step_{L}_{k} (x : ℝ) : localMatrix{L} x *ᵥ ({prev}) = localIter{L}_{k} x := by',
              '  ext i', '  fin_cases i',
              f'  all_goals norm_num [localMatrix{L}, localVector{L}, '+', '.join(f'localIter{L}_{j}' for j in range(1,k+1))+', Matrix.mulVec, dotProduct, Fin.sum_univ_succ]',
              '  all_goals ring','']
    s += [f'theorem local_moment_{L} (x : ℝ) :',
          f'    localVector{L} ⬝ᵥ ((localMatrix{L} x)^5 *ᵥ localVector{L}) = {polynomial(p)} := by',
          '  simp only [pow_succ, pow_zero, Matrix.one_mul, ← Matrix.mulVec_mulVec]',
          '  rw ['+', '.join(f'local_step_{L}_{k}' for k in range(1,6))+']',
          f'  norm_num [localVector{L}, localIter{L}_5, dotProduct, Fin.sum_univ_succ]',
          '  ring','']
    edges=[]; prev=1
    for k in range(L-1):
        edges.append((prev,2+k)); prev=2+k
    edges += [(prev,0),(0,n-1)]
    rel=' ∨ '.join(f'(u.val = {i} ∧ v.val = {j})' for i,j in edges)
    s += [f'def localGraph{L} : SimpleGraph (Fin {n}) :=',
          f'  SimpleGraph.fromRel (fun u v => {rel})',
          f'instance : DecidableRel localGraph{L}.Adj := fun u v =>',
          f'  inferInstanceAs (Decidable (u ≠ v ∧ (({rel}) ∨ ('+rel.replace('u.val','TEMP').replace('v.val','u.val').replace('TEMP','v.val')+'))))',
          f'theorem local_degree_{L} (i : Fin {n}) : localGraph{L}.degree i = !['+', '.join(str(sum(i in e for e in edges)) for i in range(n))+'] i := by',
          '  fin_cases i <;> decide',
          f'theorem localMatrix_graph_{L} (x : ℝ) :',
          f'    localMatrix{L} x = signless localGraph{L} + x • vecMulVec localVector{L} localVector{L} := by',
          '  ext i j',
          '  simp only [signless, Matrix.add_apply, SimpleGraph.degMatrix, Matrix.diagonal_apply]',
          f'  simp_rw [local_degree_{L}]',
          '  fin_cases i <;> fin_cases j',
          f'  all_goals norm_num [localMatrix{L}, localVector{L}, signless, SimpleGraph.degMatrix,',
          f'    SimpleGraph.adjMatrix_apply, localGraph{L},',
          '    SimpleGraph.fromRel_adj, Fin.sum_univ_succ, Matrix.vecMulVec]',
          '']
s += ['end GraphPositiveEnergy','']
(root/'GraphPositiveEnergy/LocalMoments.lean').write_text('\n'.join(s),encoding='utf-8')
print('Emitted five actual finite matrix identities for Lean verification.')
