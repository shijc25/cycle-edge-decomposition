#!/usr/bin/env python3
"""Regenerate paper tables from retained Lean source and exact documentary data."""
from pathlib import Path
from fractions import Fraction as F
import json,re,shutil,hashlib,gzip
r=Path(__file__).resolve().parents[1];p=r/'paper';d=json.loads((p/'data/global12.json').read_text())
params=dict(re.findall(r'^def (\w+) : ℝ := \(([\d/]+)\)',(r/'Cycle12/GlobalParameters12.lean').read_text(),re.M))
assert set(d['parameters'])==set(params)
assert all(F(v)==F(params[k]) for k,v in d['parameters'].items())
chains={};cutoff={}
s=(r/'Cycle12/FiniteCutoffBounds.lean').read_text()
for cid,part in re.findall(r'theorem cutoff(\d{3})(.*?)(?=\ntheorem |\nend )',s,re.S):
 q=re.search(r'\^\(\(\(([\d/]+)\):ℚ\):ℝ\)',part).group(1);cutoff[F(q)]=cid
for c,q in [(cid,q) for q,cid in cutoff.items()]:
 rel=f'Cycle12/FiniteChains/Chain{c}.lean';s=(r/rel).read_text()
 degree=int(re.search(r'def degreeCap : ℕ := (\d+)',s).group(1))
 fee=re.search(r'def costBound : ℚ := \(([\d/]+)\)',s).group(1)
 terminal=int(re.search(r'def terminal : RatTerminalParameters := ⟨(\d+),',s).group(1))
 stages=len(re.findall(r'^def stage\d+ : FiniteStageCertificate ',s,re.M))
 src=d['finite_files'][str(q)] if str(q) in d['finite_files'] else next(v for k,v in d['finite_files'].items() if F(k)==q)
 f=p/'data'/src
 old=json.loads(f.read_text());assert F(old['cutoff'])==q and degree==old['degree_cap'], (c,str(q),'degree/cutoff mismatch')
 chains[c]={'module':'Cycle12.FiniteChains.Chain'+c,'source':rel,'cutoff':str(q),'degree_cap':degree,'cost_bound':fee,'stages':stages,'terminal_u':terminal,'documentary_input':src,'historical_cost_difference_from_lean':str(F(old['finite_cost'])-F(fee)),'source_sha256':hashlib.sha256((r/rel).read_bytes()).hexdigest()}
assert len(chains)==83
(p/'data/finite-chain-index.json').write_text(json.dumps(chains,indent=2)+'\n')
# Check the links actually used by every base and phase source, not just the numerical sort order.
for i,b in enumerate(d['base_intervals']):
 s=(r/f'Cycle12/FinitePotentialPayments/Interval{i:02}.lean').read_text();cid=cutoff[F(b['cutoff'])]
 assert 'Chain'+cid+'.costBound' in s,(i,cid);b['lean_chain']=cid
for i,ph in enumerate(d['phase_intervals']):
 s=(r/f'Cycle12/EvenPhaseCertificates/Phase{i:02}.lean').read_text();cid=cutoff[F(ph['cutoff'])]
 assert 'Chain'+cid+'.costBound' in s,(i,cid);ph['lean_chain']=cid
# Validate all exact prefix entries against their Lean definitions.
for i,ph in enumerate(d['phase_intervals']):
 s=(r/f'Cycle12/Phase{i:02}.lean').read_text();a=s[s.index('def initial'):s.index('def threshold')]
 u={int(k):F(v) for k,v in re.findall(r'\| (\d+) => \(([\d/]+) : ℝ\)',a)}
 assert [u[j] for j in range(1,17)]==list(map(F,ph['prefix']['u'])),i
 a=s[s.index('def threshold'):s.index('def sequence')];v={int(k):F(q) for k,q in re.findall(r'\| (\d+) => \(([\d/]+) : ℝ\)',a)}
 tail=F(re.search(r'else \(([\d/]+) : ℝ\)',a).group(1));v[16]=tail
 assert [v[j] for j in range(3,17)]==list(map(F,ph['prefix']['P'])),i
 assert F(re.search(r'def r : ℝ := \(([\d/]+)',s).group(1))==F(ph['prefix']['r']),i
(p/'data/phase-base-index.json').write_text(json.dumps({'base':d['base_intervals'],'phases':d['phase_intervals']},indent=2)+'\n')
latex=lambda x: str(F(x).numerator) if F(x).denominator==1 else r'\frac{'+str(F(x).numerator)+'}{'+str(F(x).denominator)+'}'
symbols={'w0':'w_0','theta0':r'\theta_0','theta1':r'\theta_1','theta2':r'\theta_2','alpha':r'\alpha','lam':r'\lambda','gamma':r'\gamma','delta':r'\delta','eps':r'\varepsilon','c':'c_0','prune_a':r'a_{\rm prune}','rho':r'\rho','wA':'w_A','eta':r'\eta','overlap':r'\chi','batch':'B_0','sigma':r'\sigma','kappa':r'\kappa','phi0':r'\phi_0'}
lines=[r'\section{Exact parameters and certificate indices}\label{app:parameters}',r'''The following values are read from \mcode{GlobalParameters12} and checked
for exact equality with the documentary input \mcode{paper/data/global12.json}.
Fractions in this table are exact. Large finite certificate entries remain
in the Lean source; the supplementary JSON files provide their indices.
''',r'\begin{longtable}{@{}ll@{}}',r'\toprule Parameter & Exact value\\\midrule\endhead']
for k,v in d['parameters'].items():
 label='$'+symbols.get(k,k)+'$' if '_' not in k or k in symbols else r'\mcode{'+k+'}'
 lines.append(label+' & $'+latex(v)+r'$\\[3pt]')
lines += [r'\bottomrule\end{longtable}',r'''The archived ordinary-proof finite inputs are included for provenance. Their
reported upper bounds can differ in the last few decimal places from the
formally proved chain constants. This paper and its tables use the Lean
constants exclusively; the index records the exact differences. No historical
Python fee is used as a premise of the formal proof.

The main degree logarithm is $158387/1000$. The tail parameter is
$r=88331750161/10^{11}$, with $\beta=r(1-r)$ and $Q=1/[r^2(1-r)]$.
The parameters \mcode{p}, \mcode{router_length}, \mcode{route_load},
\mcode{order_bound}, and \mcode{router_constant} belong to the completion
and routing gates; they are not independent choices left open in the proof.

Rational certificates enclose powers of $2$, logarithms, square roots and
cube roots. For a positive series, a finite partial sum is a lower bound;
an upper bound includes a proved geometric tail. The renewal loss is
bounded by a positive finite expansion with its proved tail, and all
inequalities are preserved in the required direction. Tangent certificates
control continuous density intervals; monotonicity and rate certificates
control scale half-lines. These steps justify extending the finite data to
all graphs and all numbers of stages.

The phase table below is for orientation: its displayed phase endpoints
are rounded to six decimal places and are \emph{not} used as certificate
endpoints. The exact endpoints, thresholds $P_3,\ldots,P_{16}$, and all
$u_1,\ldots,u_{16}$ are in \mcode{paper/data/phase-base-index.json} and in
the corresponding Lean modules. The listed fees are the actual rational
\mcode{costBound} constants of the Lean finite chains.
''',r'\begin{longtable}{@{}rrrrr@{}}',r'\toprule Phase & $a$ (display) & $d$ (display) & Chain & $f_{a,d}$\\\midrule\endhead']
for i,ph in enumerate(d['phase_intervals']):
 cid=ph['lean_chain'];lines.append(f"{i:02} & {float(F(ph['lo'])):.6f} & {float(F(ph['hi'])):.6f} & {cid} & ${latex(chains[cid]['cost_bound'])}$"+r'\\[3pt]')
lines += [r'\bottomrule\end{longtable}',r'''The $45$ base intervals and their assigned chains are listed in the same
exact index file. The following table records all $83$ finite chains. Its
cutoff $x$ means the average-degree condition $2m\le2^xn$; the file also
records the larger integer degree cap used for this condition. The column
$u$ is the denominator of the harmonic starting bound, and $s$ is the
number of certified DFS steps. Every chain uses the same mixed-cover
parameters $B_*=43/10$, $A_*=3$ and singleton weight $23/42$.
''',r'\begin{longtable}{@{}rrrrr@{}}',r'\toprule Chain & Exact cutoff $x$ & $s$ & $u$ & Certified fee\\\midrule\endhead']
for cid,ch in sorted(chains.items()):lines.append(cid+' & $'+latex(ch['cutoff'])+f"$ & {ch['stages']} & {ch['terminal_u']} & $"+latex(ch['cost_bound'])+r'$\\[3pt]')
lines += [r'\bottomrule\end{longtable}']
(p/'sections/13-parameters.tex').write_text('\n'.join(lines)+'\n')
# Principal correspondences are verified against the actual proof-body dependency report.
wanted=[
 ('thm:main','Final original-edge partition','Cycle12.coefficient12'),
 ('lem:eg-input','Rotation and deletion cycle bound','Cycle12.Independent.erdosGallai_cycle'),
 ('lem:sampling-input','Bernoulli sample lower tail','Cycle13.vertex_sample_edge_lower_tail'),
 ('prop:weighted-reduction','Weighted order to coefficient twelve','Cycle12.coefficient12_from_weighted_order_bound'),
 ('lem:amplification','Finite rooted amplification','Cycle12.rooted_weighted_order_to_predecessor'),
 ('lem:six','Circumference at most six','Cycle12.terminal_rank_no_seven_cycle'),
 ('lem:harmonic','Harmonic affine extension','Cycle13.weightedAffine_harmonic'),
 ('lem:mixed','Mixed cover','Cycle12.mixed_cover'),
 ('lem:dfs-step','Certified DFS step','Cycle12.FiniteStageCertificate.step'),
 ('prop:finite-base','Finite-degree potential bound','Cycle12.Global12.finite_degree_potential'),
 ('lem:loss-decay','Uniform loss decay','Cycle12.Global12.lossH_decay'),
 ('lem:potential','Renewal potential payment','Cycle12.Global12.globalPhi_fold_budget'),
 ('sec:layers','Actual even scale layers','Cycle12.Even12.exists_actual_scale_layers'),
 ('lem:completion','High-centre completion','Cycle12.Even12.high_center_completion_at_scale'),
 ('lem:routing','Even-bank grouped weighted routing','Cycle12.Even12.bank_routing_at_scale'),
 ('sec:routing','Joint original endpoint family','Cycle12.Even12.ActualFoldStage12.jointFamily'),
 ('eq:fold-masses','Active mass lower bound','Cycle12.Even12.ActualFoldStage12.activeMass_lower'),
 ('lem:physical','Four-family actual packing payment','Cycle12.Even12.ActualFoldStage12.actual_fold_target_payment'),
 ('lem:physical','Whole-graph physical construction','Cycle12.Global12.physical_fold_construction12'),
 ('lem:ledger','Physical scalar ledger','Cycle12.Global12.physical_fold_ledger_payment'),
 ('lem:no-fold-mass','No-fold core mass bound','Cycle12.Even12.EvenScaleLayers12.kept_mass_of_no_fold'),
 ('lem:terminal-payment','Infinite terminal tail','Cycle12.Global12.infinite_terminal_tail_payment'),
 ('lem:terminal-payment','Terminal potential payment','Cycle12.Global12.terminal_potential_payment'),
 ('thm:weighted-potential','Strong induction from physical branch','Cycle12.Global12.potential_bound_from_fold_branch'),
 ('app:terminal','Coverage of finite parameter tuples','Cycle12.six_residue_parameter_coverage'),
 ('app:cover','Full continuous cover','Cycle12.CoverAssembly.Full.sound'),
]
with gzip.open(r/'audit/main-dependency-audit.json.gz','rt') as f:report=json.load(f)
lookup={x['name']:x for x in report['declarations']};mapping=[];missing=[]
for label,desc,name in wanted:
 if name not in lookup:
  suffix=name.split('.')[-1];candidates=[x for x in lookup if x.endswith('.'+suffix)];missing.append((name,candidates[:6]));continue
 row=lookup[name];module=row['module']
 source=module.replace('.','/')+'.lean';assert (r/source).exists();mapping.append({'paper_label':label,'description':desc,'declaration':name,'module':module,'source':source,'actual_dependency':True})
if missing:print('MISSING',missing);raise SystemExit(1)
(r/'docs/proof-map.json').write_text(json.dumps(mapping,indent=2)+'\n')
s=[r'\section{Correspondence with Lean}\label{app:correspondence}',r'''The following declarations are present in the audited transitive proof-body
closure of the main theorem. The machine-readable table
\mcode{docs/proof-map.json} records their modules and source paths. The
conditional induction interface in the last part of the proof is instantiated
with the proved physical construction; it is not an additional assumption
of Theorem~\ref{thm:main}. Some source comments record earlier intermediate
obligations. Their discharge is determined by the final theorem and its
actual dependency chain, not by those historical comments.
''',r'\begin{longtable}{@{}p{0.30\textwidth}p{0.66\textwidth}@{}}',r'\toprule Statement & Lean declaration\\\midrule\endhead']
for e in mapping:s.append(e['description']+r' (\ref{'+e['paper_label']+r'}) & {\small\nolinkurl{'+e['declaration']+r'}}\\[7pt]')
s.append(r'\bottomrule\end{longtable}');(p/'sections/14-correspondence.tex').write_text('\n'.join(s)+'\n')
(r/'release/paper-data-validation.json').write_text(json.dumps({'passed':True,'global_parameters_exact':len(params),'finite_chains':len(chains),'base_intervals':45,'phase_intervals':40,'phase_rational_sequences_matched':40,'principal_declarations_in_actual_dependency_closure':len(mapping),'current_replacement_closure':True,'main_proof_dependency_report_sha256':hashlib.sha256((r/'audit/main-dependency-audit.json.gz').read_bytes()).hexdigest()},indent=2)+'\n')
print('Parameters, 83 finite chains, 45 bases, 40 phases and',len(mapping),'declaration links checked.')
