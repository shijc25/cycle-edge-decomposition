import Cycle12.EvenCorePacking12
import Cycle12.EvenActualPrefixMass12

namespace Cycle12.Even12
open Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- All core packings are constructed from the smaller-order IH.
The remaining input is a packing of the actual stopped remainder. -/
theorem EvenScaleLayers12.terminal_packing_from_ih {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (ih : ∀ m, m<Fintype.card V → ∀ H : SimpleGraph (Fin m),
      ∃ Q : CyclePacking H, Q.weight≤C*m)
    (PH : CyclePacking (stoppedRemainder L)) {T : ℝ} (hH : PH.weight≤T) :
    ∃ Q : CyclePacking G, Q.weight≤
      ((pastCycles L.splitter 0 (L.stopIndex+1) [originalPiece G]).length:ℝ)+
      (1+C*eta)*vertexMass (pastPieces L.splitter 0 (L.stopIndex+1) [originalPiece G])+T := by
  exact terminal_packing_assembly _ _ (L.stopped_partition (L.stopIndex+1))
    (pastCycles_good L.splitter 0 (L.stopIndex+1) [originalPiece G])
    (L.past_core_packing (by omega) ih) PH hH

/-- The no-fold branch with its exact unused infinite tail. Every graph
packing in the conclusion is constructed, including all retained cores. -/
theorem EvenScaleLayers12.terminal_no_fold_bound {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (ih : ∀ m, m<Fintype.card V → ∀ H : SimpleGraph (Fin m),
      ∃ Q : CyclePacking H, Q.weight≤C*m)
    {A f : ℝ} (hA : 0<A) (hphase : A≤theta2^L.stopIndex*originalLog V)
    (hZ1 : phaseOverlap1 A<1) (hZ2 : phaseOverlap2 A<1) (hZ3 : phaseOverlap3 A<1)
    (u P : ℕ → ℝ) (hu1 : phaseMass1 A≤u 1) (hu2 : phaseMass2 A≤u 2)
    (hu : ∀ n, 0≤u n) (hup : ∀ n, 1≤n → 0<u n) (hs : Summable u)
    (hss : ∀ t, 2<t → (∑' j : ℕ, u (j+(t-2)))≤P t*u t)
    (hfold : ¬∃ i : Fin (L.stopIndex+3), 0<L.coreMass i.val ∧ i.val+2<L.stopIndex+3 ∧
      (∑ j : Fin (L.stopIndex+3) with j.val ≤ i.val+2, L.coreMass j.val)≤
        P (L.stopIndex+3-i.val)*L.coreMass i.val)
    (hfinite : ∃ PH : CyclePacking (stoppedRemainder L), PH.weight≤f*Fintype.card V) :
    ∃ Q : CyclePacking G, Q.weight≤
      (f+(1+C*eta)*(sequenceTail u 3-sequenceTail u (L.stopIndex+4))+
        phaseMass3 A*scaleMassSeries theta2 (eps*A)/2)*Fintype.card V := by
  obtain ⟨PH,hPH⟩ := hfinite
  obtain ⟨Q,hQ⟩ := L.terminal_packing_from_ih ih PH hPH
  have hmass := L.kept_mass_of_no_fold hA hphase hZ1 hZ2 u P hu1 hu2 hu hup hs hss hfold
  have hmass' := mul_le_mul_of_nonneg_left hmass (by norm_num [C,eta] : (0:ℝ)≤1+C*eta)
  have hcycles := kept_long_cycles_phase_bound L hA hphase hZ3
  refine ⟨Q,?_⟩
  nlinarith only [hQ,hmass',hcycles]

end
end Cycle12.Even12
