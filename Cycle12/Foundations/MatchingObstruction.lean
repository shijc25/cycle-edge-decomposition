import GallaiEdmondsLib.GallaiEdmonds

/-! The precise matching obstruction used in the DY structural lemma.
The barrier has more components than deleted vertices, and at least two. -/
namespace Cycle13
open SimpleGraph GallaiEdmonds
noncomputable section

def Hypomatchable {V : Type} (H : SimpleGraph V) : Prop :=
  ∀ v : V, HasPerfectMatchingOn H (Set.univ \ {v})

theorem exists_matching_obstruction {V : Type} [Finite V] (H : SimpleGraph V)
    (hperfect : ¬ HasPerfectMatchingOn H Set.univ) (hhypo : ¬ Hypomatchable H) :
    ∃ U : Set V, IsMinBarrier H U ∧ U.ncard < (comps H Uᶜ).ncard ∧
      2 ≤ (comps H Uᶜ).ncard := by
  classical
  obtain ⟨U,hU⟩ := exists_minBarrier H
  obtain ⟨M,hM,hmax⟩ := exists_maximum H
  have heq := hU.1.eq hM hmax
  have hverts : M.verts ≠ Set.univ := fun he => hperfect ⟨M,hM,he⟩
  have hvlt : M.verts.ncard < Nat.card V := by
    have hs : M.verts ⊂ Set.univ := Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _,hverts⟩
    simpa using Set.ncard_lt_ncard hs
  have hodd : U.ncard < oddC H Uᶜ := by omega
  have hle : oddC H Uᶜ ≤ (comps H Uᶜ).ncard :=
    Set.ncard_le_ncard (fun _ h => h.1)
  refine ⟨U,hU,hodd.trans_le hle,?_⟩
  by_contra! hsmall
  have hcomp : (comps H Uᶜ).ncard=1 := by omega
  have hUzero : U.ncard=0 := by omega
  have hUempty : U=∅ := (Set.ncard_eq_zero (Set.toFinite U)).mp hUzero
  obtain ⟨K,hK⟩ := Set.ncard_eq_one.mp hcomp
  have hKuniv : K=Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    have hv : v ∈ Uᶜ := by simp [hUempty]
    have hc : cc H Uᶜ v ∈ comps H Uᶜ := cc_mem_comps hv
    rw [hK,Set.mem_singleton_iff] at hc
    exact hc ▸ mem_cc_self hv
  have hKodd : K ∈ oddComps H Uᶜ := by
    have hnon : (oddComps H Uᶜ).Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by
      change 0 < oddC H Uᶜ
      omega)
    obtain ⟨J,hJ⟩ := hnon
    have hJK := hJ.1
    rw [hK,Set.mem_singleton_iff] at hJK
    exact hJK ▸ hJ
  apply hhypo
  intro v
  obtain ⟨P,hP,hPv⟩ := minBarrier_factorCritical hU hM hmax hKodd
    (show v ∈ K by rw [hKuniv]; trivial)
  exact ⟨P,hP,by simpa only [hKuniv] using hPv⟩

end
end Cycle13
