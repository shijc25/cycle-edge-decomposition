import Cycle12.Foundations.SmallBoundaryCore
import Cycle12.Foundations.ForestBound

/-! Counting the boundaries of the components left after vertex deletion.
The half-d edge-connectivity and maximum-degree bounds imply the component
condition needed for the parity blowup. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def deletedComponentVerts (G : SimpleGraph V) (S : Finset V)
    (c : (G.induce ((S : Set V)ᶜ)).ConnectedComponent) : Finset V :=
  c.supp.toFinset.image Subtype.val

theorem mem_deletedComponentVerts (G : SimpleGraph V) (S : Finset V)
    (c : (G.induce ((S : Set V)ᶜ)).ConnectedComponent) (v : ((S : Set V)ᶜ : Set V)) :
    v.val∈deletedComponentVerts G S c ↔ v∈c.supp := by
  constructor
  · intro hv
    obtain ⟨w,hw,he⟩ := mem_image.mp hv
    have heq : w=v := Subtype.ext he
    exact heq ▸ (Set.mem_toFinset.mp hw)
  · intro hv
    exact mem_image_of_mem _ (Set.mem_toFinset.mpr hv)

theorem deletedComponentVerts_subset (G : SimpleGraph V) (S : Finset V)
    (c : (G.induce ((S : Set V)ᶜ)).ConnectedComponent) :
    deletedComponentVerts G S c ⊆ Sᶜ := by
  rintro v hv
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
  exact mem_compl.mpr w.property

theorem sum_deletedComponentVerts (G : SimpleGraph V) (S : Finset V)
    (c : (G.induce ((S : Set V)ᶜ)).ConnectedComponent) (f : V → ℕ) :
    ∑ v∈deletedComponentVerts G S c, f v = ∑ v : c.supp, f v.val.val := by
  rw [deletedComponentVerts,sum_image (fun _ _ _ _ he => Subtype.ext he)]
  exact Finset.sum_subtype c.supp.toFinset (fun _ => Set.mem_toFinset) (fun v => f v.val)

theorem component_boundary_degree (G : SimpleGraph V) (S : Finset V)
    (c : (G.induce ((S : Set V)ᶜ)).ConnectedComponent) (v : c.supp) :
    (cutGraph G (deletedComponentVerts G S c)).degree v.val.val=
      (cutGraph G S).degree v.val.val := by
  have hvS : v.val.val∉S := v.val.property
  have hvK := (mem_deletedComponentVerts G S c v.val).mpr v.property
  have he : (cutGraph G (deletedComponentVerts G S c)).neighborSet v.val.val=
      (cutGraph G S).neighborSet v.val.val := by
    ext w
    constructor
    · intro hw
      have hwK : w∉deletedComponentVerts G S c := hw.2.elim And.right (fun h => (h.1 hvK).elim)
      have hwS : w∈S := by
        by_contra hn
        let y : ((S : Set V)ᶜ : Set V) := ⟨w,hn⟩
        have hy : y∈c.supp := c.mem_supp_of_adj_mem_supp v.property hw.1
        exact hwK ((mem_deletedComponentVerts G S c y).mpr hy)
      exact ⟨hw.1,Or.inr ⟨hvS,hwS⟩⟩
    · intro hw
      have hwS : w∈S := hw.2.elim (fun h => (hvS h.1).elim) And.right
      have hwK : w∉deletedComponentVerts G S c := fun h =>
        (mem_compl.mp (deletedComponentVerts_subset G S c h)) hwS
      exact ⟨hw.1,Or.inl ⟨hvK,hwK⟩⟩
  simpa only [← ncard_neighborSet,he]

set_option maxHeartbeats 1000000 in
theorem sum_component_boundaries (G : SimpleGraph V) (S : Finset V) :
    (∑ c : (G.induce ((S : Set V)ᶜ)).ConnectedComponent,
      cutSize G (deletedComponentVerts G S c))=cutSize G S := by
  have he : ∀ c : (G.induce ((S : Set V)ᶜ)).ConnectedComponent,
      cutSize G (deletedComponentVerts G S c)=∑ v : c.supp, (cutGraph G S).degree v.val.val := by
    intro c
    rw [cutSize_eq_sum,sum_deletedComponentVerts]
    exact sum_congr rfl (fun v _ => component_boundary_degree G S c v)
  simp_rw [he]
  have hsum := (Fintype.sum_sigma (fun x : Σ c : (G.induce ((S : Set V)ᶜ)).ConnectedComponent, c.supp =>
    (cutGraph G S).degree x.2.val.val)).symm
  rw [hsum]
  let e : (Σ c : (G.induce ((S : Set V)ᶜ)).ConnectedComponent, c.supp) ≃
      ((S : Set V)ᶜ : Set V) := {
    toFun x := x.2.val
    invFun v := ⟨(G.induce ((S : Set V)ᶜ)).connectedComponentMk v,⟨v,rfl⟩⟩
    left_inv := by
      rintro ⟨c,v,hv⟩
      change (G.induce ((S : Set V)ᶜ)).connectedComponentMk v=c at hv
      cases hv
      rfl
    right_inv _ := rfl }
  have hcomp : cutGraph G Sᶜ=cutGraph G S := by
    simp only [cutGraph,coe_compl,compl_compl]
    exact SimpleGraph.between_comm
  calc
    _ = ∑ v : ((S : Set V)ᶜ : Set V), (cutGraph G S).degree v.val :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = ∑ v∈Sᶜ, (cutGraph G S).degree v :=
      (Finset.sum_subtype (p := fun v : V => v∉S) Sᶜ (fun v => mem_compl) (fun v => (cutGraph G S).degree v)).symm
    _ = cutSize G Sᶜ := by rw [cutSize_eq_sum,hcomp]
    _ = cutSize G S := cutSize_compl G S

theorem cutSize_le_degree_cap (G : SimpleGraph V) (S : Finset V) {D : ℕ}
    (hdeg : ∀ v, G.degree v ≤ D) : cutSize G S ≤ D*S.card := by
  rw [cutSize_eq_sum]
  calc
    _ ≤ ∑ v∈S, D := sum_le_sum (fun v _ =>
      (degree_le_of_le (show cutGraph G S ≤ G from fun _ _ h => h.1)).trans (hdeg v))
    _ = _ := by simp [mul_comm]

theorem deleted_components_bound (G : SimpleGraph V) {d D : ℕ} (hd : 0<d)
    (hratio : 2*D ≤ 3*d) (hdeg : ∀ v, G.degree v ≤ D)
    (hcut : ∀ S : Finset V, S.Nonempty → S≠univ → d ≤ 2*cutSize G S)
    (S : Finset V) (hS : S.Nonempty) :
    Nat.card (G.induce ((S : Set V)ᶜ)).ConnectedComponent ≤ 3*S.card := by
  have hp : ∀ c : (G.induce ((S : Set V)ᶜ)).ConnectedComponent,
      d ≤ 2*cutSize G (deletedComponentVerts G S c) := by
    intro c
    apply hcut
    · obtain ⟨v,hv⟩ := c.nonempty_supp
      exact ⟨v.val,(mem_deletedComponentVerts G S c v).mpr hv⟩
    · intro he
      obtain ⟨v,hv⟩ := hS
      have hh : v∈deletedComponentVerts G S c := he ▸ mem_univ v
      exact (mem_compl.mp (deletedComponentVerts_subset G S c hh)) hv
  have hs := sum_le_sum (s := (univ : Finset (G.induce ((S : Set V)ᶜ)).ConnectedComponent))
    (fun c _ => hp c)
  simp only [sum_const,card_univ,smul_eq_mul,← mul_sum,sum_component_boundaries] at hs
  have hc := cutSize_le_degree_cap G S hdeg
  have hb : Fintype.card (G.induce ((S : Set V)ᶜ)).ConnectedComponent*d ≤ (3*S.card)*d := by
    nlinarith
  have hh := le_of_mul_le_mul_right hb hd
  simpa only [Nat.card_eq_fintype_card] using hh

theorem deleted_components_set_bound (G : SimpleGraph V) {d D : ℕ} (hd : 0<d)
    (hratio : 2*D ≤ 3*d) (hdeg : ∀ v, G.degree v ≤ D)
    (hcut : ∀ S : Finset V, S.Nonempty → S≠univ → d ≤ 2*cutSize G S)
    (S : Set V) (hS : S.Nonempty) :
    Nat.card (G.induce Sᶜ).ConnectedComponent ≤ 3*S.ncard := by
  have hh := deleted_components_bound G hd hratio hdeg hcut S.toFinset (by simpa using hS)
  have he : (S.toFinset : Set V)=S := Set.coe_toFinset S
  rw [he] at hh
  simpa only [Set.ncard_eq_toFinset_card'] using hh

end
end Cycle13
