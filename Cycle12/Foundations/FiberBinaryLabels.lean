import Cycle12.Foundations.ThreeStarCertificate

namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I R : Type} [Fintype I] [Fintype R] [DecidableEq I] [DecidableEq R]

theorem exists_fiber_binary_labels (g : I → R)
    (hg : ∀ r, (univ.filter (fun i => g i=r)).card ≤ 2) :
    ∃ slot : I → Bool, ∀ i j, g i=g j → slot i=slot j → i=j := by
  have he : ∀ r, Nonempty ({i // g i=r} ↪ Bool) := by
    intro r
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Fintype.card_subtype,Fintype.card_bool] using hg r
  let e (r : R) := Classical.choice (he r)
  have htransport : ∀ (r s : R) (h : r=s) (i j : I) (hi : g i=r) (hj : g j=s),
      e r ⟨i,hi⟩=e s ⟨j,hj⟩ → i=j := by
    intro r s h i j hi hj hc
    subst s
    exact congrArg Subtype.val ((e r).injective hc)
  exact ⟨fun i => e (g i) ⟨i,rfl⟩,fun i j h hc => htransport _ _ h i j rfl rfl hc⟩

end
end Cycle13
