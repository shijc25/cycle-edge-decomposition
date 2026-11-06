import Cycle12.Foundations.PortPairing

/-! Exact endpoint accounting for a matching. The endpoint map may identify
ports, so the statement retains loops and parallel output edges. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type} [Fintype I] [DecidableEq I] {H : SimpleGraph I}

theorem sum_matching_endpoints {A : Type} [AddCommMonoid A]
    (M : H.Subgraph) (hM : M.IsMatching) (f : I → A) :
    (∑ e : M.edgeSet, (f e.val.out.1 + f e.val.out.2)) =
      ∑ i : M.verts, f i.val := by
  classical
  calc
    _ = ∑ e : M.edgeSet, ∑ i ∈ univ.filter (fun i : M.verts => hM.toEdge i=e),
        f i.val := by
      apply sum_congr rfl
      intro e _
      have he : M.Adj e.val.out.1 e.val.out.2 := edge_out_adj M.spanningCoe e
      have heq : (⟨s(e.val.out.1,e.val.out.2),he⟩ : M.edgeSet)=e :=
        Subtype.ext e.val.out_eq
      have hf : univ.filter (fun i : M.verts => hM.toEdge i=e) =
          {⟨e.val.out.1,he.fst_mem⟩,⟨e.val.out.2,he.snd_mem⟩} := by
        ext i
        have hh := Set.ext_iff.mp (hM.toEdge_preimage_singleton he) i
        rw [heq] at hh
        simpa using hh
      rw [hf]
      simp [he.ne,Subtype.ext_iff]
    _ = _ := sum_fiberwise univ hM.toEdge (fun i => f i.val)

theorem matching_output_incidence (M : H.Subgraph) (hM : M.IsMatching)
    {V : Type} [DecidableEq V] (o : I → V) (v : V) :
    (∑ e : M.edgeSet, ((if o e.val.out.1=v then 1 else 0) +
      (if o e.val.out.2=v then 1 else 0))) =
      (univ.filter (fun i : M.verts => o i.val=v)).card := by
  rw [sum_matching_endpoints M hM (fun i => if o i=v then (1:ℕ) else 0)]
  simp

end
end Cycle13
