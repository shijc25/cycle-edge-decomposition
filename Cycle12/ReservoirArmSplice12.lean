import Cycle12.ReservoirPathFamily12

namespace Cycle12
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} {G : SimpleGraph V} {x y a b c d : V}

/-- Replace a passage through a virtual hub by a genuine reservoir path.
Both exterior arms may have length zero. -/
def spliceArms (L : G.Walk x a) (R : G.Walk y b) (P : G.Walk c d)
    (hx : G.Adj x c) (hy : G.Adj y d) : G.Walk a b :=
  L.reverse.append (.cons hx (P.append (.cons hy.symm R)))

@[simp] theorem spliceArms_support (L : G.Walk x a) (R : G.Walk y b) (P : G.Walk c d)
    (hx : G.Adj x c) (hy : G.Adj y d) :
    (spliceArms L R P hx hy).support = L.support.reverse ++ P.support ++ R.support := by
  simp [spliceArms,Walk.support_append,Walk.support_cons,List.append_assoc]

@[simp] theorem spliceArms_edges (L : G.Walk x a) (R : G.Walk y b) (P : G.Walk c d)
    (hx : G.Adj x c) (hy : G.Adj y d) :
    (spliceArms L R P hx hy).edgeSet =
      (L.edgeSet ∪ R.edgeSet) ∪ P.edgeSet ∪ {s(x,c),s(y,d)} := by
  simp only [spliceArms,Walk.edgeSet_append,Walk.edgeSet_reverse,Walk.edgeSet_cons]
  ext e
  simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
  rw [Sym2.eq_swap (a := d) (b := y)]
  tauto

theorem spliceArms_isPath (L : G.Walk x a) (R : G.Walk y b) (P : G.Walk c d)
    (hx : G.Adj x c) (hy : G.Adj y d)
    (hL : L.IsPath) (hR : R.IsPath) (hP : P.IsPath)
    (hLR : L.support.Disjoint R.support)
    (hLP : L.support.Disjoint P.support) (hRP : R.support.Disjoint P.support) :
    (spliceArms L R P hx hy).IsPath := by
  apply Walk.IsPath.mk'
  rw [spliceArms_support]
  apply List.nodup_append'.mpr
  refine ⟨List.nodup_append'.mpr ⟨List.nodup_reverse.mpr hL.support_nodup,hP.support_nodup,?_⟩,
    hR.support_nodup,?_⟩
  · intro v hv hp
    exact hLP (List.mem_reverse.mp hv) hp
  · intro v hv hr
    rcases List.mem_append.mp hv with hl | hp
    · exact hLR (List.mem_reverse.mp hl) hr
    · exact hRP hr hp

end
end Cycle12
