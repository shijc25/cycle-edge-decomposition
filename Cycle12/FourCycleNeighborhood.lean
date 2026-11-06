import Cycle12.CycleObstructions

namespace Cycle12
open SimpleGraph
variable {V : Type} {G : SimpleGraph V} {a b c d x y : V}

/-- An external vertex cannot meet two consecutive vertices of a four-cycle
when every cycle has length at most four. -/
theorem four_cycle_no_consecutive_neighbors
    (hshort : Cycle13.NoCycleAtLeast G 5) (hn : [a,b,c,d].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hx : x∉[a,b,c,d]) (hxa : G.Adj x a) (hxb : G.Adj x b) : False := by
  apply no_five_cycle hshort (a:=x) (b:=a) (c:=d) (d:=c) (e:=b)
    _ hxa hda.symm hcd.symm hbc.symm hxb.symm
  simp_all only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true,ne_comm] <;> tauto

/-- Two distinct neighbors on a four-cycle must be one of its opposite pairs;
the two other cycle vertices are not neighbors. -/
theorem four_cycle_external_pair
    (hshort : Cycle13.NoCycleAtLeast G 5) (hn : [a,b,c,d].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hx : x∉[a,b,c,d])
    (hnear : ∃ v∈[a,b,c,d], ∃ w∈[a,b,c,d], v≠w ∧ G.Adj x v ∧ G.Adj x w) :
    (G.Adj x a ∧ G.Adj x c ∧ ¬G.Adj x b ∧ ¬G.Adj x d) ∨
    (G.Adj x b ∧ G.Adj x d ∧ ¬G.Adj x a ∧ ¬G.Adj x c) := by
  have h₁ : G.Adj x a → G.Adj x b → False :=
    four_cycle_no_consecutive_neighbors hshort hn hab hbc hcd hda hx
  have h₂ : G.Adj x b → G.Adj x c → False := by
    apply four_cycle_no_consecutive_neighbors hshort (a:=b) (b:=c) (c:=d) (d:=a)
      _ hbc hcd hda hab
    all_goals
      simp_all only [List.nodup_cons,List.mem_cons,List.not_mem_nil,
        List.nodup_nil,not_or,not_false_eq_true,and_true,or_false,ne_comm] <;> tauto
  have h₃ : G.Adj x c → G.Adj x d → False := by
    apply four_cycle_no_consecutive_neighbors hshort (a:=c) (b:=d) (c:=a) (d:=b)
      _ hcd hda hab hbc
    all_goals
      simp_all only [List.nodup_cons,List.mem_cons,List.not_mem_nil,
        List.nodup_nil,not_or,not_false_eq_true,and_true,or_false,ne_comm] <;> tauto
  have h₄ : G.Adj x d → G.Adj x a → False := by
    apply four_cycle_no_consecutive_neighbors hshort (a:=d) (b:=a) (c:=b) (d:=c)
      _ hda hab hbc hcd
    all_goals
      simp_all only [List.nodup_cons,List.mem_cons,List.not_mem_nil,
        List.nodup_nil,not_or,not_false_eq_true,and_true,or_false,ne_comm] <;> tauto
  obtain ⟨v,hv,w,hw,hvw,hxv,hxw⟩ := hnear
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv hw
  rcases hv with rfl | rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl | rfl <;> aesop

/-- The two opposite attachment types cannot both occur outside a four-cycle. -/
theorem four_cycle_no_crossing_spokes
    (hshort : Cycle13.NoCycleAtLeast G 5) (hn : [a,b,c,d].Nodup)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hx : x∉[a,b,c,d]) (hy : y∉[a,b,c,d]) (hxy : x≠y)
    (hxa : G.Adj x a) (hxc : G.Adj x c)
    (hyb : G.Adj y b) (hyd : G.Adj y d) : False := by
  apply no_six_cycle hshort (a:=x) (b:=a) (c:=b) (d:=y) (e:=d) (f:=c)
    _ hxa hab hyb.symm hyd hcd.symm hxc.symm
  simp_all only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true,ne_comm] <;> tauto

/-- Spokes on the same pair cannot be joined by an edge. -/
theorem four_cycle_spokes_not_adjacent
    (hshort : Cycle13.NoCycleAtLeast G 5) (hn : [a,b,c,d].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c)
    (hx : x∉[a,b,c,d]) (hy : y∉[a,b,c,d])
    (hxc : G.Adj x c) (hya : G.Adj y a) : ¬G.Adj x y := by
  intro hxy
  have hne := hxy.ne
  apply no_five_cycle hshort (a:=x) (b:=y) (c:=a) (d:=b) (e:=c)
    _ hxy hya hab hbc hxc.symm
  simp_all only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true,ne_comm] <;> tauto

/-- With an external spoke on a,c, the other diagonal b,d is forbidden. -/
theorem four_cycle_spoke_forbids_diagonal
    (hshort : Cycle13.NoCycleAtLeast G 5) (hn : [a,b,c,d].Nodup)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hx : x∉[a,b,c,d]) (hxa : G.Adj x a) (hxc : G.Adj x c) :
    ¬G.Adj b d := by
  intro hbd
  apply no_five_cycle hshort (a:=x) (b:=a) (c:=b) (d:=d) (e:=c)
    _ hxa hab hbd hcd.symm hxc.symm
  simp_all only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true,ne_comm] <;> tauto

end Cycle12
