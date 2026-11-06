import Cycle12.SixCycleExternalTwoPath

namespace Cycle12
open SimpleGraph

theorem reachable_property_from_good_edge {W : Type} (H : SimpleGraph W) (P : W → Prop)
    (hstep : ∀ a b d, H.Adj a b → H.Adj b d → P a → P b → P d)
    {a b d : W} (hab : H.Adj a b) (ha : P a) (hb : P b) (hbd : H.Reachable b d) : P d := by
  have main : ∀ {u v : W}, (H.Walk u v) → ∀ x, H.Adj x u → P x → P u → P v := by
    intro u v p
    induction p with
    | nil => intro x _ _ hu; exact hu
    | @cons u v w huv p ih =>
      intro x hxu hx hu
      exact ih u huv hu (hstep x u v hxu huv hx hu)
  obtain ⟨p⟩ := hbd
  exact main p a hab ha hb

noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Two adjacent external vertices cannot both have the same unique cycle
neighbor. Otherwise propagation along a path in G-a contradicts robust
connectivity. No outside-component classification is assumed. -/
theorem six_cycle_no_equal_single_attachments (G : SimpleGraph V)
    (hconn : G.Connected) (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    {u x y a : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length=6)
    (hshort : Cycle13.NoCycleAtLeast G 7)
    (ha : a∈c.support) (hx : x∉c.support) (hy : y∉c.support) (hxy : G.Adj x y)
    (hX : ∀ v∈c.support, G.Adj x v ↔ v=a)
    (hY : ∀ v∈c.support, G.Adj y v ↔ v=a) : False := by
  let S : Set V := {a}ᶜ
  let H := G.induce S
  let P : S → Prop := fun v => v.val∉c.support ∧
    ∀ w∈c.support, G.Adj v.val w ↔ w=a
  have hstep : ∀ r s t : S, H.Adj r s → H.Adj s t → P r → P s → P t := by
    intro r s t hrs hst hr hs
    have htout : t.val∉c.support := by
      intro ht
      have hta := (hs.2 t.val ht).mp hst
      exact t.property hta
    by_cases hrt : r=t
    · exact hrt ▸ hr
    · have hrs' : r.val≠s.val := (show G.Adj r.val s.val from hrs).ne
      have hst' : s.val≠t.val := (show G.Adj s.val t.val from hst).ne
      have hrt' : r.val≠t.val := fun he => hrt (Subtype.ext he)
      have hnodes : [r.val,s.val,t.val].Nodup := by
        simp [List.nodup_cons,hrs',hst',hrt']
      obtain ⟨b,hb,hR,hT⟩ := six_cycle_external_two_path_unique_attachment G hconn hrobust
        c hc hlen hshort hr.1 hs.1 htout hnodes hrs hst
      have hba : b=a := (hr.2 b hb).mp ((hR b hb).mpr rfl)
      subst b
      exact ⟨htout,hT⟩
  have hxa : x≠a := fun he => hx (he ▸ ha)
  have hya : y≠a := fun he => hy (he ▸ ha)
  let x' : S := ⟨x,hxa⟩
  let y' : S := ⟨y,hya⟩
  have hother : ∃ b∈c.support, b≠a := by
    have he := c.adj_getVert_succ (i:=0) (by omega)
    by_cases h0 : c.getVert 0=a
    · refine ⟨c.getVert 1,c.getVert_mem_support 1,?_⟩
      simpa only [h0] using he.ne.symm
    · exact ⟨c.getVert 0,c.getVert_mem_support 0,h0⟩
  obtain ⟨b,hb,hba⟩ := hother
  let b' : S := ⟨b,hba⟩
  have hresult := reachable_property_from_good_edge H P hstep
    (a:=x') (b:=y') (d:=b') hxy ⟨hx,hX⟩ ⟨hy,hY⟩ (hrobust a y' b')
  exact hresult.1 hb

end
end Cycle12
