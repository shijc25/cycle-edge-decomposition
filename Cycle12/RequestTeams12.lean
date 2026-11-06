import Cycle12.GroupedDemandData12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I J : Type} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

/-- Combinatorial data for one simultaneous routing call. Capacities
are proved for the actual finite request index, before restricting to cores. -/
structure RequestTeams12 (I V : Type) [Fintype I] [Fintype V] (Q : ℕ) where
  Team : Type
  finite : Fintype Team
  team : I → Team
  hard : I → Finset V
  capacity : ∀ t,Fintype.card {j : I // team j=t} ≤ Q
  hard_capacity : ∀ j,(hard j).card ≤ 2*Q
attribute [instance] RequestTeams12.finite

namespace RequestTeams12
variable {Q : ℕ}

theorem load_le (P : RequestTeams12 I V Q) (t : P.Team) : teamLoad P.team t≤Q := by
  simpa only [teamLoad,Fintype.card_subtype] using P.capacity t

def empty : RequestTeams12 Empty V Q where
  Team := Empty
  finite := inferInstance
  team := Empty.elim
  hard := Empty.elim
  capacity := fun t => t.elim
  hard_capacity := fun j => j.elim

def singleton (hQ : 0<Q) : RequestTeams12 I V Q where
  Team := I
  finite := inferInstance
  team := id
  hard := fun _ => ∅
  capacity := by intro t; simpa using (Nat.succ_le_of_lt hQ)
  hard_capacity := by intro j; simp

def sum (P : RequestTeams12 I V Q) (R : RequestTeams12 J V Q) :
    RequestTeams12 (I ⊕ J) V Q where
  Team := P.Team ⊕ R.Team
  finite := inferInstance
  team := Sum.map P.team R.team
  hard := Sum.elim P.hard R.hard
  capacity := by
    intro t
    cases t with
    | inl t =>
      let f : {j : I⊕J // Sum.map P.team R.team j=Sum.inl t} → {j : I // P.team j=t} := by
        rintro ⟨j,hj⟩
        cases j with
        | inl j => exact ⟨j,Sum.inl.inj hj⟩
        | inr j => cases hj
      convert (Fintype.card_le_of_injective f (by
        rintro ⟨j,hj⟩ ⟨k,hk⟩ he
        cases j <;> cases k
        · exact Subtype.ext (congrArg Sum.inl (congrArg Subtype.val he))
        · cases hk
        · cases hj
        · cases hj)).trans (P.capacity t) using 1
      exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
    | inr t =>
      let f : {j : I⊕J // Sum.map P.team R.team j=Sum.inr t} → {j : J // R.team j=t} := by
        rintro ⟨j,hj⟩
        cases j with
        | inl j => cases hj
        | inr j => exact ⟨j,Sum.inr.inj hj⟩
      convert (Fintype.card_le_of_injective f (by
        rintro ⟨j,hj⟩ ⟨k,hk⟩ he
        cases j <;> cases k
        · cases hj
        · cases hj
        · cases hk
        · exact Subtype.ext (congrArg Sum.inr (congrArg Subtype.val he)))).trans (R.capacity t) using 1
      exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
  hard_capacity := by
    intro j
    cases j with
    | inl j => exact P.hard_capacity j
    | inr j => exact R.hard_capacity j

def sigma {K : Type} [Fintype K] {J : K → Type} [∀ k,Fintype (J k)]
    (P : ∀ k,RequestTeams12 (J k) V Q) : RequestTeams12 (Σ k,J k) V Q where
  Team := Σ k,(P k).Team
  finite := inferInstance
  team := fun j => ⟨j.1,(P j.1).team j.2⟩
  hard := fun j => (P j.1).hard j.2
  capacity := by
    rintro ⟨k,t⟩
    let f : {j : Σ k,J k // (⟨j.1,(P j.1).team j.2⟩ : Σ k,(P k).Team)=⟨k,t⟩} →
        {j : J k // (P k).team j=t} := by
      rintro ⟨⟨l,j⟩,hj⟩
      have hl : l=k := congrArg Sigma.fst hj
      subst l
      exact ⟨j,eq_of_heq (Sigma.mk.inj hj).2⟩
    have hf : Function.Injective f := by
      rintro ⟨⟨l,j⟩,hj⟩ ⟨⟨m,x⟩,hx⟩ he
      have hl : l=k := congrArg Sigma.fst hj
      have hm : m=k := congrArg Sigma.fst hx
      subst l
      subst m
      have hh : j=x := congrArg Subtype.val he
      cases hh
      rfl
    convert (Fintype.card_le_of_injective f hf).trans ((P k).capacity t) using 1
    exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
  hard_capacity := fun j => (P j.1).hard_capacity j.2

def mapVertices {W : Type} [Fintype W] [DecidableEq W]
    (P : RequestTeams12 I V Q) (e : V ↪ W) : RequestTeams12 I W Q where
  Team := P.Team
  finite := P.finite
  team := P.team
  hard := fun j => (P.hard j).map e
  capacity := P.capacity
  hard_capacity := by intro j; simpa only [Finset.card_map] using P.hard_capacity j

theorem restrict_load (P : RequestTeams12 I V Q) (e : J ↪ I) (t : P.Team) :
    teamLoad (P.team ∘ e) t ≤ Q := by
  have h := Fintype.card_le_of_injective
    (fun j : {j : J // P.team (e j)=t} => (⟨e j.val,j.property⟩ : {j : I // P.team j=t}))
    (by intro j k he; exact Subtype.ext (e.injective (congrArg Subtype.val he)))
  simpa only [teamLoad,Fintype.card_subtype,Function.comp_apply] using h.trans (P.capacity t)

def comap (P : RequestTeams12 I V Q) (e : J ↪ I) : RequestTeams12 J V Q where
  Team := P.Team
  finite := P.finite
  team := P.team ∘ e
  hard := P.hard ∘ e
  capacity := by intro t; simpa only [Fintype.card_subtype,teamLoad] using P.restrict_load e t
  hard_capacity := fun j => P.hard_capacity (e j)

/-- Extend a real subfamily by distinct singleton teams for all unused
requests. No load is lost or duplicated in the extension. -/
def extendEquiv (e : I ↪ J) : I⊕↥((Set.range e)ᶜ) ≃ J :=
  (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range e))

theorem extendEquiv_inl (e : I ↪ J) (j : I) : extendEquiv e (Sum.inl j)=e j := rfl

def extend (P : RequestTeams12 I V Q) (e : I ↪ J) (hQ : 0<Q) : RequestTeams12 J V Q :=
  (P.sum (singleton (I:=↥((Set.range e)ᶜ)) hQ)).comap (extendEquiv e).symm.toEmbedding

theorem extend_team (P : RequestTeams12 I V Q) (e : I ↪ J) (hQ : 0<Q) (j : I) :
    (P.extend e hQ).team (e j)=Sum.inl (P.team j) := by
  change (P.sum (singleton (I:=↥((Set.range e)ᶜ)) hQ)).team ((extendEquiv e).symm (e j))=_
  rw [←extendEquiv_inl e j,Equiv.symm_apply_apply]
  rfl

theorem extend_hard (P : RequestTeams12 I V Q) (e : I ↪ J) (hQ : 0<Q) (j : I) :
    (P.extend e hQ).hard (e j)=P.hard j := by
  change (P.sum (singleton (I:=↥((Set.range e)ᶜ)) hQ)).hard ((extendEquiv e).symm (e j))=_
  rw [←extendEquiv_inl e j,Equiv.symm_apply_apply]
  rfl

end RequestTeams12
end
end Cycle12
