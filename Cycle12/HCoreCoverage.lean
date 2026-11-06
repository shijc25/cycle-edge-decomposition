import Cycle12.TerminalKernels.Batch000
import Cycle12.TemplateApplication

namespace Cycle12
open SimpleGraph Finset

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem h_core_mem_optional {α : Type} [DecidableEq α] (x y : α)
    (p : Prop) [Decidable p] : x∈(if p then ({y}:Finset α) else ∅) ↔ p ∧ x=y := by
  by_cases hp : p <;> simp [hp]

def hCoreEdges00 (e0 e1 e2 e3 e4 : Bool) : Finset (Sym2 (Fin 5)) :=
  {s(0,1),s(0,4),s(1,2),s(2,3),s(3,4)} ∪ (if e0 then {s(0,2)} else ∅) ∪ (if e1 then {s(0,3)} else ∅) ∪ (if e2 then {s(1,3)} else ∅) ∪ (if e3 then {s(1,4)} else ∅) ∪ (if e4 then {s(2,4)} else ∅)

theorem hCoreCost00 (e0 e1 e2 e3 e4 : Bool) :
    ∃ P : Cycle13.CyclePacking (TerminalCert.graph (hCoreEdges00 e0 e1 e2 e3 e4)),
      P.cost ≤ 19*(5-1)+6*(hCoreEdges00 e0 e1 e2 e3 e4).card := by
  cases e0 <;> cases e1 <;> cases e2 <;> cases e3 <;> cases e4
  · have he : hCoreEdges00 false false false false false=TerminalKernels.Batch000.edges0 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges0,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost0
  · have he : hCoreEdges00 false false false false true=TerminalKernels.Batch000.edges16 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges16,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost16
  · have he : hCoreEdges00 false false false true false=TerminalKernels.Batch000.edges8 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges8,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost8
  · have he : hCoreEdges00 false false false true true=TerminalKernels.Batch000.edges24 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges24,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost24
  · have he : hCoreEdges00 false false true false false=TerminalKernels.Batch000.edges4 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges4,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost4
  · have he : hCoreEdges00 false false true false true=TerminalKernels.Batch000.edges20 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges20,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost20
  · have he : hCoreEdges00 false false true true false=TerminalKernels.Batch000.edges12 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges12,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost12
  · have he : hCoreEdges00 false false true true true=TerminalKernels.Batch000.edges28 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges28,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost28
  · have he : hCoreEdges00 false true false false false=TerminalKernels.Batch000.edges2 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges2,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost2
  · have he : hCoreEdges00 false true false false true=TerminalKernels.Batch000.edges18 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges18,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost18
  · have he : hCoreEdges00 false true false true false=TerminalKernels.Batch000.edges10 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges10,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost10
  · have he : hCoreEdges00 false true false true true=TerminalKernels.Batch000.edges26 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges26,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost26
  · have he : hCoreEdges00 false true true false false=TerminalKernels.Batch000.edges6 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges6,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost6
  · have he : hCoreEdges00 false true true false true=TerminalKernels.Batch000.edges22 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges22,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost22
  · have he : hCoreEdges00 false true true true false=TerminalKernels.Batch000.edges14 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges14,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost14
  · have he : hCoreEdges00 false true true true true=TerminalKernels.Batch000.edges30 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges30,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost30
  · have he : hCoreEdges00 true false false false false=TerminalKernels.Batch000.edges1 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges1,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost1
  · have he : hCoreEdges00 true false false false true=TerminalKernels.Batch000.edges17 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges17,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost17
  · have he : hCoreEdges00 true false false true false=TerminalKernels.Batch000.edges9 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges9,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost9
  · have he : hCoreEdges00 true false false true true=TerminalKernels.Batch000.edges25 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges25,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost25
  · have he : hCoreEdges00 true false true false false=TerminalKernels.Batch000.edges5 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges5,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost5
  · have he : hCoreEdges00 true false true false true=TerminalKernels.Batch000.edges21 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges21,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost21
  · have he : hCoreEdges00 true false true true false=TerminalKernels.Batch000.edges13 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges13,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost13
  · have he : hCoreEdges00 true false true true true=TerminalKernels.Batch000.edges29 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges29,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost29
  · have he : hCoreEdges00 true true false false false=TerminalKernels.Batch000.edges3 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges3,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost3
  · have he : hCoreEdges00 true true false false true=TerminalKernels.Batch000.edges19 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges19,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost19
  · have he : hCoreEdges00 true true false true false=TerminalKernels.Batch000.edges11 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges11,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost11
  · have he : hCoreEdges00 true true false true true=TerminalKernels.Batch000.edges27 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges27,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost27
  · have he : hCoreEdges00 true true true false false=TerminalKernels.Batch000.edges7 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges7,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost7
  · have he : hCoreEdges00 true true true false true=TerminalKernels.Batch000.edges23 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges23,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost23
  · have he : hCoreEdges00 true true true true false=TerminalKernels.Batch000.edges15 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges15,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost15
  · have he : hCoreEdges00 true true true true true=TerminalKernels.Batch000.edges31 := by
      ext e; simp [hCoreEdges00,TerminalKernels.Batch000.edges31,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost31

theorem hCoreNoDiag00 (e0 e1 e2 e3 e4 : Bool) :
    ∀ e∈hCoreEdges00 e0 e1 e2 e3 e4, ¬e.IsDiag := by
  intro e he
  simp only [hCoreEdges00,mem_union,mem_insert,mem_singleton,h_core_mem_optional,or_assoc] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide +kernel

def hCoreEdges01 (e0 e1 e2 e3 e4 : Bool) : Finset (Sym2 (Fin 6)) :=
  {s(0,1),s(0,4),s(1,2),s(2,3),s(3,4),s(0,5),s(3,5)} ∪ (if e0 then {s(0,2)} else ∅) ∪ (if e1 then {s(0,3)} else ∅) ∪ (if e2 then {s(1,3)} else ∅) ∪ (if e3 then {s(1,4)} else ∅) ∪ (if e4 then {s(2,4)} else ∅)

theorem hCoreCost01 (e0 e1 e2 e3 e4 : Bool) :
    ∃ P : Cycle13.CyclePacking (TerminalCert.graph (hCoreEdges01 e0 e1 e2 e3 e4)),
      P.cost ≤ 19*(6-1)+6*(hCoreEdges01 e0 e1 e2 e3 e4).card := by
  cases e0 <;> cases e1 <;> cases e2 <;> cases e3 <;> cases e4
  · have he : hCoreEdges01 false false false false false=TerminalKernels.Batch000.edges32 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges32,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost32
  · have he : hCoreEdges01 false false false false true=TerminalKernels.Batch000.edges48 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges48,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost48
  · have he : hCoreEdges01 false false false true false=TerminalKernels.Batch000.edges40 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges40,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost40
  · have he : hCoreEdges01 false false false true true=TerminalKernels.Batch000.edges56 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges56,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost56
  · have he : hCoreEdges01 false false true false false=TerminalKernels.Batch000.edges36 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges36,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost36
  · have he : hCoreEdges01 false false true false true=TerminalKernels.Batch000.edges52 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges52,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost52
  · have he : hCoreEdges01 false false true true false=TerminalKernels.Batch000.edges44 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges44,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost44
  · have he : hCoreEdges01 false false true true true=TerminalKernels.Batch000.edges60 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges60,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost60
  · have he : hCoreEdges01 false true false false false=TerminalKernels.Batch000.edges34 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges34,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost34
  · have he : hCoreEdges01 false true false false true=TerminalKernels.Batch000.edges50 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges50,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost50
  · have he : hCoreEdges01 false true false true false=TerminalKernels.Batch000.edges42 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges42,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost42
  · have he : hCoreEdges01 false true false true true=TerminalKernels.Batch000.edges58 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges58,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost58
  · have he : hCoreEdges01 false true true false false=TerminalKernels.Batch000.edges38 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges38,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost38
  · have he : hCoreEdges01 false true true false true=TerminalKernels.Batch000.edges54 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges54,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost54
  · have he : hCoreEdges01 false true true true false=TerminalKernels.Batch000.edges46 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges46,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost46
  · have he : hCoreEdges01 false true true true true=TerminalKernels.Batch000.edges62 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges62,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost62
  · have he : hCoreEdges01 true false false false false=TerminalKernels.Batch000.edges33 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges33,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost33
  · have he : hCoreEdges01 true false false false true=TerminalKernels.Batch000.edges49 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges49,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost49
  · have he : hCoreEdges01 true false false true false=TerminalKernels.Batch000.edges41 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges41,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost41
  · have he : hCoreEdges01 true false false true true=TerminalKernels.Batch000.edges57 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges57,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost57
  · have he : hCoreEdges01 true false true false false=TerminalKernels.Batch000.edges37 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges37,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost37
  · have he : hCoreEdges01 true false true false true=TerminalKernels.Batch000.edges53 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges53,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost53
  · have he : hCoreEdges01 true false true true false=TerminalKernels.Batch000.edges45 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges45,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost45
  · have he : hCoreEdges01 true false true true true=TerminalKernels.Batch000.edges61 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges61,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost61
  · have he : hCoreEdges01 true true false false false=TerminalKernels.Batch000.edges35 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges35,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost35
  · have he : hCoreEdges01 true true false false true=TerminalKernels.Batch000.edges51 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges51,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost51
  · have he : hCoreEdges01 true true false true false=TerminalKernels.Batch000.edges43 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges43,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost43
  · have he : hCoreEdges01 true true false true true=TerminalKernels.Batch000.edges59 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges59,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost59
  · have he : hCoreEdges01 true true true false false=TerminalKernels.Batch000.edges39 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges39,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost39
  · have he : hCoreEdges01 true true true false true=TerminalKernels.Batch000.edges55 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges55,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost55
  · have he : hCoreEdges01 true true true true false=TerminalKernels.Batch000.edges47 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges47,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost47
  · have he : hCoreEdges01 true true true true true=TerminalKernels.Batch000.edges63 := by
      ext e; simp [hCoreEdges01,TerminalKernels.Batch000.edges63,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost63

theorem hCoreNoDiag01 (e0 e1 e2 e3 e4 : Bool) :
    ∀ e∈hCoreEdges01 e0 e1 e2 e3 e4, ¬e.IsDiag := by
  intro e he
  simp only [hCoreEdges01,mem_union,mem_insert,mem_singleton,h_core_mem_optional,or_assoc] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide +kernel

def hCoreEdges10 (e0 e1 e2 e3 e4 : Bool) : Finset (Sym2 (Fin 6)) :=
  {s(0,1),s(0,4),s(1,2),s(2,3),s(3,4),s(0,5),s(2,5)} ∪ (if e0 then {s(0,2)} else ∅) ∪ (if e1 then {s(0,3)} else ∅) ∪ (if e2 then {s(1,3)} else ∅) ∪ (if e3 then {s(1,4)} else ∅) ∪ (if e4 then {s(2,4)} else ∅)

theorem hCoreCost10 (e0 e1 e2 e3 e4 : Bool) :
    ∃ P : Cycle13.CyclePacking (TerminalCert.graph (hCoreEdges10 e0 e1 e2 e3 e4)),
      P.cost ≤ 19*(6-1)+6*(hCoreEdges10 e0 e1 e2 e3 e4).card := by
  cases e0 <;> cases e1 <;> cases e2 <;> cases e3 <;> cases e4
  · have he : hCoreEdges10 false false false false false=TerminalKernels.Batch000.edges64 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges64,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost64
  · have he : hCoreEdges10 false false false false true=TerminalKernels.Batch000.edges80 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges80,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost80
  · have he : hCoreEdges10 false false false true false=TerminalKernels.Batch000.edges72 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges72,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost72
  · have he : hCoreEdges10 false false false true true=TerminalKernels.Batch000.edges88 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges88,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost88
  · have he : hCoreEdges10 false false true false false=TerminalKernels.Batch000.edges68 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges68,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost68
  · have he : hCoreEdges10 false false true false true=TerminalKernels.Batch000.edges84 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges84,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost84
  · have he : hCoreEdges10 false false true true false=TerminalKernels.Batch000.edges76 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges76,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost76
  · have he : hCoreEdges10 false false true true true=TerminalKernels.Batch000.edges92 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges92,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost92
  · have he : hCoreEdges10 false true false false false=TerminalKernels.Batch000.edges66 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges66,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost66
  · have he : hCoreEdges10 false true false false true=TerminalKernels.Batch000.edges82 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges82,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost82
  · have he : hCoreEdges10 false true false true false=TerminalKernels.Batch000.edges74 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges74,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost74
  · have he : hCoreEdges10 false true false true true=TerminalKernels.Batch000.edges90 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges90,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost90
  · have he : hCoreEdges10 false true true false false=TerminalKernels.Batch000.edges70 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges70,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost70
  · have he : hCoreEdges10 false true true false true=TerminalKernels.Batch000.edges86 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges86,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost86
  · have he : hCoreEdges10 false true true true false=TerminalKernels.Batch000.edges78 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges78,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost78
  · have he : hCoreEdges10 false true true true true=TerminalKernels.Batch000.edges94 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges94,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost94
  · have he : hCoreEdges10 true false false false false=TerminalKernels.Batch000.edges65 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges65,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost65
  · have he : hCoreEdges10 true false false false true=TerminalKernels.Batch000.edges81 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges81,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost81
  · have he : hCoreEdges10 true false false true false=TerminalKernels.Batch000.edges73 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges73,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost73
  · have he : hCoreEdges10 true false false true true=TerminalKernels.Batch000.edges89 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges89,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost89
  · have he : hCoreEdges10 true false true false false=TerminalKernels.Batch000.edges69 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges69,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost69
  · have he : hCoreEdges10 true false true false true=TerminalKernels.Batch000.edges85 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges85,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost85
  · have he : hCoreEdges10 true false true true false=TerminalKernels.Batch000.edges77 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges77,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost77
  · have he : hCoreEdges10 true false true true true=TerminalKernels.Batch000.edges93 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges93,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost93
  · have he : hCoreEdges10 true true false false false=TerminalKernels.Batch000.edges67 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges67,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost67
  · have he : hCoreEdges10 true true false false true=TerminalKernels.Batch000.edges83 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges83,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost83
  · have he : hCoreEdges10 true true false true false=TerminalKernels.Batch000.edges75 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges75,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost75
  · have he : hCoreEdges10 true true false true true=TerminalKernels.Batch000.edges91 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges91,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost91
  · have he : hCoreEdges10 true true true false false=TerminalKernels.Batch000.edges71 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges71,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost71
  · have he : hCoreEdges10 true true true false true=TerminalKernels.Batch000.edges87 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges87,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost87
  · have he : hCoreEdges10 true true true true false=TerminalKernels.Batch000.edges79 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges79,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost79
  · have he : hCoreEdges10 true true true true true=TerminalKernels.Batch000.edges95 := by
      ext e; simp [hCoreEdges10,TerminalKernels.Batch000.edges95,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost95

theorem hCoreNoDiag10 (e0 e1 e2 e3 e4 : Bool) :
    ∀ e∈hCoreEdges10 e0 e1 e2 e3 e4, ¬e.IsDiag := by
  intro e he
  simp only [hCoreEdges10,mem_union,mem_insert,mem_singleton,h_core_mem_optional,or_assoc] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide +kernel

def hCoreEdges11 (e0 e1 e2 e3 e4 : Bool) : Finset (Sym2 (Fin 7)) :=
  {s(0,1),s(0,4),s(1,2),s(2,3),s(3,4),s(0,5),s(2,5),s(0,6),s(3,6)} ∪ (if e0 then {s(0,2)} else ∅) ∪ (if e1 then {s(0,3)} else ∅) ∪ (if e2 then {s(1,3)} else ∅) ∪ (if e3 then {s(1,4)} else ∅) ∪ (if e4 then {s(2,4)} else ∅)

theorem hCoreCost11 (e0 e1 e2 e3 e4 : Bool) :
    ∃ P : Cycle13.CyclePacking (TerminalCert.graph (hCoreEdges11 e0 e1 e2 e3 e4)),
      P.cost ≤ 19*(7-1)+6*(hCoreEdges11 e0 e1 e2 e3 e4).card := by
  cases e0 <;> cases e1 <;> cases e2 <;> cases e3 <;> cases e4
  · have he : hCoreEdges11 false false false false false=TerminalKernels.Batch000.edges96 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges96,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost96
  · have he : hCoreEdges11 false false false false true=TerminalKernels.Batch000.edges112 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges112,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost112
  · have he : hCoreEdges11 false false false true false=TerminalKernels.Batch000.edges104 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges104,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost104
  · have he : hCoreEdges11 false false false true true=TerminalKernels.Batch000.edges120 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges120,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost120
  · have he : hCoreEdges11 false false true false false=TerminalKernels.Batch000.edges100 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges100,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost100
  · have he : hCoreEdges11 false false true false true=TerminalKernels.Batch000.edges116 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges116,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost116
  · have he : hCoreEdges11 false false true true false=TerminalKernels.Batch000.edges108 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges108,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost108
  · have he : hCoreEdges11 false false true true true=TerminalKernels.Batch000.edges124 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges124,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost124
  · have he : hCoreEdges11 false true false false false=TerminalKernels.Batch000.edges98 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges98,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost98
  · have he : hCoreEdges11 false true false false true=TerminalKernels.Batch000.edges114 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges114,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost114
  · have he : hCoreEdges11 false true false true false=TerminalKernels.Batch000.edges106 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges106,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost106
  · have he : hCoreEdges11 false true false true true=TerminalKernels.Batch000.edges122 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges122,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost122
  · have he : hCoreEdges11 false true true false false=TerminalKernels.Batch000.edges102 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges102,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost102
  · have he : hCoreEdges11 false true true false true=TerminalKernels.Batch000.edges118 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges118,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost118
  · have he : hCoreEdges11 false true true true false=TerminalKernels.Batch000.edges110 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges110,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost110
  · have he : hCoreEdges11 false true true true true=TerminalKernels.Batch000.edges126 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges126,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost126
  · have he : hCoreEdges11 true false false false false=TerminalKernels.Batch000.edges97 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges97,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost97
  · have he : hCoreEdges11 true false false false true=TerminalKernels.Batch000.edges113 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges113,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost113
  · have he : hCoreEdges11 true false false true false=TerminalKernels.Batch000.edges105 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges105,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost105
  · have he : hCoreEdges11 true false false true true=TerminalKernels.Batch000.edges121 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges121,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost121
  · have he : hCoreEdges11 true false true false false=TerminalKernels.Batch000.edges101 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges101,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost101
  · have he : hCoreEdges11 true false true false true=TerminalKernels.Batch000.edges117 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges117,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost117
  · have he : hCoreEdges11 true false true true false=TerminalKernels.Batch000.edges109 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges109,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost109
  · have he : hCoreEdges11 true false true true true=TerminalKernels.Batch000.edges125 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges125,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost125
  · have he : hCoreEdges11 true true false false false=TerminalKernels.Batch000.edges99 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges99,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost99
  · have he : hCoreEdges11 true true false false true=TerminalKernels.Batch000.edges115 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges115,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost115
  · have he : hCoreEdges11 true true false true false=TerminalKernels.Batch000.edges107 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges107,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost107
  · have he : hCoreEdges11 true true false true true=TerminalKernels.Batch000.edges123 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges123,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost123
  · have he : hCoreEdges11 true true true false false=TerminalKernels.Batch000.edges103 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges103,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost103
  · have he : hCoreEdges11 true true true false true=TerminalKernels.Batch000.edges119 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges119,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost119
  · have he : hCoreEdges11 true true true true false=TerminalKernels.Batch000.edges111 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges111,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost111
  · have he : hCoreEdges11 true true true true true=TerminalKernels.Batch000.edges127 := by
      ext e; simp [hCoreEdges11,TerminalKernels.Batch000.edges127,or_assoc,or_left_comm,or_comm]
    rw [he]
    exact TerminalKernels.Batch000.cost127

theorem hCoreNoDiag11 (e0 e1 e2 e3 e4 : Bool) :
    ∀ e∈hCoreEdges11 e0 e1 e2 e3 e4, ¬e.IsDiag := by
  intro e he
  simp only [hCoreEdges11,mem_union,mem_insert,mem_singleton,h_core_mem_optional,or_assoc] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide +kernel

noncomputable section
attribute [local instance] Classical.propDecidable

theorem terminal_h_core00 (G : SimpleGraph (Fin 5))
    (h01 : G.Adj 0 1) (h12 : G.Adj 1 2) (h23 : G.Adj 2 3)
    (h34 : G.Adj 3 4) (h40 : G.Adj 4 0)
    : ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(5-1)+6*G.edgeSet.ncard := by
  let E := hCoreEdges00 (decide (G.Adj 0 2)) (decide (G.Adj 0 3)) (decide (G.Adj 1 3)) (decide (G.Adj 1 4)) (decide (G.Adj 2 4))
  have hmodel : TerminalCert.graph E=G := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E,hCoreEdges00,TerminalCert.graph,SimpleGraph.fromEdgeSet_adj,h_core_mem_optional,
        Sym2.eq_iff,h01,h01.symm,h12,h12.symm,h23,h23.symm,h34,h34.symm,h40,h40.symm,G.adj_comm]
  have hdiag : ∀ e∈E, ¬e.IsDiag := hCoreNoDiag00 _ _ _ _ _
  have hcard : E.card=G.edgeSet.ncard := by
    rw [← hmodel,TerminalCert.edgeSet_graph E hdiag,Set.ncard_coe_finset]
  obtain ⟨P,hP⟩ := hCoreCost00 (decide (G.Adj 0 2)) (decide (G.Adj 0 3)) (decide (G.Adj 1 3)) (decide (G.Adj 1 4)) (decide (G.Adj 2 4))
  change ∃ P : Cycle13.CyclePacking G, P.cost ≤ _
  have hh : ∃ P : Cycle13.CyclePacking (TerminalCert.graph E),
      P.cost ≤ 19*(5-1)+6*E.card := ⟨P,hP⟩
  rw [hmodel,hcard] at hh
  exact hh

theorem terminal_h_core01 (G : SimpleGraph (Fin 6))
    (h01 : G.Adj 0 1) (h12 : G.Adj 1 2) (h23 : G.Adj 2 3)
    (h34 : G.Adj 3 4) (h40 : G.Adj 4 0)
    (h5 : ∀ i, G.Adj 5 i ↔ i=0 ∨ i=3)
    : ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(6-1)+6*G.edgeSet.ncard := by
  let E := hCoreEdges01 (decide (G.Adj 0 2)) (decide (G.Adj 0 3)) (decide (G.Adj 1 3)) (decide (G.Adj 1 4)) (decide (G.Adj 2 4))
  have h5r : ∀ i, G.Adj i 5 ↔ i=0 ∨ i=3 := by
    intro i; rw [G.adj_comm]; exact h5 i
  have hmodel : TerminalCert.graph E=G := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E,hCoreEdges01,TerminalCert.graph,SimpleGraph.fromEdgeSet_adj,h_core_mem_optional,
        Sym2.eq_iff,h01,h01.symm,h12,h12.symm,h23,h23.symm,h34,h34.symm,h40,h40.symm,h5,h5r,G.adj_comm]
  have hdiag : ∀ e∈E, ¬e.IsDiag := hCoreNoDiag01 _ _ _ _ _
  have hcard : E.card=G.edgeSet.ncard := by
    rw [← hmodel,TerminalCert.edgeSet_graph E hdiag,Set.ncard_coe_finset]
  obtain ⟨P,hP⟩ := hCoreCost01 (decide (G.Adj 0 2)) (decide (G.Adj 0 3)) (decide (G.Adj 1 3)) (decide (G.Adj 1 4)) (decide (G.Adj 2 4))
  change ∃ P : Cycle13.CyclePacking G, P.cost ≤ _
  have hh : ∃ P : Cycle13.CyclePacking (TerminalCert.graph E),
      P.cost ≤ 19*(6-1)+6*E.card := ⟨P,hP⟩
  rw [hmodel,hcard] at hh
  exact hh

theorem terminal_h_core10 (G : SimpleGraph (Fin 6))
    (h01 : G.Adj 0 1) (h12 : G.Adj 1 2) (h23 : G.Adj 2 3)
    (h34 : G.Adj 3 4) (h40 : G.Adj 4 0)
    (h5 : ∀ i, G.Adj 5 i ↔ i=0 ∨ i=2)
    : ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(6-1)+6*G.edgeSet.ncard := by
  let E := hCoreEdges10 (decide (G.Adj 0 2)) (decide (G.Adj 0 3)) (decide (G.Adj 1 3)) (decide (G.Adj 1 4)) (decide (G.Adj 2 4))
  have h5r : ∀ i, G.Adj i 5 ↔ i=0 ∨ i=2 := by
    intro i; rw [G.adj_comm]; exact h5 i
  have hmodel : TerminalCert.graph E=G := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E,hCoreEdges10,TerminalCert.graph,SimpleGraph.fromEdgeSet_adj,h_core_mem_optional,
        Sym2.eq_iff,h01,h01.symm,h12,h12.symm,h23,h23.symm,h34,h34.symm,h40,h40.symm,h5,h5r,G.adj_comm]
  have hdiag : ∀ e∈E, ¬e.IsDiag := hCoreNoDiag10 _ _ _ _ _
  have hcard : E.card=G.edgeSet.ncard := by
    rw [← hmodel,TerminalCert.edgeSet_graph E hdiag,Set.ncard_coe_finset]
  obtain ⟨P,hP⟩ := hCoreCost10 (decide (G.Adj 0 2)) (decide (G.Adj 0 3)) (decide (G.Adj 1 3)) (decide (G.Adj 1 4)) (decide (G.Adj 2 4))
  change ∃ P : Cycle13.CyclePacking G, P.cost ≤ _
  have hh : ∃ P : Cycle13.CyclePacking (TerminalCert.graph E),
      P.cost ≤ 19*(6-1)+6*E.card := ⟨P,hP⟩
  rw [hmodel,hcard] at hh
  exact hh

theorem terminal_h_core11 (G : SimpleGraph (Fin 7))
    (h01 : G.Adj 0 1) (h12 : G.Adj 1 2) (h23 : G.Adj 2 3)
    (h34 : G.Adj 3 4) (h40 : G.Adj 4 0)
    (h5 : ∀ i, G.Adj 5 i ↔ i=0 ∨ i=2)
    (h6 : ∀ i, G.Adj 6 i ↔ i=0 ∨ i=3)
    : ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(7-1)+6*G.edgeSet.ncard := by
  let E := hCoreEdges11 (decide (G.Adj 0 2)) (decide (G.Adj 0 3)) (decide (G.Adj 1 3)) (decide (G.Adj 1 4)) (decide (G.Adj 2 4))
  have h5r : ∀ i, G.Adj i 5 ↔ i=0 ∨ i=2 := by
    intro i; rw [G.adj_comm]; exact h5 i
  have h6r : ∀ i, G.Adj i 6 ↔ i=0 ∨ i=3 := by
    intro i; rw [G.adj_comm]; exact h6 i
  have hmodel : TerminalCert.graph E=G := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E,hCoreEdges11,TerminalCert.graph,SimpleGraph.fromEdgeSet_adj,h_core_mem_optional,
        Sym2.eq_iff,h01,h01.symm,h12,h12.symm,h23,h23.symm,h34,h34.symm,h40,h40.symm,h5,h5r,h6,h6r,G.adj_comm]
  have hdiag : ∀ e∈E, ¬e.IsDiag := hCoreNoDiag11 _ _ _ _ _
  have hcard : E.card=G.edgeSet.ncard := by
    rw [← hmodel,TerminalCert.edgeSet_graph E hdiag,Set.ncard_coe_finset]
  obtain ⟨P,hP⟩ := hCoreCost11 (decide (G.Adj 0 2)) (decide (G.Adj 0 3)) (decide (G.Adj 1 3)) (decide (G.Adj 1 4)) (decide (G.Adj 2 4))
  change ∃ P : Cycle13.CyclePacking G, P.cost ≤ _
  have hh : ∃ P : Cycle13.CyclePacking (TerminalCert.graph E),
      P.cost ≤ 19*(7-1)+6*E.card := ⟨P,hP⟩
  rw [hmodel,hcard] at hh
  exact hh

end
end Cycle12
