import Cycle12.TerminalCertificate

namespace Cycle12.TerminalTemplates
open Cycle12.TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- degree-two twins; 2 removed vertices in the template, or n-1 for a base block. -/
def edges0 : Finset (Sym2 (Fin 4)) := {s(0,2),s(0,3),s(1,2),s(1,3)}
def words0 : Fin 1 → CycleWord (Fin 4) := ![⟨0,[2,1,3]⟩]
theorem valid0 : Valid edges0 words0 := by decide +kernel
theorem cost0 : ∃ P : Cycle13.CyclePacking (graph edges0),
    P.cost ≤ 19*2+6*edges0.card :=
  sound edges0 words0 valid0 (by decide +kernel)

/-- degree-three triples; 3 removed vertices in the template, or n-1 for a base block. -/
def edges1 : Finset (Sym2 (Fin 6)) := {s(0,3),s(0,4),s(0,5),s(1,3),s(1,4),s(1,5),s(2,3),s(2,4),s(2,5)}
def words1 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[3,1,4,2,5]⟩]
theorem valid1 : Valid edges1 words1 := by decide +kernel
theorem cost1 : ∃ P : Cycle13.CyclePacking (graph edges1),
    P.cost ≤ 19*3+6*edges1.card :=
  sound edges1 words1 valid1 (by decide +kernel)

/-- two diamond modules; 4 removed vertices in the template, or n-1 for a base block. -/
def edges2 : Finset (Sym2 (Fin 6)) := {s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(1,5),s(2,3),s(4,5)}
def words2 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[2,3,1,4,5]⟩]
theorem valid2 : Valid edges2 words2 := by decide +kernel
theorem cost2 : ∃ P : Cycle13.CyclePacking (graph edges2),
    P.cost ≤ 19*4+6*edges2.card :=
  sound edges2 words2 valid2 (by decide +kernel)

/-- two three-edge paths; 4 removed vertices in the template, or n-1 for a base block. -/
def edges3 : Finset (Sym2 (Fin 6)) := {s(0,2),s(0,4),s(1,3),s(1,5),s(2,3),s(4,5)}
def words3 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[2,3,1,5,4]⟩]
theorem valid3 : Valid edges3 words3 := by decide +kernel
theorem cost3 : ∃ P : Cycle13.CyclePacking (graph edges3),
    P.cost ≤ 19*4+6*edges3.card :=
  sound edges3 words3 valid3 (by decide +kernel)

/-- double star q=2 optional=0; 3 removed vertices in the template, or n-1 for a base block. -/
def edges4 : Finset (Sym2 (Fin 5)) := {s(0,2),s(1,3),s(1,4),s(2,3),s(2,4)}
def words4 : Fin 1 → CycleWord (Fin 5) := ![⟨1,[3,2,4]⟩]
theorem valid4 : Valid edges4 words4 := by decide +kernel
theorem cost4 : ∃ P : Cycle13.CyclePacking (graph edges4),
    P.cost ≤ 19*3+6*edges4.card :=
  sound edges4 words4 valid4 (by decide +kernel)

/-- double star q=2 optional=1; 3 removed vertices in the template, or n-1 for a base block. -/
def edges5 : Finset (Sym2 (Fin 5)) := {s(0,2),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4)}
def words5 : Fin 1 → CycleWord (Fin 5) := ![⟨1,[3,2,4]⟩]
theorem valid5 : Valid edges5 words5 := by decide +kernel
theorem cost5 : ∃ P : Cycle13.CyclePacking (graph edges5),
    P.cost ≤ 19*3+6*edges5.card :=
  sound edges5 words5 valid5 (by decide +kernel)

/-- three triangle-leg modules; 6 removed vertices in the template, or n-1 for a base block. -/
def edges6 : Finset (Sym2 (Fin 8)) := {s(0,2),s(0,4),s(0,6),s(1,2),s(1,3),s(1,4),s(1,5),s(1,6),s(1,7),s(2,3),s(4,5),s(6,7)}
def words6 : Fin 2 → CycleWord (Fin 8) := ![⟨0,[2,3,1,5,4]⟩,⟨1,[6,7]⟩]
theorem valid6 : Valid edges6 words6 := by decide +kernel
theorem cost6 : ∃ P : Cycle13.CyclePacking (graph edges6),
    P.cost ≤ 19*6+6*edges6.card :=
  sound edges6 words6 valid6 (by decide +kernel)

/-- base block 0; 1 removed vertices in the template, or n-1 for a base block. -/
def edges7 : Finset (Sym2 (Fin 2)) := {s(0,1)}
def words7 : Fin 0 → CycleWord (Fin 2) := ![]
theorem valid7 : Valid edges7 words7 := by decide +kernel
theorem cost7 : ∃ P : Cycle13.CyclePacking (graph edges7),
    P.cost ≤ 19*1+6*edges7.card :=
  sound edges7 words7 valid7 (by decide +kernel)

/-- base block 1; 2 removed vertices in the template, or n-1 for a base block. -/
def edges8 : Finset (Sym2 (Fin 3)) := {s(0,1),s(0,2),s(1,2)}
def words8 : Fin 1 → CycleWord (Fin 3) := ![⟨0,[1,2]⟩]
theorem valid8 : Valid edges8 words8 := by decide +kernel
theorem cost8 : ∃ P : Cycle13.CyclePacking (graph edges8),
    P.cost ≤ 19*2+6*edges8.card :=
  sound edges8 words8 valid8 (by decide +kernel)

/-- base block 2; 3 removed vertices in the template, or n-1 for a base block. -/
def edges9 : Finset (Sym2 (Fin 4)) := {s(0,1),s(0,2),s(0,3),s(1,2),s(1,3),s(2,3)}
def words9 : Fin 1 → CycleWord (Fin 4) := ![⟨0,[1,2,3]⟩]
theorem valid9 : Valid edges9 words9 := by decide +kernel
theorem cost9 : ∃ P : Cycle13.CyclePacking (graph edges9),
    P.cost ≤ 19*3+6*edges9.card :=
  sound edges9 words9 valid9 (by decide +kernel)

/-- base block 3; 3 removed vertices in the template, or n-1 for a base block. -/
def edges10 : Finset (Sym2 (Fin 4)) := {s(0,2),s(0,3),s(1,2),s(1,3)}
def words10 : Fin 1 → CycleWord (Fin 4) := ![⟨0,[2,1,3]⟩]
theorem valid10 : Valid edges10 words10 := by decide +kernel
theorem cost10 : ∃ P : Cycle13.CyclePacking (graph edges10),
    P.cost ≤ 19*3+6*edges10.card :=
  sound edges10 words10 valid10 (by decide +kernel)

/-- base block 4; 3 removed vertices in the template, or n-1 for a base block. -/
def edges11 : Finset (Sym2 (Fin 4)) := {s(0,1),s(0,2),s(0,3),s(1,2),s(1,3)}
def words11 : Fin 1 → CycleWord (Fin 4) := ![⟨0,[2,1,3]⟩]
theorem valid11 : Valid edges11 words11 := by decide +kernel
theorem cost11 : ∃ P : Cycle13.CyclePacking (graph edges11),
    P.cost ≤ 19*3+6*edges11.card :=
  sound edges11 words11 valid11 (by decide +kernel)

/-- base block 5; 4 removed vertices in the template, or n-1 for a base block. -/
def edges12 : Finset (Sym2 (Fin 5)) := {s(0,2),s(0,3),s(0,4),s(1,2),s(1,3),s(1,4)}
def words12 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[2,1,3]⟩]
theorem valid12 : Valid edges12 words12 := by decide +kernel
theorem cost12 : ∃ P : Cycle13.CyclePacking (graph edges12),
    P.cost ≤ 19*4+6*edges12.card :=
  sound edges12 words12 valid12 (by decide +kernel)

/-- base block 6; 4 removed vertices in the template, or n-1 for a base block. -/
def edges13 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(1,3),s(1,4)}
def words13 : Fin 2 → CycleWord (Fin 5) := ![⟨0,[2,1,3]⟩,⟨0,[4,1]⟩]
theorem valid13 : Valid edges13 words13 := by decide +kernel
theorem cost13 : ∃ P : Cycle13.CyclePacking (graph edges13),
    P.cost ≤ 19*4+6*edges13.card :=
  sound edges13 words13 valid13 (by decide +kernel)

end Cycle12.TerminalTemplates
