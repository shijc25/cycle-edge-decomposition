import Cycle12.TerminalCertificate

namespace Cycle12.TerminalKernels.Batch000
open Cycle12.TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

-- Parameter key: ['H', 0, 0, 0]
def edges0 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,4),s(1,2),s(2,3),s(3,4)}
def words0 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid0 : Valid edges0 words0 := by decide +kernel
theorem cost0 : ∃ P : Cycle13.CyclePacking (graph edges0),
    P.cost ≤ 19*(5-1)+6*edges0.card :=
  sound edges0 words0 valid0 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 1]
def edges1 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,4),s(1,2),s(2,3),s(3,4)}
def words1 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid1 : Valid edges1 words1 := by decide +kernel
theorem cost1 : ∃ P : Cycle13.CyclePacking (graph edges1),
    P.cost ≤ 19*(5-1)+6*edges1.card :=
  sound edges1 words1 valid1 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 2]
def edges2 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,3),s(0,4),s(1,2),s(2,3),s(3,4)}
def words2 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid2 : Valid edges2 words2 := by decide +kernel
theorem cost2 : ∃ P : Cycle13.CyclePacking (graph edges2),
    P.cost ≤ 19*(5-1)+6*edges2.card :=
  sound edges2 words2 valid2 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 3]
def edges3 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(2,3),s(3,4)}
def words3 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid3 : Valid edges3 words3 := by decide +kernel
theorem cost3 : ∃ P : Cycle13.CyclePacking (graph edges3),
    P.cost ≤ 19*(5-1)+6*edges3.card :=
  sound edges3 words3 valid3 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 4]
def edges4 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,4),s(1,2),s(1,3),s(2,3),s(3,4)}
def words4 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid4 : Valid edges4 words4 := by decide +kernel
theorem cost4 : ∃ P : Cycle13.CyclePacking (graph edges4),
    P.cost ≤ 19*(5-1)+6*edges4.card :=
  sound edges4 words4 valid4 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 5]
def edges5 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,4),s(1,2),s(1,3),s(2,3),s(3,4)}
def words5 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid5 : Valid edges5 words5 := by decide +kernel
theorem cost5 : ∃ P : Cycle13.CyclePacking (graph edges5),
    P.cost ≤ 19*(5-1)+6*edges5.card :=
  sound edges5 words5 valid5 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 6]
def edges6 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,3),s(0,4),s(1,2),s(1,3),s(2,3),s(3,4)}
def words6 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid6 : Valid edges6 words6 := by decide +kernel
theorem cost6 : ∃ P : Cycle13.CyclePacking (graph edges6),
    P.cost ≤ 19*(5-1)+6*edges6.card :=
  sound edges6 words6 valid6 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 7]
def edges7 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(1,3),s(2,3),s(3,4)}
def words7 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid7 : Valid edges7 words7 := by decide +kernel
theorem cost7 : ∃ P : Cycle13.CyclePacking (graph edges7),
    P.cost ≤ 19*(5-1)+6*edges7.card :=
  sound edges7 words7 valid7 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 8]
def edges8 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,4),s(1,2),s(1,4),s(2,3),s(3,4)}
def words8 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid8 : Valid edges8 words8 := by decide +kernel
theorem cost8 : ∃ P : Cycle13.CyclePacking (graph edges8),
    P.cost ≤ 19*(5-1)+6*edges8.card :=
  sound edges8 words8 valid8 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 9]
def edges9 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,4),s(1,2),s(1,4),s(2,3),s(3,4)}
def words9 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid9 : Valid edges9 words9 := by decide +kernel
theorem cost9 : ∃ P : Cycle13.CyclePacking (graph edges9),
    P.cost ≤ 19*(5-1)+6*edges9.card :=
  sound edges9 words9 valid9 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 10]
def edges10 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,3),s(0,4),s(1,2),s(1,4),s(2,3),s(3,4)}
def words10 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid10 : Valid edges10 words10 := by decide +kernel
theorem cost10 : ∃ P : Cycle13.CyclePacking (graph edges10),
    P.cost ≤ 19*(5-1)+6*edges10.card :=
  sound edges10 words10 valid10 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 11]
def edges11 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(1,4),s(2,3),s(3,4)}
def words11 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid11 : Valid edges11 words11 := by decide +kernel
theorem cost11 : ∃ P : Cycle13.CyclePacking (graph edges11),
    P.cost ≤ 19*(5-1)+6*edges11.card :=
  sound edges11 words11 valid11 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 12]
def edges12 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,4),s(1,2),s(1,3),s(1,4),s(2,3),s(3,4)}
def words12 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid12 : Valid edges12 words12 := by decide +kernel
theorem cost12 : ∃ P : Cycle13.CyclePacking (graph edges12),
    P.cost ≤ 19*(5-1)+6*edges12.card :=
  sound edges12 words12 valid12 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 13]
def edges13 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,4),s(1,2),s(1,3),s(1,4),s(2,3),s(3,4)}
def words13 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid13 : Valid edges13 words13 := by decide +kernel
theorem cost13 : ∃ P : Cycle13.CyclePacking (graph edges13),
    P.cost ≤ 19*(5-1)+6*edges13.card :=
  sound edges13 words13 valid13 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 14]
def edges14 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,3),s(0,4),s(1,2),s(1,3),s(1,4),s(2,3),s(3,4)}
def words14 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid14 : Valid edges14 words14 := by decide +kernel
theorem cost14 : ∃ P : Cycle13.CyclePacking (graph edges14),
    P.cost ≤ 19*(5-1)+6*edges14.card :=
  sound edges14 words14 valid14 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 15]
def edges15 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(1,3),s(1,4),s(2,3),s(3,4)}
def words15 : Fin 2 → CycleWord (Fin 5) := ![⟨0,[1,2,3]⟩,⟨1,[3,4]⟩]
theorem valid15 : Valid edges15 words15 := by decide +kernel
theorem cost15 : ∃ P : Cycle13.CyclePacking (graph edges15),
    P.cost ≤ 19*(5-1)+6*edges15.card :=
  sound edges15 words15 valid15 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 16]
def edges16 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,4),s(1,2),s(2,3),s(2,4),s(3,4)}
def words16 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid16 : Valid edges16 words16 := by decide +kernel
theorem cost16 : ∃ P : Cycle13.CyclePacking (graph edges16),
    P.cost ≤ 19*(5-1)+6*edges16.card :=
  sound edges16 words16 valid16 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 17]
def edges17 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,4),s(1,2),s(2,3),s(2,4),s(3,4)}
def words17 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid17 : Valid edges17 words17 := by decide +kernel
theorem cost17 : ∃ P : Cycle13.CyclePacking (graph edges17),
    P.cost ≤ 19*(5-1)+6*edges17.card :=
  sound edges17 words17 valid17 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 18]
def edges18 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,3),s(0,4),s(1,2),s(2,3),s(2,4),s(3,4)}
def words18 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid18 : Valid edges18 words18 := by decide +kernel
theorem cost18 : ∃ P : Cycle13.CyclePacking (graph edges18),
    P.cost ≤ 19*(5-1)+6*edges18.card :=
  sound edges18 words18 valid18 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 19]
def edges19 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(2,3),s(2,4),s(3,4)}
def words19 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid19 : Valid edges19 words19 := by decide +kernel
theorem cost19 : ∃ P : Cycle13.CyclePacking (graph edges19),
    P.cost ≤ 19*(5-1)+6*edges19.card :=
  sound edges19 words19 valid19 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 20]
def edges20 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,4),s(1,2),s(1,3),s(2,3),s(2,4),s(3,4)}
def words20 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid20 : Valid edges20 words20 := by decide +kernel
theorem cost20 : ∃ P : Cycle13.CyclePacking (graph edges20),
    P.cost ≤ 19*(5-1)+6*edges20.card :=
  sound edges20 words20 valid20 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 21]
def edges21 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,4),s(1,2),s(1,3),s(2,3),s(2,4),s(3,4)}
def words21 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid21 : Valid edges21 words21 := by decide +kernel
theorem cost21 : ∃ P : Cycle13.CyclePacking (graph edges21),
    P.cost ≤ 19*(5-1)+6*edges21.card :=
  sound edges21 words21 valid21 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 22]
def edges22 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,3),s(0,4),s(1,2),s(1,3),s(2,3),s(2,4),s(3,4)}
def words22 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid22 : Valid edges22 words22 := by decide +kernel
theorem cost22 : ∃ P : Cycle13.CyclePacking (graph edges22),
    P.cost ≤ 19*(5-1)+6*edges22.card :=
  sound edges22 words22 valid22 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 23]
def edges23 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(1,3),s(2,3),s(2,4),s(3,4)}
def words23 : Fin 2 → CycleWord (Fin 5) := ![⟨0,[1,2,3]⟩,⟨0,[2,4]⟩]
theorem valid23 : Valid edges23 words23 := by decide +kernel
theorem cost23 : ∃ P : Cycle13.CyclePacking (graph edges23),
    P.cost ≤ 19*(5-1)+6*edges23.card :=
  sound edges23 words23 valid23 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 24]
def edges24 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,4),s(1,2),s(1,4),s(2,3),s(2,4),s(3,4)}
def words24 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid24 : Valid edges24 words24 := by decide +kernel
theorem cost24 : ∃ P : Cycle13.CyclePacking (graph edges24),
    P.cost ≤ 19*(5-1)+6*edges24.card :=
  sound edges24 words24 valid24 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 25]
def edges25 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,4),s(1,2),s(1,4),s(2,3),s(2,4),s(3,4)}
def words25 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid25 : Valid edges25 words25 := by decide +kernel
theorem cost25 : ∃ P : Cycle13.CyclePacking (graph edges25),
    P.cost ≤ 19*(5-1)+6*edges25.card :=
  sound edges25 words25 valid25 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 26]
def edges26 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,3),s(0,4),s(1,2),s(1,4),s(2,3),s(2,4),s(3,4)}
def words26 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid26 : Valid edges26 words26 := by decide +kernel
theorem cost26 : ∃ P : Cycle13.CyclePacking (graph edges26),
    P.cost ≤ 19*(5-1)+6*edges26.card :=
  sound edges26 words26 valid26 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 27]
def edges27 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(1,4),s(2,3),s(2,4),s(3,4)}
def words27 : Fin 2 → CycleWord (Fin 5) := ![⟨0,[1,2,3]⟩,⟨0,[2,4]⟩]
theorem valid27 : Valid edges27 words27 := by decide +kernel
theorem cost27 : ∃ P : Cycle13.CyclePacking (graph edges27),
    P.cost ≤ 19*(5-1)+6*edges27.card :=
  sound edges27 words27 valid27 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 28]
def edges28 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,4),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(3,4)}
def words28 : Fin 1 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩]
theorem valid28 : Valid edges28 words28 := by decide +kernel
theorem cost28 : ∃ P : Cycle13.CyclePacking (graph edges28),
    P.cost ≤ 19*(5-1)+6*edges28.card :=
  sound edges28 words28 valid28 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 29]
def edges29 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,4),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(3,4)}
def words29 : Fin 2 → CycleWord (Fin 5) := ![⟨0,[1,2,4]⟩,⟨1,[3,4]⟩]
theorem valid29 : Valid edges29 words29 := by decide +kernel
theorem cost29 : ∃ P : Cycle13.CyclePacking (graph edges29),
    P.cost ≤ 19*(5-1)+6*edges29.card :=
  sound edges29 words29 valid29 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 30]
def edges30 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,3),s(0,4),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(3,4)}
def words30 : Fin 2 → CycleWord (Fin 5) := ![⟨0,[1,2,3]⟩,⟨1,[3,4]⟩]
theorem valid30 : Valid edges30 words30 := by decide +kernel
theorem cost30 : ∃ P : Cycle13.CyclePacking (graph edges30),
    P.cost ≤ 19*(5-1)+6*edges30.card :=
  sound edges30 words30 valid30 (by decide +kernel)

-- Parameter key: ['H', 0, 0, 31]
def edges31 : Finset (Sym2 (Fin 5)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(3,4)}
def words31 : Fin 2 → CycleWord (Fin 5) := ![⟨0,[1,2,3,4]⟩,⟨0,[2,4,1,3]⟩]
theorem valid31 : Valid edges31 words31 := by decide +kernel
theorem cost31 : ∃ P : Cycle13.CyclePacking (graph edges31),
    P.cost ≤ 19*(5-1)+6*edges31.card :=
  sound edges31 words31 valid31 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 0]
def edges32 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,4),s(0,5),s(1,2),s(2,3),s(3,4),s(3,5)}
def words32 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,3,4]⟩]
theorem valid32 : Valid edges32 words32 := by decide +kernel
theorem cost32 : ∃ P : Cycle13.CyclePacking (graph edges32),
    P.cost ≤ 19*(6-1)+6*edges32.card :=
  sound edges32 words32 valid32 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 1]
def edges33 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(1,2),s(2,3),s(3,4),s(3,5)}
def words33 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,3,4]⟩]
theorem valid33 : Valid edges33 words33 := by decide +kernel
theorem cost33 : ∃ P : Cycle13.CyclePacking (graph edges33),
    P.cost ≤ 19*(6-1)+6*edges33.card :=
  sound edges33 words33 valid33 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 2]
def edges34 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(1,2),s(2,3),s(3,4),s(3,5)}
def words34 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,2,3,4]⟩,⟨0,[3,5]⟩]
theorem valid34 : Valid edges34 words34 := by decide +kernel
theorem cost34 : ∃ P : Cycle13.CyclePacking (graph edges34),
    P.cost ≤ 19*(6-1)+6*edges34.card :=
  sound edges34 words34 valid34 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 3]
def edges35 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(2,3),s(3,4),s(3,5)}
def words35 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,2,3,4]⟩,⟨0,[3,5]⟩]
theorem valid35 : Valid edges35 words35 := by decide +kernel
theorem cost35 : ∃ P : Cycle13.CyclePacking (graph edges35),
    P.cost ≤ 19*(6-1)+6*edges35.card :=
  sound edges35 words35 valid35 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 4]
def edges36 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,4),s(0,5),s(1,2),s(1,3),s(2,3),s(3,4),s(3,5)}
def words36 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,3,4]⟩]
theorem valid36 : Valid edges36 words36 := by decide +kernel
theorem cost36 : ∃ P : Cycle13.CyclePacking (graph edges36),
    P.cost ≤ 19*(6-1)+6*edges36.card :=
  sound edges36 words36 valid36 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 5]
def edges37 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(1,2),s(1,3),s(2,3),s(3,4),s(3,5)}
def words37 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,3,4]⟩]
theorem valid37 : Valid edges37 words37 := by decide +kernel
theorem cost37 : ∃ P : Cycle13.CyclePacking (graph edges37),
    P.cost ≤ 19*(6-1)+6*edges37.card :=
  sound edges37 words37 valid37 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 6]
def edges38 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(2,3),s(3,4),s(3,5)}
def words38 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,2,3,4]⟩,⟨0,[3,5]⟩]
theorem valid38 : Valid edges38 words38 := by decide +kernel
theorem cost38 : ∃ P : Cycle13.CyclePacking (graph edges38),
    P.cost ≤ 19*(6-1)+6*edges38.card :=
  sound edges38 words38 valid38 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 7]
def edges39 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(2,3),s(3,4),s(3,5)}
def words39 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,2,3,4]⟩,⟨0,[3,5]⟩]
theorem valid39 : Valid edges39 words39 := by decide +kernel
theorem cost39 : ∃ P : Cycle13.CyclePacking (graph edges39),
    P.cost ≤ 19*(6-1)+6*edges39.card :=
  sound edges39 words39 valid39 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 8]
def edges40 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,4),s(0,5),s(1,2),s(1,4),s(2,3),s(3,4),s(3,5)}
def words40 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[4,1,2,3,5]⟩]
theorem valid40 : Valid edges40 words40 := by decide +kernel
theorem cost40 : ∃ P : Cycle13.CyclePacking (graph edges40),
    P.cost ≤ 19*(6-1)+6*edges40.card :=
  sound edges40 words40 valid40 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 9]
def edges41 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(1,2),s(1,4),s(2,3),s(3,4),s(3,5)}
def words41 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[2,1,4,3,5]⟩]
theorem valid41 : Valid edges41 words41 := by decide +kernel
theorem cost41 : ∃ P : Cycle13.CyclePacking (graph edges41),
    P.cost ≤ 19*(6-1)+6*edges41.card :=
  sound edges41 words41 valid41 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 10]
def edges42 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(1,2),s(1,4),s(2,3),s(3,4),s(3,5)}
def words42 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[4,1,2,3,5]⟩]
theorem valid42 : Valid edges42 words42 := by decide +kernel
theorem cost42 : ∃ P : Cycle13.CyclePacking (graph edges42),
    P.cost ≤ 19*(6-1)+6*edges42.card :=
  sound edges42 words42 valid42 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 11]
def edges43 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(1,4),s(2,3),s(3,4),s(3,5)}
def words43 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[2,1,4,3,5]⟩]
theorem valid43 : Valid edges43 words43 := by decide +kernel
theorem cost43 : ∃ P : Cycle13.CyclePacking (graph edges43),
    P.cost ≤ 19*(6-1)+6*edges43.card :=
  sound edges43 words43 valid43 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 12]
def edges44 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(2,3),s(3,4),s(3,5)}
def words44 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[4,1,2,3,5]⟩]
theorem valid44 : Valid edges44 words44 := by decide +kernel
theorem cost44 : ∃ P : Cycle13.CyclePacking (graph edges44),
    P.cost ≤ 19*(6-1)+6*edges44.card :=
  sound edges44 words44 valid44 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 13]
def edges45 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(2,3),s(3,4),s(3,5)}
def words45 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[2,1,4,3,5]⟩]
theorem valid45 : Valid edges45 words45 := by decide +kernel
theorem cost45 : ∃ P : Cycle13.CyclePacking (graph edges45),
    P.cost ≤ 19*(6-1)+6*edges45.card :=
  sound edges45 words45 valid45 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 14]
def edges46 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(2,3),s(3,4),s(3,5)}
def words46 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[4,1,2,3,5]⟩,⟨0,[1,3]⟩]
theorem valid46 : Valid edges46 words46 := by decide +kernel
theorem cost46 : ∃ P : Cycle13.CyclePacking (graph edges46),
    P.cost ≤ 19*(6-1)+6*edges46.card :=
  sound edges46 words46 valid46 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 15]
def edges47 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(2,3),s(3,4),s(3,5)}
def words47 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[2,1,4,3,5]⟩,⟨0,[1,3]⟩]
theorem valid47 : Valid edges47 words47 := by decide +kernel
theorem cost47 : ∃ P : Cycle13.CyclePacking (graph edges47),
    P.cost ≤ 19*(6-1)+6*edges47.card :=
  sound edges47 words47 valid47 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 16]
def edges48 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,4),s(0,5),s(1,2),s(2,3),s(2,4),s(3,4),s(3,5)}
def words48 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,4,3,5]⟩]
theorem valid48 : Valid edges48 words48 := by decide +kernel
theorem cost48 : ∃ P : Cycle13.CyclePacking (graph edges48),
    P.cost ≤ 19*(6-1)+6*edges48.card :=
  sound edges48 words48 valid48 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 17]
def edges49 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(1,2),s(2,3),s(2,4),s(3,4),s(3,5)}
def words49 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,4,3,5]⟩]
theorem valid49 : Valid edges49 words49 := by decide +kernel
theorem cost49 : ∃ P : Cycle13.CyclePacking (graph edges49),
    P.cost ≤ 19*(6-1)+6*edges49.card :=
  sound edges49 words49 valid49 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 18]
def edges50 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(1,2),s(2,3),s(2,4),s(3,4),s(3,5)}
def words50 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,4,3,5]⟩]
theorem valid50 : Valid edges50 words50 := by decide +kernel
theorem cost50 : ∃ P : Cycle13.CyclePacking (graph edges50),
    P.cost ≤ 19*(6-1)+6*edges50.card :=
  sound edges50 words50 valid50 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 19]
def edges51 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(2,3),s(2,4),s(3,4),s(3,5)}
def words51 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,2,4,3,5]⟩,⟨0,[2,3]⟩]
theorem valid51 : Valid edges51 words51 := by decide +kernel
theorem cost51 : ∃ P : Cycle13.CyclePacking (graph edges51),
    P.cost ≤ 19*(6-1)+6*edges51.card :=
  sound edges51 words51 valid51 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 20]
def edges52 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,4),s(0,5),s(1,2),s(1,3),s(2,3),s(2,4),s(3,4),s(3,5)}
def words52 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,4,3,5]⟩]
theorem valid52 : Valid edges52 words52 := by decide +kernel
theorem cost52 : ∃ P : Cycle13.CyclePacking (graph edges52),
    P.cost ≤ 19*(6-1)+6*edges52.card :=
  sound edges52 words52 valid52 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 21]
def edges53 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(1,2),s(1,3),s(2,3),s(2,4),s(3,4),s(3,5)}
def words53 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,4,3,5]⟩]
theorem valid53 : Valid edges53 words53 := by decide +kernel
theorem cost53 : ∃ P : Cycle13.CyclePacking (graph edges53),
    P.cost ≤ 19*(6-1)+6*edges53.card :=
  sound edges53 words53 valid53 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 22]
def edges54 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(2,3),s(2,4),s(3,4),s(3,5)}
def words54 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,4,3,5]⟩]
theorem valid54 : Valid edges54 words54 := by decide +kernel
theorem cost54 : ∃ P : Cycle13.CyclePacking (graph edges54),
    P.cost ≤ 19*(6-1)+6*edges54.card :=
  sound edges54 words54 valid54 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 23]
def edges55 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(2,3),s(2,4),s(3,4),s(3,5)}
def words55 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,2,4,3,5]⟩,⟨0,[2,3]⟩]
theorem valid55 : Valid edges55 words55 := by decide +kernel
theorem cost55 : ∃ P : Cycle13.CyclePacking (graph edges55),
    P.cost ≤ 19*(6-1)+6*edges55.card :=
  sound edges55 words55 valid55 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 24]
def edges56 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,4),s(0,5),s(1,2),s(1,4),s(2,3),s(2,4),s(3,4),s(3,5)}
def words56 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,4,3,5]⟩]
theorem valid56 : Valid edges56 words56 := by decide +kernel
theorem cost56 : ∃ P : Cycle13.CyclePacking (graph edges56),
    P.cost ≤ 19*(6-1)+6*edges56.card :=
  sound edges56 words56 valid56 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 25]
def edges57 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(1,2),s(1,4),s(2,3),s(2,4),s(3,4),s(3,5)}
def words57 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,4,3,5]⟩]
theorem valid57 : Valid edges57 words57 := by decide +kernel
theorem cost57 : ∃ P : Cycle13.CyclePacking (graph edges57),
    P.cost ≤ 19*(6-1)+6*edges57.card :=
  sound edges57 words57 valid57 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 26]
def edges58 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(1,2),s(1,4),s(2,3),s(2,4),s(3,4),s(3,5)}
def words58 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,4,3,5]⟩]
theorem valid58 : Valid edges58 words58 := by decide +kernel
theorem cost58 : ∃ P : Cycle13.CyclePacking (graph edges58),
    P.cost ≤ 19*(6-1)+6*edges58.card :=
  sound edges58 words58 valid58 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 27]
def edges59 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(1,4),s(2,3),s(2,4),s(3,4),s(3,5)}
def words59 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,2,4,3,5]⟩,⟨0,[2,3]⟩]
theorem valid59 : Valid edges59 words59 := by decide +kernel
theorem cost59 : ∃ P : Cycle13.CyclePacking (graph edges59),
    P.cost ≤ 19*(6-1)+6*edges59.card :=
  sound edges59 words59 valid59 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 28]
def edges60 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(3,4),s(3,5)}
def words60 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,4,3,5]⟩]
theorem valid60 : Valid edges60 words60 := by decide +kernel
theorem cost60 : ∃ P : Cycle13.CyclePacking (graph edges60),
    P.cost ≤ 19*(6-1)+6*edges60.card :=
  sound edges60 words60 valid60 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 29]
def edges61 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(3,4),s(3,5)}
def words61 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,2,4,3,5]⟩,⟨0,[2,3,1,4]⟩]
theorem valid61 : Valid edges61 words61 := by decide +kernel
theorem cost61 : ∃ P : Cycle13.CyclePacking (graph edges61),
    P.cost ≤ 19*(6-1)+6*edges61.card :=
  sound edges61 words61 valid61 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 30]
def edges62 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(3,4),s(3,5)}
def words62 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,2,4,3,5]⟩,⟨0,[3,1,4]⟩]
theorem valid62 : Valid edges62 words62 := by decide +kernel
theorem cost62 : ∃ P : Cycle13.CyclePacking (graph edges62),
    P.cost ≤ 19*(6-1)+6*edges62.card :=
  sound edges62 words62 valid62 (by decide +kernel)

-- Parameter key: ['H', 0, 1, 31]
def edges63 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(3,4),s(3,5)}
def words63 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,2,4,3,5]⟩,⟨0,[2,3,1,4]⟩]
theorem valid63 : Valid edges63 words63 := by decide +kernel
theorem cost63 : ∃ P : Cycle13.CyclePacking (graph edges63),
    P.cost ≤ 19*(6-1)+6*edges63.card :=
  sound edges63 words63 valid63 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 0]
def edges64 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,4),s(0,5),s(1,2),s(2,3),s(2,5),s(3,4)}
def words64 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,3,4]⟩]
theorem valid64 : Valid edges64 words64 := by decide +kernel
theorem cost64 : ∃ P : Cycle13.CyclePacking (graph edges64),
    P.cost ≤ 19*(6-1)+6*edges64.card :=
  sound edges64 words64 valid64 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 1]
def edges65 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(1,2),s(2,3),s(2,5),s(3,4)}
def words65 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,2,3,4]⟩,⟨0,[2,5]⟩]
theorem valid65 : Valid edges65 words65 := by decide +kernel
theorem cost65 : ∃ P : Cycle13.CyclePacking (graph edges65),
    P.cost ≤ 19*(6-1)+6*edges65.card :=
  sound edges65 words65 valid65 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 2]
def edges66 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(1,2),s(2,3),s(2,5),s(3,4)}
def words66 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,3,4]⟩]
theorem valid66 : Valid edges66 words66 := by decide +kernel
theorem cost66 : ∃ P : Cycle13.CyclePacking (graph edges66),
    P.cost ≤ 19*(6-1)+6*edges66.card :=
  sound edges66 words66 valid66 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 3]
def edges67 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(2,3),s(2,5),s(3,4)}
def words67 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,2,3,4]⟩,⟨0,[2,5]⟩]
theorem valid67 : Valid edges67 words67 := by decide +kernel
theorem cost67 : ∃ P : Cycle13.CyclePacking (graph edges67),
    P.cost ≤ 19*(6-1)+6*edges67.card :=
  sound edges67 words67 valid67 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 4]
def edges68 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,4),s(0,5),s(1,2),s(1,3),s(2,3),s(2,5),s(3,4)}
def words68 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[4,3,1,2,5]⟩]
theorem valid68 : Valid edges68 words68 := by decide +kernel
theorem cost68 : ∃ P : Cycle13.CyclePacking (graph edges68),
    P.cost ≤ 19*(6-1)+6*edges68.card :=
  sound edges68 words68 valid68 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 5]
def edges69 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(1,2),s(1,3),s(2,3),s(2,5),s(3,4)}
def words69 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[4,3,1,2,5]⟩]
theorem valid69 : Valid edges69 words69 := by decide +kernel
theorem cost69 : ∃ P : Cycle13.CyclePacking (graph edges69),
    P.cost ≤ 19*(6-1)+6*edges69.card :=
  sound edges69 words69 valid69 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 6]
def edges70 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(2,3),s(2,5),s(3,4)}
def words70 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[4,3,1,2,5]⟩]
theorem valid70 : Valid edges70 words70 := by decide +kernel
theorem cost70 : ∃ P : Cycle13.CyclePacking (graph edges70),
    P.cost ≤ 19*(6-1)+6*edges70.card :=
  sound edges70 words70 valid70 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 7]
def edges71 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(2,3),s(2,5),s(3,4)}
def words71 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[4,3,1,2,5]⟩,⟨0,[2,3]⟩]
theorem valid71 : Valid edges71 words71 := by decide +kernel
theorem cost71 : ∃ P : Cycle13.CyclePacking (graph edges71),
    P.cost ≤ 19*(6-1)+6*edges71.card :=
  sound edges71 words71 valid71 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 8]
def edges72 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,4),s(0,5),s(1,2),s(1,4),s(2,3),s(2,5),s(3,4)}
def words72 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,4,3,2,5]⟩]
theorem valid72 : Valid edges72 words72 := by decide +kernel
theorem cost72 : ∃ P : Cycle13.CyclePacking (graph edges72),
    P.cost ≤ 19*(6-1)+6*edges72.card :=
  sound edges72 words72 valid72 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 9]
def edges73 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(1,2),s(1,4),s(2,3),s(2,5),s(3,4)}
def words73 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,4,3,2,5]⟩]
theorem valid73 : Valid edges73 words73 := by decide +kernel
theorem cost73 : ∃ P : Cycle13.CyclePacking (graph edges73),
    P.cost ≤ 19*(6-1)+6*edges73.card :=
  sound edges73 words73 valid73 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 10]
def edges74 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(1,2),s(1,4),s(2,3),s(2,5),s(3,4)}
def words74 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,4,3,2,5]⟩]
theorem valid74 : Valid edges74 words74 := by decide +kernel
theorem cost74 : ∃ P : Cycle13.CyclePacking (graph edges74),
    P.cost ≤ 19*(6-1)+6*edges74.card :=
  sound edges74 words74 valid74 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 11]
def edges75 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(1,4),s(2,3),s(2,5),s(3,4)}
def words75 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,4,3,2,5]⟩]
theorem valid75 : Valid edges75 words75 := by decide +kernel
theorem cost75 : ∃ P : Cycle13.CyclePacking (graph edges75),
    P.cost ≤ 19*(6-1)+6*edges75.card :=
  sound edges75 words75 valid75 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 12]
def edges76 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(2,3),s(2,5),s(3,4)}
def words76 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,4,3,2,5]⟩]
theorem valid76 : Valid edges76 words76 := by decide +kernel
theorem cost76 : ∃ P : Cycle13.CyclePacking (graph edges76),
    P.cost ≤ 19*(6-1)+6*edges76.card :=
  sound edges76 words76 valid76 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 13]
def edges77 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(2,3),s(2,5),s(3,4)}
def words77 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,4,3,2,5]⟩]
theorem valid77 : Valid edges77 words77 := by decide +kernel
theorem cost77 : ∃ P : Cycle13.CyclePacking (graph edges77),
    P.cost ≤ 19*(6-1)+6*edges77.card :=
  sound edges77 words77 valid77 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 14]
def edges78 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(2,3),s(2,5),s(3,4)}
def words78 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,4,3,2,5]⟩]
theorem valid78 : Valid edges78 words78 := by decide +kernel
theorem cost78 : ∃ P : Cycle13.CyclePacking (graph edges78),
    P.cost ≤ 19*(6-1)+6*edges78.card :=
  sound edges78 words78 valid78 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 15]
def edges79 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(2,3),s(2,5),s(3,4)}
def words79 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,4,3,2,5]⟩,⟨0,[2,1,3]⟩]
theorem valid79 : Valid edges79 words79 := by decide +kernel
theorem cost79 : ∃ P : Cycle13.CyclePacking (graph edges79),
    P.cost ≤ 19*(6-1)+6*edges79.card :=
  sound edges79 words79 valid79 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 16]
def edges80 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,4),s(0,5),s(1,2),s(2,3),s(2,4),s(2,5),s(3,4)}
def words80 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,3,4]⟩]
theorem valid80 : Valid edges80 words80 := by decide +kernel
theorem cost80 : ∃ P : Cycle13.CyclePacking (graph edges80),
    P.cost ≤ 19*(6-1)+6*edges80.card :=
  sound edges80 words80 valid80 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 17]
def edges81 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(1,2),s(2,3),s(2,4),s(2,5),s(3,4)}
def words81 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,2,3,4]⟩,⟨0,[2,5]⟩]
theorem valid81 : Valid edges81 words81 := by decide +kernel
theorem cost81 : ∃ P : Cycle13.CyclePacking (graph edges81),
    P.cost ≤ 19*(6-1)+6*edges81.card :=
  sound edges81 words81 valid81 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 18]
def edges82 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(1,2),s(2,3),s(2,4),s(2,5),s(3,4)}
def words82 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,2,3,4]⟩]
theorem valid82 : Valid edges82 words82 := by decide +kernel
theorem cost82 : ∃ P : Cycle13.CyclePacking (graph edges82),
    P.cost ≤ 19*(6-1)+6*edges82.card :=
  sound edges82 words82 valid82 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 19]
def edges83 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(2,3),s(2,4),s(2,5),s(3,4)}
def words83 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,2,3,4]⟩,⟨0,[2,5]⟩]
theorem valid83 : Valid edges83 words83 := by decide +kernel
theorem cost83 : ∃ P : Cycle13.CyclePacking (graph edges83),
    P.cost ≤ 19*(6-1)+6*edges83.card :=
  sound edges83 words83 valid83 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 20]
def edges84 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,4),s(0,5),s(1,2),s(1,3),s(2,3),s(2,4),s(2,5),s(3,4)}
def words84 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,3,4,2,5]⟩]
theorem valid84 : Valid edges84 words84 := by decide +kernel
theorem cost84 : ∃ P : Cycle13.CyclePacking (graph edges84),
    P.cost ≤ 19*(6-1)+6*edges84.card :=
  sound edges84 words84 valid84 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 21]
def edges85 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(1,2),s(1,3),s(2,3),s(2,4),s(2,5),s(3,4)}
def words85 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,3,4,2,5]⟩]
theorem valid85 : Valid edges85 words85 := by decide +kernel
theorem cost85 : ∃ P : Cycle13.CyclePacking (graph edges85),
    P.cost ≤ 19*(6-1)+6*edges85.card :=
  sound edges85 words85 valid85 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 22]
def edges86 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(2,3),s(2,4),s(2,5),s(3,4)}
def words86 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,3,4,2,5]⟩]
theorem valid86 : Valid edges86 words86 := by decide +kernel
theorem cost86 : ∃ P : Cycle13.CyclePacking (graph edges86),
    P.cost ≤ 19*(6-1)+6*edges86.card :=
  sound edges86 words86 valid86 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 23]
def edges87 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(2,3),s(2,4),s(2,5),s(3,4)}
def words87 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,3,4,2,5]⟩,⟨0,[2,3]⟩]
theorem valid87 : Valid edges87 words87 := by decide +kernel
theorem cost87 : ∃ P : Cycle13.CyclePacking (graph edges87),
    P.cost ≤ 19*(6-1)+6*edges87.card :=
  sound edges87 words87 valid87 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 24]
def edges88 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,4),s(0,5),s(1,2),s(1,4),s(2,3),s(2,4),s(2,5),s(3,4)}
def words88 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,4,3,2,5]⟩]
theorem valid88 : Valid edges88 words88 := by decide +kernel
theorem cost88 : ∃ P : Cycle13.CyclePacking (graph edges88),
    P.cost ≤ 19*(6-1)+6*edges88.card :=
  sound edges88 words88 valid88 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 25]
def edges89 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(1,2),s(1,4),s(2,3),s(2,4),s(2,5),s(3,4)}
def words89 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,4,3,2,5]⟩,⟨0,[2,4]⟩]
theorem valid89 : Valid edges89 words89 := by decide +kernel
theorem cost89 : ∃ P : Cycle13.CyclePacking (graph edges89),
    P.cost ≤ 19*(6-1)+6*edges89.card :=
  sound edges89 words89 valid89 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 26]
def edges90 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(1,2),s(1,4),s(2,3),s(2,4),s(2,5),s(3,4)}
def words90 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,4,3,2,5]⟩]
theorem valid90 : Valid edges90 words90 := by decide +kernel
theorem cost90 : ∃ P : Cycle13.CyclePacking (graph edges90),
    P.cost ≤ 19*(6-1)+6*edges90.card :=
  sound edges90 words90 valid90 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 27]
def edges91 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(1,4),s(2,3),s(2,4),s(2,5),s(3,4)}
def words91 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,4,3,2,5]⟩,⟨0,[2,4]⟩]
theorem valid91 : Valid edges91 words91 := by decide +kernel
theorem cost91 : ∃ P : Cycle13.CyclePacking (graph edges91),
    P.cost ≤ 19*(6-1)+6*edges91.card :=
  sound edges91 words91 valid91 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 28]
def edges92 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(2,5),s(3,4)}
def words92 : Fin 1 → CycleWord (Fin 6) := ![⟨0,[1,3,4,2,5]⟩]
theorem valid92 : Valid edges92 words92 := by decide +kernel
theorem cost92 : ∃ P : Cycle13.CyclePacking (graph edges92),
    P.cost ≤ 19*(6-1)+6*edges92.card :=
  sound edges92 words92 valid92 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 29]
def edges93 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(2,5),s(3,4)}
def words93 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,3,4,2,5]⟩,⟨0,[2,1,4]⟩]
theorem valid93 : Valid edges93 words93 := by decide +kernel
theorem cost93 : ∃ P : Cycle13.CyclePacking (graph edges93),
    P.cost ≤ 19*(6-1)+6*edges93.card :=
  sound edges93 words93 valid93 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 30]
def edges94 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(2,5),s(3,4)}
def words94 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,3,4,2,5]⟩,⟨0,[3,2,1,4]⟩]
theorem valid94 : Valid edges94 words94 := by decide +kernel
theorem cost94 : ∃ P : Cycle13.CyclePacking (graph edges94),
    P.cost ≤ 19*(6-1)+6*edges94.card :=
  sound edges94 words94 valid94 (by decide +kernel)

-- Parameter key: ['H', 1, 0, 31]
def edges95 : Finset (Sym2 (Fin 6)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(2,5),s(3,4)}
def words95 : Fin 2 → CycleWord (Fin 6) := ![⟨0,[1,3,4,2,5]⟩,⟨0,[3,2,1,4]⟩]
theorem valid95 : Valid edges95 words95 := by decide +kernel
theorem cost95 : ∃ P : Cycle13.CyclePacking (graph edges95),
    P.cost ≤ 19*(6-1)+6*edges95.card :=
  sound edges95 words95 valid95 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 0]
def edges96 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,4),s(0,5),s(0,6),s(1,2),s(2,3),s(2,5),s(3,4),s(3,6)}
def words96 : Fin 1 → CycleWord (Fin 7) := ![⟨0,[1,2,3,4]⟩]
theorem valid96 : Valid edges96 words96 := by decide +kernel
theorem cost96 : ∃ P : Cycle13.CyclePacking (graph edges96),
    P.cost ≤ 19*(7-1)+6*edges96.card :=
  sound edges96 words96 valid96 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 1]
def edges97 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(0,6),s(1,2),s(2,3),s(2,5),s(3,4),s(3,6)}
def words97 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[1,2,3,4]⟩,⟨0,[2,5]⟩]
theorem valid97 : Valid edges97 words97 := by decide +kernel
theorem cost97 : ∃ P : Cycle13.CyclePacking (graph edges97),
    P.cost ≤ 19*(7-1)+6*edges97.card :=
  sound edges97 words97 valid97 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 2]
def edges98 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(2,3),s(2,5),s(3,4),s(3,6)}
def words98 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[1,2,3,4]⟩,⟨0,[3,6]⟩]
theorem valid98 : Valid edges98 words98 := by decide +kernel
theorem cost98 : ∃ P : Cycle13.CyclePacking (graph edges98),
    P.cost ≤ 19*(7-1)+6*edges98.card :=
  sound edges98 words98 valid98 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 3]
def edges99 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(2,3),s(2,5),s(3,4),s(3,6)}
def words99 : Fin 3 → CycleWord (Fin 7) := ![⟨0,[1,2,3,4]⟩,⟨0,[2,5]⟩,⟨0,[3,6]⟩]
theorem valid99 : Valid edges99 words99 := by decide +kernel
theorem cost99 : ∃ P : Cycle13.CyclePacking (graph edges99),
    P.cost ≤ 19*(7-1)+6*edges99.card :=
  sound edges99 words99 valid99 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 4]
def edges100 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(2,3),s(2,5),s(3,4),s(3,6)}
def words100 : Fin 1 → CycleWord (Fin 7) := ![⟨0,[4,3,1,2,5]⟩]
theorem valid100 : Valid edges100 words100 := by decide +kernel
theorem cost100 : ∃ P : Cycle13.CyclePacking (graph edges100),
    P.cost ≤ 19*(7-1)+6*edges100.card :=
  sound edges100 words100 valid100 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 5]
def edges101 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(2,3),s(2,5),s(3,4),s(3,6)}
def words101 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[4,3,1,2,5]⟩,⟨0,[2,3,6]⟩]
theorem valid101 : Valid edges101 words101 := by decide +kernel
theorem cost101 : ∃ P : Cycle13.CyclePacking (graph edges101),
    P.cost ≤ 19*(7-1)+6*edges101.card :=
  sound edges101 words101 valid101 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 6]
def edges102 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(2,3),s(2,5),s(3,4),s(3,6)}
def words102 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[4,3,1,2,5]⟩,⟨0,[3,6]⟩]
theorem valid102 : Valid edges102 words102 := by decide +kernel
theorem cost102 : ∃ P : Cycle13.CyclePacking (graph edges102),
    P.cost ≤ 19*(7-1)+6*edges102.card :=
  sound edges102 words102 valid102 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 7]
def edges103 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(2,3),s(2,5),s(3,4),s(3,6)}
def words103 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[4,3,1,2,5]⟩,⟨0,[2,3,6]⟩]
theorem valid103 : Valid edges103 words103 := by decide +kernel
theorem cost103 : ∃ P : Cycle13.CyclePacking (graph edges103),
    P.cost ≤ 19*(7-1)+6*edges103.card :=
  sound edges103 words103 valid103 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 8]
def edges104 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,4),s(0,5),s(0,6),s(1,2),s(1,4),s(2,3),s(2,5),s(3,4),s(3,6)}
def words104 : Fin 1 → CycleWord (Fin 7) := ![⟨0,[5,2,1,4,3,6]⟩]
theorem valid104 : Valid edges104 words104 := by decide +kernel
theorem cost104 : ∃ P : Cycle13.CyclePacking (graph edges104),
    P.cost ≤ 19*(7-1)+6*edges104.card :=
  sound edges104 words104 valid104 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 9]
def edges105 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(0,6),s(1,2),s(1,4),s(2,3),s(2,5),s(3,4),s(3,6)}
def words105 : Fin 1 → CycleWord (Fin 7) := ![⟨0,[5,2,1,4,3,6]⟩]
theorem valid105 : Valid edges105 words105 := by decide +kernel
theorem cost105 : ∃ P : Cycle13.CyclePacking (graph edges105),
    P.cost ≤ 19*(7-1)+6*edges105.card :=
  sound edges105 words105 valid105 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 10]
def edges106 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(1,4),s(2,3),s(2,5),s(3,4),s(3,6)}
def words106 : Fin 1 → CycleWord (Fin 7) := ![⟨0,[5,2,1,4,3,6]⟩]
theorem valid106 : Valid edges106 words106 := by decide +kernel
theorem cost106 : ∃ P : Cycle13.CyclePacking (graph edges106),
    P.cost ≤ 19*(7-1)+6*edges106.card :=
  sound edges106 words106 valid106 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 11]
def edges107 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(1,4),s(2,3),s(2,5),s(3,4),s(3,6)}
def words107 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[5,2,1,4,3,6]⟩,⟨0,[2,3]⟩]
theorem valid107 : Valid edges107 words107 := by decide +kernel
theorem cost107 : ∃ P : Cycle13.CyclePacking (graph edges107),
    P.cost ≤ 19*(7-1)+6*edges107.card :=
  sound edges107 words107 valid107 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 12]
def edges108 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(1,4),s(2,3),s(2,5),s(3,4),s(3,6)}
def words108 : Fin 1 → CycleWord (Fin 7) := ![⟨0,[5,2,1,4,3,6]⟩]
theorem valid108 : Valid edges108 words108 := by decide +kernel
theorem cost108 : ∃ P : Cycle13.CyclePacking (graph edges108),
    P.cost ≤ 19*(7-1)+6*edges108.card :=
  sound edges108 words108 valid108 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 13]
def edges109 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(1,4),s(2,3),s(2,5),s(3,4),s(3,6)}
def words109 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[5,2,1,4,3,6]⟩,⟨0,[1,3,2]⟩]
theorem valid109 : Valid edges109 words109 := by decide +kernel
theorem cost109 : ∃ P : Cycle13.CyclePacking (graph edges109),
    P.cost ≤ 19*(7-1)+6*edges109.card :=
  sound edges109 words109 valid109 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 14]
def edges110 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(1,4),s(2,3),s(2,5),s(3,4),s(3,6)}
def words110 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[5,2,1,4,3,6]⟩,⟨0,[1,3]⟩]
theorem valid110 : Valid edges110 words110 := by decide +kernel
theorem cost110 : ∃ P : Cycle13.CyclePacking (graph edges110),
    P.cost ≤ 19*(7-1)+6*edges110.card :=
  sound edges110 words110 valid110 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 15]
def edges111 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(1,4),s(2,3),s(2,5),s(3,4),s(3,6)}
def words111 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[5,2,1,4,3,6]⟩,⟨0,[1,3,2]⟩]
theorem valid111 : Valid edges111 words111 := by decide +kernel
theorem cost111 : ∃ P : Cycle13.CyclePacking (graph edges111),
    P.cost ≤ 19*(7-1)+6*edges111.card :=
  sound edges111 words111 valid111 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 16]
def edges112 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,4),s(0,5),s(0,6),s(1,2),s(2,3),s(2,4),s(2,5),s(3,4),s(3,6)}
def words112 : Fin 1 → CycleWord (Fin 7) := ![⟨0,[1,2,4,3,6]⟩]
theorem valid112 : Valid edges112 words112 := by decide +kernel
theorem cost112 : ∃ P : Cycle13.CyclePacking (graph edges112),
    P.cost ≤ 19*(7-1)+6*edges112.card :=
  sound edges112 words112 valid112 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 17]
def edges113 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(0,6),s(1,2),s(2,3),s(2,4),s(2,5),s(3,4),s(3,6)}
def words113 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[1,2,4,3,6]⟩,⟨0,[2,5]⟩]
theorem valid113 : Valid edges113 words113 := by decide +kernel
theorem cost113 : ∃ P : Cycle13.CyclePacking (graph edges113),
    P.cost ≤ 19*(7-1)+6*edges113.card :=
  sound edges113 words113 valid113 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 18]
def edges114 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(2,3),s(2,4),s(2,5),s(3,4),s(3,6)}
def words114 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[1,2,4,3,6]⟩,⟨0,[3,2,5]⟩]
theorem valid114 : Valid edges114 words114 := by decide +kernel
theorem cost114 : ∃ P : Cycle13.CyclePacking (graph edges114),
    P.cost ≤ 19*(7-1)+6*edges114.card :=
  sound edges114 words114 valid114 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 19]
def edges115 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(2,3),s(2,4),s(2,5),s(3,4),s(3,6)}
def words115 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[1,2,4,3,6]⟩,⟨0,[3,2,5]⟩]
theorem valid115 : Valid edges115 words115 := by decide +kernel
theorem cost115 : ∃ P : Cycle13.CyclePacking (graph edges115),
    P.cost ≤ 19*(7-1)+6*edges115.card :=
  sound edges115 words115 valid115 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 20]
def edges116 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(2,3),s(2,4),s(2,5),s(3,4),s(3,6)}
def words116 : Fin 1 → CycleWord (Fin 7) := ![⟨0,[1,2,4,3,6]⟩]
theorem valid116 : Valid edges116 words116 := by decide +kernel
theorem cost116 : ∃ P : Cycle13.CyclePacking (graph edges116),
    P.cost ≤ 19*(7-1)+6*edges116.card :=
  sound edges116 words116 valid116 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 21]
def edges117 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(2,3),s(2,4),s(2,5),s(3,4),s(3,6)}
def words117 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[1,2,4,3,6]⟩,⟨0,[2,5]⟩]
theorem valid117 : Valid edges117 words117 := by decide +kernel
theorem cost117 : ∃ P : Cycle13.CyclePacking (graph edges117),
    P.cost ≤ 19*(7-1)+6*edges117.card :=
  sound edges117 words117 valid117 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 22]
def edges118 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(2,3),s(2,4),s(2,5),s(3,4),s(3,6)}
def words118 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[1,2,4,3,6]⟩,⟨0,[3,2,5]⟩]
theorem valid118 : Valid edges118 words118 := by decide +kernel
theorem cost118 : ∃ P : Cycle13.CyclePacking (graph edges118),
    P.cost ≤ 19*(7-1)+6*edges118.card :=
  sound edges118 words118 valid118 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 23]
def edges119 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(2,3),s(2,4),s(2,5),s(3,4),s(3,6)}
def words119 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[1,2,4,3,6]⟩,⟨0,[3,2,5]⟩]
theorem valid119 : Valid edges119 words119 := by decide +kernel
theorem cost119 : ∃ P : Cycle13.CyclePacking (graph edges119),
    P.cost ≤ 19*(7-1)+6*edges119.card :=
  sound edges119 words119 valid119 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 24]
def edges120 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,4),s(0,5),s(0,6),s(1,2),s(1,4),s(2,3),s(2,4),s(2,5),s(3,4),s(3,6)}
def words120 : Fin 1 → CycleWord (Fin 7) := ![⟨0,[5,2,1,4,3,6]⟩]
theorem valid120 : Valid edges120 words120 := by decide +kernel
theorem cost120 : ∃ P : Cycle13.CyclePacking (graph edges120),
    P.cost ≤ 19*(7-1)+6*edges120.card :=
  sound edges120 words120 valid120 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 25]
def edges121 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(0,6),s(1,2),s(1,4),s(2,3),s(2,4),s(2,5),s(3,4),s(3,6)}
def words121 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[5,2,1,4,3,6]⟩,⟨0,[2,4]⟩]
theorem valid121 : Valid edges121 words121 := by decide +kernel
theorem cost121 : ∃ P : Cycle13.CyclePacking (graph edges121),
    P.cost ≤ 19*(7-1)+6*edges121.card :=
  sound edges121 words121 valid121 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 26]
def edges122 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(1,4),s(2,3),s(2,4),s(2,5),s(3,4),s(3,6)}
def words122 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[5,2,1,4,3,6]⟩,⟨0,[3,2,4]⟩]
theorem valid122 : Valid edges122 words122 := by decide +kernel
theorem cost122 : ∃ P : Cycle13.CyclePacking (graph edges122),
    P.cost ≤ 19*(7-1)+6*edges122.card :=
  sound edges122 words122 valid122 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 27]
def edges123 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(1,4),s(2,3),s(2,4),s(2,5),s(3,4),s(3,6)}
def words123 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[5,2,1,4,3,6]⟩,⟨0,[3,2,4]⟩]
theorem valid123 : Valid edges123 words123 := by decide +kernel
theorem cost123 : ∃ P : Cycle13.CyclePacking (graph edges123),
    P.cost ≤ 19*(7-1)+6*edges123.card :=
  sound edges123 words123 valid123 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 28]
def edges124 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(2,5),s(3,4),s(3,6)}
def words124 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[5,2,1,4,3,6]⟩,⟨0,[1,3,2,4]⟩]
theorem valid124 : Valid edges124 words124 := by decide +kernel
theorem cost124 : ∃ P : Cycle13.CyclePacking (graph edges124),
    P.cost ≤ 19*(7-1)+6*edges124.card :=
  sound edges124 words124 valid124 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 29]
def edges125 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(2,5),s(3,4),s(3,6)}
def words125 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[5,2,1,4,3,6]⟩,⟨0,[1,3,2,4]⟩]
theorem valid125 : Valid edges125 words125 := by decide +kernel
theorem cost125 : ∃ P : Cycle13.CyclePacking (graph edges125),
    P.cost ≤ 19*(7-1)+6*edges125.card :=
  sound edges125 words125 valid125 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 30]
def edges126 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(2,5),s(3,4),s(3,6)}
def words126 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[5,2,1,4,3,6]⟩,⟨0,[1,3,2,4]⟩]
theorem valid126 : Valid edges126 words126 := by decide +kernel
theorem cost126 : ∃ P : Cycle13.CyclePacking (graph edges126),
    P.cost ≤ 19*(7-1)+6*edges126.card :=
  sound edges126 words126 valid126 (by decide +kernel)

-- Parameter key: ['H', 1, 1, 31]
def edges127 : Finset (Sym2 (Fin 7)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(2,5),s(3,4),s(3,6)}
def words127 : Fin 2 → CycleWord (Fin 7) := ![⟨0,[5,2,1,4,3,6]⟩,⟨0,[1,3,2,4]⟩]
theorem valid127 : Valid edges127 words127 := by decide +kernel
theorem cost127 : ∃ P : Cycle13.CyclePacking (graph edges127),
    P.cost ≤ 19*(7-1)+6*edges127.card :=
  sound edges127 words127 valid127 (by decide +kernel)

end Cycle12.TerminalKernels.Batch000
