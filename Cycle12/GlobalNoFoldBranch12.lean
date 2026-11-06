import Cycle12.TerminalPotentialPayments.Phase00
import Cycle12.TerminalPotentialPayments.Phase01
import Cycle12.TerminalPotentialPayments.Phase02
import Cycle12.TerminalPotentialPayments.Phase03
import Cycle12.TerminalPotentialPayments.Phase04
import Cycle12.TerminalPotentialPayments.Phase05
import Cycle12.TerminalPotentialPayments.Phase06
import Cycle12.TerminalPotentialPayments.Phase07
import Cycle12.TerminalPotentialPayments.Phase08
import Cycle12.TerminalPotentialPayments.Phase09
import Cycle12.TerminalPotentialPayments.Phase10
import Cycle12.TerminalPotentialPayments.Phase11
import Cycle12.TerminalPotentialPayments.Phase12
import Cycle12.TerminalPotentialPayments.Phase13
import Cycle12.TerminalPotentialPayments.Phase14
import Cycle12.TerminalPotentialPayments.Phase15
import Cycle12.TerminalPotentialPayments.Phase16
import Cycle12.TerminalPotentialPayments.Phase17
import Cycle12.TerminalPotentialPayments.Phase18
import Cycle12.TerminalPotentialPayments.Phase19
import Cycle12.TerminalPotentialPayments.Phase20
import Cycle12.TerminalPotentialPayments.Phase21
import Cycle12.TerminalPotentialPayments.Phase22
import Cycle12.TerminalPotentialPayments.Phase23
import Cycle12.TerminalPotentialPayments.Phase24
import Cycle12.TerminalPotentialPayments.Phase25
import Cycle12.TerminalPotentialPayments.Phase26
import Cycle12.TerminalPotentialPayments.Phase27
import Cycle12.TerminalPotentialPayments.Phase28
import Cycle12.TerminalPotentialPayments.Phase29
import Cycle12.TerminalPotentialPayments.Phase30
import Cycle12.TerminalPotentialPayments.Phase31
import Cycle12.TerminalPotentialPayments.Phase32
import Cycle12.TerminalPotentialPayments.Phase33
import Cycle12.TerminalPotentialPayments.Phase34
import Cycle12.TerminalPotentialPayments.Phase35
import Cycle12.TerminalPotentialPayments.Phase36
import Cycle12.TerminalPotentialPayments.Phase37
import Cycle12.TerminalPotentialPayments.Phase38
import Cycle12.TerminalPotentialPayments.Phase39

namespace Cycle12.Even12
open Cycle12.Global12 Real Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

def phaseLower (p : Fin 40) : ℝ :=
  match p.val with
  | 0 => PhaseMass00.lo
  | 1 => PhaseMass01.lo
  | 2 => PhaseMass02.lo
  | 3 => PhaseMass03.lo
  | 4 => PhaseMass04.lo
  | 5 => PhaseMass05.lo
  | 6 => PhaseMass06.lo
  | 7 => PhaseMass07.lo
  | 8 => PhaseMass08.lo
  | 9 => PhaseMass09.lo
  | 10 => PhaseMass10.lo
  | 11 => PhaseMass11.lo
  | 12 => PhaseMass12.lo
  | 13 => PhaseMass13.lo
  | 14 => PhaseMass14.lo
  | 15 => PhaseMass15.lo
  | 16 => PhaseMass16.lo
  | 17 => PhaseMass17.lo
  | 18 => PhaseMass18.lo
  | 19 => PhaseMass19.lo
  | 20 => PhaseMass20.lo
  | 21 => PhaseMass21.lo
  | 22 => PhaseMass22.lo
  | 23 => PhaseMass23.lo
  | 24 => PhaseMass24.lo
  | 25 => PhaseMass25.lo
  | 26 => PhaseMass26.lo
  | 27 => PhaseMass27.lo
  | 28 => PhaseMass28.lo
  | 29 => PhaseMass29.lo
  | 30 => PhaseMass30.lo
  | 31 => PhaseMass31.lo
  | 32 => PhaseMass32.lo
  | 33 => PhaseMass33.lo
  | 34 => PhaseMass34.lo
  | 35 => PhaseMass35.lo
  | 36 => PhaseMass36.lo
  | 37 => PhaseMass37.lo
  | 38 => PhaseMass38.lo
  | _ => PhaseMass39.lo
def phaseUpper (p : Fin 40) : ℝ :=
  match p.val with
  | 0 => PhaseMass00.hi
  | 1 => PhaseMass01.hi
  | 2 => PhaseMass02.hi
  | 3 => PhaseMass03.hi
  | 4 => PhaseMass04.hi
  | 5 => PhaseMass05.hi
  | 6 => PhaseMass06.hi
  | 7 => PhaseMass07.hi
  | 8 => PhaseMass08.hi
  | 9 => PhaseMass09.hi
  | 10 => PhaseMass10.hi
  | 11 => PhaseMass11.hi
  | 12 => PhaseMass12.hi
  | 13 => PhaseMass13.hi
  | 14 => PhaseMass14.hi
  | 15 => PhaseMass15.hi
  | 16 => PhaseMass16.hi
  | 17 => PhaseMass17.hi
  | 18 => PhaseMass18.hi
  | 19 => PhaseMass19.hi
  | 20 => PhaseMass20.hi
  | 21 => PhaseMass21.hi
  | 22 => PhaseMass22.hi
  | 23 => PhaseMass23.hi
  | 24 => PhaseMass24.hi
  | 25 => PhaseMass25.hi
  | 26 => PhaseMass26.hi
  | 27 => PhaseMass27.hi
  | 28 => PhaseMass28.hi
  | 29 => PhaseMass29.hi
  | 30 => PhaseMass30.hi
  | 31 => PhaseMass31.hi
  | 32 => PhaseMass32.hi
  | 33 => PhaseMass33.hi
  | 34 => PhaseMass34.hi
  | 35 => PhaseMass35.hi
  | 36 => PhaseMass36.hi
  | 37 => PhaseMass37.hi
  | 38 => PhaseMass38.hi
  | _ => PhaseMass39.hi
def foldingThreshold (p : Fin 40) : ℕ → ℝ :=
  match p.val with
  | 0 => Cycle12.Phase00.threshold
  | 1 => Cycle12.Phase01.threshold
  | 2 => Cycle12.Phase02.threshold
  | 3 => Cycle12.Phase03.threshold
  | 4 => Cycle12.Phase04.threshold
  | 5 => Cycle12.Phase05.threshold
  | 6 => Cycle12.Phase06.threshold
  | 7 => Cycle12.Phase07.threshold
  | 8 => Cycle12.Phase08.threshold
  | 9 => Cycle12.Phase09.threshold
  | 10 => Cycle12.Phase10.threshold
  | 11 => Cycle12.Phase11.threshold
  | 12 => Cycle12.Phase12.threshold
  | 13 => Cycle12.Phase13.threshold
  | 14 => Cycle12.Phase14.threshold
  | 15 => Cycle12.Phase15.threshold
  | 16 => Cycle12.Phase16.threshold
  | 17 => Cycle12.Phase17.threshold
  | 18 => Cycle12.Phase18.threshold
  | 19 => Cycle12.Phase19.threshold
  | 20 => Cycle12.Phase20.threshold
  | 21 => Cycle12.Phase21.threshold
  | 22 => Cycle12.Phase22.threshold
  | 23 => Cycle12.Phase23.threshold
  | 24 => Cycle12.Phase24.threshold
  | 25 => Cycle12.Phase25.threshold
  | 26 => Cycle12.Phase26.threshold
  | 27 => Cycle12.Phase27.threshold
  | 28 => Cycle12.Phase28.threshold
  | 29 => Cycle12.Phase29.threshold
  | 30 => Cycle12.Phase30.threshold
  | 31 => Cycle12.Phase31.threshold
  | 32 => Cycle12.Phase32.threshold
  | 33 => Cycle12.Phase33.threshold
  | 34 => Cycle12.Phase34.threshold
  | 35 => Cycle12.Phase35.threshold
  | 36 => Cycle12.Phase36.threshold
  | 37 => Cycle12.Phase37.threshold
  | 38 => Cycle12.Phase38.threshold
  | _ => Cycle12.Phase39.threshold

theorem phase_interval_cover {x : ℝ} (hx : wA ≤ x) (hx1 : x ≤ wA/theta2) :
    ∃ p : Fin 40,phaseLower p ≤ x ∧ x ≤ phaseUpper p := by
  by_cases h0 : x ≤ ((37188683587092162972253359375000/233000934795513564011848245631):ℝ)
  · refine ⟨0,?_,?_⟩
    · have he : phaseLower 0=wA := by norm_num [phaseLower,PhaseMass00.lo,wA]
      rw [he]
      exact hx
    · have he : phaseUpper 0=((37188683587092162972253359375000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass00.hi]
      rwa [he]
  by_cases h1 : x ≤ ((37480395552190802876374218750000/233000934795513564011848245631):ℝ)
  · refine ⟨1,?_,?_⟩
    · have he : phaseLower 1=((37188683587092162972253359375000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass01.lo]
      rw [he]
      exact (lt_of_not_ge h0).le
    · have he : phaseUpper 1=((37480395552190802876374218750000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass01.hi]
      rwa [he]
  by_cases h2 : x ≤ ((37772107517289442780495078125000/233000934795513564011848245631):ℝ)
  · refine ⟨2,?_,?_⟩
    · have he : phaseLower 2=((37480395552190802876374218750000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass02.lo]
      rw [he]
      exact (lt_of_not_ge h1).le
    · have he : phaseUpper 2=((37772107517289442780495078125000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass02.hi]
      rwa [he]
  by_cases h3 : x ≤ ((38063819482388082684615937500000/233000934795513564011848245631):ℝ)
  · refine ⟨3,?_,?_⟩
    · have he : phaseLower 3=((37772107517289442780495078125000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass03.lo]
      rw [he]
      exact (lt_of_not_ge h2).le
    · have he : phaseUpper 3=((38063819482388082684615937500000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass03.hi]
      rwa [he]
  by_cases h4 : x ≤ ((38355531447486722588736796875000/233000934795513564011848245631):ℝ)
  · refine ⟨4,?_,?_⟩
    · have he : phaseLower 4=((38063819482388082684615937500000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass04.lo]
      rw [he]
      exact (lt_of_not_ge h3).le
    · have he : phaseUpper 4=((38355531447486722588736796875000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass04.hi]
      rwa [he]
  by_cases h5 : x ≤ ((38647243412585362492857656250000/233000934795513564011848245631):ℝ)
  · refine ⟨5,?_,?_⟩
    · have he : phaseLower 5=((38355531447486722588736796875000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass05.lo]
      rw [he]
      exact (lt_of_not_ge h4).le
    · have he : phaseUpper 5=((38647243412585362492857656250000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass05.hi]
      rwa [he]
  by_cases h6 : x ≤ ((38938955377684002396978515625000/233000934795513564011848245631):ℝ)
  · refine ⟨6,?_,?_⟩
    · have he : phaseLower 6=((38647243412585362492857656250000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass06.lo]
      rw [he]
      exact (lt_of_not_ge h5).le
    · have he : phaseUpper 6=((38938955377684002396978515625000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass06.hi]
      rwa [he]
  by_cases h7 : x ≤ ((39230667342782642301099375000000/233000934795513564011848245631):ℝ)
  · refine ⟨7,?_,?_⟩
    · have he : phaseLower 7=((38938955377684002396978515625000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass07.lo]
      rw [he]
      exact (lt_of_not_ge h6).le
    · have he : phaseUpper 7=((39230667342782642301099375000000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass07.hi]
      rwa [he]
  by_cases h8 : x ≤ ((2324845841640075423836484375000/13705937340912562588932249743):ℝ)
  · refine ⟨8,?_,?_⟩
    · have he : phaseLower 8=((39230667342782642301099375000000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass08.lo]
      rw [he]
      exact (lt_of_not_ge h7).le
    · have he : phaseUpper 8=((2324845841640075423836484375000/13705937340912562588932249743):ℝ) := by norm_num [phaseUpper,PhaseMass08.hi]
      rwa [he]
  by_cases h9 : x ≤ ((39814091272979922109341093750000/233000934795513564011848245631):ℝ)
  · refine ⟨9,?_,?_⟩
    · have he : phaseLower 9=((2324845841640075423836484375000/13705937340912562588932249743):ℝ) := by norm_num [phaseLower,PhaseMass09.lo]
      rw [he]
      exact (lt_of_not_ge h8).le
    · have he : phaseUpper 9=((39814091272979922109341093750000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass09.hi]
      rwa [he]
  by_cases h10 : x ≤ ((3645982112552596546678359375000/21181903163228505819258931421):ℝ)
  · refine ⟨10,?_,?_⟩
    · have he : phaseLower 10=((39814091272979922109341093750000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass10.lo]
      rw [he]
      exact (lt_of_not_ge h9).le
    · have he : phaseUpper 10=((3645982112552596546678359375000/21181903163228505819258931421):ℝ) := by norm_num [phaseUpper,PhaseMass10.hi]
      rwa [he]
  by_cases h11 : x ≤ ((40397515203177201917582812500000/233000934795513564011848245631):ℝ)
  · refine ⟨11,?_,?_⟩
    · have he : phaseLower 11=((3645982112552596546678359375000/21181903163228505819258931421):ℝ) := by norm_num [phaseLower,PhaseMass11.lo]
      rw [he]
      exact (lt_of_not_ge h10).le
    · have he : phaseUpper 11=((40397515203177201917582812500000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass11.hi]
      rwa [he]
  by_cases h12 : x ≤ ((40689227168275841821703671875000/233000934795513564011848245631):ℝ)
  · refine ⟨12,?_,?_⟩
    · have he : phaseLower 12=((40397515203177201917582812500000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass12.lo]
      rw [he]
      exact (lt_of_not_ge h11).le
    · have he : phaseUpper 12=((40689227168275841821703671875000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass12.hi]
      rwa [he]
  by_cases h13 : x ≤ ((40980939133374481725824531250000/233000934795513564011848245631):ℝ)
  · refine ⟨13,?_,?_⟩
    · have he : phaseLower 13=((40689227168275841821703671875000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass13.lo]
      rw [he]
      exact (lt_of_not_ge h12).le
    · have he : phaseUpper 13=((40980939133374481725824531250000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass13.hi]
      rwa [he]
  by_cases h14 : x ≤ ((41272651098473121629945390625000/233000934795513564011848245631):ℝ)
  · refine ⟨14,?_,?_⟩
    · have he : phaseLower 14=((40980939133374481725824531250000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass14.lo]
      rw [he]
      exact (lt_of_not_ge h13).le
    · have he : phaseUpper 14=((41272651098473121629945390625000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass14.hi]
      rwa [he]
  by_cases h15 : x ≤ ((41564363063571761534066250000000/233000934795513564011848245631):ℝ)
  · refine ⟨15,?_,?_⟩
    · have he : phaseLower 15=((41272651098473121629945390625000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass15.lo]
      rw [he]
      exact (lt_of_not_ge h14).le
    · have he : phaseUpper 15=((41564363063571761534066250000000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass15.hi]
      rwa [he]
  by_cases h16 : x ≤ ((41856075028670401438187109375000/233000934795513564011848245631):ℝ)
  · refine ⟨16,?_,?_⟩
    · have he : phaseLower 16=((41564363063571761534066250000000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass16.lo]
      rw [he]
      exact (lt_of_not_ge h15).le
    · have he : phaseUpper 16=((41856075028670401438187109375000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass16.hi]
      rwa [he]
  by_cases h17 : x ≤ ((42147786993769041342307968750000/233000934795513564011848245631):ℝ)
  · refine ⟨17,?_,?_⟩
    · have he : phaseLower 17=((41856075028670401438187109375000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass17.lo]
      rw [he]
      exact (lt_of_not_ge h16).le
    · have he : phaseUpper 17=((42147786993769041342307968750000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass17.hi]
      rwa [he]
  by_cases h18 : x ≤ ((42439498958867681246428828125000/233000934795513564011848245631):ℝ)
  · refine ⟨18,?_,?_⟩
    · have he : phaseLower 18=((42147786993769041342307968750000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass18.lo]
      rw [he]
      exact (lt_of_not_ge h17).le
    · have he : phaseUpper 18=((42439498958867681246428828125000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass18.hi]
      rwa [he]
  by_cases h19 : x ≤ ((42731210923966321150549687500000/233000934795513564011848245631):ℝ)
  · refine ⟨19,?_,?_⟩
    · have he : phaseLower 19=((42439498958867681246428828125000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass19.lo]
      rw [he]
      exact (lt_of_not_ge h18).le
    · have he : phaseUpper 19=((42731210923966321150549687500000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass19.hi]
      rwa [he]
  by_cases h20 : x ≤ ((43022922889064961054670546875000/233000934795513564011848245631):ℝ)
  · refine ⟨20,?_,?_⟩
    · have he : phaseLower 20=((42731210923966321150549687500000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass20.lo]
      rw [he]
      exact (lt_of_not_ge h19).le
    · have he : phaseUpper 20=((43022922889064961054670546875000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass20.hi]
      rwa [he]
  by_cases h21 : x ≤ ((3937694077651236450799218750000/21181903163228505819258931421):ℝ)
  · refine ⟨21,?_,?_⟩
    · have he : phaseLower 21=((43022922889064961054670546875000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass21.lo]
      rw [he]
      exact (lt_of_not_ge h20).le
    · have he : phaseUpper 21=((3937694077651236450799218750000/21181903163228505819258931421):ℝ) := by norm_num [phaseUpper,PhaseMass21.hi]
      rwa [he]
  by_cases h22 : x ≤ ((43606346819262240862912265625000/233000934795513564011848245631):ℝ)
  · refine ⟨22,?_,?_⟩
    · have he : phaseLower 22=((3937694077651236450799218750000/21181903163228505819258931421):ℝ) := by norm_num [phaseLower,PhaseMass22.lo]
      rw [he]
      exact (lt_of_not_ge h21).le
    · have he : phaseUpper 22=((43606346819262240862912265625000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass22.hi]
      rwa [he]
  by_cases h23 : x ≤ ((43898058784360880767033125000000/233000934795513564011848245631):ℝ)
  · refine ⟨23,?_,?_⟩
    · have he : phaseLower 23=((43606346819262240862912265625000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass23.lo]
      rw [he]
      exact (lt_of_not_ge h22).le
    · have he : phaseUpper 23=((43898058784360880767033125000000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass23.hi]
      rwa [he]
  by_cases h24 : x ≤ ((44189770749459520671153984375000/233000934795513564011848245631):ℝ)
  · refine ⟨24,?_,?_⟩
    · have he : phaseLower 24=((43898058784360880767033125000000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass24.lo]
      rw [he]
      exact (lt_of_not_ge h23).le
    · have he : phaseUpper 24=((44189770749459520671153984375000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass24.hi]
      rwa [he]
  by_cases h25 : x ≤ ((2616557806738715327957343750000/13705937340912562588932249743):ℝ)
  · refine ⟨25,?_,?_⟩
    · have he : phaseLower 25=((44189770749459520671153984375000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass25.lo]
      rw [he]
      exact (lt_of_not_ge h24).le
    · have he : phaseUpper 25=((2616557806738715327957343750000/13705937340912562588932249743):ℝ) := by norm_num [phaseUpper,PhaseMass25.hi]
      rwa [he]
  by_cases h26 : x ≤ ((44773194679656800479395703125000/233000934795513564011848245631):ℝ)
  · refine ⟨26,?_,?_⟩
    · have he : phaseLower 26=((2616557806738715327957343750000/13705937340912562588932249743):ℝ) := by norm_num [phaseLower,PhaseMass26.lo]
      rw [he]
      exact (lt_of_not_ge h25).le
    · have he : phaseUpper 26=((44773194679656800479395703125000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass26.hi]
      rwa [he]
  by_cases h27 : x ≤ ((45064906644755440383516562500000/233000934795513564011848245631):ℝ)
  · refine ⟨27,?_,?_⟩
    · have he : phaseLower 27=((44773194679656800479395703125000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass27.lo]
      rw [he]
      exact (lt_of_not_ge h26).le
    · have he : phaseUpper 27=((45064906644755440383516562500000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass27.hi]
      rwa [he]
  by_cases h28 : x ≤ ((45356618609854080287637421875000/233000934795513564011848245631):ℝ)
  · refine ⟨28,?_,?_⟩
    · have he : phaseLower 28=((45064906644755440383516562500000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass28.lo]
      rw [he]
      exact (lt_of_not_ge h27).le
    · have he : phaseUpper 28=((45356618609854080287637421875000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass28.hi]
      rwa [he]
  by_cases h29 : x ≤ ((45648330574952720191758281250000/233000934795513564011848245631):ℝ)
  · refine ⟨29,?_,?_⟩
    · have he : phaseLower 29=((45356618609854080287637421875000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass29.lo]
      rw [he]
      exact (lt_of_not_ge h28).le
    · have he : phaseUpper 29=((45648330574952720191758281250000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass29.hi]
      rwa [he]
  by_cases h30 : x ≤ ((45940042540051360095879140625000/233000934795513564011848245631):ℝ)
  · refine ⟨30,?_,?_⟩
    · have he : phaseLower 30=((45648330574952720191758281250000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass30.lo]
      rw [he]
      exact (lt_of_not_ge h29).le
    · have he : phaseUpper 30=((45940042540051360095879140625000/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass30.hi]
      rwa [he]
  by_cases h31 : x ≤ ((46085898522600680047939570312500/233000934795513564011848245631):ℝ)
  · refine ⟨31,?_,?_⟩
    · have he : phaseLower 31=((45940042540051360095879140625000/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass31.lo]
      rw [he]
      exact (lt_of_not_ge h30).le
    · have he : phaseUpper 31=((46085898522600680047939570312500/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass31.hi]
      rwa [he]
  by_cases h32 : x ≤ ((46158826513875340023969785156250/233000934795513564011848245631):ℝ)
  · refine ⟨32,?_,?_⟩
    · have he : phaseLower 32=((46085898522600680047939570312500/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass32.lo]
      rw [he]
      exact (lt_of_not_ge h31).le
    · have he : phaseUpper 32=((46158826513875340023969785156250/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass32.hi]
      rwa [he]
  by_cases h33 : x ≤ ((46195290509512670011984892578125/233000934795513564011848245631):ℝ)
  · refine ⟨33,?_,?_⟩
    · have he : phaseLower 33=((46158826513875340023969785156250/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass33.lo]
      rw [he]
      exact (lt_of_not_ge h32).le
    · have he : phaseUpper 33=((46195290509512670011984892578125/233000934795513564011848245631):ℝ) := by norm_num [phaseUpper,PhaseMass33.hi]
      rwa [he]
  by_cases h34 : x ≤ ((92427045014662670011984892578125/466001869591027128023696491262):ℝ)
  · refine ⟨34,?_,?_⟩
    · have he : phaseLower 34=((46195290509512670011984892578125/233000934795513564011848245631):ℝ) := by norm_num [phaseLower,PhaseMass34.lo]
      rw [he]
      exact (lt_of_not_ge h33).le
    · have he : phaseUpper 34=((92427045014662670011984892578125/466001869591027128023696491262):ℝ) := by norm_num [phaseUpper,PhaseMass34.hi]
      rwa [he]
  by_cases h35 : x ≤ ((16808232184087515455634990234375/84727612652914023277035725684):ℝ)
  · refine ⟨35,?_,?_⟩
    · have he : phaseLower 35=((92427045014662670011984892578125/466001869591027128023696491262):ℝ) := by norm_num [phaseLower,PhaseMass35.lo]
      rw [he]
      exact (lt_of_not_ge h34).le
    · have he : phaseUpper 35=((16808232184087515455634990234375/84727612652914023277035725684):ℝ) := by norm_num [phaseUpper,PhaseMass35.hi]
      rwa [he]
  by_cases h36 : x ≤ ((369817572045562670011984892578125/1864007478364108512094785965048):ℝ)
  · refine ⟨36,?_,?_⟩
    · have he : phaseLower 36=((16808232184087515455634990234375/84727612652914023277035725684):ℝ) := by norm_num [phaseLower,PhaseMass36.lo]
      rw [he]
      exact (lt_of_not_ge h35).le
    · have he : phaseUpper 36=((369817572045562670011984892578125/1864007478364108512094785965048):ℝ) := by norm_num [phaseUpper,PhaseMass36.hi]
      rwa [he]
  by_cases h37 : x ≤ ((739671608086762670011984892578125/3728014956728217024189571930096):ℝ)
  · refine ⟨37,?_,?_⟩
    · have he : phaseLower 37=((369817572045562670011984892578125/1864007478364108512094785965048):ℝ) := by norm_num [phaseLower,PhaseMass37.lo]
      rw [he]
      exact (lt_of_not_ge h36).le
    · have he : phaseUpper 37=((739671608086762670011984892578125/3728014956728217024189571930096):ℝ) := by norm_num [phaseUpper,PhaseMass37.hi]
      rwa [he]
  by_cases h38 : x ≤ ((1479379680169162670011984892578125/7456029913456434048379143860192):ℝ)
  · refine ⟨38,?_,?_⟩
    · have he : phaseLower 38=((739671608086762670011984892578125/3728014956728217024189571930096):ℝ) := by norm_num [phaseLower,PhaseMass38.lo]
      rw [he]
      exact (lt_of_not_ge h37).le
    · have he : phaseUpper 38=((1479379680169162670011984892578125/7456029913456434048379143860192):ℝ) := by norm_num [phaseUpper,PhaseMass38.hi]
      rwa [he]
  refine ⟨39,?_,?_⟩
  · have he : phaseLower 39=((1479379680169162670011984892578125/7456029913456434048379143860192):ℝ) := by norm_num [phaseLower,PhaseMass39.lo]
    rw [he]
    exact (lt_of_not_ge h38).le
  · have he : phaseUpper 39=wA/theta2 := by norm_num [phaseUpper,PhaseMass39.hi,wA,theta2]
    rwa [he]

variable {V : Type} [Fintype V] [DecidableEq V]

def hasPhaseFold {G : SimpleGraph V} (L : EvenScaleLayers12 G) (p : Fin 40) : Prop :=
  ∃ i : Fin (L.stopIndex+3),0<L.coreMass i.val ∧ i.val+2<L.stopIndex+3 ∧
    (∑ j : Fin (L.stopIndex+3) with j.val  ≤  i.val+2,L.coreMass j.val) ≤ 
      foldingThreshold p (L.stopIndex+3-i.val)*L.coreMass i.val

def hasActiveFold {G : SimpleGraph V} (L : EvenScaleLayers12 G) : Prop :=
  ∃ p : Fin 40,phaseLower p ≤ theta2^L.stopIndex*originalLog V ∧
    theta2^L.stopIndex*originalLog V ≤ phaseUpper p ∧ hasPhaseFold L p

/-- The entire actual no-fold branch, covering every stopping phase and
arbitrarily many layers. Only strictly smaller graphs enter the IH. -/
theorem terminal_potential_of_no_fold {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (ih : ∀ n,n<Fintype.card V → ∀ H : SimpleGraph (Fin n),
      ∃ Q : CyclePacking H,Q.weight ≤ C*n)
    (hnofold : ¬hasActiveFold L) :
    ∃ Q : CyclePacking G,Q.weight ≤ C*orderPotential (Fintype.card V)*Fintype.card V := by
  obtain ⟨p,hlo,hhi⟩ := phase_interval_cover L.phase_lower L.phase_upper.le
  have hno : ¬hasPhaseFold L p := fun hf => hnofold ⟨p,hlo,hhi,hf⟩
  fin_cases p
  · exact TerminalPayment00.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment01.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment02.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment03.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment04.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment05.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment06.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment07.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment08.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment09.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment10.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment11.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment12.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment13.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment14.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment15.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment16.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment17.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment18.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment19.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment20.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment21.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment22.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment23.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment24.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment25.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment26.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment27.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment28.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment29.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment30.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment31.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment32.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment33.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment34.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment35.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment36.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment37.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment38.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)
  · exact TerminalPayment39.actual_terminal L ih
      (by simpa only [phaseLower,Matrix.cons_val_zero,Matrix.cons_val_succ] using hlo)
      (by simpa only [phaseUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] using hhi)
      (by simpa only [hasPhaseFold,foldingThreshold,Matrix.cons_val_zero,Matrix.cons_val_succ] using hno)

end
end Cycle12.Even12
