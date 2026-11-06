import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0862
import Cycle12.RoutedCases.Batch0863

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source370

def strip0 : RatCoverRectangle := ⟨(7/200),(141/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0862.certificate17248.rectangle,RoutedCases.Batch0862.certificate17249.rectangle,RoutedCases.Batch0862.certificate17250.rectangle,RoutedCases.Batch0862.certificate17251.rectangle,RoutedCases.Batch0862.certificate17252.rectangle,RoutedCases.Batch0862.certificate17254.rectangle,RoutedCases.Batch0862.certificate17256.rectangle,RoutedCases.Batch0862.certificate17258.rectangle,RoutedCases.Batch0862.certificate17259.rectangle,RoutedCases.Batch0863.certificate17265.rectangle,RoutedCases.Batch0863.certificate17267.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17248,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17249,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17250,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17251,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17252,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17254,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17256,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17258,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17259,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17265,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17267,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(141/4000),(71/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0862.certificate17248.rectangle,RoutedCases.Batch0862.certificate17249.rectangle,RoutedCases.Batch0862.certificate17250.rectangle,RoutedCases.Batch0862.certificate17251.rectangle,RoutedCases.Batch0862.certificate17252.rectangle,RoutedCases.Batch0862.certificate17254.rectangle,RoutedCases.Batch0862.certificate17256.rectangle,RoutedCases.Batch0862.certificate17258.rectangle,RoutedCases.Batch0863.certificate17260.rectangle,RoutedCases.Batch0863.certificate17266.rectangle,RoutedCases.Batch0863.certificate17268.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17248,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17249,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17250,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17251,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17252,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17254,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17256,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17258,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17260,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17266,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17268,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(71/2000),(143/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0862.certificate17248.rectangle,RoutedCases.Batch0862.certificate17249.rectangle,RoutedCases.Batch0862.certificate17250.rectangle,RoutedCases.Batch0862.certificate17251.rectangle,RoutedCases.Batch0862.certificate17253.rectangle,RoutedCases.Batch0862.certificate17255.rectangle,RoutedCases.Batch0862.certificate17257.rectangle,RoutedCases.Batch0863.certificate17261.rectangle,RoutedCases.Batch0863.certificate17263.rectangle,RoutedCases.Batch0863.certificate17269.rectangle,RoutedCases.Batch0863.certificate17271.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17248,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17249,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17250,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17251,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17253,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17255,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17257,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17261,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17263,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17269,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17271,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(143/4000),(287/8000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0862.certificate17248.rectangle,RoutedCases.Batch0862.certificate17249.rectangle,RoutedCases.Batch0862.certificate17250.rectangle,RoutedCases.Batch0862.certificate17251.rectangle,RoutedCases.Batch0862.certificate17253.rectangle,RoutedCases.Batch0862.certificate17255.rectangle,RoutedCases.Batch0862.certificate17257.rectangle,RoutedCases.Batch0863.certificate17262.rectangle,RoutedCases.Batch0863.certificate17264.rectangle,RoutedCases.Batch0863.certificate17270.rectangle,RoutedCases.Batch0863.certificate17272.rectangle,RoutedCases.Batch0863.certificate17273.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17248,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17249,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17250,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17251,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17253,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17255,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17257,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17262,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17264,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17270,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17272,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17273,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(287/8000),(9/250),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0862.certificate17248.rectangle,RoutedCases.Batch0862.certificate17249.rectangle,RoutedCases.Batch0862.certificate17250.rectangle,RoutedCases.Batch0862.certificate17251.rectangle,RoutedCases.Batch0862.certificate17253.rectangle,RoutedCases.Batch0862.certificate17255.rectangle,RoutedCases.Batch0862.certificate17257.rectangle,RoutedCases.Batch0863.certificate17262.rectangle,RoutedCases.Batch0863.certificate17264.rectangle,RoutedCases.Batch0863.certificate17270.rectangle,RoutedCases.Batch0863.certificate17272.rectangle,RoutedCases.Batch0863.certificate17274.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17248,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17249,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17250,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17251,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17253,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17255,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0862.sound17257,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17262,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17264,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17270,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17272,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17274,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(7/200),(9/250),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source370
