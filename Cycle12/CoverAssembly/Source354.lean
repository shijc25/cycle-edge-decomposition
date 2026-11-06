import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0842
import Cycle12.RoutedCases.Batch0843
import Cycle12.RoutedCases.Batch0844

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source354

def strip0 : RatCoverRectangle := ⟨(21/1000),(17/800),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0842.certificate16858.rectangle,RoutedCases.Batch0842.certificate16859.rectangle,RoutedCases.Batch0843.certificate16860.rectangle,RoutedCases.Batch0843.certificate16861.rectangle,RoutedCases.Batch0843.certificate16863.rectangle,RoutedCases.Batch0843.certificate16865.rectangle,RoutedCases.Batch0843.certificate16867.rectangle,RoutedCases.Batch0843.certificate16871.rectangle,RoutedCases.Batch0843.certificate16872.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16858,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16859,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16860,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16861,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16863,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16865,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16867,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16871,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16872,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(17/800),(43/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0842.certificate16858.rectangle,RoutedCases.Batch0842.certificate16859.rectangle,RoutedCases.Batch0843.certificate16860.rectangle,RoutedCases.Batch0843.certificate16861.rectangle,RoutedCases.Batch0843.certificate16863.rectangle,RoutedCases.Batch0843.certificate16865.rectangle,RoutedCases.Batch0843.certificate16867.rectangle,RoutedCases.Batch0843.certificate16871.rectangle,RoutedCases.Batch0843.certificate16873.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16858,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16859,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16860,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16861,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16863,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16865,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16867,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16871,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16873,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(43/2000),(173/8000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0842.certificate16858.rectangle,RoutedCases.Batch0842.certificate16859.rectangle,RoutedCases.Batch0843.certificate16860.rectangle,RoutedCases.Batch0843.certificate16862.rectangle,RoutedCases.Batch0843.certificate16864.rectangle,RoutedCases.Batch0843.certificate16866.rectangle,RoutedCases.Batch0843.certificate16868.rectangle,RoutedCases.Batch0843.certificate16869.rectangle,RoutedCases.Batch0843.certificate16874.rectangle,RoutedCases.Batch0843.certificate16876.rectangle,RoutedCases.Batch0843.certificate16877.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16858,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16859,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16860,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16862,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16864,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16866,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16868,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16869,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16874,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16876,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16877,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(173/8000),(87/4000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0842.certificate16858.rectangle,RoutedCases.Batch0842.certificate16859.rectangle,RoutedCases.Batch0843.certificate16860.rectangle,RoutedCases.Batch0843.certificate16862.rectangle,RoutedCases.Batch0843.certificate16864.rectangle,RoutedCases.Batch0843.certificate16866.rectangle,RoutedCases.Batch0843.certificate16868.rectangle,RoutedCases.Batch0843.certificate16869.rectangle,RoutedCases.Batch0843.certificate16874.rectangle,RoutedCases.Batch0843.certificate16876.rectangle,RoutedCases.Batch0843.certificate16878.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16858,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16859,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16860,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16862,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16864,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16866,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16868,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16869,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16874,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16876,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16878,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(87/4000),(349/16000),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0842.certificate16858.rectangle,RoutedCases.Batch0842.certificate16859.rectangle,RoutedCases.Batch0843.certificate16860.rectangle,RoutedCases.Batch0843.certificate16862.rectangle,RoutedCases.Batch0843.certificate16864.rectangle,RoutedCases.Batch0843.certificate16866.rectangle,RoutedCases.Batch0843.certificate16868.rectangle,RoutedCases.Batch0843.certificate16870.rectangle,RoutedCases.Batch0843.certificate16875.rectangle,RoutedCases.Batch0843.certificate16879.rectangle,RoutedCases.Batch0844.certificate16881.rectangle,RoutedCases.Batch0844.certificate16882.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16858,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16859,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16860,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16862,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16864,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16866,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16868,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16870,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16875,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16879,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16881,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16882,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(349/16000),(7/320),20,(some 100)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0842.certificate16858.rectangle,RoutedCases.Batch0842.certificate16859.rectangle,RoutedCases.Batch0843.certificate16860.rectangle,RoutedCases.Batch0843.certificate16862.rectangle,RoutedCases.Batch0843.certificate16864.rectangle,RoutedCases.Batch0843.certificate16866.rectangle,RoutedCases.Batch0843.certificate16868.rectangle,RoutedCases.Batch0843.certificate16870.rectangle,RoutedCases.Batch0843.certificate16875.rectangle,RoutedCases.Batch0843.certificate16879.rectangle,RoutedCases.Batch0844.certificate16881.rectangle,RoutedCases.Batch0844.certificate16883.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16858,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16859,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16860,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16862,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16864,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16866,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16868,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16870,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16875,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16879,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16881,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16883,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip6 : RatCoverRectangle := ⟨(7/320),(11/500),20,(some 100)⟩
def pieces6 : List RatCoverRectangle := [RoutedCases.Batch0842.certificate16858.rectangle,RoutedCases.Batch0842.certificate16859.rectangle,RoutedCases.Batch0843.certificate16860.rectangle,RoutedCases.Batch0843.certificate16862.rectangle,RoutedCases.Batch0843.certificate16864.rectangle,RoutedCases.Batch0843.certificate16866.rectangle,RoutedCases.Batch0843.certificate16868.rectangle,RoutedCases.Batch0843.certificate16870.rectangle,RoutedCases.Batch0843.certificate16875.rectangle,RoutedCases.Batch0844.certificate16880.rectangle,RoutedCases.Batch0844.certificate16884.rectangle]
theorem valid6 : strip6.JoinS pieces6 := by decide +kernel
theorem sound6 : strip6.Sound := rat_cover_join_s_sound strip6 pieces6 valid6 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16858,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16859,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16860,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16862,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16864,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16866,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16868,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16870,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0843.sound16875,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16880,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16884,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(21/1000),(11/500),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5,strip6]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_cons.mpr ⟨sound6,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source354
