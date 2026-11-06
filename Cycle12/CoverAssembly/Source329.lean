import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0824
import Cycle12.RoutedCases.Batch0825
import Cycle12.RoutedCases.Batch0826

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source329

def strip0 : RatCoverRectangle := ⟨(1/250),(9/2000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0824.certificate16493.rectangle,RoutedCases.Batch0824.certificate16495.rectangle,RoutedCases.Batch0824.certificate16497.rectangle,RoutedCases.Batch0825.certificate16502.rectangle,RoutedCases.Batch0825.certificate16510.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16493,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16495,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16497,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16502,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16510,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(9/2000),(19/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0824.certificate16494.rectangle,RoutedCases.Batch0824.certificate16496.rectangle,RoutedCases.Batch0824.certificate16498.rectangle,RoutedCases.Batch0825.certificate16500.rectangle,RoutedCases.Batch0825.certificate16503.rectangle,RoutedCases.Batch0825.certificate16506.rectangle,RoutedCases.Batch0825.certificate16511.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16494,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16496,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16498,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16500,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16503,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16506,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16511,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(19/4000),(39/8000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0824.certificate16494.rectangle,RoutedCases.Batch0824.certificate16496.rectangle,RoutedCases.Batch0824.certificate16499.rectangle,RoutedCases.Batch0825.certificate16501.rectangle,RoutedCases.Batch0825.certificate16504.rectangle,RoutedCases.Batch0825.certificate16505.rectangle,RoutedCases.Batch0825.certificate16507.rectangle,RoutedCases.Batch0825.certificate16512.rectangle,RoutedCases.Batch0825.certificate16514.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16494,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16496,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16499,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16501,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16504,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16505,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16507,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16512,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16514,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(39/8000),(79/16000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0824.certificate16494.rectangle,RoutedCases.Batch0824.certificate16496.rectangle,RoutedCases.Batch0824.certificate16499.rectangle,RoutedCases.Batch0825.certificate16501.rectangle,RoutedCases.Batch0825.certificate16504.rectangle,RoutedCases.Batch0825.certificate16505.rectangle,RoutedCases.Batch0825.certificate16508.rectangle,RoutedCases.Batch0825.certificate16509.rectangle,RoutedCases.Batch0825.certificate16513.rectangle,RoutedCases.Batch0825.certificate16515.rectangle,RoutedCases.Batch0825.certificate16516.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16494,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16496,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16499,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16501,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16504,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16505,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16508,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16509,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16513,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16515,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16516,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(79/16000),(159/32000),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0824.certificate16494.rectangle,RoutedCases.Batch0824.certificate16496.rectangle,RoutedCases.Batch0824.certificate16499.rectangle,RoutedCases.Batch0825.certificate16501.rectangle,RoutedCases.Batch0825.certificate16504.rectangle,RoutedCases.Batch0825.certificate16505.rectangle,RoutedCases.Batch0825.certificate16508.rectangle,RoutedCases.Batch0825.certificate16509.rectangle,RoutedCases.Batch0825.certificate16513.rectangle,RoutedCases.Batch0825.certificate16515.rectangle,RoutedCases.Batch0825.certificate16517.rectangle,RoutedCases.Batch0826.certificate16521.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16494,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16496,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16499,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16501,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16504,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16505,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16508,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16509,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16513,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16515,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16517,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16521,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(159/32000),(319/64000),20,(some 100)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0824.certificate16494.rectangle,RoutedCases.Batch0824.certificate16496.rectangle,RoutedCases.Batch0824.certificate16499.rectangle,RoutedCases.Batch0825.certificate16501.rectangle,RoutedCases.Batch0825.certificate16504.rectangle,RoutedCases.Batch0825.certificate16505.rectangle,RoutedCases.Batch0825.certificate16508.rectangle,RoutedCases.Batch0825.certificate16509.rectangle,RoutedCases.Batch0825.certificate16513.rectangle,RoutedCases.Batch0825.certificate16515.rectangle,RoutedCases.Batch0825.certificate16518.rectangle,RoutedCases.Batch0825.certificate16519.rectangle,RoutedCases.Batch0826.certificate16522.rectangle,RoutedCases.Batch0826.certificate16524.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16494,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16496,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16499,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16501,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16504,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16505,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16508,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16509,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16513,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16515,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16518,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16519,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16522,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16524,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip6 : RatCoverRectangle := ⟨(319/64000),(1/200),20,(some 100)⟩
def pieces6 : List RatCoverRectangle := [RoutedCases.Batch0824.certificate16494.rectangle,RoutedCases.Batch0824.certificate16496.rectangle,RoutedCases.Batch0824.certificate16499.rectangle,RoutedCases.Batch0825.certificate16501.rectangle,RoutedCases.Batch0825.certificate16504.rectangle,RoutedCases.Batch0825.certificate16505.rectangle,RoutedCases.Batch0825.certificate16508.rectangle,RoutedCases.Batch0825.certificate16509.rectangle,RoutedCases.Batch0825.certificate16513.rectangle,RoutedCases.Batch0825.certificate16515.rectangle,RoutedCases.Batch0825.certificate16518.rectangle,RoutedCases.Batch0826.certificate16520.rectangle,RoutedCases.Batch0826.certificate16523.rectangle,RoutedCases.Batch0826.certificate16525.rectangle]
theorem valid6 : strip6.JoinS pieces6 := by decide +kernel
theorem sound6 : strip6.Sound := rat_cover_join_s_sound strip6 pieces6 valid6 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16494,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16496,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0824.sound16499,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16501,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16504,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16505,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16508,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16509,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16513,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16515,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0825.sound16518,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16520,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16523,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16525,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/250),(1/200),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5,strip6]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_cons.mpr ⟨sound6,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source329
