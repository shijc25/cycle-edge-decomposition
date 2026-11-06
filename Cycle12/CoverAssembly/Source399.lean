import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0901
import Cycle12.RoutedCases.Batch0902

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source399

def strip0 : RatCoverRectangle := ⟨(119/2000),(477/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0901.certificate18027.rectangle,RoutedCases.Batch0901.certificate18028.rectangle,RoutedCases.Batch0901.certificate18029.rectangle,RoutedCases.Batch0901.certificate18030.rectangle,RoutedCases.Batch0901.certificate18031.rectangle,RoutedCases.Batch0901.certificate18033.rectangle,RoutedCases.Batch0901.certificate18035.rectangle,RoutedCases.Batch0901.certificate18037.rectangle,RoutedCases.Batch0901.certificate18039.rectangle,RoutedCases.Batch0902.certificate18041.rectangle,RoutedCases.Batch0902.certificate18043.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18027,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18028,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18029,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18030,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18031,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18033,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18035,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18037,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18039,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18041,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18043,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(477/8000),(191/3200),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0901.certificate18027.rectangle,RoutedCases.Batch0901.certificate18028.rectangle,RoutedCases.Batch0901.certificate18029.rectangle,RoutedCases.Batch0901.certificate18030.rectangle,RoutedCases.Batch0901.certificate18031.rectangle,RoutedCases.Batch0901.certificate18033.rectangle,RoutedCases.Batch0901.certificate18035.rectangle,RoutedCases.Batch0901.certificate18037.rectangle,RoutedCases.Batch0901.certificate18039.rectangle,RoutedCases.Batch0902.certificate18042.rectangle,RoutedCases.Batch0902.certificate18044.rectangle,RoutedCases.Batch0902.certificate18045.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18027,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18028,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18029,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18030,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18031,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18033,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18035,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18037,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18039,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18042,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18044,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18045,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(191/3200),(239/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0901.certificate18027.rectangle,RoutedCases.Batch0901.certificate18028.rectangle,RoutedCases.Batch0901.certificate18029.rectangle,RoutedCases.Batch0901.certificate18030.rectangle,RoutedCases.Batch0901.certificate18031.rectangle,RoutedCases.Batch0901.certificate18033.rectangle,RoutedCases.Batch0901.certificate18035.rectangle,RoutedCases.Batch0901.certificate18037.rectangle,RoutedCases.Batch0901.certificate18039.rectangle,RoutedCases.Batch0902.certificate18042.rectangle,RoutedCases.Batch0902.certificate18044.rectangle,RoutedCases.Batch0902.certificate18046.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18027,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18028,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18029,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18030,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18031,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18033,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18035,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18037,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18039,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18042,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18044,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18046,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(239/4000),(3/50),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0901.certificate18027.rectangle,RoutedCases.Batch0901.certificate18028.rectangle,RoutedCases.Batch0901.certificate18029.rectangle,RoutedCases.Batch0901.certificate18030.rectangle,RoutedCases.Batch0901.certificate18032.rectangle,RoutedCases.Batch0901.certificate18034.rectangle,RoutedCases.Batch0901.certificate18036.rectangle,RoutedCases.Batch0901.certificate18038.rectangle,RoutedCases.Batch0902.certificate18040.rectangle,RoutedCases.Batch0902.certificate18047.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18027,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18028,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18029,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18030,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18032,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18034,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18036,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0901.sound18038,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18040,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18047,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(119/2000),(3/50),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source399
