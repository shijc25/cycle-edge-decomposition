import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0002
import Cycle12.RoutedCases.Batch0003

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source006

def strip0 : RatCoverRectangle := ⟨(7/1000),(29/4000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0002.certificate52.rectangle,RoutedCases.Batch0002.certificate54.rectangle,RoutedCases.Batch0003.certificate62.rectangle,RoutedCases.Batch0003.certificate68.rectangle,RoutedCases.Batch0003.certificate70.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound52,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound54,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound62,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound68,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound70,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(29/4000),(3/400),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0002.certificate53.rectangle,RoutedCases.Batch0002.certificate55.rectangle,RoutedCases.Batch0003.certificate63.rectangle,RoutedCases.Batch0003.certificate69.rectangle,RoutedCases.Batch0003.certificate71.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound53,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound55,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound63,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound69,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound71,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(3/400),(31/4000),1,(some 2)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0002.certificate56.rectangle,RoutedCases.Batch0002.certificate59.rectangle,RoutedCases.Batch0003.certificate64.rectangle,RoutedCases.Batch0003.certificate66.rectangle,RoutedCases.Batch0003.certificate72.rectangle,RoutedCases.Batch0003.certificate75.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound56,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound59,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound64,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound66,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound72,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound75,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(31/4000),(1/125),1,(some 2)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0002.certificate57.rectangle,RoutedCases.Batch0002.certificate58.rectangle,RoutedCases.Batch0003.certificate60.rectangle,RoutedCases.Batch0003.certificate61.rectangle,RoutedCases.Batch0003.certificate65.rectangle,RoutedCases.Batch0003.certificate67.rectangle,RoutedCases.Batch0003.certificate73.rectangle,RoutedCases.Batch0003.certificate74.rectangle,RoutedCases.Batch0003.certificate76.rectangle,RoutedCases.Batch0003.certificate77.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound57,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0002.sound58,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound60,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound61,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound65,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound67,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound73,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound74,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound76,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound77,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(7/1000),(1/125),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source006
