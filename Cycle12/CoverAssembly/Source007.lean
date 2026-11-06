import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0003
import Cycle12.RoutedCases.Batch0004
import Cycle12.RoutedCases.Batch0005
import Cycle12.RoutedCases.Batch0006

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source007

def strip0 : RatCoverRectangle := ⟨(1/125),(33/4000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0003.certificate78.rectangle,RoutedCases.Batch0004.certificate80.rectangle,RoutedCases.Batch0004.certificate94.rectangle,RoutedCases.Batch0004.certificate96.rectangle,RoutedCases.Batch0005.certificate106.rectangle,RoutedCases.Batch0005.certificate108.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound78,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound80,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound94,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound96,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound106,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound108,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(33/4000),(17/2000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0003.certificate79.rectangle,RoutedCases.Batch0004.certificate81.rectangle,RoutedCases.Batch0004.certificate95.rectangle,RoutedCases.Batch0004.certificate97.rectangle,RoutedCases.Batch0005.certificate107.rectangle,RoutedCases.Batch0005.certificate109.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0003.sound79,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound81,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound95,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound97,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound107,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound109,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(17/2000),(7/800),1,(some 2)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0004.certificate82.rectangle,RoutedCases.Batch0004.certificate83.rectangle,RoutedCases.Batch0004.certificate88.rectangle,RoutedCases.Batch0004.certificate89.rectangle,RoutedCases.Batch0004.certificate98.rectangle,RoutedCases.Batch0005.certificate103.rectangle,RoutedCases.Batch0005.certificate110.rectangle,RoutedCases.Batch0005.certificate111.rectangle,RoutedCases.Batch0005.certificate116.rectangle,RoutedCases.Batch0005.certificate117.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound82,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound83,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound88,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound89,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound98,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound103,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound110,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound111,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound116,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound117,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(7/800),(71/8000),1,(some 2)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0004.certificate84.rectangle,RoutedCases.Batch0004.certificate86.rectangle,RoutedCases.Batch0004.certificate90.rectangle,RoutedCases.Batch0004.certificate92.rectangle,RoutedCases.Batch0004.certificate99.rectangle,RoutedCases.Batch0005.certificate101.rectangle,RoutedCases.Batch0005.certificate104.rectangle,RoutedCases.Batch0005.certificate105.rectangle,RoutedCases.Batch0005.certificate112.rectangle,RoutedCases.Batch0005.certificate114.rectangle,RoutedCases.Batch0005.certificate118.rectangle,RoutedCases.Batch0006.certificate120.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound84,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound86,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound90,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound92,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound99,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound101,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound104,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound105,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound112,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound114,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound118,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound120,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(71/8000),(9/1000),1,(some 2)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0004.certificate85.rectangle,RoutedCases.Batch0004.certificate87.rectangle,RoutedCases.Batch0004.certificate91.rectangle,RoutedCases.Batch0004.certificate93.rectangle,RoutedCases.Batch0005.certificate100.rectangle,RoutedCases.Batch0005.certificate102.rectangle,RoutedCases.Batch0005.certificate104.rectangle,RoutedCases.Batch0005.certificate105.rectangle,RoutedCases.Batch0005.certificate113.rectangle,RoutedCases.Batch0005.certificate115.rectangle,RoutedCases.Batch0005.certificate119.rectangle,RoutedCases.Batch0006.certificate121.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound85,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound87,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound91,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0004.sound93,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound100,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound102,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound104,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound105,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound113,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound115,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0005.sound119,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound121,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/125),(9/1000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source007
