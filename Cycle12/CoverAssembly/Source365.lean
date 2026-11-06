import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0853
import Cycle12.RoutedCases.Batch0854

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source365

def strip0 : RatCoverRectangle := ⟨(3/100),(121/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0853.certificate17068.rectangle,RoutedCases.Batch0853.certificate17069.rectangle,RoutedCases.Batch0853.certificate17070.rectangle,RoutedCases.Batch0853.certificate17071.rectangle,RoutedCases.Batch0853.certificate17072.rectangle,RoutedCases.Batch0853.certificate17074.rectangle,RoutedCases.Batch0853.certificate17076.rectangle,RoutedCases.Batch0853.certificate17079.rectangle,RoutedCases.Batch0854.certificate17083.rectangle,RoutedCases.Batch0854.certificate17085.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17068,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17069,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17070,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17071,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17072,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17074,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17076,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17079,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17083,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17085,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(121/4000),(61/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0853.certificate17068.rectangle,RoutedCases.Batch0853.certificate17069.rectangle,RoutedCases.Batch0853.certificate17070.rectangle,RoutedCases.Batch0853.certificate17071.rectangle,RoutedCases.Batch0853.certificate17072.rectangle,RoutedCases.Batch0853.certificate17074.rectangle,RoutedCases.Batch0853.certificate17076.rectangle,RoutedCases.Batch0853.certificate17079.rectangle,RoutedCases.Batch0854.certificate17084.rectangle,RoutedCases.Batch0854.certificate17086.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17068,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17069,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17070,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17071,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17072,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17074,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17076,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17079,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17084,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17086,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(61/2000),(123/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0853.certificate17068.rectangle,RoutedCases.Batch0853.certificate17069.rectangle,RoutedCases.Batch0853.certificate17070.rectangle,RoutedCases.Batch0853.certificate17071.rectangle,RoutedCases.Batch0853.certificate17073.rectangle,RoutedCases.Batch0853.certificate17075.rectangle,RoutedCases.Batch0853.certificate17077.rectangle,RoutedCases.Batch0853.certificate17078.rectangle,RoutedCases.Batch0854.certificate17080.rectangle,RoutedCases.Batch0854.certificate17081.rectangle,RoutedCases.Batch0854.certificate17087.rectangle,RoutedCases.Batch0854.certificate17091.rectangle,RoutedCases.Batch0854.certificate17092.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17068,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17069,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17070,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17071,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17073,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17075,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17077,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17078,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17080,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17081,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17087,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17091,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17092,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(123/4000),(247/8000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0853.certificate17068.rectangle,RoutedCases.Batch0853.certificate17069.rectangle,RoutedCases.Batch0853.certificate17070.rectangle,RoutedCases.Batch0853.certificate17071.rectangle,RoutedCases.Batch0853.certificate17073.rectangle,RoutedCases.Batch0853.certificate17075.rectangle,RoutedCases.Batch0853.certificate17077.rectangle,RoutedCases.Batch0853.certificate17078.rectangle,RoutedCases.Batch0854.certificate17080.rectangle,RoutedCases.Batch0854.certificate17082.rectangle,RoutedCases.Batch0854.certificate17088.rectangle,RoutedCases.Batch0854.certificate17089.rectangle,RoutedCases.Batch0854.certificate17093.rectangle,RoutedCases.Batch0854.certificate17095.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17068,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17069,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17070,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17071,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17073,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17075,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17077,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17078,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17080,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17082,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17088,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17089,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17093,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17095,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(247/8000),(31/1000),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0853.certificate17068.rectangle,RoutedCases.Batch0853.certificate17069.rectangle,RoutedCases.Batch0853.certificate17070.rectangle,RoutedCases.Batch0853.certificate17071.rectangle,RoutedCases.Batch0853.certificate17073.rectangle,RoutedCases.Batch0853.certificate17075.rectangle,RoutedCases.Batch0853.certificate17077.rectangle,RoutedCases.Batch0853.certificate17078.rectangle,RoutedCases.Batch0854.certificate17080.rectangle,RoutedCases.Batch0854.certificate17082.rectangle,RoutedCases.Batch0854.certificate17088.rectangle,RoutedCases.Batch0854.certificate17090.rectangle,RoutedCases.Batch0854.certificate17094.rectangle,RoutedCases.Batch0854.certificate17096.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17068,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17069,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17070,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17071,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17073,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17075,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17077,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17078,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17080,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17082,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17088,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17090,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17094,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0854.sound17096,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/100),(31/1000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source365
