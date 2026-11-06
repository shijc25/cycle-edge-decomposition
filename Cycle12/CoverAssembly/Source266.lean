import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0739
import Cycle12.RoutedCases.Batch0740

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source266

def strip0 : RatCoverRectangle := ⟨(1/40),(101/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0739.certificate14780.rectangle,RoutedCases.Batch0739.certificate14781.rectangle,RoutedCases.Batch0739.certificate14782.rectangle,RoutedCases.Batch0739.certificate14783.rectangle,RoutedCases.Batch0739.certificate14784.rectangle,RoutedCases.Batch0739.certificate14785.rectangle,RoutedCases.Batch0739.certificate14787.rectangle,RoutedCases.Batch0739.certificate14789.rectangle,RoutedCases.Batch0739.certificate14791.rectangle,RoutedCases.Batch0739.certificate14795.rectangle,RoutedCases.Batch0739.certificate14797.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14780,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14781,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14782,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14783,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14784,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14785,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14787,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14789,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14791,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14795,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14797,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(101/4000),(51/2000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0739.certificate14780.rectangle,RoutedCases.Batch0739.certificate14781.rectangle,RoutedCases.Batch0739.certificate14782.rectangle,RoutedCases.Batch0739.certificate14783.rectangle,RoutedCases.Batch0739.certificate14784.rectangle,RoutedCases.Batch0739.certificate14785.rectangle,RoutedCases.Batch0739.certificate14787.rectangle,RoutedCases.Batch0739.certificate14789.rectangle,RoutedCases.Batch0739.certificate14791.rectangle,RoutedCases.Batch0739.certificate14796.rectangle,RoutedCases.Batch0739.certificate14798.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14780,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14781,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14782,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14783,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14784,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14785,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14787,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14789,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14791,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14796,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14798,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(51/2000),(103/4000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0739.certificate14780.rectangle,RoutedCases.Batch0739.certificate14781.rectangle,RoutedCases.Batch0739.certificate14782.rectangle,RoutedCases.Batch0739.certificate14783.rectangle,RoutedCases.Batch0739.certificate14784.rectangle,RoutedCases.Batch0739.certificate14786.rectangle,RoutedCases.Batch0739.certificate14788.rectangle,RoutedCases.Batch0739.certificate14790.rectangle,RoutedCases.Batch0739.certificate14792.rectangle,RoutedCases.Batch0739.certificate14793.rectangle,RoutedCases.Batch0739.certificate14799.rectangle,RoutedCases.Batch0740.certificate14801.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14780,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14781,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14782,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14783,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14784,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14786,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14788,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14790,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14792,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14793,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14799,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14801,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(103/4000),(13/500),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0739.certificate14780.rectangle,RoutedCases.Batch0739.certificate14781.rectangle,RoutedCases.Batch0739.certificate14782.rectangle,RoutedCases.Batch0739.certificate14783.rectangle,RoutedCases.Batch0739.certificate14784.rectangle,RoutedCases.Batch0739.certificate14786.rectangle,RoutedCases.Batch0739.certificate14788.rectangle,RoutedCases.Batch0739.certificate14790.rectangle,RoutedCases.Batch0739.certificate14792.rectangle,RoutedCases.Batch0739.certificate14794.rectangle,RoutedCases.Batch0740.certificate14800.rectangle,RoutedCases.Batch0740.certificate14802.rectangle,RoutedCases.Batch0740.certificate14803.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14780,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14781,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14782,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14783,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14784,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14786,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14788,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14790,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14792,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0739.sound14794,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14800,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14802,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0740.sound14803,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/40),(13/500),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source266
