import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0905
import Cycle12.RoutedCases.Batch0906

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source402

def strip0 : RatCoverRectangle := ⟨(61/1000),(489/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0905.certificate18105.rectangle,RoutedCases.Batch0905.certificate18106.rectangle,RoutedCases.Batch0905.certificate18107.rectangle,RoutedCases.Batch0905.certificate18108.rectangle,RoutedCases.Batch0905.certificate18109.rectangle,RoutedCases.Batch0905.certificate18110.rectangle,RoutedCases.Batch0905.certificate18112.rectangle,RoutedCases.Batch0905.certificate18114.rectangle,RoutedCases.Batch0905.certificate18116.rectangle,RoutedCases.Batch0905.certificate18118.rectangle,RoutedCases.Batch0906.certificate18120.rectangle,RoutedCases.Batch0906.certificate18122.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18105,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18106,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18107,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18108,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18109,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18110,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18112,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18114,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18116,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18118,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18120,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18122,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(489/8000),(979/16000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0905.certificate18105.rectangle,RoutedCases.Batch0905.certificate18106.rectangle,RoutedCases.Batch0905.certificate18107.rectangle,RoutedCases.Batch0905.certificate18108.rectangle,RoutedCases.Batch0905.certificate18109.rectangle,RoutedCases.Batch0905.certificate18110.rectangle,RoutedCases.Batch0905.certificate18112.rectangle,RoutedCases.Batch0905.certificate18115.rectangle,RoutedCases.Batch0905.certificate18116.rectangle,RoutedCases.Batch0905.certificate18118.rectangle,RoutedCases.Batch0906.certificate18121.rectangle,RoutedCases.Batch0906.certificate18123.rectangle,RoutedCases.Batch0906.certificate18124.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18105,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18106,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18107,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18108,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18109,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18110,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18112,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18115,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18116,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18118,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18121,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18123,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18124,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(979/16000),(49/800),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0905.certificate18105.rectangle,RoutedCases.Batch0905.certificate18106.rectangle,RoutedCases.Batch0905.certificate18107.rectangle,RoutedCases.Batch0905.certificate18108.rectangle,RoutedCases.Batch0905.certificate18109.rectangle,RoutedCases.Batch0905.certificate18110.rectangle,RoutedCases.Batch0905.certificate18112.rectangle,RoutedCases.Batch0905.certificate18115.rectangle,RoutedCases.Batch0905.certificate18116.rectangle,RoutedCases.Batch0905.certificate18118.rectangle,RoutedCases.Batch0906.certificate18121.rectangle,RoutedCases.Batch0906.certificate18123.rectangle,RoutedCases.Batch0906.certificate18125.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18105,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18106,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18107,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18108,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18109,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18110,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18112,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18115,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18116,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18118,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18121,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18123,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18125,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(49/800),(123/2000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0905.certificate18105.rectangle,RoutedCases.Batch0905.certificate18106.rectangle,RoutedCases.Batch0905.certificate18107.rectangle,RoutedCases.Batch0905.certificate18108.rectangle,RoutedCases.Batch0905.certificate18109.rectangle,RoutedCases.Batch0905.certificate18111.rectangle,RoutedCases.Batch0905.certificate18113.rectangle,RoutedCases.Batch0905.certificate18117.rectangle,RoutedCases.Batch0905.certificate18119.rectangle,RoutedCases.Batch0906.certificate18126.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18105,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18106,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18107,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18108,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18109,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18111,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18113,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18117,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18119,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18126,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(61/1000),(123/2000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source402
