import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0814
import Cycle12.RoutedCases.Batch0815

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source322

def strip0 : RatCoverRectangle := ⟨(13/200),(521/8000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0814.certificate16283.rectangle,RoutedCases.Batch0814.certificate16284.rectangle,RoutedCases.Batch0814.certificate16285.rectangle,RoutedCases.Batch0814.certificate16286.rectangle,RoutedCases.Batch0814.certificate16287.rectangle,RoutedCases.Batch0814.certificate16288.rectangle,RoutedCases.Batch0814.certificate16289.rectangle,RoutedCases.Batch0814.certificate16290.rectangle,RoutedCases.Batch0814.certificate16291.rectangle,RoutedCases.Batch0814.certificate16293.rectangle,RoutedCases.Batch0814.certificate16295.rectangle,RoutedCases.Batch0814.certificate16297.rectangle,RoutedCases.Batch0814.certificate16298.rectangle,RoutedCases.Batch0815.certificate16301.rectangle,RoutedCases.Batch0815.certificate16303.rectangle,RoutedCases.Batch0815.certificate16305.rectangle,RoutedCases.Batch0815.certificate16306.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16283,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16284,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16285,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16286,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16287,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16288,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16289,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16290,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16291,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16293,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16295,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16297,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16298,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16301,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16303,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16305,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16306,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(521/8000),(261/4000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0814.certificate16283.rectangle,RoutedCases.Batch0814.certificate16284.rectangle,RoutedCases.Batch0814.certificate16285.rectangle,RoutedCases.Batch0814.certificate16286.rectangle,RoutedCases.Batch0814.certificate16287.rectangle,RoutedCases.Batch0814.certificate16288.rectangle,RoutedCases.Batch0814.certificate16289.rectangle,RoutedCases.Batch0814.certificate16290.rectangle,RoutedCases.Batch0814.certificate16291.rectangle,RoutedCases.Batch0814.certificate16293.rectangle,RoutedCases.Batch0814.certificate16295.rectangle,RoutedCases.Batch0814.certificate16297.rectangle,RoutedCases.Batch0814.certificate16299.rectangle,RoutedCases.Batch0815.certificate16302.rectangle,RoutedCases.Batch0815.certificate16303.rectangle,RoutedCases.Batch0815.certificate16305.rectangle,RoutedCases.Batch0815.certificate16307.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16283,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16284,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16285,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16286,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16287,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16288,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16289,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16290,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16291,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16293,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16295,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16297,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16299,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16302,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16303,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16305,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16307,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(261/4000),(131/2000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0814.certificate16283.rectangle,RoutedCases.Batch0814.certificate16284.rectangle,RoutedCases.Batch0814.certificate16285.rectangle,RoutedCases.Batch0814.certificate16286.rectangle,RoutedCases.Batch0814.certificate16287.rectangle,RoutedCases.Batch0814.certificate16288.rectangle,RoutedCases.Batch0814.certificate16289.rectangle,RoutedCases.Batch0814.certificate16290.rectangle,RoutedCases.Batch0814.certificate16292.rectangle,RoutedCases.Batch0814.certificate16294.rectangle,RoutedCases.Batch0814.certificate16296.rectangle,RoutedCases.Batch0815.certificate16300.rectangle,RoutedCases.Batch0815.certificate16304.rectangle,RoutedCases.Batch0815.certificate16308.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16283,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16284,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16285,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16286,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16287,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16288,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16289,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16290,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16292,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16294,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0814.sound16296,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16300,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16304,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16308,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(13/200),(131/2000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source322
