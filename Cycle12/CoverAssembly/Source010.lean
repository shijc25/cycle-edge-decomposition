import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0015
import Cycle12.RoutedCases.Batch0016

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source010

def strip0 : RatCoverRectangle := ⟨(11/1000),(9/800),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0015.certificate307.rectangle,RoutedCases.Batch0015.certificate309.rectangle,RoutedCases.Batch0015.certificate318.rectangle,RoutedCases.Batch0016.certificate320.rectangle,RoutedCases.Batch0016.certificate327.rectangle,RoutedCases.Batch0016.certificate328.rectangle,RoutedCases.Batch0016.certificate333.rectangle,RoutedCases.Batch0016.certificate334.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0015.sound307,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0015.sound309,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0015.sound318,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound320,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound327,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound328,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound333,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound334,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(9/800),(23/2000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0015.certificate308.rectangle,RoutedCases.Batch0015.certificate310.rectangle,RoutedCases.Batch0015.certificate319.rectangle,RoutedCases.Batch0016.certificate321.rectangle,RoutedCases.Batch0016.certificate327.rectangle,RoutedCases.Batch0016.certificate328.rectangle,RoutedCases.Batch0016.certificate333.rectangle,RoutedCases.Batch0016.certificate334.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0015.sound308,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0015.sound310,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0015.sound319,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound321,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound327,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound328,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound333,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound334,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(23/2000),(47/4000),1,(some 2)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0015.certificate311.rectangle,RoutedCases.Batch0015.certificate312.rectangle,RoutedCases.Batch0015.certificate315.rectangle,RoutedCases.Batch0016.certificate322.rectangle,RoutedCases.Batch0016.certificate325.rectangle,RoutedCases.Batch0016.certificate329.rectangle,RoutedCases.Batch0016.certificate331.rectangle,RoutedCases.Batch0016.certificate335.rectangle,RoutedCases.Batch0016.certificate337.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0015.sound311,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0015.sound312,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0015.sound315,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound322,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound325,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound329,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound331,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound335,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound337,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(47/4000),(3/250),1,(some 2)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0015.certificate313.rectangle,RoutedCases.Batch0015.certificate314.rectangle,RoutedCases.Batch0015.certificate316.rectangle,RoutedCases.Batch0015.certificate317.rectangle,RoutedCases.Batch0016.certificate323.rectangle,RoutedCases.Batch0016.certificate324.rectangle,RoutedCases.Batch0016.certificate326.rectangle,RoutedCases.Batch0016.certificate330.rectangle,RoutedCases.Batch0016.certificate332.rectangle,RoutedCases.Batch0016.certificate336.rectangle,RoutedCases.Batch0016.certificate338.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0015.sound313,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0015.sound314,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0015.sound316,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0015.sound317,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound323,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound324,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound326,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound330,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound332,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound336,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0016.sound338,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(11/1000),(3/250),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source010
