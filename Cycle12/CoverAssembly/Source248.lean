import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0713
import Cycle12.RoutedCases.Batch0714
import Cycle12.RoutedCases.Batch0715

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source248

def strip0 : RatCoverRectangle := ⟨(1/125),(33/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0713.certificate14270.rectangle,RoutedCases.Batch0713.certificate14272.rectangle,RoutedCases.Batch0713.certificate14274.rectangle,RoutedCases.Batch0713.certificate14276.rectangle,RoutedCases.Batch0713.certificate14279.rectangle,RoutedCases.Batch0714.certificate14283.rectangle,RoutedCases.Batch0714.certificate14284.rectangle,RoutedCases.Batch0714.certificate14289.rectangle,RoutedCases.Batch0714.certificate14290.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14270,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14272,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14274,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14276,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14279,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14283,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14284,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14289,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14290,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(33/4000),(17/2000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0713.certificate14270.rectangle,RoutedCases.Batch0713.certificate14272.rectangle,RoutedCases.Batch0713.certificate14274.rectangle,RoutedCases.Batch0713.certificate14276.rectangle,RoutedCases.Batch0713.certificate14279.rectangle,RoutedCases.Batch0714.certificate14283.rectangle,RoutedCases.Batch0714.certificate14284.rectangle,RoutedCases.Batch0714.certificate14289.rectangle,RoutedCases.Batch0714.certificate14291.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14270,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14272,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14274,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14276,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14279,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14283,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14284,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14289,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14291,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(17/2000),(7/800),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0713.certificate14271.rectangle,RoutedCases.Batch0713.certificate14273.rectangle,RoutedCases.Batch0713.certificate14275.rectangle,RoutedCases.Batch0713.certificate14277.rectangle,RoutedCases.Batch0713.certificate14278.rectangle,RoutedCases.Batch0714.certificate14280.rectangle,RoutedCases.Batch0714.certificate14282.rectangle,RoutedCases.Batch0714.certificate14285.rectangle,RoutedCases.Batch0714.certificate14287.rectangle,RoutedCases.Batch0714.certificate14292.rectangle,RoutedCases.Batch0714.certificate14297.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14271,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14273,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14275,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14277,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14278,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14280,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14282,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14285,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14287,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14292,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14297,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(7/800),(71/8000),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0713.certificate14271.rectangle,RoutedCases.Batch0713.certificate14273.rectangle,RoutedCases.Batch0713.certificate14275.rectangle,RoutedCases.Batch0713.certificate14277.rectangle,RoutedCases.Batch0713.certificate14278.rectangle,RoutedCases.Batch0714.certificate14281.rectangle,RoutedCases.Batch0714.certificate14282.rectangle,RoutedCases.Batch0714.certificate14286.rectangle,RoutedCases.Batch0714.certificate14288.rectangle,RoutedCases.Batch0714.certificate14293.rectangle,RoutedCases.Batch0714.certificate14295.rectangle,RoutedCases.Batch0714.certificate14298.rectangle,RoutedCases.Batch0715.certificate14300.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14271,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14273,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14275,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14277,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14278,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14281,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14282,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14286,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14288,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14293,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14295,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14298,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14300,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(71/8000),(143/16000),5,(some 20)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0713.certificate14271.rectangle,RoutedCases.Batch0713.certificate14273.rectangle,RoutedCases.Batch0713.certificate14275.rectangle,RoutedCases.Batch0713.certificate14277.rectangle,RoutedCases.Batch0713.certificate14278.rectangle,RoutedCases.Batch0714.certificate14281.rectangle,RoutedCases.Batch0714.certificate14282.rectangle,RoutedCases.Batch0714.certificate14286.rectangle,RoutedCases.Batch0714.certificate14288.rectangle,RoutedCases.Batch0714.certificate14294.rectangle,RoutedCases.Batch0714.certificate14296.rectangle,RoutedCases.Batch0714.certificate14299.rectangle,RoutedCases.Batch0715.certificate14301.rectangle,RoutedCases.Batch0715.certificate14302.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14271,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14273,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14275,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14277,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14278,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14281,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14282,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14286,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14288,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14294,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14296,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14299,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14301,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14302,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(143/16000),(9/1000),5,(some 20)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0713.certificate14271.rectangle,RoutedCases.Batch0713.certificate14273.rectangle,RoutedCases.Batch0713.certificate14275.rectangle,RoutedCases.Batch0713.certificate14277.rectangle,RoutedCases.Batch0713.certificate14278.rectangle,RoutedCases.Batch0714.certificate14281.rectangle,RoutedCases.Batch0714.certificate14282.rectangle,RoutedCases.Batch0714.certificate14286.rectangle,RoutedCases.Batch0714.certificate14288.rectangle,RoutedCases.Batch0714.certificate14294.rectangle,RoutedCases.Batch0714.certificate14296.rectangle,RoutedCases.Batch0714.certificate14299.rectangle,RoutedCases.Batch0715.certificate14301.rectangle,RoutedCases.Batch0715.certificate14303.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14271,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14273,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14275,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14277,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14278,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14281,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14282,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14286,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14288,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14294,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14296,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0714.sound14299,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14301,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14303,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/125),(9/1000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source248
