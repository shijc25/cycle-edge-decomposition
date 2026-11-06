import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0863
import Cycle12.RoutedCases.Batch0864
import Cycle12.RoutedCases.Batch0865

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source371

def strip0 : RatCoverRectangle := ⟨(9/250),(29/800),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0863.certificate17275.rectangle,RoutedCases.Batch0863.certificate17276.rectangle,RoutedCases.Batch0863.certificate17277.rectangle,RoutedCases.Batch0863.certificate17278.rectangle,RoutedCases.Batch0863.certificate17279.rectangle,RoutedCases.Batch0864.certificate17281.rectangle,RoutedCases.Batch0864.certificate17283.rectangle,RoutedCases.Batch0864.certificate17284.rectangle,RoutedCases.Batch0864.certificate17289.rectangle,RoutedCases.Batch0864.certificate17291.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17275,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17276,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17277,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17278,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17279,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17281,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17283,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17284,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17289,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17291,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(29/800),(73/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0863.certificate17275.rectangle,RoutedCases.Batch0863.certificate17276.rectangle,RoutedCases.Batch0863.certificate17277.rectangle,RoutedCases.Batch0863.certificate17278.rectangle,RoutedCases.Batch0863.certificate17279.rectangle,RoutedCases.Batch0864.certificate17281.rectangle,RoutedCases.Batch0864.certificate17283.rectangle,RoutedCases.Batch0864.certificate17285.rectangle,RoutedCases.Batch0864.certificate17290.rectangle,RoutedCases.Batch0864.certificate17292.rectangle,RoutedCases.Batch0864.certificate17293.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17275,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17276,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17277,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17278,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17279,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17281,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17283,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17285,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17290,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17292,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17293,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(73/2000),(293/8000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0863.certificate17275.rectangle,RoutedCases.Batch0863.certificate17276.rectangle,RoutedCases.Batch0863.certificate17277.rectangle,RoutedCases.Batch0863.certificate17278.rectangle,RoutedCases.Batch0864.certificate17280.rectangle,RoutedCases.Batch0864.certificate17282.rectangle,RoutedCases.Batch0864.certificate17286.rectangle,RoutedCases.Batch0864.certificate17287.rectangle,RoutedCases.Batch0864.certificate17294.rectangle,RoutedCases.Batch0864.certificate17298.rectangle,RoutedCases.Batch0865.certificate17300.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17275,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17276,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17277,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17278,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17280,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17282,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17286,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17287,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17294,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17298,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0865.sound17300,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(293/8000),(147/4000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0863.certificate17275.rectangle,RoutedCases.Batch0863.certificate17276.rectangle,RoutedCases.Batch0863.certificate17277.rectangle,RoutedCases.Batch0863.certificate17278.rectangle,RoutedCases.Batch0864.certificate17280.rectangle,RoutedCases.Batch0864.certificate17282.rectangle,RoutedCases.Batch0864.certificate17286.rectangle,RoutedCases.Batch0864.certificate17287.rectangle,RoutedCases.Batch0864.certificate17294.rectangle,RoutedCases.Batch0864.certificate17299.rectangle,RoutedCases.Batch0865.certificate17301.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17275,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17276,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17277,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17278,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17280,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17282,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17286,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17287,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17294,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17299,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0865.sound17301,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(147/4000),(59/1600),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0863.certificate17275.rectangle,RoutedCases.Batch0863.certificate17276.rectangle,RoutedCases.Batch0863.certificate17277.rectangle,RoutedCases.Batch0863.certificate17278.rectangle,RoutedCases.Batch0864.certificate17280.rectangle,RoutedCases.Batch0864.certificate17282.rectangle,RoutedCases.Batch0864.certificate17286.rectangle,RoutedCases.Batch0864.certificate17288.rectangle,RoutedCases.Batch0864.certificate17295.rectangle,RoutedCases.Batch0864.certificate17296.rectangle,RoutedCases.Batch0865.certificate17302.rectangle,RoutedCases.Batch0865.certificate17304.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17275,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17276,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17277,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17278,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17280,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17282,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17286,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17288,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17295,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17296,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0865.sound17302,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0865.sound17304,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(59/1600),(37/1000),20,(some 100)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0863.certificate17275.rectangle,RoutedCases.Batch0863.certificate17276.rectangle,RoutedCases.Batch0863.certificate17277.rectangle,RoutedCases.Batch0863.certificate17278.rectangle,RoutedCases.Batch0864.certificate17280.rectangle,RoutedCases.Batch0864.certificate17282.rectangle,RoutedCases.Batch0864.certificate17286.rectangle,RoutedCases.Batch0864.certificate17288.rectangle,RoutedCases.Batch0864.certificate17295.rectangle,RoutedCases.Batch0864.certificate17297.rectangle,RoutedCases.Batch0865.certificate17303.rectangle,RoutedCases.Batch0865.certificate17305.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17275,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17276,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17277,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0863.sound17278,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17280,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17282,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17286,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17288,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17295,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0864.sound17297,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0865.sound17303,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0865.sound17305,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(9/250),(37/1000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source371
