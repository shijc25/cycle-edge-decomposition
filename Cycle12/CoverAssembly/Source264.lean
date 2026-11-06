import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0736
import Cycle12.RoutedCases.Batch0737

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source264

def strip0 : RatCoverRectangle := ⟨(23/1000),(93/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0736.certificate14734.rectangle,RoutedCases.Batch0736.certificate14735.rectangle,RoutedCases.Batch0736.certificate14736.rectangle,RoutedCases.Batch0736.certificate14737.rectangle,RoutedCases.Batch0736.certificate14738.rectangle,RoutedCases.Batch0736.certificate14739.rectangle,RoutedCases.Batch0737.certificate14741.rectangle,RoutedCases.Batch0737.certificate14743.rectangle,RoutedCases.Batch0737.certificate14745.rectangle,RoutedCases.Batch0737.certificate14748.rectangle,RoutedCases.Batch0737.certificate14750.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14734,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14735,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14736,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14737,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14738,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14739,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14741,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14743,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14745,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14748,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14750,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(93/4000),(47/2000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0736.certificate14734.rectangle,RoutedCases.Batch0736.certificate14735.rectangle,RoutedCases.Batch0736.certificate14736.rectangle,RoutedCases.Batch0736.certificate14737.rectangle,RoutedCases.Batch0736.certificate14738.rectangle,RoutedCases.Batch0736.certificate14739.rectangle,RoutedCases.Batch0737.certificate14741.rectangle,RoutedCases.Batch0737.certificate14743.rectangle,RoutedCases.Batch0737.certificate14745.rectangle,RoutedCases.Batch0737.certificate14749.rectangle,RoutedCases.Batch0737.certificate14751.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14734,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14735,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14736,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14737,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14738,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14739,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14741,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14743,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14745,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14749,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14751,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(47/2000),(19/800),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0736.certificate14734.rectangle,RoutedCases.Batch0736.certificate14735.rectangle,RoutedCases.Batch0736.certificate14736.rectangle,RoutedCases.Batch0736.certificate14737.rectangle,RoutedCases.Batch0736.certificate14738.rectangle,RoutedCases.Batch0737.certificate14740.rectangle,RoutedCases.Batch0737.certificate14742.rectangle,RoutedCases.Batch0737.certificate14744.rectangle,RoutedCases.Batch0737.certificate14746.rectangle,RoutedCases.Batch0737.certificate14747.rectangle,RoutedCases.Batch0737.certificate14752.rectangle,RoutedCases.Batch0737.certificate14754.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14734,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14735,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14736,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14737,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14738,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14740,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14742,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14744,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14746,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14747,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14752,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14754,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(19/800),(3/125),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0736.certificate14734.rectangle,RoutedCases.Batch0736.certificate14735.rectangle,RoutedCases.Batch0736.certificate14736.rectangle,RoutedCases.Batch0736.certificate14737.rectangle,RoutedCases.Batch0736.certificate14738.rectangle,RoutedCases.Batch0737.certificate14740.rectangle,RoutedCases.Batch0737.certificate14742.rectangle,RoutedCases.Batch0737.certificate14744.rectangle,RoutedCases.Batch0737.certificate14746.rectangle,RoutedCases.Batch0737.certificate14747.rectangle,RoutedCases.Batch0737.certificate14753.rectangle,RoutedCases.Batch0737.certificate14755.rectangle,RoutedCases.Batch0737.certificate14756.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14734,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14735,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14736,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14737,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0736.sound14738,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14740,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14742,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14744,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14746,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14747,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14753,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14755,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14756,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(23/1000),(3/125),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source264
