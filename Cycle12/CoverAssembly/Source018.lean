import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0035
import Cycle12.RoutedCases.Batch0036
import Cycle12.RoutedCases.Batch0037
import Cycle12.RoutedCases.Batch0038

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source018

def strip0 : RatCoverRectangle := ⟨(19/1000),(77/4000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0035.certificate713.rectangle,RoutedCases.Batch0035.certificate715.rectangle,RoutedCases.Batch0036.certificate722.rectangle,RoutedCases.Batch0036.certificate724.rectangle,RoutedCases.Batch0036.certificate730.rectangle,RoutedCases.Batch0036.certificate732.rectangle,RoutedCases.Batch0036.certificate738.rectangle,RoutedCases.Batch0037.certificate740.rectangle,RoutedCases.Batch0037.certificate746.rectangle,RoutedCases.Batch0037.certificate747.rectangle,RoutedCases.Batch0037.certificate752.rectangle,RoutedCases.Batch0037.certificate753.rectangle,RoutedCases.Batch0037.certificate758.rectangle,RoutedCases.Batch0038.certificate760.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound713,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound715,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound722,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound724,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound730,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound732,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound738,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound740,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound746,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound747,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound752,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound753,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound758,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0038.sound760,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(77/4000),(39/2000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0035.certificate714.rectangle,RoutedCases.Batch0035.certificate716.rectangle,RoutedCases.Batch0036.certificate723.rectangle,RoutedCases.Batch0036.certificate725.rectangle,RoutedCases.Batch0036.certificate731.rectangle,RoutedCases.Batch0036.certificate733.rectangle,RoutedCases.Batch0036.certificate739.rectangle,RoutedCases.Batch0037.certificate741.rectangle,RoutedCases.Batch0037.certificate746.rectangle,RoutedCases.Batch0037.certificate747.rectangle,RoutedCases.Batch0037.certificate752.rectangle,RoutedCases.Batch0037.certificate753.rectangle,RoutedCases.Batch0037.certificate759.rectangle,RoutedCases.Batch0038.certificate761.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound714,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound716,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound723,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound725,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound731,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound733,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound739,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound741,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound746,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound747,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound752,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound753,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound759,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0038.sound761,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(39/2000),(79/4000),1,(some 2)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0035.certificate717.rectangle,RoutedCases.Batch0036.certificate720.rectangle,RoutedCases.Batch0036.certificate726.rectangle,RoutedCases.Batch0036.certificate728.rectangle,RoutedCases.Batch0036.certificate734.rectangle,RoutedCases.Batch0036.certificate736.rectangle,RoutedCases.Batch0037.certificate742.rectangle,RoutedCases.Batch0037.certificate744.rectangle,RoutedCases.Batch0037.certificate748.rectangle,RoutedCases.Batch0037.certificate750.rectangle,RoutedCases.Batch0037.certificate754.rectangle,RoutedCases.Batch0037.certificate756.rectangle,RoutedCases.Batch0038.certificate762.rectangle,RoutedCases.Batch0038.certificate764.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound717,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound720,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound726,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound728,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound734,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound736,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound742,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound744,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound748,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound750,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound754,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound756,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0038.sound762,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0038.sound764,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(79/4000),(1/50),1,(some 2)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0035.certificate718.rectangle,RoutedCases.Batch0035.certificate719.rectangle,RoutedCases.Batch0036.certificate721.rectangle,RoutedCases.Batch0036.certificate727.rectangle,RoutedCases.Batch0036.certificate729.rectangle,RoutedCases.Batch0036.certificate735.rectangle,RoutedCases.Batch0036.certificate737.rectangle,RoutedCases.Batch0037.certificate743.rectangle,RoutedCases.Batch0037.certificate745.rectangle,RoutedCases.Batch0037.certificate749.rectangle,RoutedCases.Batch0037.certificate751.rectangle,RoutedCases.Batch0037.certificate755.rectangle,RoutedCases.Batch0037.certificate757.rectangle,RoutedCases.Batch0038.certificate763.rectangle,RoutedCases.Batch0038.certificate765.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound718,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound719,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound721,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound727,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound729,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound735,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0036.sound737,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound743,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound745,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound749,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound751,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound755,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0037.sound757,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0038.sound763,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0038.sound765,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(19/1000),(1/50),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source018
