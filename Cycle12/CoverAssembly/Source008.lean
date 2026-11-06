import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0006
import Cycle12.RoutedCases.Batch0007
import Cycle12.RoutedCases.Batch0008
import Cycle12.RoutedCases.Batch0009

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source008

def strip0 : RatCoverRectangle := ⟨(9/1000),(37/4000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0006.certificate122.rectangle,RoutedCases.Batch0006.certificate125.rectangle,RoutedCases.Batch0007.certificate146.rectangle,RoutedCases.Batch0007.certificate148.rectangle,RoutedCases.Batch0008.certificate162.rectangle,RoutedCases.Batch0008.certificate164.rectangle,RoutedCases.Batch0008.certificate178.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound122,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound125,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound146,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound148,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound162,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound164,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound178,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(37/4000),(19/2000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0006.certificate123.rectangle,RoutedCases.Batch0006.certificate124.rectangle,RoutedCases.Batch0006.certificate126.rectangle,RoutedCases.Batch0006.certificate127.rectangle,RoutedCases.Batch0007.certificate147.rectangle,RoutedCases.Batch0007.certificate149.rectangle,RoutedCases.Batch0008.certificate163.rectangle,RoutedCases.Batch0008.certificate165.rectangle,RoutedCases.Batch0008.certificate179.rectangle,RoutedCases.Batch0009.certificate180.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound123,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound124,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound126,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound127,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound147,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound149,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound163,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound165,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound179,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0009.sound180,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(19/2000),(77/8000),1,(some 2)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0006.certificate128.rectangle,RoutedCases.Batch0006.certificate130.rectangle,RoutedCases.Batch0006.certificate138.rectangle,RoutedCases.Batch0007.certificate140.rectangle,RoutedCases.Batch0007.certificate150.rectangle,RoutedCases.Batch0007.certificate151.rectangle,RoutedCases.Batch0007.certificate156.rectangle,RoutedCases.Batch0007.certificate157.rectangle,RoutedCases.Batch0008.certificate166.rectangle,RoutedCases.Batch0008.certificate167.rectangle,RoutedCases.Batch0008.certificate172.rectangle,RoutedCases.Batch0008.certificate173.rectangle,RoutedCases.Batch0009.certificate181.rectangle,RoutedCases.Batch0009.certificate183.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound128,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound130,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound138,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound140,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound150,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound151,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound156,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound157,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound166,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound167,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound172,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound173,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0009.sound181,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0009.sound183,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(77/8000),(39/4000),1,(some 2)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0006.certificate129.rectangle,RoutedCases.Batch0006.certificate131.rectangle,RoutedCases.Batch0006.certificate139.rectangle,RoutedCases.Batch0007.certificate140.rectangle,RoutedCases.Batch0007.certificate150.rectangle,RoutedCases.Batch0007.certificate151.rectangle,RoutedCases.Batch0007.certificate156.rectangle,RoutedCases.Batch0007.certificate157.rectangle,RoutedCases.Batch0008.certificate166.rectangle,RoutedCases.Batch0008.certificate167.rectangle,RoutedCases.Batch0008.certificate172.rectangle,RoutedCases.Batch0008.certificate173.rectangle,RoutedCases.Batch0009.certificate182.rectangle,RoutedCases.Batch0009.certificate184.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound129,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound131,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound139,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound140,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound150,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound151,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound156,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound157,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound166,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound167,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound172,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound173,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0009.sound182,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0009.sound184,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(39/4000),(79/8000),1,(some 2)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0006.certificate132.rectangle,RoutedCases.Batch0006.certificate135.rectangle,RoutedCases.Batch0007.certificate141.rectangle,RoutedCases.Batch0007.certificate144.rectangle,RoutedCases.Batch0007.certificate152.rectangle,RoutedCases.Batch0007.certificate154.rectangle,RoutedCases.Batch0007.certificate158.rectangle,RoutedCases.Batch0008.certificate160.rectangle,RoutedCases.Batch0008.certificate168.rectangle,RoutedCases.Batch0008.certificate170.rectangle,RoutedCases.Batch0008.certificate174.rectangle,RoutedCases.Batch0008.certificate176.rectangle,RoutedCases.Batch0009.certificate185.rectangle,RoutedCases.Batch0009.certificate188.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound132,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound135,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound141,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound144,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound152,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound154,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound158,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound160,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound168,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound170,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound174,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound176,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0009.sound185,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0009.sound188,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(79/8000),(1/100),1,(some 2)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0006.certificate133.rectangle,RoutedCases.Batch0006.certificate134.rectangle,RoutedCases.Batch0006.certificate136.rectangle,RoutedCases.Batch0006.certificate137.rectangle,RoutedCases.Batch0007.certificate142.rectangle,RoutedCases.Batch0007.certificate143.rectangle,RoutedCases.Batch0007.certificate145.rectangle,RoutedCases.Batch0007.certificate153.rectangle,RoutedCases.Batch0007.certificate155.rectangle,RoutedCases.Batch0007.certificate159.rectangle,RoutedCases.Batch0008.certificate161.rectangle,RoutedCases.Batch0008.certificate169.rectangle,RoutedCases.Batch0008.certificate171.rectangle,RoutedCases.Batch0008.certificate175.rectangle,RoutedCases.Batch0008.certificate177.rectangle,RoutedCases.Batch0009.certificate186.rectangle,RoutedCases.Batch0009.certificate187.rectangle,RoutedCases.Batch0009.certificate189.rectangle,RoutedCases.Batch0009.certificate190.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound133,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound134,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound136,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0006.sound137,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound142,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound143,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound145,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound153,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound155,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0007.sound159,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound161,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound169,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound171,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound175,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0008.sound177,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0009.sound186,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0009.sound187,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0009.sound189,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0009.sound190,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(9/1000),(1/100),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source008
