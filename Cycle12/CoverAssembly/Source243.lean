import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0709
import Cycle12.RoutedCases.Batch0710

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source243

def strip0 : RatCoverRectangle := ⟨(1/250),(17/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0709.certificate14180.rectangle,RoutedCases.Batch0709.certificate14185.rectangle,RoutedCases.Batch0709.certificate14188.rectangle,RoutedCases.Batch0709.certificate14189.rectangle,RoutedCases.Batch0709.certificate14194.rectangle,RoutedCases.Batch0709.certificate14196.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14180,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14185,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14188,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14189,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14194,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14196,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(17/4000),(9/2000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0709.certificate14180.rectangle,RoutedCases.Batch0709.certificate14185.rectangle,RoutedCases.Batch0709.certificate14188.rectangle,RoutedCases.Batch0709.certificate14189.rectangle,RoutedCases.Batch0709.certificate14195.rectangle,RoutedCases.Batch0709.certificate14197.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14180,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14185,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14188,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14189,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14195,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14197,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(9/2000),(37/8000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0709.certificate14181.rectangle,RoutedCases.Batch0709.certificate14183.rectangle,RoutedCases.Batch0709.certificate14186.rectangle,RoutedCases.Batch0709.certificate14190.rectangle,RoutedCases.Batch0709.certificate14192.rectangle,RoutedCases.Batch0709.certificate14198.rectangle,RoutedCases.Batch0710.certificate14203.rectangle,RoutedCases.Batch0710.certificate14204.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14181,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14183,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14186,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14190,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14192,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14198,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14203,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14204,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(37/8000),(19/4000),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0709.certificate14181.rectangle,RoutedCases.Batch0709.certificate14183.rectangle,RoutedCases.Batch0709.certificate14186.rectangle,RoutedCases.Batch0709.certificate14190.rectangle,RoutedCases.Batch0709.certificate14192.rectangle,RoutedCases.Batch0709.certificate14198.rectangle,RoutedCases.Batch0710.certificate14203.rectangle,RoutedCases.Batch0710.certificate14205.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14181,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14183,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14186,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14190,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14192,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14198,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14203,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14205,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(19/4000),(39/8000),5,(some 20)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0709.certificate14182.rectangle,RoutedCases.Batch0709.certificate14184.rectangle,RoutedCases.Batch0709.certificate14187.rectangle,RoutedCases.Batch0709.certificate14191.rectangle,RoutedCases.Batch0709.certificate14193.rectangle,RoutedCases.Batch0709.certificate14199.rectangle,RoutedCases.Batch0710.certificate14201.rectangle,RoutedCases.Batch0710.certificate14206.rectangle,RoutedCases.Batch0710.certificate14208.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14182,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14184,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14187,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14191,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14193,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14199,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14201,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14206,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14208,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(39/8000),(79/16000),5,(some 20)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0709.certificate14182.rectangle,RoutedCases.Batch0709.certificate14184.rectangle,RoutedCases.Batch0709.certificate14187.rectangle,RoutedCases.Batch0709.certificate14191.rectangle,RoutedCases.Batch0709.certificate14193.rectangle,RoutedCases.Batch0710.certificate14200.rectangle,RoutedCases.Batch0710.certificate14202.rectangle,RoutedCases.Batch0710.certificate14207.rectangle,RoutedCases.Batch0710.certificate14209.rectangle,RoutedCases.Batch0710.certificate14211.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14182,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14184,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14187,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14191,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14193,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14200,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14202,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14207,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14209,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14211,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip6 : RatCoverRectangle := ⟨(79/16000),(1/200),5,(some 20)⟩
def pieces6 : List RatCoverRectangle := [RoutedCases.Batch0709.certificate14182.rectangle,RoutedCases.Batch0709.certificate14184.rectangle,RoutedCases.Batch0709.certificate14187.rectangle,RoutedCases.Batch0709.certificate14191.rectangle,RoutedCases.Batch0709.certificate14193.rectangle,RoutedCases.Batch0710.certificate14200.rectangle,RoutedCases.Batch0710.certificate14202.rectangle,RoutedCases.Batch0710.certificate14207.rectangle,RoutedCases.Batch0710.certificate14210.rectangle,RoutedCases.Batch0710.certificate14212.rectangle]
theorem valid6 : strip6.JoinS pieces6 := by decide +kernel
theorem sound6 : strip6.Sound := rat_cover_join_s_sound strip6 pieces6 valid6 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14182,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14184,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14187,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14191,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0709.sound14193,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14200,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14202,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14207,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14210,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0710.sound14212,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/250),(1/200),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5,strip6]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_cons.mpr ⟨sound6,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source243
