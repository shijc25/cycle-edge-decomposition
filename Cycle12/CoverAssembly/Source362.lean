import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0849
import Cycle12.RoutedCases.Batch0850

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source362

def strip0 : RatCoverRectangle := ⟨(27/1000),(109/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0849.certificate16988.rectangle,RoutedCases.Batch0849.certificate16989.rectangle,RoutedCases.Batch0849.certificate16990.rectangle,RoutedCases.Batch0849.certificate16991.rectangle,RoutedCases.Batch0849.certificate16992.rectangle,RoutedCases.Batch0849.certificate16994.rectangle,RoutedCases.Batch0849.certificate16996.rectangle,RoutedCases.Batch0850.certificate17000.rectangle,RoutedCases.Batch0850.certificate17005.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16988,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16989,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16990,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16991,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16992,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16994,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16996,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17000,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17005,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(109/4000),(11/400),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0849.certificate16988.rectangle,RoutedCases.Batch0849.certificate16989.rectangle,RoutedCases.Batch0849.certificate16990.rectangle,RoutedCases.Batch0849.certificate16991.rectangle,RoutedCases.Batch0849.certificate16992.rectangle,RoutedCases.Batch0849.certificate16994.rectangle,RoutedCases.Batch0849.certificate16996.rectangle,RoutedCases.Batch0850.certificate17000.rectangle,RoutedCases.Batch0850.certificate17006.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16988,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16989,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16990,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16991,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16992,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16994,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16996,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17000,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17006,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(11/400),(221/8000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0849.certificate16988.rectangle,RoutedCases.Batch0849.certificate16989.rectangle,RoutedCases.Batch0849.certificate16990.rectangle,RoutedCases.Batch0849.certificate16991.rectangle,RoutedCases.Batch0849.certificate16993.rectangle,RoutedCases.Batch0849.certificate16995.rectangle,RoutedCases.Batch0849.certificate16997.rectangle,RoutedCases.Batch0849.certificate16998.rectangle,RoutedCases.Batch0850.certificate17001.rectangle,RoutedCases.Batch0850.certificate17003.rectangle,RoutedCases.Batch0850.certificate17007.rectangle,RoutedCases.Batch0850.certificate17008.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16988,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16989,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16990,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16991,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16993,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16995,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16997,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16998,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17001,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17003,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17007,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17008,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(221/8000),(111/4000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0849.certificate16988.rectangle,RoutedCases.Batch0849.certificate16989.rectangle,RoutedCases.Batch0849.certificate16990.rectangle,RoutedCases.Batch0849.certificate16991.rectangle,RoutedCases.Batch0849.certificate16993.rectangle,RoutedCases.Batch0849.certificate16995.rectangle,RoutedCases.Batch0849.certificate16997.rectangle,RoutedCases.Batch0849.certificate16998.rectangle,RoutedCases.Batch0850.certificate17001.rectangle,RoutedCases.Batch0850.certificate17003.rectangle,RoutedCases.Batch0850.certificate17007.rectangle,RoutedCases.Batch0850.certificate17009.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16988,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16989,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16990,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16991,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16993,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16995,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16997,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16998,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17001,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17003,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17007,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17009,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(111/4000),(223/8000),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0849.certificate16988.rectangle,RoutedCases.Batch0849.certificate16989.rectangle,RoutedCases.Batch0849.certificate16990.rectangle,RoutedCases.Batch0849.certificate16991.rectangle,RoutedCases.Batch0849.certificate16993.rectangle,RoutedCases.Batch0849.certificate16995.rectangle,RoutedCases.Batch0849.certificate16997.rectangle,RoutedCases.Batch0849.certificate16999.rectangle,RoutedCases.Batch0850.certificate17002.rectangle,RoutedCases.Batch0850.certificate17004.rectangle,RoutedCases.Batch0850.certificate17010.rectangle,RoutedCases.Batch0850.certificate17012.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16988,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16989,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16990,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16991,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16993,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16995,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16997,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16999,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17002,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17004,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17010,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17012,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(223/8000),(7/250),20,(some 100)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0849.certificate16988.rectangle,RoutedCases.Batch0849.certificate16989.rectangle,RoutedCases.Batch0849.certificate16990.rectangle,RoutedCases.Batch0849.certificate16991.rectangle,RoutedCases.Batch0849.certificate16993.rectangle,RoutedCases.Batch0849.certificate16995.rectangle,RoutedCases.Batch0849.certificate16997.rectangle,RoutedCases.Batch0849.certificate16999.rectangle,RoutedCases.Batch0850.certificate17002.rectangle,RoutedCases.Batch0850.certificate17004.rectangle,RoutedCases.Batch0850.certificate17011.rectangle,RoutedCases.Batch0850.certificate17013.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16988,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16989,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16990,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16991,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16993,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16995,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16997,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16999,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17002,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17004,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17011,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0850.sound17013,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(27/1000),(7/250),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source362
