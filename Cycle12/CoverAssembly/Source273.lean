import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0749
import Cycle12.RoutedCases.Batch0750

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source273

def strip0 : RatCoverRectangle := ⟨(4/125),(129/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0749.certificate14985.rectangle,RoutedCases.Batch0749.certificate14986.rectangle,RoutedCases.Batch0749.certificate14987.rectangle,RoutedCases.Batch0749.certificate14988.rectangle,RoutedCases.Batch0749.certificate14989.rectangle,RoutedCases.Batch0749.certificate14990.rectangle,RoutedCases.Batch0749.certificate14992.rectangle,RoutedCases.Batch0749.certificate14994.rectangle,RoutedCases.Batch0749.certificate14996.rectangle,RoutedCases.Batch0749.certificate14998.rectangle,RoutedCases.Batch0749.certificate14999.rectangle,RoutedCases.Batch0750.certificate15005.rectangle,RoutedCases.Batch0750.certificate15007.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14985,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14986,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14987,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14988,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14989,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14990,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14992,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14994,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14996,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14998,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14999,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0750.sound15005,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0750.sound15007,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(129/4000),(13/400),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0749.certificate14985.rectangle,RoutedCases.Batch0749.certificate14986.rectangle,RoutedCases.Batch0749.certificate14987.rectangle,RoutedCases.Batch0749.certificate14988.rectangle,RoutedCases.Batch0749.certificate14989.rectangle,RoutedCases.Batch0749.certificate14990.rectangle,RoutedCases.Batch0749.certificate14992.rectangle,RoutedCases.Batch0749.certificate14994.rectangle,RoutedCases.Batch0749.certificate14996.rectangle,RoutedCases.Batch0749.certificate14998.rectangle,RoutedCases.Batch0750.certificate15000.rectangle,RoutedCases.Batch0750.certificate15006.rectangle,RoutedCases.Batch0750.certificate15008.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14985,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14986,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14987,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14988,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14989,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14990,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14992,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14994,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14996,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14998,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0750.sound15000,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0750.sound15006,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0750.sound15008,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(13/400),(131/4000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0749.certificate14985.rectangle,RoutedCases.Batch0749.certificate14986.rectangle,RoutedCases.Batch0749.certificate14987.rectangle,RoutedCases.Batch0749.certificate14988.rectangle,RoutedCases.Batch0749.certificate14989.rectangle,RoutedCases.Batch0749.certificate14991.rectangle,RoutedCases.Batch0749.certificate14993.rectangle,RoutedCases.Batch0749.certificate14995.rectangle,RoutedCases.Batch0749.certificate14997.rectangle,RoutedCases.Batch0750.certificate15001.rectangle,RoutedCases.Batch0750.certificate15003.rectangle,RoutedCases.Batch0750.certificate15009.rectangle,RoutedCases.Batch0750.certificate15011.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14985,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14986,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14987,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14988,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14989,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14991,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14993,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14995,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14997,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0750.sound15001,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0750.sound15003,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0750.sound15009,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0750.sound15011,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(131/4000),(33/1000),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0749.certificate14985.rectangle,RoutedCases.Batch0749.certificate14986.rectangle,RoutedCases.Batch0749.certificate14987.rectangle,RoutedCases.Batch0749.certificate14988.rectangle,RoutedCases.Batch0749.certificate14989.rectangle,RoutedCases.Batch0749.certificate14991.rectangle,RoutedCases.Batch0749.certificate14993.rectangle,RoutedCases.Batch0749.certificate14995.rectangle,RoutedCases.Batch0749.certificate14997.rectangle,RoutedCases.Batch0750.certificate15002.rectangle,RoutedCases.Batch0750.certificate15004.rectangle,RoutedCases.Batch0750.certificate15010.rectangle,RoutedCases.Batch0750.certificate15012.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14985,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14986,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14987,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14988,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14989,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14991,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14993,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14995,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0749.sound14997,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0750.sound15002,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0750.sound15004,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0750.sound15010,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0750.sound15012,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(4/125),(33/1000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source273
