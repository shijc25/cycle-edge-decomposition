import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0859
import Cycle12.RoutedCases.Batch0860

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source368

def strip0 : RatCoverRectangle := ⟨(33/1000),(133/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0859.certificate17181.rectangle,RoutedCases.Batch0859.certificate17182.rectangle,RoutedCases.Batch0859.certificate17183.rectangle,RoutedCases.Batch0859.certificate17184.rectangle,RoutedCases.Batch0859.certificate17185.rectangle,RoutedCases.Batch0859.certificate17186.rectangle,RoutedCases.Batch0859.certificate17188.rectangle,RoutedCases.Batch0859.certificate17190.rectangle,RoutedCases.Batch0859.certificate17195.rectangle,RoutedCases.Batch0859.certificate17197.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17181,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17182,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17183,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17184,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17185,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17186,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17188,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17190,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17195,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17197,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(133/4000),(67/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0859.certificate17181.rectangle,RoutedCases.Batch0859.certificate17182.rectangle,RoutedCases.Batch0859.certificate17183.rectangle,RoutedCases.Batch0859.certificate17184.rectangle,RoutedCases.Batch0859.certificate17185.rectangle,RoutedCases.Batch0859.certificate17186.rectangle,RoutedCases.Batch0859.certificate17188.rectangle,RoutedCases.Batch0859.certificate17190.rectangle,RoutedCases.Batch0859.certificate17196.rectangle,RoutedCases.Batch0859.certificate17198.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17181,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17182,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17183,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17184,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17185,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17186,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17188,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17190,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17196,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17198,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(67/2000),(269/8000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0859.certificate17181.rectangle,RoutedCases.Batch0859.certificate17182.rectangle,RoutedCases.Batch0859.certificate17183.rectangle,RoutedCases.Batch0859.certificate17184.rectangle,RoutedCases.Batch0859.certificate17185.rectangle,RoutedCases.Batch0859.certificate17187.rectangle,RoutedCases.Batch0859.certificate17189.rectangle,RoutedCases.Batch0859.certificate17191.rectangle,RoutedCases.Batch0859.certificate17193.rectangle,RoutedCases.Batch0859.certificate17199.rectangle,RoutedCases.Batch0860.certificate17201.rectangle,RoutedCases.Batch0860.certificate17202.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17181,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17182,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17183,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17184,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17185,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17187,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17189,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17191,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17193,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17199,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0860.sound17201,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0860.sound17202,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(269/8000),(27/800),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0859.certificate17181.rectangle,RoutedCases.Batch0859.certificate17182.rectangle,RoutedCases.Batch0859.certificate17183.rectangle,RoutedCases.Batch0859.certificate17184.rectangle,RoutedCases.Batch0859.certificate17185.rectangle,RoutedCases.Batch0859.certificate17187.rectangle,RoutedCases.Batch0859.certificate17189.rectangle,RoutedCases.Batch0859.certificate17191.rectangle,RoutedCases.Batch0859.certificate17193.rectangle,RoutedCases.Batch0859.certificate17199.rectangle,RoutedCases.Batch0860.certificate17201.rectangle,RoutedCases.Batch0860.certificate17203.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17181,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17182,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17183,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17184,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17185,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17187,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17189,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17191,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17193,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17199,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0860.sound17201,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0860.sound17203,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(27/800),(271/8000),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0859.certificate17181.rectangle,RoutedCases.Batch0859.certificate17182.rectangle,RoutedCases.Batch0859.certificate17183.rectangle,RoutedCases.Batch0859.certificate17184.rectangle,RoutedCases.Batch0859.certificate17185.rectangle,RoutedCases.Batch0859.certificate17187.rectangle,RoutedCases.Batch0859.certificate17189.rectangle,RoutedCases.Batch0859.certificate17192.rectangle,RoutedCases.Batch0859.certificate17194.rectangle,RoutedCases.Batch0860.certificate17200.rectangle,RoutedCases.Batch0860.certificate17204.rectangle,RoutedCases.Batch0860.certificate17206.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17181,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17182,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17183,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17184,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17185,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17187,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17189,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17192,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17194,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0860.sound17200,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0860.sound17204,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0860.sound17206,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(271/8000),(17/500),20,(some 100)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0859.certificate17181.rectangle,RoutedCases.Batch0859.certificate17182.rectangle,RoutedCases.Batch0859.certificate17183.rectangle,RoutedCases.Batch0859.certificate17184.rectangle,RoutedCases.Batch0859.certificate17185.rectangle,RoutedCases.Batch0859.certificate17187.rectangle,RoutedCases.Batch0859.certificate17189.rectangle,RoutedCases.Batch0859.certificate17192.rectangle,RoutedCases.Batch0859.certificate17194.rectangle,RoutedCases.Batch0860.certificate17200.rectangle,RoutedCases.Batch0860.certificate17205.rectangle,RoutedCases.Batch0860.certificate17207.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17181,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17182,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17183,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17184,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17185,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17187,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17189,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17192,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0859.sound17194,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0860.sound17200,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0860.sound17205,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0860.sound17207,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(33/1000),(17/500),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source368
