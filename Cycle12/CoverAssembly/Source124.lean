import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0413
import Cycle12.RoutedCases.Batch0414

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source124

def strip0 : RatCoverRectangle := ⟨(123/2000),(197/3200),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0413.certificate8267.rectangle,RoutedCases.Batch0413.certificate8269.rectangle,RoutedCases.Batch0413.certificate8271.rectangle,RoutedCases.Batch0413.certificate8273.rectangle,RoutedCases.Batch0413.certificate8274.rectangle,RoutedCases.Batch0413.certificate8275.rectangle,RoutedCases.Batch0413.certificate8276.rectangle,RoutedCases.Batch0413.certificate8277.rectangle,RoutedCases.Batch0413.certificate8278.rectangle,RoutedCases.Batch0413.certificate8279.rectangle,RoutedCases.Batch0414.certificate8280.rectangle,RoutedCases.Batch0414.certificate8281.rectangle,RoutedCases.Batch0414.certificate8282.rectangle,RoutedCases.Batch0414.certificate8283.rectangle,RoutedCases.Batch0414.certificate8284.rectangle,RoutedCases.Batch0414.certificate8285.rectangle,RoutedCases.Batch0414.certificate8286.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8267,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8269,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8271,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8273,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8274,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8275,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8276,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8277,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8278,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8279,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8280,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8281,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8282,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8283,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8284,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8285,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8286,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(197/3200),(493/8000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0413.certificate8268.rectangle,RoutedCases.Batch0413.certificate8270.rectangle,RoutedCases.Batch0413.certificate8272.rectangle,RoutedCases.Batch0413.certificate8273.rectangle,RoutedCases.Batch0413.certificate8274.rectangle,RoutedCases.Batch0413.certificate8275.rectangle,RoutedCases.Batch0413.certificate8276.rectangle,RoutedCases.Batch0413.certificate8277.rectangle,RoutedCases.Batch0413.certificate8278.rectangle,RoutedCases.Batch0413.certificate8279.rectangle,RoutedCases.Batch0414.certificate8280.rectangle,RoutedCases.Batch0414.certificate8281.rectangle,RoutedCases.Batch0414.certificate8282.rectangle,RoutedCases.Batch0414.certificate8283.rectangle,RoutedCases.Batch0414.certificate8284.rectangle,RoutedCases.Batch0414.certificate8285.rectangle,RoutedCases.Batch0414.certificate8286.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8268,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8270,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8272,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8273,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8274,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8275,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8276,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8277,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8278,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0413.sound8279,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8280,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8281,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8282,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8283,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8284,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8285,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0414.sound8286,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(123/2000),(493/8000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source124
