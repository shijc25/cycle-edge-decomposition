import Cycle12.RationalCoverAssembly
import Cycle12.CoverAssembly.SmallBase
import Cycle12.CoverAssembly.SmallTail
import Cycle12.CoverAssembly.Base
import Cycle12.CoverAssembly.Mid1
import Cycle12.CoverAssembly.Mid2
import Cycle12.CoverAssembly.Mid3
import Cycle12.CoverAssembly.Tail

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Full

def small : RatCoverRectangle := ⟨0,(3/1000),1,none⟩
def smallPieces : List RatCoverRectangle := [SmallBase.rectangle,SmallTail.rectangle]
theorem smallValid : small.JoinS smallPieces := by decide +kernel
theorem smallSound : small.Sound := rat_cover_join_s_sound small smallPieces smallValid (by
  exact List.forall_mem_cons.mpr ⟨SmallBase.sound,List.forall_mem_cons.mpr ⟨SmallTail.sound,List.forall_mem_nil _⟩⟩)

def large : RatCoverRectangle := ⟨(3/1000),(17/250),1,none⟩
def largePieces : List RatCoverRectangle := [Base.rectangle,Mid1.rectangle,Mid2.rectangle,Mid3.rectangle,Tail.rectangle]
theorem largeValid : large.JoinS largePieces := by decide +kernel
theorem largeSound : large.Sound := rat_cover_join_s_sound large largePieces largeValid (by
  exact List.forall_mem_cons.mpr ⟨Base.sound,List.forall_mem_cons.mpr ⟨Mid1.sound,List.forall_mem_cons.mpr ⟨Mid2.sound,List.forall_mem_cons.mpr ⟨Mid3.sound,List.forall_mem_cons.mpr ⟨Tail.sound,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨0,(17/250),1,none⟩
theorem valid : rectangle.JoinX [small,large] := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle [small,large] valid (by
  exact List.forall_mem_cons.mpr ⟨smallSound,List.forall_mem_cons.mpr ⟨largeSound,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Full
