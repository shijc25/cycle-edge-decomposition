import Cycle12.RationalCoverAssembly
import Cycle12.CoverAssembly.Source415
import Cycle12.CoverAssembly.Source416
import Cycle12.CoverAssembly.Source417
import Cycle12.CoverAssembly.Source418
import Cycle12.CoverAssembly.Source419
import Cycle12.CoverAssembly.Source420
import Cycle12.CoverAssembly.Source421
import Cycle12.CoverAssembly.Source422
import Cycle12.CoverAssembly.Source423
import Cycle12.CoverAssembly.Source424
import Cycle12.CoverAssembly.Source425
import Cycle12.CoverAssembly.Source426
import Cycle12.CoverAssembly.Source427
import Cycle12.CoverAssembly.Source428
import Cycle12.CoverAssembly.Source429
import Cycle12.CoverAssembly.Source430
import Cycle12.CoverAssembly.Source431
import Cycle12.CoverAssembly.Source432
import Cycle12.CoverAssembly.Source433
import Cycle12.CoverAssembly.Source434
import Cycle12.CoverAssembly.Source435
import Cycle12.CoverAssembly.Source436
import Cycle12.CoverAssembly.Source437
import Cycle12.CoverAssembly.Source438
import Cycle12.CoverAssembly.Source439
import Cycle12.CoverAssembly.Source440
import Cycle12.CoverAssembly.Source441
import Cycle12.CoverAssembly.Source442
import Cycle12.CoverAssembly.Source443
import Cycle12.CoverAssembly.Source444
import Cycle12.CoverAssembly.Source445
import Cycle12.CoverAssembly.Source446
import Cycle12.CoverAssembly.Source447
import Cycle12.CoverAssembly.Source448
import Cycle12.CoverAssembly.Source449
import Cycle12.CoverAssembly.Source450
import Cycle12.CoverAssembly.Source451
import Cycle12.CoverAssembly.Source452
import Cycle12.CoverAssembly.Source453
import Cycle12.CoverAssembly.Source454
import Cycle12.CoverAssembly.Source455
import Cycle12.CoverAssembly.Source456
import Cycle12.CoverAssembly.Source457
import Cycle12.CoverAssembly.Source458
import Cycle12.CoverAssembly.Source459
import Cycle12.CoverAssembly.Source460
import Cycle12.CoverAssembly.Source461
import Cycle12.CoverAssembly.Source462
import Cycle12.CoverAssembly.Source463
import Cycle12.CoverAssembly.Source464
import Cycle12.CoverAssembly.Source465
import Cycle12.CoverAssembly.Source466
import Cycle12.CoverAssembly.Source467
import Cycle12.CoverAssembly.Source468
import Cycle12.CoverAssembly.Source469
import Cycle12.CoverAssembly.Source470
import Cycle12.CoverAssembly.Source471
import Cycle12.CoverAssembly.Source472
import Cycle12.CoverAssembly.Source473
import Cycle12.CoverAssembly.Source474
import Cycle12.CoverAssembly.Source475
import Cycle12.CoverAssembly.Source476
import Cycle12.CoverAssembly.Source477
import Cycle12.CoverAssembly.Source478
import Cycle12.CoverAssembly.Source479
import Cycle12.CoverAssembly.Source480
import Cycle12.CoverAssembly.Source481
import Cycle12.CoverAssembly.Source482
import Cycle12.CoverAssembly.Source483
import Cycle12.CoverAssembly.Source484
import Cycle12.CoverAssembly.Source485
import Cycle12.CoverAssembly.Source486
import Cycle12.CoverAssembly.Source487
import Cycle12.CoverAssembly.Source488
import Cycle12.CoverAssembly.Source489
import Cycle12.CoverAssembly.Source490
import Cycle12.CoverAssembly.Source491
import Cycle12.CoverAssembly.Source492
import Cycle12.CoverAssembly.Source493

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Tail

def rectangle : RatCoverRectangle := ⟨(3/1000),(17/250),100,none⟩
def pieces : List RatCoverRectangle := [CoverAssembly.Source415.rectangle,CoverAssembly.Source416.rectangle,CoverAssembly.Source417.rectangle,CoverAssembly.Source418.rectangle,CoverAssembly.Source419.rectangle,CoverAssembly.Source420.rectangle,CoverAssembly.Source421.rectangle,CoverAssembly.Source422.rectangle,CoverAssembly.Source423.rectangle,CoverAssembly.Source424.rectangle,CoverAssembly.Source425.rectangle,CoverAssembly.Source426.rectangle,CoverAssembly.Source427.rectangle,CoverAssembly.Source428.rectangle,CoverAssembly.Source429.rectangle,CoverAssembly.Source430.rectangle,CoverAssembly.Source431.rectangle,CoverAssembly.Source432.rectangle,CoverAssembly.Source433.rectangle,CoverAssembly.Source434.rectangle,CoverAssembly.Source435.rectangle,CoverAssembly.Source436.rectangle,CoverAssembly.Source437.rectangle,CoverAssembly.Source438.rectangle,CoverAssembly.Source439.rectangle,CoverAssembly.Source440.rectangle,CoverAssembly.Source441.rectangle,CoverAssembly.Source442.rectangle,CoverAssembly.Source443.rectangle,CoverAssembly.Source444.rectangle,CoverAssembly.Source445.rectangle,CoverAssembly.Source446.rectangle,CoverAssembly.Source447.rectangle,CoverAssembly.Source448.rectangle,CoverAssembly.Source449.rectangle,CoverAssembly.Source450.rectangle,CoverAssembly.Source451.rectangle,CoverAssembly.Source452.rectangle,CoverAssembly.Source453.rectangle,CoverAssembly.Source454.rectangle,CoverAssembly.Source455.rectangle,CoverAssembly.Source456.rectangle,CoverAssembly.Source457.rectangle,CoverAssembly.Source458.rectangle,CoverAssembly.Source459.rectangle,CoverAssembly.Source460.rectangle,CoverAssembly.Source461.rectangle,CoverAssembly.Source462.rectangle,CoverAssembly.Source463.rectangle,CoverAssembly.Source464.rectangle,CoverAssembly.Source465.rectangle,CoverAssembly.Source466.rectangle,CoverAssembly.Source467.rectangle,CoverAssembly.Source468.rectangle,CoverAssembly.Source469.rectangle,CoverAssembly.Source470.rectangle,CoverAssembly.Source471.rectangle,CoverAssembly.Source472.rectangle,CoverAssembly.Source473.rectangle,CoverAssembly.Source474.rectangle,CoverAssembly.Source475.rectangle,CoverAssembly.Source476.rectangle,CoverAssembly.Source477.rectangle,CoverAssembly.Source478.rectangle,CoverAssembly.Source479.rectangle,CoverAssembly.Source480.rectangle,CoverAssembly.Source481.rectangle,CoverAssembly.Source482.rectangle,CoverAssembly.Source483.rectangle,CoverAssembly.Source484.rectangle,CoverAssembly.Source485.rectangle,CoverAssembly.Source486.rectangle,CoverAssembly.Source487.rectangle,CoverAssembly.Source488.rectangle,CoverAssembly.Source489.rectangle,CoverAssembly.Source490.rectangle,CoverAssembly.Source491.rectangle,CoverAssembly.Source492.rectangle,CoverAssembly.Source493.rectangle]
theorem valid : rectangle.JoinX pieces := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle pieces valid (by
  exact List.forall_mem_cons.mpr ⟨CoverAssembly.Source415.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source416.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source417.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source418.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source419.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source420.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source421.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source422.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source423.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source424.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source425.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source426.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source427.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source428.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source429.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source430.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source431.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source432.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source433.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source434.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source435.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source436.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source437.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source438.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source439.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source440.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source441.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source442.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source443.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source444.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source445.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source446.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source447.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source448.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source449.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source450.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source451.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source452.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source453.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source454.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source455.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source456.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source457.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source458.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source459.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source460.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source461.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source462.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source463.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source464.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source465.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source466.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source467.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source468.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source469.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source470.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source471.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source472.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source473.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source474.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source475.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source476.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source477.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source478.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source479.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source480.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source481.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source482.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source483.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source484.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source485.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source486.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source487.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source488.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source489.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source490.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source491.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source492.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source493.sound,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Tail
