import Cycle12.RationalCoverAssembly
import Cycle12.CoverAssembly.Source328
import Cycle12.CoverAssembly.Source329
import Cycle12.CoverAssembly.Source330
import Cycle12.CoverAssembly.Source331
import Cycle12.CoverAssembly.Source332
import Cycle12.CoverAssembly.Source333
import Cycle12.CoverAssembly.Source334
import Cycle12.CoverAssembly.Source335
import Cycle12.CoverAssembly.Source336
import Cycle12.CoverAssembly.Source337
import Cycle12.CoverAssembly.Source338
import Cycle12.CoverAssembly.Source339
import Cycle12.CoverAssembly.Source340
import Cycle12.CoverAssembly.Source341
import Cycle12.CoverAssembly.Source342
import Cycle12.CoverAssembly.Source343
import Cycle12.CoverAssembly.Source344
import Cycle12.CoverAssembly.Source345
import Cycle12.CoverAssembly.Source346
import Cycle12.CoverAssembly.Source347
import Cycle12.CoverAssembly.Source348
import Cycle12.CoverAssembly.Source349
import Cycle12.CoverAssembly.Source350
import Cycle12.CoverAssembly.Source351
import Cycle12.CoverAssembly.Source352
import Cycle12.CoverAssembly.Source353
import Cycle12.CoverAssembly.Source354
import Cycle12.CoverAssembly.Source355
import Cycle12.CoverAssembly.Source356
import Cycle12.CoverAssembly.Source357
import Cycle12.CoverAssembly.Source358
import Cycle12.CoverAssembly.Source359
import Cycle12.CoverAssembly.Source360
import Cycle12.CoverAssembly.Source361
import Cycle12.CoverAssembly.Source362
import Cycle12.CoverAssembly.Source363
import Cycle12.CoverAssembly.Source364
import Cycle12.CoverAssembly.Source365
import Cycle12.CoverAssembly.Source366
import Cycle12.CoverAssembly.Source367
import Cycle12.CoverAssembly.Source368
import Cycle12.CoverAssembly.Source369
import Cycle12.CoverAssembly.Source370
import Cycle12.CoverAssembly.Source371
import Cycle12.CoverAssembly.Source372
import Cycle12.CoverAssembly.Source373
import Cycle12.CoverAssembly.Source374
import Cycle12.CoverAssembly.Source375
import Cycle12.CoverAssembly.Source376
import Cycle12.CoverAssembly.Source377
import Cycle12.CoverAssembly.Source378
import Cycle12.CoverAssembly.Source379
import Cycle12.CoverAssembly.Source380
import Cycle12.CoverAssembly.Source381
import Cycle12.CoverAssembly.Source382
import Cycle12.CoverAssembly.Source383
import Cycle12.CoverAssembly.Source384
import Cycle12.CoverAssembly.Source385
import Cycle12.CoverAssembly.Source386
import Cycle12.CoverAssembly.Source387
import Cycle12.CoverAssembly.Source388
import Cycle12.CoverAssembly.Source389
import Cycle12.CoverAssembly.Source390
import Cycle12.CoverAssembly.Source391
import Cycle12.CoverAssembly.Source392
import Cycle12.CoverAssembly.Source393
import Cycle12.CoverAssembly.Source394
import Cycle12.CoverAssembly.Source395
import Cycle12.CoverAssembly.Source396
import Cycle12.CoverAssembly.Source397
import Cycle12.CoverAssembly.Source398
import Cycle12.CoverAssembly.Source399
import Cycle12.CoverAssembly.Source400
import Cycle12.CoverAssembly.Source401
import Cycle12.CoverAssembly.Source402
import Cycle12.CoverAssembly.Source403
import Cycle12.CoverAssembly.Source404
import Cycle12.CoverAssembly.Source405
import Cycle12.CoverAssembly.Source406
import Cycle12.CoverAssembly.Source407
import Cycle12.CoverAssembly.Source408
import Cycle12.CoverAssembly.Source409
import Cycle12.CoverAssembly.Source410
import Cycle12.CoverAssembly.Source411
import Cycle12.CoverAssembly.Source412
import Cycle12.CoverAssembly.Source413
import Cycle12.CoverAssembly.Source414

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Mid3

def rectangle : RatCoverRectangle := ⟨(3/1000),(17/250),20,(some 100)⟩
def pieces : List RatCoverRectangle := [CoverAssembly.Source328.rectangle,CoverAssembly.Source329.rectangle,CoverAssembly.Source330.rectangle,CoverAssembly.Source331.rectangle,CoverAssembly.Source332.rectangle,CoverAssembly.Source333.rectangle,CoverAssembly.Source334.rectangle,CoverAssembly.Source335.rectangle,CoverAssembly.Source336.rectangle,CoverAssembly.Source337.rectangle,CoverAssembly.Source338.rectangle,CoverAssembly.Source339.rectangle,CoverAssembly.Source340.rectangle,CoverAssembly.Source341.rectangle,CoverAssembly.Source342.rectangle,CoverAssembly.Source343.rectangle,CoverAssembly.Source344.rectangle,CoverAssembly.Source345.rectangle,CoverAssembly.Source346.rectangle,CoverAssembly.Source347.rectangle,CoverAssembly.Source348.rectangle,CoverAssembly.Source349.rectangle,CoverAssembly.Source350.rectangle,CoverAssembly.Source351.rectangle,CoverAssembly.Source352.rectangle,CoverAssembly.Source353.rectangle,CoverAssembly.Source354.rectangle,CoverAssembly.Source355.rectangle,CoverAssembly.Source356.rectangle,CoverAssembly.Source357.rectangle,CoverAssembly.Source358.rectangle,CoverAssembly.Source359.rectangle,CoverAssembly.Source360.rectangle,CoverAssembly.Source361.rectangle,CoverAssembly.Source362.rectangle,CoverAssembly.Source363.rectangle,CoverAssembly.Source364.rectangle,CoverAssembly.Source365.rectangle,CoverAssembly.Source366.rectangle,CoverAssembly.Source367.rectangle,CoverAssembly.Source368.rectangle,CoverAssembly.Source369.rectangle,CoverAssembly.Source370.rectangle,CoverAssembly.Source371.rectangle,CoverAssembly.Source372.rectangle,CoverAssembly.Source373.rectangle,CoverAssembly.Source374.rectangle,CoverAssembly.Source375.rectangle,CoverAssembly.Source376.rectangle,CoverAssembly.Source377.rectangle,CoverAssembly.Source378.rectangle,CoverAssembly.Source379.rectangle,CoverAssembly.Source380.rectangle,CoverAssembly.Source381.rectangle,CoverAssembly.Source382.rectangle,CoverAssembly.Source383.rectangle,CoverAssembly.Source384.rectangle,CoverAssembly.Source385.rectangle,CoverAssembly.Source386.rectangle,CoverAssembly.Source387.rectangle,CoverAssembly.Source388.rectangle,CoverAssembly.Source389.rectangle,CoverAssembly.Source390.rectangle,CoverAssembly.Source391.rectangle,CoverAssembly.Source392.rectangle,CoverAssembly.Source393.rectangle,CoverAssembly.Source394.rectangle,CoverAssembly.Source395.rectangle,CoverAssembly.Source396.rectangle,CoverAssembly.Source397.rectangle,CoverAssembly.Source398.rectangle,CoverAssembly.Source399.rectangle,CoverAssembly.Source400.rectangle,CoverAssembly.Source401.rectangle,CoverAssembly.Source402.rectangle,CoverAssembly.Source403.rectangle,CoverAssembly.Source404.rectangle,CoverAssembly.Source405.rectangle,CoverAssembly.Source406.rectangle,CoverAssembly.Source407.rectangle,CoverAssembly.Source408.rectangle,CoverAssembly.Source409.rectangle,CoverAssembly.Source410.rectangle,CoverAssembly.Source411.rectangle,CoverAssembly.Source412.rectangle,CoverAssembly.Source413.rectangle,CoverAssembly.Source414.rectangle]
theorem valid : rectangle.JoinX pieces := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle pieces valid (by
  exact List.forall_mem_cons.mpr ⟨CoverAssembly.Source328.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source329.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source330.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source331.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source332.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source333.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source334.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source335.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source336.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source337.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source338.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source339.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source340.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source341.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source342.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source343.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source344.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source345.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source346.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source347.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source348.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source349.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source350.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source351.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source352.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source353.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source354.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source355.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source356.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source357.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source358.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source359.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source360.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source361.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source362.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source363.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source364.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source365.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source366.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source367.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source368.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source369.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source370.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source371.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source372.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source373.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source374.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source375.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source376.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source377.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source378.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source379.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source380.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source381.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source382.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source383.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source384.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source385.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source386.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source387.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source388.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source389.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source390.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source391.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source392.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source393.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source394.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source395.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source396.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source397.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source398.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source399.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source400.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source401.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source402.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source403.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source404.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source405.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source406.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source407.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source408.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source409.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source410.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source411.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source412.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source413.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source414.sound,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Mid3
