import Cycle12.RationalCoverAssembly
import Cycle12.CoverAssembly.Source242
import Cycle12.CoverAssembly.Source243
import Cycle12.CoverAssembly.Source244
import Cycle12.CoverAssembly.Source245
import Cycle12.CoverAssembly.Source246
import Cycle12.CoverAssembly.Source247
import Cycle12.CoverAssembly.Source248
import Cycle12.CoverAssembly.Source249
import Cycle12.CoverAssembly.Source250
import Cycle12.CoverAssembly.Source251
import Cycle12.CoverAssembly.Source252
import Cycle12.CoverAssembly.Source253
import Cycle12.CoverAssembly.Source254
import Cycle12.CoverAssembly.Source255
import Cycle12.CoverAssembly.Source256
import Cycle12.CoverAssembly.Source257
import Cycle12.CoverAssembly.Source258
import Cycle12.CoverAssembly.Source259
import Cycle12.CoverAssembly.Source260
import Cycle12.CoverAssembly.Source261
import Cycle12.CoverAssembly.Source262
import Cycle12.CoverAssembly.Source263
import Cycle12.CoverAssembly.Source264
import Cycle12.CoverAssembly.Source265
import Cycle12.CoverAssembly.Source266
import Cycle12.CoverAssembly.Source267
import Cycle12.CoverAssembly.Source268
import Cycle12.CoverAssembly.Source269
import Cycle12.CoverAssembly.Source270
import Cycle12.CoverAssembly.Source271
import Cycle12.CoverAssembly.Source272
import Cycle12.CoverAssembly.Source273
import Cycle12.CoverAssembly.Source274
import Cycle12.CoverAssembly.Source275
import Cycle12.CoverAssembly.Source276
import Cycle12.CoverAssembly.Source277
import Cycle12.CoverAssembly.Source278
import Cycle12.CoverAssembly.Source279
import Cycle12.CoverAssembly.Source280
import Cycle12.CoverAssembly.Source281
import Cycle12.CoverAssembly.Source282
import Cycle12.CoverAssembly.Source283
import Cycle12.CoverAssembly.Source284
import Cycle12.CoverAssembly.Source285
import Cycle12.CoverAssembly.Source286
import Cycle12.CoverAssembly.Source287
import Cycle12.CoverAssembly.Source288
import Cycle12.CoverAssembly.Source289
import Cycle12.CoverAssembly.Source290
import Cycle12.CoverAssembly.Source291
import Cycle12.CoverAssembly.Source292
import Cycle12.CoverAssembly.Source293
import Cycle12.CoverAssembly.Source294
import Cycle12.CoverAssembly.Source295
import Cycle12.CoverAssembly.Source296
import Cycle12.CoverAssembly.Source297
import Cycle12.CoverAssembly.Source298
import Cycle12.CoverAssembly.Source299
import Cycle12.CoverAssembly.Source300
import Cycle12.CoverAssembly.Source301
import Cycle12.CoverAssembly.Source302
import Cycle12.CoverAssembly.Source303
import Cycle12.CoverAssembly.Source304
import Cycle12.CoverAssembly.Source305
import Cycle12.CoverAssembly.Source306
import Cycle12.CoverAssembly.Source307
import Cycle12.CoverAssembly.Source308
import Cycle12.CoverAssembly.Source309
import Cycle12.CoverAssembly.Source310
import Cycle12.CoverAssembly.Source311
import Cycle12.CoverAssembly.Source312
import Cycle12.CoverAssembly.Source313
import Cycle12.CoverAssembly.Source314
import Cycle12.CoverAssembly.Source315
import Cycle12.CoverAssembly.Source316
import Cycle12.CoverAssembly.Source317
import Cycle12.CoverAssembly.Source318
import Cycle12.CoverAssembly.Source319
import Cycle12.CoverAssembly.Source320
import Cycle12.CoverAssembly.Source321
import Cycle12.CoverAssembly.Source322
import Cycle12.CoverAssembly.Source323
import Cycle12.CoverAssembly.Source324
import Cycle12.CoverAssembly.Source325
import Cycle12.CoverAssembly.Source326
import Cycle12.CoverAssembly.Source327

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Mid2

def rectangle : RatCoverRectangle := ⟨(3/1000),(17/250),5,(some 20)⟩
def pieces : List RatCoverRectangle := [CoverAssembly.Source242.rectangle,CoverAssembly.Source243.rectangle,CoverAssembly.Source244.rectangle,CoverAssembly.Source245.rectangle,CoverAssembly.Source246.rectangle,CoverAssembly.Source247.rectangle,CoverAssembly.Source248.rectangle,CoverAssembly.Source249.rectangle,CoverAssembly.Source250.rectangle,CoverAssembly.Source251.rectangle,CoverAssembly.Source252.rectangle,CoverAssembly.Source253.rectangle,CoverAssembly.Source254.rectangle,CoverAssembly.Source255.rectangle,CoverAssembly.Source256.rectangle,CoverAssembly.Source257.rectangle,CoverAssembly.Source258.rectangle,CoverAssembly.Source259.rectangle,CoverAssembly.Source260.rectangle,CoverAssembly.Source261.rectangle,CoverAssembly.Source262.rectangle,CoverAssembly.Source263.rectangle,CoverAssembly.Source264.rectangle,CoverAssembly.Source265.rectangle,CoverAssembly.Source266.rectangle,CoverAssembly.Source267.rectangle,CoverAssembly.Source268.rectangle,CoverAssembly.Source269.rectangle,CoverAssembly.Source270.rectangle,CoverAssembly.Source271.rectangle,CoverAssembly.Source272.rectangle,CoverAssembly.Source273.rectangle,CoverAssembly.Source274.rectangle,CoverAssembly.Source275.rectangle,CoverAssembly.Source276.rectangle,CoverAssembly.Source277.rectangle,CoverAssembly.Source278.rectangle,CoverAssembly.Source279.rectangle,CoverAssembly.Source280.rectangle,CoverAssembly.Source281.rectangle,CoverAssembly.Source282.rectangle,CoverAssembly.Source283.rectangle,CoverAssembly.Source284.rectangle,CoverAssembly.Source285.rectangle,CoverAssembly.Source286.rectangle,CoverAssembly.Source287.rectangle,CoverAssembly.Source288.rectangle,CoverAssembly.Source289.rectangle,CoverAssembly.Source290.rectangle,CoverAssembly.Source291.rectangle,CoverAssembly.Source292.rectangle,CoverAssembly.Source293.rectangle,CoverAssembly.Source294.rectangle,CoverAssembly.Source295.rectangle,CoverAssembly.Source296.rectangle,CoverAssembly.Source297.rectangle,CoverAssembly.Source298.rectangle,CoverAssembly.Source299.rectangle,CoverAssembly.Source300.rectangle,CoverAssembly.Source301.rectangle,CoverAssembly.Source302.rectangle,CoverAssembly.Source303.rectangle,CoverAssembly.Source304.rectangle,CoverAssembly.Source305.rectangle,CoverAssembly.Source306.rectangle,CoverAssembly.Source307.rectangle,CoverAssembly.Source308.rectangle,CoverAssembly.Source309.rectangle,CoverAssembly.Source310.rectangle,CoverAssembly.Source311.rectangle,CoverAssembly.Source312.rectangle,CoverAssembly.Source313.rectangle,CoverAssembly.Source314.rectangle,CoverAssembly.Source315.rectangle,CoverAssembly.Source316.rectangle,CoverAssembly.Source317.rectangle,CoverAssembly.Source318.rectangle,CoverAssembly.Source319.rectangle,CoverAssembly.Source320.rectangle,CoverAssembly.Source321.rectangle,CoverAssembly.Source322.rectangle,CoverAssembly.Source323.rectangle,CoverAssembly.Source324.rectangle,CoverAssembly.Source325.rectangle,CoverAssembly.Source326.rectangle,CoverAssembly.Source327.rectangle]
theorem valid : rectangle.JoinX pieces := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle pieces valid (by
  exact List.forall_mem_cons.mpr ⟨CoverAssembly.Source242.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source243.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source244.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source245.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source246.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source247.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source248.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source249.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source250.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source251.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source252.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source253.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source254.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source255.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source256.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source257.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source258.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source259.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source260.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source261.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source262.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source263.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source264.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source265.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source266.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source267.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source268.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source269.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source270.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source271.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source272.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source273.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source274.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source275.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source276.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source277.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source278.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source279.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source280.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source281.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source282.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source283.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source284.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source285.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source286.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source287.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source288.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source289.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source290.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source291.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source292.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source293.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source294.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source295.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source296.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source297.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source298.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source299.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source300.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source301.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source302.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source303.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source304.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source305.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source306.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source307.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source308.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source309.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source310.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source311.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source312.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source313.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source314.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source315.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source316.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source317.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source318.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source319.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source320.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source321.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source322.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source323.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source324.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source325.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source326.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source327.sound,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Mid2
