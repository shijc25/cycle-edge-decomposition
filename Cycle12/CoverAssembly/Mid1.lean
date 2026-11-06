import Cycle12.RationalCoverAssembly
import Cycle12.CoverAssembly.Source167
import Cycle12.CoverAssembly.Source168
import Cycle12.CoverAssembly.Source169
import Cycle12.CoverAssembly.Source170
import Cycle12.CoverAssembly.Source171
import Cycle12.CoverAssembly.Source172
import Cycle12.CoverAssembly.Source173
import Cycle12.CoverAssembly.Source174
import Cycle12.CoverAssembly.Source175
import Cycle12.CoverAssembly.Source176
import Cycle12.CoverAssembly.Source177
import Cycle12.CoverAssembly.Source178
import Cycle12.CoverAssembly.Source179
import Cycle12.CoverAssembly.Source180
import Cycle12.CoverAssembly.Source181
import Cycle12.CoverAssembly.Source182
import Cycle12.CoverAssembly.Source183
import Cycle12.CoverAssembly.Source184
import Cycle12.CoverAssembly.Source185
import Cycle12.CoverAssembly.Source186
import Cycle12.CoverAssembly.Source187
import Cycle12.CoverAssembly.Source188
import Cycle12.CoverAssembly.Source189
import Cycle12.CoverAssembly.Source190
import Cycle12.CoverAssembly.Source191
import Cycle12.CoverAssembly.Source192
import Cycle12.CoverAssembly.Source193
import Cycle12.CoverAssembly.Source194
import Cycle12.CoverAssembly.Source195
import Cycle12.CoverAssembly.Source196
import Cycle12.CoverAssembly.Source197
import Cycle12.CoverAssembly.Source198
import Cycle12.CoverAssembly.Source199
import Cycle12.CoverAssembly.Source200
import Cycle12.CoverAssembly.Source201
import Cycle12.CoverAssembly.Source202
import Cycle12.CoverAssembly.Source203
import Cycle12.CoverAssembly.Source204
import Cycle12.CoverAssembly.Source205
import Cycle12.CoverAssembly.Source206
import Cycle12.CoverAssembly.Source207
import Cycle12.CoverAssembly.Source208
import Cycle12.CoverAssembly.Source209
import Cycle12.CoverAssembly.Source210
import Cycle12.CoverAssembly.Source211
import Cycle12.CoverAssembly.Source212
import Cycle12.CoverAssembly.Source213
import Cycle12.CoverAssembly.Source214
import Cycle12.CoverAssembly.Source215
import Cycle12.CoverAssembly.Source216
import Cycle12.CoverAssembly.Source217
import Cycle12.CoverAssembly.Source218
import Cycle12.CoverAssembly.Source219
import Cycle12.CoverAssembly.Source220
import Cycle12.CoverAssembly.Source221
import Cycle12.CoverAssembly.Source222
import Cycle12.CoverAssembly.Source223
import Cycle12.CoverAssembly.Source224
import Cycle12.CoverAssembly.Source225
import Cycle12.CoverAssembly.Source226
import Cycle12.CoverAssembly.Source227
import Cycle12.CoverAssembly.Source228
import Cycle12.CoverAssembly.Source229
import Cycle12.CoverAssembly.Source230
import Cycle12.CoverAssembly.Source231
import Cycle12.CoverAssembly.Source232
import Cycle12.CoverAssembly.Source233
import Cycle12.CoverAssembly.Source234
import Cycle12.CoverAssembly.Source235
import Cycle12.CoverAssembly.Source236
import Cycle12.CoverAssembly.Source237
import Cycle12.CoverAssembly.Source238
import Cycle12.CoverAssembly.Source239
import Cycle12.CoverAssembly.Source240
import Cycle12.CoverAssembly.Source241

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Mid1

def rectangle : RatCoverRectangle := ⟨(3/1000),(17/250),2,(some 5)⟩
def pieces : List RatCoverRectangle := [CoverAssembly.Source167.rectangle,CoverAssembly.Source168.rectangle,CoverAssembly.Source169.rectangle,CoverAssembly.Source170.rectangle,CoverAssembly.Source171.rectangle,CoverAssembly.Source172.rectangle,CoverAssembly.Source173.rectangle,CoverAssembly.Source174.rectangle,CoverAssembly.Source175.rectangle,CoverAssembly.Source176.rectangle,CoverAssembly.Source177.rectangle,CoverAssembly.Source178.rectangle,CoverAssembly.Source179.rectangle,CoverAssembly.Source180.rectangle,CoverAssembly.Source181.rectangle,CoverAssembly.Source182.rectangle,CoverAssembly.Source183.rectangle,CoverAssembly.Source184.rectangle,CoverAssembly.Source185.rectangle,CoverAssembly.Source186.rectangle,CoverAssembly.Source187.rectangle,CoverAssembly.Source188.rectangle,CoverAssembly.Source189.rectangle,CoverAssembly.Source190.rectangle,CoverAssembly.Source191.rectangle,CoverAssembly.Source192.rectangle,CoverAssembly.Source193.rectangle,CoverAssembly.Source194.rectangle,CoverAssembly.Source195.rectangle,CoverAssembly.Source196.rectangle,CoverAssembly.Source197.rectangle,CoverAssembly.Source198.rectangle,CoverAssembly.Source199.rectangle,CoverAssembly.Source200.rectangle,CoverAssembly.Source201.rectangle,CoverAssembly.Source202.rectangle,CoverAssembly.Source203.rectangle,CoverAssembly.Source204.rectangle,CoverAssembly.Source205.rectangle,CoverAssembly.Source206.rectangle,CoverAssembly.Source207.rectangle,CoverAssembly.Source208.rectangle,CoverAssembly.Source209.rectangle,CoverAssembly.Source210.rectangle,CoverAssembly.Source211.rectangle,CoverAssembly.Source212.rectangle,CoverAssembly.Source213.rectangle,CoverAssembly.Source214.rectangle,CoverAssembly.Source215.rectangle,CoverAssembly.Source216.rectangle,CoverAssembly.Source217.rectangle,CoverAssembly.Source218.rectangle,CoverAssembly.Source219.rectangle,CoverAssembly.Source220.rectangle,CoverAssembly.Source221.rectangle,CoverAssembly.Source222.rectangle,CoverAssembly.Source223.rectangle,CoverAssembly.Source224.rectangle,CoverAssembly.Source225.rectangle,CoverAssembly.Source226.rectangle,CoverAssembly.Source227.rectangle,CoverAssembly.Source228.rectangle,CoverAssembly.Source229.rectangle,CoverAssembly.Source230.rectangle,CoverAssembly.Source231.rectangle,CoverAssembly.Source232.rectangle,CoverAssembly.Source233.rectangle,CoverAssembly.Source234.rectangle,CoverAssembly.Source235.rectangle,CoverAssembly.Source236.rectangle,CoverAssembly.Source237.rectangle,CoverAssembly.Source238.rectangle,CoverAssembly.Source239.rectangle,CoverAssembly.Source240.rectangle,CoverAssembly.Source241.rectangle]
theorem valid : rectangle.JoinX pieces := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle pieces valid (by
  exact List.forall_mem_cons.mpr ⟨CoverAssembly.Source167.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source168.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source169.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source170.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source171.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source172.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source173.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source174.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source175.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source176.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source177.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source178.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source179.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source180.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source181.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source182.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source183.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source184.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source185.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source186.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source187.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source188.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source189.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source190.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source191.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source192.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source193.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source194.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source195.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source196.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source197.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source198.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source199.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source200.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source201.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source202.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source203.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source204.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source205.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source206.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source207.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source208.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source209.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source210.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source211.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source212.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source213.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source214.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source215.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source216.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source217.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source218.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source219.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source220.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source221.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source222.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source223.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source224.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source225.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source226.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source227.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source228.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source229.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source230.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source231.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source232.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source233.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source234.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source235.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source236.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source237.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source238.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source239.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source240.sound,List.forall_mem_cons.mpr ⟨CoverAssembly.Source241.sound,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Mid1
