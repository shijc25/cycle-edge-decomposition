import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch227
import Cycle12.MergedCutProfiles.Batch404
import Cycle12.MergedCutProfiles.Batch405
import Cycle12.MergedCutProfiles.Batch406
import Cycle12.MergedCutProfiles.Batch526
import Cycle12.MergedCutProfiles.Batch527
import Cycle12.MergedCutProfiles.Batch628
import Cycle12.MergedCutProfiles.Batch629

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch349

def retention4188 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(13040174473277417004/81625649514144777227),(379959250754813497/200000000000000000),(19/10),(10680521208092220598571606313406150563/6079348012077015952000000000000000000),false,MergedCutProfiles.Batch628.profile25129,(fun _ => MergedCutProfiles.Batch628.profile25129)⟩
theorem profilesValid4188 : retention4188.ProfilesValid := by
  exact MergedCutProfiles.Batch628.valid25129
theorem numericValid4188 : retention4188.NumericValid := by decide +kernel
def certificate4188 : RatCutBinCertificate := ⟨⟨retention4188,(2070374835686652571/1000000000000000000),(93024059904071007/500000000000000000),(793399026498316747/50000000000000000),(3897625990151809333379/1000000000000000000),(171073066263732839/100000000000000000)⟩,(99956567334231509/100000000000000000),(413448506021377273/1000000000000000000),(44276732193401643/200000000000000000),(159455666363034531/1000000000000000000)⟩
theorem valid4188 : certificate4188.Valid := by decide +kernel
theorem sound4188 : certificate4188.Sound := rat_cut_bin_certificate_sound certificate4188 profilesValid4188 numericValid4188 valid4188

def retention4189 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(64000000000000000000/244876948542434331681),(9780130854958062753/250000000000000000),1,(953108841716776023886243039326350011/638702423180934710400000000000000000),false,MergedCutProfiles.Batch628.profile25130,(fun _ => MergedCutProfiles.Batch628.profile25130)⟩
theorem profilesValid4189 : retention4189.ProfilesValid := by
  exact MergedCutProfiles.Batch628.valid25130
theorem numericValid4189 : retention4189.NumericValid := by decide +kernel
def certificate4189 : RatCutBinCertificate := ⟨⟨retention4189,(2070374835686652571/1000000000000000000),(93024059904071007/500000000000000000),(793399026498316747/50000000000000000),(3897625990151809333379/1000000000000000000),(366995851353838827/250000000000000000)⟩,(99956567334231509/100000000000000000),(161586883910045167/500000000000000000),(155884068348884081/500000000000000000),(55115346858674239/125000000000000000)⟩
theorem valid4189 : certificate4189.Valid := by decide +kernel
theorem sound4189 : certificate4189.Sound := rat_cut_bin_certificate_sound certificate4189 profilesValid4189 numericValid4189 valid4189

def retention4190 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(1/2),64,1,(10216328287349108297983858740969245439/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch227.profile9095,(fun _ => MergedCutProfiles.Batch227.profile9095)⟩
theorem profilesValid4190 : retention4190.ProfilesValid := by
  exact MergedCutProfiles.Batch227.valid9095
theorem numericValid4190 : retention4190.NumericValid := by decide +kernel
def certificate4190 : RatCutBinCertificate := ⟨⟨retention4190,(2070374835686652571/1000000000000000000),(93024059904071007/500000000000000000),(793399026498316747/50000000000000000),(3897625990151809333379/1000000000000000000),(973413661882959473/1000000000000000000)⟩,(99956567334231509/100000000000000000),(482624045337280057/1000000000000000000),(82887946904753779/500000000000000000),(4965036263206773/31250000000000000)⟩
theorem valid4190 : certificate4190.Valid := by decide +kernel
theorem sound4190 : certificate4190.Sound := rat_cut_bin_certificate_sound certificate4190 profilesValid4190 numericValid4190 valid4190

def retention4191 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(64000000000000000000/244876948542434331681),(12235101886610639769/500000000000000000),1,(145213209462882916197505323538991682527/97880815092885118152000000000000000000),false,MergedCutProfiles.Batch628.profile25130,(fun _ => MergedCutProfiles.Batch628.profile25130)⟩
theorem profilesValid4191 : retention4191.ProfilesValid := by
  exact MergedCutProfiles.Batch628.valid25130
theorem numericValid4191 : retention4191.NumericValid := by decide +kernel
def certificate4191 : RatCutBinCertificate := ⟨⟨retention4191,(1916272489686652571/1000000000000000000),(93024059904071007/500000000000000000),(793399026498316747/50000000000000000),(3897625990151809333379/1000000000000000000),(1461103861138321293/1000000000000000000)⟩,(999598004087151069/1000000000000000000),(35282046862965853/1000000000000000000),(414524435544801941/500000000000000000),(285650297074048281/250000000000000000)⟩
theorem valid4191 : certificate4191.Valid := by decide +kernel
theorem sound4191 : certificate4191.Sound := rat_cut_bin_certificate_sound certificate4191 profilesValid4191 numericValid4191 valid4191

def retention4192 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(1/2),64,1,(10216328287349108297983858740969245439/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch227.profile9095,(fun _ => MergedCutProfiles.Batch227.profile9095)⟩
theorem profilesValid4192 : retention4192.ProfilesValid := by
  exact MergedCutProfiles.Batch227.valid9095
theorem numericValid4192 : retention4192.NumericValid := by decide +kernel
def certificate4192 : RatCutBinCertificate := ⟨⟨retention4192,(1916272489686652571/1000000000000000000),(93024059904071007/500000000000000000),(793399026498316747/50000000000000000),(3897625990151809333379/1000000000000000000),(487610237429177531/500000000000000000)⟩,(999598004087151069/1000000000000000000),(105721190703733/2000000000000000),(390369172963738327/500000000000000000),(187414801595453117/250000000000000000)⟩
theorem valid4192 : certificate4192.Valid := by decide +kernel
theorem sound4192 : certificate4192.Sound := rat_cut_bin_certificate_sound certificate4192 profilesValid4192 numericValid4192 valid4192

def retention4193 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(774502368555575369/240139649079985731945),(189810403037833391/250000000000000000),(37/10),(760699601079721882403/320000000000000000000),true,MergedCutProfiles.Batch628.profile25131,![MergedCutProfiles.Batch628.profile25131,MergedCutProfiles.Batch628.profile25132,MergedCutProfiles.Batch628.profile25133,MergedCutProfiles.Batch628.profile25134,MergedCutProfiles.Batch628.profile25135,MergedCutProfiles.Batch628.profile25136,MergedCutProfiles.Batch628.profile25137,MergedCutProfiles.Batch628.profile25138,MergedCutProfiles.Batch628.profile25139,MergedCutProfiles.Batch628.profile25140,MergedCutProfiles.Batch526.profile21055,MergedCutProfiles.Batch404.profile16182,MergedCutProfiles.Batch405.profile16214,MergedCutProfiles.Batch526.profile21042,MergedCutProfiles.Batch628.profile25141,MergedCutProfiles.Batch628.profile25142]⟩
theorem profilesValid4193 : retention4193.ProfilesValid := by
  change ∀ j : Fin 16, (retention4193.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch628.valid25131
  · exact MergedCutProfiles.Batch628.valid25132
  · exact MergedCutProfiles.Batch628.valid25133
  · exact MergedCutProfiles.Batch628.valid25134
  · exact MergedCutProfiles.Batch628.valid25135
  · exact MergedCutProfiles.Batch628.valid25136
  · exact MergedCutProfiles.Batch628.valid25137
  · exact MergedCutProfiles.Batch628.valid25138
  · exact MergedCutProfiles.Batch628.valid25139
  · exact MergedCutProfiles.Batch628.valid25140
  · exact MergedCutProfiles.Batch526.valid21055
  · exact MergedCutProfiles.Batch404.valid16182
  · exact MergedCutProfiles.Batch405.valid16214
  · exact MergedCutProfiles.Batch526.valid21042
  · exact MergedCutProfiles.Batch628.valid25141
  · exact MergedCutProfiles.Batch628.valid25142
theorem numericValid4193 : retention4193.NumericValid := by decide +kernel
def certificate4193 : RatCutBinCertificate := ⟨⟨retention4193,(415497995322675463/200000000000000000),(9485872639178457/50000000000000000),(1601422808435793077/100000000000000000),(1928745821128284453269/500000000000000000),(2286121662712610823/1000000000000000000)⟩,(99956159419261117/100000000000000000),(465083705953329993/1000000000000000000),(44719232982830019/250000000000000000),(45274310586208093/500000000000000000)⟩
theorem valid4193 : certificate4193.Valid := by decide +kernel
theorem sound4193 : certificate4193.Sound := rat_cut_bin_certificate_sound certificate4193 profilesValid4193 numericValid4193 valid4193

def retention4194 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(219732010400000000/48027929815997146389),(774502368555575369/1000000000000000000),(73/20),(3025700371130449989809/1280000000000000000000),true,MergedCutProfiles.Batch628.profile25143,![MergedCutProfiles.Batch628.profile25143,MergedCutProfiles.Batch628.profile25144,MergedCutProfiles.Batch628.profile25145,MergedCutProfiles.Batch526.profile21066,MergedCutProfiles.Batch628.profile25146,MergedCutProfiles.Batch628.profile25147,MergedCutProfiles.Batch628.profile25140,MergedCutProfiles.Batch628.profile25148,MergedCutProfiles.Batch628.profile25149,MergedCutProfiles.Batch628.profile25150,MergedCutProfiles.Batch628.profile25151,MergedCutProfiles.Batch628.profile25152,MergedCutProfiles.Batch628.profile25153,MergedCutProfiles.Batch628.profile25154,MergedCutProfiles.Batch628.profile25155,MergedCutProfiles.Batch526.profile21069]⟩
theorem profilesValid4194 : retention4194.ProfilesValid := by
  change ∀ j : Fin 16, (retention4194.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch628.valid25143
  · exact MergedCutProfiles.Batch628.valid25144
  · exact MergedCutProfiles.Batch628.valid25145
  · exact MergedCutProfiles.Batch526.valid21066
  · exact MergedCutProfiles.Batch628.valid25146
  · exact MergedCutProfiles.Batch628.valid25147
  · exact MergedCutProfiles.Batch628.valid25140
  · exact MergedCutProfiles.Batch628.valid25148
  · exact MergedCutProfiles.Batch628.valid25149
  · exact MergedCutProfiles.Batch628.valid25150
  · exact MergedCutProfiles.Batch628.valid25151
  · exact MergedCutProfiles.Batch628.valid25152
  · exact MergedCutProfiles.Batch628.valid25153
  · exact MergedCutProfiles.Batch628.valid25154
  · exact MergedCutProfiles.Batch628.valid25155
  · exact MergedCutProfiles.Batch526.valid21069
theorem numericValid4194 : retention4194.NumericValid := by decide +kernel
def certificate4194 : RatCutBinCertificate := ⟨⟨retention4194,(415497995322675463/200000000000000000),(9485872639178457/50000000000000000),(1601422808435793077/100000000000000000),(1928745821128284453269/500000000000000000),(568498609182473349/250000000000000000)⟩,(99956159419261117/100000000000000000),(462325063942476099/1000000000000000000),(7239878327193661/40000000000000000),(23087764390952443/250000000000000000)⟩
theorem valid4194 : certificate4194.Valid := by decide +kernel
theorem sound4194 : certificate4194.Sound := rat_cut_bin_certificate_sound certificate4194 profilesValid4194 numericValid4194 valid4194

def retention4195 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(384376162706858082/80046549693328577315),(274665013/250000000),(27/10),(10276670642749182731363361410567404559/4394640208000000000000000000000000000),true,MergedCutProfiles.Batch628.profile25156,![MergedCutProfiles.Batch628.profile25156,MergedCutProfiles.Batch628.profile25133,MergedCutProfiles.Batch628.profile25157,MergedCutProfiles.Batch628.profile25158,MergedCutProfiles.Batch628.profile25159,MergedCutProfiles.Batch629.profile25160,MergedCutProfiles.Batch629.profile25161,MergedCutProfiles.Batch404.profile16182,MergedCutProfiles.Batch629.profile25162,MergedCutProfiles.Batch628.profile25141,MergedCutProfiles.Batch526.profile21056,MergedCutProfiles.Batch629.profile25163,MergedCutProfiles.Batch629.profile25164,MergedCutProfiles.Batch629.profile25165,MergedCutProfiles.Batch629.profile25166,MergedCutProfiles.Batch629.profile25167]⟩
theorem profilesValid4195 : retention4195.ProfilesValid := by
  change ∀ j : Fin 16, (retention4195.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch628.valid25156
  · exact MergedCutProfiles.Batch628.valid25133
  · exact MergedCutProfiles.Batch628.valid25157
  · exact MergedCutProfiles.Batch628.valid25158
  · exact MergedCutProfiles.Batch628.valid25159
  · exact MergedCutProfiles.Batch629.valid25160
  · exact MergedCutProfiles.Batch629.valid25161
  · exact MergedCutProfiles.Batch404.valid16182
  · exact MergedCutProfiles.Batch629.valid25162
  · exact MergedCutProfiles.Batch628.valid25141
  · exact MergedCutProfiles.Batch526.valid21056
  · exact MergedCutProfiles.Batch629.valid25163
  · exact MergedCutProfiles.Batch629.valid25164
  · exact MergedCutProfiles.Batch629.valid25165
  · exact MergedCutProfiles.Batch629.valid25166
  · exact MergedCutProfiles.Batch629.valid25167
theorem numericValid4195 : retention4195.NumericValid := by decide +kernel
def certificate4195 : RatCutBinCertificate := ⟨⟨retention4195,(415497995322675463/200000000000000000),(9485872639178457/50000000000000000),(1601422808435793077/100000000000000000),(1928745821128284453269/500000000000000000),(35500047503542067/15625000000000000)⟩,(99956159419261117/100000000000000000),(96440114674903989/250000000000000000),(61696431160022341/250000000000000000),(6467629406612203/40000000000000000)⟩
theorem valid4195 : certificate4195.Valid := by decide +kernel
theorem sound4195 : certificate4195.Sound := rat_cut_bin_certificate_sound certificate4195 profilesValid4195 numericValid4195 valid4195

def retention4196 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(3343987892190851857/240139649079985731945),(576564244060287123/500000000000000000),(13/5),(1453363942377366982807/640000000000000000000),true,MergedCutProfiles.Batch629.profile25168,![MergedCutProfiles.Batch629.profile25168,MergedCutProfiles.Batch629.profile25169,MergedCutProfiles.Batch405.profile16214,MergedCutProfiles.Batch526.profile21068,MergedCutProfiles.Batch527.profile21081,MergedCutProfiles.Batch405.profile16215,MergedCutProfiles.Batch629.profile25170,MergedCutProfiles.Batch526.profile21071,MergedCutProfiles.Batch629.profile25171,MergedCutProfiles.Batch527.profile21083,MergedCutProfiles.Batch629.profile25172,MergedCutProfiles.Batch629.profile25173,MergedCutProfiles.Batch629.profile25174,MergedCutProfiles.Batch629.profile25175,MergedCutProfiles.Batch527.profile21086,MergedCutProfiles.Batch629.profile25176]⟩
theorem profilesValid4196 : retention4196.ProfilesValid := by
  change ∀ j : Fin 16, (retention4196.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch629.valid25168
  · exact MergedCutProfiles.Batch629.valid25169
  · exact MergedCutProfiles.Batch405.valid16214
  · exact MergedCutProfiles.Batch526.valid21068
  · exact MergedCutProfiles.Batch527.valid21081
  · exact MergedCutProfiles.Batch405.valid16215
  · exact MergedCutProfiles.Batch629.valid25170
  · exact MergedCutProfiles.Batch526.valid21071
  · exact MergedCutProfiles.Batch629.valid25171
  · exact MergedCutProfiles.Batch527.valid21083
  · exact MergedCutProfiles.Batch629.valid25172
  · exact MergedCutProfiles.Batch629.valid25173
  · exact MergedCutProfiles.Batch629.valid25174
  · exact MergedCutProfiles.Batch629.valid25175
  · exact MergedCutProfiles.Batch527.valid21086
  · exact MergedCutProfiles.Batch629.valid25176
theorem numericValid4196 : retention4196.NumericValid := by decide +kernel
def certificate4196 : RatCutBinCertificate := ⟨⟨retention4196,(415497995322675463/200000000000000000),(9485872639178457/50000000000000000),(1601422808435793077/100000000000000000),(1928745821128284453269/500000000000000000),(551722474146670223/250000000000000000)⟩,(99956159419261117/100000000000000000),(3105593106205317/8000000000000000),(244470624351313681/1000000000000000000),(32327684846957897/200000000000000000)⟩
theorem valid4196 : certificate4196.Valid := by decide +kernel
theorem sound4196 : certificate4196.Sound := rat_cut_bin_certificate_sound certificate4196 profilesValid4196 numericValid4196 valid4196

def retention4197 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(12800000000000000000/48027929815997146389),(3343987892190851857/1000000000000000000),(27/20),(7957130660435571874676553261803652160919/5350380627505362971200000000000000000000),false,MergedCutProfiles.Batch629.profile25177,(fun _ => MergedCutProfiles.Batch629.profile25177)⟩
theorem profilesValid4197 : retention4197.ProfilesValid := by
  exact MergedCutProfiles.Batch629.valid25177
theorem numericValid4197 : retention4197.NumericValid := by decide +kernel
def certificate4197 : RatCutBinCertificate := ⟨⟨retention4197,(415497995322675463/200000000000000000),(9485872639178457/50000000000000000),(1601422808435793077/100000000000000000),(1928745821128284453269/500000000000000000),(1453982284366491263/1000000000000000000)⟩,(99956159419261117/100000000000000000),(409838906225388543/1000000000000000000),(224587438039434501/1000000000000000000),(195197261211394309/1000000000000000000)⟩
theorem valid4197 : certificate4197.Valid := by decide +kernel
theorem sound4197 : certificate4197.Sound := rat_cut_bin_certificate_sound certificate4197 profilesValid4197 numericValid4197 valid4197

def retention4198 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(1/2),64,1,(255408979415051621191349709308445271431/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch406.profile16277,(fun _ => MergedCutProfiles.Batch406.profile16277)⟩
theorem profilesValid4198 : retention4198.ProfilesValid := by
  exact MergedCutProfiles.Batch406.valid16277
theorem numericValid4198 : retention4198.NumericValid := by decide +kernel
def certificate4198 : RatCutBinCertificate := ⟨⟨retention4198,(415497995322675463/200000000000000000),(9485872639178457/50000000000000000),(1601422808435793077/100000000000000000),(1928745821128284453269/500000000000000000),(243269921570304757/250000000000000000)⟩,(99956159419261117/100000000000000000),(239340721056646699/500000000000000000),(168664282712081293/1000000000000000000),(16159411868799973/100000000000000000)⟩
theorem valid4198 : certificate4198.Valid := by decide +kernel
theorem sound4198 : certificate4198.Sound := rat_cut_bin_certificate_sound certificate4198 profilesValid4198 numericValid4198 valid4198

def retention4199 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(12800000000000000000/48027929815997146389),(24382391481740573173/1000000000000000000),1,(28716039252551838642240884173024934303/19505913185392458538400000000000000000),false,MergedCutProfiles.Batch629.profile25177,(fun _ => MergedCutProfiles.Batch629.profile25177)⟩
theorem profilesValid4199 : retention4199.ProfilesValid := by
  exact MergedCutProfiles.Batch629.valid25177
theorem numericValid4199 : retention4199.NumericValid := by decide +kernel
def certificate4199 : RatCutBinCertificate := ⟨⟨retention4199,(383831653122675463/200000000000000000),(9485872639178457/50000000000000000),(1601422808435793077/100000000000000000),(1928745821128284453269/500000000000000000),(1449435034584936227/1000000000000000000)⟩,(499797504750252751/500000000000000000),(7084025680082179/200000000000000000),(6473872667619567/7812500000000000),(1133216669306225081/1000000000000000000)⟩
theorem valid4199 : certificate4199.Valid := by decide +kernel
theorem sound4199 : certificate4199.Sound := rat_cut_bin_certificate_sound certificate4199 profilesValid4199 numericValid4199 valid4199

def certificates : List RatCutBinCertificate := [certificate4188,certificate4189,certificate4190,certificate4191,certificate4192,certificate4193,certificate4194,certificate4195,certificate4196,certificate4197,certificate4198,certificate4199]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4188,List.forall_mem_cons.mpr ⟨sound4189,List.forall_mem_cons.mpr ⟨sound4190,List.forall_mem_cons.mpr ⟨sound4191,List.forall_mem_cons.mpr ⟨sound4192,List.forall_mem_cons.mpr ⟨sound4193,List.forall_mem_cons.mpr ⟨sound4194,List.forall_mem_cons.mpr ⟨sound4195,List.forall_mem_cons.mpr ⟨sound4196,List.forall_mem_cons.mpr ⟨sound4197,List.forall_mem_cons.mpr ⟨sound4198,List.forall_mem_cons.mpr ⟨sound4199,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch349
