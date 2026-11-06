import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch393
import Cycle12.MergedCutProfiles.Batch394
import Cycle12.MergedCutProfiles.Batch704
import Cycle12.MergedCutProfiles.Batch705
import Cycle12.MergedCutProfiles.Batch706

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch422

def retention5064 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(32116757525252458629/1408963791382908709094),(737126447704738291/250000000000000000),(17/10),(659392499101638156939746277302491874759/294850579081895316400000000000000000000),false,MergedCutProfiles.Batch704.profile28198,(fun _ => MergedCutProfiles.Batch704.profile28198)⟩
theorem profilesValid5064 : retention5064.ProfilesValid := by
  exact MergedCutProfiles.Batch704.valid28198
theorem numericValid5064 : retention5064.NumericValid := by decide +kernel
def certificate5064 : RatCutBinCertificate := ⟨⟨retention5064,(488053306861738163/250000000000000000),(161735409484216873/1000000000000000000),(3691915359570146133/250000000000000000),(10465903641982879244853/500000000000000000),(1100007207473503449/500000000000000000)⟩,(999921209463200733/1000000000000000000),(179083063769378403/250000000000000000),(44691298716386017/1000000000000000000),(22982016328632917/500000000000000000)⟩
theorem valid5064 : certificate5064.Valid := by decide +kernel
theorem sound5064 : certificate5064.Sound := rat_cut_bin_certificate_sound certificate5064 profilesValid5064 numericValid5064 valid5064

def retention5065 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(1/40),(32116757525252458629/1000000000000000000),(21/20),(38079616370524523691524317434246302236893/17128937346801311268800000000000000000000),false,MergedCutProfiles.Batch704.profile28199,(fun _ => MergedCutProfiles.Batch704.profile28199)⟩
theorem profilesValid5065 : retention5065.ProfilesValid := by
  exact MergedCutProfiles.Batch704.valid28199
theorem numericValid5065 : retention5065.NumericValid := by decide +kernel
def certificate5065 : RatCutBinCertificate := ⟨⟨retention5065,(488053306861738163/250000000000000000),(161735409484216873/1000000000000000000),(3691915359570146133/250000000000000000),(10465903641982879244853/500000000000000000),(550166606244380003/250000000000000000)⟩,(999921209463200733/1000000000000000000),(336808847956703221/500000000000000000),(12048194744407873/200000000000000000),(7428754552456697/62500000000000000)⟩
theorem valid5065 : certificate5065.Valid := by decide +kernel
theorem sound5065 : certificate5065.Sound := rat_cut_bin_certificate_sound certificate5065 profilesValid5065 numericValid5065 valid5065

def retention5066 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(206956358914961024/450878789871404752475),(307360929081625283/500000000000000000),4,(4626578328422871009/2000000000000000000),true,MergedCutProfiles.Batch705.profile28200,![MergedCutProfiles.Batch705.profile28200,MergedCutProfiles.Batch705.profile28201,MergedCutProfiles.Batch705.profile28202,MergedCutProfiles.Batch705.profile28203,MergedCutProfiles.Batch705.profile28204,MergedCutProfiles.Batch705.profile28205,MergedCutProfiles.Batch705.profile28206,MergedCutProfiles.Batch705.profile28207,MergedCutProfiles.Batch705.profile28208,MergedCutProfiles.Batch705.profile28209,MergedCutProfiles.Batch705.profile28210,MergedCutProfiles.Batch705.profile28211,MergedCutProfiles.Batch705.profile28212,MergedCutProfiles.Batch705.profile28213,MergedCutProfiles.Batch705.profile28214,MergedCutProfiles.Batch705.profile28215]⟩
theorem profilesValid5066 : retention5066.ProfilesValid := by
  change ∀ j : Fin 16, (retention5066.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch705.valid28200
  · exact MergedCutProfiles.Batch705.valid28201
  · exact MergedCutProfiles.Batch705.valid28202
  · exact MergedCutProfiles.Batch705.valid28203
  · exact MergedCutProfiles.Batch705.valid28204
  · exact MergedCutProfiles.Batch705.valid28205
  · exact MergedCutProfiles.Batch705.valid28206
  · exact MergedCutProfiles.Batch705.valid28207
  · exact MergedCutProfiles.Batch705.valid28208
  · exact MergedCutProfiles.Batch705.valid28209
  · exact MergedCutProfiles.Batch705.valid28210
  · exact MergedCutProfiles.Batch705.valid28211
  · exact MergedCutProfiles.Batch705.valid28212
  · exact MergedCutProfiles.Batch705.valid28213
  · exact MergedCutProfiles.Batch705.valid28214
  · exact MergedCutProfiles.Batch705.valid28215
theorem numericValid5066 : retention5066.NumericValid := by decide +kernel
def certificate5066 : RatCutBinCertificate := ⟨⟨retention5066,(1948730099992498591/1000000000000000000),(168442616661570077/1000000000000000000),(15031611954174764881/1000000000000000000),(818199300286210727751/40000000000000000),(556484959333891339/250000000000000000)⟩,(499960068980238497/500000000000000000),(43431612564131967/62500000000000000),(52163093828411077/1000000000000000000),(23668544560699897/1000000000000000000)⟩
theorem valid5066 : certificate5066.Valid := by decide +kernel
theorem sound5066 : certificate5066.Sound := rat_cut_bin_certificate_sound certificate5066 profilesValid5066 numericValid5066 valid5066

def retention5067 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(43276754200000000/54105454784568570297),(4850539662069399/7812500000000000),4,(11520383840503264480443869898842827/4966952613959064576000000000000000),true,MergedCutProfiles.Batch705.profile28216,![MergedCutProfiles.Batch705.profile28216,MergedCutProfiles.Batch705.profile28217,MergedCutProfiles.Batch705.profile28218,MergedCutProfiles.Batch705.profile28219,MergedCutProfiles.Batch705.profile28208,MergedCutProfiles.Batch705.profile28220,MergedCutProfiles.Batch705.profile28221,MergedCutProfiles.Batch705.profile28222,MergedCutProfiles.Batch705.profile28215,MergedCutProfiles.Batch705.profile28223,MergedCutProfiles.Batch705.profile28224,MergedCutProfiles.Batch705.profile28225,MergedCutProfiles.Batch705.profile28226,MergedCutProfiles.Batch705.profile28227,MergedCutProfiles.Batch705.profile28228,MergedCutProfiles.Batch705.profile28229]⟩
theorem profilesValid5067 : retention5067.ProfilesValid := by
  change ∀ j : Fin 16, (retention5067.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch705.valid28216
  · exact MergedCutProfiles.Batch705.valid28217
  · exact MergedCutProfiles.Batch705.valid28218
  · exact MergedCutProfiles.Batch705.valid28219
  · exact MergedCutProfiles.Batch705.valid28208
  · exact MergedCutProfiles.Batch705.valid28220
  · exact MergedCutProfiles.Batch705.valid28221
  · exact MergedCutProfiles.Batch705.valid28222
  · exact MergedCutProfiles.Batch705.valid28215
  · exact MergedCutProfiles.Batch705.valid28223
  · exact MergedCutProfiles.Batch705.valid28224
  · exact MergedCutProfiles.Batch705.valid28225
  · exact MergedCutProfiles.Batch705.valid28226
  · exact MergedCutProfiles.Batch705.valid28227
  · exact MergedCutProfiles.Batch705.valid28228
  · exact MergedCutProfiles.Batch705.valid28229
theorem numericValid5067 : retention5067.NumericValid := by decide +kernel
def certificate5067 : RatCutBinCertificate := ⟨⟨retention5067,(1948730099992498591/1000000000000000000),(168442616661570077/1000000000000000000),(15031611954174764881/1000000000000000000),(818199300286210727751/40000000000000000),(1116028755365834561/500000000000000000)⟩,(499960068980238497/500000000000000000),(688538214647837193/1000000000000000000),(13627506198595139/250000000000000000),(12417165262838169/500000000000000000)⟩
theorem valid5067 : certificate5067.Valid := by decide +kernel
theorem sound5067 : certificate5067.Sound := rat_cut_bin_certificate_sound certificate5067 profilesValid5067 numericValid5067 valid5067

def retention5068 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(3081351260097736847/1352636369614214257425),(216383771/200000000),(29/10),(2590740320744090063380865768359702751/1081918855000000000000000000000000000),true,MergedCutProfiles.Batch705.profile28204,![MergedCutProfiles.Batch705.profile28204,MergedCutProfiles.Batch705.profile28209,MergedCutProfiles.Batch705.profile28214,MergedCutProfiles.Batch705.profile28224,MergedCutProfiles.Batch705.profile28227,MergedCutProfiles.Batch705.profile28230,MergedCutProfiles.Batch705.profile28231,MergedCutProfiles.Batch705.profile28232,MergedCutProfiles.Batch705.profile28233,MergedCutProfiles.Batch705.profile28234,MergedCutProfiles.Batch705.profile28235,MergedCutProfiles.Batch705.profile28236,MergedCutProfiles.Batch705.profile28237,MergedCutProfiles.Batch705.profile28238,MergedCutProfiles.Batch705.profile28239,MergedCutProfiles.Batch393.profile15730]⟩
theorem profilesValid5068 : retention5068.ProfilesValid := by
  change ∀ j : Fin 16, (retention5068.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch705.valid28204
  · exact MergedCutProfiles.Batch705.valid28209
  · exact MergedCutProfiles.Batch705.valid28214
  · exact MergedCutProfiles.Batch705.valid28224
  · exact MergedCutProfiles.Batch705.valid28227
  · exact MergedCutProfiles.Batch705.valid28230
  · exact MergedCutProfiles.Batch705.valid28231
  · exact MergedCutProfiles.Batch705.valid28232
  · exact MergedCutProfiles.Batch705.valid28233
  · exact MergedCutProfiles.Batch705.valid28234
  · exact MergedCutProfiles.Batch705.valid28235
  · exact MergedCutProfiles.Batch705.valid28236
  · exact MergedCutProfiles.Batch705.valid28237
  · exact MergedCutProfiles.Batch705.valid28238
  · exact MergedCutProfiles.Batch705.valid28239
  · exact MergedCutProfiles.Batch393.valid15730
theorem numericValid5068 : retention5068.NumericValid := by decide +kernel
def certificate5068 : RatCutBinCertificate := ⟨⟨retention5068,(1948730099992498591/1000000000000000000),(168442616661570077/1000000000000000000),(15031611954174764881/1000000000000000000),(818199300286210727751/40000000000000000),(2331250923325220443/1000000000000000000)⟩,(499960068980238497/500000000000000000),(238574048212578233/500000000000000000),(42449095449811781/250000000000000000),(108646506989906131/1000000000000000000)⟩
theorem valid5068 : certificate5068.Valid := by decide +kernel
theorem sound5068 : certificate5068.Sound := rat_cut_bin_certificate_sound certificate5068 profilesValid5068 numericValid5068 valid5068

def retention5069 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(2560000000000000000/54105454784568570297),(3081351260097736847/1000000000000000000),(3/2),(536063758046865195543/256000000000000000000),true,MergedCutProfiles.Batch706.profile28240,![MergedCutProfiles.Batch706.profile28240,MergedCutProfiles.Batch706.profile28241,MergedCutProfiles.Batch706.profile28242,MergedCutProfiles.Batch706.profile28243,MergedCutProfiles.Batch706.profile28244,MergedCutProfiles.Batch706.profile28245,MergedCutProfiles.Batch706.profile28246,MergedCutProfiles.Batch706.profile28247,MergedCutProfiles.Batch706.profile28248,MergedCutProfiles.Batch393.profile15742,MergedCutProfiles.Batch706.profile28249,MergedCutProfiles.Batch706.profile28250,MergedCutProfiles.Batch706.profile28251,MergedCutProfiles.Batch706.profile28252,MergedCutProfiles.Batch706.profile28253,MergedCutProfiles.Batch706.profile28254]⟩
theorem profilesValid5069 : retention5069.ProfilesValid := by
  change ∀ j : Fin 16, (retention5069.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch706.valid28240
  · exact MergedCutProfiles.Batch706.valid28241
  · exact MergedCutProfiles.Batch706.valid28242
  · exact MergedCutProfiles.Batch706.valid28243
  · exact MergedCutProfiles.Batch706.valid28244
  · exact MergedCutProfiles.Batch706.valid28245
  · exact MergedCutProfiles.Batch706.valid28246
  · exact MergedCutProfiles.Batch706.valid28247
  · exact MergedCutProfiles.Batch706.valid28248
  · exact MergedCutProfiles.Batch393.valid15742
  · exact MergedCutProfiles.Batch706.valid28249
  · exact MergedCutProfiles.Batch706.valid28250
  · exact MergedCutProfiles.Batch706.valid28251
  · exact MergedCutProfiles.Batch706.valid28252
  · exact MergedCutProfiles.Batch706.valid28253
  · exact MergedCutProfiles.Batch706.valid28254
theorem numericValid5069 : retention5069.NumericValid := by decide +kernel
def certificate5069 : RatCutBinCertificate := ⟨⟨retention5069,(1948730099992498591/1000000000000000000),(168442616661570077/1000000000000000000),(15031611954174764881/1000000000000000000),(818199300286210727751/40000000000000000),(206124310863209017/100000000000000000)⟩,(499960068980238497/500000000000000000),(35969296861422113/100000000000000000),(272514952257278151/1000000000000000000),(72158357132445381/250000000000000000)⟩
theorem valid5069 : certificate5069.Valid := by decide +kernel
theorem sound5069 : certificate5069.Sound := rat_cut_bin_certificate_sound certificate5069 profilesValid5069 numericValid5069 valid5069

def retention5070 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(1/2),64,1,(63850930806615332908698872210522484559/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch394.profile15795,(fun _ => MergedCutProfiles.Batch394.profile15795)⟩
theorem profilesValid5070 : retention5070.ProfilesValid := by
  exact MergedCutProfiles.Batch394.valid15795
theorem numericValid5070 : retention5070.NumericValid := by decide +kernel
def certificate5070 : RatCutBinCertificate := ⟨⟨retention5070,(1948730099992498591/1000000000000000000),(168442616661570077/1000000000000000000),(15031611954174764881/1000000000000000000),(818199300286210727751/40000000000000000),(487916766228724121/500000000000000000)⟩,(499960068980238497/500000000000000000),(14099728265485981/25000000000000000),(113002841032858421/1000000000000000000),(54303541270216979/500000000000000000)⟩
theorem valid5070 : certificate5070.Valid := by decide +kernel
theorem sound5070 : certificate5070.Sound := rat_cut_bin_certificate_sound certificate5070 profilesValid5070 numericValid5070 valid5070

def retention5071 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(2560000000000000000/54105454784568570297),(21699228970666862277/500000000000000000),1,(18163720280529392034441078918655408183/8679691588266744910800000000000000000),false,MergedCutProfiles.Batch706.profile28255,(fun _ => MergedCutProfiles.Batch706.profile28255)⟩
theorem profilesValid5071 : retention5071.ProfilesValid := by
  exact MergedCutProfiles.Batch706.valid28255
theorem numericValid5071 : retention5071.NumericValid := by decide +kernel
def certificate5071 : RatCutBinCertificate := ⟨⟨retention5071,(1728788143992498591/1000000000000000000),(168442616661570077/1000000000000000000),(15031611954174764881/1000000000000000000),(818199300286210727751/40000000000000000),(2073296241114166499/1000000000000000000)⟩,(999929151652669897/1000000000000000000),(8204857605715027/500000000000000000),(884993739165189761/1000000000000000000),(1751067278419480941/1000000000000000000)⟩
theorem valid5071 : certificate5071.Valid := by decide +kernel
theorem sound5071 : certificate5071.Sound := rat_cut_bin_certificate_sound certificate5071 profilesValid5071 numericValid5071 valid5071

def retention5072 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(1/2),64,1,(63850930806615332908698872210522484559/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch394.profile15795,(fun _ => MergedCutProfiles.Batch394.profile15795)⟩
theorem profilesValid5072 : retention5072.ProfilesValid := by
  exact MergedCutProfiles.Batch394.valid15795
theorem numericValid5072 : retention5072.NumericValid := by decide +kernel
def certificate5072 : RatCutBinCertificate := ⟨⟨retention5072,(1728788143992498591/1000000000000000000),(168442616661570077/1000000000000000000),(15031611954174764881/1000000000000000000),(818199300286210727751/40000000000000000),(24457454463220381/25000000000000000)⟩,(999929151652669897/1000000000000000000),(34776923449632881/1000000000000000000),(415244532641080893/500000000000000000),(800176242492595107/1000000000000000000)⟩
theorem valid5072 : certificate5072.Valid := by decide +kernel
theorem sound5072 : certificate5072.Sound := rat_cut_bin_certificate_sound certificate5072 profilesValid5072 numericValid5072 valid5072

def retention5073 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(30040999489415945/54105454784568570297),(148717819254534381/200000000000000000),4,(807854332009279497360729279264051119/330484042787854180000000000000000000),false,MergedCutProfiles.Batch706.profile28256,(fun _ => MergedCutProfiles.Batch706.profile28256)⟩
theorem profilesValid5073 : retention5073.ProfilesValid := by
  exact MergedCutProfiles.Batch706.valid28256
theorem numericValid5073 : retention5073.NumericValid := by decide +kernel
def certificate5073 : RatCutBinCertificate := ⟨⟨retention5073,(1960806098992498591/1000000000000000000),(168442616661570077/1000000000000000000),(15031611954174764881/1000000000000000000),(818199300286210727751/40000000000000000),(589141835355314589/250000000000000000)⟩,(999919643059278609/1000000000000000000),(794143716627782789/1000000000000000000),(4562687669687573/200000000000000000),(11217219142433423/1000000000000000000)⟩
theorem valid5073 : certificate5073.Valid := by decide +kernel
theorem sound5073 : certificate5073.Sound := rat_cut_bin_certificate_sound certificate5073 profilesValid5073 numericValid5073 valid5073

def retention5074 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(871916694887447234/1352636369614214257425),(6008199897883189/8000000000000000),4,(7345805426898545442497254614276813831/3004099948941594500000000000000000000),false,MergedCutProfiles.Batch706.profile28257,(fun _ => MergedCutProfiles.Batch706.profile28257)⟩
theorem profilesValid5074 : retention5074.ProfilesValid := by
  exact MergedCutProfiles.Batch706.valid28257
theorem numericValid5074 : retention5074.NumericValid := by decide +kernel
def certificate5074 : RatCutBinCertificate := ⟨⟨retention5074,(1960806098992498591/1000000000000000000),(168442616661570077/1000000000000000000),(15031611954174764881/1000000000000000000),(818199300286210727751/40000000000000000),(2357369430636909441/1000000000000000000)⟩,(999919643059278609/1000000000000000000),(792179871536267419/1000000000000000000),(23268516844241829/1000000000000000000),(1432874877451183/125000000000000000)⟩
theorem valid5074 : certificate5074.Valid := by decide +kernel
theorem sound5074 : certificate5074.Sound := rat_cut_bin_certificate_sound certificate5074 profilesValid5074 numericValid5074 valid5074

def retention5075 : RatCutRetentionCertificate := ⟨(57/1000),(29/500),(931010268832931963/450878789871404752475),(435958347443723617/500000000000000000),(73/20),(844595262945278880341892162085148594479/348766677954978893600000000000000000000),false,MergedCutProfiles.Batch706.profile28258,(fun _ => MergedCutProfiles.Batch706.profile28258)⟩
theorem profilesValid5075 : retention5075.ProfilesValid := by
  exact MergedCutProfiles.Batch706.valid28258
theorem numericValid5075 : retention5075.NumericValid := by decide +kernel
def certificate5075 : RatCutBinCertificate := ⟨⟨retention5075,(1960806098992498591/1000000000000000000),(168442616661570077/1000000000000000000),(15031611954174764881/1000000000000000000),(818199300286210727751/40000000000000000),(1170731297435303929/500000000000000000)⟩,(999919643059278609/1000000000000000000),(773919651461972601/1000000000000000000),(6933658089732679/250000000000000000),(14805606650585089/1000000000000000000)⟩
theorem valid5075 : certificate5075.Valid := by decide +kernel
theorem sound5075 : certificate5075.Sound := rat_cut_bin_certificate_sound certificate5075 profilesValid5075 numericValid5075 valid5075

def certificates : List RatCutBinCertificate := [certificate5064,certificate5065,certificate5066,certificate5067,certificate5068,certificate5069,certificate5070,certificate5071,certificate5072,certificate5073,certificate5074,certificate5075]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5064,List.forall_mem_cons.mpr ⟨sound5065,List.forall_mem_cons.mpr ⟨sound5066,List.forall_mem_cons.mpr ⟨sound5067,List.forall_mem_cons.mpr ⟨sound5068,List.forall_mem_cons.mpr ⟨sound5069,List.forall_mem_cons.mpr ⟨sound5070,List.forall_mem_cons.mpr ⟨sound5071,List.forall_mem_cons.mpr ⟨sound5072,List.forall_mem_cons.mpr ⟨sound5073,List.forall_mem_cons.mpr ⟨sound5074,List.forall_mem_cons.mpr ⟨sound5075,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch422
