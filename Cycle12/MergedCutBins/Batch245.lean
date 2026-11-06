import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch030
import Cycle12.MergedCutProfiles.Batch031
import Cycle12.MergedCutProfiles.Batch032
import Cycle12.MergedCutProfiles.Batch033
import Cycle12.MergedCutProfiles.Batch034
import Cycle12.MergedCutProfiles.Batch324
import Cycle12.MergedCutProfiles.Batch325
import Cycle12.MergedCutProfiles.Batch326
import Cycle12.MergedCutProfiles.Batch458
import Cycle12.MergedCutProfiles.Batch459

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch245

def retention2940 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(1622905499305891861/475027590701504258185),(1208606823/1000000000),(51/20),(18470625144618273183/8000000000000000000),true,MergedCutProfiles.Batch459.profile18360,![MergedCutProfiles.Batch459.profile18360,MergedCutProfiles.Batch324.profile12984,MergedCutProfiles.Batch458.profile18353,MergedCutProfiles.Batch459.profile18361,MergedCutProfiles.Batch459.profile18362,MergedCutProfiles.Batch458.profile18356,MergedCutProfiles.Batch324.profile12989,MergedCutProfiles.Batch459.profile18363,MergedCutProfiles.Batch324.profile12999,MergedCutProfiles.Batch459.profile18364,MergedCutProfiles.Batch325.profile13006,MergedCutProfiles.Batch458.profile18359,MergedCutProfiles.Batch325.profile13007,MergedCutProfiles.Batch031.profile1256,MergedCutProfiles.Batch030.profile1217,MergedCutProfiles.Batch459.profile18365]⟩
theorem profilesValid2940 : retention2940.ProfilesValid := by
  change ∀ j : Fin 16, (retention2940.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch459.valid18360
  · exact MergedCutProfiles.Batch324.valid12984
  · exact MergedCutProfiles.Batch458.valid18353
  · exact MergedCutProfiles.Batch459.valid18361
  · exact MergedCutProfiles.Batch459.valid18362
  · exact MergedCutProfiles.Batch458.valid18356
  · exact MergedCutProfiles.Batch324.valid12989
  · exact MergedCutProfiles.Batch459.valid18363
  · exact MergedCutProfiles.Batch324.valid12999
  · exact MergedCutProfiles.Batch459.valid18364
  · exact MergedCutProfiles.Batch325.valid13006
  · exact MergedCutProfiles.Batch458.valid18359
  · exact MergedCutProfiles.Batch325.valid13007
  · exact MergedCutProfiles.Batch031.valid1256
  · exact MergedCutProfiles.Batch030.valid1217
  · exact MergedCutProfiles.Batch459.valid18365
theorem numericValid2940 : retention2940.NumericValid := by decide +kernel
def certificate2940 : RatCutBinCertificate := ⟨⟨retention2940,(375986754775867947/200000000000000000),(12287303118992409/500000000000000000),(8894162574352425643/1000000000000000000),(265349954764930120907/62500000000000000),(57389568597955173/25000000000000000)⟩,(249891788975196571/250000000000000000),(5957606589217649/15625000000000000),(25107278621923159/100000000000000000),(87420411264628923/500000000000000000)⟩
theorem valid2940 : certificate2940.Valid := by decide +kernel
theorem sound2940 : certificate2940.Sound := rat_cut_bin_certificate_sound certificate2940 profilesValid2940 numericValid2940 valid2940

def retention2941 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(37284298252698145324/475027590701504258185),(1622905499305891861/1000000000000000000),(21/10),(1274096222355098257742481205281870571679/649162199722356744400000000000000000000),false,MergedCutProfiles.Batch459.profile18366,(fun _ => MergedCutProfiles.Batch459.profile18366)⟩
theorem profilesValid2941 : retention2941.ProfilesValid := by
  exact MergedCutProfiles.Batch459.valid18366
theorem numericValid2941 : retention2941.NumericValid := by decide +kernel
def certificate2941 : RatCutBinCertificate := ⟨⟨retention2941,(375986754775867947/200000000000000000),(12287303118992409/500000000000000000),(8894162574352425643/1000000000000000000),(265349954764930120907/62500000000000000),(1951769802091214751/1000000000000000000)⟩,(249891788975196571/250000000000000000),(24579943966613501/62500000000000000),(239697138338625333/1000000000000000000),(174957037661115671/1000000000000000000)⟩
theorem valid2941 : certificate2941.Valid := by decide +kernel
theorem sound2941 : certificate2941.Sound := rat_cut_bin_certificate_sound certificate2941 profilesValid2941 numericValid2941 valid2941

def retention2942 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(12800000000000000000/95005518140300851637),(9321074563174536331/250000000000000000),1,(20429192267575757217032103435371911131/11472091770060967792000000000000000000),false,MergedCutProfiles.Batch459.profile18367,(fun _ => MergedCutProfiles.Batch459.profile18367)⟩
theorem profilesValid2942 : retention2942.ProfilesValid := by
  exact MergedCutProfiles.Batch459.valid18367
theorem numericValid2942 : retention2942.NumericValid := by decide +kernel
def certificate2942 : RatCutBinCertificate := ⟨⟨retention2942,(375986754775867947/200000000000000000),(12287303118992409/500000000000000000),(8894162574352425643/1000000000000000000),(265349954764930120907/62500000000000000),(1775578821059198271/1000000000000000000)⟩,(249891788975196571/250000000000000000),(8221284604957683/31250000000000000),(385567874724345067/1000000000000000000),(130639704026231131/200000000000000000)⟩
theorem valid2942 : certificate2942.Valid := by decide +kernel
theorem sound2942 : certificate2942.Sound := rat_cut_bin_certificate_sound certificate2942 profilesValid2942 numericValid2942 valid2942

def retention2943 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(1/2),64,1,(63843201752088532725087077875070337159/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch032.profile1296,(fun _ => MergedCutProfiles.Batch032.profile1296)⟩
theorem profilesValid2943 : retention2943.ProfilesValid := by
  exact MergedCutProfiles.Batch032.valid1296
theorem numericValid2943 : retention2943.NumericValid := by decide +kernel
def certificate2943 : RatCutBinCertificate := ⟨⟨retention2943,(375986754775867947/200000000000000000),(12287303118992409/500000000000000000),(8894162574352425643/1000000000000000000),(265349954764930120907/62500000000000000),(992355762482005759/1000000000000000000)⟩,(249891788975196571/250000000000000000),(46496760068173969/100000000000000000),(178965828748068121/1000000000000000000),(174809717508838551/1000000000000000000)⟩
theorem valid2943 : certificate2943.Valid := by decide +kernel
theorem sound2943 : certificate2943.Sound := rat_cut_bin_certificate_sound certificate2943 profilesValid2943 numericValid2943 valid2943

def retention2944 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(12800000000000000000/95005518140300851637),(9004043892792520339/1000000000000000000),1,(61672091186704292576031678722507564643/36016175571170081356000000000000000000),false,MergedCutProfiles.Batch459.profile18367,(fun _ => MergedCutProfiles.Batch459.profile18367)⟩
theorem profilesValid2944 : retention2944.ProfilesValid := by
  exact MergedCutProfiles.Batch459.valid18367
theorem numericValid2944 : retention2944.NumericValid := by decide +kernel
def certificate2944 : RatCutBinCertificate := ⟨⟨retention2944,(406404208975867947/200000000000000000),(12287303118992409/500000000000000000),(8894162574352425643/1000000000000000000),(265349954764930120907/62500000000000000),(1706729765359388979/1000000000000000000)⟩,(999532138291564247/1000000000000000000),(79326787900909039/1000000000000000000),(142809042475614521/200000000000000000),(1023986448051596781/1000000000000000000)⟩
theorem valid2944 : certificate2944.Valid := by decide +kernel
theorem sound2944 : certificate2944.Sound := rat_cut_bin_certificate_sound certificate2944 profilesValid2944 numericValid2944 valid2944

def retention2945 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(1/2),64,1,(63843201752088532725087077875070337159/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch032.profile1296,(fun _ => MergedCutProfiles.Batch032.profile1296)⟩
theorem profilesValid2945 : retention2945.ProfilesValid := by
  exact MergedCutProfiles.Batch032.valid1296
theorem numericValid2945 : retention2945.NumericValid := by decide +kernel
def certificate2945 : RatCutBinCertificate := ⟨⟨retention2945,(406404208975867947/200000000000000000),(12287303118992409/500000000000000000),(8894162574352425643/1000000000000000000),(265349954764930120907/62500000000000000),(39677421788598751/40000000000000000)⟩,(999532138291564247/1000000000000000000),(68245054238749173/500000000000000000),(36893684175787411/62500000000000000),(576329849888353103/1000000000000000000)⟩
theorem valid2945 : certificate2945.Valid := by decide +kernel
theorem sound2945 : certificate2945.Sound := rat_cut_bin_certificate_sound certificate2945 profilesValid2945 numericValid2945 valid2945

def retention2946 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(616198346541473517/435646048538307062267),(122019474562668023/200000000000000000),4,(580349530158920619043/256000000000000000000),true,MergedCutProfiles.Batch459.profile18368,![MergedCutProfiles.Batch459.profile18368,MergedCutProfiles.Batch459.profile18369,MergedCutProfiles.Batch459.profile18370,MergedCutProfiles.Batch459.profile18371,MergedCutProfiles.Batch459.profile18372,MergedCutProfiles.Batch459.profile18373,MergedCutProfiles.Batch459.profile18374,MergedCutProfiles.Batch325.profile13024,MergedCutProfiles.Batch033.profile1330,MergedCutProfiles.Batch459.profile18375,MergedCutProfiles.Batch325.profile13025,MergedCutProfiles.Batch459.profile18376,MergedCutProfiles.Batch459.profile18377,MergedCutProfiles.Batch032.profile1317,MergedCutProfiles.Batch459.profile18378,MergedCutProfiles.Batch325.profile13027]⟩
theorem profilesValid2946 : retention2946.ProfilesValid := by
  change ∀ j : Fin 16, (retention2946.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch459.valid18368
  · exact MergedCutProfiles.Batch459.valid18369
  · exact MergedCutProfiles.Batch459.valid18370
  · exact MergedCutProfiles.Batch459.valid18371
  · exact MergedCutProfiles.Batch459.valid18372
  · exact MergedCutProfiles.Batch459.valid18373
  · exact MergedCutProfiles.Batch459.valid18374
  · exact MergedCutProfiles.Batch325.valid13024
  · exact MergedCutProfiles.Batch033.valid1330
  · exact MergedCutProfiles.Batch459.valid18375
  · exact MergedCutProfiles.Batch325.valid13025
  · exact MergedCutProfiles.Batch459.valid18376
  · exact MergedCutProfiles.Batch459.valid18377
  · exact MergedCutProfiles.Batch032.valid1317
  · exact MergedCutProfiles.Batch459.valid18378
  · exact MergedCutProfiles.Batch325.valid13027
theorem numericValid2946 : retention2946.NumericValid := by decide +kernel
def certificate2946 : RatCutBinCertificate := ⟨⟨retention2946,(117835560091006109/62500000000000000),(5353370290855499/200000000000000000),(4507549105661741169/500000000000000000),(1973339312607329729513/500000000000000000),(561149697707422483/250000000000000000)⟩,(7808859560799483/7812500000000000),(114703843952407233/200000000000000000),(13453104409982589/125000000000000000),(24537837688715913/500000000000000000)⟩
theorem valid2946 : certificate2946.Valid := by decide +kernel
theorem sound2946 : certificate2946.Sound := rat_cut_bin_certificate_sound certificate2946 profilesValid2946 numericValid2946 valid2946

def retention2947 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(173650505000000000/62235149791186723181),(616198346541473517/1000000000000000000),4,(144943807622177492037/64000000000000000000),true,MergedCutProfiles.Batch459.profile18369,![MergedCutProfiles.Batch459.profile18369,MergedCutProfiles.Batch459.profile18371,MergedCutProfiles.Batch459.profile18379,MergedCutProfiles.Batch325.profile13024,MergedCutProfiles.Batch459.profile18375,MergedCutProfiles.Batch459.profile18376,MergedCutProfiles.Batch459.profile18380,MergedCutProfiles.Batch459.profile18381,MergedCutProfiles.Batch033.profile1331,MergedCutProfiles.Batch459.profile18382,MergedCutProfiles.Batch032.profile1318,MergedCutProfiles.Batch459.profile18383,MergedCutProfiles.Batch459.profile18384,MergedCutProfiles.Batch459.profile18385,MergedCutProfiles.Batch325.profile13030,MergedCutProfiles.Batch033.profile1355]⟩
theorem profilesValid2947 : retention2947.ProfilesValid := by
  change ∀ j : Fin 16, (retention2947.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch459.valid18369
  · exact MergedCutProfiles.Batch459.valid18371
  · exact MergedCutProfiles.Batch459.valid18379
  · exact MergedCutProfiles.Batch325.valid13024
  · exact MergedCutProfiles.Batch459.valid18375
  · exact MergedCutProfiles.Batch459.valid18376
  · exact MergedCutProfiles.Batch459.valid18380
  · exact MergedCutProfiles.Batch459.valid18381
  · exact MergedCutProfiles.Batch033.valid1331
  · exact MergedCutProfiles.Batch459.valid18382
  · exact MergedCutProfiles.Batch032.valid1318
  · exact MergedCutProfiles.Batch459.valid18383
  · exact MergedCutProfiles.Batch459.valid18384
  · exact MergedCutProfiles.Batch459.valid18385
  · exact MergedCutProfiles.Batch325.valid13030
  · exact MergedCutProfiles.Batch033.valid1355
theorem numericValid2947 : retention2947.NumericValid := by decide +kernel
def certificate2947 : RatCutBinCertificate := ⟨⟨retention2947,(117835560091006109/62500000000000000),(5353370290855499/200000000000000000),(4507549105661741169/500000000000000000),(1973339312607329729513/500000000000000000),(2242355433359053647/1000000000000000000)⟩,(7808859560799483/7812500000000000),(22816751541422523/40000000000000000),(109356958057073633/1000000000000000000),(1559916642497819/31250000000000000)⟩
theorem valid2947 : certificate2947.Valid := by decide +kernel
theorem sound2947 : certificate2947.Sound := rat_cut_bin_certificate_sound certificate2947 profilesValid2947 numericValid2947 valid2947

def retention2948 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(2224220025715320293/435646048538307062267),(243110707/200000000),(51/20),(11161648451586036913139845888652435511/4862214140000000000000000000000000000),true,MergedCutProfiles.Batch459.profile18386,![MergedCutProfiles.Batch459.profile18386,MergedCutProfiles.Batch032.profile1316,MergedCutProfiles.Batch325.profile13025,MergedCutProfiles.Batch326.profile13049,MergedCutProfiles.Batch033.profile1331,MergedCutProfiles.Batch032.profile1318,MergedCutProfiles.Batch326.profile13057,MergedCutProfiles.Batch326.profile13041,MergedCutProfiles.Batch325.profile13031,MergedCutProfiles.Batch032.profile1319,MergedCutProfiles.Batch459.profile18387,MergedCutProfiles.Batch033.profile1320,MergedCutProfiles.Batch459.profile18388,MergedCutProfiles.Batch033.profile1321,MergedCutProfiles.Batch033.profile1344,MergedCutProfiles.Batch326.profile13045]⟩
theorem profilesValid2948 : retention2948.ProfilesValid := by
  change ∀ j : Fin 16, (retention2948.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch459.valid18386
  · exact MergedCutProfiles.Batch032.valid1316
  · exact MergedCutProfiles.Batch325.valid13025
  · exact MergedCutProfiles.Batch326.valid13049
  · exact MergedCutProfiles.Batch033.valid1331
  · exact MergedCutProfiles.Batch032.valid1318
  · exact MergedCutProfiles.Batch326.valid13057
  · exact MergedCutProfiles.Batch326.valid13041
  · exact MergedCutProfiles.Batch325.valid13031
  · exact MergedCutProfiles.Batch032.valid1319
  · exact MergedCutProfiles.Batch459.valid18387
  · exact MergedCutProfiles.Batch033.valid1320
  · exact MergedCutProfiles.Batch459.valid18388
  · exact MergedCutProfiles.Batch033.valid1321
  · exact MergedCutProfiles.Batch033.valid1344
  · exact MergedCutProfiles.Batch326.valid13045
theorem numericValid2948 : retention2948.NumericValid := by decide +kernel
def certificate2948 : RatCutBinCertificate := ⟨⟨retention2948,(117835560091006109/62500000000000000),(5353370290855499/200000000000000000),(4507549105661741169/500000000000000000),(1973339312607329729513/500000000000000000),(2281315037194117571/1000000000000000000)⟩,(7808859560799483/7812500000000000),(15304257940917109/40000000000000000),(124901384246262253/500000000000000000),(2166684993958887/12500000000000000)⟩
theorem valid2948 : certificate2948.Valid := by decide +kernel
theorem sound2948 : certificate2948.Sound := rat_cut_bin_certificate_sound certificate2948 profilesValid2948 numericValid2948 valid2948

def retention2949 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(64000000000000000000/435646048538307062267),(2224220025715320293/1000000000000000000),(17/10),(1570847347024822618760542615682833327279/889688010286128117200000000000000000000),false,MergedCutProfiles.Batch459.profile18389,(fun _ => MergedCutProfiles.Batch459.profile18389)⟩
theorem profilesValid2949 : retention2949.ProfilesValid := by
  exact MergedCutProfiles.Batch459.valid18389
theorem numericValid2949 : retention2949.NumericValid := by decide +kernel
def certificate2949 : RatCutBinCertificate := ⟨⟨retention2949,(117835560091006109/62500000000000000),(5353370290855499/200000000000000000),(4507549105661741169/500000000000000000),(1973339312607329729513/500000000000000000),(1756099552029491881/1000000000000000000)⟩,(7808859560799483/7812500000000000),(389182917113229637/1000000000000000000),(243541037472635767/1000000000000000000),(197492846645980497/1000000000000000000)⟩
theorem valid2949 : certificate2949.Valid := by decide +kernel
theorem sound2949 : certificate2949.Sound := rat_cut_bin_certificate_sound certificate2949 profilesValid2949 numericValid2949 valid2949

def retention2950 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1/2),64,1,(255373261473046173696668873617783571559/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch034.profile1386,(fun _ => MergedCutProfiles.Batch034.profile1386)⟩
theorem profilesValid2950 : retention2950.ProfilesValid := by
  exact MergedCutProfiles.Batch034.valid1386
theorem numericValid2950 : retention2950.NumericValid := by decide +kernel
def certificate2950 : RatCutBinCertificate := ⟨⟨retention2950,(117835560091006109/62500000000000000),(5353370290855499/200000000000000000),(4507549105661741169/500000000000000000),(1973339312607329729513/500000000000000000),(4959769636273053/5000000000000000)⟩,(7808859560799483/7812500000000000),(233441486880775793/500000000000000000),(177503010127300541/1000000000000000000),(173305939217217611/1000000000000000000)⟩
theorem valid2950 : certificate2950.Valid := by decide +kernel
theorem sound2950 : certificate2950.Sound := rat_cut_bin_certificate_sound certificate2950 profilesValid2950 numericValid2950 valid2950

def retention2951 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(64000000000000000000/435646048538307062267),(9013517942874777859/1000000000000000000),1,(60707313911426369461689822439487367043/36054071771499111436000000000000000000),false,MergedCutProfiles.Batch459.profile18389,(fun _ => MergedCutProfiles.Batch459.profile18389)⟩
theorem profilesValid2951 : retention2951.ProfilesValid := by
  exact MergedCutProfiles.Batch459.valid18389
theorem numericValid2951 : retention2951.NumericValid := by decide +kernel
def certificate2951 : RatCutBinCertificate := ⟨⟨retention2951,(127457716028506109/62500000000000000),(5353370290855499/200000000000000000),(4507549105661741169/500000000000000000),(1973339312607329729513/500000000000000000),(1677730252838499797/1000000000000000000)⟩,(499747986425672961/500000000000000000),(16187703276410571/200000000000000000),(710197035477187679/1000000000000000000),(1004008483043583651/1000000000000000000)⟩
theorem valid2951 : certificate2951.Valid := by decide +kernel
theorem sound2951 : certificate2951.Sound := rat_cut_bin_certificate_sound certificate2951 profilesValid2951 numericValid2951 valid2951

def certificates : List RatCutBinCertificate := [certificate2940,certificate2941,certificate2942,certificate2943,certificate2944,certificate2945,certificate2946,certificate2947,certificate2948,certificate2949,certificate2950,certificate2951]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2940,List.forall_mem_cons.mpr ⟨sound2941,List.forall_mem_cons.mpr ⟨sound2942,List.forall_mem_cons.mpr ⟨sound2943,List.forall_mem_cons.mpr ⟨sound2944,List.forall_mem_cons.mpr ⟨sound2945,List.forall_mem_cons.mpr ⟨sound2946,List.forall_mem_cons.mpr ⟨sound2947,List.forall_mem_cons.mpr ⟨sound2948,List.forall_mem_cons.mpr ⟨sound2949,List.forall_mem_cons.mpr ⟨sound2950,List.forall_mem_cons.mpr ⟨sound2951,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch245
