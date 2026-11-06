import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch043
import Cycle12.MergedCutProfiles.Batch044
import Cycle12.MergedCutProfiles.Batch045
import Cycle12.MergedCutProfiles.Batch046
import Cycle12.MergedCutProfiles.Batch332
import Cycle12.MergedCutProfiles.Batch333
import Cycle12.MergedCutProfiles.Batch334
import Cycle12.MergedCutProfiles.Batch463
import Cycle12.MergedCutProfiles.Batch464

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch249

def retention2988 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(1391421146352156863/59016506563303541498),(25890857240555471/20000000000000000),(49/20),(55858964111494001231/25600000000000000000),true,MergedCutProfiles.Batch332.profile13287,![MergedCutProfiles.Batch332.profile13287,MergedCutProfiles.Batch332.profile13290,MergedCutProfiles.Batch043.profile1752,MergedCutProfiles.Batch332.profile13294,MergedCutProfiles.Batch332.profile13304,MergedCutProfiles.Batch463.profile18541,MergedCutProfiles.Batch333.profile13330,MergedCutProfiles.Batch463.profile18542,MergedCutProfiles.Batch463.profile18543,MergedCutProfiles.Batch463.profile18544,MergedCutProfiles.Batch463.profile18545,MergedCutProfiles.Batch463.profile18546,MergedCutProfiles.Batch463.profile18547,MergedCutProfiles.Batch463.profile18548,MergedCutProfiles.Batch463.profile18549,MergedCutProfiles.Batch463.profile18550]⟩
theorem profilesValid2988 : retention2988.ProfilesValid := by
  change ∀ j : Fin 16, (retention2988.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch332.valid13287
  · exact MergedCutProfiles.Batch332.valid13290
  · exact MergedCutProfiles.Batch043.valid1752
  · exact MergedCutProfiles.Batch332.valid13294
  · exact MergedCutProfiles.Batch332.valid13304
  · exact MergedCutProfiles.Batch463.valid18541
  · exact MergedCutProfiles.Batch333.valid13330
  · exact MergedCutProfiles.Batch463.valid18542
  · exact MergedCutProfiles.Batch463.valid18543
  · exact MergedCutProfiles.Batch463.valid18544
  · exact MergedCutProfiles.Batch463.valid18545
  · exact MergedCutProfiles.Batch463.valid18546
  · exact MergedCutProfiles.Batch463.valid18547
  · exact MergedCutProfiles.Batch463.valid18548
  · exact MergedCutProfiles.Batch463.valid18549
  · exact MergedCutProfiles.Batch463.valid18550
theorem numericValid2988 : retention2988.NumericValid := by decide +kernel
def certificate2988 : RatCutBinCertificate := ⟨⟨retention2988,(957405645196595327/500000000000000000),(39310593322721927/1000000000000000000),(9659440590120051229/1000000000000000000),(2864750281502089248499/1000000000000000000),(2162898779439123071/1000000000000000000)⟩,(24983900853504023/25000000000000000),(390198773904484917/1000000000000000000),(242583747752121007/1000000000000000000),(16740336509327351/100000000000000000)⟩
theorem valid2988 : certificate2988.Valid := by decide +kernel
theorem sound2988 : certificate2988.Sound := rat_cut_bin_certificate_sound certificate2988 profilesValid2988 numericValid2988 valid2988

def retention2989 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(6400000000000000000/29508253281651770749),(1391421146352156863/200000000000000000),(11/10),(174890525154492556880130989345736906919/111313691708172549040000000000000000000),false,MergedCutProfiles.Batch463.profile18551,(fun _ => MergedCutProfiles.Batch463.profile18551)⟩
theorem profilesValid2989 : retention2989.ProfilesValid := by
  exact MergedCutProfiles.Batch463.valid18551
theorem numericValid2989 : retention2989.NumericValid := by decide +kernel
def certificate2989 : RatCutBinCertificate := ⟨⟨retention2989,(957405645196595327/500000000000000000),(39310593322721927/1000000000000000000),(9659440590120051229/1000000000000000000),(2864750281502089248499/1000000000000000000),(156257826612357183/100000000000000000)⟩,(24983900853504023/25000000000000000),(341114491633678679/1000000000000000000),(72999187357222527/250000000000000000),(69922021913215591/200000000000000000)⟩
theorem valid2989 : certificate2989.Valid := by decide +kernel
theorem sound2989 : certificate2989.Sound := rat_cut_bin_certificate_sound certificate2989 profilesValid2989 numericValid2989 valid2989

def retention2990 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(1/2),64,1,(255375917609544558015305480512676517159/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch044.profile1794,(fun _ => MergedCutProfiles.Batch044.profile1794)⟩
theorem profilesValid2990 : retention2990.ProfilesValid := by
  exact MergedCutProfiles.Batch044.valid1794
theorem numericValid2990 : retention2990.NumericValid := by decide +kernel
def certificate2990 : RatCutBinCertificate := ⟨⟨retention2990,(957405645196595327/500000000000000000),(39310593322721927/1000000000000000000),(9659440590120051229/1000000000000000000),(2864750281502089248499/1000000000000000000),(494884777314264597/500000000000000000)⟩,(24983900853504023/25000000000000000),(29657130252230657/62500000000000000),(171752635401280993/1000000000000000000),(167297823376982909/1000000000000000000)⟩
theorem valid2990 : certificate2990.Valid := by decide +kernel
theorem sound2990 : certificate2990.Sound := rat_cut_bin_certificate_sound certificate2990 profilesValid2990 numericValid2990 valid2990

def retention2991 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(6400000000000000000/29508253281651770749),(376999011924883791/40000000000000000),1,(14444897510513070762223761053720992781/9424975298122094775000000000000000000),false,MergedCutProfiles.Batch463.profile18551,(fun _ => MergedCutProfiles.Batch463.profile18551)⟩
theorem profilesValid2991 : retention2991.ProfilesValid := by
  exact MergedCutProfiles.Batch463.valid18551
theorem numericValid2991 : retention2991.NumericValid := by decide +kernel
def certificate2991 : RatCutBinCertificate := ⟨⟨retention2991,(1032617040696595327/500000000000000000),(39310593322721927/1000000000000000000),(9659440590120051229/1000000000000000000),(2864750281502089248499/1000000000000000000),(1524214334299104893/1000000000000000000)⟩,(249826361114196499/250000000000000000),(21644843790427273/250000000000000000),(69690891328280859/100000000000000000),(913701121432992017/1000000000000000000)⟩
theorem valid2991 : certificate2991.Valid := by decide +kernel
theorem sound2991 : certificate2991.Sound := rat_cut_bin_certificate_sound certificate2991 profilesValid2991 numericValid2991 valid2991

def retention2992 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(1/2),64,1,(255375917609544558015305480512676517159/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch044.profile1794,(fun _ => MergedCutProfiles.Batch044.profile1794)⟩
theorem profilesValid2992 : retention2992.ProfilesValid := by
  exact MergedCutProfiles.Batch044.valid1794
theorem numericValid2992 : retention2992.NumericValid := by decide +kernel
def certificate2992 : RatCutBinCertificate := ⟨⟨retention2992,(1032617040696595327/500000000000000000),(39310593322721927/1000000000000000000),(9659440590120051229/1000000000000000000),(2864750281502089248499/1000000000000000000),(989157385592843753/1000000000000000000)⟩,(249826361114196499/250000000000000000),(133412060202173363/1000000000000000000),(596356588759326439/1000000000000000000),(290252734245942159/500000000000000000)⟩
theorem valid2992 : certificate2992.Valid := by decide +kernel
theorem sound2992 : certificate2992.Sound := rat_cut_bin_certificate_sound certificate2992 profilesValid2992 numericValid2992 valid2992

def retention2993 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(656107979879009812/274952852136900303297),(318405970623638049/500000000000000000),4,(73561289569910627029/32000000000000000000),true,MergedCutProfiles.Batch463.profile18552,![MergedCutProfiles.Batch463.profile18552,MergedCutProfiles.Batch463.profile18553,MergedCutProfiles.Batch463.profile18554,MergedCutProfiles.Batch463.profile18555,MergedCutProfiles.Batch463.profile18556,MergedCutProfiles.Batch463.profile18557,MergedCutProfiles.Batch333.profile13359,MergedCutProfiles.Batch333.profile13348,MergedCutProfiles.Batch463.profile18558,MergedCutProfiles.Batch463.profile18559,MergedCutProfiles.Batch464.profile18560,MergedCutProfiles.Batch464.profile18561,MergedCutProfiles.Batch045.profile1814,MergedCutProfiles.Batch334.profile13360,MergedCutProfiles.Batch464.profile18562,MergedCutProfiles.Batch046.profile1842]⟩
theorem profilesValid2993 : retention2993.ProfilesValid := by
  change ∀ j : Fin 16, (retention2993.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch463.valid18552
  · exact MergedCutProfiles.Batch463.valid18553
  · exact MergedCutProfiles.Batch463.valid18554
  · exact MergedCutProfiles.Batch463.valid18555
  · exact MergedCutProfiles.Batch463.valid18556
  · exact MergedCutProfiles.Batch463.valid18557
  · exact MergedCutProfiles.Batch333.valid13359
  · exact MergedCutProfiles.Batch333.valid13348
  · exact MergedCutProfiles.Batch463.valid18558
  · exact MergedCutProfiles.Batch463.valid18559
  · exact MergedCutProfiles.Batch464.valid18560
  · exact MergedCutProfiles.Batch464.valid18561
  · exact MergedCutProfiles.Batch045.valid1814
  · exact MergedCutProfiles.Batch334.valid13360
  · exact MergedCutProfiles.Batch464.valid18562
  · exact MergedCutProfiles.Batch046.valid1842
theorem numericValid2993 : retention2993.NumericValid := by decide +kernel
def certificate2993 : RatCutBinCertificate := ⟨⟨retention2993,(1920215677186087073/1000000000000000000),(42146381475855499/1000000000000000000),(4898394465934615747/500000000000000000),(2707362291713132118157/1000000000000000000),(2265746558867610297/1000000000000000000)⟩,(3997274421083527/4000000000000000),(54584981175243523/100000000000000000),(30921618563878927/250000000000000000),(57269105205581097/1000000000000000000)⟩
theorem valid2993 : certificate2993.Valid := by decide +kernel
theorem sound2993 : certificate2993.Sound := rat_cut_bin_certificate_sound certificate2993 profilesValid2993 numericValid2993 valid2993

def retention2994 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1179453493000000000/274952852136900303297),(164026994969752453/250000000000000000),4,(4602901507983430133/2000000000000000000),true,MergedCutProfiles.Batch464.profile18563,![MergedCutProfiles.Batch464.profile18563,MergedCutProfiles.Batch464.profile18564,MergedCutProfiles.Batch044.profile1797,MergedCutProfiles.Batch464.profile18565,MergedCutProfiles.Batch464.profile18566,MergedCutProfiles.Batch464.profile18560,MergedCutProfiles.Batch464.profile18567,MergedCutProfiles.Batch464.profile18568,MergedCutProfiles.Batch046.profile1842,MergedCutProfiles.Batch464.profile18569,MergedCutProfiles.Batch045.profile1815,MergedCutProfiles.Batch334.profile13372,MergedCutProfiles.Batch045.profile1830,MergedCutProfiles.Batch464.profile18570,MergedCutProfiles.Batch046.profile1857,MergedCutProfiles.Batch464.profile18571]⟩
theorem profilesValid2994 : retention2994.ProfilesValid := by
  change ∀ j : Fin 16, (retention2994.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch464.valid18563
  · exact MergedCutProfiles.Batch464.valid18564
  · exact MergedCutProfiles.Batch044.valid1797
  · exact MergedCutProfiles.Batch464.valid18565
  · exact MergedCutProfiles.Batch464.valid18566
  · exact MergedCutProfiles.Batch464.valid18560
  · exact MergedCutProfiles.Batch464.valid18567
  · exact MergedCutProfiles.Batch464.valid18568
  · exact MergedCutProfiles.Batch046.valid1842
  · exact MergedCutProfiles.Batch464.valid18569
  · exact MergedCutProfiles.Batch045.valid1815
  · exact MergedCutProfiles.Batch334.valid13372
  · exact MergedCutProfiles.Batch045.valid1830
  · exact MergedCutProfiles.Batch464.valid18570
  · exact MergedCutProfiles.Batch046.valid1857
  · exact MergedCutProfiles.Batch464.valid18571
theorem numericValid2994 : retention2994.NumericValid := by decide +kernel
def certificate2994 : RatCutBinCertificate := ⟨⟨retention2994,(1920215677186087073/1000000000000000000),(42146381475855499/1000000000000000000),(4898394465934615747/500000000000000000),(2707362291713132118157/1000000000000000000),(2268407019738738441/1000000000000000000)⟩,(3997274421083527/4000000000000000),(133796604063293917/250000000000000000),(26049410542315799/200000000000000000),(3793118015957179/62500000000000000)⟩
theorem valid2994 : certificate2994.Valid := by decide +kernel
theorem sound2994 : certificate2994.Sound := rat_cut_bin_certificate_sound certificate2994 profilesValid2994 numericValid2994 valid2994

def retention2995 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1722457745426400830/274952852136900303297),(1179453493/1000000000),(51/20),(36472315215823746787/16000000000000000000),true,MergedCutProfiles.Batch333.profile13346,![MergedCutProfiles.Batch333.profile13346,MergedCutProfiles.Batch333.profile13347,MergedCutProfiles.Batch333.profile13348,MergedCutProfiles.Batch333.profile13349,MergedCutProfiles.Batch045.profile1814,MergedCutProfiles.Batch464.profile18572,MergedCutProfiles.Batch464.profile18573,MergedCutProfiles.Batch334.profile13362,MergedCutProfiles.Batch464.profile18574,MergedCutProfiles.Batch045.profile1816,MergedCutProfiles.Batch464.profile18571,MergedCutProfiles.Batch334.profile13364,MergedCutProfiles.Batch334.profile13386,MergedCutProfiles.Batch464.profile18575,MergedCutProfiles.Batch334.profile13375,MergedCutProfiles.Batch334.profile13366]⟩
theorem profilesValid2995 : retention2995.ProfilesValid := by
  change ∀ j : Fin 16, (retention2995.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch333.valid13346
  · exact MergedCutProfiles.Batch333.valid13347
  · exact MergedCutProfiles.Batch333.valid13348
  · exact MergedCutProfiles.Batch333.valid13349
  · exact MergedCutProfiles.Batch045.valid1814
  · exact MergedCutProfiles.Batch464.valid18572
  · exact MergedCutProfiles.Batch464.valid18573
  · exact MergedCutProfiles.Batch334.valid13362
  · exact MergedCutProfiles.Batch464.valid18574
  · exact MergedCutProfiles.Batch045.valid1816
  · exact MergedCutProfiles.Batch464.valid18571
  · exact MergedCutProfiles.Batch334.valid13364
  · exact MergedCutProfiles.Batch334.valid13386
  · exact MergedCutProfiles.Batch464.valid18575
  · exact MergedCutProfiles.Batch334.valid13375
  · exact MergedCutProfiles.Batch334.valid13366
theorem numericValid2995 : retention2995.NumericValid := by decide +kernel
def certificate2995 : RatCutBinCertificate := ⟨⟨retention2995,(1920215677186087073/1000000000000000000),(42146381475855499/1000000000000000000),(4898394465934615747/500000000000000000),(2707362291713132118157/1000000000000000000),(45169086726438001/20000000000000000)⟩,(3997274421083527/4000000000000000),(7802426098108343/20000000000000000),(242656657257014647/1000000000000000000),(165893854467203021/1000000000000000000)⟩
theorem valid2995 : certificate2995.Valid := by decide +kernel
theorem sound2995 : certificate2995.Sound := rat_cut_bin_certificate_sound certificate2995 profilesValid2995 numericValid2995 valid2995

def retention2996 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(31165087282653389734/274952852136900303297),(172245774542640083/100000000000000000),2,(513284630955289494882113691962184487/275593239268224132800000000000000000),false,MergedCutProfiles.Batch464.profile18576,(fun _ => MergedCutProfiles.Batch464.profile18576)⟩
theorem profilesValid2996 : retention2996.ProfilesValid := by
  exact MergedCutProfiles.Batch464.valid18576
theorem numericValid2996 : retention2996.NumericValid := by decide +kernel
def certificate2996 : RatCutBinCertificate := ⟨⟨retention2996,(1920215677186087073/1000000000000000000),(42146381475855499/1000000000000000000),(4898394465934615747/500000000000000000),(2707362291713132118157/1000000000000000000),(369189987286109559/200000000000000000)⟩,(3997274421083527/4000000000000000),(406014309509522619/1000000000000000000),(4560334435199289/20000000000000000),(16585521475368193/100000000000000000)⟩
theorem valid2996 : certificate2996.Valid := by decide +kernel
theorem sound2996 : certificate2996.Sound := rat_cut_bin_certificate_sound certificate2996 profilesValid2996 numericValid2996 valid2996

def retention2997 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(64000000000000000000/274952852136900303297),(15582543641326694867/500000000000000000),1,(192533100077363251854183454538532273703/124660349130613558936000000000000000000),false,MergedCutProfiles.Batch464.profile18577,(fun _ => MergedCutProfiles.Batch464.profile18577)⟩
theorem profilesValid2997 : retention2997.ProfilesValid := by
  exact MergedCutProfiles.Batch464.valid18577
theorem numericValid2997 : retention2997.NumericValid := by decide +kernel
def certificate2997 : RatCutBinCertificate := ⟨⟨retention2997,(1920215677186087073/1000000000000000000),(42146381475855499/1000000000000000000),(4898394465934615747/500000000000000000),(2707362291713132118157/1000000000000000000),(192025066655979383/125000000000000000)⟩,(3997274421083527/4000000000000000),(312105123243199259/1000000000000000000),(324458315026287017/1000000000000000000),(185425391193307/390625000000000)⟩
theorem valid2997 : certificate2997.Valid := by decide +kernel
theorem sound2997 : certificate2997.Sound := rat_cut_bin_certificate_sound certificate2997 profilesValid2997 numericValid2997 valid2997

def retention2998 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1/2),64,1,(63844131674568793248260656909441386031/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch046.profile1873,(fun _ => MergedCutProfiles.Batch046.profile1873)⟩
theorem profilesValid2998 : retention2998.ProfilesValid := by
  exact MergedCutProfiles.Batch046.valid1873
theorem numericValid2998 : retention2998.NumericValid := by decide +kernel
def certificate2998 : RatCutBinCertificate := ⟨⟨retention2998,(1920215677186087073/1000000000000000000),(42146381475855499/1000000000000000000),(4898394465934615747/500000000000000000),(2707362291713132118157/1000000000000000000),(989303670843545029/1000000000000000000)⟩,(3997274421083527/4000000000000000),(476447661869018401/1000000000000000000),(2661174450345041/15625000000000000),(82907235386139361/500000000000000000)⟩
theorem valid2998 : certificate2998.Valid := by decide +kernel
theorem sound2998 : certificate2998.Sound := rat_cut_bin_certificate_sound certificate2998 profilesValid2998 numericValid2998 valid2998

def retention2999 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(64000000000000000000/274952852136900303297),(1889538406956366239/200000000000000000),1,(56661634456154929263802057736306727379/37790768139127324780000000000000000000),false,MergedCutProfiles.Batch464.profile18577,(fun _ => MergedCutProfiles.Batch464.profile18577)⟩
theorem profilesValid2999 : retention2999.ProfilesValid := by
  exact MergedCutProfiles.Batch464.valid18577
theorem numericValid2999 : retention2999.NumericValid := by decide +kernel
def certificate2999 : RatCutBinCertificate := ⟨⟨retention2999,(2072237844186087073/1000000000000000000),(42146381475855499/1000000000000000000),(4898394465934615747/500000000000000000),(2707362291713132118157/1000000000000000000),(1490436315903363841/1000000000000000000)⟩,(199852931618237433/200000000000000000),(88759442904075903/1000000000000000000),(691847001256560487/1000000000000000000),(444980969361541663/500000000000000000)⟩
theorem valid2999 : certificate2999.Valid := by decide +kernel
theorem sound2999 : certificate2999.Sound := rat_cut_bin_certificate_sound certificate2999 profilesValid2999 numericValid2999 valid2999

def certificates : List RatCutBinCertificate := [certificate2988,certificate2989,certificate2990,certificate2991,certificate2992,certificate2993,certificate2994,certificate2995,certificate2996,certificate2997,certificate2998,certificate2999]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2988,List.forall_mem_cons.mpr ⟨sound2989,List.forall_mem_cons.mpr ⟨sound2990,List.forall_mem_cons.mpr ⟨sound2991,List.forall_mem_cons.mpr ⟨sound2992,List.forall_mem_cons.mpr ⟨sound2993,List.forall_mem_cons.mpr ⟨sound2994,List.forall_mem_cons.mpr ⟨sound2995,List.forall_mem_cons.mpr ⟨sound2996,List.forall_mem_cons.mpr ⟨sound2997,List.forall_mem_cons.mpr ⟨sound2998,List.forall_mem_cons.mpr ⟨sound2999,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch249
