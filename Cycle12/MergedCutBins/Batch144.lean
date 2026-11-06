import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch276
import Cycle12.MergedCutProfiles.Batch277
import Cycle12.MergedCutProfiles.Batch278

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch144

def retention1728 : RatCutRetentionCertificate := ⟨(519/8000),(13/200),(1/2),(1280477459258422807/250000000000000000),(11/10),(126760300938871294789612119479447261711/128047745925842280700000000000000000000),false,MergedCutProfiles.Batch276.profile11058,(fun _ => MergedCutProfiles.Batch276.profile11058)⟩
theorem profilesValid1728 : retention1728.ProfilesValid := by
  exact MergedCutProfiles.Batch276.valid11058
theorem numericValid1728 : retention1728.NumericValid := by decide +kernel
def certificate1728 : RatCutBinCertificate := ⟨⟨retention1728,(2389906133242459287/1000000000000000000),(55239130418189853/250000000000000000),(17376375804605394201/1000000000000000000),(35871773170322222709/200000000000000000),(29890920279345351/31250000000000000)⟩,(247393409396427097/250000000000000000),(424961796056277957/1000000000000000000),(105686986228453473/500000000000000000),(157400127437012297/1000000000000000000)⟩
theorem valid1728 : certificate1728.Valid := by decide +kernel
theorem sound1728 : certificate1728.Sound := rat_cut_bin_certificate_sound certificate1728 profilesValid1728 numericValid1728 valid1728

def retention1729 : RatCutRetentionCertificate := ⟨(519/8000),(13/200),(1/2),64,1,(15963509942512971706994076727972179999/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch276.profile11058,(fun _ => MergedCutProfiles.Batch276.profile11058)⟩
theorem profilesValid1729 : retention1729.ProfilesValid := by
  exact MergedCutProfiles.Batch276.valid11058
theorem numericValid1729 : retention1729.NumericValid := by decide +kernel
def certificate1729 : RatCutBinCertificate := ⟨⟨retention1729,(2389906133242459287/1000000000000000000),(55239130418189853/250000000000000000),(17376375804605394201/1000000000000000000),(35871773170322222709/200000000000000000),(967328942649303463/1000000000000000000)⟩,(247393409396427097/250000000000000000),(23791045604138047/62500000000000000),(251680799875924983/1000000000000000000),(237307492870146469/1000000000000000000)⟩
theorem valid1729 : certificate1729.Valid := by decide +kernel
theorem sound1729 : certificate1729.Sound := rat_cut_bin_certificate_sound certificate1729 profilesValid1729 numericValid1729 valid1729

def retention1730 : RatCutRetentionCertificate := ⟨(519/8000),(13/200),(4789905411596043710/10313834274951837531),(765253149633769287/250000000000000000),(5/4),(203859457743302692007306883658480889/191313287408442321750000000000000000),false,MergedCutProfiles.Batch276.profile11059,(fun _ => MergedCutProfiles.Batch276.profile11059)⟩
theorem profilesValid1730 : retention1730.ProfilesValid := by
  exact MergedCutProfiles.Batch276.valid11059
theorem numericValid1730 : retention1730.NumericValid := by decide +kernel
def certificate1730 : RatCutBinCertificate := ⟨⟨retention1730,(2700828609242459287/1000000000000000000),(55239130418189853/250000000000000000),(17376375804605394201/1000000000000000000),(35871773170322222709/200000000000000000),(255658995805343337/250000000000000000)⟩,(49410634098564271/50000000000000000),(190607157410286217/500000000000000000),(251142699462540593/1000000000000000000),(167027367674776189/1000000000000000000)⟩
theorem valid1730 : certificate1730.Valid := by decide +kernel
theorem sound1730 : certificate1730.Sound := rat_cut_bin_certificate_sound certificate1730 profilesValid1730 numericValid1730 valid1730

def retention1731 : RatCutRetentionCertificate := ⟨(519/8000),(13/200),(5084581113881977214/10313834274951837531),(478990541159604371/100000000000000000),(11/10),(479310774285826322831859696074411801/478990541159604371000000000000000000),false,MergedCutProfiles.Batch276.profile11060,(fun _ => MergedCutProfiles.Batch276.profile11060)⟩
theorem profilesValid1731 : retention1731.ProfilesValid := by
  exact MergedCutProfiles.Batch276.valid11060
theorem numericValid1731 : retention1731.NumericValid := by decide +kernel
def certificate1731 : RatCutBinCertificate := ⟨⟨retention1731,(2700828609242459287/1000000000000000000),(55239130418189853/250000000000000000),(17376375804605394201/1000000000000000000),(35871773170322222709/200000000000000000),(481440933542079333/500000000000000000)⟩,(49410634098564271/50000000000000000),(404871551725383981/1000000000000000000),(229048335727489801/1000000000000000000),(33943257646990789/200000000000000000)⟩
theorem valid1731 : certificate1731.Valid := by decide +kernel
theorem sound1731 : certificate1731.Sound := rat_cut_bin_certificate_sound certificate1731 profilesValid1731 numericValid1731 valid1731

def retention1732 : RatCutRetentionCertificate := ⟨(519/8000),(13/200),(155618997727902939/312540432574298107),(2542290556940988607/500000000000000000),(11/10),(63153766238929066258824938935409519927/63557263923524715175000000000000000000),false,MergedCutProfiles.Batch276.profile11061,(fun _ => MergedCutProfiles.Batch276.profile11061)⟩
theorem profilesValid1732 : retention1732.ProfilesValid := by
  exact MergedCutProfiles.Batch276.valid11061
theorem numericValid1732 : retention1732.NumericValid := by decide +kernel
def certificate1732 : RatCutBinCertificate := ⟨⟨retention1732,(2700828609242459287/1000000000000000000),(55239130418189853/250000000000000000),(17376375804605394201/1000000000000000000),(35871773170322222709/200000000000000000),(955865251496548419/1000000000000000000)⟩,(49410634098564271/50000000000000000),(203921774038882903/500000000000000000),(226372082149184317/1000000000000000000),(42018056146273811/250000000000000000)⟩
theorem valid1732 : certificate1732.Valid := by decide +kernel
theorem sound1732 : certificate1732.Sound := rat_cut_bin_certificate_sound certificate1732 profilesValid1732 numericValid1732 valid1732

def retention1733 : RatCutRetentionCertificate := ⟨(519/8000),(13/200),(1/2),(5135426925020796987/1000000000000000000),(11/10),(225968071591356742367656726201563909119/228241196667590977200000000000000000000),false,MergedCutProfiles.Batch276.profile11058,(fun _ => MergedCutProfiles.Batch276.profile11058)⟩
theorem profilesValid1733 : retention1733.ProfilesValid := by
  exact MergedCutProfiles.Batch276.valid11058
theorem numericValid1733 : retention1733.NumericValid := by decide +kernel
def certificate1733 : RatCutBinCertificate := ⟨⟨retention1733,(2700828609242459287/1000000000000000000),(55239130418189853/250000000000000000),(17376375804605394201/1000000000000000000),(35871773170322222709/200000000000000000),(476127295978744299/500000000000000000)⟩,(49410634098564271/50000000000000000),(102347491665338693/250000000000000000),(112494060144578133/500000000000000000),(41680237829996411/250000000000000000)⟩
theorem valid1733 : certificate1733.Valid := by decide +kernel
theorem sound1733 : certificate1733.Sound := rat_cut_bin_certificate_sound certificate1733 profilesValid1733 numericValid1733 valid1733

def retention1734 : RatCutRetentionCertificate := ⟨(13/200),(521/8000),(154500651799432838/1140683297626154127),(915535368722335319/1000000000000000000),(49/20),(2305109778622638436799/1280000000000000000000),true,MergedCutProfiles.Batch276.profile11062,![MergedCutProfiles.Batch276.profile11062,MergedCutProfiles.Batch276.profile11063,MergedCutProfiles.Batch276.profile11064,MergedCutProfiles.Batch276.profile11065,MergedCutProfiles.Batch276.profile11066,MergedCutProfiles.Batch276.profile11067,MergedCutProfiles.Batch276.profile11068,MergedCutProfiles.Batch276.profile11069,MergedCutProfiles.Batch276.profile11070,MergedCutProfiles.Batch276.profile11071,MergedCutProfiles.Batch276.profile11072,MergedCutProfiles.Batch276.profile11073,MergedCutProfiles.Batch276.profile11074,MergedCutProfiles.Batch276.profile11075,MergedCutProfiles.Batch276.profile11076,MergedCutProfiles.Batch276.profile11077]⟩
theorem profilesValid1734 : retention1734.ProfilesValid := by
  change ∀ j : Fin 16, (retention1734.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch276.valid11062
  · exact MergedCutProfiles.Batch276.valid11063
  · exact MergedCutProfiles.Batch276.valid11064
  · exact MergedCutProfiles.Batch276.valid11065
  · exact MergedCutProfiles.Batch276.valid11066
  · exact MergedCutProfiles.Batch276.valid11067
  · exact MergedCutProfiles.Batch276.valid11068
  · exact MergedCutProfiles.Batch276.valid11069
  · exact MergedCutProfiles.Batch276.valid11070
  · exact MergedCutProfiles.Batch276.valid11071
  · exact MergedCutProfiles.Batch276.valid11072
  · exact MergedCutProfiles.Batch276.valid11073
  · exact MergedCutProfiles.Batch276.valid11074
  · exact MergedCutProfiles.Batch276.valid11075
  · exact MergedCutProfiles.Batch276.valid11076
  · exact MergedCutProfiles.Batch276.valid11077
theorem numericValid1734 : retention1734.NumericValid := by decide +kernel
def certificate1734 : RatCutBinCertificate := ⟨⟨retention1734,(2387262251452557611/1000000000000000000),(221988859453895127/1000000000000000000),(1741804900315851241/100000000000000000),(178957909333695734639/1000000000000000000),(69051373325299729/40000000000000000)⟩,(19791508113826381/20000000000000000),(167796962816508937/500000000000000000),(297977993021686511/1000000000000000000),(15773515630145919/100000000000000000)⟩
theorem valid1734 : certificate1734.Valid := by decide +kernel
theorem sound1734 : certificate1734.Sound := rat_cut_bin_certificate_sound certificate1734 profilesValid1734 numericValid1734 valid1734

def retention1735 : RatCutRetentionCertificate := ⟨(13/200),(521/8000),(2903718324562158638/10266149678635387143),(695252933097447771/500000000000000000),(17/10),(917360723591442876831/640000000000000000000),true,MergedCutProfiles.Batch276.profile11078,![MergedCutProfiles.Batch276.profile11078,MergedCutProfiles.Batch276.profile11079,MergedCutProfiles.Batch277.profile11080,MergedCutProfiles.Batch277.profile11081,MergedCutProfiles.Batch277.profile11082,MergedCutProfiles.Batch277.profile11083,MergedCutProfiles.Batch277.profile11084,MergedCutProfiles.Batch277.profile11085,MergedCutProfiles.Batch277.profile11086,MergedCutProfiles.Batch277.profile11087,MergedCutProfiles.Batch277.profile11088,MergedCutProfiles.Batch277.profile11089,MergedCutProfiles.Batch277.profile11090,MergedCutProfiles.Batch277.profile11091,MergedCutProfiles.Batch277.profile11092,MergedCutProfiles.Batch277.profile11093]⟩
theorem profilesValid1735 : retention1735.ProfilesValid := by
  change ∀ j : Fin 16, (retention1735.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch276.valid11078
  · exact MergedCutProfiles.Batch276.valid11079
  · exact MergedCutProfiles.Batch277.valid11080
  · exact MergedCutProfiles.Batch277.valid11081
  · exact MergedCutProfiles.Batch277.valid11082
  · exact MergedCutProfiles.Batch277.valid11083
  · exact MergedCutProfiles.Batch277.valid11084
  · exact MergedCutProfiles.Batch277.valid11085
  · exact MergedCutProfiles.Batch277.valid11086
  · exact MergedCutProfiles.Batch277.valid11087
  · exact MergedCutProfiles.Batch277.valid11088
  · exact MergedCutProfiles.Batch277.valid11089
  · exact MergedCutProfiles.Batch277.valid11090
  · exact MergedCutProfiles.Batch277.valid11091
  · exact MergedCutProfiles.Batch277.valid11092
  · exact MergedCutProfiles.Batch277.valid11093
theorem numericValid1735 : retention1735.NumericValid := by decide +kernel
def certificate1735 : RatCutBinCertificate := ⟨⟨retention1735,(2387262251452557611/1000000000000000000),(221988859453895127/1000000000000000000),(1741804900315851241/100000000000000000),(178957909333695734639/1000000000000000000),(1381626343984185623/1000000000000000000)⟩,(19791508113826381/20000000000000000),(9180696034072101/25000000000000000),(264889746993562347/1000000000000000000),(158189227489349903/1000000000000000000)⟩
theorem valid1735 : certificate1735.Valid := by decide +kernel
theorem sound1735 : certificate1735.Sound := rat_cut_bin_certificate_sound certificate1735 profilesValid1735 numericValid1735 valid1735

def retention1736 : RatCutRetentionCertificate := ⟨(13/200),(521/8000),(4543769641205381800/10266149678635387143),(1451859162281079319/500000000000000000),(11/10),(689115257915654204947/640000000000000000000),true,MergedCutProfiles.Batch277.profile11094,![MergedCutProfiles.Batch277.profile11094,MergedCutProfiles.Batch277.profile11095,MergedCutProfiles.Batch277.profile11096,MergedCutProfiles.Batch277.profile11097,MergedCutProfiles.Batch277.profile11098,MergedCutProfiles.Batch277.profile11099,MergedCutProfiles.Batch277.profile11100,MergedCutProfiles.Batch277.profile11101,MergedCutProfiles.Batch277.profile11102,MergedCutProfiles.Batch277.profile11103,MergedCutProfiles.Batch277.profile11104,MergedCutProfiles.Batch277.profile11105,MergedCutProfiles.Batch277.profile11106,MergedCutProfiles.Batch277.profile11107,MergedCutProfiles.Batch277.profile11108,MergedCutProfiles.Batch277.profile11109]⟩
theorem profilesValid1736 : retention1736.ProfilesValid := by
  change ∀ j : Fin 16, (retention1736.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch277.valid11094
  · exact MergedCutProfiles.Batch277.valid11095
  · exact MergedCutProfiles.Batch277.valid11096
  · exact MergedCutProfiles.Batch277.valid11097
  · exact MergedCutProfiles.Batch277.valid11098
  · exact MergedCutProfiles.Batch277.valid11099
  · exact MergedCutProfiles.Batch277.valid11100
  · exact MergedCutProfiles.Batch277.valid11101
  · exact MergedCutProfiles.Batch277.valid11102
  · exact MergedCutProfiles.Batch277.valid11103
  · exact MergedCutProfiles.Batch277.valid11104
  · exact MergedCutProfiles.Batch277.valid11105
  · exact MergedCutProfiles.Batch277.valid11106
  · exact MergedCutProfiles.Batch277.valid11107
  · exact MergedCutProfiles.Batch277.valid11108
  · exact MergedCutProfiles.Batch277.valid11109
theorem numericValid1736 : retention1736.NumericValid := by decide +kernel
def certificate1736 : RatCutBinCertificate := ⟨⟨retention1736,(2387262251452557611/1000000000000000000),(221988859453895127/1000000000000000000),(1741804900315851241/100000000000000000),(178957909333695734639/1000000000000000000),(521630999686390141/500000000000000000)⟩,(19791508113826381/20000000000000000),(6516344701020309/15625000000000000),(218221920787751241/1000000000000000000),(78827929029588147/500000000000000000)⟩
theorem valid1736 : certificate1736.Valid := by decide +kernel
theorem sound1736 : certificate1736.Sound := rat_cut_bin_certificate_sound certificate1736 profilesValid1736 numericValid1736 valid1736

def retention1737 : RatCutRetentionCertificate := ⟨(13/200),(521/8000),(5019148478447194979/10266149678635387143),(22718848206026909/5000000000000000),1,(6256992122193787927/6400000000000000000),true,MergedCutProfiles.Batch277.profile11110,![MergedCutProfiles.Batch277.profile11110,MergedCutProfiles.Batch277.profile11111,MergedCutProfiles.Batch277.profile11112,MergedCutProfiles.Batch277.profile11113,MergedCutProfiles.Batch277.profile11114,MergedCutProfiles.Batch277.profile11115,MergedCutProfiles.Batch277.profile11116,MergedCutProfiles.Batch277.profile11117,MergedCutProfiles.Batch277.profile11118,MergedCutProfiles.Batch277.profile11119,MergedCutProfiles.Batch278.profile11120,MergedCutProfiles.Batch278.profile11121,MergedCutProfiles.Batch278.profile11122,MergedCutProfiles.Batch278.profile11123,MergedCutProfiles.Batch278.profile11124,MergedCutProfiles.Batch278.profile11125]⟩
theorem profilesValid1737 : retention1737.ProfilesValid := by
  change ∀ j : Fin 16, (retention1737.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch277.valid11110
  · exact MergedCutProfiles.Batch277.valid11111
  · exact MergedCutProfiles.Batch277.valid11112
  · exact MergedCutProfiles.Batch277.valid11113
  · exact MergedCutProfiles.Batch277.valid11114
  · exact MergedCutProfiles.Batch277.valid11115
  · exact MergedCutProfiles.Batch277.valid11116
  · exact MergedCutProfiles.Batch277.valid11117
  · exact MergedCutProfiles.Batch277.valid11118
  · exact MergedCutProfiles.Batch277.valid11119
  · exact MergedCutProfiles.Batch278.valid11120
  · exact MergedCutProfiles.Batch278.valid11121
  · exact MergedCutProfiles.Batch278.valid11122
  · exact MergedCutProfiles.Batch278.valid11123
  · exact MergedCutProfiles.Batch278.valid11124
  · exact MergedCutProfiles.Batch278.valid11125
theorem numericValid1737 : retention1737.NumericValid := by decide +kernel
def certificate1737 : RatCutBinCertificate := ⟨⟨retention1737,(2387262251452557611/1000000000000000000),(221988859453895127/1000000000000000000),(1741804900315851241/100000000000000000),(178957909333695734639/1000000000000000000),(473610813924519879/500000000000000000)⟩,(19791508113826381/20000000000000000),(217010276085482677/500000000000000000),(203717914894107657/1000000000000000000),(157815948290255539/1000000000000000000)⟩
theorem valid1737 : certificate1737.Valid := by decide +kernel
theorem sound1737 : certificate1737.Sound := rat_cut_bin_certificate_sound certificate1737 profilesValid1737 numericValid1737 valid1737

def retention1738 : RatCutRetentionCertificate := ⟨(13/200),(521/8000),(5069339963231666929/10266149678635387143),(5019148478447194979/1000000000000000000),(11/10),(2009710861923337739856836719190758067639/2007659391378877991600000000000000000000),false,MergedCutProfiles.Batch278.profile11126,(fun _ => MergedCutProfiles.Batch278.profile11126)⟩
theorem profilesValid1738 : retention1738.ProfilesValid := by
  exact MergedCutProfiles.Batch278.valid11126
theorem numericValid1738 : retention1738.NumericValid := by decide +kernel
def certificate1738 : RatCutBinCertificate := ⟨⟨retention1738,(2387262251452557611/1000000000000000000),(221988859453895127/1000000000000000000),(1741804900315851241/100000000000000000),(178957909333695734639/1000000000000000000),(193509341787538083/200000000000000000)⟩,(19791508113826381/20000000000000000),(84149600942757299/200000000000000000),(43000164523038387/200000000000000000),(80625009755821243/500000000000000000)⟩
theorem valid1738 : certificate1738.Valid := by decide +kernel
theorem sound1738 : certificate1738.Sound := rat_cut_bin_certificate_sound certificate1738 profilesValid1738 numericValid1738 valid1738

def retention1739 : RatCutRetentionCertificate := ⟨(13/200),(521/8000),(5120033362863983599/10266149678635387143),(5069339963231666929/1000000000000000000),(11/10),(2011495440486205323916484635713560807719/2027735985292666771600000000000000000000),false,MergedCutProfiles.Batch278.profile11127,(fun _ => MergedCutProfiles.Batch278.profile11127)⟩
theorem profilesValid1739 : retention1739.ProfilesValid := by
  exact MergedCutProfiles.Batch278.valid11127
theorem numericValid1739 : retention1739.NumericValid := by decide +kernel
def certificate1739 : RatCutBinCertificate := ⟨⟨retention1739,(2387262251452557611/1000000000000000000),(221988859453895127/1000000000000000000),(1741804900315851241/100000000000000000),(178957909333695734639/1000000000000000000),(479257880258779109/500000000000000000)⟩,(19791508113826381/20000000000000000),(53039409912422007/125000000000000000),(211927712326580029/1000000000000000000),(7893908419099551/50000000000000000)⟩
theorem valid1739 : certificate1739.Valid := by decide +kernel
theorem sound1739 : certificate1739.Sound := rat_cut_bin_certificate_sound certificate1739 profilesValid1739 numericValid1739 valid1739

def certificates : List RatCutBinCertificate := [certificate1728,certificate1729,certificate1730,certificate1731,certificate1732,certificate1733,certificate1734,certificate1735,certificate1736,certificate1737,certificate1738,certificate1739]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1728,List.forall_mem_cons.mpr ⟨sound1729,List.forall_mem_cons.mpr ⟨sound1730,List.forall_mem_cons.mpr ⟨sound1731,List.forall_mem_cons.mpr ⟨sound1732,List.forall_mem_cons.mpr ⟨sound1733,List.forall_mem_cons.mpr ⟨sound1734,List.forall_mem_cons.mpr ⟨sound1735,List.forall_mem_cons.mpr ⟨sound1736,List.forall_mem_cons.mpr ⟨sound1737,List.forall_mem_cons.mpr ⟨sound1738,List.forall_mem_cons.mpr ⟨sound1739,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch144
