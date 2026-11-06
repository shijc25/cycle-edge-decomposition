import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch001
import Cycle12.MergedCutProfiles.Batch002
import Cycle12.MergedCutProfiles.Batch003
import Cycle12.MergedCutProfiles.Batch004

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch001

def retention12 : RatCutRetentionCertificate := ⟨0,(3/1000),(64000000000000000000/13394240961805562679393),(4881034354796982317/1000000000000000000),(23/20),(17077655595884718090930032163383431091359/7809654967675171707200000000000000000000),false,MergedCutProfiles.Batch001.profile70,(fun _ => MergedCutProfiles.Batch001.profile70)⟩
theorem profilesValid12 : retention12.ProfilesValid := by
  exact MergedCutProfiles.Batch001.valid70
theorem numericValid12 : retention12.NumericValid := by decide +kernel
def certificate12 : RatCutBinCertificate := ⟨⟨retention12,(1970432526952519337/1000000000000000000),(357448886238193/1000000000000000000),(1336087783505573881/200000000000000000),(22659999981574252727111/250000000000000000),(2186615000930470519/1000000000000000000)⟩,(49998913044721671/50000000000000000),(119081439209951929/1000000000000000000),(4885952523113451/7812500000000000),(88823484762897171/100000000000000000)⟩
theorem valid12 : certificate12.Valid := by decide +kernel
theorem sound12 : certificate12.Sound := rat_cut_bin_certificate_sound certificate12 profilesValid12 numericValid12 valid12

def retention13 : RatCutRetentionCertificate := ⟨0,(3/1000),(1/2),64,1,(2553689015764907893961280798454983519/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch001.profile51,(fun _ => MergedCutProfiles.Batch001.profile51)⟩
theorem profilesValid13 : retention13.ProfilesValid := by
  exact MergedCutProfiles.Batch001.valid51
theorem numericValid13 : retention13.NumericValid := by decide +kernel
def certificate13 : RatCutBinCertificate := ⟨⟨retention13,(1970432526952519337/1000000000000000000),(357448886238193/1000000000000000000),(1336087783505573881/200000000000000000),(22659999981574252727111/250000000000000000),(62339333765672661/62500000000000000)⟩,(49998913044721671/50000000000000000),(65264087088968037/250000000000000000),(194138040166079457/500000000000000000),(381326558897309921/1000000000000000000)⟩
theorem valid13 : certificate13.Valid := by decide +kernel
theorem sound13 : certificate13.Sound := rat_cut_bin_certificate_sound certificate13 profilesValid13 numericValid13 valid13

def retention14 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(585871170671687059/3750800945834192207617),(568640786208774967/1000000000000000000),4,(1247695881686480412791523755073209331/568640786208774967000000000000000000),true,MergedCutProfiles.Batch001.profile71,![MergedCutProfiles.Batch001.profile71,MergedCutProfiles.Batch001.profile72,MergedCutProfiles.Batch001.profile73,MergedCutProfiles.Batch001.profile74,MergedCutProfiles.Batch001.profile75,MergedCutProfiles.Batch001.profile76,MergedCutProfiles.Batch001.profile77,MergedCutProfiles.Batch001.profile78,MergedCutProfiles.Batch001.profile79,MergedCutProfiles.Batch002.profile80,MergedCutProfiles.Batch002.profile81,MergedCutProfiles.Batch002.profile82,MergedCutProfiles.Batch002.profile83,MergedCutProfiles.Batch002.profile83,MergedCutProfiles.Batch002.profile84,MergedCutProfiles.Batch002.profile85]⟩
theorem profilesValid14 : retention14.ProfilesValid := by
  change ∀ j : Fin 16, (retention14.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch001.valid71
  · exact MergedCutProfiles.Batch001.valid72
  · exact MergedCutProfiles.Batch001.valid73
  · exact MergedCutProfiles.Batch001.valid74
  · exact MergedCutProfiles.Batch001.valid75
  · exact MergedCutProfiles.Batch001.valid76
  · exact MergedCutProfiles.Batch001.valid77
  · exact MergedCutProfiles.Batch001.valid78
  · exact MergedCutProfiles.Batch001.valid79
  · exact MergedCutProfiles.Batch002.valid80
  · exact MergedCutProfiles.Batch002.valid81
  · exact MergedCutProfiles.Batch002.valid82
  · exact MergedCutProfiles.Batch002.valid83
  · exact MergedCutProfiles.Batch002.valid83
  · exact MergedCutProfiles.Batch002.valid84
  · exact MergedCutProfiles.Batch002.valid85
theorem numericValid14 : retention14.NumericValid := by decide +kernel
def certificate14 : RatCutBinCertificate := ⟨⟨retention14,(1795708050722680871/1000000000000000000),(637434242080419/1000000000000000000),(27022124096657033/3906250000000000),(6514935146107861847401/250000000000000000),(2193510466631806721/1000000000000000000)⟩,(199986223452875253/200000000000000000),(292638857319072481/500000000000000000),(25301815400576381/250000000000000000),(44714852551648571/1000000000000000000)⟩
theorem valid14 : certificate14.Valid := by decide +kernel
theorem sound14 : certificate14.Sound := rat_cut_bin_certificate_sound certificate14 profilesValid14 numericValid14 valid14

def retention15 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(1312491441000000000/3750800945834192207617),(585871170671687059/1000000000000000000),4,(40773040660349410543895672578534839/18308474083490220593750000000000000),true,MergedCutProfiles.Batch001.profile72,![MergedCutProfiles.Batch001.profile72,MergedCutProfiles.Batch002.profile86,MergedCutProfiles.Batch001.profile77,MergedCutProfiles.Batch001.profile79,MergedCutProfiles.Batch002.profile81,MergedCutProfiles.Batch002.profile83,MergedCutProfiles.Batch002.profile85,MergedCutProfiles.Batch002.profile87,MergedCutProfiles.Batch002.profile88,MergedCutProfiles.Batch002.profile89,MergedCutProfiles.Batch002.profile90,MergedCutProfiles.Batch002.profile91,MergedCutProfiles.Batch002.profile92,MergedCutProfiles.Batch002.profile93,MergedCutProfiles.Batch002.profile94,MergedCutProfiles.Batch002.profile95]⟩
theorem profilesValid15 : retention15.ProfilesValid := by
  change ∀ j : Fin 16, (retention15.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch001.valid72
  · exact MergedCutProfiles.Batch002.valid86
  · exact MergedCutProfiles.Batch001.valid77
  · exact MergedCutProfiles.Batch001.valid79
  · exact MergedCutProfiles.Batch002.valid81
  · exact MergedCutProfiles.Batch002.valid83
  · exact MergedCutProfiles.Batch002.valid85
  · exact MergedCutProfiles.Batch002.valid87
  · exact MergedCutProfiles.Batch002.valid88
  · exact MergedCutProfiles.Batch002.valid89
  · exact MergedCutProfiles.Batch002.valid90
  · exact MergedCutProfiles.Batch002.valid91
  · exact MergedCutProfiles.Batch002.valid92
  · exact MergedCutProfiles.Batch002.valid93
  · exact MergedCutProfiles.Batch002.valid94
  · exact MergedCutProfiles.Batch002.valid95
theorem numericValid15 : retention15.NumericValid := by decide +kernel
def certificate15 : RatCutBinCertificate := ⟨⟨retention15,(1795708050722680871/1000000000000000000),(637434242080419/1000000000000000000),(27022124096657033/3906250000000000),(6514935146107861847401/250000000000000000),(1113170946783924729/500000000000000000)⟩,(199986223452875253/200000000000000000),(564990862447939119/1000000000000000000),(28107504536724159/250000000000000000),(10112582830527543/200000000000000000)⟩
theorem valid15 : certificate15.Valid := by decide +kernel
theorem sound15 : certificate15.Sound := rat_cut_bin_certificate_sound certificate15 profilesValid15 numericValid15 valid15

def retention16 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(3180062612913783330/3750800945834192207617),(1312491441/1000000000),(12/5),(37252239789762256933/16000000000000000000),true,MergedCutProfiles.Batch001.profile75,![MergedCutProfiles.Batch001.profile75,MergedCutProfiles.Batch002.profile81,MergedCutProfiles.Batch002.profile85,MergedCutProfiles.Batch002.profile96,MergedCutProfiles.Batch002.profile91,MergedCutProfiles.Batch002.profile97,MergedCutProfiles.Batch002.profile98,MergedCutProfiles.Batch002.profile99,MergedCutProfiles.Batch002.profile100,MergedCutProfiles.Batch002.profile101,MergedCutProfiles.Batch002.profile102,MergedCutProfiles.Batch002.profile103,MergedCutProfiles.Batch002.profile104,MergedCutProfiles.Batch002.profile105,MergedCutProfiles.Batch002.profile106,MergedCutProfiles.Batch002.profile107]⟩
theorem profilesValid16 : retention16.ProfilesValid := by
  change ∀ j : Fin 16, (retention16.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch001.valid75
  · exact MergedCutProfiles.Batch002.valid81
  · exact MergedCutProfiles.Batch002.valid85
  · exact MergedCutProfiles.Batch002.valid96
  · exact MergedCutProfiles.Batch002.valid91
  · exact MergedCutProfiles.Batch002.valid97
  · exact MergedCutProfiles.Batch002.valid98
  · exact MergedCutProfiles.Batch002.valid99
  · exact MergedCutProfiles.Batch002.valid100
  · exact MergedCutProfiles.Batch002.valid101
  · exact MergedCutProfiles.Batch002.valid102
  · exact MergedCutProfiles.Batch002.valid103
  · exact MergedCutProfiles.Batch002.valid104
  · exact MergedCutProfiles.Batch002.valid105
  · exact MergedCutProfiles.Batch002.valid106
  · exact MergedCutProfiles.Batch002.valid107
theorem numericValid16 : retention16.NumericValid := by decide +kernel
def certificate16 : RatCutBinCertificate := ⟨⟨retention16,(1795708050722680871/1000000000000000000),(637434242080419/1000000000000000000),(27022124096657033/3906250000000000),(6514935146107861847401/250000000000000000),(2327867865803970471/1000000000000000000)⟩,(199986223452875253/200000000000000000),(168338591861755217/500000000000000000),(296797239441494187/1000000000000000000),(110042755154713661/500000000000000000)⟩
theorem valid16 : certificate16.Valid := by decide +kernel
theorem sound16 : certificate16.Sound := rat_cut_bin_certificate_sound certificate16 profilesValid16 numericValid16 valid16

def retention17 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(64000000000000000000/3750800945834192207617),(318006261291378333/100000000000000000),(29/20),(36847649875784779467695656674728052453/16960333935540177760000000000000000000),true,MergedCutProfiles.Batch002.profile108,![MergedCutProfiles.Batch002.profile108,MergedCutProfiles.Batch002.profile109,MergedCutProfiles.Batch002.profile110,MergedCutProfiles.Batch002.profile111,MergedCutProfiles.Batch002.profile112,MergedCutProfiles.Batch002.profile113,MergedCutProfiles.Batch002.profile114,MergedCutProfiles.Batch002.profile115,MergedCutProfiles.Batch002.profile116,MergedCutProfiles.Batch002.profile117,MergedCutProfiles.Batch002.profile118,MergedCutProfiles.Batch002.profile119,MergedCutProfiles.Batch003.profile120,MergedCutProfiles.Batch003.profile121,MergedCutProfiles.Batch003.profile122,MergedCutProfiles.Batch003.profile123]⟩
theorem profilesValid17 : retention17.ProfilesValid := by
  change ∀ j : Fin 16, (retention17.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch002.valid108
  · exact MergedCutProfiles.Batch002.valid109
  · exact MergedCutProfiles.Batch002.valid110
  · exact MergedCutProfiles.Batch002.valid111
  · exact MergedCutProfiles.Batch002.valid112
  · exact MergedCutProfiles.Batch002.valid113
  · exact MergedCutProfiles.Batch002.valid114
  · exact MergedCutProfiles.Batch002.valid115
  · exact MergedCutProfiles.Batch002.valid116
  · exact MergedCutProfiles.Batch002.valid117
  · exact MergedCutProfiles.Batch002.valid118
  · exact MergedCutProfiles.Batch002.valid119
  · exact MergedCutProfiles.Batch003.valid120
  · exact MergedCutProfiles.Batch003.valid121
  · exact MergedCutProfiles.Batch003.valid122
  · exact MergedCutProfiles.Batch003.valid123
theorem numericValid17 : retention17.NumericValid := by decide +kernel
def certificate17 : RatCutBinCertificate := ⟨⟨retention17,(1795708050722680871/1000000000000000000),(637434242080419/1000000000000000000),(27022124096657033/3906250000000000),(6514935146107861847401/250000000000000000),(2172338160829508141/1000000000000000000)⟩,(199986223452875253/200000000000000000),(257434367921080973/1000000000000000000),(393159469620417683/1000000000000000000),(111135024539732387/250000000000000000)⟩
theorem valid17 : certificate17.Valid := by decide +kernel
theorem sound17 : certificate17.Sound := rat_cut_bin_certificate_sound certificate17 profilesValid17 numericValid17 valid17

def retention18 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(1/2),64,1,(15960555614684130987744105293091422311/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch003.profile124,(fun _ => MergedCutProfiles.Batch003.profile124)⟩
theorem profilesValid18 : retention18.ProfilesValid := by
  exact MergedCutProfiles.Batch003.valid124
theorem numericValid18 : retention18.NumericValid := by decide +kernel
def certificate18 : RatCutBinCertificate := ⟨⟨retention18,(1795708050722680871/1000000000000000000),(637434242080419/1000000000000000000),(27022124096657033/3906250000000000),(6514935146107861847401/250000000000000000),(997369258812242101/1000000000000000000)⟩,(199986223452875253/200000000000000000),(410375895092334429/1000000000000000000),(44821763336755183/200000000000000000),(5501852601722833/25000000000000000)⟩
theorem valid18 : certificate18.Valid := by decide +kernel
theorem sound18 : certificate18.Sound := rat_cut_bin_certificate_sound certificate18 profilesValid18 numericValid18 valid18

def retention19 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(64000000000000000000/3750800945834192207617),(3248235977562722423/1000000000000000000),(27/20),(11049558552058152828876146038144848247199/5197177564100355876800000000000000000000),false,MergedCutProfiles.Batch003.profile125,(fun _ => MergedCutProfiles.Batch003.profile125)⟩
theorem profilesValid19 : retention19.ProfilesValid := by
  exact MergedCutProfiles.Batch003.valid125
theorem numericValid19 : retention19.NumericValid := by decide +kernel
def certificate19 : RatCutBinCertificate := ⟨⟨retention19,(2119429486722680871/1000000000000000000),(637434242080419/1000000000000000000),(27022124096657033/3906250000000000),(6514935146107861847401/250000000000000000),(2125805435174245419/1000000000000000000)⟩,(19998373988448773/20000000000000000),(184449690370441083/1000000000000000000),(503325768112164387/1000000000000000000),(583111006284899459/1000000000000000000)⟩
theorem valid19 : certificate19.Valid := by decide +kernel
theorem sound19 : certificate19.Sound := rat_cut_bin_certificate_sound certificate19 profilesValid19 numericValid19 valid19

def retention20 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(1/2),64,1,(15960555614684130987744105293091422311/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch003.profile124,(fun _ => MergedCutProfiles.Batch003.profile124)⟩
theorem profilesValid20 : retention20.ProfilesValid := by
  exact MergedCutProfiles.Batch003.valid124
theorem numericValid20 : retention20.NumericValid := by decide +kernel
def certificate20 : RatCutBinCertificate := ⟨⟨retention20,(2119429486722680871/1000000000000000000),(637434242080419/1000000000000000000),(27022124096657033/3906250000000000),(6514935146107861847401/250000000000000000),(498669714607196227/500000000000000000)⟩,(19998373988448773/20000000000000000),(78630031626154009/200000000000000000),(239817489492973577/1000000000000000000),(235490108081607249/1000000000000000000)⟩
theorem valid20 : certificate20.Valid := by decide +kernel
theorem sound20 : certificate20.Sound := rat_cut_bin_certificate_sound certificate20 profilesValid20 numericValid20 valid20

def retention21 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(315061887006083071/1195024314523205584998),(285221416227561743/500000000000000000),4,(50129473042502184104872570390482223/22817713298204939440000000000000000),true,MergedCutProfiles.Batch003.profile126,![MergedCutProfiles.Batch003.profile126,MergedCutProfiles.Batch003.profile127,MergedCutProfiles.Batch003.profile128,MergedCutProfiles.Batch003.profile129,MergedCutProfiles.Batch003.profile130,MergedCutProfiles.Batch003.profile131,MergedCutProfiles.Batch003.profile132,MergedCutProfiles.Batch003.profile133,MergedCutProfiles.Batch003.profile134,MergedCutProfiles.Batch003.profile135,MergedCutProfiles.Batch003.profile136,MergedCutProfiles.Batch003.profile137,MergedCutProfiles.Batch003.profile138,MergedCutProfiles.Batch003.profile139,MergedCutProfiles.Batch003.profile140,MergedCutProfiles.Batch003.profile141]⟩
theorem profilesValid21 : retention21.ProfilesValid := by
  change ∀ j : Fin 16, (retention21.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch003.valid126
  · exact MergedCutProfiles.Batch003.valid127
  · exact MergedCutProfiles.Batch003.valid128
  · exact MergedCutProfiles.Batch003.valid129
  · exact MergedCutProfiles.Batch003.valid130
  · exact MergedCutProfiles.Batch003.valid131
  · exact MergedCutProfiles.Batch003.valid132
  · exact MergedCutProfiles.Batch003.valid133
  · exact MergedCutProfiles.Batch003.valid134
  · exact MergedCutProfiles.Batch003.valid135
  · exact MergedCutProfiles.Batch003.valid136
  · exact MergedCutProfiles.Batch003.valid137
  · exact MergedCutProfiles.Batch003.valid138
  · exact MergedCutProfiles.Batch003.valid139
  · exact MergedCutProfiles.Batch003.valid140
  · exact MergedCutProfiles.Batch003.valid141
theorem numericValid21 : retention21.NumericValid := by decide +kernel
def certificate21 : RatCutBinCertificate := ⟨⟨retention21,(1807485279528674747/1000000000000000000),(249776479000013/250000000000000000),(6999655320721799937/1000000000000000000),(525086275949533264257/31250000000000000),(439184462110248511/200000000000000000)⟩,(999892497830050613/1000000000000000000),(290457024886286643/500000000000000000),(51780524067090847/500000000000000000),(5727668965271581/125000000000000000)⟩
theorem valid21 : certificate21.Valid := by decide +kernel
theorem sound21 : certificate21.Sound := rat_cut_bin_certificate_sound certificate21 profilesValid21 numericValid21 valid21

def retention22 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(328978318250000000/597512157261602792499),(315061887006083071/500000000000000000),4,(73480926497264063971/32000000000000000000),true,MergedCutProfiles.Batch003.profile142,![MergedCutProfiles.Batch003.profile142,MergedCutProfiles.Batch003.profile129,MergedCutProfiles.Batch003.profile131,MergedCutProfiles.Batch003.profile134,MergedCutProfiles.Batch003.profile135,MergedCutProfiles.Batch003.profile138,MergedCutProfiles.Batch003.profile139,MergedCutProfiles.Batch003.profile141,MergedCutProfiles.Batch003.profile143,MergedCutProfiles.Batch003.profile144,MergedCutProfiles.Batch003.profile145,MergedCutProfiles.Batch003.profile146,MergedCutProfiles.Batch003.profile147,MergedCutProfiles.Batch003.profile148,MergedCutProfiles.Batch003.profile149,MergedCutProfiles.Batch003.profile150]⟩
theorem profilesValid22 : retention22.ProfilesValid := by
  change ∀ j : Fin 16, (retention22.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch003.valid142
  · exact MergedCutProfiles.Batch003.valid129
  · exact MergedCutProfiles.Batch003.valid131
  · exact MergedCutProfiles.Batch003.valid134
  · exact MergedCutProfiles.Batch003.valid135
  · exact MergedCutProfiles.Batch003.valid138
  · exact MergedCutProfiles.Batch003.valid139
  · exact MergedCutProfiles.Batch003.valid141
  · exact MergedCutProfiles.Batch003.valid143
  · exact MergedCutProfiles.Batch003.valid144
  · exact MergedCutProfiles.Batch003.valid145
  · exact MergedCutProfiles.Batch003.valid146
  · exact MergedCutProfiles.Batch003.valid147
  · exact MergedCutProfiles.Batch003.valid148
  · exact MergedCutProfiles.Batch003.valid149
  · exact MergedCutProfiles.Batch003.valid150
theorem numericValid22 : retention22.NumericValid := by decide +kernel
def certificate22 : RatCutBinCertificate := ⟨⟨retention22,(1807485279528674747/1000000000000000000),(249776479000013/250000000000000000),(6999655320721799937/1000000000000000000),(525086275949533264257/31250000000000000),(1147623488461563009/500000000000000000)⟩,(999892497830050613/1000000000000000000),(259894013612253133/500000000000000000),(14009687004811599/100000000000000000),(65473460061197559/1000000000000000000)⟩
theorem valid22 : certificate22.Valid := by decide +kernel
theorem sound22 : certificate22.Sound := rat_cut_bin_certificate_sound certificate22 profilesValid22 numericValid22 valid22

def retention23 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(4132049451178336111/2390048629046411169996),(1315913273/1000000000),(12/5),(1157176498120202283/500000000000000000),true,MergedCutProfiles.Batch003.profile132,![MergedCutProfiles.Batch003.profile132,MergedCutProfiles.Batch003.profile151,MergedCutProfiles.Batch003.profile143,MergedCutProfiles.Batch003.profile152,MergedCutProfiles.Batch003.profile153,MergedCutProfiles.Batch003.profile154,MergedCutProfiles.Batch003.profile155,MergedCutProfiles.Batch003.profile156,MergedCutProfiles.Batch003.profile157,MergedCutProfiles.Batch003.profile158,MergedCutProfiles.Batch003.profile159,MergedCutProfiles.Batch004.profile160,MergedCutProfiles.Batch004.profile161,MergedCutProfiles.Batch004.profile162,MergedCutProfiles.Batch004.profile163,MergedCutProfiles.Batch004.profile164]⟩
theorem profilesValid23 : retention23.ProfilesValid := by
  change ∀ j : Fin 16, (retention23.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch003.valid132
  · exact MergedCutProfiles.Batch003.valid151
  · exact MergedCutProfiles.Batch003.valid143
  · exact MergedCutProfiles.Batch003.valid152
  · exact MergedCutProfiles.Batch003.valid153
  · exact MergedCutProfiles.Batch003.valid154
  · exact MergedCutProfiles.Batch003.valid155
  · exact MergedCutProfiles.Batch003.valid156
  · exact MergedCutProfiles.Batch003.valid157
  · exact MergedCutProfiles.Batch003.valid158
  · exact MergedCutProfiles.Batch003.valid159
  · exact MergedCutProfiles.Batch004.valid160
  · exact MergedCutProfiles.Batch004.valid161
  · exact MergedCutProfiles.Batch004.valid162
  · exact MergedCutProfiles.Batch004.valid163
  · exact MergedCutProfiles.Batch004.valid164
theorem numericValid23 : retention23.NumericValid := by decide +kernel
def certificate23 : RatCutBinCertificate := ⟨⟨retention23,(1807485279528674747/1000000000000000000),(249776479000013/250000000000000000),(6999655320721799937/1000000000000000000),(525086275949533264257/31250000000000000),(2313733810573528431/1000000000000000000)⟩,(999892497830050613/1000000000000000000),(337803739560898747/1000000000000000000),(295572980377969481/1000000000000000000),(27285276701741073/125000000000000000)⟩
theorem valid23 : certificate23.Valid := by decide +kernel
theorem sound23 : certificate23.Sound := rat_cut_bin_certificate_sound certificate23 profilesValid23 numericValid23 valid23

def certificates : List RatCutBinCertificate := [certificate12,certificate13,certificate14,certificate15,certificate16,certificate17,certificate18,certificate19,certificate20,certificate21,certificate22,certificate23]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound12,List.forall_mem_cons.mpr ⟨sound13,List.forall_mem_cons.mpr ⟨sound14,List.forall_mem_cons.mpr ⟨sound15,List.forall_mem_cons.mpr ⟨sound16,List.forall_mem_cons.mpr ⟨sound17,List.forall_mem_cons.mpr ⟨sound18,List.forall_mem_cons.mpr ⟨sound19,List.forall_mem_cons.mpr ⟨sound20,List.forall_mem_cons.mpr ⟨sound21,List.forall_mem_cons.mpr ⟨sound22,List.forall_mem_cons.mpr ⟨sound23,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch001
