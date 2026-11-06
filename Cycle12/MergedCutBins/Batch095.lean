import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch189
import Cycle12.MergedCutProfiles.Batch190
import Cycle12.MergedCutProfiles.Batch191

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch095

def retention1140 : RatCutRetentionCertificate := ⟨(109/2000),(219/4000),(1765828846839393583/3869335319361141499),(3662671160803666109/1000000000000000000),(6/5),(49484081124794122091447835179869212903/45783389510045826362500000000000000000),false,MergedCutProfiles.Batch189.profile7597,(fun _ => MergedCutProfiles.Batch189.profile7597)⟩
theorem profilesValid1140 : retention1140.ProfilesValid := by
  exact MergedCutProfiles.Batch189.valid7597
theorem numericValid1140 : retention1140.NumericValid := by decide +kernel
def certificate1140 : RatCutBinCertificate := ⟨⟨retention1140,(2585423230207165147/1000000000000000000),(73656633113325057/500000000000000000),(287612269959572801/20000000000000000),(222902312226657076333/1000000000000000000),(104904394759574817/100000000000000000)⟩,(123759319878591347/125000000000000000),(23321917107257/61035156250000),(125141794226472501/500000000000000000),(180510424682222349/1000000000000000000)⟩
theorem valid1140 : certificate1140.Valid := by decide +kernel
theorem sound1140 : certificate1140.Sound := rat_cut_bin_certificate_sound certificate1140 profilesValid1140 numericValid1140 valid1140

def retention1141 : RatCutRetentionCertificate := ⟨(109/2000),(219/4000),(1912139607791537359/3869335319361141499),(1765828846839393583/250000000000000000),(21/20),(704796177871349708595532580538054202151/706331538735757433200000000000000000000),false,MergedCutProfiles.Batch189.profile7598,(fun _ => MergedCutProfiles.Batch189.profile7598)⟩
theorem profilesValid1141 : retention1141.ProfilesValid := by
  exact MergedCutProfiles.Batch189.valid7598
theorem numericValid1141 : retention1141.NumericValid := by decide +kernel
def certificate1141 : RatCutBinCertificate := ⟨⟨retention1141,(2585423230207165147/1000000000000000000),(73656633113325057/500000000000000000),(287612269959572801/20000000000000000),(222902312226657076333/1000000000000000000),(485007404712338297/500000000000000000)⟩,(123759319878591347/125000000000000000),(206618644812332361/500000000000000000),(44314052025996737/200000000000000000),(45025043346186951/250000000000000000)⟩
theorem valid1141 : certificate1141.Valid := by decide +kernel
theorem sound1141 : certificate1141.Sound := rat_cut_bin_certificate_sound certificate1141 profilesValid1141 numericValid1141 valid1141

def retention1142 : RatCutRetentionCertificate := ⟨(109/2000),(219/4000),(7725044015477810931/15477341277444565996),(1912139607791537359/250000000000000000),(21/20),(189443019626336856085864037381674447691/191213960779153735900000000000000000000),false,MergedCutProfiles.Batch189.profile7599,(fun _ => MergedCutProfiles.Batch189.profile7599)⟩
theorem profilesValid1142 : retention1142.ProfilesValid := by
  exact MergedCutProfiles.Batch189.valid7599
theorem numericValid1142 : retention1142.NumericValid := by decide +kernel
def certificate1142 : RatCutBinCertificate := ⟨⟨retention1142,(2585423230207165147/1000000000000000000),(73656633113325057/500000000000000000),(287612269959572801/20000000000000000),(222902312226657076333/1000000000000000000),(48146357104436969/50000000000000000)⟩,(123759319878591347/125000000000000000),(416278940764864951/1000000000000000000),(218893499029882209/1000000000000000000),(178276038755330341/1000000000000000000)⟩
theorem valid1142 : certificate1142.Valid := by decide +kernel
theorem sound1142 : certificate1142.Sound := rat_cut_bin_certificate_sound certificate1142 profilesValid1142 numericValid1142 valid1142

def retention1143 : RatCutRetentionCertificate := ⟨(109/2000),(219/4000),(1/2),(7725044015477810931/1000000000000000000),(21/20),(4076033725110914004002185799473262164773/4120023474921499163200000000000000000000),false,MergedCutProfiles.Batch189.profile7596,(fun _ => MergedCutProfiles.Batch189.profile7596)⟩
theorem profilesValid1143 : retention1143.ProfilesValid := by
  exact MergedCutProfiles.Batch189.valid7596
theorem numericValid1143 : retention1143.NumericValid := by decide +kernel
def certificate1143 : RatCutBinCertificate := ⟨⟨retention1143,(2585423230207165147/1000000000000000000),(73656633113325057/500000000000000000),(287612269959572801/20000000000000000),(222902312226657076333/1000000000000000000),(961511670116702669/1000000000000000000)⟩,(123759319878591347/125000000000000000),(416891758259976871/1000000000000000000),(21835689218034801/100000000000000000),(7111416458423791/40000000000000000)⟩
theorem valid1143 : certificate1143.Valid := by decide +kernel
theorem sound1143 : certificate1143.Sound := rat_cut_bin_certificate_sound certificate1143 profilesValid1143 numericValid1143 valid1143

def retention1144 : RatCutRetentionCertificate := ⟨(219/4000),(11/200),(78259311252855189/1276192314816136471),(425082801362805553/500000000000000000),(14/5),(1288616449805989512301/640000000000000000000),true,MergedCutProfiles.Batch190.profile7600,![MergedCutProfiles.Batch190.profile7600,MergedCutProfiles.Batch190.profile7601,MergedCutProfiles.Batch190.profile7602,MergedCutProfiles.Batch190.profile7603,MergedCutProfiles.Batch190.profile7604,MergedCutProfiles.Batch190.profile7605,MergedCutProfiles.Batch190.profile7606,MergedCutProfiles.Batch190.profile7607,MergedCutProfiles.Batch190.profile7608,MergedCutProfiles.Batch190.profile7609,MergedCutProfiles.Batch190.profile7610,MergedCutProfiles.Batch190.profile7611,MergedCutProfiles.Batch190.profile7612,MergedCutProfiles.Batch190.profile7613,MergedCutProfiles.Batch190.profile7614,MergedCutProfiles.Batch190.profile7615]⟩
theorem profilesValid1144 : retention1144.ProfilesValid := by
  change ∀ j : Fin 16, (retention1144.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch190.valid7600
  · exact MergedCutProfiles.Batch190.valid7601
  · exact MergedCutProfiles.Batch190.valid7602
  · exact MergedCutProfiles.Batch190.valid7603
  · exact MergedCutProfiles.Batch190.valid7604
  · exact MergedCutProfiles.Batch190.valid7605
  · exact MergedCutProfiles.Batch190.valid7606
  · exact MergedCutProfiles.Batch190.valid7607
  · exact MergedCutProfiles.Batch190.valid7608
  · exact MergedCutProfiles.Batch190.valid7609
  · exact MergedCutProfiles.Batch190.valid7610
  · exact MergedCutProfiles.Batch190.valid7611
  · exact MergedCutProfiles.Batch190.valid7612
  · exact MergedCutProfiles.Batch190.valid7613
  · exact MergedCutProfiles.Batch190.valid7614
  · exact MergedCutProfiles.Batch190.valid7615
theorem numericValid1144 : retention1144.NumericValid := by decide +kernel
def certificate1144 : RatCutBinCertificate := ⟨⟨retention1144,(560201531846584823/250000000000000000),(14887102204219317/100000000000000000),(14443280455941829001/1000000000000000000),(221515985080731664567/1000000000000000000),(487193595542331687/250000000000000000)⟩,(49568055177521711/50000000000000000),(363742164682932359/1000000000000000000),(134198911207130047/500000000000000000),(2861003381877979/20000000000000000)⟩
theorem valid1144 : certificate1144.Valid := by decide +kernel
theorem sound1144 : certificate1144.Sound := rat_cut_bin_certificate_sound certificate1144 profilesValid1144 numericValid1144 valid1144

def retention1145 : RatCutRetentionCertificate := ⟨(219/4000),(11/200),(378515107269965611/3828576944448409413),(234777933758565567/250000000000000000),(13/5),(609795318666252889011/320000000000000000000),true,MergedCutProfiles.Batch190.profile7616,![MergedCutProfiles.Batch190.profile7616,MergedCutProfiles.Batch190.profile7617,MergedCutProfiles.Batch190.profile7618,MergedCutProfiles.Batch190.profile7619,MergedCutProfiles.Batch190.profile7620,MergedCutProfiles.Batch190.profile7621,MergedCutProfiles.Batch190.profile7622,MergedCutProfiles.Batch190.profile7623,MergedCutProfiles.Batch190.profile7624,MergedCutProfiles.Batch190.profile7625,MergedCutProfiles.Batch190.profile7626,MergedCutProfiles.Batch190.profile7627,MergedCutProfiles.Batch190.profile7628,MergedCutProfiles.Batch190.profile7629,MergedCutProfiles.Batch190.profile7630,MergedCutProfiles.Batch190.profile7631]⟩
theorem profilesValid1145 : retention1145.ProfilesValid := by
  change ∀ j : Fin 16, (retention1145.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch190.valid7616
  · exact MergedCutProfiles.Batch190.valid7617
  · exact MergedCutProfiles.Batch190.valid7618
  · exact MergedCutProfiles.Batch190.valid7619
  · exact MergedCutProfiles.Batch190.valid7620
  · exact MergedCutProfiles.Batch190.valid7621
  · exact MergedCutProfiles.Batch190.valid7622
  · exact MergedCutProfiles.Batch190.valid7623
  · exact MergedCutProfiles.Batch190.valid7624
  · exact MergedCutProfiles.Batch190.valid7625
  · exact MergedCutProfiles.Batch190.valid7626
  · exact MergedCutProfiles.Batch190.valid7627
  · exact MergedCutProfiles.Batch190.valid7628
  · exact MergedCutProfiles.Batch190.valid7629
  · exact MergedCutProfiles.Batch190.valid7630
  · exact MergedCutProfiles.Batch190.valid7631
theorem numericValid1145 : retention1145.NumericValid := by decide +kernel
def certificate1145 : RatCutBinCertificate := ⟨⟨retention1145,(560201531846584823/250000000000000000),(14887102204219317/100000000000000000),(14443280455941829001/1000000000000000000),(221515985080731664567/1000000000000000000),(1845542605351080931/1000000000000000000)⟩,(49568055177521711/50000000000000000),(369328352149609283/1000000000000000000),(262791718083475123/1000000000000000000),(143036222959654577/1000000000000000000)⟩
theorem valid1145 : certificate1145.Valid := by decide +kernel
theorem sound1145 : certificate1145.Sound := rat_cut_bin_certificate_sound certificate1145 profilesValid1145 numericValid1145 valid1145

def retention1146 : RatCutRetentionCertificate := ⟨(219/4000),(11/200),(1324936947925930299/5104769259264545884),(378515107269965611/250000000000000000),(9/5),(478697806054425478059/320000000000000000000),true,MergedCutProfiles.Batch190.profile7632,![MergedCutProfiles.Batch190.profile7632,MergedCutProfiles.Batch190.profile7633,MergedCutProfiles.Batch190.profile7634,MergedCutProfiles.Batch190.profile7635,MergedCutProfiles.Batch190.profile7636,MergedCutProfiles.Batch190.profile7637,MergedCutProfiles.Batch190.profile7638,MergedCutProfiles.Batch190.profile7639,MergedCutProfiles.Batch191.profile7640,MergedCutProfiles.Batch191.profile7641,MergedCutProfiles.Batch191.profile7642,MergedCutProfiles.Batch191.profile7643,MergedCutProfiles.Batch191.profile7644,MergedCutProfiles.Batch191.profile7645,MergedCutProfiles.Batch191.profile7646,MergedCutProfiles.Batch191.profile7647]⟩
theorem profilesValid1146 : retention1146.ProfilesValid := by
  change ∀ j : Fin 16, (retention1146.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch190.valid7632
  · exact MergedCutProfiles.Batch190.valid7633
  · exact MergedCutProfiles.Batch190.valid7634
  · exact MergedCutProfiles.Batch190.valid7635
  · exact MergedCutProfiles.Batch190.valid7636
  · exact MergedCutProfiles.Batch190.valid7637
  · exact MergedCutProfiles.Batch190.valid7638
  · exact MergedCutProfiles.Batch190.valid7639
  · exact MergedCutProfiles.Batch191.valid7640
  · exact MergedCutProfiles.Batch191.valid7641
  · exact MergedCutProfiles.Batch191.valid7642
  · exact MergedCutProfiles.Batch191.valid7643
  · exact MergedCutProfiles.Batch191.valid7644
  · exact MergedCutProfiles.Batch191.valid7645
  · exact MergedCutProfiles.Batch191.valid7646
  · exact MergedCutProfiles.Batch191.valid7647
theorem numericValid1146 : retention1146.NumericValid := by decide +kernel
def certificate1146 : RatCutBinCertificate := ⟨⟨retention1146,(560201531846584823/250000000000000000),(14887102204219317/100000000000000000),(14443280455941829001/1000000000000000000),(221515985080731664567/1000000000000000000),(72717322932984231/50000000000000000)⟩,(49568055177521711/50000000000000000),(80137624763793149/200000000000000000),(232852460901356129/1000000000000000000),(143649463698990869/1000000000000000000)⟩
theorem valid1146 : certificate1146.Valid := by decide +kernel
theorem sound1146 : certificate1146.Sound := rat_cut_bin_certificate_sound certificate1146 profilesValid1146 numericValid1146 valid1146

def retention1147 : RatCutRetentionCertificate := ⟨(219/4000),(11/200),(1700633222369715836/3828576944448409413),(3974810843777790897/1000000000000000000),(21/20),(1372831390242496947273/1280000000000000000000),true,MergedCutProfiles.Batch191.profile7648,![MergedCutProfiles.Batch191.profile7648,MergedCutProfiles.Batch190.profile7624,MergedCutProfiles.Batch191.profile7649,MergedCutProfiles.Batch191.profile7650,MergedCutProfiles.Batch191.profile7651,MergedCutProfiles.Batch191.profile7652,MergedCutProfiles.Batch191.profile7653,MergedCutProfiles.Batch191.profile7654,MergedCutProfiles.Batch191.profile7655,MergedCutProfiles.Batch191.profile7656,MergedCutProfiles.Batch191.profile7657,MergedCutProfiles.Batch191.profile7658,MergedCutProfiles.Batch191.profile7659,MergedCutProfiles.Batch191.profile7660,MergedCutProfiles.Batch191.profile7661,MergedCutProfiles.Batch191.profile7662]⟩
theorem profilesValid1147 : retention1147.ProfilesValid := by
  change ∀ j : Fin 16, (retention1147.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch191.valid7648
  · exact MergedCutProfiles.Batch190.valid7624
  · exact MergedCutProfiles.Batch191.valid7649
  · exact MergedCutProfiles.Batch191.valid7650
  · exact MergedCutProfiles.Batch191.valid7651
  · exact MergedCutProfiles.Batch191.valid7652
  · exact MergedCutProfiles.Batch191.valid7653
  · exact MergedCutProfiles.Batch191.valid7654
  · exact MergedCutProfiles.Batch191.valid7655
  · exact MergedCutProfiles.Batch191.valid7656
  · exact MergedCutProfiles.Batch191.valid7657
  · exact MergedCutProfiles.Batch191.valid7658
  · exact MergedCutProfiles.Batch191.valid7659
  · exact MergedCutProfiles.Batch191.valid7660
  · exact MergedCutProfiles.Batch191.valid7661
  · exact MergedCutProfiles.Batch191.valid7662
theorem numericValid1147 : retention1147.NumericValid := by decide +kernel
def certificate1147 : RatCutBinCertificate := ⟨⟨retention1147,(560201531846584823/250000000000000000),(14887102204219317/100000000000000000),(14443280455941829001/1000000000000000000),(221515985080731664567/1000000000000000000),(524134578719433659/500000000000000000)⟩,(49568055177521711/50000000000000000),(28783138630501143/62500000000000000),(4559628388805837/25000000000000000),(29103929067474481/200000000000000000)⟩
theorem valid1147 : certificate1147.Valid := by decide +kernel
theorem sound1147 : certificate1147.Sound := rat_cut_bin_certificate_sound certificate1147 profilesValid1147 numericValid1147 valid1147

def retention1148 : RatCutRetentionCertificate := ⟨(219/4000),(11/200),(1252371389759294063/2552384629632272942),(425158305592428959/62500000000000000),(21/20),(170623457237484740103818450729815527311/170063322236971583600000000000000000000),false,MergedCutProfiles.Batch191.profile7663,(fun _ => MergedCutProfiles.Batch191.profile7663)⟩
theorem profilesValid1148 : retention1148.ProfilesValid := by
  exact MergedCutProfiles.Batch191.valid7663
theorem numericValid1148 : retention1148.NumericValid := by decide +kernel
def certificate1148 : RatCutBinCertificate := ⟨⟨retention1148,(560201531846584823/250000000000000000),(14887102204219317/100000000000000000),(14443280455941829001/1000000000000000000),(221515985080731664567/1000000000000000000),(4895199710262181/5000000000000000)⟩,(49568055177521711/50000000000000000),(466976119415212949/1000000000000000000),(17743207304764037/100000000000000000),(28995950072942849/200000000000000000)⟩
theorem valid1148 : certificate1148.Valid := by decide +kernel
theorem sound1148 : certificate1148.Sound := rat_cut_bin_certificate_sound certificate1148 profilesValid1148 numericValid1148 valid1148

def retention1149 : RatCutRetentionCertificate := ⟨(219/4000),(11/200),(3794685310970661011/7657153888896818826),(3757114169277882189/500000000000000000),(21/20),(2996808125355520866335445974791252994999/3005691335422305751200000000000000000000),false,MergedCutProfiles.Batch191.profile7664,(fun _ => MergedCutProfiles.Batch191.profile7664)⟩
theorem profilesValid1149 : retention1149.ProfilesValid := by
  exact MergedCutProfiles.Batch191.valid7664
theorem numericValid1149 : retention1149.NumericValid := by decide +kernel
def certificate1149 : RatCutBinCertificate := ⟨⟨retention1149,(560201531846584823/250000000000000000),(14887102204219317/100000000000000000),(14443280455941829001/1000000000000000000),(221515985080731664567/1000000000000000000),(486395505034798929/500000000000000000)⟩,(49568055177521711/50000000000000000),(29154762400287833/62500000000000000),(177813016476969341/1000000000000000000),(73033207273366809/500000000000000000)⟩
theorem valid1149 : certificate1149.Valid := by decide +kernel
theorem sound1149 : certificate1149.Sound := rat_cut_bin_certificate_sound certificate1149 profilesValid1149 numericValid1149 valid1149

def retention1150 : RatCutRetentionCertificate := ⟨(219/4000),(11/200),(1/2),(3794685310970661011/500000000000000000),(21/20),(3001834835062508078630623397569754014559/3035748248776528808800000000000000000000),false,MergedCutProfiles.Batch191.profile7665,(fun _ => MergedCutProfiles.Batch191.profile7665)⟩
theorem profilesValid1150 : retention1150.ProfilesValid := by
  exact MergedCutProfiles.Batch191.valid7665
theorem numericValid1150 : retention1150.NumericValid := by decide +kernel
def certificate1150 : RatCutBinCertificate := ⟨⟨retention1150,(560201531846584823/250000000000000000),(14887102204219317/100000000000000000),(14443280455941829001/1000000000000000000),(221515985080731664567/1000000000000000000),(964575141224821937/1000000000000000000)⟩,(49568055177521711/50000000000000000),(235057722845872669/500000000000000000),(175052092509875713/1000000000000000000),(71429397443513107/500000000000000000)⟩
theorem valid1150 : certificate1150.Valid := by decide +kernel
theorem sound1150 : certificate1150.Sound := rat_cut_bin_certificate_sound certificate1150 profilesValid1150 numericValid1150 valid1150

def retention1151 : RatCutRetentionCertificate := ⟨(219/4000),(11/200),(1/2),64,1,(63850163001460907861177117982454272951/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch191.profile7665,(fun _ => MergedCutProfiles.Batch191.profile7665)⟩
theorem profilesValid1151 : retention1151.ProfilesValid := by
  exact MergedCutProfiles.Batch191.valid7665
theorem numericValid1151 : retention1151.NumericValid := by decide +kernel
def certificate1151 : RatCutBinCertificate := ⟨⟨retention1151,(560201531846584823/250000000000000000),(14887102204219317/100000000000000000),(14443280455941829001/1000000000000000000),(221515985080731664567/1000000000000000000),(487280962399516283/500000000000000000)⟩,(49568055177521711/50000000000000000),(218079639627521221/500000000000000000),(201938089404624317/1000000000000000000),(19215922750410071/100000000000000000)⟩
theorem valid1151 : certificate1151.Valid := by decide +kernel
theorem sound1151 : certificate1151.Sound := rat_cut_bin_certificate_sound certificate1151 profilesValid1151 numericValid1151 valid1151

def certificates : List RatCutBinCertificate := [certificate1140,certificate1141,certificate1142,certificate1143,certificate1144,certificate1145,certificate1146,certificate1147,certificate1148,certificate1149,certificate1150,certificate1151]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1140,List.forall_mem_cons.mpr ⟨sound1141,List.forall_mem_cons.mpr ⟨sound1142,List.forall_mem_cons.mpr ⟨sound1143,List.forall_mem_cons.mpr ⟨sound1144,List.forall_mem_cons.mpr ⟨sound1145,List.forall_mem_cons.mpr ⟨sound1146,List.forall_mem_cons.mpr ⟨sound1147,List.forall_mem_cons.mpr ⟨sound1148,List.forall_mem_cons.mpr ⟨sound1149,List.forall_mem_cons.mpr ⟨sound1150,List.forall_mem_cons.mpr ⟨sound1151,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch095
