import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch001
import Cycle12.MergedCutProfiles.Batch002
import Cycle12.MergedCutProfiles.Batch003
import Cycle12.MergedCutProfiles.Batch307
import Cycle12.MergedCutProfiles.Batch440
import Cycle12.MergedCutProfiles.Batch441
import Cycle12.MergedCutProfiles.Batch561

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch304

def retention3648 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(5718514930724906741/11555922301585115699),(21123810384156213931/1000000000000000000),1,(84482598127281396879837145163658803923/84495241536624855724000000000000000000),false,MergedCutProfiles.Batch561.profile22445,(fun _ => MergedCutProfiles.Batch561.profile22445)⟩
theorem profilesValid3648 : retention3648.ProfilesValid := by
  exact MergedCutProfiles.Batch561.valid22445
theorem numericValid3648 : retention3648.NumericValid := by decide +kernel
def certificate3648 : RatCutBinCertificate := ⟨⟨retention3648,(2361128514774833293/1000000000000000000),(123364672097640231/500000000000000000),(18294995889297718301/1000000000000000000),(848395165509429942467/1000000000000000000),(968007356889042413/1000000000000000000)⟩,(199577960609044837/200000000000000000),(122059470574660307/1000000000000000000),(619248940035694927/1000000000000000000),(17872627688244579/31250000000000000)⟩
theorem valid3648 : certificate3648.Valid := by decide +kernel
theorem sound3648 : certificate3648.Sound := rat_cut_bin_certificate_sound certificate3648 profilesValid3648 numericValid3648 valid3648

def retention3649 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(1650200022866330231/3301692086167175914),(5718514930724906741/250000000000000000),1,(1416868385241874570335030968798178681/1429628732681226685250000000000000000),false,MergedCutProfiles.Batch561.profile22446,(fun _ => MergedCutProfiles.Batch561.profile22446)⟩
theorem profilesValid3649 : retention3649.ProfilesValid := by
  exact MergedCutProfiles.Batch561.valid22446
theorem numericValid3649 : retention3649.NumericValid := by decide +kernel
def certificate3649 : RatCutBinCertificate := ⟨⟨retention3649,(2361128514774833293/1000000000000000000),(123364672097640231/500000000000000000),(18294995889297718301/1000000000000000000),(848395165509429942467/1000000000000000000),(47961569388852009/50000000000000000)⟩,(199577960609044837/200000000000000000),(123176187726788723/1000000000000000000),(154239447732608083/250000000000000000),(566753002439084083/1000000000000000000)⟩
theorem valid3649 : certificate3649.Valid := by decide +kernel
theorem sound3649 : certificate3649.Sound := rat_cut_bin_certificate_sound certificate3649 profilesValid3649 numericValid3649 valid3649

def retention3650 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(1/2),(11551400160064311617/500000000000000000),1,(18312194976414251535188937513132217403/18482240256102898587200000000000000000),false,MergedCutProfiles.Batch307.profile12294,(fun _ => MergedCutProfiles.Batch307.profile12294)⟩
theorem profilesValid3650 : retention3650.ProfilesValid := by
  exact MergedCutProfiles.Batch307.valid12294
theorem numericValid3650 : retention3650.NumericValid := by decide +kernel
def certificate3650 : RatCutBinCertificate := ⟨⟨retention3650,(2361128514774833293/1000000000000000000),(123364672097640231/500000000000000000),(18294995889297718301/1000000000000000000),(848395165509429942467/1000000000000000000),(479478279975516301/500000000000000000)⟩,(199577960609044837/200000000000000000),(15401436106277603/125000000000000000),(616885506603238157/1000000000000000000),(566756889941869491/1000000000000000000)⟩
theorem valid3650 : certificate3650.Valid := by decide +kernel
theorem sound3650 : certificate3650.Sound := rat_cut_bin_certificate_sound certificate3650 profilesValid3650 numericValid3650 valid3650

def retention3651 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(648937601599197613/75016018916683844152359),(224960613978373/390625000000000),4,(40806248570673831350981784962053067/18428773497108316160000000000000000),true,MergedCutProfiles.Batch561.profile22447,![MergedCutProfiles.Batch561.profile22447,MergedCutProfiles.Batch561.profile22448,MergedCutProfiles.Batch561.profile22448,MergedCutProfiles.Batch440.profile17639,MergedCutProfiles.Batch440.profile17639,MergedCutProfiles.Batch440.profile17639,MergedCutProfiles.Batch440.profile17639,MergedCutProfiles.Batch307.profile12298,MergedCutProfiles.Batch307.profile12298,MergedCutProfiles.Batch307.profile12298,MergedCutProfiles.Batch307.profile12298,MergedCutProfiles.Batch441.profile17640,MergedCutProfiles.Batch441.profile17640,MergedCutProfiles.Batch441.profile17640,MergedCutProfiles.Batch441.profile17640,MergedCutProfiles.Batch001.profile71]⟩
theorem profilesValid3651 : retention3651.ProfilesValid := by
  change ∀ j : Fin 16, (retention3651.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch561.valid22447
  · exact MergedCutProfiles.Batch561.valid22448
  · exact MergedCutProfiles.Batch561.valid22448
  · exact MergedCutProfiles.Batch440.valid17639
  · exact MergedCutProfiles.Batch440.valid17639
  · exact MergedCutProfiles.Batch440.valid17639
  · exact MergedCutProfiles.Batch440.valid17639
  · exact MergedCutProfiles.Batch307.valid12298
  · exact MergedCutProfiles.Batch307.valid12298
  · exact MergedCutProfiles.Batch307.valid12298
  · exact MergedCutProfiles.Batch307.valid12298
  · exact MergedCutProfiles.Batch441.valid17640
  · exact MergedCutProfiles.Batch441.valid17640
  · exact MergedCutProfiles.Batch441.valid17640
  · exact MergedCutProfiles.Batch441.valid17640
  · exact MergedCutProfiles.Batch001.valid71
theorem numericValid3651 : retention3651.NumericValid := by decide +kernel
def certificate3651 : RatCutBinCertificate := ⟨⟨retention3651,(439198536121533511/250000000000000000),(637434242080419/1000000000000000000),(172941595975847257/25000000000000000),(130298704246109328290933/250000000000000000),(442724150669287577/200000000000000000)⟩,(62499789406220421/62500000000000000),(589898349379380399/1000000000000000000),(12343790450289399/125000000000000000),(44063188315508731/1000000000000000000)⟩
theorem valid3651 : certificate3651.Valid := by decide +kernel
theorem sound3651 : certificate3651.Sound := rat_cut_bin_certificate_sound certificate3651 profilesValid3651 numericValid3651 valid3651

def retention3652 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(444022511000000000/25005339638894614717453),(648937601599197613/1000000000000000000),4,(1212453422912276221699023444552495507/519150081279358090400000000000000000),true,MergedCutProfiles.Batch561.profile22448,![MergedCutProfiles.Batch561.profile22448,MergedCutProfiles.Batch440.profile17639,MergedCutProfiles.Batch440.profile17639,MergedCutProfiles.Batch307.profile12298,MergedCutProfiles.Batch307.profile12298,MergedCutProfiles.Batch441.profile17640,MergedCutProfiles.Batch441.profile17640,MergedCutProfiles.Batch001.profile71,MergedCutProfiles.Batch001.profile71,MergedCutProfiles.Batch001.profile71,MergedCutProfiles.Batch307.profile12299,MergedCutProfiles.Batch307.profile12299,MergedCutProfiles.Batch307.profile12299,MergedCutProfiles.Batch441.profile17641,MergedCutProfiles.Batch441.profile17641,MergedCutProfiles.Batch441.profile17641]⟩
theorem profilesValid3652 : retention3652.ProfilesValid := by
  change ∀ j : Fin 16, (retention3652.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch561.valid22448
  · exact MergedCutProfiles.Batch440.valid17639
  · exact MergedCutProfiles.Batch440.valid17639
  · exact MergedCutProfiles.Batch307.valid12298
  · exact MergedCutProfiles.Batch307.valid12298
  · exact MergedCutProfiles.Batch441.valid17640
  · exact MergedCutProfiles.Batch441.valid17640
  · exact MergedCutProfiles.Batch001.valid71
  · exact MergedCutProfiles.Batch001.valid71
  · exact MergedCutProfiles.Batch001.valid71
  · exact MergedCutProfiles.Batch307.valid12299
  · exact MergedCutProfiles.Batch307.valid12299
  · exact MergedCutProfiles.Batch307.valid12299
  · exact MergedCutProfiles.Batch441.valid17641
  · exact MergedCutProfiles.Batch441.valid17641
  · exact MergedCutProfiles.Batch441.valid17641
theorem numericValid3652 : retention3652.NumericValid := by decide +kernel
def certificate3652 : RatCutBinCertificate := ⟨⟨retention3652,(439198536121533511/250000000000000000),(637434242080419/1000000000000000000),(172941595975847257/25000000000000000),(130298704246109328290933/250000000000000000),(1167405441858122759/500000000000000000)⟩,(62499789406220421/62500000000000000),(32230400608517257/62500000000000000),(7139846006227149/50000000000000000),(68048622239964871/1000000000000000000)⟩
theorem valid3652 : certificate3652.Valid := by decide +kernel
theorem sound3652 : certificate3652.Sound := rat_cut_bin_certificate_sound certificate3652 profilesValid3652 numericValid3652 valid3652

def retention3653 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(16238948567397564475/25005339638894614717453),(1332067533/1000000000),(12/5),(37417513717905509089/16000000000000000000),true,MergedCutProfiles.Batch002.profile86,![MergedCutProfiles.Batch002.profile86,MergedCutProfiles.Batch001.profile78,MergedCutProfiles.Batch002.profile82,MergedCutProfiles.Batch307.profile12302,MergedCutProfiles.Batch002.profile96,MergedCutProfiles.Batch002.profile90,MergedCutProfiles.Batch002.profile92,MergedCutProfiles.Batch002.profile97,MergedCutProfiles.Batch002.profile98,MergedCutProfiles.Batch307.profile12304,MergedCutProfiles.Batch307.profile12305,MergedCutProfiles.Batch441.profile17643,MergedCutProfiles.Batch002.profile101,MergedCutProfiles.Batch561.profile22449,MergedCutProfiles.Batch561.profile22450,MergedCutProfiles.Batch561.profile22451]⟩
theorem profilesValid3653 : retention3653.ProfilesValid := by
  change ∀ j : Fin 16, (retention3653.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch002.valid86
  · exact MergedCutProfiles.Batch001.valid78
  · exact MergedCutProfiles.Batch002.valid82
  · exact MergedCutProfiles.Batch307.valid12302
  · exact MergedCutProfiles.Batch002.valid96
  · exact MergedCutProfiles.Batch002.valid90
  · exact MergedCutProfiles.Batch002.valid92
  · exact MergedCutProfiles.Batch002.valid97
  · exact MergedCutProfiles.Batch002.valid98
  · exact MergedCutProfiles.Batch307.valid12304
  · exact MergedCutProfiles.Batch307.valid12305
  · exact MergedCutProfiles.Batch441.valid17643
  · exact MergedCutProfiles.Batch002.valid101
  · exact MergedCutProfiles.Batch561.valid22449
  · exact MergedCutProfiles.Batch561.valid22450
  · exact MergedCutProfiles.Batch561.valid22451
theorem numericValid3653 : retention3653.NumericValid := by decide +kernel
def certificate3653 : RatCutBinCertificate := ⟨⟨retention3653,(439198536121533511/250000000000000000),(637434242080419/1000000000000000000),(172941595975847257/25000000000000000),(130298704246109328290933/250000000000000000),(1169103046067443873/500000000000000000)⟩,(62499789406220421/62500000000000000),(338920056312222499/1000000000000000000),(294363546735231507/1000000000000000000),(1717192129475417/7812500000000000)⟩
theorem valid3653 : certificate3653.Valid := by decide +kernel
theorem sound3653 : certificate3653.Sound := rat_cut_bin_certificate_sound certificate3653 profilesValid3653 numericValid3653 valid3653

def retention3654 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(64000000000000000000/75016018916683844152359),(1948673828087707737/40000000000000000),1,(152814774729452180924663306291191646457/64955794269590257900000000000000000000),false,MergedCutProfiles.Batch561.profile22452,(fun _ => MergedCutProfiles.Batch561.profile22452)⟩
theorem profilesValid3654 : retention3654.ProfilesValid := by
  exact MergedCutProfiles.Batch561.valid22452
theorem numericValid3654 : retention3654.NumericValid := by decide +kernel
def certificate3654 : RatCutBinCertificate := ⟨⟨retention3654,(439198536121533511/250000000000000000),(637434242080419/1000000000000000000),(172941595975847257/25000000000000000),(130298704246109328290933/250000000000000000),(2352434625981980871/1000000000000000000)⟩,(62499789406220421/62500000000000000),(87609168530635659/500000000000000000),(519055470225549497/1000000000000000000),(232958882752537077/200000000000000000)⟩
theorem valid3654 : certificate3654.Valid := by decide +kernel
theorem sound3654 : certificate3654.Sound := rat_cut_bin_certificate_sound certificate3654 profilesValid3654 numericValid3654 valid3654

def retention3655 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(1/2),64,1,(15960555614684130987744105293091422311/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch003.profile124,(fun _ => MergedCutProfiles.Batch003.profile124)⟩
theorem profilesValid3655 : retention3655.ProfilesValid := by
  exact MergedCutProfiles.Batch003.valid124
theorem numericValid3655 : retention3655.NumericValid := by decide +kernel
def certificate3655 : RatCutBinCertificate := ⟨⟨retention3655,(439198536121533511/250000000000000000),(637434242080419/1000000000000000000),(172941595975847257/25000000000000000),(130298704246109328290933/250000000000000000),(997372844570230951/1000000000000000000)⟩,(62499789406220421/62500000000000000),(102678971933671241/250000000000000000),(223806142441187583/1000000000000000000),(54948044924954689/250000000000000000)⟩
theorem valid3655 : certificate3655.Valid := by decide +kernel
theorem sound3655 : certificate3655.Sound := rat_cut_bin_certificate_sound certificate3655 profilesValid3655 numericValid3655 valid3655

def retention3656 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(64000000000000000000/75016018916683844152359),(14665424617935302959/1000000000000000000),1,(134042405054701663612841439864357579699/58661698471741211836000000000000000000),false,MergedCutProfiles.Batch561.profile22452,(fun _ => MergedCutProfiles.Batch561.profile22452)⟩
theorem profilesValid3656 : retention3656.ProfilesValid := by
  exact MergedCutProfiles.Batch561.valid22452
theorem numericValid3656 : retention3656.NumericValid := by decide +kernel
def certificate3656 : RatCutBinCertificate := ⟨⟨retention3656,(437837525121533511/250000000000000000),(637434242080419/1000000000000000000),(172941595975847257/25000000000000000),(130298704246109328290933/250000000000000000),(1142422924490429769/500000000000000000)⟩,(499998320470554009/500000000000000000),(2103661922770227/62500000000000000),(83368839271784297/100000000000000000),(82403786028993971/50000000000000000)⟩
theorem valid3656 : certificate3656.Valid := by decide +kernel
theorem sound3656 : certificate3656.Sound := rat_cut_bin_certificate_sound certificate3656 profilesValid3656 numericValid3656 valid3656

def retention3657 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(1/2),64,1,(15960555614684130987744105293091422311/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch003.profile124,(fun _ => MergedCutProfiles.Batch003.profile124)⟩
theorem profilesValid3657 : retention3657.ProfilesValid := by
  exact MergedCutProfiles.Batch003.valid124
theorem numericValid3657 : retention3657.NumericValid := by decide +kernel
def certificate3657 : RatCutBinCertificate := ⟨⟨retention3657,(437837525121533511/250000000000000000),(637434242080419/1000000000000000000),(172941595975847257/25000000000000000),(130298704246109328290933/250000000000000000),(249343336554117977/250000000000000000)⟩,(499998320470554009/500000000000000000),(19276806343920183/250000000000000000),(44961424422876973/62500000000000000),(35324050951771039/50000000000000000)⟩
theorem valid3657 : certificate3657.Valid := by decide +kernel
theorem sound3657 : certificate3657.Sound := rat_cut_bin_certificate_sound certificate3657 profilesValid3657 numericValid3657 valid3657

def retention3658 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(645947192915845418/47800972580928223399921),(567569639520166127/1000000000000000000),4,(4984329930498374630881531382300761983/2270278558080664508000000000000000000),true,MergedCutProfiles.Batch561.profile22453,![MergedCutProfiles.Batch561.profile22453,MergedCutProfiles.Batch561.profile22454,MergedCutProfiles.Batch441.profile17645,MergedCutProfiles.Batch441.profile17645,MergedCutProfiles.Batch561.profile22455,MergedCutProfiles.Batch561.profile22455,MergedCutProfiles.Batch561.profile22455,MergedCutProfiles.Batch307.profile12314,MergedCutProfiles.Batch307.profile12314,MergedCutProfiles.Batch307.profile12314,MergedCutProfiles.Batch441.profile17646,MergedCutProfiles.Batch441.profile17646,MergedCutProfiles.Batch441.profile17646,MergedCutProfiles.Batch441.profile17647,MergedCutProfiles.Batch441.profile17647,MergedCutProfiles.Batch441.profile17647]⟩
theorem profilesValid3658 : retention3658.ProfilesValid := by
  change ∀ j : Fin 16, (retention3658.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch561.valid22453
  · exact MergedCutProfiles.Batch561.valid22454
  · exact MergedCutProfiles.Batch441.valid17645
  · exact MergedCutProfiles.Batch441.valid17645
  · exact MergedCutProfiles.Batch561.valid22455
  · exact MergedCutProfiles.Batch561.valid22455
  · exact MergedCutProfiles.Batch561.valid22455
  · exact MergedCutProfiles.Batch307.valid12314
  · exact MergedCutProfiles.Batch307.valid12314
  · exact MergedCutProfiles.Batch307.valid12314
  · exact MergedCutProfiles.Batch441.valid17646
  · exact MergedCutProfiles.Batch441.valid17646
  · exact MergedCutProfiles.Batch441.valid17646
  · exact MergedCutProfiles.Batch441.valid17647
  · exact MergedCutProfiles.Batch441.valid17647
  · exact MergedCutProfiles.Batch441.valid17647
theorem numericValid3658 : retention3658.NumericValid := by decide +kernel
def certificate3658 : RatCutBinCertificate := ⟨⟨retention3658,(924644786538216869/500000000000000000),(249776479000013/250000000000000000),(1399931098764986143/200000000000000000),(336055224918426238233403/1000000000000000000),(219441480106196403/100000000000000000)⟩,(999994500574185357/1000000000000000000),(118865993105031127/200000000000000000),(19285579849927423/200000000000000000),(42605022782831953/1000000000000000000)⟩
theorem valid3658 : certificate3658.Valid := by decide +kernel
theorem sound3658 : certificate3658.Sound := rat_cut_bin_certificate_sound certificate3658 profilesValid3658 numericValid3658 valid3658

def retention3659 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(1343108110000000000/47800972580928223399921),(322973596457922709/500000000000000000),4,(6023176662821544689669486172727937223/2583788771663381672000000000000000000),true,MergedCutProfiles.Batch561.profile22454,![MergedCutProfiles.Batch561.profile22454,MergedCutProfiles.Batch441.profile17645,MergedCutProfiles.Batch561.profile22455,MergedCutProfiles.Batch307.profile12314,MergedCutProfiles.Batch441.profile17646,MergedCutProfiles.Batch441.profile17646,MergedCutProfiles.Batch441.profile17647,MergedCutProfiles.Batch441.profile17647,MergedCutProfiles.Batch003.profile126,MergedCutProfiles.Batch003.profile126,MergedCutProfiles.Batch307.profile12315,MergedCutProfiles.Batch307.profile12315,MergedCutProfiles.Batch307.profile12315,MergedCutProfiles.Batch441.profile17648,MergedCutProfiles.Batch441.profile17648,MergedCutProfiles.Batch441.profile17648]⟩
theorem profilesValid3659 : retention3659.ProfilesValid := by
  change ∀ j : Fin 16, (retention3659.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch561.valid22454
  · exact MergedCutProfiles.Batch441.valid17645
  · exact MergedCutProfiles.Batch561.valid22455
  · exact MergedCutProfiles.Batch307.valid12314
  · exact MergedCutProfiles.Batch441.valid17646
  · exact MergedCutProfiles.Batch441.valid17646
  · exact MergedCutProfiles.Batch441.valid17647
  · exact MergedCutProfiles.Batch441.valid17647
  · exact MergedCutProfiles.Batch003.valid126
  · exact MergedCutProfiles.Batch003.valid126
  · exact MergedCutProfiles.Batch307.valid12315
  · exact MergedCutProfiles.Batch307.valid12315
  · exact MergedCutProfiles.Batch307.valid12315
  · exact MergedCutProfiles.Batch441.valid17648
  · exact MergedCutProfiles.Batch441.valid17648
  · exact MergedCutProfiles.Batch441.valid17648
theorem numericValid3659 : retention3659.NumericValid := by decide +kernel
def certificate3659 : RatCutBinCertificate := ⟨⟨retention3659,(924644786538216869/500000000000000000),(249776479000013/250000000000000000),(1399931098764986143/200000000000000000),(336055224918426238233403/1000000000000000000),(291260679415913911/125000000000000000)⟩,(999994500574185357/1000000000000000000),(25619773183265763/50000000000000000),(36246722485250827/250000000000000000),(68919377671244661/1000000000000000000)⟩
theorem valid3659 : certificate3659.Valid := by decide +kernel
theorem sound3659 : certificate3659.Sound := rat_cut_bin_certificate_sound certificate3659 profilesValid3659 numericValid3659 valid3659

def certificates : List RatCutBinCertificate := [certificate3648,certificate3649,certificate3650,certificate3651,certificate3652,certificate3653,certificate3654,certificate3655,certificate3656,certificate3657,certificate3658,certificate3659]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3648,List.forall_mem_cons.mpr ⟨sound3649,List.forall_mem_cons.mpr ⟨sound3650,List.forall_mem_cons.mpr ⟨sound3651,List.forall_mem_cons.mpr ⟨sound3652,List.forall_mem_cons.mpr ⟨sound3653,List.forall_mem_cons.mpr ⟨sound3654,List.forall_mem_cons.mpr ⟨sound3655,List.forall_mem_cons.mpr ⟨sound3656,List.forall_mem_cons.mpr ⟨sound3657,List.forall_mem_cons.mpr ⟨sound3658,List.forall_mem_cons.mpr ⟨sound3659,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch304
