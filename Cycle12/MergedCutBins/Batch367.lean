import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch015
import Cycle12.MergedCutProfiles.Batch016
import Cycle12.MergedCutProfiles.Batch315
import Cycle12.MergedCutProfiles.Batch450
import Cycle12.MergedCutProfiles.Batch572
import Cycle12.MergedCutProfiles.Batch646

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch367

def retention4404 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(2476903544743812269/34110658361574968258455),(333010371519390751/500000000000000000),4,(1568144816222768012462806859656157767/666020743038781502000000000000000000),false,MergedCutProfiles.Batch646.profile25869,(fun _ => MergedCutProfiles.Batch646.profile25869)⟩
theorem profilesValid4404 : retention4404.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25869
theorem numericValid4404 : retention4404.NumericValid := by decide +kernel
def certificate4404 : RatCutBinCertificate := ⟨⟨retention4404,(1732693739350021743/1000000000000000000),(21663071517499/3125000000000000),(1928357821217704129/250000000000000000),(26431560741512952229391/100000000000000000),(293533708288892349/125000000000000000)⟩,(999993483193538271/1000000000000000000),(817735263387516209/1000000000000000000),(2215349961856157/125000000000000000),(532853314622951/62500000000000000)⟩
theorem valid4404 : certificate4404.Valid := by decide +kernel
theorem sound4404 : certificate4404.Sound := rat_cut_bin_certificate_sound certificate4404 profilesValid4404 numericValid4404 valid4404

def retention4405 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(12800000000000000000/6822131672314993651691),(2476903544743812269/1000000000000000000),(37/20),(9346792625979190629738501328290404122871/3963045671590099630400000000000000000000),false,MergedCutProfiles.Batch646.profile25867,(fun _ => MergedCutProfiles.Batch646.profile25867)⟩
theorem profilesValid4405 : retention4405.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25867
theorem numericValid4405 : retention4405.NumericValid := by decide +kernel
def certificate4405 : RatCutBinCertificate := ⟨⟨retention4405,(1732693739350021743/1000000000000000000),(21663071517499/3125000000000000),(1928357821217704129/250000000000000000),(26431560741512952229391/100000000000000000),(235560641570516719/100000000000000000)⟩,(999993483193538271/1000000000000000000),(313252322418519809/500000000000000000),(8054235260523477/100000000000000000),(80253442743858843/1000000000000000000)⟩
theorem valid4405 : certificate4405.Valid := by decide +kernel
theorem sound4405 : certificate4405.Sound := rat_cut_bin_certificate_sound certificate4405 profilesValid4405 numericValid4405 valid4405

def retention4406 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(1/40),64,1,(5521006157748263722366590743283645279/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch646.profile25870,(fun _ => MergedCutProfiles.Batch646.profile25870)⟩
theorem profilesValid4406 : retention4406.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25870
theorem numericValid4406 : retention4406.NumericValid := by decide +kernel
def certificate4406 : RatCutBinCertificate := ⟨⟨retention4406,(1732693739350021743/1000000000000000000),(21663071517499/3125000000000000),(1928357821217704129/250000000000000000),(26431560741512952229391/100000000000000000),(2155085831058302723/1000000000000000000)⟩,(999993483193538271/1000000000000000000),(76485131655265399/125000000000000000),(17510468547046013/200000000000000000),(45633757818517307/250000000000000000)⟩
theorem valid4406 : certificate4406.Valid := by decide +kernel
theorem sound4406 : certificate4406.Sound := rat_cut_bin_certificate_sound certificate4406 profilesValid4406 numericValid4406 valid4406

def retention4407 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(26094195766158844/1126032546869808610311),(147556396243375137/250000000000000000),4,(1060684898199951948161016850343541619/472180467978800438400000000000000000),true,MergedCutProfiles.Batch646.profile25871,![MergedCutProfiles.Batch646.profile25871,MergedCutProfiles.Batch646.profile25872,MergedCutProfiles.Batch646.profile25873,MergedCutProfiles.Batch646.profile25873,MergedCutProfiles.Batch572.profile22886,MergedCutProfiles.Batch646.profile25874,MergedCutProfiles.Batch646.profile25874,MergedCutProfiles.Batch646.profile25874,MergedCutProfiles.Batch572.profile22887,MergedCutProfiles.Batch572.profile22887,MergedCutProfiles.Batch646.profile25875,MergedCutProfiles.Batch646.profile25875,MergedCutProfiles.Batch646.profile25875,MergedCutProfiles.Batch572.profile22888,MergedCutProfiles.Batch572.profile22888,MergedCutProfiles.Batch572.profile22888]⟩
theorem profilesValid4407 : retention4407.ProfilesValid := by
  change ∀ j : Fin 16, (retention4407.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch646.valid25871
  · exact MergedCutProfiles.Batch646.valid25872
  · exact MergedCutProfiles.Batch646.valid25873
  · exact MergedCutProfiles.Batch646.valid25873
  · exact MergedCutProfiles.Batch572.valid22886
  · exact MergedCutProfiles.Batch646.valid25874
  · exact MergedCutProfiles.Batch646.valid25874
  · exact MergedCutProfiles.Batch646.valid25874
  · exact MergedCutProfiles.Batch572.valid22887
  · exact MergedCutProfiles.Batch572.valid22887
  · exact MergedCutProfiles.Batch646.valid25875
  · exact MergedCutProfiles.Batch646.valid25875
  · exact MergedCutProfiles.Batch646.valid25875
  · exact MergedCutProfiles.Batch572.valid22888
  · exact MergedCutProfiles.Batch572.valid22888
  · exact MergedCutProfiles.Batch572.valid22888
theorem numericValid4407 : retention4407.NumericValid := by decide +kernel
def certificate4407 : RatCutBinCertificate := ⟨⟨retention4407,(1867766899684518983/1000000000000000000),(1008381335301397/125000000000000000),(390525103957195497/50000000000000000),(229720465311909498745229/1000000000000000000),(223863841235562907/100000000000000000)⟩,(999991925755069429/1000000000000000000),(548561746560211933/1000000000000000000),(24410272919520181/200000000000000000),(27608578446985219/500000000000000000)⟩
theorem valid4407 : certificate4407.Valid := by decide +kernel
theorem sound4407 : certificate4407.Sound := rat_cut_bin_certificate_sound certificate4407 profilesValid4407 numericValid4407 valid4407

def retention4408 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(5418198500000000/125114727429978734479),(84806136240016243/125000000000000000),4,(1256491571988144756794929167499781/530038351500101518750000000000000),true,MergedCutProfiles.Batch646.profile25872,![MergedCutProfiles.Batch646.profile25872,MergedCutProfiles.Batch646.profile25873,MergedCutProfiles.Batch572.profile22886,MergedCutProfiles.Batch646.profile25874,MergedCutProfiles.Batch572.profile22887,MergedCutProfiles.Batch646.profile25875,MergedCutProfiles.Batch646.profile25875,MergedCutProfiles.Batch572.profile22888,MergedCutProfiles.Batch450.profile18013,MergedCutProfiles.Batch450.profile18013,MergedCutProfiles.Batch572.profile22889,MergedCutProfiles.Batch572.profile22889,MergedCutProfiles.Batch572.profile22890,MergedCutProfiles.Batch572.profile22890,MergedCutProfiles.Batch572.profile22891,MergedCutProfiles.Batch572.profile22891]⟩
theorem profilesValid4408 : retention4408.ProfilesValid := by
  change ∀ j : Fin 16, (retention4408.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch646.valid25872
  · exact MergedCutProfiles.Batch646.valid25873
  · exact MergedCutProfiles.Batch572.valid22886
  · exact MergedCutProfiles.Batch646.valid25874
  · exact MergedCutProfiles.Batch572.valid22887
  · exact MergedCutProfiles.Batch646.valid25875
  · exact MergedCutProfiles.Batch646.valid25875
  · exact MergedCutProfiles.Batch572.valid22888
  · exact MergedCutProfiles.Batch450.valid18013
  · exact MergedCutProfiles.Batch450.valid18013
  · exact MergedCutProfiles.Batch572.valid22889
  · exact MergedCutProfiles.Batch572.valid22889
  · exact MergedCutProfiles.Batch572.valid22890
  · exact MergedCutProfiles.Batch572.valid22890
  · exact MergedCutProfiles.Batch572.valid22891
  · exact MergedCutProfiles.Batch572.valid22891
theorem numericValid4408 : retention4408.NumericValid := by decide +kernel
def certificate4408 : RatCutBinCertificate := ⟨⟨retention4408,(1867766899684518983/1000000000000000000),(1008381335301397/125000000000000000),(390525103957195497/50000000000000000),(229720465311909498745229/1000000000000000000),(2362850810666312291/1000000000000000000)⟩,(999991925755069429/1000000000000000000),(474167530949743869/1000000000000000000),(5375346980090191/31250000000000000),(83444749767725977/1000000000000000000)⟩
theorem valid4408 : certificate4408.Valid := by decide +kernel
theorem sound4408 : certificate4408.Sound := rat_cut_bin_certificate_sound certificate4408 profilesValid4408 numericValid4408 valid4408

def retention4409 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1348006713834557017/29276846218615023868086),(1267858449/1000000000),(5/2),(99420173576028810671788917873797831/41912676000000000000000000000000000),true,MergedCutProfiles.Batch646.profile25872,![MergedCutProfiles.Batch646.profile25872,MergedCutProfiles.Batch646.profile25873,MergedCutProfiles.Batch646.profile25874,MergedCutProfiles.Batch646.profile25874,MergedCutProfiles.Batch572.profile22887,MergedCutProfiles.Batch646.profile25875,MergedCutProfiles.Batch572.profile22888,MergedCutProfiles.Batch572.profile22888,MergedCutProfiles.Batch450.profile18013,MergedCutProfiles.Batch450.profile18013,MergedCutProfiles.Batch572.profile22889,MergedCutProfiles.Batch572.profile22890,MergedCutProfiles.Batch572.profile22890,MergedCutProfiles.Batch572.profile22890,MergedCutProfiles.Batch572.profile22891,MergedCutProfiles.Batch572.profile22891]⟩
theorem profilesValid4409 : retention4409.ProfilesValid := by
  change ∀ j : Fin 16, (retention4409.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch646.valid25872
  · exact MergedCutProfiles.Batch646.valid25873
  · exact MergedCutProfiles.Batch646.valid25874
  · exact MergedCutProfiles.Batch646.valid25874
  · exact MergedCutProfiles.Batch572.valid22887
  · exact MergedCutProfiles.Batch646.valid25875
  · exact MergedCutProfiles.Batch572.valid22888
  · exact MergedCutProfiles.Batch572.valid22888
  · exact MergedCutProfiles.Batch450.valid18013
  · exact MergedCutProfiles.Batch450.valid18013
  · exact MergedCutProfiles.Batch572.valid22889
  · exact MergedCutProfiles.Batch572.valid22890
  · exact MergedCutProfiles.Batch572.valid22890
  · exact MergedCutProfiles.Batch572.valid22890
  · exact MergedCutProfiles.Batch572.valid22891
  · exact MergedCutProfiles.Batch572.valid22891
theorem numericValid4409 : retention4409.NumericValid := by decide +kernel
def certificate4409 : RatCutBinCertificate := ⟨⟨retention4409,(1867766899684518983/1000000000000000000),(1008381335301397/125000000000000000),(390525103957195497/50000000000000000),(229720465311909498745229/1000000000000000000),(1183628044442333/500000000000000)⟩,(999991925755069429/1000000000000000000),(66372064980320951/200000000000000000),(151037215860430821/500000000000000000),(110119129770653539/500000000000000000)⟩
theorem valid4409 : certificate4409.Valid := by decide +kernel
theorem sound4409 : certificate4409.Sound := rat_cut_bin_certificate_sound certificate4409 profilesValid4409 numericValid4409 valid4409

def retention4410 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(32000000000000000000/14638423109307511934043),(1348006713834557017/1000000000000000000),(12/5),(313108840913526255503968904256455357079/134800671383455701700000000000000000000),true,MergedCutProfiles.Batch015.profile611,![MergedCutProfiles.Batch015.profile611,MergedCutProfiles.Batch015.profile612,MergedCutProfiles.Batch015.profile613,MergedCutProfiles.Batch015.profile614,MergedCutProfiles.Batch015.profile615,MergedCutProfiles.Batch015.profile616,MergedCutProfiles.Batch450.profile18032,MergedCutProfiles.Batch015.profile618,MergedCutProfiles.Batch015.profile619,MergedCutProfiles.Batch016.profile640,MergedCutProfiles.Batch450.profile18033,MergedCutProfiles.Batch015.profile622,MergedCutProfiles.Batch450.profile18035,MergedCutProfiles.Batch315.profile12623,MergedCutProfiles.Batch315.profile12624,MergedCutProfiles.Batch450.profile18036]⟩
theorem profilesValid4410 : retention4410.ProfilesValid := by
  change ∀ j : Fin 16, (retention4410.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch015.valid611
  · exact MergedCutProfiles.Batch015.valid612
  · exact MergedCutProfiles.Batch015.valid613
  · exact MergedCutProfiles.Batch015.valid614
  · exact MergedCutProfiles.Batch015.valid615
  · exact MergedCutProfiles.Batch015.valid616
  · exact MergedCutProfiles.Batch450.valid18032
  · exact MergedCutProfiles.Batch015.valid618
  · exact MergedCutProfiles.Batch015.valid619
  · exact MergedCutProfiles.Batch016.valid640
  · exact MergedCutProfiles.Batch450.valid18033
  · exact MergedCutProfiles.Batch015.valid622
  · exact MergedCutProfiles.Batch450.valid18035
  · exact MergedCutProfiles.Batch315.valid12623
  · exact MergedCutProfiles.Batch315.valid12624
  · exact MergedCutProfiles.Batch450.valid18036
theorem numericValid4410 : retention4410.NumericValid := by decide +kernel
def certificate4410 : RatCutBinCertificate := ⟨⟨retention4410,(1867766899684518983/1000000000000000000),(1008381335301397/125000000000000000),(390525103957195497/50000000000000000),(229720465311909498745229/1000000000000000000),(463624886651250699/200000000000000000)⟩,(999991925755069429/1000000000000000000),(164504939224170879/500000000000000000),(152615037459528643/500000000000000000),(56758252847653451/250000000000000000)⟩
theorem valid4410 : certificate4410.Valid := by decide +kernel
theorem sound4410 : certificate4410.Sound := rat_cut_bin_certificate_sound certificate4410 profilesValid4410 numericValid4410 valid4410

def retention4411 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1/2),64,1,(255369632393373974456752157088663284991/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch016.profile655,(fun _ => MergedCutProfiles.Batch016.profile655)⟩
theorem profilesValid4411 : retention4411.ProfilesValid := by
  exact MergedCutProfiles.Batch016.valid655
theorem numericValid4411 : retention4411.NumericValid := by decide +kernel
def certificate4411 : RatCutBinCertificate := ⟨⟨retention4411,(1867766899684518983/1000000000000000000),(1008381335301397/125000000000000000),(390525103957195497/50000000000000000),(229720465311909498745229/1000000000000000000),(99560850980400827/100000000000000000)⟩,(999991925755069429/1000000000000000000),(204833814540639317/500000000000000000),(44948049254120999/200000000000000000),(110162017436785329/500000000000000000)⟩
theorem valid4411 : certificate4411.Valid := by decide +kernel
theorem sound4411 : certificate4411.Sound := rat_cut_bin_certificate_sound certificate4411 profilesValid4411 numericValid4411 valid4411

def retention4412 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(32000000000000000000/14638423109307511934043),(4153433896437213359/250000000000000000),1,(151296353691754422234017640973211645943/66454942342995413744000000000000000000),false,MergedCutProfiles.Batch646.profile25876,(fun _ => MergedCutProfiles.Batch646.profile25876)⟩
theorem profilesValid4412 : retention4412.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25876
theorem numericValid4412 : retention4412.NumericValid := by decide +kernel
def certificate4412 : RatCutBinCertificate := ⟨⟨retention4412,(1788083167684518983/1000000000000000000),(1008381335301397/125000000000000000),(390525103957195497/50000000000000000),(229720465311909498745229/1000000000000000000),(113741445205953277/50000000000000000)⟩,(999992270223109833/1000000000000000000),(29202969278835233/1000000000000000000),(846584316153787839/1000000000000000000),(1693884676613305689/1000000000000000000)⟩
theorem valid4412 : certificate4412.Valid := by decide +kernel
theorem sound4412 : certificate4412.Sound := rat_cut_bin_certificate_sound certificate4412 profilesValid4412 numericValid4412 valid4412

def retention4413 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1/2),64,1,(255369632393373974456752157088663284991/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch016.profile655,(fun _ => MergedCutProfiles.Batch016.profile655)⟩
theorem profilesValid4413 : retention4413.ProfilesValid := by
  exact MergedCutProfiles.Batch016.valid655
theorem numericValid4413 : retention4413.NumericValid := by decide +kernel
def certificate4413 : RatCutBinCertificate := ⟨⟨retention4413,(1788083167684518983/1000000000000000000),(1008381335301397/125000000000000000),(390525103957195497/50000000000000000),(229720465311909498745229/1000000000000000000),(995690810877415171/1000000000000000000)⟩,(999992270223109833/1000000000000000000),(33359632265288757/500000000000000000),(744967963434389703/1000000000000000000),(730388824374930093/1000000000000000000)⟩
theorem valid4413 : certificate4413.Valid := by decide +kernel
theorem sound4413 : certificate4413.Sound := rat_cut_bin_certificate_sound certificate4413 profilesValid4413 numericValid4413 valid4413

def retention4414 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(334478993976944407/14638423109307511934043),(20697957548078243/31250000000000000),4,(779959022710152942915606700963083/331167320769251888000000000000000),false,MergedCutProfiles.Batch646.profile25877,(fun _ => MergedCutProfiles.Batch646.profile25877)⟩
theorem profilesValid4414 : retention4414.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25877
theorem numericValid4414 : retention4414.NumericValid := by decide +kernel
def certificate4414 : RatCutBinCertificate := ⟨⟨retention4414,(1739045616684518983/1000000000000000000),(1008381335301397/125000000000000000),(390525103957195497/50000000000000000),(229720465311909498745229/1000000000000000000),(18343722298380723/7812500000000000)⟩,(62499530138095579/62500000000000000),(407903785026395601/500000000000000000),(9056478787928309/500000000000000000),(8703753711689863/1000000000000000000)⟩
theorem valid4414 : certificate4414.Valid := by decide +kernel
theorem sound4414 : certificate4414.Sound := rat_cut_bin_certificate_sound certificate4414 profilesValid4414 numericValid4414 valid4414

def retention4415 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(2297466528986703401/29276846218615023868086),(334478993976944407/500000000000000000),4,(616113427369390292329107021759363/261311714044487817968750000000000),false,MergedCutProfiles.Batch646.profile25878,(fun _ => MergedCutProfiles.Batch646.profile25878)⟩
theorem profilesValid4415 : retention4415.ProfilesValid := by
  exact MergedCutProfiles.Batch646.valid25878
theorem numericValid4415 : retention4415.NumericValid := by decide +kernel
def certificate4415 : RatCutBinCertificate := ⟨⟨retention4415,(1739045616684518983/1000000000000000000),(1008381335301397/125000000000000000),(390525103957195497/50000000000000000),(229720465311909498745229/1000000000000000000),(1175293635943386741/500000000000000000)⟩,(62499530138095579/62500000000000000),(812350910689846839/1000000000000000000),(18823986606703399/1000000000000000000),(362795740884991/40000000000000000)⟩
theorem valid4415 : certificate4415.Valid := by decide +kernel
theorem sound4415 : certificate4415.Sound := rat_cut_bin_certificate_sound certificate4415 profilesValid4415 numericValid4415 valid4415

def certificates : List RatCutBinCertificate := [certificate4404,certificate4405,certificate4406,certificate4407,certificate4408,certificate4409,certificate4410,certificate4411,certificate4412,certificate4413,certificate4414,certificate4415]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4404,List.forall_mem_cons.mpr ⟨sound4405,List.forall_mem_cons.mpr ⟨sound4406,List.forall_mem_cons.mpr ⟨sound4407,List.forall_mem_cons.mpr ⟨sound4408,List.forall_mem_cons.mpr ⟨sound4409,List.forall_mem_cons.mpr ⟨sound4410,List.forall_mem_cons.mpr ⟨sound4411,List.forall_mem_cons.mpr ⟨sound4412,List.forall_mem_cons.mpr ⟨sound4413,List.forall_mem_cons.mpr ⟨sound4414,List.forall_mem_cons.mpr ⟨sound4415,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch367
