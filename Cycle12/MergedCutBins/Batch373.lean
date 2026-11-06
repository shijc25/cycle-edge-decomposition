import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch023
import Cycle12.MergedCutProfiles.Batch024
import Cycle12.MergedCutProfiles.Batch025
import Cycle12.MergedCutProfiles.Batch320
import Cycle12.MergedCutProfiles.Batch321
import Cycle12.MergedCutProfiles.Batch455
import Cycle12.MergedCutProfiles.Batch456
import Cycle12.MergedCutProfiles.Batch582
import Cycle12.MergedCutProfiles.Batch583
import Cycle12.MergedCutProfiles.Batch649
import Cycle12.MergedCutProfiles.Batch650

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch373

def retention4476 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(64000000000000000000/13947560834922328059369),(2327726307623210461/500000000000000000),(5/4),(14469784563119544299/6400000000000000000),true,MergedCutProfiles.Batch320.profile12807,![MergedCutProfiles.Batch320.profile12807,MergedCutProfiles.Batch023.profile950,MergedCutProfiles.Batch023.profile951,MergedCutProfiles.Batch455.profile18229,MergedCutProfiles.Batch455.profile18227,MergedCutProfiles.Batch024.profile968,MergedCutProfiles.Batch320.profile12815,MergedCutProfiles.Batch649.profile25981,MergedCutProfiles.Batch649.profile25982,MergedCutProfiles.Batch649.profile25983,MergedCutProfiles.Batch024.profile981,MergedCutProfiles.Batch649.profile25984,MergedCutProfiles.Batch649.profile25985,MergedCutProfiles.Batch649.profile25986,MergedCutProfiles.Batch649.profile25987,MergedCutProfiles.Batch320.profile12829]⟩
theorem profilesValid4476 : retention4476.ProfilesValid := by
  change ∀ j : Fin 16, (retention4476.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch320.valid12807
  · exact MergedCutProfiles.Batch023.valid950
  · exact MergedCutProfiles.Batch023.valid951
  · exact MergedCutProfiles.Batch455.valid18229
  · exact MergedCutProfiles.Batch455.valid18227
  · exact MergedCutProfiles.Batch024.valid968
  · exact MergedCutProfiles.Batch320.valid12815
  · exact MergedCutProfiles.Batch649.valid25981
  · exact MergedCutProfiles.Batch649.valid25982
  · exact MergedCutProfiles.Batch649.valid25983
  · exact MergedCutProfiles.Batch024.valid981
  · exact MergedCutProfiles.Batch649.valid25984
  · exact MergedCutProfiles.Batch649.valid25985
  · exact MergedCutProfiles.Batch649.valid25986
  · exact MergedCutProfiles.Batch649.valid25987
  · exact MergedCutProfiles.Batch320.valid12829
theorem numericValid4476 : retention4476.NumericValid := by decide +kernel
def certificate4476 : RatCutBinCertificate := ⟨⟨retention4476,(376519520824818943/200000000000000000),(16814618099358171/1000000000000000000),(4217252556058038791/500000000000000000),(118201867122811528571737/1000000000000000000),(56405312984869071/25000000000000000)⟩,(999984313850334839/1000000000000000000),(173542950082411/781250000000000),(221749051405424947/500000000000000000),(610980307080295883/1000000000000000000)⟩
theorem valid4476 : certificate4476.Valid := by decide +kernel
theorem sound4476 : certificate4476.Sound := rat_cut_bin_certificate_sound certificate4476 profilesValid4476 numericValid4476 valid4476

def retention4477 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(1/2),64,1,(3990175631981414592578765135707307871/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch025.profile1008,(fun _ => MergedCutProfiles.Batch025.profile1008)⟩
theorem profilesValid4477 : retention4477.ProfilesValid := by
  exact MergedCutProfiles.Batch025.valid1008
theorem numericValid4477 : retention4477.NumericValid := by decide +kernel
def certificate4477 : RatCutBinCertificate := ⟨⟨retention4477,(376519520824818943/200000000000000000),(16814618099358171/1000000000000000000),(4217252556058038791/500000000000000000),(118201867122811528571737/1000000000000000000),(198758170640924501/200000000000000000)⟩,(999984313850334839/1000000000000000000),(5111106533600367/12500000000000000),(112718122503112959/500000000000000000),(44121469481600481/200000000000000000)⟩
theorem valid4477 : certificate4477.Valid := by decide +kernel
theorem sound4477 : certificate4477.Sound := rat_cut_bin_certificate_sound certificate4477 profilesValid4477 numericValid4477 valid4477

def retention4478 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(64000000000000000000/13947560834922328059369),(17813450815624083751/1000000000000000000),1,(160691731328645370550458895322720016123/71253803262496335004000000000000000000),false,MergedCutProfiles.Batch649.profile25988,(fun _ => MergedCutProfiles.Batch649.profile25988)⟩
theorem profilesValid4478 : retention4478.ProfilesValid := by
  exact MergedCutProfiles.Batch649.valid25988
theorem numericValid4478 : retention4478.NumericValid := by decide +kernel
def certificate4478 : RatCutBinCertificate := ⟨⟨retention4478,(358774647224818943/200000000000000000),(16814618099358171/1000000000000000000),(4217252556058038791/500000000000000000),(118201867122811528571737/1000000000000000000),(281453248251613307/125000000000000000)⟩,(499992526559132669/500000000000000000),(6825676623993273/250000000000000000),(42607902850171111/50000000000000000),(1703401250561602551/1000000000000000000)⟩
theorem valid4478 : certificate4478.Valid := by decide +kernel
theorem sound4478 : certificate4478.Sound := rat_cut_bin_certificate_sound certificate4478 profilesValid4478 numericValid4478 valid4478

def retention4479 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(1/2),64,1,(3990175631981414592578765135707307871/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch025.profile1008,(fun _ => MergedCutProfiles.Batch025.profile1008)⟩
theorem profilesValid4479 : retention4479.ProfilesValid := by
  exact MergedCutProfiles.Batch025.valid1008
theorem numericValid4479 : retention4479.NumericValid := by decide +kernel
def certificate4479 : RatCutBinCertificate := ⟨⟨retention4479,(358774647224818943/200000000000000000),(16814618099358171/1000000000000000000),(4217252556058038791/500000000000000000),(118201867122811528571737/1000000000000000000),(496983864889295029/500000000000000000)⟩,(499992526559132669/500000000000000000),(30924285363122547/500000000000000000),(75731963094941013/100000000000000000),(2964912392876763/4000000000000000)⟩
theorem valid4479 : certificate4479.Valid := by decide +kernel
theorem sound4479 : certificate4479.Sound := rat_cut_bin_certificate_sound certificate4479 profilesValid4479 numericValid4479 valid4479

def retention4480 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(687004623374694166/13947560834922328059369),(680202597400687293/1000000000000000000),4,(2153898218759372122381337718898386453/906936796534249724000000000000000000),false,MergedCutProfiles.Batch649.profile25989,(fun _ => MergedCutProfiles.Batch649.profile25989)⟩
theorem profilesValid4480 : retention4480.ProfilesValid := by
  exact MergedCutProfiles.Batch649.valid25989
theorem numericValid4480 : retention4480.NumericValid := by decide +kernel
def certificate4480 : RatCutBinCertificate := ⟨⟨retention4480,(355671560424818943/200000000000000000),(16814618099358171/1000000000000000000),(4217252556058038791/500000000000000000),(118201867122811528571737/1000000000000000000),(2360734469042422463/1000000000000000000)⟩,(999985182395744453/1000000000000000000),(98043552177414981/125000000000000000),(25131824565891087/1000000000000000000),(6094154954146617/500000000000000000)⟩
theorem valid4480 : certificate4480.Valid := by decide +kernel
theorem sound4480 : certificate4480.Sound := rat_cut_bin_certificate_sound certificate4480 profilesValid4480 numericValid4480 valid4480

def retention4481 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(1616582246718277505/13947560834922328059369),(343502311687347083/500000000000000000),4,(1306208981636623295371356998305012043/549603698699755332800000000000000000),false,MergedCutProfiles.Batch649.profile25990,(fun _ => MergedCutProfiles.Batch649.profile25990)⟩
theorem profilesValid4481 : retention4481.ProfilesValid := by
  exact MergedCutProfiles.Batch649.valid25990
theorem numericValid4481 : retention4481.NumericValid := by decide +kernel
def certificate4481 : RatCutBinCertificate := ⟨⟨retention4481,(355671560424818943/200000000000000000),(16814618099358171/1000000000000000000),(4217252556058038791/500000000000000000),(118201867122811528571737/1000000000000000000),(295307114011870921/125000000000000000)⟩,(999985182395744453/1000000000000000000),(781401434451347487/1000000000000000000),(3231649458911317/125000000000000000),(12567867386432057/1000000000000000000)⟩
theorem valid4481 : certificate4481.Valid := by decide +kernel
theorem sound4481 : certificate4481.Sound := rat_cut_bin_certificate_sound certificate4481 profilesValid4481 numericValid4481 valid4481

def retention4482 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(64000000000000000000/13947560834922328059369),(323316449343655501/200000000000000000),(47/20),(240863259949212048431482301286216036631/103461263789969760320000000000000000000),false,MergedCutProfiles.Batch649.profile25988,(fun _ => MergedCutProfiles.Batch649.profile25988)⟩
theorem profilesValid4482 : retention4482.ProfilesValid := by
  exact MergedCutProfiles.Batch649.valid25988
theorem numericValid4482 : retention4482.NumericValid := by decide +kernel
def certificate4482 : RatCutBinCertificate := ⟨⟨retention4482,(355671560424818943/200000000000000000),(16814618099358171/1000000000000000000),(4217252556058038791/500000000000000000),(118201867122811528571737/1000000000000000000),(2319721227554451413/1000000000000000000)⟩,(999985182395744453/1000000000000000000),(656705064002888733/1000000000000000000),(33568571065884567/500000000000000000),(52602810353477091/1000000000000000000)⟩
theorem valid4482 : certificate4482.Valid := by decide +kernel
theorem sound4482 : certificate4482.Sound := rat_cut_bin_certificate_sound certificate4482 profilesValid4482 numericValid4482 valid4482

def retention4483 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(1/40),64,1,(22136666361545270151663927936276487791/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch649.profile25991,(fun _ => MergedCutProfiles.Batch649.profile25991)⟩
theorem profilesValid4483 : retention4483.ProfilesValid := by
  exact MergedCutProfiles.Batch649.valid25991
theorem numericValid4483 : retention4483.NumericValid := by decide +kernel
def certificate4483 : RatCutBinCertificate := ⟨⟨retention4483,(355671560424818943/200000000000000000),(16814618099358171/1000000000000000000),(4217252556058038791/500000000000000000),(118201867122811528571737/1000000000000000000),(431647715393120607/200000000000000000)⟩,(999985182395744453/1000000000000000000),(18692007483781639/31250000000000000),(47227733767953121/500000000000000000),(197204173306080369/1000000000000000000)⟩
theorem valid4483 : certificate4483.Valid := by decide +kernel
theorem sound4483 : certificate4483.Sound := rat_cut_bin_certificate_sound certificate4483 profilesValid4483 numericValid4483 valid4483

def retention4484 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(640521470371744607/12590448292418869216701),(310841914339471963/500000000000000000),4,(58981826766112166063/25600000000000000000),true,MergedCutProfiles.Batch649.profile25992,![MergedCutProfiles.Batch649.profile25992,MergedCutProfiles.Batch649.profile25993,MergedCutProfiles.Batch649.profile25994,MergedCutProfiles.Batch582.profile23313,MergedCutProfiles.Batch649.profile25995,MergedCutProfiles.Batch649.profile25995,MergedCutProfiles.Batch649.profile25996,MergedCutProfiles.Batch582.profile23314,MergedCutProfiles.Batch582.profile23314,MergedCutProfiles.Batch583.profile23325,MergedCutProfiles.Batch649.profile25997,MergedCutProfiles.Batch649.profile25997,MergedCutProfiles.Batch582.profile23315,MergedCutProfiles.Batch582.profile23315,MergedCutProfiles.Batch649.profile25998,MergedCutProfiles.Batch649.profile25998]⟩
theorem profilesValid4484 : retention4484.ProfilesValid := by
  change ∀ j : Fin 16, (retention4484.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch649.valid25992
  · exact MergedCutProfiles.Batch649.valid25993
  · exact MergedCutProfiles.Batch649.valid25994
  · exact MergedCutProfiles.Batch582.valid23313
  · exact MergedCutProfiles.Batch649.valid25995
  · exact MergedCutProfiles.Batch649.valid25995
  · exact MergedCutProfiles.Batch649.valid25996
  · exact MergedCutProfiles.Batch582.valid23314
  · exact MergedCutProfiles.Batch582.valid23314
  · exact MergedCutProfiles.Batch583.valid23325
  · exact MergedCutProfiles.Batch649.valid25997
  · exact MergedCutProfiles.Batch649.valid25997
  · exact MergedCutProfiles.Batch582.valid23315
  · exact MergedCutProfiles.Batch582.valid23315
  · exact MergedCutProfiles.Batch649.valid25998
  · exact MergedCutProfiles.Batch649.valid25998
theorem numericValid4484 : retention4484.NumericValid := by decide +kernel
def certificate4484 : RatCutBinCertificate := ⟨⟨retention4484,(188929242828945551/100000000000000000),(1860584005120499/100000000000000000),(4272969246167985191/500000000000000000),(108113375975837050826623/1000000000000000000),(2287524470601258801/1000000000000000000)⟩,(199996563745740623/200000000000000000),(253662249756288339/500000000000000000),(148402802786473627/1000000000000000000),(17249782125993103/250000000000000000)⟩
theorem valid4484 : certificate4484.Valid := by decide +kernel
theorem sound4484 : certificate4484.Sound := rat_cut_bin_certificate_sound certificate4484 profilesValid4484 numericValid4484 valid4484

def retention4485 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(1270648508000000000/12590448292418869216701),(640521470371744607/1000000000000000000),4,(149043982002412282207/64000000000000000000),true,MergedCutProfiles.Batch649.profile25993,![MergedCutProfiles.Batch649.profile25993,MergedCutProfiles.Batch582.profile23313,MergedCutProfiles.Batch649.profile25995,MergedCutProfiles.Batch582.profile23314,MergedCutProfiles.Batch583.profile23325,MergedCutProfiles.Batch649.profile25997,MergedCutProfiles.Batch582.profile23315,MergedCutProfiles.Batch649.profile25998,MergedCutProfiles.Batch456.profile18248,MergedCutProfiles.Batch649.profile25999,MergedCutProfiles.Batch582.profile23316,MergedCutProfiles.Batch582.profile23316,MergedCutProfiles.Batch582.profile23317,MergedCutProfiles.Batch583.profile23326,MergedCutProfiles.Batch583.profile23326,MergedCutProfiles.Batch582.profile23318]⟩
theorem profilesValid4485 : retention4485.ProfilesValid := by
  change ∀ j : Fin 16, (retention4485.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch649.valid25993
  · exact MergedCutProfiles.Batch582.valid23313
  · exact MergedCutProfiles.Batch649.valid25995
  · exact MergedCutProfiles.Batch582.valid23314
  · exact MergedCutProfiles.Batch583.valid23325
  · exact MergedCutProfiles.Batch649.valid25997
  · exact MergedCutProfiles.Batch582.valid23315
  · exact MergedCutProfiles.Batch649.valid25998
  · exact MergedCutProfiles.Batch456.valid18248
  · exact MergedCutProfiles.Batch649.valid25999
  · exact MergedCutProfiles.Batch582.valid23316
  · exact MergedCutProfiles.Batch582.valid23316
  · exact MergedCutProfiles.Batch582.valid23317
  · exact MergedCutProfiles.Batch583.valid23326
  · exact MergedCutProfiles.Batch583.valid23326
  · exact MergedCutProfiles.Batch582.valid23318
theorem numericValid4485 : retention4485.NumericValid := by decide +kernel
def certificate4485 : RatCutBinCertificate := ⟨⟨retention4485,(188929242828945551/100000000000000000),(1860584005120499/100000000000000000),(4272969246167985191/500000000000000000),(108113375975837050826623/1000000000000000000),(462471816274236331/200000000000000000)⟩,(199996563745740623/200000000000000000),(123045359174096127/250000000000000000),(1986340113357527/12500000000000000),(37474846732262109/500000000000000000)⟩
theorem valid4485 : certificate4485.Valid := by decide +kernel
theorem sound4485 : certificate4485.Sound := rat_cut_bin_certificate_sound certificate4485 profilesValid4485 numericValid4485 valid4485

def retention4486 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(8513161561093550678/12590448292418869216701),(317662127/250000000),(5/2),(18839353875976740919/8000000000000000000),true,MergedCutProfiles.Batch582.profile23315,![MergedCutProfiles.Batch582.profile23315,MergedCutProfiles.Batch582.profile23317,MergedCutProfiles.Batch456.profile18262,MergedCutProfiles.Batch583.profile23321,MergedCutProfiles.Batch583.profile23323,MergedCutProfiles.Batch456.profile18263,MergedCutProfiles.Batch321.profile12849,MergedCutProfiles.Batch025.profile1010,MergedCutProfiles.Batch321.profile12867,MergedCutProfiles.Batch456.profile18252,MergedCutProfiles.Batch320.profile12836,MergedCutProfiles.Batch456.profile18265,MergedCutProfiles.Batch583.profile23331,MergedCutProfiles.Batch025.profile1026,MergedCutProfiles.Batch320.profile12837,MergedCutProfiles.Batch650.profile26000]⟩
theorem profilesValid4486 : retention4486.ProfilesValid := by
  change ∀ j : Fin 16, (retention4486.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch582.valid23315
  · exact MergedCutProfiles.Batch582.valid23317
  · exact MergedCutProfiles.Batch456.valid18262
  · exact MergedCutProfiles.Batch583.valid23321
  · exact MergedCutProfiles.Batch583.valid23323
  · exact MergedCutProfiles.Batch456.valid18263
  · exact MergedCutProfiles.Batch321.valid12849
  · exact MergedCutProfiles.Batch025.valid1010
  · exact MergedCutProfiles.Batch321.valid12867
  · exact MergedCutProfiles.Batch456.valid18252
  · exact MergedCutProfiles.Batch320.valid12836
  · exact MergedCutProfiles.Batch456.valid18265
  · exact MergedCutProfiles.Batch583.valid23331
  · exact MergedCutProfiles.Batch025.valid1026
  · exact MergedCutProfiles.Batch320.valid12837
  · exact MergedCutProfiles.Batch650.valid26000
theorem numericValid4486 : retention4486.NumericValid := by decide +kernel
def certificate4486 : RatCutBinCertificate := ⟨⟨retention4486,(188929242828945551/100000000000000000),(1860584005120499/100000000000000000),(4272969246167985191/500000000000000000),(108113375975837050826623/1000000000000000000),(1172318011872699141/500000000000000000)⟩,(199996563745740623/200000000000000000),(328929960806817509/1000000000000000000),(38164862919389541/125000000000000000),(27633863953318943/125000000000000000)⟩
theorem valid4486 : certificate4486.Valid := by decide +kernel
theorem sound4486 : certificate4486.Sound := rat_cut_bin_certificate_sound certificate4486 profilesValid4486 numericValid4486 valid4486

def retention4487 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(64000000000000000000/12590448292418869216701),(4256580780546775339/500000000000000000),(21/20),(7561294326920413911337733897606921824679/3405264624437420271200000000000000000000),false,MergedCutProfiles.Batch650.profile26001,(fun _ => MergedCutProfiles.Batch650.profile26001)⟩
theorem profilesValid4487 : retention4487.ProfilesValid := by
  exact MergedCutProfiles.Batch650.valid26001
theorem numericValid4487 : retention4487.NumericValid := by decide +kernel
def certificate4487 : RatCutBinCertificate := ⟨⟨retention4487,(188929242828945551/100000000000000000),(1860584005120499/100000000000000000),(4272969246167985191/500000000000000000),(108113375975837050826623/1000000000000000000),(1108076463526748177/500000000000000000)⟩,(199996563745740623/200000000000000000),(1638704468530721/8000000000000000),(235060204671812149/500000000000000000),(50168551991320903/62500000000000000)⟩
theorem valid4487 : certificate4487.Valid := by decide +kernel
theorem sound4487 : certificate4487.Sound := rat_cut_bin_certificate_sound certificate4487 profilesValid4487 numericValid4487 valid4487

def certificates : List RatCutBinCertificate := [certificate4476,certificate4477,certificate4478,certificate4479,certificate4480,certificate4481,certificate4482,certificate4483,certificate4484,certificate4485,certificate4486,certificate4487]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4476,List.forall_mem_cons.mpr ⟨sound4477,List.forall_mem_cons.mpr ⟨sound4478,List.forall_mem_cons.mpr ⟨sound4479,List.forall_mem_cons.mpr ⟨sound4480,List.forall_mem_cons.mpr ⟨sound4481,List.forall_mem_cons.mpr ⟨sound4482,List.forall_mem_cons.mpr ⟨sound4483,List.forall_mem_cons.mpr ⟨sound4484,List.forall_mem_cons.mpr ⟨sound4485,List.forall_mem_cons.mpr ⟨sound4486,List.forall_mem_cons.mpr ⟨sound4487,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch373
