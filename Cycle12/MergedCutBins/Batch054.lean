import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch107
import Cycle12.MergedCutProfiles.Batch108
import Cycle12.MergedCutProfiles.Batch109
import Cycle12.MergedCutProfiles.Batch110

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch054

def retention648 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(1/2),(6187944001186392239/500000000000000000),(21/20),(4943267954609293082757373068683883342399/4950355200949113791200000000000000000000),false,MergedCutProfiles.Batch107.profile4319,(fun _ => MergedCutProfiles.Batch107.profile4319)⟩
theorem profilesValid648 : retention648.ProfilesValid := by
  exact MergedCutProfiles.Batch107.valid4319
theorem numericValid648 : retention648.NumericValid := by decide +kernel
def certificate648 : RatCutBinCertificate := ⟨⟨retention648,(310702373916455967/125000000000000000),(23060041821265367/250000000000000000),(12081787966095065807/1000000000000000000),(15048211230393984179/50000000000000000),(195728441037547327/200000000000000000)⟩,(992478433061543411/1000000000000000000),(206789421067389559/500000000000000000),(221268569325846227/1000000000000000000),(190931792788963007/1000000000000000000)⟩
theorem valid648 : certificate648.Valid := by decide +kernel
theorem sound648 : certificate648.Sound := rat_cut_bin_certificate_sound certificate648 profilesValid648 numericValid648 valid648

def retention649 : RatCutRetentionCertificate := ⟨(89/2000),(179/4000),(818552823133886430/24531142369496734013),(810448339736521217/1000000000000000000),(31/10),(169845653314886486959/80000000000000000000),true,MergedCutProfiles.Batch108.profile4323,![MergedCutProfiles.Batch108.profile4323,MergedCutProfiles.Batch108.profile4324,MergedCutProfiles.Batch108.profile4325,MergedCutProfiles.Batch108.profile4326,MergedCutProfiles.Batch108.profile4327,MergedCutProfiles.Batch108.profile4328,MergedCutProfiles.Batch108.profile4329,MergedCutProfiles.Batch108.profile4330,MergedCutProfiles.Batch108.profile4331,MergedCutProfiles.Batch108.profile4332,MergedCutProfiles.Batch108.profile4333,MergedCutProfiles.Batch108.profile4334,MergedCutProfiles.Batch108.profile4335,MergedCutProfiles.Batch108.profile4336,MergedCutProfiles.Batch108.profile4337,MergedCutProfiles.Batch108.profile4338]⟩
theorem profilesValid649 : retention649.ProfilesValid := by
  change ∀ j : Fin 16, (retention649.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch108.valid4323
  · exact MergedCutProfiles.Batch108.valid4324
  · exact MergedCutProfiles.Batch108.valid4325
  · exact MergedCutProfiles.Batch108.valid4326
  · exact MergedCutProfiles.Batch108.valid4327
  · exact MergedCutProfiles.Batch108.valid4328
  · exact MergedCutProfiles.Batch108.valid4329
  · exact MergedCutProfiles.Batch108.valid4330
  · exact MergedCutProfiles.Batch108.valid4331
  · exact MergedCutProfiles.Batch108.valid4332
  · exact MergedCutProfiles.Batch108.valid4333
  · exact MergedCutProfiles.Batch108.valid4334
  · exact MergedCutProfiles.Batch108.valid4335
  · exact MergedCutProfiles.Batch108.valid4336
  · exact MergedCutProfiles.Batch108.valid4337
  · exact MergedCutProfiles.Batch108.valid4338
theorem numericValid649 : retention649.NumericValid := by decide +kernel
def certificate649 : RatCutBinCertificate := ⟨⟨retention649,(2108540953063887229/1000000000000000000),(11674148968388029/125000000000000000),(3044533470984429167/250000000000000000),(59831432486578824093/200000000000000000),(2072936688028906233/1000000000000000000)⟩,(496798805894623267/500000000000000000),(97534660360461687/250000000000000000),(48528067947964571/200000000000000000),(127177069929600861/1000000000000000000)⟩
theorem valid649 : certificate649.Valid := by decide +kernel
theorem sound649 : certificate649.Sound := rat_cut_bin_certificate_sound certificate649 profilesValid649 numericValid649 valid649

def retention650 : RatCutRetentionCertificate := ⟨(89/2000),(179/4000),(894552158000000000/24531142369496734013),(81855282313388643/100000000000000000),(61/20),(53960760515824161223/25600000000000000000),true,MergedCutProfiles.Batch108.profile4339,![MergedCutProfiles.Batch108.profile4339,MergedCutProfiles.Batch108.profile4340,MergedCutProfiles.Batch108.profile4341,MergedCutProfiles.Batch108.profile4342,MergedCutProfiles.Batch108.profile4343,MergedCutProfiles.Batch108.profile4344,MergedCutProfiles.Batch108.profile4345,MergedCutProfiles.Batch108.profile4346,MergedCutProfiles.Batch108.profile4347,MergedCutProfiles.Batch108.profile4348,MergedCutProfiles.Batch108.profile4349,MergedCutProfiles.Batch108.profile4350,MergedCutProfiles.Batch108.profile4351,MergedCutProfiles.Batch108.profile4352,MergedCutProfiles.Batch108.profile4353,MergedCutProfiles.Batch108.profile4354]⟩
theorem profilesValid650 : retention650.ProfilesValid := by
  change ∀ j : Fin 16, (retention650.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch108.valid4339
  · exact MergedCutProfiles.Batch108.valid4340
  · exact MergedCutProfiles.Batch108.valid4341
  · exact MergedCutProfiles.Batch108.valid4342
  · exact MergedCutProfiles.Batch108.valid4343
  · exact MergedCutProfiles.Batch108.valid4344
  · exact MergedCutProfiles.Batch108.valid4345
  · exact MergedCutProfiles.Batch108.valid4346
  · exact MergedCutProfiles.Batch108.valid4347
  · exact MergedCutProfiles.Batch108.valid4348
  · exact MergedCutProfiles.Batch108.valid4349
  · exact MergedCutProfiles.Batch108.valid4350
  · exact MergedCutProfiles.Batch108.valid4351
  · exact MergedCutProfiles.Batch108.valid4352
  · exact MergedCutProfiles.Batch108.valid4353
  · exact MergedCutProfiles.Batch108.valid4354
theorem numericValid650 : retention650.NumericValid := by decide +kernel
def certificate650 : RatCutBinCertificate := ⟨⟨retention650,(2108540953063887229/1000000000000000000),(11674148968388029/125000000000000000),(3044533470984429167/250000000000000000),(59831432486578824093/200000000000000000),(2058516803003699329/1000000000000000000)⟩,(496798805894623267/500000000000000000),(391167603597232341/1000000000000000000),(60418309102062513/250000000000000000),(5097192437891031/40000000000000000)⟩
theorem valid650 : certificate650.Valid := by decide +kernel
theorem sound650 : certificate650.Sound := rat_cut_bin_certificate_sound certificate650 profilesValid650 numericValid650 valid650

def retention651 : RatCutRetentionCertificate := ⟨(89/2000),(179/4000),(988900992038869226/24531142369496734013),(447276079/500000000),(57/20),(16741578603814661637/8000000000000000000),true,MergedCutProfiles.Batch108.profile4355,![MergedCutProfiles.Batch108.profile4355,MergedCutProfiles.Batch108.profile4356,MergedCutProfiles.Batch108.profile4357,MergedCutProfiles.Batch108.profile4358,MergedCutProfiles.Batch108.profile4328,MergedCutProfiles.Batch108.profile4359,MergedCutProfiles.Batch109.profile4360,MergedCutProfiles.Batch109.profile4361,MergedCutProfiles.Batch109.profile4362,MergedCutProfiles.Batch109.profile4363,MergedCutProfiles.Batch109.profile4364,MergedCutProfiles.Batch109.profile4365,MergedCutProfiles.Batch109.profile4366,MergedCutProfiles.Batch109.profile4367,MergedCutProfiles.Batch109.profile4368,MergedCutProfiles.Batch109.profile4369]⟩
theorem profilesValid651 : retention651.ProfilesValid := by
  change ∀ j : Fin 16, (retention651.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch108.valid4355
  · exact MergedCutProfiles.Batch108.valid4356
  · exact MergedCutProfiles.Batch108.valid4357
  · exact MergedCutProfiles.Batch108.valid4358
  · exact MergedCutProfiles.Batch108.valid4328
  · exact MergedCutProfiles.Batch108.valid4359
  · exact MergedCutProfiles.Batch109.valid4360
  · exact MergedCutProfiles.Batch109.valid4361
  · exact MergedCutProfiles.Batch109.valid4362
  · exact MergedCutProfiles.Batch109.valid4363
  · exact MergedCutProfiles.Batch109.valid4364
  · exact MergedCutProfiles.Batch109.valid4365
  · exact MergedCutProfiles.Batch109.valid4366
  · exact MergedCutProfiles.Batch109.valid4367
  · exact MergedCutProfiles.Batch109.valid4368
  · exact MergedCutProfiles.Batch109.valid4369
theorem numericValid651 : retention651.NumericValid := by decide +kernel
def certificate651 : RatCutBinCertificate := ⟨⟨retention651,(2108540953063887229/1000000000000000000),(11674148968388029/125000000000000000),(3044533470984429167/250000000000000000),(59831432486578824093/200000000000000000),(2046606493140368293/1000000000000000000)⟩,(496798805894623267/500000000000000000),(189441661881812781/500000000000000000),(126698832899313809/500000000000000000),(28181779309590083/200000000000000000)⟩
theorem valid651 : certificate651.Valid := by decide +kernel
theorem sound651 : certificate651.Sound := rat_cut_bin_certificate_sound certificate651 profilesValid651 numericValid651 valid651

def retention652 : RatCutRetentionCertificate := ⟨(89/2000),(179/4000),(1850969918950481071/24531142369496734013),(494450496019434613/500000000000000000),(13/5),(1262706133000411073929/640000000000000000000),true,MergedCutProfiles.Batch109.profile4370,![MergedCutProfiles.Batch109.profile4370,MergedCutProfiles.Batch109.profile4371,MergedCutProfiles.Batch109.profile4372,MergedCutProfiles.Batch109.profile4373,MergedCutProfiles.Batch109.profile4374,MergedCutProfiles.Batch109.profile4375,MergedCutProfiles.Batch109.profile4376,MergedCutProfiles.Batch109.profile4377,MergedCutProfiles.Batch109.profile4378,MergedCutProfiles.Batch109.profile4379,MergedCutProfiles.Batch109.profile4380,MergedCutProfiles.Batch109.profile4381,MergedCutProfiles.Batch109.profile4382,MergedCutProfiles.Batch109.profile4383,MergedCutProfiles.Batch109.profile4384,MergedCutProfiles.Batch109.profile4385]⟩
theorem profilesValid652 : retention652.ProfilesValid := by
  change ∀ j : Fin 16, (retention652.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch109.valid4370
  · exact MergedCutProfiles.Batch109.valid4371
  · exact MergedCutProfiles.Batch109.valid4372
  · exact MergedCutProfiles.Batch109.valid4373
  · exact MergedCutProfiles.Batch109.valid4374
  · exact MergedCutProfiles.Batch109.valid4375
  · exact MergedCutProfiles.Batch109.valid4376
  · exact MergedCutProfiles.Batch109.valid4377
  · exact MergedCutProfiles.Batch109.valid4378
  · exact MergedCutProfiles.Batch109.valid4379
  · exact MergedCutProfiles.Batch109.valid4380
  · exact MergedCutProfiles.Batch109.valid4381
  · exact MergedCutProfiles.Batch109.valid4382
  · exact MergedCutProfiles.Batch109.valid4383
  · exact MergedCutProfiles.Batch109.valid4384
  · exact MergedCutProfiles.Batch109.valid4385
theorem numericValid652 : retention652.NumericValid := by decide +kernel
def certificate652 : RatCutBinCertificate := ⟨⟨retention652,(2108540953063887229/1000000000000000000),(11674148968388029/125000000000000000),(3044533470984429167/250000000000000000),(59831432486578824093/200000000000000000),(96546529966623463/50000000000000000)⟩,(496798805894623267/500000000000000000),(48215276324575783/125000000000000000),(15426384812021261/62500000000000000),(5646316642029853/40000000000000000)⟩
theorem valid652 : certificate652.Valid := by decide +kernel
theorem sound652 : certificate652.Sound := rat_cut_bin_certificate_sound certificate652 profilesValid652 numericValid652 valid652

def retention653 : RatCutRetentionCertificate := ⟨(89/2000),(179/4000),(139092350534385777/500635558561157837),(1850969918950481071/1000000000000000000),(33/20),(4312781390439563159657719963605954266031/2961551870320769713600000000000000000000),false,MergedCutProfiles.Batch109.profile4386,(fun _ => MergedCutProfiles.Batch109.profile4386)⟩
theorem profilesValid653 : retention653.ProfilesValid := by
  exact MergedCutProfiles.Batch109.valid4386
theorem numericValid653 : retention653.NumericValid := by decide +kernel
def certificate653 : RatCutBinCertificate := ⟨⟨retention653,(2108540953063887229/1000000000000000000),(11674148968388029/125000000000000000),(3044533470984429167/250000000000000000),(59831432486578824093/200000000000000000),(285914725289560451/200000000000000000)⟩,(496798805894623267/500000000000000000),(106601775225503659/250000000000000000),(210139626795318781/1000000000000000000),(140791002751382237/1000000000000000000)⟩
theorem valid653 : certificate653.Valid := by decide +kernel
theorem sound653 : certificate653.Sound := rat_cut_bin_certificate_sound certificate653 profilesValid653 numericValid653 valid653

def retention654 : RatCutRetentionCertificate := ⟨(89/2000),(179/4000),(11321119883205139558/24531142369496734013),(6815525176184903073/1000000000000000000),1,(265549651467566200833/256000000000000000000),true,MergedCutProfiles.Batch109.profile4387,![MergedCutProfiles.Batch109.profile4387,MergedCutProfiles.Batch109.profile4388,MergedCutProfiles.Batch109.profile4389,MergedCutProfiles.Batch109.profile4390,MergedCutProfiles.Batch109.profile4391,MergedCutProfiles.Batch109.profile4392,MergedCutProfiles.Batch109.profile4393,MergedCutProfiles.Batch109.profile4394,MergedCutProfiles.Batch109.profile4395,MergedCutProfiles.Batch109.profile4396,MergedCutProfiles.Batch109.profile4397,MergedCutProfiles.Batch109.profile4398,MergedCutProfiles.Batch109.profile4399,MergedCutProfiles.Batch110.profile4400,MergedCutProfiles.Batch110.profile4401,MergedCutProfiles.Batch110.profile4402]⟩
theorem profilesValid654 : retention654.ProfilesValid := by
  change ∀ j : Fin 16, (retention654.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch109.valid4387
  · exact MergedCutProfiles.Batch109.valid4388
  · exact MergedCutProfiles.Batch109.valid4389
  · exact MergedCutProfiles.Batch109.valid4390
  · exact MergedCutProfiles.Batch109.valid4391
  · exact MergedCutProfiles.Batch109.valid4392
  · exact MergedCutProfiles.Batch109.valid4393
  · exact MergedCutProfiles.Batch109.valid4394
  · exact MergedCutProfiles.Batch109.valid4395
  · exact MergedCutProfiles.Batch109.valid4396
  · exact MergedCutProfiles.Batch109.valid4397
  · exact MergedCutProfiles.Batch109.valid4398
  · exact MergedCutProfiles.Batch109.valid4399
  · exact MergedCutProfiles.Batch110.valid4400
  · exact MergedCutProfiles.Batch110.valid4401
  · exact MergedCutProfiles.Batch110.valid4402
theorem numericValid654 : retention654.NumericValid := by decide +kernel
def certificate654 : RatCutBinCertificate := ⟨⟨retention654,(2108540953063887229/1000000000000000000),(11674148968388029/125000000000000000),(3044533470984429167/250000000000000000),(59831432486578824093/200000000000000000),(510566171782198031/500000000000000000)⟩,(496798805894623267/500000000000000000),(243156611176408507/500000000000000000),(163102339949512149/1000000000000000000),(28770507486467073/200000000000000000)⟩
theorem valid654 : certificate654.Valid := by decide +kernel
theorem sound654 : certificate654.Sound := rat_cut_bin_certificate_sound certificate654 profilesValid654 numericValid654 valid654

def retention655 : RatCutRetentionCertificate := ⟨(89/2000),(179/4000),(12137772852225814229/24531142369496734013),(5660559941602569779/500000000000000000),(21/20),(4562774374280562979591591600209540986279/4528447953282055823200000000000000000000),false,MergedCutProfiles.Batch110.profile4403,(fun _ => MergedCutProfiles.Batch110.profile4403)⟩
theorem profilesValid655 : retention655.ProfilesValid := by
  exact MergedCutProfiles.Batch110.valid4403
theorem numericValid655 : retention655.NumericValid := by decide +kernel
def certificate655 : RatCutBinCertificate := ⟨⟨retention655,(2108540953063887229/1000000000000000000),(11674148968388029/125000000000000000),(3044533470984429167/250000000000000000),(59831432486578824093/200000000000000000),(49530048683480429/50000000000000000)⟩,(496798805894623267/500000000000000000),(242188551839287903/500000000000000000),(32900389194416271/200000000000000000),(142822998574304161/1000000000000000000)⟩
theorem valid655 : certificate655.Valid := by decide +kernel
theorem sound655 : certificate655.Sound := rat_cut_bin_certificate_sound certificate655 profilesValid655 numericValid655 valid655

def retention656 : RatCutRetentionCertificate := ⟨(89/2000),(179/4000),(250186746545879028/500635558561157837),(12137772852225814229/1000000000000000000),(21/20),(19397859666695188899198168050691831905159/19420436563561302766400000000000000000000),false,MergedCutProfiles.Batch110.profile4404,(fun _ => MergedCutProfiles.Batch110.profile4404)⟩
theorem profilesValid656 : retention656.ProfilesValid := by
  exact MergedCutProfiles.Batch110.valid4404
theorem numericValid656 : retention656.NumericValid := by decide +kernel
def certificate656 : RatCutBinCertificate := ⟨⟨retention656,(2108540953063887229/1000000000000000000),(11674148968388029/125000000000000000),(3044533470984429167/250000000000000000),(59831432486578824093/200000000000000000),(490929148643579191/500000000000000000)⟩,(496798805894623267/500000000000000000),(48695222262394459/100000000000000000),(16264210457103291/100000000000000000),(70372993017719113/500000000000000000)⟩
theorem valid656 : certificate656.Valid := by decide +kernel
theorem sound656 : certificate656.Sound := rat_cut_bin_certificate_sound certificate656 profilesValid656 numericValid656 valid656

def retention657 : RatCutRetentionCertificate := ⟨(89/2000),(179/4000),(1/2),(3064787645187018093/250000000000000000),(21/20),(102001282311072738043917251026869165513/102159588172900603100000000000000000000),false,MergedCutProfiles.Batch110.profile4405,(fun _ => MergedCutProfiles.Batch110.profile4405)⟩
theorem profilesValid657 : retention657.ProfilesValid := by
  exact MergedCutProfiles.Batch110.valid4405
theorem numericValid657 : retention657.NumericValid := by decide +kernel
def certificate657 : RatCutBinCertificate := ⟨⟨retention657,(2108540953063887229/1000000000000000000),(11674148968388029/125000000000000000),(3044533470984429167/250000000000000000),(59831432486578824093/200000000000000000),(490735620276346627/500000000000000000)⟩,(496798805894623267/500000000000000000),(15215800972538489/31250000000000000),(162675633415071713/1000000000000000000),(140818917384288061/1000000000000000000)⟩
theorem valid657 : certificate657.Valid := by decide +kernel
theorem sound657 : certificate657.Sound := rat_cut_bin_certificate_sound certificate657 profilesValid657 numericValid657 valid657

def retention658 : RatCutRetentionCertificate := ⟨(89/2000),(179/4000),(10930022203823649559/24531142369496734013),(29445848941629431/7812500000000000),(6/5),(415680511921485338884474246571104265951/376906866452856716800000000000000000000),false,MergedCutProfiles.Batch110.profile4406,(fun _ => MergedCutProfiles.Batch110.profile4406)⟩
theorem profilesValid658 : retention658.ProfilesValid := by
  exact MergedCutProfiles.Batch110.valid4406
theorem numericValid658 : retention658.NumericValid := by decide +kernel
def certificate658 : RatCutBinCertificate := ⟨⟨retention658,(2489083162063887229/1000000000000000000),(11674148968388029/125000000000000000),(3044533470984429167/250000000000000000),(59831432486578824093/200000000000000000),(1079965388936150829/1000000000000000000)⟩,(992441243461444659/1000000000000000000),(185882205311428093/500000000000000000),(65093370028293971/250000000000000000),(6057214285700547/31250000000000000)⟩
theorem valid658 : certificate658.Valid := by decide +kernel
theorem sound658 : certificate658.Sound := rat_cut_bin_certificate_sound certificate658 profilesValid658 numericValid658 valid658

def retention659 : RatCutRetentionCertificate := ⟨(89/2000),(179/4000),(12194279801155130706/24531142369496734013),(10930022203823649559/1000000000000000000),(21/20),(17531665799221365540768207669785179258239/17488035526117839294400000000000000000000),false,MergedCutProfiles.Batch110.profile4407,(fun _ => MergedCutProfiles.Batch110.profile4407)⟩
theorem profilesValid659 : retention659.ProfilesValid := by
  exact MergedCutProfiles.Batch110.valid4407
theorem numericValid659 : retention659.NumericValid := by decide +kernel
def certificate659 : RatCutBinCertificate := ⟨⟨retention659,(2489083162063887229/1000000000000000000),(11674148968388029/125000000000000000),(3044533470984429167/250000000000000000),(59831432486578824093/200000000000000000),(122806412254531011/125000000000000000)⟩,(992441243461444659/1000000000000000000),(81732844592591391/200000000000000000),(112818446778690501/500000000000000000),(193673311756674079/1000000000000000000)⟩
theorem valid659 : certificate659.Valid := by decide +kernel
theorem sound659 : certificate659.Sound := rat_cut_bin_certificate_sound certificate659 profilesValid659 numericValid659 valid659

def certificates : List RatCutBinCertificate := [certificate648,certificate649,certificate650,certificate651,certificate652,certificate653,certificate654,certificate655,certificate656,certificate657,certificate658,certificate659]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound648,List.forall_mem_cons.mpr ⟨sound649,List.forall_mem_cons.mpr ⟨sound650,List.forall_mem_cons.mpr ⟨sound651,List.forall_mem_cons.mpr ⟨sound652,List.forall_mem_cons.mpr ⟨sound653,List.forall_mem_cons.mpr ⟨sound654,List.forall_mem_cons.mpr ⟨sound655,List.forall_mem_cons.mpr ⟨sound656,List.forall_mem_cons.mpr ⟨sound657,List.forall_mem_cons.mpr ⟨sound658,List.forall_mem_cons.mpr ⟨sound659,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch054
