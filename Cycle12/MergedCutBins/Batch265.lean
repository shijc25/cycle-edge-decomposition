import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch372
import Cycle12.MergedCutProfiles.Batch487
import Cycle12.MergedCutProfiles.Batch488

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch265

def retention3180 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(45030134447636185480/99889477241786592563),(9825011217736900381/1000000000000000000),(21/20),(17155148179680091899070211441769135890999/15720017948379040609600000000000000000000),false,MergedCutProfiles.Batch487.profile19488,(fun _ => MergedCutProfiles.Batch487.profile19488)⟩
theorem profilesValid3180 : retention3180.ProfilesValid := by
  exact MergedCutProfiles.Batch487.valid19488
theorem numericValid3180 : retention3180.NumericValid := by decide +kernel
def certificate3180 : RatCutBinCertificate := ⟨⟨retention3180,(2067653077504617027/1000000000000000000),(114392751307786871/1000000000000000000),(201386138320021857/15625000000000000),(1294770104493794485091/1000000000000000000),(268006036642655367/250000000000000000)⟩,(249644305448760783/250000000000000000),(451074273615944687/1000000000000000000),(189814732908823817/1000000000000000000),(22009945459035441/125000000000000000)⟩
theorem valid3180 : certificate3180.Valid := by decide +kernel
theorem sound3180 : certificate3180.Sound := rat_cut_bin_certificate_sound certificate3180 profilesValid3180 numericValid3180 valid3180

def retention3181 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(49741282821100178808/99889477241786592563),(1125753361190904637/25000000000000000),1,(1440979566068393946574053910123062027/1440964302324357935360000000000000000),false,MergedCutProfiles.Batch487.profile19489,(fun _ => MergedCutProfiles.Batch487.profile19489)⟩
theorem profilesValid3181 : retention3181.ProfilesValid := by
  exact MergedCutProfiles.Batch487.valid19489
theorem numericValid3181 : retention3181.NumericValid := by decide +kernel
def certificate3181 : RatCutBinCertificate := ⟨⟨retention3181,(2067653077504617027/1000000000000000000),(114392751307786871/1000000000000000000),(201386138320021857/15625000000000000),(1294770104493794485091/1000000000000000000),(196331853080804019/200000000000000000)⟩,(249644305448760783/250000000000000000),(460749185737917523/1000000000000000000),(91107703296912583/500000000000000000),(174804844846574877/1000000000000000000)⟩
theorem valid3181 : certificate3181.Valid := by decide +kernel
theorem sound3181 : certificate3181.Sound := rat_cut_bin_certificate_sound certificate3181 profilesValid3181 numericValid3181 valid3181

def retention3182 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(1/2),(6217660352637522351/125000000000000000),1,(19362233542484820652770245785760921/19430188601992257346875000000000000),false,MergedCutProfiles.Batch372.profile14918,(fun _ => MergedCutProfiles.Batch372.profile14918)⟩
theorem profilesValid3182 : retention3182.ProfilesValid := by
  exact MergedCutProfiles.Batch372.valid14918
theorem numericValid3182 : retention3182.NumericValid := by decide +kernel
def certificate3182 : RatCutBinCertificate := ⟨⟨retention3182,(2067653077504617027/1000000000000000000),(114392751307786871/1000000000000000000),(201386138320021857/15625000000000000),(1294770104493794485091/1000000000000000000),(122268910038911169/125000000000000000)⟩,(249644305448760783/250000000000000000),(461556753161311499/1000000000000000000),(36318066785461417/200000000000000000),(4348661685085331/25000000000000000)⟩
theorem valid3182 : certificate3182.Valid := by decide +kernel
theorem sound3182 : certificate3182.Sound := rat_cut_bin_certificate_sound certificate3182 profilesValid3182 numericValid3182 valid3182

def retention3183 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(45730784546856066554/99889477241786592563),(4988942145967276989/500000000000000000),1,(4687115810510599661719269387026442479/4434615240859801768000000000000000000),false,MergedCutProfiles.Batch487.profile19490,(fun _ => MergedCutProfiles.Batch487.profile19490)⟩
theorem profilesValid3183 : retention3183.ProfilesValid := by
  exact MergedCutProfiles.Batch487.valid19490
theorem numericValid3183 : retention3183.NumericValid := by decide +kernel
def certificate3183 : RatCutBinCertificate := ⟨⟨retention3183,(2186715853504617027/1000000000000000000),(114392751307786871/1000000000000000000),(201386138320021857/15625000000000000),(1294770104493794485091/1000000000000000000),(207506071278409531/200000000000000000)⟩,(39939811123241467/40000000000000000),(60500323705255569/500000000000000000),(124285881064519011/200000000000000000),(583098954796820703/1000000000000000000)⟩
theorem valid3183 : certificate3183.Valid := by decide +kernel
theorem sound3183 : certificate3183.Sound := rat_cut_bin_certificate_sound certificate3183 profilesValid3183 numericValid3183 valid3183

def retention3184 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(49519886700196074074/99889477241786592563),(22865392273428033277/500000000000000000),1,(3533549974091518893845691508602813439/3517752657450466658000000000000000000),false,MergedCutProfiles.Batch487.profile19491,(fun _ => MergedCutProfiles.Batch487.profile19491)⟩
theorem profilesValid3184 : retention3184.ProfilesValid := by
  exact MergedCutProfiles.Batch487.valid19491
theorem numericValid3184 : retention3184.NumericValid := by decide +kernel
def certificate3184 : RatCutBinCertificate := ⟨⟨retention3184,(2186715853504617027/1000000000000000000),(114392751307786871/1000000000000000000),(201386138320021857/15625000000000000),(1294770104493794485091/1000000000000000000),(123135335011685423/125000000000000000)⟩,(39939811123241467/40000000000000000),(127442952118072283/1000000000000000000),(608283558148955331/1000000000000000000),(585680818675314259/1000000000000000000)⟩
theorem valid3184 : certificate3184.Valid := by decide +kernel
theorem sound3184 : certificate3184.Sound := rat_cut_bin_certificate_sound certificate3184 profilesValid3184 numericValid3184 valid3184

def retention3185 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(1/2),(24759943350098037037/500000000000000000),1,(154204937125968297167145270869137889/154749645938112731481250000000000000),false,MergedCutProfiles.Batch372.profile14918,(fun _ => MergedCutProfiles.Batch372.profile14918)⟩
theorem profilesValid3185 : retention3185.ProfilesValid := by
  exact MergedCutProfiles.Batch372.valid14918
theorem numericValid3185 : retention3185.NumericValid := by decide +kernel
def certificate3185 : RatCutBinCertificate := ⟨⟨retention3185,(2186715853504617027/1000000000000000000),(114392751307786871/1000000000000000000),(201386138320021857/15625000000000000),(1294770104493794485091/1000000000000000000),(244268001511941297/250000000000000000)⟩,(39939811123241467/40000000000000000),(64243906311117297/500000000000000000),(75772305807562473/125000000000000000),(115987204048785137/200000000000000000)⟩
theorem valid3185 : certificate3185.Valid := by decide +kernel
theorem sound3185 : certificate3185.Sound := rat_cut_bin_certificate_sound certificate3185 profilesValid3185 numericValid3185 valid3185

def retention3186 : RatCutRetentionCertificate := ⟨(49/1000),(99/2000),(98647549890628253/12200395166876784908),(386815213765820029/500000000000000000),(7/2),(18349449875049576443/8000000000000000000),true,MergedCutProfiles.Batch487.profile19492,![MergedCutProfiles.Batch487.profile19492,MergedCutProfiles.Batch487.profile19493,MergedCutProfiles.Batch487.profile19494,MergedCutProfiles.Batch487.profile19495,MergedCutProfiles.Batch487.profile19496,MergedCutProfiles.Batch487.profile19497,MergedCutProfiles.Batch487.profile19498,MergedCutProfiles.Batch487.profile19499,MergedCutProfiles.Batch487.profile19500,MergedCutProfiles.Batch487.profile19501,MergedCutProfiles.Batch487.profile19502,MergedCutProfiles.Batch487.profile19503,MergedCutProfiles.Batch487.profile19504,MergedCutProfiles.Batch487.profile19505,MergedCutProfiles.Batch487.profile19506,MergedCutProfiles.Batch487.profile19507]⟩
theorem profilesValid3186 : retention3186.ProfilesValid := by
  change ∀ j : Fin 16, (retention3186.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch487.valid19492
  · exact MergedCutProfiles.Batch487.valid19493
  · exact MergedCutProfiles.Batch487.valid19494
  · exact MergedCutProfiles.Batch487.valid19495
  · exact MergedCutProfiles.Batch487.valid19496
  · exact MergedCutProfiles.Batch487.valid19497
  · exact MergedCutProfiles.Batch487.valid19498
  · exact MergedCutProfiles.Batch487.valid19499
  · exact MergedCutProfiles.Batch487.valid19500
  · exact MergedCutProfiles.Batch487.valid19501
  · exact MergedCutProfiles.Batch487.valid19502
  · exact MergedCutProfiles.Batch487.valid19503
  · exact MergedCutProfiles.Batch487.valid19504
  · exact MergedCutProfiles.Batch487.valid19505
  · exact MergedCutProfiles.Batch487.valid19506
  · exact MergedCutProfiles.Batch487.valid19507
theorem numericValid3186 : retention3186.NumericValid := by decide +kernel
def certificate3186 : RatCutBinCertificate := ⟨⟨retention3186,(1039401304388942213/500000000000000000),(7315173282470881/62500000000000000),(13102927914331457069/1000000000000000000),(80158553512351214387/62500000000000000),(557171849096690379/250000000000000000)⟩,(12482053674009459/12500000000000000),(423600265144643569/1000000000000000000),(21254126696459387/100000000000000000),(218771577205397/2000000000000000)⟩
theorem valid3186 : certificate3186.Valid := by decide +kernel
theorem sound3186 : certificate3186.Sound := rat_cut_bin_certificate_sound certificate3186 profilesValid3186 numericValid3186 valid3186

def retention3187 : RatCutRetentionCertificate := ⟨(49/1000),(99/2000),(34148142406250000/3050098791719196227),(98647549890628253/125000000000000000),(69/20),(363788448148538332589/160000000000000000000),true,MergedCutProfiles.Batch487.profile19508,![MergedCutProfiles.Batch487.profile19508,MergedCutProfiles.Batch487.profile19509,MergedCutProfiles.Batch487.profile19510,MergedCutProfiles.Batch487.profile19511,MergedCutProfiles.Batch487.profile19498,MergedCutProfiles.Batch487.profile19512,MergedCutProfiles.Batch487.profile19513,MergedCutProfiles.Batch487.profile19514,MergedCutProfiles.Batch487.profile19515,MergedCutProfiles.Batch487.profile19516,MergedCutProfiles.Batch487.profile19517,MergedCutProfiles.Batch487.profile19518,MergedCutProfiles.Batch487.profile19519,MergedCutProfiles.Batch488.profile19520,MergedCutProfiles.Batch488.profile19521,MergedCutProfiles.Batch488.profile19522]⟩
theorem profilesValid3187 : retention3187.ProfilesValid := by
  change ∀ j : Fin 16, (retention3187.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch487.valid19508
  · exact MergedCutProfiles.Batch487.valid19509
  · exact MergedCutProfiles.Batch487.valid19510
  · exact MergedCutProfiles.Batch487.valid19511
  · exact MergedCutProfiles.Batch487.valid19498
  · exact MergedCutProfiles.Batch487.valid19512
  · exact MergedCutProfiles.Batch487.valid19513
  · exact MergedCutProfiles.Batch487.valid19514
  · exact MergedCutProfiles.Batch487.valid19515
  · exact MergedCutProfiles.Batch487.valid19516
  · exact MergedCutProfiles.Batch487.valid19517
  · exact MergedCutProfiles.Batch487.valid19518
  · exact MergedCutProfiles.Batch487.valid19519
  · exact MergedCutProfiles.Batch488.valid19520
  · exact MergedCutProfiles.Batch488.valid19521
  · exact MergedCutProfiles.Batch488.valid19522
theorem numericValid3187 : retention3187.NumericValid := by decide +kernel
def certificate3187 : RatCutBinCertificate := ⟨⟨retention3187,(1039401304388942213/500000000000000000),(7315173282470881/62500000000000000),(13102927914331457069/1000000000000000000),(80158553512351214387/62500000000000000),(276201557275269147/125000000000000000)⟩,(12482053674009459/12500000000000000),(105692685431019993/250000000000000000),(213254594219960113/1000000000000000000),(27596202414109291/250000000000000000)⟩
theorem valid3187 : certificate3187.Valid := by decide +kernel
theorem sound3187 : certificate3187.Sound := rat_cut_bin_certificate_sound certificate3187 profilesValid3187 numericValid3187 valid3187

def retention3188 : RatCutRetentionCertificate := ⟨(49/1000),(99/2000),(1095926995790969345/97603161335014279264),(1092740557/1000000000),(13/5),(8993355717718390589/4000000000000000000),true,MergedCutProfiles.Batch487.profile19508,![MergedCutProfiles.Batch487.profile19508,MergedCutProfiles.Batch487.profile19509,MergedCutProfiles.Batch487.profile19510,MergedCutProfiles.Batch487.profile19511,MergedCutProfiles.Batch487.profile19498,MergedCutProfiles.Batch487.profile19512,MergedCutProfiles.Batch487.profile19513,MergedCutProfiles.Batch487.profile19514,MergedCutProfiles.Batch487.profile19515,MergedCutProfiles.Batch487.profile19516,MergedCutProfiles.Batch487.profile19517,MergedCutProfiles.Batch487.profile19518,MergedCutProfiles.Batch487.profile19519,MergedCutProfiles.Batch488.profile19520,MergedCutProfiles.Batch488.profile19523,MergedCutProfiles.Batch488.profile19524]⟩
theorem profilesValid3188 : retention3188.ProfilesValid := by
  change ∀ j : Fin 16, (retention3188.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch487.valid19508
  · exact MergedCutProfiles.Batch487.valid19509
  · exact MergedCutProfiles.Batch487.valid19510
  · exact MergedCutProfiles.Batch487.valid19511
  · exact MergedCutProfiles.Batch487.valid19498
  · exact MergedCutProfiles.Batch487.valid19512
  · exact MergedCutProfiles.Batch487.valid19513
  · exact MergedCutProfiles.Batch487.valid19514
  · exact MergedCutProfiles.Batch487.valid19515
  · exact MergedCutProfiles.Batch487.valid19516
  · exact MergedCutProfiles.Batch487.valid19517
  · exact MergedCutProfiles.Batch487.valid19518
  · exact MergedCutProfiles.Batch487.valid19519
  · exact MergedCutProfiles.Batch488.valid19520
  · exact MergedCutProfiles.Batch488.valid19523
  · exact MergedCutProfiles.Batch488.valid19524
theorem numericValid3188 : retention3188.NumericValid := by decide +kernel
def certificate3188 : RatCutBinCertificate := ⟨⟨retention3188,(1039401304388942213/500000000000000000),(7315173282470881/62500000000000000),(13102927914331457069/1000000000000000000),(80158553512351214387/62500000000000000),(110002893452300261/50000000000000000)⟩,(12482053674009459/12500000000000000),(362332908177949529/1000000000000000000),(269825588509089797/1000000000000000000),(87815054974581811/500000000000000000)⟩
theorem valid3188 : certificate3188.Valid := by decide +kernel
theorem sound3188 : certificate3188.Sound := rat_cut_bin_certificate_sound certificate3188 profilesValid3188 numericValid3188 valid3188

def retention3189 : RatCutRetentionCertificate := ⟨(49/1000),(99/2000),(290837147404932819/24400790333753569816),(219185399158193869/200000000000000000),(13/5),(574953955320912528153/256000000000000000000),true,MergedCutProfiles.Batch488.profile19525,![MergedCutProfiles.Batch488.profile19525,MergedCutProfiles.Batch487.profile19494,MergedCutProfiles.Batch488.profile19526,MergedCutProfiles.Batch488.profile19527,MergedCutProfiles.Batch488.profile19528,MergedCutProfiles.Batch488.profile19529,MergedCutProfiles.Batch488.profile19530,MergedCutProfiles.Batch488.profile19531,MergedCutProfiles.Batch488.profile19532,MergedCutProfiles.Batch488.profile19533,MergedCutProfiles.Batch488.profile19534,MergedCutProfiles.Batch488.profile19535,MergedCutProfiles.Batch488.profile19536,MergedCutProfiles.Batch488.profile19521,MergedCutProfiles.Batch488.profile19522,MergedCutProfiles.Batch488.profile19537]⟩
theorem profilesValid3189 : retention3189.ProfilesValid := by
  change ∀ j : Fin 16, (retention3189.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch488.valid19525
  · exact MergedCutProfiles.Batch487.valid19494
  · exact MergedCutProfiles.Batch488.valid19526
  · exact MergedCutProfiles.Batch488.valid19527
  · exact MergedCutProfiles.Batch488.valid19528
  · exact MergedCutProfiles.Batch488.valid19529
  · exact MergedCutProfiles.Batch488.valid19530
  · exact MergedCutProfiles.Batch488.valid19531
  · exact MergedCutProfiles.Batch488.valid19532
  · exact MergedCutProfiles.Batch488.valid19533
  · exact MergedCutProfiles.Batch488.valid19534
  · exact MergedCutProfiles.Batch488.valid19535
  · exact MergedCutProfiles.Batch488.valid19536
  · exact MergedCutProfiles.Batch488.valid19521
  · exact MergedCutProfiles.Batch488.valid19522
  · exact MergedCutProfiles.Batch488.valid19537
theorem numericValid3189 : retention3189.NumericValid := by decide +kernel
def certificate3189 : RatCutBinCertificate := ⟨⟨retention3189,(1039401304388942213/500000000000000000),(7315173282470881/62500000000000000),(13102927914331457069/1000000000000000000),(80158553512351214387/62500000000000000),(137352052006101733/62500000000000000)⟩,(12482053674009459/12500000000000000),(45282687013404167/125000000000000000),(67474521022738109/250000000000000000),(35129046853421381/200000000000000000)⟩
theorem valid3189 : certificate3189.Valid := by decide +kernel
theorem sound3189 : certificate3189.Sound := rat_cut_bin_certificate_sound certificate3189 profilesValid3189 numericValid3189 valid3189

def retention3190 : RatCutRetentionCertificate := ⟨(49/1000),(99/2000),(2630646653193916775/97603161335014279264),(290837147404932819/250000000000000000),(5/2),(34760315402551097641/16000000000000000000),true,MergedCutProfiles.Batch488.profile19538,![MergedCutProfiles.Batch488.profile19538,MergedCutProfiles.Batch488.profile19539,MergedCutProfiles.Batch487.profile19501,MergedCutProfiles.Batch488.profile19540,MergedCutProfiles.Batch487.profile19518,MergedCutProfiles.Batch488.profile19541,MergedCutProfiles.Batch488.profile19542,MergedCutProfiles.Batch488.profile19543,MergedCutProfiles.Batch488.profile19544,MergedCutProfiles.Batch488.profile19545,MergedCutProfiles.Batch488.profile19546,MergedCutProfiles.Batch488.profile19547,MergedCutProfiles.Batch488.profile19548,MergedCutProfiles.Batch488.profile19549,MergedCutProfiles.Batch488.profile19550,MergedCutProfiles.Batch488.profile19551]⟩
theorem profilesValid3190 : retention3190.ProfilesValid := by
  change ∀ j : Fin 16, (retention3190.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch488.valid19538
  · exact MergedCutProfiles.Batch488.valid19539
  · exact MergedCutProfiles.Batch487.valid19501
  · exact MergedCutProfiles.Batch488.valid19540
  · exact MergedCutProfiles.Batch487.valid19518
  · exact MergedCutProfiles.Batch488.valid19541
  · exact MergedCutProfiles.Batch488.valid19542
  · exact MergedCutProfiles.Batch488.valid19543
  · exact MergedCutProfiles.Batch488.valid19544
  · exact MergedCutProfiles.Batch488.valid19545
  · exact MergedCutProfiles.Batch488.valid19546
  · exact MergedCutProfiles.Batch488.valid19547
  · exact MergedCutProfiles.Batch488.valid19548
  · exact MergedCutProfiles.Batch488.valid19549
  · exact MergedCutProfiles.Batch488.valid19550
  · exact MergedCutProfiles.Batch488.valid19551
theorem numericValid3190 : retention3190.NumericValid := by decide +kernel
def certificate3190 : RatCutBinCertificate := ⟨⟨retention3190,(1039401304388942213/500000000000000000),(7315173282470881/62500000000000000),(13102927914331457069/1000000000000000000),(80158553512351214387/62500000000000000),(1063047825306923957/500000000000000000)⟩,(12482053674009459/12500000000000000),(364769737842095939/1000000000000000000),(267360192128981289/1000000000000000000),(175636329240542099/1000000000000000000)⟩
theorem valid3190 : certificate3190.Valid := by decide +kernel
theorem sound3190 : certificate3190.Sound := rat_cut_bin_certificate_sound certificate3190 profilesValid3190 numericValid3190 valid3190

def retention3191 : RatCutRetentionCertificate := ⟨(49/1000),(99/2000),(6615478221949402795/24400790333753569816),(105225866127756671/40000000000000000),(3/2),(62248846928639812788458115901019188511/42090346451102668400000000000000000000),false,MergedCutProfiles.Batch488.profile19552,(fun _ => MergedCutProfiles.Batch488.profile19552)⟩
theorem profilesValid3191 : retention3191.ProfilesValid := by
  exact MergedCutProfiles.Batch488.valid19552
theorem numericValid3191 : retention3191.NumericValid := by decide +kernel
def certificate3191 : RatCutBinCertificate := ⟨⟨retention3191,(1039401304388942213/500000000000000000),(7315173282470881/62500000000000000),(13102927914331457069/1000000000000000000),(80158553512351214387/62500000000000000),(1451079851755308659/1000000000000000000)⟩,(12482053674009459/12500000000000000),(202926637619137981/500000000000000000),(228161899135810087/1000000000000000000),(176977325493536503/1000000000000000000)⟩
theorem valid3191 : certificate3191.Valid := by decide +kernel
theorem sound3191 : certificate3191.Sound := rat_cut_bin_certificate_sound certificate3191 profilesValid3191 numericValid3191 valid3191

def certificates : List RatCutBinCertificate := [certificate3180,certificate3181,certificate3182,certificate3183,certificate3184,certificate3185,certificate3186,certificate3187,certificate3188,certificate3189,certificate3190,certificate3191]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3180,List.forall_mem_cons.mpr ⟨sound3181,List.forall_mem_cons.mpr ⟨sound3182,List.forall_mem_cons.mpr ⟨sound3183,List.forall_mem_cons.mpr ⟨sound3184,List.forall_mem_cons.mpr ⟨sound3185,List.forall_mem_cons.mpr ⟨sound3186,List.forall_mem_cons.mpr ⟨sound3187,List.forall_mem_cons.mpr ⟨sound3188,List.forall_mem_cons.mpr ⟨sound3189,List.forall_mem_cons.mpr ⟨sound3190,List.forall_mem_cons.mpr ⟨sound3191,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch265
