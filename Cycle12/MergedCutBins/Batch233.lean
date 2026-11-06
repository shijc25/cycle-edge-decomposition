import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch005
import Cycle12.MergedCutProfiles.Batch006
import Cycle12.MergedCutProfiles.Batch007
import Cycle12.MergedCutProfiles.Batch308
import Cycle12.MergedCutProfiles.Batch309
import Cycle12.MergedCutProfiles.Batch441
import Cycle12.MergedCutProfiles.Batch442

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch233

def retention2796 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(1/2),64,1,(63842211595158023048219618863822294719/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch005.profile236,(fun _ => MergedCutProfiles.Batch005.profile236)⟩
theorem profilesValid2796 : retention2796.ProfilesValid := by
  exact MergedCutProfiles.Batch005.valid236
theorem numericValid2796 : retention2796.NumericValid := by decide +kernel
def certificate2796 : RatCutBinCertificate := ⟨⟨retention2796,(358699172037669049/200000000000000000),(721626522366223/500000000000000000),(1770790956639435221/250000000000000000),(7347702253895599093683/125000000000000000),(997169116601674669/1000000000000000000)⟩,(999969519314328231/1000000000000000000),(413079277724320691/1000000000000000000),(110854963168222577/500000000000000000),(217683813818084091/1000000000000000000)⟩
theorem valid2796 : certificate2796.Valid := by decide +kernel
theorem sound2796 : certificate2796.Sound := rat_cut_bin_certificate_sound certificate2796 profilesValid2796 numericValid2796 valid2796

def retention2797 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(32000000000000000000/4131200709807438311641),(373364398994646671/50000000000000000),1,(63083750394307258462176331701601004079/29869151919571733680000000000000000000),false,MergedCutProfiles.Batch441.profile17669,(fun _ => MergedCutProfiles.Batch441.profile17669)⟩
theorem profilesValid2797 : retention2797.ProfilesValid := by
  exact MergedCutProfiles.Batch441.valid17669
theorem numericValid2797 : retention2797.NumericValid := by decide +kernel
def certificate2797 : RatCutBinCertificate := ⟨⟨retention2797,(388645840437669049/200000000000000000),(721626522366223/500000000000000000),(1770790956639435221/250000000000000000),(7347702253895599093683/125000000000000000),(1055803725261269787/500000000000000000)⟩,(999966974577435251/1000000000000000000),(70788314693995657/1000000000000000000),(734825341770320361/1000000000000000000),(1209566259383284349/1000000000000000000)⟩
theorem valid2797 : certificate2797.Valid := by decide +kernel
theorem sound2797 : certificate2797.Sound := rat_cut_bin_certificate_sound certificate2797 profilesValid2797 numericValid2797 valid2797

def retention2798 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(1/2),64,1,(63842211595158023048219618863822294719/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch005.profile236,(fun _ => MergedCutProfiles.Batch005.profile236)⟩
theorem profilesValid2798 : retention2798.ProfilesValid := by
  exact MergedCutProfiles.Batch005.valid236
theorem numericValid2798 : retention2798.NumericValid := by decide +kernel
def certificate2798 : RatCutBinCertificate := ⟨⟨retention2798,(388645840437669049/200000000000000000),(721626522366223/500000000000000000),(1770790956639435221/250000000000000000),(7347702253895599093683/125000000000000000),(997138607198374959/1000000000000000000)⟩,(999966974577435251/1000000000000000000),(149906072875621577/1000000000000000000),(564604576363193791/1000000000000000000),(110866720338994373/200000000000000000)⟩
theorem valid2798 : certificate2798.Valid := by decide +kernel
theorem sound2798 : certificate2798.Sound := rat_cut_bin_certificate_sound certificate2798 profilesValid2798 numericValid2798 valid2798

def retention2799 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(639623708801194803/6043575782156220922300),(7166373756065163/12500000000000000),4,(562171189950959305836481689974960511/254804400215650240000000000000000000),true,MergedCutProfiles.Batch441.profile17670,![MergedCutProfiles.Batch441.profile17670,MergedCutProfiles.Batch441.profile17671,MergedCutProfiles.Batch441.profile17672,MergedCutProfiles.Batch441.profile17673,MergedCutProfiles.Batch005.profile238,MergedCutProfiles.Batch441.profile17674,MergedCutProfiles.Batch441.profile17675,MergedCutProfiles.Batch308.profile12359,MergedCutProfiles.Batch005.profile239,MergedCutProfiles.Batch006.profile254,MergedCutProfiles.Batch441.profile17676,MergedCutProfiles.Batch309.profile12360,MergedCutProfiles.Batch309.profile12360,MergedCutProfiles.Batch006.profile240,MergedCutProfiles.Batch309.profile12367,MergedCutProfiles.Batch309.profile12361]⟩
theorem profilesValid2799 : retention2799.ProfilesValid := by
  change ∀ j : Fin 16, (retention2799.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch441.valid17670
  · exact MergedCutProfiles.Batch441.valid17671
  · exact MergedCutProfiles.Batch441.valid17672
  · exact MergedCutProfiles.Batch441.valid17673
  · exact MergedCutProfiles.Batch005.valid238
  · exact MergedCutProfiles.Batch441.valid17674
  · exact MergedCutProfiles.Batch441.valid17675
  · exact MergedCutProfiles.Batch308.valid12359
  · exact MergedCutProfiles.Batch005.valid239
  · exact MergedCutProfiles.Batch006.valid254
  · exact MergedCutProfiles.Batch441.valid17676
  · exact MergedCutProfiles.Batch309.valid12360
  · exact MergedCutProfiles.Batch309.valid12360
  · exact MergedCutProfiles.Batch006.valid240
  · exact MergedCutProfiles.Batch309.valid12367
  · exact MergedCutProfiles.Batch309.valid12361
theorem numericValid2799 : retention2799.NumericValid := by decide +kernel
def certificate2799 : RatCutBinCertificate := ⟨⟨retention2799,(112469670809740929/62500000000000000),(1970684370264843/1000000000000000000),(7168225569116837359/1000000000000000000),(5439191980260362501551/125000000000000000),(551076591072827411/250000000000000000)⟩,(999958704397371413/1000000000000000000),(591401519902386181/1000000000000000000),(48979428132181003/500000000000000000),(5440211577865827/125000000000000000)⟩
theorem valid2799 : certificate2799.Valid := by decide +kernel
theorem sound2799 : certificate2799.Sound := rat_cut_bin_certificate_sound certificate2799 profilesValid2799 numericValid2799 valid2799

def retention2800 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(12947805970000000/60435757821562209223),(639623708801194803/1000000000000000000),4,(148261165575424273803/64000000000000000000),true,MergedCutProfiles.Batch441.profile17671,![MergedCutProfiles.Batch441.profile17671,MergedCutProfiles.Batch441.profile17673,MergedCutProfiles.Batch441.profile17674,MergedCutProfiles.Batch308.profile12359,MergedCutProfiles.Batch006.profile254,MergedCutProfiles.Batch309.profile12360,MergedCutProfiles.Batch006.profile240,MergedCutProfiles.Batch309.profile12361,MergedCutProfiles.Batch006.profile241,MergedCutProfiles.Batch006.profile255,MergedCutProfiles.Batch309.profile12362,MergedCutProfiles.Batch006.profile242,MergedCutProfiles.Batch006.profile243,MergedCutProfiles.Batch309.profile12364,MergedCutProfiles.Batch006.profile244,MergedCutProfiles.Batch006.profile244]⟩
theorem profilesValid2800 : retention2800.ProfilesValid := by
  change ∀ j : Fin 16, (retention2800.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch441.valid17671
  · exact MergedCutProfiles.Batch441.valid17673
  · exact MergedCutProfiles.Batch441.valid17674
  · exact MergedCutProfiles.Batch308.valid12359
  · exact MergedCutProfiles.Batch006.valid254
  · exact MergedCutProfiles.Batch309.valid12360
  · exact MergedCutProfiles.Batch006.valid240
  · exact MergedCutProfiles.Batch309.valid12361
  · exact MergedCutProfiles.Batch006.valid241
  · exact MergedCutProfiles.Batch006.valid255
  · exact MergedCutProfiles.Batch309.valid12362
  · exact MergedCutProfiles.Batch006.valid242
  · exact MergedCutProfiles.Batch006.valid243
  · exact MergedCutProfiles.Batch309.valid12364
  · exact MergedCutProfiles.Batch006.valid244
  · exact MergedCutProfiles.Batch006.valid244
theorem numericValid2800 : retention2800.NumericValid := by decide +kernel
def certificate2800 : RatCutBinCertificate := ⟨⟨retention2800,(112469670809740929/62500000000000000),(1970684370264843/1000000000000000000),(7168225569116837359/1000000000000000000),(5439191980260362501551/125000000000000000),(2314601825940128283/1000000000000000000)⟩,(999958704397371413/1000000000000000000),(523070266019934271/1000000000000000000),(68979766519387353/500000000000000000),(65102370887913411/1000000000000000000)⟩
theorem valid2800 : certificate2800.Valid := by decide +kernel
theorem sound2800 : certificate2800.Sound := rat_cut_bin_certificate_sound certificate2800 profilesValid2800 numericValid2800 valid2800

def retention2801 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(344041112397696554/1510893945539055230575),(1294780597/1000000000),(49/20),(18833110329230527267/8000000000000000000),true,MergedCutProfiles.Batch441.profile17671,![MergedCutProfiles.Batch441.profile17671,MergedCutProfiles.Batch441.profile17673,MergedCutProfiles.Batch441.profile17675,MergedCutProfiles.Batch005.profile239,MergedCutProfiles.Batch441.profile17676,MergedCutProfiles.Batch309.profile12360,MergedCutProfiles.Batch309.profile12367,MergedCutProfiles.Batch309.profile12361,MergedCutProfiles.Batch006.profile255,MergedCutProfiles.Batch309.profile12362,MergedCutProfiles.Batch006.profile242,MergedCutProfiles.Batch309.profile12363,MergedCutProfiles.Batch006.profile243,MergedCutProfiles.Batch309.profile12364,MergedCutProfiles.Batch006.profile244,MergedCutProfiles.Batch309.profile12365]⟩
theorem profilesValid2801 : retention2801.ProfilesValid := by
  change ∀ j : Fin 16, (retention2801.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch441.valid17671
  · exact MergedCutProfiles.Batch441.valid17673
  · exact MergedCutProfiles.Batch441.valid17675
  · exact MergedCutProfiles.Batch005.valid239
  · exact MergedCutProfiles.Batch441.valid17676
  · exact MergedCutProfiles.Batch309.valid12360
  · exact MergedCutProfiles.Batch309.valid12367
  · exact MergedCutProfiles.Batch309.valid12361
  · exact MergedCutProfiles.Batch006.valid255
  · exact MergedCutProfiles.Batch309.valid12362
  · exact MergedCutProfiles.Batch006.valid242
  · exact MergedCutProfiles.Batch309.valid12363
  · exact MergedCutProfiles.Batch006.valid243
  · exact MergedCutProfiles.Batch309.valid12364
  · exact MergedCutProfiles.Batch006.valid244
  · exact MergedCutProfiles.Batch309.valid12365
theorem numericValid2801 : retention2801.NumericValid := by decide +kernel
def certificate2801 : RatCutBinCertificate := ⟨⟨retention2801,(112469670809740929/62500000000000000),(1970684370264843/1000000000000000000),(7168225569116837359/1000000000000000000),(5439191980260362501551/125000000000000000),(2352926723375242753/1000000000000000000)⟩,(999958704397371413/1000000000000000000),(42721691663999941/125000000000000000),(291288698599300089/1000000000000000000),(42945282622831953/200000000000000000)⟩
theorem valid2801 : certificate2801.Valid := by decide +kernel
theorem sound2801 : certificate2801.Sound := rat_cut_bin_certificate_sound certificate2801 profilesValid2801 numericValid2801 valid2801

def retention2802 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(38577186597746165163/6043575782156220922300),(172020556198848277/125000000000000000),(47/20),(45408289107592270089/20000000000000000000),true,MergedCutProfiles.Batch006.profile250,![MergedCutProfiles.Batch006.profile250,MergedCutProfiles.Batch006.profile269,MergedCutProfiles.Batch441.profile17677,MergedCutProfiles.Batch441.profile17678,MergedCutProfiles.Batch441.profile17679,MergedCutProfiles.Batch442.profile17680,MergedCutProfiles.Batch442.profile17681,MergedCutProfiles.Batch442.profile17682,MergedCutProfiles.Batch442.profile17683,MergedCutProfiles.Batch442.profile17684,MergedCutProfiles.Batch442.profile17685,MergedCutProfiles.Batch442.profile17686,MergedCutProfiles.Batch442.profile17687,MergedCutProfiles.Batch442.profile17688,MergedCutProfiles.Batch442.profile17689,MergedCutProfiles.Batch442.profile17690]⟩
theorem profilesValid2802 : retention2802.ProfilesValid := by
  change ∀ j : Fin 16, (retention2802.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch006.valid250
  · exact MergedCutProfiles.Batch006.valid269
  · exact MergedCutProfiles.Batch441.valid17677
  · exact MergedCutProfiles.Batch441.valid17678
  · exact MergedCutProfiles.Batch441.valid17679
  · exact MergedCutProfiles.Batch442.valid17680
  · exact MergedCutProfiles.Batch442.valid17681
  · exact MergedCutProfiles.Batch442.valid17682
  · exact MergedCutProfiles.Batch442.valid17683
  · exact MergedCutProfiles.Batch442.valid17684
  · exact MergedCutProfiles.Batch442.valid17685
  · exact MergedCutProfiles.Batch442.valid17686
  · exact MergedCutProfiles.Batch442.valid17687
  · exact MergedCutProfiles.Batch442.valid17688
  · exact MergedCutProfiles.Batch442.valid17689
  · exact MergedCutProfiles.Batch442.valid17690
theorem numericValid2802 : retention2802.NumericValid := by decide +kernel
def certificate2802 : RatCutBinCertificate := ⟨⟨retention2802,(112469670809740929/62500000000000000),(1970684370264843/1000000000000000000),(7168225569116837359/1000000000000000000),(5439191980260362501551/125000000000000000),(1134625929877792437/500000000000000000)⟩,(999958704397371413/1000000000000000000),(344032576101914997/1000000000000000000),(288871274734663003/1000000000000000000),(214796157260432487/1000000000000000000)⟩
theorem valid2802 : certificate2802.Valid := by decide +kernel
theorem sound2802 : certificate2802.Sound := rat_cut_bin_certificate_sound certificate2802 profilesValid2802 numericValid2802 valid2802

def retention2803 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(640000000000000000/60435757821562209223),(38577186597746165163/1000000000000000000),1,(86029966116913475596718838002333847353/38577186597746165163000000000000000000),false,MergedCutProfiles.Batch442.profile17691,(fun _ => MergedCutProfiles.Batch442.profile17691)⟩
theorem profilesValid2803 : retention2803.ProfilesValid := by
  exact MergedCutProfiles.Batch442.valid17691
theorem numericValid2803 : retention2803.NumericValid := by decide +kernel
def certificate2803 : RatCutBinCertificate := ⟨⟨retention2803,(112469670809740929/62500000000000000),(1970684370264843/1000000000000000000),(7168225569116837359/1000000000000000000),(5439191980260362501551/125000000000000000),(2229578897206007931/1000000000000000000)⟩,(999958704397371413/1000000000000000000),(188643838216583097/1000000000000000000),(248162889099957591/500000000000000000),(209218398123034479/200000000000000000)⟩
theorem valid2803 : certificate2803.Valid := by decide +kernel
theorem sound2803 : certificate2803.Sound := rat_cut_bin_certificate_sound certificate2803 profilesValid2803 numericValid2803 valid2803

def retention2804 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(1/2),64,1,(255368860549321472084694123425840443671/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch007.profile295,(fun _ => MergedCutProfiles.Batch007.profile295)⟩
theorem profilesValid2804 : retention2804.ProfilesValid := by
  exact MergedCutProfiles.Batch007.valid295
theorem numericValid2804 : retention2804.NumericValid := by decide +kernel
def certificate2804 : RatCutBinCertificate := ⟨⟨retention2804,(112469670809740929/62500000000000000),(1970684370264843/1000000000000000000),(7168225569116837359/1000000000000000000),(5439191980260362501551/125000000000000000),(997039889985225191/1000000000000000000)⟩,(999958704397371413/1000000000000000000),(104134443299328521/250000000000000000),(54666686334806487/250000000000000000),(214666157205387909/1000000000000000000)⟩
theorem valid2804 : certificate2804.Valid := by decide +kernel
theorem sound2804 : certificate2804.Sound := rat_cut_bin_certificate_sound certificate2804 profilesValid2804 numericValid2804 valid2804

def retention2805 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(640000000000000000/60435757821562209223),(7483537804844551507/1000000000000000000),1,(3131332911221521224555997669702586709/1496707560968910301400000000000000000),false,MergedCutProfiles.Batch442.profile17691,(fun _ => MergedCutProfiles.Batch442.profile17691)⟩
theorem profilesValid2805 : retention2805.ProfilesValid := by
  exact MergedCutProfiles.Batch442.valid17691
theorem numericValid2805 : retention2805.NumericValid := by decide +kernel
def certificate2805 : RatCutBinCertificate := ⟨⟨retention2805,(121895918872240929/62500000000000000),(1970684370264843/1000000000000000000),(7168225569116837359/1000000000000000000),(5439191980260362501551/125000000000000000),(2091611267893310431/1000000000000000000)⟩,(999955243352125653/1000000000000000000),(71777569755758617/1000000000000000000),(732383241735494447/1000000000000000000),(1197182339078297457/1000000000000000000)⟩
theorem valid2805 : certificate2805.Valid := by decide +kernel
theorem sound2805 : certificate2805.Sound := rat_cut_bin_certificate_sound certificate2805 profilesValid2805 numericValid2805 valid2805

def retention2806 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(1/2),64,1,(255368860549321472084694123425840443671/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch007.profile295,(fun _ => MergedCutProfiles.Batch007.profile295)⟩
theorem profilesValid2806 : retention2806.ProfilesValid := by
  exact MergedCutProfiles.Batch007.valid295
theorem numericValid2806 : retention2806.NumericValid := by decide +kernel
def certificate2806 : RatCutBinCertificate := ⟨⟨retention2806,(121895918872240929/62500000000000000),(1970684370264843/1000000000000000000),(7168225569116837359/1000000000000000000),(5439191980260362501551/125000000000000000),(249249606661938481/250000000000000000)⟩,(999955243352125653/1000000000000000000),(6023310355180129/40000000000000000),(140834558993502933/250000000000000000),(138251799216201343/250000000000000000)⟩
theorem valid2806 : certificate2806.Valid := by decide +kernel
theorem sound2806 : certificate2806.Sound := rat_cut_bin_certificate_sound certificate2806 profilesValid2806 numericValid2806 valid2806

def retention2807 : RatCutRetentionCertificate := ⟨(7/1000),(3/400),(642002531642094239/5252959943483066461804),(575442095817284289/1000000000000000000),4,(141362029482112737604554042341251451/63938010646364921000000000000000000),true,MergedCutProfiles.Batch442.profile17692,![MergedCutProfiles.Batch442.profile17692,MergedCutProfiles.Batch442.profile17693,MergedCutProfiles.Batch442.profile17694,MergedCutProfiles.Batch442.profile17695,MergedCutProfiles.Batch442.profile17696,MergedCutProfiles.Batch442.profile17697,MergedCutProfiles.Batch442.profile17698,MergedCutProfiles.Batch442.profile17699,MergedCutProfiles.Batch442.profile17699,MergedCutProfiles.Batch442.profile17700,MergedCutProfiles.Batch442.profile17701,MergedCutProfiles.Batch442.profile17702,MergedCutProfiles.Batch442.profile17703,MergedCutProfiles.Batch442.profile17704,MergedCutProfiles.Batch442.profile17704,MergedCutProfiles.Batch442.profile17705]⟩
theorem profilesValid2807 : retention2807.ProfilesValid := by
  change ∀ j : Fin 16, (retention2807.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch442.valid17692
  · exact MergedCutProfiles.Batch442.valid17693
  · exact MergedCutProfiles.Batch442.valid17694
  · exact MergedCutProfiles.Batch442.valid17695
  · exact MergedCutProfiles.Batch442.valid17696
  · exact MergedCutProfiles.Batch442.valid17697
  · exact MergedCutProfiles.Batch442.valid17698
  · exact MergedCutProfiles.Batch442.valid17699
  · exact MergedCutProfiles.Batch442.valid17699
  · exact MergedCutProfiles.Batch442.valid17700
  · exact MergedCutProfiles.Batch442.valid17701
  · exact MergedCutProfiles.Batch442.valid17702
  · exact MergedCutProfiles.Batch442.valid17703
  · exact MergedCutProfiles.Batch442.valid17704
  · exact MergedCutProfiles.Batch442.valid17704
  · exact MergedCutProfiles.Batch442.valid17705
theorem numericValid2807 : retention2807.NumericValid := by decide +kernel
def certificate2807 : RatCutBinCertificate := ⟨⟨retention2807,(180436997786074881/100000000000000000),(90635594743493/40000000000000000),(181371966023790381/25000000000000000),(38194222826487881556691/1000000000000000000),(220866896538016743/100000000000000000)⟩,(199990570226759163/200000000000000000),(73636569998521363/125000000000000000),(12397021731568279/125000000000000000),(5520532581219461/125000000000000000)⟩
theorem valid2807 : certificate2807.Valid := by decide +kernel
theorem sound2807 : certificate2807.Sound := rat_cut_bin_certificate_sound certificate2807 profilesValid2807 numericValid2807 valid2807

def certificates : List RatCutBinCertificate := [certificate2796,certificate2797,certificate2798,certificate2799,certificate2800,certificate2801,certificate2802,certificate2803,certificate2804,certificate2805,certificate2806,certificate2807]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2796,List.forall_mem_cons.mpr ⟨sound2797,List.forall_mem_cons.mpr ⟨sound2798,List.forall_mem_cons.mpr ⟨sound2799,List.forall_mem_cons.mpr ⟨sound2800,List.forall_mem_cons.mpr ⟨sound2801,List.forall_mem_cons.mpr ⟨sound2802,List.forall_mem_cons.mpr ⟨sound2803,List.forall_mem_cons.mpr ⟨sound2804,List.forall_mem_cons.mpr ⟨sound2805,List.forall_mem_cons.mpr ⟨sound2806,List.forall_mem_cons.mpr ⟨sound2807,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch233
