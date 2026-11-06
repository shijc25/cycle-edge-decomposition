import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch350
import Cycle12.MergedCutProfiles.Batch351
import Cycle12.MergedCutProfiles.Batch352
import Cycle12.MergedCutProfiles.Batch472
import Cycle12.MergedCutProfiles.Batch473
import Cycle12.MergedCutProfiles.Batch602

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch331

def retention3972 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(32000000000000000000/333242582177592760029),(624467976704960041/250000000000000000),(33/20),(29873636199904175504277530409849123701/15611699417624001025000000000000000000),false,MergedCutProfiles.Batch602.profile24084,(fun _ => MergedCutProfiles.Batch602.profile24084)⟩
theorem profilesValid3972 : retention3972.ProfilesValid := by
  exact MergedCutProfiles.Batch602.valid24084
theorem numericValid3972 : retention3972.NumericValid := by decide +kernel
def certificate3972 : RatCutBinCertificate := ⟨⟨retention3972,(1869853342491414037/1000000000000000000),(69043717129131353/1000000000000000000),(5506235676800618567/500000000000000000),(7378856415501689003879/1000000000000000000),(947099118840843667/500000000000000000)⟩,(999763125067472501/1000000000000000000),(201851556256236451/500000000000000000),(230106467053092961/1000000000000000000),(103278805644006391/500000000000000000)⟩
theorem valid3972 : certificate3972.Valid := by decide +kernel
theorem sound3972 : certificate3972.Sound := rat_cut_bin_certificate_sound certificate3972 profilesValid3972 numericValid3972 valid3972

def retention3973 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(1/2),64,1,(63845591220989223006162834149049868551/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch350.profile14023,(fun _ => MergedCutProfiles.Batch350.profile14023)⟩
theorem profilesValid3973 : retention3973.ProfilesValid := by
  exact MergedCutProfiles.Batch350.valid14023
theorem numericValid3973 : retention3973.NumericValid := by decide +kernel
def certificate3973 : RatCutBinCertificate := ⟨⟨retention3973,(1869853342491414037/1000000000000000000),(69043717129131353/1000000000000000000),(5506235676800618567/500000000000000000),(7378856415501689003879/1000000000000000000),(123233017629828073/125000000000000000)⟩,(999763125067472501/1000000000000000000),(538375638457324531/1000000000000000000),(128262827059056509/1000000000000000000),(31125411983213577/250000000000000000)⟩
theorem valid3973 : certificate3973.Valid := by decide +kernel
theorem sound3973 : certificate3973.Sound := rat_cut_bin_certificate_sound certificate3973 profilesValid3973 numericValid3973 valid3973

def retention3974 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(32000000000000000000/333242582177592760029),(23405900672940531853/1000000000000000000),1,(176293682184805522292243836666017122211/93623602691762127412000000000000000000),false,MergedCutProfiles.Batch602.profile24084,(fun _ => MergedCutProfiles.Batch602.profile24084)⟩
theorem profilesValid3974 : retention3974.ProfilesValid := by
  exact MergedCutProfiles.Batch602.valid24084
theorem numericValid3974 : retention3974.NumericValid := by decide +kernel
def certificate3974 : RatCutBinCertificate := ⟨⟨retention3974,(1827875452491414037/1000000000000000000),(69043717129131353/1000000000000000000),(5506235676800618567/500000000000000000),(7378856415501689003879/1000000000000000000),(1871544641328123059/1000000000000000000)⟩,(999768442955443569/1000000000000000000),(16046028061464207/500000000000000000),(838195056294110729/1000000000000000000),(1452226637525360137/1000000000000000000)⟩
theorem valid3974 : certificate3974.Valid := by decide +kernel
theorem sound3974 : certificate3974.Sound := rat_cut_bin_certificate_sound certificate3974 profilesValid3974 numericValid3974 valid3974

def retention3975 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(1/2),64,1,(63845591220989223006162834149049868551/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch350.profile14023,(fun _ => MergedCutProfiles.Batch350.profile14023)⟩
theorem profilesValid3975 : retention3975.ProfilesValid := by
  exact MergedCutProfiles.Batch350.valid14023
theorem numericValid3975 : retention3975.NumericValid := by decide +kernel
def certificate3975 : RatCutBinCertificate := ⟨⟨retention3975,(1827875452491414037/1000000000000000000),(69043717129131353/1000000000000000000),(5506235676800618567/500000000000000000),(7378856415501689003879/1000000000000000000),(49306366268847741/50000000000000000)⟩,(999768442955443569/1000000000000000000),(30453326928705173/500000000000000000),(379867653615558867/500000000000000000),(36882731774011179/50000000000000000)⟩
theorem valid3975 : certificate3975.Valid := by decide +kernel
theorem sound3975 : certificate3975.Sound := rat_cut_bin_certificate_sound certificate3975 profilesValid3975 numericValid3975 valid3975

def retention3976 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(605480351859360707/630190216641826303955),(290927358553692631/500000000000000000),4,(57085443706682684691/25600000000000000000),true,MergedCutProfiles.Batch602.profile24085,![MergedCutProfiles.Batch602.profile24085,MergedCutProfiles.Batch602.profile24086,MergedCutProfiles.Batch602.profile24087,MergedCutProfiles.Batch602.profile24088,MergedCutProfiles.Batch602.profile24089,MergedCutProfiles.Batch602.profile24090,MergedCutProfiles.Batch602.profile24091,MergedCutProfiles.Batch602.profile24092,MergedCutProfiles.Batch602.profile24093,MergedCutProfiles.Batch602.profile24094,MergedCutProfiles.Batch602.profile24095,MergedCutProfiles.Batch602.profile24096,MergedCutProfiles.Batch602.profile24097,MergedCutProfiles.Batch472.profile18913,MergedCutProfiles.Batch473.profile18934,MergedCutProfiles.Batch602.profile24098]⟩
theorem profilesValid3976 : retention3976.ProfilesValid := by
  change ∀ j : Fin 16, (retention3976.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch602.valid24085
  · exact MergedCutProfiles.Batch602.valid24086
  · exact MergedCutProfiles.Batch602.valid24087
  · exact MergedCutProfiles.Batch602.valid24088
  · exact MergedCutProfiles.Batch602.valid24089
  · exact MergedCutProfiles.Batch602.valid24090
  · exact MergedCutProfiles.Batch602.valid24091
  · exact MergedCutProfiles.Batch602.valid24092
  · exact MergedCutProfiles.Batch602.valid24093
  · exact MergedCutProfiles.Batch602.valid24094
  · exact MergedCutProfiles.Batch602.valid24095
  · exact MergedCutProfiles.Batch602.valid24096
  · exact MergedCutProfiles.Batch602.valid24097
  · exact MergedCutProfiles.Batch472.valid18913
  · exact MergedCutProfiles.Batch473.valid18934
  · exact MergedCutProfiles.Batch602.valid24098
theorem numericValid3976 : retention3976.NumericValid := by decide +kernel
def certificate3976 : RatCutBinCertificate := ⟨⟨retention3976,(374915395695224577/200000000000000000),(1140020255178431/15625000000000000),(1397573684429472121/125000000000000000),(3541884737025657501189/500000000000000000),(2180968137408071043/1000000000000000000)⟩,(49987681832834077/50000000000000000),(717875038943324847/1000000000000000000),(44178268952364921/1000000000000000000),(4877511577774863/250000000000000000)⟩
theorem valid3976 : certificate3976.Valid := by decide +kernel
theorem sound3976 : certificate3976.Sound := rat_cut_bin_certificate_sound certificate3976 profilesValid3976 numericValid3976 valid3976

def retention3977 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(226159343800000000/126038043328365260791),(605480351859360707/1000000000000000000),4,(274522292699543775497936448528742239/121096070371872141400000000000000000),true,MergedCutProfiles.Batch602.profile24099,![MergedCutProfiles.Batch602.profile24099,MergedCutProfiles.Batch602.profile24100,MergedCutProfiles.Batch602.profile24101,MergedCutProfiles.Batch473.profile18933,MergedCutProfiles.Batch472.profile18912,MergedCutProfiles.Batch602.profile24102,MergedCutProfiles.Batch602.profile24097,MergedCutProfiles.Batch473.profile18934,MergedCutProfiles.Batch351.profile14057,MergedCutProfiles.Batch472.profile18914,MergedCutProfiles.Batch602.profile24103,MergedCutProfiles.Batch473.profile18935,MergedCutProfiles.Batch602.profile24104,MergedCutProfiles.Batch602.profile24105,MergedCutProfiles.Batch472.profile18916,MergedCutProfiles.Batch473.profile18936]⟩
theorem profilesValid3977 : retention3977.ProfilesValid := by
  change ∀ j : Fin 16, (retention3977.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch602.valid24099
  · exact MergedCutProfiles.Batch602.valid24100
  · exact MergedCutProfiles.Batch602.valid24101
  · exact MergedCutProfiles.Batch473.valid18933
  · exact MergedCutProfiles.Batch472.valid18912
  · exact MergedCutProfiles.Batch602.valid24102
  · exact MergedCutProfiles.Batch602.valid24097
  · exact MergedCutProfiles.Batch473.valid18934
  · exact MergedCutProfiles.Batch351.valid14057
  · exact MergedCutProfiles.Batch472.valid18914
  · exact MergedCutProfiles.Batch602.valid24103
  · exact MergedCutProfiles.Batch473.valid18935
  · exact MergedCutProfiles.Batch602.valid24104
  · exact MergedCutProfiles.Batch602.valid24105
  · exact MergedCutProfiles.Batch472.valid18916
  · exact MergedCutProfiles.Batch473.valid18936
theorem numericValid3977 : retention3977.NumericValid := by decide +kernel
def certificate3977 : RatCutBinCertificate := ⟨⟨retention3977,(374915395695224577/200000000000000000),(1140020255178431/15625000000000000),(1397573684429472121/125000000000000000),(3541884737025657501189/500000000000000000),(2218047365932449657/1000000000000000000)⟩,(49987681832834077/50000000000000000),(687526188833025709/1000000000000000000),(54888441210492309/1000000000000000000),(6189656053119511/250000000000000000)⟩
theorem valid3977 : certificate3977.Valid := by decide +kernel
theorem sound3977 : certificate3977.Sound := rat_cut_bin_certificate_sound certificate3977 profilesValid3977 numericValid3977 valid3977

def retention3978 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(1382846830399554474/630190216641826303955),(1130796719/1000000000),(11/4),(666320118211805154201707161594352191/282699179750000000000000000000000000),true,MergedCutProfiles.Batch602.profile24106,![MergedCutProfiles.Batch602.profile24106,MergedCutProfiles.Batch602.profile24107,MergedCutProfiles.Batch602.profile24091,MergedCutProfiles.Batch602.profile24093,MergedCutProfiles.Batch602.profile24102,MergedCutProfiles.Batch602.profile24108,MergedCutProfiles.Batch602.profile24098,MergedCutProfiles.Batch602.profile24109,MergedCutProfiles.Batch602.profile24103,MergedCutProfiles.Batch473.profile18935,MergedCutProfiles.Batch350.profile14027,MergedCutProfiles.Batch472.profile18916,MergedCutProfiles.Batch473.profile18936,MergedCutProfiles.Batch602.profile24110,MergedCutProfiles.Batch602.profile24111,MergedCutProfiles.Batch602.profile24112]⟩
theorem profilesValid3978 : retention3978.ProfilesValid := by
  change ∀ j : Fin 16, (retention3978.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch602.valid24106
  · exact MergedCutProfiles.Batch602.valid24107
  · exact MergedCutProfiles.Batch602.valid24091
  · exact MergedCutProfiles.Batch602.valid24093
  · exact MergedCutProfiles.Batch602.valid24102
  · exact MergedCutProfiles.Batch602.valid24108
  · exact MergedCutProfiles.Batch602.valid24098
  · exact MergedCutProfiles.Batch602.valid24109
  · exact MergedCutProfiles.Batch602.valid24103
  · exact MergedCutProfiles.Batch473.valid18935
  · exact MergedCutProfiles.Batch350.valid14027
  · exact MergedCutProfiles.Batch472.valid18916
  · exact MergedCutProfiles.Batch473.valid18936
  · exact MergedCutProfiles.Batch602.valid24110
  · exact MergedCutProfiles.Batch602.valid24111
  · exact MergedCutProfiles.Batch602.valid24112
theorem numericValid3978 : retention3978.NumericValid := by decide +kernel
def certificate3978 : RatCutBinCertificate := ⟨⟨retention3978,(374915395695224577/200000000000000000),(1140020255178431/15625000000000000),(1397573684429472121/125000000000000000),(3541884737025657501189/500000000000000000),(290419092970811739/125000000000000000)⟩,(49987681832834077/50000000000000000),(455956718741196867/1000000000000000000),(185954073745103211/1000000000000000000),(24701029247324399/200000000000000000)⟩
theorem valid3978 : certificate3978.Valid := by decide +kernel
theorem sound3978 : certificate3978.Sound := rat_cut_bin_certificate_sound certificate3978 profilesValid3978 numericValid3978 valid3978

def retention3979 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(27638062027258367802/630190216641826303955),(691423415199777237/500000000000000000),(12/5),(757850400898505074921345158855575109/360116362083217310937500000000000000),false,MergedCutProfiles.Batch602.profile24113,(fun _ => MergedCutProfiles.Batch602.profile24113)⟩
theorem profilesValid3979 : retention3979.ProfilesValid := by
  exact MergedCutProfiles.Batch602.valid24113
theorem numericValid3979 : retention3979.NumericValid := by decide +kernel
def certificate3979 : RatCutBinCertificate := ⟨⟨retention3979,(374915395695224577/200000000000000000),(1140020255178431/15625000000000000),(1397573684429472121/125000000000000000),(3541884737025657501189/500000000000000000),(1037550308265995541/500000000000000000)⟩,(49987681832834077/50000000000000000),(362004197454603/781250000000000),(180195549326068471/1000000000000000000),(123566056357675007/1000000000000000000)⟩
theorem valid3979 : certificate3979.Valid := by decide +kernel
theorem sound3979 : certificate3979.Sound := rat_cut_bin_certificate_sound certificate3979 profilesValid3979 numericValid3979 valid3979

def retention3980 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(12800000000000000000/126038043328365260791),(13819031013629183901/500000000000000000),1,(12944306460285010175660497044265504901/6909515506814591950500000000000000000),false,MergedCutProfiles.Batch602.profile24114,(fun _ => MergedCutProfiles.Batch602.profile24114)⟩
theorem profilesValid3980 : retention3980.ProfilesValid := by
  exact MergedCutProfiles.Batch602.valid24114
theorem numericValid3980 : retention3980.NumericValid := by decide +kernel
def certificate3980 : RatCutBinCertificate := ⟨⟨retention3980,(374915395695224577/200000000000000000),(1140020255178431/15625000000000000),(1397573684429472121/125000000000000000),(3541884737025657501189/500000000000000000),(3635097574577579/1953125000000000)⟩,(49987681832834077/50000000000000000),(292630297128410059/1000000000000000000),(6954886976539719/20000000000000000),(121244975631315749/200000000000000000)⟩
theorem valid3980 : certificate3980.Valid := by decide +kernel
theorem sound3980 : certificate3980.Sound := rat_cut_bin_certificate_sound certificate3980 profilesValid3980 numericValid3980 valid3980

def retention3981 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(1/2),64,1,(255383218571243657304565787478649566351/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch352.profile14113,(fun _ => MergedCutProfiles.Batch352.profile14113)⟩
theorem profilesValid3981 : retention3981.ProfilesValid := by
  exact MergedCutProfiles.Batch352.valid14113
theorem numericValid3981 : retention3981.NumericValid := by decide +kernel
def certificate3981 : RatCutBinCertificate := ⟨⟨retention3981,(374915395695224577/200000000000000000),(1140020255178431/15625000000000000),(1397573684429472121/125000000000000000),(3541884737025657501189/500000000000000000),(15396214810390357/15625000000000000)⟩,(49987681832834077/50000000000000000),(540067180720473793/1000000000000000000),(508872326231371/4000000000000000),(4936955461336509/40000000000000000)⟩
theorem valid3981 : certificate3981.Valid := by decide +kernel
theorem sound3981 : certificate3981.Sound := rat_cut_bin_certificate_sound certificate3981 profilesValid3981 numericValid3981 valid3981

def retention3982 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(12800000000000000000/126038043328365260791),(2366603828322453309/100000000000000000),1,(11051365921151612597583705511651161149/5916509570806133272500000000000000000),false,MergedCutProfiles.Batch602.profile24114,(fun _ => MergedCutProfiles.Batch602.profile24114)⟩
theorem profilesValid3982 : retention3982.ProfilesValid := by
  exact MergedCutProfiles.Batch602.valid24114
theorem numericValid3982 : retention3982.NumericValid := by decide +kernel
def certificate3982 : RatCutBinCertificate := ⟨⟨retention3982,(366019883695224577/200000000000000000),(1140020255178431/15625000000000000),(1397573684429472121/125000000000000000),(3541884737025657501189/500000000000000000),(1855943383527920469/1000000000000000000)⟩,(499879741077305101/500000000000000000),(32080556798207609/1000000000000000000),(838228246988232127/1000000000000000000),(1442218757528293703/1000000000000000000)⟩
theorem valid3982 : certificate3982.Valid := by decide +kernel
theorem sound3982 : certificate3982.Sound := rat_cut_bin_certificate_sound certificate3982 profilesValid3982 numericValid3982 valid3982

def retention3983 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(1/2),64,1,(255383218571243657304565787478649566351/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch352.profile14113,(fun _ => MergedCutProfiles.Batch352.profile14113)⟩
theorem profilesValid3983 : retention3983.ProfilesValid := by
  exact MergedCutProfiles.Batch352.valid14113
theorem numericValid3983 : retention3983.NumericValid := by decide +kernel
def certificate3983 : RatCutBinCertificate := ⟨⟨retention3983,(366019883695224577/200000000000000000),(1140020255178431/15625000000000000),(1397573684429472121/125000000000000000),(3541884737025657501189/500000000000000000),(492823997808322929/500000000000000000)⟩,(499879741077305101/500000000000000000),(60406653688039559/1000000000000000000),(761021236242444489/1000000000000000000),(46158923932189457/62500000000000000)⟩
theorem valid3983 : certificate3983.Valid := by decide +kernel
theorem sound3983 : certificate3983.Sound := rat_cut_bin_certificate_sound certificate3983 profilesValid3983 numericValid3983 valid3983

def certificates : List RatCutBinCertificate := [certificate3972,certificate3973,certificate3974,certificate3975,certificate3976,certificate3977,certificate3978,certificate3979,certificate3980,certificate3981,certificate3982,certificate3983]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3972,List.forall_mem_cons.mpr ⟨sound3973,List.forall_mem_cons.mpr ⟨sound3974,List.forall_mem_cons.mpr ⟨sound3975,List.forall_mem_cons.mpr ⟨sound3976,List.forall_mem_cons.mpr ⟨sound3977,List.forall_mem_cons.mpr ⟨sound3978,List.forall_mem_cons.mpr ⟨sound3979,List.forall_mem_cons.mpr ⟨sound3980,List.forall_mem_cons.mpr ⟨sound3981,List.forall_mem_cons.mpr ⟨sound3982,List.forall_mem_cons.mpr ⟨sound3983,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch331
