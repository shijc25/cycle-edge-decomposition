import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch046
import Cycle12.MergedCutProfiles.Batch047
import Cycle12.MergedCutProfiles.Batch048
import Cycle12.MergedCutProfiles.Batch049
import Cycle12.MergedCutProfiles.Batch335
import Cycle12.MergedCutProfiles.Batch336
import Cycle12.MergedCutProfiles.Batch337
import Cycle12.MergedCutProfiles.Batch338
import Cycle12.MergedCutProfiles.Batch464
import Cycle12.MergedCutProfiles.Batch465

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch250

def retention3000 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1/2),64,1,(63844131674568793248260656909441386031/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch046.profile1873,(fun _ => MergedCutProfiles.Batch046.profile1873)⟩
theorem profilesValid3000 : retention3000.ProfilesValid := by
  exact MergedCutProfiles.Batch046.valid1873
theorem numericValid3000 : retention3000.NumericValid := by decide +kernel
def certificate3000 : RatCutBinCertificate := ⟨⟨retention3000,(2072237844186087073/1000000000000000000),(42146381475855499/1000000000000000000),(4898394465934615747/500000000000000000),(2707362291713132118157/1000000000000000000),(30895301940045919/31250000000000000)⟩,(199852931618237433/200000000000000000),(133809075304862151/1000000000000000000),(297785877552620177/500000000000000000),(579424600009210241/1000000000000000000)⟩
theorem valid3000 : certificate3000.Valid := by decide +kernel
theorem sound3000 : certificate3000.Sound := rat_cut_bin_certificate_sound certificate3000 profilesValid3000 numericValid3000 valid3000

def retention3001 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(655870518745967157/256722563520525037319),(642947278449139453/1000000000000000000),4,(589991140868135937797/256000000000000000000),true,MergedCutProfiles.Batch464.profile18578,![MergedCutProfiles.Batch464.profile18578,MergedCutProfiles.Batch464.profile18579,MergedCutProfiles.Batch464.profile18580,MergedCutProfiles.Batch464.profile18581,MergedCutProfiles.Batch464.profile18582,MergedCutProfiles.Batch464.profile18583,MergedCutProfiles.Batch335.profile13430,MergedCutProfiles.Batch335.profile13415,MergedCutProfiles.Batch464.profile18584,MergedCutProfiles.Batch464.profile18585,MergedCutProfiles.Batch335.profile13416,MergedCutProfiles.Batch464.profile18586,MergedCutProfiles.Batch464.profile18587,MergedCutProfiles.Batch335.profile13432,MergedCutProfiles.Batch464.profile18588,MergedCutProfiles.Batch464.profile18589]⟩
theorem profilesValid3001 : retention3001.ProfilesValid := by
  change ∀ j : Fin 16, (retention3001.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch464.valid18578
  · exact MergedCutProfiles.Batch464.valid18579
  · exact MergedCutProfiles.Batch464.valid18580
  · exact MergedCutProfiles.Batch464.valid18581
  · exact MergedCutProfiles.Batch464.valid18582
  · exact MergedCutProfiles.Batch464.valid18583
  · exact MergedCutProfiles.Batch335.valid13430
  · exact MergedCutProfiles.Batch335.valid13415
  · exact MergedCutProfiles.Batch464.valid18584
  · exact MergedCutProfiles.Batch464.valid18585
  · exact MergedCutProfiles.Batch335.valid13416
  · exact MergedCutProfiles.Batch464.valid18586
  · exact MergedCutProfiles.Batch464.valid18587
  · exact MergedCutProfiles.Batch335.valid13432
  · exact MergedCutProfiles.Batch464.valid18588
  · exact MergedCutProfiles.Batch464.valid18589
theorem numericValid3001 : retention3001.NumericValid := by decide +kernel
def certificate3001 : RatCutBinCertificate := ⟨⟨retention3001,(963976888793768213/500000000000000000),(9018985876591161/200000000000000000),(1987432000980355189/200000000000000000),(2564153043510182492643/1000000000000000000),(1134828181117297199/500000000000000000)⟩,(999279779281483477/1000000000000000000),(269180743188645259/500000000000000000),(128271590188661127/1000000000000000000),(59576803386314653/1000000000000000000)⟩
theorem valid3001 : certificate3001.Valid := by decide +kernel
theorem sound3001 : certificate3001.Sound := rat_cut_bin_certificate_sound certificate3001 profilesValid3001 numericValid3001 valid3001

def retention3002 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1160389425000000000/256722563520525037319),(655870518745967157/1000000000000000000),4,(7359238750944884577/3200000000000000000),true,MergedCutProfiles.Batch464.profile18590,![MergedCutProfiles.Batch464.profile18590,MergedCutProfiles.Batch335.profile13429,MergedCutProfiles.Batch464.profile18591,MergedCutProfiles.Batch335.profile13430,MergedCutProfiles.Batch048.profile1929,MergedCutProfiles.Batch464.profile18592,MergedCutProfiles.Batch464.profile18593,MergedCutProfiles.Batch464.profile18594,MergedCutProfiles.Batch464.profile18589,MergedCutProfiles.Batch335.profile13433,MergedCutProfiles.Batch464.profile18595,MergedCutProfiles.Batch336.profile13445,MergedCutProfiles.Batch047.profile1909,MergedCutProfiles.Batch335.profile13435,MergedCutProfiles.Batch047.profile1895,MergedCutProfiles.Batch047.profile1880]⟩
theorem profilesValid3002 : retention3002.ProfilesValid := by
  change ∀ j : Fin 16, (retention3002.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch464.valid18590
  · exact MergedCutProfiles.Batch335.valid13429
  · exact MergedCutProfiles.Batch464.valid18591
  · exact MergedCutProfiles.Batch335.valid13430
  · exact MergedCutProfiles.Batch048.valid1929
  · exact MergedCutProfiles.Batch464.valid18592
  · exact MergedCutProfiles.Batch464.valid18593
  · exact MergedCutProfiles.Batch464.valid18594
  · exact MergedCutProfiles.Batch464.valid18589
  · exact MergedCutProfiles.Batch335.valid13433
  · exact MergedCutProfiles.Batch464.valid18595
  · exact MergedCutProfiles.Batch336.valid13445
  · exact MergedCutProfiles.Batch047.valid1909
  · exact MergedCutProfiles.Batch335.valid13435
  · exact MergedCutProfiles.Batch047.valid1895
  · exact MergedCutProfiles.Batch047.valid1880
theorem numericValid3002 : retention3002.NumericValid := by decide +kernel
def certificate3002 : RatCutBinCertificate := ⟨⟨retention3002,(963976888793768213/500000000000000000),(9018985876591161/200000000000000000),(1987432000980355189/200000000000000000),(2564153043510182492643/1000000000000000000),(2264765582604171527/1000000000000000000)⟩,(999279779281483477/1000000000000000000),(266462791839673399/500000000000000000),(26333034146774761/200000000000000000),(61262909282729129/1000000000000000000)⟩
theorem valid3002 : certificate3002.Valid := by decide +kernel
theorem sound3002 : certificate3002.Sound := rat_cut_bin_certificate_sound certificate3002 profilesValid3002 numericValid3002 valid3002

def retention3003 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1191517806091315851/256722563520525037319),(46415577/40000000),(51/20),(4576364944587400679/2000000000000000000),true,MergedCutProfiles.Batch464.profile18590,![MergedCutProfiles.Batch464.profile18590,MergedCutProfiles.Batch464.profile18596,MergedCutProfiles.Batch335.profile13414,MergedCutProfiles.Batch464.profile18597,MergedCutProfiles.Batch464.profile18584,MergedCutProfiles.Batch335.profile13416,MergedCutProfiles.Batch336.profile13444,MergedCutProfiles.Batch464.profile18598,MergedCutProfiles.Batch335.profile13418,MergedCutProfiles.Batch464.profile18599,MergedCutProfiles.Batch047.profile1894,MergedCutProfiles.Batch335.profile13420,MergedCutProfiles.Batch465.profile18600,MergedCutProfiles.Batch465.profile18601,MergedCutProfiles.Batch465.profile18602,MergedCutProfiles.Batch465.profile18603]⟩
theorem profilesValid3003 : retention3003.ProfilesValid := by
  change ∀ j : Fin 16, (retention3003.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch464.valid18590
  · exact MergedCutProfiles.Batch464.valid18596
  · exact MergedCutProfiles.Batch335.valid13414
  · exact MergedCutProfiles.Batch464.valid18597
  · exact MergedCutProfiles.Batch464.valid18584
  · exact MergedCutProfiles.Batch335.valid13416
  · exact MergedCutProfiles.Batch336.valid13444
  · exact MergedCutProfiles.Batch464.valid18598
  · exact MergedCutProfiles.Batch335.valid13418
  · exact MergedCutProfiles.Batch464.valid18599
  · exact MergedCutProfiles.Batch047.valid1894
  · exact MergedCutProfiles.Batch335.valid13420
  · exact MergedCutProfiles.Batch465.valid18600
  · exact MergedCutProfiles.Batch465.valid18601
  · exact MergedCutProfiles.Batch465.valid18602
  · exact MergedCutProfiles.Batch465.valid18603
theorem numericValid3003 : retention3003.NumericValid := by decide +kernel
def certificate3003 : RatCutBinCertificate := ⟨⟨retention3003,(963976888793768213/500000000000000000),(9018985876591161/200000000000000000),(1987432000980355189/200000000000000000),(2564153043510182492643/1000000000000000000),(453174440649380689/200000000000000000)⟩,(999279779281483477/1000000000000000000),(97500638885413887/250000000000000000),(242768447387420403/1000000000000000000),(165762354963247393/1000000000000000000)⟩
theorem valid3003 : certificate3003.Valid := by decide +kernel
theorem sound3003 : certificate3003.Sound := rat_cut_bin_certificate_sound certificate3003 profilesValid3003 numericValid3003 valid3003

def retention3004 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(2320772556810957867/256722563520525037319),(1191517806091315851/1000000000000000000),(5/2),(576691668879547599211/256000000000000000000),true,MergedCutProfiles.Batch335.profile13429,![MergedCutProfiles.Batch335.profile13429,MergedCutProfiles.Batch335.profile13430,MergedCutProfiles.Batch464.profile18592,MergedCutProfiles.Batch464.profile18594,MergedCutProfiles.Batch335.profile13433,MergedCutProfiles.Batch336.profile13445,MergedCutProfiles.Batch335.profile13435,MergedCutProfiles.Batch047.profile1880,MergedCutProfiles.Batch465.profile18604,MergedCutProfiles.Batch335.profile13425,MergedCutProfiles.Batch465.profile18605,MergedCutProfiles.Batch465.profile18606,MergedCutProfiles.Batch047.profile1912,MergedCutProfiles.Batch465.profile18607,MergedCutProfiles.Batch047.profile1899,MergedCutProfiles.Batch047.profile1885]⟩
theorem profilesValid3004 : retention3004.ProfilesValid := by
  change ∀ j : Fin 16, (retention3004.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch335.valid13429
  · exact MergedCutProfiles.Batch335.valid13430
  · exact MergedCutProfiles.Batch464.valid18592
  · exact MergedCutProfiles.Batch464.valid18594
  · exact MergedCutProfiles.Batch335.valid13433
  · exact MergedCutProfiles.Batch336.valid13445
  · exact MergedCutProfiles.Batch335.valid13435
  · exact MergedCutProfiles.Batch047.valid1880
  · exact MergedCutProfiles.Batch465.valid18604
  · exact MergedCutProfiles.Batch335.valid13425
  · exact MergedCutProfiles.Batch465.valid18605
  · exact MergedCutProfiles.Batch465.valid18606
  · exact MergedCutProfiles.Batch047.valid1912
  · exact MergedCutProfiles.Batch465.valid18607
  · exact MergedCutProfiles.Batch047.valid1899
  · exact MergedCutProfiles.Batch047.valid1885
theorem numericValid3004 : retention3004.NumericValid := by decide +kernel
def certificate3004 : RatCutBinCertificate := ⟨⟨retention3004,(963976888793768213/500000000000000000),(9018985876591161/200000000000000000),(1987432000980355189/200000000000000000),(2564153043510182492643/1000000000000000000),(2230829019633925129/1000000000000000000)⟩,(999279779281483477/1000000000000000000),(391207685742690437/1000000000000000000),(241635618693883623/1000000000000000000),(16577987142020207/100000000000000000)⟩
theorem valid3004 : certificate3004.Valid := by decide +kernel
theorem sound3004 : certificate3004.Sound := rat_cut_bin_certificate_sound certificate3004 profilesValid3004 numericValid3004 valid3004

def retention3005 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(53850122501921755484/256722563520525037319),(2320772556810957867/1000000000000000000),(33/20),(666967330352705916755978339003932440951/412581787877503620800000000000000000000),false,MergedCutProfiles.Batch465.profile18608,(fun _ => MergedCutProfiles.Batch465.profile18608)⟩
theorem profilesValid3005 : retention3005.ProfilesValid := by
  exact MergedCutProfiles.Batch465.valid18608
theorem numericValid3005 : retention3005.NumericValid := by decide +kernel
def certificate3005 : RatCutBinCertificate := ⟨⟨retention3005,(963976888793768213/500000000000000000),(9018985876591161/200000000000000000),(1987432000980355189/200000000000000000),(2564153043510182492643/1000000000000000000),(1602133937665337379/1000000000000000000)⟩,(999279779281483477/1000000000000000000),(420427832876303959/1000000000000000000),(4305562337488237/20000000000000000),(41653958842845193/250000000000000000)⟩
theorem valid3005 : certificate3005.Valid := by decide +kernel
theorem sound3005 : certificate3005.Sound := rat_cut_bin_certificate_sound certificate3005 profilesValid3005 numericValid3005 valid3005

def retention3006 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(64000000000000000000/256722563520525037319),(13462530625480438871/250000000000000000),1,(65304528124901269750509452803048392867/43080098001537404387200000000000000000),false,MergedCutProfiles.Batch465.profile18609,(fun _ => MergedCutProfiles.Batch465.profile18609)⟩
theorem profilesValid3006 : retention3006.ProfilesValid := by
  exact MergedCutProfiles.Batch465.valid18609
theorem numericValid3006 : retention3006.NumericValid := by decide +kernel
def certificate3006 : RatCutBinCertificate := ⟨⟨retention3006,(963976888793768213/500000000000000000),(9018985876591161/200000000000000000),(1987432000980355189/200000000000000000),(2564153043510182492643/1000000000000000000),(150713717206971457/100000000000000000)⟩,(999279779281483477/1000000000000000000),(15676132109526669/50000000000000000),(161405787566834301/500000000000000000),(472931119711726153/1000000000000000000)⟩
theorem valid3006 : certificate3006.Valid := by decide +kernel
theorem sound3006 : certificate3006.Sound := rat_cut_bin_certificate_sound certificate3006 profilesValid3006 numericValid3006 valid3006

def retention3007 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1/2),64,1,(255377162141591932400424606355354448199/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch049.profile1962,(fun _ => MergedCutProfiles.Batch049.profile1962)⟩
theorem profilesValid3007 : retention3007.ProfilesValid := by
  exact MergedCutProfiles.Batch049.valid1962
theorem numericValid3007 : retention3007.NumericValid := by decide +kernel
def certificate3007 : RatCutBinCertificate := ⟨⟨retention3007,(963976888793768213/500000000000000000),(9018985876591161/200000000000000000),(1987432000980355189/200000000000000000),(2564153043510182492643/1000000000000000000),(494408982047426301/500000000000000000)⟩,(999279779281483477/1000000000000000000),(23820639682499241/50000000000000000),(42585254291888691/250000000000000000),(82876480219151023/500000000000000000)⟩
theorem valid3007 : certificate3007.Valid := by decide +kernel
theorem sound3007 : certificate3007.Sound := rat_cut_bin_certificate_sound certificate3007 profilesValid3007 numericValid3007 valid3007

def retention3008 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(64000000000000000000/256722563520525037319),(9558409571558448327/1000000000000000000),1,(56040735402842435676022144121602819907/38233638286233793308000000000000000000),false,MergedCutProfiles.Batch465.profile18609,(fun _ => MergedCutProfiles.Batch465.profile18609)⟩
theorem profilesValid3008 : retention3008.ProfilesValid := by
  exact MergedCutProfiles.Batch465.valid18609
theorem numericValid3008 : retention3008.NumericValid := by decide +kernel
def certificate3008 : RatCutBinCertificate := ⟨⟨retention3008,(1038258171793768213/500000000000000000),(9018985876591161/200000000000000000),(1987432000980355189/200000000000000000),(2564153043510182492643/1000000000000000000),(145632097928903699/100000000000000000)⟩,(999224279252718241/1000000000000000000),(5613609294370657/62500000000000000),(34470213219378707/50000000000000000),(217635498399279483/250000000000000000)⟩
theorem valid3008 : certificate3008.Valid := by decide +kernel
theorem sound3008 : certificate3008.Sound := rat_cut_bin_certificate_sound certificate3008 profilesValid3008 numericValid3008 valid3008

def retention3009 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1/2),64,1,(255377162141591932400424606355354448199/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch049.profile1962,(fun _ => MergedCutProfiles.Batch049.profile1962)⟩
theorem profilesValid3009 : retention3009.ProfilesValid := by
  exact MergedCutProfiles.Batch049.valid1962
theorem numericValid3009 : retention3009.NumericValid := by decide +kernel
def certificate3009 : RatCutBinCertificate := ⟨⟨retention3009,(1038258171793768213/500000000000000000),(9018985876591161/200000000000000000),(1987432000980355189/200000000000000000),(2564153043510182492643/1000000000000000000),(19762875710614389/20000000000000000)⟩,(999224279252718241/1000000000000000000),(66186456705048123/500000000000000000),(74801969632537121/125000000000000000),(145468602459324751/250000000000000000)⟩
theorem valid3009 : certificate3009.Valid := by decide +kernel
theorem sound3009 : certificate3009.Sound := rat_cut_bin_certificate_sound certificate3009 profilesValid3009 numericValid3009 valid3009

def retention3010 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(218047155842275192/80054158363377277325),(647664819333490669/1000000000000000000),4,(118208650841971348337/51200000000000000000),true,MergedCutProfiles.Batch465.profile18610,![MergedCutProfiles.Batch465.profile18610,MergedCutProfiles.Batch465.profile18611,MergedCutProfiles.Batch465.profile18612,MergedCutProfiles.Batch465.profile18613,MergedCutProfiles.Batch465.profile18614,MergedCutProfiles.Batch465.profile18615,MergedCutProfiles.Batch337.profile13493,MergedCutProfiles.Batch465.profile18616,MergedCutProfiles.Batch465.profile18617,MergedCutProfiles.Batch465.profile18618,MergedCutProfiles.Batch336.profile13479,MergedCutProfiles.Batch465.profile18619,MergedCutProfiles.Batch338.profile13524,MergedCutProfiles.Batch337.profile13495,MergedCutProfiles.Batch338.profile13536,MergedCutProfiles.Batch465.profile18620]⟩
theorem profilesValid3010 : retention3010.ProfilesValid := by
  change ∀ j : Fin 16, (retention3010.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch465.valid18610
  · exact MergedCutProfiles.Batch465.valid18611
  · exact MergedCutProfiles.Batch465.valid18612
  · exact MergedCutProfiles.Batch465.valid18613
  · exact MergedCutProfiles.Batch465.valid18614
  · exact MergedCutProfiles.Batch465.valid18615
  · exact MergedCutProfiles.Batch337.valid13493
  · exact MergedCutProfiles.Batch465.valid18616
  · exact MergedCutProfiles.Batch465.valid18617
  · exact MergedCutProfiles.Batch465.valid18618
  · exact MergedCutProfiles.Batch336.valid13479
  · exact MergedCutProfiles.Batch465.valid18619
  · exact MergedCutProfiles.Batch338.valid13524
  · exact MergedCutProfiles.Batch337.valid13495
  · exact MergedCutProfiles.Batch338.valid13536
  · exact MergedCutProfiles.Batch465.valid18620
theorem numericValid3010 : retention3010.NumericValid := by decide +kernel
def certificate3010 : RatCutBinCertificate := ⟨⟨retention3010,(77333771313074839/40000000000000000),(481579510880593/10000000000000000),(10080644210854032517/1000000000000000000),(2433461079447895543817/1000000000000000000),(1135909002586123273/500000000000000000)⟩,(249810329147249703/250000000000000000),(534587928579897673/1000000000000000000),(130621525829264337/1000000000000000000),(60792946403062567/1000000000000000000)⟩
theorem valid3010 : certificate3010.Valid := by decide +kernel
theorem sound3010 : certificate3010.Sound := rat_cut_bin_certificate_sound certificate3010 profilesValid3010 numericValid3010 valid3010

def retention3011 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(1153426663130340668/240162475090131831975),(81767683440853197/125000000000000000),4,(9189939085290193107/4000000000000000000),true,MergedCutProfiles.Batch465.profile18621,![MergedCutProfiles.Batch465.profile18621,MergedCutProfiles.Batch465.profile18622,MergedCutProfiles.Batch465.profile18623,MergedCutProfiles.Batch337.profile13493,MergedCutProfiles.Batch338.profile13523,MergedCutProfiles.Batch337.profile13494,MergedCutProfiles.Batch465.profile18624,MergedCutProfiles.Batch465.profile18625,MergedCutProfiles.Batch465.profile18620,MergedCutProfiles.Batch465.profile18626,MergedCutProfiles.Batch337.profile13482,MergedCutProfiles.Batch337.profile13497,MergedCutProfiles.Batch338.profile13537,MergedCutProfiles.Batch337.profile13484,MergedCutProfiles.Batch465.profile18627,MergedCutProfiles.Batch465.profile18628]⟩
theorem profilesValid3011 : retention3011.ProfilesValid := by
  change ∀ j : Fin 16, (retention3011.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch465.valid18621
  · exact MergedCutProfiles.Batch465.valid18622
  · exact MergedCutProfiles.Batch465.valid18623
  · exact MergedCutProfiles.Batch337.valid13493
  · exact MergedCutProfiles.Batch338.valid13523
  · exact MergedCutProfiles.Batch337.valid13494
  · exact MergedCutProfiles.Batch465.valid18624
  · exact MergedCutProfiles.Batch465.valid18625
  · exact MergedCutProfiles.Batch465.valid18620
  · exact MergedCutProfiles.Batch465.valid18626
  · exact MergedCutProfiles.Batch337.valid13482
  · exact MergedCutProfiles.Batch337.valid13497
  · exact MergedCutProfiles.Batch338.valid13537
  · exact MergedCutProfiles.Batch337.valid13484
  · exact MergedCutProfiles.Batch465.valid18627
  · exact MergedCutProfiles.Batch465.valid18628
theorem numericValid3011 : retention3011.NumericValid := by decide +kernel
def certificate3011 : RatCutBinCertificate := ⟨⟨retention3011,(77333771313074839/40000000000000000),(481579510880593/10000000000000000),(10080644210854032517/1000000000000000000),(2433461079447895543817/1000000000000000000),(2260540067531763417/1000000000000000000)⟩,(249810329147249703/250000000000000000),(21358926580824577/40000000000000000),(65503440335426291/500000000000000000),(12166346858551227/200000000000000000)⟩
theorem valid3011 : certificate3011.Valid := by decide +kernel
theorem sound3011 : certificate3011.Sound := rat_cut_bin_certificate_sound certificate3011 profilesValid3011 numericValid3011 valid3011

def certificates : List RatCutBinCertificate := [certificate3000,certificate3001,certificate3002,certificate3003,certificate3004,certificate3005,certificate3006,certificate3007,certificate3008,certificate3009,certificate3010,certificate3011]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3000,List.forall_mem_cons.mpr ⟨sound3001,List.forall_mem_cons.mpr ⟨sound3002,List.forall_mem_cons.mpr ⟨sound3003,List.forall_mem_cons.mpr ⟨sound3004,List.forall_mem_cons.mpr ⟨sound3005,List.forall_mem_cons.mpr ⟨sound3006,List.forall_mem_cons.mpr ⟨sound3007,List.forall_mem_cons.mpr ⟨sound3008,List.forall_mem_cons.mpr ⟨sound3009,List.forall_mem_cons.mpr ⟨sound3010,List.forall_mem_cons.mpr ⟨sound3011,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch250
