import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch011
import Cycle12.MergedCutProfiles.Batch012
import Cycle12.MergedCutProfiles.Batch312
import Cycle12.MergedCutProfiles.Batch446
import Cycle12.MergedCutProfiles.Batch447

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch236

def retention2832 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(1/2),64,1,(62345958716102427160851921466530999/62500000000000000000000000000000000),false,MergedCutProfiles.Batch011.profile461,(fun _ => MergedCutProfiles.Batch011.profile461)⟩
theorem profilesValid2832 : retention2832.ProfilesValid := by
  exact MergedCutProfiles.Batch011.valid461
theorem numericValid2832 : retention2832.NumericValid := by decide +kernel
def certificate2832 : RatCutBinCertificate := ⟨⟨retention2832,(1813578092676477869/1000000000000000000),(4061079806220747/1000000000000000000),(1858279164791913287/250000000000000000),(10908395511668070660349/500000000000000000),(996544491913020997/1000000000000000000)⟩,(499958572451413639/500000000000000000),(212852290394574059/500000000000000000),(26342374137671987/125000000000000000),(206773560932939839/1000000000000000000)⟩
theorem valid2832 : certificate2832.Valid := by decide +kernel
theorem sound2832 : certificate2832.Sound := rat_cut_bin_certificate_sound certificate2832 profilesValid2832 numericValid2832 valid2832

def retention2833 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(32000000000000000000/1460960179092951431811),(7732962793596426583/1000000000000000000),1,(15737427176158678794402237237270088593/7732962793596426583000000000000000000),false,MergedCutProfiles.Batch446.profile17841,(fun _ => MergedCutProfiles.Batch446.profile17841)⟩
theorem profilesValid2833 : retention2833.ProfilesValid := by
  exact MergedCutProfiles.Batch446.valid17841
theorem numericValid2833 : retention2833.NumericValid := by decide +kernel
def certificate2833 : RatCutBinCertificate := ⟨⟨retention2833,(1964012227676477869/1000000000000000000),(4061079806220747/1000000000000000000),(1858279164791913287/250000000000000000),(10908395511668070660349/500000000000000000),(1017018304584514719/500000000000000000)⟩,(124988784021190717/125000000000000000),(36237033730025703/500000000000000000),(730669356151049849/1000000000000000000),(18384144618015361/15625000000000000)⟩
theorem valid2833 : certificate2833.Valid := by decide +kernel
theorem sound2833 : certificate2833.Sound := rat_cut_bin_certificate_sound certificate2833 profilesValid2833 numericValid2833 valid2833

def retention2834 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(1/2),64,1,(62345958716102427160851921466530999/62500000000000000000000000000000000),false,MergedCutProfiles.Batch011.profile461,(fun _ => MergedCutProfiles.Batch011.profile461)⟩
theorem profilesValid2834 : retention2834.ProfilesValid := by
  exact MergedCutProfiles.Batch011.valid461
theorem numericValid2834 : retention2834.NumericValid := by decide +kernel
def certificate2834 : RatCutBinCertificate := ⟨⟨retention2834,(1964012227676477869/1000000000000000000),(4061079806220747/1000000000000000000),(1858279164791913287/250000000000000000),(10908395511668070660349/500000000000000000),(996462302293564643/1000000000000000000)⟩,(124988784021190717/125000000000000000),(147938267298044769/1000000000000000000),(284151485806786197/500000000000000000),(69695026992341817/125000000000000000)⟩
theorem valid2834 : certificate2834.Valid := by decide +kernel
theorem sound2834 : certificate2834.Sound := rat_cut_bin_certificate_sound certificate2834 profilesValid2834 numericValid2834 valid2834

def retention2835 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(89982989089484327/343417417683480102216),(71990651625078479/125000000000000000),4,(5092724600795136911084927033914115559/2303700852002511328000000000000000000),true,MergedCutProfiles.Batch446.profile17842,![MergedCutProfiles.Batch446.profile17842,MergedCutProfiles.Batch446.profile17843,MergedCutProfiles.Batch446.profile17844,MergedCutProfiles.Batch446.profile17845,MergedCutProfiles.Batch011.profile462,MergedCutProfiles.Batch446.profile17846,MergedCutProfiles.Batch312.profile12484,MergedCutProfiles.Batch446.profile17847,MergedCutProfiles.Batch446.profile17848,MergedCutProfiles.Batch011.profile478,MergedCutProfiles.Batch446.profile17849,MergedCutProfiles.Batch312.profile12485,MergedCutProfiles.Batch446.profile17850,MergedCutProfiles.Batch011.profile464,MergedCutProfiles.Batch312.profile12494,MergedCutProfiles.Batch312.profile12486]⟩
theorem profilesValid2835 : retention2835.ProfilesValid := by
  change ∀ j : Fin 16, (retention2835.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch446.valid17842
  · exact MergedCutProfiles.Batch446.valid17843
  · exact MergedCutProfiles.Batch446.valid17844
  · exact MergedCutProfiles.Batch446.valid17845
  · exact MergedCutProfiles.Batch011.valid462
  · exact MergedCutProfiles.Batch446.valid17846
  · exact MergedCutProfiles.Batch312.valid12484
  · exact MergedCutProfiles.Batch446.valid17847
  · exact MergedCutProfiles.Batch446.valid17848
  · exact MergedCutProfiles.Batch011.valid478
  · exact MergedCutProfiles.Batch446.valid17849
  · exact MergedCutProfiles.Batch312.valid12485
  · exact MergedCutProfiles.Batch446.valid17850
  · exact MergedCutProfiles.Batch011.valid464
  · exact MergedCutProfiles.Batch312.valid12494
  · exact MergedCutProfiles.Batch312.valid12486
theorem numericValid2835 : retention2835.NumericValid := by decide +kernel
def certificate2835 : RatCutBinCertificate := ⟨⟨retention2835,(1817588025887970869/1000000000000000000),(246507623072377/50000000000000000),(7524783897598156927/1000000000000000000),(18170925009373157771189/1000000000000000000),(2205907519392847601/1000000000000000000)⟩,(62493773681752461/62500000000000000),(596999984984321141/1000000000000000000),(47522310884524919/500000000000000000),(10571487979410733/250000000000000000)⟩
theorem valid2835 : certificate2835.Valid := by decide +kernel
theorem sound2835 : certificate2835.Sound := rat_cut_bin_certificate_sound certificate2835 profilesValid2835 numericValid2835 valid2835

def retention2836 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(23208297875000000/42927177210435012777),(629880923626390289/1000000000000000000),4,(147116781114449505809/64000000000000000000),true,MergedCutProfiles.Batch446.profile17843,![MergedCutProfiles.Batch446.profile17843,MergedCutProfiles.Batch446.profile17845,MergedCutProfiles.Batch446.profile17846,MergedCutProfiles.Batch446.profile17847,MergedCutProfiles.Batch011.profile478,MergedCutProfiles.Batch446.profile17850,MergedCutProfiles.Batch011.profile464,MergedCutProfiles.Batch312.profile12486,MergedCutProfiles.Batch312.profile12487,MergedCutProfiles.Batch011.profile479,MergedCutProfiles.Batch446.profile17851,MergedCutProfiles.Batch312.profile12495,MergedCutProfiles.Batch312.profile12489,MergedCutProfiles.Batch011.profile467,MergedCutProfiles.Batch446.profile17852,MergedCutProfiles.Batch312.profile12491]⟩
theorem profilesValid2836 : retention2836.ProfilesValid := by
  change ∀ j : Fin 16, (retention2836.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch446.valid17843
  · exact MergedCutProfiles.Batch446.valid17845
  · exact MergedCutProfiles.Batch446.valid17846
  · exact MergedCutProfiles.Batch446.valid17847
  · exact MergedCutProfiles.Batch011.valid478
  · exact MergedCutProfiles.Batch446.valid17850
  · exact MergedCutProfiles.Batch011.valid464
  · exact MergedCutProfiles.Batch312.valid12486
  · exact MergedCutProfiles.Batch312.valid12487
  · exact MergedCutProfiles.Batch011.valid479
  · exact MergedCutProfiles.Batch446.valid17851
  · exact MergedCutProfiles.Batch312.valid12495
  · exact MergedCutProfiles.Batch312.valid12489
  · exact MergedCutProfiles.Batch011.valid467
  · exact MergedCutProfiles.Batch446.valid17852
  · exact MergedCutProfiles.Batch312.valid12491
theorem numericValid2836 : retention2836.NumericValid := by decide +kernel
def certificate2836 : RatCutBinCertificate := ⟨⟨retention2836,(1817588025887970869/1000000000000000000),(246507623072377/50000000000000000),(7524783897598156927/1000000000000000000),(18170925009373157771189/1000000000000000000),(143371015796512217/62500000000000000)⟩,(62493773681752461/62500000000000000),(270294202849058337/500000000000000000),(3965538326868411/31250000000000000),(29636703311354753/500000000000000000)⟩
theorem valid2836 : certificate2836.Valid := by decide +kernel
theorem sound2836 : certificate2836.Sound := rat_cut_bin_certificate_sound certificate2836 profilesValid2836 numericValid2836 valid2836

def retention2837 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(662128769115918956/300490240473045089439),(1299664681/1000000000),(49/20),(753383683748097317804015552832512479/324916170250000000000000000000000000),true,MergedCutProfiles.Batch446.profile17848,![MergedCutProfiles.Batch446.profile17848,MergedCutProfiles.Batch312.profile12486,MergedCutProfiles.Batch312.profile12495,MergedCutProfiles.Batch011.profile468,MergedCutProfiles.Batch012.profile494,MergedCutProfiles.Batch012.profile482,MergedCutProfiles.Batch011.profile473,MergedCutProfiles.Batch312.profile12499,MergedCutProfiles.Batch312.profile12500,MergedCutProfiles.Batch446.profile17853,MergedCutProfiles.Batch012.profile486,MergedCutProfiles.Batch012.profile487,MergedCutProfiles.Batch446.profile17854,MergedCutProfiles.Batch312.profile12502,MergedCutProfiles.Batch312.profile12503,MergedCutProfiles.Batch446.profile17855]⟩
theorem profilesValid2837 : retention2837.ProfilesValid := by
  change ∀ j : Fin 16, (retention2837.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch446.valid17848
  · exact MergedCutProfiles.Batch312.valid12486
  · exact MergedCutProfiles.Batch312.valid12495
  · exact MergedCutProfiles.Batch011.valid468
  · exact MergedCutProfiles.Batch012.valid494
  · exact MergedCutProfiles.Batch012.valid482
  · exact MergedCutProfiles.Batch011.valid473
  · exact MergedCutProfiles.Batch312.valid12499
  · exact MergedCutProfiles.Batch312.valid12500
  · exact MergedCutProfiles.Batch446.valid17853
  · exact MergedCutProfiles.Batch012.valid486
  · exact MergedCutProfiles.Batch012.valid487
  · exact MergedCutProfiles.Batch446.valid17854
  · exact MergedCutProfiles.Batch312.valid12502
  · exact MergedCutProfiles.Batch312.valid12503
  · exact MergedCutProfiles.Batch446.valid17855
theorem numericValid2837 : retention2837.NumericValid := by decide +kernel
def certificate2837 : RatCutBinCertificate := ⟨⟨retention2837,(1817588025887970869/1000000000000000000),(246507623072377/50000000000000000),(7524783897598156927/1000000000000000000),(18170925009373157771189/1000000000000000000),(36184126695084507/15625000000000000)⟩,(62493773681752461/62500000000000000),(88234167326156647/250000000000000000),(139743107341529469/500000000000000000),(50920671281659881/250000000000000000)⟩
theorem valid2837 : certificate2837.Valid := by decide +kernel
theorem sound2837 : certificate2837.Sound := rat_cut_bin_certificate_sound certificate2837 profilesValid2837 numericValid2837 valid2837

def retention2838 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(8000000000000000000/300490240473045089439),(165532192278979739/31250000000000000),(6/5),(1120349719892666523669114776308410910031/529703015292735164800000000000000000000),true,MergedCutProfiles.Batch012.profile487,![MergedCutProfiles.Batch012.profile487,MergedCutProfiles.Batch446.profile17856,MergedCutProfiles.Batch446.profile17857,MergedCutProfiles.Batch446.profile17858,MergedCutProfiles.Batch312.profile12506,MergedCutProfiles.Batch446.profile17859,MergedCutProfiles.Batch446.profile17860,MergedCutProfiles.Batch446.profile17861,MergedCutProfiles.Batch446.profile17862,MergedCutProfiles.Batch312.profile12508,MergedCutProfiles.Batch446.profile17863,MergedCutProfiles.Batch446.profile17864,MergedCutProfiles.Batch446.profile17865,MergedCutProfiles.Batch446.profile17866,MergedCutProfiles.Batch312.profile12510,MergedCutProfiles.Batch446.profile17867]⟩
theorem profilesValid2838 : retention2838.ProfilesValid := by
  change ∀ j : Fin 16, (retention2838.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch012.valid487
  · exact MergedCutProfiles.Batch446.valid17856
  · exact MergedCutProfiles.Batch446.valid17857
  · exact MergedCutProfiles.Batch446.valid17858
  · exact MergedCutProfiles.Batch312.valid12506
  · exact MergedCutProfiles.Batch446.valid17859
  · exact MergedCutProfiles.Batch446.valid17860
  · exact MergedCutProfiles.Batch446.valid17861
  · exact MergedCutProfiles.Batch446.valid17862
  · exact MergedCutProfiles.Batch312.valid12508
  · exact MergedCutProfiles.Batch446.valid17863
  · exact MergedCutProfiles.Batch446.valid17864
  · exact MergedCutProfiles.Batch446.valid17865
  · exact MergedCutProfiles.Batch446.valid17866
  · exact MergedCutProfiles.Batch312.valid12510
  · exact MergedCutProfiles.Batch446.valid17867
theorem numericValid2838 : retention2838.NumericValid := by decide +kernel
def certificate2838 : RatCutBinCertificate := ⟨⟨retention2838,(1817588025887970869/1000000000000000000),(246507623072377/50000000000000000),(7524783897598156927/1000000000000000000),(18170925009373157771189/1000000000000000000),(2113623527005959183/1000000000000000000)⟩,(62493773681752461/62500000000000000),(48949672943689741/200000000000000000),(20533261947985009/50000000000000000),(141580695069273917/250000000000000000)⟩
theorem valid2838 : certificate2838.Valid := by decide +kernel
theorem sound2838 : certificate2838.Sound := rat_cut_bin_certificate_sound certificate2838 profilesValid2838 numericValid2838 valid2838

def retention2839 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(1/2),64,1,(63842289268809469711650675485864946351/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch012.profile509,(fun _ => MergedCutProfiles.Batch012.profile509)⟩
theorem profilesValid2839 : retention2839.ProfilesValid := by
  exact MergedCutProfiles.Batch012.valid509
theorem numericValid2839 : retention2839.NumericValid := by decide +kernel
def certificate2839 : RatCutBinCertificate := ⟨⟨retention2839,(1817588025887970869/1000000000000000000),(246507623072377/50000000000000000),(7524783897598156927/1000000000000000000),(18170925009373157771189/1000000000000000000),(996344906906070841/1000000000000000000)⟩,(62493773681752461/62500000000000000),(429403513976109097/1000000000000000000),(207596159062442903/1000000000000000000),(203646252132531271/1000000000000000000)⟩
theorem valid2839 : certificate2839.Valid := by decide +kernel
theorem sound2839 : certificate2839.Sound := rat_cut_bin_certificate_sound certificate2839 profilesValid2839 numericValid2839 valid2839

def retention2840 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(8000000000000000000/300490240473045089439),(196741146112402689/25000000000000000),1,(63470967900057902178827933337763136831/31478583377984430240000000000000000000),false,MergedCutProfiles.Batch446.profile17868,(fun _ => MergedCutProfiles.Batch446.profile17868)⟩
theorem profilesValid2840 : retention2840.ProfilesValid := by
  exact MergedCutProfiles.Batch446.valid17868
theorem numericValid2840 : retention2840.NumericValid := by decide +kernel
def certificate2840 : RatCutBinCertificate := ⟨⟨retention2840,(1967497943887970869/1000000000000000000),(246507623072377/50000000000000000),(7524783897598156927/1000000000000000000),(18170925009373157771189/1000000000000000000),(251879145322879719/125000000000000000)⟩,(499946081208344353/500000000000000000),(36160481217374973/500000000000000000),(365522857871019609/500000000000000000),(1172654531197647329/1000000000000000000)⟩
theorem valid2840 : certificate2840.Valid := by decide +kernel
theorem sound2840 : certificate2840.Sound := rat_cut_bin_certificate_sound certificate2840 profilesValid2840 numericValid2840 valid2840

def retention2841 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(1/2),64,1,(63842289268809469711650675485864946351/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch012.profile509,(fun _ => MergedCutProfiles.Batch012.profile509)⟩
theorem profilesValid2841 : retention2841.ProfilesValid := by
  exact MergedCutProfiles.Batch012.valid509
theorem numericValid2841 : retention2841.NumericValid := by decide +kernel
def certificate2841 : RatCutBinCertificate := ⟨⟨retention2841,(1967497943887970869/1000000000000000000),(246507623072377/50000000000000000),(7524783897598156927/1000000000000000000),(18170925009373157771189/1000000000000000000),(996246687639655463/1000000000000000000)⟩,(499946081208344353/500000000000000000),(146278165301819093/1000000000000000000),(285720777543301651/500000000000000000),(560509786410391747/1000000000000000000)⟩
theorem valid2841 : certificate2841.Valid := by decide +kernel
theorem sound2841 : certificate2841.Sound := rat_cut_bin_certificate_sound certificate2841 profilesValid2841 numericValid2841 valid2841

def retention2842 : RatCutRetentionCertificate := ⟨(11/1000),(23/2000),(601806759512494694/2194444176716075134529),(144581116767101131/250000000000000000),4,(5125800628696252930288640201069395191/2313297868273618096000000000000000000),true,MergedCutProfiles.Batch446.profile17869,![MergedCutProfiles.Batch446.profile17869,MergedCutProfiles.Batch446.profile17870,MergedCutProfiles.Batch446.profile17871,MergedCutProfiles.Batch446.profile17872,MergedCutProfiles.Batch446.profile17873,MergedCutProfiles.Batch446.profile17874,MergedCutProfiles.Batch446.profile17875,MergedCutProfiles.Batch446.profile17876,MergedCutProfiles.Batch446.profile17877,MergedCutProfiles.Batch446.profile17878,MergedCutProfiles.Batch446.profile17879,MergedCutProfiles.Batch447.profile17880,MergedCutProfiles.Batch447.profile17881,MergedCutProfiles.Batch447.profile17882,MergedCutProfiles.Batch447.profile17883,MergedCutProfiles.Batch447.profile17884]⟩
theorem profilesValid2842 : retention2842.ProfilesValid := by
  change ∀ j : Fin 16, (retention2842.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch446.valid17869
  · exact MergedCutProfiles.Batch446.valid17870
  · exact MergedCutProfiles.Batch446.valid17871
  · exact MergedCutProfiles.Batch446.valid17872
  · exact MergedCutProfiles.Batch446.valid17873
  · exact MergedCutProfiles.Batch446.valid17874
  · exact MergedCutProfiles.Batch446.valid17875
  · exact MergedCutProfiles.Batch446.valid17876
  · exact MergedCutProfiles.Batch446.valid17877
  · exact MergedCutProfiles.Batch446.valid17878
  · exact MergedCutProfiles.Batch446.valid17879
  · exact MergedCutProfiles.Batch447.valid17880
  · exact MergedCutProfiles.Batch447.valid17881
  · exact MergedCutProfiles.Batch447.valid17882
  · exact MergedCutProfiles.Batch447.valid17883
  · exact MergedCutProfiles.Batch447.valid17884
theorem numericValid2842 : retention2842.NumericValid := by decide +kernel
def certificate2842 : RatCutBinCertificate := ⟨⟨retention2842,(911303731629063933/500000000000000000),(1349374580489341/250000000000000000),(7618207140337950593/1000000000000000000),(8377854801191924745717/500000000000000000),(442126532281706897/200000000000000000)⟩,(999891760913355757/1000000000000000000),(594302389386326063/1000000000000000000),(96442248321444837/1000000000000000000),(43015982583917763/1000000000000000000)⟩
theorem valid2842 : certificate2842.Valid := by decide +kernel
theorem sound2842 : certificate2842.Sound := rat_cut_bin_certificate_sound certificate2842 profilesValid2842 numericValid2842 valid2842

def retention2843 : RatCutRetentionCertificate := ⟨(11/1000),(23/2000),(1272398760000000000/2194444176716075134529),(300903379756247347/500000000000000000),4,(2121330782281733303831104736014119/940323061738272959375000000000000),true,MergedCutProfiles.Batch447.profile17885,![MergedCutProfiles.Batch447.profile17885,MergedCutProfiles.Batch447.profile17886,MergedCutProfiles.Batch447.profile17887,MergedCutProfiles.Batch447.profile17888,MergedCutProfiles.Batch447.profile17889,MergedCutProfiles.Batch447.profile17881,MergedCutProfiles.Batch447.profile17883,MergedCutProfiles.Batch447.profile17890,MergedCutProfiles.Batch447.profile17891,MergedCutProfiles.Batch447.profile17892,MergedCutProfiles.Batch447.profile17893,MergedCutProfiles.Batch447.profile17894,MergedCutProfiles.Batch447.profile17895,MergedCutProfiles.Batch447.profile17896,MergedCutProfiles.Batch447.profile17897,MergedCutProfiles.Batch447.profile17898]⟩
theorem profilesValid2843 : retention2843.ProfilesValid := by
  change ∀ j : Fin 16, (retention2843.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch447.valid17885
  · exact MergedCutProfiles.Batch447.valid17886
  · exact MergedCutProfiles.Batch447.valid17887
  · exact MergedCutProfiles.Batch447.valid17888
  · exact MergedCutProfiles.Batch447.valid17889
  · exact MergedCutProfiles.Batch447.valid17881
  · exact MergedCutProfiles.Batch447.valid17883
  · exact MergedCutProfiles.Batch447.valid17890
  · exact MergedCutProfiles.Batch447.valid17891
  · exact MergedCutProfiles.Batch447.valid17892
  · exact MergedCutProfiles.Batch447.valid17893
  · exact MergedCutProfiles.Batch447.valid17894
  · exact MergedCutProfiles.Batch447.valid17895
  · exact MergedCutProfiles.Batch447.valid17896
  · exact MergedCutProfiles.Batch447.valid17897
  · exact MergedCutProfiles.Batch447.valid17898
theorem numericValid2843 : retention2843.NumericValid := by decide +kernel
def certificate2843 : RatCutBinCertificate := ⟨⟨retention2843,(911303731629063933/500000000000000000),(1349374580489341/250000000000000000),(7618207140337950593/1000000000000000000),(8377854801191924745717/500000000000000000),(225079427163424533/100000000000000000)⟩,(999891760913355757/1000000000000000000),(71028050888908153/125000000000000000),(55296537833318579/500000000000000000),(50433538814702209/1000000000000000000)⟩
theorem valid2843 : certificate2843.Valid := by decide +kernel
theorem sound2843 : certificate2843.Sound := rat_cut_bin_certificate_sound certificate2843 profilesValid2843 numericValid2843 valid2843

def certificates : List RatCutBinCertificate := [certificate2832,certificate2833,certificate2834,certificate2835,certificate2836,certificate2837,certificate2838,certificate2839,certificate2840,certificate2841,certificate2842,certificate2843]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2832,List.forall_mem_cons.mpr ⟨sound2833,List.forall_mem_cons.mpr ⟨sound2834,List.forall_mem_cons.mpr ⟨sound2835,List.forall_mem_cons.mpr ⟨sound2836,List.forall_mem_cons.mpr ⟨sound2837,List.forall_mem_cons.mpr ⟨sound2838,List.forall_mem_cons.mpr ⟨sound2839,List.forall_mem_cons.mpr ⟨sound2840,List.forall_mem_cons.mpr ⟨sound2841,List.forall_mem_cons.mpr ⟨sound2842,List.forall_mem_cons.mpr ⟨sound2843,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch236
