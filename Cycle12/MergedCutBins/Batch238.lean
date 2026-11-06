import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch013
import Cycle12.MergedCutProfiles.Batch014
import Cycle12.MergedCutProfiles.Batch015
import Cycle12.MergedCutProfiles.Batch016
import Cycle12.MergedCutProfiles.Batch314
import Cycle12.MergedCutProfiles.Batch315
import Cycle12.MergedCutProfiles.Batch449
import Cycle12.MergedCutProfiles.Batch450
import Cycle12.MergedCutProfiles.Batch451

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch238

def retention2856 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(295389831101636841/852766459039374206461),(57913896892782441/100000000000000000),4,(11350143980933492973/5120000000000000000),true,MergedCutProfiles.Batch449.profile17979,![MergedCutProfiles.Batch449.profile17979,MergedCutProfiles.Batch449.profile17980,MergedCutProfiles.Batch449.profile17981,MergedCutProfiles.Batch449.profile17982,MergedCutProfiles.Batch013.profile556,MergedCutProfiles.Batch449.profile17983,MergedCutProfiles.Batch449.profile17984,MergedCutProfiles.Batch314.profile12566,MergedCutProfiles.Batch449.profile17985,MergedCutProfiles.Batch013.profile557,MergedCutProfiles.Batch314.profile12574,MergedCutProfiles.Batch449.profile17986,MergedCutProfiles.Batch314.profile12567,MergedCutProfiles.Batch449.profile17987,MergedCutProfiles.Batch449.profile17988,MergedCutProfiles.Batch314.profile12575]⟩
theorem profilesValid2856 : retention2856.ProfilesValid := by
  change ∀ j : Fin 16, (retention2856.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch449.valid17979
  · exact MergedCutProfiles.Batch449.valid17980
  · exact MergedCutProfiles.Batch449.valid17981
  · exact MergedCutProfiles.Batch449.valid17982
  · exact MergedCutProfiles.Batch013.valid556
  · exact MergedCutProfiles.Batch449.valid17983
  · exact MergedCutProfiles.Batch449.valid17984
  · exact MergedCutProfiles.Batch314.valid12566
  · exact MergedCutProfiles.Batch449.valid17985
  · exact MergedCutProfiles.Batch013.valid557
  · exact MergedCutProfiles.Batch314.valid12574
  · exact MergedCutProfiles.Batch449.valid17986
  · exact MergedCutProfiles.Batch314.valid12567
  · exact MergedCutProfiles.Batch449.valid17987
  · exact MergedCutProfiles.Batch449.valid17988
  · exact MergedCutProfiles.Batch314.valid12575
theorem numericValid2856 : retention2856.NumericValid := by decide +kernel
def certificate2856 : RatCutBinCertificate := ⟨⟨retention2856,(365483743600086969/200000000000000000),(21663071517499/3125000000000000),(3856715472535746849/500000000000000000),(1651972473570312641507/125000000000000000),(2210255673897807497/1000000000000000000)⟩,(999862538386312007/1000000000000000000),(595695367938830081/1000000000000000000),(5982438720102689/62500000000000000),(21348807897319339/500000000000000000)⟩
theorem valid2856 : certificate2856.Valid := by decide +kernel
theorem sound2856 : certificate2856.Sound := rat_cut_bin_certificate_sound certificate2856 profilesValid2856 numericValid2856 valid2856

def retention2857 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(636945186500000000/852766459039374206461),(295389831101636841/500000000000000000),4,(558773229076460309/250000000000000000),true,MergedCutProfiles.Batch449.profile17980,![MergedCutProfiles.Batch449.profile17980,MergedCutProfiles.Batch449.profile17982,MergedCutProfiles.Batch449.profile17989,MergedCutProfiles.Batch449.profile17990,MergedCutProfiles.Batch314.profile12574,MergedCutProfiles.Batch314.profile12567,MergedCutProfiles.Batch013.profile558,MergedCutProfiles.Batch449.profile17991,MergedCutProfiles.Batch449.profile17992,MergedCutProfiles.Batch314.profile12576,MergedCutProfiles.Batch014.profile582,MergedCutProfiles.Batch014.profile560,MergedCutProfiles.Batch314.profile12570,MergedCutProfiles.Batch449.profile17993,MergedCutProfiles.Batch314.profile12578,MergedCutProfiles.Batch314.profile12571]⟩
theorem profilesValid2857 : retention2857.ProfilesValid := by
  change ∀ j : Fin 16, (retention2857.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch449.valid17980
  · exact MergedCutProfiles.Batch449.valid17982
  · exact MergedCutProfiles.Batch449.valid17989
  · exact MergedCutProfiles.Batch449.valid17990
  · exact MergedCutProfiles.Batch314.valid12574
  · exact MergedCutProfiles.Batch314.valid12567
  · exact MergedCutProfiles.Batch013.valid558
  · exact MergedCutProfiles.Batch449.valid17991
  · exact MergedCutProfiles.Batch449.valid17992
  · exact MergedCutProfiles.Batch314.valid12576
  · exact MergedCutProfiles.Batch014.valid582
  · exact MergedCutProfiles.Batch014.valid560
  · exact MergedCutProfiles.Batch314.valid12570
  · exact MergedCutProfiles.Batch449.valid17993
  · exact MergedCutProfiles.Batch314.valid12578
  · exact MergedCutProfiles.Batch314.valid12571
theorem numericValid2857 : retention2857.NumericValid := by decide +kernel
def certificate2857 : RatCutBinCertificate := ⟨⟨retention2857,(365483743600086969/200000000000000000),(21663071517499/3125000000000000),(3856715472535746849/500000000000000000),(1651972473570312641507/125000000000000000),(1114261796978442687/500000000000000000)⟩,(999862538386312007/1000000000000000000),(582929306987061293/1000000000000000000),(25617486982288483/250000000000000000),(23095017291866781/500000000000000000)⟩
theorem valid2857 : certificate2857.Valid := by decide +kernel
theorem sound2857 : certificate2857.Sound := rat_cut_bin_certificate_sound certificate2857 profilesValid2857 numericValid2857 valid2857

def retention2858 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(2475730464811269271/1705532918078748412922),(1273890373/1000000000),(49/20),(37169584993275199553/16000000000000000000),true,MergedCutProfiles.Batch449.profile17982,![MergedCutProfiles.Batch449.profile17982,MergedCutProfiles.Batch449.profile17990,MergedCutProfiles.Batch449.profile17986,MergedCutProfiles.Batch449.profile17991,MergedCutProfiles.Batch013.profile559,MergedCutProfiles.Batch449.profile17994,MergedCutProfiles.Batch449.profile17995,MergedCutProfiles.Batch314.profile12571,MergedCutProfiles.Batch314.profile12579,MergedCutProfiles.Batch014.profile563,MergedCutProfiles.Batch449.profile17996,MergedCutProfiles.Batch449.profile17997,MergedCutProfiles.Batch449.profile17998,MergedCutProfiles.Batch014.profile566,MergedCutProfiles.Batch014.profile567,MergedCutProfiles.Batch014.profile568]⟩
theorem profilesValid2858 : retention2858.ProfilesValid := by
  change ∀ j : Fin 16, (retention2858.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch449.valid17982
  · exact MergedCutProfiles.Batch449.valid17990
  · exact MergedCutProfiles.Batch449.valid17986
  · exact MergedCutProfiles.Batch449.valid17991
  · exact MergedCutProfiles.Batch013.valid559
  · exact MergedCutProfiles.Batch449.valid17994
  · exact MergedCutProfiles.Batch449.valid17995
  · exact MergedCutProfiles.Batch314.valid12571
  · exact MergedCutProfiles.Batch314.valid12579
  · exact MergedCutProfiles.Batch014.valid563
  · exact MergedCutProfiles.Batch449.valid17996
  · exact MergedCutProfiles.Batch449.valid17997
  · exact MergedCutProfiles.Batch449.valid17998
  · exact MergedCutProfiles.Batch014.valid566
  · exact MergedCutProfiles.Batch014.valid567
  · exact MergedCutProfiles.Batch014.valid568
theorem numericValid2858 : retention2858.NumericValid := by decide +kernel
def certificate2858 : RatCutBinCertificate := ⟨⟨retention2858,(365483743600086969/200000000000000000),(21663071517499/3125000000000000),(3856715472535746849/500000000000000000),(1651972473570312641507/125000000000000000),(2319075352357854413/1000000000000000000)⟩,(999862538386312007/1000000000000000000),(44759185829831223/125000000000000000),(17135895103885479/62500000000000000),(199098682636607307/1000000000000000000)⟩
theorem valid2858 : certificate2858.Valid := by decide +kernel
theorem sound2858 : certificate2858.Sound := rat_cut_bin_certificate_sound certificate2858 profilesValid2858 numericValid2858 valid2858

def retention2859 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(32000000000000000000/852766459039374206461),(2475730464811269271/1000000000000000000),(33/20),(2678124632786280175647/1280000000000000000000),true,MergedCutProfiles.Batch449.profile17999,![MergedCutProfiles.Batch449.profile17999,MergedCutProfiles.Batch450.profile18000,MergedCutProfiles.Batch450.profile18001,MergedCutProfiles.Batch450.profile18002,MergedCutProfiles.Batch314.profile12592,MergedCutProfiles.Batch450.profile18003,MergedCutProfiles.Batch450.profile18004,MergedCutProfiles.Batch450.profile18005,MergedCutProfiles.Batch450.profile18006,MergedCutProfiles.Batch314.profile12594,MergedCutProfiles.Batch450.profile18007,MergedCutProfiles.Batch450.profile18008,MergedCutProfiles.Batch450.profile18009,MergedCutProfiles.Batch450.profile18010,MergedCutProfiles.Batch314.profile12596,MergedCutProfiles.Batch450.profile18011]⟩
theorem profilesValid2859 : retention2859.ProfilesValid := by
  change ∀ j : Fin 16, (retention2859.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch449.valid17999
  · exact MergedCutProfiles.Batch450.valid18000
  · exact MergedCutProfiles.Batch450.valid18001
  · exact MergedCutProfiles.Batch450.valid18002
  · exact MergedCutProfiles.Batch314.valid12592
  · exact MergedCutProfiles.Batch450.valid18003
  · exact MergedCutProfiles.Batch450.valid18004
  · exact MergedCutProfiles.Batch450.valid18005
  · exact MergedCutProfiles.Batch450.valid18006
  · exact MergedCutProfiles.Batch314.valid12594
  · exact MergedCutProfiles.Batch450.valid18007
  · exact MergedCutProfiles.Batch450.valid18008
  · exact MergedCutProfiles.Batch450.valid18009
  · exact MergedCutProfiles.Batch450.valid18010
  · exact MergedCutProfiles.Batch314.valid12596
  · exact MergedCutProfiles.Batch450.valid18011
theorem numericValid2859 : retention2859.NumericValid := by decide +kernel
def certificate2859 : RatCutBinCertificate := ⟨⟨retention2859,(365483743600086969/200000000000000000),(21663071517499/3125000000000000),(3856715472535746849/500000000000000000),(1651972473570312641507/125000000000000000),(522393756037218437/250000000000000000)⟩,(999862538386312007/1000000000000000000),(30323618120534189/100000000000000000),(66981635964607919/200000000000000000),(161855208189364173/500000000000000000)⟩
theorem valid2859 : certificate2859.Valid := by decide +kernel
theorem sound2859 : certificate2859.Sound := rat_cut_bin_certificate_sound certificate2859 profilesValid2859 numericValid2859 valid2859

def retention2860 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(1/2),64,1,(63842362441861810878166029772824077959/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch015.profile610,(fun _ => MergedCutProfiles.Batch015.profile610)⟩
theorem profilesValid2860 : retention2860.ProfilesValid := by
  exact MergedCutProfiles.Batch015.valid610
theorem numericValid2860 : retention2860.NumericValid := by decide +kernel
def certificate2860 : RatCutBinCertificate := ⟨⟨retention2860,(365483743600086969/200000000000000000),(21663071517499/3125000000000000),(3856715472535746849/500000000000000000),(1651972473570312641507/125000000000000000),(995894582917937301/1000000000000000000)⟩,(999862538386312007/1000000000000000000),(434927440434388389/1000000000000000000),(40592385718893169/200000000000000000),(99501995757444167/500000000000000000)⟩
theorem valid2860 : certificate2860.Valid := by decide +kernel
theorem sound2860 : certificate2860.Sound := rat_cut_bin_certificate_sound certificate2860 profilesValid2860 numericValid2860 valid2860

def retention2861 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(32000000000000000000/852766459039374206461),(999847510871568229/125000000000000000),1,(63179911496111819402246808985886128527/31995120347890183328000000000000000000),false,MergedCutProfiles.Batch450.profile18012,(fun _ => MergedCutProfiles.Batch450.profile18012)⟩
theorem profilesValid2861 : retention2861.ProfilesValid := by
  exact MergedCutProfiles.Batch450.valid18012
theorem numericValid2861 : retention2861.NumericValid := by decide +kernel
def certificate2861 : RatCutBinCertificate := ⟨⟨retention2861,(395760002400086969/200000000000000000),(21663071517499/3125000000000000),(3856715472535746849/500000000000000000),(1651972473570312641507/125000000000000000),(1972894971359360727/1000000000000000000)⟩,(31245348475378171/31250000000000000),(36655746713993191/500000000000000000),(728614679040223043/1000000000000000000),(1152894462780383809/1000000000000000000)⟩
theorem valid2861 : certificate2861.Valid := by decide +kernel
theorem sound2861 : certificate2861.Sound := rat_cut_bin_certificate_sound certificate2861 profilesValid2861 numericValid2861 valid2861

def retention2862 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(1/2),64,1,(63842362441861810878166029772824077959/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch015.profile610,(fun _ => MergedCutProfiles.Batch015.profile610)⟩
theorem profilesValid2862 : retention2862.ProfilesValid := by
  exact MergedCutProfiles.Batch015.valid610
theorem numericValid2862 : retention2862.NumericValid := by decide +kernel
def certificate2862 : RatCutBinCertificate := ⟨⟨retention2862,(395760002400086969/200000000000000000),(21663071517499/3125000000000000),(3856715472535746849/500000000000000000),(1651972473570312641507/125000000000000000),(995758534143852137/1000000000000000000)⟩,(31245348475378171/31250000000000000),(36312989486772591/250000000000000000),(143347558584424869/250000000000000000),(562126589293761279/1000000000000000000)⟩
theorem valid2862 : certificate2862.Valid := by decide +kernel
theorem sound2862 : certificate2862.Sound := rat_cut_bin_certificate_sound certificate2862 profilesValid2862 numericValid2862 valid2862

def retention2863 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(585807643154978989/1463842310930751193404),(9062618241877769/15625000000000000),4,(2218245423896570251/1000000000000000000),true,MergedCutProfiles.Batch450.profile18013,![MergedCutProfiles.Batch450.profile18013,MergedCutProfiles.Batch450.profile18014,MergedCutProfiles.Batch450.profile18015,MergedCutProfiles.Batch450.profile18016,MergedCutProfiles.Batch450.profile18017,MergedCutProfiles.Batch450.profile18018,MergedCutProfiles.Batch450.profile18019,MergedCutProfiles.Batch315.profile12609,MergedCutProfiles.Batch450.profile18020,MergedCutProfiles.Batch450.profile18021,MergedCutProfiles.Batch015.profile612,MergedCutProfiles.Batch315.profile12620,MergedCutProfiles.Batch450.profile18022,MergedCutProfiles.Batch450.profile18023,MergedCutProfiles.Batch450.profile18024,MergedCutProfiles.Batch315.profile12611]⟩
theorem profilesValid2863 : retention2863.ProfilesValid := by
  change ∀ j : Fin 16, (retention2863.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch450.valid18013
  · exact MergedCutProfiles.Batch450.valid18014
  · exact MergedCutProfiles.Batch450.valid18015
  · exact MergedCutProfiles.Batch450.valid18016
  · exact MergedCutProfiles.Batch450.valid18017
  · exact MergedCutProfiles.Batch450.valid18018
  · exact MergedCutProfiles.Batch450.valid18019
  · exact MergedCutProfiles.Batch315.valid12609
  · exact MergedCutProfiles.Batch450.valid18020
  · exact MergedCutProfiles.Batch450.valid18021
  · exact MergedCutProfiles.Batch015.valid612
  · exact MergedCutProfiles.Batch315.valid12620
  · exact MergedCutProfiles.Batch450.valid18022
  · exact MergedCutProfiles.Batch450.valid18023
  · exact MergedCutProfiles.Batch450.valid18024
  · exact MergedCutProfiles.Batch315.valid12611
theorem numericValid2863 : retention2863.NumericValid := by decide +kernel
def certificate2863 : RatCutBinCertificate := ⟨⟨retention2863,(1831262035690379651/1000000000000000000),(1008381335301397/125000000000000000),(1562100323579834151/200000000000000000),(5743011293647465710453/500000000000000000),(2210679769934991661/1000000000000000000)⟩,(124980208886614071/125000000000000000),(298751802021148971/500000000000000000),(18957009642444417/200000000000000000),(42298696956189523/1000000000000000000)⟩
theorem valid2863 : certificate2863.Valid := by decide +kernel
theorem sound2863 : certificate2863.Sound := rat_cut_bin_certificate_sound certificate2863 profilesValid2863 numericValid2863 valid2863

def retention2864 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(318870166750000000/365960577732687798351),(585807643154978989/1000000000000000000),4,(5213501156656848235686062458120847911/2343230572619915956000000000000000000),true,MergedCutProfiles.Batch450.profile18025,![MergedCutProfiles.Batch450.profile18025,MergedCutProfiles.Batch450.profile18026,MergedCutProfiles.Batch450.profile18027,MergedCutProfiles.Batch450.profile18020,MergedCutProfiles.Batch015.profile612,MergedCutProfiles.Batch315.profile12610,MergedCutProfiles.Batch450.profile18024,MergedCutProfiles.Batch315.profile12621,MergedCutProfiles.Batch450.profile18028,MergedCutProfiles.Batch015.profile614,MergedCutProfiles.Batch450.profile18029,MergedCutProfiles.Batch315.profile12614,MergedCutProfiles.Batch450.profile18030,MergedCutProfiles.Batch450.profile18031,MergedCutProfiles.Batch015.profile616,MergedCutProfiles.Batch315.profile12616]⟩
theorem profilesValid2864 : retention2864.ProfilesValid := by
  change ∀ j : Fin 16, (retention2864.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch450.valid18025
  · exact MergedCutProfiles.Batch450.valid18026
  · exact MergedCutProfiles.Batch450.valid18027
  · exact MergedCutProfiles.Batch450.valid18020
  · exact MergedCutProfiles.Batch015.valid612
  · exact MergedCutProfiles.Batch315.valid12610
  · exact MergedCutProfiles.Batch450.valid18024
  · exact MergedCutProfiles.Batch315.valid12621
  · exact MergedCutProfiles.Batch450.valid18028
  · exact MergedCutProfiles.Batch015.valid614
  · exact MergedCutProfiles.Batch450.valid18029
  · exact MergedCutProfiles.Batch315.valid12614
  · exact MergedCutProfiles.Batch450.valid18030
  · exact MergedCutProfiles.Batch450.valid18031
  · exact MergedCutProfiles.Batch015.valid616
  · exact MergedCutProfiles.Batch315.valid12616
theorem numericValid2864 : retention2864.NumericValid := by decide +kernel
def certificate2864 : RatCutBinCertificate := ⟨⟨retention2864,(1831262035690379651/1000000000000000000),(1008381335301397/125000000000000000),(1562100323579834151/200000000000000000),(5743011293647465710453/500000000000000000),(2217354598286957279/1000000000000000000)⟩,(124980208886614071/125000000000000000),(591720977963701381/1000000000000000000),(24447785993900161/250000000000000000),(43830252053451867/1000000000000000000)⟩
theorem valid2864 : certificate2864.Valid := by decide +kernel
theorem sound2864 : certificate2864.Sound := rat_cut_bin_certificate_sound certificate2864 profilesValid2864 numericValid2864 valid2864

def retention2865 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1070504989485838381/487947436976917064468),(1275480667/1000000000),(49/20),(18506123157301579919/8000000000000000000),true,MergedCutProfiles.Batch015.profile611,![MergedCutProfiles.Batch015.profile611,MergedCutProfiles.Batch015.profile612,MergedCutProfiles.Batch015.profile613,MergedCutProfiles.Batch015.profile614,MergedCutProfiles.Batch015.profile615,MergedCutProfiles.Batch015.profile616,MergedCutProfiles.Batch450.profile18032,MergedCutProfiles.Batch015.profile618,MergedCutProfiles.Batch015.profile619,MergedCutProfiles.Batch016.profile640,MergedCutProfiles.Batch450.profile18033,MergedCutProfiles.Batch450.profile18034,MergedCutProfiles.Batch450.profile18035,MergedCutProfiles.Batch315.profile12623,MergedCutProfiles.Batch315.profile12624,MergedCutProfiles.Batch450.profile18036]⟩
theorem profilesValid2865 : retention2865.ProfilesValid := by
  change ∀ j : Fin 16, (retention2865.fine j).Valid
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
  · exact MergedCutProfiles.Batch450.valid18034
  · exact MergedCutProfiles.Batch450.valid18035
  · exact MergedCutProfiles.Batch315.valid12623
  · exact MergedCutProfiles.Batch315.valid12624
  · exact MergedCutProfiles.Batch450.valid18036
theorem numericValid2865 : retention2865.NumericValid := by decide +kernel
def certificate2865 : RatCutBinCertificate := ⟨⟨retention2865,(1831262035690379651/1000000000000000000),(1008381335301397/125000000000000000),(1562100323579834151/200000000000000000),(5743011293647465710453/500000000000000000),(461726286394512191/200000000000000000)⟩,(124980208886614071/125000000000000000),(180711403325584497/500000000000000000),(135375275853956331/500000000000000000),(7839373605037513/40000000000000000)⟩
theorem valid2865 : certificate2865.Valid := by decide +kernel
theorem sound2865 : certificate2865.Sound := rat_cut_bin_certificate_sound certificate2865 profilesValid2865 numericValid2865 valid2865

def retention2866 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(16000000000000000000/365960577732687798351),(3211514968457515143/1000000000000000000),(29/20),(2637000689353680470463/1280000000000000000000),true,MergedCutProfiles.Batch016.profile643,![MergedCutProfiles.Batch016.profile643,MergedCutProfiles.Batch016.profile648,MergedCutProfiles.Batch450.profile18037,MergedCutProfiles.Batch450.profile18038,MergedCutProfiles.Batch450.profile18039,MergedCutProfiles.Batch451.profile18040,MergedCutProfiles.Batch451.profile18041,MergedCutProfiles.Batch451.profile18042,MergedCutProfiles.Batch451.profile18043,MergedCutProfiles.Batch451.profile18044,MergedCutProfiles.Batch451.profile18045,MergedCutProfiles.Batch451.profile18046,MergedCutProfiles.Batch451.profile18047,MergedCutProfiles.Batch451.profile18048,MergedCutProfiles.Batch451.profile18049,MergedCutProfiles.Batch451.profile18050]⟩
theorem profilesValid2866 : retention2866.ProfilesValid := by
  change ∀ j : Fin 16, (retention2866.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch016.valid643
  · exact MergedCutProfiles.Batch016.valid648
  · exact MergedCutProfiles.Batch450.valid18037
  · exact MergedCutProfiles.Batch450.valid18038
  · exact MergedCutProfiles.Batch450.valid18039
  · exact MergedCutProfiles.Batch451.valid18040
  · exact MergedCutProfiles.Batch451.valid18041
  · exact MergedCutProfiles.Batch451.valid18042
  · exact MergedCutProfiles.Batch451.valid18043
  · exact MergedCutProfiles.Batch451.valid18044
  · exact MergedCutProfiles.Batch451.valid18045
  · exact MergedCutProfiles.Batch451.valid18046
  · exact MergedCutProfiles.Batch451.valid18047
  · exact MergedCutProfiles.Batch451.valid18048
  · exact MergedCutProfiles.Batch451.valid18049
  · exact MergedCutProfiles.Batch451.valid18050
theorem numericValid2866 : retention2866.NumericValid := by decide +kernel
def certificate2866 : RatCutBinCertificate := ⟨⟨retention2866,(1831262035690379651/1000000000000000000),(1008381335301397/125000000000000000),(1562100323579834151/200000000000000000),(5743011293647465710453/500000000000000000),(411482847882619147/200000000000000000)⟩,(124980208886614071/125000000000000000),(143336035427037611/500000000000000000),(11097574246218597/31250000000000000),(12066888962155963/31250000000000000)⟩
theorem valid2866 : certificate2866.Valid := by decide +kernel
theorem sound2866 : certificate2866.Sound := rat_cut_bin_certificate_sound certificate2866 profilesValid2866 numericValid2866 valid2866

def retention2867 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1/2),64,1,(255369632393373974456752157088663284991/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch016.profile655,(fun _ => MergedCutProfiles.Batch016.profile655)⟩
theorem profilesValid2867 : retention2867.ProfilesValid := by
  exact MergedCutProfiles.Batch016.valid655
theorem numericValid2867 : retention2867.NumericValid := by decide +kernel
def certificate2867 : RatCutBinCertificate := ⟨⟨retention2867,(1831262035690379651/1000000000000000000),(1008381335301397/125000000000000000),(1562100323579834151/200000000000000000),(5743011293647465710453/500000000000000000),(497823106799024117/500000000000000000)⟩,(124980208886614071/125000000000000000),(87732219694600063/200000000000000000),(99934702815664521/500000000000000000),(39183905257870889/200000000000000000)⟩
theorem valid2867 : certificate2867.Valid := by decide +kernel
theorem sound2867 : certificate2867.Sound := rat_cut_bin_certificate_sound certificate2867 profilesValid2867 numericValid2867 valid2867

def certificates : List RatCutBinCertificate := [certificate2856,certificate2857,certificate2858,certificate2859,certificate2860,certificate2861,certificate2862,certificate2863,certificate2864,certificate2865,certificate2866,certificate2867]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2856,List.forall_mem_cons.mpr ⟨sound2857,List.forall_mem_cons.mpr ⟨sound2858,List.forall_mem_cons.mpr ⟨sound2859,List.forall_mem_cons.mpr ⟨sound2860,List.forall_mem_cons.mpr ⟨sound2861,List.forall_mem_cons.mpr ⟨sound2862,List.forall_mem_cons.mpr ⟨sound2863,List.forall_mem_cons.mpr ⟨sound2864,List.forall_mem_cons.mpr ⟨sound2865,List.forall_mem_cons.mpr ⟨sound2866,List.forall_mem_cons.mpr ⟨sound2867,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch238
