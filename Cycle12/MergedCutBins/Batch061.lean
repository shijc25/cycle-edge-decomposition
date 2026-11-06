import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch122
import Cycle12.MergedCutProfiles.Batch123
import Cycle12.MergedCutProfiles.Batch124
import Cycle12.MergedCutProfiles.Batch125

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch061

def retention732 : RatCutRetentionCertificate := ⟨(37/800),(93/2000),(11208934902944504377/22499097179828279839),(5494037301707922937/500000000000000000),(21/20),(4397109151639378122798011936036420301791/4395229841366338349600000000000000000000),false,MergedCutProfiles.Batch122.profile4917,(fun _ => MergedCutProfiles.Batch122.profile4917)⟩
theorem profilesValid732 : retention732.ProfilesValid := by
  exact MergedCutProfiles.Batch122.valid4917
theorem numericValid732 : retention732.NumericValid := by decide +kernel
def certificate732 : RatCutBinCertificate := ⟨⟨retention732,(2129070161864492131/1000000000000000000),(50858016999050421/500000000000000000),(1565580850186765421/125000000000000000),(35273467744402477229/125000000000000000),(982271721770031473/1000000000000000000)⟩,(993208118316980171/1000000000000000000),(3031192379515583/6250000000000000),(41014371776555581/250000000000000000),(3523893255218523/25000000000000000)⟩
theorem valid732 : certificate732.Valid := by decide +kernel
theorem sound732 : certificate732.Sound := rat_cut_bin_certificate_sound certificate732 profilesValid732 numericValid732 valid732

def retention733 : RatCutRetentionCertificate := ⟨(37/800),(93/2000),(1/2),(11208934902944504377/1000000000000000000),(21/20),(17884032343184096094241499931332726283311/17934295844711207003200000000000000000000),false,MergedCutProfiles.Batch122.profile4918,(fun _ => MergedCutProfiles.Batch122.profile4918)⟩
theorem profilesValid733 : retention733.ProfilesValid := by
  exact MergedCutProfiles.Batch122.valid4918
theorem numericValid733 : retention733.NumericValid := by decide +kernel
def certificate733 : RatCutBinCertificate := ⟨⟨retention733,(2129070161864492131/1000000000000000000),(50858016999050421/500000000000000000),(1565580850186765421/125000000000000000),(35273467744402477229/125000000000000000),(979041506364402819/1000000000000000000)⟩,(993208118316980171/1000000000000000000),(4860878621520019/10000000000000000),(81632427116182077/500000000000000000),(140055050788746389/1000000000000000000)⟩
theorem valid733 : certificate733.Valid := by decide +kernel
theorem sound733 : certificate733.Sound := rat_cut_bin_certificate_sound certificate733 profilesValid733 numericValid733 valid733

def retention734 : RatCutRetentionCertificate := ⟨(37/800),(93/2000),(10077172343777816533/22499097179828279839),(3725643604067568697/1000000000000000000),(6/5),(409023506694733622671179993490464437991/372564360406756869700000000000000000000),false,MergedCutProfiles.Batch122.profile4919,(fun _ => MergedCutProfiles.Batch122.profile4919)⟩
theorem profilesValid734 : retention734.ProfilesValid := by
  exact MergedCutProfiles.Batch122.valid4919
theorem numericValid734 : retention734.NumericValid := by decide +kernel
def certificate734 : RatCutBinCertificate := ⟨⟨retention734,(2505796833864492131/1000000000000000000),(50858016999050421/500000000000000000),(1565580850186765421/125000000000000000),(35273467744402477229/125000000000000000),(268359430887088431/250000000000000000)⟩,(992005260775060007/1000000000000000000),(47329451416609313/125000000000000000),(126819069963172437/500000000000000000),(187410604328251643/1000000000000000000)⟩
theorem valid734 : certificate734.Valid := by decide +kernel
theorem sound734 : certificate734.Sound := rat_cut_bin_certificate_sound certificate734 profilesValid734 numericValid734 valid734

def retention735 : RatCutRetentionCertificate := ⟨(37/800),(93/2000),(11131467532518860947/22499097179828279839),(10077172343777816533/1000000000000000000),(21/20),(16214554767281163940652801981083410632991/16123475750044506452800000000000000000000),false,MergedCutProfiles.Batch123.profile4920,(fun _ => MergedCutProfiles.Batch123.profile4920)⟩
theorem profilesValid735 : retention735.ProfilesValid := by
  exact MergedCutProfiles.Batch123.valid4920
theorem numericValid735 : retention735.NumericValid := by decide +kernel
def certificate735 : RatCutBinCertificate := ⟨⟨retention735,(2505796833864492131/1000000000000000000),(50858016999050421/500000000000000000),(1565580850186765421/125000000000000000),(35273467744402477229/125000000000000000),(246070088205507041/250000000000000000)⟩,(992005260775060007/1000000000000000000),(103233227077577987/250000000000000000),(221839355695090099/1000000000000000000),(1894384454368047/10000000000000000)⟩
theorem valid735 : certificate735.Valid := by decide +kernel
theorem sound735 : certificate735.Sound := rat_cut_bin_certificate_sound certificate735 profilesValid735 numericValid735 valid735

def retention736 : RatCutRetentionCertificate := ⟨(37/800),(93/2000),(11242782207844049557/22499097179828279839),(11131467532518860947/1000000000000000000),(21/20),(17769036096371973039615261976817729912471/17810348052030177515200000000000000000000),false,MergedCutProfiles.Batch123.profile4921,(fun _ => MergedCutProfiles.Batch123.profile4921)⟩
theorem profilesValid736 : retention736.ProfilesValid := by
  exact MergedCutProfiles.Batch123.valid4921
theorem numericValid736 : retention736.NumericValid := by decide +kernel
def certificate736 : RatCutBinCertificate := ⟨⟨retention736,(2505796833864492131/1000000000000000000),(50858016999050421/500000000000000000),(1565580850186765421/125000000000000000),(35273467744402477229/125000000000000000),(488156014368266331/500000000000000000)⟩,(992005260775060007/1000000000000000000),(416303125148919297/1000000000000000000),(218872305157168751/1000000000000000000),(11684355408978949/62500000000000000)⟩
theorem valid736 : certificate736.Valid := by decide +kernel
theorem sound736 : certificate736.Sound := rat_cut_bin_certificate_sound certificate736 profilesValid736 numericValid736 valid736

def retention737 : RatCutRetentionCertificate := ⟨(37/800),(93/2000),(1/2),(11242782207844049557/1000000000000000000),(21/20),(17938867297850622969085907406241755738791/17988451532550479291200000000000000000000),false,MergedCutProfiles.Batch122.profile4918,(fun _ => MergedCutProfiles.Batch122.profile4918)⟩
theorem profilesValid737 : retention737.ProfilesValid := by
  exact MergedCutProfiles.Batch122.valid4918
theorem numericValid737 : retention737.NumericValid := by decide +kernel
def certificate737 : RatCutBinCertificate := ⟨⟨retention737,(2505796833864492131/1000000000000000000),(50858016999050421/500000000000000000),(1565580850186765421/125000000000000000),(35273467744402477229/125000000000000000),(195175026996498669/200000000000000000)⟩,(992005260775060007/1000000000000000000),(416489501693053577/1000000000000000000),(109354511025248609/500000000000000000),(46717399405010473/250000000000000000)⟩
theorem valid737 : certificate737.Valid := by decide +kernel
theorem sound737 : certificate737.Sound := rat_cut_bin_certificate_sound certificate737 profilesValid737 numericValid737 valid737

def retention738 : RatCutRetentionCertificate := ⟨(93/2000),(187/4000),(837724157326525534/22227941112471521667),(51839366171195887/62500000000000000),3,(8407534137807929127/4000000000000000000),true,MergedCutProfiles.Batch123.profile4922,![MergedCutProfiles.Batch123.profile4922,MergedCutProfiles.Batch123.profile4923,MergedCutProfiles.Batch123.profile4924,MergedCutProfiles.Batch123.profile4925,MergedCutProfiles.Batch123.profile4926,MergedCutProfiles.Batch123.profile4927,MergedCutProfiles.Batch123.profile4928,MergedCutProfiles.Batch123.profile4929,MergedCutProfiles.Batch123.profile4930,MergedCutProfiles.Batch123.profile4931,MergedCutProfiles.Batch123.profile4932,MergedCutProfiles.Batch123.profile4933,MergedCutProfiles.Batch123.profile4934,MergedCutProfiles.Batch123.profile4935,MergedCutProfiles.Batch123.profile4936,MergedCutProfiles.Batch123.profile4937]⟩
theorem profilesValid738 : retention738.ProfilesValid := by
  change ∀ j : Fin 16, (retention738.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch123.valid4922
  · exact MergedCutProfiles.Batch123.valid4923
  · exact MergedCutProfiles.Batch123.valid4924
  · exact MergedCutProfiles.Batch123.valid4925
  · exact MergedCutProfiles.Batch123.valid4926
  · exact MergedCutProfiles.Batch123.valid4927
  · exact MergedCutProfiles.Batch123.valid4928
  · exact MergedCutProfiles.Batch123.valid4929
  · exact MergedCutProfiles.Batch123.valid4930
  · exact MergedCutProfiles.Batch123.valid4931
  · exact MergedCutProfiles.Batch123.valid4932
  · exact MergedCutProfiles.Batch123.valid4933
  · exact MergedCutProfiles.Batch123.valid4934
  · exact MergedCutProfiles.Batch123.valid4935
  · exact MergedCutProfiles.Batch123.valid4936
  · exact MergedCutProfiles.Batch123.valid4937
theorem numericValid738 : retention738.NumericValid := by decide +kernel
def certificate738 : RatCutBinCertificate := ⟨⟨retention738,(426411054045357163/200000000000000000),(102941493058315297/1000000000000000000),(2515075777424674363/200000000000000000),(279916723399605254071/1000000000000000000),(1024758533411978461/500000000000000000)⟩,(99315256850220439/100000000000000000),(380335728133361683/1000000000000000000),(12599547707210507/50000000000000000),(133976928878254201/1000000000000000000)⟩
theorem valid738 : certificate738.Valid := by decide +kernel
theorem sound738 : certificate738.Sound := rat_cut_bin_certificate_sound certificate738 profilesValid738 numericValid738 valid738

def retention739 : RatCutRetentionCertificate := ⟨(93/2000),(187/4000),(51259985000000000/1307525947792442451),(418862078663262767/500000000000000000),3,(53766939504541924739/25600000000000000000),true,MergedCutProfiles.Batch123.profile4938,![MergedCutProfiles.Batch123.profile4938,MergedCutProfiles.Batch123.profile4939,MergedCutProfiles.Batch123.profile4940,MergedCutProfiles.Batch123.profile4941,MergedCutProfiles.Batch123.profile4942,MergedCutProfiles.Batch123.profile4943,MergedCutProfiles.Batch123.profile4944,MergedCutProfiles.Batch123.profile4945,MergedCutProfiles.Batch123.profile4946,MergedCutProfiles.Batch123.profile4947,MergedCutProfiles.Batch123.profile4948,MergedCutProfiles.Batch123.profile4949,MergedCutProfiles.Batch123.profile4950,MergedCutProfiles.Batch123.profile4951,MergedCutProfiles.Batch123.profile4952,MergedCutProfiles.Batch123.profile4953]⟩
theorem profilesValid739 : retention739.ProfilesValid := by
  change ∀ j : Fin 16, (retention739.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch123.valid4938
  · exact MergedCutProfiles.Batch123.valid4939
  · exact MergedCutProfiles.Batch123.valid4940
  · exact MergedCutProfiles.Batch123.valid4941
  · exact MergedCutProfiles.Batch123.valid4942
  · exact MergedCutProfiles.Batch123.valid4943
  · exact MergedCutProfiles.Batch123.valid4944
  · exact MergedCutProfiles.Batch123.valid4945
  · exact MergedCutProfiles.Batch123.valid4946
  · exact MergedCutProfiles.Batch123.valid4947
  · exact MergedCutProfiles.Batch123.valid4948
  · exact MergedCutProfiles.Batch123.valid4949
  · exact MergedCutProfiles.Batch123.valid4950
  · exact MergedCutProfiles.Batch123.valid4951
  · exact MergedCutProfiles.Batch123.valid4952
  · exact MergedCutProfiles.Batch123.valid4953
theorem numericValid739 : retention739.NumericValid := by decide +kernel
def certificate739 : RatCutBinCertificate := ⟨⟨retention739,(426411054045357163/200000000000000000),(102941493058315297/1000000000000000000),(2515075777424674363/200000000000000000),(279916723399605254071/1000000000000000000),(1023952341692860931/500000000000000000)⟩,(99315256850220439/100000000000000000),(47380775130047477/125000000000000000),(10129585443293023/40000000000000000),(26969280351392721/200000000000000000)⟩
theorem valid739 : certificate739.Valid := by decide +kernel
theorem sound739 : certificate739.Sound := rat_cut_bin_certificate_sound certificate739 profilesValid739 numericValid739 valid739

def retention740 : RatCutRetentionCertificate := ⟨(93/2000),(187/4000),(962942316653058079/22227941112471521667),(174283949/200000000),(57/20),(518936480629853139/250000000000000000),true,MergedCutProfiles.Batch123.profile4954,![MergedCutProfiles.Batch123.profile4954,MergedCutProfiles.Batch123.profile4955,MergedCutProfiles.Batch123.profile4956,MergedCutProfiles.Batch123.profile4957,MergedCutProfiles.Batch123.profile4958,MergedCutProfiles.Batch123.profile4959,MergedCutProfiles.Batch123.profile4929,MergedCutProfiles.Batch124.profile4960,MergedCutProfiles.Batch124.profile4961,MergedCutProfiles.Batch123.profile4948,MergedCutProfiles.Batch124.profile4962,MergedCutProfiles.Batch124.profile4963,MergedCutProfiles.Batch123.profile4936,MergedCutProfiles.Batch124.profile4964,MergedCutProfiles.Batch124.profile4965,MergedCutProfiles.Batch124.profile4966]⟩
theorem profilesValid740 : retention740.ProfilesValid := by
  change ∀ j : Fin 16, (retention740.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch123.valid4954
  · exact MergedCutProfiles.Batch123.valid4955
  · exact MergedCutProfiles.Batch123.valid4956
  · exact MergedCutProfiles.Batch123.valid4957
  · exact MergedCutProfiles.Batch123.valid4958
  · exact MergedCutProfiles.Batch123.valid4959
  · exact MergedCutProfiles.Batch123.valid4929
  · exact MergedCutProfiles.Batch124.valid4960
  · exact MergedCutProfiles.Batch124.valid4961
  · exact MergedCutProfiles.Batch123.valid4948
  · exact MergedCutProfiles.Batch124.valid4962
  · exact MergedCutProfiles.Batch124.valid4963
  · exact MergedCutProfiles.Batch123.valid4936
  · exact MergedCutProfiles.Batch124.valid4964
  · exact MergedCutProfiles.Batch124.valid4965
  · exact MergedCutProfiles.Batch124.valid4966
theorem numericValid740 : retention740.NumericValid := by decide +kernel
def certificate740 : RatCutBinCertificate := ⟨⟨retention740,(426411054045357163/200000000000000000),(102941493058315297/1000000000000000000),(2515075777424674363/200000000000000000),(279916723399605254071/1000000000000000000),(506499441058076683/250000000000000000)⟩,(99315256850220439/100000000000000000),(37693418036573153/100000000000000000),(31911779436340247/125000000000000000),(1093408080710689/7812500000000000)⟩
theorem valid740 : certificate740.Valid := by decide +kernel
theorem sound740 : certificate740.Sound := rat_cut_bin_certificate_sound certificate740 profilesValid740 numericValid740 valid740

def retention741 : RatCutRetentionCertificate := ⟨(93/2000),(187/4000),(1732053591654720251/22227941112471521667),(962942316653058079/1000000000000000000),(53/20),(2518204384623803497223/1280000000000000000000),true,MergedCutProfiles.Batch124.profile4967,![MergedCutProfiles.Batch124.profile4967,MergedCutProfiles.Batch123.profile4941,MergedCutProfiles.Batch124.profile4968,MergedCutProfiles.Batch124.profile4969,MergedCutProfiles.Batch124.profile4961,MergedCutProfiles.Batch124.profile4970,MergedCutProfiles.Batch124.profile4971,MergedCutProfiles.Batch124.profile4972,MergedCutProfiles.Batch124.profile4973,MergedCutProfiles.Batch124.profile4974,MergedCutProfiles.Batch124.profile4975,MergedCutProfiles.Batch124.profile4976,MergedCutProfiles.Batch124.profile4977,MergedCutProfiles.Batch124.profile4978,MergedCutProfiles.Batch124.profile4979,MergedCutProfiles.Batch124.profile4980]⟩
theorem profilesValid741 : retention741.ProfilesValid := by
  change ∀ j : Fin 16, (retention741.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch124.valid4967
  · exact MergedCutProfiles.Batch123.valid4941
  · exact MergedCutProfiles.Batch124.valid4968
  · exact MergedCutProfiles.Batch124.valid4969
  · exact MergedCutProfiles.Batch124.valid4961
  · exact MergedCutProfiles.Batch124.valid4970
  · exact MergedCutProfiles.Batch124.valid4971
  · exact MergedCutProfiles.Batch124.valid4972
  · exact MergedCutProfiles.Batch124.valid4973
  · exact MergedCutProfiles.Batch124.valid4974
  · exact MergedCutProfiles.Batch124.valid4975
  · exact MergedCutProfiles.Batch124.valid4976
  · exact MergedCutProfiles.Batch124.valid4977
  · exact MergedCutProfiles.Batch124.valid4978
  · exact MergedCutProfiles.Batch124.valid4979
  · exact MergedCutProfiles.Batch124.valid4980
theorem numericValid741 : retention741.NumericValid := by decide +kernel
def certificate741 : RatCutBinCertificate := ⟨⟨retention741,(426411054045357163/200000000000000000),(102941493058315297/1000000000000000000),(2515075777424674363/200000000000000000),(279916723399605254071/1000000000000000000),(1921090299201940753/1000000000000000000)⟩,(99315256850220439/100000000000000000),(76408220668052731/200000000000000000),(125173151362263253/500000000000000000),(140196913434937823/1000000000000000000)⟩
theorem valid741 : certificate741.Valid := by decide +kernel
theorem sound741 : certificate741.Sound := rat_cut_bin_certificate_sound certificate741 profilesValid741 numericValid741 valid741

def retention742 : RatCutRetentionCertificate := ⟨(93/2000),(187/4000),(2002681073721548453/7409313704157173889),(1732053591654720251/1000000000000000000),(17/10),(1884713337768240563711/1280000000000000000000),true,MergedCutProfiles.Batch124.profile4981,![MergedCutProfiles.Batch124.profile4981,MergedCutProfiles.Batch124.profile4982,MergedCutProfiles.Batch124.profile4983,MergedCutProfiles.Batch124.profile4984,MergedCutProfiles.Batch124.profile4985,MergedCutProfiles.Batch124.profile4986,MergedCutProfiles.Batch124.profile4987,MergedCutProfiles.Batch124.profile4988,MergedCutProfiles.Batch124.profile4989,MergedCutProfiles.Batch124.profile4990,MergedCutProfiles.Batch124.profile4991,MergedCutProfiles.Batch124.profile4992,MergedCutProfiles.Batch124.profile4993,MergedCutProfiles.Batch124.profile4994,MergedCutProfiles.Batch124.profile4995,MergedCutProfiles.Batch124.profile4996]⟩
theorem profilesValid742 : retention742.ProfilesValid := by
  change ∀ j : Fin 16, (retention742.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch124.valid4981
  · exact MergedCutProfiles.Batch124.valid4982
  · exact MergedCutProfiles.Batch124.valid4983
  · exact MergedCutProfiles.Batch124.valid4984
  · exact MergedCutProfiles.Batch124.valid4985
  · exact MergedCutProfiles.Batch124.valid4986
  · exact MergedCutProfiles.Batch124.valid4987
  · exact MergedCutProfiles.Batch124.valid4988
  · exact MergedCutProfiles.Batch124.valid4989
  · exact MergedCutProfiles.Batch124.valid4990
  · exact MergedCutProfiles.Batch124.valid4991
  · exact MergedCutProfiles.Batch124.valid4992
  · exact MergedCutProfiles.Batch124.valid4993
  · exact MergedCutProfiles.Batch124.valid4994
  · exact MergedCutProfiles.Batch124.valid4995
  · exact MergedCutProfiles.Batch124.valid4996
theorem numericValid742 : retention742.NumericValid := by decide +kernel
def certificate742 : RatCutBinCertificate := ⟨⟨retention742,(426411054045357163/200000000000000000),(102941493058315297/1000000000000000000),(2515075777424674363/200000000000000000),(279916723399605254071/1000000000000000000),(721379321436533951/500000000000000000)⟩,(99315256850220439/100000000000000000),(10539347448017361/25000000000000000),(214286657508617013/1000000000000000000),(140058600482770097/1000000000000000000)⟩
theorem valid742 : certificate742.Valid := by decide +kernel
theorem sound742 : certificate742.Sound := rat_cut_bin_certificate_sound certificate742 profilesValid742 numericValid742 valid742

def retention743 : RatCutRetentionCertificate := ⟨(93/2000),(187/4000),(10180423827336650047/22227941112471521667),(6008043221164645359/1000000000000000000),1,(266355940650331163439/256000000000000000000),true,MergedCutProfiles.Batch124.profile4997,![MergedCutProfiles.Batch124.profile4997,MergedCutProfiles.Batch124.profile4998,MergedCutProfiles.Batch124.profile4999,MergedCutProfiles.Batch125.profile5000,MergedCutProfiles.Batch125.profile5001,MergedCutProfiles.Batch125.profile5002,MergedCutProfiles.Batch125.profile5003,MergedCutProfiles.Batch125.profile5004,MergedCutProfiles.Batch125.profile5005,MergedCutProfiles.Batch125.profile5006,MergedCutProfiles.Batch125.profile5007,MergedCutProfiles.Batch125.profile5008,MergedCutProfiles.Batch125.profile5009,MergedCutProfiles.Batch125.profile5010,MergedCutProfiles.Batch125.profile5011,MergedCutProfiles.Batch125.profile5012]⟩
theorem profilesValid743 : retention743.ProfilesValid := by
  change ∀ j : Fin 16, (retention743.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch124.valid4997
  · exact MergedCutProfiles.Batch124.valid4998
  · exact MergedCutProfiles.Batch124.valid4999
  · exact MergedCutProfiles.Batch125.valid5000
  · exact MergedCutProfiles.Batch125.valid5001
  · exact MergedCutProfiles.Batch125.valid5002
  · exact MergedCutProfiles.Batch125.valid5003
  · exact MergedCutProfiles.Batch125.valid5004
  · exact MergedCutProfiles.Batch125.valid5005
  · exact MergedCutProfiles.Batch125.valid5006
  · exact MergedCutProfiles.Batch125.valid5007
  · exact MergedCutProfiles.Batch125.valid5008
  · exact MergedCutProfiles.Batch125.valid5009
  · exact MergedCutProfiles.Batch125.valid5010
  · exact MergedCutProfiles.Batch125.valid5011
  · exact MergedCutProfiles.Batch125.valid5012
theorem numericValid743 : retention743.NumericValid := by decide +kernel
def certificate743 : RatCutBinCertificate := ⟨⟨retention743,(426411054045357163/200000000000000000),(102941493058315297/1000000000000000000),(2515075777424674363/200000000000000000),(279916723399605254071/1000000000000000000),(204599783021330513/200000000000000000)⟩,(99315256850220439/100000000000000000),(60632485516824069/125000000000000000),(164007487250676113/1000000000000000000),(142306039326247691/1000000000000000000)⟩
theorem valid743 : certificate743.Valid := by decide +kernel
theorem sound743 : certificate743.Sound := rat_cut_bin_certificate_sound certificate743 profilesValid743 numericValid743 valid743

def certificates : List RatCutBinCertificate := [certificate732,certificate733,certificate734,certificate735,certificate736,certificate737,certificate738,certificate739,certificate740,certificate741,certificate742,certificate743]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound732,List.forall_mem_cons.mpr ⟨sound733,List.forall_mem_cons.mpr ⟨sound734,List.forall_mem_cons.mpr ⟨sound735,List.forall_mem_cons.mpr ⟨sound736,List.forall_mem_cons.mpr ⟨sound737,List.forall_mem_cons.mpr ⟨sound738,List.forall_mem_cons.mpr ⟨sound739,List.forall_mem_cons.mpr ⟨sound740,List.forall_mem_cons.mpr ⟨sound741,List.forall_mem_cons.mpr ⟨sound742,List.forall_mem_cons.mpr ⟨sound743,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch061
