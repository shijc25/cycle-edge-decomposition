import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch081
import Cycle12.MergedCutProfiles.Batch082
import Cycle12.MergedCutProfiles.Batch083
import Cycle12.MergedCutProfiles.Batch674
import Cycle12.MergedCutProfiles.Batch675
import Cycle12.MergedCutProfiles.Batch676

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch398

def retention4776 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(2000000000000000000/98467221350285359993),(1309200199226407579/250000000000000000),(6/5),(283927993610996602071813445452699154991/130920019922640757900000000000000000000),true,MergedCutProfiles.Batch674.profile26967,![MergedCutProfiles.Batch674.profile26967,MergedCutProfiles.Batch674.profile26972,MergedCutProfiles.Batch674.profile26973,MergedCutProfiles.Batch674.profile26974,MergedCutProfiles.Batch674.profile26975,MergedCutProfiles.Batch674.profile26976,MergedCutProfiles.Batch674.profile26977,MergedCutProfiles.Batch674.profile26978,MergedCutProfiles.Batch674.profile26979,MergedCutProfiles.Batch674.profile26980,MergedCutProfiles.Batch081.profile3268,MergedCutProfiles.Batch674.profile26981,MergedCutProfiles.Batch082.profile3284,MergedCutProfiles.Batch674.profile26982,MergedCutProfiles.Batch674.profile26983,MergedCutProfiles.Batch082.profile3286]⟩
theorem profilesValid4776 : retention4776.ProfilesValid := by
  change ∀ j : Fin 16, (retention4776.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch674.valid26967
  · exact MergedCutProfiles.Batch674.valid26972
  · exact MergedCutProfiles.Batch674.valid26973
  · exact MergedCutProfiles.Batch674.valid26974
  · exact MergedCutProfiles.Batch674.valid26975
  · exact MergedCutProfiles.Batch674.valid26976
  · exact MergedCutProfiles.Batch674.valid26977
  · exact MergedCutProfiles.Batch674.valid26978
  · exact MergedCutProfiles.Batch674.valid26979
  · exact MergedCutProfiles.Batch674.valid26980
  · exact MergedCutProfiles.Batch081.valid3268
  · exact MergedCutProfiles.Batch674.valid26981
  · exact MergedCutProfiles.Batch082.valid3284
  · exact MergedCutProfiles.Batch674.valid26982
  · exact MergedCutProfiles.Batch674.valid26983
  · exact MergedCutProfiles.Batch082.valid3286
theorem numericValid4776 : retention4776.NumericValid := by decide +kernel
def certificate4776 : RatCutBinCertificate := ⟨⟨retention4776,(1885537524495224577/1000000000000000000),(1140020255178431/15625000000000000),(5633066575666683359/500000000000000000),(35594456451166953387459/1000000000000000000),(2154060080359742261/1000000000000000000)⟩,(249987696843208519/250000000000000000),(57631091369783879/200000000000000000),(353274100313107371/1000000000000000000),(246611726853744351/500000000000000000)⟩
theorem valid4776 : certificate4776.Valid := by decide +kernel
theorem sound4776 : certificate4776.Sound := rat_cut_bin_certificate_sound certificate4776 profilesValid4776 numericValid4776 valid4776

def retention4777 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(1/2),64,1,(997592574846148187433561955338803151/1000000000000000000000000000000000000),false,MergedCutProfiles.Batch083.profile3339,(fun _ => MergedCutProfiles.Batch083.profile3339)⟩
theorem profilesValid4777 : retention4777.ProfilesValid := by
  exact MergedCutProfiles.Batch083.valid3339
theorem numericValid4777 : retention4777.NumericValid := by decide +kernel
def certificate4777 : RatCutBinCertificate := ⟨⟨retention4777,(1885537524495224577/1000000000000000000),(1140020255178431/15625000000000000),(5633066575666683359/500000000000000000),(35594456451166953387459/1000000000000000000),(985381529172632261/1000000000000000000)⟩,(249987696843208519/250000000000000000),(261302501562157649/500000000000000000),(69130624180724587/500000000000000000),(67083794762099517/500000000000000000)⟩
theorem valid4777 : certificate4777.Valid := by decide +kernel
theorem sound4777 : certificate4777.Sound := rat_cut_bin_certificate_sound certificate4777 profilesValid4777 numericValid4777 valid4777

def retention4778 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(2000000000000000000/98467221350285359993),(30216135628240838473/1000000000000000000),1,(13220003586795551376045589822137582249/6043227125648167694600000000000000000),false,MergedCutProfiles.Batch674.profile26984,(fun _ => MergedCutProfiles.Batch674.profile26984)⟩
theorem profilesValid4778 : retention4778.ProfilesValid := by
  exact MergedCutProfiles.Batch674.valid26984
theorem numericValid4778 : retention4778.NumericValid := by decide +kernel
def certificate4778 : RatCutBinCertificate := ⟨⟨retention4778,(1754132620495224577/1000000000000000000),(1140020255178431/15625000000000000),(5633066575666683359/500000000000000000),(35594456451166953387459/1000000000000000000),(1088106732632659621/500000000000000000)⟩,(124994277132455079/125000000000000000),(21011989618347333/1000000000000000000),(217733364798945011/250000000000000000),(883960099327003551/500000000000000000)⟩
theorem valid4778 : certificate4778.Valid := by decide +kernel
theorem sound4778 : certificate4778.Sound := rat_cut_bin_certificate_sound certificate4778 profilesValid4778 numericValid4778 valid4778

def retention4779 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(1/2),64,1,(997592574846148187433561955338803151/1000000000000000000000000000000000000),false,MergedCutProfiles.Batch083.profile3339,(fun _ => MergedCutProfiles.Batch083.profile3339)⟩
theorem profilesValid4779 : retention4779.ProfilesValid := by
  exact MergedCutProfiles.Batch083.valid3339
theorem numericValid4779 : retention4779.NumericValid := by decide +kernel
def certificate4779 : RatCutBinCertificate := ⟨⟨retention4779,(1754132620495224577/1000000000000000000),(1140020255178431/15625000000000000),(5633066575666683359/500000000000000000),(35594456451166953387459/1000000000000000000),(986232528563321947/1000000000000000000)⟩,(124994277132455079/125000000000000000),(92729804412503/2000000000000000),(79819071902872831/100000000000000000),(193804802014148479/250000000000000000)⟩
theorem valid4779 : certificate4779.Valid := by decide +kernel
theorem sound4779 : certificate4779.Sound := rat_cut_bin_certificate_sound certificate4779 profilesValid4779 numericValid4779 valid4779

def retention4780 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(689731254800024839/3150951083209131519776),(682902232475272117/1000000000000000000),4,(6520688963609643079118488516498704303/2731608929901088468000000000000000000),false,MergedCutProfiles.Batch674.profile26985,(fun _ => MergedCutProfiles.Batch674.profile26985)⟩
theorem profilesValid4780 : retention4780.ProfilesValid := by
  exact MergedCutProfiles.Batch674.valid26985
theorem numericValid4780 : retention4780.NumericValid := by decide +kernel
def certificate4780 : RatCutBinCertificate := ⟨⟨retention4780,(1832001907495224577/1000000000000000000),(1140020255178431/15625000000000000),(5633066575666683359/500000000000000000),(35594456451166953387459/1000000000000000000),(73114578281865689/31250000000000000)⟩,(999952184660319021/1000000000000000000),(218427578180971407/250000000000000000),(416659805609037/50000000000000000),(4014357356732921/1000000000000000000)⟩
theorem valid4780 : certificate4780.Valid := by decide +kernel
theorem sound4780 : certificate4780.Sound := rat_cut_bin_certificate_sound certificate4780 profilesValid4780 numericValid4780 valid4780

def retention4781 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(893378763410125111/3150951083209131519776),(689731254800024839/1000000000000000000),4,(329823262121512106832670178855872767/137946250960004967800000000000000000),false,MergedCutProfiles.Batch674.profile26986,(fun _ => MergedCutProfiles.Batch674.profile26986)⟩
theorem profilesValid4781 : retention4781.ProfilesValid := by
  exact MergedCutProfiles.Batch674.valid26986
theorem numericValid4781 : retention4781.NumericValid := by decide +kernel
def certificate4781 : RatCutBinCertificate := ⟨⟨retention4781,(1832001907495224577/1000000000000000000),(1140020255178431/15625000000000000),(5633066575666683359/500000000000000000),(35594456451166953387459/1000000000000000000),(292937185789990979/125000000000000000)⟩,(999952184660319021/1000000000000000000),(217510072800493151/250000000000000000),(8836391316729443/1000000000000000000),(4269967627963371/1000000000000000000)⟩
theorem valid4781 : certificate4781.Valid := by decide +kernel
theorem sound4781 : certificate4781.Sound := rat_cut_bin_certificate_sound certificate4781 profilesValid4781 numericValid4781 valid4781

def retention4782 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(6218755930005005039/3150951083209131519776),(893378763410125111/1000000000000000000),(18/5),(213859143524602090152885762278877676751/89337876341012511100000000000000000000),false,MergedCutProfiles.Batch674.profile26987,(fun _ => MergedCutProfiles.Batch674.profile26987)⟩
theorem profilesValid4782 : retention4782.ProfilesValid := by
  exact MergedCutProfiles.Batch674.valid26987
theorem numericValid4782 : retention4782.NumericValid := by decide +kernel
def certificate4782 : RatCutBinCertificate := ⟨⟨retention4782,(1832001907495224577/1000000000000000000),(1140020255178431/15625000000000000),(5633066575666683359/500000000000000000),(35594456451166953387459/1000000000000000000),(2351112248422662159/1000000000000000000)⟩,(999952184660319021/1000000000000000000),(408143468303110353/500000000000000000),(9007755244818627/500000000000000000),(611201773371767/62500000000000000)⟩
theorem valid4782 : certificate4782.Valid := by decide +kernel
theorem sound4782 : certificate4782.Sound := rat_cut_bin_certificate_sound certificate4782 profilesValid4782 numericValid4782 valid4782

def retention4783 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(1/40),(6218755930005005039/1000000000000000000),(13/10),(5464944554823144867875206875281667573511/2487502372002002015600000000000000000000),false,MergedCutProfiles.Batch674.profile26988,(fun _ => MergedCutProfiles.Batch674.profile26988)⟩
theorem profilesValid4783 : retention4783.ProfilesValid := by
  exact MergedCutProfiles.Batch674.valid26988
theorem numericValid4783 : retention4783.NumericValid := by decide +kernel
def certificate4783 : RatCutBinCertificate := ⟨⟨retention4783,(1832001907495224577/1000000000000000000),(1140020255178431/15625000000000000),(5633066575666683359/500000000000000000),(35594456451166953387459/1000000000000000000),(2181536894257615233/1000000000000000000)⟩,(999952184660319021/1000000000000000000),(360262744254781217/500000000000000000),(4330463838168613/100000000000000000),(1880476417172443/31250000000000000)⟩
theorem valid4783 : certificate4783.Valid := by decide +kernel
theorem sound4783 : certificate4783.Sound := rat_cut_bin_certificate_sound certificate4783 profilesValid4783 numericValid4783 valid4783

def retention4784 : RatCutRetentionCertificate := ⟨(1/25),(161/4000),(605351188993768403/3107746678209120739629),(581730594132313983/1000000000000000000),4,(260409469259455222979014504055451847/116346118826462796600000000000000000),true,MergedCutProfiles.Batch674.profile26989,![MergedCutProfiles.Batch674.profile26989,MergedCutProfiles.Batch674.profile26990,MergedCutProfiles.Batch674.profile26991,MergedCutProfiles.Batch674.profile26992,MergedCutProfiles.Batch674.profile26993,MergedCutProfiles.Batch674.profile26994,MergedCutProfiles.Batch674.profile26995,MergedCutProfiles.Batch674.profile26996,MergedCutProfiles.Batch674.profile26997,MergedCutProfiles.Batch674.profile26998,MergedCutProfiles.Batch674.profile26999,MergedCutProfiles.Batch675.profile27000,MergedCutProfiles.Batch675.profile27001,MergedCutProfiles.Batch675.profile27002,MergedCutProfiles.Batch675.profile27003,MergedCutProfiles.Batch675.profile27004]⟩
theorem profilesValid4784 : retention4784.ProfilesValid := by
  change ∀ j : Fin 16, (retention4784.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch674.valid26989
  · exact MergedCutProfiles.Batch674.valid26990
  · exact MergedCutProfiles.Batch674.valid26991
  · exact MergedCutProfiles.Batch674.valid26992
  · exact MergedCutProfiles.Batch674.valid26993
  · exact MergedCutProfiles.Batch674.valid26994
  · exact MergedCutProfiles.Batch674.valid26995
  · exact MergedCutProfiles.Batch674.valid26996
  · exact MergedCutProfiles.Batch674.valid26997
  · exact MergedCutProfiles.Batch674.valid26998
  · exact MergedCutProfiles.Batch674.valid26999
  · exact MergedCutProfiles.Batch675.valid27000
  · exact MergedCutProfiles.Batch675.valid27001
  · exact MergedCutProfiles.Batch675.valid27002
  · exact MergedCutProfiles.Batch675.valid27003
  · exact MergedCutProfiles.Batch675.valid27004
theorem numericValid4784 : retention4784.NumericValid := by decide +kernel
def certificate4784 : RatCutBinCertificate := ⟨⟨retention4784,(117979257409286751/62500000000000000),(73960994768012751/1000000000000000000),(5676341686360618027/500000000000000000),(35328760435458533561193/1000000000000000000),(1094519651413489133/500000000000000000)⟩,(199990093350531917/200000000000000000),(14107003696056679/20000000000000000),(9687931307287307/200000000000000000),(21460316216456273/1000000000000000000)⟩
theorem valid4784 : certificate4784.Valid := by decide +kernel
theorem sound4784 : certificate4784.Sound := rat_cut_bin_certificate_sound certificate4784 profilesValid4784 numericValid4784 valid4784

def retention4785 : RatCutRetentionCertificate := ⟨(1/25),(161/4000),(1158759331000000000/3107746678209120739629),(605351188993768403/1000000000000000000),4,(1825689065762498413/800000000000000000),true,MergedCutProfiles.Batch675.profile27005,![MergedCutProfiles.Batch675.profile27005,MergedCutProfiles.Batch675.profile27006,MergedCutProfiles.Batch674.profile26994,MergedCutProfiles.Batch675.profile27007,MergedCutProfiles.Batch674.profile26998,MergedCutProfiles.Batch675.profile27000,MergedCutProfiles.Batch675.profile27002,MergedCutProfiles.Batch675.profile27003,MergedCutProfiles.Batch675.profile27008,MergedCutProfiles.Batch675.profile27009,MergedCutProfiles.Batch675.profile27010,MergedCutProfiles.Batch675.profile27011,MergedCutProfiles.Batch675.profile27012,MergedCutProfiles.Batch675.profile27013,MergedCutProfiles.Batch675.profile27014,MergedCutProfiles.Batch675.profile27015]⟩
theorem profilesValid4785 : retention4785.ProfilesValid := by
  change ∀ j : Fin 16, (retention4785.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch675.valid27005
  · exact MergedCutProfiles.Batch675.valid27006
  · exact MergedCutProfiles.Batch674.valid26994
  · exact MergedCutProfiles.Batch675.valid27007
  · exact MergedCutProfiles.Batch674.valid26998
  · exact MergedCutProfiles.Batch675.valid27000
  · exact MergedCutProfiles.Batch675.valid27002
  · exact MergedCutProfiles.Batch675.valid27003
  · exact MergedCutProfiles.Batch675.valid27008
  · exact MergedCutProfiles.Batch675.valid27009
  · exact MergedCutProfiles.Batch675.valid27010
  · exact MergedCutProfiles.Batch675.valid27011
  · exact MergedCutProfiles.Batch675.valid27012
  · exact MergedCutProfiles.Batch675.valid27013
  · exact MergedCutProfiles.Batch675.valid27014
  · exact MergedCutProfiles.Batch675.valid27015
theorem numericValid4785 : retention4785.NumericValid := by decide +kernel
def certificate4785 : RatCutBinCertificate := ⟨⟨retention4785,(117979257409286751/62500000000000000),(73960994768012751/1000000000000000000),(5676341686360618027/500000000000000000),(35328760435458533561193/1000000000000000000),(1116459907026136511/500000000000000000)⟩,(199990093350531917/200000000000000000),(673358468354268823/1000000000000000000),(60343442483443613/1000000000000000000),(27372952342975611/1000000000000000000)⟩
theorem valid4785 : certificate4785.Valid := by decide +kernel
theorem sound4785 : certificate4785.Sound := rat_cut_bin_certificate_sound certificate4785 profilesValid4785 numericValid4785 valid4785

def retention4786 : RatCutRetentionCertificate := ⟨(1/25),(161/4000),(5969299504204841159/3107746678209120739629),(1158759331/1000000000),(11/4),(948390822166616551/400000000000000000),true,MergedCutProfiles.Batch674.profile26998,![MergedCutProfiles.Batch674.profile26998,MergedCutProfiles.Batch675.profile27009,MergedCutProfiles.Batch675.profile27014,MergedCutProfiles.Batch675.profile27016,MergedCutProfiles.Batch675.profile27017,MergedCutProfiles.Batch675.profile27018,MergedCutProfiles.Batch675.profile27019,MergedCutProfiles.Batch675.profile27020,MergedCutProfiles.Batch675.profile27021,MergedCutProfiles.Batch675.profile27022,MergedCutProfiles.Batch675.profile27023,MergedCutProfiles.Batch675.profile27024,MergedCutProfiles.Batch675.profile27025,MergedCutProfiles.Batch675.profile27026,MergedCutProfiles.Batch675.profile27027,MergedCutProfiles.Batch675.profile27028]⟩
theorem profilesValid4786 : retention4786.ProfilesValid := by
  change ∀ j : Fin 16, (retention4786.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch674.valid26998
  · exact MergedCutProfiles.Batch675.valid27009
  · exact MergedCutProfiles.Batch675.valid27014
  · exact MergedCutProfiles.Batch675.valid27016
  · exact MergedCutProfiles.Batch675.valid27017
  · exact MergedCutProfiles.Batch675.valid27018
  · exact MergedCutProfiles.Batch675.valid27019
  · exact MergedCutProfiles.Batch675.valid27020
  · exact MergedCutProfiles.Batch675.valid27021
  · exact MergedCutProfiles.Batch675.valid27022
  · exact MergedCutProfiles.Batch675.valid27023
  · exact MergedCutProfiles.Batch675.valid27024
  · exact MergedCutProfiles.Batch675.valid27025
  · exact MergedCutProfiles.Batch675.valid27026
  · exact MergedCutProfiles.Batch675.valid27027
  · exact MergedCutProfiles.Batch675.valid27028
theorem numericValid4786 : retention4786.NumericValid := by decide +kernel
def certificate4786 : RatCutBinCertificate := ⟨⟨retention4786,(117979257409286751/62500000000000000),(73960994768012751/1000000000000000000),(5676341686360618027/500000000000000000),(35328760435458533561193/1000000000000000000),(467431578741799177/200000000000000000)⟩,(199990093350531917/200000000000000000),(43958624902768337/100000000000000000),(3982160844536139/20000000000000000),(26716173469357771/200000000000000000)⟩
theorem valid4786 : certificate4786.Valid := by decide +kernel
theorem sound4786 : certificate4786.Sound := rat_cut_bin_certificate_sound certificate4786 profilesValid4786 numericValid4786 valid4786

def retention4787 : RatCutRetentionCertificate := ⟨(1/25),(161/4000),(64000000000000000000/3107746678209120739629),(5969299504204841159/1000000000000000000),(6/5),(2798385770152351057539/1280000000000000000000),true,MergedCutProfiles.Batch675.profile27029,![MergedCutProfiles.Batch675.profile27029,MergedCutProfiles.Batch675.profile27030,MergedCutProfiles.Batch675.profile27031,MergedCutProfiles.Batch675.profile27032,MergedCutProfiles.Batch675.profile27033,MergedCutProfiles.Batch675.profile27034,MergedCutProfiles.Batch675.profile27035,MergedCutProfiles.Batch675.profile27036,MergedCutProfiles.Batch675.profile27037,MergedCutProfiles.Batch675.profile27038,MergedCutProfiles.Batch675.profile27039,MergedCutProfiles.Batch676.profile27040,MergedCutProfiles.Batch676.profile27041,MergedCutProfiles.Batch676.profile27042,MergedCutProfiles.Batch676.profile27043,MergedCutProfiles.Batch676.profile27044]⟩
theorem profilesValid4787 : retention4787.ProfilesValid := by
  change ∀ j : Fin 16, (retention4787.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch675.valid27029
  · exact MergedCutProfiles.Batch675.valid27030
  · exact MergedCutProfiles.Batch675.valid27031
  · exact MergedCutProfiles.Batch675.valid27032
  · exact MergedCutProfiles.Batch675.valid27033
  · exact MergedCutProfiles.Batch675.valid27034
  · exact MergedCutProfiles.Batch675.valid27035
  · exact MergedCutProfiles.Batch675.valid27036
  · exact MergedCutProfiles.Batch675.valid27037
  · exact MergedCutProfiles.Batch675.valid27038
  · exact MergedCutProfiles.Batch675.valid27039
  · exact MergedCutProfiles.Batch676.valid27040
  · exact MergedCutProfiles.Batch676.valid27041
  · exact MergedCutProfiles.Batch676.valid27042
  · exact MergedCutProfiles.Batch676.valid27043
  · exact MergedCutProfiles.Batch676.valid27044
theorem numericValid4787 : retention4787.NumericValid := by decide +kernel
def certificate4787 : RatCutBinCertificate := ⟨⟨retention4787,(117979257409286751/62500000000000000),(73960994768012751/1000000000000000000),(5676341686360618027/500000000000000000),(35328760435458533561193/1000000000000000000),(16964698718221073/7812500000000000)⟩,(199990093350531917/200000000000000000),(279821088099755649/1000000000000000000),(72751630903397581/200000000000000000),(131366547427851687/250000000000000000)⟩
theorem valid4787 : certificate4787.Valid := by decide +kernel
theorem sound4787 : certificate4787.Sound := rat_cut_bin_certificate_sound certificate4787 profilesValid4787 numericValid4787 valid4787

def certificates : List RatCutBinCertificate := [certificate4776,certificate4777,certificate4778,certificate4779,certificate4780,certificate4781,certificate4782,certificate4783,certificate4784,certificate4785,certificate4786,certificate4787]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4776,List.forall_mem_cons.mpr ⟨sound4777,List.forall_mem_cons.mpr ⟨sound4778,List.forall_mem_cons.mpr ⟨sound4779,List.forall_mem_cons.mpr ⟨sound4780,List.forall_mem_cons.mpr ⟨sound4781,List.forall_mem_cons.mpr ⟨sound4782,List.forall_mem_cons.mpr ⟨sound4783,List.forall_mem_cons.mpr ⟨sound4784,List.forall_mem_cons.mpr ⟨sound4785,List.forall_mem_cons.mpr ⟨sound4786,List.forall_mem_cons.mpr ⟨sound4787,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch398
