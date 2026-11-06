import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch043
import Cycle12.MergedCutProfiles.Batch044
import Cycle12.MergedCutProfiles.Batch332
import Cycle12.MergedCutProfiles.Batch462
import Cycle12.MergedCutProfiles.Batch463
import Cycle12.MergedCutProfiles.Batch594
import Cycle12.MergedCutProfiles.Batch595
import Cycle12.MergedCutProfiles.Batch654
import Cycle12.MergedCutProfiles.Batch655

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch382

def retention4584 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(636526989203438309/5901650656330354149808),(308903412305451663/500000000000000000),4,(1137411131690649951021953002625694643/494245459688722660800000000000000000),true,MergedCutProfiles.Batch654.profile26193,![MergedCutProfiles.Batch654.profile26193,MergedCutProfiles.Batch654.profile26194,MergedCutProfiles.Batch654.profile26195,MergedCutProfiles.Batch654.profile26196,MergedCutProfiles.Batch594.profile23776,MergedCutProfiles.Batch654.profile26197,MergedCutProfiles.Batch654.profile26198,MergedCutProfiles.Batch654.profile26199,MergedCutProfiles.Batch654.profile26199,MergedCutProfiles.Batch594.profile23777,MergedCutProfiles.Batch655.profile26200,MergedCutProfiles.Batch655.profile26201,MergedCutProfiles.Batch594.profile23778,MergedCutProfiles.Batch594.profile23778,MergedCutProfiles.Batch655.profile26202,MergedCutProfiles.Batch655.profile26203]⟩
theorem profilesValid4584 : retention4584.ProfilesValid := by
  change ∀ j : Fin 16, (retention4584.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch654.valid26193
  · exact MergedCutProfiles.Batch654.valid26194
  · exact MergedCutProfiles.Batch654.valid26195
  · exact MergedCutProfiles.Batch654.valid26196
  · exact MergedCutProfiles.Batch594.valid23776
  · exact MergedCutProfiles.Batch654.valid26197
  · exact MergedCutProfiles.Batch654.valid26198
  · exact MergedCutProfiles.Batch654.valid26199
  · exact MergedCutProfiles.Batch654.valid26199
  · exact MergedCutProfiles.Batch594.valid23777
  · exact MergedCutProfiles.Batch655.valid26200
  · exact MergedCutProfiles.Batch655.valid26201
  · exact MergedCutProfiles.Batch594.valid23778
  · exact MergedCutProfiles.Batch594.valid23778
  · exact MergedCutProfiles.Batch655.valid26202
  · exact MergedCutProfiles.Batch655.valid26203
theorem numericValid4584 : retention4584.NumericValid := by decide +kernel
def certificate4584 : RatCutBinCertificate := ⟨⟨retention4584,(1898490043119659533/1000000000000000000),(39310593322721927/1000000000000000000),(4829725965455099743/500000000000000000),(57295072897978197163157/1000000000000000000),(283800429087827969/125000000000000000)⟩,(124996009616996463/125000000000000000),(111888866040157503/200000000000000000),(14453012585981811/125000000000000000),(6671008876905447/125000000000000000)⟩
theorem valid4584 : certificate4584.Valid := by decide +kernel
theorem sound4584 : certificate4584.Sound := rat_cut_bin_certificate_sound certificate4584 profilesValid4584 numericValid4584 valid4584

def retention4585 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(77070441000000000/368853166020647134363),(636526989203438309/1000000000000000000),4,(5923154237631431651421355126915330527/2546107956813753236000000000000000000),true,MergedCutProfiles.Batch654.profile26194,![MergedCutProfiles.Batch654.profile26194,MergedCutProfiles.Batch654.profile26196,MergedCutProfiles.Batch655.profile26204,MergedCutProfiles.Batch654.profile26198,MergedCutProfiles.Batch594.profile23777,MergedCutProfiles.Batch655.profile26201,MergedCutProfiles.Batch594.profile23778,MergedCutProfiles.Batch655.profile26202,MergedCutProfiles.Batch594.profile23779,MergedCutProfiles.Batch594.profile23787,MergedCutProfiles.Batch462.profile18517,MergedCutProfiles.Batch594.profile23780,MergedCutProfiles.Batch655.profile26205,MergedCutProfiles.Batch594.profile23781,MergedCutProfiles.Batch594.profile23788,MergedCutProfiles.Batch655.profile26206]⟩
theorem profilesValid4585 : retention4585.ProfilesValid := by
  change ∀ j : Fin 16, (retention4585.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch654.valid26194
  · exact MergedCutProfiles.Batch654.valid26196
  · exact MergedCutProfiles.Batch655.valid26204
  · exact MergedCutProfiles.Batch654.valid26198
  · exact MergedCutProfiles.Batch594.valid23777
  · exact MergedCutProfiles.Batch655.valid26201
  · exact MergedCutProfiles.Batch594.valid23778
  · exact MergedCutProfiles.Batch655.valid26202
  · exact MergedCutProfiles.Batch594.valid23779
  · exact MergedCutProfiles.Batch594.valid23787
  · exact MergedCutProfiles.Batch462.valid18517
  · exact MergedCutProfiles.Batch594.valid23780
  · exact MergedCutProfiles.Batch655.valid26205
  · exact MergedCutProfiles.Batch594.valid23781
  · exact MergedCutProfiles.Batch594.valid23788
  · exact MergedCutProfiles.Batch655.valid26206
theorem numericValid4585 : retention4585.NumericValid := by decide +kernel
def certificate4585 : RatCutBinCertificate := ⟨⟨retention4585,(1898490043119659533/1000000000000000000),(39310593322721927/1000000000000000000),(4829725965455099743/500000000000000000),(57295072897978197163157/1000000000000000000),(2295451508980466131/1000000000000000000)⟩,(124996009616996463/125000000000000000),(21705779147491767/40000000000000000),(31409111971775487/250000000000000000),(11766943465040269/200000000000000000)⟩
theorem valid4585 : certificate4585.Valid := by decide +kernel
theorem sound4585 : certificate4585.Sound := rat_cut_bin_certificate_sound certificate4585 profilesValid4585 numericValid4585 valid4585

def retention4586 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(9252655025636718345/5901650656330354149808),(77070441/62500000),(51/20),(37535440217013698041/16000000000000000000),true,MergedCutProfiles.Batch655.profile26202,![MergedCutProfiles.Batch655.profile26202,MergedCutProfiles.Batch594.profile23788,MergedCutProfiles.Batch655.profile26207,MergedCutProfiles.Batch594.profile23789,MergedCutProfiles.Batch332.profile13295,MergedCutProfiles.Batch594.profile23792,MergedCutProfiles.Batch463.profile18521,MergedCutProfiles.Batch594.profile23797,MergedCutProfiles.Batch655.profile26208,MergedCutProfiles.Batch463.profile18529,MergedCutProfiles.Batch043.profile1735,MergedCutProfiles.Batch332.profile13307,MergedCutProfiles.Batch655.profile26209,MergedCutProfiles.Batch463.profile18538,MergedCutProfiles.Batch332.profile13287,MergedCutProfiles.Batch594.profile23798]⟩
theorem profilesValid4586 : retention4586.ProfilesValid := by
  change ∀ j : Fin 16, (retention4586.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch655.valid26202
  · exact MergedCutProfiles.Batch594.valid23788
  · exact MergedCutProfiles.Batch655.valid26207
  · exact MergedCutProfiles.Batch594.valid23789
  · exact MergedCutProfiles.Batch332.valid13295
  · exact MergedCutProfiles.Batch594.valid23792
  · exact MergedCutProfiles.Batch463.valid18521
  · exact MergedCutProfiles.Batch594.valid23797
  · exact MergedCutProfiles.Batch655.valid26208
  · exact MergedCutProfiles.Batch463.valid18529
  · exact MergedCutProfiles.Batch043.valid1735
  · exact MergedCutProfiles.Batch332.valid13307
  · exact MergedCutProfiles.Batch655.valid26209
  · exact MergedCutProfiles.Batch463.valid18538
  · exact MergedCutProfiles.Batch332.valid13287
  · exact MergedCutProfiles.Batch594.valid23798
theorem numericValid4586 : retention4586.NumericValid := by decide +kernel
def certificate4586 : RatCutBinCertificate := ⟨⟨retention4586,(1898490043119659533/1000000000000000000),(39310593322721927/1000000000000000000),(4829725965455099743/500000000000000000),(57295072897978197163157/1000000000000000000),(1163131611181342647/500000000000000000)⟩,(124996009616996463/125000000000000000),(183475528439125923/500000000000000000),(265167097941280529/1000000000000000000),(187496847566228661/1000000000000000000)⟩
theorem valid4586 : certificate4586.Valid := by decide +kernel
theorem sound4586 : certificate4586.Sound := rat_cut_bin_certificate_sound certificate4586 profilesValid4586 numericValid4586 valid4586

def retention4587 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(4000000000000000000/368853166020647134363),(1850531005127343669/200000000000000000),(21/20),(1298036606295344221176491977079630424671/592169921640749974080000000000000000000),false,MergedCutProfiles.Batch655.profile26210,(fun _ => MergedCutProfiles.Batch655.profile26210)⟩
theorem profilesValid4587 : retention4587.ProfilesValid := by
  exact MergedCutProfiles.Batch655.valid26210
theorem numericValid4587 : retention4587.NumericValid := by decide +kernel
def certificate4587 : RatCutBinCertificate := ⟨⟨retention4587,(1898490043119659533/1000000000000000000),(39310593322721927/1000000000000000000),(4829725965455099743/500000000000000000),(57295072897978197163157/1000000000000000000),(54597193301965929/25000000000000000)⟩,(124996009616996463/125000000000000000),(56223082418750971/250000000000000000),(219689106574841391/500000000000000000),(752689852187120683/1000000000000000000)⟩
theorem valid4587 : certificate4587.Valid := by decide +kernel
theorem sound4587 : certificate4587.Sound := rat_cut_bin_certificate_sound certificate4587 profilesValid4587 numericValid4587 valid4587

def retention4588 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(1/2),64,1,(255375917609544558015305480512676517159/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch044.profile1794,(fun _ => MergedCutProfiles.Batch044.profile1794)⟩
theorem profilesValid4588 : retention4588.ProfilesValid := by
  exact MergedCutProfiles.Batch044.valid1794
theorem numericValid4588 : retention4588.NumericValid := by decide +kernel
def certificate4588 : RatCutBinCertificate := ⟨⟨retention4588,(1898490043119659533/1000000000000000000),(39310593322721927/1000000000000000000),(4829725965455099743/500000000000000000),(57295072897978197163157/1000000000000000000),(989835987137555633/1000000000000000000)⟩,(124996009616996463/125000000000000000),(224006823359133063/500000000000000000),(96130873958313803/500000000000000000),(3748061158488257/20000000000000000)⟩
theorem valid4588 : certificate4588.Valid := by decide +kernel
theorem sound4588 : certificate4588.Sound := rat_cut_bin_certificate_sound certificate4588 profilesValid4588 numericValid4588 valid4588

def retention4589 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(4000000000000000000/368853166020647134363),(5584342271231188367/250000000000000000),1,(198635009571981716975263651694044179087/89349476339699013872000000000000000000),false,MergedCutProfiles.Batch655.profile26210,(fun _ => MergedCutProfiles.Batch655.profile26210)⟩
theorem profilesValid4589 : retention4589.ProfilesValid := by
  exact MergedCutProfiles.Batch655.valid26210
theorem numericValid4589 : retention4589.NumericValid := by decide +kernel
def certificate4589 : RatCutBinCertificate := ⟨⟨retention4589,(1750560143119659533/1000000000000000000),(39310593322721927/1000000000000000000),(4829725965455099743/500000000000000000),(57295072897978197163157/1000000000000000000),(2216000328013716157/1000000000000000000)⟩,(249992641094108193/250000000000000000),(6139743893209661/250000000000000000),(34411410185066749/40000000000000000),(1734283598580202613/1000000000000000000)⟩
theorem valid4589 : certificate4589.Valid := by decide +kernel
theorem sound4589 : certificate4589.Sound := rat_cut_bin_certificate_sound certificate4589 profilesValid4589 numericValid4589 valid4589

def retention4590 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(1/2),64,1,(255375917609544558015305480512676517159/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch044.profile1794,(fun _ => MergedCutProfiles.Batch044.profile1794)⟩
theorem profilesValid4590 : retention4590.ProfilesValid := by
  exact MergedCutProfiles.Batch044.valid1794
theorem numericValid4590 : retention4590.NumericValid := by decide +kernel
def certificate4590 : RatCutBinCertificate := ⟨⟨retention4590,(1750560143119659533/1000000000000000000),(39310593322721927/1000000000000000000),(4829725965455099743/500000000000000000),(57295072897978197163157/1000000000000000000),(990438010134626913/1000000000000000000)⟩,(249992641094108193/250000000000000000),(27474055603789773/500000000000000000),(775225016913219331/1000000000000000000),(756088587873538821/1000000000000000000)⟩
theorem valid4590 : certificate4590.Valid := by decide +kernel
theorem sound4590 : certificate4590.Sound := rat_cut_bin_certificate_sound certificate4590 profilesValid4590 numericValid4590 valid4590

def retention4591 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(678265901493785141/5901650656330354149808),(671550397518599149/1000000000000000000),4,(397908922654357100421029073080281897/167887599379649787250000000000000000),false,MergedCutProfiles.Batch655.profile26211,(fun _ => MergedCutProfiles.Batch655.profile26211)⟩
theorem profilesValid4591 : retention4591.ProfilesValid := by
  exact MergedCutProfiles.Batch655.valid26211
theorem numericValid4591 : retention4591.NumericValid := by decide +kernel
def certificate4591 : RatCutBinCertificate := ⟨⟨retention4591,(1790898092119659533/1000000000000000000),(39310593322721927/1000000000000000000),(4829725965455099743/500000000000000000),(57295072897978197163157/1000000000000000000),(2340937879951548893/1000000000000000000)⟩,(99996988609408711/100000000000000000),(858709040132526183/1000000000000000000),(10487990551533587/1000000000000000000),(2519862644388681/500000000000000000)⟩
theorem valid4591 : certificate4591.Valid := by decide +kernel
theorem sound4591 : certificate4591.Sound := rat_cut_bin_certificate_sound certificate4591 profilesValid4591 numericValid4591 valid4591

def retention4592 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(1050849279344105155/5901650656330354149808),(678265901493785141/1000000000000000000),4,(1288067042154068625605153485995326907/542612721195028112800000000000000000),false,MergedCutProfiles.Batch655.profile26212,(fun _ => MergedCutProfiles.Batch655.profile26212)⟩
theorem profilesValid4592 : retention4592.ProfilesValid := by
  exact MergedCutProfiles.Batch655.valid26212
theorem numericValid4592 : retention4592.NumericValid := by decide +kernel
def certificate4592 : RatCutBinCertificate := ⟨⟨retention4592,(1790898092119659533/1000000000000000000),(39310593322721927/1000000000000000000),(4829725965455099743/500000000000000000),(57295072897978197163157/1000000000000000000),(36635477629487803/15625000000000000)⟩,(99996988609408711/100000000000000000),(427464571406910343/500000000000000000),(11072095395573729/1000000000000000000),(5336830527176109/1000000000000000000)⟩
theorem valid4592 : certificate4592.Valid := by decide +kernel
theorem sound4592 : certificate4592.Sound := rat_cut_bin_certificate_sound certificate4592 profilesValid4592 numericValid4592 valid4592

def retention4593 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(5096239464432012245/1475412664082588537452),(210169855868821031/200000000000000000),(63/20),(158372796914023622296211825371966383311/67254353878022729920000000000000000000),false,MergedCutProfiles.Batch655.profile26213,(fun _ => MergedCutProfiles.Batch655.profile26213)⟩
theorem profilesValid4593 : retention4593.ProfilesValid := by
  exact MergedCutProfiles.Batch655.valid26213
theorem numericValid4593 : retention4593.NumericValid := by decide +kernel
def certificate4593 : RatCutBinCertificate := ⟨⟨retention4593,(1790898092119659533/1000000000000000000),(39310593322721927/1000000000000000000),(4829725965455099743/500000000000000000),(57295072897978197163157/1000000000000000000),(29148439122215337/12500000000000000)⟩,(99996988609408711/100000000000000000),(193400613762208753/250000000000000000),(13907995378701263/500000000000000000),(4206894659590419/250000000000000000)⟩
theorem valid4593 : certificate4593.Valid := by decide +kernel
theorem sound4593 : certificate4593.Sound := rat_cut_bin_certificate_sound certificate4593 profilesValid4593 numericValid4593 valid4593

def retention4594 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(1/40),(1019247892886402449/50000000000000000),(11/10),(11156865519648043362658078566142291861/5096239464432012245000000000000000000),false,MergedCutProfiles.Batch655.profile26214,(fun _ => MergedCutProfiles.Batch655.profile26214)⟩
theorem profilesValid4594 : retention4594.ProfilesValid := by
  exact MergedCutProfiles.Batch655.valid26214
theorem numericValid4594 : retention4594.NumericValid := by decide +kernel
def certificate4594 : RatCutBinCertificate := ⟨⟨retention4594,(1790898092119659533/1000000000000000000),(39310593322721927/1000000000000000000),(4829725965455099743/500000000000000000),(57295072897978197163157/1000000000000000000),(2181217781738889461/1000000000000000000)⟩,(99996988609408711/100000000000000000),(668259107072369181/1000000000000000000),(62379482590019663/1000000000000000000),(22728138161149347/200000000000000000)⟩
theorem valid4594 : certificate4594.Valid := by decide +kernel
theorem sound4594 : certificate4594.Sound := rat_cut_bin_certificate_sound certificate4594 profilesValid4594 numericValid4594 valid4594

def retention4595 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(586442270897867269/5499057042738006065942),(35930440085400161/62500000000000000),4,(142012668510035111/64000000000000000),true,MergedCutProfiles.Batch655.profile26215,![MergedCutProfiles.Batch655.profile26215,MergedCutProfiles.Batch655.profile26216,MergedCutProfiles.Batch655.profile26217,MergedCutProfiles.Batch655.profile26218,MergedCutProfiles.Batch595.profile23816,MergedCutProfiles.Batch655.profile26219,MergedCutProfiles.Batch655.profile26220,MergedCutProfiles.Batch655.profile26221,MergedCutProfiles.Batch655.profile26222,MergedCutProfiles.Batch595.profile23817,MergedCutProfiles.Batch655.profile26223,MergedCutProfiles.Batch655.profile26224,MergedCutProfiles.Batch595.profile23831,MergedCutProfiles.Batch595.profile23831,MergedCutProfiles.Batch595.profile23818,MergedCutProfiles.Batch655.profile26225]⟩
theorem profilesValid4595 : retention4595.ProfilesValid := by
  change ∀ j : Fin 16, (retention4595.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch655.valid26215
  · exact MergedCutProfiles.Batch655.valid26216
  · exact MergedCutProfiles.Batch655.valid26217
  · exact MergedCutProfiles.Batch655.valid26218
  · exact MergedCutProfiles.Batch595.valid23816
  · exact MergedCutProfiles.Batch655.valid26219
  · exact MergedCutProfiles.Batch655.valid26220
  · exact MergedCutProfiles.Batch655.valid26221
  · exact MergedCutProfiles.Batch655.valid26222
  · exact MergedCutProfiles.Batch595.valid23817
  · exact MergedCutProfiles.Batch655.valid26223
  · exact MergedCutProfiles.Batch655.valid26224
  · exact MergedCutProfiles.Batch595.valid23831
  · exact MergedCutProfiles.Batch595.valid23831
  · exact MergedCutProfiles.Batch595.valid23818
  · exact MergedCutProfiles.Batch655.valid26225
theorem numericValid4595 : retention4595.NumericValid := by decide +kernel
def certificate4595 : RatCutBinCertificate := ⟨⟨retention4595,(929398518179652177/500000000000000000),(42146381475855499/1000000000000000000),(9796801993206856219/1000000000000000000),(54147318024800195909169/1000000000000000000),(2186961345943272443/1000000000000000000)⟩,(999967020914476037/1000000000000000000),(33948075680553889/50000000000000000),(1817212864021681/31250000000000000),(12842608201602539/500000000000000000)⟩
theorem valid4595 : certificate4595.Valid := by decide +kernel
theorem sound4595 : certificate4595.Sound := rat_cut_bin_certificate_sound certificate4595 profilesValid4595 numericValid4595 valid4595

def certificates : List RatCutBinCertificate := [certificate4584,certificate4585,certificate4586,certificate4587,certificate4588,certificate4589,certificate4590,certificate4591,certificate4592,certificate4593,certificate4594,certificate4595]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4584,List.forall_mem_cons.mpr ⟨sound4585,List.forall_mem_cons.mpr ⟨sound4586,List.forall_mem_cons.mpr ⟨sound4587,List.forall_mem_cons.mpr ⟨sound4588,List.forall_mem_cons.mpr ⟨sound4589,List.forall_mem_cons.mpr ⟨sound4590,List.forall_mem_cons.mpr ⟨sound4591,List.forall_mem_cons.mpr ⟨sound4592,List.forall_mem_cons.mpr ⟨sound4593,List.forall_mem_cons.mpr ⟨sound4594,List.forall_mem_cons.mpr ⟨sound4595,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch382
