import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch338
import Cycle12.MergedCutProfiles.Batch339
import Cycle12.MergedCutProfiles.Batch340
import Cycle12.MergedCutProfiles.Batch341
import Cycle12.MergedCutProfiles.Batch342
import Cycle12.MergedCutProfiles.Batch466
import Cycle12.MergedCutProfiles.Batch467
import Cycle12.MergedCutProfiles.Batch468
import Cycle12.MergedCutProfiles.Batch597
import Cycle12.MergedCutProfiles.Batch598
import Cycle12.MergedCutProfiles.Batch599

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch328

def retention3936 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(2119072937508961594/900307249488733784293),(145805360574488593/125000000000000000),(27/10),(11747832939002067023/5000000000000000000),true,MergedCutProfiles.Batch598.profile23933,![MergedCutProfiles.Batch598.profile23933,MergedCutProfiles.Batch598.profile23934,MergedCutProfiles.Batch597.profile23918,MergedCutProfiles.Batch598.profile23920,MergedCutProfiles.Batch466.profile18653,MergedCutProfiles.Batch340.profile13607,MergedCutProfiles.Batch338.profile13556,MergedCutProfiles.Batch598.profile23929,MergedCutProfiles.Batch598.profile23935,MergedCutProfiles.Batch466.profile18657,MergedCutProfiles.Batch598.profile23936,MergedCutProfiles.Batch598.profile23937,MergedCutProfiles.Batch339.profile13573,MergedCutProfiles.Batch466.profile18660,MergedCutProfiles.Batch466.profile18661,MergedCutProfiles.Batch598.profile23938]⟩
theorem profilesValid3936 : retention3936.ProfilesValid := by
  change ∀ j : Fin 16, (retention3936.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch598.valid23933
  · exact MergedCutProfiles.Batch598.valid23934
  · exact MergedCutProfiles.Batch597.valid23918
  · exact MergedCutProfiles.Batch598.valid23920
  · exact MergedCutProfiles.Batch466.valid18653
  · exact MergedCutProfiles.Batch340.valid13607
  · exact MergedCutProfiles.Batch338.valid13556
  · exact MergedCutProfiles.Batch598.valid23929
  · exact MergedCutProfiles.Batch598.valid23935
  · exact MergedCutProfiles.Batch466.valid18657
  · exact MergedCutProfiles.Batch598.valid23936
  · exact MergedCutProfiles.Batch598.valid23937
  · exact MergedCutProfiles.Batch339.valid13573
  · exact MergedCutProfiles.Batch466.valid18660
  · exact MergedCutProfiles.Batch466.valid18661
  · exact MergedCutProfiles.Batch598.valid23938
theorem numericValid3936 : retention3936.NumericValid := by decide +kernel
def certificate3936 : RatCutBinCertificate := ⟨⟨retention3936,(1846808941920205997/1000000000000000000),(51337219122942991/1000000000000000000),(10227353689100283593/1000000000000000000),(9255469691434617884019/1000000000000000000),(1162268446266404683/500000000000000000)⟩,(999810070437427249/1000000000000000000),(445864698725545563/1000000000000000000),(12124521667726511/62500000000000000),(131132103594314177/1000000000000000000)⟩
theorem valid3936 : certificate3936.Valid := by decide +kernel
theorem sound3936 : certificate3936.Sound := rat_cut_bin_certificate_sound certificate3936 profilesValid3936 numericValid3936 valid3936

def retention3937 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(64000000000000000000/900307249488733784293),(1059536468754480797/500000000000000000),(9/5),(421487793219965783540593035897634121199/211907293750896159400000000000000000000),false,MergedCutProfiles.Batch598.profile23939,(fun _ => MergedCutProfiles.Batch598.profile23939)⟩
theorem profilesValid3937 : retention3937.ProfilesValid := by
  exact MergedCutProfiles.Batch598.valid23939
theorem numericValid3937 : retention3937.NumericValid := by decide +kernel
def certificate3937 : RatCutBinCertificate := ⟨⟨retention3937,(1846808941920205997/1000000000000000000),(51337219122942991/1000000000000000000),(10227353689100283593/1000000000000000000),(9255469691434617884019/1000000000000000000),(1972333295294002029/1000000000000000000)⟩,(999810070437427249/1000000000000000000),(406035694843988041/1000000000000000000),(227997447022310987/1000000000000000000),(97016543289351281/500000000000000000)⟩
theorem valid3937 : certificate3937.Valid := by decide +kernel
theorem sound3937 : certificate3937.Sound := rat_cut_bin_certificate_sound certificate3937 profilesValid3937 numericValid3937 valid3937

def retention3938 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(1/2),64,1,(255378512847706981515811673095846818951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch340.profile13635,(fun _ => MergedCutProfiles.Batch340.profile13635)⟩
theorem profilesValid3938 : retention3938.ProfilesValid := by
  exact MergedCutProfiles.Batch340.valid13635
theorem numericValid3938 : retention3938.NumericValid := by decide +kernel
def certificate3938 : RatCutBinCertificate := ⟨⟨retention3938,(1846808941920205997/1000000000000000000),(51337219122942991/1000000000000000000),(10227353689100283593/1000000000000000000),(9255469691434617884019/1000000000000000000),(988302073828083117/1000000000000000000)⟩,(999810070437427249/1000000000000000000),(33006142171500099/62500000000000000),(134725277456160157/1000000000000000000),(26219857081017961/200000000000000000)⟩
theorem valid3938 : certificate3938.Valid := by decide +kernel
theorem sound3938 : certificate3938.Sound := rat_cut_bin_certificate_sound certificate3938 profilesValid3938 numericValid3938 valid3938

def retention3939 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(64000000000000000000/900307249488733784293),(11206161808415574559/500000000000000000),1,(35059272932322895185652140587809790363/17929858893464919294400000000000000000),false,MergedCutProfiles.Batch598.profile23939,(fun _ => MergedCutProfiles.Batch598.profile23939)⟩
theorem profilesValid3939 : retention3939.ProfilesValid := by
  exact MergedCutProfiles.Batch598.valid23939
theorem numericValid3939 : retention3939.NumericValid := by decide +kernel
def certificate3939 : RatCutBinCertificate := ⟨⟨retention3939,(1813444729920205997/1000000000000000000),(51337219122942991/1000000000000000000),(10227353689100283593/1000000000000000000),(9255469691434617884019/1000000000000000000),(243281763856768257/125000000000000000)⟩,(62488343857048081/62500000000000000),(31782428595448427/1000000000000000000),(8390892962977367/10000000000000000),(1502310330756359279/1000000000000000000)⟩
theorem valid3939 : certificate3939.Valid := by decide +kernel
theorem sound3939 : certificate3939.Sound := rat_cut_bin_certificate_sound certificate3939 profilesValid3939 numericValid3939 valid3939

def retention3940 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(1/2),64,1,(255378512847706981515811673095846818951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch340.profile13635,(fun _ => MergedCutProfiles.Batch340.profile13635)⟩
theorem profilesValid3940 : retention3940.ProfilesValid := by
  exact MergedCutProfiles.Batch340.valid13635
theorem numericValid3940 : retention3940.NumericValid := by decide +kernel
def certificate3940 : RatCutBinCertificate := ⟨⟨retention3940,(1813444729920205997/1000000000000000000),(51337219122942991/1000000000000000000),(10227353689100283593/1000000000000000000),(9255469691434617884019/1000000000000000000),(30889673400729929/31250000000000000)⟩,(62488343857048081/62500000000000000),(977784962819101/15625000000000000),(755454377869878081/1000000000000000000),(735247301934487237/1000000000000000000)⟩
theorem valid3940 : certificate3940.Valid := by decide +kernel
theorem sound3940 : certificate3940.Sound := rat_cut_bin_certificate_sound certificate3940 profilesValid3940 numericValid3940 valid3940

def retention3941 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(596454270276798350/845190195104070023853),(56750577239489553/100000000000000000),4,(14064885051624541761/6400000000000000000),true,MergedCutProfiles.Batch598.profile23940,![MergedCutProfiles.Batch598.profile23940,MergedCutProfiles.Batch598.profile23941,MergedCutProfiles.Batch598.profile23942,MergedCutProfiles.Batch598.profile23943,MergedCutProfiles.Batch598.profile23944,MergedCutProfiles.Batch598.profile23945,MergedCutProfiles.Batch598.profile23946,MergedCutProfiles.Batch598.profile23947,MergedCutProfiles.Batch467.profile18694,MergedCutProfiles.Batch598.profile23948,MergedCutProfiles.Batch468.profile18728,MergedCutProfiles.Batch340.profile13638,MergedCutProfiles.Batch467.profile18695,MergedCutProfiles.Batch598.profile23949,MergedCutProfiles.Batch598.profile23950,MergedCutProfiles.Batch598.profile23951]⟩
theorem profilesValid3941 : retention3941.ProfilesValid := by
  change ∀ j : Fin 16, (retention3941.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch598.valid23940
  · exact MergedCutProfiles.Batch598.valid23941
  · exact MergedCutProfiles.Batch598.valid23942
  · exact MergedCutProfiles.Batch598.valid23943
  · exact MergedCutProfiles.Batch598.valid23944
  · exact MergedCutProfiles.Batch598.valid23945
  · exact MergedCutProfiles.Batch598.valid23946
  · exact MergedCutProfiles.Batch598.valid23947
  · exact MergedCutProfiles.Batch467.valid18694
  · exact MergedCutProfiles.Batch598.valid23948
  · exact MergedCutProfiles.Batch468.valid18728
  · exact MergedCutProfiles.Batch340.valid13638
  · exact MergedCutProfiles.Batch467.valid18695
  · exact MergedCutProfiles.Batch598.valid23949
  · exact MergedCutProfiles.Batch598.valid23950
  · exact MergedCutProfiles.Batch598.valid23951
theorem numericValid3941 : retention3941.NumericValid := by decide +kernel
def certificate3941 : RatCutBinCertificate := ⟨⟨retention3941,(92651572632111689/50000000000000000),(853665110250683/15625000000000000),(5188675833094102109/500000000000000000),(8816557147355995766017/1000000000000000000),(1079307452122069249/500000000000000000)⟩,(999800611403979309/1000000000000000000),(183958632492397021/250000000000000000),(9612055345659351/250000000000000000),(261866698034147/15625000000000000)⟩
theorem valid3941 : certificate3941.Valid := by decide +kernel
theorem sound3941 : certificate3941.Sound := rat_cut_bin_certificate_sound certificate3941 profilesValid3941 numericValid3941 valid3941

def retention3942 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(1158615823000000000/845190195104070023853),(11929085405535967/20000000000000000),4,(4502373740468683671/2000000000000000000),true,MergedCutProfiles.Batch598.profile23952,![MergedCutProfiles.Batch598.profile23952,MergedCutProfiles.Batch598.profile23953,MergedCutProfiles.Batch598.profile23954,MergedCutProfiles.Batch468.profile18721,MergedCutProfiles.Batch598.profile23955,MergedCutProfiles.Batch598.profile23956,MergedCutProfiles.Batch598.profile23949,MergedCutProfiles.Batch341.profile13654,MergedCutProfiles.Batch598.profile23957,MergedCutProfiles.Batch598.profile23958,MergedCutProfiles.Batch467.profile18710,MergedCutProfiles.Batch342.profile13680,MergedCutProfiles.Batch598.profile23959,MergedCutProfiles.Batch467.profile18698,MergedCutProfiles.Batch599.profile23960,MergedCutProfiles.Batch341.profile13655]⟩
theorem profilesValid3942 : retention3942.ProfilesValid := by
  change ∀ j : Fin 16, (retention3942.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch598.valid23952
  · exact MergedCutProfiles.Batch598.valid23953
  · exact MergedCutProfiles.Batch598.valid23954
  · exact MergedCutProfiles.Batch468.valid18721
  · exact MergedCutProfiles.Batch598.valid23955
  · exact MergedCutProfiles.Batch598.valid23956
  · exact MergedCutProfiles.Batch598.valid23949
  · exact MergedCutProfiles.Batch341.valid13654
  · exact MergedCutProfiles.Batch598.valid23957
  · exact MergedCutProfiles.Batch598.valid23958
  · exact MergedCutProfiles.Batch467.valid18710
  · exact MergedCutProfiles.Batch342.valid13680
  · exact MergedCutProfiles.Batch598.valid23959
  · exact MergedCutProfiles.Batch467.valid18698
  · exact MergedCutProfiles.Batch599.valid23960
  · exact MergedCutProfiles.Batch341.valid13655
theorem numericValid3942 : retention3942.NumericValid := by decide +kernel
def certificate3942 : RatCutBinCertificate := ⟨⟨retention3942,(92651572632111689/50000000000000000),(853665110250683/15625000000000000),(5188675833094102109/500000000000000000),(8816557147355995766017/1000000000000000000),(276520436291548413/125000000000000000)⟩,(999800611403979309/1000000000000000000),(173610696584178969/250000000000000000),(13082943932534697/250000000000000000),(23489672770424957/1000000000000000000)⟩
theorem valid3942 : certificate3942.Valid := by decide +kernel
theorem sound3942 : certificate3942.Sound := rat_cut_bin_certificate_sound certificate3942 profilesValid3942 numericValid3942 valid3942

def retention3943 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(1729673560751184517/845190195104070023853),(1158615823/1000000000),(11/4),(9444655754195559397/4000000000000000000),true,MergedCutProfiles.Batch598.profile23942,![MergedCutProfiles.Batch598.profile23942,MergedCutProfiles.Batch598.profile23954,MergedCutProfiles.Batch467.profile18694,MergedCutProfiles.Batch598.profile23956,MergedCutProfiles.Batch467.profile18709,MergedCutProfiles.Batch598.profile23957,MergedCutProfiles.Batch599.profile23961,MergedCutProfiles.Batch342.profile13680,MergedCutProfiles.Batch599.profile23962,MergedCutProfiles.Batch599.profile23960,MergedCutProfiles.Batch467.profile18699,MergedCutProfiles.Batch467.profile18712,MergedCutProfiles.Batch599.profile23963,MergedCutProfiles.Batch467.profile18701,MergedCutProfiles.Batch599.profile23964,MergedCutProfiles.Batch341.profile13656]⟩
theorem profilesValid3943 : retention3943.ProfilesValid := by
  change ∀ j : Fin 16, (retention3943.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch598.valid23942
  · exact MergedCutProfiles.Batch598.valid23954
  · exact MergedCutProfiles.Batch467.valid18694
  · exact MergedCutProfiles.Batch598.valid23956
  · exact MergedCutProfiles.Batch467.valid18709
  · exact MergedCutProfiles.Batch598.valid23957
  · exact MergedCutProfiles.Batch599.valid23961
  · exact MergedCutProfiles.Batch342.valid13680
  · exact MergedCutProfiles.Batch599.valid23962
  · exact MergedCutProfiles.Batch599.valid23960
  · exact MergedCutProfiles.Batch467.valid18699
  · exact MergedCutProfiles.Batch467.valid18712
  · exact MergedCutProfiles.Batch599.valid23963
  · exact MergedCutProfiles.Batch467.valid18701
  · exact MergedCutProfiles.Batch599.valid23964
  · exact MergedCutProfiles.Batch341.valid13656
theorem numericValid3943 : retention3943.NumericValid := by decide +kernel
def certificate3943 : RatCutBinCertificate := ⟨⟨retention3943,(92651572632111689/50000000000000000),(853665110250683/15625000000000000),(5188675833094102109/500000000000000000),(8816557147355995766017/1000000000000000000),(1167167691185402581/500000000000000000)⟩,(999800611403979309/1000000000000000000),(89109639877889951/200000000000000000),(194248104839469791/1000000000000000000),(2033910816429277/15625000000000000)⟩
theorem valid3943 : certificate3943.Valid := by decide +kernel
theorem sound3943 : certificate3943.Sound := rat_cut_bin_certificate_sound certificate3943 profilesValid3943 numericValid3943 valid3943

def retention3944 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(64000000000000000000/845190195104070023853),(1729673560751184517/1000000000000000000),(41/20),(5481840084442161990717498835889936585151/2767477697201895227200000000000000000000),false,MergedCutProfiles.Batch599.profile23965,(fun _ => MergedCutProfiles.Batch599.profile23965)⟩
theorem profilesValid3944 : retention3944.ProfilesValid := by
  exact MergedCutProfiles.Batch599.valid23965
theorem numericValid3944 : retention3944.NumericValid := by decide +kernel
def certificate3944 : RatCutBinCertificate := ⟨⟨retention3944,(92651572632111689/50000000000000000),(853665110250683/15625000000000000),(5188675833094102109/500000000000000000),(8816557147355995766017/1000000000000000000),(392161571239808593/200000000000000000)⟩,(999800611403979309/1000000000000000000),(220892796615212027/500000000000000000),(39461174754573419/200000000000000000),(7429754562355289/50000000000000000)⟩
theorem valid3944 : certificate3944.Valid := by decide +kernel
theorem sound3944 : certificate3944.Sound := rat_cut_bin_certificate_sound certificate3944 profilesValid3944 numericValid3944 valid3944

def retention3945 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(1/2),64,1,(15961201781755751449307002574243876199/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch342.profile13711,(fun _ => MergedCutProfiles.Batch342.profile13711)⟩
theorem profilesValid3945 : retention3945.ProfilesValid := by
  exact MergedCutProfiles.Batch342.valid13711
theorem numericValid3945 : retention3945.NumericValid := by decide +kernel
def certificate3945 : RatCutBinCertificate := ⟨⟨retention3945,(92651572632111689/50000000000000000),(853665110250683/15625000000000000),(5188675833094102109/500000000000000000),(8816557147355995766017/1000000000000000000),(197563858155792941/200000000000000000)⟩,(999800611403979309/1000000000000000000),(16550356413527833/31250000000000000),(133761351346287491/1000000000000000000),(32524360616214567/250000000000000000)⟩
theorem valid3945 : certificate3945.Valid := by decide +kernel
theorem sound3945 : certificate3945.Sound := rat_cut_bin_certificate_sound certificate3945 profilesValid3945 numericValid3945 valid3945

def retention3946 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(64000000000000000000/845190195104070023853),(22496868987899232201/1000000000000000000),1,(8733918988603867925125698034525499149/4499373797579846440200000000000000000),false,MergedCutProfiles.Batch599.profile23965,(fun _ => MergedCutProfiles.Batch599.profile23965)⟩
theorem profilesValid3946 : retention3946.ProfilesValid := by
  exact MergedCutProfiles.Batch599.valid23965
theorem numericValid3946 : retention3946.NumericValid := by decide +kernel
def certificate3946 : RatCutBinCertificate := ⟨⟨retention3946,(90871388132111689/50000000000000000),(853665110250683/15625000000000000),(5188675833094102109/500000000000000000),(8816557147355995766017/1000000000000000000),(1931572631599969099/1000000000000000000)⟩,(199960888489580731/200000000000000000),(31963405530525413/1000000000000000000),(167713294709218053/200000000000000000),(1491378197985324777/1000000000000000000)⟩
theorem valid3946 : certificate3946.Valid := by decide +kernel
theorem sound3946 : certificate3946.Sound := rat_cut_bin_certificate_sound certificate3946 profilesValid3946 numericValid3946 valid3946

def retention3947 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(1/2),64,1,(15961201781755751449307002574243876199/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch342.profile13711,(fun _ => MergedCutProfiles.Batch342.profile13711)⟩
theorem profilesValid3947 : retention3947.ProfilesValid := by
  exact MergedCutProfiles.Batch342.valid13711
theorem numericValid3947 : retention3947.NumericValid := by decide +kernel
def certificate3947 : RatCutBinCertificate := ⟨⟨retention3947,(90871388132111689/50000000000000000),(853665110250683/15625000000000000),(5188675833094102109/500000000000000000),(8816557147355995766017/1000000000000000000),(988006736713116589/1000000000000000000)⟩,(199960888489580731/200000000000000000),(62489087413399957/1000000000000000000),(94460248696613461/125000000000000000),(367561488483614179/500000000000000000)⟩
theorem valid3947 : certificate3947.Valid := by decide +kernel
theorem sound3947 : certificate3947.Sound := rat_cut_bin_certificate_sound certificate3947 profilesValid3947 numericValid3947 valid3947

def certificates : List RatCutBinCertificate := [certificate3936,certificate3937,certificate3938,certificate3939,certificate3940,certificate3941,certificate3942,certificate3943,certificate3944,certificate3945,certificate3946,certificate3947]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3936,List.forall_mem_cons.mpr ⟨sound3937,List.forall_mem_cons.mpr ⟨sound3938,List.forall_mem_cons.mpr ⟨sound3939,List.forall_mem_cons.mpr ⟨sound3940,List.forall_mem_cons.mpr ⟨sound3941,List.forall_mem_cons.mpr ⟨sound3942,List.forall_mem_cons.mpr ⟨sound3943,List.forall_mem_cons.mpr ⟨sound3944,List.forall_mem_cons.mpr ⟨sound3945,List.forall_mem_cons.mpr ⟨sound3946,List.forall_mem_cons.mpr ⟨sound3947,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch328
