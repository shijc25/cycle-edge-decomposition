import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch001
import Cycle12.MergedCutProfiles.Batch002
import Cycle12.MergedCutProfiles.Batch003
import Cycle12.MergedCutProfiles.Batch307

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch161

def retention1932 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(1/2),64,1,(10216831075443792460644374972913285751/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch307.profile12294,(fun _ => MergedCutProfiles.Batch307.profile12294)⟩
theorem profilesValid1932 : retention1932.ProfilesValid := by
  exact MergedCutProfiles.Batch307.valid12294
theorem numericValid1932 : retention1932.NumericValid := by decide +kernel
def certificate1932 : RatCutBinCertificate := ⟨⟨retention1932,(2428078689874166461/1000000000000000000),(123364672097640231/500000000000000000),(4570958873971526223/250000000000000000),(84787762377982862633/500000000000000000),(241242801447675407/250000000000000000)⟩,(494555334263642661/500000000000000000),(376452138624285517/1000000000000000000),(25576482653065223/100000000000000000),(120232314490644927/500000000000000000)⟩
theorem valid1932 : certificate1932.Valid := by decide +kernel
theorem sound1932 : certificate1932.Sound := rat_cut_bin_certificate_sound certificate1932 profilesValid1932 numericValid1932 valid1932

def retention1933 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(4248944029786685312/9244737841268092559),(339413571042567119/125000000000000000),(5/4),(2900154368393830670622361092044750719/2715308568340536952000000000000000000),false,MergedCutProfiles.Batch307.profile12295,(fun _ => MergedCutProfiles.Batch307.profile12295)⟩
theorem profilesValid1933 : retention1933.ProfilesValid := by
  exact MergedCutProfiles.Batch307.valid12295
theorem numericValid1933 : retention1933.NumericValid := by decide +kernel
def certificate1933 : RatCutBinCertificate := ⟨⟨retention1933,(2741768944874166461/1000000000000000000),(123364672097640231/500000000000000000),(4570958873971526223/250000000000000000),(84787762377982862633/500000000000000000),(4087229820604699/4000000000000000)⟩,(246924579054738633/250000000000000000),(365209202018211713/1000000000000000000),(133458655008871341/500000000000000000),(173372034345011033/1000000000000000000)⟩
theorem valid1933 : certificate1933.Valid := by decide +kernel
theorem sound1933 : certificate1933.Sound := rat_cut_bin_certificate_sound certificate1933 profilesValid1933 numericValid1933 valid1933

def retention1934 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(4555443103458325846/9244737841268092559),(33194875232708479/7812500000000000),(11/10),(105756763200218099413693770524899930231/106223600744667132800000000000000000000),false,MergedCutProfiles.Batch307.profile12296,(fun _ => MergedCutProfiles.Batch307.profile12296)⟩
theorem profilesValid1934 : retention1934.ProfilesValid := by
  exact MergedCutProfiles.Batch307.valid12296
theorem numericValid1934 : retention1934.NumericValid := by decide +kernel
def certificate1934 : RatCutBinCertificate := ⟨⟨retention1934,(2741768944874166461/1000000000000000000),(123364672097640231/500000000000000000),(4570958873971526223/250000000000000000),(84787762377982862633/500000000000000000),(477447050672022749/500000000000000000)⟩,(246924579054738633/250000000000000000),(3053132122082029/7812500000000000),(121008786552400737/500000000000000000),(174769385511768979/1000000000000000000)⟩
theorem valid1934 : certificate1934.Valid := by decide +kernel
theorem sound1934 : certificate1934.Sound := rat_cut_bin_certificate_sound certificate1934 profilesValid1934 numericValid1934 valid1934

def retention1935 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(4600997534492909105/9244737841268092559),(2277721551729162923/500000000000000000),(11/10),(56353301210729240039318237841063666557/56943038793229073075000000000000000000),false,MergedCutProfiles.Batch307.profile12297,(fun _ => MergedCutProfiles.Batch307.profile12297)⟩
theorem profilesValid1935 : retention1935.ProfilesValid := by
  exact MergedCutProfiles.Batch307.valid12297
theorem numericValid1935 : retention1935.NumericValid := by decide +kernel
def certificate1935 : RatCutBinCertificate := ⟨⟨retention1935,(2741768944874166461/1000000000000000000),(123364672097640231/500000000000000000),(4570958873971526223/250000000000000000),(84787762377982862633/500000000000000000),(948933187910146329/1000000000000000000)⟩,(246924579054738633/250000000000000000),(196627902820991683/500000000000000000),(59929720059809583/250000000000000000),(174034668171867047/1000000000000000000)⟩
theorem valid1935 : certificate1935.Valid := by decide +kernel
theorem sound1935 : certificate1935.Sound := rat_cut_bin_certificate_sound certificate1935 profilesValid1935 numericValid1935 valid1935

def retention1936 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(1/2),(920199506898581821/200000000000000000),(11/10),(72564778361124776579028790708846299319/73615960551886545680000000000000000000),false,MergedCutProfiles.Batch307.profile12294,(fun _ => MergedCutProfiles.Batch307.profile12294)⟩
theorem profilesValid1936 : retention1936.ProfilesValid := by
  exact MergedCutProfiles.Batch307.valid12294
theorem numericValid1936 : retention1936.NumericValid := by decide +kernel
def certificate1936 : RatCutBinCertificate := ⟨⟨retention1936,(2741768944874166461/1000000000000000000),(123364672097640231/500000000000000000),(4570958873971526223/250000000000000000),(84787762377982862633/500000000000000000),(472505328838160969/500000000000000000)⟩,(246924579054738633/250000000000000000),(394888123515572887/1000000000000000000),(238198908014876693/1000000000000000000),(17257273551239277/100000000000000000)⟩
theorem valid1936 : certificate1936.Valid := by decide +kernel
theorem sound1936 : certificate1936.Sound := rat_cut_bin_certificate_sound certificate1936 profilesValid1936 numericValid1936 valid1936

def retention1937 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(583079676171607343/7501601891668384415235),(35724418940030839/62500000000000000),4,(15735161829267206858599946746285803/7144883788006167800000000000000000),true,MergedCutProfiles.Batch307.profile12298,![MergedCutProfiles.Batch307.profile12298,MergedCutProfiles.Batch001.profile71,MergedCutProfiles.Batch307.profile12299,MergedCutProfiles.Batch001.profile72,MergedCutProfiles.Batch307.profile12300,MergedCutProfiles.Batch001.profile73,MergedCutProfiles.Batch001.profile73,MergedCutProfiles.Batch001.profile74,MergedCutProfiles.Batch002.profile86,MergedCutProfiles.Batch001.profile75,MergedCutProfiles.Batch001.profile75,MergedCutProfiles.Batch001.profile76,MergedCutProfiles.Batch001.profile77,MergedCutProfiles.Batch001.profile77,MergedCutProfiles.Batch307.profile12301,MergedCutProfiles.Batch001.profile78]⟩
theorem profilesValid1937 : retention1937.ProfilesValid := by
  change ∀ j : Fin 16, (retention1937.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch307.valid12298
  · exact MergedCutProfiles.Batch001.valid71
  · exact MergedCutProfiles.Batch307.valid12299
  · exact MergedCutProfiles.Batch001.valid72
  · exact MergedCutProfiles.Batch307.valid12300
  · exact MergedCutProfiles.Batch001.valid73
  · exact MergedCutProfiles.Batch001.valid73
  · exact MergedCutProfiles.Batch001.valid74
  · exact MergedCutProfiles.Batch002.valid86
  · exact MergedCutProfiles.Batch001.valid75
  · exact MergedCutProfiles.Batch001.valid75
  · exact MergedCutProfiles.Batch001.valid76
  · exact MergedCutProfiles.Batch001.valid77
  · exact MergedCutProfiles.Batch001.valid77
  · exact MergedCutProfiles.Batch307.valid12301
  · exact MergedCutProfiles.Batch001.valid78
theorem numericValid1937 : retention1937.NumericValid := by decide +kernel
def certificate1937 : RatCutBinCertificate := ⟨⟨retention1937,(450089143465335109/250000000000000000),(637434242080419/1000000000000000000),(6917663821593591299/1000000000000000000),(2605974078352198744117/50000000000000000),(1100817107823660611/500000000000000000)⟩,(199993093895002323/200000000000000000),(580530110494939907/1000000000000000000),(103769712569261853/1000000000000000000),(46031875033015989/1000000000000000000)⟩
theorem valid1937 : certificate1937.Valid := by decide +kernel
theorem sound1937 : certificate1937.Sound := rat_cut_bin_certificate_sound certificate1937 profilesValid1937 numericValid1937 valid1937

def retention1938 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(263618383600000000/1500320378333676883047),(583079676171607343/1000000000000000000),4,(569400181575688732383/256000000000000000000),true,MergedCutProfiles.Batch001.profile71,![MergedCutProfiles.Batch001.profile71,MergedCutProfiles.Batch001.profile72,MergedCutProfiles.Batch001.profile73,MergedCutProfiles.Batch002.profile86,MergedCutProfiles.Batch001.profile76,MergedCutProfiles.Batch001.profile77,MergedCutProfiles.Batch307.profile12301,MergedCutProfiles.Batch001.profile79,MergedCutProfiles.Batch002.profile80,MergedCutProfiles.Batch002.profile81,MergedCutProfiles.Batch002.profile82,MergedCutProfiles.Batch002.profile83,MergedCutProfiles.Batch002.profile84,MergedCutProfiles.Batch002.profile85,MergedCutProfiles.Batch307.profile12302,MergedCutProfiles.Batch002.profile87]⟩
theorem profilesValid1938 : retention1938.ProfilesValid := by
  change ∀ j : Fin 16, (retention1938.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch001.valid71
  · exact MergedCutProfiles.Batch001.valid72
  · exact MergedCutProfiles.Batch001.valid73
  · exact MergedCutProfiles.Batch002.valid86
  · exact MergedCutProfiles.Batch001.valid76
  · exact MergedCutProfiles.Batch001.valid77
  · exact MergedCutProfiles.Batch307.valid12301
  · exact MergedCutProfiles.Batch001.valid79
  · exact MergedCutProfiles.Batch002.valid80
  · exact MergedCutProfiles.Batch002.valid81
  · exact MergedCutProfiles.Batch002.valid82
  · exact MergedCutProfiles.Batch002.valid83
  · exact MergedCutProfiles.Batch002.valid84
  · exact MergedCutProfiles.Batch002.valid85
  · exact MergedCutProfiles.Batch307.valid12302
  · exact MergedCutProfiles.Batch002.valid87
theorem numericValid1938 : retention1938.NumericValid := by decide +kernel
def certificate1938 : RatCutBinCertificate := ⟨⟨retention1938,(450089143465335109/250000000000000000),(637434242080419/1000000000000000000),(6917663821593591299/1000000000000000000),(2605974078352198744117/50000000000000000),(2223555877490719993/1000000000000000000)⟩,(199993093895002323/200000000000000000),(566999488739783467/1000000000000000000),(5564338407829477/50000000000000000),(12488583713956057/250000000000000000)⟩
theorem valid1938 : certificate1938.Valid := by decide +kernel
theorem sound1938 : certificate1938.Sound := rat_cut_bin_certificate_sound certificate1938 profilesValid1938 numericValid1938 valid1938

def retention1939 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(1200654495839226301/2500533963889461471745),(659045959/500000000),(12/5),(37422977860574267637/16000000000000000000),true,MergedCutProfiles.Batch001.profile73,![MergedCutProfiles.Batch001.profile73,MergedCutProfiles.Batch001.profile76,MergedCutProfiles.Batch001.profile79,MergedCutProfiles.Batch002.profile82,MergedCutProfiles.Batch002.profile85,MergedCutProfiles.Batch002.profile87,MergedCutProfiles.Batch002.profile96,MergedCutProfiles.Batch002.profile90,MergedCutProfiles.Batch002.profile91,MergedCutProfiles.Batch002.profile93,MergedCutProfiles.Batch002.profile94,MergedCutProfiles.Batch002.profile95,MergedCutProfiles.Batch307.profile12303,MergedCutProfiles.Batch307.profile12304,MergedCutProfiles.Batch307.profile12305,MergedCutProfiles.Batch002.profile100]⟩
theorem profilesValid1939 : retention1939.ProfilesValid := by
  change ∀ j : Fin 16, (retention1939.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch001.valid73
  · exact MergedCutProfiles.Batch001.valid76
  · exact MergedCutProfiles.Batch001.valid79
  · exact MergedCutProfiles.Batch002.valid82
  · exact MergedCutProfiles.Batch002.valid85
  · exact MergedCutProfiles.Batch002.valid87
  · exact MergedCutProfiles.Batch002.valid96
  · exact MergedCutProfiles.Batch002.valid90
  · exact MergedCutProfiles.Batch002.valid91
  · exact MergedCutProfiles.Batch002.valid93
  · exact MergedCutProfiles.Batch002.valid94
  · exact MergedCutProfiles.Batch002.valid95
  · exact MergedCutProfiles.Batch307.valid12303
  · exact MergedCutProfiles.Batch307.valid12304
  · exact MergedCutProfiles.Batch307.valid12305
  · exact MergedCutProfiles.Batch002.valid100
theorem numericValid1939 : retention1939.NumericValid := by decide +kernel
def certificate1939 : RatCutBinCertificate := ⟨⟨retention1939,(450089143465335109/250000000000000000),(637434242080419/1000000000000000000),(6917663821593591299/1000000000000000000),(2605974078352198744117/50000000000000000),(1169268983606425887/500000000000000000)⟩,(199993093895002323/200000000000000000),(166586939741525549/500000000000000000),(3757855863410191/12500000000000000),(27992554642664877/125000000000000000)⟩
theorem valid1939 : certificate1939.Valid := by decide +kernel
theorem sound1939 : certificate1939.Sound := rat_cut_bin_certificate_sound certificate1939 profilesValid1939 numericValid1939 valid1939

def retention1940 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(12800000000000000000/1500320378333676883047),(3601963487517678903/1000000000000000000),(27/20),(707651799153665478237/320000000000000000000),true,MergedCutProfiles.Batch002.profile101,![MergedCutProfiles.Batch002.profile101,MergedCutProfiles.Batch002.profile108,MergedCutProfiles.Batch307.profile12306,MergedCutProfiles.Batch002.profile109,MergedCutProfiles.Batch307.profile12307,MergedCutProfiles.Batch002.profile110,MergedCutProfiles.Batch307.profile12308,MergedCutProfiles.Batch002.profile111,MergedCutProfiles.Batch307.profile12309,MergedCutProfiles.Batch002.profile112,MergedCutProfiles.Batch307.profile12310,MergedCutProfiles.Batch002.profile113,MergedCutProfiles.Batch307.profile12311,MergedCutProfiles.Batch002.profile114,MergedCutProfiles.Batch307.profile12312,MergedCutProfiles.Batch002.profile115]⟩
theorem profilesValid1940 : retention1940.ProfilesValid := by
  change ∀ j : Fin 16, (retention1940.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch002.valid101
  · exact MergedCutProfiles.Batch002.valid108
  · exact MergedCutProfiles.Batch307.valid12306
  · exact MergedCutProfiles.Batch002.valid109
  · exact MergedCutProfiles.Batch307.valid12307
  · exact MergedCutProfiles.Batch002.valid110
  · exact MergedCutProfiles.Batch307.valid12308
  · exact MergedCutProfiles.Batch002.valid111
  · exact MergedCutProfiles.Batch307.valid12309
  · exact MergedCutProfiles.Batch002.valid112
  · exact MergedCutProfiles.Batch307.valid12310
  · exact MergedCutProfiles.Batch002.valid113
  · exact MergedCutProfiles.Batch307.valid12311
  · exact MergedCutProfiles.Batch002.valid114
  · exact MergedCutProfiles.Batch307.valid12312
  · exact MergedCutProfiles.Batch002.valid115
theorem numericValid1940 : retention1940.NumericValid := by decide +kernel
def certificate1940 : RatCutBinCertificate := ⟨⟨retention1940,(450089143465335109/250000000000000000),(637434242080419/1000000000000000000),(6917663821593591299/1000000000000000000),(2605974078352198744117/50000000000000000),(442237582700384443/200000000000000000)⟩,(199993093895002323/200000000000000000),(242805485187375857/1000000000000000000),(413402715968378759/1000000000000000000),(506489818744972847/1000000000000000000)⟩
theorem valid1940 : certificate1940.Valid := by decide +kernel
theorem sound1940 : certificate1940.Sound := rat_cut_bin_certificate_sound certificate1940 profilesValid1940 numericValid1940 valid1940

def retention1941 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(1/2),64,1,(15960555614684130987744105293091422311/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch003.profile124,(fun _ => MergedCutProfiles.Batch003.profile124)⟩
theorem profilesValid1941 : retention1941.ProfilesValid := by
  exact MergedCutProfiles.Batch003.valid124
theorem numericValid1941 : retention1941.NumericValid := by decide +kernel
def certificate1941 : RatCutBinCertificate := ⟨⟨retention1941,(450089143465335109/250000000000000000),(637434242080419/1000000000000000000),(6917663821593591299/1000000000000000000),(2605974078352198744117/50000000000000000),(24934220761781697/25000000000000000)⟩,(199993093895002323/200000000000000000),(203007460284639991/500000000000000000),(28502021374037679/125000000000000000),(55979694170964641/250000000000000000)⟩
theorem valid1941 : certificate1941.Valid := by decide +kernel
theorem sound1941 : certificate1941.Sound := rat_cut_bin_certificate_sound certificate1941 profilesValid1941 numericValid1941 valid1941

def retention1942 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(12800000000000000000/1500320378333676883047),(2306072357448409151/500000000000000000),(23/20),(3952168793832197084774041989622758749071/1844857885958727320800000000000000000000),false,MergedCutProfiles.Batch307.profile12313,(fun _ => MergedCutProfiles.Batch307.profile12313)⟩
theorem profilesValid1942 : retention1942.ProfilesValid := by
  exact MergedCutProfiles.Batch307.valid12313
theorem numericValid1942 : retention1942.NumericValid := by decide +kernel
def certificate1942 : RatCutBinCertificate := ⟨⟨retention1942,(512209694215335109/250000000000000000),(637434242080419/1000000000000000000),(6917663821593591299/1000000000000000000),(2605974078352198744117/50000000000000000),(2142044807468745439/1000000000000000000)⟩,(999960703629642427/1000000000000000000),(117100141402480253/1000000000000000000),(19672830187704453/31250000000000000),(54237050917333211/62500000000000000)⟩
theorem valid1942 : certificate1942.Valid := by decide +kernel
theorem sound1942 : certificate1942.Sound := rat_cut_bin_certificate_sound certificate1942 profilesValid1942 numericValid1942 valid1942

def retention1943 : RatCutRetentionCertificate := ⟨(3/1000),(1/250),(1/2),64,1,(15960555614684130987744105293091422311/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch003.profile124,(fun _ => MergedCutProfiles.Batch003.profile124)⟩
theorem profilesValid1943 : retention1943.ProfilesValid := by
  exact MergedCutProfiles.Batch003.valid124
theorem numericValid1943 : retention1943.NumericValid := by decide +kernel
def certificate1943 : RatCutBinCertificate := ⟨⟨retention1943,(512209694215335109/250000000000000000),(637434242080419/1000000000000000000),(6917663821593591299/1000000000000000000),(2605974078352198744117/50000000000000000),(997345933859224429/1000000000000000000)⟩,(999960703629642427/1000000000000000000),(125750625399573701/500000000000000000),(401268036838195367/1000000000000000000),(394046563657763529/1000000000000000000)⟩
theorem valid1943 : certificate1943.Valid := by decide +kernel
theorem sound1943 : certificate1943.Sound := rat_cut_bin_certificate_sound certificate1943 profilesValid1943 numericValid1943 valid1943

def certificates : List RatCutBinCertificate := [certificate1932,certificate1933,certificate1934,certificate1935,certificate1936,certificate1937,certificate1938,certificate1939,certificate1940,certificate1941,certificate1942,certificate1943]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1932,List.forall_mem_cons.mpr ⟨sound1933,List.forall_mem_cons.mpr ⟨sound1934,List.forall_mem_cons.mpr ⟨sound1935,List.forall_mem_cons.mpr ⟨sound1936,List.forall_mem_cons.mpr ⟨sound1937,List.forall_mem_cons.mpr ⟨sound1938,List.forall_mem_cons.mpr ⟨sound1939,List.forall_mem_cons.mpr ⟨sound1940,List.forall_mem_cons.mpr ⟨sound1941,List.forall_mem_cons.mpr ⟨sound1942,List.forall_mem_cons.mpr ⟨sound1943,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch161
