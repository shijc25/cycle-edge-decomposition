import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch357
import Cycle12.MergedCutProfiles.Batch358
import Cycle12.MergedCutProfiles.Batch359
import Cycle12.MergedCutProfiles.Batch476
import Cycle12.MergedCutProfiles.Batch477
import Cycle12.MergedCutProfiles.Batch604
import Cycle12.MergedCutProfiles.Batch605
import Cycle12.MergedCutProfiles.Batch682
import Cycle12.MergedCutProfiles.Batch683

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch404

def retention4848 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(446144899821627162/1413622755423419206487),(139155885553411121/200000000000000000),4,(6670465950758636324084873817180838431/2783117711068222420000000000000000000),false,MergedCutProfiles.Batch682.profile27307,(fun _ => MergedCutProfiles.Batch682.profile27307)⟩
theorem profilesValid4848 : retention4848.ProfilesValid := by
  exact MergedCutProfiles.Batch682.valid27307
theorem numericValid4848 : retention4848.NumericValid := by decide +kernel
def certificate4848 : RatCutBinCertificate := ⟨⟨retention4848,(1842166636154060891/1000000000000000000),(81190354661587239/1000000000000000000),(230577501884345397/20000000000000000),(32772344532278908303541/1000000000000000000),(234486750491353271/100000000000000000)⟩,(999948117539833849/1000000000000000000),(860768011250271841/1000000000000000000),(636051498817671/62500000000000000),(4927552151309843/1000000000000000000)⟩
theorem valid4848 : certificate4848.Valid := by decide +kernel
theorem sound4848 : certificate4848.Sound := rat_cut_bin_certificate_sound certificate4848 profilesValid4848 numericValid4848 valid4848

def retention4849 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(5735916568025511783/2827245510846838412974),(223072449910813581/250000000000000000),(18/5),(1113014302599860608433845303919296923/464734270647528293750000000000000000),false,MergedCutProfiles.Batch682.profile27308,(fun _ => MergedCutProfiles.Batch682.profile27308)⟩
theorem profilesValid4849 : retention4849.ProfilesValid := by
  exact MergedCutProfiles.Batch682.valid27308
theorem numericValid4849 : retention4849.NumericValid := by decide +kernel
def certificate4849 : RatCutBinCertificate := ⟨⟨retention4849,(1842166636154060891/1000000000000000000),(81190354661587239/1000000000000000000),(230577501884345397/20000000000000000),(32772344532278908303541/1000000000000000000),(2348244283427951787/1000000000000000000)⟩,(999948117539833849/1000000000000000000),(50717334346142771/62500000000000000),(950300122897161/50000000000000000),(5152128504086247/500000000000000000)⟩
theorem valid4849 : certificate4849.Valid := by decide +kernel
theorem sound4849 : certificate4849.Sound := rat_cut_bin_certificate_sound certificate4849 profilesValid4849 numericValid4849 valid4849

def retention4850 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(1/40),(5735916568025511783/1000000000000000000),(27/20),(20206502792763207204104238724427708175599/9177466508840818852800000000000000000000),false,MergedCutProfiles.Batch682.profile27309,(fun _ => MergedCutProfiles.Batch682.profile27309)⟩
theorem profilesValid4850 : retention4850.ProfilesValid := by
  exact MergedCutProfiles.Batch682.valid27309
theorem numericValid4850 : retention4850.NumericValid := by decide +kernel
def certificate4850 : RatCutBinCertificate := ⟨⟨retention4850,(1842166636154060891/1000000000000000000),(81190354661587239/1000000000000000000),(230577501884345397/20000000000000000),(32772344532278908303541/1000000000000000000),(2184237935739649591/1000000000000000000)⟩,(999948117539833849/1000000000000000000),(179486989053966101/250000000000000000),(22077051756715049/500000000000000000),(29544528323550119/500000000000000000)⟩
theorem valid4850 : certificate4850.Valid := by decide +kernel
theorem sound4850 : certificate4850.Sound := rat_cut_bin_certificate_sound certificate4850 profilesValid4850 numericValid4850 valid4850

def retention4851 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(295021159594385543/1341292276172464202232),(555846555390123591/1000000000000000000),4,(557354021141778911599/256000000000000000000),true,MergedCutProfiles.Batch682.profile27310,![MergedCutProfiles.Batch682.profile27310,MergedCutProfiles.Batch682.profile27311,MergedCutProfiles.Batch682.profile27312,MergedCutProfiles.Batch682.profile27313,MergedCutProfiles.Batch682.profile27314,MergedCutProfiles.Batch682.profile27315,MergedCutProfiles.Batch682.profile27316,MergedCutProfiles.Batch682.profile27317,MergedCutProfiles.Batch682.profile27318,MergedCutProfiles.Batch604.profile24183,MergedCutProfiles.Batch682.profile27319,MergedCutProfiles.Batch683.profile27320,MergedCutProfiles.Batch683.profile27321,MergedCutProfiles.Batch683.profile27322,MergedCutProfiles.Batch604.profile24184,MergedCutProfiles.Batch605.profile24203]⟩
theorem profilesValid4851 : retention4851.ProfilesValid := by
  change ∀ j : Fin 16, (retention4851.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch682.valid27310
  · exact MergedCutProfiles.Batch682.valid27311
  · exact MergedCutProfiles.Batch682.valid27312
  · exact MergedCutProfiles.Batch682.valid27313
  · exact MergedCutProfiles.Batch682.valid27314
  · exact MergedCutProfiles.Batch682.valid27315
  · exact MergedCutProfiles.Batch682.valid27316
  · exact MergedCutProfiles.Batch682.valid27317
  · exact MergedCutProfiles.Batch682.valid27318
  · exact MergedCutProfiles.Batch604.valid24183
  · exact MergedCutProfiles.Batch682.valid27319
  · exact MergedCutProfiles.Batch683.valid27320
  · exact MergedCutProfiles.Batch683.valid27321
  · exact MergedCutProfiles.Batch683.valid27322
  · exact MergedCutProfiles.Batch604.valid24184
  · exact MergedCutProfiles.Batch605.valid24203
theorem numericValid4851 : retention4851.NumericValid := by decide +kernel
def certificate4851 : RatCutBinCertificate := ⟨⟨retention4851,(1871791797829828149/1000000000000000000),(21376650541548341/250000000000000000),(11709299178050645457/1000000000000000000),(31583197446211058204217/1000000000000000000),(2122489395025453901/1000000000000000000)⟩,(999945546088610453/1000000000000000000),(99127918542772763/125000000000000000),(11536231819135563/500000000000000000),(9883256359361/1000000000000000)⟩
theorem valid4851 : certificate4851.Valid := by decide +kernel
theorem sound4851 : certificate4851.Sound := rat_cut_bin_certificate_sound certificate4851 profilesValid4851 numericValid4851 valid4851

def retention4852 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(70884730187500000/167661534521558025279),(295021159594385543/500000000000000000),4,(288475055286814475871/128000000000000000000),true,MergedCutProfiles.Batch682.profile27311,![MergedCutProfiles.Batch682.profile27311,MergedCutProfiles.Batch683.profile27323,MergedCutProfiles.Batch682.profile27315,MergedCutProfiles.Batch682.profile27317,MergedCutProfiles.Batch604.profile24195,MergedCutProfiles.Batch682.profile27319,MergedCutProfiles.Batch683.profile27321,MergedCutProfiles.Batch604.profile24184,MergedCutProfiles.Batch683.profile27324,MergedCutProfiles.Batch604.profile24196,MergedCutProfiles.Batch604.profile24185,MergedCutProfiles.Batch683.profile27325,MergedCutProfiles.Batch476.profile19072,MergedCutProfiles.Batch683.profile27326,MergedCutProfiles.Batch604.profile24197,MergedCutProfiles.Batch604.profile24187]⟩
theorem profilesValid4852 : retention4852.ProfilesValid := by
  change ∀ j : Fin 16, (retention4852.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch682.valid27311
  · exact MergedCutProfiles.Batch683.valid27323
  · exact MergedCutProfiles.Batch682.valid27315
  · exact MergedCutProfiles.Batch682.valid27317
  · exact MergedCutProfiles.Batch604.valid24195
  · exact MergedCutProfiles.Batch682.valid27319
  · exact MergedCutProfiles.Batch683.valid27321
  · exact MergedCutProfiles.Batch604.valid24184
  · exact MergedCutProfiles.Batch683.valid27324
  · exact MergedCutProfiles.Batch604.valid24196
  · exact MergedCutProfiles.Batch604.valid24185
  · exact MergedCutProfiles.Batch683.valid27325
  · exact MergedCutProfiles.Batch476.valid19072
  · exact MergedCutProfiles.Batch683.valid27326
  · exact MergedCutProfiles.Batch604.valid24197
  · exact MergedCutProfiles.Batch604.valid24187
theorem numericValid4852 : retention4852.NumericValid := by decide +kernel
def certificate4852 : RatCutBinCertificate := ⟨⟨retention4852,(1871791797829828149/1000000000000000000),(21376650541548341/250000000000000000),(11709299178050645457/1000000000000000000),(31583197446211058204217/1000000000000000000),(274879577903373733/125000000000000000)⟩,(999945546088610453/1000000000000000000),(11485451478182079/15625000000000000),(9670869624432039/250000000000000000),(3449530995873679/200000000000000000)⟩
theorem valid4852 : certificate4852.Valid := by decide +kernel
theorem sound4852 : certificate4852.Sound := rat_cut_bin_certificate_sound certificate4852 profilesValid4852 numericValid4852 valid4852

def retention4853 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(2013160060451645695/1341292276172464202232),(1134155683/1000000000),(14/5),(168843101603405152939250930569071879/70884730187500000000000000000000000),true,MergedCutProfiles.Batch683.profile27327,![MergedCutProfiles.Batch683.profile27327,MergedCutProfiles.Batch683.profile27322,MergedCutProfiles.Batch604.profile24185,MergedCutProfiles.Batch683.profile27326,MergedCutProfiles.Batch683.profile27328,MergedCutProfiles.Batch604.profile24189,MergedCutProfiles.Batch604.profile24198,MergedCutProfiles.Batch683.profile27329,MergedCutProfiles.Batch604.profile24192,MergedCutProfiles.Batch357.profile14287,MergedCutProfiles.Batch476.profile19074,MergedCutProfiles.Batch683.profile27330,MergedCutProfiles.Batch357.profile14317,MergedCutProfiles.Batch605.profile24200,MergedCutProfiles.Batch683.profile27331,MergedCutProfiles.Batch605.profile24206]⟩
theorem profilesValid4853 : retention4853.ProfilesValid := by
  change ∀ j : Fin 16, (retention4853.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch683.valid27327
  · exact MergedCutProfiles.Batch683.valid27322
  · exact MergedCutProfiles.Batch604.valid24185
  · exact MergedCutProfiles.Batch683.valid27326
  · exact MergedCutProfiles.Batch683.valid27328
  · exact MergedCutProfiles.Batch604.valid24189
  · exact MergedCutProfiles.Batch604.valid24198
  · exact MergedCutProfiles.Batch683.valid27329
  · exact MergedCutProfiles.Batch604.valid24192
  · exact MergedCutProfiles.Batch357.valid14287
  · exact MergedCutProfiles.Batch476.valid19074
  · exact MergedCutProfiles.Batch683.valid27330
  · exact MergedCutProfiles.Batch357.valid14317
  · exact MergedCutProfiles.Batch605.valid24200
  · exact MergedCutProfiles.Batch683.valid27331
  · exact MergedCutProfiles.Batch605.valid24206
theorem numericValid4853 : retention4853.NumericValid := by decide +kernel
def certificate4853 : RatCutBinCertificate := ⟨⟨retention4853,(1871791797829828149/1000000000000000000),(21376650541548341/250000000000000000),(11709299178050645457/1000000000000000000),(31583197446211058204217/1000000000000000000),(2343666664460842929/1000000000000000000)⟩,(999945546088610453/1000000000000000000),(467636398062211123/1000000000000000000),(176929756008930761/1000000000000000000),(117195164354055551/1000000000000000000)⟩
theorem valid4853 : certificate4853.Valid := by decide +kernel
theorem sound4853 : certificate4853.Sound := rat_cut_bin_certificate_sound certificate4853 profilesValid4853 numericValid4853 valid4853

def retention4854 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(4000000000000000000/167661534521558025279),(402632012090329139/100000000000000000),(27/20),(278556763251526903587/128000000000000000000),true,MergedCutProfiles.Batch605.profile24206,![MergedCutProfiles.Batch605.profile24206,MergedCutProfiles.Batch683.profile27332,MergedCutProfiles.Batch683.profile27333,MergedCutProfiles.Batch683.profile27334,MergedCutProfiles.Batch477.profile19112,MergedCutProfiles.Batch683.profile27335,MergedCutProfiles.Batch683.profile27336,MergedCutProfiles.Batch357.profile14299,MergedCutProfiles.Batch358.profile14325,MergedCutProfiles.Batch683.profile27337,MergedCutProfiles.Batch683.profile27338,MergedCutProfiles.Batch683.profile27339,MergedCutProfiles.Batch683.profile27340,MergedCutProfiles.Batch683.profile27341,MergedCutProfiles.Batch683.profile27342,MergedCutProfiles.Batch683.profile27343]⟩
theorem profilesValid4854 : retention4854.ProfilesValid := by
  change ∀ j : Fin 16, (retention4854.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch605.valid24206
  · exact MergedCutProfiles.Batch683.valid27332
  · exact MergedCutProfiles.Batch683.valid27333
  · exact MergedCutProfiles.Batch683.valid27334
  · exact MergedCutProfiles.Batch477.valid19112
  · exact MergedCutProfiles.Batch683.valid27335
  · exact MergedCutProfiles.Batch683.valid27336
  · exact MergedCutProfiles.Batch357.valid14299
  · exact MergedCutProfiles.Batch358.valid14325
  · exact MergedCutProfiles.Batch683.valid27337
  · exact MergedCutProfiles.Batch683.valid27338
  · exact MergedCutProfiles.Batch683.valid27339
  · exact MergedCutProfiles.Batch683.valid27340
  · exact MergedCutProfiles.Batch683.valid27341
  · exact MergedCutProfiles.Batch683.valid27342
  · exact MergedCutProfiles.Batch683.valid27343
theorem numericValid4854 : retention4854.NumericValid := by decide +kernel
def certificate4854 : RatCutBinCertificate := ⟨⟨retention4854,(1871791797829828149/1000000000000000000),(21376650541548341/250000000000000000),(11709299178050645457/1000000000000000000),(31583197446211058204217/1000000000000000000),(539442999508928621/250000000000000000)⟩,(999945546088610453/1000000000000000000),(80009948138768727/250000000000000000),(15766115502866569/50000000000000000),(48680802560281817/125000000000000000)⟩
theorem valid4854 : certificate4854.Valid := by decide +kernel
theorem sound4854 : certificate4854.Sound := rat_cut_bin_certificate_sound certificate4854 profilesValid4854 numericValid4854 valid4854

def retention4855 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(1/2),64,1,(63846487671256044251940764516727514191/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch359.profile14365,(fun _ => MergedCutProfiles.Batch359.profile14365)⟩
theorem profilesValid4855 : retention4855.ProfilesValid := by
  exact MergedCutProfiles.Batch359.valid14365
theorem numericValid4855 : retention4855.NumericValid := by decide +kernel
def certificate4855 : RatCutBinCertificate := ⟨⟨retention4855,(1871791797829828149/1000000000000000000),(21376650541548341/250000000000000000),(11709299178050645457/1000000000000000000),(31583197446211058204217/1000000000000000000),(491966349207074289/500000000000000000)⟩,(999945546088610453/1000000000000000000),(137609417510264611/250000000000000000),(120928160649758117/1000000000000000000),(58588576883371421/500000000000000000)⟩
theorem valid4855 : certificate4855.Valid := by decide +kernel
theorem sound4855 : certificate4855.Sound := rat_cut_bin_certificate_sound certificate4855 profilesValid4855 numericValid4855 valid4855

def retention4856 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(4000000000000000000/167661534521558025279),(32939414938904403883/1000000000000000000),1,(57289463927879687217714452202011688519/26351531951123523106400000000000000000),false,MergedCutProfiles.Batch683.profile27344,(fun _ => MergedCutProfiles.Batch683.profile27344)⟩
theorem profilesValid4856 : retention4856.ProfilesValid := by
  exact MergedCutProfiles.Batch683.valid27344
theorem numericValid4856 : retention4856.NumericValid := by decide +kernel
def certificate4856 : RatCutBinCertificate := ⟨⟨retention4856,(1743633497829828149/1000000000000000000),(21376650541548341/250000000000000000),(11709299178050645457/1000000000000000000),(31583197446211058204217/1000000000000000000),(540328501532644361/250000000000000000)⟩,(7999594195752687/8000000000000000),(10174432891590759/500000000000000000),(109117773922158341/125000000000000000),(1770437672172964511/1000000000000000000)⟩
theorem valid4856 : certificate4856.Valid := by decide +kernel
theorem sound4856 : certificate4856.Sound := rat_cut_bin_certificate_sound certificate4856 profilesValid4856 numericValid4856 valid4856

def retention4857 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(1/2),64,1,(63846487671256044251940764516727514191/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch359.profile14365,(fun _ => MergedCutProfiles.Batch359.profile14365)⟩
theorem profilesValid4857 : retention4857.ProfilesValid := by
  exact MergedCutProfiles.Batch359.valid14365
theorem numericValid4857 : retention4857.NumericValid := by decide +kernel
def certificate4857 : RatCutBinCertificate := ⟨⟨retention4857,(1743633497829828149/1000000000000000000),(21376650541548341/250000000000000000),(11709299178050645457/1000000000000000000),(31583197446211058204217/1000000000000000000),(984868568364119767/1000000000000000000)⟩,(7999594195752687/8000000000000000),(44655997803964179/1000000000000000000),(100357297514896003/125000000000000000),(760436115232039/976562500000000)⟩
theorem valid4857 : certificate4857.Valid := by decide +kernel
theorem sound4857 : certificate4857.Sound := rat_cut_bin_certificate_sound certificate4857 profilesValid4857 numericValid4857 valid4857

def retention4858 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(699668974387979993/2682584552344928404464),(692741558799980191/1000000000000000000),4,(83037910626416430802289298964650329/34637077939999009550000000000000000),false,MergedCutProfiles.Batch683.profile27345,(fun _ => MergedCutProfiles.Batch683.profile27345)⟩
theorem profilesValid4858 : retention4858.ProfilesValid := by
  exact MergedCutProfiles.Batch683.valid27345
theorem numericValid4858 : retention4858.NumericValid := by decide +kernel
def certificate4858 : RatCutBinCertificate := ⟨⟨retention4858,(1850071288829828149/1000000000000000000),(21376650541548341/250000000000000000),(11709299178050645457/1000000000000000000),(31583197446211058204217/1000000000000000000),(2343330266676433031/1000000000000000000)⟩,(999946177981697597/1000000000000000000),(857774334244536763/1000000000000000000),(10630878649813561/1000000000000000000),(1285170595164921/250000000000000000)⟩
theorem valid4858 : certificate4858.Valid := by decide +kernel
theorem sound4858 : certificate4858.Sound := rat_cut_bin_certificate_sound certificate4858 profilesValid4858 numericValid4858 valid4858

def retention4859 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(24924385518778859/74516237565136900124),(699668974387979993/1000000000000000000),4,(1343642726372056365107870169105295587/559735179510383994400000000000000000),false,MergedCutProfiles.Batch683.profile27346,(fun _ => MergedCutProfiles.Batch683.profile27346)⟩
theorem profilesValid4859 : retention4859.ProfilesValid := by
  exact MergedCutProfiles.Batch683.valid27346
theorem numericValid4859 : retention4859.NumericValid := by decide +kernel
def certificate4859 : RatCutBinCertificate := ⟨⟨retention4859,(1850071288829828149/1000000000000000000),(21376650541548341/250000000000000000),(11709299178050645457/1000000000000000000),(31583197446211058204217/1000000000000000000),(36663389181896529/15625000000000000)⟩,(999946177981697597/1000000000000000000),(213620706594852419/250000000000000000),(11142166075229107/1000000000000000000),(5403201297170253/1000000000000000000)⟩
theorem valid4859 : certificate4859.Valid := by decide +kernel
theorem sound4859 : certificate4859.Sound := rat_cut_bin_certificate_sound certificate4859 profilesValid4859 numericValid4859 valid4859

def certificates : List RatCutBinCertificate := [certificate4848,certificate4849,certificate4850,certificate4851,certificate4852,certificate4853,certificate4854,certificate4855,certificate4856,certificate4857,certificate4858,certificate4859]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4848,List.forall_mem_cons.mpr ⟨sound4849,List.forall_mem_cons.mpr ⟨sound4850,List.forall_mem_cons.mpr ⟨sound4851,List.forall_mem_cons.mpr ⟨sound4852,List.forall_mem_cons.mpr ⟨sound4853,List.forall_mem_cons.mpr ⟨sound4854,List.forall_mem_cons.mpr ⟨sound4855,List.forall_mem_cons.mpr ⟨sound4856,List.forall_mem_cons.mpr ⟨sound4857,List.forall_mem_cons.mpr ⟨sound4858,List.forall_mem_cons.mpr ⟨sound4859,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch404
