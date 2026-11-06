import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch021

def certificate840 : RatMajorityCertificate := ⟨0,(1002587926292467181/1000000000000000000),(623195993/526987500),(1751198458801071067/4000000000000000000),(10944990367506694169/25000000000000000000),(707431232967566163/1000000000000000000),false⟩
theorem valid840 : certificate840.Valid := by decide +kernel
theorem bound840 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate840.a certificate840.b certificate840.c x ≤ (certificate840.bound:ℝ) :=
  rat_majority_certificate_sound certificate840 valid840 x hx0 hx1

def certificate841 : RatMajorityCertificate := ⟨(46096766991435601/250000000000000000),(204430919546386324785647452632489219/250000000000000000000000000000000000),(623195993/526987500),(7966668628876809121/20000000000000000000),(19916671572192022803/50000000000000000000),(707431232967566163/1000000000000000000),false⟩
theorem valid841 : certificate841.Valid := by decide +kernel
theorem bound841 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate841.a certificate841.b certificate841.c x ≤ (certificate841.bound:ℝ) :=
  rat_majority_certificate_sound certificate841 valid841 x hx0 hx1

def certificate842 : RatMajorityCertificate := ⟨0,(1002587926292467181/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540865717897297179/1000000000000000000),false⟩
theorem valid842 : certificate842.Valid := by decide +kernel
theorem bound842 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate842.a certificate842.b certificate842.c x ≤ (certificate842.bound:ℝ) :=
  rat_majority_certificate_sound certificate842 valid842 x hx0 hx1

def certificate843 : RatMajorityCertificate := ⟨(3886372467731149/31250000000000000),(27434442583416888404789683386079031/31250000000000000000000000000000000),1,(36637027148228233801/100000000000000000000),(18318513574114116901/50000000000000000000),(540865717897297179/1000000000000000000),false⟩
theorem valid843 : certificate843.Valid := by decide +kernel
theorem bound843 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate843.a certificate843.b certificate843.c x ≤ (certificate843.bound:ℝ) :=
  rat_majority_certificate_sound certificate843 valid843 x hx0 hx1

def certificate844 : RatMajorityCertificate := ⟨0,(250668801021381187/250000000000000000),(621361963/526150000),(43743371952907603419/100000000000000000000),(2187168597645380171/5000000000000000000),(352947755515845973/500000000000000000),false⟩
theorem valid844 : certificate844.Valid := by decide +kernel
theorem bound844 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate844.a certificate844.b certificate844.c x ≤ (certificate844.bound:ℝ) :=
  rat_majority_certificate_sound certificate844 valid844 x hx0 hx1

def certificate845 : RatMajorityCertificate := ⟨(182915110656040273/1000000000000000000),(204817689544538306173314837243455949/250000000000000000000000000000000000),(621361963/526150000),(311193657250791011/781250000000000000),(39832788128101249409/100000000000000000000),(352947755515845973/500000000000000000),false⟩
theorem valid845 : certificate845.Valid := by decide +kernel
theorem bound845 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate845.a certificate845.b certificate845.c x ≤ (certificate845.bound:ℝ) :=
  rat_majority_certificate_sound certificate845 valid845 x hx0 hx1

def certificate846 : RatMajorityCertificate := ⟨0,(250668801021381187/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108159433543566773/200000000000000000),false⟩
theorem valid846 : certificate846.Valid := by decide +kernel
theorem bound846 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate846.a certificate846.b certificate846.c x ≤ (certificate846.bound:ℝ) :=
  rat_majority_certificate_sound certificate846 valid846 x hx0 hx1

def certificate847 : RatMajorityCertificate := ⟨(3854230140602043/31250000000000000),(6867264783712978541412308426034959/7812500000000000000000000000000000),1,(36661101085746737631/100000000000000000000),(1145659408929585551/3125000000000000000),(108159433543566773/200000000000000000),false⟩
theorem valid847 : certificate847.Valid := by decide +kernel
theorem bound847 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate847.a certificate847.b certificate847.c x ≤ (certificate847.bound:ℝ) :=
  rat_majority_certificate_sound certificate847 valid847 x hx0 hx1

def certificate848 : RatMajorityCertificate := ⟨0,(1002762611013538417/1000000000000000000),(2480118571/2101350000),(437271605188349321/1000000000000000000),(43727160518834932101/100000000000000000000),(705189757419314451/1000000000000000000),false⟩
theorem valid848 : certificate848.Valid := by decide +kernel
theorem bound848 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate848.a certificate848.b certificate848.c x ≤ (certificate848.bound:ℝ) :=
  rat_majority_certificate_sound certificate848 valid848 x hx0 hx1

def certificate849 : RatMajorityCertificate := ⟨(45422784123738217/250000000000000000),(205142383145960570097827265419417511/250000000000000000000000000000000000),(2480118571/2101350000),(39847043155641282917/100000000000000000000),(19923521577820641459/50000000000000000000),(705189757419314451/1000000000000000000),false⟩
theorem valid849 : certificate849.Valid := by decide +kernel
theorem bound849 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate849.a certificate849.b certificate849.c x ≤ (certificate849.bound:ℝ) :=
  rat_majority_certificate_sound certificate849 valid849 x hx0 hx1

def certificate850 : RatMajorityCertificate := ⟨0,(1002762611013538417/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(6760266168366397/12500000000000000),false⟩
theorem valid850 : certificate850.Valid := by decide +kernel
theorem bound850 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate850.a certificate850.b certificate850.c x ≤ (certificate850.bound:ℝ) :=
  rat_majority_certificate_sound certificate850 valid850 x hx0 hx1

def certificate851 : RatMajorityCertificate := ⟨(61590904937286189/500000000000000000),(439620248857169475009672181724977187/500000000000000000000000000000000000),1,(366648765968694638699639/1000000000000000000000000),(9166219149217365967491/25000000000000000000000),(6760266168366397/12500000000000000),false⟩
theorem valid851 : certificate851.Valid := by decide +kernel
theorem bound851 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate851.a certificate851.b certificate851.c x ≤ (certificate851.bound:ℝ) :=
  rat_majority_certificate_sound certificate851 valid851 x hx0 hx1

def certificate852 : RatMajorityCertificate := ⟨0,(1002850050670708613/1000000000000000000),(154559528/131138125),(4368944401538811547/10000000000000000000),(43689444015388115471/100000000000000000000),(351787786994736347/500000000000000000),false⟩
theorem valid852 : certificate852.Valid := by decide +kernel
theorem bound852 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate852.a certificate852.b certificate852.c x ≤ (certificate852.bound:ℝ) :=
  rat_majority_certificate_sound certificate852 valid852 x hx0 hx1

def certificate853 : RatMajorityCertificate := ⟨(44952258901544281/250000000000000000),(205632137550500658752864281732407747/250000000000000000000000000000000000),(154559528/131138125),(1594216662120835967/4000000000000000000),(4981927069127612397/12500000000000000000),(351787786994736347/500000000000000000),false⟩
theorem valid853 : certificate853.Valid := by decide +kernel
theorem bound853 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate853.a certificate853.b certificate853.c x ≤ (certificate853.bound:ℝ) :=
  rat_majority_certificate_sound certificate853 valid853 x hx0 hx1

def certificate854 : RatMajorityCertificate := ⟨0,(1002850050670708613/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108151796864470167/200000000000000000),false⟩
theorem valid854 : certificate854.Valid := by decide +kernel
theorem bound854 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate854.a certificate854.b certificate854.c x ≤ (certificate854.bound:ℝ) :=
  rat_majority_certificate_sound certificate854 valid854 x hx0 hx1

def certificate855 : RatMajorityCertificate := ⟨(122207315196632739/1000000000000000000),(880294438433434211988225683354918993/1000000000000000000000000000000000000),1,(4585955575431975749/12500000000000000000),(36687644603455805993/100000000000000000000),(108151796864470167/200000000000000000),false⟩
theorem valid855 : certificate855.Valid := by decide +kernel
theorem bound855 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate855.a certificate855.b certificate855.c x ≤ (certificate855.bound:ℝ) :=
  rat_majority_certificate_sound certificate855 valid855 x hx0 hx1

def certificate856 : RatMajorityCertificate := ⟨0,(100293745277393243/100000000000000000),(616498931/523792500),(43652557841746426387/100000000000000000000),(10913139460436606597/25000000000000000000),(702028431458928999/1000000000000000000),false⟩
theorem valid856 : certificate856.Valid := by decide +kernel
theorem bound856 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate856.a certificate856.b certificate856.c x ≤ (certificate856.bound:ℝ) :=
  rat_majority_certificate_sound certificate856 valid856 x hx0 hx1

def certificate857 : RatMajorityCertificate := ⟨(35652649142454553/200000000000000000),(16483011343921039020162377563214621/20000000000000000000000000000000000),(616498931/523792500),(39856128286473285621/100000000000000000000),(19928064143236642811/50000000000000000000),(702028431458928999/1000000000000000000),false⟩
theorem valid857 : certificate857.Valid := by decide +kernel
theorem bound857 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate857.a certificate857.b certificate857.c x ≤ (certificate857.bound:ℝ) :=
  rat_majority_certificate_sound certificate857 valid857 x hx0 hx1

def certificate858 : RatMajorityCertificate := ⟨0,(100293745277393243/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270381655872858727/500000000000000000),false⟩
theorem valid858 : certificate858.Valid := by decide +kernel
theorem bound858 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate858.a certificate858.b certificate858.c x ≤ (certificate858.bound:ℝ) :=
  rat_majority_certificate_sound certificate858 valid858 x hx0 hx1

def certificate859 : RatMajorityCertificate := ⟨(60932163080985733/500000000000000000),(44035757795451653725820410886397881/50000000000000000000000000000000000),1,(7339157511630112551/20000000000000000000),(9173946889537640689/25000000000000000000),(270381655872858727/500000000000000000),false⟩
theorem valid859 : certificate859.Valid := by decide +kernel
theorem bound859 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate859.a certificate859.b certificate859.c x ≤ (certificate859.bound:ℝ) :=
  rat_majority_certificate_sound certificate859 valid859 x hx0 hx1

def certificate860 : RatMajorityCertificate := ⟨0,(1003024734143526871/1000000000000000000),(819002323/697410000),(8718381230418957507/20000000000000000000),(2724494134505924221/6250000000000000000),(699493764586730747/1000000000000000000),false⟩
theorem valid860 : certificate860.Valid := by decide +kernel
theorem bound860 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate860.a certificate860.b certificate860.c x ≤ (certificate860.bound:ℝ) :=
  rat_majority_certificate_sound certificate860 valid860 x hx0 hx1

def certificate861 : RatMajorityCertificate := ⟨(17609771654655249/100000000000000000),(82639436882113890685454073527304121/100000000000000000000000000000000000),(819002323/697410000),(9961890330791828887/25000000000000000000),(39847561323167315549/100000000000000000000),(699493764586730747/1000000000000000000),false⟩
theorem valid861 : certificate861.Valid := by decide +kernel
theorem bound861 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate861.a certificate861.b certificate861.c x ≤ (certificate861.bound:ℝ) :=
  rat_majority_certificate_sound certificate861 valid861 x hx0 hx1

def certificate862 : RatMajorityCertificate := ⟨0,(1003024734143526871/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(27033658741031683/50000000000000000),false⟩
theorem valid862 : certificate862.Valid := by decide +kernel
theorem bound862 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate862.a certificate862.b certificate862.c x ≤ (certificate862.bound:ℝ) :=
  rat_majority_certificate_sound certificate862 valid862 x hx0 hx1

def certificate863 : RatMajorityCertificate := ⟨(24124024116121603/200000000000000000),(176407953953160472541955923665905787/200000000000000000000000000000000000),1,(9181178638027056663/25000000000000000000),(36724714552108226653/100000000000000000000),(27033658741031683/50000000000000000),false⟩
theorem valid863 : certificate863.Valid := by decide +kernel
theorem bound863 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate863.a certificate863.b certificate863.c x ≤ (certificate863.bound:ℝ) :=
  rat_majority_certificate_sound certificate863 valid863 x hx0 hx1

def certificate864 : RatMajorityCertificate := ⟨0,(125388974572502011/125000000000000000),(76567891/65293750),(43553254468344352691/100000000000000000000),(10888313617086088173/25000000000000000000),(697872145685072637/1000000000000000000),false⟩
theorem valid864 : certificate864.Valid := by decide +kernel
theorem bound864 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate864.a certificate864.b certificate864.c x ≤ (certificate864.bound:ℝ) :=
  rat_majority_certificate_sound certificate864 valid864 x hx0 hx1

def certificate865 : RatMajorityCertificate := ⟨(87208437601981643/500000000000000000),(51759510721268501014093209797415927/62500000000000000000000000000000000),(76567891/65293750),(19924788527265148933/50000000000000000000),(39849577054530297867/100000000000000000000),(697872145685072637/1000000000000000000),false⟩
theorem valid865 : certificate865.Valid := by decide +kernel
theorem bound865 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate865.a certificate865.b certificate865.c x ≤ (certificate865.bound:ℝ) :=
  rat_majority_certificate_sound certificate865 valid865 x hx0 hx1

def certificate866 : RatMajorityCertificate := ⟨0,(125388974572502011/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270338154323677179/500000000000000000),false⟩
theorem valid866 : certificate866.Valid := by decide +kernel
theorem bound866 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate866.a certificate866.b certificate866.c x ≤ (certificate866.bound:ℝ) :=
  rat_majority_certificate_sound certificate866 valid866 x hx0 hx1

def certificate867 : RatMajorityCertificate := ⟨(7516550063770207/62500000000000000),(6894318405962354832711760250613723/7812500000000000000000000000000000),1,(36733113934735681843/100000000000000000000),(9183278483683920461/25000000000000000000),(270338154323677179/500000000000000000),false⟩
theorem valid867 : certificate867.Valid := by decide +kernel
theorem bound867 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate867.a certificate867.b certificate867.c x ≤ (certificate867.bound:ℝ) :=
  rat_majority_certificate_sound certificate867 valid867 x hx0 hx1

def certificate868 : RatMajorityCertificate := ⟨0,(501599293107539959/500000000000000000),(305468227/260832500),(2175888814255312281/5000000000000000000),(43517776285106245621/100000000000000000000),(696463442869509629/1000000000000000000),false⟩
theorem valid868 : certificate868.Valid := by decide +kernel
theorem bound868 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate868.a certificate868.b certificate868.c x ≤ (certificate868.bound:ℝ) :=
  rat_majority_certificate_sound certificate868 valid868 x hx0 hx1

def certificate869 : RatMajorityCertificate := ⟨(86833598845296003/500000000000000000),(207243974754985806359828541494516123/250000000000000000000000000000000000),(305468227/260832500),(19915881000081593653/50000000000000000000),(39831762000163187307/100000000000000000000),(696463442869509629/1000000000000000000),false⟩
theorem valid869 : certificate869.Valid := by decide +kernel
theorem bound869 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate869.a certificate869.b certificate869.c x ≤ (certificate869.bound:ℝ) :=
  rat_majority_certificate_sound certificate869 valid869 x hx0 hx1

def certificate870 : RatMajorityCertificate := ⟨0,(501599293107539959/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540611099238681007/1000000000000000000),false⟩
theorem valid870 : certificate870.Valid := by decide +kernel
theorem bound870 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate870.a certificate870.b certificate870.c x ≤ (certificate870.bound:ℝ) :=
  rat_majority_certificate_sound certificate870 valid870 x hx0 hx1

def certificate871 : RatMajorityCertificate := ⟨(11925505387401939/100000000000000000),(44178104238483023830355389363419499/50000000000000000000000000000000000),1,(574321264818918899/1562500000000000000),(36756560948410809537/100000000000000000000),(540611099238681007/1000000000000000000),false⟩
theorem valid871 : certificate871.Valid := by decide +kernel
theorem bound871 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate871.a certificate871.b certificate871.c x ≤ (certificate871.bound:ℝ) :=
  rat_majority_certificate_sound certificate871 valid871 x hx0 hx1

def certificate872 : RatMajorityCertificate := ⟨0,(100328500532319339/100000000000000000),(2434899669/2084020000),(8690807203499575523/20000000000000000000),(2715877251093617351/6250000000000000000),(138745852274881951/200000000000000000),false⟩
theorem valid872 : certificate872.Valid := by decide +kernel
theorem bound872 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate872.a certificate872.b certificate872.c x ≤ (certificate872.bound:ℝ) :=
  rat_majority_certificate_sound certificate872 valid872 x hx0 hx1

def certificate873 : RatMajorityCertificate := ⟨(34094162563648717/200000000000000000),(16645083899547855416825469538361937/20000000000000000000000000000000000),(2434899669/2084020000),(7969005131264976781/20000000000000000000),(19922512828162441953/50000000000000000000),(138745852274881951/200000000000000000),false⟩
theorem valid873 : certificate873.Valid := by decide +kernel
theorem bound873 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate873.a certificate873.b certificate873.c x ≤ (certificate873.bound:ℝ) :=
  rat_majority_certificate_sound certificate873 valid873 x hx0 hx1

def certificate874 : RatMajorityCertificate := ⟨0,(100328500532319339/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540593354293462753/1000000000000000000),false⟩
theorem valid874 : certificate874.Valid := by decide +kernel
theorem bound874 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate874.a certificate874.b certificate874.c x ≤ (certificate874.bound:ℝ) :=
  rat_majority_certificate_sound certificate874 valid874 x hx0 hx1

def certificate875 : RatMajorityCertificate := ⟨(118699837316286509/1000000000000000000),(88419523840946069042180331594502449/100000000000000000000000000000000000),1,(36769526727048563783/100000000000000000000),(4596190840881070473/12500000000000000000),(540593354293462753/1000000000000000000),false⟩
theorem valid875 : certificate875.Valid := by decide +kernel
theorem bound875 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate875.a certificate875.b certificate875.c x ≤ (certificate875.bound:ℝ) :=
  rat_majority_certificate_sound certificate875 valid875 x hx0 hx1

def certificate876 : RatMajorityCertificate := ⟨0,(1003306977646147329/1000000000000000000),(607621827/520982500),(1736248531077991023/4000000000000000000),(5425776659618721947/12500000000000000000),(345820680831067613/500000000000000000),false⟩
theorem valid876 : certificate876.Valid := by decide +kernel
theorem bound876 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate876.a certificate876.b certificate876.c x ≤ (certificate876.bound:ℝ) :=
  rat_majority_certificate_sound certificate876 valid876 x hx0 hx1

def certificate877 : RatMajorityCertificate := ⟨(167873203734803059/1000000000000000000),(834878620979206139980441536086120589/1000000000000000000000000000000000000),(607621827/520982500),(39859454077168105871/100000000000000000000),(2491215879823006617/6250000000000000000),(345820680831067613/500000000000000000),false⟩
theorem valid877 : certificate877.Valid := by decide +kernel
theorem bound877 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate877.a certificate877.b certificate877.c x ≤ (certificate877.bound:ℝ) :=
  rat_majority_certificate_sound certificate877 valid877 x hx0 hx1

def certificate878 : RatMajorityCertificate := ⟨0,(1003306977646147329/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135114377722909053/250000000000000000),false⟩
theorem valid878 : certificate878.Valid := by decide +kernel
theorem bound878 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate878.a certificate878.b certificate878.c x ≤ (certificate878.bound:ℝ) :=
  rat_majority_certificate_sound certificate878 valid878 x hx0 hx1

def certificate879 : RatMajorityCertificate := ⟨(117293841047769963/1000000000000000000),(885625248488001632729901026001121173/1000000000000000000000000000000000000),1,(36801829476312856719/100000000000000000000),(460022868453910709/1250000000000000000),(135114377722909053/250000000000000000),false⟩
theorem valid879 : certificate879.Valid := by decide +kernel
theorem bound879 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate879.a certificate879.b certificate879.c x ≤ (certificate879.bound:ℝ) :=
  rat_majority_certificate_sound certificate879 valid879 x hx0 hx1

end Cycle12.MajorityCertificates.Batch021
