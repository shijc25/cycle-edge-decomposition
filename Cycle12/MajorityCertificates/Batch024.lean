import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch024

def certificate960 : RatMajorityCertificate := ⟨0,(251067458273058393/250000000000000000),(93531409/82426000),(426639580329894339/1000000000000000000),(42663958032989433901/100000000000000000000),(661828700734875467/1000000000000000000),false⟩
theorem valid960 : certificate960.Valid := by decide +kernel
theorem bound960 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate960.a certificate960.b certificate960.c x ≤ (certificate960.bound:ℝ) :=
  rat_majority_certificate_sound certificate960 valid960 x hx0 hx1

def certificate961 : RatMajorityCertificate := ⟨(145996650954306927/1000000000000000000),(214412450201581667793353468084611689/250000000000000000000000000000000000),(93531409/82426000),(495312764104778403/1250000000000000000),(39625021128382272241/100000000000000000000),(661828700734875467/1000000000000000000),false⟩
theorem valid961 : certificate961.Valid := by decide +kernel
theorem bound961 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate961.a certificate961.b certificate961.c x ≤ (certificate961.bound:ℝ) :=
  rat_majority_certificate_sound certificate961 valid961 x hx0 hx1

def certificate962 : RatMajorityCertificate := ⟨0,(251067458273058393/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(269805206313151857/500000000000000000),false⟩
theorem valid962 : certificate962.Valid := by decide +kernel
theorem bound962 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate962.a certificate962.b certificate962.c x ≤ (certificate962.bound:ℝ) :=
  rat_majority_certificate_sound certificate962 valid962 x hx0 hx1

def certificate963 : RatMajorityCertificate := ⟨(104541399240524057/1000000000000000000),(224820514881430980942573974517739599/250000000000000000000000000000000000),1,(37092721479186904931/100000000000000000000),(9273180369796726233/25000000000000000000),(269805206313151857/500000000000000000),false⟩
theorem valid963 : certificate963.Valid := by decide +kernel
theorem bound963 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate963.a certificate963.b certificate963.c x ≤ (certificate963.bound:ℝ) :=
  rat_majority_certificate_sound certificate963 valid963 x hx0 hx1

def certificate964 : RatMajorityCertificate := ⟨0,(1004306354975158643/1000000000000000000),(2333812171/2059980000),(42620903885576085293/100000000000000000000),(21310451942788042647/50000000000000000000),(660074045320724617/1000000000000000000),false⟩
theorem valid964 : certificate964.Valid := by decide +kernel
theorem bound964 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate964.a certificate964.b certificate964.c x ≤ (certificate964.bound:ℝ) :=
  rat_majority_certificate_sound certificate964 valid964 x hx0 hx1

def certificate965 : RatMajorityCertificate := ⟨(72107440176513633/500000000000000000),(429735217077315604797743203172719981/500000000000000000000000000000000000),(2333812171/2059980000),(2476437662269347027/6250000000000000000),(39623002596309552433/100000000000000000000),(660074045320724617/1000000000000000000),false⟩
theorem valid965 : certificate965.Valid := by decide +kernel
theorem bound965 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate965.a certificate965.b certificate965.c x ≤ (certificate965.bound:ℝ) :=
  rat_majority_certificate_sound certificate965 valid965 x hx0 hx1

def certificate966 : RatMajorityCertificate := ⟨0,(1004306354975158643/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(539539901550843587/1000000000000000000),false⟩
theorem valid966 : certificate966.Valid := by decide +kernel
theorem bound966 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate966.a certificate966.b certificate966.c x ≤ (certificate966.bound:ℝ) :=
  rat_majority_certificate_sound certificate966 valid966 x hx0 hx1

def certificate967 : RatMajorityCertificate := ⟨(51831002269060251/500000000000000000),(450098972524030243973838430749600607/500000000000000000000000000000000000),1,(9278115605366356759/25000000000000000000),(37112462421465427037/100000000000000000000),(539539901550843587/1000000000000000000),false⟩
theorem valid967 : certificate967.Valid := by decide +kernel
theorem bound967 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate967.a certificate967.b certificate967.c x ≤ (certificate967.bound:ℝ) :=
  rat_majority_certificate_sound certificate967 valid967 x hx0 hx1

def certificate968 : RatMajorityCertificate := ⟨0,(50000480631938011/50000000000000000),(34494439/29940000),(21537768164973512007/50000000000000000000),(8615107265989404803/20000000000000000000),(340174393341370181/500000000000000000),false⟩
theorem valid968 : certificate968.Valid := by decide +kernel
theorem bound968 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate968.a certificate968.b certificate968.c x ≤ (certificate968.bound:ℝ) :=
  rat_majority_certificate_sound certificate968 valid968 x hx0 hx1

def certificate969 : RatMajorityCertificate := ⟨(200219159061551533/1000000000000000000),(39989426447137987663814657661979137/50000000000000000000000000000000000),(34494439/29940000),(9671439749995034093/25000000000000000000),(38685758999980136373/100000000000000000000),(340174393341370181/500000000000000000),false⟩
theorem valid969 : certificate969.Valid := by decide +kernel
theorem bound969 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate969.a certificate969.b certificate969.c x ≤ (certificate969.bound:ℝ) :=
  rat_majority_certificate_sound certificate969 valid969 x hx0 hx1

def certificate970 : RatMajorityCertificate := ⟨0,(50000480631938011/50000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543619800084044591/1000000000000000000),false⟩
theorem valid970 : certificate970.Valid := by decide +kernel
theorem bound970 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate970.a certificate970.b certificate970.c x ≤ (certificate970.bound:ℝ) :=
  rat_majority_certificate_sound certificate970 valid970 x hx0 hx1

def certificate971 : RatMajorityCertificate := ⟨(159499017896987697/1000000000000000000),(42025453076766543469629631866349333/50000000000000000000000000000000000),1,(34947571939322671/97656250000000000),(7157262733173283021/20000000000000000000),(543619800084044591/1000000000000000000),false⟩
theorem valid971 : certificate971.Valid := by decide +kernel
theorem bound971 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate971.a certificate971.b certificate971.c x ≤ (certificate971.bound:ℝ) :=
  rat_majority_certificate_sound certificate971 valid971 x hx0 hx1

def certificate972 : RatMajorityCertificate := ⟨0,(500007475346239577/500000000000000000),(2755984897/2388440000),(43116961938211204729/100000000000000000000),(4311696193821120473/10000000000000000000),(682326444642234657/1000000000000000000),false⟩
theorem valid972 : certificate972.Valid := by decide +kernel
theorem bound972 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate972.a certificate972.b certificate972.c x ≤ (certificate972.bound:ℝ) :=
  rat_majority_certificate_sound certificate972 valid972 x hx0 hx1

def certificate973 : RatMajorityCertificate := ⟨(51003889836482287/250000000000000000),(99499542646582657802566448781127401/125000000000000000000000000000000000),(2755984897/2388440000),(1545157049367164511/4000000000000000000),(4828615779272389097/12500000000000000000),(682326444642234657/1000000000000000000),false⟩
theorem valid973 : certificate973.Valid := by decide +kernel
theorem bound973 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate973.a certificate973.b certificate973.c x ≤ (certificate973.bound:ℝ) :=
  rat_majority_certificate_sound certificate973 valid973 x hx0 hx1

def certificate974 : RatMajorityCertificate := ⟨0,(500007475346239577/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54355056770696903/100000000000000000),false⟩
theorem valid974 : certificate974.Valid := by decide +kernel
theorem bound974 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate974.a certificate974.b certificate974.c x ≤ (certificate974.bound:ℝ) :=
  rat_majority_certificate_sound certificate974 valid974 x hx0 hx1

def certificate975 : RatMajorityCertificate := ⟨(158887781349647581/1000000000000000000),(420562396930236959679361557455486763/500000000000000000000000000000000000),1,(3580148710177317659/10000000000000000000),(35801487101773176591/100000000000000000000),(54355056770696903/100000000000000000),false⟩
theorem valid975 : certificate975.Valid := by decide +kernel
theorem bound975 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate975.a certificate975.b certificate975.c x ≤ (certificate975.bound:ℝ) :=
  rat_majority_certificate_sound certificate975 valid975 x hx0 hx1

def certificate976 : RatMajorityCertificate := ⟨0,(100002142692181721/100000000000000000),(343972341/297740000),(43149579519230033477/100000000000000000000),(21574789759615016739/50000000000000000000),(341620167527938647/500000000000000000),false⟩
theorem valid976 : certificate976.Valid := by decide +kernel
theorem bound976 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate976.a certificate976.b certificate976.c x ≤ (certificate976.bound:ℝ) :=
  rat_majority_certificate_sound certificate976 valid976 x hx0 hx1

def certificate977 : RatMajorityCertificate := ⟨(100467384470150689/500000000000000000),(39954117628396569450306584958644231/50000000000000000000000000000000000),(343972341/297740000),(2421490951761366609/6250000000000000000),(7748771045636373149/20000000000000000000),(341620167527938647/500000000000000000),false⟩
theorem valid977 : certificate977.Valid := by decide +kernel
theorem bound977 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate977.a certificate977.b certificate977.c x ≤ (certificate977.bound:ℝ) :=
  rat_majority_certificate_sound certificate977 valid977 x hx0 hx1

def certificate978 : RatMajorityCertificate := ⟨0,(100002142692181721/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543642719927484319/1000000000000000000),false⟩
theorem valid978 : certificate978.Valid := by decide +kernel
theorem bound978 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate978.a certificate978.b certificate978.c x ≤ (certificate978.bound:ℝ) :=
  rat_majority_certificate_sound certificate978 valid978 x hx0 hx1

def certificate979 : RatMajorityCertificate := ⟨(159650069227665029/1000000000000000000),(84036793688460072765733561415265091/100000000000000000000000000000000000),1,(35782604993110652281/100000000000000000000),(17891302496555326141/50000000000000000000),(543642719927484319/1000000000000000000),false⟩
theorem valid979 : certificate979.Valid := by decide +kernel
theorem bound979 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate979.a certificate979.b certificate979.c x ≤ (certificate979.bound:ℝ) :=
  rat_majority_certificate_sound certificate979 valid979 x hx0 hx1

def certificate980 : RatMajorityCertificate := ⟨0,(1000029022280704499/1000000000000000000),(2748824071/2375610000),(10798063653373010667/25000000000000000000),(43192254613492042669/100000000000000000000),(684830005865720979/1000000000000000000),false⟩
theorem valid980 : certificate980.Valid := by decide +kernel
theorem bound980 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate980.a certificate980.b certificate980.c x ≤ (certificate980.bound:ℝ) :=
  rat_majority_certificate_sound certificate980 valid980 x hx0 hx1

def certificate981 : RatMajorityCertificate := ⟨(200568694210386499/1000000000000000000),(799454507109374091339615279201840999/1000000000000000000000000000000000000),(2748824071/2375610000),(38797762478326533231/100000000000000000000),(2424860154895408327/6250000000000000000),(684830005865720979/1000000000000000000),false⟩
theorem valid981 : certificate981.Valid := by decide +kernel
theorem bound981 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate981.a certificate981.b certificate981.c x ≤ (certificate981.bound:ℝ) :=
  rat_majority_certificate_sound certificate981 valid981 x hx0 hx1

def certificate982 : RatMajorityCertificate := ⟨0,(1000029022280704499/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(21743631751661729/40000000000000000),false⟩
theorem valid982 : certificate982.Valid := by decide +kernel
theorem bound982 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate982.a certificate982.b certificate982.c x ≤ (certificate982.bound:ℝ) :=
  rat_majority_certificate_sound certificate982 valid982 x hx0 hx1

def certificate983 : RatMajorityCertificate := ⟨(159178331246925949/1000000000000000000),(840846071315567027990783728195855449/1000000000000000000000000000000000000),1,(17897165861619640939/50000000000000000000),(35794331723239281879/100000000000000000000),(21743631751661729/40000000000000000),false⟩
theorem valid983 : certificate983.Valid := by decide +kernel
theorem bound983 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate983.a certificate983.b certificate983.c x ≤ (certificate983.bound:ℝ) :=
  rat_majority_certificate_sound certificate983 valid983 x hx0 hx1

def certificate984 : RatMajorityCertificate := ⟨0,(1000033102361922243/1000000000000000000),(457922309/395480000),(43210648021456703061/100000000000000000000),(21605324010728351531/50000000000000000000),(85680753027996917/125000000000000000),false⟩
theorem valid984 : certificate984.Valid := by decide +kernel
theorem bound984 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate984.a certificate984.b certificate984.c x ≤ (certificate984.bound:ℝ) :=
  rat_majority_certificate_sound certificate984 valid984 x hx0 hx1

def certificate985 : RatMajorityCertificate := ⟨(199737324018529339/1000000000000000000),(800289166566203862322216510067812623/1000000000000000000000000000000000000),(457922309/395480000),(3883862517051422161/10000000000000000000),(38838625170514221611/100000000000000000000),(85680753027996917/125000000000000000),false⟩
theorem valid985 : certificate985.Valid := by decide +kernel
theorem bound985 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate985.a certificate985.b certificate985.c x ≤ (certificate985.bound:ℝ) :=
  rat_majority_certificate_sound certificate985 valid985 x hx0 hx1

def certificate986 : RatMajorityCertificate := ⟨0,(1000033102361922243/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271772317471279659/500000000000000000),false⟩
theorem valid986 : certificate986.Valid := by decide +kernel
theorem bound986 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate986.a certificate986.b certificate986.c x ≤ (certificate986.bound:ℝ) :=
  rat_majority_certificate_sound certificate986 valid986 x hx0 hx1

def certificate987 : RatMajorityCertificate := ⟨(79384286778524157/500000000000000000),(420629636595045082663516278868875849/500000000000000000000000000000000000),1,(8951125233001979831/25000000000000000000),(1432180037280316773/4000000000000000000),(271772317471279659/500000000000000000),false⟩
theorem valid987 : certificate987.Valid := by decide +kernel
theorem bound987 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate987.a certificate987.b certificate987.c x ≤ (certificate987.bound:ℝ) :=
  rat_majority_certificate_sound certificate987 valid987 x hx0 hx1

def certificate988 : RatMajorityCertificate := ⟨0,(20000751353194361/20000000000000000),(2746290341/2369850000),(1351029730816786743/3125000000000000000),(43232951386137175777/100000000000000000000),(686308024633436699/1000000000000000000),false⟩
theorem valid988 : certificate988.Valid := by decide +kernel
theorem bound988 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate988.a certificate988.b certificate988.c x ≤ (certificate988.bound:ℝ) :=
  rat_majority_certificate_sound certificate988 valid988 x hx0 hx1

def certificate989 : RatMajorityCertificate := ⟨(24976915742041451/125000000000000000),(2000536837823038036609127878542189/2500000000000000000000000000000000),(2746290341/2369850000),(38859746913542552749/100000000000000000000),(155438987654170211/400000000000000000),(686308024633436699/1000000000000000000),false⟩
theorem valid989 : certificate989.Valid := by decide +kernel
theorem bound989 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate989.a certificate989.b certificate989.c x ≤ (certificate989.bound:ℝ) :=
  rat_majority_certificate_sound certificate989 valid989 x hx0 hx1

def certificate990 : RatMajorityCertificate := ⟨0,(20000751353194361/20000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108727174150171223/200000000000000000),false⟩
theorem valid990 : certificate990.Valid := by decide +kernel
theorem bound990 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate990.a certificate990.b certificate990.c x ≤ (certificate990.bound:ℝ) :=
  rat_majority_certificate_sound certificate990 valid990 x hx0 hx1

def certificate991 : RatMajorityCertificate := ⟨(159530903560342569/1000000000000000000),(16810013417933520259982862400946591/20000000000000000000000000000000000),1,(17892807787020223853/50000000000000000000),(35785615574040447707/100000000000000000000),(108727174150171223/200000000000000000),false⟩
theorem valid991 : certificate991.Valid := by decide +kernel
theorem bound991 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate991.a certificate991.b certificate991.c x ≤ (certificate991.bound:ℝ) :=
  rat_majority_certificate_sound certificate991 valid991 x hx0 hx1

def certificate992 : RatMajorityCertificate := ⟨0,(250011872821938637/250000000000000000),(2741967449/2363550000),(43262322474302372223/100000000000000000000),(337986894330487283/781250000000000000),(687491150607215387/1000000000000000000),false⟩
theorem valid992 : certificate992.Valid := by decide +kernel
theorem bound992 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate992.a certificate992.b certificate992.c x ≤ (certificate992.bound:ℝ) :=
  rat_majority_certificate_sound certificate992 valid992 x hx0 hx1

def certificate993 : RatMajorityCertificate := ⟨(626063789156221/3125000000000000),(624763722135612110435168331189223/781250000000000000000000000000000),(2741967449/2363550000),(1943826695999396789/5000000000000000000),(38876533919987935781/100000000000000000000),(687491150607215387/1000000000000000000),false⟩
theorem valid993 : certificate993.Valid := by decide +kernel
theorem bound993 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate993.a certificate993.b certificate993.c x ≤ (certificate993.bound:ℝ) :=
  rat_majority_certificate_sound certificate993 valid993 x hx0 hx1

def certificate994 : RatMajorityCertificate := ⟨0,(250011872821938637/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(6796250080435803/12500000000000000),false⟩
theorem valid994 : certificate994.Valid := by decide +kernel
theorem bound994 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate994.a certificate994.b certificate994.c x ≤ (certificate994.bound:ℝ) :=
  rat_majority_certificate_sound certificate994 valid994 x hx0 hx1

def certificate995 : RatMajorityCertificate := ⟨(32008090416132787/200000000000000000),(41999971933996424111943790242208681/50000000000000000000000000000000000),1,(44716250927970343490571/125000000000000000000000),(357730007423762747924569/1000000000000000000000000),(6796250080435803/12500000000000000),false⟩
theorem valid995 : certificate995.Valid := by decide +kernel
theorem bound995 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate995.a certificate995.b certificate995.c x ≤ (certificate995.bound:ℝ) :=
  rat_majority_certificate_sound certificate995 valid995 x hx0 hx1

def certificate996 : RatMajorityCertificate := ⟨0,(250014580983304097/250000000000000000),(1369892903/1178890000),(43306868371176741719/100000000000000000000),(1082671709279418543/2500000000000000000),(344609128905663251/500000000000000000),false⟩
theorem valid996 : certificate996.Valid := by decide +kernel
theorem bound996 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate996.a certificate996.b certificate996.c x ≤ (certificate996.bound:ℝ) :=
  rat_majority_certificate_sound certificate996 valid996 x hx0 hx1

def certificate997 : RatMajorityCertificate := ⟨(200484898791050733/1000000000000000000),(199890433018579417862442327306246899/250000000000000000000000000000000000),(1369892903/1178890000),(7783807847033085009/20000000000000000000),(19459519617582712523/50000000000000000000),(344609128905663251/500000000000000000),false⟩
theorem valid997 : certificate997.Valid := by decide +kernel
theorem bound997 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate997.a certificate997.b certificate997.c x ≤ (certificate997.bound:ℝ) :=
  rat_majority_certificate_sound certificate997 valid997 x hx0 hx1

def certificate998 : RatMajorityCertificate := ⟨0,(250014580983304097/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(849437034629871/1562500000000000),false⟩
theorem valid998 : certificate998.Valid := by decide +kernel
theorem bound998 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate998.a certificate998.b certificate998.c x ≤ (certificate998.bound:ℝ) :=
  rat_majority_certificate_sound certificate998 valid998 x hx0 hx1

def certificate999 : RatMajorityCertificate := ⟨(7974272841360381/50000000000000000),(10507044566085947410139526309219043/12500000000000000000000000000000000),1,(178934060438528108725301/500000000000000000000000),(357868120877056217450603/1000000000000000000000000),(849437034629871/1562500000000000),false⟩
theorem valid999 : certificate999.Valid := by decide +kernel
theorem bound999 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate999.a certificate999.b certificate999.c x ≤ (certificate999.bound:ℝ) :=
  rat_majority_certificate_sound certificate999 valid999 x hx0 hx1

end Cycle12.MajorityCertificates.Batch024
