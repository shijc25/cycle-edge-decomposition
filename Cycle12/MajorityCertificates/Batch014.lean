import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch014

def certificate560 : RatMajorityCertificate := ⟨0,(252124703376467977/250000000000000000),(2271974151/1945240000),(4344477063548268351/10000000000000000000),(43444770635482683511/100000000000000000000),(348674885350933607/500000000000000000),false⟩
theorem valid560 : certificate560.Valid := by decide +kernel
theorem bound560 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate560.a certificate560.b certificate560.c x ≤ (certificate560.bound:ℝ) :=
  rat_majority_certificate_sound certificate560 valid560 x hx0 hx1

def certificate561 : RatMajorityCertificate := ⟨(2847781243932851/15625000000000000),(3221452488849673086464803060187573/3906250000000000000000000000000000),(2271974151/1945240000),(19780872646567583021/50000000000000000000),(39561745293135166043/100000000000000000000),(348674885350933607/500000000000000000),false⟩
theorem valid561 : certificate561.Valid := by decide +kernel
theorem bound561 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate561.a certificate561.b certificate561.c x ≤ (certificate561.bound:ℝ) :=
  rat_majority_certificate_sound certificate561 valid561 x hx0 hx1

def certificate562 : RatMajorityCertificate := ⟨0,(252124703376467977/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108651037840991079/200000000000000000),false⟩
theorem valid562 : certificate562.Valid := by decide +kernel
theorem bound562 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate562.a certificate562.b certificate562.c x ≤ (certificate562.bound:ℝ) :=
  rat_majority_certificate_sound certificate562 valid562 x hx0 hx1

def certificate563 : RatMajorityCertificate := ⟨(15136176487749271/125000000000000000),(27699383914830843293800553663405233/31250000000000000000000000000000000),1,(36727221500116909761/100000000000000000000),(18363610750058454881/50000000000000000000),(108651037840991079/200000000000000000),false⟩
theorem valid563 : certificate563.Valid := by decide +kernel
theorem bound563 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate563.a certificate563.b certificate563.c x ≤ (certificate563.bound:ℝ) :=
  rat_majority_certificate_sound certificate563 valid563 x hx0 hx1

def certificate564 : RatMajorityCertificate := ⟨0,(1008519748273701313/1000000000000000000),(9462007/8104125),(2714703246721467511/6250000000000000000),(43435251947543480177/100000000000000000000),(696935170085942903/1000000000000000000),false⟩
theorem valid564 : certificate564.Valid := by decide +kernel
theorem bound564 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate564.a certificate564.b certificate564.c x ≤ (certificate564.bound:ℝ) :=
  rat_majority_certificate_sound certificate564 valid564 x hx0 hx1

def certificate565 : RatMajorityCertificate := ⟨(22707838511003857/125000000000000000),(103163664955255193820478243391035759/125000000000000000000000000000000000),(9462007/8104125),(39566865532230277129/100000000000000000000),(3956686553223027713/10000000000000000000),(696935170085942903/1000000000000000000),false⟩
theorem valid565 : certificate565.Valid := by decide +kernel
theorem bound565 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate565.a certificate565.b certificate565.c x ≤ (certificate565.bound:ℝ) :=
  rat_majority_certificate_sound certificate565 valid565 x hx0 hx1

def certificate566 : RatMajorityCertificate := ⟨0,(1008519748273701313/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543256912610338729/1000000000000000000),false⟩
theorem valid566 : certificate566.Valid := by decide +kernel
theorem bound566 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate566.a certificate566.b certificate566.c x ≤ (certificate566.bound:ℝ) :=
  rat_majority_certificate_sound certificate566 valid566 x hx0 hx1

def certificate567 : RatMajorityCertificate := ⟨(24202234067185133/200000000000000000),(177295518645641513955771614883820371/200000000000000000000000000000000000),1,(183645339026857111677347/500000000000000000000000),(73458135610742844670939/200000000000000000000000),(543256912610338729/1000000000000000000),false⟩
theorem valid567 : certificate567.Valid := by decide +kernel
theorem bound567 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate567.a certificate567.b certificate567.c x ≤ (certificate567.bound:ℝ) :=
  rat_majority_certificate_sound certificate567 valid567 x hx0 hx1

def certificate568 : RatMajorityCertificate := ⟨0,(1008540651010050701/1000000000000000000),(162160387/138910000),(5428894405388032417/12500000000000000000),(43431155243104259337/100000000000000000000),(139391386603653449/200000000000000000),false⟩
theorem valid568 : certificate568.Valid := by decide +kernel
theorem bound568 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate568.a certificate568.b certificate568.c x ≤ (certificate568.bound:ℝ) :=
  rat_majority_certificate_sound certificate568 valid568 x hx0 hx1

def certificate569 : RatMajorityCertificate := ⟨(5734811228922611/31250000000000000),(25733105093826725406736895284699689/31250000000000000000000000000000000),(162160387/138910000),(7903267234342273321/20000000000000000000),(19758168085855683303/50000000000000000000),(139391386603653449/200000000000000000),false⟩
theorem valid569 : certificate569.Valid := by decide +kernel
theorem bound569 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate569.a certificate569.b certificate569.c x ≤ (certificate569.bound:ℝ) :=
  rat_majority_certificate_sound certificate569 valid569 x hx0 hx1

def certificate570 : RatMajorityCertificate := ⟨0,(1008540651010050701/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67906742002830693/125000000000000000),false⟩
theorem valid570 : certificate570.Valid := by decide +kernel
theorem bound570 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate570.a certificate570.b certificate570.c x ≤ (certificate570.bound:ℝ) :=
  rat_majority_certificate_sound certificate570 valid570 x hx0 hx1

def certificate571 : RatMajorityCertificate := ⟨(120886839987059959/1000000000000000000),(886621358710953420890561907483018741/1000000000000000000000000000000000000),1,(36731971136654752011/100000000000000000000),(9182992784163688003/25000000000000000000),(67906742002830693/125000000000000000),false⟩
theorem valid571 : certificate571.Valid := by decide +kernel
theorem bound571 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate571.a certificate571.b certificate571.c x ≤ (certificate571.bound:ℝ) :=
  rat_majority_certificate_sound certificate571 valid571 x hx0 hx1

def certificate572 : RatMajorityCertificate := ⟨0,(1008561521440750483/1000000000000000000),(1134381907/972245000),(43416994564039698417/100000000000000000000),(21708497282019849209/50000000000000000000),(69617132500834241/100000000000000000),false⟩
theorem valid572 : certificate572.Valid := by decide +kernel
theorem bound572 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate572.a certificate572.b certificate572.c x ≤ (certificate572.bound:ℝ) :=
  rat_majority_certificate_sound certificate572 valid572 x hx0 hx1

def certificate573 : RatMajorityCertificate := ⟨(180847698411186909/1000000000000000000),(826165491582105820219502448254972953/1000000000000000000000000000000000000),(1134381907/972245000),(19784247265013995681/50000000000000000000),(39568494530027991363/100000000000000000000),(69617132500834241/100000000000000000),false⟩
theorem valid573 : certificate573.Valid := by decide +kernel
theorem bound573 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate573.a certificate573.b certificate573.c x ≤ (certificate573.bound:ℝ) :=
  rat_majority_certificate_sound certificate573 valid573 x hx0 hx1

def certificate574 : RatMajorityCertificate := ⟨0,(1008561521440750483/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271616591619311811/500000000000000000),false⟩
theorem valid574 : certificate574.Valid := by decide +kernel
theorem bound574 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate574.a certificate574.b certificate574.c x ≤ (certificate574.bound:ℝ) :=
  rat_majority_certificate_sound certificate574 valid574 x hx0 hx1

def certificate575 : RatMajorityCertificate := ⟨(120587723527028103/1000000000000000000),(886941383533254437440167237048176251/1000000000000000000000000000000000000),1,(3673888204934775097/10000000000000000000),(36738882049347750971/100000000000000000000),(271616591619311811/500000000000000000),false⟩
theorem valid575 : certificate575.Valid := by decide +kernel
theorem bound575 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate575.a certificate575.b certificate575.c x ≤ (certificate575.bound:ℝ) :=
  rat_majority_certificate_sound certificate575 valid575 x hx0 hx1

def certificate576 : RatMajorityCertificate := ⟨0,(201716471858396247/200000000000000000),(188952733/162020000),(10851153995105003551/25000000000000000000),(8680923196084002841/20000000000000000000),(34778159961783693/50000000000000000),false⟩
theorem valid576 : certificate576.Valid := by decide +kernel
theorem bound576 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate576.a certificate576.b certificate576.c x ≤ (certificate576.bound:ℝ) :=
  rat_majority_certificate_sound certificate576 valid576 x hx0 hx1

def certificate577 : RatMajorityCertificate := ⟨(179346822501041237/1000000000000000000),(165539263584472175500616421566962461/200000000000000000000000000000000000),(188952733/162020000),(39593185954244901413/100000000000000000000),(19796592977122450707/50000000000000000000),(34778159961783693/50000000000000000),false⟩
theorem valid577 : certificate577.Valid := by decide +kernel
theorem bound577 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate577.a certificate577.b certificate577.c x ≤ (certificate577.bound:ℝ) :=
  rat_majority_certificate_sound certificate577 valid577 x hx0 hx1

def certificate578 : RatMajorityCertificate := ⟨0,(201716471858396247/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271614053843481461/500000000000000000),false⟩
theorem valid578 : certificate578.Valid := by decide +kernel
theorem bound578 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate578.a certificate578.b certificate578.c x ≤ (certificate578.bound:ℝ) :=
  rat_majority_certificate_sound certificate578 valid578 x hx0 hx1

def certificate579 : RatMajorityCertificate := ⟨(120442815434491681/1000000000000000000),(177421172068258592682740915676878793/200000000000000000000000000000000000),1,(9185563620747151833/25000000000000000000),(36742254482988607333/100000000000000000000),(271614053843481461/500000000000000000),false⟩
theorem valid579 : certificate579.Valid := by decide +kernel
theorem bound579 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate579.a certificate579.b certificate579.c x ≤ (certificate579.bound:ℝ) :=
  rat_majority_certificate_sound certificate579 valid579 x hx0 hx1

def certificate580 : RatMajorityCertificate := ⟨0,(504301559869757873/500000000000000000),(6996131/6000000),(21699886341301879691/50000000000000000000),(43399772682603759383/100000000000000000000),(695436975695481491/1000000000000000000),false⟩
theorem valid580 : certificate580.Valid := by decide +kernel
theorem bound580 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate580.a certificate580.b certificate580.c x ≤ (certificate580.bound:ℝ) :=
  rat_majority_certificate_sound certificate580 valid580 x hx0 hx1

def certificate581 : RatMajorityCertificate := ⟨(22488406092791707/125000000000000000),(51696756712140309372202031287640789/62500000000000000000000000000000000),(6996131/6000000),(39574294142637157277/100000000000000000000),(19787147071318578639/50000000000000000000),(695436975695481491/1000000000000000000),false⟩
theorem valid581 : certificate581.Valid := by decide +kernel
theorem bound581 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate581.a certificate581.b certificate581.c x ≤ (certificate581.bound:ℝ) :=
  rat_majority_certificate_sound certificate581 valid581 x hx0 hx1

def certificate582 : RatMajorityCertificate := ⟨0,(504301559869757873/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108644604479267031/200000000000000000),false⟩
theorem valid582 : certificate582.Valid := by decide +kernel
theorem bound582 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate582.a certificate582.b certificate582.c x ≤ (certificate582.bound:ℝ) :=
  rat_majority_certificate_sound certificate582 valid582 x hx0 hx1

def certificate583 : RatMajorityCertificate := ⟨(60149038821125433/500000000000000000),(221817525832718758435493468927715991/250000000000000000000000000000000000),1,(2296601364870654583/6250000000000000000),(36745621837930473329/100000000000000000000),(108644604479267031/200000000000000000),false⟩
theorem valid583 : certificate583.Valid := by decide +kernel
theorem bound583 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate583.a certificate583.b certificate583.c x ≤ (certificate583.bound:ℝ) :=
  rat_majority_certificate_sound certificate583 valid583 x hx0 hx1

def certificate584 : RatMajorityCertificate := ⟨0,(100862389149774643/100000000000000000),(1132951183/971875000),(21696592939863918913/50000000000000000000),(43393185879727837827/100000000000000000000),(69520201003090247/100000000000000000),false⟩
theorem valid584 : certificate584.Valid := by decide +kernel
theorem bound584 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate584.a certificate584.b certificate584.c x ≤ (certificate584.bound:ℝ) :=
  rat_majority_certificate_sound certificate584 valid584 x hx0 hx1

def certificate585 : RatMajorityCertificate := ⟨(5625598983083301/31250000000000000),(2584538307098133189531446553463457/3125000000000000000000000000000000),(1132951183/971875000),(39564769171116044229/100000000000000000000),(3956476917111604423/10000000000000000000),(69520201003090247/100000000000000000),false⟩
theorem valid585 : certificate585.Valid := by decide +kernel
theorem bound585 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate585.a certificate585.b certificate585.c x ≤ (certificate585.bound:ℝ) :=
  rat_majority_certificate_sound certificate585 valid585 x hx0 hx1

def certificate586 : RatMajorityCertificate := ⟨0,(100862389149774643/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135804535668866737/250000000000000000),false⟩
theorem valid586 : certificate586.Valid := by decide +kernel
theorem bound586 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate586.a certificate586.b certificate586.c x ≤ (certificate586.bound:ℝ) :=
  rat_majority_certificate_sound certificate586 valid586 x hx0 hx1

def certificate587 : RatMajorityCertificate := ⟨(30038806808278107/250000000000000000),(22185811465552214335726554079359199/25000000000000000000000000000000000),1,(7349788998443117459/20000000000000000000),(1148404531006737103/3125000000000000000),(135804535668866737/250000000000000000),false⟩
theorem valid587 : certificate587.Valid := by decide +kernel
theorem bound587 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate587.a certificate587.b certificate587.c x ≤ (certificate587.bound:ℝ) :=
  rat_majority_certificate_sound certificate587 valid587 x hx0 hx1

def certificate588 : RatMajorityCertificate := ⟨0,(504322292539563367/500000000000000000),(5866069/5035000),(4337744248982646747/10000000000000000000),(43377442489826467471/100000000000000000000),(138881576284516671/200000000000000000),false⟩
theorem valid588 : certificate588.Valid := by decide +kernel
theorem bound588 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate588.a certificate588.b certificate588.c x ≤ (certificate588.bound:ℝ) :=
  rat_majority_certificate_sound certificate588 valid588 x hx0 hx1

def certificate589 : RatMajorityCertificate := ⟨(35581303016182499/200000000000000000),(82920014199246634756373607353085867/100000000000000000000000000000000000),(5866069/5035000),(1237535291604621177/3125000000000000000),(7920225866269575533/20000000000000000000),(138881576284516671/200000000000000000),false⟩
theorem valid589 : certificate589.Valid := by decide +kernel
theorem bound589 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate589.a certificate589.b certificate589.c x ≤ (certificate589.bound:ℝ) :=
  rat_majority_certificate_sound certificate589 valid589 x hx0 hx1

def certificate590 : RatMajorityCertificate := ⟨0,(504322292539563367/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543218064017740693/1000000000000000000),false⟩
theorem valid590 : certificate590.Valid := by decide +kernel
theorem bound590 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate590.a certificate590.b certificate590.c x ≤ (certificate590.bound:ℝ) :=
  rat_majority_certificate_sound certificate590 valid590 x hx0 hx1

def certificate591 : RatMajorityCertificate := ⟨(60029988129122649/500000000000000000),(221886685035379774691289044749600817/250000000000000000000000000000000000),1,(7350235343187423557/20000000000000000000),(18375588357968558893/50000000000000000000),(543218064017740693/1000000000000000000),false⟩
theorem valid591 : certificate591.Valid := by decide +kernel
theorem bound591 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate591.a certificate591.b certificate591.c x ≤ (certificate591.bound:ℝ) :=
  rat_majority_certificate_sound certificate591 valid591 x hx0 hx1

def certificate592 : RatMajorityCertificate := ⟨0,(63041577797654527/62500000000000000),(141479456/121454375),(43373245157087623839/100000000000000000000),(271082782231797649/625000000000000000),(694319723902860211/1000000000000000000),false⟩
theorem valid592 : certificate592.Valid := by decide +kernel
theorem bound592 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate592.a certificate592.b certificate592.c x ≤ (certificate592.bound:ℝ) :=
  rat_majority_certificate_sound certificate592 valid592 x hx0 hx1

def certificate593 : RatMajorityCertificate := ⟨(44652204288580277/250000000000000000),(12945449038918335105508298648036021/15625000000000000000000000000000000),(141479456/121454375),(39579415516992687283/100000000000000000000),(9894853879248171821/25000000000000000000),(694319723902860211/1000000000000000000),false⟩
theorem valid593 : certificate593.Valid := by decide +kernel
theorem bound593 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate593.a certificate593.b certificate593.c x ≤ (certificate593.bound:ℝ) :=
  rat_majority_certificate_sound certificate593 valid593 x hx0 hx1

def certificate594 : RatMajorityCertificate := ⟨0,(63041577797654527/62500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67898722563572523/125000000000000000),false⟩
theorem valid594 : certificate594.Valid := by decide +kernel
theorem bound594 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate594.a certificate594.b certificate594.c x ≤ (certificate594.bound:ℝ) :=
  rat_majority_certificate_sound certificate594 valid594 x hx0 hx1

def certificate595 : RatMajorityCertificate := ⟨(59843310159378159/500000000000000000),(27748172205745655757990176968724207/31250000000000000000000000000000000),1,(36759775474671948721/100000000000000000000),(18379887737335974361/50000000000000000000),(67898722563572523/125000000000000000),false⟩
theorem valid595 : certificate595.Valid := by decide +kernel
theorem bound595 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate595.a certificate595.b certificate595.c x ≤ (certificate595.bound:ℝ) :=
  rat_majority_certificate_sound certificate595 valid595 x hx0 hx1

def certificate596 : RatMajorityCertificate := ⟨0,(201737165054414713/200000000000000000),(2263058477/1943040000),(43369128099531181503/100000000000000000000),(677642626555174711/1562500000000000000),(694239671716377411/1000000000000000000),false⟩
theorem valid596 : certificate596.Valid := by decide +kernel
theorem bound596 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate596.a certificate596.b certificate596.c x ≤ (certificate596.bound:ℝ) :=
  rat_majority_certificate_sound certificate596 valid596 x hx0 hx1

def certificate597 : RatMajorityCertificate := ⟨(11210246609209629/62500000000000000),(10347049445398103765438849881128523/12500000000000000000000000000000000),(2263058477/1943040000),(39556444933746339911/100000000000000000000),(4944555616718292489/12500000000000000000),(694239671716377411/1000000000000000000),false⟩
theorem valid597 : certificate597.Valid := by decide +kernel
theorem bound597 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate597.a certificate597.b certificate597.c x ≤ (certificate597.bound:ℝ) :=
  rat_majority_certificate_sound certificate597 valid597 x hx0 hx1

def certificate598 : RatMajorityCertificate := ⟨0,(201737165054414713/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543184242693662291/1000000000000000000),false⟩
theorem valid598 : certificate598.Valid := by decide +kernel
theorem bound598 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate598.a certificate598.b certificate598.c x ≤ (certificate598.bound:ℝ) :=
  rat_majority_certificate_sound certificate598 valid598 x hx0 hx1

def certificate599 : RatMajorityCertificate := ⟨(59768902907645257/500000000000000000),(88810973496206437829079212834533759/100000000000000000000000000000000000),1,(18381615311678043841/50000000000000000000),(36763230623356087683/100000000000000000000),(543184242693662291/1000000000000000000),false⟩
theorem valid599 : certificate599.Valid := by decide +kernel
theorem bound599 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate599.a certificate599.b certificate599.c x ≤ (certificate599.bound:ℝ) :=
  rat_majority_certificate_sound certificate599 valid599 x hx0 hx1

end Cycle12.MajorityCertificates.Batch014
