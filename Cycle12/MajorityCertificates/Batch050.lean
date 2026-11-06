import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch050

def certificate2000 : RatMajorityCertificate := ⟨0,(1000045353298101759/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(273418181312679157/500000000000000000),false⟩
theorem valid2000 : certificate2000.Valid := by decide +kernel
theorem bound2000 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2000.a certificate2000.b certificate2000.c x ≤ (certificate2000.bound:ℝ) :=
  rat_majority_certificate_sound certificate2000 valid2000 x hx0 hx1

def certificate2001 : RatMajorityCertificate := ⟨(46477199644940593/250000000000000000),(203532030785294414791734704776196913/250000000000000000000000000000000000),1,(35114735409588193479/100000000000000000000),(877868385239704837/2500000000000000000),(273418181312679157/500000000000000000),false⟩
theorem valid2001 : certificate2001.Valid := by decide +kernel
theorem bound2001 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2001.a certificate2001.b certificate2001.c x ≤ (certificate2001.bound:ℝ) :=
  rat_majority_certificate_sound certificate2001 valid2001 x hx0 hx1

def certificate2002 : RatMajorityCertificate := ⟨0,(25001152239924191/25000000000000000),(1422574443/1175000000),(44412963734039169777/100000000000000000000),(22206481867019584889/50000000000000000000),(730593172656412379/1000000000000000000),false⟩
theorem valid2002 : certificate2002.Valid := by decide +kernel
theorem bound2002 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2002.a certificate2002.b certificate2002.c x ≤ (certificate2002.bound:ℝ) :=
  rat_majority_certificate_sound certificate2002 valid2002 x hx0 hx1

def certificate2003 : RatMajorityCertificate := ⟨(87487522512970189/500000000000000000),(10313287250521532771823612397057901/12500000000000000000000000000000000),(1422574443/1175000000),(20357568900245904813/50000000000000000000),(40715137800491809627/100000000000000000000),(730593172656412379/1000000000000000000),false⟩
theorem valid2003 : certificate2003.Valid := by decide +kernel
theorem bound2003 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2003.a certificate2003.b certificate2003.c x ≤ (certificate2003.bound:ℝ) :=
  rat_majority_certificate_sound certificate2003 valid2003 x hx0 hx1

def certificate2004 : RatMajorityCertificate := ⟨0,(25001152239924191/25000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275898124452450021/500000000000000000),false⟩
theorem valid2004 : certificate2004.Valid := by decide +kernel
theorem bound2004 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2004.a certificate2004.b certificate2004.c x ≤ (certificate2004.bound:ℝ) :=
  rat_majority_certificate_sound certificate2004 valid2004 x hx0 hx1

def certificate2005 : RatMajorityCertificate := ⟨(22359636356260689/100000000000000000),(1941098551420201798856238406572401/2500000000000000000000000000000000),1,(17047540973277611089/50000000000000000000),(34095081946555222179/100000000000000000000),(275898124452450021/500000000000000000),false⟩
theorem valid2005 : certificate2005.Valid := by decide +kernel
theorem bound2005 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2005.a certificate2005.b certificate2005.c x ≤ (certificate2005.bound:ℝ) :=
  rat_majority_certificate_sound certificate2005 valid2005 x hx0 hx1

def certificate2006 : RatMajorityCertificate := ⟨0,(25001152239924191/25000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(273346432785170621/500000000000000000),false⟩
theorem valid2006 : certificate2006.Valid := by decide +kernel
theorem bound2006 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2006.a certificate2006.b certificate2006.c x ≤ (certificate2006.bound:ℝ) :=
  rat_majority_certificate_sound certificate2006 valid2006 x hx0 hx1

def certificate2007 : RatMajorityCertificate := ⟨(184759496189190169/1000000000000000000),(20381951947926554175166277757521721/25000000000000000000000000000000000),1,(878616859175517561/2500000000000000000),(35144674367020702441/100000000000000000000),(273346432785170621/500000000000000000),false⟩
theorem valid2007 : certificate2007.Valid := by decide +kernel
theorem bound2007 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2007.a certificate2007.b certificate2007.c x ≤ (certificate2007.bound:ℝ) :=
  rat_majority_certificate_sound certificate2007 valid2007 x hx0 hx1

def certificate2008 : RatMajorityCertificate := ⟨0,(500023908532324389/500000000000000000),(2846382657/2350000000),(22212305794618156717/50000000000000000000),(8884922317847262687/20000000000000000000),(146210282378992557/200000000000000000),false⟩
theorem valid2008 : certificate2008.Valid := by decide +kernel
theorem bound2008 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2008.a certificate2008.b certificate2008.c x ≤ (certificate2008.bound:ℝ) :=
  rat_majority_certificate_sound certificate2008 valid2008 x hx0 hx1

def certificate2009 : RatMajorityCertificate := ⟨(87373384997226391/500000000000000000),(206323172798149501527933666716249901/250000000000000000000000000000000000),(2846382657/2350000000),(10183213860693525337/25000000000000000000),(40732855442774101349/100000000000000000000),(146210282378992557/200000000000000000),false⟩
theorem valid2009 : certificate2009.Valid := by decide +kernel
theorem bound2009 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2009.a certificate2009.b certificate2009.c x ≤ (certificate2009.bound:ℝ) :=
  rat_majority_certificate_sound certificate2009 valid2009 x hx0 hx1

def certificate2010 : RatMajorityCertificate := ⟨0,(500023908532324389/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(13796634774855699/25000000000000000),false⟩
theorem valid2010 : certificate2010.Valid := by decide +kernel
theorem bound2010 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2010.a certificate2010.b certificate2010.c x ≤ (certificate2010.bound:ℝ) :=
  rat_majority_certificate_sound certificate2010 valid2010 x hx0 hx1

def certificate2011 : RatMajorityCertificate := ⟨(56022877051155591/250000000000000000),(96993199182736418925851850276991101/125000000000000000000000000000000000),1,(1704059112764230183/5000000000000000000),(34081182255284603661/100000000000000000000),(13796634774855699/25000000000000000),false⟩
theorem valid2011 : certificate2011.Valid := by decide +kernel
theorem bound2011 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2011.a certificate2011.b certificate2011.c x ≤ (certificate2011.bound:ℝ) :=
  rat_majority_certificate_sound certificate2011 valid2011 x hx0 hx1

def certificate2012 : RatMajorityCertificate := ⟨0,(500023908532324389/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(546603184474967013/1000000000000000000),false⟩
theorem valid2012 : certificate2012.Valid := by decide +kernel
theorem bound2012 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2012.a certificate2012.b certificate2012.c x ≤ (certificate2012.bound:ℝ) :=
  rat_majority_certificate_sound certificate2012 valid2012 x hx0 hx1

def certificate2013 : RatMajorityCertificate := ⟨(184035155974931429/1000000000000000000),(408001930534383223880520395740678119/500000000000000000000000000000000000),1,(7032702861819745369/20000000000000000000),(17581757154549363423/50000000000000000000),(546603184474967013/1000000000000000000),false⟩
theorem valid2013 : certificate2013.Valid := by decide +kernel
theorem bound2013 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2013.a certificate2013.b certificate2013.c x ≤ (certificate2013.bound:ℝ) :=
  rat_majority_certificate_sound certificate2013 valid2013 x hx0 hx1

def certificate2014 : RatMajorityCertificate := ⟨0,(100004929967488637/100000000000000000),(2848664371/2350000000),(11111534332623288161/25000000000000000000),(8889227466098630529/20000000000000000000),(22870367767652393/31250000000000000),false⟩
theorem valid2014 : certificate2014.Valid := by decide +kernel
theorem bound2014 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2014.a certificate2014.b certificate2014.c x ≤ (certificate2014.bound:ℝ) :=
  rat_majority_certificate_sound certificate2014 valid2014 x hx0 hx1

def certificate2015 : RatMajorityCertificate := ⟨(86898189514036371/500000000000000000),(41312217627091555784024600052783673/50000000000000000000000000000000000),(2848664371/2350000000),(50973239131379899840191/125000000000000000000000),(407785913051039198721529/1000000000000000000000000),(22870367767652393/31250000000000000),false⟩
theorem valid2015 : certificate2015.Valid := by decide +kernel
theorem bound2015 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2015.a certificate2015.b certificate2015.c x ≤ (certificate2015.bound:ℝ) :=
  rat_majority_certificate_sound certificate2015 valid2015 x hx0 hx1

def certificate2016 : RatMajorityCertificate := ⟨0,(100004929967488637/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(34495431803370447/62500000000000000),false⟩
theorem valid2016 : certificate2016.Valid := by decide +kernel
theorem bound2016 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2016.a certificate2016.b certificate2016.c x ≤ (certificate2016.bound:ℝ) :=
  rat_majority_certificate_sound certificate2016 valid2016 x hx0 hx1

def certificate2017 : RatMajorityCertificate := ⟨(44906335865073727/200000000000000000),(15510131020214506072835220960259901/20000000000000000000000000000000000),1,(34068813946216320523/100000000000000000000),(8517203486554080131/25000000000000000000),(34495431803370447/62500000000000000),false⟩
theorem valid2017 : certificate2017.Valid := by decide +kernel
theorem bound2017 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2017.a certificate2017.b certificate2017.c x ≤ (certificate2017.bound:ℝ) :=
  rat_majority_certificate_sound certificate2017 valid2017 x hx0 hx1

def certificate2018 : RatMajorityCertificate := ⟨0,(100004929967488637/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(273160576397673219/500000000000000000),false⟩
theorem valid2018 : certificate2018.Valid := by decide +kernel
theorem bound2018 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2018.a certificate2018.b certificate2018.c x ≤ (certificate2018.bound:ℝ) :=
  rat_majority_certificate_sound certificate2018 valid2018 x hx0 hx1

def certificate2019 : RatMajorityCertificate := ⟨(181762040227369181/1000000000000000000),(81827829863802729639390271978503703/100000000000000000000000000000000000),1,(35222453101643425217/100000000000000000000),(17611226550821712609/50000000000000000000),(273160576397673219/500000000000000000),false⟩
theorem valid2019 : certificate2019.Valid := by decide +kernel
theorem bound2019 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2019.a certificate2019.b certificate2019.c x ≤ (certificate2019.bound:ℝ) :=
  rat_majority_certificate_sound certificate2019 valid2019 x hx0 hx1

def certificate2020 : RatMajorityCertificate := ⟨0,(40002031219450759/40000000000000000),(2850948441/2350000000),(1389614532410005407/3125000000000000000),(1778706601484806921/4000000000000000000),(366326679764180567/500000000000000000),false⟩
theorem valid2020 : certificate2020.Valid := by decide +kernel
theorem bound2020 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2020.a certificate2020.b certificate2020.c x ≤ (certificate2020.bound:ℝ) :=
  rat_majority_certificate_sound certificate2020 valid2020 x hx0 hx1

def certificate2021 : RatMajorityCertificate := ⟨(43210044970657509/250000000000000000),(8272018236952576819364297920900669/10000000000000000000000000000000000),(2850948441/2350000000),(10206105345642178529/25000000000000000000),(40824421382568714117/100000000000000000000),(366326679764180567/500000000000000000),false⟩
theorem valid2021 : certificate2021.Valid := by decide +kernel
theorem bound2021 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2021.a certificate2021.b certificate2021.c x ≤ (certificate2021.bound:ℝ) :=
  rat_majority_certificate_sound certificate2021 valid2021 x hx0 hx1

def certificate2022 : RatMajorityCertificate := ⟨0,(40002031219450759/40000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(110398133457008629/200000000000000000),false⟩
theorem valid2022 : certificate2022.Valid := by decide +kernel
theorem bound2022 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2022.a certificate2022.b certificate2022.c x ≤ (certificate2022.bound:ℝ) :=
  rat_majority_certificate_sound certificate2022 valid2022 x hx0 hx1

def certificate2023 : RatMajorityCertificate := ⟨(224987515430235997/1000000000000000000),(31002073603223799284000591909228277/40000000000000000000000000000000000),1,(1702799685032685943/5000000000000000000),(34055993700653718861/100000000000000000000),(110398133457008629/200000000000000000),false⟩
theorem valid2023 : certificate2023.Valid := by decide +kernel
theorem bound2023 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2023.a certificate2023.b certificate2023.c x ≤ (certificate2023.bound:ℝ) :=
  rat_majority_certificate_sound certificate2023 valid2023 x hx0 hx1

def certificate2024 : RatMajorityCertificate := ⟨0,(40002031219450759/40000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109208707424157671/200000000000000000),false⟩
theorem valid2024 : certificate2024.Valid := by decide +kernel
theorem bound2024 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2024.a certificate2024.b certificate2024.c x ≤ (certificate2024.bound:ℝ) :=
  rat_majority_certificate_sound certificate2024 valid2024 x hx0 hx1

def certificate2025 : RatMajorityCertificate := ⟨(44877867323314633/250000000000000000),(8205301955133088731577682392343553/10000000000000000000000000000000000),1,(1764027807397569847/5000000000000000000),(35280556147951396941/100000000000000000000),(109208707424157671/200000000000000000),false⟩
theorem valid2025 : certificate2025.Valid := by decide +kernel
theorem bound2025 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2025.a certificate2025.b certificate2025.c x ≤ (certificate2025.bound:ℝ) :=
  rat_majority_certificate_sound certificate2025 valid2025 x hx0 hx1

def certificate2026 : RatMajorityCertificate := ⟨0,(1000052258243293749/1000000000000000000),(568894161/470000000),(8881311909439136521/20000000000000000000),(22203279773597841303/50000000000000000000),(730054042456525011/1000000000000000000),false⟩
theorem valid2026 : certificate2026.Valid := by decide +kernel
theorem bound2026 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2026.a certificate2026.b certificate2026.c x ≤ (certificate2026.bound:ℝ) :=
  rat_majority_certificate_sound certificate2026 valid2026 x hx0 hx1

def certificate2027 : RatMajorityCertificate := ⟨(34357660489670277/200000000000000000),(165650995688007599583263476534801527/200000000000000000000000000000000000),(568894161/470000000),(20393434795383408343/50000000000000000000),(40786869590766816687/100000000000000000000),(730054042456525011/1000000000000000000),false⟩
theorem valid2027 : certificate2027.Valid := by decide +kernel
theorem bound2027 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2027.a certificate2027.b certificate2027.c x ≤ (certificate2027.bound:ℝ) :=
  rat_majority_certificate_sound certificate2027 valid2027 x hx0 hx1

def certificate2028 : RatMajorityCertificate := ⟨0,(1000052258243293749/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(552023635437420207/1000000000000000000),false⟩
theorem valid2028 : certificate2028.Valid := by decide +kernel
theorem bound2028 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2028.a certificate2028.b certificate2028.c x ≤ (certificate2028.bound:ℝ) :=
  rat_majority_certificate_sound certificate2028 valid2028 x hx0 hx1

def certificate2029 : RatMajorityCertificate := ⟨(1759538567940577/7812500000000000),(6053277749190587240685279812446827/7812500000000000000000000000000000),1,(8512356950385537947/25000000000000000000),(34049427801542151789/100000000000000000000),(552023635437420207/1000000000000000000),false⟩
theorem valid2029 : certificate2029.Valid := by decide +kernel
theorem bound2029 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2029.a certificate2029.b certificate2029.c x ≤ (certificate2029.bound:ℝ) :=
  rat_majority_certificate_sound certificate2029 valid2029 x hx0 hx1

def certificate2030 : RatMajorityCertificate := ⟨0,(1000052258243293749/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(545714090904262353/1000000000000000000),false⟩
theorem valid2030 : certificate2030.Valid := by decide +kernel
theorem bound2030 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2030.a certificate2030.b certificate2030.c x ≤ (certificate2030.bound:ℝ) :=
  rat_majority_certificate_sound certificate2030 valid2030 x hx0 hx1

def certificate2031 : RatMajorityCertificate := ⟨(35364964101164717/200000000000000000),(164643639436595959434796234734545967/200000000000000000000000000000000000),1,(17674795711166453541/50000000000000000000),(35349591422332907083/100000000000000000000),(545714090904262353/1000000000000000000),false⟩
theorem valid2031 : certificate2031.Valid := by decide +kernel
theorem bound2031 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2031.a certificate2031.b certificate2031.c x ≤ (certificate2031.bound:ℝ) :=
  rat_majority_certificate_sound certificate2031 valid2031 x hx0 hx1

def certificate2032 : RatMajorityCertificate := ⟨0,(200010746339373559/200000000000000000),(1427762549/1175000000),(4451073977808923983/10000000000000000000),(44510739778089239831/100000000000000000000),(146852230757638411/200000000000000000),false⟩
theorem valid2032 : certificate2032.Valid := by decide +kernel
theorem bound2032 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2032.a certificate2032.b certificate2032.c x ≤ (certificate2032.bound:ℝ) :=
  rat_majority_certificate_sound certificate2032 valid2032 x hx0 hx1

def certificate2033 : RatMajorityCertificate := ⟨(170914046158617307/1000000000000000000),(165826100407306368970478744004414387/200000000000000000000000000000000000),(1427762549/1175000000),(81832569661904263829661/200000000000000000000000),(204581424154760659574153/500000000000000000000000),(146852230757638411/200000000000000000),false⟩
theorem valid2033 : certificate2033.Valid := by decide +kernel
theorem bound2033 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2033.a certificate2033.b certificate2033.c x ≤ (certificate2033.bound:ℝ) :=
  rat_majority_certificate_sound certificate2033 valid2033 x hx0 hx1

def certificate2034 : RatMajorityCertificate := ⟨0,(200010746339373559/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(138031459100630113/250000000000000000),false⟩
theorem valid2034 : certificate2034.Valid := by decide +kernel
theorem bound2034 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2034.a certificate2034.b certificate2034.c x ≤ (certificate2034.bound:ℝ) :=
  rat_majority_certificate_sound certificate2034 valid2034 x hx0 hx1

def certificate2035 : RatMajorityCertificate := ⟨(225952664119028751/1000000000000000000),(154817785351556825929435367149805191/200000000000000000000000000000000000),1,(2126800599567858381/6250000000000000000),(34028809593085734097/100000000000000000000),(138031459100630113/250000000000000000),false⟩
theorem valid2035 : certificate2035.Valid := by decide +kernel
theorem bound2035 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2035.a certificate2035.b certificate2035.c x ≤ (certificate2035.bound:ℝ) :=
  rat_majority_certificate_sound certificate2035 valid2035 x hx0 hx1

def certificate2036 : RatMajorityCertificate := ⟨0,(200010746339373559/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54549697992638711/100000000000000000),false⟩
theorem valid2036 : certificate2036.Valid := by decide +kernel
theorem bound2036 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2036.a certificate2036.b certificate2036.c x ≤ (certificate2036.bound:ℝ) :=
  rat_majority_certificate_sound certificate2036 valid2036 x hx0 hx1

def certificate2037 : RatMajorityCertificate := ⟨(175042389856415349/1000000000000000000),(165000387303164333339222470027642909/200000000000000000000000000000000000),1,(8848800061226878599/25000000000000000000),(35395200244907514397/100000000000000000000),(54549697992638711/100000000000000000),false⟩
theorem valid2037 : certificate2037.Valid := by decide +kernel
theorem bound2037 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2037.a certificate2037.b certificate2037.c x ≤ (certificate2037.bound:ℝ) :=
  rat_majority_certificate_sound certificate2037 valid2037 x hx0 hx1

def certificate2038 : RatMajorityCertificate := ⟨0,(1000055199604832851/1000000000000000000),(2857818031/2350000000),(44532289940487477071/100000000000000000000),(2783268121280467317/6250000000000000000),(735067565987292801/1000000000000000000),false⟩
theorem valid2038 : certificate2038.Valid := by decide +kernel
theorem bound2038 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2038.a certificate2038.b certificate2038.c x ≤ (certificate2038.bound:ℝ) :=
  rat_majority_certificate_sound certificate2038 valid2038 x hx0 hx1

def certificate2039 : RatMajorityCertificate := ⟨(84972422956749547/500000000000000000),(415050486401497976048446468795031503/500000000000000000000000000000000000),(2857818031/2350000000),(10240575587890451393/25000000000000000000),(40962302351561805573/100000000000000000000),(735067565987292801/1000000000000000000),false⟩
theorem valid2039 : certificate2039.Valid := by decide +kernel
theorem bound2039 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2039.a certificate2039.b certificate2039.c x ≤ (certificate2039.bound:ℝ) :=
  rat_majority_certificate_sound certificate2039 valid2039 x hx0 hx1

end Cycle12.MajorityCertificates.Batch050
