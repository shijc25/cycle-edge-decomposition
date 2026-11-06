import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch047

def certificate1880 : RatMajorityCertificate := ⟨0,(200006602248025787/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(137076810162324883/250000000000000000),false⟩
theorem valid1880 : certificate1880.Valid := by decide +kernel
theorem bound1880 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1880.a certificate1880.b certificate1880.c x ≤ (certificate1880.bound:ℝ) :=
  rat_majority_certificate_sound certificate1880 valid1880 x hx0 hx1

def certificate1881 : RatMajorityCertificate := ⟨(197513512221165777/1000000000000000000),(160502595770596503151751486102108501/200000000000000000000000000000000000),1,(34808675635016240233/100000000000000000000),(17404337817508120117/50000000000000000000),(137076810162324883/250000000000000000),false⟩
theorem valid1881 : certificate1881.Valid := by decide +kernel
theorem bound1881 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1881.a certificate1881.b certificate1881.c x ≤ (certificate1881.bound:ℝ) :=
  rat_majority_certificate_sound certificate1881 valid1881 x hx0 hx1

def certificate1882 : RatMajorityCertificate := ⟨0,(250008321069709981/250000000000000000),(707270729/587500000),(22130372903791618959/50000000000000000000),(44260745807583237919/100000000000000000000),(725167249388208271/1000000000000000000),false⟩
theorem valid1882 : certificate1882.Valid := by decide +kernel
theorem bound1882 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1882.a certificate1882.b certificate1882.c x ≤ (certificate1882.bound:ℝ) :=
  rat_majority_certificate_sound certificate1882 valid1882 x hx0 hx1

def certificate1883 : RatMajorityCertificate := ⟨(11479978163579597/62500000000000000),(12755430000263406357009814401142343/15625000000000000000000000000000000),(707270729/587500000),(252127731043554473/625000000000000000),(40340436966968715681/100000000000000000000),(725167249388208271/1000000000000000000),false⟩
theorem valid1883 : certificate1883.Valid := by decide +kernel
theorem bound1883 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1883.a certificate1883.b certificate1883.c x ≤ (certificate1883.bound:ℝ) :=
  rat_majority_certificate_sound certificate1883 valid1883 x hx0 hx1

def certificate1884 : RatMajorityCertificate := ⟨0,(250008321069709981/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(110287170634922051/200000000000000000),false⟩
theorem valid1884 : certificate1884.Valid := by decide +kernel
theorem bound1884 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1884.a certificate1884.b certificate1884.c x ≤ (certificate1884.bound:ℝ) :=
  rat_majority_certificate_sound certificate1884 valid1884 x hx0 hx1

def certificate1885 : RatMajorityCertificate := ⟨(44203280147654911/200000000000000000),(38950476358452749994254867959633309/50000000000000000000000000000000000),1,(17083633070359832359/50000000000000000000),(34167266140719664719/100000000000000000000),(110287170634922051/200000000000000000),false⟩
theorem valid1885 : certificate1885.Valid := by decide +kernel
theorem bound1885 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1885.a certificate1885.b certificate1885.c x ≤ (certificate1885.bound:ℝ) :=
  rat_majority_certificate_sound certificate1885 valid1885 x hx0 hx1

def certificate1886 : RatMajorityCertificate := ⟨0,(250008321069709981/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274070547800983569/500000000000000000),false⟩
theorem valid1886 : certificate1886.Valid := by decide +kernel
theorem bound1886 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1886.a certificate1886.b certificate1886.c x ≤ (certificate1886.bound:ℝ) :=
  rat_majority_certificate_sound certificate1886 valid1886 x hx0 hx1

def certificate1887 : RatMajorityCertificate := ⟨(24527949834065761/125000000000000000),(25118848576416895196901041647939459/31250000000000000000000000000000000),1,(34843031256152038181/100000000000000000000),(17421515628076019091/50000000000000000000),(274070547800983569/500000000000000000),false⟩
theorem valid1887 : certificate1887.Valid := by decide +kernel
theorem bound1887 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1887.a certificate1887.b certificate1887.c x ≤ (certificate1887.bound:ℝ) :=
  rat_majority_certificate_sound certificate1887 valid1887 x hx0 hx1

def certificate1888 : RatMajorityCertificate := ⟨0,(500016819186586113/500000000000000000),(2829646141/2350000000),(44266099151959129827/100000000000000000000),(11066524787989782457/25000000000000000000),(5666900201355091/7812500000000000),false⟩
theorem valid1888 : certificate1888.Valid := by decide +kernel
theorem bound1888 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1888.a certificate1888.b certificate1888.c x ≤ (certificate1888.bound:ℝ) :=
  rat_majority_certificate_sound certificate1888 valid1888 x hx0 hx1

def certificate1889 : RatMajorityCertificate := ⟨(183447853533635167/1000000000000000000),(408289806976091125361091926429364129/500000000000000000000000000000000000),(2829646141/2350000000),(20175909720637261831/50000000000000000000),(40351819441274523663/100000000000000000000),(5666900201355091/7812500000000000),false⟩
theorem valid1889 : certificate1889.Valid := by decide +kernel
theorem bound1889 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1889.a certificate1889.b certificate1889.c x ≤ (certificate1889.bound:ℝ) :=
  rat_majority_certificate_sound certificate1889 valid1889 x hx0 hx1

def certificate1890 : RatMajorityCertificate := ⟨0,(500016819186586113/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275709580207006183/500000000000000000),false⟩
theorem valid1890 : certificate1890.Valid := by decide +kernel
theorem bound1890 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1890.a certificate1890.b certificate1890.c x ≤ (certificate1890.bound:ℝ) :=
  rat_majority_certificate_sound certificate1890 valid1890 x hx0 hx1

def certificate1891 : RatMajorityCertificate := ⟨(110446841524712433/500000000000000000),(194783131204901389008366286683757071/250000000000000000000000000000000000),1,(3417069501584724979/10000000000000000000),(34170695015847249791/100000000000000000000),(275709580207006183/500000000000000000),false⟩
theorem valid1891 : certificate1891.Valid := by decide +kernel
theorem bound1891 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1891.a certificate1891.b certificate1891.c x ≤ (certificate1891.bound:ℝ) :=
  rat_majority_certificate_sound certificate1891 valid1891 x hx0 hx1

def certificate1892 : RatMajorityCertificate := ⟨0,(500016819186586113/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(548079548920046001/1000000000000000000),false⟩
theorem valid1892 : certificate1892.Valid := by decide +kernel
theorem bound1892 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1892.a certificate1892.b certificate1892.c x ≤ (certificate1892.bound:ℝ) :=
  rat_majority_certificate_sound certificate1892 valid1892 x hx0 hx1

def certificate1893 : RatMajorityCertificate := ⟨(195743846805738653/1000000000000000000),(402141603531434277262444951642874211/500000000000000000000000000000000000),1,(871394703056987419/2500000000000000000),(34855788122279496761/100000000000000000000),(548079548920046001/1000000000000000000),false⟩
theorem valid1893 : certificate1893.Valid := by decide +kernel
theorem bound1893 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1893.a certificate1893.b certificate1893.c x ≤ (certificate1893.bound:ℝ) :=
  rat_majority_certificate_sound certificate1893 valid1893 x hx0 hx1

def certificate1894 : RatMajorityCertificate := ⟨0,(250008498294221067/250000000000000000),(283020971/235000000),(44271454524971043361/100000000000000000000),(22135727262485521681/50000000000000000000),(145111884221134729/200000000000000000),false⟩
theorem valid1894 : certificate1894.Valid := by decide +kernel
theorem bound1894 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1894.a certificate1894.b certificate1894.c x ≤ (certificate1894.bound:ℝ) :=
  rat_majority_certificate_sound certificate1894 valid1894 x hx0 hx1

def certificate1895 : RatMajorityCertificate := ⟨(183216439644423531/1000000000000000000),(204202831355904949574710170109272423/250000000000000000000000000000000000),(283020971/235000000),(8072638267926992521/20000000000000000000),(20181595669817481303/50000000000000000000),(145111884221134729/200000000000000000),false⟩
theorem valid1895 : certificate1895.Valid := by decide +kernel
theorem bound1895 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1895.a certificate1895.b certificate1895.c x ≤ (certificate1895.bound:ℝ) :=
  rat_majority_certificate_sound certificate1895 valid1895 x hx0 hx1

def certificate1896 : RatMajorityCertificate := ⟨0,(250008498294221067/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(551431532124885863/1000000000000000000),false⟩
theorem valid1896 : certificate1896.Valid := by decide +kernel
theorem bound1896 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1896.a certificate1896.b certificate1896.c x ≤ (certificate1896.bound:ℝ) :=
  rat_majority_certificate_sound certificate1896 valid1896 x hx0 hx1

def certificate1897 : RatMajorityCertificate := ⟨(110491405986478617/500000000000000000),(97380458662013906791040807733575661/125000000000000000000000000000000000),1,(6833641535197623201/20000000000000000000),(17084103837994058003/50000000000000000000),(551431532124885863/1000000000000000000),false⟩
theorem valid1897 : certificate1897.Valid := by decide +kernel
theorem bound1897 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1897.a certificate1897.b certificate1897.c x ≤ (certificate1897.bound:ℝ) :=
  rat_majority_certificate_sound certificate1897 valid1897 x hx0 hx1

def certificate1898 : RatMajorityCertificate := ⟨0,(250008498294221067/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109599476158882003/200000000000000000),false⟩
theorem valid1898 : certificate1898.Valid := by decide +kernel
theorem bound1898 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1898.a certificate1898.b certificate1898.c x ≤ (certificate1898.bound:ℝ) :=
  rat_majority_certificate_sound certificate1898 valid1898 x hx0 hx1

def certificate1899 : RatMajorityCertificate := ⟨(2438785163221709/12500000000000000),(2515389212358477056510057620456497/3125000000000000000000000000000000),1,(34872814552637553793/100000000000000000000),(17436407276318776897/50000000000000000000),(109599476158882003/200000000000000000),false⟩
theorem valid1899 : certificate1899.Valid := by decide +kernel
theorem bound1899 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1899.a certificate1899.b certificate1899.c x ≤ (certificate1899.bound:ℝ) :=
  rat_majority_certificate_sound certificate1899 valid1899 x hx0 hx1

def certificate1900 : RatMajorityCertificate := ⟨0,(1000034128832922299/1000000000000000000),(2830748999/2350000000),(2213828900631599843/5000000000000000000),(44276578012631996861/100000000000000000000),(725740362323868799/1000000000000000000),false⟩
theorem valid1900 : certificate1900.Valid := by decide +kernel
theorem bound1900 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1900.a certificate1900.b certificate1900.c x ≤ (certificate1900.bound:ℝ) :=
  rat_majority_certificate_sound certificate1900 valid1900 x hx0 hx1

def certificate1901 : RatMajorityCertificate := ⟨(182921749809820613/1000000000000000000),(817106136117264572053420938242450713/1000000000000000000000000000000000000),(2830748999/2350000000),(40375905287064079381/100000000000000000000),(20187952643532039691/50000000000000000000),(725740362323868799/1000000000000000000),false⟩
theorem valid1901 : certificate1901.Valid := by decide +kernel
theorem bound1901 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1901.a certificate1901.b certificate1901.c x ≤ (certificate1901.bound:ℝ) :=
  rat_majority_certificate_sound certificate1901 valid1901 x hx0 hx1

def certificate1902 : RatMajorityCertificate := ⟨0,(1000034128832922299/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275716422503994007/500000000000000000),false⟩
theorem valid1902 : certificate1902.Valid := by decide +kernel
theorem bound1902 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1902.a certificate1902.b certificate1902.c x ≤ (certificate1902.bound:ℝ) :=
  rat_majority_certificate_sound certificate1902 valid1902 x hx0 hx1

def certificate1903 : RatMajorityCertificate := ⟨(110495989582923437/500000000000000000),(389517303734370652815253423712978337/500000000000000000000000000000000000),1,(6833590459379026489/20000000000000000000),(17083976148447566223/50000000000000000000),(275716422503994007/500000000000000000),false⟩
theorem valid1903 : certificate1903.Valid := by decide +kernel
theorem bound1903 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1903.a certificate1903.b certificate1903.c x ≤ (certificate1903.bound:ℝ) :=
  rat_majority_certificate_sound certificate1903 valid1903 x hx0 hx1

def certificate1904 : RatMajorityCertificate := ⟨0,(1000034128832922299/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109583015449672957/200000000000000000),false⟩
theorem valid1904 : certificate1904.Valid := by decide +kernel
theorem bound1904 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1904.a certificate1904.b certificate1904.c x ≤ (certificate1904.bound:ℝ) :=
  rat_majority_certificate_sound certificate1904 valid1904 x hx0 hx1

def certificate1905 : RatMajorityCertificate := ⟨(24307547873651211/125000000000000000),(100695888642223945748496863809745911/125000000000000000000000000000000000),1,(17444927974913395949/50000000000000000000),(34889855949826791899/100000000000000000000),(109583015449672957/200000000000000000),false⟩
theorem valid1905 : certificate1905.Valid := by decide +kernel
theorem bound1905 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1905.a certificate1905.b certificate1905.c x ≤ (certificate1905.bound:ℝ) :=
  rat_majority_certificate_sound certificate1905 valid1905 x hx0 hx1

def certificate1906 : RatMajorityCertificate := ⟨0,(25000857659925147/25000000000000000),(22648281/18800000),(8855859175342051301/20000000000000000000),(22139647938355128253/50000000000000000000),(725841158355515233/1000000000000000000),false⟩
theorem valid1906 : certificate1906.Valid := by decide +kernel
theorem bound1906 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1906.a certificate1906.b certificate1906.c x ≤ (certificate1906.bound:ℝ) :=
  rat_majority_certificate_sound certificate1906 valid1906 x hx0 hx1

def certificate1907 : RatMajorityCertificate := ⟨(182816679334356509/1000000000000000000),(20430283882026720747694705647768177/25000000000000000000000000000000000),(22648281/18800000),(40381363245655057851/100000000000000000000),(10095340811413764463/25000000000000000000),(725841158355515233/1000000000000000000),false⟩
theorem valid1907 : certificate1907.Valid := by decide +kernel
theorem bound1907 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1907.a certificate1907.b certificate1907.c x ≤ (certificate1907.bound:ℝ) :=
  rat_majority_certificate_sound certificate1907 valid1907 x hx0 hx1

def certificate1908 : RatMajorityCertificate := ⟨0,(25000857659925147/25000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(68929451004076749/125000000000000000),false⟩
theorem valid1908 : certificate1908.Valid := by decide +kernel
theorem bound1908 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1908.a certificate1908.b certificate1908.c x ≤ (certificate1908.bound:ℝ) :=
  rat_majority_certificate_sound certificate1908 valid1908 x hx0 hx1

def certificate1909 : RatMajorityCertificate := ⟨(44202318112341571/200000000000000000),(3895075668619646570245879243614063/5000000000000000000000000000000000),1,(8541851351660063663/25000000000000000000),(34167405406640254653/100000000000000000000),(68929451004076749/125000000000000000),false⟩
theorem valid1909 : certificate1909.Valid := by decide +kernel
theorem bound1909 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1909.a certificate1909.b certificate1909.c x ≤ (certificate1909.bound:ℝ) :=
  rat_majority_certificate_sound certificate1909 valid1909 x hx0 hx1

def certificate1910 : RatMajorityCertificate := ⟨0,(25000857659925147/25000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(68485729345020663/125000000000000000),false⟩
theorem valid1910 : certificate1910.Valid := by decide +kernel
theorem bound1910 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1910.a certificate1910.b certificate1910.c x ≤ (certificate1910.bound:ℝ) :=
  rat_majority_certificate_sound certificate1910 valid1910 x hx0 hx1

def certificate1911 : RatMajorityCertificate := ⟨(194231445706015537/1000000000000000000),(20144904932747573160119968960991061/25000000000000000000000000000000000),1,(34895924260782737329/100000000000000000000),(3489592426078273733/10000000000000000000),(68485729345020663/125000000000000000),false⟩
theorem valid1911 : certificate1911.Valid := by decide +kernel
theorem bound1911 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1911.a certificate1911.b certificate1911.c x ≤ (certificate1911.bound:ℝ) :=
  rat_majority_certificate_sound certificate1911 valid1911 x hx0 hx1

def certificate1912 : RatMajorityCertificate := ⟨0,(500017574175569267/500000000000000000),(2828316527/2350000000),(2212672971849945697/5000000000000000000),(44253459436998913941/100000000000000000000),(724757477311169027/1000000000000000000),false⟩
theorem valid1912 : certificate1912.Valid := by decide +kernel
theorem bound1912 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1912.a certificate1912.b certificate1912.c x ≤ (certificate1912.bound:ℝ) :=
  rat_majority_certificate_sound certificate1912 valid1912 x hx0 hx1

def certificate1913 : RatMajorityCertificate := ⟨(3648528770809519/20000000000000000),(8176022978221438111593655752547427/10000000000000000000000000000000000),(2828316527/2350000000),(4036431506867826997/10000000000000000000),(40364315068678269971/100000000000000000000),(724757477311169027/1000000000000000000),false⟩
theorem valid1913 : certificate1913.Valid := by decide +kernel
theorem bound1913 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1913.a certificate1913.b certificate1913.c x ≤ (certificate1913.bound:ℝ) :=
  rat_majority_certificate_sound certificate1913 valid1913 x hx0 hx1

def certificate1914 : RatMajorityCertificate := ⟨0,(500017574175569267/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275710003394525639/500000000000000000),false⟩
theorem valid1914 : certificate1914.Valid := by decide +kernel
theorem bound1914 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1914.a certificate1914.b certificate1914.c x ≤ (certificate1914.bound:ℝ) :=
  rat_majority_certificate_sound certificate1914 valid1914 x hx0 hx1

def certificate1915 : RatMajorityCertificate := ⟨(110447692029452501/500000000000000000),(194783000045927437070294707988113233/250000000000000000000000000000000000),1,(854266369332545923/2500000000000000000),(34170654773301836921/100000000000000000000),(275710003394525639/500000000000000000),false⟩
theorem valid1915 : certificate1915.Valid := by decide +kernel
theorem bound1915 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1915.a certificate1915.b certificate1915.c x ≤ (certificate1915.bound:ℝ) :=
  rat_majority_certificate_sound certificate1915 valid1915 x hx0 hx1

def certificate1916 : RatMajorityCertificate := ⟨0,(500017574175569267/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(17136877925796831/31250000000000000),false⟩
theorem valid1916 : certificate1916.Valid := by decide +kernel
theorem bound1916 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1916.a certificate1916.b certificate1916.c x ≤ (certificate1916.bound:ℝ) :=
  rat_majority_certificate_sound certificate1916 valid1916 x hx0 hx1

def certificate1917 : RatMajorityCertificate := ⟨(24758807577563663/125000000000000000),(50122357867533073072999540041254979/62500000000000000000000000000000000),1,(434922809710407651/1250000000000000000),(34793824776832612081/100000000000000000000),(17136877925796831/31250000000000000),false⟩
theorem valid1917 : certificate1917.Valid := by decide +kernel
theorem bound1917 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1917.a certificate1917.b certificate1917.c x ≤ (certificate1917.bound:ℝ) :=
  rat_majority_certificate_sound certificate1917 valid1917 x hx0 hx1

def certificate1918 : RatMajorityCertificate := ⟨0,(250008966504081883/250000000000000000),(565859309/470000000),(1770511058230281187/4000000000000000000),(11065694113939257419/25000000000000000000),(725057669527114933/1000000000000000000),false⟩
theorem valid1918 : certificate1918.Valid := by decide +kernel
theorem bound1918 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1918.a certificate1918.b certificate1918.c x ≤ (certificate1918.bound:ℝ) :=
  rat_majority_certificate_sound certificate1918 valid1918 x hx0 hx1

def certificate1919 : RatMajorityCertificate := ⟨(45393689096929489/250000000000000000),(51153412329089519153904839666652213/62500000000000000000000000000000000),(565859309/470000000),(40395313984163566197/100000000000000000000),(20197656992081783099/50000000000000000000),(725057669527114933/1000000000000000000),false⟩
theorem valid1919 : certificate1919.Valid := by decide +kernel
theorem bound1919 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1919.a certificate1919.b certificate1919.c x ≤ (certificate1919.bound:ℝ) :=
  rat_majority_certificate_sound certificate1919 valid1919 x hx0 hx1

end Cycle12.MajorityCertificates.Batch047
