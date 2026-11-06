import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch048

def certificate1920 : RatMajorityCertificate := ⟨0,(250008966504081883/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275706373726602279/500000000000000000),false⟩
theorem valid1920 : certificate1920.Valid := by decide +kernel
theorem bound1920 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1920.a certificate1920.b certificate1920.c x ≤ (certificate1920.bound:ℝ) :=
  rat_majority_certificate_sound certificate1920 valid1920 x hx0 hx1

def certificate1921 : RatMajorityCertificate := ⟨(22084033551283977/100000000000000000),(19479690246010212021095813806111309/25000000000000000000000000000000000),1,(34172195307751166051/100000000000000000000),(8543048826937791513/25000000000000000000),(275706373726602279/500000000000000000),false⟩
theorem valid1921 : certificate1921.Valid := by decide +kernel
theorem bound1921 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1921.a certificate1921.b certificate1921.c x ≤ (certificate1921.bound:ℝ) :=
  rat_majority_certificate_sound certificate1921 valid1921 x hx0 hx1

def certificate1922 : RatMajorityCertificate := ⟨0,(250008966504081883/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(68526987098199371/125000000000000000),false⟩
theorem valid1922 : certificate1922.Valid := by decide +kernel
theorem bound1922 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1922.a certificate1922.b certificate1922.c x ≤ (certificate1922.bound:ℝ) :=
  rat_majority_certificate_sound certificate1922 valid1922 x hx0 hx1

def certificate1923 : RatMajorityCertificate := ⟨(19679605518992233/100000000000000000),(20080818813396914158928124926985261/25000000000000000000000000000000000),1,(2176737901005756963/6250000000000000000),(34827806416092111409/100000000000000000000),(68526987098199371/125000000000000000),false⟩
theorem valid1923 : certificate1923.Valid := by decide +kernel
theorem bound1923 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1923.a certificate1923.b certificate1923.c x ≤ (certificate1923.bound:ℝ) :=
  rat_majority_certificate_sound certificate1923 valid1923 x hx0 hx1

def certificate1924 : RatMajorityCertificate := ⟨0,(1000036135760449599/1000000000000000000),(707594613/587500000),(44273057771907399949/100000000000000000000),(885461155438147999/2000000000000000000),(181355449307797803/250000000000000000),false⟩
theorem valid1924 : certificate1924.Valid := by decide +kernel
theorem bound1924 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1924.a certificate1924.b certificate1924.c x ≤ (certificate1924.bound:ℝ) :=
  rat_majority_certificate_sound certificate1924 valid1924 x hx0 hx1

def certificate1925 : RatMajorityCertificate := ⟨(180991496273674857/1000000000000000000),(819038099221421981995316265737967657/1000000000000000000000000000000000000),(707594613/587500000),(40420569687664419187/100000000000000000000),(10105142421916104797/25000000000000000000),(181355449307797803/250000000000000000),false⟩
theorem valid1925 : certificate1925.Valid := by decide +kernel
theorem bound1925 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1925.a certificate1925.b certificate1925.c x ≤ (certificate1925.bound:ℝ) :=
  rat_majority_certificate_sound certificate1925 valid1925 x hx0 hx1

def certificate1926 : RatMajorityCertificate := ⟨0,(1000036135760449599/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(551488303274302853/1000000000000000000),false⟩
theorem valid1926 : certificate1926.Valid := by decide +kernel
theorem bound1926 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1926.a certificate1926.b certificate1926.c x ≤ (certificate1926.bound:ℝ) :=
  rat_majority_certificate_sound certificate1926 valid1926 x hx0 hx1

def certificate1927 : RatMajorityCertificate := ⟨(13836876469276649/62500000000000000),(48664882009697986463314421447886249/62500000000000000000000000000000000),1,(17078420212650710639/50000000000000000000),(34156840425301421279/100000000000000000000),(551488303274302853/1000000000000000000),false⟩
theorem valid1927 : certificate1927.Valid := by decide +kernel
theorem bound1927 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1927.a certificate1927.b certificate1927.c x ≤ (certificate1927.bound:ℝ) :=
  rat_majority_certificate_sound certificate1927 valid1927 x hx0 hx1

def certificate1928 : RatMajorityCertificate := ⟨0,(1000036135760449599/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274028946112426879/500000000000000000),false⟩
theorem valid1928 : certificate1928.Valid := by decide +kernel
theorem bound1928 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1928.a certificate1928.b certificate1928.c x ≤ (certificate1928.bound:ℝ) :=
  rat_majority_certificate_sound certificate1928 valid1928 x hx0 hx1

def certificate1929 : RatMajorityCertificate := ⟨(195567123511348469/1000000000000000000),(804461945282374106771284269799686069/1000000000000000000000000000000000000),1,(8715123548128554749/25000000000000000000),(34860494192514218997/100000000000000000000),(274028946112426879/500000000000000000),false⟩
theorem valid1929 : certificate1929.Valid := by decide +kernel
theorem bound1929 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1929.a certificate1929.b certificate1929.c x ≤ (certificate1929.bound:ℝ) :=
  rat_majority_certificate_sound certificate1929 valid1929 x hx0 hx1

def certificate1930 : RatMajorityCertificate := ⟨0,(15625570233784551/15625000000000000),(141548083/117500000),(44278598075210499739/100000000000000000000),(2213929903760524987/5000000000000000000),(725630351136323813/1000000000000000000),false⟩
theorem valid1930 : certificate1930.Valid := by decide +kernel
theorem bound1930 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1930.a certificate1930.b certificate1930.c x ≤ (certificate1930.bound:ℝ) :=
  rat_majority_certificate_sound certificate1930 valid1930 x hx0 hx1

def certificate1931 : RatMajorityCertificate := ⟨(4520227844916997/25000000000000000),(320008118181154657045092224086653/390625000000000000000000000000000),(141548083/117500000),(2021543916168753721/5000000000000000000),(40430878323375074421/100000000000000000000),(725630351136323813/1000000000000000000),false⟩
theorem valid1931 : certificate1931.Valid := by decide +kernel
theorem bound1931 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1931.a certificate1931.b certificate1931.c x ≤ (certificate1931.bound:ℝ) :=
  rat_majority_certificate_sound certificate1931 valid1931 x hx0 hx1

def certificate1932 : RatMajorityCertificate := ⟨0,(15625570233784551/15625000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(34466814575817477/62500000000000000),false⟩
theorem valid1932 : certificate1932.Valid := by decide +kernel
theorem bound1932 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1932.a certificate1932.b certificate1932.c x ≤ (certificate1932.bound:ℝ) :=
  rat_majority_certificate_sound certificate1932 valid1932 x hx0 hx1

def certificate1933 : RatMajorityCertificate := ⟨(221248638815192423/1000000000000000000),(12168434088848531046172957410342927/15625000000000000000000000000000000),1,(17080396757182143991/50000000000000000000),(34160793514364287983/100000000000000000000),(34466814575817477/62500000000000000),false⟩
theorem valid1933 : certificate1933.Valid := by decide +kernel
theorem bound1933 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1933.a certificate1933.b certificate1933.c x ≤ (certificate1933.bound:ℝ) :=
  rat_majority_certificate_sound certificate1933 valid1933 x hx0 hx1

def certificate1934 : RatMajorityCertificate := ⟨0,(15625570233784551/15625000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(273992060323651047/500000000000000000),false⟩
theorem valid1934 : certificate1934.Valid := by decide +kernel
theorem bound1934 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1934.a certificate1934.b certificate1934.c x ≤ (certificate1934.bound:ℝ) :=
  rat_majority_certificate_sound certificate1934 valid1934 x hx0 hx1

def certificate1935 : RatMajorityCertificate := ⟨(194991242114981339/1000000000000000000),(12578720885144022051978567288506211/15625000000000000000000000000000000),1,(2179736623700475741/6250000000000000000),(34875785979207611857/100000000000000000000),(273992060323651047/500000000000000000),false⟩
theorem valid1935 : certificate1935.Valid := by decide +kernel
theorem bound1935 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1935.a certificate1935.b certificate1935.c x ≤ (certificate1935.bound:ℝ) :=
  rat_majority_certificate_sound certificate1935 valid1935 x hx0 hx1

def certificate1936 : RatMajorityCertificate := ⟨0,(125004606838914253/125000000000000000),(353938191/293750000),(22141881731353221729/50000000000000000000),(44283763462706443459/100000000000000000000),(11340847652839561/15625000000000000),false⟩
theorem valid1936 : certificate1936.Valid := by decide +kernel
theorem bound1936 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1936.a certificate1936.b certificate1936.c x ≤ (certificate1936.bound:ℝ) :=
  rat_majority_certificate_sound certificate1936 valid1936 x hx0 hx1

def certificate1937 : RatMajorityCertificate := ⟨(90261128648879711/500000000000000000),(51219246519867258569639311959579117/62500000000000000000000000000000000),(353938191/293750000),(40443403458367927943/100000000000000000000),(5055425432295990993/12500000000000000000),(11340847652839561/15625000000000000),false⟩
theorem valid1937 : certificate1937.Valid := by decide +kernel
theorem bound1937 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1937.a certificate1937.b certificate1937.c x ≤ (certificate1937.bound:ℝ) :=
  rat_majority_certificate_sound certificate1937 valid1937 x hx0 hx1

def certificate1938 : RatMajorityCertificate := ⟨0,(125004606838914253/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(137866914330646251/250000000000000000),false⟩
theorem valid1938 : certificate1938.Valid := by decide +kernel
theorem bound1938 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1938.a certificate1938.b certificate1938.c x ≤ (certificate1938.bound:ℝ) :=
  rat_majority_certificate_sound certificate1938 valid1938 x hx0 hx1

def certificate1939 : RatMajorityCertificate := ⟨(221237554406734073/1000000000000000000),(97348893332297558767187588979557531/125000000000000000000000000000000000),1,(17080552490645673277/50000000000000000000),(6832220996258269311/20000000000000000000),(137866914330646251/250000000000000000),false⟩
theorem valid1939 : certificate1939.Valid := by decide +kernel
theorem bound1939 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1939.a certificate1939.b certificate1939.c x ≤ (certificate1939.bound:ℝ) :=
  rat_majority_certificate_sound certificate1939 valid1939 x hx0 hx1

def certificate1940 : RatMajorityCertificate := ⟨0,(125004606838914253/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(547886583911047069/1000000000000000000),false⟩
theorem valid1940 : certificate1940.Valid := by decide +kernel
theorem bound1940 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1940.a certificate1940.b certificate1940.c x ≤ (certificate1940.bound:ℝ) :=
  rat_majority_certificate_sound certificate1940 valid1940 x hx0 hx1

def certificate1941 : RatMajorityCertificate := ⟨(97114454457104459/500000000000000000),(50362549221671139685477538235045873/62500000000000000000000000000000000),1,(34896002046128695351/100000000000000000000),(4362000255766086919/12500000000000000000),(547886583911047069/1000000000000000000),false⟩
theorem valid1941 : certificate1941.Valid := by decide +kernel
theorem bound1941 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1941.a certificate1941.b certificate1941.c x ≤ (certificate1941.bound:ℝ) :=
  rat_majority_certificate_sound certificate1941 valid1941 x hx0 hx1

def certificate1942 : RatMajorityCertificate := ⟨0,(1000036988406292589/1000000000000000000),(2832050459/2350000000),(2768058611699689591/6250000000000000000),(44288937787195033457/100000000000000000000),(725998772469545357/1000000000000000000),false⟩
theorem valid1942 : certificate1942.Valid := by decide +kernel
theorem bound1942 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1942.a certificate1942.b certificate1942.c x ≤ (certificate1942.bound:ℝ) :=
  rat_majority_certificate_sound certificate1942 valid1942 x hx0 hx1

def certificate1943 : RatMajorityCertificate := ⟨(45059629340338931/250000000000000000),(204947951077356782329553505586517641/250000000000000000000000000000000000),(2832050459/2350000000),(40455854753290055919/100000000000000000000),(505698184416125699/1250000000000000000),(725998772469545357/1000000000000000000),false⟩
theorem valid1943 : certificate1943.Valid := by decide +kernel
theorem bound1943 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1943.a certificate1943.b certificate1943.c x ≤ (certificate1943.bound:ℝ) :=
  rat_majority_certificate_sound certificate1943 valid1943 x hx0 hx1

def certificate1944 : RatMajorityCertificate := ⟨0,(1000036988406292589/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275735075923127803/500000000000000000),false⟩
theorem valid1944 : certificate1944.Valid := by decide +kernel
theorem bound1944 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1944.a certificate1944.b certificate1944.c x ≤ (certificate1944.bound:ℝ) :=
  rat_majority_certificate_sound certificate1944 valid1944 x hx0 hx1

def certificate1945 : RatMajorityCertificate := ⟨(221255327747440553/1000000000000000000),(778773476776894913728274475598038283/1000000000000000000000000000000000000),1,(341606089758918112215883/1000000000000000000000000),(85401522439729528053971/250000000000000000000000),(275735075923127803/500000000000000000),false⟩
theorem valid1945 : certificate1945.Valid := by decide +kernel
theorem bound1945 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1945.a certificate1945.b certificate1945.c x ≤ (certificate1945.bound:ℝ) :=
  rat_majority_certificate_sound certificate1945 valid1945 x hx0 hx1

def certificate1946 : RatMajorityCertificate := ⟨0,(1000036988406292589/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(136956356296667113/250000000000000000),false⟩
theorem valid1946 : certificate1946.Valid := by decide +kernel
theorem bound1946 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1946.a certificate1946.b certificate1946.c x ≤ (certificate1946.bound:ℝ) :=
  rat_majority_certificate_sound certificate1946 valid1946 x hx0 hx1

def certificate1947 : RatMajorityCertificate := ⟨(96875220087416901/500000000000000000),(403139690855729116144404392970353311/500000000000000000000000000000000000),1,(1396346991647045389/4000000000000000000),(17454337395588067363/50000000000000000000),(136956356296667113/250000000000000000),false⟩
theorem valid1947 : certificate1947.Valid := by decide +kernel
theorem bound1947 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1947.a certificate1947.b certificate1947.c x ≤ (certificate1947.bound:ℝ) :=
  rat_majority_certificate_sound certificate1947 valid1947 x hx0 hx1

def certificate1948 : RatMajorityCertificate := ⟨0,(500018584164401879/500000000000000000),(566466363/470000000),(8858321782813183689/20000000000000000000),(22145804457032959223/50000000000000000000),(72609661420493597/100000000000000000),false⟩
theorem valid1948 : certificate1948.Valid := by decide +kernel
theorem bound1948 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1948.a certificate1948.b certificate1948.c x ≤ (certificate1948.bound:ℝ) :=
  rat_majority_certificate_sound certificate1948 valid1948 x hx0 hx1

def certificate1949 : RatMajorityCertificate := ⟨(45029829060088573/250000000000000000),(102488894669309942055432002692371333/125000000000000000000000000000000000),(566466363/470000000),(2023080052415644131/5000000000000000000),(40461601048312882621/100000000000000000000),(72609661420493597/100000000000000000),false⟩
theorem valid1949 : certificate1949.Valid := by decide +kernel
theorem bound1949 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1949.a certificate1949.b certificate1949.c x ≤ (certificate1949.bound:ℝ) :=
  rat_majority_certificate_sound certificate1949 valid1949 x hx0 hx1

def certificate1950 : RatMajorityCertificate := ⟨0,(500018584164401879/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275738163444214007/500000000000000000),false⟩
theorem valid1950 : certificate1950.Valid := by decide +kernel
theorem bound1950 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1950.a certificate1950.b certificate1950.c x ≤ (certificate1950.bound:ℝ) :=
  rat_majority_certificate_sound certificate1950 valid1950 x hx0 hx1

def certificate1951 : RatMajorityCertificate := ⟨(221299767386825137/1000000000000000000),(389364587799730096160997019632767577/500000000000000000000000000000000000),1,(8539841991705532867/25000000000000000000),(34159367966822131469/100000000000000000000),(275738163444214007/500000000000000000),false⟩
theorem valid1951 : certificate1951.Valid := by decide +kernel
theorem bound1951 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1951.a certificate1951.b certificate1951.c x ≤ (certificate1951.bound:ℝ) :=
  rat_majority_certificate_sound certificate1951 valid1951 x hx0 hx1

def certificate1952 : RatMajorityCertificate := ⟨0,(500018584164401879/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54778784856576261/100000000000000000),false⟩
theorem valid1952 : certificate1952.Valid := by decide +kernel
theorem bound1952 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1952.a certificate1952.b certificate1952.c x ≤ (certificate1952.bound:ℝ) :=
  rat_majority_certificate_sound certificate1952 valid1952 x hx0 hx1

def certificate1953 : RatMajorityCertificate := ⟨(193455848513532059/1000000000000000000),(403287064692342569021051516573661139/500000000000000000000000000000000000),1,(3491647193005128289/10000000000000000000),(34916471930051282891/100000000000000000000),(54778784856576261/100000000000000000),false⟩
theorem valid1953 : certificate1953.Valid := by decide +kernel
theorem bound1953 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1953.a certificate1953.b certificate1953.c x ≤ (certificate1953.bound:ℝ) :=
  rat_majority_certificate_sound certificate1953 valid1953 x hx0 hx1

def certificate1954 : RatMajorityCertificate := ⟨0,(31251217332061107/31250000000000000),(713884051/587500000),(11127711051775572473/25000000000000000000),(44510844207102289893/100000000000000000000),(735627526956331133/1000000000000000000),false⟩
theorem valid1954 : certificate1954.Valid := by decide +kernel
theorem bound1954 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1954.a certificate1954.b certificate1954.c x ≤ (certificate1954.bound:ℝ) :=
  rat_majority_certificate_sound certificate1954 valid1954 x hx0 hx1

def certificate1955 : RatMajorityCertificate := ⟨(46588139022860411/250000000000000000),(6356868275315589068128886616865023/7812500000000000000000000000000000),(713884051/587500000),(20266616241286730999/50000000000000000000),(40533232482573461999/100000000000000000000),(735627526956331133/1000000000000000000),false⟩
theorem valid1955 : certificate1955.Valid := by decide +kernel
theorem bound1955 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1955.a certificate1955.b certificate1955.c x ≤ (certificate1955.bound:ℝ) :=
  rat_majority_certificate_sound certificate1955 valid1955 x hx0 hx1

def certificate1956 : RatMajorityCertificate := ⟨0,(31251217332061107/31250000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(27592083139139829/50000000000000000),false⟩
theorem valid1956 : certificate1956.Valid := by decide +kernel
theorem bound1956 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1956.a certificate1956.b certificate1956.c x ≤ (certificate1956.bound:ℝ) :=
  rat_majority_certificate_sound certificate1956 valid1956 x hx0 hx1

def certificate1957 : RatMajorityCertificate := ⟨(223945832169627173/1000000000000000000),(24252637460318806469197848156339489/31250000000000000000000000000000000),1,(17042616155519816677/50000000000000000000),(6817046462207926671/20000000000000000000),(27592083139139829/50000000000000000),false⟩
theorem valid1957 : certificate1957.Valid := by decide +kernel
theorem bound1957 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1957.a certificate1957.b certificate1957.c x ≤ (certificate1957.bound:ℝ) :=
  rat_majority_certificate_sound certificate1957 valid1957 x hx0 hx1

def certificate1958 : RatMajorityCertificate := ⟨0,(31251217332061107/31250000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(273918621781848867/500000000000000000),false⟩
theorem valid1958 : certificate1958.Valid := by decide +kernel
theorem bound1958 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1958.a certificate1958.b certificate1958.c x ≤ (certificate1958.bound:ℝ) :=
  rat_majority_certificate_sound certificate1958 valid1958 x hx0 hx1

def certificate1959 : RatMajorityCertificate := ⟨(7753455127869167/40000000000000000),(1007743782007021301638698854812131/1250000000000000000000000000000000),1,(17453203865550770483/50000000000000000000),(34906407731101540967/100000000000000000000),(273918621781848867/500000000000000000),false⟩
theorem valid1959 : certificate1959.Valid := by decide +kernel
theorem bound1959 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1959.a certificate1959.b certificate1959.c x ≤ (certificate1959.bound:ℝ) :=
  rat_majority_certificate_sound certificate1959 valid1959 x hx0 hx1

end Cycle12.MajorityCertificates.Batch048
