import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch049

def certificate1960 : RatMajorityCertificate := ⟨0,(200008084272540413/200000000000000000),(1428907787/1175000000),(22266133429622202391/50000000000000000000),(44532266859244404783/100000000000000000000),(92052884623558309/125000000000000000),false⟩
theorem valid1960 : certificate1960.Valid := by decide +kernel
theorem bound1960 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1960.a certificate1960.b certificate1960.c x ≤ (certificate1960.bound:ℝ) :=
  rat_majority_certificate_sound certificate1960 valid1960 x hx0 hx1

def certificate1961 : RatMajorityCertificate := ⟨(92699885790958313/500000000000000000),(81463315566937344634477097709196731/100000000000000000000000000000000000),(1428907787/1175000000),(5072437687886282219/12500000000000000000),(40579501503090257753/100000000000000000000),(92052884623558309/125000000000000000),false⟩
theorem valid1961 : certificate1961.Valid := by decide +kernel
theorem bound1961 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1961.a certificate1961.b certificate1961.c x ≤ (certificate1961.bound:ℝ) :=
  rat_majority_certificate_sound certificate1961 valid1961 x hx0 hx1

def certificate1962 : RatMajorityCertificate := ⟨0,(200008084272540413/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275944188289964891/500000000000000000),false⟩
theorem valid1962 : certificate1962.Valid := by decide +kernel
theorem bound1962 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1962.a certificate1962.b certificate1962.c x ≤ (certificate1962.bound:ℝ) :=
  rat_majority_certificate_sound certificate1962 valid1962 x hx0 hx1

def certificate1963 : RatMajorityCertificate := ⟨(224279242516777259/1000000000000000000),(155150422634663298189788610403132033/200000000000000000000000000000000000),1,(681517384057475097/2000000000000000000),(34075869202873754851/100000000000000000000),(275944188289964891/500000000000000000),false⟩
theorem valid1963 : certificate1963.Valid := by decide +kernel
theorem bound1963 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1963.a certificate1963.b certificate1963.c x ≤ (certificate1963.bound:ℝ) :=
  rat_majority_certificate_sound certificate1963 valid1963 x hx0 hx1

def certificate1964 : RatMajorityCertificate := ⟨0,(200008084272540413/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109509471756457437/200000000000000000),false⟩
theorem valid1964 : certificate1964.Valid := by decide +kernel
theorem bound1964 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1964.a certificate1964.b certificate1964.c x ≤ (certificate1964.bound:ℝ) :=
  rat_majority_certificate_sound certificate1964 valid1964 x hx0 hx1

def certificate1965 : RatMajorityCertificate := ⟨(191558171185869497/1000000000000000000),(161694901426903303942464679523517739/200000000000000000000000000000000000),1,(34966601192292762841/100000000000000000000),(17483300596146381421/50000000000000000000),(109509471756457437/200000000000000000),false⟩
theorem valid1965 : certificate1965.Valid := by decide +kernel
theorem bound1965 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1965.a certificate1965.b certificate1965.c x ≤ (certificate1965.bound:ℝ) :=
  rat_majority_certificate_sound certificate1965 valid1965 x hx0 hx1

def certificate1966 : RatMajorityCertificate := ⟨0,(250010473485732701/250000000000000000),(357512993/293750000),(44553753847631075573/100000000000000000000),(22276876923815537787/50000000000000000000),(184305996459546329/250000000000000000),false⟩
theorem valid1966 : certificate1966.Valid := by decide +kernel
theorem bound1966 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1966.a certificate1966.b certificate1966.c x ≤ (certificate1966.bound:ℝ) :=
  rat_majority_certificate_sound certificate1966 valid1966 x hx0 hx1

def certificate1967 : RatMajorityCertificate := ⟨(46114606515432109/250000000000000000),(50973483761901739501229406513303591/62500000000000000000000000000000000),(357512993/293750000),(20312749150981864671/50000000000000000000),(40625498301963729343/100000000000000000000),(184305996459546329/250000000000000000),false⟩
theorem valid1967 : certificate1967.Valid := by decide +kernel
theorem bound1967 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1967.a certificate1967.b certificate1967.c x ≤ (certificate1967.bound:ℝ) :=
  rat_majority_certificate_sound certificate1967 valid1967 x hx0 hx1

def certificate1968 : RatMajorityCertificate := ⟨0,(250010473485732701/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(34496044590964577/62500000000000000),false⟩
theorem valid1968 : certificate1968.Valid := by decide +kernel
theorem bound1968 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1968.a certificate1968.b certificate1968.c x ≤ (certificate1968.bound:ℝ) :=
  rat_majority_certificate_sound certificate1968 valid1968 x hx0 hx1

def certificate1969 : RatMajorityCertificate := ⟨(1754875522999837/7812500000000000),(1514469563693574671564100551430263/1953125000000000000000000000000000),1,(17033089381931928383/50000000000000000000),(34066178763863856767/100000000000000000000),(34496044590964577/62500000000000000),false⟩
theorem valid1969 : certificate1969.Valid := by decide +kernel
theorem bound1969 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1969.a certificate1969.b certificate1969.c x ≤ (certificate1969.bound:ℝ) :=
  rat_majority_certificate_sound certificate1969 valid1969 x hx0 hx1

def certificate1970 : RatMajorityCertificate := ⟨0,(250010473485732701/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(547065368703272793/1000000000000000000),false⟩
theorem valid1970 : certificate1970.Valid := by decide +kernel
theorem bound1970 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1970.a certificate1970.b certificate1970.c x ≤ (certificate1970.bound:ℝ) :=
  rat_majority_certificate_sound certificate1970 valid1970 x hx0 hx1

def certificate1971 : RatMajorityCertificate := ⟨(37548738997426513/200000000000000000),(40614516681607741489765338791498387/50000000000000000000000000000000000),1,(35066790871577777367/100000000000000000000),(4383348858947222171/12500000000000000000),(547065368703272793/1000000000000000000),false⟩
theorem valid1971 : certificate1971.Valid := by decide +kernel
theorem bound1971 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1971.a certificate1971.b certificate1971.c x ≤ (certificate1971.bound:ℝ) :=
  rat_majority_certificate_sound certificate1971 valid1971 x hx0 hx1

def certificate1972 : RatMajorityCertificate := ⟨0,(1000042412602879859/1000000000000000000),(177466451/146875000),(11089802396203108217/25000000000000000000),(44359209584812432869/100000000000000000000),(728602436606159057/1000000000000000000),false⟩
theorem valid1972 : certificate1972.Valid := by decide +kernel
theorem bound1972 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1972.a certificate1972.b certificate1972.c x ≤ (certificate1972.bound:ℝ) :=
  rat_majority_certificate_sound certificate1972 valid1972 x hx0 hx1

def certificate1973 : RatMajorityCertificate := ⟨(177334231630529057/1000000000000000000),(822700659766007651440347818020437037/1000000000000000000000000000000000000),(177466451/146875000),(20300511583744742621/50000000000000000000),(40601023167489485243/100000000000000000000),(728602436606159057/1000000000000000000),false⟩
theorem valid1973 : certificate1973.Valid := by decide +kernel
theorem bound1973 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1973.a certificate1973.b certificate1973.c x ≤ (certificate1973.bound:ℝ) :=
  rat_majority_certificate_sound certificate1973 valid1973 x hx0 hx1

def certificate1974 : RatMajorityCertificate := ⟨0,(1000042412602879859/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(551282918865700831/1000000000000000000),false⟩
theorem valid1974 : certificate1974.Valid := by decide +kernel
theorem bound1974 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1974.a certificate1974.b certificate1974.c x ≤ (certificate1974.bound:ℝ) :=
  rat_majority_certificate_sound certificate1974 valid1974 x hx0 hx1

def certificate1975 : RatMajorityCertificate := ⟨(13742070104770063/62500000000000000),(48759997845947827392456153191138883/62500000000000000000000000000000000),1,(34199205933542203951/100000000000000000000),(2137450370846387747/6250000000000000000),(551282918865700831/1000000000000000000),false⟩
theorem valid1975 : certificate1975.Valid := by decide +kernel
theorem bound1975 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1975.a certificate1975.b certificate1975.c x ≤ (certificate1975.bound:ℝ) :=
  rat_majority_certificate_sound certificate1975 valid1975 x hx0 hx1

def certificate1976 : RatMajorityCertificate := ⟨0,(1000042412602879859/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(547421143168435177/1000000000000000000),false⟩
theorem valid1976 : certificate1976.Valid := by decide +kernel
theorem bound1976 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1976.a certificate1976.b certificate1976.c x ≤ (certificate1976.bound:ℝ) :=
  rat_majority_certificate_sound certificate1976 valid1976 x hx0 hx1

def certificate1977 : RatMajorityCertificate := ⟨(95278769508511933/500000000000000000),(404738395772313950364912430533142553/500000000000000000000000000000000000),1,(218706007537677967/625000000000000000),(34992961206028474721/100000000000000000000),(547421143168435177/1000000000000000000),false⟩
theorem valid1977 : certificate1977.Valid := by decide +kernel
theorem bound1977 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1977.a certificate1977.b certificate1977.c x ≤ (certificate1977.bound:ℝ) :=
  rat_majority_certificate_sound certificate1977 valid1977 x hx0 hx1

def certificate1978 : RatMajorityCertificate := ⟨0,(500021573391598257/500000000000000000),(2840598817/2350000000),(22184977990793282401/50000000000000000000),(44369955981586564803/100000000000000000000),(364499872835456939/500000000000000000),false⟩
theorem valid1978 : certificate1978.Valid := by decide +kernel
theorem bound1978 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1978.a certificate1978.b certificate1978.c x ≤ (certificate1978.bound:ℝ) :=
  rat_majority_certificate_sound certificate1978 valid1978 x hx0 hx1

def certificate1979 : RatMajorityCertificate := ⟨(176864270085250679/1000000000000000000),(411585622786814628496140525695533497/500000000000000000000000000000000000),(2840598817/2350000000),(20311910020867876549/50000000000000000000),(40623820041735753099/100000000000000000000),(364499872835456939/500000000000000000),false⟩
theorem valid1979 : certificate1979.Valid := by decide +kernel
theorem bound1979 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1979.a certificate1979.b certificate1979.c x ≤ (certificate1979.bound:ℝ) :=
  rat_majority_certificate_sound certificate1979 valid1979 x hx0 hx1

def certificate1980 : RatMajorityCertificate := ⟨0,(500021573391598257/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(551681423122404941/1000000000000000000),false⟩
theorem valid1980 : certificate1980.Valid := by decide +kernel
theorem bound1980 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1980.a certificate1980.b certificate1980.c x ≤ (certificate1980.bound:ℝ) :=
  rat_majority_certificate_sound certificate1980 valid1980 x hx0 hx1

def certificate1981 : RatMajorityCertificate := ⟨(8910915154609467/40000000000000000),(15545213119697067547148456207100981/20000000000000000000000000000000000),1,(34118167987355536279/100000000000000000000),(852954199683888407/2500000000000000000),(551681423122404941/1000000000000000000),false⟩
theorem valid1981 : certificate1981.Valid := by decide +kernel
theorem bound1981 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1981.a certificate1981.b certificate1981.c x ≤ (certificate1981.bound:ℝ) :=
  rat_majority_certificate_sound certificate1981 valid1981 x hx0 hx1

def certificate1982 : RatMajorityCertificate := ⟨0,(500021573391598257/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109454651518957211/200000000000000000),false⟩
theorem valid1982 : certificate1982.Valid := by decide +kernel
theorem bound1982 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1982.a certificate1982.b certificate1982.c x ≤ (certificate1982.bound:ℝ) :=
  rat_majority_certificate_sound certificate1982 valid1982 x hx0 hx1

def certificate1983 : RatMajorityCertificate := ⟨(189387175594095489/1000000000000000000),(405323899870847733217215070016037327/500000000000000000000000000000000000),1,(35023721578677996763/100000000000000000000),(8755930394669499191/25000000000000000000),(109454651518957211/200000000000000000),false⟩
theorem valid1983 : certificate1983.Valid := by decide +kernel
theorem bound1983 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1983.a certificate1983.b certificate1983.c x ≤ (certificate1983.bound:ℝ) :=
  rat_majority_certificate_sound certificate1983 valid1983 x hx0 hx1

def certificate1984 : RatMajorityCertificate := ⟨0,(500021940866067901/500000000000000000),(568347051/470000000),(22190352634997461259/50000000000000000000),(44380705269994922519/100000000000000000000),(22793672389997981/31250000000000000),false⟩
theorem valid1984 : certificate1984.Valid := by decide +kernel
theorem bound1984 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1984.a certificate1984.b certificate1984.c x ≤ (certificate1984.bound:ℝ) :=
  rat_majority_certificate_sound certificate1984 valid1984 x hx0 hx1

def certificate1985 : RatMajorityCertificate := ⟨(44098387592554993/250000000000000000),(102955323863423500113685033985420307/125000000000000000000000000000000000),(568347051/470000000),(40646626255392740679/100000000000000000000),(1016165656384818517/2500000000000000000),(22793672389997981/31250000000000000),false⟩
theorem valid1985 : certificate1985.Valid := by decide +kernel
theorem bound1985 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1985.a certificate1985.b certificate1985.c x ≤ (certificate1985.bound:ℝ) :=
  rat_majority_certificate_sound certificate1985 valid1985 x hx0 hx1

def certificate1986 : RatMajorityCertificate := ⟨0,(500021940866067901/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(551712478165127119/1000000000000000000),false⟩
theorem valid1986 : certificate1986.Valid := by decide +kernel
theorem bound1986 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1986.a certificate1986.b certificate1986.c x ≤ (certificate1986.bound:ℝ) :=
  rat_majority_certificate_sound certificate1986 valid1986 x hx0 hx1

def certificate1987 : RatMajorityCertificate := ⟨(44599189039142999/200000000000000000),(77703815108808635865169156017224901/100000000000000000000000000000000000),1,(34111917869276318123/100000000000000000000),(8527979467319079531/25000000000000000000),(551712478165127119/1000000000000000000),false⟩
theorem valid1987 : certificate1987.Valid := by decide +kernel
theorem bound1987 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1987.a certificate1987.b certificate1987.c x ≤ (certificate1987.bound:ℝ) :=
  rat_majority_certificate_sound certificate1987 valid1987 x hx0 hx1

def certificate1988 : RatMajorityCertificate := ⟨0,(500021940866067901/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(136781631135324609/250000000000000000),false⟩
theorem valid1988 : certificate1988.Valid := by decide +kernel
theorem bound1988 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1988.a certificate1988.b certificate1988.c x ≤ (certificate1988.bound:ℝ) :=
  rat_majority_certificate_sound certificate1988 valid1988 x hx0 hx1

def certificate1989 : RatMajorityCertificate := ⟨(94111212886432661/500000000000000000),(202953299108300191062300773909885439/250000000000000000000000000000000000),1,(35054265706151056729/100000000000000000000),(3505426570615105673/10000000000000000000),(136781631135324609/250000000000000000),false⟩
theorem valid1989 : certificate1989.Valid := by decide +kernel
theorem bound1989 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1989.a certificate1989.b certificate1989.c x ≤ (certificate1989.bound:ℝ) :=
  rat_majority_certificate_sound certificate1989 valid1989 x hx0 hx1

def certificate1990 : RatMajorityCertificate := ⟨0,(1000044617290180847/1000000000000000000),(2842872459/2350000000),(22195728384794003957/50000000000000000000),(8878291353917601583/20000000000000000000),(729795706853336877/1000000000000000000),false⟩
theorem valid1990 : certificate1990.Valid := by decide +kernel
theorem bound1990 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1990.a certificate1990.b certificate1990.c x ≤ (certificate1990.bound:ℝ) :=
  rat_majority_certificate_sound certificate1990 valid1990 x hx0 hx1

def certificate1991 : RatMajorityCertificate := ⟨(175921901239722091/1000000000000000000),(824114866891941977011872946589008923/1000000000000000000000000000000000000),(2842872459/2350000000),(10167361322299543471/25000000000000000000),(8133889057839634777/20000000000000000000),(729795706853336877/1000000000000000000),false⟩
theorem valid1991 : certificate1991.Valid := by decide +kernel
theorem bound1991 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1991.a certificate1991.b certificate1991.c x ≤ (certificate1991.bound:ℝ) :=
  rat_majority_certificate_sound certificate1991 valid1991 x hx0 hx1

def certificate1992 : RatMajorityCertificate := ⟨0,(1000044617290180847/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275856892073849061/500000000000000000),false⟩
theorem valid1992 : certificate1992.Valid := by decide +kernel
theorem bound1992 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1992.a certificate1992.b certificate1992.c x ≤ (certificate1992.bound:ℝ) :=
  rat_majority_certificate_sound certificate1992 valid1992 x hx0 hx1

def certificate1993 : RatMajorityCertificate := ⟨(27875406912298727/125000000000000000),(97128926523854763654416941682118231/125000000000000000000000000000000000),1,(6822343291280204189/20000000000000000000),(17055858228200510473/50000000000000000000),(275856892073849061/500000000000000000),false⟩
theorem valid1993 : certificate1993.Valid := by decide +kernel
theorem bound1993 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1993.a certificate1993.b certificate1993.c x ≤ (certificate1993.bound:ℝ) :=
  rat_majority_certificate_sound certificate1993 valid1993 x hx0 hx1

def certificate1994 : RatMajorityCertificate := ⟨0,(1000044617290180847/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(273490436582587689/500000000000000000),false⟩
theorem valid1994 : certificate1994.Valid := by decide +kernel
theorem bound1994 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1994.a certificate1994.b certificate1994.c x ≤ (certificate1994.bound:ℝ) :=
  rat_majority_certificate_sound certificate1994 valid1994 x hx0 hx1

def certificate1995 : RatMajorityCertificate := ⟨(187062789757825723/1000000000000000000),(812973481297582460315608115821472619/1000000000000000000000000000000000000),1,(877115197162967657/2500000000000000000),(35084607886518706281/100000000000000000000),(273490436582587689/500000000000000000),false⟩
theorem valid1995 : certificate1995.Valid := by decide +kernel
theorem bound1995 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1995.a certificate1995.b certificate1995.c x ≤ (certificate1995.bound:ℝ) :=
  rat_majority_certificate_sound certificate1995 valid1995 x hx0 hx1

def certificate1996 : RatMajorityCertificate := ⟨0,(1000045353298101759/1000000000000000000),(711002597/587500000),(4440221008460520819/10000000000000000000),(44402210084605208191/100000000000000000000),(146038858078990693/200000000000000000),false⟩
theorem valid1996 : certificate1996.Valid := by decide +kernel
theorem bound1996 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1996.a certificate1996.b certificate1996.c x ≤ (certificate1996.bound:ℝ) :=
  rat_majority_certificate_sound certificate1996 valid1996 x hx0 hx1

def certificate1997 : RatMajorityCertificate := ⟨(21931149643415913/125000000000000000),(103073524868879314747503204566109033/125000000000000000000000000000000000),(711002597/587500000),(5086534971770869201/12500000000000000000),(40692279774166953609/100000000000000000000),(146038858078990693/200000000000000000),false⟩
theorem valid1997 : certificate1997.Valid := by decide +kernel
theorem bound1997 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1997.a certificate1997.b certificate1997.c x ≤ (certificate1997.bound:ℝ) :=
  rat_majority_certificate_sound certificate1997 valid1997 x hx0 hx1

def certificate1998 : RatMajorityCertificate := ⟨0,(1000045353298101759/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(551763795336112229/1000000000000000000),false⟩
theorem valid1998 : certificate1998.Valid := by decide +kernel
theorem bound1998 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1998.a certificate1998.b certificate1998.c x ≤ (certificate1998.bound:ℝ) :=
  rat_majority_certificate_sound certificate1998 valid1998 x hx0 hx1

def certificate1999 : RatMajorityCertificate := ⟨(27920439703516119/125000000000000000),(97083963174721595120783399441246679/125000000000000000000000000000000000),1,(8525403501096246863/25000000000000000000),(34101614004384987453/100000000000000000000),(551763795336112229/1000000000000000000),false⟩
theorem valid1999 : certificate1999.Valid := by decide +kernel
theorem bound1999 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1999.a certificate1999.b certificate1999.c x ≤ (certificate1999.bound:ℝ) :=
  rat_majority_certificate_sound certificate1999 valid1999 x hx0 hx1

end Cycle12.MajorityCertificates.Batch049
