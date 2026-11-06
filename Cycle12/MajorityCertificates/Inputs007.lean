import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch007

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs007

def inputs140 : RatMajorityInputs := ⟨(13415717745574287420495447/25000000000000000000000),(104448066943341/25000000000000),(251403715751578669/250000000000000000),(213174877253248307/1000000000000000000),(104448066943341/50000000000000),(61907835789548569/500000000000000000),25⟩
theorem inputs_valid140 : inputs140.Valid := by decide +kernel
def envelope140 : RatMajorityEnvelope := ⟨70,0,inputs140,(2389923277/1994260000),(726186720740312439/1000000000000000000)⟩
theorem envelope_sound140 : envelope140.Sound := by
  apply rat_majority_inputs_envelopes inputs140 inputs_valid140
  · norm_num [envelope140]
  · intro rho hr0 hr1
    have hh := Batch007.bound280 rho hr0 hr1
    norm_num [Batch007.certificate280,envelope140,inputs140,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound281 rho hr0 hr1
    norm_num [Batch007.certificate281,envelope140,inputs140,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs141 : RatMajorityInputs := ⟨(13415717745574287420495447/25000000000000000000000),(61596652481581/12500000000000),(251403715751578669/250000000000000000),(8179511013062727/62500000000000000),(61596652481581/25000000000000),(42552644315302143/500000000000000000),26⟩
theorem inputs_valid141 : inputs141.Valid := by decide +kernel
def envelope141 : RatMajorityEnvelope := ⟨70,1,inputs141,1,(542944942135122611/1000000000000000000)⟩
theorem envelope_sound141 : envelope141.Sound := by
  apply rat_majority_inputs_envelopes inputs141 inputs_valid141
  · norm_num [envelope141]
  · intro rho hr0 hr1
    have hh := Batch007.bound282 rho hr0 hr1
    norm_num [Batch007.certificate282,envelope141,inputs141,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound283 rho hr0 hr1
    norm_num [Batch007.certificate283,envelope141,inputs141,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs142 : RatMajorityInputs := ⟨(6652889133969440180017319/12500000000000000000000),(209235470321493/50000000000000),(502830730077786809/500000000000000000),(2653355594359/12500000000000),(209235470321493/100000000000000),(61698115975823389/500000000000000000),25⟩
theorem inputs_valid142 : inputs142.Valid := by decide +kernel
def envelope142 : RatMajorityEnvelope := ⟨71,0,inputs142,(2387847583/1993220000),(145149463984587353/200000000000000000)⟩
theorem envelope_sound142 : envelope142.Sound := by
  apply rat_majority_inputs_envelopes inputs142 inputs_valid142
  · norm_num [envelope142]
  · intro rho hr0 hr1
    have hh := Batch007.bound284 rho hr0 hr1
    norm_num [Batch007.certificate284,envelope142,inputs142,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound285 rho hr0 hr1
    norm_num [Batch007.certificate285,envelope142,inputs142,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs143 : RatMajorityInputs := ⟨(6652889133969440180017319/12500000000000000000000),(246384339285013/50000000000000),(502830730077786809/500000000000000000),(130876169782552757/1000000000000000000),(246384339285013/100000000000000),(85107221088385287/1000000000000000000),27⟩
theorem inputs_valid143 : inputs143.Valid := by decide +kernel
def envelope143 : RatMajorityEnvelope := ⟨71,1,inputs143,1,(271483336283526381/500000000000000000)⟩
theorem envelope_sound143 : envelope143.Sound := by
  apply rat_majority_inputs_envelopes inputs143 inputs_valid143
  · norm_num [envelope143]
  · intro rho hr0 hr1
    have hh := Batch007.bound286 rho hr0 hr1
    norm_num [Batch007.certificate286,envelope143,inputs143,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound287 rho hr0 hr1
    norm_num [Batch007.certificate287,envelope143,inputs143,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs144 : RatMajorityInputs := ⟨(26395197330631476903560119/50000000000000000000000),(206298212700113/50000000000000),(25142701813632421/25000000000000000),(5505533091514701/25000000000000000),(206298212700113/100000000000000),(127074452136130809/1000000000000000000),25⟩
theorem inputs_valid144 : inputs144.Valid := by decide +kernel
def envelope144 : RatMajorityEnvelope := ⟨72,0,inputs144,(1194505301/996095000),(45478139175459991/62500000000000000)⟩
theorem envelope_sound144 : envelope144.Sound := by
  apply rat_majority_inputs_envelopes inputs144 inputs_valid144
  · norm_num [envelope144]
  · intro rho hr0 hr1
    have hh := Batch007.bound288 rho hr0 hr1
    norm_num [Batch007.certificate288,envelope144,inputs144,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound289 rho hr0 hr1
    norm_num [Batch007.certificate289,envelope144,inputs144,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs145 : RatMajorityInputs := ⟨(26395197330631476903560119/50000000000000000000000),(493126346640849/100000000000000),(25142701813632421/25000000000000000),(130561968645481227/1000000000000000000),(493126346640849/200000000000000),(84955156422702653/1000000000000000000),26⟩
theorem inputs_valid145 : inputs145.Valid := by decide +kernel
def envelope145 : RatMajorityEnvelope := ⟨72,1,inputs145,1,(135738677964928859/250000000000000000)⟩
theorem envelope_sound145 : envelope145.Sound := by
  apply rat_majority_inputs_envelopes inputs145 inputs_valid145
  · norm_num [envelope145]
  · intro rho hr0 hr1
    have hh := Batch007.bound290 rho hr0 hr1
    norm_num [Batch007.certificate290,envelope145,inputs145,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound291 rho hr0 hr1
    norm_num [Batch007.certificate291,envelope145,inputs145,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs146 : RatMajorityInputs := ⟨(6545539058309049869048349/12500000000000000000000),(52364630624463/12500000000000),(100575472619027981/100000000000000000),(42334876206334941/200000000000000000),(52364630624463/25000000000000),(2462426014095711/20000000000000000),25⟩
theorem inputs_valid146 : inputs146.Valid := by decide +kernel
def envelope146 : RatMajorityEnvelope := ⟨73,0,inputs146,(158954591/132744000),(725259056286153483/1000000000000000000)⟩
theorem envelope_sound146 : envelope146.Sound := by
  apply rat_majority_inputs_envelopes inputs146 inputs_valid146
  · norm_num [envelope146]
  · intro rho hr0 hr1
    have hh := Batch007.bound292 rho hr0 hr1
    norm_num [Batch007.certificate292,envelope146,inputs146,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound293 rho hr0 hr1
    norm_num [Batch007.certificate293,envelope146,inputs146,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs147 : RatMajorityInputs := ⟨(6545539058309049869048349/12500000000000000000000),(7705132166979/1562500000000),(100575472619027981/100000000000000000),(65280057628387901/500000000000000000),(7705132166979/3125000000000),(84954259281530141/1000000000000000000),26⟩
theorem inputs_valid147 : inputs147.Valid := by decide +kernel
def envelope147 : RatMajorityEnvelope := ⟨73,1,inputs147,1,(542975856841041669/1000000000000000000)⟩
theorem envelope_sound147 : envelope147.Sound := by
  apply rat_majority_inputs_envelopes inputs147 inputs_valid147
  · norm_num [envelope147]
  · intro rho hr0 hr1
    have hh := Batch007.bound294 rho hr0 hr1
    norm_num [Batch007.certificate294,envelope147,inputs147,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound295 rho hr0 hr1
    norm_num [Batch007.certificate295,envelope147,inputs147,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs148 : RatMajorityInputs := ⟨(5194525769750218846496519/10000000000000000000000),(20883805282131/5000000000000),(201160272052086753/200000000000000000),(213330344208536807/1000000000000000000),(20883805282131/10000000000000),(123887605928343779/1000000000000000000),25⟩
theorem inputs_valid148 : inputs148.Valid := by decide +kernel
def envelope148 : RatMajorityEnvelope := ⟨74,0,inputs148,(238348641/199015000),(725618654364167109/1000000000000000000)⟩
theorem envelope_sound148 : envelope148.Sound := by
  apply rat_majority_inputs_envelopes inputs148 inputs_valid148
  · norm_num [envelope148]
  · intro rho hr0 hr1
    have hh := Batch007.bound296 rho hr0 hr1
    norm_num [Batch007.certificate296,envelope148,inputs148,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound297 rho hr0 hr1
    norm_num [Batch007.certificate297,envelope148,inputs148,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs149 : RatMajorityInputs := ⟨(5194525769750218846496519/10000000000000000000000),(6166148574237/1250000000000),(201160272052086753/200000000000000000),(65208386541816579/500000000000000000),(6166148574237/2500000000000),(42442434215226019/500000000000000000),26⟩
theorem inputs_valid149 : inputs149.Valid := by decide +kernel
def envelope149 : RatMajorityEnvelope := ⟨74,1,inputs149,1,(135745506266726243/250000000000000000)⟩
theorem envelope_sound149 : envelope149.Sound := by
  apply rat_majority_inputs_envelopes inputs149 inputs_valid149
  · norm_num [envelope149]
  · intro rho hr0 hr1
    have hh := Batch007.bound298 rho hr0 hr1
    norm_num [Batch007.certificate298,envelope149,inputs149,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound299 rho hr0 hr1
    norm_num [Batch007.certificate299,envelope149,inputs149,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs150 : RatMajorityInputs := ⟨(25766286515571404491635063/50000000000000000000000),(26200245636929/6250000000000),(1005848030043886201/1000000000000000000),(105646536909890377/500000000000000000),(26200245636929/12500000000000),(30736204729542557/250000000000000000),25⟩
theorem inputs_valid150 : inputs150.Valid := by decide +kernel
def envelope150 : RatMajorityEnvelope := ⟨75,0,inputs150,(2381126389/1989140000),(72492174666023131/100000000000000000)⟩
theorem envelope_sound150 : envelope150.Sound := by
  apply rat_majority_inputs_envelopes inputs150 inputs_valid150
  · norm_num [envelope150]
  · intro rho hr0 hr1
    have hh := Batch007.bound300 rho hr0 hr1
    norm_num [Batch007.certificate300,envelope150,inputs150,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound301 rho hr0 hr1
    norm_num [Batch007.certificate301,envelope150,inputs150,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs151 : RatMajorityInputs := ⟨(25766286515571404491635063/50000000000000000000000),(246646759337281/50000000000000),(1005848030043886201/1000000000000000000),(16301917714059161/125000000000000000),(246646759337281/100000000000000),(42442087730273423/500000000000000000),26⟩
theorem inputs_valid151 : inputs151.Valid := by decide +kernel
def envelope151 : RatMajorityEnvelope := ⟨75,1,inputs151,1,(108600645202111751/200000000000000000)⟩
theorem envelope_sound151 : envelope151.Sound := by
  apply rat_majority_inputs_envelopes inputs151 inputs_valid151
  · norm_num [envelope151]
  · intro rho hr0 hr1
    have hh := Batch007.bound302 rho hr0 hr1
    norm_num [Batch007.certificate302,envelope151,inputs151,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound303 rho hr0 hr1
    norm_num [Batch007.certificate303,envelope151,inputs151,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs152 : RatMajorityInputs := ⟨(12781597863495490662382519/25000000000000000000000),(6539415237971/1562500000000),(2011789406963521/2000000000000000),(106099808075927703/500000000000000000),(6539415237971/3125000000000),(123364378496205379/1000000000000000000),25⟩
theorem inputs_valid152 : inputs152.Valid := by decide +kernel
def envelope152 : RatMajorityEnvelope := ⟨76,0,inputs152,(339970391/284020000),(90621785116226011/125000000000000000)⟩
theorem envelope_sound152 : envelope152.Sound := by
  apply rat_majority_inputs_envelopes inputs152 inputs_valid152
  · norm_num [envelope152]
  · intro rho hr0 hr1
    have hh := Batch007.bound304 rho hr0 hr1
    norm_num [Batch007.certificate304,envelope152,inputs152,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound305 rho hr0 hr1
    norm_num [Batch007.certificate305,envelope152,inputs152,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs153 : RatMajorityInputs := ⟨(12781597863495490662382519/25000000000000000000000),(15421361699513/3125000000000),(2011789406963521/2000000000000000),(65124410197350463/500000000000000000),(15421361699513/6250000000000),(42401775081873253/500000000000000000),28⟩
theorem inputs_valid153 : inputs153.Valid := by decide +kernel
def envelope153 : RatMajorityEnvelope := ⟨76,1,inputs153,1,(543006979578935267/1000000000000000000)⟩
theorem envelope_sound153 : envelope153.Sound := by
  apply rat_majority_inputs_envelopes inputs153 inputs_valid153
  · norm_num [envelope153]
  · intro rho hr0 hr1
    have hh := Batch007.bound306 rho hr0 hr1
    norm_num [Batch007.certificate306,envelope153,inputs153,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound307 rho hr0 hr1
    norm_num [Batch007.certificate307,envelope153,inputs153,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs154 : RatMajorityInputs := ⟨(10145317245770917728090947/20000000000000000000000),(83084887184827/20000000000000),(502970688770813271/500000000000000000),(108181266072166363/500000000000000000),(83084887184827/40000000000000),(15661282091562911/125000000000000000),26⟩
theorem inputs_valid154 : inputs154.Valid := by decide +kernel
def envelope154 : RatMajorityEnvelope := ⟨77,0,inputs154,(2379886393/1987150000),(90749062905134489/125000000000000000)⟩
theorem envelope_sound154 : envelope154.Sound := by
  apply rat_majority_inputs_envelopes inputs154 inputs_valid154
  · norm_num [envelope154]
  · intro rho hr0 hr1
    have hh := Batch007.bound308 rho hr0 hr1
    norm_num [Batch007.certificate308,envelope154,inputs154,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound309 rho hr0 hr1
    norm_num [Batch007.certificate309,envelope154,inputs154,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs155 : RatMajorityInputs := ⟨(10145317245770917728090947/20000000000000000000000),(24674222685299/5000000000000),(502970688770813271/500000000000000000),(130248050395874441/1000000000000000000),(24674222685299/10000000000000),(3392127092664573/40000000000000000),26⟩
theorem inputs_valid155 : inputs155.Valid := by decide +kernel
def envelope155 : RatMajorityEnvelope := ⟨77,1,inputs155,1,(543028256866526031/1000000000000000000)⟩
theorem envelope_sound155 : envelope155.Sound := by
  apply rat_majority_inputs_envelopes inputs155 inputs_valid155
  · norm_num [envelope155]
  · intro rho hr0 hr1
    have hh := Batch007.bound310 rho hr0 hr1
    norm_num [Batch007.certificate310,envelope155,inputs155,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound311 rho hr0 hr1
    norm_num [Batch007.certificate311,envelope155,inputs155,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs156 : RatMajorityInputs := ⟨(1258325844543939458956241/2500000000000000000000),(209689946013931/50000000000000),(1005988049187207481/1000000000000000000),(105529740406776341/500000000000000000),(209689946013931/100000000000000),(15354587313359863/125000000000000000),25⟩
theorem inputs_valid156 : inputs156.Valid := by decide +kernel
def envelope156 : RatMajorityEnvelope := ⟨78,0,inputs156,(95045517/79446800),(362162033528628973/500000000000000000)⟩
theorem envelope_sound156 : envelope156.Sound := by
  apply rat_majority_inputs_envelopes inputs156 inputs_valid156
  · norm_num [envelope156]
  · intro rho hr0 hr1
    have hh := Batch007.bound312 rho hr0 hr1
    norm_num [Batch007.certificate312,envelope156,inputs156,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound313 rho hr0 hr1
    norm_num [Batch007.certificate313,envelope156,inputs156,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs157 : RatMajorityInputs := ⟨(1258325844543939458956241/2500000000000000000000),(493677159992797/100000000000000),(1005988049187207481/1000000000000000000),(65039699832985049/500000000000000000),(493677159992797/200000000000000),(4236075307112497/50000000000000000),26⟩
theorem inputs_valid157 : inputs157.Valid := by decide +kernel
def envelope157 : RatMajorityEnvelope := ⟨78,1,inputs157,1,(543031805300947067/1000000000000000000)⟩
theorem envelope_sound157 : envelope157.Sound := by
  apply rat_majority_inputs_envelopes inputs157 inputs_valid157
  · norm_num [envelope157]
  · intro rho hr0 hr1
    have hh := Batch007.bound314 rho hr0 hr1
    norm_num [Batch007.certificate314,envelope157,inputs157,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound315 rho hr0 hr1
    norm_num [Batch007.certificate315,envelope157,inputs157,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs158 : RatMajorityInputs := ⟨(49754153745413604714495387/100000000000000000000000),(83423507121459/20000000000000),(4024232188047261/4000000000000000),(107039614180627361/500000000000000000),(83423507121459/40000000000000),(124234089062969913/1000000000000000000),25⟩
theorem inputs_valid158 : inputs158.Valid := by decide +kernel
def envelope158 : RatMajorityEnvelope := ⟨79,0,inputs158,(2376825059/1977590000),(729665532219830377/1000000000000000000)⟩
theorem envelope_sound158 : envelope158.Sound := by
  apply rat_majority_inputs_envelopes inputs158 inputs_valid158
  · norm_num [envelope158]
  · intro rho hr0 hr1
    have hh := Batch007.bound316 rho hr0 hr1
    norm_num [Batch007.certificate316,envelope158,inputs158,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound317 rho hr0 hr1
    norm_num [Batch007.certificate317,envelope158,inputs158,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs159 : RatMajorityInputs := ⟨(49754153745413604714495387/100000000000000000000000),(123046164171159/25000000000000),(4024232188047261/4000000000000000),(16423831685322513/125000000000000000),(123046164171159/50000000000000),(1066951333709223/12500000000000000),26⟩
theorem inputs_valid159 : inputs159.Valid := by decide +kernel
def envelope159 : RatMajorityEnvelope := ⟨79,1,inputs159,1,(271601229843435523/500000000000000000)⟩
theorem envelope_sound159 : envelope159.Sound := by
  apply rat_majority_inputs_envelopes inputs159 inputs_valid159
  · norm_num [envelope159]
  · intro rho hr0 hr1
    have hh := Batch007.bound318 rho hr0 hr1
    norm_num [Batch007.certificate318,envelope159,inputs159,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch007.bound319 rho hr0 hr1
    norm_num [Batch007.certificate319,envelope159,inputs159,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope140,envelope141,envelope142,envelope143,envelope144,envelope145,envelope146,envelope147,envelope148,envelope149,envelope150,envelope151,envelope152,envelope153,envelope154,envelope155,envelope156,envelope157,envelope158,envelope159]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound140
  · exact envelope_sound141
  · exact envelope_sound142
  · exact envelope_sound143
  · exact envelope_sound144
  · exact envelope_sound145
  · exact envelope_sound146
  · exact envelope_sound147
  · exact envelope_sound148
  · exact envelope_sound149
  · exact envelope_sound150
  · exact envelope_sound151
  · exact envelope_sound152
  · exact envelope_sound153
  · exact envelope_sound154
  · exact envelope_sound155
  · exact envelope_sound156
  · exact envelope_sound157
  · exact envelope_sound158
  · exact envelope_sound159

end Cycle12.MajorityCertificates.Inputs007
