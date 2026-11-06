import Cycle12.RationalDecay

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Decay135

def certificate2700 : RatDecayCertificate := ⟨(42398842930509253/250000000000000000),(231118446031702313983/250000000000000000),40,(1/200000000000000000),(1/40000000000000000000000000000000000),48⟩
theorem valid2700 : certificate2700.Valid := by decide +kernel
theorem sound2700 : certificate2700.Sound := rat_decay_certificate_sound certificate2700 valid2700

def certificate2701 : RatDecayCertificate := ⟨(164964798857652981/1000000000000000000),(231118446031702313983/250000000000000000),40,(1/200000000000000000),(1/40000000000000000000000000000000000),48⟩
theorem valid2701 : certificate2701.Valid := by decide +kernel
theorem sound2701 : certificate2701.Sound := rat_decay_certificate_sound certificate2701 valid2701

def certificate2702 : RatDecayCertificate := ⟨(13937879872224453211/1000000000000000000),(231118446031702313983/250000000000000000),40,(1/200000000000000000),(1/40000000000000000000000000000000000),48⟩
theorem valid2702 : certificate2702.Valid := by decide +kernel
theorem sound2702 : certificate2702.Sound := rat_decay_certificate_sound certificate2702 valid2702

def certificate2703 : RatDecayCertificate := ⟨(13572631670586502881/1000000000000000000),(231118446031702313983/250000000000000000),40,(1/200000000000000000),(1/40000000000000000000000000000000000),48⟩
theorem valid2703 : certificate2703.Valid := by decide +kernel
theorem sound2703 : certificate2703.Sound := rat_decay_certificate_sound certificate2703 valid2703

def certificate2704 : RatDecayCertificate := ⟨(120438835704745411/500000000000000000),(231118446031702313983/250000000000000000),40,(1/200000000000000000),(1/40000000000000000000000000000000000),48⟩
theorem valid2704 : certificate2704.Valid := by decide +kernel
theorem sound2704 : certificate2704.Sound := rat_decay_certificate_sound certificate2704 valid2704

def certificate2705 : RatDecayCertificate := ⟨(240181685145640357/1000000000000000000),(231118446031702313983/250000000000000000),40,(1/200000000000000000),(1/40000000000000000000000000000000000),48⟩
theorem valid2705 : certificate2705.Valid := by decide +kernel
theorem sound2705 : certificate2705.Sound := rat_decay_certificate_sound certificate2705 valid2705

def certificate2706 : RatDecayCertificate := ⟨(51190778014577282013/1000000000000000000),(231118446031702313983/250000000000000000),40,(1/200000000000000000),(1/40000000000000000000000000000000000),48⟩
theorem valid2706 : certificate2706.Valid := by decide +kernel
theorem sound2706 : certificate2706.Sound := rat_decay_certificate_sound certificate2706 valid2706

end Cycle12.CutFailureCertificates.Decay135
