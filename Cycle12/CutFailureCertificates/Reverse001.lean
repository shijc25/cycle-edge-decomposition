import Cycle12.RationalReverseLocal
import Cycle12.GeometryCertificates.Batch044
import Cycle12.GeometryCertificates.Batch045
import Cycle12.GeometryCertificates.Batch046
import Cycle12.GeometryCertificates.Batch047
import Cycle12.PopulationCertificates.Batch044
import Cycle12.PopulationCertificates.Batch045
import Cycle12.PopulationCertificates.Batch046
import Cycle12.PopulationCertificates.Batch047

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Reverse001

def certificate20 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch044.certificate892,PopulationCertificates.Batch044.certificate892,(66024617426344354431/250000000000000000)⟩
theorem valid20 : certificate20.Valid := by decide +kernel
theorem sound20 : certificate20.Sound := rat_reverse_local_certificate_sound certificate20 valid20

def certificate21 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch044.certificate895,PopulationCertificates.Batch044.certificate895,(24541518497936938909/100000000000000000)⟩
theorem valid21 : certificate21.Valid := by decide +kernel
theorem sound21 : certificate21.Sound := rat_reverse_local_certificate_sound certificate21 valid21

def certificate22 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch044.certificate898,PopulationCertificates.Batch044.certificate898,(228818270988643024839/1000000000000000000)⟩
theorem valid22 : certificate22.Valid := by decide +kernel
theorem sound22 : certificate22.Sound := rat_reverse_local_certificate_sound certificate22 valid22

def certificate23 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch045.certificate901,PopulationCertificates.Batch045.certificate901,(106984050045440563669/500000000000000000)⟩
theorem valid23 : certificate23.Valid := by decide +kernel
theorem sound23 : certificate23.Sound := rat_reverse_local_certificate_sound certificate23 valid23

def certificate24 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch045.certificate904,PopulationCertificates.Batch045.certificate904,(200643835873219544161/1000000000000000000)⟩
theorem valid24 : certificate24.Valid := by decide +kernel
theorem sound24 : certificate24.Sound := rat_reverse_local_certificate_sound certificate24 valid24

def certificate25 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch045.certificate907,PopulationCertificates.Batch045.certificate907,(188641782133004498637/1000000000000000000)⟩
theorem valid25 : certificate25.Valid := by decide +kernel
theorem sound25 : certificate25.Sound := rat_reverse_local_certificate_sound certificate25 valid25

def certificate26 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch045.certificate910,PopulationCertificates.Batch045.certificate910,(11111972196377217403/62500000000000000)⟩
theorem valid26 : certificate26.Valid := by decide +kernel
theorem sound26 : certificate26.Sound := rat_reverse_local_certificate_sound certificate26 valid26

def certificate27 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch045.certificate913,PopulationCertificates.Batch045.certificate913,(8397892743185907243/50000000000000000)⟩
theorem valid27 : certificate27.Valid := by decide +kernel
theorem sound27 : certificate27.Sound := rat_reverse_local_certificate_sound certificate27 valid27

def certificate28 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch045.certificate916,PopulationCertificates.Batch045.certificate916,(159001572031092771457/1000000000000000000)⟩
theorem valid28 : certificate28.Valid := by decide +kernel
theorem sound28 : certificate28.Sound := rat_reverse_local_certificate_sound certificate28 valid28

def certificate29 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch045.certificate919,PopulationCertificates.Batch045.certificate919,(75413782362913917327/500000000000000000)⟩
theorem valid29 : certificate29.Valid := by decide +kernel
theorem sound29 : certificate29.Sound := rat_reverse_local_certificate_sound certificate29 valid29

def certificate30 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch046.certificate922,PopulationCertificates.Batch046.certificate922,(71673440678203893081/500000000000000000)⟩
theorem valid30 : certificate30.Valid := by decide +kernel
theorem sound30 : certificate30.Sound := rat_reverse_local_certificate_sound certificate30 valid30

def certificate31 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch046.certificate925,PopulationCertificates.Batch046.certificate925,(4265093293577547547/31250000000000000)⟩
theorem valid31 : certificate31.Valid := by decide +kernel
theorem sound31 : certificate31.Sound := rat_reverse_local_certificate_sound certificate31 valid31

def certificate32 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch046.certificate928,PopulationCertificates.Batch046.certificate928,(33474572514713658619/250000000000000000)⟩
theorem valid32 : certificate32.Valid := by decide +kernel
theorem sound32 : certificate32.Sound := rat_reverse_local_certificate_sound certificate32 valid32

def certificate33 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch046.certificate931,PopulationCertificates.Batch046.certificate931,(130794770295182130821/1000000000000000000)⟩
theorem valid33 : certificate33.Valid := by decide +kernel
theorem sound33 : certificate33.Sound := rat_reverse_local_certificate_sound certificate33 valid33

def certificate34 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch046.certificate934,PopulationCertificates.Batch046.certificate934,(24871695721055746119/200000000000000000)⟩
theorem valid34 : certificate34.Valid := by decide +kernel
theorem sound34 : certificate34.Sound := rat_reverse_local_certificate_sound certificate34 valid34

def certificate35 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch046.certificate937,PopulationCertificates.Batch046.certificate937,(15276206246377236421/125000000000000000)⟩
theorem valid35 : certificate35.Valid := by decide +kernel
theorem sound35 : certificate35.Sound := rat_reverse_local_certificate_sound certificate35 valid35

def certificate36 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch047.certificate940,PopulationCertificates.Batch047.certificate940,(11956327692888543107/100000000000000000)⟩
theorem valid36 : certificate36.Valid := by decide +kernel
theorem sound36 : certificate36.Sound := rat_reverse_local_certificate_sound certificate36 valid36

def certificate37 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch047.certificate943,PopulationCertificates.Batch047.certificate943,(118568633072295810743/1000000000000000000)⟩
theorem valid37 : certificate37.Valid := by decide +kernel
theorem sound37 : certificate37.Sound := rat_reverse_local_certificate_sound certificate37 valid37

def certificate38 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch047.certificate946,PopulationCertificates.Batch047.certificate946,(117305588853859211441/1000000000000000000)⟩
theorem valid38 : certificate38.Valid := by decide +kernel
theorem sound38 : certificate38.Sound := rat_reverse_local_certificate_sound certificate38 valid38

def certificate39 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch047.certificate949,PopulationCertificates.Batch047.certificate949,(116065987269368630229/1000000000000000000)⟩
theorem valid39 : certificate39.Valid := by decide +kernel
theorem sound39 : certificate39.Sound := rat_reverse_local_certificate_sound certificate39 valid39

end Cycle12.CutFailureCertificates.Reverse001
