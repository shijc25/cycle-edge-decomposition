import Cycle12.RationalReverseLocal
import Cycle12.GeometryCertificates.Batch050
import Cycle12.GeometryCertificates.Batch051
import Cycle12.GeometryCertificates.Batch052
import Cycle12.GeometryCertificates.Batch053
import Cycle12.PopulationCertificates.Batch050
import Cycle12.PopulationCertificates.Batch051
import Cycle12.PopulationCertificates.Batch052
import Cycle12.PopulationCertificates.Batch053

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Reverse003

def certificate60 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch050.certificate1012,PopulationCertificates.Batch050.certificate1012,(77218118608469083343/1000000000000000000)⟩
theorem valid60 : certificate60.Valid := by decide +kernel
theorem sound60 : certificate60.Sound := rat_reverse_local_certificate_sound certificate60 valid60

def certificate61 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch050.certificate1015,PopulationCertificates.Batch050.certificate1015,(18747053999192045381/250000000000000000)⟩
theorem valid61 : certificate61.Valid := by decide +kernel
theorem sound61 : certificate61.Sound := rat_reverse_local_certificate_sound certificate61 valid61

def certificate62 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch050.certificate1018,PopulationCertificates.Batch050.certificate1018,(72888725871462779773/1000000000000000000)⟩
theorem valid62 : certificate62.Valid := by decide +kernel
theorem sound62 : certificate62.Sound := rat_reverse_local_certificate_sound certificate62 valid62

def certificate63 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch051.certificate1021,PopulationCertificates.Batch051.certificate1021,(70906998550451973203/1000000000000000000)⟩
theorem valid63 : certificate63.Valid := by decide +kernel
theorem sound63 : certificate63.Sound := rat_reverse_local_certificate_sound certificate63 valid63

def certificate64 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch051.certificate1024,PopulationCertificates.Batch051.certificate1024,(4314744067986771071/62500000000000000)⟩
theorem valid64 : certificate64.Valid := by decide +kernel
theorem sound64 : certificate64.Sound := rat_reverse_local_certificate_sound certificate64 valid64

def certificate65 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch051.certificate1027,PopulationCertificates.Batch051.certificate1027,(67267887837799300067/1000000000000000000)⟩
theorem valid65 : certificate65.Valid := by decide +kernel
theorem sound65 : certificate65.Sound := rat_reverse_local_certificate_sound certificate65 valid65

def certificate66 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch051.certificate1030,PopulationCertificates.Batch051.certificate1030,(32798299802838086183/500000000000000000)⟩
theorem valid66 : certificate66.Valid := by decide +kernel
theorem sound66 : certificate66.Sound := rat_reverse_local_certificate_sound certificate66 valid66

def certificate67 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch051.certificate1033,PopulationCertificates.Batch051.certificate1033,(64014108188366111713/1000000000000000000)⟩
theorem valid67 : certificate67.Valid := by decide +kernel
theorem sound67 : certificate67.Sound := rat_reverse_local_certificate_sound certificate67 valid67

def certificate68 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch051.certificate1036,PopulationCertificates.Batch051.certificate1036,(62516274457600879333/1000000000000000000)⟩
theorem valid68 : certificate68.Valid := by decide +kernel
theorem sound68 : certificate68.Sound := rat_reverse_local_certificate_sound certificate68 valid68

def certificate69 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch051.certificate1039,PopulationCertificates.Batch051.certificate1039,(61097290752170452307/1000000000000000000)⟩
theorem valid69 : certificate69.Valid := by decide +kernel
theorem sound69 : certificate69.Sound := rat_reverse_local_certificate_sound certificate69 valid69

def certificate70 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch052.certificate1042,PopulationCertificates.Batch052.certificate1042,(59752297220787890613/1000000000000000000)⟩
theorem valid70 : certificate70.Valid := by decide +kernel
theorem sound70 : certificate70.Sound := rat_reverse_local_certificate_sound certificate70 valid70

def certificate71 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch052.certificate1045,PopulationCertificates.Batch052.certificate1045,(2923859838509496973/50000000000000000)⟩
theorem valid71 : certificate71.Valid := by decide +kernel
theorem sound71 : certificate71.Sound := rat_reverse_local_certificate_sound certificate71 valid71

def certificate72 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch052.certificate1048,PopulationCertificates.Batch052.certificate1048,(11453364316802280833/200000000000000000)⟩
theorem valid72 : certificate72.Valid := by decide +kernel
theorem sound72 : certificate72.Sound := rat_reverse_local_certificate_sound certificate72 valid72

def certificate73 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch052.certificate1051,PopulationCertificates.Batch052.certificate1051,(5611846643325898801/100000000000000000)⟩
theorem valid73 : certificate73.Valid := by decide +kernel
theorem sound73 : certificate73.Sound := rat_reverse_local_certificate_sound certificate73 valid73

def certificate74 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch052.certificate1054,PopulationCertificates.Batch052.certificate1054,(2751414878950761561/50000000000000000)⟩
theorem valid74 : certificate74.Valid := by decide +kernel
theorem sound74 : certificate74.Sound := rat_reverse_local_certificate_sound certificate74 valid74

def certificate75 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch052.certificate1057,PopulationCertificates.Batch052.certificate1057,(53993102576625658271/1000000000000000000)⟩
theorem valid75 : certificate75.Valid := by decide +kernel
theorem sound75 : certificate75.Sound := rat_reverse_local_certificate_sound certificate75 valid75

def certificate76 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch053.certificate1060,PopulationCertificates.Batch053.certificate1060,(6626502733626162647/125000000000000000)⟩
theorem valid76 : certificate76.Valid := by decide +kernel
theorem sound76 : certificate76.Sound := rat_reverse_local_certificate_sound certificate76 valid76

def certificate77 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch053.certificate1063,PopulationCertificates.Batch053.certificate1063,(10415616153009196183/200000000000000000)⟩
theorem valid77 : certificate77.Valid := by decide +kernel
theorem sound77 : certificate77.Sound := rat_reverse_local_certificate_sound certificate77 valid77

def certificate78 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch053.certificate1066,PopulationCertificates.Batch053.certificate1066,(51190778014577282013/1000000000000000000)⟩
theorem valid78 : certificate78.Valid := by decide +kernel
theorem sound78 : certificate78.Sound := rat_reverse_local_certificate_sound certificate78 valid78

end Cycle12.CutFailureCertificates.Reverse003
