import Cycle12.RationalReverseLocal
import Cycle12.GeometryCertificates.Batch041
import Cycle12.GeometryCertificates.Batch042
import Cycle12.GeometryCertificates.Batch043
import Cycle12.GeometryCertificates.Batch044
import Cycle12.PopulationCertificates.Batch041
import Cycle12.PopulationCertificates.Batch042
import Cycle12.PopulationCertificates.Batch043
import Cycle12.PopulationCertificates.Batch044

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Reverse000

def certificate0 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch041.certificate832,PopulationCertificates.Batch041.certificate832,(8142440866839713898969/1000000000000000000)⟩
theorem valid0 : certificate0.Valid := by decide +kernel
theorem sound0 : certificate0.Sound := rat_reverse_local_certificate_sound certificate0 valid0

def certificate1 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch041.certificate835,PopulationCertificates.Batch041.certificate835,(5249632139338523756971/1000000000000000000)⟩
theorem valid1 : certificate1.Valid := by decide +kernel
theorem sound1 : certificate1.Sound := rat_reverse_local_certificate_sound certificate1 valid1

def certificate2 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch041.certificate838,PopulationCertificates.Batch041.certificate838,(459076752045237331641/125000000000000000)⟩
theorem valid2 : certificate2.Valid := by decide +kernel
theorem sound2 : certificate2.Sound := rat_reverse_local_certificate_sound certificate2 valid2

def certificate3 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch042.certificate841,PopulationCertificates.Batch042.certificate841,(1359192886780647008809/500000000000000000)⟩
theorem valid3 : certificate3.Valid := by decide +kernel
theorem sound3 : certificate3.Sound := rat_reverse_local_certificate_sound certificate3 valid3

def certificate4 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch042.certificate844,PopulationCertificates.Batch042.certificate844,(524214142517447081827/250000000000000000)⟩
theorem valid4 : certificate4.Valid := by decide +kernel
theorem sound4 : certificate4.Sound := rat_reverse_local_certificate_sound certificate4 valid4

def certificate5 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch042.certificate847,PopulationCertificates.Batch042.certificate847,(166925026710124212391/100000000000000000)⟩
theorem valid5 : certificate5.Valid := by decide +kernel
theorem sound5 : certificate5.Sound := rat_reverse_local_certificate_sound certificate5 valid5

def certificate6 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch042.certificate850,PopulationCertificates.Batch042.certificate850,(170290686494742212221/125000000000000000)⟩
theorem valid6 : certificate6.Valid := by decide +kernel
theorem sound6 : certificate6.Sound := rat_reverse_local_certificate_sound certificate6 valid6

def certificate7 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch042.certificate853,PopulationCertificates.Batch042.certificate853,(1134454185206295057247/1000000000000000000)⟩
theorem valid7 : certificate7.Valid := by decide +kernel
theorem sound7 : certificate7.Sound := rat_reverse_local_certificate_sound certificate7 valid7

def certificate8 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch042.certificate856,PopulationCertificates.Batch042.certificate856,(960547271630004333981/1000000000000000000)⟩
theorem valid8 : certificate8.Valid := by decide +kernel
theorem sound8 : certificate8.Sound := rat_reverse_local_certificate_sound certificate8 valid8

def certificate9 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch042.certificate859,PopulationCertificates.Batch042.certificate859,(82477837719044182909/100000000000000000)⟩
theorem valid9 : certificate9.Valid := by decide +kernel
theorem sound9 : certificate9.Sound := rat_reverse_local_certificate_sound certificate9 valid9

def certificate10 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch043.certificate862,PopulationCertificates.Batch043.certificate862,(716663889080923635183/1000000000000000000)⟩
theorem valid10 : certificate10.Valid := by decide +kernel
theorem sound10 : certificate10.Sound := rat_reverse_local_certificate_sound certificate10 valid10

def certificate11 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch043.certificate865,PopulationCertificates.Batch043.certificate865,(629152087847950917263/1000000000000000000)⟩
theorem valid11 : certificate11.Valid := by decide +kernel
theorem sound11 : certificate11.Sound := rat_reverse_local_certificate_sound certificate11 valid11

def certificate12 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch043.certificate868,PopulationCertificates.Batch043.certificate868,(27864686587306082013/50000000000000000)⟩
theorem valid12 : certificate12.Valid := by decide +kernel
theorem sound12 : certificate12.Sound := rat_reverse_local_certificate_sound certificate12 valid12

def certificate13 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch043.certificate871,PopulationCertificates.Batch043.certificate871,(6219309248321387863/12500000000000000)⟩
theorem valid13 : certificate13.Valid := by decide +kernel
theorem sound13 : certificate13.Sound := rat_reverse_local_certificate_sound certificate13 valid13

def certificate14 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch043.certificate874,PopulationCertificates.Batch043.certificate874,(44731267185079002101/100000000000000000)⟩
theorem valid14 : certificate14.Valid := by decide +kernel
theorem sound14 : certificate14.Sound := rat_reverse_local_certificate_sound certificate14 valid14

def certificate15 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch043.certificate877,PopulationCertificates.Batch043.certificate877,(202332711057162724971/500000000000000000)⟩
theorem valid15 : certificate15.Valid := by decide +kernel
theorem sound15 : certificate15.Sound := rat_reverse_local_certificate_sound certificate15 valid15

def certificate16 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch044.certificate880,PopulationCertificates.Batch044.certificate880,(184069479988831151739/500000000000000000)⟩
theorem valid16 : certificate16.Valid := by decide +kernel
theorem sound16 : certificate16.Sound := rat_reverse_local_certificate_sound certificate16 valid16

def certificate17 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch044.certificate883,PopulationCertificates.Batch044.certificate883,(168324487635071533077/500000000000000000)⟩
theorem valid17 : certificate17.Valid := by decide +kernel
theorem sound17 : certificate17.Sound := rat_reverse_local_certificate_sound certificate17 valid17

def certificate18 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch044.certificate886,PopulationCertificates.Batch044.certificate886,(309208350229141526139/1000000000000000000)⟩
theorem valid18 : certificate18.Valid := by decide +kernel
theorem sound18 : certificate18.Sound := rat_reverse_local_certificate_sound certificate18 valid18

def certificate19 : RatReverseLocalCertificate := ⟨GeometryCertificates.Batch044.certificate889,PopulationCertificates.Batch044.certificate889,(142609576731169286461/500000000000000000)⟩
theorem valid19 : certificate19.Valid := by decide +kernel
theorem sound19 : certificate19.Sound := rat_reverse_local_certificate_sound certificate19 valid19

end Cycle12.CutFailureCertificates.Reverse000
