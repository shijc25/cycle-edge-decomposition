import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch286
import Cycle12.MergedCutProfiles.Batch287
import Cycle12.MergedCutProfiles.Batch288

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch150

def retention1800 : RatCutRetentionCertificate := ⟨(21/320),(263/4000),(1234169895734207215/2508003200668990217),(4650575479082364093/1000000000000000000),(11/10),(1862271033732125674512771944341844410991/1860230191632945637200000000000000000000),false,MergedCutProfiles.Batch286.profile11475,(fun _ => MergedCutProfiles.Batch286.profile11475)⟩
theorem profilesValid1800 : retention1800.ProfilesValid := by
  exact MergedCutProfiles.Batch286.valid11475
theorem numericValid1800 : retention1800.NumericValid := by decide +kernel
def certificate1800 : RatCutBinCertificate := ⟨⟨retention1800,(2710793315522510043/1000000000000000000),(14200228663144707/62500000000000000),(8814343946614643429/500000000000000000),(35398377488915435619/200000000000000000),(962656205139512871/1000000000000000000)⟩,(988104704045018349/1000000000000000000),(396980483107844557/1000000000000000000),(236260415600900741/1000000000000000000),(174253515321697921/1000000000000000000)⟩
theorem valid1800 : certificate1800.Valid := by decide +kernel
theorem sound1800 : certificate1800.Sound := rat_cut_bin_certificate_sound certificate1800 profilesValid1800 numericValid1800 valid1800

def retention1801 : RatCutRetentionCertificate := ⟨(21/320),(263/4000),(4986046378766197149/10032012802675960868),(246833979146841443/50000000000000000),(11/10),(100169435379339117176366847564937279/100748562917078140000000000000000000),false,MergedCutProfiles.Batch286.profile11476,(fun _ => MergedCutProfiles.Batch286.profile11476)⟩
theorem profilesValid1801 : retention1801.ProfilesValid := by
  exact MergedCutProfiles.Batch286.valid11476
theorem numericValid1801 : retention1801.NumericValid := by decide +kernel
def certificate1801 : RatCutBinCertificate := ⟨⟨retention1801,(2710793315522510043/1000000000000000000),(14200228663144707/62500000000000000),(8814343946614643429/500000000000000000),(35398377488915435619/200000000000000000),(14934553542867473/15625000000000000)⟩,(988104704045018349/1000000000000000000),(99955837179375843/250000000000000000),(23364425881599333/100000000000000000),(34547988203678937/200000000000000000)⟩
theorem valid1801 : certificate1801.Valid := by decide +kernel
theorem sound1801 : certificate1801.Sound := rat_cut_bin_certificate_sound certificate1801 profilesValid1801 numericValid1801 valid1801

def retention1802 : RatCutRetentionCertificate := ⟨(21/320),(263/4000),(1/2),(4986046378766197149/1000000000000000000),(11/10),(1972391658444530214291314273679112778519/1994418551506478859600000000000000000000),false,MergedCutProfiles.Batch286.profile11473,(fun _ => MergedCutProfiles.Batch286.profile11473)⟩
theorem profilesValid1802 : retention1802.ProfilesValid := by
  exact MergedCutProfiles.Batch286.valid11473
theorem numericValid1802 : retention1802.NumericValid := by decide +kernel
def certificate1802 : RatCutBinCertificate := ⟨⟨retention1802,(2710793315522510043/1000000000000000000),(14200228663144707/62500000000000000),(8814343946614643429/500000000000000000),(35398377488915435619/200000000000000000),(950515494793575691/1000000000000000000)⟩,(988104704045018349/1000000000000000000),(50256377654585373/125000000000000000),(14475522613572167/62500000000000000),(42662410747057961/250000000000000000)⟩
theorem valid1802 : certificate1802.Valid := by decide +kernel
theorem sound1802 : certificate1802.Sound := rat_cut_bin_certificate_sound certificate1802 profilesValid1802 numericValid1802 valid1802

def retention1803 : RatCutRetentionCertificate := ⟨(263/4000),(527/8000),(1345980022622438269/9986027114144570898),(913072024108182507/1000000000000000000),(49/20),(576961148874145242781/320000000000000000000),true,MergedCutProfiles.Batch286.profile11477,![MergedCutProfiles.Batch286.profile11477,MergedCutProfiles.Batch286.profile11478,MergedCutProfiles.Batch286.profile11479,MergedCutProfiles.Batch287.profile11480,MergedCutProfiles.Batch287.profile11481,MergedCutProfiles.Batch287.profile11482,MergedCutProfiles.Batch287.profile11483,MergedCutProfiles.Batch287.profile11484,MergedCutProfiles.Batch287.profile11485,MergedCutProfiles.Batch287.profile11486,MergedCutProfiles.Batch287.profile11487,MergedCutProfiles.Batch287.profile11488,MergedCutProfiles.Batch287.profile11489,MergedCutProfiles.Batch287.profile11490,MergedCutProfiles.Batch287.profile11491,MergedCutProfiles.Batch287.profile11492]⟩
theorem profilesValid1803 : retention1803.ProfilesValid := by
  change ∀ j : Fin 16, (retention1803.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch286.valid11477
  · exact MergedCutProfiles.Batch286.valid11478
  · exact MergedCutProfiles.Batch286.valid11479
  · exact MergedCutProfiles.Batch287.valid11480
  · exact MergedCutProfiles.Batch287.valid11481
  · exact MergedCutProfiles.Batch287.valid11482
  · exact MergedCutProfiles.Batch287.valid11483
  · exact MergedCutProfiles.Batch287.valid11484
  · exact MergedCutProfiles.Batch287.valid11485
  · exact MergedCutProfiles.Batch287.valid11486
  · exact MergedCutProfiles.Batch287.valid11487
  · exact MergedCutProfiles.Batch287.valid11488
  · exact MergedCutProfiles.Batch287.valid11489
  · exact MergedCutProfiles.Batch287.valid11490
  · exact MergedCutProfiles.Batch287.valid11491
  · exact MergedCutProfiles.Batch287.valid11492
theorem numericValid1803 : retention1803.NumericValid := by decide +kernel
def certificate1803 : RatCutBinCertificate := ⟨⟨retention1803,(30009995404666049/12500000000000000),(57064330308281523/250000000000000000),(8835637598779032713/500000000000000000),(176606313810354852443/1000000000000000000),(172698327403381211/100000000000000000)⟩,(247365066026214591/250000000000000000),(332362613234673317/1000000000000000000),(37690112580751683/125000000000000000),(9970664574394277/62500000000000000)⟩
theorem valid1803 : certificate1803.Valid := by decide +kernel
theorem sound1803 : certificate1803.Sound := rat_cut_bin_certificate_sound certificate1803 profilesValid1803 numericValid1803 valid1803

def retention1804 : RatCutRetentionCertificate := ⟨(263/4000),(527/8000),(1364037019015303015/4993013557072285449),(1345980022622438269/1000000000000000000),(7/4),(372879678884553432937/256000000000000000000),true,MergedCutProfiles.Batch287.profile11493,![MergedCutProfiles.Batch287.profile11493,MergedCutProfiles.Batch287.profile11494,MergedCutProfiles.Batch287.profile11495,MergedCutProfiles.Batch287.profile11496,MergedCutProfiles.Batch287.profile11497,MergedCutProfiles.Batch287.profile11498,MergedCutProfiles.Batch287.profile11499,MergedCutProfiles.Batch287.profile11500,MergedCutProfiles.Batch287.profile11501,MergedCutProfiles.Batch287.profile11502,MergedCutProfiles.Batch287.profile11503,MergedCutProfiles.Batch287.profile11504,MergedCutProfiles.Batch287.profile11505,MergedCutProfiles.Batch287.profile11506,MergedCutProfiles.Batch287.profile11507,MergedCutProfiles.Batch287.profile11508]⟩
theorem profilesValid1804 : retention1804.ProfilesValid := by
  change ∀ j : Fin 16, (retention1804.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch287.valid11493
  · exact MergedCutProfiles.Batch287.valid11494
  · exact MergedCutProfiles.Batch287.valid11495
  · exact MergedCutProfiles.Batch287.valid11496
  · exact MergedCutProfiles.Batch287.valid11497
  · exact MergedCutProfiles.Batch287.valid11498
  · exact MergedCutProfiles.Batch287.valid11499
  · exact MergedCutProfiles.Batch287.valid11500
  · exact MergedCutProfiles.Batch287.valid11501
  · exact MergedCutProfiles.Batch287.valid11502
  · exact MergedCutProfiles.Batch287.valid11503
  · exact MergedCutProfiles.Batch287.valid11504
  · exact MergedCutProfiles.Batch287.valid11505
  · exact MergedCutProfiles.Batch287.valid11506
  · exact MergedCutProfiles.Batch287.valid11507
  · exact MergedCutProfiles.Batch287.valid11508
theorem numericValid1804 : retention1804.NumericValid := by decide +kernel
def certificate1804 : RatCutBinCertificate := ⟨⟨retention1804,(30009995404666049/12500000000000000),(57064330308281523/250000000000000000),(8835637598779032713/500000000000000000),(176606313810354852443/1000000000000000000),(1402262596362351079/1000000000000000000)⟩,(247365066026214591/250000000000000000),(90240120333154333/250000000000000000),(271221303036404309/1000000000000000000),(32019518324996983/200000000000000000)⟩
theorem valid1804 : certificate1804.Valid := by decide +kernel
theorem sound1804 : certificate1804.Sound := rat_cut_bin_certificate_sound certificate1804 profilesValid1804 numericValid1804 valid1804

def retention1805 : RatCutRetentionCertificate := ⟨(263/4000),(527/8000),(4311608769690663775/9986027114144570898),(272807403803060603/100000000000000000),(23/20),(141387681415863395251/128000000000000000000),true,MergedCutProfiles.Batch287.profile11509,![MergedCutProfiles.Batch287.profile11509,MergedCutProfiles.Batch287.profile11510,MergedCutProfiles.Batch287.profile11511,MergedCutProfiles.Batch287.profile11512,MergedCutProfiles.Batch287.profile11513,MergedCutProfiles.Batch287.profile11514,MergedCutProfiles.Batch287.profile11515,MergedCutProfiles.Batch287.profile11516,MergedCutProfiles.Batch287.profile11517,MergedCutProfiles.Batch287.profile11518,MergedCutProfiles.Batch287.profile11519,MergedCutProfiles.Batch288.profile11520,MergedCutProfiles.Batch288.profile11521,MergedCutProfiles.Batch288.profile11522,MergedCutProfiles.Batch288.profile11523,MergedCutProfiles.Batch288.profile11524]⟩
theorem profilesValid1805 : retention1805.ProfilesValid := by
  change ∀ j : Fin 16, (retention1805.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch287.valid11509
  · exact MergedCutProfiles.Batch287.valid11510
  · exact MergedCutProfiles.Batch287.valid11511
  · exact MergedCutProfiles.Batch287.valid11512
  · exact MergedCutProfiles.Batch287.valid11513
  · exact MergedCutProfiles.Batch287.valid11514
  · exact MergedCutProfiles.Batch287.valid11515
  · exact MergedCutProfiles.Batch287.valid11516
  · exact MergedCutProfiles.Batch287.valid11517
  · exact MergedCutProfiles.Batch287.valid11518
  · exact MergedCutProfiles.Batch287.valid11519
  · exact MergedCutProfiles.Batch288.valid11520
  · exact MergedCutProfiles.Batch288.valid11521
  · exact MergedCutProfiles.Batch288.valid11522
  · exact MergedCutProfiles.Batch288.valid11523
  · exact MergedCutProfiles.Batch288.valid11524
theorem numericValid1805 : retention1805.NumericValid := by decide +kernel
def certificate1805 : RatCutBinCertificate := ⟨⟨retention1805,(30009995404666049/12500000000000000),(57064330308281523/250000000000000000),(8835637598779032713/500000000000000000),(176606313810354852443/1000000000000000000),(213782833600170651/200000000000000000)⟩,(247365066026214591/250000000000000000),(50716124052525661/125000000000000000),(114136993803356489/500000000000000000),(80839766251448413/500000000000000000)⟩
theorem valid1805 : certificate1805.Valid := by decide +kernel
theorem sound1805 : certificate1805.Sound := rat_cut_bin_certificate_sound certificate1805 profilesValid1805 numericValid1805 valid1805

def retention1806 : RatCutRetentionCertificate := ⟨(263/4000),(527/8000),(4858428681823947109/9986027114144570898),(172464350787626551/40000000000000000),1,(50207293828153729571/51200000000000000000),true,MergedCutProfiles.Batch288.profile11525,![MergedCutProfiles.Batch288.profile11525,MergedCutProfiles.Batch288.profile11526,MergedCutProfiles.Batch288.profile11527,MergedCutProfiles.Batch288.profile11528,MergedCutProfiles.Batch288.profile11529,MergedCutProfiles.Batch288.profile11530,MergedCutProfiles.Batch288.profile11531,MergedCutProfiles.Batch288.profile11532,MergedCutProfiles.Batch288.profile11533,MergedCutProfiles.Batch288.profile11534,MergedCutProfiles.Batch288.profile11535,MergedCutProfiles.Batch288.profile11536,MergedCutProfiles.Batch288.profile11537,MergedCutProfiles.Batch288.profile11538,MergedCutProfiles.Batch288.profile11539,MergedCutProfiles.Batch288.profile11540]⟩
theorem profilesValid1806 : retention1806.ProfilesValid := by
  change ∀ j : Fin 16, (retention1806.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch288.valid11525
  · exact MergedCutProfiles.Batch288.valid11526
  · exact MergedCutProfiles.Batch288.valid11527
  · exact MergedCutProfiles.Batch288.valid11528
  · exact MergedCutProfiles.Batch288.valid11529
  · exact MergedCutProfiles.Batch288.valid11530
  · exact MergedCutProfiles.Batch288.valid11531
  · exact MergedCutProfiles.Batch288.valid11532
  · exact MergedCutProfiles.Batch288.valid11533
  · exact MergedCutProfiles.Batch288.valid11534
  · exact MergedCutProfiles.Batch288.valid11535
  · exact MergedCutProfiles.Batch288.valid11536
  · exact MergedCutProfiles.Batch288.valid11537
  · exact MergedCutProfiles.Batch288.valid11538
  · exact MergedCutProfiles.Batch288.valid11539
  · exact MergedCutProfiles.Batch288.valid11540
theorem numericValid1806 : retention1806.NumericValid := by decide +kernel
def certificate1806 : RatCutBinCertificate := ⟨⟨retention1806,(30009995404666049/12500000000000000),(57064330308281523/250000000000000000),(8835637598779032713/500000000000000000),(176606313810354852443/1000000000000000000),(474795563984461139/500000000000000000)⟩,(247365066026214591/250000000000000000),(214707163776143293/500000000000000000),(103793509019133831/500000000000000000),(15962872826095233/100000000000000000)⟩
theorem valid1806 : certificate1806.Valid := by decide +kernel
theorem sound1806 : certificate1806.Sound := rat_cut_bin_certificate_sound certificate1806 profilesValid1806 numericValid1806 valid1806

def retention1807 : RatCutRetentionCertificate := ⟨(263/4000),(527/8000),(4956083098328608447/9986027114144570898),(4858428681823947109/1000000000000000000),(11/10),(1933597595791089234376695189246028001599/1943371472729578843600000000000000000000),false,MergedCutProfiles.Batch288.profile11541,(fun _ => MergedCutProfiles.Batch288.profile11541)⟩
theorem profilesValid1807 : retention1807.ProfilesValid := by
  exact MergedCutProfiles.Batch288.valid11541
theorem numericValid1807 : retention1807.NumericValid := by decide +kernel
def certificate1807 : RatCutBinCertificate := ⟨⟨retention1807,(30009995404666049/12500000000000000),(57064330308281523/250000000000000000),(8835637598779032713/500000000000000000),(176606313810354852443/1000000000000000000),(120106318467004339/125000000000000000)⟩,(247365066026214591/250000000000000000),(83830285494600197/200000000000000000),(216386010140333251/1000000000000000000),(160566413271692383/1000000000000000000)⟩
theorem valid1807 : certificate1807.Valid := by decide +kernel
theorem sound1807 : certificate1807.Sound := rat_cut_bin_certificate_sound certificate1807 profilesValid1807 numericValid1807 valid1807

def retention1808 : RatCutRetentionCertificate := ⟨(263/4000),(527/8000),(1/2),(4956083098328608447/1000000000000000000),(11/10),(1960085915790536018236750838964825885151/1982433239331443378800000000000000000000),false,MergedCutProfiles.Batch288.profile11542,(fun _ => MergedCutProfiles.Batch288.profile11542)⟩
theorem profilesValid1808 : retention1808.ProfilesValid := by
  exact MergedCutProfiles.Batch288.valid11542
theorem numericValid1808 : retention1808.NumericValid := by decide +kernel
def certificate1808 : RatCutBinCertificate := ⟨⟨retention1808,(30009995404666049/12500000000000000),(57064330308281523/250000000000000000),(8835637598779032713/500000000000000000),(176606313810354852443/1000000000000000000),(954607376876814899/1000000000000000000)⟩,(247365066026214591/250000000000000000),(421074682905338417/1000000000000000000),(214718144379736863/1000000000000000000),(158878379653346537/1000000000000000000)⟩
theorem valid1808 : certificate1808.Valid := by decide +kernel
theorem sound1808 : certificate1808.Sound := rat_cut_bin_certificate_sound certificate1808 profilesValid1808 numericValid1808 valid1808

def retention1809 : RatCutRetentionCertificate := ⟨(263/4000),(527/8000),(1/2),64,1,(3990901203360961013954159587126961751/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch288.profile11542,(fun _ => MergedCutProfiles.Batch288.profile11542)⟩
theorem profilesValid1809 : retention1809.ProfilesValid := by
  exact MergedCutProfiles.Batch288.valid11542
theorem numericValid1809 : retention1809.NumericValid := by decide +kernel
def certificate1809 : RatCutBinCertificate := ⟨⟨retention1809,(30009995404666049/12500000000000000),(57064330308281523/250000000000000000),(8835637598779032713/500000000000000000),(176606313810354852443/1000000000000000000),(193342778176485849/200000000000000000)⟩,(247365066026214591/250000000000000000),(189363017176443299/500000000000000000),(1584689627245693/6250000000000000),(238892599573597271/1000000000000000000)⟩
theorem valid1809 : certificate1809.Valid := by decide +kernel
theorem sound1809 : certificate1809.Sound := rat_cut_bin_certificate_sound certificate1809 profilesValid1809 numericValid1809 valid1809

def retention1810 : RatCutRetentionCertificate := ⟨(263/4000),(527/8000),(4627777617298940137/9986027114144570898),(1478702017317138463/500000000000000000),(5/4),(10086464502038522564234178082077340699/9463692910829686163200000000000000000),false,MergedCutProfiles.Batch288.profile11543,(fun _ => MergedCutProfiles.Batch288.profile11543)⟩
theorem profilesValid1810 : retention1810.ProfilesValid := by
  exact MergedCutProfiles.Batch288.valid11543
theorem numericValid1810 : retention1810.NumericValid := by decide +kernel
def certificate1810 : RatCutBinCertificate := ⟨⟨retention1810,(33906138117166049/12500000000000000),(57064330308281523/250000000000000000),(8835637598779032713/500000000000000000),(176606313810354852443/1000000000000000000),(1021995019979798591/1000000000000000000)⟩,(988087120478718677/1000000000000000000),(372682264225684721/1000000000000000000),(259466482868551661/1000000000000000000),(171382116309940549/1000000000000000000)⟩
theorem valid1810 : certificate1810.Valid := by decide +kernel
theorem sound1810 : certificate1810.Sound := rat_cut_bin_certificate_sound certificate1810 profilesValid1810 numericValid1810 valid1810

def retention1811 : RatCutRetentionCertificate := ⟨(263/4000),(527/8000),(4912479193263107881/9986027114144570898),(4627777617298940137/1000000000000000000),(11/10),(1853291268318933482048076378162378803671/1851111046919576054800000000000000000000),false,MergedCutProfiles.Batch288.profile11544,(fun _ => MergedCutProfiles.Batch288.profile11544)⟩
theorem profilesValid1811 : retention1811.ProfilesValid := by
  exact MergedCutProfiles.Batch288.valid11544
theorem numericValid1811 : retention1811.NumericValid := by decide +kernel
def certificate1811 : RatCutBinCertificate := ⟨⟨retention1811,(33906138117166049/12500000000000000),(57064330308281523/250000000000000000),(8835637598779032713/500000000000000000),(176606313810354852443/1000000000000000000),(481313731430774459/500000000000000000)⟩,(988087120478718677/1000000000000000000),(1582665912901451/4000000000000000),(23747650047108383/100000000000000000),(175015422546711931/1000000000000000000)⟩
theorem valid1811 : certificate1811.Valid := by decide +kernel
theorem sound1811 : certificate1811.Sound := rat_cut_bin_certificate_sound certificate1811 profilesValid1811 numericValid1811 valid1811

def certificates : List RatCutBinCertificate := [certificate1800,certificate1801,certificate1802,certificate1803,certificate1804,certificate1805,certificate1806,certificate1807,certificate1808,certificate1809,certificate1810,certificate1811]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1800,List.forall_mem_cons.mpr ⟨sound1801,List.forall_mem_cons.mpr ⟨sound1802,List.forall_mem_cons.mpr ⟨sound1803,List.forall_mem_cons.mpr ⟨sound1804,List.forall_mem_cons.mpr ⟨sound1805,List.forall_mem_cons.mpr ⟨sound1806,List.forall_mem_cons.mpr ⟨sound1807,List.forall_mem_cons.mpr ⟨sound1808,List.forall_mem_cons.mpr ⟨sound1809,List.forall_mem_cons.mpr ⟨sound1810,List.forall_mem_cons.mpr ⟨sound1811,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch150
