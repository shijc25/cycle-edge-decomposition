import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch005
import Cycle12.MergedCutCells.Batch051
import Cycle12.MergedCutCells.Batch052
import Cycle12.MergedCutCells.Batch053
import Cycle12.MergedCutCells.Batch054
import Cycle12.MergedCutCells.Batch055
import Cycle12.MergedCutCells.Batch056
import Cycle12.PopulationCertificates.Batch005

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch014

def certificate168 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate112,PopulationCertificates.Batch005.certificate112,[MergedCutCells.Batch051.certificate623,MergedCutCells.Batch052.certificate624],(809199731449247527/1000000000000000000),(some (178541921/200000000)),(1/2),(32836824595260677/100000000000000000),(some (284494488801498793/500000000000000000)),(some (256147827412317399/1000000000000000000))⟩
theorem numericValid168 : certificate168.NumericValid := by decide +kernel
theorem cellsSound168 : ∀ c∈certificate168.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch051.certificate623,MergedCutCells.Batch052.certificate624], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.sound623,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.sound624,List.forall_mem_nil _⟩⟩
theorem cellsNumeric168 : ∀ c∈certificate168.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch051.certificate623,MergedCutCells.Batch052.certificate624], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.numericValid623,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.numericValid624,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid168 : ∀ c∈certificate168.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch051.certificate623,MergedCutCells.Batch052.certificate624], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid57,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid57,List.forall_mem_nil _⟩⟩
theorem populationMatches168 : ∀ c∈certificate168.cells, c.population=certificate168.population := by
  change ∀ c∈[MergedCutCells.Batch051.certificate623,MergedCutCells.Batch052.certificate624], c.population=PopulationCertificates.Batch005.certificate112
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers168 {x : ℝ} (hx : certificate168.interval.Contains x) : ∃ c∈certificate168.cells, c.region.interval.Contains x := rat_cut_group_covers certificate168 numericValid168 hx

def certificate169 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate112,PopulationCertificates.Batch005.certificate112,[MergedCutCells.Batch052.certificate625,MergedCutCells.Batch052.certificate626,MergedCutCells.Batch052.certificate627,MergedCutCells.Batch052.certificate628,MergedCutCells.Batch052.certificate629,MergedCutCells.Batch052.certificate630,MergedCutCells.Batch052.certificate631],(178541921/200000000),none,(1/2),(240373920235504517/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid169 : certificate169.NumericValid := by decide +kernel
theorem cellsSound169 : ∀ c∈certificate169.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch052.certificate625,MergedCutCells.Batch052.certificate626,MergedCutCells.Batch052.certificate627,MergedCutCells.Batch052.certificate628,MergedCutCells.Batch052.certificate629,MergedCutCells.Batch052.certificate630,MergedCutCells.Batch052.certificate631], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.sound625,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.sound626,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.sound627,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.sound628,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.sound629,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.sound630,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.sound631,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric169 : ∀ c∈certificate169.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch052.certificate625,MergedCutCells.Batch052.certificate626,MergedCutCells.Batch052.certificate627,MergedCutCells.Batch052.certificate628,MergedCutCells.Batch052.certificate629,MergedCutCells.Batch052.certificate630,MergedCutCells.Batch052.certificate631], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.numericValid625,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.numericValid626,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.numericValid627,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.numericValid628,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.numericValid629,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.numericValid630,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.numericValid631,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid169 : ∀ c∈certificate169.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch052.certificate625,MergedCutCells.Batch052.certificate626,MergedCutCells.Batch052.certificate627,MergedCutCells.Batch052.certificate628,MergedCutCells.Batch052.certificate629,MergedCutCells.Batch052.certificate630,MergedCutCells.Batch052.certificate631], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches169 : ∀ c∈certificate169.cells, c.population=certificate169.population := by
  change ∀ c∈[MergedCutCells.Batch052.certificate625,MergedCutCells.Batch052.certificate626,MergedCutCells.Batch052.certificate627,MergedCutCells.Batch052.certificate628,MergedCutCells.Batch052.certificate629,MergedCutCells.Batch052.certificate630,MergedCutCells.Batch052.certificate631], c.population=PopulationCertificates.Batch005.certificate112
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers169 {x : ℝ} (hx : certificate169.interval.Contains x) : ∃ c∈certificate169.cells, c.region.interval.Contains x := rat_cut_group_covers certificate169 numericValid169 hx

def certificate170 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate113,PopulationCertificates.Batch005.certificate113,[MergedCutCells.Batch052.certificate632,MergedCutCells.Batch052.certificate633,MergedCutCells.Batch052.certificate634,MergedCutCells.Batch052.certificate635],(468203268992639253/125000000000000000),none,(1/2),(73277097873067737/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid170 : certificate170.NumericValid := by decide +kernel
theorem cellsSound170 : ∀ c∈certificate170.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch052.certificate632,MergedCutCells.Batch052.certificate633,MergedCutCells.Batch052.certificate634,MergedCutCells.Batch052.certificate635], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.sound632,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.sound633,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.sound634,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.sound635,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric170 : ∀ c∈certificate170.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch052.certificate632,MergedCutCells.Batch052.certificate633,MergedCutCells.Batch052.certificate634,MergedCutCells.Batch052.certificate635], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.numericValid632,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.numericValid633,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.numericValid634,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch052.numericValid635,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid170 : ∀ c∈certificate170.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch052.certificate632,MergedCutCells.Batch052.certificate633,MergedCutCells.Batch052.certificate634,MergedCutCells.Batch052.certificate635], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches170 : ∀ c∈certificate170.cells, c.population=certificate170.population := by
  change ∀ c∈[MergedCutCells.Batch052.certificate632,MergedCutCells.Batch052.certificate633,MergedCutCells.Batch052.certificate634,MergedCutCells.Batch052.certificate635], c.population=PopulationCertificates.Batch005.certificate113
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers170 {x : ℝ} (hx : certificate170.interval.Contains x) : ∃ c∈certificate170.cells, c.region.interval.Contains x := rat_cut_group_covers certificate170 numericValid170 hx

def certificate171 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate114,PopulationCertificates.Batch005.certificate114,[MergedCutCells.Batch053.certificate636,MergedCutCells.Batch053.certificate637],(404599930538972933/500000000000000000),(some (178541949/200000000)),(1/2),(317015859352170693/1000000000000000000),(some (287838387542961843/500000000000000000)),(some (131260235222638649/500000000000000000))⟩
theorem numericValid171 : certificate171.NumericValid := by decide +kernel
theorem cellsSound171 : ∀ c∈certificate171.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch053.certificate636,MergedCutCells.Batch053.certificate637], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.sound636,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.sound637,List.forall_mem_nil _⟩⟩
theorem cellsNumeric171 : ∀ c∈certificate171.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch053.certificate636,MergedCutCells.Batch053.certificate637], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.numericValid636,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.numericValid637,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid171 : ∀ c∈certificate171.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch053.certificate636,MergedCutCells.Batch053.certificate637], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid58,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid58,List.forall_mem_nil _⟩⟩
theorem populationMatches171 : ∀ c∈certificate171.cells, c.population=certificate171.population := by
  change ∀ c∈[MergedCutCells.Batch053.certificate636,MergedCutCells.Batch053.certificate637], c.population=PopulationCertificates.Batch005.certificate114
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers171 {x : ℝ} (hx : certificate171.interval.Contains x) : ∃ c∈certificate171.cells, c.region.interval.Contains x := rat_cut_group_covers certificate171 numericValid171 hx

def certificate172 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate114,PopulationCertificates.Batch005.certificate114,[MergedCutCells.Batch053.certificate638,MergedCutCells.Batch053.certificate639,MergedCutCells.Batch053.certificate640,MergedCutCells.Batch053.certificate641,MergedCutCells.Batch053.certificate642,MergedCutCells.Batch053.certificate643,MergedCutCells.Batch053.certificate644],(178541949/200000000),none,(1/2),(236240738924926539/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid172 : certificate172.NumericValid := by decide +kernel
theorem cellsSound172 : ∀ c∈certificate172.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch053.certificate638,MergedCutCells.Batch053.certificate639,MergedCutCells.Batch053.certificate640,MergedCutCells.Batch053.certificate641,MergedCutCells.Batch053.certificate642,MergedCutCells.Batch053.certificate643,MergedCutCells.Batch053.certificate644], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.sound638,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.sound639,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.sound640,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.sound641,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.sound642,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.sound643,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.sound644,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric172 : ∀ c∈certificate172.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch053.certificate638,MergedCutCells.Batch053.certificate639,MergedCutCells.Batch053.certificate640,MergedCutCells.Batch053.certificate641,MergedCutCells.Batch053.certificate642,MergedCutCells.Batch053.certificate643,MergedCutCells.Batch053.certificate644], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.numericValid638,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.numericValid639,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.numericValid640,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.numericValid641,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.numericValid642,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.numericValid643,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.numericValid644,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid172 : ∀ c∈certificate172.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch053.certificate638,MergedCutCells.Batch053.certificate639,MergedCutCells.Batch053.certificate640,MergedCutCells.Batch053.certificate641,MergedCutCells.Batch053.certificate642,MergedCutCells.Batch053.certificate643,MergedCutCells.Batch053.certificate644], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches172 : ∀ c∈certificate172.cells, c.population=certificate172.population := by
  change ∀ c∈[MergedCutCells.Batch053.certificate638,MergedCutCells.Batch053.certificate639,MergedCutCells.Batch053.certificate640,MergedCutCells.Batch053.certificate641,MergedCutCells.Batch053.certificate642,MergedCutCells.Batch053.certificate643,MergedCutCells.Batch053.certificate644], c.population=PopulationCertificates.Batch005.certificate114
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers172 {x : ℝ} (hx : certificate172.interval.Contains x) : ∃ c∈certificate172.cells, c.region.interval.Contains x := rat_cut_group_covers certificate172 numericValid172 hx

def certificate173 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate115,PopulationCertificates.Batch005.certificate115,[MergedCutCells.Batch053.certificate645,MergedCutCells.Batch053.certificate646,MergedCutCells.Batch053.certificate647,MergedCutCells.Batch054.certificate648],(1874914729348946183/500000000000000000),none,(1/2),(11677952813497263/20000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid173 : certificate173.NumericValid := by decide +kernel
theorem cellsSound173 : ∀ c∈certificate173.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch053.certificate645,MergedCutCells.Batch053.certificate646,MergedCutCells.Batch053.certificate647,MergedCutCells.Batch054.certificate648], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.sound645,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.sound646,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.sound647,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.sound648,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric173 : ∀ c∈certificate173.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch053.certificate645,MergedCutCells.Batch053.certificate646,MergedCutCells.Batch053.certificate647,MergedCutCells.Batch054.certificate648], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.numericValid645,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.numericValid646,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch053.numericValid647,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.numericValid648,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid173 : ∀ c∈certificate173.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch053.certificate645,MergedCutCells.Batch053.certificate646,MergedCutCells.Batch053.certificate647,MergedCutCells.Batch054.certificate648], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches173 : ∀ c∈certificate173.cells, c.population=certificate173.population := by
  change ∀ c∈[MergedCutCells.Batch053.certificate645,MergedCutCells.Batch053.certificate646,MergedCutCells.Batch053.certificate647,MergedCutCells.Batch054.certificate648], c.population=PopulationCertificates.Batch005.certificate115
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers173 {x : ℝ} (hx : certificate173.interval.Contains x) : ∃ c∈certificate173.cells, c.region.interval.Contains x := rat_cut_group_covers certificate173 numericValid173 hx

def certificate174 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate116,PopulationCertificates.Batch005.certificate116,[MergedCutCells.Batch054.certificate649,MergedCutCells.Batch054.certificate650],(810448339736521217/1000000000000000000),(some (447276079/500000000)),(1/2),(82048698406038861/250000000000000000),(some (23155055901035667/40000000000000000)),(some (10625698352646607/40000000000000000))⟩
theorem numericValid174 : certificate174.NumericValid := by decide +kernel
theorem cellsSound174 : ∀ c∈certificate174.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch054.certificate649,MergedCutCells.Batch054.certificate650], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.sound649,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.sound650,List.forall_mem_nil _⟩⟩
theorem cellsNumeric174 : ∀ c∈certificate174.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch054.certificate649,MergedCutCells.Batch054.certificate650], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.numericValid649,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.numericValid650,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid174 : ∀ c∈certificate174.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch054.certificate649,MergedCutCells.Batch054.certificate650], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid59,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid59,List.forall_mem_nil _⟩⟩
theorem populationMatches174 : ∀ c∈certificate174.cells, c.population=certificate174.population := by
  change ∀ c∈[MergedCutCells.Batch054.certificate649,MergedCutCells.Batch054.certificate650], c.population=PopulationCertificates.Batch005.certificate116
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers174 {x : ℝ} (hx : certificate174.interval.Contains x) : ∃ c∈certificate174.cells, c.region.interval.Contains x := rat_cut_group_covers certificate174 numericValid174 hx

def certificate175 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate116,PopulationCertificates.Batch005.certificate116,[MergedCutCells.Batch054.certificate651,MergedCutCells.Batch054.certificate652,MergedCutCells.Batch054.certificate653,MergedCutCells.Batch054.certificate654,MergedCutCells.Batch054.certificate655,MergedCutCells.Batch054.certificate656,MergedCutCells.Batch054.certificate657],(447276079/500000000),none,(1/2),(50498848970996309/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid175 : certificate175.NumericValid := by decide +kernel
theorem cellsSound175 : ∀ c∈certificate175.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch054.certificate651,MergedCutCells.Batch054.certificate652,MergedCutCells.Batch054.certificate653,MergedCutCells.Batch054.certificate654,MergedCutCells.Batch054.certificate655,MergedCutCells.Batch054.certificate656,MergedCutCells.Batch054.certificate657], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.sound651,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.sound652,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.sound653,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.sound654,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.sound655,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.sound656,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.sound657,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric175 : ∀ c∈certificate175.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch054.certificate651,MergedCutCells.Batch054.certificate652,MergedCutCells.Batch054.certificate653,MergedCutCells.Batch054.certificate654,MergedCutCells.Batch054.certificate655,MergedCutCells.Batch054.certificate656,MergedCutCells.Batch054.certificate657], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.numericValid651,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.numericValid652,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.numericValid653,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.numericValid654,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.numericValid655,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.numericValid656,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.numericValid657,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid175 : ∀ c∈certificate175.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch054.certificate651,MergedCutCells.Batch054.certificate652,MergedCutCells.Batch054.certificate653,MergedCutCells.Batch054.certificate654,MergedCutCells.Batch054.certificate655,MergedCutCells.Batch054.certificate656,MergedCutCells.Batch054.certificate657], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches175 : ∀ c∈certificate175.cells, c.population=certificate175.population := by
  change ∀ c∈[MergedCutCells.Batch054.certificate651,MergedCutCells.Batch054.certificate652,MergedCutCells.Batch054.certificate653,MergedCutCells.Batch054.certificate654,MergedCutCells.Batch054.certificate655,MergedCutCells.Batch054.certificate656,MergedCutCells.Batch054.certificate657], c.population=PopulationCertificates.Batch005.certificate116
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers175 {x : ℝ} (hx : certificate175.interval.Contains x) : ∃ c∈certificate175.cells, c.region.interval.Contains x := rat_cut_group_covers certificate175 numericValid175 hx

def certificate176 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate117,PopulationCertificates.Batch005.certificate117,[MergedCutCells.Batch054.certificate658,MergedCutCells.Batch054.certificate659,MergedCutCells.Batch055.certificate660],(29445848941629431/7812500000000000),none,(1/2),(626553819724481891/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid176 : certificate176.NumericValid := by decide +kernel
theorem cellsSound176 : ∀ c∈certificate176.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch054.certificate658,MergedCutCells.Batch054.certificate659,MergedCutCells.Batch055.certificate660], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.sound658,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.sound659,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.sound660,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric176 : ∀ c∈certificate176.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch054.certificate658,MergedCutCells.Batch054.certificate659,MergedCutCells.Batch055.certificate660], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.numericValid658,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch054.numericValid659,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.numericValid660,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid176 : ∀ c∈certificate176.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch054.certificate658,MergedCutCells.Batch054.certificate659,MergedCutCells.Batch055.certificate660], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches176 : ∀ c∈certificate176.cells, c.population=certificate176.population := by
  change ∀ c∈[MergedCutCells.Batch054.certificate658,MergedCutCells.Batch054.certificate659,MergedCutCells.Batch055.certificate660], c.population=PopulationCertificates.Batch005.certificate117
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers176 {x : ℝ} (hx : certificate176.interval.Contains x) : ∃ c∈certificate176.cells, c.region.interval.Contains x := rat_cut_group_covers certificate176 numericValid176 hx

def certificate177 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate118,PopulationCertificates.Batch005.certificate118,[MergedCutCells.Batch055.certificate661,MergedCutCells.Batch055.certificate662],(817784392546406683/1000000000000000000),(some (220126711/250000000)),(1/2),(22552919157010279/62500000000000000),(some (579818127777700061/1000000000000000000)),(some (66642689790204293/250000000000000000))⟩
theorem numericValid177 : certificate177.NumericValid := by decide +kernel
theorem cellsSound177 : ∀ c∈certificate177.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch055.certificate661,MergedCutCells.Batch055.certificate662], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.sound661,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.sound662,List.forall_mem_nil _⟩⟩
theorem cellsNumeric177 : ∀ c∈certificate177.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch055.certificate661,MergedCutCells.Batch055.certificate662], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.numericValid661,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.numericValid662,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid177 : ∀ c∈certificate177.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch055.certificate661,MergedCutCells.Batch055.certificate662], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid60,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid60,List.forall_mem_nil _⟩⟩
theorem populationMatches177 : ∀ c∈certificate177.cells, c.population=certificate177.population := by
  change ∀ c∈[MergedCutCells.Batch055.certificate661,MergedCutCells.Batch055.certificate662], c.population=PopulationCertificates.Batch005.certificate118
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers177 {x : ℝ} (hx : certificate177.interval.Contains x) : ∃ c∈certificate177.cells, c.region.interval.Contains x := rat_cut_group_covers certificate177 numericValid177 hx

def certificate178 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate118,PopulationCertificates.Batch005.certificate118,[MergedCutCells.Batch055.certificate663,MergedCutCells.Batch055.certificate664,MergedCutCells.Batch055.certificate665,MergedCutCells.Batch055.certificate666,MergedCutCells.Batch055.certificate667,MergedCutCells.Batch055.certificate668,MergedCutCells.Batch055.certificate669],(220126711/250000000),none,(1/2),(126676612866801279/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid178 : certificate178.NumericValid := by decide +kernel
theorem cellsSound178 : ∀ c∈certificate178.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch055.certificate663,MergedCutCells.Batch055.certificate664,MergedCutCells.Batch055.certificate665,MergedCutCells.Batch055.certificate666,MergedCutCells.Batch055.certificate667,MergedCutCells.Batch055.certificate668,MergedCutCells.Batch055.certificate669], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.sound663,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.sound664,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.sound665,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.sound666,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.sound667,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.sound668,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.sound669,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric178 : ∀ c∈certificate178.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch055.certificate663,MergedCutCells.Batch055.certificate664,MergedCutCells.Batch055.certificate665,MergedCutCells.Batch055.certificate666,MergedCutCells.Batch055.certificate667,MergedCutCells.Batch055.certificate668,MergedCutCells.Batch055.certificate669], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.numericValid663,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.numericValid664,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.numericValid665,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.numericValid666,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.numericValid667,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.numericValid668,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.numericValid669,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid178 : ∀ c∈certificate178.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch055.certificate663,MergedCutCells.Batch055.certificate664,MergedCutCells.Batch055.certificate665,MergedCutCells.Batch055.certificate666,MergedCutCells.Batch055.certificate667,MergedCutCells.Batch055.certificate668,MergedCutCells.Batch055.certificate669], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches178 : ∀ c∈certificate178.cells, c.population=certificate178.population := by
  change ∀ c∈[MergedCutCells.Batch055.certificate663,MergedCutCells.Batch055.certificate664,MergedCutCells.Batch055.certificate665,MergedCutCells.Batch055.certificate666,MergedCutCells.Batch055.certificate667,MergedCutCells.Batch055.certificate668,MergedCutCells.Batch055.certificate669], c.population=PopulationCertificates.Batch005.certificate118
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers178 {x : ℝ} (hx : certificate178.interval.Contains x) : ∃ c∈certificate178.cells, c.region.interval.Contains x := rat_cut_group_covers certificate178 numericValid178 hx

def certificate179 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate119,PopulationCertificates.Batch005.certificate119,[MergedCutCells.Batch055.certificate670,MergedCutCells.Batch055.certificate671,MergedCutCells.Batch056.certificate672,MergedCutCells.Batch056.certificate673],(1888509322327770433/500000000000000000),none,(1/2),(128161009840089301/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid179 : certificate179.NumericValid := by decide +kernel
theorem cellsSound179 : ∀ c∈certificate179.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch055.certificate670,MergedCutCells.Batch055.certificate671,MergedCutCells.Batch056.certificate672,MergedCutCells.Batch056.certificate673], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.sound670,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.sound671,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.sound672,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.sound673,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric179 : ∀ c∈certificate179.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch055.certificate670,MergedCutCells.Batch055.certificate671,MergedCutCells.Batch056.certificate672,MergedCutCells.Batch056.certificate673], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.numericValid670,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch055.numericValid671,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.numericValid672,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.numericValid673,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid179 : ∀ c∈certificate179.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch055.certificate670,MergedCutCells.Batch055.certificate671,MergedCutCells.Batch056.certificate672,MergedCutCells.Batch056.certificate673], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches179 : ∀ c∈certificate179.cells, c.population=certificate179.population := by
  change ∀ c∈[MergedCutCells.Batch055.certificate670,MergedCutCells.Batch055.certificate671,MergedCutCells.Batch056.certificate672,MergedCutCells.Batch056.certificate673], c.population=PopulationCertificates.Batch005.certificate119
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers179 {x : ℝ} (hx : certificate179.interval.Contains x) : ∃ c∈certificate179.cells, c.region.interval.Contains x := rat_cut_group_covers certificate179 numericValid179 hx

end Cycle12.MergedCutGroups.Batch014
