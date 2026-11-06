import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch223
import Cycle12.MergedCutProfiles.Batch224
import Cycle12.MergedCutProfiles.Batch225

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch114

def retention1368 : RatCutRetentionCertificate := ⟨(119/2000),(239/4000),(1041986413332785261/2101821367760234893),(6007970774585725039/1000000000000000000),(11/10),(2410742066868683506219640154666333190759/2403188309834290015600000000000000000000),false,MergedCutProfiles.Batch223.profile8928,(fun _ => MergedCutProfiles.Batch223.profile8928)⟩
theorem profilesValid1368 : retention1368.ProfilesValid := by
  exact MergedCutProfiles.Batch223.valid8928
theorem numericValid1368 : retention1368.NumericValid := by decide +kernel
def certificate1368 : RatCutBinCertificate := ⟨⟨retention1368,(2309520674254567439/1000000000000000000),(90319036891105957/500000000000000000),(7858748083479551897/500000000000000000),(3970296207259030741/20000000000000000),(973942052420788909/1000000000000000000)⟩,(990426110264388983/1000000000000000000),(55938379530385653/125000000000000000),(4816720076519631/25000000000000000),(18609450977140363/125000000000000000)⟩
theorem valid1368 : certificate1368.Valid := by decide +kernel
theorem sound1368 : certificate1368.Sound := rat_cut_bin_certificate_sound certificate1368 profilesValid1368 numericValid1368 valid1368

def retention1369 : RatCutRetentionCertificate := ⟨(119/2000),(239/4000),(1/2),(3125959239998355783/500000000000000000),(21/20),(819101956384604510814329775180804466077/833589130666228208800000000000000000000),false,MergedCutProfiles.Batch223.profile8929,(fun _ => MergedCutProfiles.Batch223.profile8929)⟩
theorem profilesValid1369 : retention1369.ProfilesValid := by
  exact MergedCutProfiles.Batch223.valid8929
theorem numericValid1369 : retention1369.NumericValid := by decide +kernel
def certificate1369 : RatCutBinCertificate := ⟨⟨retention1369,(2309520674254567439/1000000000000000000),(90319036891105957/500000000000000000),(7858748083479551897/500000000000000000),(3970296207259030741/20000000000000000),(190949370986071627/200000000000000000)⟩,(990426110264388983/1000000000000000000),(227489889167599657/500000000000000000),(186722360953390839/1000000000000000000),(9223810718152497/62500000000000000)⟩
theorem valid1369 : certificate1369.Valid := by decide +kernel
theorem sound1369 : certificate1369.Sound := rat_cut_bin_certificate_sound certificate1369 profilesValid1369 numericValid1369 valid1369

def retention1370 : RatCutRetentionCertificate := ⟨(119/2000),(239/4000),(1/2),64,1,(255407462780207600768163919548987552831/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch223.profile8929,(fun _ => MergedCutProfiles.Batch223.profile8929)⟩
theorem profilesValid1370 : retention1370.ProfilesValid := by
  exact MergedCutProfiles.Batch223.valid8929
theorem numericValid1370 : retention1370.NumericValid := by decide +kernel
def certificate1370 : RatCutBinCertificate := ⟨⟨retention1370,(2309520674254567439/1000000000000000000),(90319036891105957/500000000000000000),(7858748083479551897/500000000000000000),(3970296207259030741/20000000000000000),(485571079961930969/500000000000000000)⟩,(990426110264388983/1000000000000000000),(41399500598110221/100000000000000000),(6903167373653511/31250000000000000),(209277561043936577/1000000000000000000)⟩
theorem valid1370 : certificate1370.Valid := by decide +kernel
theorem sound1370 : certificate1370.Sound := rat_cut_bin_certificate_sound certificate1370 profilesValid1370 numericValid1370 valid1370

def retention1371 : RatCutRetentionCertificate := ⟨(119/2000),(239/4000),(2941866409427830082/6305464103280704679),(3507046356201153171/1000000000000000000),(6/5),(46437702595005383286716258831233143733/43838079452514414637500000000000000000),false,MergedCutProfiles.Batch223.profile8930,(fun _ => MergedCutProfiles.Batch223.profile8930)⟩
theorem profilesValid1371 : retention1371.ProfilesValid := by
  exact MergedCutProfiles.Batch223.valid8930
theorem numericValid1371 : retention1371.NumericValid := by decide +kernel
def certificate1371 : RatCutBinCertificate := ⟨⟨retention1371,(2640077180254567439/1000000000000000000),(90319036891105957/500000000000000000),(7858748083479551897/500000000000000000),(3970296207259030741/20000000000000000),(1022882436759832721/1000000000000000000)⟩,(494526277495059977/500000000000000000),(98684870048384573/250000000000000000),(119168520662371953/500000000000000000),(8344670155058731/50000000000000000)⟩
theorem valid1371 : certificate1371.Valid := by decide +kernel
theorem sound1371 : certificate1371.Sound := rat_cut_bin_certificate_sound certificate1371 profilesValid1371 numericValid1371 valid1371

def retention1372 : RatCutRetentionCertificate := ⟨(119/2000),(239/4000),(6245700947967706633/12610928206561409358),(1470933204713915041/250000000000000000),(21/20),(582057166520415748233363606886702139159/588373281885566016400000000000000000000),false,MergedCutProfiles.Batch223.profile8931,(fun _ => MergedCutProfiles.Batch223.profile8931)⟩
theorem profilesValid1372 : retention1372.ProfilesValid := by
  exact MergedCutProfiles.Batch223.valid8931
theorem numericValid1372 : retention1372.NumericValid := by decide +kernel
def certificate1372 : RatCutBinCertificate := ⟨⟨retention1372,(2640077180254567439/1000000000000000000),(90319036891105957/500000000000000000),(7858748083479551897/500000000000000000),(3970296207259030741/20000000000000000),(23935036265111087/25000000000000000)⟩,(494526277495059977/500000000000000000),(421737486537919593/1000000000000000000),(107072695719639431/500000000000000000),(84071314077865407/500000000000000000)⟩
theorem valid1372 : certificate1372.Valid := by decide +kernel
theorem sound1372 : certificate1372.Sound := rat_cut_bin_certificate_sound certificate1372 profilesValid1372 numericValid1372 valid1372

def retention1373 : RatCutRetentionCertificate := ⟨(119/2000),(239/4000),(1/2),(6245700947967706633/1000000000000000000),(21/20),(9819088070864424399190702542338893630151/9993121516748330612800000000000000000000),false,MergedCutProfiles.Batch223.profile8929,(fun _ => MergedCutProfiles.Batch223.profile8929)⟩
theorem profilesValid1373 : retention1373.ProfilesValid := by
  exact MergedCutProfiles.Batch223.valid8929
theorem numericValid1373 : retention1373.NumericValid := by decide +kernel
def certificate1373 : RatCutBinCertificate := ⟨⟨retention1373,(2640077180254567439/1000000000000000000),(90319036891105957/500000000000000000),(7858748083479551897/500000000000000000),(3970296207259030741/20000000000000000),(118840159601280251/125000000000000000)⟩,(494526277495059977/500000000000000000),(424700794264717547/1000000000000000000),(211597401350025413/1000000000000000000),(41592610914729197/250000000000000000)⟩
theorem valid1373 : certificate1373.Valid := by decide +kernel
theorem sound1373 : certificate1373.Sound := rat_cut_bin_certificate_sound certificate1373 profilesValid1373 numericValid1373 valid1373

def retention1374 : RatCutRetentionCertificate := ⟨(239/4000),(3/50),(893532594393400169/12486961035491489733),(850165604323558663/1000000000000000000),(11/4),(507534982377671749547/256000000000000000000),true,MergedCutProfiles.Batch223.profile8932,![MergedCutProfiles.Batch223.profile8932,MergedCutProfiles.Batch223.profile8933,MergedCutProfiles.Batch223.profile8934,MergedCutProfiles.Batch223.profile8935,MergedCutProfiles.Batch223.profile8936,MergedCutProfiles.Batch223.profile8937,MergedCutProfiles.Batch223.profile8938,MergedCutProfiles.Batch223.profile8939,MergedCutProfiles.Batch223.profile8940,MergedCutProfiles.Batch223.profile8941,MergedCutProfiles.Batch223.profile8942,MergedCutProfiles.Batch223.profile8943,MergedCutProfiles.Batch223.profile8944,MergedCutProfiles.Batch223.profile8945,MergedCutProfiles.Batch223.profile8946,MergedCutProfiles.Batch223.profile8947]⟩
theorem profilesValid1374 : retention1374.ProfilesValid := by
  change ∀ j : Fin 16, (retention1374.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch223.valid8932
  · exact MergedCutProfiles.Batch223.valid8933
  · exact MergedCutProfiles.Batch223.valid8934
  · exact MergedCutProfiles.Batch223.valid8935
  · exact MergedCutProfiles.Batch223.valid8936
  · exact MergedCutProfiles.Batch223.valid8937
  · exact MergedCutProfiles.Batch223.valid8938
  · exact MergedCutProfiles.Batch223.valid8939
  · exact MergedCutProfiles.Batch223.valid8940
  · exact MergedCutProfiles.Batch223.valid8941
  · exact MergedCutProfiles.Batch223.valid8942
  · exact MergedCutProfiles.Batch223.valid8943
  · exact MergedCutProfiles.Batch223.valid8944
  · exact MergedCutProfiles.Batch223.valid8945
  · exact MergedCutProfiles.Batch223.valid8946
  · exact MergedCutProfiles.Batch223.valid8947
theorem numericValid1374 : retention1374.NumericValid := by decide +kernel
def certificate1374 : RatCutBinCertificate := ⟨⟨retention1374,(1164008638755611433/500000000000000000),(182428996879551849/1000000000000000000),(3947309366890257321/250000000000000000),(197461089196585477267/1000000000000000000),(954279989171274779/500000000000000000)⟩,(9903184537773961/10000000000000000),(175112177656777689/500000000000000000),(141160510002721961/500000000000000000),(29865344338299723/200000000000000000)⟩
theorem valid1374 : certificate1374.Valid := by decide +kernel
theorem sound1374 : certificate1374.Sound := rat_cut_bin_certificate_sound certificate1374 profilesValid1374 numericValid1374 valid1374

def retention1375 : RatCutRetentionCertificate := ⟨(239/4000),(3/50),(389642424290811316/4162320345163829911),(893532594393400169/1000000000000000000),(13/5),(2452374838787409511781/1280000000000000000000),true,MergedCutProfiles.Batch223.profile8948,![MergedCutProfiles.Batch223.profile8948,MergedCutProfiles.Batch223.profile8949,MergedCutProfiles.Batch223.profile8950,MergedCutProfiles.Batch223.profile8951,MergedCutProfiles.Batch223.profile8952,MergedCutProfiles.Batch223.profile8953,MergedCutProfiles.Batch223.profile8954,MergedCutProfiles.Batch223.profile8955,MergedCutProfiles.Batch223.profile8956,MergedCutProfiles.Batch223.profile8957,MergedCutProfiles.Batch223.profile8958,MergedCutProfiles.Batch223.profile8959,MergedCutProfiles.Batch224.profile8960,MergedCutProfiles.Batch224.profile8961,MergedCutProfiles.Batch224.profile8962,MergedCutProfiles.Batch224.profile8963]⟩
theorem profilesValid1375 : retention1375.ProfilesValid := by
  change ∀ j : Fin 16, (retention1375.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch223.valid8948
  · exact MergedCutProfiles.Batch223.valid8949
  · exact MergedCutProfiles.Batch223.valid8950
  · exact MergedCutProfiles.Batch223.valid8951
  · exact MergedCutProfiles.Batch223.valid8952
  · exact MergedCutProfiles.Batch223.valid8953
  · exact MergedCutProfiles.Batch223.valid8954
  · exact MergedCutProfiles.Batch223.valid8955
  · exact MergedCutProfiles.Batch223.valid8956
  · exact MergedCutProfiles.Batch223.valid8957
  · exact MergedCutProfiles.Batch223.valid8958
  · exact MergedCutProfiles.Batch223.valid8959
  · exact MergedCutProfiles.Batch224.valid8960
  · exact MergedCutProfiles.Batch224.valid8961
  · exact MergedCutProfiles.Batch224.valid8962
  · exact MergedCutProfiles.Batch224.valid8963
theorem numericValid1375 : retention1375.NumericValid := by decide +kernel
def certificate1375 : RatCutBinCertificate := ⟨⟨retention1375,(1164008638755611433/500000000000000000),(182428996879551849/1000000000000000000),(3947309366890257321/250000000000000000),(197461089196585477267/1000000000000000000),(115372212805347849/62500000000000000)⟩,(9903184537773961/10000000000000000),(88721646375179933/250000000000000000),(277461107418101407/1000000000000000000),(74562174136991241/500000000000000000)⟩
theorem valid1375 : certificate1375.Valid := by decide +kernel
theorem sound1375 : certificate1375.Sound := rat_cut_bin_certificate_sound certificate1375 profilesValid1375 numericValid1375 valid1375

def retention1376 : RatCutRetentionCertificate := ⟨(239/4000),(3/50),(2416839318354164036/12486961035491489733),(292231818218108487/250000000000000000),(41/20),(526470330116898038043/320000000000000000000),true,MergedCutProfiles.Batch224.profile8964,![MergedCutProfiles.Batch224.profile8964,MergedCutProfiles.Batch224.profile8965,MergedCutProfiles.Batch224.profile8966,MergedCutProfiles.Batch224.profile8967,MergedCutProfiles.Batch224.profile8968,MergedCutProfiles.Batch224.profile8969,MergedCutProfiles.Batch224.profile8970,MergedCutProfiles.Batch224.profile8971,MergedCutProfiles.Batch224.profile8972,MergedCutProfiles.Batch224.profile8973,MergedCutProfiles.Batch224.profile8974,MergedCutProfiles.Batch224.profile8975,MergedCutProfiles.Batch224.profile8976,MergedCutProfiles.Batch224.profile8977,MergedCutProfiles.Batch224.profile8978,MergedCutProfiles.Batch224.profile8979]⟩
theorem profilesValid1376 : retention1376.ProfilesValid := by
  change ∀ j : Fin 16, (retention1376.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch224.valid8964
  · exact MergedCutProfiles.Batch224.valid8965
  · exact MergedCutProfiles.Batch224.valid8966
  · exact MergedCutProfiles.Batch224.valid8967
  · exact MergedCutProfiles.Batch224.valid8968
  · exact MergedCutProfiles.Batch224.valid8969
  · exact MergedCutProfiles.Batch224.valid8970
  · exact MergedCutProfiles.Batch224.valid8971
  · exact MergedCutProfiles.Batch224.valid8972
  · exact MergedCutProfiles.Batch224.valid8973
  · exact MergedCutProfiles.Batch224.valid8974
  · exact MergedCutProfiles.Batch224.valid8975
  · exact MergedCutProfiles.Batch224.valid8976
  · exact MergedCutProfiles.Batch224.valid8977
  · exact MergedCutProfiles.Batch224.valid8978
  · exact MergedCutProfiles.Batch224.valid8979
theorem numericValid1376 : retention1376.NumericValid := by decide +kernel
def certificate1376 : RatCutBinCertificate := ⟨⟨retention1376,(1164008638755611433/500000000000000000),(182428996879551849/1000000000000000000),(3947309366890257321/250000000000000000),(197461089196585477267/1000000000000000000),(159005775925353147/100000000000000000)⟩,(9903184537773961/10000000000000000),(18665600494229263/50000000000000000),(258845492507539437/1000000000000000000),(149921937926245859/1000000000000000000)⟩
theorem valid1376 : certificate1376.Valid := by decide +kernel
theorem sound1376 : certificate1376.Sound := rat_cut_bin_certificate_sound certificate1376 profilesValid1376 numericValid1376 valid1376

def retention1377 : RatCutRetentionCertificate := ⟨(239/4000),(3/50),(1616674870456935130/4162320345163829911),(604209829588541009/250000000000000000),(5/4),(15348940447251318701/12800000000000000000),true,MergedCutProfiles.Batch224.profile8980,![MergedCutProfiles.Batch224.profile8980,MergedCutProfiles.Batch224.profile8981,MergedCutProfiles.Batch224.profile8982,MergedCutProfiles.Batch224.profile8983,MergedCutProfiles.Batch224.profile8984,MergedCutProfiles.Batch224.profile8985,MergedCutProfiles.Batch224.profile8986,MergedCutProfiles.Batch224.profile8987,MergedCutProfiles.Batch224.profile8988,MergedCutProfiles.Batch224.profile8989,MergedCutProfiles.Batch224.profile8990,MergedCutProfiles.Batch224.profile8991,MergedCutProfiles.Batch224.profile8992,MergedCutProfiles.Batch224.profile8993,MergedCutProfiles.Batch224.profile8994,MergedCutProfiles.Batch224.profile8995]⟩
theorem profilesValid1377 : retention1377.ProfilesValid := by
  change ∀ j : Fin 16, (retention1377.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch224.valid8980
  · exact MergedCutProfiles.Batch224.valid8981
  · exact MergedCutProfiles.Batch224.valid8982
  · exact MergedCutProfiles.Batch224.valid8983
  · exact MergedCutProfiles.Batch224.valid8984
  · exact MergedCutProfiles.Batch224.valid8985
  · exact MergedCutProfiles.Batch224.valid8986
  · exact MergedCutProfiles.Batch224.valid8987
  · exact MergedCutProfiles.Batch224.valid8988
  · exact MergedCutProfiles.Batch224.valid8989
  · exact MergedCutProfiles.Batch224.valid8990
  · exact MergedCutProfiles.Batch224.valid8991
  · exact MergedCutProfiles.Batch224.valid8992
  · exact MergedCutProfiles.Batch224.valid8993
  · exact MergedCutProfiles.Batch224.valid8994
  · exact MergedCutProfiles.Batch224.valid8995
theorem numericValid1377 : retention1377.NumericValid := by decide +kernel
def certificate1377 : RatCutBinCertificate := ⟨⟨retention1377,(1164008638755611433/500000000000000000),(182428996879551849/1000000000000000000),(3947309366890257321/250000000000000000),(197461089196585477267/1000000000000000000),(582751636823071491/500000000000000000)⟩,(9903184537773961/10000000000000000),(420872551078031507/1000000000000000000),(42978604275473459/200000000000000000),(37849424380222313/250000000000000000)⟩
theorem valid1377 : certificate1377.Valid := by decide +kernel
theorem sound1377 : certificate1377.Sound := rat_cut_bin_certificate_sound certificate1377 profilesValid1377 numericValid1377 valid1377

def retention1378 : RatCutRetentionCertificate := ⟨(239/4000),(3/50),(5977131241540136968/12486961035491489733),(485002461137080539/100000000000000000),1,(25549893383392090203/25600000000000000000),true,MergedCutProfiles.Batch224.profile8996,![MergedCutProfiles.Batch224.profile8996,MergedCutProfiles.Batch224.profile8997,MergedCutProfiles.Batch224.profile8998,MergedCutProfiles.Batch224.profile8999,MergedCutProfiles.Batch225.profile9000,MergedCutProfiles.Batch225.profile9001,MergedCutProfiles.Batch225.profile9002,MergedCutProfiles.Batch225.profile9003,MergedCutProfiles.Batch225.profile9004,MergedCutProfiles.Batch225.profile9005,MergedCutProfiles.Batch225.profile9006,MergedCutProfiles.Batch225.profile9007,MergedCutProfiles.Batch225.profile9008,MergedCutProfiles.Batch225.profile9009,MergedCutProfiles.Batch225.profile9010,MergedCutProfiles.Batch225.profile9011]⟩
theorem profilesValid1378 : retention1378.ProfilesValid := by
  change ∀ j : Fin 16, (retention1378.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch224.valid8996
  · exact MergedCutProfiles.Batch224.valid8997
  · exact MergedCutProfiles.Batch224.valid8998
  · exact MergedCutProfiles.Batch224.valid8999
  · exact MergedCutProfiles.Batch225.valid9000
  · exact MergedCutProfiles.Batch225.valid9001
  · exact MergedCutProfiles.Batch225.valid9002
  · exact MergedCutProfiles.Batch225.valid9003
  · exact MergedCutProfiles.Batch225.valid9004
  · exact MergedCutProfiles.Batch225.valid9005
  · exact MergedCutProfiles.Batch225.valid9006
  · exact MergedCutProfiles.Batch225.valid9007
  · exact MergedCutProfiles.Batch225.valid9008
  · exact MergedCutProfiles.Batch225.valid9009
  · exact MergedCutProfiles.Batch225.valid9010
  · exact MergedCutProfiles.Batch225.valid9011
theorem numericValid1378 : retention1378.NumericValid := by decide +kernel
def certificate1378 : RatCutBinCertificate := ⟨⟨retention1378,(1164008638755611433/500000000000000000),(182428996879551849/1000000000000000000),(3947309366890257321/250000000000000000),(197461089196585477267/1000000000000000000),(971139653221084837/1000000000000000000)⟩,(9903184537773961/10000000000000000),(113808938503436461/250000000000000000),(93260426750277833/500000000000000000),(149302756990183511/1000000000000000000)⟩
theorem valid1378 : certificate1378.Valid := by decide +kernel
theorem sound1378 : certificate1378.Sound := rat_cut_bin_certificate_sound certificate1378 profilesValid1378 numericValid1378 valid1378

def retention1379 : RatCutRetentionCertificate := ⟨(239/4000),(3/50),(6158244295290044660/12486961035491489733),(747141405192517121/125000000000000000),(11/10),(602494563969037035843558647047193603839/597713124154013696800000000000000000000),false,MergedCutProfiles.Batch225.profile9012,(fun _ => MergedCutProfiles.Batch225.profile9012)⟩
theorem profilesValid1379 : retention1379.ProfilesValid := by
  exact MergedCutProfiles.Batch225.valid9012
theorem numericValid1379 : retention1379.NumericValid := by decide +kernel
def certificate1379 : RatCutBinCertificate := ⟨⟨retention1379,(1164008638755611433/500000000000000000),(182428996879551849/1000000000000000000),(3947309366890257321/250000000000000000),(197461089196585477267/1000000000000000000),(978407672128476597/1000000000000000000)⟩,(9903184537773961/10000000000000000),(221291318916541193/500000000000000000),(196655471460164501/1000000000000000000),(15245896673756359/100000000000000000)⟩
theorem valid1379 : certificate1379.Valid := by decide +kernel
theorem sound1379 : certificate1379.Sound := rat_cut_bin_certificate_sound certificate1379 profilesValid1379 numericValid1379 valid1379

def certificates : List RatCutBinCertificate := [certificate1368,certificate1369,certificate1370,certificate1371,certificate1372,certificate1373,certificate1374,certificate1375,certificate1376,certificate1377,certificate1378,certificate1379]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1368,List.forall_mem_cons.mpr ⟨sound1369,List.forall_mem_cons.mpr ⟨sound1370,List.forall_mem_cons.mpr ⟨sound1371,List.forall_mem_cons.mpr ⟨sound1372,List.forall_mem_cons.mpr ⟨sound1373,List.forall_mem_cons.mpr ⟨sound1374,List.forall_mem_cons.mpr ⟨sound1375,List.forall_mem_cons.mpr ⟨sound1376,List.forall_mem_cons.mpr ⟨sound1377,List.forall_mem_cons.mpr ⟨sound1378,List.forall_mem_cons.mpr ⟨sound1379,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch114
