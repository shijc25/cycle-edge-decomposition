import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch068
import Cycle12.MergedCutProfiles.Batch069
import Cycle12.MergedCutProfiles.Batch070

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch034

def retention408 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(19324248317199379096/39735965222884822823),(13777673887245052739/1000000000000000000),(21/20),(22636124901271415814835750170087727116479/22044278219592084382400000000000000000000),false,MergedCutProfiles.Batch068.profile2735,(fun _ => MergedCutProfiles.Batch068.profile2735)⟩
theorem profilesValid408 : retention408.ProfilesValid := by
  exact MergedCutProfiles.Batch068.valid2735
theorem numericValid408 : retention408.NumericValid := by decide +kernel
def certificate408 : RatCutBinCertificate := ⟨⟨retention408,(2041151659260645091/1000000000000000000),(3628243259175483/62500000000000000),(663008666071467203/62500000000000000),(211315119221540813759/500000000000000000),(1015119493916759271/1000000000000000000)⟩,(248860287188808163/250000000000000000),(119421625459118887/250000000000000000),(42349576517390869/250000000000000000),(152787246674965479/1000000000000000000)⟩
theorem valid408 : certificate408.Valid := by decide +kernel
theorem sound408 : certificate408.Sound := rat_cut_bin_certificate_sound certificate408 profilesValid408 numericValid408 valid408

def retention409 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(19712665708375086616/39735965222884822823),(2415531039649922387/125000000000000000),1,(76999429345806956140702922185183584423/77296993268797516384000000000000000000),false,MergedCutProfiles.Batch068.profile2736,(fun _ => MergedCutProfiles.Batch068.profile2736)⟩
theorem profilesValid409 : retention409.ProfilesValid := by
  exact MergedCutProfiles.Batch068.valid2736
theorem numericValid409 : retention409.NumericValid := by decide +kernel
def certificate409 : RatCutBinCertificate := ⟨⟨retention409,(2041151659260645091/1000000000000000000),(3628243259175483/62500000000000000),(663008666071467203/62500000000000000),(211315119221540813759/500000000000000000),(984980320438489113/1000000000000000000)⟩,(248860287188808163/250000000000000000),(242644917952739087/500000000000000000),(163841176250088491/1000000000000000000),(152834576336049461/1000000000000000000)⟩
theorem valid409 : certificate409.Valid := by decide +kernel
theorem sound409 : certificate409.Sound := rat_cut_bin_certificate_sound certificate409 profilesValid409 numericValid409 valid409

def retention410 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(1/2),(2464083213546885827/125000000000000000),1,(243642984180107489029537295573910503/246408321354688582700000000000000000),false,MergedCutProfiles.Batch068.profile2737,(fun _ => MergedCutProfiles.Batch068.profile2737)⟩
theorem profilesValid410 : retention410.ProfilesValid := by
  exact MergedCutProfiles.Batch068.valid2737
theorem numericValid410 : retention410.NumericValid := by decide +kernel
def certificate410 : RatCutBinCertificate := ⟨⟨retention410,(2041151659260645091/1000000000000000000),(3628243259175483/62500000000000000),(663008666071467203/62500000000000000),(211315119221540813759/500000000000000000),(977607360037462117/1000000000000000000)⟩,(248860287188808163/250000000000000000),(488603964610864027/1000000000000000000),(20182041431029273/125000000000000000),(149679213891966849/1000000000000000000)⟩
theorem valid410 : certificate410.Valid := by decide +kernel
theorem sound410 : certificate410.Sound := rat_cut_bin_certificate_sound certificate410 profilesValid410 numericValid410 valid410

def retention411 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(16938117154206819562/39735965222884822823),(942492059316894563/250000000000000000),(5/4),(17306361095869770806573727674114042911/15079872949070313008000000000000000000),false,MergedCutProfiles.Batch068.profile2738,(fun _ => MergedCutProfiles.Batch068.profile2738)⟩
theorem profilesValid411 : retention411.ProfilesValid := by
  exact MergedCutProfiles.Batch068.valid2738
theorem numericValid411 : retention411.NumericValid := by decide +kernel
def certificate411 : RatCutBinCertificate := ⟨⟨retention411,(2424912444260645091/1000000000000000000),(3628243259175483/62500000000000000),(663008666071467203/62500000000000000),(211315119221540813759/500000000000000000),(1131058273970829151/1000000000000000000)⟩,(124322969177644379/125000000000000000),(175089383461073859/500000000000000000),(141184422996663141/500000000000000000),(213087587153275143/1000000000000000000)⟩
theorem valid411 : certificate411.Valid := by decide +kernel
theorem sound411 : certificate411.Sound := rat_cut_bin_certificate_sound certificate411 profilesValid411 numericValid411 valid411

def retention412 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(19664628178454143705/39735965222884822823),(8469058577103409781/500000000000000000),1,(13505034528183241228992959277425738963/13550493723365455649600000000000000000),false,MergedCutProfiles.Batch068.profile2739,(fun _ => MergedCutProfiles.Batch068.profile2739)⟩
theorem profilesValid412 : retention412.ProfilesValid := by
  exact MergedCutProfiles.Batch068.valid2739
theorem numericValid412 : retention412.NumericValid := by decide +kernel
def certificate412 : RatCutBinCertificate := ⟨⟨retention412,(2424912444260645091/1000000000000000000),(3628243259175483/62500000000000000),(663008666071467203/62500000000000000),(211315119221540813759/500000000000000000),(491687510617587903/500000000000000000)⟩,(124322969177644379/125000000000000000),(402768611306302691/1000000000000000000),(115477589012864117/500000000000000000),(13341302888776687/62500000000000000)⟩
theorem valid412 : certificate412.Valid := by decide +kernel
theorem sound412 : certificate412.Sound := rat_cut_bin_certificate_sound certificate412 profilesValid412 numericValid412 valid412

def retention413 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(19861274460238685143/39735965222884822823),(3932925635690828741/200000000000000000),1,(2431226182348439264791242996280613487/2458078522306767963125000000000000000),false,MergedCutProfiles.Batch068.profile2740,(fun _ => MergedCutProfiles.Batch068.profile2740)⟩
theorem profilesValid413 : retention413.ProfilesValid := by
  exact MergedCutProfiles.Batch068.valid2740
theorem numericValid413 : retention413.NumericValid := by decide +kernel
def certificate413 : RatCutBinCertificate := ⟨⟨retention413,(2424912444260645091/1000000000000000000),(3628243259175483/62500000000000000),(663008666071467203/62500000000000000),(211315119221540813759/500000000000000000),(975805718018250071/1000000000000000000)⟩,(124322969177644379/125000000000000000),(81178575690369157/200000000000000000),(114063094846356663/500000000000000000),(210908381409083531/1000000000000000000)⟩
theorem valid413 : certificate413.Valid := by decide +kernel
theorem sound413 : certificate413.Sound := rat_cut_bin_certificate_sound certificate413 profilesValid413 numericValid413 valid413

def retention414 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(1/2),(19861274460238685143/1000000000000000000),1,(2455033756017824320072184514987305711/2482659307529835642875000000000000000),false,MergedCutProfiles.Batch068.profile2737,(fun _ => MergedCutProfiles.Batch068.profile2737)⟩
theorem profilesValid414 : retention414.ProfilesValid := by
  exact MergedCutProfiles.Batch068.valid2737
theorem numericValid414 : retention414.NumericValid := by decide +kernel
def certificate414 : RatCutBinCertificate := ⟨⟨retention414,(2424912444260645091/1000000000000000000),(3628243259175483/62500000000000000),(663008666071467203/62500000000000000),(211315119221540813759/500000000000000000),(121950304203896667/125000000000000000)⟩,(124322969177644379/125000000000000000),(405977453563766927/1000000000000000000),(228049942900132697/1000000000000000000),(52723745447118867/250000000000000000)⟩
theorem valid414 : certificate414.Valid := by decide +kernel
theorem sound414 : certificate414.Sound := rat_cut_bin_certificate_sound certificate414 profilesValid414 numericValid414 valid414

def retention415 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(768320644154854230/37419646445651247031),(190178377266053027/250000000000000000),(67/20),(21795847669632113557/10000000000000000000),true,MergedCutProfiles.Batch068.profile2741,![MergedCutProfiles.Batch068.profile2741,MergedCutProfiles.Batch068.profile2742,MergedCutProfiles.Batch068.profile2743,MergedCutProfiles.Batch068.profile2744,MergedCutProfiles.Batch068.profile2745,MergedCutProfiles.Batch068.profile2746,MergedCutProfiles.Batch068.profile2747,MergedCutProfiles.Batch068.profile2748,MergedCutProfiles.Batch068.profile2749,MergedCutProfiles.Batch068.profile2750,MergedCutProfiles.Batch068.profile2751,MergedCutProfiles.Batch068.profile2752,MergedCutProfiles.Batch068.profile2753,MergedCutProfiles.Batch068.profile2754,MergedCutProfiles.Batch068.profile2755,MergedCutProfiles.Batch068.profile2756]⟩
theorem profilesValid415 : retention415.ProfilesValid := by
  change ∀ j : Fin 16, (retention415.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch068.valid2741
  · exact MergedCutProfiles.Batch068.valid2742
  · exact MergedCutProfiles.Batch068.valid2743
  · exact MergedCutProfiles.Batch068.valid2744
  · exact MergedCutProfiles.Batch068.valid2745
  · exact MergedCutProfiles.Batch068.valid2746
  · exact MergedCutProfiles.Batch068.valid2747
  · exact MergedCutProfiles.Batch068.valid2748
  · exact MergedCutProfiles.Batch068.valid2749
  · exact MergedCutProfiles.Batch068.valid2750
  · exact MergedCutProfiles.Batch068.valid2751
  · exact MergedCutProfiles.Batch068.valid2752
  · exact MergedCutProfiles.Batch068.valid2753
  · exact MergedCutProfiles.Batch068.valid2754
  · exact MergedCutProfiles.Batch068.valid2755
  · exact MergedCutProfiles.Batch068.valid2756
theorem numericValid415 : retention415.NumericValid := by decide +kernel
def certificate415 : RatCutBinCertificate := ⟨⟨retention415,(2044963405672943657/1000000000000000000),(61591158108543061/1000000000000000000),(10686964870379908197/1000000000000000000),(201006317128626647647/500000000000000000),(535025207612912027/250000000000000000)⟩,(248801762650866271/250000000000000000),(16729149346213073/40000000000000000),(217189308232647499/1000000000000000000),(110314611945863411/1000000000000000000)⟩
theorem valid415 : certificate415.Valid := by decide +kernel
theorem sound415 : certificate415.Sound := rat_cut_bin_certificate_sound certificate415 profilesValid415 numericValid415 valid415

def retention416 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(874420562330816090/37419646445651247031),(76832064415485423/100000000000000000),(67/20),(278013387121524077351/128000000000000000000),true,MergedCutProfiles.Batch068.profile2757,![MergedCutProfiles.Batch068.profile2757,MergedCutProfiles.Batch068.profile2758,MergedCutProfiles.Batch068.profile2759,MergedCutProfiles.Batch069.profile2760,MergedCutProfiles.Batch069.profile2761,MergedCutProfiles.Batch069.profile2762,MergedCutProfiles.Batch068.profile2748,MergedCutProfiles.Batch069.profile2763,MergedCutProfiles.Batch069.profile2764,MergedCutProfiles.Batch069.profile2765,MergedCutProfiles.Batch069.profile2766,MergedCutProfiles.Batch069.profile2767,MergedCutProfiles.Batch069.profile2768,MergedCutProfiles.Batch069.profile2769,MergedCutProfiles.Batch069.profile2770,MergedCutProfiles.Batch069.profile2771]⟩
theorem profilesValid416 : retention416.ProfilesValid := by
  change ∀ j : Fin 16, (retention416.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch068.valid2757
  · exact MergedCutProfiles.Batch068.valid2758
  · exact MergedCutProfiles.Batch068.valid2759
  · exact MergedCutProfiles.Batch069.valid2760
  · exact MergedCutProfiles.Batch069.valid2761
  · exact MergedCutProfiles.Batch069.valid2762
  · exact MergedCutProfiles.Batch068.valid2748
  · exact MergedCutProfiles.Batch069.valid2763
  · exact MergedCutProfiles.Batch069.valid2764
  · exact MergedCutProfiles.Batch069.valid2765
  · exact MergedCutProfiles.Batch069.valid2766
  · exact MergedCutProfiles.Batch069.valid2767
  · exact MergedCutProfiles.Batch069.valid2768
  · exact MergedCutProfiles.Batch069.valid2769
  · exact MergedCutProfiles.Batch069.valid2770
  · exact MergedCutProfiles.Batch069.valid2771
theorem numericValid416 : retention416.NumericValid := by decide +kernel
def certificate416 : RatCutBinCertificate := ⟨⟨retention416,(2044963405672943657/1000000000000000000),(61591158108543061/1000000000000000000),(10686964870379908197/1000000000000000000),(201006317128626647647/500000000000000000),(1066247836938154283/500000000000000000)⟩,(248801762650866271/250000000000000000),(417708028020024941/1000000000000000000),(217643533023648727/1000000000000000000),(110450228075777839/1000000000000000000)⟩
theorem valid416 : certificate416.Valid := by decide +kernel
theorem sound416 : certificate416.Sound := rat_cut_bin_certificate_sound certificate416 profilesValid416 numericValid416 valid416

def retention417 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(973113028000000000/37419646445651247031),(87442056233081609/100000000000000000),3,(275723999832145137997/128000000000000000000),true,MergedCutProfiles.Batch069.profile2772,![MergedCutProfiles.Batch069.profile2772,MergedCutProfiles.Batch069.profile2773,MergedCutProfiles.Batch069.profile2774,MergedCutProfiles.Batch069.profile2775,MergedCutProfiles.Batch069.profile2776,MergedCutProfiles.Batch069.profile2777,MergedCutProfiles.Batch069.profile2778,MergedCutProfiles.Batch069.profile2779,MergedCutProfiles.Batch069.profile2765,MergedCutProfiles.Batch069.profile2780,MergedCutProfiles.Batch069.profile2781,MergedCutProfiles.Batch069.profile2782,MergedCutProfiles.Batch069.profile2783,MergedCutProfiles.Batch069.profile2784,MergedCutProfiles.Batch069.profile2785,MergedCutProfiles.Batch069.profile2786]⟩
theorem profilesValid417 : retention417.ProfilesValid := by
  change ∀ j : Fin 16, (retention417.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch069.valid2772
  · exact MergedCutProfiles.Batch069.valid2773
  · exact MergedCutProfiles.Batch069.valid2774
  · exact MergedCutProfiles.Batch069.valid2775
  · exact MergedCutProfiles.Batch069.valid2776
  · exact MergedCutProfiles.Batch069.valid2777
  · exact MergedCutProfiles.Batch069.valid2778
  · exact MergedCutProfiles.Batch069.valid2779
  · exact MergedCutProfiles.Batch069.valid2765
  · exact MergedCutProfiles.Batch069.valid2780
  · exact MergedCutProfiles.Batch069.valid2781
  · exact MergedCutProfiles.Batch069.valid2782
  · exact MergedCutProfiles.Batch069.valid2783
  · exact MergedCutProfiles.Batch069.valid2784
  · exact MergedCutProfiles.Batch069.valid2785
  · exact MergedCutProfiles.Batch069.valid2786
theorem numericValid417 : retention417.NumericValid := by decide +kernel
def certificate417 : RatCutBinCertificate := ⟨⟨retention417,(2044963405672943657/1000000000000000000),(61591158108543061/1000000000000000000),(10686964870379908197/1000000000000000000),(201006317128626647647/500000000000000000),(264841882530196493/125000000000000000)⟩,(248801762650866271/250000000000000000),(79169266277717151/200000000000000000),(237309792704485231/1000000000000000000),(131310771616000957/1000000000000000000)⟩
theorem valid417 : certificate417.Valid := by decide +kernel
theorem sound417 : certificate417.Sound := rat_cut_bin_certificate_sound certificate417 profilesValid417 numericValid417 valid417

def retention418 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(1190372674547203697/37419646445651247031),(243278257/250000000),(11/4),(34018744861859767899/16000000000000000000),true,MergedCutProfiles.Batch069.profile2787,![MergedCutProfiles.Batch069.profile2787,MergedCutProfiles.Batch069.profile2788,MergedCutProfiles.Batch069.profile2789,MergedCutProfiles.Batch069.profile2790,MergedCutProfiles.Batch069.profile2791,MergedCutProfiles.Batch069.profile2792,MergedCutProfiles.Batch069.profile2793,MergedCutProfiles.Batch069.profile2794,MergedCutProfiles.Batch069.profile2781,MergedCutProfiles.Batch069.profile2795,MergedCutProfiles.Batch069.profile2796,MergedCutProfiles.Batch069.profile2797,MergedCutProfiles.Batch069.profile2798,MergedCutProfiles.Batch069.profile2799,MergedCutProfiles.Batch070.profile2800,MergedCutProfiles.Batch070.profile2801]⟩
theorem profilesValid418 : retention418.ProfilesValid := by
  change ∀ j : Fin 16, (retention418.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch069.valid2787
  · exact MergedCutProfiles.Batch069.valid2788
  · exact MergedCutProfiles.Batch069.valid2789
  · exact MergedCutProfiles.Batch069.valid2790
  · exact MergedCutProfiles.Batch069.valid2791
  · exact MergedCutProfiles.Batch069.valid2792
  · exact MergedCutProfiles.Batch069.valid2793
  · exact MergedCutProfiles.Batch069.valid2794
  · exact MergedCutProfiles.Batch069.valid2781
  · exact MergedCutProfiles.Batch069.valid2795
  · exact MergedCutProfiles.Batch069.valid2796
  · exact MergedCutProfiles.Batch069.valid2797
  · exact MergedCutProfiles.Batch069.valid2798
  · exact MergedCutProfiles.Batch069.valid2799
  · exact MergedCutProfiles.Batch070.valid2800
  · exact MergedCutProfiles.Batch070.valid2801
theorem numericValid418 : retention418.NumericValid := by decide +kernel
def certificate418 : RatCutBinCertificate := ⟨⟨retention418,(2044963405672943657/1000000000000000000),(61591158108543061/1000000000000000000),(10686964870379908197/1000000000000000000),(201006317128626647647/500000000000000000),(1046879730068141153/500000000000000000)⟩,(248801762650866271/250000000000000000),(95576175441194543/250000000000000000),(250092769948365339/1000000000000000000),(147413086539035467/1000000000000000000)⟩
theorem valid418 : certificate418.Valid := by decide +kernel
theorem sound418 : certificate418.Sound := rat_cut_bin_certificate_sound certificate418 profilesValid418 numericValid418 valid418

def retention419 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(3701004048307411156/37419646445651247031),(1190372674547203697/1000000000000000000),(23/10),(2423271314568306015773/1280000000000000000000),true,MergedCutProfiles.Batch070.profile2802,![MergedCutProfiles.Batch070.profile2802,MergedCutProfiles.Batch070.profile2803,MergedCutProfiles.Batch070.profile2804,MergedCutProfiles.Batch070.profile2805,MergedCutProfiles.Batch070.profile2806,MergedCutProfiles.Batch070.profile2807,MergedCutProfiles.Batch070.profile2808,MergedCutProfiles.Batch070.profile2809,MergedCutProfiles.Batch070.profile2810,MergedCutProfiles.Batch070.profile2811,MergedCutProfiles.Batch070.profile2812,MergedCutProfiles.Batch070.profile2813,MergedCutProfiles.Batch070.profile2814,MergedCutProfiles.Batch070.profile2815,MergedCutProfiles.Batch070.profile2816,MergedCutProfiles.Batch070.profile2817]⟩
theorem profilesValid419 : retention419.ProfilesValid := by
  change ∀ j : Fin 16, (retention419.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch070.valid2802
  · exact MergedCutProfiles.Batch070.valid2803
  · exact MergedCutProfiles.Batch070.valid2804
  · exact MergedCutProfiles.Batch070.valid2805
  · exact MergedCutProfiles.Batch070.valid2806
  · exact MergedCutProfiles.Batch070.valid2807
  · exact MergedCutProfiles.Batch070.valid2808
  · exact MergedCutProfiles.Batch070.valid2809
  · exact MergedCutProfiles.Batch070.valid2810
  · exact MergedCutProfiles.Batch070.valid2811
  · exact MergedCutProfiles.Batch070.valid2812
  · exact MergedCutProfiles.Batch070.valid2813
  · exact MergedCutProfiles.Batch070.valid2814
  · exact MergedCutProfiles.Batch070.valid2815
  · exact MergedCutProfiles.Batch070.valid2816
  · exact MergedCutProfiles.Batch070.valid2817
theorem numericValid419 : retention419.NumericValid := by decide +kernel
def certificate419 : RatCutBinCertificate := ⟨⟨retention419,(2044963405672943657/1000000000000000000),(61591158108543061/1000000000000000000),(10686964870379908197/1000000000000000000),(201006317128626647647/500000000000000000),(1866072452960069883/1000000000000000000)⟩,(248801762650866271/250000000000000000),(49476760193033067/125000000000000000),(237339679409830297/1000000000000000000),(147720632665830069/1000000000000000000)⟩
theorem valid419 : certificate419.Valid := by decide +kernel
theorem sound419 : certificate419.Sound := rat_cut_bin_certificate_sound certificate419 profilesValid419 numericValid419 valid419

def certificates : List RatCutBinCertificate := [certificate408,certificate409,certificate410,certificate411,certificate412,certificate413,certificate414,certificate415,certificate416,certificate417,certificate418,certificate419]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound408,List.forall_mem_cons.mpr ⟨sound409,List.forall_mem_cons.mpr ⟨sound410,List.forall_mem_cons.mpr ⟨sound411,List.forall_mem_cons.mpr ⟨sound412,List.forall_mem_cons.mpr ⟨sound413,List.forall_mem_cons.mpr ⟨sound414,List.forall_mem_cons.mpr ⟨sound415,List.forall_mem_cons.mpr ⟨sound416,List.forall_mem_cons.mpr ⟨sound417,List.forall_mem_cons.mpr ⟨sound418,List.forall_mem_cons.mpr ⟨sound419,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch034
