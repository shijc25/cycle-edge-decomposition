import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch013
import Cycle12.MergedCutProfiles.Batch014
import Cycle12.MergedCutProfiles.Batch015
import Cycle12.MergedCutProfiles.Batch016
import Cycle12.MergedCutProfiles.Batch314
import Cycle12.MergedCutProfiles.Batch315
import Cycle12.MergedCutProfiles.Batch316

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch167

def retention2004 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(2453909385203642241/682213167231499365169),(19844063/15625000),(49/20),(9178845712083041173/4000000000000000000),true,MergedCutProfiles.Batch013.profile557,![MergedCutProfiles.Batch013.profile557,MergedCutProfiles.Batch013.profile559,MergedCutProfiles.Batch014.profile561,MergedCutProfiles.Batch014.profile563,MergedCutProfiles.Batch014.profile565,MergedCutProfiles.Batch014.profile567,MergedCutProfiles.Batch014.profile569,MergedCutProfiles.Batch014.profile571,MergedCutProfiles.Batch014.profile573,MergedCutProfiles.Batch014.profile574,MergedCutProfiles.Batch314.profile12588,MergedCutProfiles.Batch014.profile576,MergedCutProfiles.Batch314.profile12589,MergedCutProfiles.Batch314.profile12590,MergedCutProfiles.Batch014.profile590,MergedCutProfiles.Batch014.profile591]⟩
theorem profilesValid2004 : retention2004.ProfilesValid := by
  change ∀ j : Fin 16, (retention2004.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch013.valid557
  · exact MergedCutProfiles.Batch013.valid559
  · exact MergedCutProfiles.Batch014.valid561
  · exact MergedCutProfiles.Batch014.valid563
  · exact MergedCutProfiles.Batch014.valid565
  · exact MergedCutProfiles.Batch014.valid567
  · exact MergedCutProfiles.Batch014.valid569
  · exact MergedCutProfiles.Batch014.valid571
  · exact MergedCutProfiles.Batch014.valid573
  · exact MergedCutProfiles.Batch014.valid574
  · exact MergedCutProfiles.Batch314.valid12588
  · exact MergedCutProfiles.Batch014.valid576
  · exact MergedCutProfiles.Batch314.valid12589
  · exact MergedCutProfiles.Batch314.valid12590
  · exact MergedCutProfiles.Batch014.valid590
  · exact MergedCutProfiles.Batch014.valid591
theorem numericValid2004 : retention2004.NumericValid := by decide +kernel
def certificate2004 : RatCutBinCertificate := ⟨⟨retention2004,(231550024312635889/125000000000000000),(21663071517499/3125000000000000),(7713429156654005149/1000000000000000000),(660788836219184268857/125000000000000000),(1145316355374434817/500000000000000000)⟩,(15619556993347519/15625000000000000),(10989803029399357/31250000000000000),(280803625311178071/1000000000000000000),(10089910320696927/50000000000000000)⟩
theorem valid2004 : certificate2004.Valid := by decide +kernel
theorem sound2004 : certificate2004.Sound := rat_cut_bin_certificate_sound certificate2004 profilesValid2004 numericValid2004 valid2004

def retention2005 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(64000000000000000000/682213167231499365169),(2453909385203642241/1000000000000000000),(8/5),(2425817873709573435573/1280000000000000000000),true,MergedCutProfiles.Batch314.profile12591,![MergedCutProfiles.Batch314.profile12591,MergedCutProfiles.Batch314.profile12592,MergedCutProfiles.Batch314.profile12593,MergedCutProfiles.Batch314.profile12594,MergedCutProfiles.Batch314.profile12595,MergedCutProfiles.Batch314.profile12596,MergedCutProfiles.Batch314.profile12597,MergedCutProfiles.Batch314.profile12598,MergedCutProfiles.Batch314.profile12599,MergedCutProfiles.Batch315.profile12600,MergedCutProfiles.Batch315.profile12601,MergedCutProfiles.Batch315.profile12602,MergedCutProfiles.Batch315.profile12603,MergedCutProfiles.Batch315.profile12604,MergedCutProfiles.Batch315.profile12605,MergedCutProfiles.Batch315.profile12606]⟩
theorem profilesValid2005 : retention2005.ProfilesValid := by
  change ∀ j : Fin 16, (retention2005.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch314.valid12591
  · exact MergedCutProfiles.Batch314.valid12592
  · exact MergedCutProfiles.Batch314.valid12593
  · exact MergedCutProfiles.Batch314.valid12594
  · exact MergedCutProfiles.Batch314.valid12595
  · exact MergedCutProfiles.Batch314.valid12596
  · exact MergedCutProfiles.Batch314.valid12597
  · exact MergedCutProfiles.Batch314.valid12598
  · exact MergedCutProfiles.Batch314.valid12599
  · exact MergedCutProfiles.Batch315.valid12600
  · exact MergedCutProfiles.Batch315.valid12601
  · exact MergedCutProfiles.Batch315.valid12602
  · exact MergedCutProfiles.Batch315.valid12603
  · exact MergedCutProfiles.Batch315.valid12604
  · exact MergedCutProfiles.Batch315.valid12605
  · exact MergedCutProfiles.Batch315.valid12606
theorem numericValid2005 : retention2005.NumericValid := by decide +kernel
def certificate2005 : RatCutBinCertificate := ⟨⟨retention2005,(231550024312635889/125000000000000000),(21663071517499/3125000000000000),(7713429156654005149/1000000000000000000),(660788836219184268857/125000000000000000),(946253280986306833/500000000000000000)⟩,(15619556993347519/15625000000000000),(65580918313350217/200000000000000000),(153230160500499879/500000000000000000),(278458619961528249/1000000000000000000)⟩
theorem valid2005 : certificate2005.Valid := by decide +kernel
theorem sound2005 : certificate2005.Sound := rat_cut_bin_certificate_sound certificate2005 profilesValid2005 numericValid2005 valid2005

def retention2006 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(1/2),64,1,(63842362441861810878166029772824077959/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch015.profile610,(fun _ => MergedCutProfiles.Batch015.profile610)⟩
theorem profilesValid2006 : retention2006.ProfilesValid := by
  exact MergedCutProfiles.Batch015.valid610
theorem numericValid2006 : retention2006.NumericValid := by decide +kernel
def certificate2006 : RatCutBinCertificate := ⟨⟨retention2006,(231550024312635889/125000000000000000),(21663071517499/3125000000000000),(7713429156654005149/1000000000000000000),(660788836219184268857/125000000000000000),(497936065630819009/500000000000000000)⟩,(15619556993347519/15625000000000000),(53937436687620899/125000000000000000),(102914723707559139/500000000000000000),(40353638040830321/200000000000000000)⟩
theorem valid2006 : certificate2006.Valid := by decide +kernel
theorem sound2006 : certificate2006.Sound := rat_cut_bin_certificate_sound certificate2006 profilesValid2006 numericValid2006 valid2006

def retention2007 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(64000000000000000000/682213167231499365169),(2471453906485928251/500000000000000000),(23/20),(3646429087938819623995410889830308717631/1977163125188742600800000000000000000000),false,MergedCutProfiles.Batch315.profile12607,(fun _ => MergedCutProfiles.Batch315.profile12607)⟩
theorem profilesValid2007 : retention2007.ProfilesValid := by
  exact MergedCutProfiles.Batch315.valid12607
theorem numericValid2007 : retention2007.NumericValid := by decide +kernel
def certificate2007 : RatCutBinCertificate := ⟨⟨retention2007,(265801669812635889/125000000000000000),(21663071517499/3125000000000000),(7713429156654005149/1000000000000000000),(660788836219184268857/125000000000000000),(921037782045123109/500000000000000000)⟩,(999600118009147741/1000000000000000000),(65620461639710327/500000000000000000),(600667084586721091/1000000000000000000),(750309921833822861/1000000000000000000)⟩
theorem valid2007 : certificate2007.Valid := by decide +kernel
theorem sound2007 : certificate2007.Sound := rat_cut_bin_certificate_sound certificate2007 profilesValid2007 numericValid2007 valid2007

def retention2008 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(1/2),64,1,(63842362441861810878166029772824077959/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch015.profile610,(fun _ => MergedCutProfiles.Batch015.profile610)⟩
theorem profilesValid2008 : retention2008.ProfilesValid := by
  exact MergedCutProfiles.Batch015.valid610
theorem numericValid2008 : retention2008.NumericValid := by decide +kernel
def certificate2008 : RatCutBinCertificate := ⟨⟨retention2008,(265801669812635889/125000000000000000),(21663071517499/3125000000000000),(7713429156654005149/1000000000000000000),(660788836219184268857/125000000000000000),(995625871217466647/1000000000000000000)⟩,(999600118009147741/1000000000000000000),(24281781417154311/100000000000000000),(413385296546353563/1000000000000000000),(81021832875026229/200000000000000000)⟩
theorem valid2008 : certificate2008.Valid := by decide +kernel
theorem sound2008 : certificate2008.Sound := rat_cut_bin_certificate_sound certificate2008 profilesValid2008 numericValid2008 valid2008

def retention2009 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(206546492605675012/195178974790766825787),(119092271769551423/200000000000000000),4,(8962130090858267237/4000000000000000000),true,MergedCutProfiles.Batch315.profile12608,![MergedCutProfiles.Batch315.profile12608,MergedCutProfiles.Batch015.profile611,MergedCutProfiles.Batch315.profile12609,MergedCutProfiles.Batch015.profile612,MergedCutProfiles.Batch315.profile12610,MergedCutProfiles.Batch315.profile12611,MergedCutProfiles.Batch315.profile12612,MergedCutProfiles.Batch015.profile614,MergedCutProfiles.Batch315.profile12613,MergedCutProfiles.Batch315.profile12614,MergedCutProfiles.Batch315.profile12615,MergedCutProfiles.Batch015.profile627,MergedCutProfiles.Batch315.profile12616,MergedCutProfiles.Batch015.profile617,MergedCutProfiles.Batch315.profile12617,MergedCutProfiles.Batch015.profile628]⟩
theorem profilesValid2009 : retention2009.ProfilesValid := by
  change ∀ j : Fin 16, (retention2009.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch315.valid12608
  · exact MergedCutProfiles.Batch015.valid611
  · exact MergedCutProfiles.Batch315.valid12609
  · exact MergedCutProfiles.Batch015.valid612
  · exact MergedCutProfiles.Batch315.valid12610
  · exact MergedCutProfiles.Batch315.valid12611
  · exact MergedCutProfiles.Batch315.valid12612
  · exact MergedCutProfiles.Batch015.valid614
  · exact MergedCutProfiles.Batch315.valid12613
  · exact MergedCutProfiles.Batch315.valid12614
  · exact MergedCutProfiles.Batch315.valid12615
  · exact MergedCutProfiles.Batch015.valid627
  · exact MergedCutProfiles.Batch315.valid12616
  · exact MergedCutProfiles.Batch015.valid617
  · exact MergedCutProfiles.Batch315.valid12617
  · exact MergedCutProfiles.Batch015.valid628
theorem numericValid2009 : retention2009.NumericValid := by decide +kernel
def certificate2009 : RatCutBinCertificate := ⟨⟨retention2009,(1859115213225949127/1000000000000000000),(1008381335301397/125000000000000000),(244078099696727509/31250000000000000),(4594407606916828314031/1000000000000000000),(1116425895372984597/500000000000000000)⟩,(999598156535480557/1000000000000000000),(276947561598786531/500000000000000000),(118874754377627421/1000000000000000000),(10746577596990387/200000000000000000)⟩
theorem valid2009 : certificate2009.Valid := by decide +kernel
theorem sound2009 : certificate2009.Sound := rat_cut_bin_certificate_sound certificate2009 profilesValid2009 numericValid2009 valid2009

def retention2010 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1246204541000000000/585536924372300477361),(154909869454256259/250000000000000000),4,(36286463914384802799/16000000000000000000),true,MergedCutProfiles.Batch015.profile611,![MergedCutProfiles.Batch015.profile611,MergedCutProfiles.Batch015.profile612,MergedCutProfiles.Batch315.profile12611,MergedCutProfiles.Batch015.profile614,MergedCutProfiles.Batch315.profile12614,MergedCutProfiles.Batch015.profile627,MergedCutProfiles.Batch015.profile617,MergedCutProfiles.Batch015.profile628,MergedCutProfiles.Batch315.profile12618,MergedCutProfiles.Batch015.profile620,MergedCutProfiles.Batch015.profile621,MergedCutProfiles.Batch015.profile629,MergedCutProfiles.Batch015.profile623,MergedCutProfiles.Batch015.profile624,MergedCutProfiles.Batch015.profile625,MergedCutProfiles.Batch015.profile626]⟩
theorem profilesValid2010 : retention2010.ProfilesValid := by
  change ∀ j : Fin 16, (retention2010.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch015.valid611
  · exact MergedCutProfiles.Batch015.valid612
  · exact MergedCutProfiles.Batch315.valid12611
  · exact MergedCutProfiles.Batch015.valid614
  · exact MergedCutProfiles.Batch315.valid12614
  · exact MergedCutProfiles.Batch015.valid627
  · exact MergedCutProfiles.Batch015.valid617
  · exact MergedCutProfiles.Batch015.valid628
  · exact MergedCutProfiles.Batch315.valid12618
  · exact MergedCutProfiles.Batch015.valid620
  · exact MergedCutProfiles.Batch015.valid621
  · exact MergedCutProfiles.Batch015.valid629
  · exact MergedCutProfiles.Batch015.valid623
  · exact MergedCutProfiles.Batch015.valid624
  · exact MergedCutProfiles.Batch015.valid625
  · exact MergedCutProfiles.Batch015.valid626
theorem numericValid2010 : retention2010.NumericValid := by decide +kernel
def certificate2010 : RatCutBinCertificate := ⟨⟨retention2010,(1859115213225949127/1000000000000000000),(1008381335301397/125000000000000000),(244078099696727509/31250000000000000),(4594407606916828314031/1000000000000000000),(2260223262901383941/1000000000000000000)⟩,(999598156535480557/1000000000000000000),(106632057581847793/200000000000000000),(8219844120280807/62500000000000000),(30244651287685989/500000000000000000)⟩
theorem valid2010 : certificate2010.Valid := by decide +kernel
theorem sound2010 : certificate2010.Sound := rat_cut_bin_certificate_sound certificate2010 profilesValid2010 numericValid2010 valid2010

def retention2011 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1373564259651302555/585536924372300477361),(1246204541/1000000000),(49/20),(9209333258107016183/4000000000000000000),true,MergedCutProfiles.Batch315.profile12619,![MergedCutProfiles.Batch315.profile12619,MergedCutProfiles.Batch315.profile12620,MergedCutProfiles.Batch315.profile12621,MergedCutProfiles.Batch315.profile12613,MergedCutProfiles.Batch315.profile12615,MergedCutProfiles.Batch315.profile12616,MergedCutProfiles.Batch315.profile12622,MergedCutProfiles.Batch315.profile12618,MergedCutProfiles.Batch015.profile620,MergedCutProfiles.Batch015.profile621,MergedCutProfiles.Batch015.profile622,MergedCutProfiles.Batch015.profile623,MergedCutProfiles.Batch315.profile12623,MergedCutProfiles.Batch315.profile12624,MergedCutProfiles.Batch315.profile12625,MergedCutProfiles.Batch315.profile12626]⟩
theorem profilesValid2011 : retention2011.ProfilesValid := by
  change ∀ j : Fin 16, (retention2011.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch315.valid12619
  · exact MergedCutProfiles.Batch315.valid12620
  · exact MergedCutProfiles.Batch315.valid12621
  · exact MergedCutProfiles.Batch315.valid12613
  · exact MergedCutProfiles.Batch315.valid12615
  · exact MergedCutProfiles.Batch315.valid12616
  · exact MergedCutProfiles.Batch315.valid12622
  · exact MergedCutProfiles.Batch315.valid12618
  · exact MergedCutProfiles.Batch015.valid620
  · exact MergedCutProfiles.Batch015.valid621
  · exact MergedCutProfiles.Batch015.valid622
  · exact MergedCutProfiles.Batch015.valid623
  · exact MergedCutProfiles.Batch315.valid12623
  · exact MergedCutProfiles.Batch315.valid12624
  · exact MergedCutProfiles.Batch315.valid12625
  · exact MergedCutProfiles.Batch315.valid12626
theorem numericValid2011 : retention2011.NumericValid := by decide +kernel
def certificate2011 : RatCutBinCertificate := ⟨⟨retention2011,(1859115213225949127/1000000000000000000),(1008381335301397/125000000000000000),(244078099696727509/31250000000000000),(4594407606916828314031/1000000000000000000),(1148814433479276909/500000000000000000)⟩,(999598156535480557/1000000000000000000),(11050543552498899/31250000000000000),(139389010788957129/500000000000000000),(199915567229767909/1000000000000000000)⟩
theorem valid2011 : certificate2011.Valid := by decide +kernel
theorem sound2011 : certificate2011.Sound := rat_cut_bin_certificate_sound certificate2011 profilesValid2011 numericValid2011 valid2011

def retention2012 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(11901099679936878988/585536924372300477361),(274712851930260511/200000000000000000),(23/10),(139385178918266644207/64000000000000000000),true,MergedCutProfiles.Batch315.profile12627,![MergedCutProfiles.Batch315.profile12627,MergedCutProfiles.Batch315.profile12628,MergedCutProfiles.Batch315.profile12629,MergedCutProfiles.Batch016.profile647,MergedCutProfiles.Batch016.profile650,MergedCutProfiles.Batch315.profile12630,MergedCutProfiles.Batch315.profile12631,MergedCutProfiles.Batch315.profile12632,MergedCutProfiles.Batch315.profile12633,MergedCutProfiles.Batch315.profile12634,MergedCutProfiles.Batch315.profile12635,MergedCutProfiles.Batch315.profile12636,MergedCutProfiles.Batch315.profile12637,MergedCutProfiles.Batch315.profile12638,MergedCutProfiles.Batch315.profile12639,MergedCutProfiles.Batch316.profile12640]⟩
theorem profilesValid2012 : retention2012.ProfilesValid := by
  change ∀ j : Fin 16, (retention2012.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch315.valid12627
  · exact MergedCutProfiles.Batch315.valid12628
  · exact MergedCutProfiles.Batch315.valid12629
  · exact MergedCutProfiles.Batch016.valid647
  · exact MergedCutProfiles.Batch016.valid650
  · exact MergedCutProfiles.Batch315.valid12630
  · exact MergedCutProfiles.Batch315.valid12631
  · exact MergedCutProfiles.Batch315.valid12632
  · exact MergedCutProfiles.Batch315.valid12633
  · exact MergedCutProfiles.Batch315.valid12634
  · exact MergedCutProfiles.Batch315.valid12635
  · exact MergedCutProfiles.Batch315.valid12636
  · exact MergedCutProfiles.Batch315.valid12637
  · exact MergedCutProfiles.Batch315.valid12638
  · exact MergedCutProfiles.Batch315.valid12639
  · exact MergedCutProfiles.Batch316.valid12640
theorem numericValid2012 : retention2012.NumericValid := by decide +kernel
def certificate2012 : RatCutBinCertificate := ⟨⟨retention2012,(1859115213225949127/1000000000000000000),(1008381335301397/125000000000000000),(244078099696727509/31250000000000000),(4594407606916828314031/1000000000000000000),(543369250129266417/250000000000000000)⟩,(999598156535480557/1000000000000000000),(178626935612221629/500000000000000000),(137508454915269303/500000000000000000),(199957834231199043/1000000000000000000)⟩
theorem valid2012 : certificate2012.Valid := by decide +kernel
theorem sound2012 : certificate2012.Sound := rat_cut_bin_certificate_sound certificate2012 profilesValid2012 numericValid2012 valid2012

def retention2013 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(64000000000000000000/585536924372300477361),(2975274919984219747/250000000000000000),(21/20),(8528886013884924629862745703268138321/4648867062475343354687500000000000000),false,MergedCutProfiles.Batch316.profile12641,(fun _ => MergedCutProfiles.Batch316.profile12641)⟩
theorem profilesValid2013 : retention2013.ProfilesValid := by
  exact MergedCutProfiles.Batch316.valid12641
theorem numericValid2013 : retention2013.NumericValid := by decide +kernel
def certificate2013 : RatCutBinCertificate := ⟨⟨retention2013,(1859115213225949127/1000000000000000000),(1008381335301397/125000000000000000),(244078099696727509/31250000000000000),(4594407606916828314031/1000000000000000000),(1832599834700743293/1000000000000000000)⟩,(999598156535480557/1000000000000000000),(63420151976819839/250000000000000000),(398273698196650427/1000000000000000000),(304838458226051907/500000000000000000)⟩
theorem valid2013 : certificate2013.Valid := by decide +kernel
theorem sound2013 : certificate2013.Sound := rat_cut_bin_certificate_sound certificate2013 profilesValid2013 numericValid2013 valid2013

def retention2014 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1/2),64,1,(255369632393373974456752157088663284991/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch016.profile655,(fun _ => MergedCutProfiles.Batch016.profile655)⟩
theorem profilesValid2014 : retention2014.ProfilesValid := by
  exact MergedCutProfiles.Batch016.valid655
theorem numericValid2014 : retention2014.NumericValid := by decide +kernel
def certificate2014 : RatCutBinCertificate := ⟨⟨retention2014,(1859115213225949127/1000000000000000000),(1008381335301397/125000000000000000),(244078099696727509/31250000000000000),(4594407606916828314031/1000000000000000000),(497808722453650433/500000000000000000)⟩,(999598156535480557/1000000000000000000),(433701581414470547/1000000000000000000),(203984260572954901/1000000000000000000),(7995930810686281/40000000000000000)⟩
theorem valid2014 : certificate2014.Valid := by decide +kernel
theorem sound2014 : certificate2014.Sound := rat_cut_bin_certificate_sound certificate2014 profilesValid2014 numericValid2014 valid2014

def retention2015 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(64000000000000000000/585536924372300477361),(4889979367912039857/1000000000000000000),(23/20),(14105115052980045575028148966606127197679/7823966988659263771200000000000000000000),false,MergedCutProfiles.Batch316.profile12641,(fun _ => MergedCutProfiles.Batch316.profile12641)⟩
theorem profilesValid2015 : retention2015.ProfilesValid := by
  exact MergedCutProfiles.Batch316.valid12641
theorem numericValid2015 : retention2015.NumericValid := by decide +kernel
def certificate2015 : RatCutBinCertificate := ⟨⟨retention2015,(2139093607225949127/1000000000000000000),(1008381335301397/125000000000000000),(244078099696727509/31250000000000000),(4594407606916828314031/1000000000000000000),(360053569901872973/200000000000000000)⟩,(62471102478511477/62500000000000000),(27337765511735563/200000000000000000),(29495499842693147/50000000000000000),(180506049325476841/250000000000000000)⟩
theorem valid2015 : certificate2015.Valid := by decide +kernel
theorem sound2015 : certificate2015.Sound := rat_cut_bin_certificate_sound certificate2015 profilesValid2015 numericValid2015 valid2015

def certificates : List RatCutBinCertificate := [certificate2004,certificate2005,certificate2006,certificate2007,certificate2008,certificate2009,certificate2010,certificate2011,certificate2012,certificate2013,certificate2014,certificate2015]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2004,List.forall_mem_cons.mpr ⟨sound2005,List.forall_mem_cons.mpr ⟨sound2006,List.forall_mem_cons.mpr ⟨sound2007,List.forall_mem_cons.mpr ⟨sound2008,List.forall_mem_cons.mpr ⟨sound2009,List.forall_mem_cons.mpr ⟨sound2010,List.forall_mem_cons.mpr ⟨sound2011,List.forall_mem_cons.mpr ⟨sound2012,List.forall_mem_cons.mpr ⟨sound2013,List.forall_mem_cons.mpr ⟨sound2014,List.forall_mem_cons.mpr ⟨sound2015,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch167
