module

public import VerifiedGarbage.Spec.Ffdh.VettedGroups
public import VerifiedGarbage.Proof.Ffdh.VettedValidation.Power

/-! Kernel-checked binary-power certificate for the published ffdhe4096 parameters.
Each small block checks its arithmetic; the shared append theorem composes the blocks. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation.Ffdhe4096

open VG.Proof.Ffdh.VettedValidation

private theorem initial : 2 ^ (0 : Nat) % Spec.Ffdh.ffdhe4096Prime = 1 := by decide +kernel

private def prefix0 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (31 : Nat) * 2 ^ (96 : Nat))
private def residue0 : Nat := 0x75347f049e76fe7adf8210464fec3521cd9d45c129aa48124fcff20ba82b27c0c4614c2dbe20213532482f1878bd6bb6df60616f8f49708ad226d3c6be6f770f8271bcb1b32b507627b752d53075e276950a56db798e2842907aeeebc7f8067da3016c93c0ced735c3c2e009288ad61b2a33b404dcd7ab395717c820f310eec5fcd9a8a621bfb403bed69ba9c0062f8958a0fe3dc0e477e65f870011a4500636d51a47a5687fe8ffcc746e3517a22681aa8f2d2b3b6bd351a96980dd26e0df24f0028cb186c4093f55e7cda3c9b712215edae6d6044c184c7b08bc2bafe70ce001f67b38bbc5bd1b93aee96636f1d98bdae6c8935122e5cd3f0fd303ee193faacaea26c9de071a43fecce592267ee44a02d3f5e9bd19f19bbe12ea56ff2e5090acaa775f98a6f6603e150a2c6571ad05126d4abf7e8e369f640066e541d23bb2946e26d2992630cc426e546d9e191283f5305ec471edbcc42b64fb321392af84edadd387ee74332e94c432b5a42e0448b0406d9bbfe971fe55dd6d1013237fde9b296bb69d1fef6eb4a4c8cc84fae0c9300f1776772ab1526b8b512fdf8a87f3574fae6a9140fb73bcc2d013136d2920d67f17d6470fd876db63cd1cd29dd77ceafcfaca2394fba60ff0864a24daae4a05b97f715e09abd1bb250ba868761f6653c9d07ad5434967e9414a49ac1b7eba4836d0b05299bacf30935a81ee06113b
private theorem part0 : 2 ^ prefix0 % Spec.Ffdh.ffdhe4096Prime = residue0 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue0)
    (e := 0) (a := 1) (b := 2147483647) (n := 31)
    initial (by decide +kernel) (by decide +kernel)
  rw [show 0 * 2 ^ (31 : Nat) + 2147483647 = prefix0 from by decide +kernel] at result
  exact result

private def prefix1 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (31 : Nat) * 2 ^ (64 : Nat))
private def residue1 : Nat := 0x8f851f3730bd9d318270b43530a26259cb064f3662cfd1a17dc57b5ee4c43fe18ae502dbbe683399fb2fdcc99a08f2540b727c523cf51be8b9c54ed42db39599ae4f7e5617dd12cc5e6ba7aee3f109cfabd418fe85b210e3e5a453ab671de25b848b8a3b07329872a98d0c0d90afad8462fd7be36dba82f42a77482d2599ec200b24d4c8e72038ea108fdbafe232a8fa81e9c44d2f7f61dcef1e82616da65190140630795d78b71186ad68125694084bf9c8172739a874203093ba6cf1fcc6cee3e12eef4a575f1ec9cc670a6b03a539ce343c483da55ade7215c9b90753d5a8658c558ca0573dde72c2ddede46f5cd5a64081feaeb6a04541517dcec00e4c20bdedd536dbf8bd1595378b911f97fa7440b1afdcdad71ce829de9fc92e10f915c64734f3003fc963305ecb43464da2780db207a1d66a12f3e121ca5a01ea04a593289802733a0e9412a2729355f2cffd931cfbdd5f28fb7132ec8632f750bc3e1599f409ccf9370236aebf132fd82823af33c9dc0ac2f2b55f00e8440c96fdee761202858418cd70cb32e6cfd0782f13381bbfc38b4fc9cb04c353af2e74eb2f00f47c0f5645b7f33fb43a9bdc5cf607169f720e7a503ff1aaeb427d3c276d87bc7b42551ebb9106e04552a98da6b8bf04c690d6d6498894d44d5958b64d82159184348a3d1b915e284fcaae73798e034a7a903b7f839cc4de3000507092265c
private theorem part1 : 2 ^ prefix1 % Spec.Ffdh.ffdhe4096Prime = residue1 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue1)
    (e := prefix0) (a := residue0) (b := 4294967295) (n := 32)
    part0 (by decide +kernel) (by decide +kernel)
  rw [show prefix0 * 2 ^ (32 : Nat) + 4294967295 = prefix1 from by decide +kernel] at result
  exact result

private def prefix2 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (31 : Nat) * 2 ^ (32 : Nat))
private def residue2 : Nat := 0xeff13f4c1d86cb3620957e38d956d4052077b915e3c10e693779ef248e913b9a44302d200a2330708668eb47b62e4cd9ef334cffbd3a8135d9bf466e76dc4559566fbd8519ebf1f3506438d5b57cbe9d7d849671101fadb1bd4be48eb5472b16c35032efd766488cf159d9b242cdb2def5aa1ade48603b0d1a2c4826e1d07714eadbcc69e14b9847d268c90b60b02ffe86cc0853404c6a6780fc672f77c0ab8c5150d06ee8213b0e4c6bbd18da58ce8d38c4e4033bc564c6c9c0ceae73d49644e7541ecd19036a278e483df9ddddcda0497c395fa7b09c93aa4d61d9f2e1f44bd5b4ec4c545585c5ffcc87be571dc217ccb8b04eda21ff105d14d67dca7815d4d9f09afb8bd3d891d142b08045e6d040246263b8054d0c21dbcfe05df97d27296edae869aed0a766755b7a5f0a98bbf527192d3033636d32a6ec3f0af762eaefb01b32a5ee081df2cc5fe05988db89f77dd2eb86ca156dbf4a519b03865ada5d26445ca79be75de16c4b94234e9617147f6300d16eb6a77de6ce6266cb4370f113add0c06ca0325bc0d68552002771d0acb2686a97125b82aada19ff78cdfef532eb8f801af44ec403b8c6558d08b6f6f9fc2d9828a30d2d3ee8c01a8695101455bd3ec483593a52e5da23d58a32b49c03cbf4efea0b9679aafdfbdae09ba813ffb02a0d22aab165fa4cef13e77bcb948599d5a3da8993d170b177db0caff06a
private theorem part2 : 2 ^ prefix2 % Spec.Ffdh.ffdhe4096Prime = residue2 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue2)
    (e := prefix1) (a := residue1) (b := 3606850092) (n := 32)
    part1 (by decide +kernel) (by decide +kernel)
  rw [show prefix1 * 2 ^ (32 : Nat) + 3606850092 = prefix2 from by decide +kernel] at result
  exact result

private def prefix3 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (31 : Nat) * 2 ^ (0 : Nat))
private def residue3 : Nat := 0x7368ade741b5d6a12e5911e9036d9d021d2ec5024308c388bc714caf5d948fccb6495336adcbfef9963e60d68848881e4a830743076a144fd9679a04122ef77c8987b0f35110dcb39f2353b99883b017d7dc9f5c4ab5142e432f8f2559720063bddb066beaf9e8baccded2deefc5e4d6c7554c786ce10f6d487b33facae67ef3eef6030653bca692c100882432bfedd2560979ed0892de26e03815ed7fa2768283aef67c6eb9ed1e6de5ac22c617a93400c9bc3171adf6254fb2cedea8318b205a20c4c8f392930b1097ae5c3b867e6d7ba0612468e62f36bb36ee3e5571539ad69d436e281aa7c0593e58262c598365bf70c946cc402d90fa60802e152290b8503762cdb539558a73490f1a45d991e59f0794c2a8f7b5cac088172e1e440806a24675fa84909976fda304e85531a6379763cdfc0a4368ebb462e1042259ea4acc78a1412d2f943d2a8518d1756a8292d3a32c367caf3799a6f4b3e10642b418589d7a45072a292035e301ddfca806e1b0df8db6964cc228e45b73b4515d4db65bb909fe39e2e10082f8915269d182eb212cf86acecfcb397f679b307f4942033730af94547b11ad4ca58f1e50415d53fd50571ece81f2293bbcc424653fc11c577ffeb687b8d5529df35afc124310d0d26641320e876eca14b2d27f025083e0e7fc962ded04acdd543649d12e323c70d452110d231fd768dfef9c1be1cfc831
private theorem part3 : 2 ^ prefix3 % Spec.Ffdh.ffdhe4096Prime = residue3 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue3)
    (e := prefix2) (a := residue2) (b := 1365091661) (n := 32)
    part2 (by decide +kernel) (by decide +kernel)
  rw [show prefix2 * 2 ^ (32 : Nat) + 1365091661 = prefix3 from by decide +kernel] at result
  exact result

private def prefix4 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (30 : Nat) * 2 ^ (96 : Nat))
private def residue4 : Nat := 0x7333e1927856e9b10a9c6ac652731769d367a1d18ac1df8ec489689aef2d862d81994113af411b6a4ae926ab4f811472ba4aadf09f1ee12a6b755931038d32cd1a7b711e63a5962394762adb657c976e6ff47d6a0c70cda5563c03fc0499d6ff8258b698dcc66438564d2575aa3708dcccdae93ced70f152182c01c171afcd243e5bb4b197d742f91df174753e5ab072462a91e31884009a27b6987fb262baf31e9047b1be5c4926f6fb37d5c3e2cacdffcf45537a6dac2ffe4bc0f47b06eb1bd9c8fd2cfffe2f0b68d80c56446e2ff7cc7e0dba00f7cf3951de7cd2fa480ce014673dc00d5759cc6a23949ff1c9ba60cc684f9fe6a507da297d527e8b9f0764d865db8c35e880b4d75f7b03ae244a83892fe02053d2d1d2b3a08df546e70f187ec71859bfaae1430ebfddd8ff4d6934e50cc13154ebad567648d7a131326caa483cb3fca538b6104d77a7e05445189a3ac73834c445968f787ff698bab17c2250096f7ff0c66f14dcb1b085ad5d0d433cb4c9a8beb10107c1a77b17cf85ad24b6d83fbd0782c9a738bc3b0417d2af75b92d2bf2d0316017cd770205d46d77d39b9e06da4bbdbf1f8dbeefbfd9b5feaba830f66a22e702935bbaa180cb05eda19bae64db1c562051a0e2927a233b8de2ee4ecd30d34a9a9fd8ea0bcfabd1a93c780bb5dd5d69907d66c7b2f4e01e15fd466ffd2531f68fb0b3026032977f9c5e
private theorem part4 : 2 ^ prefix4 % Spec.Ffdh.ffdhe4096Prime = residue4 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue4)
    (e := prefix3) (a := residue3) (b := 1475226384) (n := 32)
    part3 (by decide +kernel) (by decide +kernel)
  rw [show prefix3 * 2 ^ (32 : Nat) + 1475226384 = prefix4 from by decide +kernel] at result
  exact result

private def prefix5 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (30 : Nat) * 2 ^ (64 : Nat))
private def residue5 : Nat := 0xdf7d1fca4e79a199760f7aca6d29878e7e68e6203fdf3eb575a855afd91406717602f730fb72c8c20ba8c7a661c1862dbbf342336000aa8f571422f29d4f9b2b532f1763011b732de65f89d397ebae9e36db9ee0b50b94c387f888e79764667e12fd804eaa5dbbf416a821a5046ba16dede1d85b50dbb0d857acec895a5c7f85f90b9a6932cdd60d8210b94b57ff3005cc689987045fa2c6c3cb783c13c454044668afe8efe058d19a84514f26e66507ed789f792f6f5bae687dd9a54062740e04c02cf01831e43df199a6772ff6ab1a8922d9e473d9f18d272695dc70ee4e947be20d8af365a4d917315fcbc4f5aeeb849e27a0ea5eea7308ac592af202cc18f8dd30cea0c7c1b5b89a4fa9b4c4b0f23d6f3e666dff8d140f793a187cc9f821145375b2cdfabaec809fed7fd3849ab0c28740ad8c2d8d9f891af0236162cbe0be10b56fe48e980d0857735b7bc9621d3c7a2976f61301d097735fe32eb8cb590ac3de0a15f25d8da78868fafca531f53804fa78e3deb72654c296d78994a00124f68d901f5e03610f9935781aec236b167a07330a90b0e6b8f7d435fa54f15ff1c777ace30643ddfa61ffdaa0ead4c2177166172a09ef28f1ced4338fd65d4af26037c982a9cce372cc89d34337b576accd602633816ffe8a7169fab66be00759bbfab31f9ca6f81720152e2f124a87cc9ad618de77225bd9346fcffc0d51b2
private theorem part5 : 2 ^ prefix5 % Spec.Ffdh.ffdhe4096Prime = residue5 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue5)
    (e := prefix4) (a := residue4) (b := 329162360) (n := 32)
    part4 (by decide +kernel) (by decide +kernel)
  rw [show prefix4 * 2 ^ (32 : Nat) + 329162360 = prefix5 from by decide +kernel] at result
  exact result

private def prefix6 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (30 : Nat) * 2 ^ (32 : Nat))
private def residue6 : Nat := 0x4b00713156fedf9abf377ac6dce8d4ecf7b3d40b4a61ed2ea1fcfe315894faf1a4619165135c9b420084a8d1decc6f2e2c215c2ab065a50703e49858af07eb6a50bb92ae9d083f75e78ac66be8bfa9d8aa5eb6afbc87a24cc1a4f879e34f2b075303da55eb406bd13c5d892f42a24c88a1078edf68af59efccff1584a3d6535fbe7cc2cd29c189739ec8ce2aa3f2254e8374573ea599ca18dfa87c7543e640dd2ca5415133c06bd44ac886ce1b94ff2961acb5375b200e68a4097160f9ab5123c80be10e50054e19b7304d38ded0e97547c9fe2fd936b5ed18a82e0aa61035d7f1ad0ca6e065a98e6eb50d2c30bd5287f0f62d1151dc17c41e8cf4de93b9665cbf431329b0cc97e9e252cb73db07d5ca43b15a95f1718a4a77bac23cb3d502aa9e0589cc6a97b93bc100c1ce2d7b3de91bc95251edde775bb8ec88a1961842c7b8e0a98edfdbd6eec8a21f2d4a45471727dccf1033de04ae9eeb8236bc84389928c88b7e041938f8677a62d35bf6cce164ead9d13d023e3c7c32526ef63aede4c09602e960b844e205034edde5e57891efc50e40ae3e1a6f1189ea91299aceef84df638f84008eaadea77e1728abefd326f3f6f4404312966f0830bc90496b08368518cc021db460b63c4efb8d7710b94984ac703196f8492dff248d32ff53cc72997884cb0d4fc19bcdb473501d98b12d66973e443ea209205dd4f158032383
private theorem part6 : 2 ^ prefix6 % Spec.Ffdh.ffdhe4096Prime = residue6 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue6)
    (e := prefix5) (a := residue5) (b := 3965510337) (n := 32)
    part5 (by decide +kernel) (by decide +kernel)
  rw [show prefix5 * 2 ^ (32 : Nat) + 3965510337 = prefix6 from by decide +kernel] at result
  exact result

private def prefix7 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (30 : Nat) * 2 ^ (0 : Nat))
private def residue7 : Nat := 0xc52d11e9df27c440cc73309099715a45fad906410b40e074bd9169bf0a23944a89ff729627862f6c1f9d0554ac552518aad3c91cded7b35831ebc292c017dfcfd31395af487c33aaecc1fcb3432d120cb118744e13b9f905cd1f6c8ea33883432df39c528341f7e228c63932b1e919a38545046d41b985b4e539c25f6b4edf4e2912cdde6f59a70f1a5db9992e8f137dafd667e251ce5cbb2abc8e1b1f50ec4d6059f380608b71846bcbf5b5c5d52d1220855112bcd04e96f046c336d120943e7344621cc6067bc8af4ae12a0d3e595f8d6bb9042db75e7f53c8e01d60e1bcaacd211e6bc0783deaf24cc390391ff6ca7800e4dbde647f51c9543643351539d4b72915c38a5a2e8f707e89d3a1b06024db8897534be90e441f74d71060c716adbba98ddb0ae50036026ad70f27a4feff0830cf0ff0e9c3069429def9576757dc56aec96c9972882c5272829302bc4b31b022a4c03bcebde6f901fc93fe35528873b5f11ef4f471424774dfb671d98284078ffde3010b1517bb3945c6b53bf0ba6fe76f8516ed39d006c62d1aefed7dd931a8aed8e7be63a4bba03d9b97455043df117d94c43f8add21798e2a3f06ee7825e3b05cb4ec9a7d5843deb91b390a495612648ad94f2b0d75bc836fe4b0d2a1281d25647137ae95effa20b5df3f41cfbb5129de70aaafb04b4d8f41a5efce30559c786aae7e4a21796fba515cd31ad7
private theorem part7 : 2 ^ prefix7 % Spec.Ffdh.ffdhe4096Prime = residue7 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue7)
    (e := prefix6) (a := residue6) (b := 3877018442) (n := 32)
    part6 (by decide +kernel) (by decide +kernel)
  rw [show prefix6 * 2 ^ (32 : Nat) + 3877018442 = prefix7 from by decide +kernel] at result
  exact result

private def prefix8 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (29 : Nat) * 2 ^ (96 : Nat))
private def residue8 : Nat := 0x409b98775edbddb1dd33a4f78828f3be38134d492ad3df534823251e4aebc66d391baa94280200ba051f900b5f9cd7762e4c5df2878464ee5c2905fd261dfc7693eb8e2a82cd1019de6bf7814063a01322306bf292d44f08b88716a7916180d3e113cea38d98f0680936d432a4d0d86334450b9bb63afc9d114bca0f37b74d2dc6438ab5537be07941ca5474885c6fd069d7a2c033d87982a3886fbf9bf9d0c456e12dbc05fecc48edfd1ff1f9c9b9ad1136e67dee3466e675c98a023939414ca33da80459266c2a37c13a09878dec2538c13bb4e390390a238d5fd85c76904fdb1b611a5983e723cfc583bca1f0256c8e73d48e88b63e5cfb2af6a8d87891df1fb6f0d15ada2d11cd231daf5a9e54e1fb4c72899d3f5ef586baf79f7dace208df79072efa29496ecb197228972c12c8a5232fc3e29d79a04ad8cea6884f083f2ffe12b91cc3a5b1f7a8b6cf1ae906b4069603458e291032bc48c43b5a621ce9f67df08558192a3cb91983cdb2b2c1593c12592f1a798ddf2959142efeb49397872de7db6fc45fe58b148cf6e9960e05eda700e5f4393bd6a9d7916f452560c3c07013c71871039c04797be66fd5a407b1901e066240b13049c01ae87665fc7fb8305cfb1c6a8693f8fd84136499d8fc40a745116c9e798ba1060da862cda4a0cd178208aa89901bd553bb353250fb6dc05f7bdfd7072a0b3efbe37bcceeacc3
private theorem part8 : 2 ^ prefix8 % Spec.Ffdh.ffdhe4096Prime = residue8 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue8)
    (e := prefix7) (a := residue7) (b := 3572538144) (n := 32)
    part7 (by decide +kernel) (by decide +kernel)
  rw [show prefix7 * 2 ^ (32 : Nat) + 3572538144 = prefix8 from by decide +kernel] at result
  exact result

private def prefix9 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (29 : Nat) * 2 ^ (64 : Nat))
private def residue9 : Nat := 0xd4fe646170e82fff3efb8864324a815de1c8bbc4be2dc89f1e02ea7cfb362cdda10e1cdd9db90ce2953ef83a7c0c6827894d78dcab4e8f2d83760b6e147e81b374810440556e694f52690c37cd084a3ba84450305a52bfc008baf01135bd033555867412211ef64235c4b5cfee965c90056b56ec068c93d9e1bf3da445dd1b66bdbee15c5d3c1f862ba37d2ce7c2cf246a46108bf593f13e8f30598986441d8456c9c26e1417707c431c5f62dcc4283b1743e46595517a7d527cc41816de7de0e89b14e490f5c1f0e4200a734a10eef98dec689947cc03caa00440d6e13360f75069aed2c01258f67e6c06aec60150cdc68005239e35ee73ab8a05b40fce4eb9766b5a0561643bf6008360299b17e79a2c4abbbf9a438639f127ef4962b9aec6744318a3f526bac758ad9991a8f5826f4f9a6ac51569670397d5306c8dd7eccedf488abb6ca2c5efb9b7f36d381d952c44b9ffffd101df98587c9270606ac1097e73ddb1b9a0a3a0c04739b6285b68f74180a9d16b7e6768065ee714ea127c13161776b91191e56bdca156c0a14bc7d541cd88bcfd46a8acfbaf458cb17fa31698e914f779ff45dfb1e0906919a72bc294e8f24b10c610f71c8c8c3e79955cb6d63f1728f26d75bb268b7bb1c081883658bf92a9dc01509fd86141aee4cf0ce16a6e60e9f18eaa450ea095c0d935fe4f2f916d08cdc5f046db4ace7f4d93b4bc
private theorem part9 : 2 ^ prefix9 % Spec.Ffdh.ffdhe4096Prime = residue9 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue9)
    (e := prefix8) (a := residue8) (b := 2318539261) (n := 32)
    part8 (by decide +kernel) (by decide +kernel)
  rw [show prefix8 * 2 ^ (32 : Nat) + 2318539261 = prefix9 from by decide +kernel] at result
  exact result

private def prefix10 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (29 : Nat) * 2 ^ (32 : Nat))
private def residue10 : Nat := 0xd70d68aa58d0ee4f29d8cb55b59f8a330bcf0967ac9272449251c0f53e3969246165cafcc84b2a8bd7020c6e20e749af8528387334526d4bb3ce40cf347503c6e2c15523953d4c38d4fe38647d804984021c7fdcd35160c07290ebc79b6b62df36087c2a6847e5c388469f94289bb8641af161fe85c9a377cabe18b49fc40f7619532afdccabdfc910224a53723bb5ca408e352e9161362eefec70b99d24b626ad751e7775d3b9eb39846ab1859a24c692bdbc5a2a2d428ce638ece4cc75a229295c4e03804aaf463153450cd5ba9b25c36cb85880265d86fa5ba1368c819c2d995ab1351c4508d3ea78fcf970966dfdea8a96132d786d120dd6f3b65971145c5755e3ea1d0d04170036f274cb629bfe448b9f74fff3f52dc64827fde82fb1f483975a082fec44262d34b52802218fc33b71e6c917e02b0b35b4b47290ef3e8222c30934f064a962b3335bbf9b4b9ef077b0cad898de52c3672e0b0de44d7c591f4e6ad02f84a8642f381a62ed70b7645f7c9311c6eccd45c9d432bef68971730253954f9cb020c3c3ac98ebd75a6aa538db1fa2cc1ef80716b438069c728a2220ff4706d3bc50051d635f784de3c9fdf39167cae81dd9ced4838086f61eac140676a8d5722a9c44ecb08656204965d48825b83e3a20345f8bc9ca341168c8f52dbc5490e0160f3191bc9986e450d2e6b4916fad95aee43493175c7564bec23e
private theorem part10 : 2 ^ prefix10 % Spec.Ffdh.ffdhe4096Prime = residue10 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue10)
    (e := prefix9) (a := residue9) (b := 3863596775) (n := 32)
    part9 (by decide +kernel) (by decide +kernel)
  rw [show prefix9 * 2 ^ (32 : Nat) + 3863596775 = prefix10 from by decide +kernel] at result
  exact result

private def prefix11 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (29 : Nat) * 2 ^ (0 : Nat))
private def residue11 : Nat := 0xa41eb87cbc7c5ff41a0e3c6ba934f969a0ea7fa624f75b0c755cd75f5206f5cf19c8e5c5f6e96105057efaad1e08947bb2b60a4a31926b73137b62fd0dfcd88c62bbc96b7cd0096f505014c39254419909fb63fc2734b5187a42b48c34e80b1f1cc2c34d50993345e3b3936ff9d7846f261fdc5810d53b2bd27e255c4631b47fd9cd0b87b85e7592ea7755703a66a8c3364920cc73e7a4033df56c2aa40a866819fcd851988c4526bb183403fb784116d8b1c67eeb7d077ee91784bfde4ed913a85a589bfe61a9610fa66e28f903d2af7b1de7b198e1745ebc3ce91d057a8e46ec94a93b011ea90947fe8035bafca2d80ba995fdedc3eff17d8bb669587499b2615b378a1d2f10662f7ec5acabd2c3faceaee067f6e1b9300da20568f89c8efa2a82e47a740c6689173ac000f9761ff28be3410849d5849d50670c99f7f3085d36cea60a8a557f9f2107e2c7b8bc51eae83f8c07445422160b040caf9c7522fd7bc93c8a88c6b8477358811baf6746c53f5ee4479514286f89b7ba3c6583717bf27ccea5e06bf2c0e81171a4d33645acd7dbb1a52e26390358de4b11de34fd13dd171288ee71ad5600c09571be4f908754e9e05eb57c4de3f1a918838cc16e1e6ef13cf93e23fb48e687ed2734dbf480c6ed405a7156ece86d0c8130904ab1df17c6e678ca5b8a7f9358bfab48c8e2ae66365eaec5e96ffee63540f85d743b63
private theorem part11 : 2 ^ prefix11 % Spec.Ffdh.ffdhe4096Prime = residue11 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue11)
    (e := prefix10) (a := residue10) (b := 307076988) (n := 32)
    part10 (by decide +kernel) (by decide +kernel)
  rw [show prefix10 * 2 ^ (32 : Nat) + 307076988 = prefix11 from by decide +kernel] at result
  exact result

private def prefix12 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (28 : Nat) * 2 ^ (96 : Nat))
private def residue12 : Nat := 0x7435f5047124c67865f472522daf5a7876b2ecc1a9d84680b7e6928fa9aa79870b458973b9c84f9b17c1c353e47a0f7afe34b3b874514c89cc3d814b22373ec26fe8c9708ef552c1c0db00fbace739ad261e33342da4401247b4e6bc9b2335e4b2a38ec1a3b20f65d6bc7df85c98ba83daa893a59a062602d7a5004cb2cad090f54399a046e69c9fbcc8d3008e229a00ddc90ac94c3da8523ddbfe24671ccfd591e5634252278302e03ec6aeb512097529ec9d33e1816509f0ab48a5f5ad8325284be5f27a05851b03708aeb00d261fd8d97eea4bc9ca6cac4062c907564ef840ec62906daa285c1358388c18fce2fca4fe6fd30e6662e7c5d06cf726ea55805ed9753bb2914ab6fd58bf38c1a25ba9521395f4edc49fde02c1144654f70180ec0ae1cb79041c84f32fc562d935eed605501fdef7729de7ae8f80ec040599140115e6dba875f303ee0731216be86a701780c83bb707aac983b6093b8b1955878bbcd2a12c432341afe364dcdf563d48c78438e90f15e052e87a861ea802c9cfb1faf1173dae6bcfa55fb7012195fc35b6cf183e7fa84f8fccf56bd379ba33776378bfac0c3079ca096125a236543aeb458955762293d925de17a69ed12a8b564e5be7001edf00cba72bf8498273d805c43b5bbba6dc6ccf9306909cae65ce9e6bf95681d5a996c2c1568a290f1c191d6ae9defd53821440a6d3f097d1e8100ea
private theorem part12 : 2 ^ prefix12 % Spec.Ffdh.ffdhe4096Prime = residue12 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue12)
    (e := prefix11) (a := residue11) (b := 3197628849) (n := 32)
    part11 (by decide +kernel) (by decide +kernel)
  rw [show prefix11 * 2 ^ (32 : Nat) + 3197628849 = prefix12 from by decide +kernel] at result
  exact result

private def prefix13 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (28 : Nat) * 2 ^ (64 : Nat))
private def residue13 : Nat := 0x62f1269802f6432c4b3d01ef8d85528563520ff7effe984f94b8ba2b650f3a7a37c38ebc2db58529bfe2a1a98b7f2d611f3ad1ce1793a5b3f7a17067c08dc9fc3162c92c5abbad8488797b496db7631b644d80c91684548bad6fb18011c53105f4ac0f7f048df7948dc86dc782579171daa6cd0a064ab0c097c88456e145460cc9e0ea7e0032cc08625fdd0f491bb0fc9c89ecfc99e881781a6d2a3c816f3eb189f0741f78976f95af06987e50916e929f65ab0ab95dcdfc24ee2b7075e61881d92029acf7587db11c999726cf220f15b0f136c95705c797b7fe3b9fa3347a0356eed2be8d2e9ad05184aca3736ff3c7029f700bc30dd59ccd42d8be8ad3301cfa4ec2fee02210fb69c84ad4fcfe26c3dc4407be35906802c894d789340663b8a55ed357e016f311e84fcc0dec40eb48804f16162843dd299e36b27012e4d8050de1d149a17892a8219a4f7aab6f6d322fe07b60be69e8d9a5ce2e62ae70609071ae951176619d6bc485831fb82c7e0d65b28a1569ae7221a81f347ed3eeaf1cf1726b83802af55665ad61504fe8e33748b1859f39d985b5848f8bfbd787b70401b58bfe4b971a28144d75a186a58e9f9a8d084c3891afb328ba8dfe352c1e4ddbdc4f77320f773dc44bfbb77c5b5a6f804a92dd0287025f419827487ebe9197e388dd36bcec60e79bcbecc7457ed259c574011a1d47109dd72c978508dc363a
private theorem part13 : 2 ^ prefix13 % Spec.Ffdh.ffdhe4096Prime = residue13 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue13)
    (e := prefix12) (a := residue12) (b := 2978364140) (n := 32)
    part12 (by decide +kernel) (by decide +kernel)
  rw [show prefix12 * 2 ^ (32 : Nat) + 2978364140 = prefix13 from by decide +kernel] at result
  exact result

private def prefix14 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (28 : Nat) * 2 ^ (32 : Nat))
private def residue14 : Nat := 0xef9039253846c25863eb98e3e283b1e803a2426a75e08ab8fe3e732ff3b91afe90e53181a00030785eadf235180338b302d3bd6aaecc3cb3861eb1a897820a42ca8f7df002856d2469b7b2cae2bd2e274f05288c3ce4651e60d7dce38e933870f4bf5bb94ed6e5e0d4029299be5aca0b3bb1869a3e60c174706e6ca760c82e9961f6c1ee5f88b62d9ff16097c7d68e1691aa10531489a50198f5a2bf8379d177862346e3afa7de00a8909813f1262b48b8c1ab6ffaa408b85dc7fbfa59f94abdabe7e6549bf2fa5e13e851ad7f3533730dafc3a76a8266cd576053d4e2dc65021b68568621e51b269ef70e6c6715b423857e008fa77b4ea975925bd839d20776a90e57f549edccf5c28962ada1515f632604c76339016ea056c3eed027ba2aad060d43d235c5bffb7241e142f3dc38ce8af42383f1d742fa88ed20e69ec2090f8c2f3d48ed4c5eed24975dda8869bfbed5c9b5f62fcf781ebee5d16077edfbc43501339e14fb8bd5081e25a127fd4d324253bfe76320e522f11b4db7d3f7c800fcc9638e4cfbc02454cd7a3e1b376251f41a2620a8fc6cce36c2a70af5aaf3eb5ef62256c7dfc309cc18c22a8fbae9b56227a1fdcba6ad2acf889f43ead0237d2ab47aef8ec89759475a906059950386a1af5b8c5add422b5a8e739624c7657688162429e6a41a622f1ce6bc35ee7f70899dad5100c6687a2ab61643f4e398e8
private theorem part14 : 2 ^ prefix14 % Spec.Ffdh.ffdhe4096Prime = residue14 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue14)
    (e := prefix13) (a := residue13) (b := 2067847425) (n := 32)
    part13 (by decide +kernel) (by decide +kernel)
  rw [show prefix13 * 2 ^ (32 : Nat) + 2067847425 = prefix14 from by decide +kernel] at result
  exact result

private def prefix15 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (28 : Nat) * 2 ^ (0 : Nat))
private def residue15 : Nat := 0xb53b70ab775f7fe434b63b02b9163b09a035174e6254dfa5704704ab74d1faa1cec418a3dba4c9c33ca25af1cf30fc857e2a3a747aae09e7815b8a0e9ce7793bcd7e30fc8d7938d7391c1f255a70f5ed9f8bd513575655cd06f23c2f42900e4c98b4fcfac646b7bb2773994b898b4750f0105b6fa1a584d2a168b500bedd30daed874fc3bfa23445c8cb85268d22a1a58f833004023d11cf4b800cb8aa4f43385b34ce0dfa1d46b6de127424e90a680d86c8a369bc844859877b38fafe9bc9e3488723c7135d8aba15abc9e350e83185e31de8ec60eea6f238173dae02cdb97dac8fcac9988a46d643969787aa35c6fa082cfadb8f56f49d61f82375e4dba6dfc366994c67a625a35bda01359b5815c1c2e5352b80b35a6f1fdc9fa038f701905d040f3109e86da181ca7c2e4deb9e2a47af80abf0a0ee9cef08a89b8927e2e72c744ee88c1e4ae4ee3f7dba14667c4c1895ac85107815ed70e746b6777d459658717ced5f6126aa6910dfe28236acc77da43831e68b33adf29842b87783b513388422004b1cdb64f33d6546d496734699a6999a5daa7c02bc429bd476b92c1646a0c3de27ea0da67f656ac9f3692ad97ceef57333eceac4d98f71e8b9a567a093594df83f1f7decb367e1c5654ff50fcb09c88e2ca09c0779a1a4479c6c0bcdd95ecae72622764792cd0f6af42f33345a377fee7d6b875d6159c6e9997f937d
private theorem part15 : 2 ^ prefix15 % Spec.Ffdh.ffdhe4096Prime = residue15 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue15)
    (e := prefix14) (a := residue14) (b := 1466052797) (n := 32)
    part14 (by decide +kernel) (by decide +kernel)
  rw [show prefix14 * 2 ^ (32 : Nat) + 1466052797 = prefix15 from by decide +kernel] at result
  exact result

private def prefix16 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (27 : Nat) * 2 ^ (96 : Nat))
private def residue16 : Nat := 0xb5c932113edecfb200123f06c1030ada78154556b56c5eba04cf09ee49b697d47ed35d73d56c1eb8d3b335ee6b8589ce8d7c1a1cd0a7fe5570709defadf281dfa757971ddd08998f05349e94decd7dbd79c04e4628b022ae213520d0e695348c8af54cedfc281fd5f23c732da093bb3147a350c5cece260711312e957bc5daab966760b5dbc62f48ce0019b4147059cea5e1c3943cd1deeccd24dd547908e4f847595e57e159e9f9b17daebb8f1c16070d7e3b821c26de180a2cdf059135f564a66c6846f712583aa80de17cd10797816a608f0bd664933162e62c7155fc1ce0a73f829b2540a35325bac5ef533db27ae147569a92ce14325067dff5cbdb066a91769502a992dc50efd9b0f6348af6b88c9ed186e24099f726c4165d5a725f8a97852020a53169b42621d18b2add76f149be785b6e20285804e62570e9ce0310ff193db1cce79c9185c0ac2fe9d160182e320286656a6613f1c69a440966e2c9052a0469c13e052f030369756f21759c0629e7d141885d03a7f530591f8eebe0143ebb5c74d3e13b5bb0a6fcddf7ee8d0578e7c7546c56ab39e2844da04decd4d769ac896b7c18d9d5988b97ee4214be98fe60c5c74adc62baa0bbe595a247274c1087b2cea2d53ccfcd35a8d168ee3782398620bf1b98a6c2412c4cba57e630dda4fd29ccc6b5f0957c3e916d69c78b869445581e3001de5490cd0226b52dd2
private theorem part16 : 2 ^ prefix16 % Spec.Ffdh.ffdhe4096Prime = residue16 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue16)
    (e := prefix15) (a := residue15) (b := 1777307498) (n := 32)
    part15 (by decide +kernel) (by decide +kernel)
  rw [show prefix15 * 2 ^ (32 : Nat) + 1777307498 = prefix16 from by decide +kernel] at result
  exact result

private def prefix17 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (27 : Nat) * 2 ^ (64 : Nat))
private def residue17 : Nat := 0x3e469fb6fb72bf2d18ea74d946fbb7a73cfd8c1d629cdbebdf60e0c7c526614a215f1fff1bd7fc0cfb2a06536c7916be8dd5c78d63953770d04138b6bb2a85b06f42c5c9f565f4df8a4a15caebb270bbe6fa951c6b242dfacadbd361d43499c2496af34d920ece5704d5e90b0abf982e973b88d93e11e923c87a048608c6d80d61e094057ea8665d364594772e162f7afe4df4b6c1f733b38f2a906d7eaac55e5e694d5bae2b035c1a32958defd509a57bd5c35f938deb16ea36bd735b679462ed9a98cc3638e4062904fd1c765b82974af5d294ffa266a11d7e45bdee7ca6d6cd2d528fc0a3ddb6e1bdf00795723f487161a1f0360cfa8d97ddfb2dcdc462b6641f819d566c07eed251dc9ce5f0feae0dd28c55a136a1161495300235696a584dab4da3d6c6df8583285f484160819f27fbb08942f0935e4039e927929bc3e4f0ca70f3a74297bfb28d58e9bf461b7ff8a9a93d25310cb8503a108840ffddf5db2023fee3b47fc2a472b03d801bf84343a6399bd29b51d8fc617a35e918be7613f7be0caa1721325d4de2277afcfe49ff7e94f586026fdc742e4e2be155b79f59b2cf50c1b6d860953c0ba2d953b7e3ff62a876e2d8e260a19a67583c49cb7d6e60601dbe9611302108b0a26c9df62b51627ae4ac834713291b1490268e6fc55a355e0fc1359087982f008505b4bc9a4915c918eaea7d55dbd1dbc8bcc08054
private theorem part17 : 2 ^ prefix17 % Spec.Ffdh.ffdhe4096Prime = residue17 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue17)
    (e := prefix16) (a := residue16) (b := 3942560432) (n := 32)
    part16 (by decide +kernel) (by decide +kernel)
  rw [show prefix16 * 2 ^ (32 : Nat) + 3942560432 = prefix17 from by decide +kernel] at result
  exact result

private def prefix18 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (27 : Nat) * 2 ^ (32 : Nat))
private def residue18 : Nat := 0x238bdfc485eb55c77ba3c1eb54e8199dbd436e39ac211c0ebdde7c56ca58ddcae4a7ae5cfecbfca19ee73e4dc3d2b70377827f7c6c0acd5cbca931c2c9a1a1439323a586acace534a7ed4bbac9a3989e202d0c3842d827983a5a2e348c93aa9929d5d19391c1521c97ee174d176f7ca15471fa00224888113cc0c4726541a42aa40308915e85f7fc776854831de3f9c97288a7f08541c6e578e6ce091221429a7c5047c4f9639873793c6f780e3f213ce442504b496e9f3f2a6953f788ee94856107d956b91bfd4d2fbd47b96ab505c119e721e1441400fa8f77813bdfe93e2de0c105a5dda5c98db1437ebc249e46f67c5709fc88cf3912cc4a3e2610715839a7c5c42cfebcedd550481f49ee49c185c39074564a28979614008ec980ab1e841b7325db6360e4d99aa65b0a4c728f91f7b809ed3e64ca797b188b924b2cab3fdb92b86960a8638d2c0e2f67c19ea7ea473b8a1e4ae08441e3dd67a7d77046035dbdb07a13548975fa50860bc70bb3313eddc914019c37347c9fbcca079261b59d72632b77aaed4971f51f8d0eba39e96a421c0e585a918e0f020040ac8bd46ed9a109098f58bb03d163b96ef4317764db3742f43a9b72c838bc95510331005493ffbd20d1c5aebcb81d4dd9a5be5993070b809615e14b648d8ff4bed106b81f41e9abd5b66d344b4b5a9e8cb9df019873b992401d13c620d0346a25d7dadf99
private theorem part18 : 2 ^ prefix18 % Spec.Ffdh.ffdhe4096Prime = residue18 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue18)
    (e := prefix17) (a := residue17) (b := 2451176079) (n := 32)
    part17 (by decide +kernel) (by decide +kernel)
  rw [show prefix17 * 2 ^ (32 : Nat) + 2451176079 = prefix18 from by decide +kernel] at result
  exact result

private def prefix19 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (27 : Nat) * 2 ^ (0 : Nat))
private def residue19 : Nat := 0xefa1e910cb8abe4b6b10c395c085f12904f6101d2c955cecd173f7017b1941a1eacb70c456633dd42067406fea7203f59e94ba215c4b17295641e3cc0ff07445604956421ad6169494c67256cb43e61a941b213c59d48e43f1d00faacec2560121fa756137b3b9c1b99153493fd0de524a20915332911dcdc117686555bf40b7799506e8d7217f3088d9c40d0bea4f1764f7b07a68d979c9923ed2628112472fd41fa9d2d52f2a73395289fe26a4742849239effa40bac4ada702e470fe5ee81aa0bee108d53d6dabff08fb4b2e80a42b216e3ed193ed8c9b314bcc819c457af62711d88d1ca66bc08db33f731434ce9a69230e1a9e8a8fbbdb4d9ccff6f23642e53b161ce6ec477908eab501c5fc413ce5fb2d80553e43e6f09a4fa55589a5672ec3dc1fcf8a0ed93a52d82924b16ada58feb4830723c099d3288526a3392105ac5aefd3b632b9f0bb64a02a4ec0fafbd8af0c02144494b5408fc66416348a5bd7127c74ad3bc6b8ec000882e8de85ebd7d4006f039bb05933dca9bb4cd1a6196a3eaec073b99920f543655abe30163b611b5ae0966ba4e6510c57210d70059976ef3d6fe17ae33a97b328b91eab9b3e0433e6183c9315270b3b8456d9552ea264695bc6557278e127bee44ede294c220f9103f81fdfe00c9d4cd57ca688a4ae23338c1625183b296ca8af9082bb00baf2863466f0e93c4a86a5cc2d543b984
private theorem part19 : 2 ^ prefix19 % Spec.Ffdh.ffdhe4096Prime = residue19 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue19)
    (e := prefix18) (a := residue18) (b := 2944612200) (n := 32)
    part18 (by decide +kernel) (by decide +kernel)
  rw [show prefix18 * 2 ^ (32 : Nat) + 2944612200 = prefix19 from by decide +kernel] at result
  exact result

private def prefix20 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (26 : Nat) * 2 ^ (96 : Nat))
private def residue20 : Nat := 0xbab947f2b7a17f7aae8a0ecff5b68e4e7080b9f6f6dde9cc1f2ea6566dee03f6d96a2eaac427c98a5f2d6e879172ada3ec9ae4401e189ecd73f77fd1009a862102705e6c38c054b33f0c6c7541aab08060b30f7035da01945188641e082daa2af1b03f337a725a0ad8b67f600bcda47e10cd961e318f5568283ad419a2ad65c1b45ff181cda1ca22359fc3a4572ad18ae6b20cf9d821f4b7f20875674f30dd3faa95b3d95270250e74dd667a93fecd17780b189a9ab81144ae8880dc9eb19c083a6d9d5c607645a540c135ec8cc3ee84856d55163cc98f5306b9a70a706ce419bdf10be23e9399f156b371cf852fcbdf5316982145a71f664cda8c9c85217bb360cb1e067c1e6fe33c1f6bd3227892bd65ac5a4bf2f8a2c275d93cb6419cd386cce9c8812dde6185bf455a43b6f3594e5749f04305d794f515e0d16f1ed38dfdb07b1be1388d2647ff3102437dbb8b937383e967eb3712adf69dab702ec4a0768b5ddabe115be3899bb6f32649d86353a13c14465a5bfea5e0bb2c30009e620d51569d52a91bc417c0ea33d68229d8a751c7b426a9d9e1d8a5a006c079a8730c5508eabf388768ce4698f4ff28fb4bade9ed23de83c90d6bd2f311ed45d74ec024f4c4a0584cbed989f9dd002b8b9c0610415aa4cabab72b4e650d80a654f7bade3e2b679c546ebdf539af4322f3c5a2464648f904e5bc2c38f26ba97ebd89a1
private theorem part20 : 2 ^ prefix20 % Spec.Ffdh.ffdhe4096Prime = residue20 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue20)
    (e := prefix19) (a := residue19) (b := 1118941866) (n := 32)
    part19 (by decide +kernel) (by decide +kernel)
  rw [show prefix19 * 2 ^ (32 : Nat) + 1118941866 = prefix20 from by decide +kernel] at result
  exact result

private def prefix21 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (26 : Nat) * 2 ^ (64 : Nat))
private def residue21 : Nat := 0x9e84f82ce87da487626f8951fd54c6f02131be3227cbfb6c4def867dc417bde1759b44babe9ff92b82c736d23be1fb75a7db129d6527f22c0df5d6f73d3b253e15f27dc3a36f590da458c5af78612f1b104c67aca2136726c6ad45a6e24a8fdd5a184580f6c6d7f673accb5cbb72e537c7365766f42d30460166716cbf00e3c38972d3cc087d30a97378958de8ceb4499804c30140aee32baa17de331da850682c83b2c1bb351ddc03bc83a2663ee6bef76510ccf1a99a1f81d24d8266ae3cd1759f8ab2905b9cfd9b0b50821208fce9ebcc1477e1cda94194375cf4a08e7267d61ab2e51bfa62e48de6e0d2aa11c777af8031edc49c11accd94e847dbda1093ebe1538b95f243c91c42d2fd625f20dd26245654c327de43852bacfaca12f1f9170df309d633c94983073a8ad821d4206822517efd8152ba2f73bdee477d2a81c6f761822521b3678567f0e9a75129afb493e3ccbd708472f4ca48141b9a2c37f1382f6b5525cc42fa68b81570f73915043122cc193c68dc33494f19ace55c534dda1b19aab2ed7b2f9125dcb9de07704ba15b234bdacaeeebde603527d2fcccfb16d783c386d1f5f521126ecb64b20f029f5cee67be526bb33ad346b7508b06933eb0ac7285739762863b2335dea95bf316667c46f564a06e6492c91692b35ab3215021dbe9f091fc67e0fa53e8af7ab7c569a81ca515c682907335042b037b
private theorem part21 : 2 ^ prefix21 % Spec.Ffdh.ffdhe4096Prime = residue21 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue21)
    (e := prefix20) (a := residue20) (b := 2666958201) (n := 32)
    part20 (by decide +kernel) (by decide +kernel)
  rw [show prefix20 * 2 ^ (32 : Nat) + 2666958201 = prefix21 from by decide +kernel] at result
  exact result

private def prefix22 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (26 : Nat) * 2 ^ (32 : Nat))
private def residue22 : Nat := 0xbd1ea655b8c3b832041ced3682db896eddfdee7a8dc04640003d2d1998e29e58f585262366398f4161fa57a9acbbe36ed50f0b2df625bb3b3a908935ab196ff6692814c185f2e87d316ef2d723d4faa0e63cf1210aab33b2088d8db905a957b10761392e2c9706c1d0a89b4c5b9ad0c5485ef58764e765095be67d94d0fdefa74d134b16d720f14bef91c8a4d693ddca3a02adc0d6c8ad1140c1d5bc92a890259be748c35e2ad8e23243c4759413458b32536302efce6c38ca9546b6776f3a59e61567bf43c9e063f114c6525eb21acaa7cb534dc4acff75b139be7f37c273a4d317ec6d039cdad562faa6261167db7850919741390c0b994dc69dd2d59f09d548db0487ef851717c9d1675272543d79330d827f6b80587092ca4a8852b37d3c6fb469a54906315b96a403329dad7742ac31514fa31cad3b3f41bcb5a50b2a17d95505865c69381d8987dae144009ad4ab264b4b455bf26dd927ae7d2fbc8c65b747ab9cfe03e8a2399560db9e856d5173ea5cd9356bcc941544ec6c12b8144c0efcb025e85fc566ccf8b56dbae32d3284dd6e2f6cd22db27afa24ef6a0360ac38cc17e832ffc783b9855e17e5cfa511ba88dfb26e1947621a94e0d80ab3e8bd7b08e2bfec3a9f80ba087e0e6eefb9d07736c1b161c725cea44a927057541a078dc1a50e59108349bb9db94e321fb619db4099725bf4e4d226ed5d984efc6325
private theorem part22 : 2 ^ prefix22 % Spec.Ffdh.ffdhe4096Prime = residue22 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue22)
    (e := prefix21) (a := residue21) (b := 3668674991) (n := 32)
    part21 (by decide +kernel) (by decide +kernel)
  rw [show prefix21 * 2 ^ (32 : Nat) + 3668674991 = prefix22 from by decide +kernel] at result
  exact result

private def prefix23 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (26 : Nat) * 2 ^ (0 : Nat))
private def residue23 : Nat := 0xf241c7a579b605f646e301716f13bbfe60faaae6c9b5f635e4f702b643026a83f93babe82d9975fa97026ba43eb2b3f870d384c635c005c8ff7e17f54c517c82b31e078813719aab360a7b001fc01421315f91d891065911f21eefec041b54da6849a8300fbad907c7963bfef320d593ba7f7afdb2fa879bf36673a80a9065f6aeec1ac8098bd6ef64a6fb12d4cfe830521ab07e1fb0caa2d98839df57d871e746224b3c67784aada977d90e4b3e69fb189e306f890e8c20257d6bbeb9e8f0975bb45628839d1515e53aec858f95b35d6a7708e8de0ed307fce7fb7dec1d3f8ae4a17ef559b20e5739d1d6a1bc1d86f690043cf96b5527213ce1f8f6f0bbc34a0c7bf50f991c583c230a52286d4b86e650233630591aac4352f939e72caecdc6cba551b30275ea704cdd1db8c8de80e9065092aaddedc5fec5b52a2bbfa0d8305f956508581de51ec33ac8094facdb6938dd2e61ee2cfac2d3fef1fb4cce7b55e3a4f2e9a92d8942d7693dd36233842b719bd0c034b868db2ca184f3b7f5238fc2383aeab225e03471914147c3467d053b7cf28c059483cc75da3f178c6c95d819ae1d0c016bf6e03fc09be8bcc10d61fa471b66666dfe86f317ff07b1b86e21fb6164b225285c147cfac699830f28648021e2e150d4ace17f4ecad5e44a2055543df87aae0ee78112faed4cbc7a16489bbd1b816767dd4f96faf6b1798999e1
private theorem part23 : 2 ^ prefix23 % Spec.Ffdh.ffdhe4096Prime = residue23 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue23)
    (e := prefix22) (a := residue22) (b := 1068229786) (n := 32)
    part22 (by decide +kernel) (by decide +kernel)
  rw [show prefix22 * 2 ^ (32 : Nat) + 1068229786 = prefix23 from by decide +kernel] at result
  exact result

private def prefix24 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (25 : Nat) * 2 ^ (96 : Nat))
private def residue24 : Nat := 0x822121a65a6da40b00143b31871aa869fa8bbe14d4b4e5e1197ba7a42b0c4e2fc8b722f413255f88c9e18982aafd9d949f08984acf79ba3f5438f66c57c08d2cae698d97d2ef0d93274fa5d208f72e642f1306fe49ae4c19ff37a400e9326fd27fb1db3caf6d171dae31deb73f996fa6ed21e4d2c18d1d6cfdc280fe2fb2cb6cc19a867aec393129478f567eedecf458954f68d0ab6392c107fb33ab29d10c0d64e60949d14e27a2f0a9907b5b8d6de408b01ca5745a2221eb349d54c9dc0e99cebd9b198adcbdc84b91f4d470550429fa279735e4aefb1e7534646bc019f37983f36f1a30245d0228280d1d11c360ac0194516442a7b32334bdd7faf903e733a4dc5a6f36baeecb228eabe96980711c65bc567e89f1f0e894a77836388b271af934b81408e7c9aba03b79cea6d82f389f00d9da28d319dab8160d2d15dfd32b88628b6cfe5ff05ed532f83647778d5ea6a8d0b4b22948b959bbe36e2666d6434f80f3d313b8df95c4a74f26960132c94598429cc8d201c20d7de684ca01511dd428595ecd9e5789ccc69383d3b6a929dad290bc420b199cfb414799ae98955b4500fe1f80a9f8e629bb7c4a7875919a786b073a15dc7b65b9259cd4c26ce6a318d4fcbed8a6dcf25745ba4da644bd4d5d926e3b7ab7e5852693ae3b6bedfbb5eea9cfefafaa2825497fd3aaf801e4e3c969d9858bb0228b7420692b71f497ff
private theorem part24 : 2 ^ prefix24 % Spec.Ffdh.ffdhe4096Prime = residue24 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue24)
    (e := prefix23) (a := residue23) (b := 3425142328) (n := 32)
    part23 (by decide +kernel) (by decide +kernel)
  rw [show prefix23 * 2 ^ (32 : Nat) + 3425142328 = prefix24 from by decide +kernel] at result
  exact result

private def prefix25 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (25 : Nat) * 2 ^ (64 : Nat))
private def residue25 : Nat := 0x72b2d7947ca7a6c96c8533198832e4c43ab8aeefbdebe73a027937e7f3e18dc580237012891dc034da25937b38f721c3a6520d529f4410cae4d357cf07066773009d149f6f379f5bc61ce51e1c33ba0a4067aa8e7c767cf461964438b99388e8aa5ead35c0b609a53f7c3111b313a4258a579ce1990b793757d6a89e52cc47d679fe09cd34226128a03fbf24e7eb71320349a64e702ea9bf3cc57a160d1648ba7e990e9c28bc0576e2567e32a93f9888c83703f74e55489617fcd2f0568814a6790afa4a68978b80762fde066b19a87f8aa7d1934dd89505e290239170bca9847e05e7352db0aae2b5f2f00d47469adbda54125bc043dd6f363823f27469b01a4f30746a71296b6d24c8b73f44a68d07779793292d02c534e7792bf2938a81a76166200fd8db3644d1b5dd980d9b449a4fc3951e58b31430bacc17ba9b2051f93bf25ae436cd493bd75cc8840ea7a7c61bf301148dd1e11e41871f6ba140a5e0b8dad3513a95a7e784679f65f4a81a06932376317ce9677c16d8007728ae48c1b1db602e2dff1cb12adf0f72c306dd49b969e9998819b0dcbe68ad1159f744c2d319f436ddb872e650a0555cbe28085fee5fbc67d81aa2fa6430e217bd4bd2b4bb1cb3eb84648b6e3d2541d15f461b58380810bc537c1f19fa9dab5b79eebc628dbe88fb610fcc4fa2b076f020f9e8b6fc20c17b20ec09978800ebf7b0d07499
private theorem part25 : 2 ^ prefix25 % Spec.Ffdh.ffdhe4096Prime = residue25 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue25)
    (e := prefix24) (a := residue24) (b := 1886602683) (n := 32)
    part24 (by decide +kernel) (by decide +kernel)
  rw [show prefix24 * 2 ^ (32 : Nat) + 1886602683 = prefix25 from by decide +kernel] at result
  exact result

private def prefix26 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (25 : Nat) * 2 ^ (32 : Nat))
private def residue26 : Nat := 0xe90cdccfdf159fced38bf800a902c55dec50d88a595bdc35509fe3881c4e62c0d45077742b19cdeee2c1e201ae883ae57470f3a679b62328d07940a0efa4e3a4015cf84cce11a11382628d0e5c23b332df50cac7d306d8f3523048091db02c79cc9e5e2ac2802789b9a23dc7e87aa4babc9d8ec172f000661c755a98d962da32d47a4a9c9c98b5481f51b6430da57e091219eb861e557b6b142a9ba85bda4470d973a6fbda35b4d0a500c95b8308ed375018d42313d2681e927017f5c10ec21fbf17d54bdee08fdf8f4cc1dcf8b355dfbd6fa502daa2cbbd132d9584a1e48a241d95b227285ffc79c39597dc84cf26cd7971c0449054ce69bbbefd4dd61d4a7c8c53c52795db9c6e4d7e61a60a925dfc0abe1a8371c7a454325cb8f039240590562f670d878e96b0812c0b8f09d467e363abd2ce16603ce50bc2cfd975b7f9a11be0448d1c3fd8e4a1b1cd6d46a7b95d5fbf73041081cd02f6e376c7474be31d8d42a0425efa79147c339766926c2f344201daab8a6e03aa413671040b99f736bda0d6af1f7167a7f930f932ff5a7815041f2e78142003cf418506d3ff0acf2741271a0f989854334b021f9e556cb6cc7fd3756bd0e4ccaeedb06e47df61db9b2c08e5b5ae1bdf1c303ffe67af4445fb83f99cc16415babb5be08e1792c5483464d0d7057df842b4e8d7c8f4f3a5fdded0d6a9747a6086a0bc81e3ee7078bba2
private theorem part26 : 2 ^ prefix26 % Spec.Ffdh.ffdhe4096Prime = residue26 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue26)
    (e := prefix25) (a := residue25) (b := 4048766189) (n := 32)
    part25 (by decide +kernel) (by decide +kernel)
  rw [show prefix25 * 2 ^ (32 : Nat) + 4048766189 = prefix26 from by decide +kernel] at result
  exact result

private def prefix27 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (25 : Nat) * 2 ^ (0 : Nat))
private def residue27 : Nat := 0xc91e4aaf6c3a0a111161f9826d17a6bdcc36328b85ac1b92661d5d30e17408297505f2f11f0d26fc69cca18fa7e108ea552de700a7dcc7e3420e1964551da7d668b18885bd620b8efee90539cd3eef0b4e0f88cc9f2cc2c0a5a95d5508d2a4ba9ebbbf4b125ff3306626adee1aa8f19b620f0564768425ddd491240c3b43bdebef370662aa90eab0b1195ec48b4e2e95847da83be8d0fd7fc0e9fb0cfd799c6fd85990364f166636965bb6752c3c739710f22d3f7029b219432f14429a33cdb33139e449389d079e86d6802ba3ca684472b07c209ae9fbf45dbd2e7838c5865d90fa0e752d7d2e330ad55ca17159b1e1bd082b60646da9bb6dc853497db619ab38c37e60d58ea19e731a1bdf63c278b95f9b0dfd48d58c82fd6e29d9bc3518d502581e4da4de7c6a81e2adbae3573ab934460274509177283074fd4be5d4725bf443ed8eb122fb6cebcfb96b25396e9bae40714a6d53a6e1d5336249669dcb3cf51468836b37d66378f6b60837317fbd7fb3b72fc0ffb264fec9a1d613caae6d80dea9e4fe41e30eccd26c8f904d015028ca7504a0a9e6e7867933da16c3b39addd84d0c46df22ee9526c503715ceda87b08858c7ffcfbc16568485e08199ab1a18b9feb8c3498567e828fc26f34111dc79aff13a58e55603fb3d7a086c290ed944c7f3527844b7aa28fec4321b4227de76be0738d0f2ddb8f3b8721d8768465
private theorem part27 : 2 ^ prefix27 % Spec.Ffdh.ffdhe4096Prime = residue27 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue27)
    (e := prefix26) (a := residue26) (b := 2046293049) (n := 32)
    part26 (by decide +kernel) (by decide +kernel)
  rw [show prefix26 * 2 ^ (32 : Nat) + 2046293049 = prefix27 from by decide +kernel] at result
  exact result

private def prefix28 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (24 : Nat) * 2 ^ (96 : Nat))
private def residue28 : Nat := 0xe001e864457652ffe25d4c4de2539ed1ac41d257747218a4a32f632a32c822a3a4c950df22d7342d3858ee05232f3ea17db0abc5b3f1085a218bafbb5a349d9cafeede90bda1ce26b81091525b898a26781c9b74b77838d0c9a173aed31603880b5dd267ba86c6f54ba9c1c265d6006a3252cd422d6599829e71ea7d0f38a3dd3d7c292b7d33ccbdd9cd3257e6c702962d8653e37a2717ffff7f0db8a8acc7ecbe22406a4bd67aac40f302de693c0f5ea2a12cd9d1dad98106053de216f4e5970dd4c2c78ff4c6d34fd3a1d883c5c93c24a9dd00e68901152e1681ba85cb1d97e93464f011d29db45e09e88218b80cc225a516ebf2139e949e0be7ca22fbc3b8e11afe760d0b69fb0ff25a3b60a65067a72d2beda3d2082b901e0723d8f1ab63c756b4ff73a64f21002a45244abf2150ef8750e13745e840e455116c652683e564cc76cf328f91ff305cefb28abcc0e36594d7def5cb99b28e7c226450b23564f1097012a10f4d26745c6dec3d0865f5179ed3c29b477b278f0a8d758ac6d11298a4993fb06b09786a746f5a74863afc38389d2f5139da6a490c03d2211e66c8c59ab851be8b35812559601ccce7a23e678ff9054b4c4b684acf0b83709e8e866be5c72735a8d86cc988e2f58d39e5681317c072e14d2c1bc36cd4a5ce7713968ec59b654ad245887747759ea104ef8b11099040caf72932e7cb270cbc46534
private theorem part28 : 2 ^ prefix28 % Spec.Ffdh.ffdhe4096Prime = residue28 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue28)
    (e := prefix27) (a := residue27) (b := 251178064) (n := 32)
    part27 (by decide +kernel) (by decide +kernel)
  rw [show prefix27 * 2 ^ (32 : Nat) + 251178064 = prefix28 from by decide +kernel] at result
  exact result

private def prefix29 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (24 : Nat) * 2 ^ (64 : Nat))
private def residue29 : Nat := 0x6d9cc79ae961fc5ef836eb4655b4ad7e8a619ee846a70cc00953a2b69f6031e000adcf5a68670246b66acf7ba063492aa013b230bf1db5db7a77fc1c560011850b5b341e956073774cc6bc1af646ee3eb8e726405f51541b4842afadd46c110bf5c6503a228c4ad4fea862904047f729283f23aa6689d6863f48537a2d9e2005eb03695c53d40e0657fbccd0890aa1886deed1ac8b96b4c207f8e8fffddef16bae6ab1d7452a3650dff0fe05afde228ce1737a23edad15e754c3f18cbb101f3bf0bace891d0beb1fabd2d1afd4dbf4d911f60c2676234dda1587ba9fd23e8454bee628a341f97353dabb84b779e7e2469b6b96c223b0266650a5e39660ad56e6231bf6528fe3ad0b1acb67b40a76b675e40402f0dce2543b554fdf8fde123f2a0ecc0b8aac1e4c9953b7bc74cc37c488c395e3e11a52376049b239a6b33d0d25e1bbee436def1bc9240515b7bc4de1f10ef39620c6ac7c2be57594f67492d0f0d6b56d58f2dbee7cfc2257b898c6ec7a2d5c865c97309e1e52fcd320c97ac9077e444adfdf530f452842a14194257654b843c456f034d0d1beef1f4c11fa045c7b8a4de19e30bef45e5f1328b909926d0d2402c6cf232fa94fc70d19f3b86b963a4fc1ff98b62b2d4e47a8980aacc1ac6bcb823fdd1555d3e8e5a097d72657a1bee6be70eb8f9af33441dcb32919805aae67bd6e06ecec7985cdae8fbf887518
private theorem part29 : 2 ^ prefix29 % Spec.Ffdh.ffdhe4096Prime = residue29 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue29)
    (e := prefix28) (a := residue28) (b := 2606166938) (n := 32)
    part28 (by decide +kernel) (by decide +kernel)
  rw [show prefix28 * 2 ^ (32 : Nat) + 2606166938 = prefix29 from by decide +kernel] at result
  exact result

private def prefix30 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (24 : Nat) * 2 ^ (32 : Nat))
private def residue30 : Nat := 0x5e69d66228016415fb6760bdd7aede276f8030ff5ec25d4d6466fdc16e88f9a0056b5e12281c15e740c718f578b6ff03b0d231eb8e21e5d2ff47c0a8dfff0d059f384124e941868079b658d8a64f05a860ca6003a95ea5fd479920eb4f6c8ca055cfd6155232b021cccc2ca37d8bd8eacbab9af450e7527bee9a05fb73bada015bca38bb361fa2d1bffea8049f1d47c8e4d7bb5e4aec5c2b14ca432a3fc37e46f41d64ba22162566ba52ce3e8155dd17f83dc34cfa6ee6a2a0f75988e103674a31576791461d674f860a17ed71ea491394024a2bced1b5f7bdc25c864359d176e51069927c8bd876789d616c5526a02cf61bac5c6d7798eeb04a65dfcb503ff37b7716583e9013102b1a3dcdf04766b59c1fd4cb98b59b3e3eabad81c0bb0810d95030e572c6ff72b7f54d037b1260f36e6761f81cd5eef302b9f64f53338b91123798a2e8033c7b87c244b91a7bcc1e8f30325f51393850ca72e621b3901192f8618c09a024fd8fae77d9c6e63de078994d301d2adbad2100a8ef6ef9462aa6c5cb2b1950e90cd5084e86b166f9f3e336f55b73bcdd6d7eeb08bc8b15d92946c5d59b78df48799d39bbb9c908266fbcca7bb6f4c5c713702e67caf61dea61894c30f8de47f897ea2a3c752612567c7e9f448ec871956efb8643cacbb58afd0279b647a9cfa1bf40e4b16dbfb1266d4afe77c1c4f11885dcf097fddda1f5080c
private theorem part30 : 2 ^ prefix30 % Spec.Ffdh.ffdhe4096Prime = residue30 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue30)
    (e := prefix29) (a := residue29) (b := 2555798823) (n := 32)
    part29 (by decide +kernel) (by decide +kernel)
  rw [show prefix29 * 2 ^ (32 : Nat) + 2555798823 = prefix30 from by decide +kernel] at result
  exact result

private def prefix31 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (24 : Nat) * 2 ^ (0 : Nat))
private def residue31 : Nat := 0x6d35d2f1e430c1014082a3407570b51e506e1b15096ace10df08018f270da3687b9ba0424d3adf362bab60f99ded5d8a2eaf2196e0350236dccad42824a951c009884aa803356cec16d1b89ea707fb6ba5d8cea7605f5e00ca78aa4d3df6b385ae566522dab8c6e5acc5ac6f3957120777d8be07ab3309eba8b4d354aaed964fac885da543f1d89e716c6543a62629caa42270ead74117c9c11ce52199cb928c973ad1eb8a429971d75c03c4e30cef212fb0e62ee7da5a8bab2a95c09e9bed02bcbde28864d5824441740e4055491c45b3a02f22dfb177dd1f191c8784f41f3921b51e81e4b6232ec4c7cd4d1329896dc9c89e0187681deb9c724142f4ec8f8f5c9623926df04f3175f80264fd2f978404973c5495373f5056819d3039901c81bb2d59f78fd80854450bc765e57d32f34558267ffec3b4aa2704c926d269a21ede15339dc586da66683cbecf4324d92abdfb506660d829af41514149ad557a28163cba957b7c832df8e1c6218e01e9bb83594fa2816fe4deff74048471c074288d94e62a2d774eb6cfa30d663894e07cb2a566023af2b4e274b15e61077ae6671b0ddea6c4d170e73ec9bc81b429ef09098dd078b331ce0ec7b21447eaec80fc5d8969ffd0bbc709aa801892b22ba698cf759e6dd477b7a93cbf50e609384d0d0a3cb21baa8c50bfbeb660b3cae21faf59f3015758ead91a88f1117cd2304ad0
private theorem part31 : 2 ^ prefix31 % Spec.Ffdh.ffdhe4096Prime = residue31 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue31)
    (e := prefix30) (a := residue30) (b := 2753379517) (n := 32)
    part30 (by decide +kernel) (by decide +kernel)
  rw [show prefix30 * 2 ^ (32 : Nat) + 2753379517 = prefix31 from by decide +kernel] at result
  exact result

private def prefix32 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (23 : Nat) * 2 ^ (96 : Nat))
private def residue32 : Nat := 0xb3d5e2561027a441fea7682b8e99a4f4b97c8a6e11784a640c3bc1f543e37d9346d4778ab7716810ad02d00d95afe87846d6a2bc053ed529cbbd233233cb1c780e48f37454ce561e07143a837261483a1b2feb8e0969c98caac169e0a42aa04332acc013ed58f6aadc24c0039de29032bcdef4b193ccbc16f02edcbd71370e771b17858608b2d8ab579962c21418b55f8900d087f5dfc0430750c522a894863197b0f3afbb2ee26712b3f745bac5b20a443bef8cd31f7da239328d6efd3971b30f50f55142fe5f40821f5f1edb84504c36915348b9f17408e9218b69e5cb36896b08dd143e426c39cbee377371728e1b8546d38ac7f8282ba11ef3a80a5de02d6d671d47b31a3483d67b00f176cd1594f35e659ccb05df2e63e2fa2411c22a3e89efa6828fb1b7202fa34de02ab6af1473879236d19b94963bbbd205b54a270e195f02634cb3ef568c274fe99598f9a452e3e236a599e6a254e101f2c1af9e2cf2bb9048295609356203a27ff59196362b51ab1c3bd2a2e0dc8e8d0f347c3e92c39578c3c8d776bfea701095a9fd9eb7945fb7dc18428b6700ce37d9cd6e029148ea7769330a46544ea1dc17963a9d4033c96b2bdfbb6f191613997197352772bb51a66781e96c240da44ad2f1175e922d2dbb352bff9caa99a10c6dcc3fdf27f09fb0c1c3ea7788cca048a67b77d9ff834ee703317e691a4d7399f20527151a
private theorem part32 : 2 ^ prefix32 % Spec.Ffdh.ffdhe4096Prime = residue32 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue32)
    (e := prefix31) (a := residue31) (b := 1577408705) (n := 32)
    part31 (by decide +kernel) (by decide +kernel)
  rw [show prefix31 * 2 ^ (32 : Nat) + 1577408705 = prefix32 from by decide +kernel] at result
  exact result

private def prefix33 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (23 : Nat) * 2 ^ (64 : Nat))
private def residue33 : Nat := 0x5b052850e1e85978edd2cdaef16f03f1155b3886d2ce0dd6ce07ac7a3786a1830443e5c8ab25c920d17abc95355a072b5c45075cd53b8d75ff49ac697453b39af1bc77c1945b22053b3518ececde5ad485ec09428c8f3a4d69abead6a591bac5547933b6d4adf1dcde6a557467a73d47ea56032acfa02aa60dc481194294cc66f4fe0ab7e5688388c6377536ce0a812d0815a267cf578605489b2e2943ceaed4b2c4af947800d3a0ccd79945138d9ce088265d6310d4e6f2eea0bf401889cd96f441a2993aa9993389d449e483ab762ce04bee9e36892ee742b91109f6d29e240af4800680a9f385ca6db960054a9e0dc75a77e77d7f8e219fa5083e61380da5fb13fdc1746c1a0956c020b9f6f807f33275b0dd10424fcde5d7d3cfa9a31c38d1c1562945dae9269053ccb5bc9095e7d2c418eb4b55ceb66651980d5f085e6ff0b3a8d10ff781e0fea7e1e68e1871350cbf32b89e3ca4532be7b898980badc9f0b42d547f578f5c0e29a69f80cb87229fbb428720d59c261dbdcfa4ef0c63a3a7a10dfe4e1f5491a70e12581e224aaf943d37cb1afa06496ae0e6744398031d55ac259692dae4fe2100dd953337976dff2f4f35b32627c7623f3cc6f01519b80f28adb166b4612e079e2eecff2994839b961a9dc1884f9c592f5ef0d25997e25b389536e6c177cc5a36f24fe6afee618d5bf5f91288597b875817ab5c13fd31
private theorem part33 : 2 ^ prefix33 % Spec.Ffdh.ffdhe4096Prime = residue33 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue33)
    (e := prefix32) (a := residue32) (b := 1502772656) (n := 32)
    part32 (by decide +kernel) (by decide +kernel)
  rw [show prefix32 * 2 ^ (32 : Nat) + 1502772656 = prefix33 from by decide +kernel] at result
  exact result

private def prefix34 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (23 : Nat) * 2 ^ (32 : Nat))
private def residue34 : Nat := 0x9f151a7b1f6071d9f572cb62250e3615d2c55a9894bcb29d99bf5c9aff761a9752cf50902104c3016b7dd0789870ec2a2e664a011171c34e1a11e1a20a3804a83de61f470b6703ded07e0ac8adcd34e88ec27d2a3831e88fb81d53e1b8a5bc90b642c4f480d34bb647f43f0b4b6ecca1b1f133718db136514afb62d56a476b68e0188d3140a101963f4119fcdcfbf78d56e98c6d51a8f2401b8dbd1005dfe11f94aaf7cc5b88c563127e8f6f79f0ce420558dbbae2022c7896628ccd67da1e99db42f69da7c6bac4a5871c9b1f4cbba3a5b7a9291eb1396cafcebb387603bdbb53a5befdcb8883d897f837857f56600e4752c87c3d547d36ac59f5d2d14114da8d6624b1b23a213514d548c2339a15f7f2402bf5c36e04b46dafb56e70b2b8e3db948c7df68f5eccb0edddb09e8364d24be5ee86da10781df847f5780c9d5ee1d75f50903cacbddb074f0faf1335fa0902715d1eb8a09ff91638096678189bbd0dab3f903c6dacc7bdabec90d1b746e7649c3e8e33ea3faf95556e67849360a8ce8e12e9e14d940494a74bc0d70373f153509ff3a9887261988ba7e38d63f2b4bd7368963d187455e60fc671602f1f76337bb8d476f3096c76cd43a47bfd31266775e7ff3bc7187c83ad09a235b855e0a65cec99a4d5744441e378323c68a38d471965d05742cd56eeb396df7effc36877c4fe77c16de89c3d7d9718e1d794aa
private theorem part34 : 2 ^ prefix34 % Spec.Ffdh.ffdhe4096Prime = residue34 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue34)
    (e := prefix33) (a := residue33) (b := 3900986533) (n := 32)
    part33 (by decide +kernel) (by decide +kernel)
  rw [show prefix33 * 2 ^ (32 : Nat) + 3900986533 = prefix34 from by decide +kernel] at result
  exact result

private def prefix35 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (23 : Nat) * 2 ^ (0 : Nat))
private def residue35 : Nat := 0xd32f7bbf54043c8b430c9e5fe4e3ec5ffded01245b5f8143b1e17bb33d0c69eabbe1c310857eb67743b419faa6e308593366d93cfe12d0c68de04db3dc5b99944fd97ac3418e47dd467d4c65d22af348a4500534b8923972b69fc55bfad0bc2bc93dddb7a3cc2fd476a71eb239754b6468cd786867a10c7294018fa646223242c9f596f5a201d4754fc06284e7eac5f4ad69416b33955650fbaaee66db55df6dbf0d7ea8df39495a9a72979125c270082facdcb5186d7519b11b4eb5b58d03d15f6ec3f4b52e67ed349e8440aea4e46dbb53295529f7e7660f4b77b76427fef9d8cb8178f725794a81edb1090e22d62764509c290f1da677a218d97a49d8f4d65af565f10a1c006c8492597b251ae87b62b4ccb519a05bcc97253ae7d8e5ccbfaeaa76a2e9e81872c3c75312dd0f6c702ddacce54d493ec28dd11f97d3fd3c33ee8cc350abdb16ee7d983944e35b7b64a99aede7da145b87bedd08620c909704f78be28a4c7643ee346d4e88d06c24c28ef2d9f03ac3650bd664f8bf8cddcc7e9bd19e5d81a7cc6ba55cac5b6f3760a2769517e29889827cec849a4f4d6585d723d9351f16aaa4fc153e3f398c715aadebefef1c9fba1fffbf821ffb965b4a9dc3514f192fc51b226490eab60e1aceb38e582de72a8c2b3062ac7b912a6a8ec68940145c70c8a088d7c2cc38014bb0a25791b3c3b41617d94a2c39c28eda5be3
private theorem part35 : 2 ^ prefix35 % Spec.Ffdh.ffdhe4096Prime = residue35 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue35)
    (e := prefix34) (a := residue34) (b := 3647238653) (n := 32)
    part34 (by decide +kernel) (by decide +kernel)
  rw [show prefix34 * 2 ^ (32 : Nat) + 3647238653 = prefix35 from by decide +kernel] at result
  exact result

private def prefix36 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (22 : Nat) * 2 ^ (96 : Nat))
private def residue36 : Nat := 0x81ae0aa892542c44fed97e235e68b9442c134351e2a9167bd3eef1fae6a4ec2d81fda0f5822478b1ac00687ab97ba47ab4689a7e05465d448a0c6308da88d0e080a44e7e262092fd78e0ca9cb7988cef7750e31a1437bb214c19caac5fe23815e440843844c14dd18b92157886b97d3f0365052e118b123c55c23649b8e69233da86ad20ac69f6029d97ba07ed1822a5175c42dec1e9743822fddd2bfe2215f8609a5c49c62df1a1fe9211ed94c400c7e846b7533d785125240c870269c2e549c93a83485cffd69b8b833dbba0fae58d131f32db30516dfc959464b191f857b953d17ce8e0967772fac61947a6b2dd11e96808688cf1b73591ac2e2c8747939caa17712f70ee93dbcdae2bdcba5d4c576430bc60a8c3cf0aee81f09c7ae320abc244a6269f7b58be6546254936a259018054f4e879059d424d4ad9fd29fc6a55d951dd5b8afca11ede3210d1c3c609d7a28a08dd85293cf462ed4c8649fb23b2d7e5b0a7a4851be874326528472310ba906e228d9e3e1a7ca62583f13844ab7608543c4a6d6634583e5eca3b651a1045e3de864e43bee4ab6fa051c68303d408d02aae44d24fe684b4a6d9f5d8e04f988737cfc6c820876eb02f496e5800b2dfdea07dc90bb17a19864415dcd0896ad047cdd1a2dc22c3be40909de27cba4fc6c7919ceb7dc6b911179ac64e6e6bfda6dd4889ee0111d8c81c9b7592e4609de0
private theorem part36 : 2 ^ prefix36 % Spec.Ffdh.ffdhe4096Prime = residue36 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue36)
    (e := prefix35) (a := residue35) (b := 3702877531) (n := 32)
    part35 (by decide +kernel) (by decide +kernel)
  rw [show prefix35 * 2 ^ (32 : Nat) + 3702877531 = prefix36 from by decide +kernel] at result
  exact result

private def prefix37 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (22 : Nat) * 2 ^ (64 : Nat))
private def residue37 : Nat := 0xe985ff9ce07a5476315755d4ad4b34dcea63f22bd88f0e3e98bd3e14d8dbffffc31cb9040d385b2fc86558c520a1d51f8b1c327d6ae434d9d02f12f36d19e40c26bf9a926480ee6b711667b50e1617d2b690078bc9a918602dc5979e4ad8eadf34e6433498dd7d6ffae61c0a5ef726bbc86437c15f0d224a706dcc30c9b458ce78e4c4940e4c6f73eb45f65cc14757b88bb560be11bfc45424fc613b65ec5ce767b9533c38997afc74ff4b1a0686e64723979f999c38cc3d93574b66674263d84c64061169924568122835d08968df6927c419d922f6dfb97cf38d735d8407ae8a9bc15a5d7fa17efdffdf90c74825218b6dd9040a950d278fd2938014296eec629fe8a6f2f4eacc431a4ec2027ea6436346d8ce214caa69a76630d8d9166b91aa69ad10d444a2904b746d184ac6afe339e6cab8746e138d0fa2fa441a6b12853ee2e37943f6d98920c7565214341d8ce1c767c9d3c7d0b4129729bc2e3f737e5490a6abf52970302de4021e0a3458a6d16481b217b25d2f77ae98cb75a0e3527600dbf4fe760d6e6a791a7588ce2ddc9df01e2843baba8164f34dae0fdb65294d9585d98312f24f57234705ab2d7d72681ccb1766c9982fd9265155a1f1caccacf95b7e0c9d0e632bcbf506b3b47a08a7ffd68fd463381b347bc708c56205d6999e2e2bfa490020fc3b4ce4130a079fd1346925caa03988667b4e48421f532b
private theorem part37 : 2 ^ prefix37 % Spec.Ffdh.ffdhe4096Prime = residue37 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue37)
    (e := prefix36) (a := residue36) (b := 2959866420) (n := 32)
    part36 (by decide +kernel) (by decide +kernel)
  rw [show prefix36 * 2 ^ (32 : Nat) + 2959866420 = prefix37 from by decide +kernel] at result
  exact result

private def prefix38 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (22 : Nat) * 2 ^ (32 : Nat))
private def residue38 : Nat := 0x55f85a32584311923c44ecb12811e09ea8e990a362ff91f34dbb6e4eaab904f5c327f1536e10dfd0fdd5f2484b8e7808d344a8fdfc8504e0ec84e7ac29f433add6a87217134a1c0abc8e0cc466ea8d888623fff5064c2f9ff175081db5ba3ce5932947cb94148f3142b62afbb29cdc6390f1f08041e071cccf251fb16527a9ed5e2168e415016567878c3a6cdc0b617d67ef852c609a6414fdc4595363edfb03da9ab36d0fc7b2fc3305457711bef9a31c8bc415a8326f36329af0fd586f21f798779b3b739659fc8d75c47fa7284d2b33ce913652fa52cde77cf0f71312bd02197427c2c39fbe4cda638b169d3da6b6971623f06b3d6c0d5285b193d79b7cc7ad9b46d900ac8f690782a8df6f5bdc322b6b943917ec8e79fe02017d6763f4aba9cfca6536457d4eb2834eb3d1b9a93141039daa300d1b610c5aa9a01be6053894e345a40c7e5d5fb2f7a614fe833146f7d2cc8668d1cf6b3b733063ad2bd3ff25083e9934e1cfc6cb7e39ca53e5decaea9ddab042465659afba6138a0f37623308828524f1ea6b1b8a50244bd6313bbca96957648ac74d5b66bfc70743586712c43c794a15c3a3fa69f057470a47875d881c2df0b07c4af6635a7ad6157f5a4274f102ab93336f8afeb7c886773f923cec5c0ecdea2446522beaa6250017f9191c3ba43a022105cb0030e04805c4b15710c8d17a54f71c9935a450ecfc7d21e
private theorem part38 : 2 ^ prefix38 % Spec.Ffdh.ffdhe4096Prime = residue38 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue38)
    (e := prefix37) (a := residue37) (b := 245866833) (n := 32)
    part37 (by decide +kernel) (by decide +kernel)
  rw [show prefix37 * 2 ^ (32 : Nat) + 245866833 = prefix38 from by decide +kernel] at result
  exact result

private def prefix39 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (22 : Nat) * 2 ^ (0 : Nat))
private def residue39 : Nat := 0x49418f304d8bcbf20e8eda773635e8c0514f3c48470dc10571afc077c24b28556d5d7c286e529c4e4a99257b99cc6e727269256497d69b86240ac2d590a9d2a4be192372a9d2a99349b7227735eb4cd5746739cf1350ce8636cf43b94174c191bd68092b8539252890e8dcd2c888c33453f364dc813167717220039eb67e2efad1bec1a0c97a7e2852a13605428a4825b2edb6081a7b7b78a771f4558955657a93a80b1ffed77c98e3a728cbbf434eb8a537733caac09e1bb4f32594dfa2452852fe5fb8152c6f93864ea5855208450b7e8f544ee5eae5e929ebcab635b3fab2722c243695103a5f13dae43ca5b3495ac59b7f426c197803fa53fb101975574a6b00a8130364d34b5bcd8fa9df09a84278c0b558b3873cecd0a8a239fac4804ba7251a05efefb8c36ad8e5a420997aa758c857e9816a7ebf1ce9b7646c1c4aa5ac673c3ffed9331aa39a6be80a1518a1b126952def0e19bf478c9bd18425a81e99ca286a4a98130516b529b946310c49bf7115dd5472827783cb2d90fceacfa441e8fc4448190ef6747ae9b173086907072ae8dba22401be2e07e5ebcf0b5f8e1fb684e0e7a83095275d2589a5bb490a2df0e23ce7b03668b55ae8d02d0891e43f240c5b89cff1e8df53f69a226bf6fafc45a7e5da9cc699d525978c08303f18739c6147476b6f5687f16352fb742fd2709e5b11adb3a61432281398854f93ee
private theorem part39 : 2 ^ prefix39 % Spec.Ffdh.ffdhe4096Prime = residue39 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue39)
    (e := prefix38) (a := residue38) (b := 4011632378) (n := 32)
    part38 (by decide +kernel) (by decide +kernel)
  rw [show prefix38 * 2 ^ (32 : Nat) + 4011632378 = prefix39 from by decide +kernel] at result
  exact result

private def prefix40 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (21 : Nat) * 2 ^ (96 : Nat))
private def residue40 : Nat := 0xd3712e3b99a4f4e958322aa47cc6440dd089abe4dd2ef3b0850603987a2f421ad08499af5351d077085c54df478bf96b2306ce1e143d240db74b4e048c202564a3691e878aabcd41ffb53e0e38f7a5183af816aae1c56902100b754d06d691d4811c81c7058a626bcf0ba754d3e787f2b7145f67e2d20e92f1ec6cfc36abc26b5fad734ff5120a9cf796bc5d01bf3f6a655fddb261e202e35cb5a4637ac7fe0325c864cd30442e760ee2245571570ab557a4659d5f3307489bae9857626f61379cf1b0c3877342952ac9e16e57272a1665406e329ce1970474b0db282105b218ab718cb9486bfeb2d245c5beef58bc8928f5915bc8ca01b02c717840517446838baeed7569547955489eb0cb8b05d639bc78b3a732b02bd3cdc0c03f4cb1f5dff840b676e1e286b0a43e2589de23ce0d72f40096a0123c6ccbdc2ce25deaf64177d928c259f4abf58a35bb8751f5dc2a5f72a9220a4d70beaec6c9508b60b5159da1948755825e129a1580153efc7e625e3eee295823b7e94cc5adbbd5bba11ce1add10b40789470b9d4412a9d68a7e3d4b6212eb32175de4e03c8c65bc95edf73a5e7e84501829d839de904d560b149fb9555958f7db0c6ac7f92567ceecf04815d6d83906083a3bf6f8d84558990980cd68d1836e86fee996688a3807aaffae96249fd4806361186fa309ca9c471adee3b1d0eb1bbdd954817e698c70aa0fe
private theorem part40 : 2 ^ prefix40 % Spec.Ffdh.ffdhe4096Prime = residue40 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue40)
    (e := prefix39) (a := residue39) (b := 1462466291) (n := 32)
    part39 (by decide +kernel) (by decide +kernel)
  rw [show prefix39 * 2 ^ (32 : Nat) + 1462466291 = prefix40 from by decide +kernel] at result
  exact result

private def prefix41 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (21 : Nat) * 2 ^ (64 : Nat))
private def residue41 : Nat := 0x4b9aff2cb55871a76a6883fd9f6ad906a88b3904ad649daaaca5144ce8280092c328b97cf2fed4a3015df322b85cf9ac34c376dfaf3ce831b9e121d358de8986806ac1d39a87683c5a1cc56a72d17020c3c6889d7e86a83b5ba2ff6ba8d5b3fa054cddef1f10fedc36ecde1c71b65e97ad1db0f63ee0a962ebb785baa705cf9c28a592b288f2ab315c23242ecf036cb50926057cc3422958a793f65d1498e59e2b3c93a4e487503c37dfe8e0f6d3663c859f6235274ed88e3398834fc9d433119cd806bc45448bf7f9e92838cbb0f3ea300b3ec3194adee3c9fdbd8a790050edc5c34d308ad0c313d39a22abd0bb0b07d7f926cd3df1dcc2b50d81bbfa77c3cd137959bf797e8ebe08bc53b524c9796f62205c54cf0011fc88108b018a2522eecc9e4fa0f7cb50424fa8af9d0a0ff736e6536e2bb93ed274a13560c5317992405c9ad2448bd2256fefbc1a678a66930168b6e1ebcd2b79c7516502e4b36418e3382d0b521c9c395ea96ec89512eaf8a096f8cad82b10a24e5f3e01ba2b003ef87fd5627d12b5904d71c1929b2f2a61b9275d551a7939002b92f576858476805d93e4890ba2b0326bc2b5a4c46d8148d956e69ca70891749f9b451e90b90b1252e635651e0738fae37a1c138b90c9d5381be18b2e7fb22ef3ee26da52e40b0e26f0abc3e97aa22d4dfffdb2c64eba2d26cad39b3d0431e6233e837a22c727bdc6
private theorem part41 : 2 ^ prefix41 % Spec.Ffdh.ffdhe4096Prime = residue41 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue41)
    (e := prefix40) (a := residue40) (b := 2981715340) (n := 32)
    part40 (by decide +kernel) (by decide +kernel)
  rw [show prefix40 * 2 ^ (32 : Nat) + 2981715340 = prefix41 from by decide +kernel] at result
  exact result

private def prefix42 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (21 : Nat) * 2 ^ (32 : Nat))
private def residue42 : Nat := 0x549db3dd52629b75227531f0ddf32f952bcfc3dc3d1fbf0f05fb5a48f938da3291a5d4a5189424be1459ba45fd10d5e6ad06eb83f50838c041863ca55cc19b29f88f6bba95054bdcee76d702b95b582e66cd938692938a6dcea2143418b1310335a888db9cc0520130858cd4ade3f0eddb41289bae4f48b3218b078d88c237cd896c6ccdeb2d8d0a78522333436ae8c9b1fbc3e09cbad2f218abab89fb333e762901b2742cebbd7da136ca66d1a47aa186889af978139d8cdf3de651a588f11198fe56e990d47f1490b25cda620588113b9dda7bd2374eb3113a86dc7f29946696791bf463a9c28ec06e63435f760fd8a0912283fa0735254ed8e9cdb43d32f1ab857be52004d1e3ce0d0abc5375b7a996b605d64dd3a3b4f25db6379cc8815621db99beceb426b7f3a44d0ee18fe8419648fa2d8c4a8fb4517036a89abafe99f030e09d4126c37e188db6b5f75392fdd4e446195bafa2421abafc42b083f4def4c1a933fc3b4aa62f5f432a71579cc5aa434353377dea6418ac3a9a49258456e33ff97f7bf2cc2d40bcf453aaa8b51fd8f4cf34b323e271e7efa0a915c3188e745ea95925e292764ef329983c349ce2feb456166eccf8b0fa83bd22174545131ae22548fb3d309272c99315f1cd4d3fda763de559cf9f1dda7667a515ba850d2adc48bf927e413d4c2a1a612a8fba38d7bc6131c3774e1c34ad4b1ba0ce176d
private theorem part42 : 2 ^ prefix42 % Spec.Ffdh.ffdhe4096Prime = residue42 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue42)
    (e := prefix41) (a := residue41) (b := 2240009188) (n := 32)
    part41 (by decide +kernel) (by decide +kernel)
  rw [show prefix41 * 2 ^ (32 : Nat) + 2240009188 = prefix42 from by decide +kernel] at result
  exact result

private def prefix43 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (21 : Nat) * 2 ^ (0 : Nat))
private def residue43 : Nat := 0xedb169d1fe328226705f7efea7bed48b4097aac7d6ac7fe11ae2ab77e36f4383a0d56812f0e15febaba7901488802770f60b17869318bd975e41b643efaf3e11097f426dd743546de69ce1ecaf7c8a66cac3d158b32e70738eeef774d5b19b76c98aed9b9a065018e53351b007057fe430b19104f19b815f658d7a4fc5a922dad561f8d92439b02ffdb2151075f43aab1751ff7990bc7f35aa5d411a374ac57721983fc15bf892cef40647213c2a101e6166a0845001a4322d3a06c97ef58c0327d3a8410e61c10ddfa9e65b90b2fb41ce12a1a3bb31728492c96384999a6c080d687d0c3b6d4c51b5e4f3627dfee218cc992a184a20a93fd76e4346d1d7787a0ce460d07c219a6ba882ed39d33b5b1d881f418a26647a6a09036daad0f096c14e8e8fec1105196b1f3968ee8f9077405a1c014303f186710c3fe8817e5e05ae6feb189f67962ec826475114f26fc0449c0fe44414e603810e5bec21aa8a3dd2575aeabcc46a53ae750c3906e52948c97425396bbcfb1a635e261de685a2e74c4a15403dfe6d3bf89fd18226d6ed0120023a9b47ad8cd0d04129ef6658267584831bc38966b5bef85d4b0e06e39bae5bf6d168c48731f573ffa33a2e15224d6fa75f2f94bbed007bff5c4276d9afff121dd2873d8f152e6e36eb9f6f58ab93ad572728a3e6dbc8b259374b34e103247033d1e7e0d45ceaa5017602ba6a63c83
private theorem part43 : 2 ^ prefix43 % Spec.Ffdh.ffdhe4096Prime = residue43 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue43)
    (e := prefix42) (a := residue42) (b := 1996830392) (n := 32)
    part42 (by decide +kernel) (by decide +kernel)
  rw [show prefix42 * 2 ^ (32 : Nat) + 1996830392 = prefix43 from by decide +kernel] at result
  exact result

private def prefix44 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (20 : Nat) * 2 ^ (96 : Nat))
private def residue44 : Nat := 0x6dc9f808e52e214eba90ccdf22a6449286595402423f6d6c9042da0712abb633dbdab819f43b623ddb7d11a1d8a73f0c4100346bc03ddbfd4ec845c163ad2e409598e22da761e54e5f924ad6709e8dafa506c45afec235a8644087b90594583116ca86e7b769b9ac7d2eb5803b9a67941fa3de5df2f407a3a716066eaada7223abe5f5472156312ec05978f0f33f17e10184c51ba5b5f23c96b194fef99d46fb97ab56e14007d5c6d057672682115b71964b652f105e8189491b99b8c8272930e108195f7cd227236cca2d1e550eb4c0641559c9c64bf806e20d6ea2db8281b9552a2703a405ee71c025d4824bd77454dd215117e77efcb49fc3f913220b9620c6d5871ed3fef577d6dea37d502eba1166e128516a0b341a65c10ddddccc3bad75808359c9cf80a6132e7fe36f284e6d28843e77740e8c02fb15caecd49f2ebfa934c9895fe13e97806298f7dcc6795b55e13aa299e4e1f32ddce32ddbfae9188fbaad6ec1966e95992128418757ead10527ce4ed0a21b511704928f05f2c9bce9b73dafb16d707ea2e01865042e9813173aa0c429c6fbcc17db1567dc42bf71f84a2e20023c1e4b223186757db3613ce0b89cae47a531ba749c593dd1ce5c1a1b3bf948a0a08558cf9f883ce182a1d18f77d7463bbf4808e20031ec33f22e7e7974223ca1b6476f0fd27dcf394df80c85333f3d2f6f0c51c816f7dc0bbea76a
private theorem part44 : 2 ^ prefix44 % Spec.Ffdh.ffdhe4096Prime = residue44 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue44)
    (e := prefix43) (a := residue43) (b := 1325497968) (n := 32)
    part43 (by decide +kernel) (by decide +kernel)
  rw [show prefix43 * 2 ^ (32 : Nat) + 1325497968 = prefix44 from by decide +kernel] at result
  exact result

private def prefix45 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (20 : Nat) * 2 ^ (64 : Nat))
private def residue45 : Nat := 0x5f29fc5094304b22264ea57b8261d204874e9e02f9744ef775fbf4b5fab51aa37b14a33af38b1adca5513caefa55b74c02b6b672a25d72abd99932cb312c7bd64ca1f18c622be2397f8e2b2e5d5d3771411d2c8b9937fabab3cb7c99c1ec1a59f7e02979fefd5e31646343249d112c33edd00fa4b2725a21404ddc6be86d7212e0f08da09d8a129df6099e03922211a17529fde39f27ff65dc014c264a37c3cebadc7c0aefabd6e73cd281808f03c2dd28a84fdf794a8edd634331172c29b1d2e78b711853a0ed661e66d80c5e7153ec2f297fc663938ba3969732f31eea7cb8676425596c5bd933fc4f771d9e66bd332cddd0ccb5a952ccf3cefd006837b19eddac78da0513ff9d3c2616d7870a57ab4a3582858c2515a75fef68bd6bd9eda3cb8c7e96475e5cead112f880eeced49e0bf91c728f5e0dd22e0bb6409df358e83aaa8971a824075bb7c5476dcd222e0bf2721fae5639793e10e93a1c9cac5153d1aceb325357a826f61c8ff8e33c56a3e1da5dfbd044cd3567f6549a5a8c74ef57c6dd1e758e7c06dd975b7f7d4aef26f3981068968696ec37116fff0e908a0d3479992c2b5c71920acf43e8478655009042f5c81ad98729f0429a4e1c05f30559fd1711f7e5f7d44b7c368bd6d3a523d45871c33465d91e24a374c39f55cb7dc79864f1ff9bdd0c7473d96af185e5214d2056e20b7afffc72220a774bc58198
private theorem part45 : 2 ^ prefix45 % Spec.Ffdh.ffdhe4096Prime = residue45 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue45)
    (e := prefix44) (a := residue44) (b := 3875271030) (n := 32)
    part44 (by decide +kernel) (by decide +kernel)
  rw [show prefix44 * 2 ^ (32 : Nat) + 3875271030 = prefix45 from by decide +kernel] at result
  exact result

private def prefix46 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (20 : Nat) * 2 ^ (32 : Nat))
private def residue46 : Nat := 0x998e8c1ac4f8e740ce081cdc8e3d26d492cc117b21b1d71b48cbc3b6d19fe1fbb23b2434381d7ef739d35e1c1228f7e3b46450afd9a6a721910a3ccfc2c9077a517a1d2a309894e2900df647ef262f5b4205ed46c9bf5e08d5a7753f5964c9ea008849f8077bb925bb586b024aab239994ec282dc50540ddc231f590ac5e4a558ed1b00a224c3e507a54a533f0eb7126fab67e70729e7d0bc3df0333bffe838d3697114b47b8c93239ceac4d09930da9909d809181e9531ca5ce922b1ef6a815bb062f0f7f27416fd9b44c31d0483cf26759b865b248ed6eefe4cd467986414bd2e9a9226541d166e58c5f2ac03760895ed543d7a0c01fdf8ee45513c29ad0dcba89bdbb0599bc9e8c017b17f8b1358eccc617ca8e677963475e369bb5b42032bd5750688db7306fa3b24da7eeb7bd264a8cefd93112767e186f57ad8b7f5e2a67868f62db10366769be1efeabf080a794225ee380c41166a433274545ead56659d89e4088f90397f8bc9304472226ea08bd1e499d51988a9a5c87c1b5dbf85a00eccdd2ffec92de3dc67be33c81ce2cc53af13610d51352eb359a005f5d9c907ceb6eaa9954efc91944e21de62a033ac06d480fadeef7a49c6fe35a9cac35457edba32a55f7db7584811ce661321ed2e1fac2e7805c698b5d47f7a6abea4f98cf6c52780f3190c43fbfca574594fad8dc1dcaa432d063496923ddc7c0f51348
private theorem part46 : 2 ^ prefix46 % Spec.Ffdh.ffdhe4096Prime = residue46 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue46)
    (e := prefix45) (a := residue45) (b := 1612317286) (n := 32)
    part45 (by decide +kernel) (by decide +kernel)
  rw [show prefix45 * 2 ^ (32 : Nat) + 1612317286 = prefix46 from by decide +kernel] at result
  exact result

private def prefix47 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (20 : Nat) * 2 ^ (0 : Nat))
private def residue47 : Nat := 0x5a71754014c6bd8a997b82c23c8a39e50edeb20330e315bd3b0c49795f9ce5edf060ca9404b25ac88e327652400494c551193a6b79c45deb08c04d336498a86c2a8fa03b2593d6be5e1fcc915d46ba63960c86909e633518fd3b800d1e6833bde0252eb70aa4c20cc3bafb607fcceaf938b2753a1cb00b21348df1aae56294c8c8aa0523675397d51fa2c70caf4e7c279f883e1d79cad5c6f1bbe3e69c2c932b271eb8d23d2d32b11d3815ec6d77078a1e3a46a862ff9e92359b5cfc2341877c4c97283bc26be0077c194e7895aac9ea60a189578de62f5f27936a04a95f62d1ea267d6af52182a32c7d03fe79c7bba254585e786549917ba50163b95ed29bc37d73eacec81d98f6e4e14809662103d9dd43b8a7d7d49fae3b52fe6daf58b2c9abaf4de00fd5cf3ea744b02dd57ef8f4f4789279d25db97892df46d59d71fe18c5f7084a6506ff4e23377a0c74f98dd1e30ef0b2a3d48de749abbcddf13ef6055ab4bf8b190424b26f330f9439769c178b22dc65537cb55179e99dd4a8a332b792c5da5040aa1879fb3264bfa1e48e4ddaf65486a8a03953a147993e8c14e5e57b5530a95faf22ad5954b3237dd3c7ee75a9ab6e30179c6d5c38238dded663d778acfc375162e2e4d5b69edcf68056e13ec8f89c5e55b8683af1f8add5b258f7427d3e784521d9199be40ca2c39f3ebc6d3ce9cfd4dffc77502ed4757d996272
private theorem part47 : 2 ^ prefix47 % Spec.Ffdh.ffdhe4096Prime = residue47 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue47)
    (e := prefix46) (a := residue46) (b := 2484737968) (n := 32)
    part46 (by decide +kernel) (by decide +kernel)
  rw [show prefix46 * 2 ^ (32 : Nat) + 2484737968 = prefix47 from by decide +kernel] at result
  exact result

private def prefix48 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (19 : Nat) * 2 ^ (96 : Nat))
private def residue48 : Nat := 0xabd09647ba2bdbcf3b3f7b753ba83e963f682298bc3acde05832217bb205c3f72863745f4150f886bdc61d12b03fc11502d4756b5f3e739c0fa7df40f492773b4da3e735b9d8cb05e62a04cc636836f5cbae3b14262a15ef10c1a838ea9bae6f4589545e2bce3344e0a11fca96f8f8b6b37f42d9f3509894332890632e7da8d8ec88822544b065e8a9a4853b49b1b46f7171a4d43f328b0508acf29f2573b02fc18a88b975b2461ab521a74b62881cc0e21678e1acd211e2e10629dca58c2e865c93726a26a883509783c75090cba7a8ac30e5eb7fba64539da7a9f6a2dbc112cd1aa46411b18cb850000632da88aceecb6c3113df35730269141446239d5c8afa8353db7d77416277984a74669feb3be8eb4309c3ed5fffd72e124db4304c32a2374a52365e628cd47a773e30dcf6a54ddc089a4d291588cd15d1b674d48c82ae30c1af9b13f387ec4502ef917c811692e185b9b6f3e746c9774c94bbd9a82efcc0a049cc6b574d6be4a286d06e00cee41d396de4b7094c78b99f14755732948c108e99e229c0dbedec8ce9ecbeb44a54ec9658ce9c0802997e91e14569bcc52e7e4d5d8303531b02e8d7c6d2301749177aebedae63b9db62136d4dadef3f53501c0c6499c4c01ecc860b89d246602258116fdd769838024081d736c650d6c3883661dddda8255aa07bc14c3fe9e24262a2de82a25be5a1cf1c8f43b7d002a9
private theorem part48 : 2 ^ prefix48 % Spec.Ffdh.ffdhe4096Prime = residue48 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue48)
    (e := prefix47) (a := residue47) (b := 3367599950) (n := 32)
    part47 (by decide +kernel) (by decide +kernel)
  rw [show prefix47 * 2 ^ (32 : Nat) + 3367599950 = prefix48 from by decide +kernel] at result
  exact result

private def prefix49 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (19 : Nat) * 2 ^ (64 : Nat))
private def residue49 : Nat := 0xe947731cbb83ad0fcc0ef94a46ba8c89963f7d5aac02f83bde94f0cc9749f7d18ad0799b375fa4f2db737e90c5aacaa849de0be8df5f2387f7f979336640effc925db1cf2fb537f00720ca04e931d721f56b0a0d219f716a40efaaadf323d7c4abb1b433b259116b900891d1bfab7120e0b928402dc7ecf4d3719a4a752ba62cf5c04dbce091e57fae6f44ce716f75efe878e1c6657ddf1206b8047e25a5ba18bb014eb898be1212b59ff0d0bc52a734b6e75c50a3f0c617de46e23c72881666feebc829be2d3be0acf5578ff0245a9d33f9e6475b1f9c6504b95574c6a292acfc1a69fb48cfff12b0d1de0b082a0cc8ed85a181791101e8981f5ed08ca05a83d5d9cd717a4ba7974171de078a151eb7b67081beac60ae17b6536e2ec6e312efa1f19bb431a14a1bfdc1da1f5c3254bbafd1fd1c6833dfac44f109ab7601edfec914d71074469412a26943ad00f83a0e0f1c29e0ed47c382279b6a2641e0320aa5ac407d0830a3f8c269f1dce726f5d84335e42bd6f28379008afbd8332b8da131cae87c76b0a030af2ea78888f75a1064b63986c6a0a10f3180cda20e176f967cdfee4978f2915ad3b6fd7acfb2164a6f3af02c5a12d8801d8fed9d11892630bc62cd995e6293ab3b979f7c04d99d10c66dd6b39ee8a21b1c75ed71f415007f179f14978d6f37485a68fe4982f60a039bbad8e05ebfd278667c6454d61790fb
private theorem part49 : 2 ^ prefix49 % Spec.Ffdh.ffdhe4096Prime = residue49 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue49)
    (e := prefix48) (a := residue48) (b := 1958920703) (n := 32)
    part48 (by decide +kernel) (by decide +kernel)
  rw [show prefix48 * 2 ^ (32 : Nat) + 1958920703 = prefix49 from by decide +kernel] at result
  exact result

private def prefix50 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (19 : Nat) * 2 ^ (32 : Nat))
private def residue50 : Nat := 0x3e1ccfd560986049ba870702d8e9aca97787e05c4e8ca2c0b5f4f154f829d984fb0b972ebba5146f20811597b7d7b4f25d18c93772f3ae60cc3b5cbd57461003a5d5d3677814013173af866f927fc5df0a552421b013e646fa6d326864cf26f1ba13c44f2379cda51e390d59f95d06431da4725866928216ce85cf6082d18a99898770c60d223c3db342cd38b10d9d9cc01d990e15997226156536d97e4e296e16e46767089155cad4539cf31624d7555293ad1ecf1779b7affae9cd7647947d0212656a9410b7101ac25a91ee6ae3594ce44df34d2130056e250c1b352edb6af971178087c6782fba4d1811248425235c70e15366af37cf63bdee4aa176d5b87579a60fa13359f5b802da5bb0cb3163118f8e84f43af1f4d6eb347be65873f2839ba0ce8d79b58c0f9ca667b4c5bc90eff1603fc1e7787af71f53c5ccfd51c4c14b4298f06a78b20a8ef91ec64162d9a2f4b961b1fda5b3c3b7badc68318f4564adc185c0a86b2846c5382d4dd725e09e62f75027a04a26e9e2b68d4ccf3ebccdda02e1d18c2f16524e0a587e5c161717ac45c57540a9099a20aa1457a07e2ebef5323c93d510ef72134bef65ebf88f9636d76846d410e2cfe6c53359d846b3404be25bf1b479126cf49ce43b3366e41cbb913d6e169848a875873ce1e91c0abcb4104b483f2131634768c3ac9d81480abd190d5674be9d0ecaacd0b13b10ee
private theorem part50 : 2 ^ prefix50 % Spec.Ffdh.ffdhe4096Prime = residue50 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue50)
    (e := prefix49) (a := residue49) (b := 3341256985) (n := 32)
    part49 (by decide +kernel) (by decide +kernel)
  rw [show prefix49 * 2 ^ (32 : Nat) + 3341256985 = prefix50 from by decide +kernel] at result
  exact result

private def prefix51 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (19 : Nat) * 2 ^ (0 : Nat))
private def residue51 : Nat := 0x2f330fcf1b85ed0724a3f36b0b74b60689962e596123d1652b2734984f994a4e791b0668cf8bda45ca4609d55eb09d4a38e45e0b242ee107fc6b58dddae9161c492a9f23a4b117ca3fcddc757b1fe46ef0a7bf9e6a3027a2108bcee1b672bd8f87cb010737e9b62a35a00966cf8627a9e80b8297547979ff4d53720e5ad06aa89888cde72e911f43a5f1f5a16d4c1ee0e6a722d9c6f0c0ac20def039531bfba801ac09cc455c918dd5d8fa5ebd1d6e8d133258319c36cdc331e22b9cf673f4e09a3418541229e1205017e50d4f7226ec34aaad34d866de9276388b2d4740fbe3057fe1df3a75fa7e96442e501aff2eaa417964c4d89a170af0eb934ae57e242a93d79cba0c9d88f4d86fdcfb92832e87b49341e84a55b3056ebd07573b7c2b94411a1395e968f0947ab1e31f455a0c5b1c9831a65513af233286b99a2738102f0af44c2e2f398bec5dec4119d10cd9ed8941f5eadb4b0785e5bf40087d63ae86d1b1008bc9390e743d96c86d3a42b118e34f448850e89795a16bd6b1122770c985cddb895d73727dc3ff7f63d5553510100001481bc4c55b063f9985c12e1c7df8eb1453143421de59e8b3d21d9cb93b7ce9db35c8e26a1396fb8c23ffe5504be89205ebe3fb43f588a13216cec87ff8b22920c0cd739e926270649090682fc1276b44d7254ff5cf17d408a3fa07199781261c8cd30c82f45e9afa9c226497b
private theorem part51 : 2 ^ prefix51 % Spec.Ffdh.ffdhe4096Prime = residue51 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue51)
    (e := prefix50) (a := residue50) (b := 2004435137) (n := 32)
    part50 (by decide +kernel) (by decide +kernel)
  rw [show prefix50 * 2 ^ (32 : Nat) + 2004435137 = prefix51 from by decide +kernel] at result
  exact result

private def prefix52 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (18 : Nat) * 2 ^ (96 : Nat))
private def residue52 : Nat := 0x981747b6ef8269b00d5f28a85200bf09dc6ed327cdc7ae7e61d2caac09111eae4b14d553cddc45500b91e482529b314a2d92acb43c12db18d5872b3445393c1e5f2a691cdbafd6e8045657f95477d242a9d1fd938ec7043c328b3dccebc5506693a2db29a41845c7c4c3eaf098c35b1c7220166f2e486e686d333847d8867fe35145b88ea15398ba1d937038ae780c2c38e4d1c2bcc415dc3b0f1c450b2e33376fe27c2fcf433172f39fa920c50d85406e69f7d5d41ba4d9030cdc179babce18087c86e78a0523dfa87e93156d213e2ffb702362f9c53832777359cf6011f342e39ee236b1451744f0aa162f125d6ee48fd9a430c7d198f4155b366cae6e288142f1f6886bc547c42c32b400b9dc6e3aec3d6d4d02d839a6fa527dffed5f31311e515efbb045b96fc4ac3c251b9e3c6f5a07f441312f09a4422afe8da7da81619351a507996251ae2e68ebdd64e19569e567ce94bc768d6111f4133664b9d82169cbbd8886206ada41310689c4030c38af9ff0cf85d2ff8366f277d70fb8b4097c31609b9c689bf70e827febf39dc9634deaa834dfbe849e159ec9f482ac3deb6f70bb3c3ce11766fbaa38ccc9c43395814814279c20ab398d5af7b66b7de212a811d1314ddf284b25dd06ce2fc05af370e865931972ec54a91bdf3c1c2fc0f8f31048e95ad41d52af3fe97922f78fff7d4037222162e6010bc43343ff7751ca
private theorem part52 : 2 ^ prefix52 % Spec.Ffdh.ffdhe4096Prime = residue52 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue52)
    (e := prefix51) (a := residue51) (b := 3791592845) (n := 32)
    part51 (by decide +kernel) (by decide +kernel)
  rw [show prefix51 * 2 ^ (32 : Nat) + 3791592845 = prefix52 from by decide +kernel] at result
  exact result

private def prefix53 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (18 : Nat) * 2 ^ (64 : Nat))
private def residue53 : Nat := 0xb91d24f39abbcf2f1f639bcdc393647266775ed0f3456ff5945ffae4a09394a634273c5eb4ec25c78cbf39e3c90534ebc2f4772e8fddd987510ee2afdf5b69f2fe0340da294652e6cf584117206903a600941c8fa520704d8754d9695f24397c1405b77ebf1f12d74598236de875c235c32d0e2ebec7084c4ec1bd364ee5c99d45f36a1230e9dc5ca0a36edfb99d8dd561e8ee0cacd176e528770b2785d439aab2b93b9a971667e8adcc546ceaa711899a73b6d0d5f35d1c6a7494873d0f759f498d541526672e01e5c21a3285b51bb11b5250cf41012ff0153c6eb0581e638f2c469efb5e320a014944623cbc828f2ceb5571e262953cdb36cb33461ba4efbe91a1dc2c7193fa77eefec7832b2f0137aacdf963484f89e794c210f70fe5a4d80452c2277c0d2ff0a7a4fcdf53fb7f48e6b0eb77e218a7de5e5c1a4215c6202c6bc3bbe6bb37051e0a40362398cb57a7986197a3c315ac039c924769663baa98b17950554ae6fa08cac34dd71d6e23454d6ec07789408a4d93fe7f3564b7e607ad0c3cf2be98c237bbfbcdb9deccdb11e96e667878f143004f18c12c33b07dc7e6db5dc2b0e674fbd270b7c99836fcd6a1dad1f4306658a47fb4f519f0b9801f75100d88b4f0b79d4762aabd3b89575a9258d3bc2080248b9f8ca79609a51324a922d2f1207e2c02c8b1974ed09241fa95387301610206e82fb0f31b4207aa00
private theorem part53 : 2 ^ prefix53 % Spec.Ffdh.ffdhe4096Prime = residue53 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue53)
    (e := prefix52) (a := residue52) (b := 2788677305) (n := 32)
    part52 (by decide +kernel) (by decide +kernel)
  rw [show prefix52 * 2 ^ (32 : Nat) + 2788677305 = prefix53 from by decide +kernel] at result
  exact result

private def prefix54 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (18 : Nat) * 2 ^ (32 : Nat))
private def residue54 : Nat := 0xfda78ce59fc649245375992b6dba263987e07de93db1b0e9c8a9dc16f4e579d1d45bc50728acc59e94bde88eb435c5ae9167ae488c4a02803b60b754d3c71d2658cd7543879f11155d23325b4d47bfabb600d9766e3725afd6fa047e8f4302385ecce192481ddd3244f2a1076686f933e103bbb2746811720be2c660f4c30b9f1e9eb1fc1cf7f977b87bfb886212c2f92c16f051b90b54e64f3c1e10d5db095f446e4f90a3ea1170450a60999fda3f0c3f7994c53c3f62bd4846b258df4e7209b6deee64e2be1f15cc0f1df1c2275346d890d8c51927826ecd2138aede25da6ab39a090be10282a00e2dae76e722a2e729bbe184b088d04f0b07f8b61e95bc82dbe461dad05b58eb31c96f21ec92e40012f95393238e99cac3073b618e0bffa16374fdaeabc90b0366bf2c8c2cc84536db64a020840e40c5eabb4629b0d1b62369470f78c606580c15e80194a974a7c2ff5e2ac69a8711248165bbfd47563221b832dd034fcb81e201d39f3a9d6d443320d1b567fd9bdbf55db9ec9cee7253539d917f7f300013c31365524ac32e4c5e92b0ed7bf483a5646a283f48c1f87152d786bde2a9b948c23afa2014f89ed7c3a5c00b83e67f321a1d513465e3ff6104cb4811f8b11c79ee90a72c9d58cb4cfaec5079778f3085c99d874a5f0fdaf28716611115ab4180972d6b45f9735ee6304e11cc18b56a98bb93ed976adecc5f26
private theorem part54 : 2 ^ prefix54 % Spec.Ffdh.ffdhe4096Prime = residue54 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue54)
    (e := prefix53) (a := residue53) (b := 2648374878) (n := 32)
    part53 (by decide +kernel) (by decide +kernel)
  rw [show prefix53 * 2 ^ (32 : Nat) + 2648374878 = prefix54 from by decide +kernel] at result
  exact result

private def prefix55 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (18 : Nat) * 2 ^ (0 : Nat))
private def residue55 : Nat := 0xa075210bd5426753d5ef5f1828d3c9eaeecdd2581fad7f99b0917a244468b1cbe9cb686c8bda1c0f46d078ef6e71b0c439c93be2e04bdd7e54596ec718a7b89a34ae6d47be830863387524060caea76b69280e7012e670d2c5ef88e4a61f043bcafd39b6a2b91e61606d1b7452ac498c95ed6debbdc1c68a31613bf5026e63e33b81009e7c7f0984a8909db3640ff4d2688775751818796f0467722ab82d1471a9ae630bf965204e4911b13bb06bb5cd34c609e647924110a6cbe941f88cb62a2cbb4641469770904ef231d96c525c2e4db77d1e74ecb17bb27ab32af607248b92aa9e374af73ebbca35d50355b16f3ad6f3530b706d1fc731403821500515fa4ff8fc1352a85e0360388ff048c213ce02d378204ecdb4496e6e32cb314c00c58c32ccd7d9986ffbee04285cc89d633505d6a388f23894ae504298d05fb4218b3513fb1027a2dc7289341b11afd281ab9979d34054f503fe9b1f149f91bb522ef7f6c53bb2359ecbc461bd63e7ec74d15425e473be0b1c5b73cd255816f6d8835ab26286bb08ec76e473e0487fa88cd880009d4416ba529814efbc150f6ca342a35856cd00904cc0bc6d9606e5ec4abe349a87b550e55b49c79c909d0ac08b69c45f54925ecd7217b3151fc0b74da1e1edd2db6abd52e024dbdf11fa9b7b517ee96a656591353eda8a069dab51fa3a3dc9552d27266a32d47056a5c666385cab
private theorem part55 : 2 ^ prefix55 % Spec.Ffdh.ffdhe4096Prime = residue55 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue55)
    (e := prefix54) (a := residue54) (b := 392237058) (n := 32)
    part54 (by decide +kernel) (by decide +kernel)
  rw [show prefix54 * 2 ^ (32 : Nat) + 392237058 = prefix55 from by decide +kernel] at result
  exact result

private def prefix56 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (17 : Nat) * 2 ^ (96 : Nat))
private def residue56 : Nat := 0x1020389962bb024536488f6f172f094c93d3659d9ebe854dd260886de9b0055f5074944215f2dc3de52384f191a95f91ab8be22feea42e4422f5e7e588e316398470467444980fe2bd47f15624ef464c2baff1dfb6e9c41c658e2b20e1e8dfb6728609b6a7d289005530898bf0ba976171ae00193310a922a6f491cc22cd8c7c75a5a700c931895a2ae097f87122bdf2358e3ea26fc0d3e2e48785677322dc73b6d503a0f51b2188a1e610b791662ed9b34fc634524ae123bc1de4791b2f51f5b0726c86083a25e8719f0e4a612c057f38fbe5a89d2c3c85a439e320977280045cee25a4e1562a64881a8b23929cf961d7ecb846757057097f5906ef12642b0440de5e58e4092c8f5b93891cd7db100cb48898b1dab0129855a0425b2338d43c308e7f6aaf6d9ed828a16a4c68d2d82294c7dafde9d561c7d9d96156b9a71c2dc9d2a7204fa78ca59c6724dc1e87b8580f071e86fc9907d1d2d249de7d9c18fda4abd74f004a7744792be5fa348bf3919230979ad06b93ba8c5c2e24b055cafb7faa160930fa052fd4561d2d5cb6730ae62c0c0bc6e5dac660495157f9cd8dc5e65acce431f5786c8fb2e09a2cfd53a5f92f51ea486bf31595c84f88d3eee350444129b69239a2e522257ca0ec608e93baf223b0efbe2fea4a08cfad42597b89cc932ce1f47fcfee5d7e059b9262aeac802f75275c28233a116be117d037f79b
private theorem part56 : 2 ^ prefix56 % Spec.Ffdh.ffdhe4096Prime = residue56 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue56)
    (e := prefix55) (a := residue55) (b := 3804723393) (n := 32)
    part55 (by decide +kernel) (by decide +kernel)
  rw [show prefix55 * 2 ^ (32 : Nat) + 3804723393 = prefix56 from by decide +kernel] at result
  exact result

private def prefix57 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (17 : Nat) * 2 ^ (64 : Nat))
private def residue57 : Nat := 0x12beb1c0de38bb1bce3ac9dbaf9930f97aaa399b96cde311276e95a5314db70f91d3f1a64ff0d93e682508315c01d49c28f31dae668d1ef08e86500c55f6d20d7b1bbb5aaae5125bbe768a586bc4dee93406d4c309f1a4ddd183a093716ca69144b4573cffd840f2d31a4c916e1a51a6c3135b331cc2551375ea85f2961370dcfdda436b0629bd168bf496a05e05c7f73f89c79a7caccf474601cfd2dd55696b961ab1c7d97fd61182f5803a506f00179b59bc994c9ce4823eed4f1d285cc060923cd073d09007e67c49e51d3d911161bdfbf0a71e00eb790a8cd2808d213f0ddc5a61cb29de7d16984a4623f9edde0cb8124b1e01db418b9b01c3102a6b4759d852d0921c7052712d8802019e9b73530b18de0cb7d3e7dbc7e039959deb917eccc22888716b5214141aeeba0a123018e30cd11085dee0afe9e4de1d99b72e47c071aff3be849d09006cc1c94a4c58c79759a02dd42990a2f2a97845bb1c97109a4312ebbf212b7d489a98c17cb691a91b483e3f7523c09941b50b88374a1064097684f3cb2c147403e1fdae4d9209b64ea2089dbd6fbb6c22fd967e8d05aee53b49175abed63da6f085595fa1f024aa6e3d833bbd0276306a58d25d4d70123eb62a1279d40192f13715f5fa45e73af81a447334cde295e7906e3d7554f19d8b2a02cb67337247f010eb145d95b5857365633c716f07e144f5d47621d741599a
private theorem part57 : 2 ^ prefix57 % Spec.Ffdh.ffdhe4096Prime = residue57 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue57)
    (e := prefix56) (a := residue56) (b := 3196797401) (n := 32)
    part56 (by decide +kernel) (by decide +kernel)
  rw [show prefix56 * 2 ^ (32 : Nat) + 3196797401 = prefix57 from by decide +kernel] at result
  exact result

private def prefix58 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (17 : Nat) * 2 ^ (32 : Nat))
private def residue58 : Nat := 0xb511ba67b01d678e248f417bcfa8c01a1271fc116646b7c41f542ce4a09d8ec0c7924c0b12b3de849a40a6e44cfdf30344d81b45d444f0d1f566e1fab267974964801395de658ebe5fd7d07442f47bbf4eeec75051adcdfacdeaf6fa9cf7c77aef624a5ea2b6b541a6223ee8c78f313d7276cb653f6b082272e5141950a5fb088341ff5b04a2618dcfa28542180eac1a7482aaef2458cf85b67e2b45a8dc01237e50285fcccf67ffb7af9c70949610d71c49da5f05dcb38863d1ca8e725ecb76ff5fa757a482bcd70c4bc1a4cbec174d4d38f6e969f2fda8646931de79a89f7584fe1d07aead3acbdf61d505d0dc1e8bf49920ab0c1ec9c0aa031bd1f3f1bbfb7c4f8f30b567bd2c18c0b834d050dfa99756ca6a619fad14c9ba19dfeb62ad355b96903271a15bbfc5b2b1ad458663553b67f28235825d98ebcd03f480d33d777abbb9e3d6a68bcf916783b091890170fe24edde2709c074aaaca1bf1e1706b3f46bc334a3f4ba03db48e7be34fdba9cb5b6b27faa6afd1777a929579a0fe1d3303a88394b48aea16fec4a96f8146cc5df88d5c5f26b6915fa266edcf10d37f73b3c6acf356b6dc2584f6f8393b07ad6d48ef8c76e59491da425362348f1c45e198bd277a874a5d02b8c3b25b0d2889c94d1bcf2cfeff90d4af89e0082db7e1cff347d80b5bfe698ebdff9fa91b1680859f1fa9de0fa9cb81e3571f72b66eece
private theorem part58 : 2 ^ prefix58 % Spec.Ffdh.ffdhe4096Prime = residue58 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue58)
    (e := prefix57) (a := residue57) (b := 1668916499) (n := 32)
    part57 (by decide +kernel) (by decide +kernel)
  rw [show prefix57 * 2 ^ (32 : Nat) + 1668916499 = prefix58 from by decide +kernel] at result
  exact result

private def prefix59 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (17 : Nat) * 2 ^ (0 : Nat))
private def residue59 : Nat := 0x78bac978cb7ed5b5a7d4568d3c3f96e8cbcd0dcd5e0225b2eb34b138a83010c87c7bd0658ca3dc31551aae11fcc44911023170b05ca6511fb0d9d8245e93cd582217fb11c496395cc4c1481a2cf6b921429bc9d9140b18308300574f38be1dba1fd1bb82231f60710da9ca5efeac57f8f33f9d93bbfe2f13f1d57971bba2c2373b4bbd136790be871fe1ba261d8e8cfe1753249f6ab119450d1e69f663f075cb367ea7999c9614d4df1578668ef37313e535543993bedb0093cc2078ea7841916a3b9dbfd1cd27dd04569cbdbf50ba954f5b42913b27e5ec30e9b2eaab5ed6896427ed2723592f5b3b62635b2d0fba26b15350c36aea54abd92ea3c34d7a1c47fd39b7bcfd5483726b70f9d66b09c2a0adc48b72ec63a482ed7223120024d0da6142c8e88704de903c970742ae8056d74655f87f3a788c444198ac0a79648fae5b09740d9f5b0ef397ff43e1555566025113503f6279ce6bfe7a2406770425ab04b8853622aea43e96053e2de557647e07c750962c9d166cb3eab83b0d538d53f60b32e03c585d37d2dd826c848953add5af921a6c98688825d142225d850f9da9b5d40e74ae05352ecbbf7f84f9b5c5095f8bdf84762e8e0b1adab9d8453468823f2b58cf2d7359baaa86502df1603c4a7595a51e29581ea88a1c941943304faae2e5ad8bb0e008651527ca8d129ad03c63f7eeab394632a4dff89357544080
private theorem part59 : 2 ^ prefix59 % Spec.Ffdh.ffdhe4096Prime = residue59 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue59)
    (e := prefix58) (a := residue58) (b := 1624864765) (n := 32)
    part58 (by decide +kernel) (by decide +kernel)
  rw [show prefix58 * 2 ^ (32 : Nat) + 1624864765 = prefix59 from by decide +kernel] at result
  exact result

private def prefix60 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (16 : Nat) * 2 ^ (96 : Nat))
private def residue60 : Nat := 0xf95b027bc79fccf3c022a6ba086d191f60b7a55670e9055e82bc2c6f3d371d6b4685ec6cd9026291c2d2a1bb270c0b3f9930db69d59a4378dee62132a9c708bdc6cc94638f627c2460390ff5215ee4b3e9e6d29763dae7f25394c257ec95cd07e29c726cff0dfcbce1eed9ef498086281afed43404f4daaf4ef64188a4913b379c4edd5233435b773f88d3d1855d70e3cafc081e386036d499ec94f53915e3d0e811d531896ce72659f93020a80164af61ea9fde93fca127a4114d84f84b48efb852e28a0fa1bc751a7698989559e9fb1ef5f0dc14ec4d9f299739f7bcdee9b78b721911f84e259b2248bebffe0899893b37b3513678737dff2ada81981013f9b7778ee0c53943e2b617143cf68159d33df107817b245fb6c8ce19c8c587aad97f365828d78bf0c353fd34658ff4b6de6182ab7c392e11db842fb319c5959dc890fb329a4fc2e5ba5225ebb8064cce76c194d4149e640b73033a4672f1f673b8de8ba6c6416398cb62c44b7f0c20a4920a5f20c5c54c45a2c7665b16e3de8a80d8dd12392ee20e2c31fec79af2e5c37a2382afbc5aff817a30b04071760d686fb8e48dbab82b40cc831c9d0a831be7dbe76cd7acfbdbb04161b09a025ca80e73b4473f8465fbfccd6fe8370b9a70bf1eedf800262bd6adb88e6c784229e722a998c5d4fa29fbf5d9c4e682c410f2e6c374de6a53561c07718a29f6f6484f9e92
private theorem part60 : 2 ^ prefix60 % Spec.Ffdh.ffdhe4096Prime = residue60 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue60)
    (e := prefix59) (a := residue59) (b := 1144365340) (n := 32)
    part59 (by decide +kernel) (by decide +kernel)
  rw [show prefix59 * 2 ^ (32 : Nat) + 1144365340 = prefix60 from by decide +kernel] at result
  exact result

private def prefix61 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (16 : Nat) * 2 ^ (64 : Nat))
private def residue61 : Nat := 0x84ae1215950ccb6c744caa5569444cae82546788d1f911775862ddeddbc80873b227933d3e45a19cae3cf5b371a53ef6d27a28808d808bc3bee38a10f6242ad5a537d67912d33fe484938f42f289333b00a277619285a00af6d72a3a8946d579cbd6ac6af8869ce0751b3e868ff28f324117f8f08763648ac5d7fcad15cca8e270138f646a7a5554828dfc8aa0a8081183d911dd451395a2c5810371dcae8de82d6a6f76ba8d5637f921a036ec1b438929289c814fd10a141cf0dc863bfb86caeaba47431f9c61750c6e49532b93f17be3993c487fd977d94a2006f3496fef441ec5e8cf356f7179276af5da57984b54c98e66248ae95828de213aef951afb22707d77692b58ef45d2f1a2c84db24fb853186584be5a314f7feb2ae46d6b7f9c4ab88ba4c336158ce574e4ca028b11e55951325f171b3e2e5627aacd4e369312da6058e6c26218d329787b216497807ecd29f91bc693068ce65b10936b299f5ba58e077c1c88187ef9ddf2e933dc19ba3c7c53d0e76bc089905c5dc63ca6bfbe03d1e3293f7f9820013e4bac8113a92d1338886cb1f7dee37c8e945923195de1c1001fb04a51216ca65bb8f5a333084405270e22b9f79c7a2875c8d8fd7d934a3187d6a981ac4a642c72e6506df1b131a7fcb1cad532904a09765a8ebc29129d7fc06027d576bdac20c0ba876857d199dd44b17b9041742981a9bdc50afe03c8
private theorem part61 : 2 ^ prefix61 % Spec.Ffdh.ffdhe4096Prime = residue61 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue61)
    (e := prefix60) (a := residue60) (b := 814737390) (n := 32)
    part60 (by decide +kernel) (by decide +kernel)
  rw [show prefix60 * 2 ^ (32 : Nat) + 814737390 = prefix61 from by decide +kernel] at result
  exact result

private def prefix62 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (16 : Nat) * 2 ^ (32 : Nat))
private def residue62 : Nat := 0x837885b20930087f250ecc7b8ef42c9b5e12bd73a706302bb1281e7663f4812b5e1527d3230d1627f6d97797e405ebdc9a9740858979ac8f6f4b663f044be536cb66dcbd4a613ad542a59dac91513b7da8345c8957a61c0b70ec3c6df8633f801ac96172af8bf6d3255817026c97f990aaca16713fd64865dc7c1ecc4a3683141a7a8517605ef059931620d43a9eb494ca73dfee1a1c4e21187a51e33d1e6919fae39641fea72ab387ca7b60f1ae14033d3e5bed711cb3d1c02c5b4da2b07a952e15379e7ee59d7d7dd7bdfe7949df74bb3f23b77580ab255f20b93c80f611fe259e2df56ce3a6d67e443c9dd146485ca8604b457b82ea3bd7d230dff8cd9ebc25eab15b3ff29b1abf3b3a43293ee7ae91c2ca33ec5c278dff13e4794931ba2de2282d7da95a8b7a3466d0b935b106b06fcadd8f1aa7017c6799c321523fcd4bd10d06cf1a570990d4ad2c2cb429d4ae8f1a39c43929a76dc8555eee2bcdd1e0c75bf6916c826ca339e141aba2817f2078f0adc0e00476e2a32405de56e19fca991b548ae66a627d1cee81e1b598003926da35fd7bda8e80b53ae45aedebf9f73bd7e350d4ab69798b9579e2f020062be40a5ffeee5d67de0b248c3c1da2850bf47551464ca928bf45f9b09a59d3580cbf2274c70d5fe8331ebe19939b6617c8181dc5c89c48ec9bccb82131c47f1f37bfa16124ada6c8ae5a99b042286ddaff
private theorem part62 : 2 ^ prefix62 % Spec.Ffdh.ffdhe4096Prime = residue62 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue62)
    (e := prefix61) (a := residue61) (b := 1864019357) (n := 32)
    part61 (by decide +kernel) (by decide +kernel)
  rw [show prefix61 * 2 ^ (32 : Nat) + 1864019357 = prefix62 from by decide +kernel] at result
  exact result

private def prefix63 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (16 : Nat) * 2 ^ (0 : Nat))
private def residue63 : Nat := 0xbd6332e8fabbe6ab5fdec083658893883ff1d1cc918d52a1fd50cf4cf8bc6465f3e3aafef0c27977284c6d6f81e1d0fc9d6015e0cb2bb7255237fe95883ce26cbb45752db9ee2f3084e9bc589e08245c33acd0e51dbe4a37b12f54535882148e21fcaa3f4b5add0f328d971c499c7479c398058d4697065fa59c899b2912a9309d8839a57f801faa9c0fd795c5893db5d0b272e90351b5c705561bfbcba6c1d672db9ef97aae6caaf6a51dd68f0f3611464c44cec27aeba28999d0d59d9f12216cbdd8d7d10f8aa632fd01ced19e913ed87f7093ae8c340304b77c2b92be8e54cb48880ef1f98a6cdca608fc638bfcf6a26d4eb3daa5ba6706f6ed6479ee577e3b602e4fd97de50f60a1b66cc9e3e590136e926cb3db7f06411d9e3a7d7eba6ad5de05e02947e90bd39ff6f7e8468fe5da9e3a7abf6e45d8f4e695f3925850e04240bcb526b7384847f8fe91a24fac78c0ae78af8dd733a15be1e087dae1994b0f3710d2312ffd5f0ca3591df8b9f1010dc66103d05f2917fe28260ec6f9449480219f492c834319974b28388c412ebc31ceb503e6ed994be6e58b9215fe5a28ec05dc9859346469b98146f527d8f25a0f13368db1cc139f9751e285fc74df88d05967247ca4e2087f5931c06b2ea20b7518b6ab2cc36cce6534be9f7bf5ac297e5c3ecbe558147d341cd51100525d8a424ca608aaaaa3ceb39dc6aafeed223d
private theorem part63 : 2 ^ prefix63 % Spec.Ffdh.ffdhe4096Prime = residue63 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue63)
    (e := prefix62) (a := residue62) (b := 2995552685) (n := 32)
    part62 (by decide +kernel) (by decide +kernel)
  rw [show prefix62 * 2 ^ (32 : Nat) + 2995552685 = prefix63 from by decide +kernel] at result
  exact result

private def prefix64 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (96 : Nat))
private def residue64 : Nat := 0xf6514e31993d2481226a20e9bc74ab5fc41fb65967726c60b0a06cb540b6ffc0a7c15dde4f60c4cae84a81d6135d55137dc2d46a35b285d8ec08e769fd0b44f81a70d47a28b7d23bf0ce34273289ce052783fabfb056315ad5b77a0ab1224594248701c876dc72dfe8bbd37e189f062dac40248a4f090651bd29c55abc9ab36004b9fc643d013cef6460afe38704802111a4b4b123e848ae84a8eb0b713bbf37cb3b7754404e0df71786484eedcd7daa5cc1838142c40f960f4bca8f89cf827395e94f36e9e6ef3a3d62d9bc2f88e71e57b9e28cf801bcf7db58c68c8505bb35593ef2dc9b4128a2d63e12e12c6f72a8ff597156987debe29c8ea7b678c9ab979a0365c0ddd57e0415715c8b6fe9cf2c64e821461706873cb7bec82131c18372a7a460755f29da03c70fddf9c8cf42443fda0162d6935ef60fd6680614daa82ce987ff5f10364480df1d8f3e0531b7c591f5f8ac072cbd1f19c94475bcef19ab659c72dc5fa72431c55c600f2742f8ef93c90715cafea662fe0238455aedb1165e52a8069cfe286ae40974b14ee0aabcce8551fe94594d31101de070b469ef77b45895b2872490707ddb35f28ca63e8a49893eda2306fc230aa3ff453d4f8c113db0905024cf37bf7971b6b0b5586afb17e04aab6758eef68c3faf00774d4b4a7296546ce52234b6380319f753cd9a15cc4e94cd6a845bbedb18a36966a10e2c
private theorem part64 : 2 ^ prefix64 % Spec.Ffdh.ffdhe4096Prime = residue64 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue64)
    (e := prefix63) (a := residue63) (b := 3726277231) (n := 32)
    part63 (by decide +kernel) (by decide +kernel)
  rw [show prefix63 * 2 ^ (32 : Nat) + 3726277231 = prefix64 from by decide +kernel] at result
  exact result

private def prefix65 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (64 : Nat))
private def residue65 : Nat := 0x5b043de226209a0bdc21574ae8ed5941436b4d63b19037a7df57980b2cfa72db1d6bf241a10173b2d0a3df241b9d460f4af07dcbdeafd137d2c15081bc7af9ff911e3fc7009e27799d3e66d53cd707395ab5ddf7fbd64259cc2fa2c5ed8fe2c97d1abb9b0826fab03e143accaea6cd21f56d197ea41ceacfa68bf6321a9460b7077ffcad1fd087ce981755494b2f83a0ffbf7488146d077e90ad36c2ce7be83d46829a23239e67935c02a6f6c95f3725e9f7de874718c1c646886c1704420eb094261aa221fc6c831ff8adf67abc3e61eed9dd6156f993ae28dcc2c7eab0ad8202672ba0ca0e7d2bfb46a0ee83e363b112e6f9c1dc0455a7e3e45cfbfdb624c81c479c64ededee177f7e6dfcfbb3fe01beaba61717fd7f6fe8253fd7f78569ac0e2721dc984464436f260f6caec5373680092861d5e6f5d05b0dc08bc4eb0e237a3fb3a446f35eb08281f804e980e98aded73bdf962df08ec690543f149e1b7d9ba00be947028877aab6ea0fe8a6db802fa1c54925847d7a1b00de88f318d9d67968e56d72f0ae9f2dc712a8c7ae756e8153351b90756f75c1cbbc7e1df1bff57cdf8dc2baedf1447480d0551ddb8172428a8f7eafb9503146ec13a9c12c850814f1c12d2c1d5331b3b3c228b272beb7ed4ad7ce186742ba8b4f224f3fa2981bf66fd16456e46986eba0dd805b9161c10fe90e8b17ddc34ad189989921989b1b
private theorem part65 : 2 ^ prefix65 % Spec.Ffdh.ffdhe4096Prime = residue65 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue65)
    (e := prefix64) (a := residue64) (b := 2093875484) (n := 32)
    part64 (by decide +kernel) (by decide +kernel)
  rw [show prefix64 * 2 ^ (32 : Nat) + 2093875484 = prefix65 from by decide +kernel] at result
  exact result

private def prefix66 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (32 : Nat))
private def residue66 : Nat := 0x9f64ddda41c9ba3ddff97cee9e53ba9a3f76d889b78c07d122dc3afbf061c9b85524cab6aede5f9b7f85bde77868341056479df4ce99a597390ecd79811a4ea8fc0f6d6b14a61fb0cba55b8f50539723486ba2d6ff2cd667ab38c0a85221879de9728fc2bab2a4bdc9f3303083ea22c8183d5e588b6de62cb80391d4e3a6be4696d7caf5f713bccb24a1424790418f8aaa6fe29c83f3ba4c8b95913792a543071a27ca36624c3c9d83b4f4d9b7daa29431a7620d9f6e9131719f3012ca829ae9363d958e4f044b2c9556f8b6b335146f4ee2923714ae769e20fdca114e65fcba4f782ea1c84a56fee1f5bfdd9372c69f757b3b755ccf105a81d45381e788399abb59b9e7e2a8b578de5d2529558050f2c0c41c00cceed868b9cd62af170e598b60d02efedf96b8ffc900395df3b3abe1d0c4b12c5e88f73f91d447b2071d2bd4c479befaf65d7e91dea469df730f834f8d94e4d86a6e61a60087aa167aee03a1cc5a71439b16401359b988765079ba9aac04cd5520fb3f9dc27a5b31836bc3152367888400d91dfaa202215b2b42b07d9a44d84b6c0bc3d0c21fb04dfd4fbb19101cb11407f4976c3b7d46e27102d184af85407133268f0f95438e18dbbfe519d4f3719f409c88b4ef8b160cf1fe9c503bb1b0ebcaa2382cb36ed383c0230e8cca83256943bef99021d189514e596c237fd182724a6edf83c45c3212ec9c4442
private theorem part66 : 2 ^ prefix66 % Spec.Ffdh.ffdhe4096Prime = residue66 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue66)
    (e := prefix65) (a := residue65) (b := 819607524) (n := 32)
    part65 (by decide +kernel) (by decide +kernel)
  rw [show prefix65 * 2 ^ (32 : Nat) + 819607524 = prefix66 from by decide +kernel] at result
  exact result

private def prefix67 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (0 : Nat))
private def residue67 : Nat := 0x4c1f2f122c2fd6151780441e13cb36c54f08c915a39debb14129155f69c2cca85cce66af0cd3fa7f666ac321080b288d8aa734e710f631a87cd0f165970cbf9dd2adb7de6251dcb073217aa5326a2ca946146582b6018dc33e48772b18b3e5d26bff58cebc6d6337ea082ccdd5f52b3ed9596a2abd497bb218b83903e1c53f5011e914aa59321eb4f7dddaacfbdbd1dbcca55ecea16a821a0359e05b5e75eb24632bae35a8bcf1393bff7fe9b93a70147eaa752ae96435f498dac9f1bc0fcb3af87a37a1f0e30d20e4efc4d27d1dce69e3448c44cf267d4b8e209b544d6d89cdce5124b6fac9eaf38fe82e837df8b49c7d49ba184a796bbda00b9ccf9948ff0f6dfb77c7f0f577436c04204db76f2a1f29e1d3c1cf8ceda0bdc2c9c8c2be078d3cdc87cf6768e1abd0223ed727a985adbb1983bd4054a6f99eedc359b6b2529971a41bbaf8e5192eeb537c8bb30928c17628789355fd016a19ff5277b0db27a64f635276ad4a0b0e7ddc3ec6a28e6cb19b7b29f68629bc2782d983eb9a5dc9f6716a42e529224253483168b7d98f6261deec3ca4f1e772f22eec17cbd9e0c79760956f693b2a0b058a862c2e4fd68c5fc65d637ad57c8b7ccf73de84ede5fb2c04f909d1628e3ef8a52b6585b987fbe611584220118461271c44c42802b2bcb3cebcdabfecc6ecc286e30592f382f66c1d1aac8476d87de20549e5977edde15d
private theorem part67 : 2 ^ prefix67 % Spec.Ffdh.ffdhe4096Prime = residue67 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue67)
    (e := prefix66) (a := residue66) (b := 3950208131) (n := 32)
    part66 (by decide +kernel) (by decide +kernel)
  rw [show prefix66 * 2 ^ (32 : Nat) + 3950208131 = prefix67 from by decide +kernel] at result
  exact result

private def prefix68 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (96 : Nat))
private def residue68 : Nat := 0x9410e8039eefa6a8757e687d4ac9882f10572fdc661a48cbe5caa3db5f4d9c44f6f849ee6d402856b544601d311902e77ef8ad1c1f29c8f506f5ae4f1d83c6827d3ed9d7688aacbf352d575761797c308239bcf6e235f17ef86d9ea9fdc9e62f24cbf2eb583e869ba43cc539a09d62a16ab41cd720d31d5e332516ab16a056462023511674ec16f4251c15ddc868475575efb95c4b1c215dc1e8b55d8dccd2feac6a529b58e8741769d52af1d4593584da02dfa3d409b779fe4a1e5fddd564c73c7004761170a2ec6e950bd7dd3efd9df5fdc3564cc944c4c0bb0f51ae01c138a004ee3591dcc23f875838d062863552e2fdb5a2e58f20be3dcdf5b32c4abc8fe404d8c3a99fb42b385cc0d9e72864fb7f01468986d80464f2de7ba548e883d9b40a7e08addcf57f8af9161c4b4948286ee8c1b55f0572ff7dba5d3e62c2addd1a70fa4b45a2f808fb8fc9b116c021e384f7893e761ce7b07be47662aa1702226c618eaaf952901328a8eb2014483e887ff9d75582249e39284447116dcefb17610678d623aad657a61f3307551c008a8a9c772575e36a0f192ee957bba0e4827fc79dc5618c46744873725752eebe5d36eec703cfb1c3f5c95e03b8337e8298bdc14631e36b225f0b177c462e1533a11671d3192a3dcee6ab9c293234308d0f9ec5a8929fd3faea71d14b39e313d5f03906a191801aa5c9ce02164286cd32a4
private theorem part68 : 2 ^ prefix68 % Spec.Ffdh.ffdhe4096Prime = residue68 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue68)
    (e := prefix67) (a := residue67) (b := 3178008211) (n := 32)
    part67 (by decide +kernel) (by decide +kernel)
  rw [show prefix67 * 2 ^ (32 : Nat) + 3178008211 = prefix68 from by decide +kernel] at result
  exact result

private def prefix69 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (64 : Nat))
private def residue69 : Nat := 0x228c6860ca3e9db9a64d1feb6f73146fa2347fec460358992126de3b552d5d89c41215a3a08114804da6a60d2f2fca77ccbff7adef93a3be9535a9e1f4b87f0876236a97a813b9388fa2b7f7259b9baa0044a6d3bae06bfd55d733ae9610db98d11df7d4c3cf21f82c44802177de9418a966e581e5e6027aec4148ffb75f64327322d26526743c5c557bb07f94b339867f674e3dea903d46dad547ff4a3ed340f7bda7bae6f9f3a6259cc67d48c0a5c0414ec373a8438cbb022f9bc8153563d9941cdd02e8fb98f54d77433118bba806821e2096d4f3f2d77215c208ac29fb79743851b736cb86167fabed715bacc284a275fe7aca9bb3384e22c94232c7fa3da862ff3bcbaa34f1e0d2a75850cc935ad61c97dff9464ed4745dd979bc467060e8fabe384f427995632fdc7fa1df38c00654d0372dd975982e996d6dd9533cd7a867cfb8450a408debb863438f41a1485fd6a4a3fa7d4c633fcf94de90f97e548ec4b6bc488a0dd5d2ab2c41de01b4dbd6c6ab00d61814c54e6beab68b923e85d8ce24edab565aed6684028951ba55d796d7e55ebafa843b1f1e9bf23bef94b5a0bbaccd496171138e866054d2e578e47146bda130479a9d7744317c4aa46f3be3b16f5e874205a278a7360ec9387b6d79c0fb61ce0f85a1bda5999132fd0134449e8dfe99b4fa83d4b74a97b15b725601850e1a9703088186830a5d4bfe98c4
private theorem part69 : 2 ^ prefix69 % Spec.Ffdh.ffdhe4096Prime = residue69 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue69)
    (e := prefix68) (a := residue68) (b := 1224473591) (n := 32)
    part68 (by decide +kernel) (by decide +kernel)
  rw [show prefix68 * 2 ^ (32 : Nat) + 1224473591 = prefix69 from by decide +kernel] at result
  exact result

private def prefix70 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (32 : Nat))
private def residue70 : Nat := 0x3b6aa263aaeb22f232f4970cd662823650e0caedaa9221b8fca6ccf8aafe0b3a72f64b2a472702350491cd133046bd21921cd6429b81d46f7935eb20dc47179452ca98c924f4d56fb796dc8aa338b679456cc481c8ca2e87a67551a327996fe487497f5d85c1071e6c8000410ff8fcf773f52d175f2f1ceab11c52842d148aa12e29ca35c91b6108f7a1c6e9d05af9c352dfa9d260f7bbfe8d1ddcef4d148fd47aefa14a2b9cd1516c7393ee3d0ee155ff4ab2513b8f44a828fb40c29f9a68380d480bc78e321884cbd406e6a4952b5ef805b9fcdc758bd4a2f2674e672ca4856d633d4afd55eeff67777e4164b679db134875f99ed2ce329b006384616719a6daf3e8d62e960f16dc480ddaa27571c78aa7e79e4ad1b9ea782a26b6bda18e58fdc4a45227011d4aba6d01b3401b4df87a99907c078da483d39ec1f0922694aeb5c90e3a41ffe4446951272e0078e668a4dca802ba193d01ea893e04c03fb6b82eb26f10d4da3419653626423ca52007ac55b126d7035cc293f3aaadc688cbacd66e6e80bed2411e4b121edc57dd22d06ead28f891b3ec64bf05ed514ac1cbe206929a56dce27656d0ea92e426c018d45d046840ef9aaca4f6ba84a547f6c93b42d801a93a298f872d2bfa43c492c1c19649f93964d9172fdd89e6a7f92c1ce42436d03664815cd1a8207934108ec070318680b9fa3acab4aa774ff87861aa02
private theorem part70 : 2 ^ prefix70 % Spec.Ffdh.ffdhe4096Prime = residue70 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue70)
    (e := prefix69) (a := residue69) (b := 751196285) (n := 32)
    part69 (by decide +kernel) (by decide +kernel)
  rw [show prefix69 * 2 ^ (32 : Nat) + 751196285 = prefix70 from by decide +kernel] at result
  exact result

private def prefix71 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (0 : Nat))
private def residue71 : Nat := 0x98a1718d3edf2c224417cf2f0ba30adb2485d342efcc6cc0e3dbd474e6b436938615f7850374d9540742a61bc2203f6b6c5fc2d50289e577ec4772006720f26801ca28c84a11c5411a20a33639e7a7c81b2915356f443b4e441deb62daeca5488b53011bd7127592b8114795a0a2225e2a06d7d9cb42e1ecd7cf9ce2e311e08f9293cf4cc6f25a53fcd3cb1b20ede11dae5fe714e882a46d808b19c1e7206b8ae30779bb281a3b86fb08deb476018b4133c614c9cae1b289deb3f5ee3ec99ca62fca29c4a49dc8f9e0d33bf26e347eee167c93f0687d486d786b0a5de09244753b4bbb94b5474ee4b6856478f7383c31b2a38509f9023f9f70dc264794e6c80ec365f98cfc5b295a79371ef4a2d93e2ccf64c39bda5177029cc307708eb651858b3c181bc673a2307353ea75fe6eb6b16a2788b19a04b85d477e18b04d46c71a4a046710a2c08aafb9bb6040ab60b6065ff8accf05074213266936d4d3161780411c62014cde296f0d1d9b27ae3bf927beef76a88025ac494ce316b0d4430bd2233858253726d17941b7352785bd899eb042b6cda108ad8330cb8b269f35507da9bcde8af6039128f7f36046d36142c2914cf3bd26009feeba6725faf1ae66c65e8ee7ca0d9c93ead73c96c8de6fc78dd6cacbdb4902c37b0a7c8f9aa9fbf1dff0cb2635da77e363ff7cbd369918a92bb8cc77bcdba4f93540ac7e645bed0447
private theorem part71 : 2 ^ prefix71 % Spec.Ffdh.ffdhe4096Prime = residue71 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue71)
    (e := prefix70) (a := residue70) (b := 1623420046) (n := 32)
    part70 (by decide +kernel) (by decide +kernel)
  rw [show prefix70 * 2 ^ (32 : Nat) + 1623420046 = prefix71 from by decide +kernel] at result
  exact result

private def prefix72 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (96 : Nat))
private def residue72 : Nat := 0xa58bd42385d8133c574f155d2ec9d8190403bf9c81c1f56f4780663b6ab31970ac5819bd4c444c4b38934a3bf71c567154b3889d6b1134be0f3e4e435822def5d8e375e50e98ca178f111f8ab634d6f0bafe5e89fc7cdc2acc9c886c748adc54415e5826f4a30fca95cac43fb9050098bb58198f8bb5e1c5c54122944bdf7a3b7bc855845c3269aa7d2a971ca1671ae96412b5ff41976f4b62915d5650f075bf63c16484951ab18940f0341ba5986b87d6c6d45b3140417d3dc3c065b11e6b05974bc9cce4a5dc455c6ef6bb90fe5cff520ac24c4df78e3755cd623c8405400892e0a662d50ed917043aefb36fc3bcd0d004f4e5cf3f6bacc042fea397547121d2011cacf02c0b03f13d599497f7b56d6f4c99258aea8fb139a64b6991850dcd481b92b2e8b664fef1a6babd5ea1e540a24c48c687eb652018479bd6ba4c3dd8ad9fb0368e4fd423843784e461bda1f811e935edea08fdec1f2eed21c1fd69c3852211150c113a685581825246556af532cf5c54758f10b9cfec0892b0cf47de8b9800a9d2543ff59a8d2f06ad7753f9e9607dba5c425ba27c260fdcb817fb0e34eaa630377af2b3defebee24a6142e0e816e7b6a8133ae871b92dd2123a167318c21625e92b4ba2ad66e882680dfdf43511c36a1cd988e57c284b04952778dd4ff09c1cb0b7bec2e21036a3dc31efc1c2dd2e80b4a6f51012bd95d3ea39b3d4
private theorem part72 : 2 ^ prefix72 % Spec.Ffdh.ffdhe4096Prime = residue72 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue72)
    (e := prefix71) (a := residue71) (b := 1467943300) (n := 32)
    part71 (by decide +kernel) (by decide +kernel)
  rw [show prefix71 * 2 ^ (32 : Nat) + 1467943300 = prefix72 from by decide +kernel] at result
  exact result

private def prefix73 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (64 : Nat))
private def residue73 : Nat := 0xc658a72ff0d52d11bb4f994c3b6d68920821d0d6586374be77d9b438749c054c06e13f8ccf7e5527e44726cea3061d964c440f4b632c26fce8fcde5aa637bd2ddbb5c02f4d77356151074f6745ed70d0a0ce14664f2cf94df9c6a4ecb9d59de742b0b5645f2af23fa7d33339941859fd100790cdfa10d4e126a7792a3159e5a3b01ba8372e96e622f7821da34503092991716620ac9436bbb201a9127b0a495b00484575ad2fc744a58e60c706eda77e184d577dbbc10ac9db370eb849777ed76d01b050085e731a993434602137e44af40b908f15eb608e8988ad3921c24ef3d7656d4962fa0ed524bd9e18e735bc5f76e1460b14790ee768aeb076af30d8bd0a4a832d031b7b90b7d2ac62acc261e18f0d3883c5803a06a9afe7908bcdc6d5be00e45b4d053cb78c1f20cd5dda6d0762239eace9ac354dcfcf4572cbd415d85ab3d866db7f566aabd49bfe4f217eec01ad5610a7445e56fbdd093de7c3835bc5485c5249d45e640eaa085cc34e53a9e10a3b9397c81a815c46de065feac7f1827d11c3b071c34cf16906a1ae5859482fd4899170e1a453fdc4ab5075fea8d60d0385a09006bdcbb268c475ba5f60fe6977d07e230d083fbf0bd06902271dd21965376b36e854ed5eae609c7288641be667054cf8749e4f38be6f782ddc83441dff5ac75ba675d04b0959af9fed9923bc0e688441f43e9ece9e46cec8e395f1
private theorem part73 : 2 ^ prefix73 % Spec.Ffdh.ffdhe4096Prime = residue73 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue73)
    (e := prefix72) (a := residue72) (b := 3263809848) (n := 32)
    part72 (by decide +kernel) (by decide +kernel)
  rw [show prefix72 * 2 ^ (32 : Nat) + 3263809848 = prefix73 from by decide +kernel] at result
  exact result

private def prefix74 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (32 : Nat))
private def residue74 : Nat := 0x44101a30ee0d130f5affc9b35efa7deeab2cde08b632802fccb217f1ae6c10b40d292e4803ec40554aad37e2ce51baeca527a2f4d0e96db0ae14d6577332d48c0f198b2b13d4a2223e9a47140a4ada2198ee8b3bb0f9af2645a04fa9e936539249b62e841664c67f2e8175bb4044519ddbe263a1700fe0a13226a2a06e1cb06340452cbc7e6fc2b591d460ecbb339eb838156dac858bf648055ba624b7b9105e7ce98349f31cf9e5f569ca3789f1edb9fb164034ca6d39059f89739a496eca3eea3e81bbca1e2911ff7b6e6adf1e150bb1f4b02e9bd2693f8dcba8412c55d5f7a8b753371b25a921235427f6ed3672016500d1d2a960af1dab6c1f49c2bd5e8b54bfa4196e0d23132781feb4ab47bbcbe8bd0e35bc933175744518d115328f677f1e832191a2e96cc0de2dfca67dc53acfd450756c1857088a9b38a0ef23c68f4d79fac4b8768030721d3724747a7f5bd796e0e47ec65e284e752e10f333028011e6f34e70ec0ca6a040b5ac4782efed3250aa71dbf3ef97f8c12794e854427f169224b0333c936935b10fa8adc016daefeb7c643391cb69b371ed15d994966bdb2a4c36daee4d0f3231f76b1aaae271fce49577fc49ebde35e056198223ded33012b134c40349c3f8e8356655cdc0f636e9e3558b7f9535f7c7fa35177aa498cd86aaba780a0ea94c68d912e0732c35f42a4c21950c9fb692c645d77228cf98
private theorem part74 : 2 ^ prefix74 % Spec.Ffdh.ffdhe4096Prime = residue74 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue74)
    (e := prefix73) (a := residue73) (b := 1510573641) (n := 32)
    part73 (by decide +kernel) (by decide +kernel)
  rw [show prefix73 * 2 ^ (32 : Nat) + 1510573641 = prefix74 from by decide +kernel] at result
  exact result

private def prefix75 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (0 : Nat))
private def residue75 : Nat := 0xfd5a81b2bf41f90e09268d5feb3099c4b1fb00b6d858b3c38449107516c15b4663bc5ce48fe23f9c7f0d5abdee4e4cfb2e47bc106f136bdc717b212f2c04d029abe11dcbc1cd30e6d9bace2e48a0c02af31593c3219deb6000f824e869071393a765634eec244d596d6ac71e43ae35b3eb582af2de86e7c0416e2e2f37e9333fa6aaf125dd45fcb57ebe960e5b45aaa8310ecc8b475832dda649442aa2e35c9743e7aa0cd9e336a4ff54bc31be215149a332d6a0089e65e92d5ed71065d5b279b45ee09df5d76907fa0889008aacc1762f149eea5df02c425a9337fb5d559fb0b93a1f32cb08b1e14293f64b59d3c62a8f1ccc3a2975217a610b7fc127b583eea5dceee1ae4ddb606a2e7907e6d2d9d19fff2bd5bec6621d6fc0e4ce6dae7d8c2563a5f97bca5cd97786aaeac864d61747f44eed326ae0321b893b2b7cf76152893dcd42fa71883c515ab46bf391336fda4ba214a7c8dcd8aabd3cda01201c3e409a99d591094253cb238d859f2610fc2c53955bb6da5f7d9b4538dcedad7b95130e8e0e8902fb6beb8a2e10e5beda7349d9c47fc153fdd4669873ce7ae5a993907deae8ce28d984a702b094f5372bc94c32f08e9c23e4019edca951c548de7b53f1618cd456e5b76265ae0055ae8baa5265c5167345451189a371b088170d55e46934222f38e5ecf727550b5265b103c115125b36d3c2abe9fa78f9943b0c28
private theorem part75 : 2 ^ prefix75 % Spec.Ffdh.ffdhe4096Prime = residue75 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue75)
    (e := prefix74) (a := residue74) (b := 3726752930) (n := 32)
    part74 (by decide +kernel) (by decide +kernel)
  rw [show prefix74 * 2 ^ (32 : Nat) + 3726752930 = prefix75 from by decide +kernel] at result
  exact result

private def prefix76 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (96 : Nat))
private def residue76 : Nat := 0xd4edec96bc56e50b235c51ebc0794280d5b8c9f1dd26f36aac8fc701f653ec4e89de6d70c612514a04dd45a4e418ebe77ba6dff19a98d970e36535f644417e800272e5e7ee1d4c6079f5228d06202ca5d5ecb4c67aab804d45f60de9e4ada1f7e4215bbe8d6cd2534f477ae81d78d5cc48d43089975004b9ff60331424020f266b3aa7d7d56432506cd0b00e9b33e1be1afe357b1c9514824b0be4bd5ea4f5b66b85c1e6b8ee23e301b191facae130491c3a1937dc102b13210bbe3d2a64d9b3bdc1a7f47ff0605e2bf4d46e843f71c86c150af54b53577e3e41f3a586cede2d76c138e780444f206e0d8a1531fe983e920f8fffa47f548c8eb29292d020a7b52d2da4654f5bbea34407a1500ee3e724316960f5f37dea24bd6708936144913a4b062ad207107ad49be8226df718b619b2e4b42ef8677ff7c9164d4ccbffa8b73a6fd57f1cb32ff33893da2c484f706f9ff9f5e3beefb9d02f7b4f5f08652d0baba2212ed2e6795fe83b066b62895ee92f49e3d9f8ddf2f90d651629fc4633c0ac90ad492118f5e04a4b638e9734a0afee723721d9a207ada12ca49c27f674425672bbd280e2f637fefdd4097a0db026a5d5120c20094ca09bbf2e2eb30df482d2e1a8bd0be47ba4f6316afff30a46a1d879ae0172a631c750bccb87bebdd7af310a2504915a58aef3a13c436e170c0eec23f6f9bc4036ab15d731acbc91b142
private theorem part76 : 2 ^ prefix76 % Spec.Ffdh.ffdhe4096Prime = residue76 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue76)
    (e := prefix75) (a := residue75) (b := 2055119401) (n := 32)
    part75 (by decide +kernel) (by decide +kernel)
  rw [show prefix75 * 2 ^ (32 : Nat) + 2055119401 = prefix76 from by decide +kernel] at result
  exact result

private def prefix77 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (64 : Nat))
private def residue77 : Nat := 0xe10fa479c0731cdff740c83e7a6e451d8dc18fbad89360bfd885b32e84024ae50ec558f0a191cd67231f664a1b724008d9e2e4927d743e9021b0df37ffd0ed6ee8336c5f43d94c671bd0f871f10c24cb4905510c92fae23e8b59cd68d1f8bda2065f5310b318f5529ce07731de19115502a9761eeeede6002b334e113971cd48ea8a2d939284ee055b51696cc950e195ce9b9882e805e3e14f5b10ac3ae7d6d32038bade34f176e8802c8fede12cc68b797d4c60cf1a7a15914d2619f49756ee8eaafb47c62c18d96d93309e4c029b003c140594728a377ef8271b94c5f53d7852638ea562142cfc952eca4acc484c4ae17708afbba3ebf7112e6a7c576314f2d94f517f76859c2f46db54533af8a61c06b41c62958c748b59a2d81c4a235d358be4309b2179655c7747571bcd172168f6600a4332cb3d24cad6230def5e14e3561d4062c6c1c2ead416967173a85fbd37d2f3c8ac3510aa14057dec75696f14bb635d8b0e236dacc0da4207ada0c170e4c1d02221ef6cb584a72c0c618e3c7bbaa288940cffac3cd25fe00c8d8e67e23db3988c164c7c1f8dda574864620d10f5b18d01419233084bd59576e14dd77a6556ad2ceccef9630d87de7ec2d4fdd34162940771a90255a612a674f7e5cfc0f4df40424b68cd6f2fa0e59a08139fb873100f87ed44001234ee49a96bd586832af7ce9edd2198c2c7319dcddba23768
private theorem part77 : 2 ^ prefix77 % Spec.Ffdh.ffdhe4096Prime = residue77 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue77)
    (e := prefix76) (a := residue76) (b := 1902880489) (n := 32)
    part76 (by decide +kernel) (by decide +kernel)
  rw [show prefix76 * 2 ^ (32 : Nat) + 1902880489 = prefix77 from by decide +kernel] at result
  exact result

private def prefix78 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (32 : Nat))
private def residue78 : Nat := 0xcc2b5c254b37320a69d849b40a22e312352ec925af52f21fb74d38bafd6005a0c5bc52b8ce75c4ff03f69aae235cb71a343c08f6aa9357f0efeb1eb4bef0bc0d777729ae60d7ce3e8a8580d16f9c2762e21cdb4d99a4122268b15c0488da65bcc93763dfea9a89cd084f4013e7fdf7608ff11388b0bc99d2cfaea888056fa4cee044a861bbfe2cb8757b1cc6443b437f69e1120ebfcf0fe59003195edeeca31f09102f25a317d44548271573ec68752d9a835f6d90399a08af2aef055bc7a7e60b44cbe3803dfc2963688592731a5ec0366d80a62fe289df97dfbacf9c6ed46ffb6f1e08ea5d9562e3a402cc7ec5339f1b0c5a7fa465879a7dbf9c89eca820c8507a11e1dee8eacb40a6d5adbcea31fcc33b2b5a58e6df6c95b22f173fcf817969b9301bc80747646487ef9ea8350e9c5b324d1a7b372c83cb5d291bd31d1813db137ff13f24eed88b9708d13b522d2d8fe0e1176e083df01300d2f1eb95b0cda98f3f9950306f49c57720e236b4e3361448888b04c4448bc96564738a870532c88ed53f2c5adc25b8e9350867d76c51508ae2800b7aada1efeb066478354d63bf1b440073b75cf46e6a3b38c9b72837520bc1dcc6e975df41cf300f698e5c10efd7a4e21768482eb172952eab596b5bc376cdca782cbfba74829115fd1fc99da4ec7208bee396f03e1b60e59201ab1e713a03c79bdb14b403a21e1540ad145b
private theorem part78 : 2 ^ prefix78 % Spec.Ffdh.ffdhe4096Prime = residue78 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue78)
    (e := prefix77) (a := residue77) (b := 2994303247) (n := 32)
    part77 (by decide +kernel) (by decide +kernel)
  rw [show prefix77 * 2 ^ (32 : Nat) + 2994303247 = prefix78 from by decide +kernel] at result
  exact result

private def prefix79 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (0 : Nat))
private def residue79 : Nat := 0x67c96f2c44fdc0dcb084a863e53a48c25d8bf6f44810425e35aebc227768aedf6cf3e40fd4f71e43315431efc35b94aa5123aa9a043543d01994e1a33e8a10a7f9844d367c30324f02b8e2fbf53d6688de28105c0936f93e30e4999b773223a1fa6fdf21c686d987c4b5ec4d191e8d685682756a14be4f5cf63bfa60106171b6df6209db8133c582c2db5620a5fda737e9b961d66672e6ee19ea92f5508be960e2658abd1c746f7b2293ea2a859f4b2b9015281cf821ed227dde6985fab4975b2c9b8e24641533c0c74b08eab87eb7bee306fff5cfc60b5cfd26a50a231cf84a976c92bb478a735dbe9db5bdd681d22dd69503344f3677e4ca92fc7c3bb18c1af732827ac0b0ed56800c0fc801f1eb52cd0782d788f83e7374ecca5568a0fae8fe8c183ac3fbc67b6a062999c664df788eb9fac86e7b6f29f42522a32a8c8bb2cd8985011c2c5473fc0f7b31986dd86a58eb418209404b4b78331e334a6e36325dca1c6aac1285ea1e499fd7e6cf93d1e4826961b0836fed25b9260a956bcc97f355593e764ca856811239339ad7d24798d730f97020226111b4b659963a5f7ba346e96126fa3feb38f85c09392ac1814b399dcff865b32484317d7a5a72f882a847b0a5366870e95dabb6f84b882ba4bd32d8517a5097ce37bc070636541cd7c2ac3c074d5da8a94b95c23defa75c71276be90d9c18ba09d174a5768070efc5
private theorem part79 : 2 ^ prefix79 % Spec.Ffdh.ffdhe4096Prime = residue79 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue79)
    (e := prefix78) (a := residue78) (b := 955950591) (n := 32)
    part78 (by decide +kernel) (by decide +kernel)
  rw [show prefix78 * 2 ^ (32 : Nat) + 955950591 = prefix79 from by decide +kernel] at result
  exact result

private def prefix80 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (96 : Nat))
private def residue80 : Nat := 0xa96f36852e580f7efcf9679ada0db65deb9d69e50ae3520498304f9b69c0516eccad094b1dad953bb72a01d7812e66ae2bc7d0d4da2f08493af37bb3f54668980d5156aac703ad129c9b3cf98ee2ec91e3e2faf8e4987f6b6c064f5b3906256a4f9a8fcfd80b3f48f38e6470323983bdd9695d6b4b8664bf3ce9a30dd7cfb5d3215994c6d1e785337bdc3e6adcc871c0bb6b0894edfdec42ff9fb59c82c5b10bd6e40bee9d00b6b8e9799288413a22822582b71d3863f28ac7276a10046a70c374cd9425eb189c56076a641dc4181e25ee15970c2316bd9c947e2940910e14390c6a3cd88d14e211863957844f71ac46af3f4218d51c8b2832495d6eb5eea20176d84e6b8f0c5b88253cfd458675d8d3ba0e82f778e49a366d37a87fe112384eb57c352129417e98958378230555fc3dc28c8e20ac390953d66a82d416aa8dcd0aed4fbb4274592d5496da59bd00f52741e75cf13ae497b0501626336063b443eac96c944469c074a9672419cad522854fd6b8ed25ed41f6b2b81dcd77a8ab7def271c78406af89c7be11163606a8ec87b00d552db6db92c71fd551bf9040bba7ae07e37d13633bb4faf7d0c98fe7285a7c0a6a118375a2cc04b0e8883593a0c2e042066e5f272eb150147a8b027b61ce91dbde6f35e157c193913899b0ac7f6c4f9985b9a0f8173f5ea95252ad3893fb60bb2aac43f9f21cc5ff6c70505eeb8
private theorem part80 : 2 ^ prefix80 % Spec.Ffdh.ffdhe4096Prime = residue80 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue80)
    (e := prefix79) (a := residue79) (b := 2924953941) (n := 32)
    part79 (by decide +kernel) (by decide +kernel)
  rw [show prefix79 * 2 ^ (32 : Nat) + 2924953941 = prefix80 from by decide +kernel] at result
  exact result

private def prefix81 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (64 : Nat))
private def residue81 : Nat := 0x735a2a43b8cdeea9a64211f0aaf56c23329b6236c54ee7b182e3ea2df762514ead1b360314f083bab1784ffe4a9e8d3add6d34674b1a7c1b3bd82dbef88dc62adf534cedfa21e3d4f45805f7190790e99f4ac77e85f62f5e5d3ac879bcdcf6d257b7b41c1c43093c2d7eade350d0bf6f6d28ce3a9714969423fedb26f4e1a79972a4d2c1c33cd89e36d078ef6c5a5dae323736e3b932e37f254ea0edccac4af94ffdc0ed8a6bde30ce2f141d1811a82d0ef8b595c360dbc0d76337030bc7516f0534abf7f1d7b44f5dca45889b521ddfa933baff27270b8f8d000b55e92475daff9e584e5dea6035c986d0f7c53a82023b4bc1ff5a2ded866a1f2b216670cd7cb207d35b838fa3aaea2070ec767fa6bc17f9f5f6e4a60ce880f3aa06d5dc68e9f7741fa7fc82590914b51b681f7ab5cb38b09b44524980a0f6e928295c955e6d98faecc4bf089f23e066b74bf93dedb8ef1ba0470c7043e80db34d337f03640b3cb0a784e6ad22c4401eb6b9eb8d5a72c75069c91db277f8ac2925837278fd5e4e2a8d9280a473b56578d8ce2b5c827a9e89b75342f28dd102a1dc1f8e0758afd7977a9c36b056ee51ad397f4d58a0800be0efa4e7a2913be199c838739fefbde247b3b9c6573142e1b30202a610d35a2f0a1d04ab446cf9c9c2d51ccb15095540dec0243847541d3e77ba98ad659c6db97521f7052629c9bba90a541c7dca4e
private theorem part81 : 2 ^ prefix81 % Spec.Ffdh.ffdhe4096Prime = residue81 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue81)
    (e := prefix80) (a := residue80) (b := 3461282639) (n := 32)
    part80 (by decide +kernel) (by decide +kernel)
  rw [show prefix80 * 2 ^ (32 : Nat) + 3461282639 = prefix81 from by decide +kernel] at result
  exact result

private def prefix82 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (32 : Nat))
private def residue82 : Nat := 0x494e8b4dadac9d1bd682976f8b98cf0be51f0b6827a5e961ef8b7fb368298cd426d8db57d6f2a35d7cecbda3b09ac1c278574fca1a5f6e820af8a6c3082041ca3aae7fa8364a8abe3afe3df4a4c8d3855bd1e0ae98da8d5a148ad88ab3f9a3c31afa5ac2f045fe6922ac5665eda618294d836ad6fe142421eb1b05e4935703ba8e0f8ba80fc2589ba3dc0135a9e09f28f68db8381373ae060a0392894e13e1e8cc419975a7ad5aa4cfb82c64079852f37f01f7a792f4f60d6598f566807abadc9dde2ec069c09241e2c647e5a1302c2c3a34d870eda98976f74e723e0344cceee3e13ad15866d93b367a6d1ed04451b6444f7c6ccba7f485202f6756019973d1bd9556238777772273ed94a628268202ebca5c09f930cbce78be6d2c81dce87bed9fdc58830cb7074ac1bd4a34435f542ee648433cf6dc514395ea21d6e6acf257c95a6fe8942f9740d53ea19a6f2d398c6162f1c67e8629bfd5c935b131ad9a47dac52550bae5978c0ffe7292d07a513c45a50b96701d090546af2d760481ffe7952a9f697e1d1b0c0fbbdb2411e4704770e4194059abb6859237e9abc6d478709f591c1300eedd986e909bc7f8c90520f2a3a92ab31c529ff0535a33027384c45e859e564e5e92609dc7d2d3fbdd840bb28b86b80ad17246d04a7542256e05ba7448d96faf478e73b3cd747bec785b71688edee7f52a37fbd1be3a16d47881
private theorem part82 : 2 ^ prefix82 % Spec.Ffdh.ffdhe4096Prime = residue82 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue82)
    (e := prefix81) (a := residue81) (b := 1949734370) (n := 32)
    part81 (by decide +kernel) (by decide +kernel)
  rw [show prefix81 * 2 ^ (32 : Nat) + 1949734370 = prefix82 from by decide +kernel] at result
  exact result

private def prefix83 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (0 : Nat))
private def residue83 : Nat := 0x201b11e20677bda39a4b1ced99370818d4223cbccf3dcddaa5acdd4540c1a8c0d7aeab5d4969ce340a5699126559ef1340e2aec28feee5b94f4bc837f058b28b7ad84568b2fbe024a2b34769892db2dcf12962939d637e6fbee4c6a0cc2c33f9e0c2af2acc86603fb5c9a43ec0ab1679e3e28514b1033b44d730ed41fc5ce3abb0d5569ea5c86adade7704cee125df486ed32ff3da9423da3f9a630988ce6bd9784aab80398daf490ddd0fe60664e6da7c1be91c7d87b4e8cff27747d4e86f5efe5addcbee575bb76ae9095babfacc20a5fb996444791773f722233833e169d097f51a828af46fbfa4382fb536726ab054a782bd2ab07d96dfb0f92c9cb4aa693b3574da4acb74fe78370ab8de560e61278a0d7538f4332045074547611b4906e1874f341e84ac97cc9a85738bd5be47b498f3b067ba86e9fdff71c7014138ee28cdb87644ecb32b88519c8a0db8b6366fa10133acbbf2d5b6ee45328196edfe8d221a06d9136485801c7072eccbd2a381e1f10bb0d49f1637326f21569881a52d5e117c51177f482ba662f80d6083053a71ed07393ff38cab282834303951cd68897434d2073ad913f27beae28e21d119101f2146fe1970990be2bab7f800403a960701cd868fd6985ae8b36d970fb1e267364b50b46aab6d4f2fd78d968f8fb5af335e60c835366a869ee4f524e7f4e9a4f623ea875332cf77aa37cb88d721
private theorem part83 : 2 ^ prefix83 % Spec.Ffdh.ffdhe4096Prime = residue83 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue83)
    (e := prefix82) (a := residue82) (b := 2434473222) (n := 32)
    part82 (by decide +kernel) (by decide +kernel)
  rw [show prefix82 * 2 ^ (32 : Nat) + 2434473222 = prefix83 from by decide +kernel] at result
  exact result

private def prefix84 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (96 : Nat))
private def residue84 : Nat := 0x54564aff2d2392ac288dbf42f33778a5dd015811058298ba15373a3d81c80441a0986f193f054e10559e51dfd4a9c8d075987369b22febe09573779df88becac5816c2b29afa8683cea22a5615621df10b3d88069a5f2e167cd9b7a66df799c8652f3316e2b2964dffbe0194e1e4ef6882144a9f3ea34b15d3b68fbf14900b19c227455f911509aff0a82410806356b9b7484e5247803bd9f7b1e361084e668a27a4869574627b4aac94eee166c5389afe302b3c34ace1de0e03df07c0c654a2dacf636352cc8b936ee3c953a25f3b2b068bc979bd7ec3bf55d70c8631ac1343784dd904299e3484d4656d3faa3e888dfea3a57787a895cd90eb0c176ae2646adccd6e6bb1905552b2f4def71e24c4520516f24d4f724ec167049f5780a041ed64fa4d17bd89d9fe12cbc9d7c9da0dec030d480be42ab12b4f94e92476ff3f101186c131485b47dbbbc0f9f1c1dc9210266302d2fca259c1afe39e758cb4bd3be90d0ca5944e0cd08c0e365b202d63f51d0a4978331560d7b5a35327ba3a4593d10fc92ae48268f69a5e6b183028c6fd831b8cabb9a169c7fb3d39ba4be429e4f2159edb7b8c0b6c50174d289bd4191ff14ab315a022c016409a25dc61c01faeb42ced3e591e8c4e29b949297d1cb3e16d5d17a1bcd77ed598dabbd9c0d8cfd8741882b49e985ce4771ce3c261a7ebc3874780cd83ba279008be4b8f1f6af0c4
private theorem part84 : 2 ^ prefix84 % Spec.Ffdh.ffdhe4096Prime = residue84 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue84)
    (e := prefix83) (a := residue83) (b := 3588395211) (n := 32)
    part83 (by decide +kernel) (by decide +kernel)
  rw [show prefix83 * 2 ^ (32 : Nat) + 3588395211 = prefix84 from by decide +kernel] at result
  exact result

private def prefix85 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (64 : Nat))
private def residue85 : Nat := 0x236662692fdaf237c4c87e1335ee3df3f8a7c0f3b4830997c0b8c5fb003169d9ad409ace4aed7f9ae6453343ac416c1b1121a69b9dac2995716253da9e6c3386ee611f9f1d70ffb96124177c70e52efdb7ed046cc0fd3f74f4b739b3e87631d556788a405aa695b5922f3540c565fbff0148ff0a9eed81f330379ab65187ac6be770bf21e4075e53641f5949bdfc92a67d38fc17919fe1493e13bc8c200b9b7374efbd6e13513910d964d4a0d0d3200d481a77e2bbe7e2a198844f82efc218153a65fd5db80c5dcdca9bda0ad9cb4798e6c15ec70b13304c82e230dd1665d1c52ad98b321f7f11c6d08b9f33d4e18481415573af8523a16ffdcec8cd928391a87353b88e4d73740ae2a644ec2af94fe73bfeeb7f052a1db786cdb94aab981e9dc050be0b79a2ac1365c6866627ead24830c14c01ea07b669402485ae0bd81d7c42e81e1f4f9e002238e78ea9cb1f9c67701b64eea9face1ac2b06a1c5ba42948f94755e8d0d35b737959fa8e3a2acc4fc2fe3515275e990d9eee01ca31a612d9783ae965d777eb193a0d30f7b4663343bf7fb0721067a14055d1514321b87f14d5b97751155cc35c3ad0cc0de056926a9f6d5cc5e450601fbd709d49fce2e575e5f87ae0f59e9789dd0405dc878ad6d94aaf788d670f2d12636248ff2fca966630f4cdb386f652db1767c28421bb08fa13ec92136f1b81be7ac0f6d066e56878
private theorem part85 : 2 ^ prefix85 % Spec.Ffdh.ffdhe4096Prime = residue85 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue85)
    (e := prefix84) (a := residue84) (b := 3448173933) (n := 32)
    part84 (by decide +kernel) (by decide +kernel)
  rw [show prefix84 * 2 ^ (32 : Nat) + 3448173933 = prefix85 from by decide +kernel] at result
  exact result

private def prefix86 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (32 : Nat))
private def residue86 : Nat := 0x91af5c19b4470e7820fe5db4388c59e9453a2484c2a050d2a9a2fec60d56e545909f37c64624da7ef7c6a66480df0169a6966cc3d88cdf97136be3d01cc845331ee571b3ab579c5f4dd6dfeb7cfaa8c190eb6371bb4574c1067847602c22efe603c80b4a87d9a264db5afe162ecebc6133acf710fcbbf30377cf04b569b047cac969c59a3d66e18f5aa7cb2ce25fdf7150de1e09b6b14b26bcffc6a9c5fdb7c8cbd80766f12d1a3c3c159f2a98bf449763edc2e47d9593cac99e226ba36adf336bec2653d98c3a478592c6c2e3405a7bf911eb853d64ce1ea08b6b785805ad7d64f2dbe19461eb3f88e3f65de6161894f1b11e0ad4216e1b3f9c9b056e743be8393981f9e7378964a7e1f762c1ad76979579c27b75945e6972bbc48d503304a2c1647d48116579e98ca75df97dfe15bc04d6999dc724e5edbd12e0485602741b3ab8f389d825cecbf7cab45a1539f69ca6a44952cfcbfaa0806db8fd56da4b3831475690a02624a578564267be1a8c4f2ad675e10c1f01b3a602637310397820d67a795e61e43111bc2a8fcd4bdd41586331c45f6b04715aeacf06926123df289691bbba99d46cd505b6a75f13cf46442e9624d7e7e61be28b0b1bf6053c9bcef1859cf12f2687b48ff5f1ee56b50ead4b9f26aff10f9cd8c037085f0d5ffd6a08058592b0f03600d22af788d17da960f191bf930bb1aa518389c321ae5ef2e2
private theorem part86 : 2 ^ prefix86 % Spec.Ffdh.ffdhe4096Prime = residue86 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue86)
    (e := prefix85) (a := residue85) (b := 249548065) (n := 32)
    part85 (by decide +kernel) (by decide +kernel)
  rw [show prefix85 * 2 ^ (32 : Nat) + 249548065 = prefix86 from by decide +kernel] at result
  exact result

private def prefix87 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (0 : Nat))
private def residue87 : Nat := 0x355eb647968f8c7ce37cc45457258cda946961a9aff88e3e6cbed6b7d9722e18d9d3f5ace4d876e79ec40209273879c62dda97d657a49b5d3d9ecf2ed822de3e66d64563d8b36ae0e3a68279c7630cff9cb19a1d249f31309c3b97eab44796120adf06ce99a92c305d2359e143cc9e8b260b9949777d40a8996902d796922640bd49831ce479cd79d9adae4bd0ce7f9a647afcb819abc0cbd9f7d09ec059c6deba3351593687f1a7efe77ca49d08318e578df0cc2816bdb76fdeef17fe8eb2aa5beb0de68f2565f2f3f37513502cac099562e7e0c46473d98d8478aafd7685c392a55a95e2ee6629f78774e8cf4b0c2007960a480e480507e994b94c055d013c5578907e0c5a81549d584b280c49a094262e29f6adbe99c2f2c245066a967db4a67a5d6196cf6ae514ef5fa284f5a12786c3a69e968bdeee7c462d992d549362d48006364bfa7f8cced7e058e66ca4e6b05d78a6c823b3b057d4201b1d74a89d32b3bacd9f88dc48338a00f8569e09fe7108728299f82593c414220cc5d600370d3562046124f63fa9298332030321f92043fcb04f30384779766d218ebb16021c2ec1b447b4faf80bf92a8c0d91b9fa85c3781786b592110eedd4de954e332f4811ce2413951cf1d246e11df0c3eb52b916fecb111f024a0bb301bf33e2a8b1cef594099d74c4538cfbb183624059254b76521da20620e8be52cc778f9bc18d
private theorem part87 : 2 ^ prefix87 % Spec.Ffdh.ffdhe4096Prime = residue87 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue87)
    (e := prefix86) (a := residue86) (b := 1793205287) (n := 32)
    part86 (by decide +kernel) (by decide +kernel)
  rw [show prefix86 * 2 ^ (32 : Nat) + 1793205287 = prefix87 from by decide +kernel] at result
  exact result

private def prefix88 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (96 : Nat))
private def residue88 : Nat := 0x55d5a9df132afcb3d6e839ef1daa6ab6fa60d5e8e3b88b658c7ceca11baec300870bd81e2a4028446ebc2c35042be3e551564046aee80772ebe37058fd5eb841f81e88e0d5933044083a06751a31e745d17b1f4402d8bca440ad308a48fc15d233d180587bc9340965560b52c424632786d747ce3e4659c1106ba2441a2517cd1e074f22fdf88d014a92e845d2c337e9fce304aa4fc0dfb6d6f4f0653a0d619ad505d10aaefc6f387b003fcf230d28f6e08a2f82f81dd4749605dfd825a4c724a55c44b5ad80ac7102eb7c13bbf98805bc9b16ba6d9c05716a229c49a5a64790eb69b22848ff71ff289c1da5a7557267c11aa37ea7f3f1f89651cf0c71a5b8a9eb37992477947fc47725c033ba2e7a8335e28974bc6c4ef4b8870a07053ed84e02f83c7ff5c359305e3036c85703d8c8d410f983f4097adcf128180c96b97f6336972bc2cca6b98214a182c94256175f5a37745edf372d9ef7822640bb1717675b7e05a40d5d0586e8718dffc58fe2305c86253a5941974afeb62ec57ab521e163cda1ef55b1839be0b0532b9b5281538d98e919fdb885d835ff7ce48dbe6727192c0a4ec5970ffeb7a19c580886fe126be551c96ace6ca10951487064e85f76fc8d8854fd69a28e54407030dbf9d8da33db77aff696df12abecf93ccb982170a172cddf9d3b91a5546b059088b50d1a49606bf8e57352af2234424e1da84654
private theorem part88 : 2 ^ prefix88 % Spec.Ffdh.ffdhe4096Prime = residue88 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue88)
    (e := prefix87) (a := residue87) (b := 90073141) (n := 32)
    part87 (by decide +kernel) (by decide +kernel)
  rw [show prefix87 * 2 ^ (32 : Nat) + 90073141 = prefix88 from by decide +kernel] at result
  exact result

private def prefix89 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (64 : Nat))
private def residue89 : Nat := 0x8d569121663d8d6b7652891d6d95acadfe5863dbb3d8a8bc03965e1a24ff339f62891903b2cd8b5e189168ae32197f1546d06314eebd9cfd1bdb30387e59852280cabc28aab89f9ffbbd28c950c2ad7922584773da65a377033c67975fb2176d0c757a29a89741fdd331abe9eb5c520700977bac6f9d7dca4cbf69ac1dd9cec728d5058cfe6299a3a8b1a0468df4a5f3d0c17fd6537af468e0a48dd845e9ea7a28c048438fd57558b7c99eb47420d890654e186bfac08dffe58ad2324747167762fc5aa8e4faa5b4ca2b3d16d6215a37f133e2616a572750495b77f902fe248cd1ff2bfbb5a9371332ab149912251e03b2c6ccf79eb114501f080bb46234a295b3abcc95a59f2063c8362283d129f831097830f0deae6bff73316e464fbba14dcd12a28dee7d3b2cc87982942095971685fda882f0a47926cb9ea6205569911edc68d3c5a8f85ceb97f1aae419a23cc95a6b4a946758633e671988137c181a1b5dc90eb178f39a848766b797c5a9e3d9571e90a2156bdec4404c2613a2fb40fb59c3fb748aeaf8ba1e3ec023be39d4cef399e3e04fb4d04838fe061cd47b22f9bb49023562df7b674959fba002a494851c6459a0f3ba834c0794dc8124650977f03a7c0326c1b879e721a1cbe4f3a2c11ecd159adf726d52e7487ec5f79e74736e932d641477c0ac8b2ba4988756d488c089ce4b6ca46320f455246f7259fc9a
private theorem part89 : 2 ^ prefix89 % Spec.Ffdh.ffdhe4096Prime = residue89 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue89)
    (e := prefix88) (a := residue88) (b := 4247383799) (n := 32)
    part88 (by decide +kernel) (by decide +kernel)
  rw [show prefix88 * 2 ^ (32 : Nat) + 4247383799 = prefix89 from by decide +kernel] at result
  exact result

private def prefix90 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (32 : Nat))
private def residue90 : Nat := 0x1db97bcb15945c2940c1af2c514e1342da78cf9207d1963cb66f7040baaa248d6c9c0a183c4f0e1e6732cf8dcbb6ee0f25633f948beece51459f71cbf53583039a0a2adf930c3c61563be76ec270e4d68d0cf2b6154bc6ab68b7d0ce48ed4c3ce0b20b3fe005b99976836158c9fb94d18986e1d683973ced9f4298af8cb7f625433e48623e8e90ba987195163c5472467a40e112d40ac833cdfe97b69d47f6d0f8a31cd8282c56fe102728731e34d32a8c4265e89f687018773521625dd067b7ec9593dd11ae3c86303726e03cb8bd5cfd6c3186430fbf922f146cac22994b456c3265227aefc888e556512a88b2448ec76abe78a834928d99710f3a984c66bcee56aec07699ccf4a436bb0fa2f08a007c02d2fd057cd968c1bc3f740dbc4afaa90b868da996a89a75a5d840d63a01bfee5479631aaf2e963c51b898fb5853c771474d65ed33bedacee88272dcafd47819c188d081d158766603074ce43fbc03669b49d6e730a01a56b3a63b2d8a6c3c8c3b2424d934c7fd47617245d327bdcca049bbc939d161f2c2e65708a7e79a5a90adb62e057a597afb182da5552c9de6305e6c6c805cfb3d5c10b7c33b168e3ab277dcab2ce31e5c88d3063f6f308aa6de7e4dffcf7e9caae9dc8cbabd648ca37a4bdc091fc1b3519bed3a1b10323307508c50f8676c5433cedbd406fa8f1deff7b6df998f63a1e4117ecfed6d3157c6
private theorem part90 : 2 ^ prefix90 % Spec.Ffdh.ffdhe4096Prime = residue90 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue90)
    (e := prefix89) (a := residue89) (b := 2651689079) (n := 32)
    part89 (by decide +kernel) (by decide +kernel)
  rw [show prefix89 * 2 ^ (32 : Nat) + 2651689079 = prefix90 from by decide +kernel] at result
  exact result

private def prefix91 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (0 : Nat))
private def residue91 : Nat := 0x83f108e7f7de59ab798b2505e5c647dfb227144c6e39caf97b55fb821653ed12d650a7c58cc4aa0251a70d3ba0542967907ef15cdf53a0ec507d212d3b2921a21c4ec983c244237da4359d1c0f4ca427009978e0afdf0dc26d0b19a8c6587d61217efc1405aac0a8c3cbc4025ab1937e2883e767f17294c4a7963320b86b70060ddaeb51df305125f401c22e695da8eb80bb3aef760fae6122c372906bdf1555164566ba5b8478d352876111f792f58d162250d85a2e66199e0b5e74089e090604c5f756bd619005111b545a0d9ce1bf021af1b1bfc6d2d8be056e8c763a12fccff244d7e12994c7b501b795d99703918072bb0df895be12a82af9d8b25cf050d856c3c7075edc79fd4ee67728b5eb15588b115e09fe37636de0fb89bd4ce3f11351d27f4134319990ee5efaa9665bcf2ed79985e479169afaec7d7ceab98eee172c218337809716fccebf543fe12b3e354207871d50ddc1210be6456bdab18843b4209b1c9232c8c42cc9ca4009187d1e42dc46d2c771bc90b28f9992ef3d8d72abf7a225dcaa7caad7ce2c87f5e7f44230927b265f2ac2b299fae3eebc1eafd92a081e0b30fa60a6555d09cbae3bcefc15d98cbff2ca134937fbbc15d9f580736a666512c1c3ca0cb8278f28ed0747eb80f3590d7f33777dbee1a8ecb2e0dc754b0c3ebff8034cdd4444e75767f468f6b4faa47d9ae8ae22f3dc077816b7df
private theorem part91 : 2 ^ prefix91 % Spec.Ffdh.ffdhe4096Prime = residue91 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue91)
    (e := prefix90) (a := residue90) (b := 535482046) (n := 32)
    part90 (by decide +kernel) (by decide +kernel)
  rw [show prefix90 * 2 ^ (32 : Nat) + 535482046 = prefix91 from by decide +kernel] at result
  exact result

private def prefix92 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (96 : Nat))
private def residue92 : Nat := 0x2e90dacaeca988585ed79242955d5e351b7215ab4535639fc8f6273e92c7cce5149eac8aea14933224af157718376a573e1447ca2ffa332ae6ac9c4ed117916c876a333d65dae9dcc2b1e7e376e3256468e1f88c8b8cd0d138f7a0c0554f7fdd298b3ed5e3c9d36d15f642f9e14f79d2e8c6a19326abe644ccb4ef4fcdb49d0a76a4a9630c78e323ab2ce8628a625857749bb252c74ecd8b654665f7c1a4c55b9eb1a112c1b7195d74aac9ad184b01dc82f13f99e701b509bbad8d60106ac5c57523f6844072d20b002b7159b1ba955856f3cdf98160411ee73a46312495f9904314f4c90858fca776a06bcc5bf42a9bae40595383d84a25283511a01a6889ddb0ad411a23b1f874b74cec7369933de9dce8367aa6b118e6fd5160e6d02ab2f0fcfd1850254a375fa9f92be3169ba9ec487a25391a2c8beead9712a8131396945c1b379d3aec5a4a00f9d9c18725730cd23828df61a80f3fa6b5389f19d10b06209fe9a23c081252ee37a2da51677de0c18010fae3b1e7cf006bbcfd162b447bc648857b863517eb06c2ee4fdb49e31a1c7e19fb347c320acf63ce01b99be3fb083db83b77e08129633782d2cc2dc0ef221ecf5f979bf6ed498219c10318c9d46bf690e3ba26a0313bc596c4ec345b1d767dcf0bf9c9f37fa9effd539641018e16b5c4de9e50feff479231f7b01c836c40e3d4ef225ee944178ac646c39b09c4
private theorem part92 : 2 ^ prefix92 % Spec.Ffdh.ffdhe4096Prime = residue92 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue92)
    (e := prefix91) (a := residue91) (b := 317853333) (n := 32)
    part91 (by decide +kernel) (by decide +kernel)
  rw [show prefix91 * 2 ^ (32 : Nat) + 317853333 = prefix92 from by decide +kernel] at result
  exact result

private def prefix93 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (64 : Nat))
private def residue93 : Nat := 0xd18df269f2fd6bf8525eebf220a90e85854707625e109ee74377ab960a3d64b59ff98db9809011eea4df44217d8ad817c308d99f62e771316a28830750e49087f9c45a137243f81505515d33b295d12710a61b85ea5acf96dbfa98bdbe2730ac811f2148f32553d5774dfd0f67cad69fd55567d98f9f51eb42d4580a4ee1008cf54fbf8bb25df20cc4c88a52f05cc31423df539f704e5a6d8cccc99d8e2bfd2f2d13c02bc7ae554cf6c40a9509edc77d23bf7eba9d0ea265f4ade0d8ebbbafc3d8a1d6d5ccc10902fc315c0784fd836b04517c7dc24567ea8dd87b8660b5b8c4d601009b58de8844c1eed92afa66bc4961a51127aeb74bfb09ad42a3f8129d6ae18716671eb00edf0deaf188883c9363304f5c605946e69ca8b2d1af5a99641a89d9530ede0bbf62d274d8a65771782efa51b00a408f2256e78cd60ae7bbf8b58385022736e271495175a0d330fe5e8e1582a3f7cee21df107466e95d09d518e3a4f61fe52ae1a51d76aebdebdf2f7a4430a81868f7ff5f71046557c1265334d30112a85a6e0a756dd73714c99f53d653c83fba729695a45c40a0d0e3d5d4ae5b62fcb6590b8609f830821d4b4cbb55e415a410afb2101e86c4b5c0154de247e85f943511331a5b6c0a00fab13d7ccf20821485d9251f7e41edffa41327e914d63697cc2c47e4f6f2bdcf9abef6fb466c17cf336272367a037151ec51d707050
private theorem part93 : 2 ^ prefix93 % Spec.Ffdh.ffdhe4096Prime = residue93 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue93)
    (e := prefix92) (a := residue92) (b := 3008302968) (n := 32)
    part92 (by decide +kernel) (by decide +kernel)
  rw [show prefix92 * 2 ^ (32 : Nat) + 3008302968 = prefix93 from by decide +kernel] at result
  exact result

private def prefix94 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (32 : Nat))
private def residue94 : Nat := 0xe99febc19c133599f5a13f0235b94bebf5d738936b83ab63e4c814368215706e167d5282d48d53b2be36356f0b621bb86b4e73490ce9d2a96f5a16648be87c53cd2adfff88fbe5e1691f2d58da59f62579bc3e298b6b74550a71d6d4c4775ca68085791ff7bfe2db22f6ff3e1f5d7ad0641cf044555c76bde4c4e59321418fea822c22a7e51772e4747cd1e289c720bc1d4dd2595cb9fcb3c44ee0a51ec69bc3ee76a4fc9b9c27055ce66aa6c1e1d39ca63ae85f72b77bfcc512f39f7599847cfdbeccaa622af0013a4e101849d196ac075f650eadff8dda8fac91dd1de0284575a9b105f16fc84862f7527c8e32703c7c508497084cd748c0a30d02c79a7d187ce7a0496707f7ad4450ab82fa48e390d03b2301d4fbe40d03f005713f113f5d8ced5d892fac1a98308704d7deb514a8fcf73d87e37f6ecf3e098a523c3a9a086cb395d5ec5064048c512ede9c1c52702bd52d7c80ca795f2dda83e0c45df339926b2cee7bfbb05f7fd66acf53f0436d66bb87ba0a6501cbdecfeb5c74ef0d5b15d5b4a71e1ebb5ce814e73460ded6e5c3734c391d05774cb98c16ddd24dca2822f742c0e1e47ae139f3a637eb55205dbe9d5cbcd32ffd0f9f3e656309ecb5a610c2132141db3c4484bf8995015781b908c6f7603dcbcfae0d6ef3734af40c6ff8232cce6aa98015c3fcd48341b24b538c27669b5177f74f77112a0e3cc8ca8
private theorem part94 : 2 ^ prefix94 % Spec.Ffdh.ffdhe4096Prime = residue94 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue94)
    (e := prefix93) (a := residue93) (b := 3073878369) (n := 32)
    part93 (by decide +kernel) (by decide +kernel)
  rw [show prefix93 * 2 ^ (32 : Nat) + 3073878369 = prefix94 from by decide +kernel] at result
  exact result

private def prefix95 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (0 : Nat))
private def residue95 : Nat := 0x968a3f5331b32eb83725082dd2e3bc436082676a835d63de6fef2024b9a2ec9ed69aa434daf344fcb1e5023b437b839aa3e6d13f554ed01411aa0e8acea614c53be1ab61c2d6845a8f53c0f6fce90190d3aeddcc2c33cc3b76d4e96c9e177cbc49d506880053896c3656290f3497beaf7ae27be9e76fef211d9d4c65b250d955b43788a3e8217d4119266b399336a3018ce4981a3bb4d2155b0f2a88f8acb7e49e99ae14948a9a1a1515345d37bd3ef0196b98beaa1a2e6931aba3e74d4779f1604ceaceca78dd7056c57da687bff447164ff8411dc79e5a01422979af847187f3582d74c93d8ee6e022f38cdd1d031434ddeaa9fd189642d8a42c34d852c046a2bfe97466dc9241daa0d7cc0452a2def172b4b8f871224a28ebea82815499c47e8b20b3439e8aeed2cf86cbf27f562fc0eac69231f092dabe06ae5e0b4488b23ab64eac37babb9476c342d205af951d9f754d43b43d486eb88ac5489f8e239ae42c54c8cf390f4e02809358e6f1677724632ef0496044d83dd907739524bf94f5d5a88c92931bcf8aa0530a482080d467cd31c0263781e96fd38d43c363956b0faad3fa2d844013a0faad072839aaef76d20fa07c662185e13c472d3277d1fae665ab47353be6c43884ff88f8e13a0a06b7dd47e5179bd23a52313980149eaabc379260296abde20068bda7e4d6dc214601eda204052bc5d42e83529b584063
private theorem part95 : 2 ^ prefix95 % Spec.Ffdh.ffdhe4096Prime = residue95 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue95)
    (e := prefix94) (a := residue94) (b := 2334587517) (n := 32)
    part94 (by decide +kernel) (by decide +kernel)
  rw [show prefix94 * 2 ^ (32 : Nat) + 2334587517 = prefix95 from by decide +kernel] at result
  exact result

private def prefix96 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (96 : Nat))
private def residue96 : Nat := 0xda553be44f671d9260803dcb4feda38125644dccce13a169257d890226f1544d59d71abbddbdf933517424bbc708d2c3cbda4ad83bfa49ee5a7dc19be3678c397bdc89ac976626e0b8a01a03bb7018a129b8842b2c573fe82af917dffb461b31462d6b421c309d94fabf52c0a03c54fa96a36386dab7b9598c01e1634a04977f710cd8ff95725bb3c635c85d79e6a5cb7219611fdd9782db3f96a83b3670574379a0284648ed29baaf3b1154abe9e35ae1d9a558156d8e5b14932a12c9908a2f1fdadfb69f9bd0f13af2829f0369f0335c750a3c0e9c1aa752a3d1671f602050c7bb16e1b9748260f25156b9bae3b8cbaea4324362b2152cd51cedb17cdf133c332cddf2bb82b5fb20512b0db82d19a0cacca6321631d2e3764992b244a98dbb49c6ab572d2f01aedf52a574aa049b2dd682c389e7f1cd3714c7bb8be7a155611b2e1a2058fabf13c32af8eb7392aaffc2678d32819aa8175f792e80b766ae9af5a9536a79dfa24eba10c0bc97320b0bfca9366323f75c53a8b70bf671a5d16bdc9a8892c26a7ad8751c2067915a93c6705043bc722769bac5e39aca7c0d829c522af64b79b0cc112c1fe577e4ae9c71b4b960c3e90e6068abeee36a6605539e84418ae082ba7de5b5cc72c09453a2e1030ed62f93e0e4092e12c66c511d7fc3a3109af060935424c7d69b76a97e9ac0ed341ac2e3a631c869c8e589fe14e5f8
private theorem part96 : 2 ^ prefix96 % Spec.Ffdh.ffdhe4096Prime = residue96 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue96)
    (e := prefix95) (a := residue95) (b := 3164108018) (n := 32)
    part95 (by decide +kernel) (by decide +kernel)
  rw [show prefix95 * 2 ^ (32 : Nat) + 3164108018 = prefix96 from by decide +kernel] at result
  exact result

private def prefix97 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (64 : Nat))
private def residue97 : Nat := 0x9084df26e5d4ad93c39da0add307c83f2fbeea911a680fde38dee6c471ef7e09ab51c13757d3f20f8dc9152b16131680da070bf94c641acb150e99e51df355938b770e9515c31a2d02a9f506735d2b43540d10bca41cdb8a5c645d247e7aae57e7badaadfd75de1a896d6cf9be189ee6045db036da0cd9c5801ed44cfcedb049f0772f09ec0a8c05c4e14ba4a1db11ab4dae0ac1f2425e80fb7df8387db36a39913e851fb682f069415d810e1c0dfa4bdc8e1b5b49e1e6e859d85bd36c687a31bfca7c19a9a0bd77bd7b8237311e3be90389af1940bc8e04a3383a901503dc7cd3f6c6ac94a619cf647d90f2ff52e81bd585ca87967ee0042c3aa403b5615168b1bf320262d6e2aeaa6f4b5a09b81dd8ef1a87c845cc28d96f79f8d197a7dce9303f9d89d875c1fe55fda860c939395d3d42f1c4ea130f474dd4e69531cf9b983e4bf89e36c0fa73712974509b37ce6d724f3cada09671d9828abbfef7772d97918490f31bac53dddb6aa8ddca3488c4b5654d3ab59f099b58d6d88c6f141bc395d1ab52c478c0615bc61b4b5c2d60808c9aa1b530b79ff9f6c34531a4c29d39ba0ed09bf9b10a78ea131807483d21ea1c22859b1ee5914d64d890b31fc84eb97c750a834a7c0a9f325c6aee79c0f017b9a95e6795ee5238a41b9e5eb8ce010326207bbfa5ac0edad7a1e2aed93a6a34c7de3272a2d504d8d2fbeb18928d8271
private theorem part97 : 2 ^ prefix97 % Spec.Ffdh.ffdhe4096Prime = residue97 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue97)
    (e := prefix96) (a := residue96) (b := 1925458907) (n := 32)
    part96 (by decide +kernel) (by decide +kernel)
  rw [show prefix96 * 2 ^ (32 : Nat) + 1925458907 = prefix97 from by decide +kernel] at result
  exact result

private def prefix98 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (32 : Nat))
private def residue98 : Nat := 0xf8fa805ab9e2b0fd0b925712d80e283023596189151007f35280cbabb0f46af2cf5f8291badfb8fdf40fc74b804757b663f0bac3bdba325e9190b5454d36b770f2f817fef0f6ec341842d2d259f4a412dcd0dfd34da1d7695a311aa6407f3f84ec868b6208d99d30a5a38f96bf428da93e7e22176829a28077d792de1a20802cd69f80d53908c3ef90b4e48ccb5a5abcea34a730aea06df17c2ce960e879f1daf647361a938fbf9350ad8331ec92d82e9705ea055664049346ee8bd0e7b460de83550735e7e2efc9588fad66df0a23f5da7e58d2551eb8956d7999b7ade62504302186ec71850ee4b8742ad0bba36c37ee3f8bc284b10a7c75b457842436f08b79ceed687b76c653476b528ce783235e2b98020ac5d7a93b705afc05368af7acde50d3dc2cd67e45e7f68db65b6e9e69dbf6ede83433201e8150d37a9e75c02a62429809b4987a40747f0401a06db0b62abcacaa6a8f93b2ccf24a56e59b34d66f0e6a39d74b6ed66f2716c0b2e66cf47f55486025c7e2af7aec4ada4ccca0d2757216d4ecc0187b983019608fc515f8256f5115654c88162d53dec0b3b516d0cc586ead2d98f364a5fce00ed5f913af971877cd64c7cf6846059cc1488bed4dab0c86a63b8d488649601238a993eb2eba4dc799fbc7d5314ab19efc5c5d3736b5abc02b9918e526e40ea8285c18c39c50b5c2cf934223a337cb2e1068bd068e
private theorem part98 : 2 ^ prefix98 % Spec.Ffdh.ffdhe4096Prime = residue98 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue98)
    (e := prefix97) (a := residue97) (b := 1446948769) (n := 32)
    part97 (by decide +kernel) (by decide +kernel)
  rw [show prefix97 * 2 ^ (32 : Nat) + 1446948769 = prefix98 from by decide +kernel] at result
  exact result

private def prefix99 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (0 : Nat))
private def residue99 : Nat := 0xcbb842a55098a3f54782b259ec97606ab9f7519443313e3de917284ff05d675121b40593df5933ac38600a4b067d568b0c8dc0fe91fe1702b9f07cd6b2bbb697443f76eaecbc0973a8ba8a4a307a8977381a49930f009ac716bbd1bc3dcbb4658fece63aa87b7a2c9bd34c69ab16427ae82aa47b39070b36ccef843db4cd66dddf4740361aa2d7554690ed7934b671cd5b2e020d24184636b278cbec7a5e03acb0d6d7968ec1f512cf35938eca2d06a541d9c1df56d6c20d5c9ae01890e4fa08bcff485131eba8c1e4f90d78ea92a6f3e2a9f0eba7665b7e4812834c157d41bf951f500bd61a1f71b3d23e351791296d01f10bbd639d6d36b5f25a6d4d71268d9fbbc47196ad3ec619585cf4e17c3b39933ed4d4f2ea8cb14bcf935da02c2d39a872e6868b767cf8b6df1933e1d0dd173712bc61f666a962a882bb20e23c3ee9631e52852b7dc1e6f2ca512fd1ebd4ebacf858fa1fcbf2a33a85629b985c9ae89b2546504a69ad08696cca675919f2e5e7bab13a8b406f9cf96616122b10829f5562b995408a9e4fe700996f8d144df41fa227c0d358fd26fe4d95ec2cb05aed83f73c22bcb8d0aa8b1d382c2f468b89246b53b420186cec4c678387b21b5386f90db77a0b2f27c78d4e49a551e1c1f2d1e44f5deb0ac02aecdde26eddae36944cecdead3307c7ada4f2ee71dce3ffa5bfb7e7c84b9300447dab9ac600fe3c40
private theorem part99 : 2 ^ prefix99 % Spec.Ffdh.ffdhe4096Prime = residue99 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue99)
    (e := prefix98) (a := residue98) (b := 1800386188) (n := 32)
    part98 (by decide +kernel) (by decide +kernel)
  rw [show prefix98 * 2 ^ (32 : Nat) + 1800386188 = prefix99 from by decide +kernel] at result
  exact result

private def prefix100 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (96 : Nat))
private def residue100 : Nat := 0x34dc8e969e6500219a95b3dee76856db334405631422f59fff84561d4009fb1f962f3cdd202d46b7051c44d5f246fd342ee975e42ca428d52847678215fc4effada23a90b7daab4faca32e0e8fa0f76b40f326086f360951fbbdf1710aef10ff7b55d5d8023596edc3febaf19df043914090008857f0f24db73c0dd5e7da6bc9e0c6fcb45b7ceae5b38e3ca6503c9017dae1ef1d55897d2e8aaa62de291d725b40ec44a8c29b7a574b8bf166e49d2566982f9938f8f5a2e93da26fb17c342df60263339d3486d90354bd13a28f0892fe98d3681db8180202bdcac6c0e1e7a7c9431035f0607574323dacb637da35cb2dbb794150107bc71fb86d81a144456ef5fa28bb1ac0eef0a4cea3cc508cad37f744291b3fcfc8cd8be21e07229f63da1011ac1d0844a9b77c345d5c7094f3d1ede9fd30bd98418d99bb7afddd22468a091f9079f16a780373393a3eb34c346b27f073cd7144204aaa547bd64bebd4be60a85496c3856c35506b20fddb975d2bf0f9f6c2a31841cf4fdbf0ee2b3516cbbb2bd7a2d42ddb64d52e18a81d6da78cad21935b78be8f12a139648d5b0a4eb016c68f8b8ad06975909e8fd3578bc638b4f001fde45dc8912a1fc331848bdacf9c2bb3118348c02991f2db71a2b8091bbd269cce30face87ab6c66f3d7333df156f3ed2345eeba37993976b222538f49a1650c035680a69c1a1fc1c6c4b5fac62d
private theorem part100 : 2 ^ prefix100 % Spec.Ffdh.ffdhe4096Prime = residue100 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue100)
    (e := prefix99) (a := residue99) (b := 1001514894) (n := 32)
    part99 (by decide +kernel) (by decide +kernel)
  rw [show prefix99 * 2 ^ (32 : Nat) + 1001514894 = prefix100 from by decide +kernel] at result
  exact result

private def prefix101 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (64 : Nat))
private def residue101 : Nat := 0xeac8bb9c2d96afead7a20a2eb1e3b4b33b186aa9785a6637c6cba27cedad517a39d0aa54db11260b9655c530659ff0508feee4c75d8063c1a2df6930247d54ef0ac3dff8b512bdff9eeadee359a9d4f8b997642741342a3fc7c8fc274867886c6a2e4d119a4f01bec90afdea34790b536da887d684c2e42089deb9d8ea5de88eccf74d69cb165f93c3d083ddfee29af5d3921653f39ea18acf399fc6085b7f1809848d553657a15e0ea3401865fdfac57d72a5988da2177b017f3543f52a285823a57d2bfed1d30eaf6d0f972b24060af008e837482b1aee23d1df69cefd7d6d0851ef73fd421c5727e40c15fab1d9da88ede332179b11f6cb19370438dc6889289a0caba74d1780a33b060f0e102a2ba36ca6b242fd401125ecd188b9a4a14d6ef2c18dbf416647256c6e39b1420cd0a71f9069be7de3d218c97a6c3081d2b6fb2dacbb6b2c21e8ff7984e38b8cd85af5a0e723b56866ccf180b1bec094ee32048835ebc10c8a5aca46c30afd26dca390ecb242266779e500bea89d1fbcca32f51e0383222afba2f2f3c44b96eb22c3c7ef4ac7245a8c86cfe4527fe955d1cd7a757b22d18b58706c2346789f2028f5958f4e5ddb89ade8a6dd90f84e4d51b0fb53fa35daf91ff81bc5be41b09e7e6eab5da236893d407abf62730373638a2eb34df4017c5a2f8c0ad303f7dfa9fe5bb5f9f2fd2179fc4cce60df229b3b1fa4
private theorem part101 : 2 ^ prefix101 % Spec.Ffdh.ffdhe4096Prime = residue101 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue101)
    (e := prefix100) (a := residue100) (b := 2860621826) (n := 32)
    part100 (by decide +kernel) (by decide +kernel)
  rw [show prefix100 * 2 ^ (32 : Nat) + 2860621826 = prefix101 from by decide +kernel] at result
  exact result

private def prefix102 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (32 : Nat))
private def residue102 : Nat := 0xe34f02d013c8fa912e04e9d894143694ef940ddc5ab792f33b03e19e69e6fe4b10ae83fbfefa78e70f28722f0d6976446f4e171c24559ce8d947d4f8c29b08a2fe994756ea50a7390d75911045f08949bccc98ce6c87ec6856ced2fd6940e620ccce5b6a343a5c8a0b544f1c81d5824feb58be9740e02808c05c6a4c1f782d946eae3bfe8f3021385c4f1430815211c9d8deec4df983821c9b58b5bf48bc6778b899b8ca4174bf41cc6adfd619131b48badb656a2d5ae30c46b6456b2af6803605a8b161410998ebb2782a13a9218aae034cbafc033ddd6b7c5980ccdbce02bb2dc00a8f02825df12248684417c874496fcbf9266b79c353c5dd1b5a5b0e757a51ef1847f2e491b2b1b3bcbafd68fbde12184e37dc25c636386dd1c130ae3756e33f98a02ba48152990e67d10ebf41764fdfe12347a874c2044c7530765752ae01d20a1bbe030476db0fb7ddfaa6f9740487056dce476fe7b9659dd12599e261477cc434436464dbea3b7cf55074b86f18c903497b276e2d2ef2468d8a4c71ab4804373969632d5ad6a752e47e1cd6e9da250297c29f47fb8010bbd96824e7e1e25c083cca163f2f00022699a79e75a51cce4e119bf04cd24ccc68e1f7b7bf26f5598c9deae845acc99b1f3f68cbf1bcbfd1b97c7cff5caefa0a703202d9635072480a54a8d8e29fe1b66981fd68e924b7315b6153bc1d862a69b98f9cf3d655
private theorem part102 : 2 ^ prefix102 % Spec.Ffdh.ffdhe4096Prime = residue102 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue102)
    (e := prefix101) (a := residue101) (b := 1140501970) (n := 32)
    part101 (by decide +kernel) (by decide +kernel)
  rw [show prefix101 * 2 ^ (32 : Nat) + 1140501970 = prefix102 from by decide +kernel] at result
  exact result

private def prefix103 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (0 : Nat))
private def residue103 : Nat := 0x3942db068cd2a8da09f9fd8cf87499e7645443a21c44e30f95579a140d09b2fc4e7a7598d357be85fe8721a50572cfe0b1ba60e14ea82841f964aa0b25b217598a70861c972b9fe6f2e0a8bddf3954799c89c81e0c89c5ab69e677e37e23053d0770d5a63d3f545ea912bda18af23d5cb56d5f9a30dc068f300c5e6b252eff20692f2cb12e1e7d003ba2245f7248ded7443eef4845a4d3feae1cbb40ab4bd4a4060007ace35774ad884f9c0a2398e5e794352e9f887157c31c69a231c2962365f8b7184098945d60ecc6967a0342d4ec0c9caec95ea5290012ec2ee1b0e358bac4a96a8cc19d2417b9d00ebae4471ea8bddf70a2a6ffe6d64215441ec7294e739037add645dc57554c606a0bad94d1ea232acd1c283ce9894f80c4d8d19fb7a50a65af16d95de8b081ec8da259ce14ee1cb07b440ef98ce9970f868e639e0a90bb80da956c15630180223df97cd29666e6f8f640af70e5f34101551dff89d17ee5fb2b7215b7e666c2550da9f7a655657b8165d7b79ada5bca06dc65c0e05fe21436efd8456a880a6879f109921600539e968a98f3aa8c1a6cbb62eedbd01d602dfd471920cbe4f27236755540d41f3c360e163b91d7d7cfe47f60d9304e60eae9be2d55870937743c33b85ce7c569aa929b9608b89e0c80a4d859c89df0efb702ea99f1c5e31d6597a437aba21616e74fe81bbcdb09b67e33d6f8968058a6e5
private theorem part103 : 2 ^ prefix103 % Spec.Ffdh.ffdhe4096Prime = residue103 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue103)
    (e := prefix102) (a := residue102) (b := 3206080061) (n := 32)
    part102 (by decide +kernel) (by decide +kernel)
  rw [show prefix102 * 2 ^ (32 : Nat) + 3206080061 = prefix103 from by decide +kernel] at result
  exact result

private def prefix104 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (96 : Nat))
private def residue104 : Nat := 0xbada4de62d89efe09ddf5c76807d675726f0ab57ebba4177cec32f036a7f7936eaa2311b4e5a0706ae70f21da625fdd01f3823298fc204a12e4b04de13e28cc530218163c269fbb76f858f5fca75db8464162bc88c1572e668435d8f61b3b0e37f10bddf75fd39e950a9b2aada6a93d25e3335375cc451f94b0c1de6fcfede5bf9cc705e7f148531f58cc6aa467ac7a7d1c67901b3b861c58041310497cede70828595443f38832d71cdf7fafaae9a6bd40ab187b8b7038af36a147b670fa19d65e966ba3416207fb73a854c8c590cc802c5d59ae9a83b7c0825e0bc0b7f67e9a8a673c4a771c29018719f9177d5178497dc1d2b4416e5160ded9b62b0ba263fd01574d229787e1a35c03f901c3e5f613bf72eea232ed4f1fcf4ff2346e8e20f4863cbf1842730c06b9b6c380a50440691d51e2ff4b9529aec59effcce17e4c32796b146f51c4e891c9d8923f4470f21bc162902e4ff15739bc193821f43a8f82dd1d202dcab8dea2775bbad54b54becdd7bfb6c2d0dc33984271dcbc327886b7016316fca9eb487fc9ae8026fc5ca9bd086b037b52a596d723b11e7113532d97043c6fb0c47f932217ce3f45e053fe5dfe2a819e68f905502863518d0043de952fe850ca58eece48ea158535efc0143d1088d999babf6afec7c063d598f6210d6a96f447f37d52f46cf5691bbf1dcbbdd361bb32fba53b88f61af9f97a4d601
private theorem part104 : 2 ^ prefix104 % Spec.Ffdh.ffdhe4096Prime = residue104 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue104)
    (e := prefix103) (a := residue103) (b := 949675075) (n := 32)
    part103 (by decide +kernel) (by decide +kernel)
  rw [show prefix103 * 2 ^ (32 : Nat) + 949675075 = prefix104 from by decide +kernel] at result
  exact result

private def prefix105 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (64 : Nat))
private def residue105 : Nat := 0x8f889e33c492e9e9b7b20fa01f0f26bb9a58c97b5e98fa0da89a27477d4309e94dc9a238f5468a4bacdc0f86b8c3d954849e5a46867a3ced0abe192de824c3c270888abf46d868603f2ca0d41223567d0aa2934904e27e71a053f116e26f688353f89d02a34771d6227b59d2bb222bd43d5868ccbd6b4dded090989a84c35fe50336cf51c33d2ca0c2022efaf051993810f8f8c2c74ca76a80c413bba176ced28f14ceddfa6edb8d958626c8f47590c6013bb6cb2bc0a7262c704e4f7200ee2c7a3526b14dd7b1590a245e6a948267a31782a731b386af149d34ae4b059b845dbdb12a136972a87498b8e984588f27cecfa6a1c009d54f0b6defd624eac0633f12ee3d36e11907afa815195108f3f2439bfb5736b08faeb4fd6f4d806ec613ad71b6da6e62e5e2a35d19eba57e179fd37274e9941d88f876e9ea6facbc42a3bd6850e35ac3845b087386ebaea1bda2ea8c7323d423042b63257bed63984907fb685d3a99c0fb3b30468f0d770c615bf195de1aa3638802e2742ef993fb84756a653db0e519b1e67bc2910bd7b7750df879a193bbbc85f6cd780bd6ee11eabac6bc05a34e9e23cdc1c7d197e8c7208b9eaec350abefa2882b833dedbb7c8ca1b8db361e2a51ec65ac31ca42aabf2e4daa6b85399b042f047ed742c73267e1e3477c77b36a8176a10577886dc5c1024f5474f43dc96ac781c5b292ec2d810ffadf
private theorem part105 : 2 ^ prefix105 % Spec.Ffdh.ffdhe4096Prime = residue105 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue105)
    (e := prefix104) (a := residue104) (b := 2010781893) (n := 32)
    part104 (by decide +kernel) (by decide +kernel)
  rw [show prefix104 * 2 ^ (32 : Nat) + 2010781893 = prefix105 from by decide +kernel] at result
  exact result

private def prefix106 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (32 : Nat))
private def residue106 : Nat := 0x244a59929effa2a000d163169b1c6a9d7e0aeac2dd4b0ffa318de5c67e04b13c777e3a964aac08af9d6fec8aec62e35f7d32fef89dd8f304057b728b452d054815d404d0ff6af8544a4de75a0703755756d329183a4d70553b581f6704def20aa077e2df9027c88a17a0047ce5aed7c16aa1b22e536b66654db10568dc03787a3f066597980c090292e42535b6720ba67d6cfa93d1ab30c0be5882dc7819842a7eeff0d2f11cba770f8c71c7db4a3112e4802ab4ada6f52e05bc280278349217788c43dcd4ff87d1e7efa9551ab5204cca72850943502e66296ceef47295a98d2bbdf3345a5fa2278996aaa9e540a97b362b9a073af0bdfbcb2506ad4b3fcb3e8b6f1f0eb08d89cd9fc9dbed156e19e78bcb2980b3ddafb4445481a311513d58d18342573ac3aaa8581c5e775d60d13243c7071ffa2d0571b83e43498422d0d672375a056a6824dd0decbf7f74fa9e1b512cafb95376674d07f788b71ea1ac9943be018b6db7bd453fa8a726dac4e6e2b4542420e2df72526d283778670821c1f294fd7ec489af6509a2a0a12d1d4b45291ede57a814cea144b2c352378439f498e3ebad08f325f74e69f6ca41dd92767f4b627ea5135fe6b37a8feddc49837596d86d607b435ab7880c9fc35ff766037707443ab357ada9f9d8928fc4d651eeccba34fe32892325e0ca02840f467ad5b8bbe8ca34310cda735a565f5b112f96
private theorem part106 : 2 ^ prefix106 % Spec.Ffdh.ffdhe4096Prime = residue106 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue106)
    (e := prefix105) (a := residue105) (b := 1991577344) (n := 32)
    part105 (by decide +kernel) (by decide +kernel)
  rw [show prefix105 * 2 ^ (32 : Nat) + 1991577344 = prefix106 from by decide +kernel] at result
  exact result

private def prefix107 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (0 : Nat))
private def residue107 : Nat := 0x3efb04ec07e33f3b313af66f1920373dc0955dbb90122632d4c38ccc96008d3d69013bbde7b3555b97ef2b140d55cd6f7a543c996c4223e661360830af4175f470887b96a47d6b96f6a9231fd957013e469b9847e03b7162bdfc9beb21965e327dd459a5e0d43a67981893ae64f5deebd918838b5a950b284a4a1cfb2365402d9d780f99fa4daa5432529f7928bba5ef85289fa687ae0f712c1bd1c8b68915bd382be69a8ae70216facdbddd5cf98d17758044272f93f9c721af8e2684bdb8c2771c76eac305996ffe29eb5e8296ff4884c41e5dacc4182b20e9611c02ae399d9bc0dee2164b081767bdfd64812fc72dce061278a77011a702f096d77eb0eca6cbf46284afd0627fc353a0056d92c40949f8382205d8018bb27cf771cc1015b6eb1e5c054888c2742da409cd5146885370ac4a74d6709ceef4198fe87725e341d4be5b5187cc2df18288e81b1371ec6b36c0f5caed2f615a1e84782b2d1f9e7e8af58b0f22fdaed72103aeb89bbce4bcf247f9f3325fe144994a46020a0818634b59884cbe7650dd4032150777eba635297693d5da87c1474bd11badba335d825c02ae0727b5dbff4b2f5e1a0bc85f2a1a6af8eaaeb0c2b4635d8c87b2bf0c91fbcb9883d964f94322b8ebeb54020a615c35c8e69ad1ef7f52d82df3cfcbe530d60d7bee4578eebf4e3b44c558fbeb35774b4c0e9bbc91819f0a7e6562596714
private theorem part107 : 2 ^ prefix107 % Spec.Ffdh.ffdhe4096Prime = residue107 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue107)
    (e := prefix106) (a := residue106) (b := 2530161689) (n := 32)
    part106 (by decide +kernel) (by decide +kernel)
  rw [show prefix106 * 2 ^ (32 : Nat) + 2530161689 = prefix107 from by decide +kernel] at result
  exact result

private def prefix108 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (96 : Nat))
private def residue108 : Nat := 0xaf5e61e6b286c322c2e7f6fefa34fc9a3ed27086b24abd213787a4c837938a9b1d884159ccfd7c6e43751c4d6daf356caf7e4c9bba7c7199b211ce1d9f8b36c77911208b01a2a91ac068cab9773488602c114a8984a786ca6cdbe25883067e0bb14993b481324cd4b07ab49d6d9968a34a3dde2abe9d362699c3d97b587812121db26bdff862f850a0ff966edd456c0968322a2e4563a10bc3e8ea7416f2da9f34369b15589ca1d1e9e540e02757e63c3a48869b9992d72d1d8ee2ca72cbcffbeced2f98a43c429550dba89213151f1b74a2967165f1ba5c1b179c78168a35957053099852b289c0154f3c7edf52822f3d8512784fb722a4ab77753c7ee8d5f0209b1daaf3a316513a7c14046b4353597fb8bc571b0c28a0ee630a46491d81cd111158b1512ce232fb64e9d69db56cbf0c560d2520ba8faff444506a78407b0145fe7265aad63d622ff15f6824997f0b2466336c6da3739aa344b27dd4ee901d45c9085c520eb4efe12a4a90264930da185fae7f456d11ea406557023293fe4823002000ccfd4b76f66ba3169e5f6a24622f9cd831fbfe11c9e9b850c65c0aa3e9e7d7a93e11ca191060e93797dab218af16a3ac80546a21aab1470ad5fe2104246f1a4f066555dcf384189671a41fc40307e2d3300269790498592035fe86d4a9b4e673b85315f7c181a1412b4f22b9572e8eb2046f1211cec7f7fac0b4412e
private theorem part108 : 2 ^ prefix108 % Spec.Ffdh.ffdhe4096Prime = residue108 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue108)
    (e := prefix107) (a := residue107) (b := 1417916421) (n := 32)
    part107 (by decide +kernel) (by decide +kernel)
  rw [show prefix107 * 2 ^ (32 : Nat) + 1417916421 = prefix108 from by decide +kernel] at result
  exact result

private def prefix109 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (64 : Nat))
private def residue109 : Nat := 0x92e693a971969339c6526aaf5d8a14472aae10866efd52ce534d8d2bde76eccea7f397e96c2d980109f2367037395f1f76c02d8352bf774b052bcd053e6f911d64574b8648cf9c0d410036c02e0d7422712db2b64e4c5ef8574aee477707092592f5a4df2301afb315394529512c80d68afb1b68d07024928f9465bf293d2b147b91ab05ef0dcb48e5dfdc258cbbb5aab4578037077634afe699fe8cdaa15cc48c1b7c91c360be9195e2a9c225c602a199dbae79fc746f9e8f1eed7a3fad832b27d4172f6cb6c3bc77c831cfdbae1ca346dcea7375ce7f7607c8107a51b4010b0ccf5574e50ca0ded3e78293bceb2d32e864bd24737813b97dfb229cfcd9db3d658b0e8da991abe38c184477f54704fd38c0f3a61973b40785f9aaa95e21770be6f1704d70a822b3e639ee69d15bcb82d7928d77db9cbe9081acdef54ebe879a9d30d1eee9fade541e62b2c6348392ff62233be581345870c37ee21a6b851459eac32148b9d9057dff7bbd5465dcbe97fd326ca672291a9f39a5191516826b428f68d2c2560b0586f26371a8ba82ddb077f505e626942c9518b68743c9a1624afdd4afe27262233a8e9a30b8bdde775c2203f3934ad4750d60d508134b933d164f341f3212869128889f8c1ea243967e3ccb16ddef8192a7d8a77975743a524f6a335bcffa1ecb033a50bd629fca44689b23c7a0c376d67af8ce89ed131172f9
private theorem part109 : 2 ^ prefix109 % Spec.Ffdh.ffdhe4096Prime = residue109 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue109)
    (e := prefix108) (a := residue108) (b := 1220581474) (n := 32)
    part108 (by decide +kernel) (by decide +kernel)
  rw [show prefix108 * 2 ^ (32 : Nat) + 1220581474 = prefix109 from by decide +kernel] at result
  exact result

private def prefix110 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (32 : Nat))
private def residue110 : Nat := 0x8d968203e20c54738f36ecf20c382a87bf58037b409dfe61234a85170729eca0387e5264b4b7b1dd7429a5f16830b3404e7088dc2637a9c272279819940ecb4813371ffd8c772351842cd68f6a2d540586bd96ae637830eccda803a47e6a2999e93c06b778a34a46b9936846e6733a707426f1d106b3bff6243d1f59cda028495bb975e417231f562a6c7e08f32ae0950ef3bbcc295544584806e27125315870fa2b589b71bbb668f5a9aac8b3936f58b83f0202e9d5db1b925a7af8d16ccdc0fa6e1fdbf2c21eb04db50d5c1ece2322a32563f88a93fdefb2ba9d729c9258cd05eab73bf77c8eaf70ebaf745bceca0b0535de75be6745fc579524d04a105bdb71594c7c8c5b6fddb65f54c7f39bea0d998f3e9a6553d1d3ae8eea4703698a0ff95a17c09920891215e8d76de0bed28792ce57114d86def42fdc54ed300d960085538a7a511cc419e7168f7dad3566519f56a9e027ccf5343a342ce667fbf2f97d255584d1d0d2afb7d54078007eb1482b336451c717234af6f264ab1c3cd6fa5397ce29367dfcf2e31a5998b3bf6430d15d9eca3ea9e2df01ed346eb5b723b014f9c028dc034e95e8f4faa2a70422f9771c0c44414266d4d808c9911b5d44c876ac22e662d35606c94b21689daccd0ae1ea1fe7be13a004ac55f162d8fbe81f887605a36f307db226476ab6ae73f5ce57a4d2041c05e984e5d4f2984dc94206
private theorem part110 : 2 ^ prefix110 % Spec.Ffdh.ffdhe4096Prime = residue110 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue110)
    (e := prefix109) (a := residue109) (b := 920894588) (n := 32)
    part109 (by decide +kernel) (by decide +kernel)
  rw [show prefix109 * 2 ^ (32 : Nat) + 920894588 = prefix110 from by decide +kernel] at result
  exact result

private def prefix111 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (0 : Nat))
private def residue111 : Nat := 0x2f65da260931bc864c58facd22cfff670719e86f28231ab283fcfdce3ec16acb378ee7edf4526b52c2959e389e1dd6733e6cf4a052cfa153ebc860375295447d128fefded2eafb02a7b7fd31b8bfcf270c0e36bb078c72a814094720e4c303b2221e3f3ea6b1b1dbba1ee5b8a6a2df99341ba3545304cb67e8668b1a0c61cf55c08ac839193f8a62cc5883277b08193ce2a386c7b44d77bb4d03564dba53a20d9f6a73bcb8f26c2071268e39448a0a12e7ce0b2ab2ff35d1447252c99868fb227602c999a68205f9707379945dc06aade40cbec1f41b5158e3a1ee0b74ff71c5d640ad83c9771d0ca9f4c7e06081f4b1ee6b2f38709537e5cabb71f37b2869bcba718c2038ed7eeebefc784abf680d63a2b91b01b458c57af9b23a8e36d9deac979f5fbf304bf3ace3fc1b174cd5bb3cd6cb8ab883f34c8c497b11f918c45ea4ca55977cf7ed3d00618d478bae84271e618daf3c65dde5373f2e7a50168c062f60c9f743decc10dde448eebf50d7581a89db64cf126d20b00878f0083ca65e13e2ebe6b32311cf2791a549928e5a166cc04f28109fc9ae0c8671e601c3a8315d84524e673f3ad819d8d76ea301d43f82b508d3713a4761a987a46c494227225e79c6318650ea944d3b87cf9aae9b5c6e856a75c07709fb5db928b1fdaa361254e9e01edeb6bea640defd36c7eb6fab069c4750bc17b71d59e75f217ff41254e8
private theorem part111 : 2 ^ prefix111 % Spec.Ffdh.ffdhe4096Prime = residue111 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue111)
    (e := prefix110) (a := residue110) (b := 3101065244) (n := 32)
    part110 (by decide +kernel) (by decide +kernel)
  rw [show prefix110 * 2 ^ (32 : Nat) + 3101065244 = prefix111 from by decide +kernel] at result
  exact result

private def prefix112 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (96 : Nat))
private def residue112 : Nat := 0xfe9b0e470c6969dfac18eef583981b9aa80e868e535072d3fe3c27eebc6c505368b1d45043d417f96079e113e0dd962314917bb55559b4ea0d957d6c9a2c8b17196b956d195f47016dcb431137fa3dd94207d1ba86c166c8b0e8d64085b4fccede1e2ac3c1c86ed40193e4f5248de21118e30eeac9f91fbe0989f3a278b71686fd82db2ecf348d23134122aaf39e0396020e7e07730f25990a89b0b32c5ccb5c26175d0c834edb27bbe404f94c8b31f587a70d4cc6785aeff816f69675c96f93b715ae9a394b0f01bad7bc0359640eac0c91ec873f88e85571218572253947c97c6644581d5b4f2f32d2db0c945061782717e35195d7361dcea40d3b475ff8ca189c6e210575087166b7f10d4d5532cbc8f14bccc417e1474fd670693fab2bcd65e12452705c0927fbe796e12db535d32764e35166e21f8ce08cc452b3157d3dd6c02f227b787a29f4fe0a8a2d84bc373d0a4128f3e92c705d4c595bf13f6ad4384f83855b1595caf22e8110d30f88017710205c4144369ed1e9a4a3a56cce427bfb37f738fa11a12aeff5f1cbace1073fb2a5f14b83b7129122f023acf8cb776eabb5784ae31291f28d47c4d61cad715f70a32a19a0814589d06134bafc0ba7f01f21b4ed759b5e2027a7e1dbba3a545d435be1b109940b6ca3c29b77c5d331ad6da0c7a5cf37759fc3074dc6c30634f39f24e5ab3a959b7b848dabc8718b71
private theorem part112 : 2 ^ prefix112 % Spec.Ffdh.ffdhe4096Prime = residue112 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue112)
    (e := prefix111) (a := residue111) (b := 76860625) (n := 32)
    part111 (by decide +kernel) (by decide +kernel)
  rw [show prefix111 * 2 ^ (32 : Nat) + 76860625 = prefix112 from by decide +kernel] at result
  exact result

private def prefix113 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (64 : Nat))
private def residue113 : Nat := 0x6b0b9772c2a6e3a90fad3c6a8ef71c8c2a1f2e55b498cbc404fbab8ea6ec98b3fb4356b6ea1bcb8b836ffbcc6aea5e48fb0e8dee59dcec5ee6d9034a69e28213ef6cdbe79891cdbf558220f79bcf31770f596761c7045b2301959e6e7d4c03e030e0e2f12484ec27026c1e19e7ede0ca0402be39651d19df48f630e571ab30edd5d56e4746e9e9675847dcd72ee6dcb6b7efe9b3c069ecea44f8bc4eca84e4bc94fb6cb56b4740246cacda32fc93965a1dfe9713dbe5762aca0e3090143bf5b307125ad313942d97995cef32d372498f2919d24618579902606572e29a5ccd7fc09b36213b488d032d2e26775ded879d48aaf52f90b1ec49b6bb63750562a2f79a64ae6408d4932f0d5e6235b1396757dddadf226d7311cb3db37eeb1514b900bb4457c1c64eddb4079fe101b5b2ccf390f57ba13498cfd3f8694d4ed3a7cfe2171a8f734be153f5516718c825b157938b14509ce1ca9456e38d4fdb989d9bfb86bc7b14738490655bf1a70fc79356265a5ff43142f532beb0da2804b1e20d832e86c6b94b089353b9013488b08962330ef9626f8644c731a3206c1f21c273506a458953295fb6fd503bb11cfad9e275bc233f46f2c7920f53d92526d85a53858a93aea51c298b0c9ca4cc07018f68590a4fccc32c3f6cf4956217229c3f42920ad76356d4b1e601164d9f2850a331a7ed9d10e840b2b7809eb087b297d730cf
private theorem part113 : 2 ^ prefix113 % Spec.Ffdh.ffdhe4096Prime = residue113 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue113)
    (e := prefix112) (a := residue112) (b := 2581972413) (n := 32)
    part112 (by decide +kernel) (by decide +kernel)
  rw [show prefix112 * 2 ^ (32 : Nat) + 2581972413 = prefix113 from by decide +kernel] at result
  exact result

private def prefix114 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (32 : Nat))
private def residue114 : Nat := 0xb794501dd38971193c91aa8bf09247a8224503d7666dcceba9ba5a4be083759a4b981a1f344826b2c0312efb3879e488546387f1ea7be13b3e23fc8c351916102bfceed6db75b154004241fb81a98435ca89dde7074e7cc139549c900cc09434f04788a4fb77187cbdd63f23001f7bbf701aabf72455c50a4e303f2ea25d28405c41a78b8c2c0853ca2c6d8033b2e9918e5c7bc79e6604bc8d0c713d59e0e913d20bcad61b53cb51687ca8a428698453615c212ac9d83adf8791262e5fb2544f8af4aa9dad92c41b19718bc78ea211a2b0c3f1a21bbf38bc7bb0ad295c5878dfef3dff19cd5845df09599a4ec1ca6c3e5873f6c1af38500ec7121621fdb9a74451e5dc39a0b53e3efa740cb0e496bd908d11ce88454ad613152c136c88867f3cf3aeb22ca539b511b14ab8a31877c8731972f9917d9e97df86f645d25aeed4f4877b6ab51947a70bacd3b34c5a8b957cb15f483fb5d08c5e8e093a696ca172288c28c3fb178c2e530795f938568241eff40da1dc954c1aef611cf52c072ea68609e095a4579cfb0eb912f2a6506731af0c7c52111c7bda682b6953ea72d85abd9a1f21276cf4f0bd876d5d759d7ce559e183348d5b1c2903b24ef8e2344c919c5cfcbaee1dc874b4a5ea236d99548629ca81f3b05e30224dc7dd89766d570d489516cde51ce624947e6ef78ea331c85d699b60b52ac8fae721458b6629d09e6f
private theorem part114 : 2 ^ prefix114 % Spec.Ffdh.ffdhe4096Prime = residue114 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue114)
    (e := prefix113) (a := residue113) (b := 219077790) (n := 32)
    part113 (by decide +kernel) (by decide +kernel)
  rw [show prefix113 * 2 ^ (32 : Nat) + 219077790 = prefix114 from by decide +kernel] at result
  exact result

private def prefix115 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (0 : Nat))
private def residue115 : Nat := 0xacf73ea6beab1e18858a2acd9de7bb339672d9d006c692cd65d13005d5ce640fc681da9e483a48953afeb78b8d639728bc563453eed44bc8bbe744986be34e84ff116cc9d30d21e96edfa912b34db2c4350bbf645c17066be8799d36e2d2b4f782af3718af74bbe570592cc26ef21e0ddde742dabf1af7c18f4e8b8ab2ae840c5065765247c56edc61964cbeef733b9a3a7ad38bcf63f429cea352d24993139de51885d78256c02e528a09c931443b492c0e9e18595d8c90b7c1d2809c0ae3611dc744db576a1f7238a28cf6a45b638dd874a071409e7d3481fea7f4de4a1e95db9329631b01871b6dd8f1b5f902647d9d1e853ef018202d3fbfd26f8b04ee35203961a56c2b4410da590a46aaca055eee09babbb72c256b5d4bad773559f14747479fa8d90da3d583bd811922319f286ab79095f9964e269e370deaa2598b56153b5ade1e3024fabb6141b8f5babb1430bd269f3aa5694ccbcfb121f739a5d363aa3412b19838055f211b05fc8195b1416bbb09fccf55a46a56e014bb888edfd1445e06843d8fd6ebc96e126f4d4b87c647f3e99d609382ce40500aee38895b83d170c5a8238ebe38e4de9cbec62d837c44feb89ca98b99810128d495cb7b008a5fcb01997d6fe6dbde80bbfaeb0c79308712faa759f1a9f632fe2a0ddef3190ea5e16d22cb5fdcc6db192610c75f296dbc8466be6befbde9b273ec4c6873f2
private theorem part115 : 2 ^ prefix115 % Spec.Ffdh.ffdhe4096Prime = residue115 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue115)
    (e := prefix114) (a := residue114) (b := 3097493534) (n := 32)
    part114 (by decide +kernel) (by decide +kernel)
  rw [show prefix114 * 2 ^ (32 : Nat) + 3097493534 = prefix115 from by decide +kernel] at result
  exact result

private def prefix116 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (96 : Nat))
private def residue116 : Nat := 0x53c0923c88a7ab3759826d3d87d4214b9d4d1e6bba1264b3b066f633fa24f6016b333078d43ba54fbe0dd8aad04af6b0915be6fdd3aa3259a377d754fc34e1fa948996e9ad2ec2121bae645a06c10088f84eb6b9dd3fb8f13822d3f0d84835cf433c57ee27db5f55462316cd8fea191d04a7691811d4563f47241de69b2880f9e59f1053140424343190f043f47a48dfa297606874a1d9c89d64817f1eb15158eb520974e9515f899c86d56f926d740150c48713bd9a897d8d0613c1374229a46487eb3e2e4aff811efc40fcf744573da3f3e1f8c887f4e968f38f1f174089fc4e0f96b0798043d87112700ac743ac658cb57d08fb3053ca78929cc5e9a0fb6c46c9501146ea87ea1015b2815ce30253d39b161eb644cfa0a31538fefba5c10cc3b5ab1b7c10489536a9663164eea53037be27c03556449640bf6be9082eb7714d1d15524111d0fde1f50626aa1c5f72071942ab3435137c59ed4efb255b8355ceb1062c6db680c8147aa19c56e66e9d8b520e444f070d907e70a7964a35a368043a38b5aa5a2421b2536e7b8155e5b7b939dd74d5dc2e814918bfddf1be4d89838a98943a8f12c67f57bf59463664742d1d5bc581dae4666a9a4aa8afa20b68f12e775c509263ade4a1607b70199a956038c3a8b883e35b7c72c63a1f0e8707b3688a6ae6ac78783eb460734246062b1b2cb8bb3b681831bef1c80f32eca147
private theorem part116 : 2 ^ prefix116 % Spec.Ffdh.ffdhe4096Prime = residue116 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue116)
    (e := prefix115) (a := residue115) (b := 354903892) (n := 32)
    part115 (by decide +kernel) (by decide +kernel)
  rw [show prefix115 * 2 ^ (32 : Nat) + 354903892 = prefix116 from by decide +kernel] at result
  exact result

private def prefix117 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (64 : Nat))
private def residue117 : Nat := 0x41cf52d92c645d62dc9ff88d895c6ee8152ac43c66dd6bba99e7b008b00998c21e4213a1ef363d78cda8155a9afab6ffc05f9753a7f067ab7eab329ba9f4d6def95f8cc47ad64a6f166b5365d44a48ddb6f6dca707f0f16d5230ceb0dcae09965535c1e665d2b25a49e4d1d7657b290574508f9de9ecdfe2ad86290b4955f50ddbfec312346fc1483748815d22dceacdc32b2ba3d5869179632bbeed3869bd846cfb71bbacf1dde711325dce5d53e8db659800c39fa3543418447ee02b48e11dae5680a630b4232aa7eed6b050ccc0c37b072b5be383ba0e2ed624ba88fc779bb9b4b63cb495d29007a7d024e2fb080c3f707e8ebec08621b3f85f580f9de731e79343fccbce64f608a49d3fb2a7937969608f11571102d36a35df9d6d991ad9a214c237840c111ef5a5ca6ac782c74dc7ae34bf31c344c3e5ebe9273dd74168a9166aec899488b1fcb51c6ecc64783fd92c8787740b04badcb8cde2c4a429a778455cf7e5e52d4cf61eb7cc83dc688401dc1cc56d2149dc1f9073a6dfbfc6b3d441e1da7207d235d1a8f6a6325dde897d454c9a4320a0b66dca82c6ef15c5308c6f7a0ffad24f9794b2f9da421e54463efc69e52af4480ef0700b09dd83335c975c827c57076285f3a375255a21ce847fc7da03e529a74470db134f9e88be2d69529a690afd7548f8079f286d26568b42dcfe01cce31293a1ffd9bee565b60
private theorem part117 : 2 ^ prefix117 % Spec.Ffdh.ffdhe4096Prime = residue117 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue117)
    (e := prefix116) (a := residue116) (b := 4240868710) (n := 32)
    part116 (by decide +kernel) (by decide +kernel)
  rw [show prefix116 * 2 ^ (32 : Nat) + 4240868710 = prefix117 from by decide +kernel] at result
  exact result

private def prefix118 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (32 : Nat))
private def residue118 : Nat := 0x3df99de7d9b40c675f07269402eee5449a01d5a7df4524ea44b160099767aea6c67b394a65ee5eb2f42024ff1f650a8a18cf254da275683746d9c2d9d7d0740473de2d19fd7a52b367df89f5e269a87cb6aad5629bad9a1699224b8d97ab98a81049d7d4a671dd343384a7cb11b8f651db5e9d690e63d367c449839feb0bfa5113cb3e94adbbbc4557bc47e61cb951c70ae45ab3b91a580bc9b2b8b12c966e706bf2d873898aed23284f378c1906a0e42ffd22c085fded45747f5d9598d4f20ac69e54accc3eaf2bcfe74863a45f6e9986ba34abb148005db278e9af8efb1e2e6bc6c8e831db7674fc7efd1702b1bfa9a49490713992103c158c8e12e72893303568a69da66131564bafc56924155bf95f8dc93ca2498cbdf7bc17eb5dbdf5b4bb359cb9b969f2297d928275ae972e85d24d7c91019e9d5ab9be3db55e32d41d806d9815ff95985a0adffa693144b8653a975242c273f71dd0d57b6b73ecec8b11bb5e56915730c52ff977c65fb8395e867d0cfb1f4eed4e0220dfb8739e50819179615d8eefdb8633401510873cb1411ed07be975832013ef2844be4d490295dc71e87b5ed85a8c74ab6fc7ce92386da589a485644ea39424ac9bf6d7cf51e1bcb8f7966055786d1a7366cc62c49c8e4595ffd542df2c0190fea804eb9a2b8c61bc2095d0dd7071806b017df1ac5962565c30ffed6967cc5af8f2d8771e87e0
private theorem part118 : 2 ^ prefix118 % Spec.Ffdh.ffdhe4096Prime = residue118 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue118)
    (e := prefix117) (a := residue117) (b := 88164582) (n := 32)
    part117 (by decide +kernel) (by decide +kernel)
  rw [show prefix117 * 2 ^ (32 : Nat) + 88164582 = prefix118 from by decide +kernel] at result
  exact result

private def prefix119 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (0 : Nat))
private def residue119 : Nat := 0x9c1868947348f05e536bc5fe8ae3097ee1f44244b33d32ecef6af8464483f1deb177b5f74e0e37367a190b61f4bed394cc993f153f0b91bdaaf5580d79631f2dea095b61814989532fa1a5b74dde7e6721f99399704fc93dbf48d2cf36218b4162db58f8bf609f46532ee26b6b187c7ab0f5fd3c375cf62b6066bfde776feba60de0c81733e7f7234a30ba8274304076cf45f3038429a98d426fc5cbff1236167d6864922f9bd60c06e713c9d5eb2a0e145b853a9f665ce8150643a3fecfa2dcf248059920e5b599ca4ee2935bdde0c3b952fb73bcf2b771479925cd8a0e70a0a705ca7cf56787cf719261484a3992c9b423ae9a44604b1e5a39a0f762cf1890d1001c98916ae6e3841cd53c1f45ab2610b94418808eabc0fc7a8d3da693fcfc599166d3dc8f5d599fe9b58f6f2c9c2a04ad382becb14d097cd48049de77d37961dfc596c2906ad92ea6be4d33c67f41593f0fc4ab77748ab9c6205f067385ad6b14293773bd81249e01d7126ed5cb91d12968fd4cedb98d4f2e698092438117787e8c052709f66fbae3c2172043f294628bfe2c9e8ab6c1b7cc21d7a8512c295d49f8abd2818a11db9fce921f7a52ab737aa4757c3447e3656af0d8a592f193c24b135ee173e2068f5476811535e53ecb9e02c38f7aa33af008717cb2b40853451bcd5d60257dda6fcf665a3fe653a190106b7c1f7f11b04598c6bf48c21e0c
private theorem part119 : 2 ^ prefix119 % Spec.Ffdh.ffdhe4096Prime = residue119 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue119)
    (e := prefix118) (a := residue118) (b := 3882139367) (n := 32)
    part118 (by decide +kernel) (by decide +kernel)
  rw [show prefix118 * 2 ^ (32 : Nat) + 3882139367 = prefix119 from by decide +kernel] at result
  exact result

private def prefix120 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (96 : Nat))
private def residue120 : Nat := 0x6544cbc0320ec609dd109c6d3517e7370e01c2d0f7feaf1cddda9541abd684a08c31f9f679b06c167f2c3063f4da09b792e0b82dc710c95b5bbf76a1255a3efef3e0679219cb053caf29e74bdbdfb378cf7571fb8a22e2e97c3afa93a96c9ddf6016f1b78781ffda401d83592e630bfcc091592129f2976a913ace9b67284133c34cfa34de665f9dba8d609d1018795cdbdcaf2ed6e90f9660003428feed2e774813cb8ae66ed6c00e88afd87f78efc845e02cb612f867a961cf7461db6270c1817db078125849fea1a82d3addc5059c6ee22d8a24e95094133f9243f8f054711fcc5c2d934b7c1b435b12bf9b13f33601f11913fbb1ddc9f66a68b6a25629f8584e6944da575f1b9c16955d2551e09e61a0833529fba02fc10f743101ab8296db1f1408205d116b4717a92700bb527c72227b83f194272c2e331e913fa8a5b9f72f1dfff79802c161b6840ba95bfef3eb13c9a33a6c45be638ba2aa706b38c78d9dfd4a8670fb5e2cc2673dd978b72a5bdb0baffc8b3251e3f0cf245c8ad4b98dcedb2bf5fa409143f86bfda85a48816ca4f81fbc544aad570a42988abd1d17124ed57636892de80bfb4481f29563b4d25fdb83eb2ff320e4a9412ec4463328f86bd1656f486f6bd54740e91677a8ce4026cf8964b8867866ebd1812635a5551a36cc3f68905837517be5a0c8dfe71beee8ee91b216499acd971c6b0ca134df
private theorem part120 : 2 ^ prefix120 % Spec.Ffdh.ffdhe4096Prime = residue120 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue120)
    (e := prefix119) (a := residue119) (b := 3345275565) (n := 32)
    part119 (by decide +kernel) (by decide +kernel)
  rw [show prefix119 * 2 ^ (32 : Nat) + 3345275565 = prefix120 from by decide +kernel] at result
  exact result

private def prefix121 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (64 : Nat))
private def residue121 : Nat := 0x2bc32946f28c49abe03d9d17c0d3f49dc132453440798a189ed1348e17091a8a953b2e902570c71ffe972957576bef796ba6dfea80fad29ebde9f1737529bf39255ca4eecc120c609f9e36a079464678c1ed505c19eb7f7da2a296ecd17eda248f05a8e966257ea8d4d4042e9e6b80849a3c2ab2bad15bf0606fc6833f77d6e8a021672773702d0044972a69dfb7e277eb076a15c096c802a56ecbbd825e7140ca5dc4171930a5241bc00a1385631a13ed18199bfa3b3d0d09c44e7703901d4141fb08d59fa48017e53588bedee79605114d5e3f7ffd6253b58379ed74386f9c092c41eb25cf2ccf18a57f3b9766ed94dbacd03c75ea1759515e1d3a060cded63570f0c58e2b299648c47a6d0aebdbf2f6c450c2d3d900dddcb429f538662ee9c03d9b67be203996fb559c9567f6c7650cfac317b71f2807f676e8db38e4e760438a7c9daa90b230b1f06b0b1da7991727d3e02885b247cb2e12852c08d4f21bbbfbe65cc032b437d847d8531bc0fcb8e73c93725d32de8281d8637f04cfe5c5904ff06f9488bdfb613b827e301e603b2777d1f50eb25205f0309a0ce8686fd96bef4b1b21e824e308030181025e72f3f24d9e737ea30ae69d6270f87f96a9c92fa348286b57b375b88abe6cbf9173b06edeb73e932afc91a2f4cd37d694f6bd9f553ee671c7bf6a2348dc4bdf5bb377106f93dad42db31382d8897cd53383cd
private theorem part121 : 2 ^ prefix121 % Spec.Ffdh.ffdhe4096Prime = residue121 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue121)
    (e := prefix120) (a := residue120) (b := 1069830709) (n := 32)
    part120 (by decide +kernel) (by decide +kernel)
  rw [show prefix120 * 2 ^ (32 : Nat) + 1069830709 = prefix121 from by decide +kernel] at result
  exact result

private def prefix122 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (32 : Nat))
private def residue122 : Nat := 0x14bd2136506b1393838adf79011c05eeccc32f7099eff1167a5a700bb24f595dc9ece180e6d256b43eff573f90fcf8048c83614018fad371b06d53d10f0da5d1896086e2053f51746824ae0e5d97b7e96ff74fea0bcb7f73eddc95d40d55497d139b601dc3fe665a3a8a74e320261b8453612c7223aed623f4c1b569daf295bcbb5cea7591d61835e5b6485ccb1c7ea16fb1068ebd6545592361751f2654416b2b865c522ff966c4c58db5b7741aed04c9ee964666cf4400d34d1757275ca4f1c96254955c286a0d740d5812c57351cbe3c5cd5bf455ba5e1d29690ca4a0220b4897e7d50561b96d963dbcc1d23efc71781c01e3ab54cea19700ddfa6cbcbd224a091243e288156951229e397b52f041f44548641bf30bb30eb75fc0b54923bcabb3b4b88a55969c228b608519f43a6c4e53a53295c445bd571fa0e4eae38fa35aafa61bd362af80cc4cfd3d692a7ba4f47502d88003384b24623e8d6eb1672321a92f9abcada1bfcd1fa46a8868c996bbceb547a983b81cf7d0c932a986af03779ce35ca34387d0646b1c8223194b048fcd94ec3e8fe95ccc6fa4852ac2b13538689a71e0a4178f05603bdd1576ff138d77a10197773ed959b9c15fa2bcf319161d271abe1c8068d4c59f2458daa6bfcedddd57a6783175b84a3f8580ab3f21b167fdfea42e3335a6a8aa0c723b014842690775643fa6b9b5068985a726dea8
private theorem part122 : 2 ^ prefix122 % Spec.Ffdh.ffdhe4096Prime = residue122 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue122)
    (e := prefix121) (a := residue121) (b := 2799359016) (n := 32)
    part121 (by decide +kernel) (by decide +kernel)
  rw [show prefix121 * 2 ^ (32 : Nat) + 2799359016 = prefix122 from by decide +kernel] at result
  exact result

private def prefix123 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (0 : Nat))
private def residue123 : Nat := 0xb644e51aae78c20dfcae69962c3123d3b197511a685974e7d34a709d48cb468d96886d0780c9c9fada59dbe73a147d831bb31d328714db7aa2523f690b66bbab09c3b718a4e1b79eb736e9e6d2ca1b821fe7ac7b42cbdfbbdf0ceca47fab5c9182be6285e9879f692e777743188c2dfddeba395060374af2cd5d3067177dc7678386433db7c70a086f17fc2e61bea8446e5c56ba49835e26699b86c69f217a28bbc4e5fa84ed3b5036f9ca322bb80e866ceaa01317ce649cab4fb29272e9746433e11948d29cd2b679ea9523925d8cc068b9511790ec43e670e999dc48897678baea64204dda535ac44e2591aa9c1f993ff974ad7b9388509738a748de3f9d514132d084e3d52de96d98a84b82677d5d96e590829262c29f69eb3dfd0dbf837812d2e9baf3f5b108990a5b32d8fe066fde239bdadf72ae7ae91508be49b4b287d0c40defeef131bdbbe1cc395cf20fe49849ee974916a45b8dff3efaa87656da9ede2dd4041679245810a3ab0553948eb9e24eaaebc1ae7d1667b19d140457013a528a7bbc64a020f0f5e5c9a762646f030dc12bd29beee5c40212cdfa202abce6853db84bdb80f9f23a2ece31546097fa59e8334d0661bfa1c19fb8b32d3a3f814d83f5fe7e0ff0325d4c2d7a8f313bce8e0ca98cab77cc3d621ed15472a432c0b206a1d87e84493310b665889836281e62938c9fba40ac6cd92f1ec2a31f04
private theorem part123 : 2 ^ prefix123 % Spec.Ffdh.ffdhe4096Prime = residue123 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue123)
    (e := prefix122) (a := residue122) (b := 4196450672) (n := 32)
    part122 (by decide +kernel) (by decide +kernel)
  rw [show prefix122 * 2 ^ (32 : Nat) + 4196450672 = prefix123 from by decide +kernel] at result
  exact result

private def prefix124 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (96 : Nat))
private def residue124 : Nat := 0x77ce4a5450f106b67533a19c9c321a8ae276366780ced01c5923a373bad25e01a4293440815654689f93107fa1e1b553c0ed5366fd6d2282ee2624af63288d7aba9eba013017169f320eb6acb82e721d32472f4d236259b12adeca42174dbb79ba60f3b27b30442d73e35a554cc7d5d5a0a60edb1c7d9faf1be8dfd087438d7ba3724e247a1d45195ca0bb9e01abb33362153e3890aff1059ca14c7f2e945036572c8ce966fefcb3a7f7874f0066e3fea63a4df4d912515affb9b2f84c54bf52c77de655087668418b5757cffe48fc7a571fc9490288c6bc011ba5f8690db414e58b944cdaf46f1430f4fb7b927eca38f71d15cdfe8f6cb96141d464e85c0a3a6fffa287c79f42cd9373763ab6be984dcbfb66ed74c09c605b0ab0408e5fad7790126d58f2f300b19e815a669284598191f27077cda85ef1cc8e19c6c4211d47054f49a159909549969f106e0d95aa2757a74bbeae175649b6b416999c96021f6d5d5e67936c4850e7db570934584a64aa9a1bedfb838629ce77948014244a8467c2d0f1ec5291138104c813bf5d6babc0ff57e209e33f204f774945757facb0992bf11f753ca1a20a7bc32ff2829fd2d5684772ea946eb3dc2ac01c10524125cdd4e74a7c53e67158e43080df025b97e5b8b3522b21aa5f6d3dbe43773e51702097bc8f0f9071f8bd4e70d40884872f8289361de1da2b90a15ccca2eda0bb4
private theorem part124 : 2 ^ prefix124 % Spec.Ffdh.ffdhe4096Prime = residue124 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue124)
    (e := prefix123) (a := residue123) (b := 3812950079) (n := 32)
    part123 (by decide +kernel) (by decide +kernel)
  rw [show prefix123 * 2 ^ (32 : Nat) + 3812950079 = prefix124 from by decide +kernel] at result
  exact result

private def prefix125 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (64 : Nat))
private def residue125 : Nat := 0x39bc4668770f3ec0edc8b065eb2f0e3ca22362e05909104ff03abf52f64cf223c55584e3bfa982e7a84c4cd237ffdba55c2f27103f96cf5e5e6a559c6da4f12cca547c06e33e663a0c2c37608ca6441861e67a6542fbac74059b6303e04cf68c42d50ab39bdadfdbadecc1ecb46ee4d8a8165e0e11e524cdf68dd9334e394a34b2f7d72117de17d9680ccb2ef8d60e038dedcb9b9030ebccf8d7ec5fe91fa34f2566ad9a2f84dbba3f26fca3516c58c117959779b8cc58f7d015b5e59e81cef221337ad92720a4d1283de7dbe2a45cd816487e7d6dd27d55f745db44b79b336a07146a08c6cfb9e1f5c23143d847826fc316824c88997ad3e7a8e56ec160a5abb9a2b99dc5d2128554aae4966b620422b1437c018a03ec1bc171f68f301628e249509f01a6232316213874ad4c5f6b60217070b6328d6304e42adc104c5fa83be0ea25cc87391daa4735308bd2c68b0480a32ebf2e37464f17176ce24cf49d9b53a4c94ebf036bde7e43ae924f6ec51e6e3bbabe4f2b8429422216cba66f995ff14cf4e6ae3a3f84d75308c8f046d7c4530e7b6d46c2d05e0aa3f96086faca2feb602e3a19341cbc591badb7e54f053ef13371786a00b57a8fa286149df4005d1aa950a3b2b1092a918532d64b5e1bc2f0cd52cbf131444894bd733caa2177f7723d11e385c2dc2350c5acb0077e70df804d1f37b0e05605630c832b656ebce2
private theorem part125 : 2 ^ prefix125 % Spec.Ffdh.ffdhe4096Prime = residue125 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue125)
    (e := prefix124) (a := residue124) (b := 791850933) (n := 32)
    part124 (by decide +kernel) (by decide +kernel)
  rw [show prefix124 * 2 ^ (32 : Nat) + 791850933 = prefix125 from by decide +kernel] at result
  exact result

private def prefix126 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (32 : Nat))
private def residue126 : Nat := 0x40c2c2b0344825cc8100121eb6f482a2e9ff0ba29ca7159b850ec80a58c19fd7e49e49237b3aeec02ea3aebae4ff68410692a142a076f1fef1cbd777cbcd13d5714a3e8bd630b1d25e70b3e7ca8c1257f53c9a15f000ce4b1fa66ed148726213c660ca0bd10ac8a1b1555f9b13848e7e5762361d6f253510e855eb6fcb7cf66948c3ab3db963faada3b3e908472d558119022eed001ef0c133a4647e09876f1e03fa0ce4657e66ddcb92c72d716e9346cecc91e97df67f7dc1d00221fe527589f5a06cf8efa7dbf801db64292d8b3b71b0fb726a8913f140edc61a731006876f8aa2d65227cfa307291cf00115d2fda437f3c57d59a2a50acca7679516f4f60eaad8144c655603b43e23d8633c92ab114a2627de0efab3823e8885fff6c6c3bb3327761846b887e399e48fdc5e728a248dda049d401ccc550545175fad04ef3d236cf8e0786c1860a63fa00b21a13a332b061cdebbcf3c891db339e608291ae79c369eccd41898d52125d95bed5d53078d984f80c8f5149143d455dea14c1a71febe4f5dab4b7690d6895a1325e54bb04908129b7ce25681c2eada40947bea408e027639990316b6ddd7b486269141541c290c1f5ec943b8ca14c463c37edfc8d71727fad50f86a05bf188210db72fba047701cbaee32d42660bc545d0a5649e029e5f8b79c45ca62566c0cbc40ed1ad94ab12abf7b79000f575e9f905536ee3
private theorem part126 : 2 ^ prefix126 % Spec.Ffdh.ffdhe4096Prime = residue126 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue126)
    (e := prefix125) (a := residue125) (b := 2147483647) (n := 32)
    part125 (by decide +kernel) (by decide +kernel)
  rw [show prefix125 * 2 ^ (32 : Nat) + 2147483647 = prefix126 from by decide +kernel] at result
  exact result

private def prefix127 : Nat := ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (0 : Nat))
private def residue127 : Nat := 0x1
private theorem part127 : 2 ^ prefix127 % Spec.Ffdh.ffdhe4096Prime = residue127 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe4096Prime) (r := residue127)
    (e := prefix126) (a := residue126) (b := 4294967295) (n := 32)
    part126 (by decide +kernel) (by decide +kernel)
  rw [show prefix126 * 2 ^ (32 : Nat) + 4294967295 = prefix127 from by decide +kernel] at result
  exact result

theorem subgroup : 2 ^ ((Spec.Ffdh.ffdhe4096Prime - 1) / 2) % Spec.Ffdh.ffdhe4096Prime = 1 := by
  rw [show (Spec.Ffdh.ffdhe4096Prime - 1) / 2 = prefix127 from by decide +kernel]
  exact part127

end VG.Proof.Ffdh.VettedValidation.Ffdhe4096
