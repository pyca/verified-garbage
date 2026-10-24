module

public import VerifiedGarbage.Spec.Ffdh.VettedGroups
public import VerifiedGarbage.Proof.Ffdh.VettedValidation.Power

/-! Kernel-checked binary-power certificate for the published modp3072 parameters.
Each small block checks its arithmetic; the shared append theorem composes the blocks. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation.Modp3072

open VG.Proof.Ffdh.VettedValidation

private theorem initial : 2 ^ (0 : Nat) % Spec.Ffdh.modp3072Prime = 1 := by decide +kernel

private def prefix0 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (23 : Nat) * 2 ^ (96 : Nat))
private def residue0 : Nat := 0x706cea1bf9bb7b08887ae3bcc5debbdb231a9ba4f735ace17e4ac7e9c67f368ab1179e317ebf46d6e302b628f6f603e48c344923260ce71cf848edcc3f2c12cd6ca050d4a8116440e6522a702205c923bba738db25649949a0e529227eed167858afddaae00b79be98aa9661cfe3b77305f7157273e9e86da1cbf05488ed9cdd7dd390d4a1bc813c331ca180bba9f15595d064a92f75369994b72dbe3b711be1d3cd8ae5e942da6e5f9c40526e0f9f5cecf3215f177acfd1078dfc1af06d5e000100fcf7c30115a17e59bd2183f7a1b68dbe00290cdccd472484e0d3768473e5ef5a3f6707291246ffd532b62c27d854c2916acc7cadb7fd1a15001d82e6e27ea40fd07c8da82cc28126a7e7a78474d2c8bfb26d991d0b024b2a0257062e8d70abc539b31d68a9b2e2cf2688e10990a2f3b174ea88e899aa098e26e61e6582774e23514bfae1ff282f2661fab91b45359429f3d16fab74ac3af88ec5b12695480b87a13004c552f36e49ef63897b923d424805e26136676e4122623324a04be0
private theorem part0 : 2 ^ prefix0 % Spec.Ffdh.modp3072Prime = residue0 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue0)
    (e := 0) (a := 1) (b := 2147483647) (n := 31)
    initial (by decide +kernel) (by decide +kernel)
  rw [show 0 * 2 ^ (31 : Nat) + 2147483647 = prefix0 from by decide +kernel] at result
  exact result

private def prefix1 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (23 : Nat) * 2 ^ (64 : Nat))
private def residue1 : Nat := 0x39128c236c6fddb50dc9c651b781afc10511a38c0a536c439206366c740e7c00f1323baddb3f95960c11f53be3e08c630817adc2afe9d41d9d3e72659643947a2633240d891cb411742ef732cb74baa01c9cb8db560ea684a0f3716d3fb3399af145e25664ec626b9dda3d5e9bf441c9cb39432cf39c5e30d65b831d4f51ce01bd04eb5cd39a27f7e17603afd87754838149f7208dcd6b3c97a92b71451a7e93ceb4d01298f11785e50b714b2e4f8a3cb1bd15d25eb9ca7078303e8f5096a9e9d122397756599499fa73a0f6b43c2f882f83dd821b5bf34a01010464cfe08cd30e51fc3eb4389baa8c94dc89a86f71aea03c8d9ba242be950484d2b3adbb294c958e1c4a705b3ba0571cb34c6d25459d35efca2ebcd22c87b78c37ec6168d89cccbe1af9f212f6c41c9e55d8e303f52aa6f03076c99db0662b621a332d10870663ca143aecd6a13bffbc60695de0f091abaad8e37346c2713fd47193c94ee60ca193f91128c7f9754d6d8a71142db6cc6e42fe0021adc75ceeed90ae2d4382b5
private theorem part1 : 2 ^ prefix1 % Spec.Ffdh.modp3072Prime = residue1 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue1)
    (e := prefix0) (a := residue0) (b := 4294967295) (n := 32)
    part0 (by decide +kernel) (by decide +kernel)
  rw [show prefix0 * 2 ^ (32 : Nat) + 4294967295 = prefix1 from by decide +kernel] at result
  exact result

private def prefix2 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (23 : Nat) * 2 ^ (32 : Nat))
private def residue2 : Nat := 0x3f42f46e4afb418cfe53d611102669f2a0efc3cd50a2e9922043d4157cd79811a4d3043938d6e18a9dea6bc61d1f8a7b2d74fe2bab25c20864e6633efe52fc371f512c34be119f285da3b871b6d0bc56d1a2c09e692e135e5e4900079fb0776c654d50ffe8598ac69c2151392f2b9b19701c87cba3f3a13591f2e80cdb7c35cf467c9a7fba0fc96c8164ca03313e0ebe83bedddda6147bfb6cec4a7dc96bcb2a724abf044ac8ad02f104aebabcf1c284019982826e6b16ad47ddfefb972f23aaa0a21b8491cd7998f4fe564c8c0ca38b27ad4e67f48d7a4fbf183992f6bd720671a0e5944d85270189e9692df1a843867be853046a83176ce2046df7c6f1177b978177051f54a187ac23c21f431da014c45fb072ff4bf6bdefea74780cdc046479a2f4193b5d10decd4e2b98a51b036ca03fb1e35c6ac35c901c9262ea947d8f0923623f0084b3527449689d408ac3f4e274d9c7b91acf09e12fdf3c81f660c14223c1c72da1b06494ca93a9267ef1dda17382688c00eb7579357896eee24964
private theorem part2 : 2 ^ prefix2 % Spec.Ffdh.modp3072Prime = residue2 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue2)
    (e := prefix1) (a := residue1) (b := 3834113361) (n := 32)
    part1 (by decide +kernel) (by decide +kernel)
  rw [show prefix1 * 2 ^ (32 : Nat) + 3834113361 = prefix2 from by decide +kernel] at result
  exact result

private def prefix3 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (23 : Nat) * 2 ^ (0 : Nat))
private def residue3 : Nat := 0xfdc6b0b95216cd9e8c33825877aed6091e3c9a372a149fc137f913180b8dd6f7b5e31a4ddaec5e134c8a9546931ac118fd58c799b26ebe5dedb69f406baf3a31cf3d9e338ac6b96c51ae810418e25ef7533853cea7a7aefea4141006c0cfbd412ba2e4a5449668afd7ecf75c9614a0494a53b77b6c153e4a8a17cbea10c736ca62981f504acadfefad9353db4dac38aa1f95e5560ca295973f8041045ba462c269487a374691d8f40950b9d3873f66574eaadff3c2e0063be0d619f12288c8618daffcb5fb178e10873d9a0a9cdc8316f09c2ba67bc79abf31fe788770464804ddbff628be3b03a2f3f690d46850d38e8f84d45c876829d4c74ff1f6c6f2a9971ccbf8cea1f3ae8be133d4b483963d6dcbafbd79f899a0bda9c3b73f64d697271fc74777f79ede0ee7118dbb99e56834e19fb167c7c9ff4878e79a0275cb164245120041f350e342b2bddb155e3355b4e6d367b8aad4d546cae211508b194c802dffb60c3646f973025df6443ee7b7b994b62c3e7b74dcfebffff1205869c1cf
private theorem part3 : 2 ^ prefix3 % Spec.Ffdh.modp3072Prime = residue3 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue3)
    (e := prefix2) (a := residue2) (b := 280256794) (n := 32)
    part2 (by decide +kernel) (by decide +kernel)
  rw [show prefix2 * 2 ^ (32 : Nat) + 280256794 = prefix3 from by decide +kernel] at result
  exact result

private def prefix4 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (22 : Nat) * 2 ^ (96 : Nat))
private def residue4 : Nat := 0x27ec3e26b850344d8800a79322f6c3f021c19bee420123639c0f68b9ba93741d6663be34f931e1ca60f06b8604ddb80f6b888a4b3725c4e47ee642d4e60e281781109f25183616e4cd31e2fab1fb228590a24cb06ecd06715690e7f772f0974d4cf3aaa41f885cc9d33ec506d85ea6a5bccc50fa9a0b75ddf789194ddb15a65e05ff51a4f7d6340d37537e6aed081329f824b0b3259f8d803ac79e4a8a7500cc55a934abb9e6c704f2f3c6d34f77a8b6d0668da36bdbebfc1622eb25e48e1b8004c6f7051a6dc77f6cd8f818e2d449525afd87b1da2b776c02f0d7001c99a8e6dc99a90b27273b897b71e56e23ace30a2bdfa0a25300123face250aed4cb5317205505aa9ca459b218bd89700b07f07c3bc1b54c8f523c2f2aa49c708862a693c6baf6526ce5a32f13238478c77b3cd29846c26024676fb8d83767acd213a063e336e01f08659f5efbf06c4dee8ddbbbc6c523b7ad022e37fc01df62251ed0481df2f77a25d9b122e40ed9606b2f734ca8d30c81862d656c2aa5e28793d38a7
private theorem part4 : 2 ^ prefix4 % Spec.Ffdh.modp3072Prime = residue4 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue4)
    (e := prefix3) (a := residue3) (b := 1650667845) (n := 32)
    part3 (by decide +kernel) (by decide +kernel)
  rw [show prefix3 * 2 ^ (32 : Nat) + 1650667845 = prefix4 from by decide +kernel] at result
  exact result

private def prefix5 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (22 : Nat) * 2 ^ (64 : Nat))
private def residue5 : Nat := 0xb32c7e11007b0e888159e0725498516e2f01d4c4bd6b15bffe2616e94c55ed108adbcfa709cf74ffd11a1a7dee799ff71c2a3956e21446d22ba73e6ecd7d61505391f010edd325cce2dd1e52070adc333a986af05363b8ad404ba66e1bcba3f4a1f6dab63e5e06f1cbf55ac0fe1e2bbaf50278cf6fa2a4039f664e971edaaf5c82234dcb6037ef10ac3792c106714578868907ad97ebf4caf950d3c7c1c3b3d9cb878874b633d7252d49cc7a061e7ea6eb96e663850a6284c1a160e123d45cef044b3d445f9dfaca9a25a8d79a5e754bff8a68b6279c6fb815ea0b27d3d14fd7b6e24da836c4bac8859dba0a7ab3ad4c481a34a6a82f1b951bf84761c5ad2e335db61756fa43183c9af7765dd87346b46217c15d314f0c58b384cc83642d8de4732e0e0efbe6efb593fe818a1b83d43be4154d2257066f6b4e99887b744a7134d15b66dd304449093e12166afe6805296792072cd3c6a392a0fef309ccc7f7665398c15213b50a2b69dff0c4a48ad04239272c5b30387ede3616b97a326dec37
private theorem part5 : 2 ^ prefix5 % Spec.Ffdh.modp3072Prime = residue5 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue5)
    (e := prefix4) (a := residue4) (b := 3228438120) (n := 32)
    part4 (by decide +kernel) (by decide +kernel)
  rw [show prefix4 * 2 ^ (32 : Nat) + 3228438120 = prefix5 from by decide +kernel] at result
  exact result

private def prefix6 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (22 : Nat) * 2 ^ (32 : Nat))
private def residue6 : Nat := 0xe81b85f1f495cd63a807a7e11ecf4c24794b13d24d299916890a18030e371b95a4db33f8a07bad08be73ec8941dfff253342ad53fd3d9c0384f9ac577027fba3c81f62d58172feb64877b38f2dc963cb655729b824b5e904f5e2c809fb306dfdad3b559525a730ca36e288dd0e0339e9be6771409e693c7736c16c85c054dd8b46382058812b214b50dc669faa80b774c51dfd3278e7942bce679fac1097bbd69e8f2cff5d4b04de68525f2aee0c3d00251152cf68e33d9f8420432eebdfcd6b46429f099a56b8b7a7afc67b20fd695c3483481f69135298ced5797428edc91c873c5d54c9227ac7cfdd619d87c6961e40564fcae62b52732dcf564dae540dc60b83b8dd5f039156a1a62e3a142602f9d9bc06782fc9520a9af1ffc91b6f8834695bfc642f0729dc9f7745c8a8f778e0290761f83bf985897af0a8a4d829a9fc7718018637325b697a5e6d06024ae903372eb5c644ceb19bb8892003f2d974f66b18d576328c980422a46212134921964d4f7ada9ad7c3563bd7f4acd164066
private theorem part6 : 2 ^ prefix6 % Spec.Ffdh.modp3072Prime = residue6 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue6)
    (e := prefix5) (a := residue5) (b := 2491492100) (n := 32)
    part5 (by decide +kernel) (by decide +kernel)
  rw [show prefix5 * 2 ^ (32 : Nat) + 2491492100 = prefix6 from by decide +kernel] at result
  exact result

private def prefix7 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (22 : Nat) * 2 ^ (0 : Nat))
private def residue7 : Nat := 0xaf609e3d491b1fb9fe9a3979c9aaf38c612ef33a530d4cf024c2d497d8e9a549a97e29bf6b1b413a552ae098e90a395a3c1af773f315434eefd9993c46cb262e2422276d29f05d28b4f5ce5b9260890c70a8b79575e5836becc2aaf60d80ca5daa8a6a4820f9a8337a535ba685679d9cb26ee029cfbf0799091818a1464473ae019967666695baed7b727ee703a97a0b5bcd259d1654d349f842abcd1286b0dcf9717bdd898df2386d3e1eff254e3775e6b8986098afd419fbb1d09fa9f16c2da7a7467b91d6ea52f8fa8e0fe698290b082924e36e9926cc1464769a02b9d9e638cdfda33538aacbb21a502d02f351efc9f50c887d553625b8cbc061e4109380985a9accac1ad7ff975ba117e21067a0dcdbd0b757e33757de106ce386de0e65a9f8344d96b36f2cc8c41acbe5efcf06429d4efc81912434c6abfacabdaadf5d6227bfae25d4636d475cc4da44ede4c8ed29f739f32a04aec116c10ad673748dc266893d3934b41e309be4c4609f3b8129ad70a6bde22d0e297528d61d6633ef
private theorem part7 : 2 ^ prefix7 % Spec.Ffdh.modp3072Prime = residue7 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue7)
    (e := prefix6) (a := residue6) (b := 1161029178) (n := 32)
    part6 (by decide +kernel) (by decide +kernel)
  rw [show prefix6 * 2 ^ (32 : Nat) + 1161029178 = prefix7 from by decide +kernel] at result
  exact result

private def prefix8 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (21 : Nat) * 2 ^ (96 : Nat))
private def residue8 : Nat := 0x2ede3fcf0fc5bba623faea9e4b02db147c94646c19560596486d1809c3d3c7c6482eb941840a9450459c7eb1e9dd0e546c5429664ddbc9557f1003039bd338c4e5213cf546ae9fa7e51ef9555a0a589bded58aec66a3a430de5af667cf32f81401a1b0e5af218368be08a7273d05c6fdd4ec36e774dc1c8387150455e4c222b8c7964f53cbad57d2d3ac17c2a5d62c427a53bbf08423747655b9483522799c52616e5aa01b927564d41650c8c00d87858ab20679c19142543e5d71954f8f6c23b38401b6da0d3c1bcb8128ec09d8e87e207df0c12ef750d4b4264b7d0a246a053f1208e1f0103111f14fe1644690d492f396fb4f4a959a96779a77a2e0400d18806b9cf75d707f58f9b50e8512a77ca9061a94797f5e3dc55aa4ba68da0fc8d5672e19f6b26c3403c29abeb1029167279dabeb974c323c8e3267c7c94804d7b34f77ac97e746c298a5e5bd733a2ae4d92a86b34b711678d872c38e1196872fb4d261fe3bdfc8a2475da81f516129542bc478778e61d0b52781f698eed34421e3
private theorem part8 : 2 ^ prefix8 % Spec.Ffdh.modp3072Prime = residue8 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue8)
    (e := prefix7) (a := residue7) (b := 17162067) (n := 32)
    part7 (by decide +kernel) (by decide +kernel)
  rw [show prefix7 * 2 ^ (32 : Nat) + 17162067 = prefix8 from by decide +kernel] at result
  exact result

private def prefix9 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (21 : Nat) * 2 ^ (64 : Nat))
private def residue9 : Nat := 0x4ef060b1fcd8e23fb99e35a849e87c82319eb0191553db2959b8e42469a24e5697f79049956490e3bc6a3e8f27e2f3a67e33916b7b68905877281212df3d7362c44dc9180b54a7d588b24705a75b76984250f0bf28ca3e4f2f176d9cabf39efd4b9d31dfda296b0341de8cc1804dcd314bcddb3acdef5560e2d3eb6b9121fde36e5f6ea5089ceaa1dc32dda5bfffbfb7ca6ca3cf2814091d0aa2ef8645fd47825539c157d8d9bb68c1233ecfaf3f1b0a5fe52bb9bfda2551787c90db0fcb779b95db0b09d839a784b5fc90283c31564a08a851963af56767e4bfa42c8d5aaed274ca74b8f6b689436ffde25db56fedd242ba18f0d6f929004a356e1f14b0283a3252dc22717b71b2bef8a39a797e64fc8b06e246abdb5a42f0aad87c15ec766e4626b0666e199e907be83f54909d8fe24b70616b4b51612f0951acf47733c278380ef7a8498edf586388ebd7ec4ac6046e15f04e86c2b2911976a5888c106e077dca0b8655f98a62c8cfca694a361766162f63069120964de2d71512b1cfc93
private theorem part9 : 2 ^ prefix9 % Spec.Ffdh.modp3072Prime = residue9 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue9)
    (e := prefix8) (a := residue8) (b := 495570321) (n := 32)
    part8 (by decide +kernel) (by decide +kernel)
  rw [show prefix8 * 2 ^ (32 : Nat) + 495570321 = prefix9 from by decide +kernel] at result
  exact result

private def prefix10 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (21 : Nat) * 2 ^ (32 : Nat))
private def residue10 : Nat := 0x60964efa354434658ce41db1f25cb28d3db09c1d126f7638a0467e99f2e92d351c4253c568965c4feb80cd4721884fe84ef481b9c132900a3c4c9dcf3e74816a243a9b6d5f40c77c35f1e9b1d49c799a949503fd57d18988ea5826aa77b566c85d421159350d44202b1bcfda6e9c84f558bdfe9f1bc8a4916d39fc4e196f6bcd62116bac1ab135be28e41934ba702aa63bcc67cb356524a7c0bfae9ecd41ac8ef9719ca76fc85fed1845f97b4ebdfab98c46a244db15edffdb80b542da2ed9130652c176e00bb8841f9c4ee2a7ee4202e3817b67d9eb23dde84669f16eab115cf7082f5e7cefc84480aa9c61a239189e6900a76a1b00163812dd2c4efac5ffdb35ac613aaa4121703156d78361ab6c5b2c172ad62bdb9b23977b2505e13965dc2aab07c5a65c32cf5baeadd0dc23005f73a6601d692e688e4a7b9b7c958aa5e020f23b1c0e49ed15b90824f8b1ec8b4f70eb58b471afaf879d8aa564ed190b04d75a042e3de308f8917a941742ef560df19fd52c5c6cab7904de73d87bae9996
private theorem part10 : 2 ^ prefix10 % Spec.Ffdh.modp3072Prime = residue10 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue10)
    (e := prefix9) (a := residue9) (b := 681903164) (n := 32)
    part9 (by decide +kernel) (by decide +kernel)
  rw [show prefix9 * 2 ^ (32 : Nat) + 681903164 = prefix10 from by decide +kernel] at result
  exact result

private def prefix11 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (21 : Nat) * 2 ^ (0 : Nat))
private def residue11 : Nat := 0x16238ee097197380aa1cd47fb59b700e701a13bada7926df8f8a132d7afd27b1b746c45a6fb6f550ccc3fd256b45da5e3a6b9cd80f2dd6aeb8cae7614ec232b81059d51a26c5958dcf251547a0c8fd03963afbc3bceba54a207bc29c0852610ee93258a34b09d5178a4a0aa134465a57135512da51dfb0e44067f9d65a06c3a83286445f8ddbc57d581a628c12db234ab72349e78e476f5e351fac3ab772bd340962e6f0bbaa4124793e43a79496f3063ed6afe862dd57b042c81fbc5ec85f0350ddf21738755688d40a072b43c28a3e2b25f39759ac3cfd5e6b8da81cdd77df82e1bd5d17ce8228994ad7a79490247a69b4aa5b4b3381757ad8e746b3f4dd1ff199b9b967cc36fb3dc0ac282dd4bd1cf5463e10161c87e84dc3ab3b4480c39eac24f0106493165b80f90842b946d9784ea46052ced7b30050cd86b837da8a4f6cabfb031b8d55976b7fd407b58d5be03f7d3e6ec6efb8ebc12b78529f85e09132149230d925a5e3a813628b970cfc9ba54b312c6f9ebe4f56a51ac4aca787ae
private theorem part11 : 2 ^ prefix11 % Spec.Ffdh.modp3072Prime = residue11 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue11)
    (e := prefix10) (a := residue10) (b := 3340370542) (n := 32)
    part10 (by decide +kernel) (by decide +kernel)
  rw [show prefix10 * 2 ^ (32 : Nat) + 3340370542 = prefix11 from by decide +kernel] at result
  exact result

private def prefix12 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (20 : Nat) * 2 ^ (96 : Nat))
private def residue12 : Nat := 0x91eb28c03c4b0c400cb088526561c0a0c685521e221ac2e849a22b67d238b90ea76e3b85f4d04eed3de9498e310e4ba735548742bf1b1f8c84e359fecbda095ba5919b30198ee8bce528a830c54082f6195495c71059732dafa11c0e16e2175bfae46b6fb1e479406baf1111e2fad483dacc977ae54901355d6311aebb3f0d3dab3d0da157abb50c0c08471c1ed296fef5002ea9a1951d4ee41265a5fb0299acb737c3690f7db300ee8827bb5465f431ef9ddd4e1d242262085d76ca79866b5ba4e776b1c6890588e5a9079f0bd33754bccbc7684e083227c4c07503d9b5d1a82b325145d86ae9ec6af0b3be1dfa740344f33d1766faa63dbd483915b02fb330336076a44f614882e6abd7b6de409970d975e2d1f85a36d9cd7037bbd18b9e3ff8cc03c1467f54a2c6b5143d0f42f2bdc00f951a46f0e42c4000d674a3bab0b8c03cad20b6aa60ae9070355696f8881b13cc0622c1edad798d21698bc659b46404c84d99f0486bae8ad3b1cd7a8b980c0c97cd789ac4818f73f11ba56ed54fb
private theorem part12 : 2 ^ prefix12 % Spec.Ffdh.modp3072Prime = residue12 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue12)
    (e := prefix11) (a := residue11) (b := 4157246681) (n := 32)
    part11 (by decide +kernel) (by decide +kernel)
  rw [show prefix11 * 2 ^ (32 : Nat) + 4157246681 = prefix12 from by decide +kernel] at result
  exact result

private def prefix13 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (20 : Nat) * 2 ^ (64 : Nat))
private def residue13 : Nat := 0x98b5b2c1038f8d22b3794892644b031f9f478db373fa499ec327af32b8382128a82116017c3085fdf87776df52823b89a9544de43924191ef3b46a750d71331cbfecdb04924c274b61eb3ed00e342a2d1098aaf2d63323fda98f00b58abd7d14c471558f52ef4e4ac55a3783edc3adf2b1faa121f26ed0a12962bb55a7c447c605c4006d9b7a2f026c8e966d965dd3a6b24884178dbf133e146b59e383c33bcd9f17d701cc368424bfbe5053f8d4fc8de4761c2f3e8c8b589ba161080dee29150c6adc0dd871f294e820fe5b00a51d6935e1454e4b7d67c20cbc0194f85c3aca204f8a4695e40f113f39aaeeb5f86fe02150eaff9e3717f0474a8cc30dcfa70dc9b95315d09ef0e37ef9a236889e6df585e2d8f74a14397b62f767ee10090e726650ba7fbc5812dbc934637c10fc217457093540a9c94c7c0c1b96c48c3f5f9ebee079c4f33ee7be3d6d2bbdc18d72c45805d1dcb728c1a4836fed08fbf8f20c4e003876b91364addb41ed6adaf8c85e2f4c471b8b030d7dfe6345ef5b627dc4
private theorem part13 : 2 ^ prefix13 % Spec.Ffdh.modp3072Prime = residue13 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue13)
    (e := prefix12) (a := residue12) (b := 3869057421) (n := 32)
    part12 (by decide +kernel) (by decide +kernel)
  rw [show prefix12 * 2 ^ (32 : Nat) + 3869057421 = prefix13 from by decide +kernel] at result
  exact result

private def prefix14 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (20 : Nat) * 2 ^ (32 : Nat))
private def residue14 : Nat := 0xf25f5a6164a4fc3edb0c574a39a9a49f1e97249ebe0baa80960b2e17bf15d359f30ae934fe50e1940532fc25343da15c878a4102324f4da155bd3fda029cf00d126a483c328be4a9b2f1ba69456d8b5c4eb7e42909d6e985d0db68ff0317179bdf1315f1211d42c38956b04d7620928e4c64b909950671ff5b321b2ae1f4318ad4e205b17d22adb2086171882f12dd42487ef5125dffedc59bd36f7eb98d21104f7b99b7c4096135a2b370c4c52ab901cb3c521c9c6f366e7ef00814771af80d36fd5b9c13d1fe6296cf98ca31ea86f2afb9934255176672a4fdad172bc0fc53a739d7c5146c5dcca22507d214ba3569ca37f78c4e245a0c8ae30882bb554860ccd3ba601a6b1f22e0f0434442eb6c87b1cadc49d2556b6edc64f7616573b35973fd955a2931a15f4c496a8694da82c4726459ea695bed89695dc51ee07e2aab2d1f1e42b8f59d6bfcaa648b38b13210c62788a8a8e8e9c0cc83f1808f73dbf5a1e36f5331f8a99e2d72aa0d8cabda66efb201aa60c8a64264b0b9cc31cbcfaa
private theorem part14 : 2 ^ prefix14 % Spec.Ffdh.modp3072Prime = residue14 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue14)
    (e := prefix13) (a := residue13) (b := 2551547190) (n := 32)
    part13 (by decide +kernel) (by decide +kernel)
  rw [show prefix13 * 2 ^ (32 : Nat) + 2551547190 = prefix14 from by decide +kernel] at result
  exact result

private def prefix15 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (20 : Nat) * 2 ^ (0 : Nat))
private def residue15 : Nat := 0x8d2dad595baebff003e28a990f2a71ce0968859d45f282d1215ed04b2409084aabc9e22d86e4c56153791efaa86de283889f991d474955d4fc204bb0525e0e05c80b26dc06facc2e1933585289f41828961ee768d59388233319752dbd546d35ddfc440070727fc0d0536569d3d3bbbc200a5f05bd294de96faa287d95fe0366e31c175c7d283fcf4634f2cc225e38a4a1a1ec638f8012bf2f4574b33a5874e4859bdb72350b855b9bf2469da0a2e05c8b5985322ad13a6c3c40f214d88237dac941810cef0d71d84f00e798763fe43a291a29265b1327733aec87bf39108684d912b863588faf9bc86145f84436d37617a9f6f3c17757992eb65d0dec3d7a0796b90596108cc6e03f854f6ba65cbdefcf6538dffc851cf971cbe9bb20fd32f9f65967685d7985e61037e7aecee64b63525a5d7cc6631d6a83d0effc5b45f91b55ce8101bb081e5e2d36a28e958519d990e5fbb03c0169730180c694c2f19de17e0e26bcb109f30f36d8e927faf4bb120ef738b46527386a6f215d7711a21ba2
private theorem part15 : 2 ^ prefix15 % Spec.Ffdh.modp3072Prime = residue15 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue15)
    (e := prefix14) (a := residue14) (b := 4180642331) (n := 32)
    part14 (by decide +kernel) (by decide +kernel)
  rw [show prefix14 * 2 ^ (32 : Nat) + 4180642331 = prefix15 from by decide +kernel] at result
  exact result

private def prefix16 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (19 : Nat) * 2 ^ (96 : Nat))
private def residue16 : Nat := 0x6bad5a42b08d9c566a4a40d63c5a7b5b3dfe4f85980aca954ddd8fc7e2f87d33e868ddde945560552aab2f2e765bb7a2dc3b348bf09b6d07b76a7b7564bf443eeff3e64abb570896d84a6f47919577295b2858ed402cde578b1f4d0f3de5ca69b7b1211a8793851c210848849b6554f6cdf7f63029044e73ad4fcebb6572e9d9b0f68902b8c384e75f80620923bcd1ae947619a15b61ca935a935721472a958028de333a26fac93266288ad6c54513636f075f58ae5068b1487f45dc234119b0f3e25e2e970a9ca1692b1b830112a83fb57aece5f727a2de1b0515d83053f1305f841ff3b6109d57de16918b8862d1106bd873841c82b92d61cdc65b2c8716ca5931a90a1f2a8b6bf80ba0cff9c28812618649989ea4d3867138ae53b8a7382d9df392f204e76f737f5ff2e732e66604bc23facb2ec8341b93968bf7bd84bfdb407b3b2716e9237659ddc753db2823fb3809e0d22d9b392a0892241a5a196c470acd77c436d113632a5ed988a907bb0497c1f1119a081a8499510558874e4ff
private theorem part16 : 2 ^ prefix16 % Spec.Ffdh.modp3072Prime = residue16 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue16)
    (e := prefix15) (a := residue15) (b := 2817563318) (n := 32)
    part15 (by decide +kernel) (by decide +kernel)
  rw [show prefix15 * 2 ^ (32 : Nat) + 2817563318 = prefix16 from by decide +kernel] at result
  exact result

private def prefix17 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (19 : Nat) * 2 ^ (64 : Nat))
private def residue17 : Nat := 0xf3f9b1b1e4f62626d92c8f496d58c6fc1246a26567f373e851614db09933501ba03866586c572bed8fa96d9eab5ec374092411aa173c1a097ffe8b390bfaba999052fa7b6d3214cb4672894fb77cc67013aac8e8775352a96863910509bbf83d0d19441446f1a639846639f9f0c456016fa222be91fa787d4a48cd343dd0b61de68a2b6cd9421dae027f4e57400879fc917b3f0eb95ea0834ff6db9552f2b949b83b339078de0b9b383f160beae3092bca8217fa7e9784d38ec56b53ed33a72b7e46030142eb66fc368aef92c2bd42253ccfeed97d3cb35a07052e05abe8ba881bafea04e0124407f23f0e73ae857da96f200d3589031a00ee1e7a18a53b30cdc57b0482c760b212a292d069f12a8a144aa6d37c51b0855d091f11879e0c7dab5650677a31ee05e2c7aec5712ddfae382c51aff6034c7844fe25767e201730e6d007fcf7a953563262c6eb43259e8e4df81bc39d0c8588a011f7cd4513b744cab8318a626126496172aa97113b55847c0136f9802c040f173c54a212e0d5ac9
private theorem part17 : 2 ^ prefix17 % Spec.Ffdh.modp3072Prime = residue17 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue17)
    (e := prefix16) (a := residue16) (b := 3064520994) (n := 32)
    part16 (by decide +kernel) (by decide +kernel)
  rw [show prefix16 * 2 ^ (32 : Nat) + 3064520994 = prefix17 from by decide +kernel] at result
  exact result

private def prefix18 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (19 : Nat) * 2 ^ (32 : Nat))
private def residue18 : Nat := 0x48636fd5b7a38532a85b933ab856433e3fbc24b871fc9858bd5ddac3a63d3c60ec1c0ec869065a65f48ec9c54739bcadbed6c8e3342afbb2d0bd1aa658740a230324221669c2fb9b2bd8edfa8ad50b61f52b8036a3974107cc7a04fce2255f717b1d00fc8821e66ee47f1e35f64a2ba6e5952155a1ac0490a1d1dead5e174ed868154c9e3728351937aecbc295642e7e0ea07a33497069ce60834f3da9fe3d40a70bc5cc4405b3a57175008e7de845911f78b576fefcfbe747e007d5f943bb3ad9fd9b35915118fab4c0d47a072921e516de6c9893b7bb0c19f858e8e525ffaf88200e68b5cbf3e41678183f9c0eea817b2f2fb982ed26e9fc8d93265dabb2716357043fea67da90257c8ab0ddaf4b99ab98d6853e5e939af8e9036757e40517f81eb5136999edb7cf5a3d3b32deecb39c1d06f978c663cbed89d0ce2111880c9f305c2e0c53dfc711b192da7fa43179fdaaa812daa6e254eb322214a681374a9f98522c54ae2227cb1ee5d3d9fafc09a4e314d1076675540d13f12a1d43fa58
private theorem part18 : 2 ^ prefix18 % Spec.Ffdh.modp3072Prime = residue18 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue18)
    (e := prefix17) (a := residue17) (b := 4064467643) (n := 32)
    part17 (by decide +kernel) (by decide +kernel)
  rw [show prefix17 * 2 ^ (32 : Nat) + 4064467643 = prefix18 from by decide +kernel] at result
  exact result

private def prefix19 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (19 : Nat) * 2 ^ (0 : Nat))
private def residue19 : Nat := 0x5d4a60e45ca9e399a1254a77dd88b5d73712f014eaca791135cce4cc1a6c0783832d6063b919f46f6c668ba996a0b8d4de9ffe9440a3117b2eb4c7d4f33b86bce6342cf6005684fd1017ecc9b7de3676b8ec4fbfcf18eafaa784b263a21911ddd4fa573e92cff8009431ada41d693beea0cd6d2a68a02dc086ae26765ffc3d709c026e61d5d22583baaa8063ab545fb6ca021f511417c9b7919a9b9362f7b7edd1039abfe3a6e6dc713030db6dc7afc01bc46b52ffed348ae7585b399587dfa8d972212e59cff0d71a8c42edd82acbeab8b92a2eee1e902982225b9a862952e882338f4cfa87470e6a93ac14df2f2167870e251eaeefdb708b7271eb305c729ca9e07cfb615d54a23b49b67ee9adddf8fb5a60285624d1089fb3697cc2fb5027457d155a1b07d9ecb038720665fd99c23b229ef14f28c68cc2b6ca08ed20721428be32677c452c957744050e5c4cdb0ae5f4a18edd95ada7b8efa5c58b915c82a03a1e4940601b874fd0f463e4fb10cae69c47bc06e0f2a6b64903bd9eb877f8
private theorem part19 : 2 ^ prefix19 % Spec.Ffdh.modp3072Prime = residue19 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue19)
    (e := prefix18) (a := residue18) (b := 825180003) (n := 32)
    part18 (by decide +kernel) (by decide +kernel)
  rw [show prefix18 * 2 ^ (32 : Nat) + 825180003 = prefix19 from by decide +kernel] at result
  exact result

private def prefix20 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (18 : Nat) * 2 ^ (96 : Nat))
private def residue20 : Nat := 0x1c3eb440cb2e3f609fa0525443868efe78e299f8fc9167ce0c4549d801793ec486cdf37fabcb599985f96a5b249b493f3504b913638c842100ca8ae04891249f71ac8688dd6b28eb49aaf8d577915a2c02a71d0c5af56c45ca0aceef73ab8c73e86b52285d259d75efcfd2e65dd7b227be6dc34077f6ae5b28ca784880f80825efe717d9bf1ba2e87f9a4b372eb55deb4d824a421e4bc86c2448ae19c279cb451618da5dd363eebdc9405dd87971afa764929905c1576b36c9492076fdbaf8d920a98fe7d89012b0c4d625fdd9eef0c0156cf2a9969bb431e84574b6f77da69b456e85e69cf371b00993271793f8c48c04ff9475cdfeb460a4de8e0f9d3b4aeb2b9e459b0bc92c8818eff4d156b52044699611a2b5ef581f7829b1eca3cc5d1574827c0b6de6f1a94c5a048422f95e5f3b4ba14271d4055e24fef39ec7e909fbcf62ff3574943d40b29ea15c4c54d4a5c57fb0fc6f6b7e48ec02557b558838a57838efb3c86cfdf69116a5221d0a4134625223c231f6ff1fd7348a82f50a2351
private theorem part20 : 2 ^ prefix20 % Spec.Ffdh.modp3072Prime = residue20 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue20)
    (e := prefix19) (a := residue19) (b := 2049319284) (n := 32)
    part19 (by decide +kernel) (by decide +kernel)
  rw [show prefix19 * 2 ^ (32 : Nat) + 2049319284 = prefix20 from by decide +kernel] at result
  exact result

private def prefix21 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (18 : Nat) * 2 ^ (64 : Nat))
private def residue21 : Nat := 0x6da4933f92afc3599a804feceba62a775e39fd261b4c735416c463ad8ef7baaf5cacd36a9b428291adac678629b590983f5e1c9ed69b346930d3fdbeb86b5c1a70625c67541f14d581723147f721edd3517eaf76f9cfc29b5f001d32a8b0c8418094b87009f4da5cc331ce9eb42227f602789b204dba752b9cab1fc68c7e35fc1734f390d3677feb542ee73012d584106defd4f8be2528ae99feb5774c9ed3c068839931a75f40c3c2a8ada6cae46a1d0b9d3da3cd2e01081f93ee57e7d205fc05c2b2b4062b7040c05d64badeb80ff417227bcab219c1713fc21f2e8cd6886fc8ec9d6df639d6b8981798fc4d618b44d319fd26770545ccde01076db4facd47d964cf3fd8ff79947e7f3d126ade65685ac9111a3c00164ceffe2ff99a52e871a3e2065fcdfee41a5ab5e04a8030ae28db6b672671fa74cfabbec685f41285b3e76ce5b65b9c22e7ba5887f65518179cf71c50b5ad7f32e363e380e2f84ef9f2ade678ad8eb5d7d4fa1c5456f285be5513f5363090234f8dbf1693f1d8d025d8
private theorem part21 : 2 ^ prefix21 % Spec.Ffdh.modp3072Prime = residue21 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue21)
    (e := prefix20) (a := residue20) (b := 3541825205) (n := 32)
    part20 (by decide +kernel) (by decide +kernel)
  rw [show prefix20 * 2 ^ (32 : Nat) + 3541825205 = prefix21 from by decide +kernel] at result
  exact result

private def prefix22 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (18 : Nat) * 2 ^ (32 : Nat))
private def residue22 : Nat := 0xe35a8df46bc5f0bd339e8cdb5924a8e8fed937c7e9478bb186642958c3b658d4755d62dcf78149f3062386df1b5c548f810527c60ca6b5045ff07299b45d4bccaee2fa8170864966f15bde999f60cd5e5126de79510d5151a3602eff0243db5c350c8eb018aa425ac0b44ddf0c9a4737f32c1289b50edd1517fd85aeefb2edc3c42f9a96fad7b3350096c2f97c8b9cfaf8184f50f5ad155c6127069801507a1f8fcba477790183ea655a889ed3b991c345f18c2ed8a357b6dc4963b5d46628d1d4233b89c1944377eaa60c311c83b65db1af132294a698753abd5a71ae3b7484da455d4b583b4991afbc8ac07d4f7f5ed1c204f4741799685f3cd5fca07a6562486b263256ab3a4d171eef125191740f83e5b73fa40331d7a9803abca47abcbe2f429c523273083fc10347807759b0aee681cb279bbff5be88bdb35e8af7e574f41c557ca913d7a33a62a82bd83b27e368dc4480a3625ff05fe7880197880825b5744f5d81f3d2bb35aa4c5a883b9cece2cce32e95a4363bd6948e4228e41ce2
private theorem part22 : 2 ^ prefix22 % Spec.Ffdh.modp3072Prime = residue22 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue22)
    (e := prefix21) (a := residue21) (b := 2248126043) (n := 32)
    part21 (by decide +kernel) (by decide +kernel)
  rw [show prefix21 * 2 ^ (32 : Nat) + 2248126043 = prefix22 from by decide +kernel] at result
  exact result

private def prefix23 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (18 : Nat) * 2 ^ (0 : Nat))
private def residue23 : Nat := 0x9a149de80eff555ef87c3befe5f42662ff62cbd995effea8ac786f8246fd666137d3f5bbc84d000fb8c21dc71e7a6613d7803ac973d24675a7bfc5f7fbad3dd9f1adbeae209fb44435b4a1dd1d5e4d5c5f2496673354f5d3cf31b03fcbffae5a4888a6520e8aa97fefa4c74a64bfc6892a5360644046b6bac9a335ec993945694428426960dd3daf3e568ec36dd64a57a0c9a05b96c4440bc413d144dd77cb663145de9f472f9c803f177d369ec1909fe983584978741dc64aadfc34f0b9938f7ae3987e7ffa7208c9f9eda5f15bc4cd252cd98b767274377aba8dc1c7d2dd8b7a2406fda676e2937a4438f93192fded0bad59cf7265b2232f2137310d54f51dc735a4e79b808a365081a0a14bf82f3710aeded094686d4be63622eb5efb2ed2ce8163c7cafad516c6fadcaf12f27945ef2a8ef0e5f68c8e1486228ef126d769915717c60f9102a46c13760e3741386e44a9b66daf424992c6b626b163806bd4cd07be7056c004ba7be21dfee65599af5773fddd14aa6c86792b8074afbcd559
private theorem part23 : 2 ^ prefix23 % Spec.Ffdh.modp3072Prime = residue23 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue23)
    (e := prefix22) (a := residue22) (b := 2047040502) (n := 32)
    part22 (by decide +kernel) (by decide +kernel)
  rw [show prefix22 * 2 ^ (32 : Nat) + 2047040502 = prefix23 from by decide +kernel] at result
  exact result

private def prefix24 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (17 : Nat) * 2 ^ (96 : Nat))
private def residue24 : Nat := 0xe436e4182b09f6aa4d9f55787dc707f8f0cdfca29dafadf25774db438a7a9fd8eead405e9734182da8c01acf0202ec78b9b8ce56fdbdd1a04fa04d3d96e987029c78b4492a4fc78c7c43d124a3cd77f7d7e1cb72acfed2d88c15cf59fb9ad31fbb9fa7bfcc776d0517ceda22ea8cec3712b433f0cf1b3d5ec09617c4688b6f7f9ab8c99d4d1b673d8a68a28b9fd9fb88aad8b82666d17c2833607f7109eed6ed9641d3daf7c9a643fb17ba481c18179bd5dd41a7024cc4056402d8b1147f1b78e15434fbf31d814a19d31f6ea259c048b168274c766768746d63871ed274e618c4bd1391a48541e18bf4045c13577a0deffd46c80417570e6e556d4a9f780e6e81d7b7eb40d7d7e172ae5ee992bad1bc08b07ddf87e27d46143d50226ebf181fe392048f829eb17d96c8a87013dd7f51b1c78c6a590e3bb73aee1d9551245302ab9baebea26d105340262b874c960dee735ac4f0e88a47bfcb97a645e06a38857d21aa956ad8ee75bc232dcffe33744ad118b7a394d50b7de64573b4d53eaa8d
private theorem part24 : 2 ^ prefix24 % Spec.Ffdh.modp3072Prime = residue24 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue24)
    (e := prefix23) (a := residue23) (b := 4145821181) (n := 32)
    part23 (by decide +kernel) (by decide +kernel)
  rw [show prefix23 * 2 ^ (32 : Nat) + 4145821181 = prefix24 from by decide +kernel] at result
  exact result

private def prefix25 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (17 : Nat) * 2 ^ (64 : Nat))
private def residue25 : Nat := 0xb3074c1821ba13ae6026135c933e4d1e77e617ac1592f1347cdaadbb88b590e8f72472a962865a7c1abe420613d12a12dbaecea756d86415ba2b12f1885803bf4c53415f2cd7e0737226782259124dc928c6b338e795118f60964c8554285a79dc1c6455efd5032cea148812abc27e347d516e31a10dadfe72ea50634b5bd9609425c78e282a95d7e9eee4d76d95e78fb9a921853e1f953798e024f7b56e250818c41c72f17630d4ff2c81a1efc6bf9e6ce64302012f208683bbaaf3949383db3b648036b3dbb0fa7719336fde1a4102aed6bd7ab4bfa6581c36cbb56959b8e89aad9ff0faed720bab47fdb6c2c03a29cda629914f3a9feaa46cb06c3d685f140f67df1401d80414f251779f80e0f78538acc1dd142113ed3d60bc580dbc73fc775abbe2bdab26db7cd382e5a7ec27b71820484d35de4ca84cc6554caec022bb64e5f165e4f19568b59798bdb8cdaa50e2722a4fe17adb4747df045af3c62ec0ff6510df84a556ab031c88da55ae314f01cd2e0f0ee681614fe62635bf1b5236
private theorem part25 : 2 ^ prefix25 % Spec.Ffdh.modp3072Prime = residue25 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue25)
    (e := prefix24) (a := residue24) (b := 2906968018) (n := 32)
    part24 (by decide +kernel) (by decide +kernel)
  rw [show prefix24 * 2 ^ (32 : Nat) + 2906968018 = prefix25 from by decide +kernel] at result
  exact result

private def prefix26 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (17 : Nat) * 2 ^ (32 : Nat))
private def residue26 : Nat := 0xc72861b723bfd9e3978684d38b36fd8a506d4f75dab84c86ee621aabac90435b6b087ccb269a8a9496c08e7c176b629ad77a20600e6fe9ad3ac5248cd233dafd9dca8c17e6e2224cf3b9e06f85b05d7abbcb66044a04ee68508d0a9e93f569daf0ffed3c303e407a400d3f4a513c189ae81fc3720bcfa164f3337857594f2d59329629bcf41a3b2058120e373441046b588e80ce4a9a1f31eb8b10fc86185f5bac4c8948891bba0475dab7f50232129e55f593ba07f1ba98ae31b3267d8398e615dfe57f5d179332eadd3dca9019ca37486a9e2ce1ffc49c8ed85af22c99b0b843e8357e639f27985440440999fd4071601bae654cc84e1d9f1a33a5adcc6a881c9bfade02ecf82baa525ba6f31d3dedabd25184d7808c8ca435157c46037a9019f86de34edfef6d9b3993329ad38582761e320433c0b55dbd4075be909fb7c62c55ad36335a0856e322b10455da88c22fc80baa029b1b1e999686280ca90c810b90b75efcd24b0735583ecc0f6ad3f5e6e2adf365685413c77c15ea428ac261
private theorem part26 : 2 ^ prefix26 % Spec.Ffdh.modp3072Prime = residue26 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue26)
    (e := prefix25) (a := residue25) (b := 3612316168) (n := 32)
    part25 (by decide +kernel) (by decide +kernel)
  rw [show prefix25 * 2 ^ (32 : Nat) + 3612316168 = prefix26 from by decide +kernel] at result
  exact result

private def prefix27 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (17 : Nat) * 2 ^ (0 : Nat))
private def residue27 : Nat := 0xfd6c3c6a096df65fc4d979e8951895a404998479647be3d3136ab265e0be62fa169bdd873839106c80b76103d31de616955e1aa4dee0f6c76c9461f534674a0180f60dd85987de1864ad1c760f241eefb406381eb660a0b584102e1290b2be3eb49c2917692d47d88c9e5a1860ac0aacb90472ba2070fc40d4a36361df9fbbd53d5bef1592df0630ad7359ee4cb2304548ae55cc2f2b547abba4d9af839d9c0c6f5e33291c2e5351776fca328a3995a50f07fb3cab82c211a3229daec529580756695dd0ea9e1fe817672aff4f7f8985b6ffa6d61067c5f87b8612fe721dd48e10ddd8d89c4fceaa7c6f325ad6828bbcee00127672956fcdffb436d36ec576f3b60fc732fe5ad870185d2fe6c1133a5da9d2a62a0461888738218a60de0f9e5acd261c4ebf30bdf572abd30c1637a130ff891fa8a0d27af5acede1477069d5a2aee7529ddc7112b140bd2b63aa811937cba57b24eae5cd31b5012a881be2085031183634828e6e6325cc76f8e8c471fde174d32197f9d207c98faed5fce03937
private theorem part27 : 2 ^ prefix27 % Spec.Ffdh.modp3072Prime = residue27 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue27)
    (e := prefix26) (a := residue26) (b := 3190132723) (n := 32)
    part26 (by decide +kernel) (by decide +kernel)
  rw [show prefix26 * 2 ^ (32 : Nat) + 3190132723 = prefix27 from by decide +kernel] at result
  exact result

private def prefix28 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (16 : Nat) * 2 ^ (96 : Nat))
private def residue28 : Nat := 0x90f3293a4adaffc236c2356c56f04f0850b7d9bfd8b1667147130c9be1f65f53fc7ab071441f74a11db6c81f1c631135da6f15900df25aef7af5b17b24346bc01fb658d0f6f172a075b11e211c33404cef30b4ed6c6fa536b5fed48ae0f32a892b5aa59f1e57c24aea13c64583f22880f34ba466f22df246aed2269a1d4c7b61c3e55fbb277a72b4e1434e1066207aea3d2ae3eccafa40e553fb1f46feac2c6a1ca63be11c84f4b5d8b24086b8e9a8e8058b9f2aaf1ad498005f7ceae0488ee68034eaf1ead2502e5860f13b738bba7ab380c442531ca99e0419a719ff7add611f706574f0253abb41f8e077b4c058bae7a96449ff107b6fd9d15b0188371971ed9353609fb8acc624da80b73c4fbe458b011520fafc368822ec1edadba005b9fdc524b86f428b72b3d5934fef25bd03f2b254c0c54066acae982e91d4da00ff38880a62475d284e6bc59b5c4fdf2879c435dec74e3c7e83b6508ec1d1f7b61f62a6ff25b1503753bea859fb9ae746c186bbf08c2d99ba4314cf1d76296c3a1d
private theorem part28 : 2 ^ prefix28 % Spec.Ffdh.modp3072Prime = residue28 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue28)
    (e := prefix27) (a := residue27) (b := 613692200) (n := 32)
    part27 (by decide +kernel) (by decide +kernel)
  rw [show prefix27 * 2 ^ (32 : Nat) + 613692200 = prefix28 from by decide +kernel] at result
  exact result

private def prefix29 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (16 : Nat) * 2 ^ (64 : Nat))
private def residue29 : Nat := 0x3d79e0450dd12105a7982b5888b0e76a766cbb86cc506be6175e6e1f9b9c6e540de90258cbca897cc2fbde730009e1afe5db6341ef47922952d908c790256eae7151f171c11d4b4b4829e9168f2e2ae80c499a309bb0cf4ffcca616004e4bb01d4f2982a1adec804297f92044d58ae0d8c036e19ab8929d08a563806fa5390278749b004173e0f47fea858f103ef796da88af826e8942791ef6169967a46b2c459f0633cb848cd45643df37940ff98a389bb51a8b3d58ebf8cd7b346f5fae426223eea775280c9ccef98b94911debfc92bd2e710cd3374a62449a258f85e6f96497d4fec7657e97b036d91bb92d976bafe2f4fd521cfd8d6b30d37c938b4a62b48d856382fad4d43c9fb31eb534dc4881cb1beb2e1982384419be2972a33da600a948234f2f4410b6efbd8138f5f6e7543100781183daba396a2fd72004f4629cdea6fbc7f090c3c240156fa480f17ab3f0a2477b4903484cfadc247d6e8fa5f22fe102fd63cb359496c017274c64ee872d709eecc38623358810f7340580465
private theorem part29 : 2 ^ prefix29 % Spec.Ffdh.modp3072Prime = residue29 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue29)
    (e := prefix28) (a := residue28) (b := 4134677918) (n := 32)
    part28 (by decide +kernel) (by decide +kernel)
  rw [show prefix28 * 2 ^ (32 : Nat) + 4134677918 = prefix29 from by decide +kernel] at result
  exact result

private def prefix30 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (16 : Nat) * 2 ^ (32 : Nat))
private def residue30 : Nat := 0xbeb2cb448e85120a63c064607aca880a8d3b08531afe04e8875956165054b4064c1339a1b3f901a4e1441405d9800b6ef4ce80ebdf1c693c0b0d0fa3204a1a5300bc0d85c492f83751ed7f7699c84dabca7468cdbab9dab592994871b97ea6cde65af7ab4abc1d6e190423c840df854978eeebf45c479dc91dfb085cec6f33c9950c4c86ea8ada21647cdbc55aef6d518d69dc3180f2d71894acef9261fdf351d751cf2bcc983d32dd7517d24e938b938a30400be132502612c7b99b75f7fe34eb65fd35f2d1241e36530400a499b34eeb3b4fd049e2c17735772c2c1221141a32427eaa3a3575091ab93049ff577624b96d5b0ec9e01c492e8aa6b4dbcbc07f91696ee4230a1b5f2cad0eb76bfdd153a33e73d9e5e5b1c468400bc54e2fb6229c4317b8deb7b6ffb334586cca5e9528b37bc58ea9b10a0c7fe55a2cca4df544f992bdc4f901ac382c2449c235c8479a81968b20162f3535767a64cacb57b19c3b5f287515030cf7adb4215bab23462ff9eb8260d6d7d60f10dc1e3642efffe9
private theorem part30 : 2 ^ prefix30 % Spec.Ffdh.modp3072Prime = residue30 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue30)
    (e := prefix29) (a := residue29) (b := 3774889564) (n := 32)
    part29 (by decide +kernel) (by decide +kernel)
  rw [show prefix29 * 2 ^ (32 : Nat) + 3774889564 = prefix30 from by decide +kernel] at result
  exact result

private def prefix31 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (16 : Nat) * 2 ^ (0 : Nat))
private def residue31 : Nat := 0xbe8b2ae62de3eddd3e62e85e54817ea8b2cc9e92bf995a567406cb0cd1c3ca7f824a57a30499d58f1f542e3fbccb30f49fdc3725d8201f2494c9e714137345a014aa9fd84cabf1f475026d8de4aa54528c0115341a4670b866d2993077b47fcb5ba06876a854b21e8f04bd33717d5e1e1ec4a7585330d81ff64635291d303f75b966e477d428c11a410ab25ea6dfc9c7d17c667e7a2d42467e7373b4bfecc5091bbed959ae7d984c58d0d1a175d8e0600a5e75d648541dd4a511783b5198b6dd83757a9660a3b5ed15486a0bd9be32ee5079f15b86a9cb75048c15c9c169fe5438b63f7cfbd8afd74549c64b36edb68756ac167afe4c097491e1982899f48d3365590692398d26a4c90445ed8a166e4a1c829d05d8cb6f2bc1907ac48701d9eb8ebbe8a137aa276a25f9545e84cb71e9280804cc545ab12132a34aefc2283a0b9261259772bbc055fcbe91d8ad658f466dd7cbac8d3f932911dc0ac0c1014cb0ea0a02214e13c8a7bab9cf81e5bb6912457ef2fa5f9b825006357ec25349ccae
private theorem part31 : 2 ^ prefix31 % Spec.Ffdh.modp3072Prime = residue31 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue31)
    (e := prefix30) (a := residue30) (b := 1353834370) (n := 32)
    part30 (by decide +kernel) (by decide +kernel)
  rw [show prefix30 * 2 ^ (32 : Nat) + 1353834370 = prefix31 from by decide +kernel] at result
  exact result

private def prefix32 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (96 : Nat))
private def residue32 : Nat := 0xa9e34f3bc169e234c24159ad14612255e527d54614f8cd791e33b6cb91972746f99345395f72120b33eb918b2f1ef83d6491476bf420af3777ca3ca1c1c1769cc726dcbdaad0485e7415f9edd774ab5081dc6d982344d601ce4b0229926f65d863903f21b2f627b49a3b3771108d1a084a89527d317f07ad7c8ca7111e290c591cdd2861a4cad7afe26d49c1bca95c5ee830c60c1b3ee017d2846ac29cd2b385012d87b12b2530b24aa53d4e46480bd7e8d80bc72a0dd09bc646b94acb0d2d1ca070cf16f91d5821aa0b68685a525bf6eeab2895f047f0655022fd12fb01be81d43d1b7bb6d4fd7bf8f5964d2e8d0550a81e03e0dc721b1ffbcca852e9dd84e990acbdbc41b4303666d83daa2482e895b5474dfdbea348428f77febf55948db9224af112401f9d80817df4cba3fa18dfed4599a6143c9a16a40d42c19585420c5668e4b50fdcdedb5ca4d6671cf2e5b156b2746956ef949274b500f27e719d1546cc3ceb8e1fbe6a4bf70f213c8bcd2025dfa0d898ad6dc6c2fa92426c87685e
private theorem part32 : 2 ^ prefix32 % Spec.Ffdh.modp3072Prime = residue32 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue32)
    (e := prefix31) (a := residue31) (b := 3429704731) (n := 32)
    part31 (by decide +kernel) (by decide +kernel)
  rw [show prefix31 * 2 ^ (32 : Nat) + 3429704731 = prefix32 from by decide +kernel] at result
  exact result

private def prefix33 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (64 : Nat))
private def residue33 : Nat := 0xec08937b882a2a0c502e087429c34e137cf07a72d223bbc5135ec6efc450d0f22dba4a6835eda89ec51585a1c0950ebe9427a855640529c4f11bb4520a12ac1d7dc522135b56344879fe578e430414666dbd157586ee6dc4f1ff115497f55ef58aa9fddcac0fe16360d6fd56f8dcafb9a4b2b2422970f4e23d48510927ddbfeb909852d386eb0702a76e4a03589b62c7b9d8199285efb283936265284115b3f6b670cc637db36d21ec85b82af04fe4f4759545d0e0af572da7d7d850bb1f7d2798dae50bc8c8c5ca17c9174a3a2cfa621b1a6ab96642625ab371860c6a5e8f78b044f4d7a97ed62b16b1da4697d943fc7cb3c276cf34deac721524975f4ad0ca93102490f2fe937ccd15398589a387fe5c325d20350874535eedf544bbb13d706475d67a8f152b83d27dd81273568768bce7a4e26165c875083b22473132653fd3751ea4a8617daf1de5cff1e091f4b1df6e437c5aae6bc2b2f42c8c0aa4799adec76f0a02460319e3fbdb82b976f25cf39995804c1f28be696f2c39f24b159
private theorem part33 : 2 ^ prefix33 % Spec.Ffdh.modp3072Prime = residue33 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue33)
    (e := prefix32) (a := residue32) (b := 237693389) (n := 32)
    part32 (by decide +kernel) (by decide +kernel)
  rw [show prefix32 * 2 ^ (32 : Nat) + 237693389 = prefix33 from by decide +kernel] at result
  exact result

private def prefix34 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (32 : Nat))
private def residue34 : Nat := 0x4e478f719ec0ae52f2e1fed67e939db05aab70604b66c2d87076e5839648584649a0ca30dba08da84c5d8743565befca2f7ec9f0619483aa903a5c906b4769474910675aa19d94777810306eef9e2d2736b15e419036219e467599e1040c414710c0775650b101667bf9075aa65d88877cbe3111a121649a02d593510673ebb38cca4f1a82f5f699de0044e18b7f103a051e06b83e44f7d17f68a34052cb5fe01c47b33bcbd084ca6cde27b9bea16cb42df5ab4771ed36c77c47e2c750a713cb080c875cae31fcc7e7ae126df57190f69aefc1b0ce436ec683cfa1f7d1c0ebac86f7ae8efb87a606b88f91d606c128360209db4bc2134272e30f7b0ddd6b5bc89f4e3b07a8b441f576f4063ab4cbbf38d37b5d8f5937214847b03bc8f2f2897c8c443e53f89dc72b5b1a40946c7da4309230e8b59a259f3b43a276cf83876d1838b9cf90c344d63fed7ede6888c427b4f826e900b0d862c916125f75a6e8578e02ba4922ce17936663c3fdf40a128f04fb6f3c5d903374db45575cf49b667102
private theorem part34 : 2 ^ prefix34 % Spec.Ffdh.modp3072Prime = residue34 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue34)
    (e := prefix33) (a := residue33) (b := 881532884) (n := 32)
    part33 (by decide +kernel) (by decide +kernel)
  rw [show prefix33 * 2 ^ (32 : Nat) + 881532884 = prefix34 from by decide +kernel] at result
  exact result

private def prefix35 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (0 : Nat))
private def residue35 : Nat := 0xab2f649e9c56f2bb85bb306ded2648b3a9a4e71664e4a731dfe4e50129514e91a5915b3c271478a8707230f756bf377d7a7e016bd0e2fe5108bf1bf0b86bbfdc61378f7ba151d96da9167352ab973c7765a9275826b4d1887851e5514f5163275de7958c84e115287df18fbf1f03431340faafdb6db7fb08b6032c22bc7cd74191036a159b47522eff82c3f71b2c5d5a3371b5bcccf694ced6c82d97b30d64292d9ed07ff236167cb498d0b6809abf6fd5ae2c37237213ca1b8cdbac11d3050e63b9a3712ebd74b2c4412528b932c17f135a776236eef7c8ad8ab4d82355dbfebaedb8a36e1206cc491d134ec86b1c2ce845bad1560023ed24dab1e56ea9254b29b941cd9aec8374b1f5ad392b9195710cd88d600a70da41eb06df4e6f6c6146a84bd04fed0e5336177ada366b8f48838c3e623bb83dfe75aef4a36e92923d0b50603050209534aabb1af0e9c313b78a403c559b8c3b932f76252e4d09088ed35006e87a5a423e289f51309dcb08db332c5256c97de4c7d421ffeb55fb723d41
private theorem part35 : 2 ^ prefix35 % Spec.Ffdh.modp3072Prime = residue35 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue35)
    (e := prefix34) (a := residue34) (b := 2123524015) (n := 32)
    part34 (by decide +kernel) (by decide +kernel)
  rw [show prefix34 * 2 ^ (32 : Nat) + 2123524015 = prefix35 from by decide +kernel] at result
  exact result

private def prefix36 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (96 : Nat))
private def residue36 : Nat := 0x3a02ad30ea0ed13fd55833f1dac31ff2022276114a75512c9f85b16799d988ce25b9b026bce2e6c3382cd13416c8a944af2c88deedb08e4d78ca3afcdec090a70256e49865ebbdd642e12085f9bc7b2d7c34717d33cb2700a8856774c183fc90b5850d4d54d666e38142b7b9d8432ea0300ea9498cfdacb1ad81967100e6d0314a92d8a8c44f83705d247a84d4b914ffa57971983b14424081b80e410f47e80735289429879d69878f4eb986afc4ced4b0de52809fa949ec4430254b5614850a76d81f3d430d42b07b75db8f83e8d7296a989af0cbcfcbe163783f865dcc7c7bec6889347e4250a94802babbd79bce6e42dbb8ddbbfc67b820689e44d613c30ac4647ffee630a0d05192ea9650bb0ec03da3b7decc72e611e5eabd941cafc5ceae8abb04b1e92894b44087d43600e4c69ee5ffe600c30e213dbdfd76a34fe4a81d0a61f4a3eccee58708b745fafad2356cdeb49a80075e64e10cc6f6b7d5dbb843f059750c86903625cad84375dce2e9bbc8f8f1afa277c02512236ab4eb4847
private theorem part36 : 2 ^ prefix36 % Spec.Ffdh.modp3072Prime = residue36 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue36)
    (e := prefix35) (a := residue35) (b := 3249712785) (n := 32)
    part35 (by decide +kernel) (by decide +kernel)
  rw [show prefix35 * 2 ^ (32 : Nat) + 3249712785 = prefix36 from by decide +kernel] at result
  exact result

private def prefix37 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (64 : Nat))
private def residue37 : Nat := 0x63f9b28fac51371206fdc09b669d85e16372c60ed947a48bf08dbf1616a6535c37daf3b9e0f0a2d7aa9fe4d17fb6cd597169fedad342222be624d531a375274dd556e45c45578888c56b0053e2923631ed24c0623e98b36a39c15ab31230b082e8e189991f365721cf8d937763f5c7d79fda2a952ad2faa79a860bf026fd9349da4986e6a2530f4bf51f3d5adb7b41ff366c48718db8f97ab375f5d6b16b4e807affeac64e877f1dd5356bb6e4b509d530e65e4792ef3f98c3cfb2909602964e329f5365c37538fd6bed7c09e928560a90c14c875f31a2bccc7f6c69ac19cffcf822560e1d624d845c5655c4ac06bffcb3536a2370686eb7e148400f3b56b53a3a43a59b47817cfb4c8942ad74548d7174b8615e7a596e99b8c15f74e560b00bd16f33cbf26ae1eef44347387d566c8e18a6434af4f146198ddf0d09bbf9cd293e209d2fb4f596dda74d1705fba7cdcab3b58f1a5920a06dfd3ce43451ed7b604abc252cb6e0509aa709d366a598549dca2da2b0ff2f45f0ee16d3dfa224c7b7
private theorem part37 : 2 ^ prefix37 % Spec.Ffdh.modp3072Prime = residue37 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue37)
    (e := prefix36) (a := residue36) (b := 3998340811) (n := 32)
    part36 (by decide +kernel) (by decide +kernel)
  rw [show prefix36 * 2 ^ (32 : Nat) + 3998340811 = prefix37 from by decide +kernel] at result
  exact result

private def prefix38 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (32 : Nat))
private def residue38 : Nat := 0xbab309dab98d4029842ee626ac7ef5159b37802554e6c362cf0b596557c40c4f1692d7e6543eea105644089d5a35002d4caa9219137fdfe1390ed9dddd376d07c7ffdb9bdfa529cce471ad76ee16e0f19352be955d6603003e40a965f148ad85daa46affbfa1453932c02baeb32e59f22cb3fb498ebdc142f264fe54f44ff3f137b6dbfd329137525357b4b8477503da5a94690a3a48b2a5c2caf8de248fbe3e63aec824b8995b9aee10626c57d37e0b11fa4625151de2861cacc0ac03fe41875f6f8e1c8483f86a0bc2f8b94e99ef8adab51882a0c086440ce67ee35c38454fa53ffaa58cf4ce317bf56b26dbc21ff13d307e9047b17964d6a682e30255622439e009db7fce58c4b83c9f41ae3373baaaaa78afe702706feba2295fa5f4a93fdd5035aff88d19275055ed0ecc99417cbfeefab3827ef3bde3f52b9286c18c14c9cf8b59f8d1e33f7f5edc961a8c3ff9b76f37df8cb7062fe92bdd6bc5112e07a469de70b690d2cd8e36c59adf5fb1b5e720f79f7035cc909afdb6f386d40955
private theorem part38 : 2 ^ prefix38 % Spec.Ffdh.modp3072Prime = residue38 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue38)
    (e := prefix37) (a := residue37) (b := 238123435) (n := 32)
    part37 (by decide +kernel) (by decide +kernel)
  rw [show prefix37 * 2 ^ (32 : Nat) + 238123435 = prefix38 from by decide +kernel] at result
  exact result

private def prefix39 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (0 : Nat))
private def residue39 : Nat := 0x6f6d6ee8992518983e50ebc202c9224701f3c4fa10ac005e2c90dc765cd3d85ab822eef31622e3a6fffc2397a9f769106a55ac778283199f17a759c981bbb102f7057b4cabb811e693decc3fe7e395449731fdaa3c2cb8746075bfed2f31601f25a794e2e96c0dbc6fcea0b74a35c3ce5b3537238ef8c90b475fbe9f83299e7f80bc052c21042f559514f0efcc6040101c27e2b157bf1d2618114dff288484ab3cd4a1d2d4bfb59f7136acd82c9354c45cc615947d73c0c94d4050fec5a68203d3a559f1674859331ee11895b6606b42202cd0fa603efde5a497d0f6dd13025500cc9f5a0b686a5f8870dbab61939ede57a078994fdce55860aa455c4e4417317b58f6a0e240f631db7ce256c11a09bffe4d66d5d483b87f721ff50ce96e887503e261bef752c484cdb2785866c1acaf9a295458c0a55286094e3ef45663599060c91831023279addf49ba6260e5607be2d423e83273c8315059b4199ca6be9805a5741700d75dcfdb66ea151277fcd9c5432fb7b19a0f513f93d2b6809a0021
private theorem part39 : 2 ^ prefix39 % Spec.Ffdh.modp3072Prime = residue39 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue39)
    (e := prefix38) (a := residue38) (b := 272804189) (n := 32)
    part38 (by decide +kernel) (by decide +kernel)
  rw [show prefix38 * 2 ^ (32 : Nat) + 272804189 = prefix39 from by decide +kernel] at result
  exact result

private def prefix40 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (96 : Nat))
private def residue40 : Nat := 0x7cb77ec2e7e0789a3942f3bfdf6a546aef22e70fbacdbb9cc9ce43bb61c58a107a5ad8fe471ba854575c2a78d19bd9e5ea4c54359e7c4a0b2774638dbe1e5910fe3387e745f63a700f578fed577890a3a03270fb8804807c9de58a511cef86c8c549be5e87ba28aa83c10975bc016e71c5216d3d520156dcd83c66112040f79a9737a53bfc60b5e0140b9fa3ce9c269c4a37453ed5fd4873008b04060aa56123c65278a6f4e3df01d2a1a89b1d3c1e1fb8ab2b91ac7341d2e5591a0c94fb2195ca8b2bc8c7e5d8520f0b9abc61d1944cf1f3c02d6e6df68be3dd0082068bc927902a62d9c53ecbaaa23e1ccf8671065943f9d4324edda0a658bb56850ffcad64776c69ea8081ecd90fecc1295ed54e8a29d6b2c8637c97a16bb94463904895e6bdb32d0d0474357496a5d644784396a7228d46bc64db8d02c0f0c8b8ee4ca762c822b86adfde27ebd64c01e075c229f5bd7c514631076abe37b0656b99bd243bcbbf7f0407204f2721a6f73dc829c6450a46fab71bbe55d2bf291f936a8577e0
private theorem part40 : 2 ^ prefix40 % Spec.Ffdh.modp3072Prime = residue40 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue40)
    (e := prefix39) (a := residue39) (b := 3479868547) (n := 32)
    part39 (by decide +kernel) (by decide +kernel)
  rw [show prefix39 * 2 ^ (32 : Nat) + 3479868547 = prefix40 from by decide +kernel] at result
  exact result

private def prefix41 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (64 : Nat))
private def residue41 : Nat := 0xc6472186a46662a61a31c4117f053b64cbd8efa52200a58af4d8e7ea4cabcb730a12e42353bf90773ab8dd3d58ba6466d99ef567250f19537658e3c7f8acf40790818ae01e55ea6ddf67b1ace48756c90c9df8d035855067949cddb96f9f0037d24e1581a1dac71eb45a3563bd63f3a48d61369efd048b193dda030a77cf37f8593d8648a21b7f0ba10788f3d2952f35b5c8c41c2a961617a589cb15527acc1ee46f4cd05a53dd6ed1484ddb3bac46b0d640e75038838c6193d5455ce8fa5756eda9ca26265bc5a7149ef7b6d404e67a10d4660b4909dba7444570e7cf7b75f810dece4123c08d8c580a2c6e4f5a874a12e813b45596a980513c60205262075b5b88bc6b139cc47042800cd83b5359601e7e285ee46dfbd19d22d66740549593cf979f749dc50d2fee55a8e520e6ba76f9512e1297ca76567263ee8db12f445a0894b850e1157f39ecc0e4ce55cb67e3c54902a62f56938a5611a5d37f9461504b1a3443c192e572d852ffbbc4ba5ba1e653a772f9fb5046071464d7caa5499e
private theorem part41 : 2 ^ prefix41 % Spec.Ffdh.modp3072Prime = residue41 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue41)
    (e := prefix40) (a := residue40) (b := 3091942198) (n := 32)
    part40 (by decide +kernel) (by decide +kernel)
  rw [show prefix40 * 2 ^ (32 : Nat) + 3091942198 = prefix41 from by decide +kernel] at result
  exact result

private def prefix42 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (32 : Nat))
private def residue42 : Nat := 0xcca136b46f87db3816485b6060efb27568962cf0e3a371985864f38b4b85818debc61aaf7618b72d4e3ec0d99fda6fbec3729e7660ae5a48282b8d393247737928a98722fd1180b90f203213d9f084a8df8b976a8ab191b842bfc20df3e6832254e866f488f1a13c7ee1508dc61ef9e30d65868233edb737786d67768945224659cac112b88159952d3e82adbe99dda1f00f4d38094fa08677ccbcc5a69f4588c9e5a8aa9e6e54a277d16e0b12da40950786cfcffb3228491d8925878a6d2b004780b1386dbebd42593b9f90a68882106d82af5b3923295fcb828c17f21157330ceba0aaa96a11a6dfbd8faa2cfd6dae4725d471116625a0a85e5eaf770aa9c2dfc10be77c0680f99be940a687464b760ef0bd5d27e32f050432f7626f33b30cdc244e6f7fa17a562b87d919da8985c13d067b0d6d9dec8799c9e11c336385f7b023f212ad9bc5216afe4e4de53d086c836dd064d788e55c27442f72f1d17542641c7f13d0a5568938b5d885cd288d1ad70aa18ce19aa8510b07efe43bad6131
private theorem part42 : 2 ^ prefix42 % Spec.Ffdh.modp3072Prime = residue42 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue42)
    (e := prefix41) (a := residue41) (b := 3011910311) (n := 32)
    part41 (by decide +kernel) (by decide +kernel)
  rw [show prefix41 * 2 ^ (32 : Nat) + 3011910311 = prefix42 from by decide +kernel] at result
  exact result

private def prefix43 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (0 : Nat))
private def residue43 : Nat := 0x7f257c49876601dc9a2d9b120d64fa46618a86f380f54408764aa96d33a167bba962b4793d1b4bb5ce4fa6fdc88b4e1e4c4411001aaea8fb876ee99edb44179d4a2cbc7213aa05a4b091724007dba3bfe6baa3fc6aaf4fc28e034194c2cff34d1689e591ae0b277355471a3c268cb1afbc96fa5e053dabf7f83ed896f14ffb960fa762a764ef6788290400df766e15ccf9c05c66f1817f9f0229c8b53068d98ee08967af9153f4aeb4056e26a4b9ac5e3f86ae21e1a4ccaa7b89978460373b95604c061c4a39c4bfbf1da8d37bf57d891d8e7deefdb6ae3e1fb7b3d1bd0e3abaefc536c046219b8193b96f520cb1888b1b8404725803dbe415aa37672b3326762d85419720412035af221815999f8b448735fc5d009d6af18a926503b410853f75f91d26d4b0099f86d1aab99ebd9e4082604f427d97b437a5044774c6828fea7c4f40fcbbcb284572de934668d3a1655bb6b4d6f703b39a18516cd882e2338ab3aeee683a87a259f403c51b66c3fd5b31184cd81eb38c550bae2bcff6eec782
private theorem part43 : 2 ^ prefix43 % Spec.Ffdh.modp3072Prime = residue43 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue43)
    (e := prefix42) (a := residue42) (b := 626936834) (n := 32)
    part42 (by decide +kernel) (by decide +kernel)
  rw [show prefix42 * 2 ^ (32 : Nat) + 626936834 = prefix43 from by decide +kernel] at result
  exact result

private def prefix44 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (96 : Nat))
private def residue44 : Nat := 0x4becb84e1c21c068174bd016addfa54f028b74f3348f4050fd77cd58813d225010048a55999553ae2eb78c8e99b98f3d229d15e300b951e31adfd2e2e9bba096af86765e72fc186df2fff4185660fee660109fc387ddb0bdc0447f5f187a85ae2320de63e4b8d0d39d462bb3d878b32763949401f012ce53844b119d9f6bc0006dd673b969f08aef8d535369f9b390a4071f20903a3abf7e584f78df0be781a7f7c91815bfd0e58e4c64914caabb6b00bf42066faa390808255591ddf47073c07af708edcb893a1390f04a328e5c92d1f90529f7c48d90243c33d156a4c9454880b7861d751072a79c7b15a5e7f81d06fc8f1864bda89bd0c7d9b3adc7522ea84c6eceddeeec8edcc663a99768a58d25e8fdc3df3c1d28f1a9f8c69162897001781a028295d1b13efd2831f65191b791ca9f8f0686fac35ceed8a38dc95b5e4c02f8bd7550256490b7cb44172b12fabde9ab3ba1dce31ff681dc8df6938630f2f150165390bfda5c985de4b493c50cee4d39f0f177fe8365f84d95cddf5ae093
private theorem part44 : 2 ^ prefix44 % Spec.Ffdh.modp3072Prime = residue44 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue44)
    (e := prefix43) (a := residue43) (b := 2025469444) (n := 32)
    part43 (by decide +kernel) (by decide +kernel)
  rw [show prefix43 * 2 ^ (32 : Nat) + 2025469444 = prefix44 from by decide +kernel] at result
  exact result

private def prefix45 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (64 : Nat))
private def residue45 : Nat := 0x517ae8cd027dd50f9ecbc3e40388920f93b36851afafca047008e7e174bee087d6e846bafbd81d10cfd7cdcb184ee117ab19bcb0fd5c0ecc96affa89f369039fc94d374d3527f9de6dca94e95b06b621adc260d99ffff24adb4042f4097f252814b2b43203a14710ba7bbed990f46e3b37259264e073050f78cdc48914f0899248a9a35f0437b330d7ea632a04ddd664e000a098ead409167e0b10ab89c6821f2638cf7676878ff4390477d6b1ed1dc96f9fdda77c57e52c4ae2c0b95db54960876b79632bd509e477e360a3f95ed9ecfe131c3b786754b8814046313fd23c47459691f2021e26e68628eb881c12d8ffbde3c80fe7681744e83a49963f2fd8aa7ba9ab982f6a3813bcff24a77abffeb52f39760b24e01063e340e8dbe4c9e99a50ef850af2c6a76d956b93ec2d9efa46d36b77274fe1ebe558f55898ee94d72197389fe0198b81b535efcf8c16d664e3dd9709bd6d19eb655ba9303b1120431b3d56c5564865b746b0fedb1f3705158fe4aa2789615807c805bedfb05e442edf
private theorem part45 : 2 ^ prefix45 % Spec.Ffdh.modp3072Prime = residue45 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue45)
    (e := prefix44) (a := residue44) (b := 1695289534) (n := 32)
    part44 (by decide +kernel) (by decide +kernel)
  rw [show prefix44 * 2 ^ (32 : Nat) + 1695289534 = prefix45 from by decide +kernel] at result
  exact result

private def prefix46 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (32 : Nat))
private def residue46 : Nat := 0x461693b84b10561dd35f2b79ae4a86b15463ce21a3bd837bd34f68fce3106b4f4549e37f8023867af32085431a3358b1eba4237a272bd9746dd5d456ed8917219e51649ac2aef5fdc3bc59c2ac455d401c458aaeb0e8627939126d7781aaaeaf2432fb7858fa8b39c800e49af431ccf1ddace1e0129d1652fc5cbda27da7a71d95e67a818d0bd437a8aae3b81e4be1ee69e594c09ed51f6064f3248e48659931e9738bc661c397a5e406185007d2bb3c2998e321f658da1975a3ea17dbcedf19719a73edb64eaf4c864308537c9719043315622943163aa46e6c6d91d4a6653ce75ff3ae45af25cf5fc22154039996d149dd703ef7489f15a09291ab1e06565cc0ca5c2062e7960ca5083cdeaec5341b56823424d4db71cea6d40ac4cba53bdb13ca5015b195045e8d37292766df7e0680aaddbf247758646d97607213442ab1f4f0cd39077332a2efd214990f9f8c0455a21cf935fa400bbcf892e6b4ede77b8b173afc2abc4ef5dce1e77efb52155e67f44c641b4461612bbc6c14ca931e9d
private theorem part46 : 2 ^ prefix46 % Spec.Ffdh.modp3072Prime = residue46 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue46)
    (e := prefix45) (a := residue45) (b := 424161059) (n := 32)
    part45 (by decide +kernel) (by decide +kernel)
  rw [show prefix45 * 2 ^ (32 : Nat) + 424161059 = prefix46 from by decide +kernel] at result
  exact result

private def prefix47 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (0 : Nat))
private def residue47 : Nat := 0xd738922b2b6a13b26d281ea86a76ae470ed76440b4749158a7ba216009be06df58555340e3fd374ab9e043f9b74264926f44422a561afac60fa393cb17d0d2a27c795d26298f32f89e6f208e1fc0a8cc689094dfafd01678e1901db60e15a8c9c73c3b7390e710ec9b6ade4f84ce66d2644a8340cb9a712df70151103cf07574e8ac3b3f8b8e00fcf6a6ea73513e63d2268be5b39422fb04409f6c701ad5ee18c17b39a0fbfc60845fbb6ffe67dde863d7688bb4438d9077e99b0cea0991938dc7e9461efd61a0236e4ada864bcc403db6f0ea34aadbc48a3481fcac791670a93803d0006a290d4972a2f27dd0305443c4a62451d7024f928977627268d53e32e89c471692070815f3c52b8a687c4dadf41d779ad2f763b26b93cab54741db2d201ea079597c5a097eca4468b4a00275090b0f52911a62281b64c97447413462a9affb85f2b4580bef064b3bbbd7bbcd7696aeddc17bcc8e43e707971e8605faa72e2d68a15b66f67091f102fca4f54a2dc835f5b33c9e8967b46e395d8c2230
private theorem part47 : 2 ^ prefix47 % Spec.Ffdh.modp3072Prime = residue47 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue47)
    (e := prefix46) (a := residue46) (b := 387671837) (n := 32)
    part46 (by decide +kernel) (by decide +kernel)
  rw [show prefix46 * 2 ^ (32 : Nat) + 387671837 = prefix47 from by decide +kernel] at result
  exact result

private def prefix48 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (96 : Nat))
private def residue48 : Nat := 0x517abbf32a3f58ccc65bbb15c34bb566487cd70aefe0dbc8139fd2ff3a1731ba91cda46bc39a9fa115360b5b0fe7673d42ca13f726588f9d5a502df3b1a08079cc50ce912dc8b499b0284ea4022d7478214747c46a48578861ef0b473ea7f57ab56868607bd3647778401e61acc3f96664a9175c161f067ae1ff71a09b3d84da4dd4d0ac5d1a5aae256f3822ccf9344011e9169ecea1f6d965956945bd63a41afa8c5e2cd4c1bc2bd8972254e65b7c5be0056b36b9c7804662435292fe637ebdd6555eec05bf9cb8c2c85c2161d767e77ed6b7b1353402b429de52c638479dc9ac25a7fdba0aac910ddd8d0c428f1b6d078a63fee64e6b44a5a5c9060149bcd1db15d0ed7a9c76c5749d310955b4f418a36636e90bbaa135012e19e0e0a2d51b902a1979c6a344fa23ee421695f86e92a91d02b723c155171739bd45312d0ba40f1733b8c9a5d3a16137e1c026b646c29388b7c90928ff10efe09c7ab9bf0b869fe8bcfa5854c5f7e0e948bd641f9e30167c519afee41bfed98efccb6657af7f
private theorem part48 : 2 ^ prefix48 % Spec.Ffdh.modp3072Prime = residue48 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue48)
    (e := prefix47) (a := residue47) (b := 4056890262) (n := 32)
    part47 (by decide +kernel) (by decide +kernel)
  rw [show prefix47 * 2 ^ (32 : Nat) + 4056890262 = prefix48 from by decide +kernel] at result
  exact result

private def prefix49 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (64 : Nat))
private def residue49 : Nat := 0xe50c1a487adcdf7e7000afaf1e97d920026922e210718ae3db578fe48c5abca9eed7c73ce84c72d20e133fbb9b404344e14d04fc8587f4883cfed696058ed0f6ebb65e4ee361712a82815cd6093ad0fd61fc14809d30367fcb658a0b93ee3fedd9d65f28b27bd65fb20445c92900bd47f394940823f0ba8f4714411528dfc47944e48860c2a8734d10e16e09b00179b1031042b40e410257f81546cc8d35f4c2f8dd531e26fe113105ca2bc3bb7767e6eedae1d0353e0b093a5c258bece68004edc15059d95d3cadf083c92711736461afaea22595e08088a473d27d81432d9d121b6292b7cd56ebc43483ea01edc4c2044e8b6a23021a4cc438c4bea26e5c292d5d07ef85c6dea92eeb415ac06380b636e70a48078176f152ad31df74894d93923762ec2a229d5db68d75cdde2db320ea7892589cd16319d302c9c8aa1d0b6cf970d63df07d9f93c3d42ef67b8006f0c6e863b2f1cf7dfd7b37f7a8cfcf95b629fea962de32a34257a99cf8c8f2fd13459d65feed324061de1d6b8fe10155b4
private theorem part49 : 2 ^ prefix49 % Spec.Ffdh.modp3072Prime = residue49 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue49)
    (e := prefix48) (a := residue48) (b := 201802497) (n := 32)
    part48 (by decide +kernel) (by decide +kernel)
  rw [show prefix48 * 2 ^ (32 : Nat) + 201802497 = prefix49 from by decide +kernel] at result
  exact result

private def prefix50 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (32 : Nat))
private def residue50 : Nat := 0xc5e635994bb73e048226915771fb2318d4bb3d3736850ce63dbf6fe7a7909f1a24502cc0c907eb92bd3e3ffd17bd705228815629418ea7c74d79e938d153ec6dfd847e1b32b57153ebfdb69627a833b87bb50be1c5ef84ee779cb1b4f0591c08693f486cdab2f4720855b2489c7291c58f12b1353ffcfc88c72a4aa62bdc6eecafbd91e0233a44c76b5667b9a0e12e9cc929571df4b7f5cb9727f061eddcfc0c76beb9250987061390d9ce1b9b24be9eefdefb5eee7ea8e54275fba59a749f04dd8c08937529c63063a35a4f8254ec1307fbad950628d3249e3740637567d253e9b6a4246dcae6ed2f226b583ca82d401aeeaf504285d0e142c5a923a4f470446e970cdb342ad14e2305b5a3be00820c5e3d343233be007114102f65bb72b09f2b979c1f0c8b10357ca0d491878412538ff30a55e0f9de52ccc6f6d1c45ca6a911f45575c7b7c2522aa93e8c69dbedafffea06e8da4f43a378f4a54124d3ead02b0f38fb080a8e150339df885d73b98dcba1864abf827a2626f7209c579b9fbb
private theorem part50 : 2 ^ prefix50 % Spec.Ffdh.modp3072Prime = residue50 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue50)
    (e := prefix49) (a := residue49) (b := 3449012689) (n := 32)
    part49 (by decide +kernel) (by decide +kernel)
  rw [show prefix49 * 2 ^ (32 : Nat) + 3449012689 = prefix50 from by decide +kernel] at result
  exact result

private def prefix51 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (0 : Nat))
private def residue51 : Nat := 0xac7c471eaab04081ffc08768fa130f4bd07189049795ee5bbf0b08e5a04a207f52ea89a9d4c41f84e14f3f983b44071badc6fdd7a477378c38aca3fc54e6f566beaac2b3737aabad1f295309479348453934e2bf494fa9549b68c6adc15a04833ef427ce301ee435d21f43c0d401049d6d644b1f22c64ca89e48aa63fba78f4bd7582f42be510bd409bae92238635f1a0a1f7e8d2a9b56b76b12105a8ed6731bddbd52c8fc52827a78b6a5bc7f8e1194b472333745b110ae3031f78590d9491607a43bc55d452bc8b1431c0614a9f4dbeb3e639b58a4a6d39b90685693e3fa61ed6518adecbeeba7436e4d5b50cfe5f22410815853c034772d8a7a1cc5a78617a8fcecbc6d5e8e2066da98c8954e61d64b2e855b4525c5417a3daee87dbb592209c27cf763f64de88520a4340f907287a1f088c071ef8b01c34af346afceb8d1a095ebc9e6a8890fe71c0f4bf116cacafbdcbbcc3aa9c07fe60748fd5c238e1ff2a328e1dacc14af56da89c4cfd1de8a7eb78f37a10a5bb7aa45942e5d98c2b8
private theorem part51 : 2 ^ prefix51 % Spec.Ffdh.modp3072Prime = residue51 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue51)
    (e := prefix50) (a := residue50) (b := 1979961671) (n := 32)
    part50 (by decide +kernel) (by decide +kernel)
  rw [show prefix50 * 2 ^ (32 : Nat) + 1979961671 = prefix51 from by decide +kernel] at result
  exact result

private def prefix52 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (96 : Nat))
private def residue52 : Nat := 0xbee19701343f94c977c26f14495b16b4a9441e088ee16d532cc5ca8822cd3284304c380001b466e5974d57d9354289bcb4e1f67a142698f054c9a586535f26894317c0045d171291f4c9d4c2c62ac5ec4b3703a1f618542bcdb2801fe946b46f4c28a7e7d74fd2ea1ae25d7908c5db9bb4a99fdfd96ba54c11828937c1c8c451766c7af51e213e089cbc2d7a0f75a3370d80e8a9d43565c99de7efe5e88902933c2fe759a449a714adddf8e3ad8fce123b6b67ca32522707458e4169f30433b1e000a7623e08d9a1ddf189e180d155cb57d1b0596dbe8d5d13856dbfe743f6f3b9c85ec2599c65d3ef098ea0aebb7293c558c07ac98c76480e31e73d6eb6ae7f4db1e593c3cd12414881580ee1d0f254fdc52a3d14eea73c6d02da867cba60e82538b7d6b9e624f72a9b20f5c99227044d07761285d18561d65c2a76c12a5a5e400a12af5a634283166add1a98e68f425e19306008a58249274ce2cab4123abc660319d97457fbf3b5a3e36f4b6b9df388bd80ebca642ede4a00d8b015151b0b
private theorem part52 : 2 ^ prefix52 % Spec.Ffdh.modp3072Prime = residue52 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue52)
    (e := prefix51) (a := residue51) (b := 3672289016) (n := 32)
    part51 (by decide +kernel) (by decide +kernel)
  rw [show prefix51 * 2 ^ (32 : Nat) + 3672289016 = prefix52 from by decide +kernel] at result
  exact result

private def prefix53 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (64 : Nat))
private def residue53 : Nat := 0xf354253104b2692fbeaf844f83113f19734402000948b004f254fc851e91dfa922708005b493dc05adfbcc7cb39b13904f540a1362f5ed3ab57b13bf3f57083c0e2c0ce20c5910a1fc983f4be1bfe2593af9a3f2d9a024fc451dbbea4ffa6d98797c646b43073de2dc78e8763f7cacee9cd1a8c6201e971cea34d96608d1c8c69d6859cff975b2c8312246a5c916c12bfbe6e640a66650bc34036ee07b09687e07fb21f84e525756a4550c802da163c614ad40f269aa090cfb9da33aa3716f9d3bbef4a1cf4d13c41e5c5feb605606b4c39724db5af523bf5e12fd896c0a76bcb60670554bf03359cd5c719ab1ad15348a1bb6ec949a045067a56b815ee9cecdfe50b7d83b21096671c10a74066ebaa87ec7959fcbbcf782c614fa80eeeb43d3cbc2dd212a06e602d36292d5f3252201074f20b66a1351b89c4e4a88668d840f817460fe3ae03a2ef48c38f298f7081730984cd5e22eeac23cc4000410cc5eef15cdcb2c08684c34964926126b6224b9eb143ec3b576d1a3ff6c0293ee36c236
private theorem part53 : 2 ^ prefix53 % Spec.Ffdh.modp3072Prime = residue53 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue53)
    (e := prefix52) (a := residue52) (b := 933636452) (n := 32)
    part52 (by decide +kernel) (by decide +kernel)
  rw [show prefix52 * 2 ^ (32 : Nat) + 933636452 = prefix53 from by decide +kernel] at result
  exact result

private def prefix54 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (32 : Nat))
private def residue54 : Nat := 0x10dd0b7488207cbc215099b75f75813fc3278ce5d4a59310c716e44ee5edb9496a9802b58b578b373d36f028145eb79309efe39c1abd28ea76ab28c497a687c1a8c5e7a80b5c7b69a067a54d030570b9fadbe5809c0a98436f18436625d6cd6a0426ca8c4e27e2c71654d264abec591b1226b0daced17d432e9d1e36485428e4bb8f89535d6d649c2b58bdc7a4b1adf60e0917fde6b21498358d4d0179997a1cce53e81ee226cf902686c8b571c5da9896352f57d0c3ce7510cd6607a8206aa4e6359b027de4aeb735dd3602f5e86ca9c741d704f246d4533a028f7de6044563e4f8f345c9740d2a0c9323cd5e85cf62e6a808069f8210195e5be4628177447a99853be54227628ec1036ce85ef4ad34d49971bd92aa47c73a7f083114b96a811905d53c97df3a849f633500743647954cb27d45e158ea71d4848d271c1db82495296338366fa2f50d5077482dd8a8c3031a2c575f7ba34bcf4d45f73c42be8fd7c1b7c8a19c5aaf418d057391b07f86b98f2d859ef5203dda12a1228d951f43
private theorem part54 : 2 ^ prefix54 % Spec.Ffdh.modp3072Prime = residue54 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue54)
    (e := prefix53) (a := residue53) (b := 4011189755) (n := 32)
    part53 (by decide +kernel) (by decide +kernel)
  rw [show prefix53 * 2 ^ (32 : Nat) + 4011189755 = prefix54 from by decide +kernel] at result
  exact result

private def prefix55 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (0 : Nat))
private def residue55 : Nat := 0xc7dba4e800f869a82f6cc9c5a922ec7d2f6bc357be0825461571af3d8b49244ca851ff1e7fddb86d8090a83cb16a0a5e9799ea61754556de18982999fce6fe5a1e11618f1c7aa98f792308473140b695602dc517c5fca77a4ce6ed68075eb6d345856d5437454aefd87a976c3c00ac60e2d92699275f9eea0791739766309fc2b8a70aa3f2c35714fe6d3999ea194c1c63762d8887c12a51363a86058ca8f835311cbb4d344612039c2b4fe7bcb5db1744fe907ee437ba4df433d37ed662f52d28d0c73d3d3dd5de05311a5cf3289d56b418ddb6e99b86065c785f849396801d4c5a3f46aeb52bff15e0a8e08ff6831ca54cabc49e8f384a67b52b8755b6264b1cada09c9ef8bb39673f28a08ad1071df291f5325f4e00f83cccc2a9f7fd9189bc57ebf06da2ad79e264d97879abcbb96d8ebd060dc63f045c7aa74cb447d245152915667f89305fe37aee61a3b392c9af488a45f6de0e679f54d1d3ee217aaf7146af35e2c2c0d6c5336da7b00c4f80a7faa5f519d81a6ec5539243b1d1d384
private theorem part55 : 2 ^ prefix55 % Spec.Ffdh.modp3072Prime = residue55 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue55)
    (e := prefix54) (a := residue54) (b := 1252789132) (n := 32)
    part54 (by decide +kernel) (by decide +kernel)
  rw [show prefix54 * 2 ^ (32 : Nat) + 1252789132 = prefix55 from by decide +kernel] at result
  exact result

private def prefix56 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (96 : Nat))
private def residue56 : Nat := 0x742121886222b5059e353ea84be0f97437d2c96a566ff81105770d3a9358640247338ee48e9759e2b1ebb8dad5cc2f0ea11ee31405addfc960b643f37d6b797ca78f654e7033a9587bd0ece1c8615e61e1f8b44e7b25664fa206d9046a9d685da893ca2142d5a69d3a93855f54296f3704d005951efecc56fce20c7ef7f2ce4a366a1ce4928ab87aa20550feb2320bcec65c2e3067cde4996ad7e1b8ec53d5eb33c7f4ef4cabca19325ed78fafd114b5e4e5c4e41d7a08843b5cc48b1afce0464fe7628f96ceaba11b8a00335298f3460b01c96fd7d48c7064030584a6068a7cef628509f6e3db39def2288f3664ea2d8549cebf99545784c24bfc2cec09d091e67e5019289e97e612bca1c5de1777911d239e3c7dc31ea7999206cf3113e54e3ad552b1b779a8628086b50f6349c83b9d56f78a9c6e2abb33fcc953ed95b645f7d18c6199d31375bbc3c90d23095e03fe653ce031dfb8c3e745533d200b8365f8d7b20b14c0e7e0ca4d4caa117f2e470cc22caa83617ce8deb4766503fbd10d
private theorem part56 : 2 ^ prefix56 % Spec.Ffdh.modp3072Prime = residue56 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue56)
    (e := prefix55) (a := residue55) (b := 483042494) (n := 32)
    part55 (by decide +kernel) (by decide +kernel)
  rw [show prefix55 * 2 ^ (32 : Nat) + 483042494 = prefix56 from by decide +kernel] at result
  exact result

private def prefix57 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (64 : Nat))
private def residue57 : Nat := 0xf8b1eaeccd8e086386ad4ded9691727ca6bfa5a209a9217642f5550196a7c6ab5f1d21961da9c11bc9fde40452e7d024e273abaf87a3438c9f8d082a787899045c1e94cc292ad618cf59511a6fafe110486c6e3e7da12df06d5e985e801a954617597f557f0d02c0346512664b995ce3818ed66f29e0c8e8a90cdad8c30ef90a1908d183bbdbf24f643c5d306d3bec23e8f10fb6a3794a850c01f59b6576cf8f965ab086db9c6cb6d2c3cc8967ed3e64ae850ee9261527538ad485f58c9465b96fdc09e9324fb18962fec2a36b5d8359620a0a89e0657e178cf4f590985b64ccd90f91683709ea64d377279dedc6e874123f8479cbf5c8dd4de3bd8de536f20d4cc76332eb3b1fff22dd6b88ee55ca63c5dcb3c37530fe6d99fba957e2c39b00b64e93752e16fff69f332386d935f7dd6bdac70cbcbacb7c938206dde9798aaa142ca821d0401edcd42db9ee13b7cbe9d4f5f7e969045b7a9c11bcac8ae80de83342d0f5278ca051aee94e2c4222338ec38d7d17d13434ac1f634365e05a4675
private theorem part57 : 2 ^ prefix57 % Spec.Ffdh.modp3072Prime = residue57 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue57)
    (e := prefix56) (a := residue56) (b := 1967830386) (n := 32)
    part56 (by decide +kernel) (by decide +kernel)
  rw [show prefix56 * 2 ^ (32 : Nat) + 1967830386 = prefix57 from by decide +kernel] at result
  exact result

private def prefix58 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (32 : Nat))
private def residue58 : Nat := 0x85437e1b7bf2d16463c28a9685f84f1b709ef6cd22594b77c9fea5896e5324d805299300c24a7c0b0b95f272f539c225a44857aabf72f1db57b25cbde6121f43884ddd167e564d87aea1b0da8c35083a4da0581e9cd87791afae7e68c2269c9f2af4ddbca062b2628afd3e7d04a6ffba4051e28f570647def841322d5cc77918a1fa0c2abf8943a977115aa1168e95310e08b07ba9c07d2e275aa73cb64308fcc2db5667188567b4a90c43547c84039b2f97a21ca59ce89529c66d7b193f4b917cf69c546fca968f5d27fa3e9234e30f346bde9c0cda224c3ba0eb57b9a728ad17ca624bfa8ef1285b2706f4e8a31ec77838c75f0dbdf45d696b5a58bc87f7eebade1e536ac5e8097c6bf0b55165e456d72f0a95adfbd7c589f258bc59091688444c6dd45ba9dc35c5e5cff08e2e93bebf2347e82376391bf088be4701d3d114229727d74173602004bd04dcd31fe08f10b515ffe521d0827bcea8dd9537335f116734de0cebdc338efa42a28d53754f022eb58e47e205c90f65a4b056a03f24
private theorem part58 : 2 ^ prefix58 % Spec.Ffdh.modp3072Prime = residue58 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue58)
    (e := prefix57) (a := residue57) (b := 2330530572) (n := 32)
    part57 (by decide +kernel) (by decide +kernel)
  rw [show prefix57 * 2 ^ (32 : Nat) + 2330530572 = prefix58 from by decide +kernel] at result
  exact result

private def prefix59 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (0 : Nat))
private def residue59 : Nat := 0x4ab14c50b4292b3496393f5b48720d6f27a5e8107d1ca7d70c7fee4e13c408285708d61729bdb8004fa6bc7be55e5e91b35d56652217a1437aee9ba3b2bf3ecaf07acdebbf0270a3343b5e8e25cf0bfcf4e53816da96e84d53267be8e122d7774ddcbf639bb9d6f8c3f7b276374cd4c7d18c3ece62df9eba17c64e6d0534b2e8acc908dd9408e0d46f8767296fc4191ed0b199b1622cfac4582a702793ce88cb149a4932b215cfcd1084847a24be3781e61804b6c8e9a788c2261d9e1066c72fae96703978091dae50dd9245b25e540fa4a1fc7d9cc76e26c4220464bb3141ea2fa366e84dc35def9bf4e784d610595ea7cb66dfa6fbb8261ae636eaecc94ce0a5dfc9c6a74e46daf0b3d9018c7d1c28d85d3b6c0df7c75b2ff9dae86ba6c3c7ac854fff0a12c281657f5cb7239e5006df45fc416d4c2c7c17e520650b0e63f2769bbec0296d87ac48f13f99e418c75bbc1a327d5611ba8bbb40529f533c791e3b4083974f78e6605cc968401f2973be43eee3a8cb33476463bf950544269426
private theorem part59 : 2 ^ prefix59 % Spec.Ffdh.modp3072Prime = residue59 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue59)
    (e := prefix58) (a := residue58) (b := 1283261064) (n := 32)
    part58 (by decide +kernel) (by decide +kernel)
  rw [show prefix58 * 2 ^ (32 : Nat) + 1283261064 = prefix59 from by decide +kernel] at result
  exact result

private def prefix60 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (96 : Nat))
private def residue60 : Nat := 0x14e680d6c45295cde9dbe63cac1aa58924d6d1e39fb09d1fc8f7d746a0c12f564f799fa5fcf0883457c55969df41a90de97b3f1d50a1859a4846bba35912a37970a66f957fb560c78a22a747447744f836d849e87fbaaff84afd0e2dd434d3ab8a477ae0db494881b5a3d4f01765417f2031ee4ee5e6f85f4f7926a99946dfaa143da99c31aae05807efe9045346c42e4d52028527a9f640f155699fc628082ab0529e5e68153a9f6d3232576763890a88323f092bf554405af8ffc29b0f3f281f5c3bdf584bc24b20fe47a8ab0fcd911c4eba10ead62b6d5bd5cad2c71be0927c5b38f6c67b400bdc7ef89ba5cef358834067e94026303d70edb6cf7b5def2006de7ecee55667315ea4fb5760484ef15c8d89c14ca1a9743b8dfa1e06db92fd8c0b4e9a571b0964cbf654a9c28096edf3056c1d7a27aa8cf2be086dbdfb5ad988522a058fd16215e1b331227babcadb7783f2be84c51cd49d9450f1dbcd71087c34403ecf18ea4ac2f2060e26990c8843f75d583670c9870c743a8aea85361d
private theorem part60 : 2 ^ prefix60 % Spec.Ffdh.modp3072Prime = residue60 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue60)
    (e := prefix59) (a := residue59) (b := 179914541) (n := 32)
    part59 (by decide +kernel) (by decide +kernel)
  rw [show prefix59 * 2 ^ (32 : Nat) + 179914541 = prefix60 from by decide +kernel] at result
  exact result

private def prefix61 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (64 : Nat))
private def residue61 : Nat := 0xb7114689587259d13cc2eb5245d4667110c70eff896f0a18964a19725a13bd16d4562fcd53b2d0eacb7b27b52767e317b59e6ec65e59a09d7bc666d575c5962d8657a9b7e984b23e8f019fae04d3a7e628253881e8be6640628600f21dff22ec348be4418ed0257abdce0f24c668a1b1678f4a73ce931655c0c722acb082cdb61bae5792ae795d06377462b23465848eade48b2b4cbcf04e345ab716421bc31c88447e32e37f58c98d54a32e48601da6420d3478d908a49a48fa114d7dba2fdef327b8e67179c241d6d40411dd1ac08be256f962f621763c64f76ca101d1c0ed4d5070268215c751efd69d062657a749446233d72711f05df3142f8a2c6aef84ba3e1fee60dfe4c236a4d0107d227b706aaa3d4e0828ed46e82a1437e6c8f0c23068c806fd98ad6e315bb7408df86a452be20fe9702a9d077cd0b90a2593ba6541b0e744ec38c255253c28ae348a577fedf724b9d76419a89af70e82062dc7a9298c766dae534f0ae665a2e94f9b03c13ed2a8b20a8aa732908ae9a22fd4ad71
private theorem part61 : 2 ^ prefix61 % Spec.Ffdh.modp3072Prime = residue61 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue61)
    (e := prefix60) (a := residue60) (b := 1163223574) (n := 32)
    part60 (by decide +kernel) (by decide +kernel)
  rw [show prefix60 * 2 ^ (32 : Nat) + 1163223574 = prefix61 from by decide +kernel] at result
  exact result

private def prefix62 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (32 : Nat))
private def residue62 : Nat := 0x7f27bb1e3d3d161d87e369da8c9f9c871181db08fc053ffec88ec46cc5088f21c38ce9eafdc79f9bb97013773c85f0ba8bfee7ae6328d043c4cff158980eb47841abe4a885ed2e30c5ef6a30fc100f32a6c13fcba9cfab3a1d8d1a4244abc7cdbe360a79872fd1dd14396a23e47cf56765b930f0d42d0a1d1ce0294107a5ccb5f16611c7d66893e2e16cbc4a9f040e5fe4b328203c04896777df838cfe4592df630f2f951b9727cef17ca25cda5ef375f0d8f0400fdd1d26b8741aa97b95213fc633e75b342db9d9bf5d4a6502e0394c9a7b4b304924f44dc4a761fe94aa60380fd75c363adc9838f8f0fb054bfd5f31033aa56185a1bc7b2fe4693a5a17b4adcd1df7a468cbe8862eb6c527e9d91c410e414465543261b401c2c72eaa1bfec5c0125a6bdba8bd11ea54fa236606fcfa9a266f28a776dd6a8cf10cd3f8eab1b1de4719e2931982c39cdeab5bf5c599441a1ef4820f4e0fd97b6f3f16c9f3970bcb903e9af48dca30f79d0617557d7a2d0ebfe8d9c3431aa7ad8e7110b7907665
private theorem part62 : 2 ^ prefix62 % Spec.Ffdh.modp3072Prime = residue62 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue62)
    (e := prefix61) (a := residue61) (b := 3600386950) (n := 32)
    part61 (by decide +kernel) (by decide +kernel)
  rw [show prefix61 * 2 ^ (32 : Nat) + 3600386950 = prefix62 from by decide +kernel] at result
  exact result

private def prefix63 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (0 : Nat))
private def residue63 : Nat := 0x45e0e14bd1425d54658b710aa36aff66fe2528d8940fca9cb10c67e44b7abb774ce272af5f74bbb7e2235f2569aab933e21d80af456e8827d932a265f3efa6445c515fc77a9f5a7508c6cffeb6c6775f9b6fc1c1229faab1b8bbcb21a4796677954769e034fa9b14797f075a2b12b20b8c47b29fb965076e55eee5f18d77f6b7d5e6cc68c3e274f6c17c310664c263569ecf5832a0712a71df0f10d268cdc8c356873407909397bf7bf23f1d495800f3fdb7651ea9ebcd40e82297dae4bc8bc3285c2aed78abb94ba9544244d8300cb1827045e5005755284efa53e55002afe03508d67f0b6e7bd0bb3b944531674fb5fbb858227e3ec9bcd77b0f7588696e2038fe7c8238091b66bf712ea9a296869c62bf732a9bc18bb3a6d822dac58e6de9304a4ff1d961269768afcfbef0b6cb6fd8d96bf70fc32949d82191f6ec3087ad8d17029f07889365987c019811c7c59c98f295323d59c7030979602ad02a17e6c26f2e00f95eedf5b1f3efe84433fac132283f5cfe2b1a7fc46d5d82c6befdd0
private theorem part63 : 2 ^ prefix63 % Spec.Ffdh.modp3072Prime = residue63 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue63)
    (e := prefix62) (a := residue62) (b := 2183675161) (n := 32)
    part62 (by decide +kernel) (by decide +kernel)
  rw [show prefix62 * 2 ^ (32 : Nat) + 2183675161 = prefix63 from by decide +kernel] at result
  exact result

private def prefix64 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (96 : Nat))
private def residue64 : Nat := 0xefbc8d9d8db975aa256dbfccab6fda583f0e3368d789c80c08c1ca22cff52678a42f9ff826ce99079ad087508357bb50bd25b952dbb1532ba81a0815b69ad4264e35f030a21dbbb8d78fdd84e9af0c5f8d90e3b0332d8b28cf10e6063314e5ea86724f224ff88281f7c2248fa85deddf336bad1bb3fc03585c2f040403279c12077139b1fb6301285587859157c20f6703dff91b96a123b0c67598da8d140207da6207cdea7ad46dce0b0e041cb977126f0c98854260631926dabd97b2fe145aeb97e8d5fd372cd080cebe56ab9107b74d8848cfee0c5dc1b69608330353e73c4ab01fdfa8e890dfab398060643897d0820a95b13a11feb81ab9c350048735951871aee604026fbf8935f9a10aef16b817d85c94160f0a8d245e77fe258abcd95dbf8ea1c7a999ef749e3d7cd5d821112d320a58aac352821830ae16c10fc2b574e65e6e94b50d3b5d7d4eebb49e70ce0faa1a278911f40043232b86d2b77ccb599239a352fee531349711d3fd36f6458636f2c43055fd4a7999681fc5ea9f31
private theorem part64 : 2 ^ prefix64 % Spec.Ffdh.modp3072Prime = residue64 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue64)
    (e := prefix63) (a := residue63) (b := 3559559381) (n := 32)
    part63 (by decide +kernel) (by decide +kernel)
  rw [show prefix63 * 2 ^ (32 : Nat) + 3559559381 = prefix64 from by decide +kernel] at result
  exact result

private def prefix65 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (64 : Nat))
private def residue65 : Nat := 0x641956fcc83b0c1f3732f220fd70e4a8462627b642504f2e3361d04b9571292adcda9c59a2e049a24da3d763ab0e38152646c941796e69ce316234d7e9b5624522aaf53c43bb221b9a33060a2f8b8781b9cdcab14b6a05d8c96dfb75d5fcddf2baa4c3af5acdb0a3dce1c8696dfbcff591d3090ae52030ff82f54d1773bc16e67c776cd09e8fb6b2c1f8ea9f028c41e33b3eb19c7366f1310ffc330079b2a628a18c88a0edbbaa648d473f99d23c3bdc63c944ed5d6cfdf2e107372a18525e5c8f0b8d59f35fb755e97cc9a6c61a585b4762c404e6ba178691179229aa9610c95c87a7989d96d92c879ddfa8d99940fa5b4b0cb8f063b8f43bbd661102511f2c187e7477e3a9f12110d772ed4d67e1756d8282c71345b6c627f8fb8f1f1b923db6cf417160b654bd66e916488e1b943d9b37a1321a797f481fa1a6fb88c89e4c4242d053e1597fc66fafd38b3be8e2c2e2b7bd7163a238d97acb48385b2422cbc45d8d6f0ee3b5300ee52a661fc7d1f2a3163da7fc3851573af19c5420d53cb4
private theorem part65 : 2 ^ prefix65 % Spec.Ffdh.modp3072Prime = residue65 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue65)
    (e := prefix64) (a := residue64) (b := 4019084594) (n := 32)
    part64 (by decide +kernel) (by decide +kernel)
  rw [show prefix64 * 2 ^ (32 : Nat) + 4019084594 = prefix65 from by decide +kernel] at result
  exact result

private def prefix66 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (32 : Nat))
private def residue66 : Nat := 0x15552dd38e8fcd7bd8267f21dfcd74f7266bf2227902e0c2a6fe5a7092053aab60c67b437bd21276ee88a936d11ddfa12f30ec4edc5a0762625dcfd6bb6641d84e5d7dc5668aad124cfc51a50165109a6f729e7088c3e3ea14c26f41230eca0f9e08622f018ee2af22e153c40b1a9bf76b432a5017cd1e67e8ffd56530cb385a7a8f61d940080dbd6f5455a952039bbe612dd82ecbac5a63af35b9e519837425a1fdff65f940c9843ab5ad3fa28bf312879d306488fe4b7c826b1127cfd7ce1380acecf363a5372e7007e4cae48f93e4b0a51425e69e88abffabe5200c9be707c2493d27214bfa79a09121007ef24c2e4705a608331e532276ee4c10557b027d7523b063819d46fbc647d927d8dc2b9f81b4a90b47befe5b9e2024fc8d3260d30d1727043a6899255225d0171284dc5af38c32bb22469d29552083da4b5802a62913f6b39f9a1c40b8286fa1e44c26ec50f4cb94f749a8a5e9ce7163ba5364950fb2d26b7c62c735b7e6706828e0a9d3b4891773a24a3d48f4c432a60f88feba
private theorem part66 : 2 ^ prefix66 % Spec.Ffdh.modp3072Prime = residue66 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue66)
    (e := prefix65) (a := residue65) (b := 1987953282) (n := 32)
    part65 (by decide +kernel) (by decide +kernel)
  rw [show prefix65 * 2 ^ (32 : Nat) + 1987953282 = prefix66 from by decide +kernel] at result
  exact result

private def prefix67 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (0 : Nat))
private def residue67 : Nat := 0x544bf8d07b9fd6498a3be5fa828bbcee575bdd2930f5e33d6a06c2fb868108ad2104dbf51acf5370780f89b838afbd26b4a66694404a4984b65a660422470496d94fdf916d57cabf935f54c8444b56c07d4fb72e278b51f22ed478473863dfdbe633c95c834499c9fc19b7e1d25fac313a46f3fa3a3c888a7d6058c34521e58aa205da0ceb732497e91b023a84ddafad7df4e3644f8d22e4f81362edc0e2d648ef883a306b12ebf4c50fb6a6d9e44ed2fd9c7e61298fa49438874e7adcf357fcc23f76d48266f68deaade94537159bd9ce2b3eb1e4c883028527e107e75f752cc126caa2e2229e63fdc676d4223260d108772808e783e047430ddc9c4c3a64944e553618b7375067615ea4baf503e5e0461713dfd13262e6836d4587da7f9e2395d4f00443b8fcaf18046cdf9222cdaaf2bcf7f5903837e8365e543de8c7caa28fda3c4e499c42873e93a5e3796b27d42711c1186bf156bea0b728fc47d7f9b8b2dcca6101a97bec068f6254279ee29afb1b099531776f36d3cd5e5653eb98cb
private theorem part67 : 2 ^ prefix67 % Spec.Ffdh.modp3072Prime = residue67 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue67)
    (e := prefix66) (a := residue66) (b := 745404293) (n := 32)
    part66 (by decide +kernel) (by decide +kernel)
  rw [show prefix66 * 2 ^ (32 : Nat) + 745404293 = prefix67 from by decide +kernel] at result
  exact result

private def prefix68 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (96 : Nat))
private def residue68 : Nat := 0xe515e946bd626243fc8067d5f189beedfce347131e4e24973d79eb208adef68bec2a8b7e2c9e3e4c7b835c8d47ecd6d03f05c42d0720d72aba5adacc44c6ecb433675a7c5ab4ea02d963798bb8f88c88a6994f98b02243bfa7132dd4dad0f6a10d2951ab1c52d74d3368548352928017f6ea2ee99e24ce7be8b46fa01da5a703bc6332154259b42c9e84c84edf2ddc4adbc92c982441180edba4e13dbe6d2792826975d45140862543e4a7d9280124782b28df972be2790c9dce0f5d40027b3458ba59046a709d83686cc4ced2173c74b3c648a28a90406cc71e06dd986ea53c6d8e6ed75e68c69cf66b7030a8fd7f6a2d3b4b5eb9acfaa4a1e4fb42b9d504fbfd0fe0b65b4e41dbe87fbbeef67083395baf03d91eebbd6850a0bb01ea2b970a370096f4499c1c245b11397b9cdff8621c02aff4e1ad74000d6da51e6a25d0b6b7db9f97fdd31e9a3619356622cb7df35029153ee998fd87e1dcb7be18dd4226bfbf8807f717c62994f90125966de6a454445a5bed2ee6119f5d4a1c254b84d5
private theorem part68 : 2 ^ prefix68 % Spec.Ffdh.modp3072Prime = residue68 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue68)
    (e := prefix67) (a := residue67) (b := 1165310123) (n := 32)
    part67 (by decide +kernel) (by decide +kernel)
  rw [show prefix67 * 2 ^ (32 : Nat) + 1165310123 = prefix68 from by decide +kernel] at result
  exact result

private def prefix69 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (64 : Nat))
private def residue69 : Nat := 0x39d901585c9f9a507e6185bfcb5864e62470e47f4c8c381a43c17ab8b072dded9301f0c61fe61d901575a5c0bbc25b354fe13322fc60c8d6799c39d0f46165ef5955b4916b0bbf385db7b715f0ce4fdeac141cc33b83e0ec585cbc5489e64528f0e65a520356e551c3703dc85d0e4829662f65f47afb49a6cfe939252c80137a84cef5e27f5c709c10b4f8951acf6a6b7e282d23c671f19eafa3fbf1351148b9d76f840f2865330688fed3259d08a6b1020cc1718a57c9ad009f7b9d69ae27655d4882c4ecefd30fe3c048c658a5f2f22d561719d268e0d606483172b2a7dd6907ea324cabe53aa19bb818b76b57a422f55f6aa1b6569e64afe0ea1b1527319ea0e1015a9084ac74476298bbf4567d136ce551addd51da8f739ef77d440cd66345f73351b01de48a5c2d6b7295c07c5bc4b482dbed92379c3a8e8565665aa8bfd62c45c3b9136005caa94a2241c45ed193f786112148b37092041aa3a8af7da3ab29bb58064e8952028685d61205f9d28d7be2dfd4e66580c5fa7d8de9cad29d
private theorem part69 : 2 ^ prefix69 % Spec.Ffdh.modp3072Prime = residue69 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue69)
    (e := prefix68) (a := residue68) (b := 2927822398) (n := 32)
    part68 (by decide +kernel) (by decide +kernel)
  rw [show prefix68 * 2 ^ (32 : Nat) + 2927822398 = prefix69 from by decide +kernel] at result
  exact result

private def prefix70 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (32 : Nat))
private def residue70 : Nat := 0x7d419ab171497181bbd8eeb8c230577aa7ad4a6b678461061d54ac2d3bf72da7b4ac56a484a59db2b00c9423965e6c156e1dd9256c4b2e81f47fbd503ea5383eb19b16319143445d79a58cee29c3ce32e41d44ad97952ad70df30895693b57411cf78e97153545a542db4fb41aec590fc6a1d5aec3a4293702b954dc83662eb1d43b1398e1733548fa763d18dbadf546df5cf52de08ff6248564817dea266c9da8dda311ee1758a44c384cec8db10d1485c2010d535aeee95a98b74309e73d1c0e9d317ccb85cc696b39427463509f3b80fc6f7c5ee6765acaa092f51e68a50238b59ec66c5228384145685e1bf36b7c3a9ac0ae1e9de5bdf679134116ef605c6e902d8c11d3a88de48861b2393c6c776631dee864cfc2f91a425c34295f4e87eff3bcb4d3ad4be63ffa6008b970b5e987386f842c52a8cca029e413453de8233747756fec0e842340b5886275829d14613dd8025c4a040f630a2d201e1a481381ecb8ecd4a84adb539d3734ad9d1e380c45d1e7b02a83b407e02ce0d54eb648
private theorem part70 : 2 ^ prefix70 % Spec.Ffdh.modp3072Prime = residue70 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue70)
    (e := prefix69) (a := residue69) (b := 3653994434) (n := 32)
    part69 (by decide +kernel) (by decide +kernel)
  rw [show prefix69 * 2 ^ (32 : Nat) + 3653994434 = prefix70 from by decide +kernel] at result
  exact result

private def prefix71 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (0 : Nat))
private def residue71 : Nat := 0x72975a7b9ca37ec1fd32bbc2c1cff26f13763587ec742d70d6d0e3f3259e41931e3d0dc1364385b2800d8c5a214028b5d41695060b66bb70a4148274b57e5a34176532bd0d6ac54ecc50b5bf1dc1118cc0466a50b62ea02bb7a8303ef61f841e5555a0720a1318f1957f9a20afdc1475b8305d44d8625f522fdaf1dd77c0c5ed095ba573517b4f69a9a17c661ce1fa16d43cd4bb579d92a63a4701ea6831742ec1a9292411258223c25ca093e217f2343157a53971adb0d7079f1a1b9b5352d1fcf2effdfa4eb1824313ddb9c4c85037ebddbaece4ecf71198b4073f81b29b9e977bd3e3708c5979ff84c8b2881337ed894d32a18794e631a5b7b0067d12192a5cac80ac1ec8beb6cb0cd444368dcad6c237b30ebe2c00c09b753974b4b45844da3b45dce365ed1c91136749a86b1128ca7bb187b78f0e913ba2c7bab3a3646b2281aeca815d4e11f0d14fcd63c2092eb07772484277c936cfc95fed4be4ff8d3ee357d0430e1f42dc5425491c7d237c1bc320dc0950841223e683b1bd2f239e
private theorem part71 : 2 ^ prefix71 % Spec.Ffdh.modp3072Prime = residue71 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue71)
    (e := prefix70) (a := residue70) (b := 3547394659) (n := 32)
    part70 (by decide +kernel) (by decide +kernel)
  rw [show prefix70 * 2 ^ (32 : Nat) + 3547394659 = prefix71 from by decide +kernel] at result
  exact result

private def prefix72 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (96 : Nat))
private def residue72 : Nat := 0xffd9eded129801f4bb318e5871de879f1e35a35c6226d49d1358db3f64ea753ceec63d87e928ab788ad62b9739adf6b7bf34b36edd7bcd9c0210e032978f283034eced7f1f46441a0b784b792fbc5c32dfdb16773ea54baa34e481e0cbd269e3bff3edab55de51122639a1350d9d2af951a7c9c33b534718a656719d16c660ec8b9602f4ce5c295e49287d99ba2228cae0a5181b79191c2bb26504d39d6ebd8b848e6efc16ffc2a0c0123c51b612ba232509656290c18d39d2421752c046ee141d0b6241e2be836bf8aa4b494bd1747b23518a8f6da1ea945a3788a3eb70681f9e28275d6a1ea4a54bf08c2ff34b160f1e26529226efddfd7499264dedf5b2fcb582298d3c0d94c777ec49edce10e39c8b85c68b897bde8c68a4cd1349b761e2126befffc043831c3624cf157290d825f3ce3ce50695e25ce1bdf1a5d928790b1d3a62089338314a8f3c2bb0b0d6d6cbe57f1f56bb229baa6e324a6ffd6f958d320616601513b97469ef44e574549fdd9cdd34f946a64598a0c9c3a64224eb0c
private theorem part72 : 2 ^ prefix72 % Spec.Ffdh.modp3072Prime = residue72 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue72)
    (e := prefix71) (a := residue71) (b := 3589986118) (n := 32)
    part71 (by decide +kernel) (by decide +kernel)
  rw [show prefix71 * 2 ^ (32 : Nat) + 3589986118 = prefix72 from by decide +kernel] at result
  exact result

private def prefix73 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (64 : Nat))
private def residue73 : Nat := 0x3ca6cda50c880a1d60fe9e39627a96ec5ffa9b44c995ab728c64fa975969c7bbc8351ee6f42702a0bbbd5e40e09478bb61bb52f89c32136f7f4bfb17ca04f1b7f80f4e2cf26898333d50a66c54fbc285275e83f19a2a70487afc48b1a1d8fb3286b3e128ef25368074a4dd5962154a161894c853707329ce21379f2913f8e37a379d85b9ee312d84673dc3520170244d9043665795c5e2e544dd8807640230bd04c170219b7decad91611fba1d2c80f36cceb1adbb777594c77c0383ca261d62bdfa91f3cfd9ae77b7f545a08f4c16d34ca57ab39be8822d3a4b5f4acdd9344c3bdb11ff3941411d6a0ef3003bc533a2a326af62151cfc3aad192d90ddb5066112ddb13a3526179f5b0662ceb14c437992d525cb7cb343e21fa10d9bca7f526331f9d898f7a0f92a108e4b6af7d0e8f984cc46f9d27b04c330777717e28a05e8dd7282c9478c2e0228134c5be6e0ff2d9b50e796278f127ac0f5bf11f9c8e3762b0389491859a80862580a549763debcd21f59a62698a824980a99747a8908f0
private theorem part73 : 2 ^ prefix73 % Spec.Ffdh.modp3072Prime = residue73 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue73)
    (e := prefix72) (a := residue72) (b := 1837406699) (n := 32)
    part72 (by decide +kernel) (by decide +kernel)
  rw [show prefix72 * 2 ^ (32 : Nat) + 1837406699 = prefix73 from by decide +kernel] at result
  exact result

private def prefix74 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (32 : Nat))
private def residue74 : Nat := 0xd96a38b45fa618f621ff7b7ed8ead0ad29522f0f17aacedb57fdbac354d757a3e4b0023777aca8722a11a869bf83a3f64735f80d0e16629221af9c874b69f540a380e9b52fca7381572be9f08462bcb2b3ed681712b472e55876417360ea28bc3f318ebcecacc7177287371edb961fea2f9aec57e96ae1f7648bec53bd0ea5a4c3b67904e82279f610d495be035c0c75315d6d72f1cf1df6f6d47f28c4af3d2dbc805f76aba63ce9dc650127cdb13399a299a67630481c148ba6e185116e8b5422fe9ddf40a43b594680cad222442ba1f7f0a1aec312dd16f3894ce133bd17ed1de324eadceb925bfa7a23fdedef584ea4641b0c28118d464b80e557a4e0b61775ab6708ea21f2e28cb10d76e1c7a87e8a05144e2655dd8a3b46fa0c55c3f4da9ce5531dd8380c0b5c674cf2924f61cc75324d78cb28535d5310cf1f3957732b016507df72fe3f2c6297cc8028df49649d163c7e1a50997096875ddd0bf2761e9d3d5ed812f8cdbeec878dd72dd873d684c4c403d3cc47b5d223faf090c982a3
private theorem part74 : 2 ^ prefix74 % Spec.Ffdh.modp3072Prime = residue74 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue74)
    (e := prefix73) (a := residue73) (b := 2403748464) (n := 32)
    part73 (by decide +kernel) (by decide +kernel)
  rw [show prefix73 * 2 ^ (32 : Nat) + 2403748464 = prefix74 from by decide +kernel] at result
  exact result

private def prefix75 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (0 : Nat))
private def residue75 : Nat := 0xf4182d0c6db9ff8bfb8804856c6c84cabfde3d3eafe09684c4dc215b16242b9ac7c05f2edbd84dacc61e55e375dc9f88207561d7f6a6f9b0b544be25a4ccd9e8ec334c9c220054b15bbc37bfbed716d6bbd60f1ee8eeba58e2fad0b58cbd2e87786c71f5b65b4b16853758c63204a158eba84497059783571653f1bee449b46ac663422d84ffe7bd0c063f7564a01c05cbd221cc05ce377a795e345b27e5aeffc2c46c9eb248661d3b79a2520f46005614247d60cdc583e46ea79822f8e658aeea155dccbd146680ebe472715cedda4674d7f8208478e11e443c4325600bec2afb2cadda0fb3bf0f17714d9c4d833f540258d2ce91121268995809f6cbcf66c75dd0e0527ae7763e3d3b3397cfaec33bd69238a9c447bc54a0dca920b31df7cf5c43cb8bd22ab4bc29fc44a85c48df6619f774e6049f60517b4aec44f8a5d924a98bf5a037a45ebb6548411329d315a861f739044695294b023939cd2114d42a505878770c059fb8c2c114cecca309f8cf6b60a8bdfb52a1d3e3b90f5949581e
private theorem part75 : 2 ^ prefix75 % Spec.Ffdh.modp3072Prime = residue75 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue75)
    (e := prefix74) (a := residue74) (b := 621981902) (n := 32)
    part74 (by decide +kernel) (by decide +kernel)
  rw [show prefix74 * 2 ^ (32 : Nat) + 621981902 = prefix75 from by decide +kernel] at result
  exact result

private def prefix76 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (96 : Nat))
private def residue76 : Nat := 0xba60bd1a9eae88b0869d23cc545bdc3de3a617dbe22d9d7c40717aabb3b61b9cf2c19f59b555f876bc5d239717e445471bc9da2a1a677038decdc37525e1856d5bad0f3d261aeb22196a3e1d9b40918ecacb205d5c99e133511d47620373609b7dd0c3ef11905f5c63b9b91637bcd0609384289d9803d1ded35aabb12b7560479140b40d01d6563e2a9b22e027a5d1f01242e955080d3a411eb19e784b58918b14e1bd75760f5851663bbfe2294ba27b84f415c0467575af6dcd4a18a9e2ad28cfb86a2a62c284fec06cf048ab93bfad5b037d5b55ef652c47022372a69edb9fa2bf3cbdf14a442573fe37bff0195ed6ef7e29c9661e2208ed06c30f22529df0ab1572985f7103ef802e925abf386adc44fb5dc11d46332e7386917c75b671d9899e63603fa129545fa86e6fe89dc74faf3a16d0ea69603b4383673d4fa832d50bad830baa0cfc4bb0d4585696e1cdcc21b746be78ec2eaccf16e57fda193656c747c00c0f02490ad98f6d627d6b5fb357b33b9c6d327bcbe82a10d03fe2da8d
private theorem part76 : 2 ^ prefix76 % Spec.Ffdh.modp3072Prime = residue76 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue76)
    (e := prefix75) (a := residue75) (b := 3883002131) (n := 32)
    part75 (by decide +kernel) (by decide +kernel)
  rw [show prefix75 * 2 ^ (32 : Nat) + 3883002131 = prefix76 from by decide +kernel] at result
  exact result

private def prefix77 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (64 : Nat))
private def residue77 : Nat := 0x5e1a69ddc97b875795da8bf4a5c827caa3bd65936720082cb3585eba5019b7905987152727d26c7b9f4ac3ba28d31bf661bd7543b2c733334fc6f24223192ceb62d89376207d397ee251c93ffeb3e6700a884aa4e2fe2133c59b7cd5e5183e173ed7c46b577cf6d75390ddda552791fc575ae414d39aea0291432fb198198311f09510599bc4589295ce80f6b14d67cf62c283952c28bbf17d56e3c2fae0d936151b6027e47a697fe11012de1543db613cb98f8cbd5e05ae4e4f8df45480f9006ae0158d74f05703c63c90b35b1550c72f4dc96a7b4f3d538c5f1622e4805482d3a7c5438b1bfd6ba9ad183c4f1c5480cc4e77577939aa075b1e04f629e5b6ffd34515ac37ce8fd730d815da5eff4d007d706af3b983126a7c7cee6fdde16383f40d83ad1447e87ae067f4dc15a60750a657942a82dd67743ae69626de3cfae88a51c85de4d870ec5592cb6293cc8e74a88cd0ebdf7b57875de497c9fe0e55ed84c6f1ecabf73ffac23e3c6babdd41e0f48ec43e40c12fa12305f264a05b102c
private theorem part77 : 2 ^ prefix77 % Spec.Ffdh.modp3072Prime = residue77 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue77)
    (e := prefix76) (a := residue76) (b := 225015605) (n := 32)
    part76 (by decide +kernel) (by decide +kernel)
  rw [show prefix76 * 2 ^ (32 : Nat) + 225015605 = prefix77 from by decide +kernel] at result
  exact result

private def prefix78 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (32 : Nat))
private def residue78 : Nat := 0x4788d15199d0e30ef049639a837f6dcd0f574b0963cb6b081c77214e2d0fd05650af124ecd5cc05086a7eeac771ea7115833952a975221c6c638287b7c05ada4890e6e5d9fd1d65b8fc9faacbf0e23828b8d37f1a21b68be5de006122b2e2cd0f20c19f88cf4b8e6e8c2fe0ec13609fd0ae825717c10837f612628e42175b795562b03759d60a343c439e48319095a5253526f95d76bd508a335168dbc0a85104db369f56c6b9630af4c8b2308a056f5780528ded6b862d495dabcb0c00bf2b956b78adbf54b6ef40a84d82bd54dc605a68daf951a39683f2f0139da2adccdd6e9254a95d3d2aefc29cc74c62868974d088b1007d3bb2e9e146ef6a02f8c433b3accb774c59fcc3bc148da16ae87ed16ff63006411d654cbd935e70afd0860c8d042c3635d5367a02097c9cb824f478f33cb762e834129ffd5bd9cf51735053e0dd3a4892b76683a3bdffad7b5f325080e14a2bbf00542dfe2a03ae8135f8bfb81ff19b167759e1ba1c79dedeacb6ff0bf5d347dca6ccf8e8d9d163a13f826be
private theorem part78 : 2 ^ prefix78 % Spec.Ffdh.modp3072Prime = residue78 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue78)
    (e := prefix77) (a := residue77) (b := 4170710275) (n := 32)
    part77 (by decide +kernel) (by decide +kernel)
  rw [show prefix77 * 2 ^ (32 : Nat) + 4170710275 = prefix78 from by decide +kernel] at result
  exact result

private def prefix79 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (0 : Nat))
private def residue79 : Nat := 0xaa18b7c2f14dff6504324ea88b8f005fdc25a67e9f917d0cdf2cf10f739a0727e830d5fa0c8629fda94d6fee5807450974362f411b7048e94b0ba40d1b2905dd0b3e288bddce5daea61cc47abf4c83d670ac59fa8a25355520e29ffc0e6ec333a247690911be09dc7374c57f55a8ac698507d6ba7a1df59a022f56e6313194d3e0a7ced3dba460be41ff8de80d79eb40e5b1331b2a36c3d0a6ff45ebcf337ae4d6bc4f24caf9d67a9b5a754c39ded0dc6315f70930e2784c3e6df0c958c9f843ddfdcef640bbdeafe09702be62ab630f561c48167d742b01f0767783b0bd9baf2dd4fc759599c951aeb7f5678cbc2ea4bd2c27344b448d41e05f6ebcb92b6098b22316df0ef0bf25ab3d37600342026ea525e848da118b2b2ba9e64a06f87e56dcbd53bb3fa962063be262fd1ccc5d068813e10dda2f8a8b01f9acca51a68c249cadd566e725a07dc00aeee109f4633dd295bb7e320c097fd7a7ad4748704eb76aacad32c57c920d03e3272468f2014466780f662378a5a1cae6b77163937630
private theorem part79 : 2 ^ prefix79 % Spec.Ffdh.modp3072Prime = residue79 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue79)
    (e := prefix78) (a := residue78) (b := 1824850994) (n := 32)
    part78 (by decide +kernel) (by decide +kernel)
  rw [show prefix78 * 2 ^ (32 : Nat) + 1824850994 = prefix79 from by decide +kernel] at result
  exact result

private def prefix80 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (96 : Nat))
private def residue80 : Nat := 0xa1219a1060e3ee612b75d8a7d85d02a296d51847ac752f045e44dc937d0831b8b981bcf793a28cc0e688e000c3c4649847d8f0a4dbb4d3ee7b07f8717d5a02de4ad3205f743d8a4e99465497d06e31aa0300fa49f4fbb5e808e5104ee92f9d6a2d509a27461445e30924e3c8ea569efed1732f9aebd983279eb55c60f644d86c9fedf4dda786e4a78a74008439e53c6fd1320da4e9947eb7690472db2374d7da3a925c4ee824b67bb99160d704e97f3bd1df073487730ec0a955dc58c8ec171024648f936846e1b6bca58075916413e4a8412d21c473f1d332d954110fec2aa078c1072c17f224152b513efcdbb956e681d44adaeb9a06fdf1dbdc55bbf0562df42ae18732de450d44ed6d53a1f16cd111a5a49f1c717bfe34255a96a7c7e284ca0598a04776ce67497486d60475cb9c8c92301b2eebc56ad35299c104b384dc82370fdbf322d5ad0b041ae3aa5f4137b8602b1316e8d4b8231b98828614225a4534af48f2cbd47a00a65a32fa58b926e447cf9e6b6636224d82dc63c6801891
private theorem part80 : 2 ^ prefix80 % Spec.Ffdh.modp3072Prime = residue80 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue80)
    (e := prefix79) (a := residue79) (b := 1815806265) (n := 32)
    part79 (by decide +kernel) (by decide +kernel)
  rw [show prefix79 * 2 ^ (32 : Nat) + 1815806265 = prefix80 from by decide +kernel] at result
  exact result

private def prefix81 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (64 : Nat))
private def residue81 : Nat := 0xddb2c38cb4b8cb4ed521e9b770c942dce88f211f110f5dfc053896c0c2c75c6cbcf99a636e88f4835dfb5a28213329bf2dfada61cbb8b7af526703452534321b7bb71f69cb6bb8b30c00a9c1dfea0a4a75cdba6f0138d576e70088f820e52d7d7fc5c357759d9ae417d55b393ecc9c04aa42491e8c8cabe057c2f4276d590244f4ad346b2b166ba3034e5e5fcc5b16ec1859c28f3f87ce3997fa7952ee2bdfb55080a191992c20d5164a7965b0320e24c664cdbba96b4c74517c48c06370709e703e89c3734b1a71ee07da4a6159557d89b2dcc41d4cf11d123473fbf0bfa60a7dd16b3359ef7681e57b1475816e8120ab73c09c65c9861bbc8bc2793c3b9040583666ba231cbc4f1522f190a77617cead17ea882085de5b9a01d0d6934e953a30235d18fde14adad03ecbab0176b5892b160f1be7788d95d5ad7f7e69f5f4f28541002f63669d19ed632efe6f71fcd559675758c60b6e1cbc09d1a11710537d081ca11f53a52ef718a736681da3ba4bbf6b8e8a5b7c14d8a73b068e9b05a187
private theorem part81 : 2 ^ prefix81 % Spec.Ffdh.modp3072Prime = residue81 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue81)
    (e := prefix80) (a := residue80) (b := 2674144562) (n := 32)
    part80 (by decide +kernel) (by decide +kernel)
  rw [show prefix80 * 2 ^ (32 : Nat) + 2674144562 = prefix81 from by decide +kernel] at result
  exact result

private def prefix82 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (32 : Nat))
private def residue82 : Nat := 0xa3b7d140ab652baa92aec4c52f420076ca1d924c8ef400e31025ac117d53564a765acc7e5436764b22ad7b1269052c986ed0eba0a47f24753598c02babf1897dfc9a4c9472b242a6a40939d4b8653e519bc11aff28003caa40105bce8b1a252c5fb8d101d89c3b5fb6b095666e69d5b14b7ca7af7f9b219edb35b238a1edd95585670e972dc1b851a1cafaf51d49a34124f3e707a6dd9ccc4d086e5d7d2dc058c1970981529bd468e03a841dad9801fbfa547b9d06a18751ca79752b102d2636d86a8d18fe6ccac6d1e4c8fedcc345fc649a5a54889ea9965fdba2c036d22df56088db339b3d566a0d3511bab27b34265329975cf4c03b9f294c756c19338f13e1af44bb3ec2ffa7c07ec593c2280d46d3ed3e7d116d48c15024fbb029b6624b7dac5d4a423f91c5e7f7e5bb704b58ff1c347b1db804d6362afd8a0b4058c4e4b5bbe4e5107e7a02e8440b566310717121826e21fd62e588476e48bf77c1d495a2376cc2712d224633d22e9fb4e187e6d2ce6b64f126e9ad4e314871fc4cdb0f
private theorem part82 : 2 ^ prefix82 % Spec.Ffdh.modp3072Prime = residue82 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue82)
    (e := prefix81) (a := residue81) (b := 688887180) (n := 32)
    part81 (by decide +kernel) (by decide +kernel)
  rw [show prefix81 * 2 ^ (32 : Nat) + 688887180 = prefix82 from by decide +kernel] at result
  exact result

private def prefix83 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (0 : Nat))
private def residue83 : Nat := 0x835ac5be010297c6166a6882663a7318c1a187b9c4bb5792f959a98a53ec16bd2ed3067ec6afb02aed2740fb3b23d74a6674e1a83c3b8174eeedd7c08ca868d221d6ccfd6317595bdebd19ffd5cf564969c8ac7c6c791b6e967065cd24694987a253788314cdfe3be2aa56bed9bdd5aa90ea3221b167ab26c450c58ae2c5ddfdc933e4811d127ff6f1e58090a5623e2ea23aa9bffb6d6d1145ab805e3cbdf755bd1e4879e477e1a1129c0089f991629dd5d8057daab60a95edcac0f90002fdc12671bdc6650a267f730ea6f8c6b60d5c797a7ebae845d24f080e0ac4e5874d1040d3eba480573113a96881ea6eb4629b3780507e3749488a2918b7cdaeb7c1533c82e5898f9277fc1bace09e9067d969dbbda6fd921d176c6139cc0174d0f24d37e75e99e18866ffc9d8af0c08b135b8a741c8703bff29538e97614341ae2578ca94e2275846d92813acecc2fde8aee3e58764f305b95635af43d9b48f10b554cb5a20c11fb8e9771c4620ac123b0df35172dbc1ceb5fd0fae0a0551338a77b4
private theorem part83 : 2 ^ prefix83 % Spec.Ffdh.modp3072Prime = residue83 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue83)
    (e := prefix82) (a := residue82) (b := 196972550) (n := 32)
    part82 (by decide +kernel) (by decide +kernel)
  rw [show prefix82 * 2 ^ (32 : Nat) + 196972550 = prefix83 from by decide +kernel] at result
  exact result

private def prefix84 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (96 : Nat))
private def residue84 : Nat := 0x41555f88ca01fe4e79048849ddb20b80db66a8251e068ff6c580b98ee86e8d7e3a7ce629cf40b8f8a29f04ae1b7799a95120d0dfdee5f7f2b54dfc2dce6adca7208cb0585b2c9ceb255e0c8c3194e96604ecb2303c460c86acf15817fea6220b66ad0bb48b0bf40cf7f5bafc26ca5bdc053614e963def49d07af5f98b89b1ba4425dc50c1728994f69addcd724753bf47abdc0d8bb71268019832b4415243484ee87bb9649ca0b816ab92ff4fe155f7887b5b60b08e9e4ae3e266ab5c64395e7c2a549f21661a01552affe4edb2c7d811d3e804a06aa19ade17e0e4b61b341be83d8f7a61522a9c8e3cd5ccacc58b0927f3eabe9e8b498f58d7257326eb8eab35a19947011abb0d3e6a0aefa14a9cf59e33ddc3e7fa4b0e446428ed4802af51dd02070c996780b63fd35899d29ae814f2e146228c72487d3ec2014c93d260386e94a01dd914bd0f794ceb266263bda1d1d0ca0cc60f763cb6ba30ecf0608c2132c17701005771894a319c14291c3da68258cd018031904b323810519565ebab0
private theorem part84 : 2 ^ prefix84 % Spec.Ffdh.modp3072Prime = residue84 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue84)
    (e := prefix83) (a := residue83) (b := 1576045483) (n := 32)
    part83 (by decide +kernel) (by decide +kernel)
  rw [show prefix83 * 2 ^ (32 : Nat) + 1576045483 = prefix84 from by decide +kernel] at result
  exact result

private def prefix85 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (64 : Nat))
private def residue85 : Nat := 0xb6e1fb936d8d1a50879f879052912fdb237daaa7ba0029ce4c5cf8f2ca6d719c407e8822942ced3265b7cf7c88685c052f11bb26c597e70766a1475db634687d651905f7818870ff0e6d47510e977588cd46fe60ed027b2a40c1d0f9c5e42e94abfa97af90cb7d5ff4b11a77e42a34aaf5c8c660398a32af496a6eff790dd149ff6ff116a3ba5e5195f3f010226ce5754f4d579cd56f20aa48889279028d9228197046eb19b032de8ec95ca10140f79e42d30ae66c8ee5756b9a0cb110a9cd10f629ddb974b933f179710caf5ef89d1172d8cb61513ac2af665387776e0cb6d27cbccad2b4e84c117af7fd3995104e6f5b99f1a3c76548755565b43bf3db816fd45ade1af356c32c7edc3d7ea63dfcb4dc896527330304b0942f444eec8b89638070a85b1ce600453a0f0a07f196b8c1831aa80f078e38a385326923963121d5b9e22747fe94b3c9980719b048e6793931b27bf26fd4fb85f6b641cc75bdd15e653f6a08b934b62074ec1577676b9560c499a456e4d0f72563c38d4bc09442aa
private theorem part85 : 2 ^ prefix85 % Spec.Ffdh.modp3072Prime = residue85 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue85)
    (e := prefix84) (a := residue84) (b := 3174084278) (n := 32)
    part84 (by decide +kernel) (by decide +kernel)
  rw [show prefix84 * 2 ^ (32 : Nat) + 3174084278 = prefix85 from by decide +kernel] at result
  exact result

private def prefix86 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (32 : Nat))
private def residue86 : Nat := 0x727681ee686c32db3e37ae77459360c4b97012981aee1248209413b78f4b845230df216f06a3f32d61edff20005a2e7bdbb09ed47886f4bccdd16b92307d2386c29d7bcff0ce1fbba751322249a97912e9345d274457a3d64e92888bfff04c48a9ab1dacf98ba72d713dca4de3746937a0470618dc57db84734a295b0e17dbedf67cc9be706c108410bda888bece0d8d2569919a31c3fbfaadb738115653d3992a536d8d2864164c74c15f25066190541ae39c4350b392a576b27262bf7d70defc34a157822dc34ff40ea4b8d35b042ea4ae674334dbb184e3f6319daa537193880c1e7e37013892b56611380bd7f4c05896d1b2521e680562ba8f2d9637be40846077d1b1e606c44db3f11e03b8cd78948547a1f30d5fdedbc7d9ffdc1192e8033b90ecae8ff3f1febc8ba08efe4eddc3393149f6e551c86c04e9375ad932306c36d677fc032dbc51000df56eb41e2fb9730151bf72669988076b9eb57ab674f69f1f8cfbded57bd39cd2b69152c57ad9fa37643f6fe51c4606447beed9c2b8
private theorem part86 : 2 ^ prefix86 % Spec.Ffdh.modp3072Prime = residue86 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue86)
    (e := prefix85) (a := residue85) (b := 998556768) (n := 32)
    part85 (by decide +kernel) (by decide +kernel)
  rw [show prefix85 * 2 ^ (32 : Nat) + 998556768 = prefix86 from by decide +kernel] at result
  exact result

private def prefix87 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (0 : Nat))
private def residue87 : Nat := 0x91848ec3c884db25636e0115ae6a82ec0c67aa635619800b8d25865c23612b66f4c8fcae8cc9143cd5a4dc8a5f2473d8c2d20fb9b68036c4d626f9d63cbd4ff80ef9fc05621a3272e128d61275767c0c6be97f1a927f96ef2eec52a7301e58741ad9080ced72b6c5728f39a9f7067d1993d3c0927c9dd6c428e6295f507393080086ed7889689195caa3dc2e77afa0fc6bcafd3c90aaa4f5602874d2531bfc10b66ba5d13c8940141207fea9732dd74b407e2b54c82728aa0a254d160dc679613f8adbcb475b76e56834f2151d12a55985f317f443a48a74c89bfbdcae6286c573b552e3e11679c633959784f9913ce0670b2cfdf2c6b210976a42127d33828e4b366ca25926e21a1e1c43f914038125845f42b12d9bf2fea8053c08f80fe3987c7905699d866bf9c6b1cff7e9713d8b31524688a597269b6ea8ebbb7671bd68ed013cb2160153dfd7b3a2a2dfb77f4b9e2618eb707a0812ecc528f7017c65788a12a27b628d2666d36f3943eb11a2d5c92aedea179712ccc073264eece685c
private theorem part87 : 2 ^ prefix87 % Spec.Ffdh.modp3072Prime = residue87 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue87)
    (e := prefix86) (a := residue86) (b := 1567400817) (n := 32)
    part86 (by decide +kernel) (by decide +kernel)
  rw [show prefix86 * 2 ^ (32 : Nat) + 1567400817 = prefix87 from by decide +kernel] at result
  exact result

private def prefix88 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (96 : Nat))
private def residue88 : Nat := 0x4feed51e1113e7cc54c768b80ba8af3a8cc33044fa6eb485543ea5d27e41a07c68adb4df7fd038c3dc21c89ea32cc1751df442411e137c1702ae96d186491e8309dd3adece76d6391dc0489565c06cc84928f0ff5fe59d25492ce9fcef164454fe44b05bf8b37c6fdc33b37290feafd5f7bffe992177aeae71a64a7bc3309774dffd1fe2b934785cd44775e01321f3d74832b421305811f1d7a43253696e058cbd585b8aebe73474c29c17c23a967f7d9b2d3873f933c5c053ee9fec367cfb86c33e72f356b24800f4ae8512deb19288d4b7b5103145a295df9aa6e6ec02dff1cc5425fd4d2722c289dbbb237640661e3416d64cb1cbbbe8e14db3f37aaf5ef9132586e1341b7ae5c9d487797b1269275a9dd60bce5e6363ffd21b6cda5e90c22bfbf6b9af66dccd2a63e59662cc7ca62956604f620b70c861f3ead5549eb87393206ee88a3fedcc16526d093d57f8b3960d50a76610a26430642bcaecb1aa154ff936013653c7c78ffa04ca55ab4539980fec36c6ebc1d958c46fce0b7e8bca
private theorem part88 : 2 ^ prefix88 % Spec.Ffdh.modp3072Prime = residue88 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue88)
    (e := prefix87) (a := residue87) (b := 74524624) (n := 32)
    part87 (by decide +kernel) (by decide +kernel)
  rw [show prefix87 * 2 ^ (32 : Nat) + 74524624 = prefix88 from by decide +kernel] at result
  exact result

private def prefix89 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (64 : Nat))
private def residue89 : Nat := 0x222ea5775d6cf2573e1ac08831b510c58e9f3968bb1d34b010d46d029fc7c94d40c81b13d9e76eaae869aa420bce7d5c11b2ae0b552175ec1baf0b722564a7c427fbb8a76d993176bf3cb10d2fb492b5baeb1cfc418b57842f8c4c7a70f0ba33e6af84449ec25f3605baba9542c9fba964b99568341a7fa174ce5d206a2f5bf74947bd3752514b93b47ce58f09faeac0307fe14edb85c31eca4f216fd589af9332ca7d651376bcc138ed2e8a662321975b30e2f797d390dd1046d673b6f7849af91432649761fbc6dc7036768f69811b580684c2b8ff0b5117e1e7abc547a6bfe7d953f28f87f890c7c0692bf9f27ca438af4882a9896b3ebc35e18142c42fd8ea27af47b06e32511b55b7cc87c7f2e4dc273073e58cc71d9975ef7031ec08b275889a64499fd6f708f66431bfc8c88bf97eb08e31e422f5d10976ad48403f9087fe8dbde48390f43d3dcbecf845057f8d5196295c644a5807f1b9b816f796ba7529c1e98923317a0e98e2a7cbc864e94732a4824d37ae523293772f4c1f08df
private theorem part89 : 2 ^ prefix89 % Spec.Ffdh.modp3072Prime = residue89 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue89)
    (e := prefix88) (a := residue88) (b := 980604312) (n := 32)
    part88 (by decide +kernel) (by decide +kernel)
  rw [show prefix88 * 2 ^ (32 : Nat) + 980604312 = prefix89 from by decide +kernel] at result
  exact result

private def prefix90 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (32 : Nat))
private def residue90 : Nat := 0x717c42ef215fc64e6f77bcc34b8544e431a3c562b519cc62ccfaa407ec2ce9f8820253bd2f2ed0ae470e7816729c5ee7a4cec22dded867aa2fed2e46d5fd6f8bb286caf0b56e9c10e90c4c2e5c18710955e4300bb2824238b2d6a151d1b2a39be201c40434d97b606045ffe44d05788156f189d8caa32c4e600260a367ab30250e051afa517b969f092979a3feb7acdd64b263bacac296fa9b8e1a0692e407c036e2876bfcff016d061f8e79b8ba665230a3a5a353e1d849bd6b4fc73d0bd58455348559e488b7c61e5279efb8c1debfaf70973cf987b9dd896e9ad6b9df65aff34b61fa74a9f1686c5819431fa12af5d8556f92ae0f00685945c6ea187106be09861777e9592e0ff728e1005dc2bed13c2f54676f0eca469af561df66923299fc2cfa87c19d3cb3ddbcb186594f381e97d8810c79975eb6defe9bafed2aed15d41c221d81b8464f9cd8d4c937493a5cd2300ef1b424f989408996cff833a8ba33f8a98a8d74efb31d6f1635857c7df72e4b44762568b28f00b12239627bdea
private theorem part90 : 2 ^ prefix90 % Spec.Ffdh.modp3072Prime = residue90 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue90)
    (e := prefix89) (a := residue89) (b := 2716708350) (n := 32)
    part89 (by decide +kernel) (by decide +kernel)
  rw [show prefix89 * 2 ^ (32 : Nat) + 2716708350 = prefix90 from by decide +kernel] at result
  exact result

private def prefix91 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (0 : Nat))
private def residue91 : Nat := 0x9bda5821b845f23cf8714ebceeae8dda4ae89ab6f4a25fa052bea1f73d1632b119075402be214222616e099b86c1cc9940fb0304ffd0bc7db13861d5b7bd0f8ab6f02ddcd550110a63eb8f6a4f1d014e80f7afc57e926a2d2f7bbf428881a359b1341c0073e2b70f91ae7a863e3b9be6106d4c215f0224d64439792175e0a020a9356dfad0012ec00729cc319586c74a4fd218edd3b4cfd816d2a5286a67fb6fa32313d3bddb33f833d2d69856813fa5d8b08f62be286a829c165b56ee35c08d65c162dabcbdd537bba9146e9f49dc1ff47ef75c9f16f27275c6ef2cc5797453db83302de8eaa2455dc6a1c36aac4748128c4b98d804355ebb16ba27a5067d1674643db59d9df9fbf2d7327d2a5fecc707eb413a1f7df2e060d47b94a86aa4e57b6f8d690f7eab0307db647c6c0a1351b5ae4e066d54a70d0b72ca493ebf91bad58186d850947d9ca49df6fbe77517b175d86a9cc0949bf156855a6ce419734063b3aa30a667a9f0973dbbe7f7b051930421bca639c3738eec7234e196f90ed6
private theorem part91 : 2 ^ prefix91 % Spec.Ffdh.modp3072Prime = residue91 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue91)
    (e := prefix90) (a := residue90) (b := 1887340615) (n := 32)
    part90 (by decide +kernel) (by decide +kernel)
  rw [show prefix90 * 2 ^ (32 : Nat) + 1887340615 = prefix91 from by decide +kernel] at result
  exact result

private def prefix92 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (96 : Nat))
private def residue92 : Nat := 0x52917b508836802f9d0436ffeb91d24cf5390bfd6afb8ff13bbba7ad0e711f81265deaa93f213f314ce8a744eb662bdfc2b9279758c7387cd02e4df05eebc1354172821e2b8dfd4113525142987ceed9579b94f56b3e829b9e2f683e4bbe2dd139f03ab4ca79e4801eff90c5847a4cf43d75a149fdde64ee8f2259f2421c7ad7805adad706e35bb0a014df83019227abbd8ee32ccf677b12bcdecc32933f68ea89758f206b6bd381b1da76acddd71640c3dc27aa9989af5408c306cee644bfe89a9905e1d67fc74122d3019dc9fa1e0b7cb793073b529834749e850ecc39caf06a573f56665d898d7f88af101b904482681cb7f083755f7de80bb66863dbc6efa730d2d7d47fdfd5ac1a6fe4df56f7681442ad36675e2d9c38186918f471b268257ab56076fdaf2b1fd9eb5c3967fe7743d94350245513303d11dce7f9f5a74722d155ec83d0a298eb9e71147855ef4dd6d8a0d15ddd1ca873bb48aae413d560129c12e9934f417c06a2fe00fa4cc66f3cd9a765617cb1952b1cbe6ce69e3899
private theorem part92 : 2 ^ prefix92 % Spec.Ffdh.modp3072Prime = residue92 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue92)
    (e := prefix91) (a := residue91) (b := 633432208) (n := 32)
    part91 (by decide +kernel) (by decide +kernel)
  rw [show prefix91 * 2 ^ (32 : Nat) + 633432208 = prefix92 from by decide +kernel] at result
  exact result

private def prefix93 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (64 : Nat))
private def residue93 : Nat := 0xace9f266439845afccc3363236ec48f8bb6e2ba600ea4944d520b25e148020447b005458056b7f50121ac857b2effa59f4813b7e576cee31fe83e6b6688733766da4d6587c572d2f094ba8907cc04167132516ab227414eb292998dfce5bb61964f214137012e39d859738f83527a3b2a7ee3fa445f8adc73a09c93e16ee8dd0c4cab98b548cdec073114bf310d11aebaa56e4a8d14eeabf5a0ca293abb51f53df5535ee2337b59dac363de18437a28bd60da8c254d91ca498dc07c51740eeaf2dc3d9f8dbd48cb43628d51462f62314f60c2b1efb4e1fa09ce08bd8a6c46c403f9d7928d854dbeca9c89648867dca61f1522280af5eaa9709eb8d3c8ca9663aa11bcc8851c8d89fa6babd38d996c1e091f2cf01e3aa36dcde1a5535e4f80ad3da4c031a5dc41e749d958c98ae1294eff43bbf5e9145282c3b7821aa9913d48832c4de7497d9d0f13d206725113c13453218f3b07e3c41760359e345e8c860f14d0aef98344dbd52bac87037a89ef184dec131da1d68d836039e07e1aaf54590
private theorem part93 : 2 ^ prefix93 % Spec.Ffdh.modp3072Prime = residue93 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue93)
    (e := prefix92) (a := residue92) (b := 1419602277) (n := 32)
    part92 (by decide +kernel) (by decide +kernel)
  rw [show prefix92 * 2 ^ (32 : Nat) + 1419602277 = prefix93 from by decide +kernel] at result
  exact result

private def prefix94 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (32 : Nat))
private def residue94 : Nat := 0xeabf18200d4012cd170744c5eb6a1de1cd0d941e1fbd3dcb2a4037faf237286773854fac5796cfb1d0cc0c0f9ad06457cbae94c1dd5b371a6d8f611d2c5fc2d0fb45a55e52d3b60bf2cfba40053c7b1d6414dfb9fa3f291aa36350578c49f8e1dce859672ce5725f10ace72e17b1b2a51383bd0352fc7285ea05e90a2d62a3ec70c27b7bf70f8559f1774d22fa743eea410139de99b4f040a24ec46aafac7afe19455c07656edb825bb854b10b92d87afeb9fdb3d4f7258872ee2bf1f9c1f4010ff537e3893910bd2e27d84f9df2dcf1055a7e02c0b8afc9d0045f096cf927a8877f058fbcf48b0d07409250d450032273b67a688bb958522727b3d8833ac3784fa3de94291e6f1be69565a67b89a75a08d1c36660642261ff348ce059c5f6f5086fb14f3aa42d923e92cf5b02584171aa065a533695367ed698ec1b44b21dad22f2bdcad91016228199cb55f79f6edafa03460b540eca7287ec5bb463028ce315d54bb730267a9335bc4d4397c405a10cfb7831e8e7165e60db45a2ca622cd
private theorem part94 : 2 ^ prefix94 % Spec.Ffdh.modp3072Prime = residue94 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue94)
    (e := prefix93) (a := residue93) (b := 2147483647) (n := 32)
    part93 (by decide +kernel) (by decide +kernel)
  rw [show prefix93 * 2 ^ (32 : Nat) + 2147483647 = prefix94 from by decide +kernel] at result
  exact result

private def prefix95 : Nat := ((Spec.Ffdh.modp3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (0 : Nat))
private def residue95 : Nat := 0x1
private theorem part95 : 2 ^ prefix95 % Spec.Ffdh.modp3072Prime = residue95 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp3072Prime) (r := residue95)
    (e := prefix94) (a := residue94) (b := 4294967295) (n := 32)
    part94 (by decide +kernel) (by decide +kernel)
  rw [show prefix94 * 2 ^ (32 : Nat) + 4294967295 = prefix95 from by decide +kernel] at result
  exact result

theorem subgroup : 2 ^ ((Spec.Ffdh.modp3072Prime - 1) / 2) % Spec.Ffdh.modp3072Prime = 1 := by
  rw [show (Spec.Ffdh.modp3072Prime - 1) / 2 = prefix95 from by decide +kernel]
  exact part95

end VG.Proof.Ffdh.VettedValidation.Modp3072
