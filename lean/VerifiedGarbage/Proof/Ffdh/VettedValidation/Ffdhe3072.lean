module

public import VerifiedGarbage.Spec.Ffdh.VettedGroups
public import VerifiedGarbage.Proof.Ffdh.VettedValidation.Power

/-! Kernel-checked binary-power certificate for the published ffdhe3072 parameters.
Each small block checks its arithmetic; the shared append theorem composes the blocks. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation.Ffdhe3072

open VG.Proof.Ffdh.VettedValidation

private theorem initial : 2 ^ (0 : Nat) % Spec.Ffdh.ffdhe3072Prime = 1 := by decide +kernel

private def prefix0 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (23 : Nat) * 2 ^ (96 : Nat))
private def residue0 : Nat := 0x9b6d351ca1ef2514fdfde7cd579d682b68b329e1ff301cc6cd5040ce606627e4d402b4031d09692c213817e8896dc6f16b702cc2635499b4aca04cf00afd77c1cb31070099af9c896e094d170b599c19501026113464d53a4c0dae997181269c20d59cba5474c6cb3f6fc1e8b9f9f38241459e51d672d168bc3b35d9a3de4993ae8e8b69f866305df94eb3b2df07d2dc2260f74394ff51ce096cf7b86224f98fdc550b4d68a48339171aa0a590314e638dea25ac207bf2cd2b9ad203e1b3dc9183129c6bd39a56d16cecec1ed85e324a926219225bb64f290be0ec17501411a87dc0b5ab0397a94a4a7c8c6c2f056a5324fc784bfa08af5c7cda5ad97da9c3ac300b0ef2dfa121b44fbbd5c105045e7be7a1aeee7fd709cb3fdcc7227c284652c79facb50ae8a427416ed4070c4551d6c0fcaf78ecc63a568e949a837beae4452f3763323c2ac63e34d14686d77ec183c07d6706a124697b71fe64aa75fb729d7bd78e643fdd63fbb225058f896f0140d45ace818fabf14796a6f2a93d18a065
private theorem part0 : 2 ^ prefix0 % Spec.Ffdh.ffdhe3072Prime = residue0 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue0)
    (e := 0) (a := 1) (b := 2147483647) (n := 31)
    initial (by decide +kernel) (by decide +kernel)
  rw [show 0 * 2 ^ (31 : Nat) + 2147483647 = prefix0 from by decide +kernel] at result
  exact result

private def prefix1 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (23 : Nat) * 2 ^ (64 : Nat))
private def residue1 : Nat := 0xcab59777634dc9a45bb5204c542e6f01f1373275b7074f0572d99d2410ac1b9f56d9dc766b16eccd332bd73c01a1afef51ead7aa48a528cbae7eecf5bbb763e16edeafbcaa00ec2fc4881f240f62c408fce2a617b5d475d9b6e221b0ddec06b3d5d3b28cf16e6a10c051c9709dda9902b350a05abfae87653e4a037332b3d3402bf6aba3e7c26f9c446fd9103731e582894d887aff7fcc3e5719faecf561c4515e24dec1d42d9d465851329ba67e1bc0c9e032d2cd1397f657f931d023ab73c6dd41a8a1028c65ea71443fbe628ea7377a90fca20949f1bfb904e97448a89d437c59f8d010df67bec6db80aecb16f852aa0781398de4e5667c49e0ab969e1b0a9a230130338a8706d1d9910767ce9a483787ae64802738a6976f866b334a7b133f7c0c8e29cb1c3eb3fe7168bd4d9e1781b4f9b8ee3ef24b192b817c4a079c32a9bd034605fd84cb6ca9aba56ca0e2df203257367c868772317d132fe7f95ccde3cad3db007d9020764d5a6af7c5040553fdffc1382755cadfe399a61259bb43
private theorem part1 : 2 ^ prefix1 % Spec.Ffdh.ffdhe3072Prime = residue1 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue1)
    (e := prefix0) (a := residue0) (b := 4294967295) (n := 32)
    part0 (by decide +kernel) (by decide +kernel)
  rw [show prefix0 * 2 ^ (32 : Nat) + 4294967295 = prefix1 from by decide +kernel] at result
  exact result

private def prefix2 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (23 : Nat) * 2 ^ (32 : Nat))
private def residue2 : Nat := 0x65e9698fa5f363db227fa1ed9aa39d0eb99e597a2d1b8c199b4fcc6db3d1308f4b947ecc3d9867331b82640e7e0c9b41a8a365996513b6ae935dc4de79476e5d76bd0685d97e76bc4d01c22e943db50d30293e80a5a4414f4b5950f3dd443916c47a245fa75ce49f57925c5b1be4d0f62eae761ff0e3be1855d5037b6300b42962d78155e18e8e55a49712681a57481b899817085c38db1fac815c2bc71a6de208c928c3ee7c6eb4c120d5c9247c341814a09966a36f4fbfe07b63ba3d2c9bbc193e43c6de379d3f1f82ad8faf3bde820c6e27c105d382415235fbc94ae7acc148a4f6628db0e048d37b183e9b7b3f379b5073298d6d703819a6a00846ad8cde10d6dd0c1b51dbeb17ff6bc286e432de11c0882df425d540052f8ca6a74f394a4e3602523787652bd420382f808a6595024372c2886376556be6b5be9a0f64b64f93049a21d78fc028419de74272dbc2670a4ad7da76d28a3fe854aacb0d28408b841b81996f522ed7e9af067308ad082bc43b73a5ee54cbd2316deb0ea21b35
private theorem part2 : 2 ^ prefix2 % Spec.Ffdh.ffdhe3072Prime = residue2 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue2)
    (e := prefix1) (a := residue1) (b := 3606850092) (n := 32)
    part1 (by decide +kernel) (by decide +kernel)
  rw [show prefix1 * 2 ^ (32 : Nat) + 3606850092 = prefix2 from by decide +kernel] at result
  exact result

private def prefix3 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (23 : Nat) * 2 ^ (0 : Nat))
private def residue3 : Nat := 0x8ea3796b950b6e3f7deae858d3a348d78a57ce64d3ad977d1493d626a5ada1a739a0ef969adbb5eaa615c270bbdffae78e53fa7cd179bfef02f25ed19517577a088fae81e785b9470d150987b92dd92f2da01024e6fb13e3a0f4eb9e47ec464d2a4664061aa0e1318b59c358dc4754db0f12bbb822e79146753f95b610cde35a4797df9655cd1a93d7c87bbe2f0a076b3b9fb041dd682d3a85a6bbe031b43a4bf1adb437a86311270e6649eb4fe6227a2c98433796f3d0b6c0fb823e5185daa48d790731189abefd0699e72e8ade93ea04df2ad644435380d647cdba205b87a9f30bf6e07836ab1864d8e234af5ae8a9f363f409ad717210266c8634c3a87c126bceda60e4c0a9241e2acb155759f86c19ce0309f9aaff315f16f7811e1763d616f77426c49e0efe43353a89a216e86b2a05c66e513a363d6d48ce22886871e053e6e470ae3bd914ba5acc4820da37029d231cf033f783f6b6071fa2c66d87300a41b9bb86ba077e81b1128caf029242d4d8acf04541194c2ab7bb739bf16cd9
private theorem part3 : 2 ^ prefix3 % Spec.Ffdh.ffdhe3072Prime = residue3 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue3)
    (e := prefix2) (a := residue2) (b := 1365091661) (n := 32)
    part2 (by decide +kernel) (by decide +kernel)
  rw [show prefix2 * 2 ^ (32 : Nat) + 1365091661 = prefix3 from by decide +kernel] at result
  exact result

private def prefix4 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (22 : Nat) * 2 ^ (96 : Nat))
private def residue4 : Nat := 0xe7f3b87d6f720458f5c111da907a5cc6cfcf8cca929dbd415ba910c3d2bf2b7354f279c97990b117c921e5744a2493754ba0444ba0a3cff9d1686da0d81dd96eddb26962c12b2cb2e8f542bd97f9deb2398753d36bfb4c188a59f33c52e78ec5fc669f44a0f5f90bde03ee781a75b636d88a750267fbd7630a0f8b5698a6b89da3be9ed7f1a4aac7d69dd4548aa372dbb2666e8bd61dbc0f3b063e6879b086d3e78f6d6348190d43e03f1c0ae17357c90267d207150869f5380806485bb08f70e862dc5041c8987a06390979281e40b1a413aab9fb6209c8a3cf2286ccddfaa861638031ed5ce08676a39b0e9d59d1659368653b55042bdc28f25b9fb61453270bae8c05d1ac343bcc09544f8fb4ea369ad3aa41864239789d7179d2bcb2c0b245652e73af6937bc61ea005dc6dc1fe366ac80c797559ddd4d6669d0e6ae000718d3ce17d222cbd406163d4a7c50e786ca4f539f4bf466d9ce57c924a6d012248049175127d8d8e631c87ec4863033c7a25d1ec146c39d477e4a9bc782a610a4
private theorem part4 : 2 ^ prefix4 % Spec.Ffdh.ffdhe3072Prime = residue4 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue4)
    (e := prefix3) (a := residue3) (b := 1475226384) (n := 32)
    part3 (by decide +kernel) (by decide +kernel)
  rw [show prefix3 * 2 ^ (32 : Nat) + 1475226384 = prefix4 from by decide +kernel] at result
  exact result

private def prefix5 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (22 : Nat) * 2 ^ (64 : Nat))
private def residue5 : Nat := 0xae04addbc9321b8582c23f005e0798ef465fdf98fcf91c24f0edea71c4f7eec908051245d1dd08ffefe84f027a841b34ca5f90d89d47a1a843e354b1161352ffd48eadb886aaef584f04dbd75a968f58dd43f0e7f41c63bb72818e779f80d7b524be835694d9750bfeb02de4054b10b329a628250d4b09e7c7da05e33b4eb36b907a35e9e6e704ecd62d0aa0087229dfe771da56adc30aba16ebee9628a14d54597b8586e2ccd2b93f25992fd61360471139465a73bf96b3a9e953de4d5667ec063312dd1e744318fe239ad672e5ca0d64dc24bf967fd48b7765a31e3dc38953ca6ea18a49c5f497cd8ae4a57a90ca2399184b91babdfe701ae699453351bb2c8ab505417f48790a8a9e6c19b12e9ee1cf08c30552dc469c5d5f090d0c2c5f4fcc089c47362ce9433c13fd9fb9ba9aba3a48df36c0a77c008f72febefe5991e89d0c864970233415ae5b2768741eb97514f54f4013fc85b758a06ff1c428b4bb18b167500ae5dd7580870f08c6cb74e50bc2953fee895a364418d5cd0ccc3f81
private theorem part5 : 2 ^ prefix5 % Spec.Ffdh.ffdhe3072Prime = residue5 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue5)
    (e := prefix4) (a := residue4) (b := 329162360) (n := 32)
    part4 (by decide +kernel) (by decide +kernel)
  rw [show prefix4 * 2 ^ (32 : Nat) + 329162360 = prefix5 from by decide +kernel] at result
  exact result

private def prefix6 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (22 : Nat) * 2 ^ (32 : Nat))
private def residue6 : Nat := 0x75b46ac85e3e98aff076bf9d796cc50f9a9bd05d2d9003d09a10fb91260ec2024a173b9630797d3f70aa1ee323c6771fb07c674602e0428dbde76cd325410048d750b81366d334882048141743a58a2934d93cc1ac78d2a5409ef306905997902cd6cf2d49347d51f9ef7913a19eab380ccfeb7e27afe9d755a41b28fa25c7682f9fea927b84c628e2dbbd5d2049c10ecfc298aa95486a0906c55d67f39cc86513e483333d274256b7f0e56b5bff8f74f30d3a0b98be7ad8da44271c80fadbeb6a1fadf7066e3e03b651bb4469a1d46f92e35d981230ace7148eeb1822b2e1f4b2eb7d346fef377419189f9299c2330c98288526ddd2d090f95fa0e6138d43bc0c06da52884cd0f6f2e630955333154a86ab9604a945cf0ab92e478eb9ef8ea78c0e155dbb2995a23c6f2ec018d2f0cc416520a65586f631b92db3c0c09ee6c290950a022cb8e5873a789dec82f8ce6eac78cb59d5ef0d1a2bc216fa4cedb256e4c922d351b4eae8f1a5a312d60eed605e391038cc247bebc938331bddacaba7
private theorem part6 : 2 ^ prefix6 % Spec.Ffdh.ffdhe3072Prime = residue6 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue6)
    (e := prefix5) (a := residue5) (b := 3965510337) (n := 32)
    part5 (by decide +kernel) (by decide +kernel)
  rw [show prefix5 * 2 ^ (32 : Nat) + 3965510337 = prefix6 from by decide +kernel] at result
  exact result

private def prefix7 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (22 : Nat) * 2 ^ (0 : Nat))
private def residue7 : Nat := 0xe9f979d3f5b252088f964cbfcdbe45970fe3acb1968aed1bee20bb48f8d4dad96c3f1222ebfc976384bbbd8bfabe665ddee873e376ab8ba801efd887e032960c8c96bfdca40e49a77940b837fc92a53d7219d6ddfe4a3417e89d31dc65d1303d81e563b991802e7941a4bb97cc54b3898ecdd0b7452540fc18c32347e9335b5683a12c453aa1ce132a962ee96809335cbf01b1b13181223b05049fb6efa688002f85a654fcd502d7f7fdcf40c17c42dbce3cb87c87af0f3ec17c86d3ac996e71bc97fa0adc7d214cdb45988cab063c91c578df3a6475602ec5ffac6fe99dd4441728c66faeb3dbab4ef60cc8f8cbdc4e47895f0fe3c44455bcced326db5cae432312fe4e968418091053b39e0c23e53647536795f51e33c16f553cca3193ff63b3acabe4b0dda587b40cce23448fc7434286b4f98159bacb7131d8158fef61c34d082084f215601ccb3f4c52d177775c66883b93c7a4cb9cae08b525878ced1f6de33a3c89a53df2ea4652de3b66d37357a05bf7a9ee5f7772dd92abaff2b1dd
private theorem part7 : 2 ^ prefix7 % Spec.Ffdh.ffdhe3072Prime = residue7 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue7)
    (e := prefix6) (a := residue6) (b := 3877018442) (n := 32)
    part6 (by decide +kernel) (by decide +kernel)
  rw [show prefix6 * 2 ^ (32 : Nat) + 3877018442 = prefix7 from by decide +kernel] at result
  exact result

private def prefix8 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (21 : Nat) * 2 ^ (96 : Nat))
private def residue8 : Nat := 0x449a42c5da947a4cfddb3d205aa490a8ea3e3841608f3a7289996f46f5ab9b97a1ac2f5d678b97d1a99d20d26b46afcdd3a81086b8aaa64c275f5a21f913a878ff858336362eecd4a24abefb17df82ad7d16aa330031030689c6e4769c36463b2e4514f02346b2131bb910d6cfbec3d346378261764de5d422548414944f15540abf7a0d8632cf8182c3fc23ad38796e3ed82a84f55ee24038d31d6d3e204fbb223601c8c5ef9040846383e9ffe9a4e28bdb936dc19e19b2335c450106cac7338faf12113c3b88111f56875e3958f892fa2cae13e834eeea3f639570b046463376d730273012f4f754d5c12007f8cc509e1e135c73859f49f2b299f9e7a4e112973495af49adcfc508b417693c39842322429b1a48e440475401b2a194a8d98e5eae14dcd8817465a1a6b9cb5173048a9c6e2a232984a921c7190a0993b0484e6003690977100cd61e1355f6e38e8a6415894706fc2752110d5722f7ff640307b1c7c312860227fcf2e519a108ed53b30e22cd951d24e4aa7fce190ceab386d9
private theorem part8 : 2 ^ prefix8 % Spec.Ffdh.ffdhe3072Prime = residue8 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue8)
    (e := prefix7) (a := residue7) (b := 3572538144) (n := 32)
    part7 (by decide +kernel) (by decide +kernel)
  rw [show prefix7 * 2 ^ (32 : Nat) + 3572538144 = prefix8 from by decide +kernel] at result
  exact result

private def prefix9 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (21 : Nat) * 2 ^ (64 : Nat))
private def residue9 : Nat := 0xf5f4ba61f33c443a2dece2909faab04084099d466ed845228e4a144207cf3b9608fc5a64f2a7d72943353bc972cc18f37f90b53b8477242dc1f4516c79ed63a3c7e39cf144775220ab001a288f16ed54ca4ad03a32ed7d8519f0634cd1343e380af600bf6f04603953819132e02211fcb2ed751c01f8e0d68474e7b49bddd144f1ad27d68fe6b890451546241873519127977daf12f8b753afa68ddbc094416b0d5297fd372935103b72da0bf5842451b43711d1a558b376abcc89f8855a4ff72ce3de7649cc30b2ecf3592388c2b93213187fc7466b6f7b4c1fd3257f807764bb80724c2d8af56be0d1eef1f79a03fb858a1abfa684ef575ff12a679f8ab6aaa57bb5ebd04ca2adbb2cc030144ca384721dc9dc199225530e5f50dafffa20b0c21310802e347d0b8180cfc2c87f37a77b14ec061dbb0bf69a87ef06811593624833d08dff69275140825aeffbf267cdcfcaf8725ef0497f32751bbe3c23f77b5692817f7c01bca6c839d1ffbc477116c2b532b17386314147bcb4a45e7394e5
private theorem part9 : 2 ^ prefix9 % Spec.Ffdh.ffdhe3072Prime = residue9 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue9)
    (e := prefix8) (a := residue8) (b := 2318539261) (n := 32)
    part8 (by decide +kernel) (by decide +kernel)
  rw [show prefix8 * 2 ^ (32 : Nat) + 2318539261 = prefix9 from by decide +kernel] at result
  exact result

private def prefix10 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (21 : Nat) * 2 ^ (32 : Nat))
private def residue10 : Nat := 0x1b6bb0e92206b4f3079947c169782759d552c19d247be1aea397f7a7c5cd7e37f0e6cee41507d507c1afbac8403f4f72c2f22bc59c59a49e96d8cffecd66577305afce7defa025d6a47b53c2b8cab511e9819a31f3e81685cf219b18aafbaba16bea9db658f64fcd572681c2d3acb77e66ba85f9fc0e4682b2fae1557fac3aef22a3ddc6a4bd41422d8e048e14e2fd5123b5bf3f9494bf10f087970899e9656810ee17cbbfea6e8a2c71fcc677554efb28c946062f18b8fcbda72087528b4448836ff8c6c390885f95c29dca55c52bf7de0b23d495751e5895c9c4f488d48866dadcba512ca989f85e062a283cb63ad7e8b6be63cd8f63b000a50305df1941e746c1d6ca21fd057bf71da34351bc231ad0ee64715cb7d199cbcde1354eed1c34abcbcdfefe2be65b0e93c513e5b8afcb0672859e7646555213548d829cfa1055bdd1c95b447f8656049dca3371c3527b0459dbfc9d4a031b709fe53707b9ff4525bd77ccda6c69375abf9202cf3f9bb4fc698109a5eafad0a44e020908f46a66
private theorem part10 : 2 ^ prefix10 % Spec.Ffdh.ffdhe3072Prime = residue10 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue10)
    (e := prefix9) (a := residue9) (b := 3863596775) (n := 32)
    part9 (by decide +kernel) (by decide +kernel)
  rw [show prefix9 * 2 ^ (32 : Nat) + 3863596775 = prefix10 from by decide +kernel] at result
  exact result

private def prefix11 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (21 : Nat) * 2 ^ (0 : Nat))
private def residue11 : Nat := 0x11f7bcd42022bd5a4846dd3c60cedd7a83f303844228da362dfaedb0a2daac57e8ceb1fcb0dccc2e19b0bae5159ae85be260a113476cb678a1149b604851f2f356fbe29d315b5c89cc40b333b16a7e25bd08ac4ca83c144b66075facbbcec6270db4efe1fcb77f88ad02fba12a3ad710ae4dd0350c615a6d7c4897df0f00311f70c3002b2513f8960bce4b6dfb0768f220f64d2d8ac5759d488b830c772746d9bb01d3a6a6073590ae1f7d7dff812fefd924d5231bd6ea986a0277560061ac22e71ebb0ff4d597e1c90598f965fa83d36441e13d90936b6dc9a1dc2fccf2165db1e6eef193761e29b86c3cffd3951a7cf733708bdba86f66875b7d493dd880f22d9f5a68374cc90646067deccf23de1856e10f558459d896a634938b71a18f6ffe9bc44bcdcb9ea4ec15d0c4b7ff904b0ed64a3ee2cc480e951a5aba3196ca1b6e182eccf8441113ded3e97c1580295d2f962b03c50d8ab9542876f28aa6ef10b0a88faed81c1c378b1357e6e2da33a133b07560f5cec5d7cc01aa58637d6604
private theorem part11 : 2 ^ prefix11 % Spec.Ffdh.ffdhe3072Prime = residue11 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue11)
    (e := prefix10) (a := residue10) (b := 307076988) (n := 32)
    part10 (by decide +kernel) (by decide +kernel)
  rw [show prefix10 * 2 ^ (32 : Nat) + 307076988 = prefix11 from by decide +kernel] at result
  exact result

private def prefix12 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (20 : Nat) * 2 ^ (96 : Nat))
private def residue12 : Nat := 0x7e3a1a2adafdb3c8b4abaadf945b8f99f732012b4d2363648657a40a7fa71b07a079f729b00d412aaec7c4f6bea9eb6db62696911ab02b10cadc45468c6fa942cb0c61f38566f192d4a4f1fe1461f2e62c22d8bb1a09c765fbc24386bcbc9c5a8c3459aae587596cd9925cd1332fdc0056d2db620a7b693d818176fed7e033495727b5af413ee39fdbae3d6a847913e4a20d9f081965e90f4c48f5346a823ba184f1ad64d75740ea9dfa32c9aa10569bde6da6e7abe916385a1b1d340026ef8a44aa331804ed518a6cef6eaef06b4459e67d6a95c548269a7fc110d200f8a490aecd4c9cae08d93f68e367be282ce75364a7cf05bc7361eaea90e33b33dd22b333f462d560868ce2d26174bd9cb5c64e44f1157a13128a248e58b4f169541f39c8061af3a8f024764bf3868219f83f26218d89be9b684e7c8111abb59a4cc2c9d82a4b14d94dfa2dceee8ce0c01fce5d344e092dcb0eb3aec9eb0843e7e5e161c6b32107f7c74ec759a8506b3159fb72340369b224f328225a89c2e50207b24b
private theorem part12 : 2 ^ prefix12 % Spec.Ffdh.ffdhe3072Prime = residue12 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue12)
    (e := prefix11) (a := residue11) (b := 3197628849) (n := 32)
    part11 (by decide +kernel) (by decide +kernel)
  rw [show prefix11 * 2 ^ (32 : Nat) + 3197628849 = prefix12 from by decide +kernel] at result
  exact result

private def prefix13 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (20 : Nat) * 2 ^ (64 : Nat))
private def residue13 : Nat := 0xb5f9dbca8f404aae9adbb601f0cc4d625b39533747c71bd2dcfa47be4f8dc9595539511f635c9cb3d6da2d1e15065d5c31b5aef131c7e0e95c767966b35fd07d42604bd3704411a5b6eb603b7bbee7569ac214c2edaeb5c49a926854bdacafc05bfebb9c8df0a333bb7910373128efbf2adc1bb8fb078b0b6b9e557b08d969a20e286a0459ee444283fbfdf8d2f2f309d04df4212e11214b12a20e3f5837c2b9195114a9e7fed06b336e8f404952d27ad529a16d9d31f71adb626a6c1f539fce45624c4fdfe16a8d373ae90673ae0a1bcc8f976f1af39da74af6da2c148fc9b17ad1cd2cf5af52e3efb06a5defce3250a8a9fdf385ccb55fa11fcee1de0cb6911c9edcecd1cafb64f2e09fe8b73bbbbbceada3dd17b322d6534f8b9cf070490a4e56dd2931f640b0c76f5e7d2f0bead0eb9fa9b2bcd2ecb14cbf774f4414650147ed05e5fbf5d0063f55f25af5e27d8e04e4addafaff32cb9cbf2e8f39b7fe4e87f93485b8bdee1810638187f09de35a15a0f2b9239a5348e4c09b7e50d23f7f
private theorem part13 : 2 ^ prefix13 % Spec.Ffdh.ffdhe3072Prime = residue13 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue13)
    (e := prefix12) (a := residue12) (b := 2978364140) (n := 32)
    part12 (by decide +kernel) (by decide +kernel)
  rw [show prefix12 * 2 ^ (32 : Nat) + 2978364140 = prefix13 from by decide +kernel] at result
  exact result

private def prefix14 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (20 : Nat) * 2 ^ (32 : Nat))
private def residue14 : Nat := 0xae156f065920c383d71ea78a3858d563effcffcdf487b93e571fbe31945770c759033bc4b3a3e729b3bfbbaedea5f85760ef8ff7af0646c0efad47bbb1f2b323cb3a417e3f64339ad6674a7c86dcb08f4dac1025b737fd8897e8ae0f8787a1989f92b1a1ea7c4e7da27c1b7398226f9f09f66c82d416a5c68c1b555b3c6f03ebaccd71f35f45c05a04952c875d659800f2e308dc8ecc1ada97d0ea32eea5beb8a1e5569218231d8d4df2b4fb6711b9d865bd13bcbe2a2cab667e5f55df021fa78aff6a800f83110cfbb8d03e4156b4fbdfe526db29f62eb9e2c2b2b162a458853846fa4c1ca18146d66b8acd6403c062a80858fadda4819555e42a6df32b9b5eec9a4daeb4a1d4ab8b491d6cfee52b5b3d347724e745b76ae54a2b83027847c17b863f80f85eaf0716bde341ccd88e0bd586670c1c879bd5c46a5052ff2347ca1a7a1cf8875e03e5a495df117338c2c5914d64c4963e13cb3fdd7a177c49e76a83e6d989e06d96aa6db8f1b7b4af0fff0debe11271d2e0828eae1a7c80add1b4
private theorem part14 : 2 ^ prefix14 % Spec.Ffdh.ffdhe3072Prime = residue14 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue14)
    (e := prefix13) (a := residue13) (b := 2067847425) (n := 32)
    part13 (by decide +kernel) (by decide +kernel)
  rw [show prefix13 * 2 ^ (32 : Nat) + 2067847425 = prefix14 from by decide +kernel] at result
  exact result

private def prefix15 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (20 : Nat) * 2 ^ (0 : Nat))
private def residue15 : Nat := 0x6a1ca118a893c2c7e1e0390ec644624b3743d8b065689c17318421aa6cd4ddf2d5c58714f4605e8de279fb2e118073d04a54909ee0f5b165d4379ad55decf8808a844b47dea3e6fef1a4776e88b75f49a1400ac90fd5b49d3ce26381a60fac2193e324bab22eed16094783e3e88c8d0aadfa56110d112842e4325610fd30c2771de0afc9c83138a01100738f78c41ae5a6f3280a9dd1b082b8069d7c9e317a15de7da8017adea1f3f4cd76d6405667cb3c0e8143386f95fd98c1047e493841a56279bd95c309d6c201ffc0686e9f5f29eb54c747850b7ee80180b4662a726b5a7ffbc51f5dd97343774044c975d223184e3f610b0f394c22329b4b9a0b115dbe4ca16197e82b25002353934b8befae6c100a91ee0c1c43798b4c024346b10dfacd7f8048864239b6b687c09e716dfed9ec55d8eb4b13d2854e0c2364bc6ed37574b3bdb071c4a60e381b6b6ec9babe19a89c39247522c5ad8dc1581baf5b48286636cb7c341ddde27970e9a53cbce8b61ba50986e7c0ac59cdea24043ec34596
private theorem part15 : 2 ^ prefix15 % Spec.Ffdh.ffdhe3072Prime = residue15 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue15)
    (e := prefix14) (a := residue14) (b := 1466052797) (n := 32)
    part14 (by decide +kernel) (by decide +kernel)
  rw [show prefix14 * 2 ^ (32 : Nat) + 1466052797 = prefix15 from by decide +kernel] at result
  exact result

private def prefix16 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (19 : Nat) * 2 ^ (96 : Nat))
private def residue16 : Nat := 0x1b38b918847f1a6b4f81337a5e2aa4196404ffa33335c9dc75a2e5e02a3a7195a3b23d9467efe1cb8d7966df30ede77b62a33f914a09f258f4a6a4e3e8911a09d8e1a6a68b9fe9ed0b2f24c4ffb3ceff50985d7fe7178c3ea63eca45d6f703b80b1fb452d82f0b03af79f693e8aa0b863647cd2e4a085adf60e9388b4b74aaafa3b8b3f8705213ac8be09ed0872847fd2cd8496207a401828cd70479237fb23d7c70325c8b08bf347e8d82f173b13cb6cb27156a7b5aa7c73bdab156db75e0becddd2d6e747adce3883ae1f61fb15b85096f12ecfd432277c67c55a9cdf37c8f7e1886f671fc6a9c624c6275cb2f8f92f44bd129113ac2cee5d69554a7f9981d6f47d4186fe203a9e08e9e9cb0c111fc1729838fa8d3147a14fc949d59cf61954f65b255fbabf05b0bdd57f64cb0e5498962b5a85b0f7b93f795d8b23947cfc92790fc71f1ac9507165fd9ae323385e316288309f11b21d7853c87225d08dea397c6547c20c2bfc6837f1077a04a80f73f02d50a9935ebc5eb1dc71efb9133af
private theorem part16 : 2 ^ prefix16 % Spec.Ffdh.ffdhe3072Prime = residue16 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue16)
    (e := prefix15) (a := residue15) (b := 1777307498) (n := 32)
    part15 (by decide +kernel) (by decide +kernel)
  rw [show prefix15 * 2 ^ (32 : Nat) + 1777307498 = prefix16 from by decide +kernel] at result
  exact result

private def prefix17 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (19 : Nat) * 2 ^ (64 : Nat))
private def residue17 : Nat := 0xde2e5fcfd9cdf37740c06cd9fecada8912052d7c52fcc69cc797b83d5dec79c2d43151f1c50337c21e13d0b4af05b21f12c0ab36ba47b13282e2735fe1f2919df21e9fb54730e107466b50587f2f2b7c2cba13b02e537b7236c71532c985fde000b4f664a484683dfa51523873e26c110206c575330f977717808aa4b8be923ad1d6ab68a7ed3b189f6f3dce2e4d70c4d26cca36a20d82e18e11b9428b75200b80c4c80cbd43a09c227f114c2c0cc535df4692fb49d9650f73f0ef41db2222ebc7e50297746d4a26b15483f524056c8514e9567346edb6b08e715b9013057ca70be91428494feaa90f70ffff7206f9066c05631e584a553d5264db49175dda610a001822ce1c195cc770f78a8e21e1604ceb8b26b5e2fb490dc82f81b009b2c2978477a09518148bb7909c1570e1b06e5f1aea790b6f8882eb3142ba34dc76e00225d5d260ac652f0b793fc8871c5c23f3be00088f704fc8356b21824acf92b5753a5d9b1944857116b9ffb7f682308f47f1ce571d2940d4be9e791961d94de0
private theorem part17 : 2 ^ prefix17 % Spec.Ffdh.ffdhe3072Prime = residue17 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue17)
    (e := prefix16) (a := residue16) (b := 3942560432) (n := 32)
    part16 (by decide +kernel) (by decide +kernel)
  rw [show prefix16 * 2 ^ (32 : Nat) + 3942560432 = prefix17 from by decide +kernel] at result
  exact result

private def prefix18 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (19 : Nat) * 2 ^ (32 : Nat))
private def residue18 : Nat := 0x3223f43c57820da5114fdd68cca1cddcd2891e95abba5a089d9eee0d944f0356128e33a2633a7f5719e2882e44875868ce561d1e23e9724c2dd833a3b84d97db39ebabe432bc09ff4457d722c042ecb8e147c15c305c308072bc67a2f1834d7b95f8fe38e0e6d749af8fd27862b46e03adcf39c82e633bfc50064cfab3ab690aa9c955045f9bab92b92590fed1e02ef468c06dc9e0e7bb446680592a677e31455eb10b31310979e790e9be80ba9431ffb3e75420cd60315a01d13641a72bb879643ea3553dc63d3124ad70213292c6c534b5d88b57b333434b60c18b52a64382369cc4602390a288e601187e786f8ba6ec24f70f998f4efb04a2f92741a2a7f21b67dda270a966c0f0f1c1bd55d4a6004e8924f66feba8e4e777bfcf8cf2df636ced4ec99223f85cfd610acd6b8b1d8206d9cda5767fb3f3cc15a16f2e070ff8f8daa4718c91526c3729bd8c42a177a29544efb1285b71d7242d0e44662d2ff93463d9a655cffe074ceab09fd0a21065737ab20a34ca40b09a0e2eda18aee724
private theorem part18 : 2 ^ prefix18 % Spec.Ffdh.ffdhe3072Prime = residue18 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue18)
    (e := prefix17) (a := residue17) (b := 2451176079) (n := 32)
    part17 (by decide +kernel) (by decide +kernel)
  rw [show prefix17 * 2 ^ (32 : Nat) + 2451176079 = prefix18 from by decide +kernel] at result
  exact result

private def prefix19 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (19 : Nat) * 2 ^ (0 : Nat))
private def residue19 : Nat := 0x444f9b891dfeefb98403ade55a2b7fc1018260a92d436a914175761bc3bca24f0d591f859f9ae08f0b2101ebb59e0570534331fe06a451fabca3761a9ecfa8f91477661c646e64fff12618bfe0532adedfa358a46c3e7ad950d1f1c5eb613c35558542d6ad992e2a1633c1276292b6486ff061f111877c32654417e5fe9b9c126a8cc8a83aab18b231661367b0d9a3b85bf735607950cb8f5d934328f4a3b607d3a43f442435ad185a2a960b8c995c474f44346fb2ce86af6031830136912fd2d460b4e301e4d84e7b6f0db85cc0603db68b1b053ec21ab4b3eaddfd741290dd50c131d042d56a039ff09e80a5d631e0814504d9844902aee441269bfc3122c929c210f65055b65d78d76e00629628d412b8cddb91eac4feb7622f1b8b7a64a2417a03c214199a99aee4cdd34bab7b3a922970ae9bcaeddbb45f62de99841cae91d934f5368c3f2c3f4525efc647ff19930b926d84d7a603b5a147e561a2e42dfaa121733ff2e76499085c9949360116e49f6feeae2e0383b9afea1ea88caf97
private theorem part19 : 2 ^ prefix19 % Spec.Ffdh.ffdhe3072Prime = residue19 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue19)
    (e := prefix18) (a := residue18) (b := 2944612200) (n := 32)
    part18 (by decide +kernel) (by decide +kernel)
  rw [show prefix18 * 2 ^ (32 : Nat) + 2944612200 = prefix19 from by decide +kernel] at result
  exact result

private def prefix20 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (18 : Nat) * 2 ^ (96 : Nat))
private def residue20 : Nat := 0xc1440dc8e92a167884f774cbe3592863163e5957f1c0f5d505f25c00252898d4cbeb8a53e844b7640d8f735c4fe84075b98da08c6a172bb12494bf18e3fd4255de282738b1da1447981fc4da7b9f91d8224fe8eab7a1ea17474cf47b8c72083a1749d25b109b507fa8cbfd862683c9e64e13395638c900b0a7f2329d9f753afeabba93578a290cfad02ea1f6a2128f629289c56d0237e68063d2213e8c4addcb8b354d3b79f4677fe1ea9bcdac6a41101909549bcc9576365eb23b2e62fa5db2a8db163906dd8e8648db4abd97061f7215d2660402e18bbdd41bf3df2f5d7f9ae571864b17d3dfaea4b5d210384e06b625634eb83e8f27097a6b89b86774d0ab935de160b00ca1c15240db784c59722898e140ef64bc31374323541e4b2c7df6a78c5c87452eb767422c23350bfdc00a2cbe21325b717b78d3189538b3fbac087b5bb4bdcb0031ad101738cedc3f333d24239bde57ecb5c9c96f7b5c2ee0f8190931e51b71c5eb679619e3bcc15a894dfc6fb5f003242a9472301c1848534f4b
private theorem part20 : 2 ^ prefix20 % Spec.Ffdh.ffdhe3072Prime = residue20 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue20)
    (e := prefix19) (a := residue19) (b := 1118941866) (n := 32)
    part19 (by decide +kernel) (by decide +kernel)
  rw [show prefix19 * 2 ^ (32 : Nat) + 1118941866 = prefix20 from by decide +kernel] at result
  exact result

private def prefix21 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (18 : Nat) * 2 ^ (64 : Nat))
private def residue21 : Nat := 0xcb8a57e1898d38fa8302b3350e0916958d4480f41474b1f19eb9a4662915d3f1256676615e87ab7e1d1be4a1378f912de3b5ebbf67c85b2cd9aed137a86d8c5c8cea7bbaf3fb9a5713220e5a9f4ebe8adf27119b16a31a65580d5be350c6d83afc0d1474b1fa3b1c726adef5a05aaebabcd2eb15b54b7850ad402aaba4a40785f72250eba0fd782ba721cffaa223681bfd4dcefe2228e87320a713545d3a9b3b5f836309e23c0eafff4e67e27c365de7eecd4825b7f9891921b20ea8ff37a30d8f99a275d768d607d1ba6c8b2fe9161f0612e85db8c5acdf06567336e4957708a35ebd649ba80d8b964ffefe3600a9d4482b736080d1f8b1848538ca5f31c267168d921e057686899c4c2f0b55d7815465c61d711f3a70c3183980de22789f4f17f8f32f04ad8266168ccc4ef712d13354d1333afd2e0dfe57b0bcec12d6bd6675afc48202789b268c021d69472fb0edfdbae9315949df86a25927903b82f57d16ea6a264c8476aa3af2a59956d9f22f502ac2594b5cfac4ef5e175f15e5af7a
private theorem part21 : 2 ^ prefix21 % Spec.Ffdh.ffdhe3072Prime = residue21 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue21)
    (e := prefix20) (a := residue20) (b := 2666958201) (n := 32)
    part20 (by decide +kernel) (by decide +kernel)
  rw [show prefix20 * 2 ^ (32 : Nat) + 2666958201 = prefix21 from by decide +kernel] at result
  exact result

private def prefix22 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (18 : Nat) * 2 ^ (32 : Nat))
private def residue22 : Nat := 0x85e0a2cb5ece31180d06f6af8d9f5083beaad7c8745cb4804a01b6f474d5f3bd6b8fe4f333d4b38c9f3ba4b3fe45af427deb08754c19ddd4ab707ce91bede64d245fb7beeda2da6a34227be3ffde98d377b45f944d8d5a380ff7aadd23d498029d876b033d5fe337d03a057710d787d45c94b59b1e99eb992cc1443a53bd13f4f8914bebad1a83c85318d28f82c037f865f24f2c3aa501ccd728719a392df46acf908de8f259d10bcb6f05053ab38a9ca4523b827eb6a02671d5b522d4ff89915fe8e07ade89fd29b761f6c3adc019c37e1015e7885597a1ffb8ae6da6ce081334ed3923bef8e629591b58a2b174663d15d53f6a6abcbafa8bfa9f4327b6a5b7679b2a351ddea3b8a36f6de70354a5ba990c3c97ba2b4a05cd0b23e47e5e7f0daa06c2bea8ca077ac71479223e7efedf947ca6ac66edf26d993d96dbe89c0a7ee533f40aed31d2785bbff3116f8daab271ba012b781786599441f733c70281ca256b82d6c0b4b5d9798707d0ecb7700750995ca0e59e89051671fff51de2a1ba
private theorem part22 : 2 ^ prefix22 % Spec.Ffdh.ffdhe3072Prime = residue22 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue22)
    (e := prefix21) (a := residue21) (b := 3668674991) (n := 32)
    part21 (by decide +kernel) (by decide +kernel)
  rw [show prefix21 * 2 ^ (32 : Nat) + 3668674991 = prefix22 from by decide +kernel] at result
  exact result

private def prefix23 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (18 : Nat) * 2 ^ (0 : Nat))
private def residue23 : Nat := 0x7025878f6268039731c8287f93eab72c308fe0911ecff681b532402b9889e553f512019ad5f8710cb0e8dc22ef31982d6f5d99dc79243186ebb4e8d57698c780e7faf698b7d7b5010453f07f878b87d882d0959e0462055ef8afdd6a7f27fd78d336cdb5578b6aed8e8d8afb1ca797db34ebb96f68e1b3a6f42054c4386c9d93b3251f775e2bdf7fd270a4b0e86efaf11514a1b8f01ad0fd116e611d07a3ebd54d1d525009639c6eced22e5d7cb6b2db95e85061943e7580a18e1e678875d133fdfe677ddbf278c1f926c04bde3de594a2534170dfbae65a8567e39dae64b65d215282a0aa77e42ce848cd7af6ba42f1c81cfbc09a388ccd525c16f960b72efec62baf58abecc5d45134973528cadd9ad31402a811414edd7efa89fe1642602ff1c2ac3bf33c1aa0a59f57f14756ad7b5d36f3c1cd5c22973e12db6c9bef82929c806bf12b29a1e8cd21de5e8b200805f665fabb01ba1dc0003d59f295ea954682bdc2421b1e8c111ab9cee620c45ec2780301d498def7b9c546f4020b01191a
private theorem part23 : 2 ^ prefix23 % Spec.Ffdh.ffdhe3072Prime = residue23 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue23)
    (e := prefix22) (a := residue22) (b := 1068229786) (n := 32)
    part22 (by decide +kernel) (by decide +kernel)
  rw [show prefix22 * 2 ^ (32 : Nat) + 1068229786 = prefix23 from by decide +kernel] at result
  exact result

private def prefix24 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (17 : Nat) * 2 ^ (96 : Nat))
private def residue24 : Nat := 0x46307f33969df244819e7c5b1c331ed315d791c346572c03072598cabe236a1207791c3f6b42da1bd32b7a7cf83ade1aa45bfa823911299dee861d856630a4815a1c738c6d7d645ccec4be77fb236641f1a23fdc6697e616cb7869f00e24b42e2f20d1aa8c2af2f491edfac682e6afdc4668276bac074f146fd5ef7b1bc06aac28c67448758cda2c45373da0086e97e22491db9d13d1d49150ca0218982bea05b936a26d71351c25af2776b919b5521ed4da6990bb12a03e05da1541913ede98f6e3390f8ab460def6897562569c18b4b23f1f73aa3c9bbb1edb78c1d95660b25a6b51c24afa5d0b1023c4683cc3383ca41142ffa26bb03fdd44fe780de7516f87d0be9a8cc6dd84e82a75645832d49f6082b7b2068062cf01213a7c1162ae69b873a4cc344af823094c3404ecaa60028036520dd74a73c9aaa9d173953ff48c2ab84b0d265084491617cb3b85a8f7748cc5a81d88db732b7f0d93793d5133eedb1edcd5af860826ac338704a7cc0d35e4eab38023e0ae9b595840852f9bc841
private theorem part24 : 2 ^ prefix24 % Spec.Ffdh.ffdhe3072Prime = residue24 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue24)
    (e := prefix23) (a := residue23) (b := 3425142328) (n := 32)
    part23 (by decide +kernel) (by decide +kernel)
  rw [show prefix23 * 2 ^ (32 : Nat) + 3425142328 = prefix24 from by decide +kernel] at result
  exact result

private def prefix25 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (17 : Nat) * 2 ^ (64 : Nat))
private def residue25 : Nat := 0x8e08206def585f1fe7b2dfaa85209f60b84e8400f54036f6904b4b0ba1d8eb186ddefdc77ed3fed2f543675c1e3702bedcdd4d8b13088a743d26474a3a4a5dfa84d9ace7e7bbf451520045ce1c9a13a67c11fde10d34924228a578730546975b27b2cde529b5ce8d203acfb61ed1a9b65adf8ecf95b9d6ac756c846ac86f4ed00738e19227011321b6558ec674899b89c9f21f1d52d4be31464e98daa4cca10d332427f1de9cd26ad299cfaa1f5387b7b21840f0072d71bba8e58ecb37b59756285c17e045a0e88f5fe166eb5887b536f28bd75b8c9dbeb6467f2a9615db7d0d8ba69987d342c3d8fb048062b7a74affbfeebdf41901dbe05f6ced198f2dd4d1326c02dfcb04f922a456f45ee3e14a7ef6297d0f31d908c5a312fdd038b5edfddae8495517e291fef282b199db513093a0fcdaf0c7ce81e87af47e91eef89f40d7977a6481cd1b104961f5ee3880f93cf97e7e0f4138295654455ae829c4de85c0b1f06a570e3c5c194197a80fbccb5f371b445fa3256c64e404c1245ae7eb45
private theorem part25 : 2 ^ prefix25 % Spec.Ffdh.ffdhe3072Prime = residue25 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue25)
    (e := prefix24) (a := residue24) (b := 1886602683) (n := 32)
    part24 (by decide +kernel) (by decide +kernel)
  rw [show prefix24 * 2 ^ (32 : Nat) + 1886602683 = prefix25 from by decide +kernel] at result
  exact result

private def prefix26 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (17 : Nat) * 2 ^ (32 : Nat))
private def residue26 : Nat := 0xc68f8875ee3e894aefb8bbf629fade5f4eb8c668263e8783d2b6d13e58636991e5b4ecc221e099436b32caa03b43444d303c15e335810407066898deb8904b88425348e0337b19ec181db57e6f7a5fe61aabe3dbd77d1a89e7b4b1a35cec815e584b0f5c13612b71d39b8654f49250d3b11e186943a414f550fb73e646994e1cf4b83c8f6d9b388b45ecd41bc2af635704b37f5e26467c8af930117ef424a874a1cd9250d4a264be93ec279ca2173ba0d4927d2e49b6f886b68c4c1a3ca35d46261b2e79dabcdb6ff7abd1bb2d18ee9ada7cf483610f22bb165392dd15b837c337f526d848022c98a3a844b00298b6ea0d28bc1ca3f7136bc36dc9a2d866b4760c547eb31e4d64e9c8ff7232b49a2cf32deb092ce0b55f77bb44f5d5ec23962616a0d8e9c261dc990de8262bb19dfe1d419bbdeafea7acd6f21bc131ed3316a9498083fdab4d84f1bb9c1fbb7601c4993ad8d5d3504a47f092e3507274df0bc42b790d01814bc9ac7d397a9d44196c65dff8d6dac1cc03f887f2b5fc77ed4cc1
private theorem part26 : 2 ^ prefix26 % Spec.Ffdh.ffdhe3072Prime = residue26 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue26)
    (e := prefix25) (a := residue25) (b := 4048766189) (n := 32)
    part25 (by decide +kernel) (by decide +kernel)
  rw [show prefix25 * 2 ^ (32 : Nat) + 4048766189 = prefix26 from by decide +kernel] at result
  exact result

private def prefix27 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (17 : Nat) * 2 ^ (0 : Nat))
private def residue27 : Nat := 0x1e936d3c5b5d19e2c34199f19c3ea7ccbc86d2e7c9c1be990ecd278fb5a0ebaafd2e55b43f1abb1cab0641ddf75fdf440a14abdc7b346a1d0e63db406c6e786eb1e3e7849b4affd455006e08634635a1368e54a2d920060e09d1a83006bd233ec77312bb66849244c54a0b126c41b89ed18bd414b255cb9501cc84024730faf79fe2ccc1fc346bb4bff0c7281bb935f895efdd87cfb8d31cd87a2d82ab82c5dbd12c2451f9991633c15db50ca0940ca00af1c661f2dd129ac299c4ea972ebfa0da2062624780dfa24236c869e75949af0e882d6c97155b5f723c8580a6b88fa3877bf08387bc34fc18ccf222ae92e641457b9dffefb43252eb638bbfdaa4109b1c7c746273b42521739d5763f1ccf250ae61f49dd6ce6ac6778c1060e25d70557f6f91027edc160fb7709d057b942c2ccffa8d04b6d73814f3879044882e2b051dee708dbf7384188f4fc3dd0af636310f0a04d61fb78121390ded8d95f3d101082f48154330f627955970d041f064bf779ac7856cf0c9502a5d2017ae361e3f
private theorem part27 : 2 ^ prefix27 % Spec.Ffdh.ffdhe3072Prime = residue27 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue27)
    (e := prefix26) (a := residue26) (b := 2046293049) (n := 32)
    part26 (by decide +kernel) (by decide +kernel)
  rw [show prefix26 * 2 ^ (32 : Nat) + 2046293049 = prefix27 from by decide +kernel] at result
  exact result

private def prefix28 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (16 : Nat) * 2 ^ (96 : Nat))
private def residue28 : Nat := 0xabc34d6389c4b1a8ca6434662d44ea41596fa531dec89207adbac0c3be0471e1fcfdf3a21d7c9cc86918a0f91f48fdbfd8851e6ff4d33629ad9b7f000871bdacdfa0bd79614f8755e9cff0dcdcc56637aca3615741b22d4b163958b7a56f1627470cbcaf33e5e867822ba885b8751f218a6eb9289d391a30a0287f3fc411a26e6d5ffc9466938f4c0a2ba47432250fb22900ce324432487bee96c0195a090a5e455a1133b97bf20b88670ef623b906660aecdd771861bad529c17e8f6d1cb0672be5ad0da9707eec3b054bfc1da3dd1738db8363db3c2711e9828f51a0ebff09e165b4964fa95440fffeae373f2a53638e7fbf34f0be118a8bec012b45d300be511baeb8bdeb686a0a8447ed184fd9e622637c3de01c343b361257a1a915d9b9de10dfe7b164cb7cabe55095232fbc3fc7a3a9191b03bfcce10d5ca260ced0e2a5d64ca44121ecc8a75398943789d3e6e54c778c6a2167290ffda7054e4fc476ea54594039e0652bf318a772bec454502d9a67670afdd82d035db41dd0484ba4
private theorem part28 : 2 ^ prefix28 % Spec.Ffdh.ffdhe3072Prime = residue28 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue28)
    (e := prefix27) (a := residue27) (b := 251178064) (n := 32)
    part27 (by decide +kernel) (by decide +kernel)
  rw [show prefix27 * 2 ^ (32 : Nat) + 251178064 = prefix28 from by decide +kernel] at result
  exact result

private def prefix29 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (16 : Nat) * 2 ^ (64 : Nat))
private def residue29 : Nat := 0x40fb0ba8a9a9825b987ac129f873ae18683b60312a4b9c5d62152cf23d500de2296ce788a92a5e5f44ca7a8593847929dd35338ce92ce6175601e614172414b08f818b55ccb01172ed6cadbfa47fdd1d0e705761d529a001ae37cbc739e81cf0b45f41c8d14605277a7a144d8e721341758dd9fe70364b97cb5e4c139c8481d9eba8aa1268dcf4273d95c8eab26a764eb692a0feb8cd0f4df0bba7f797260a098c7fd96611c3991e263802b3b25197b553f5181168cd6d9b4c2ccbdf96610879571db23365db811f3a4389652c58a504767e1e3e76d5f21e1081943b201792a3e76fbc32ca02243ebf3bcbe90e0ff3dbce251766e1e35e7b804bd7f74af3b9afc4dba81792fe75443a55fa92d98518c721cef2fca0b885d1b740d8190a98119b0311be97c246c3acbd6403be354e16b030725449c732f20cfabfb26ef30393122f785c7221d5578c8def388bf280bcb81ea7a0fbc98adc32022346199a0b2a56180f6acfd4205c3687ad59f71a4699abf22eeb2942c1a490f33c951851b386be
private theorem part29 : 2 ^ prefix29 % Spec.Ffdh.ffdhe3072Prime = residue29 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue29)
    (e := prefix28) (a := residue28) (b := 2606166938) (n := 32)
    part28 (by decide +kernel) (by decide +kernel)
  rw [show prefix28 * 2 ^ (32 : Nat) + 2606166938 = prefix29 from by decide +kernel] at result
  exact result

private def prefix30 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (16 : Nat) * 2 ^ (32 : Nat))
private def residue30 : Nat := 0x210fb5fb27a9dbb5099ecc2b643c05b616c50bed92043fce4875e988b6a18d8d98c16cf5a88c91878ce8052e455b12a1022dcc45d80c59bb8193eab54e5dd8a403aa89c7b0f4818b7320d59db9d6f18d5d82df760e1009094d80e4ba13eb92f0b02a09ad3d9ad9dfd2d1f9ba7860b5d5aaa59cbb2aa95bef99ac8691e9b09fccd784efa5840459599865c15d5737330e44cf97925c2647d7a953969099114ba68d33f77b9e969042920a9fcb94b01df311083f2488b1d7dbb81a62c1cd72a64927a7c66708287a85b47acf64adc5121c0428170e73095f7479691d71d362d14d372e06268134c1fc18865ca3f7f43b8825dc096ad6a6601381663c3eebec8a168f0dfd548e967fd5badfe75c2ba9bea8ef895e36b5fa53b00e80d855ac80ea80d4fd60c4a6f3395f227e9c0a0ee685a269af95f9f23d75ecd00ec6cfb46681e4e44d5ffde2eae4f77d3ed459cd3256202b87a70e5e5fc69f6dc7f8064d99c2cd997635a96e6956a89f597687e0299a135c7b7127db7e20e955dbb03510316a24
private theorem part30 : 2 ^ prefix30 % Spec.Ffdh.ffdhe3072Prime = residue30 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue30)
    (e := prefix29) (a := residue29) (b := 2555798823) (n := 32)
    part29 (by decide +kernel) (by decide +kernel)
  rw [show prefix29 * 2 ^ (32 : Nat) + 2555798823 = prefix30 from by decide +kernel] at result
  exact result

private def prefix31 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (16 : Nat) * 2 ^ (0 : Nat))
private def residue31 : Nat := 0xcc074e43909728609fff447999f5acbec80127398bf8f162045967b3e6d6630be10a814507b6b6b06b5fe95e36ec2d5a259f4bf816767e4e1de3fe93ed0e18c1d5c5b116e9d1ac2ef43eb8c9035d6402ce7cc5523037b60b521ac8ab0265681027f49a6af5feb9e9ab4fa93b920c5042ad9bda3a73d047b78d7f1548dd8361a62836f7c359b979ae69a18b9ef9d8c0fc1aa4d8537fdeedcbfdf833cd3ba0ecede079736ed76c222b3737898cff9501c004a34e4f43165111456095c6651b48d04f830b2d766e52d18f96d7d508303db60fae00b4a1d66603a84624650a132c5da79651d51f808213d5e814ea2e225587de867a7d7de78f96d00df367ca10d0795a5718ea3789e0c7da56234041cad62434e84c7e1d083576188bf9f4a8def4bf99c6d54f7fdeeef0e7b42320e218709109c00e5c700be5bf4b66464fc0f918d11f57d228153586c744f61a8ec47466da17d2de4a8cfa4a0cf0224b1c4ef50f4daff64a79f812826470fc47fee2d12a48b43c7a0849c22d57e57e3887005b55c9
private theorem part31 : 2 ^ prefix31 % Spec.Ffdh.ffdhe3072Prime = residue31 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue31)
    (e := prefix30) (a := residue30) (b := 2753379517) (n := 32)
    part30 (by decide +kernel) (by decide +kernel)
  rw [show prefix30 * 2 ^ (32 : Nat) + 2753379517 = prefix31 from by decide +kernel] at result
  exact result

private def prefix32 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (96 : Nat))
private def residue32 : Nat := 0x7c396489ce86178292f9446e01afbc02b67f00658a971dc82ad55038f19051f8cf2b0094b2154ef9d1510f9ea08ea18a43bf1236c34283edf349f97fd283e0261f52b035d1743e780b45b1a2c6123ffdb34456fc7edc3c585bb1a7d58ef16de4b0e49dd5a173ea750e0ef7e166758fc4a72f9dabc7ade48524072de7a63df0f0bb3229c26f2ee2e4cedbfd673b3a4cd67343867e848f136e4cc6a8a10f85a356ae095ce9104d499400ec032c786353113298869d248bd4e22d39a87c31d04821b4f3dc68769d26909012be1c8b93f8cd515622cd0bfd2e96bbe14473d3ad97111407c463f5f6584baea8b673eb9366df37f0a8a800777c61e07387e0ccbe6b6bffffa7e93a5107179ba883e50368a8bdfe3eb7cbbddc38deec1c12539d3f21ffb79db35eff5ffdfbc243f397ea36ccf273412d2dbe733e6eb741ce20bc3f34c47168c7025b3496fd3642d3fcd4477d9ce4c0d21bbc9334da3715e6b3bcfbe050c5ef5508a771602cea85546e4aa1b7fc407f5d59e61935610d6a534e48ae85a1
private theorem part32 : 2 ^ prefix32 % Spec.Ffdh.ffdhe3072Prime = residue32 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue32)
    (e := prefix31) (a := residue31) (b := 1577408705) (n := 32)
    part31 (by decide +kernel) (by decide +kernel)
  rw [show prefix31 * 2 ^ (32 : Nat) + 1577408705 = prefix32 from by decide +kernel] at result
  exact result

private def prefix33 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (64 : Nat))
private def residue33 : Nat := 0xd2cf33d7630551d1c38bb88a9e96a4a376f53a7aa4f0c24288f19d96f6f97a014311231353e94d4926b596a036b8e1ff3a952e7d9061309211bda51e0d98eaf68e5c0b4df61cfd51de26c5a409e1aba97b2e987bd2d145f51c03f7ee6395caf573e9d57cc3a1c88d4bf0063ca0be8b97d70c56bdb9b1c8e6883a65385e05adc9e68a24b3b44bf538d4a9463235c6eb50ee905769a0c4bce49eccaa28316277baf251bc92c81f95312ed2c26f19e4cb85687eadd930e946ccdb278db09b9bce872c1526975feb26527b5a150efda025ace839d37fd1a793871976d406a31e5409716226484e0fe138b3cb2ccc1a7dc542defbae978b427cb976d313ab063f69eca6e69b4d15ff86f993c7c5b6eac8b08d89e2698033642089dc1788993d7a7ef441d4d195931493f0b0d6c76c3613e9f7aca381d978d47d0823d77d1b02be242071c54cebc421355e05837d27629e4ed55d8b16a3b8aac1a2fb152e03c53fa9143d36d41a461c4a664850f769598a934bf2b32ecfb5489ed432ee20172ac44a69
private theorem part33 : 2 ^ prefix33 % Spec.Ffdh.ffdhe3072Prime = residue33 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue33)
    (e := prefix32) (a := residue32) (b := 1502772656) (n := 32)
    part32 (by decide +kernel) (by decide +kernel)
  rw [show prefix32 * 2 ^ (32 : Nat) + 1502772656 = prefix33 from by decide +kernel] at result
  exact result

private def prefix34 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (32 : Nat))
private def residue34 : Nat := 0xb83ad90cc4a3e82007965876aca6be4273a4cffbe7c3e3824749ccefebbffb50fd2e153d47892ede84f640e4e39db98ea4f0c1200df41a4d9cc01a8ada7946516ce7e98125915255e2b7cfb44c43a93e8881284ece7154475db6a1c2511e28230af819935fb1ef4051580d2e80f6e38e6eff5a32f96fc68b0c7ae2ac2312c1d73b2ba438ed75f9e68b4b6259c183eed736def2fdb7749bc4de988e79250cd27b055563d8eecb144813cecc344127f297d68e639d30aebd3a01be0c0725ac0a740df85684cfe497186b4ec544797a18047ec6264eecc007233231f9e2499d1d7c52a7b166779ca30087066395529eaf7e0313d5977f41bb120bd7acb7b83382e13461cd5f855dfa7d355f0573b413abecd7863f5dbe0f5066b83443120dc9e58b6bbeaba4264ab82fe11432d676a6ea2708cfcdaf379f08b856376f7e9eb6bb9cbf21b3c8d9523de52efe9ddc8a16049257e57179fe8efac46d179344850465abeebb7e32c219c977d3239c617c777ab8a646d4bc506aa26181711a2b99bc6732
private theorem part34 : 2 ^ prefix34 % Spec.Ffdh.ffdhe3072Prime = residue34 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue34)
    (e := prefix33) (a := residue33) (b := 3900986533) (n := 32)
    part33 (by decide +kernel) (by decide +kernel)
  rw [show prefix33 * 2 ^ (32 : Nat) + 3900986533 = prefix34 from by decide +kernel] at result
  exact result

private def prefix35 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (0 : Nat))
private def residue35 : Nat := 0xcd6fefc516732e349f08d0b7955a8d22cd4e7704145dc9d90e572916832f95c6b0f536c3675f273bf3d9dfbbdff47535e0f5b92a1c51ef9469c5580d9585ee64e257383474d27125bb48b1d8a8a9d053f4c03bf45bb4c4b56547645cb3ce7c5d95bcbf8315189417aefb44d1603bfdd44335b0010985c117ff3d590c56efc2aa4d1226a198ad064841196f520f6b31016689d103ef3cb944aaafa8679c75e73acc363960c047a49c0267e93818bb6d69100d2528102f15321151673d4ee387dcaccfbfb38bf52c7cb283e7d76a7e200cbde477e6622dbaac98a9344ee0ae983393a3a95df4e70c42c14cc7d2335596661332071909e0e7adede0425b0e2c18f1c6efab4b001b709bc60ac2a1ff590ffe1ab1e1a238648ceb5a4036a552c16dd68795a7c853548d5b8169c831fbcd6a308bd614432f78cdb8f5e19fb197cf39c770e08269f8bb811acf22f47af3b22bde0e0e95657739cd05abcc0dc64f79960e29d39638b54726156f70f1210deae0ed83864839c130cf18028051454f6c30c8
private theorem part35 : 2 ^ prefix35 % Spec.Ffdh.ffdhe3072Prime = residue35 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue35)
    (e := prefix34) (a := residue34) (b := 3647238653) (n := 32)
    part34 (by decide +kernel) (by decide +kernel)
  rw [show prefix34 * 2 ^ (32 : Nat) + 3647238653 = prefix35 from by decide +kernel] at result
  exact result

private def prefix36 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (96 : Nat))
private def residue36 : Nat := 0x424a0962fed5477bd140b998905bd609e8721bed2d5a7a8647b5f8bd0038ea205eab6f7430b2d0b527681780deb820ec92e82601c2b87857ff03c1faea633be4bcbbab9569bb9603f9c9a81c73325c4d9dc1d0e627a52e9db7dac6b90330e4954f5f7a47973f3dba03e8d795ff678c095f18cff2b6f6075d0ebfcd64afd6ad3e8f23734b5d22fd0db787c99a94dd02698837718e708a02d80401ce386e0ebff138d59520255fa6de7045ae06f19c5aeec0bc953d5190938173ebfe5942aa48fb7f65ed6e348ed78f302d661859c51fc6b8c98824cd20513a6695b5ab60c503b18ff052dddf9268b6fc787d895f6bd273cce2535186f312c8d4e9efba773035ab63185cc2169178550658d07378ad5bba30f4b8e2114c7034129596e0ad650a500a962c0cb194082f5f279d1640b638e1dc122527389173886874daab6ef59adbeb6509ea0739d9c8e613c22410de5c4bf508df552bc801b41751ee80eeb9e3e4747c852a9f2aa527663cfc45a7e616a246b662539475734f7832d0391f74dfb8
private theorem part36 : 2 ^ prefix36 % Spec.Ffdh.ffdhe3072Prime = residue36 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue36)
    (e := prefix35) (a := residue35) (b := 3702877531) (n := 32)
    part35 (by decide +kernel) (by decide +kernel)
  rw [show prefix35 * 2 ^ (32 : Nat) + 3702877531 = prefix36 from by decide +kernel] at result
  exact result

private def prefix37 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (64 : Nat))
private def residue37 : Nat := 0xd2f65d94a797217f8b6170e7a861d01ab1054dbdba2b0c409bb9008b940782fa7e0811ace709bb196094c78c5d34944bbc540057ddd09d6e78c7c230bde64bc87a08000edc1936cb452d2c958da9a3038e095727060844091debff867c24ffd356c3b2dd1650eb503b4477272a94a8249d18d4b1cc792952298e787ab3462fdf85d11ab8be89a5c9c5da3bc7548b4d6bcbc6b645a1a38fd31add8cbd906b163ec88299e9884677b15c1c51367a18f1a7619bf7fecebcfac657baa49f9872d4be5da4bd905674ba008053898f1fdff684888ee39cf991959fab160f13595b995fa53997e211887902949b7a6a9333a8e8fb9761e0281b9fdef403a5b824e8f16d8774876299b4b39de7cf5e2d1b922344c2f2de38683d127cd786b1afc9ebd9a82e1f10ac534e4d9ab23ad96aff9e0c41271066544fb65d1fdf9337520ae2470b3d70a556cc47b9be62d10233b9aac556ad6ad0b9728204aef5da01679ed5849ed05ae83b8aae4591dd6e4094ee6b2e32252b279906c74701b95d598df42eed9d
private theorem part37 : 2 ^ prefix37 % Spec.Ffdh.ffdhe3072Prime = residue37 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue37)
    (e := prefix36) (a := residue36) (b := 2959866420) (n := 32)
    part36 (by decide +kernel) (by decide +kernel)
  rw [show prefix36 * 2 ^ (32 : Nat) + 2959866420 = prefix37 from by decide +kernel] at result
  exact result

private def prefix38 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (32 : Nat))
private def residue38 : Nat := 0xccc1533096601c12d96c0513606855db4b59869e3dc433fa14274e9d6259d70580571177a6f560be50aecbac246fa5f68437d6737a067dc70159faca78ed6964c24ff77ea5cd69b424693dd29dec10d3b06b6e921bc8cac805854e7d110bb94f20608b7936f290a26c1d3ba0630a891989a580eb43eddd9bbccd1a0a20e206e904c2e9d86845c0484f215d85eae1466eb1ed1c45d6a8614b279419ab4579a2529919e24ffa654d255f82ed17d849c83552da5de20d925cd484cc734af654aba55f879f550be01a1fefc94ff0a80b1beeda2116d9f2e83bddfb50c9e196b8e7fbd1136a54c76dde36591378e5d2701511a7cdc034c74c4f5fae20534422d4370fe1a0d8696e1e908de28a202130f894008ad2b29c42ae27d9c439571535f7cb05daaeb3d84ffa00d112b3bbc142f475fc9001f19346849b971101d073841c31b704403e61fa9e19c286326d96f062e62adff909aca54d76af8c22db865abcfdd539b86a2128e741b1252024aee76c88aad8e2d488ce07dcbda58e504a46885710
private theorem part38 : 2 ^ prefix38 % Spec.Ffdh.ffdhe3072Prime = residue38 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue38)
    (e := prefix37) (a := residue37) (b := 245866833) (n := 32)
    part37 (by decide +kernel) (by decide +kernel)
  rw [show prefix37 * 2 ^ (32 : Nat) + 245866833 = prefix38 from by decide +kernel] at result
  exact result

private def prefix39 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (0 : Nat))
private def residue39 : Nat := 0x1379560507ce576fbddbe58a56965acbf490f075ca997f48e23a2d2f26a8412697a07370e3e83a1bb7cc348b7d6ee02d949a0c0c1c4ddeaad2b34256e943ebe026db7bb02ef45f798aa795142a96c8a662698dffb8a578ae6a8a0d84fed1775d4c5d97eec28253ae52b791c9121de6df8e8a6f95cbf6435beed7673bbd1f32e645fbb9def6c174672576161b8fb6472b26d05da07e0cf2b27468182f88eabb13a8634fbbd56add8e31deebfe785006160de424bc210335975968279e65ba96b965434ae1975f06719175bae46f32bcb893da83535a502e4545794a2e806be6c1874f74f2dafb02b5ef2d436ebe8c99dc25b9ecc96f89b83c6305154a6e9a2c3a0231ad305f903780ceb70cf0433c4174d09a60fec9e9b8dcb61eeb380040d437ef3ca4a8c844ba88c3cef32a7b40e33239d136b0f5b94b2e7ed3b187ab8c8dbf3c4622ffff68ed2c6f2f43301e2f714212a3f739205b308358d31309f5d698e3924b1efa6854a052ae0f504fde378e1b7c12d34269e606239010794cdd4ccf2c
private theorem part39 : 2 ^ prefix39 % Spec.Ffdh.ffdhe3072Prime = residue39 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue39)
    (e := prefix38) (a := residue38) (b := 4011632378) (n := 32)
    part38 (by decide +kernel) (by decide +kernel)
  rw [show prefix38 * 2 ^ (32 : Nat) + 4011632378 = prefix39 from by decide +kernel] at result
  exact result

private def prefix40 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (96 : Nat))
private def residue40 : Nat := 0x2c9dcb62fc99b98ed13ce1268b1d130baa31ed8300e52f77d67168b1cf6dddd3577824bbd4a63b346732a3536c9f732f2f173d0ed67c8155ec4dff1e1cbf59967768820e03ac0cbe0de2441cffd1eb4deb15788966ffb94d92dabdeadf21f055375543c37a00f78feb7b6b151e5a63c45e9fb547d2090eeecccceb80e5780e43e645b352e2901ad7751ffc3a4dd044c51c6a77acc4c7f1a8e7cfcd7aee206d79345161c76619f99d027e2624095bad00bbf57873edf5579f56a654c86434107916a4042a84dba88bcfc5b3bc638d69eb64bdb1c5ca5580eb46f0fd226b47f41ee552a2bf9879a2b622b69e04eef8953760ef1d57544c48cd7156a9823eb6a03cebac6a34b063d4001a77060dc2ab71b423f88783b3a2d5c09b85c9508d4ba9660c42c1b8d1d1b4068cb1020a7bebf930942105f6e80f87e4fe2f1c022c36722ef5b72f597fd1852e4ece6ead2021183f60883924c27b6794c54394737c2811d8bb88d803180b503f0c488153409461a8190ec4e8f47c1d2bf0f1271fd6a99daa
private theorem part40 : 2 ^ prefix40 % Spec.Ffdh.ffdhe3072Prime = residue40 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue40)
    (e := prefix39) (a := residue39) (b := 1462466291) (n := 32)
    part39 (by decide +kernel) (by decide +kernel)
  rw [show prefix39 * 2 ^ (32 : Nat) + 1462466291 = prefix40 from by decide +kernel] at result
  exact result

private def prefix41 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (64 : Nat))
private def residue41 : Nat := 0xe58cd85977fc2a16c8d0aec68389596a9f36b30fea13cca72ab00de43147167d3771ff53a6112bfe75055061436ddffb7671076c6ebaa2966dbbfeff596da878429077e562daed1c019d3b74399b5fa00ff7537951609d103e59a33980a5e00d23e0e21ee10358137c0c9a372a10281a0e555069db32ee708fbadfb880c07dd9f4b743952ee5a18c4ef7a705331364912a1a957c55be95b54f22a07d813d1b06b586b5224f2fb8e4c17d5fa7f3893548cfd4b8ee7afc4ff84d6b105108fa397248c321209dc1bd9adb909b66b51cfec811e33d6651bfca99ced6b5f88a2bc852820cc509ee9e4502648d8351c548d487e9f067cc90b1c0e6ec2f5be38e5f65eeb7e9d1c401213514d065ccce797d9fd33586e3904e61c7ddc8d0607ccb7b9c5ceb9d666e056e024e05cf4bca630b9c20fd572e3badda9839f16788e1093a53f71aa31644aaa85f6b1a4bee61a0a76059cc542ff8f06f98cf884abb253911ee1064e6fa847ea77eb0514a48a9a9675155837a79ae8d702a539255defa0115441f
private theorem part41 : 2 ^ prefix41 % Spec.Ffdh.ffdhe3072Prime = residue41 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue41)
    (e := prefix40) (a := residue40) (b := 2981715340) (n := 32)
    part40 (by decide +kernel) (by decide +kernel)
  rw [show prefix40 * 2 ^ (32 : Nat) + 2981715340 = prefix41 from by decide +kernel] at result
  exact result

private def prefix42 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (32 : Nat))
private def residue42 : Nat := 0xa16204198c032e53d6c5891249903554fc36e1447e239000dd2f6545e81ce39985cad60c116c8e2053648e813b648deb3752698211354df35208d84a1f627953a7200c840d21a8eaaf819289f4e4ddf26380dc732b595cd3bf04281ed0b938f83b984bd1c4f636c30011eb9c8465ac690cb88d5bbbe625290e9f397cae34b5f625d4860808b6dbe26e7573ca0ae368d511b0a789b33bbabb0676ba2bd38d3bb314016805bdf06b53b7e418a7b137b57c85f6b63860b6ea697c5c9b60125324804f97eab808c2f8be03ef448d2b9f5a7fe9e0b1c6d6e3f3f14c0cb4b09ddd58fcc33c2141e9dc5fbe0bbb7d9fd9d03d24127b05970f980f1c8b00404d8e7f9d1decafdef0605fae0ceabf91c0d8367bddf6d63d5bec118b5b59810caa46ebd6d4a1447bab74d2aa90a2c0cc5bb718429223af4a1dd028030d3080d63c5df620623136522d1606c3e56dae02f89667c20e3620bc1e3504d4bc8e10bdf57decfe8d46c643031d07fcea2eb5ca896638e80736d45bec874afc102869e89d29f97d42
private theorem part42 : 2 ^ prefix42 % Spec.Ffdh.ffdhe3072Prime = residue42 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue42)
    (e := prefix41) (a := residue41) (b := 2240009188) (n := 32)
    part41 (by decide +kernel) (by decide +kernel)
  rw [show prefix41 * 2 ^ (32 : Nat) + 2240009188 = prefix42 from by decide +kernel] at result
  exact result

private def prefix43 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (0 : Nat))
private def residue43 : Nat := 0xa108fae169a98d091d4538a97ab1717b618fdaf741f354bf5fab47460486c161828d91ced509440e1831106b6d6f141d33bccf3f05cc974ed716661a24bf80c977f226cdb83ad9ceef0995d209a8b0da03f5a4478c00bc8de3dde7f37138f3d7d4401f8c09c35d1ea40fc9f90c6cae33dff92f73d3953011a4d0fb6c4c338989dbff7c211f6e2cf974ac0e5924e5c7f605d25c599b095a918cc977201976dfe23a2365b92386f4868f9d696a641c0004c0c601baf9bc0750173278913ee8aa26c2708c8bd5d6364e80d6fbe1662ea6416631b4e520f8a6c58cf90d0ba1046e655eebd645c2932b05b86b02b7e02f1a4ecef5f16a3f6298308604bba6bbb6e6ff4f5d8abd7398b492eb4aa13debb0776a1c58cf4fcefa06d25c8ecbbd26381a956b34fbfea59a86bf63d803f0b7e138fb1499bf551e10087ebcf1ed5e049b72bb48cdea854823a587b2459c7e4e5ff2d5dd7a83d298b1b2fab52b21c55d3d6919e5b71c483641b538da1dfb098fd0e07d167fbf6338882d7ad0cace35e4fc6cc0
private theorem part43 : 2 ^ prefix43 % Spec.Ffdh.ffdhe3072Prime = residue43 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue43)
    (e := prefix42) (a := residue42) (b := 1996830392) (n := 32)
    part42 (by decide +kernel) (by decide +kernel)
  rw [show prefix42 * 2 ^ (32 : Nat) + 1996830392 = prefix43 from by decide +kernel] at result
  exact result

private def prefix44 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (96 : Nat))
private def residue44 : Nat := 0x70148469c5194eb99b3f6d142e9738c1d5d1d27f57e5462648bf3b460424671e0f9d573efeef622eec025d6322c29de5553c56f0a9f7afd399cf244aaf756c23c7a449dbaa0dc79124f671920b01b7c060baf5bb67294e61de0c6e0db8d58d633ece8bddd6e0e755ae217cfa51c76c1f8e5aa2cb464771437b9e46eafd103e9edfdb335d7f9ffeeeb210a041eae6df65e888bd075ad87e7a20cddf82aace4132e207ffde3bbf6bc477101d05a0beea91b34f68bc5a45303c5369dd1bee75c45dc91a6cb9523c295ce2bab62acaae0dc079390e87ee580bf88a827ad5e6235b210ea2ef6b35ffb39e213f6df7ef407265e767cef045734a7555a4e266521465ab41f0dcdb5a2cc5525925381529302b4e6586cfda38f652c80daa80a8dc063353ad98ecf04f874396a6de42748618dffbec41dacd31593dac285d08c5554cb9d48cf88c6a5186d342dffed57bc94031da63a96c809b19f85399b65bbcfdddaa9d34f77a766955f5df36137ce9893d8907b5fc633710a178dc74879cb0d327980b
private theorem part44 : 2 ^ prefix44 % Spec.Ffdh.ffdhe3072Prime = residue44 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue44)
    (e := prefix43) (a := residue43) (b := 1325497968) (n := 32)
    part43 (by decide +kernel) (by decide +kernel)
  rw [show prefix43 * 2 ^ (32 : Nat) + 1325497968 = prefix44 from by decide +kernel] at result
  exact result

private def prefix45 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (64 : Nat))
private def residue45 : Nat := 0xa8c2a933385a7cd3a09486895c5592bf677ed209405305ec66a2d29f002b946426249434f1391e169c78ad45585fc762c60ae940b8a2a6a5fcdd88b73dafdb6cdc5ea8797178c9b13300ff38a83648b285c9d0d6b73398e0ab6df00f26213e01130b32921ca9485dfd039e4974af85d980d533eac4b22834d6a5e2ccda656cffca2c98960b25f4fd08ec2fdfb80821acc5623a92b438a01dfed2e6ca33fa05aac5e3ae568f045e2652d393286e890fa3a25031470a95127858542e2c581ea9e4e6f728c41e473eff95a0a718762485ca21e233bee79bd1dad5f93144bab23ebbd8705f67ae52bbda8539aee55ac7f929f01b10d757d19962a5a3a91a62d9e3480f8b57d37e446b32718f1b5aa6339d2877ba67d4523dabce5e2e7929dfcceb69d9c061050fb732c7362e9d5974a49e41c86ba11c56e166de5bc4660fac3458967b5228ecfd6a9073a7e31d2ed348b4969cfd92b880ef7a4f2c5f7fd0813e29b06b66d4cc4210d4276ffa82e5b7851bdc7466873ae58a3089d5aafd5734e47f59
private theorem part45 : 2 ^ prefix45 % Spec.Ffdh.ffdhe3072Prime = residue45 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue45)
    (e := prefix44) (a := residue44) (b := 3875271030) (n := 32)
    part44 (by decide +kernel) (by decide +kernel)
  rw [show prefix44 * 2 ^ (32 : Nat) + 3875271030 = prefix45 from by decide +kernel] at result
  exact result

private def prefix46 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (32 : Nat))
private def residue46 : Nat := 0x37152bd316628255d514ec94f4718b8f162638ee80ad37e6974e6a15cf9f19f9e1c960184b8997ee0ccb57c8cdf3aeb6c462c4500595d60023e7a2d1ec573683b1107f1eadef4e614679da78a1b2262ac34fc8f2570e96475f526714e6c1e75c634520c5f1d299cd66d7f11a54d514b3dce15ec175cf69612920430d592149a0c7389def29cd32dcee8cb7eca34472748ba75e2c6b3a625ea77ac02c4f9b78aed67208d1f2d7f4fd59e4cf0545a795f2e0ec8144dddc652b6a113f43dfa088778c61d1f6ca34577cde6d32da90834d1e409d4c92be18a896d0523270fb3ccfde05195f67cb8229a83f28c79f5d88d7f49329aee6257a667b65d649c79af8c4d4c2e956bdeb4afae3bf8cb69f50f86a1127a7cb6aa481899afb9fc597bb5ad80482309eb9dc021b7d5775816a95046012f8fb417fb830542a1e52c31f8db647b7a825e04a9a38fb1764592764669ae4e724a68617801d0e11184f47857729135fc0127a6cad0f67f41266b92db28614b8fbebef1b27fd077e3dd76278a1610fd2
private theorem part46 : 2 ^ prefix46 % Spec.Ffdh.ffdhe3072Prime = residue46 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue46)
    (e := prefix45) (a := residue45) (b := 1612317286) (n := 32)
    part45 (by decide +kernel) (by decide +kernel)
  rw [show prefix45 * 2 ^ (32 : Nat) + 1612317286 = prefix46 from by decide +kernel] at result
  exact result

private def prefix47 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (0 : Nat))
private def residue47 : Nat := 0xa9bdc59f196f9d7551c0b77d83fd99a9ba329eba4cf92f95a84728e5a4372fbe5f01e973626cff895b6785d8661faa92d1a00980f485c7280cd32908651fbf8de5d0eb7cfddb8419e980045ee10f760ed1324538d2ecf03532d93f6f21e571859aacd8d8737aa0b8ed3e9607d428e69f8cf5624fab70050a9afbef0fbc3d1f8ebfbc8a54cb5a21709912ce2bfe489441361d09d00fa7952e8d47a6af0ebcfe537ea475be7e83fac1880a68c2d5122486505c9dad9966b3cfac5914a32c79aa1619b3100e1c9579dc35996a1ff47dd2db3b079b9c0736ad128e7e3ff8f86ef469c48fd3a6d63f57e2d7cb96db7b46e49c48837b12ab9a217ad73b8eb6e1355a0315374f4cbe42ffb35b634a37e614a634c6bc6831e4ac7bb10d811d406713a1140ab15d4421a975e7aac03ef97f27ff9acd3b49894d853a15a8f088f82105f0482712797f01b75d3e1f16004113ab1d638b5dce5fbdb5abd0aa5bf994cc28fb432afeaa08e17855ec3074aa872c314accdd354db701974e65f677244655057c61
private theorem part47 : 2 ^ prefix47 % Spec.Ffdh.ffdhe3072Prime = residue47 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue47)
    (e := prefix46) (a := residue46) (b := 2484737968) (n := 32)
    part46 (by decide +kernel) (by decide +kernel)
  rw [show prefix46 * 2 ^ (32 : Nat) + 2484737968 = prefix47 from by decide +kernel] at result
  exact result

private def prefix48 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (96 : Nat))
private def residue48 : Nat := 0x515810c96857dab8fee148355794365547b3100a7d10569ff11c25351699e1de8c7cf91c1bc13f707f39845aca35e0d60936e653aeca274d0b7821193e154cd78fd41f10da7ae996fb65f4172052629ee0c521be3b0f075a153dbadc95ff47cfcff98279200606a50fc174c1d43573ef6b8f076a316e1fce53c91a33df580ecdfc7693fa4372c415509f2ecf69de8397f90e071cab479d6a771ec30233858dcdd01b69dc814ea43c7eeea305eb212526173648774b19233970ce3a7084951be7272a321e1d8bb443a15b1b89a18e663762ea64dd9f1229d1b1e1c40dc62e2d53507e6a96ccaef0882398cc3b532ca85f922455e9b7384759062f4e956eaebfecb92bd2cc89749bedfa110dd024a4121173ef73aea6e26a95cbfb6667e55c35844031bdc143db3636145e595c34576cbc1997f2229139d3467e2dedd648fae0c60de3052cdf81950becf479583fd7dd3cb70fc656bf6db72fc97a16b01a416eb2fab08d067bca84205d3e470dcdb22c4ba5967a965a17fa0b2faeb5baa7b98979
private theorem part48 : 2 ^ prefix48 % Spec.Ffdh.ffdhe3072Prime = residue48 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue48)
    (e := prefix47) (a := residue47) (b := 3367599950) (n := 32)
    part47 (by decide +kernel) (by decide +kernel)
  rw [show prefix47 * 2 ^ (32 : Nat) + 3367599950 = prefix48 from by decide +kernel] at result
  exact result

private def prefix49 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (64 : Nat))
private def residue49 : Nat := 0xf542467c70a7a114ef850064bb073a1dd2e089a35c5d627a9df997d7c8ce289ea24349f5922ad9bb87470aed55186929425b5bd543b6716d6a37d332d7e7d055157ecf8a6e0822f6b1f545c93edafe20130c6f5560048fb6e752fd673e4137432f5846935056d9c51c6717f427a676d67efe0d1bf4900b558025208fc7304db4a80cd5eaf4a986182dea6a2dde6a37c0dbb9b48f76b03a314da37cffe2fca79d3efcd50113301bf333bf0138002a0ef5fe4425cce3518e3fe4dcf884f20886f905c48ff09308986bf59e385c28fe8b4debda71f3bf530904a8a9215963254bfdbd14a7cd9e789abfed944676e660068dfd6f55b07fb1dc59dae1abee659b647e7c1f8184e4ff992d1c5933ccf79653e7294ae0115d802761b866976fa11c2a4ac20c3a5e3fcbb7096dd62cef660eceff5741630202b98f4038866553dad0bbcc7c6daddd7cf0b791bbff58d0c0d86bb50b0172be23e99dfc02224982d391d13b922fd2f7b5fc58786d45aa064ed7af015f3ac9edb64064236d8e01faed038329
private theorem part49 : 2 ^ prefix49 % Spec.Ffdh.ffdhe3072Prime = residue49 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue49)
    (e := prefix48) (a := residue48) (b := 1958920703) (n := 32)
    part48 (by decide +kernel) (by decide +kernel)
  rw [show prefix48 * 2 ^ (32 : Nat) + 1958920703 = prefix49 from by decide +kernel] at result
  exact result

private def prefix50 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (32 : Nat))
private def residue50 : Nat := 0x97905cd0d01cb3125694e8a213391ad0d729c4724b56c9051153a40bbc5bb8c493c0433945d26df89b1d824c76cd49b356386fc1647f60a4946590662465492d55c7ebafda9f3d125e37c6c5e1abe99b851b11876b76f9f35ec4d4a8fd121643bb88747bb3ba197afa5f549d59b08d2e53023b3366ecd67b9f8d4a75e0f09898bb2f28c3105d3d0db3a538b33b19dc2bdd49ce09bad3a8a3b292a109e5104e76d0ef7942716371b12ab9a0da3bb9ab47839876cc3b2ba961fcf369a713dd039d0821298d8b8f6cd64f4595d27e9e5dd4d34b6283a13363b0310549b018ed3ffb80b7f5e5fa83c253830e4dcdb611898d1f0f012388fd44c615d6d548f8bcbf94cba68bbb859750c6ba62856a627937b60569ff6a10dcb87b3fb8e7217fc4991d712c628144e6afc52b4e4d7c8469a3dcd9758a6db99068bf98084e4cb18c65cfef4ee61b82cb13de00f66974b9362d1b22bd58d1f5644658dbae4ece7a690e93372991542613b1816a97b9b4af456ec007082c3c61717951131cf54b083eb48d
private theorem part50 : 2 ^ prefix50 % Spec.Ffdh.ffdhe3072Prime = residue50 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue50)
    (e := prefix49) (a := residue49) (b := 3341256985) (n := 32)
    part49 (by decide +kernel) (by decide +kernel)
  rw [show prefix49 * 2 ^ (32 : Nat) + 3341256985 = prefix50 from by decide +kernel] at result
  exact result

private def prefix51 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (0 : Nat))
private def residue51 : Nat := 0x20a7671fbbd968e14caa36a3eaff894cb0fe3ca48ef23148c17cda66629034f685180c8b97f1eca2b0fe30ede468218d8c073e1ac88e72bd97d4a9caea52c55f4ca378f72a0620a2bff46d64332360952e3ed3e46d2563b74b669eecb6e35c2e75515039e99ef56ba4d9fc4351ce81be362ea471a6860d18c9b255069a36ce6869b3004cb2e5fd5525d055fd2c841f0bca2a45dfba5167fe2ee8a30effa8a8ea8a0febf4dcecf97fef2facff8ce2517b352c6097af0bca153ab7a927a8f44732953cf5b6c08655a5f0f33b75211116f77551d24f43520c1a1d835c7b5c42ec4df643a32474d3e856fd45b04077da6759d3e761c087851dfc5e5935c0da9a79408f233fa41cb189820927bc98ba102eb24d2102892e154ea6a9a6fdadad843b6034d065d49104e1563b7344b12c050474807511e128274f951ac10e3cba2ded37b14c547b1d95d3b689a4df521e38203943c9d3b39787a9d122fbfda5dc7cdfe11d0b68af8c9b916cdcd645a651ad69d5c55b442793d67d05fa78bb32ce00cbab
private theorem part51 : 2 ^ prefix51 % Spec.Ffdh.ffdhe3072Prime = residue51 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue51)
    (e := prefix50) (a := residue50) (b := 2004435137) (n := 32)
    part50 (by decide +kernel) (by decide +kernel)
  rw [show prefix50 * 2 ^ (32 : Nat) + 2004435137 = prefix51 from by decide +kernel] at result
  exact result

private def prefix52 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (96 : Nat))
private def residue52 : Nat := 0xbc6fb042a5ee923fe42c4fba29fc83f59cb0d48baeba52738ea3ffd283792d50304f77c10f7d16938e879319bc320530655354bd22a4d1542ff032e437b20c03f623c81d01ce61e14254f4a86c5c2f33ecc436e503ae886741d25976c11207a7e41b991602820f4a0b7eb425209d2a0a0086c4d1049783cdaa27c31f048b2d83cc38b3b207ab00ada5ccfa77ec10c8efe45faa83190d947ba3e250f4865cb064e58133e55064a8e38329b4a17de5c6c4a194ba8d5555cfab7203c11545451ff8eaad36b201a28b8b6521a5e9102ae59ef5f4d9180d3a0ee8ee731cbacd273ba03761230ddb5c5c86fe4ac806bc974d81a050a2e32efabd538de3a0f4ad14a3af79f326c48f4274ecc1ee558cb3b4948de4b968e7bc2427f84cde8eec77bf275f2f78ae73f01a2a80f71b31799fc37321c327322b25268cfdcf8c293e9c768b70ab579f787955a3771e6a76963118752b90a724bba3a173c47cbdfda361ec7a74368d44bad8db2628273484ff864c01689983cd6b8327cb2f6af1be79a9fcb3be
private theorem part52 : 2 ^ prefix52 % Spec.Ffdh.ffdhe3072Prime = residue52 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue52)
    (e := prefix51) (a := residue51) (b := 3791592845) (n := 32)
    part51 (by decide +kernel) (by decide +kernel)
  rw [show prefix51 * 2 ^ (32 : Nat) + 3791592845 = prefix52 from by decide +kernel] at result
  exact result

private def prefix53 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (64 : Nat))
private def residue53 : Nat := 0x11920eecc7048e245ba61e87a7a7b24182ed980bd97d945c170f622767de368c578ce8f80d0e9174cc6c90733455756ae49779b6f5542306c52387173087722f0103876bcfc9e0bad8306459738374191ed2d16505439f8b7e6ae9f192500a1f323342daf36b2dedf16c0cdffc1cfbdec9c712a9f4d75357136396f78278d0815d0002f7020a738c4015bc1dc2d2ae5055339d37ede8d8ff6d3a30afe3dea87fa890c2f0bfa2b538f31009b270afaa5cf18789fcccdc76b7cfc2597af44c33bbd0d7ab4cb05a673520ed3cbf18fb9375583dbd598a1c10c9c210d9d52239ca076bc4f9b44aa8fb9e16f092308d987ca8ca147ebd20682baf498f69c7263728305705df0743983972f899aa3ddd40f58d4a86eb7ff861f0fb629aa08bbdf6b34d99633ff3eafdf27ddf4ea58f7fbd2bf5040aeac44e108e48c405d8cfa203f0154067418b0773c3b29a249e7f2a73f3dd3772dd1404127c2b6c09c37d46d8de23dfbec37744d93fc3093a3781767f5f919aded0507bccd24b1d926059ef820514
private theorem part53 : 2 ^ prefix53 % Spec.Ffdh.ffdhe3072Prime = residue53 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue53)
    (e := prefix52) (a := residue52) (b := 2788677305) (n := 32)
    part52 (by decide +kernel) (by decide +kernel)
  rw [show prefix52 * 2 ^ (32 : Nat) + 2788677305 = prefix53 from by decide +kernel] at result
  exact result

private def prefix54 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (32 : Nat))
private def residue54 : Nat := 0xa87f2c740888f54db0e0bb2cdd4f3a52cfa086358eab52e6f0ae16a32b9c6a085911d4984a5ed22d8cfe2141789b89b1639904a6cb064016a2cb47d6b7ba51b24aeb7fc7dd5ce218eb7e0882ee469db87cfea370f673a63ba3c8e1cb36d13543e45c542db552b3ccd8d833371afaf7f79d097f35cfe8620afb166755d0c94eae8d9893b69a8a4fd3feb12c3e4581cf90a212ca2a560cff80b2ad9b6a9812ae6e1d77f2e34b53eb9e2f49f4850580ae1cc01e998d43c5c77f3f0381a42542e4472a50b73765dd16e2627aad9d89b19ddb2d43cf5960d1352136f2c04f7215ffb4db7e2868c4aaf0b3c33708f3302c8224fdb1af27bedd9603798f4405d6be3d07f565e26e8c61cd5be09e1fdf85624aaa0b756e226757d0398f194ee4f5ac900be9670267de205a9dddfabd69b95e4df59b1848e9f4125eca747187ba525f4c03a63d2e5a69eca9b68987bb5699d48a24232fecbb8c62ed65b6e637299f288a57797cda0bc52936763d6367ac2d928ed79c86d5766c56c3fdb0196f6e2b288ded
private theorem part54 : 2 ^ prefix54 % Spec.Ffdh.ffdhe3072Prime = residue54 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue54)
    (e := prefix53) (a := residue53) (b := 2648374878) (n := 32)
    part53 (by decide +kernel) (by decide +kernel)
  rw [show prefix53 * 2 ^ (32 : Nat) + 2648374878 = prefix54 from by decide +kernel] at result
  exact result

private def prefix55 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (0 : Nat))
private def residue55 : Nat := 0x8a65815c4d72726b0453d72e3cbea46b7eaa7a3ce9c811c5ee5bdbce3536bb6b10407a49fbf408b64456edc574206550bcbd63478730adcb273cf3cfff2f61fc7fd4c36c72de52cb7980c52b4d7f9f40c32eeb25d51184ec39096db06c5e89bf1ee4c0e66840a65c8447e58006bae72e52922add38214440131e0fbf9a974cfba34af284e5e41394b4ee1999b55b8c4bcfa69041351cba665f7c3f521c1027b3ae2449f916cbb4451c0a7a7d42074b14a9c2db8a5888885a1641f956490540d6a27f5c5348ff62215acb96a975d56cc5db9e7d3936334f254b28dc0afa18c990eba38fd1a8d4f341e1c7e68a8e70fb424e0a90ee9be4d3ea9d513520be39c2cbf4582455a0b4f1ff984ccfa42391ee3109f95149514d03673ead116ddc4a4358279c6e2b81be6232df2874a975ab06228b5410a7bf0906eb17af7e0e1ea9d6af78475413d1441362bc0bc9fd25f2e5949ffadc569c7873cc511c30b3c105e1e0e9099e98bbc576db59f0ba76589feb87883308cc14dcbf8b52b2167cd5e5f509
private theorem part55 : 2 ^ prefix55 % Spec.Ffdh.ffdhe3072Prime = residue55 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue55)
    (e := prefix54) (a := residue54) (b := 392237058) (n := 32)
    part54 (by decide +kernel) (by decide +kernel)
  rw [show prefix54 * 2 ^ (32 : Nat) + 392237058 = prefix55 from by decide +kernel] at result
  exact result

private def prefix56 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (96 : Nat))
private def residue56 : Nat := 0x4776701ddef767114f1648ba9bb1879ea97c57f6cdc8483e015ff5b42c381e47a6b95d508dfe5a87cd064f6c44bb8c166ea6ddc7fa2abbc044902c2d476dc22ae70e4a200bfa96d7f5d93d10d421a506608920d4da81ba39d48c30ae66ee702252e6415a6ce9b53aef0648da73a0842fc7a206ae4459053731464b00aef95594edd4136006e609bb82f3e85744f43b89329de89c20fb026dc9fe3558902201a10add9ab8c98d1bcc07d1d06d80d6d594372a543b5b1848908f5c9b8cf3b26f0d815e57d90f90937f401f706e3754f46fa61c102d7e94438d0d04358e9fb49634a8e3baeeb7f3e073d9c314a50d8cd8bf1e53fd35f1f32a9397b7500c601a98a39e332fc4cf0af36c59b713aedb61722039327c6e6f7acaf5cc6a1da08d5df68784b99d52637fb28388cb27f36beb2386a84198be72bcb58ba699ac2b46c07cba3375d3cd1584963badf09223bfd7e18d01eed6955094f896f312f910bcf64086ba208f19cdfae4dc885566dad3b6916ce507edc970cf42a5b6ad6e055fb84ec5
private theorem part56 : 2 ^ prefix56 % Spec.Ffdh.ffdhe3072Prime = residue56 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue56)
    (e := prefix55) (a := residue55) (b := 3804723393) (n := 32)
    part55 (by decide +kernel) (by decide +kernel)
  rw [show prefix55 * 2 ^ (32 : Nat) + 3804723393 = prefix56 from by decide +kernel] at result
  exact result

private def prefix57 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (64 : Nat))
private def residue57 : Nat := 0x7a4bdca8cc48a6de9112a13c9f642de21685cebe7fd4bceb613c6083ef5092e0d2b99f9e8f1718e2845e111ef51be917a0570c8ae6eafa67a8e9191ee9f050f929f1b4b37013911355cc71f760b9c60883b2274edad241a2d16e48df015754b78c0796b3fac0a959ee8a2e75d0593ceea4a14d3889161a5b246f81a5166d339c19726066b4582761a8e1ee31fe0b62a1d2cdcba4e68c75f059c4b66553cc64fc1b0d2cfbf2109898f86aeb191970b75800471c61d87569ebeceef72e5783529575f6701906d14d56dc62e221191e7a718e8547e20a31b019a96e87dd4696ff67348c101e038965847f62b9eb780d0e770e07d084de0d302844e7c725a34b3200b4438492b9e1e7519e08180ce44df3c7b35e657c336ee6e62290cad30868eef9f67f7d0c05cdaee2e82cbbd720b6abc89cc08bb4b1b970c8e1ac160911ecd4b69c4d6cf400c01143617adf3ad43d587715124867babf53db25549c930143872db602930b7588e2bef4d9a6a9710df51eacc5cd7a8c09d1b50508de95367a4ac8
private theorem part57 : 2 ^ prefix57 % Spec.Ffdh.ffdhe3072Prime = residue57 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue57)
    (e := prefix56) (a := residue56) (b := 3196797401) (n := 32)
    part56 (by decide +kernel) (by decide +kernel)
  rw [show prefix56 * 2 ^ (32 : Nat) + 3196797401 = prefix57 from by decide +kernel] at result
  exact result

private def prefix58 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (32 : Nat))
private def residue58 : Nat := 0xbf3a542601d4afacec871e0465f0565970261303049492562d32abe8a6967a598fd2a3e9081451474f06a13a5ca157e857690f727e8fed9a19ca2e841c23035a7b85e4f3c08acc6f24c3820e1fee34ae22c01fdf43d869d814f24c316bf309a273d25df82056c32d8a357c9bdc8b2700dd90c74f05d381a4e06ed36047712d6fc7b9a061b9406ebdcd2aa2ab83fc44bf596c7a75f0fea1fa662939cdf1a895f5133cb66fce3c09e1789283213338a14c5195c3ce52fd2478f0729ac121f3baba1edfdc24ed1d30671e77950b49db1d35d21d9df4c399a70f88738ee27acc7d0ba9ce29c3277e5a810c6e3fb68bce7380abd9b9b1105a3dcf3f8ef4a36bf259d435dc069c0447f84448a7e43c9ef5a49b2bf14642c4d2b83749646fb81babc1ca478c78a7ad24a475cd152a8217c0e12f7ba92e65656c45b547805dc6bac2082ef37e866d572d13ea621da280c8f7aae5307c986d68bfaa9b6b073f25350bdf6d9b11029423e27a36baa2784fa35c7ee8f25040e43fef4c27c02ae94e7de2d974
private theorem part58 : 2 ^ prefix58 % Spec.Ffdh.ffdhe3072Prime = residue58 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue58)
    (e := prefix57) (a := residue57) (b := 1668916499) (n := 32)
    part57 (by decide +kernel) (by decide +kernel)
  rw [show prefix57 * 2 ^ (32 : Nat) + 1668916499 = prefix58 from by decide +kernel] at result
  exact result

private def prefix59 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (0 : Nat))
private def residue59 : Nat := 0xe0717b6c9a1d72a5f9c47c7512e5ae60afd50695dc817f37986b9d61f842ad6fa1a4715186f024d35bdf30cc613c32844d169dc1cb107d7a88b70f17f6cb11185aa002eb1b0a4c7a86c4f38552407e22f7fd6490fb3726355c4e87097b1c33d7044a0299211e8ddd081ac71c12303cd67550c78b06616f75c45609f40e00f4ee9f4521167173eb71d256a7a1adb1e6c53c45a979038f5ceeb16a452a05fab66fd99d3127cb056472374147b2f0ba77d75d42ebd54144bf79d5f8d51edd9475e57f85e501fd8d7fbfefd78207dfd8126ae1ae85bef30cd8d5c77e96a6a66b4f691e38711bb1018e858e263347f27c2eb5ded53b4b01e9a6db3956a942f149f72a0eb8749878d93a1b7582dff3a2ff8acbed6df2ae0c08798125417a9e251e18373bfb726a67c87ade4b550b4b863626f06398c15e981c54940d0d98899d956ecbebcfbc573f833abc09ef5a6f8b3fb67c6f4b371a7de3e5c0074f18943a6d712d172156e9b5594c2cfbdf37f986a424e65b5d486cf308e2410f994edf928379a9
private theorem part59 : 2 ^ prefix59 % Spec.Ffdh.ffdhe3072Prime = residue59 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue59)
    (e := prefix58) (a := residue58) (b := 1624864765) (n := 32)
    part58 (by decide +kernel) (by decide +kernel)
  rw [show prefix58 * 2 ^ (32 : Nat) + 1624864765 = prefix59 from by decide +kernel] at result
  exact result

private def prefix60 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (96 : Nat))
private def residue60 : Nat := 0xa0cb21afd1743a42fe509c0f233f74cc25e31d06d6b46119e166aa99fe031896a679fdf445514f79108a3f4d5e665a447e88fcb29c69c074970368c0b1c5208c4f025888c4a4ddcd0856f1ec04caac05f3f2a5c3973b915ea4ff2ffe3830615291730484969b48b515dd956c51411095c15c22ecedd3fb9c426cede024a415bcf7f36fc78f8cd56d9f6f2eca9c5b52b079748daff0cc68b1905f578186efe382f0f9b8124ebee5ffaa0c5b0106001f9db998b550ad8201616f9d06c6cfac1949bd5a38bf2ace9d6b362b78ffcfe4494fa33bbc95016c268d693968762c8e3bd7b6bef70ff3e45e173cff50d2194f6de6e76f285b6645288ec63b610cc90349df77774265c13d61474bfbf88071e99a42a2c98d2ee97fef4bbe2ab55972db54170738c5d9a1cb5be548e9bfe68a324879ad309ea1a14e3d75b9cc2f0c5379777ef0bf3599a095d5cb6d6ac958bb25d6249f77fc783ec803969feb4749d6f38d4126d2514328aff6ad3cbed2a9482f5e43f02baa69e66cdb6faf647a69df946523
private theorem part60 : 2 ^ prefix60 % Spec.Ffdh.ffdhe3072Prime = residue60 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue60)
    (e := prefix59) (a := residue59) (b := 1144365340) (n := 32)
    part59 (by decide +kernel) (by decide +kernel)
  rw [show prefix59 * 2 ^ (32 : Nat) + 1144365340 = prefix60 from by decide +kernel] at result
  exact result

private def prefix61 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (64 : Nat))
private def residue61 : Nat := 0xf96df02cb9db4fa3fbba58a46994f377879ce788e76ab822b68f6abbfa397e8f85b8707f51f5f54923f6bb4976e207c032ad4d950355d1f931c5e456addcd81114c82b2745db14e7279de93411ec27b0d349564dc7921fc3255924d002b193e7bc89dc190d31f0f6a95a7bceda5d63d7db891eee393198f517545e1d682297c3588857d3e863cb86869b3bd988a12939da1bef3fc021c44979f919cfa4af198ff88b4322dd3a2749ab7ea16ac8f10735e95e5a900381de205dedf4cc09386a2dca3ae77b569c54ae8a8a6f46e1b555705ca2f3265d7e414eecb8d8676fc4f7d4440006b661d3f2b62c27b8713ea48a54b60b05128088da485afd730ed218b37c52f6e521cb2e0c45dd676c10bb828a1ef518a4465aa27d5f21a3b03355da6910fe9a292ec47469324a1169267a769b043d969d86efd71461a316eb39fb9f764e47d7f483f6c449f3d6132683b57a431bc1ea998d95f6e92c70423ce0f7849acd911f328f1d04ec056730192fc0ac783a4934ccc1a318d0eb6ca0b7403dbbddb9
private theorem part61 : 2 ^ prefix61 % Spec.Ffdh.ffdhe3072Prime = residue61 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue61)
    (e := prefix60) (a := residue60) (b := 814737390) (n := 32)
    part60 (by decide +kernel) (by decide +kernel)
  rw [show prefix60 * 2 ^ (32 : Nat) + 814737390 = prefix61 from by decide +kernel] at result
  exact result

private def prefix62 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (32 : Nat))
private def residue62 : Nat := 0x5491ef21bc7fd21b944aafcbb4f3e247413e4367bb88cff7d4dda80c6850c703ff32d8cce813279aee452026eb676554134eed51b3c94ad66064665f0c692db381f55ce42b697ee38336e49b0e91e2d491fb4fc815459557d509aec6c0724a904350b12b5a6098740991df1e99250e977cc68b70f74bd37936f7a5eb1c0e802753741faf450bb3d3a9294cf60ebc7be0fb7f471e20fe094464ff2bb3dcc0503449ce718418e53f65179ea548c1d78e4b03ae0d1bfe9dae49ad6a45a51b5e9d3e1b8b7a90a58540625137e67d59a974c152bdb31576855dbd432ebada9bede37bdf7fa6d5ef7acbcf2fc58b5bf477afb0685f617e751935fb0c3b02de19451f2e1d5eb04341105b78af281386612f7e096c12874bf91da6fc205ba673d3b3906248238a540aefd96a3139dcb8318a3251f6f34b1c5e61ed32f7a564c2429130423306ceb1f31ea81755169b06ff04dee2e5571808f701c709a49927f434db26867d4670a8180c6efe49bc4facec2c964289421f15d04e827c8fd90a01677c2dc9
private theorem part62 : 2 ^ prefix62 % Spec.Ffdh.ffdhe3072Prime = residue62 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue62)
    (e := prefix61) (a := residue61) (b := 1864019357) (n := 32)
    part61 (by decide +kernel) (by decide +kernel)
  rw [show prefix61 * 2 ^ (32 : Nat) + 1864019357 = prefix62 from by decide +kernel] at result
  exact result

private def prefix63 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (0 : Nat))
private def residue63 : Nat := 0x2a8032ad0ac9057abb455eea0b5875df39b5fe845308a8df2b92cb99584c869bf75ece925cdf1c58ba0e3c897a72fc09a240478d2fb2715bcaccd4a9477feaa74b5bb8ba84b9a912c312b9bf414743406e5f11f03d83ae350623fc2d4b3967501c03289882189abec1c5aac6e2debcf3a43c3c5da1595abd8f2edce83a3e9aa1527b3d38d6f0ca710656f2b32bd6c9e3e61acad67e4b588ed18ac06a06b03f7a2f486dd83035b973af08a8d321ac951928c23870dff44f9bb260f6fe4039f2ee7092c5a33ff1277cd5ae9d4801c0e19bf9b28d3185297b8ad3e700e35a340d38a317461adcc8080c48ad68d2834e7f5488fc6d80f54be73813de8c4cb7b48d7ef1c490184c91f9f9f18863a4c8c75c8f363a545e6af8ff4eb47582e30d0935f12c650beeb9c4b0e312d9c573af32ddb18fbad2576dcdd97fa2d960ae9d1f8face2407098d84d2333bfa2efe25fab3b8d10f3a820f5ae499e597a66ef84f20c443ba9297bfaf728e2375ba514fc517e41771e032def1cdf569ba96ab714fb10dd
private theorem part63 : 2 ^ prefix63 % Spec.Ffdh.ffdhe3072Prime = residue63 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue63)
    (e := prefix62) (a := residue62) (b := 2995552685) (n := 32)
    part62 (by decide +kernel) (by decide +kernel)
  rw [show prefix62 * 2 ^ (32 : Nat) + 2995552685 = prefix63 from by decide +kernel] at result
  exact result

private def prefix64 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (96 : Nat))
private def residue64 : Nat := 0x3634df1cf87ff44f0efcac8d02a0cef7408bff08d110cc0b7ec43a6c8abc521349ea67d8513724c6c66b5d5821871ddbcde0d397b1cba9e3e169f55147be6e77b4404b2ae2339e78b78c0575903185684c5bbbdb5e3aa4bab1aafc66f1d0bdb3aa29d7eb2bf8da54cbc9d3e3dddb7bacb33f6b6a8534da5c28654d672c829463fd6fbd0a63ac709697e4ea83a65497831b4eb2e0d2cc1c85f64c12d5ca4548d63495f2afeae70a9334dd9d73a55c867eef5e99219aabfab2d0a15d4cc18e5d74ace3c37b4c83c462f54d273605992fdc82644c4d19fb8269dd0eeedb9ab645f6ebb2c7859a7c606331478d88257cde0bd75c47c3dc3559bf16645b980e9462d4cae4b35c9c804d0861bbcec595d5c512182a700c5b2330af85ca10a0cc2beb30b1b723b1f8ec2412ce293602aaaea96f7d1fb9004252d80de3a4428a308ac61aeb3311162816d274259c99c646ee60d627ca479c85fcf60bee90f53986aa0d7d9e6a3e7c682e19057d7b3fb01f8c59dbee0fde63a06985dd499d67ec29714a02
private theorem part64 : 2 ^ prefix64 % Spec.Ffdh.ffdhe3072Prime = residue64 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue64)
    (e := prefix63) (a := residue63) (b := 3726277231) (n := 32)
    part63 (by decide +kernel) (by decide +kernel)
  rw [show prefix63 * 2 ^ (32 : Nat) + 3726277231 = prefix64 from by decide +kernel] at result
  exact result

private def prefix65 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (64 : Nat))
private def residue65 : Nat := 0x3b261d2916a587686f8af30f44f87ea76bb9d1528ff5cd7fb72825e2937ee3a7c27cfbd9f48e8cc07d47fe38ce0d0d574d9503ae5506df4db19aef72fa03b6acbb3eaf90c27297177c487df85f1aaaa12f5a3df9566b84338c6a4aee090fcd9d074aff3c11cb0cf9a77bab31094705c560500395f5d9a3a2aa837a8033aa7ba0352fbd91a033a133602231b96c7db2292e1cf33f4671ffec929dccbd019725779ad9f54fcab44d73dc256e2254db2ebb7519ab640e7e89c3d5eaea998b1a28e5faef23eaf7b13c12b99d748e7578ec7681a1a01c506465aabf75ee5c8d20f6342e558021915d71a863532b9a22f7895ce4a4b699a3d2ab4b23c9fc0d9d453b62a9297fae0c6ad1ff9798215ec4e2a59aa21859aaf63d596ef010ae05f2b2442be93ba2cdb12abdbfd87c2921b46cfa7038553d78e4e0e981eea5a78471ef77b025e5eef237d3a2d3caec2244f5358b1f66f4d3b61e6c846183d0816a8525592337a2eacd168cff0d9babb2ae1a74997ef76b35a071190ff53166af3fb6cba01e
private theorem part65 : 2 ^ prefix65 % Spec.Ffdh.ffdhe3072Prime = residue65 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue65)
    (e := prefix64) (a := residue64) (b := 2093875484) (n := 32)
    part64 (by decide +kernel) (by decide +kernel)
  rw [show prefix64 * 2 ^ (32 : Nat) + 2093875484 = prefix65 from by decide +kernel] at result
  exact result

private def prefix66 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (32 : Nat))
private def residue66 : Nat := 0xfb7b4fa5f174ad4a027e16f2d3655b15be047e7934d356085ac9abc31ce5bb296fe6d4030b4d4ddebf2d84688f2edc622c081852413c494b7988956792fc854414cb504c34716dcb9251b85b53200124959372f00e2d2af43b9244f0fb9595827edbbb3c5da96c457e7bfc1bbef22ad53583d67cdd57b588c49f2e1bd31ef4a5c6e617cf2392fb4c501ad95833df5f8a0fc868698069d1db2b29ad880fb3a7b95eee0ac680ef31d1178f7235295fd04aa420aaf26d8f4c1a097ca8d3ec0df5d4eff571075f21f127a28c4254d3e2beb6cd8af053cbad4d394b2daac72cdf70aefcaf842ed24c0dcd11d1398f678f5456105bb97898e552c8b670162e0641aab3434d3442a8f2f29b0fceff20af4776b652b0a5052e8bbdcc7b1ea57eb3ede92db316080254279a32c6b91bdab4200ab73af71520d20242c3b896957efab38517016ba044ec45b4d652a896d07946a2bb6523808acc71a1b5d7f7a7bca6034678cf469bf0fcf71d260f9d938c7e7e52d275ea9effed8c39209b736fbcfd1bbf22
private theorem part66 : 2 ^ prefix66 % Spec.Ffdh.ffdhe3072Prime = residue66 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue66)
    (e := prefix65) (a := residue65) (b := 819607524) (n := 32)
    part65 (by decide +kernel) (by decide +kernel)
  rw [show prefix65 * 2 ^ (32 : Nat) + 819607524 = prefix66 from by decide +kernel] at result
  exact result

private def prefix67 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (0 : Nat))
private def residue67 : Nat := 0x5e46d663f06b36bb0567ac4f7e079468cd4ff51f7581b9de9889af95773065de4f0ba718077f3832bb6bb1840c676cd47fdcc2614c8775fada07b56a3be8975f70114e4b423f1815f609c2748e3cdc5600a3be1a2f48bc1eb09a23e2415c7fe6037e24c3dc10a6a030175df878462e483257c11fd9e4ec3460b0384f7f593eef6383819d92d1a8354771238d93cc9b1851160dedad64927a430cc5afebe2da55fc7d63758094bde28bc10b8f96c67ebfeb9e21718c33b6b5816e7c7292bdde14d4361fbba5cd13a6867e886d47b13597e1502c662b5693f032ead7a96c8fd75fb08bdffe1ce2e82deb00114c517ad01b83017e47de60b853d309cd607cfea38d0b3798a2d41987c2e397a59d142d5a24e764bb35b1e10f62e8870b5da9c9957ad365d5abd624908a2676eefc21b3a317e6bf48cd267a7fcd5463b00e9b72d833ab97753b0da3dee7645ded0d96485e448d417c5e5a0cb244c42f0e0762bb5be266ae170f55583a00d6527ca48eac88f76867a901ba44f150a1791a44a08abc91
private theorem part67 : 2 ^ prefix67 % Spec.Ffdh.ffdhe3072Prime = residue67 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue67)
    (e := prefix66) (a := residue66) (b := 3950208131) (n := 32)
    part66 (by decide +kernel) (by decide +kernel)
  rw [show prefix66 * 2 ^ (32 : Nat) + 3950208131 = prefix67 from by decide +kernel] at result
  exact result

private def prefix68 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (96 : Nat))
private def residue68 : Nat := 0xf2d378093f97be4a70b9306ec28639b57433bd036380a397d472f061208e5c0f82dde6117f21bc874c7662d46d1d49dd166f32cd6d0d6348c70b6c1167b0eb3479c8ab709a27bcad3411f6f0de6330db4a1c6a4abaf74a5c2ca7d3e189dac6ac3eca32516250cad698c2eff7f21828696045a4e014663bd62fc8c146306a581c274e480afb6e6c8e4ce6e54118b6f88f94f8daf302f6e484713bf91adbc0fde25150237450562be3e44bfdc4b6f8e8f9b32caf5a85677fadb3d3925330f87ae592143d183247995ccc8449099b58cd53196d55470c33ab1c6039440bc4cbf8d0094d8249c40a66f95c0fc709a1377bf13c9284002a912bf1aac3437e048f007e4f4bb94dc83f8f1c2d9859c8e8647995fe60d38d37a3bd531010fad934678d47486775ef37d06a0c0d20e7d29a7c20a1e0fde3a644978ba9feb6045d1bff4c35195feec9056eb791829b2807ef9f4ad8fad768d395e5bcdc84e1c8c8b95d038e3e9e0fc8ddf83661aaf78ae36e171ba0ec6cda964a11b8396f6ea909e3c2ec7
private theorem part68 : 2 ^ prefix68 % Spec.Ffdh.ffdhe3072Prime = residue68 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue68)
    (e := prefix67) (a := residue67) (b := 3178008211) (n := 32)
    part67 (by decide +kernel) (by decide +kernel)
  rw [show prefix67 * 2 ^ (32 : Nat) + 3178008211 = prefix68 from by decide +kernel] at result
  exact result

private def prefix69 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (64 : Nat))
private def residue69 : Nat := 0xb5955a3c39da090db404a3f8478cf60cb3ae151dd3bd179e33b8ea0d3a48bde9437e9853099eafadc3b9a30979e9fe97a2ec2b1b117fbeefeb231be5a59cabe744fedc5d7e9e7251a6d541df7b5da4903fbb9613a0673f610a62b7df171463d1addd3e6a6fb4d42f4cd460125d0f0fb56b49092e1166ef6d1bc724ce14e2346a693ad248e460e676a498b04d1dce036157d701ebc5990cfa709ba2bfef09001eddad7b5942316d0829b7dd2e62d7ef2a53636197fda856c7636bf5ff3eade43db3a75d5157b343d69d3674ef08d5d06a3286c08569db564f2a8f7eefb38e225880b79bf8e05eae5a3165e45d696f46066a78e2ae8d42fb9be66622d345bdddb35001aae0a52942ddef88a689a157b380fcf03507b8bdcc8569e01d837c766630e6100c732bcc231f1addcd49110f8e277a54b76482efbf214cfb40f261910bcecb3487d55509b8cf180d12cc3d56c6f3b1f29da2942e539ab08791e9ae868b326291a5547456f6e219528996821ab4e10659c2296868be31c931786782e5bd49
private theorem part69 : 2 ^ prefix69 % Spec.Ffdh.ffdhe3072Prime = residue69 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue69)
    (e := prefix68) (a := residue68) (b := 1224473591) (n := 32)
    part68 (by decide +kernel) (by decide +kernel)
  rw [show prefix68 * 2 ^ (32 : Nat) + 1224473591 = prefix69 from by decide +kernel] at result
  exact result

private def prefix70 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (32 : Nat))
private def residue70 : Nat := 0x38e08c3d14918f3609d650b08d0d9b996270a8b19149a15b8f8760c8fbd89c8b1a2a96ab2c5abda2c3a2e29e3829dead9ddcf9387d518e4c415200b784e678175a1ef488f5260e81836b0d993aa8df8f8d5c12715ed6e38c3b0a0bd546bbe5fca6c9b7b8f4767c11b3ca9010d32ad21fa4c60001364871bdd8b52a1886b6a271bbcfc8b0c41d17e1b9602b6717da50f25c4ca93e513211bcddc12ceb302c78348982fe3fa8cc7dc3695577e7c462027d06d64e80a6172f998aac45b7b802c3c8c626243e8744f1afc5bc449ba0c933252b4416c18f9a2098f5ac716340d78b847a8549746cb80365ecd5cbd8ef51c8daa671f3cce550e46c8e807a3211a8b6ffb9898ec4de83ad1dedd5709073a0ee1376a342aa822949f1d9ce6d45c0606b494e8b866450bcf6bb7a3d3b22f8b13b1427f18aaef46e534b4b3ce53ea2e3ddc4be07738e2d0199b6e7b13a98af7f0510529b5b2b30bbdeaa79ea3f7a9df84f302f59f6fabe2389176e9bf4bcbbe31ada6aa127c17947f7680a39db718b9835ca
private theorem part70 : 2 ^ prefix70 % Spec.Ffdh.ffdhe3072Prime = residue70 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue70)
    (e := prefix69) (a := residue69) (b := 751196285) (n := 32)
    part69 (by decide +kernel) (by decide +kernel)
  rw [show prefix69 * 2 ^ (32 : Nat) + 751196285 = prefix70 from by decide +kernel] at result
  exact result

private def prefix71 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (0 : Nat))
private def residue71 : Nat := 0x468004228d5fa71fb5fa00c0b3c0c81a467ac12b8220ef4048d17dd29ce7f86c01ea183bbe8f0c598788a736443d31422515e252796e46547eea72d145c579bafbb0aa8c4003991ebd4fc74202c204d1e2f300af7eb5997242e9e6745c99ea5b5204ab1f890bcd793c329f1d2a2508b34771411fcfea8700a5c7d0f45e2c501872916572e1277f07e433959ffef88aa62fee402c412f8a5f98517ad531794687787a94d67d77852e2233b532c1e2966ff5bdcbca793267ccc32eba27f00a05d1e3a1f42c19f659b83e2db13fc828edc5fb62dc19e0dfd715ba33511bf50e6abd149730d99a84c4db1fbd81bcd548fdbb96c1b9e66ab0d4c761a2a5cde17a6af679a3d3db973225ad4e6df8ab68b7777cac4d008b34307cd83304095252bd32b81e7067ba99589a4fd9f59a0436329343f4fe75f0501c45144ec946fd076ca8c336c180ba1c8c2451416fc839eb1f2b2e417405ff7bbee4d5887212c530ffcb763c41ea04b42bf6b371b7b32a8867acca0293bb94ac80bdc8f415248cf2dea824
private theorem part71 : 2 ^ prefix71 % Spec.Ffdh.ffdhe3072Prime = residue71 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue71)
    (e := prefix70) (a := residue70) (b := 1623420046) (n := 32)
    part70 (by decide +kernel) (by decide +kernel)
  rw [show prefix70 * 2 ^ (32 : Nat) + 1623420046 = prefix71 from by decide +kernel] at result
  exact result

private def prefix72 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (96 : Nat))
private def residue72 : Nat := 0x51cf029a39cb2a8b2bcb6827fa4fca65f03654b8e4ade0025f6c9797393553d160bce53ed27e621fdb6634e36c81c31bb5cd567fe7a59ef7c825595a8309cdc02834c1477c83409cce4c1e1f41f78c6fa47025ff4d73c2a899ec5ae226e41049d69a243cd204cee11fc720f9e4f873ff1f624da02b658832247f44f6b1c03f6a4dd4e8fab6d4e7500994cb84425a776368bad918f54b50e3254b6fbd9ff27bd52ba1d9737cfe1f619d65fa1eabd7b640722e45829ea7db7e1f59d827724e2e0ffc39d0792336ced1eed0b1ee175f45e41ca16e354dfc0815896ddcb575f01dd9ba9aecc5ee825724b012798bf40667493f9da84649174e3eb097a87cfcb862f93c4845309a5b9d9f4d2289632dff41c985befcae419d53aa17d245fd3a62b86d4498b6796cca9fc268efbce6fb02553f0ee2b26a99b7b03e25aa534f6e382bf5ff3a559b191891bab316f6ee21c5c53c229d73bc0652e502cfe1f300a4774b1195345c39bd174c8e27d70302c06bda4db4088691238a6c26fdcbd45d81ab9241
private theorem part72 : 2 ^ prefix72 % Spec.Ffdh.ffdhe3072Prime = residue72 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue72)
    (e := prefix71) (a := residue71) (b := 1467943300) (n := 32)
    part71 (by decide +kernel) (by decide +kernel)
  rw [show prefix71 * 2 ^ (32 : Nat) + 1467943300 = prefix72 from by decide +kernel] at result
  exact result

private def prefix73 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (64 : Nat))
private def residue73 : Nat := 0x79cbaa977f994af47e4dc1fda1a4fcb182fa14c7f607d024082dc4df85255b43c729528321709d05a98b6e87a2c8681b43fab36ebee60bb634b4257d1cedd3ff4f9ed2d52767cce9487047c04aedc5286e3b971b17c71fa0878479678c81e5b66161099ff4d979c29e422ea931436db50b23827ce164f3f55350acf86088bd3b8e393836127072fc7db29bf53a443abb800da4cdeb15b662f7768a6b9cbc658416e1da450b82eb95ce6b42d6a7dd6e65dfc763f05b421d479bc33ebf1a7bda7eb77106f354385e1a6ff4ecb1ab5d22827d1657582fe99a3602f6e96ab2f3d425e2e6f5d070aa501597c5888f459d0c0d7d6068666fb8802de2c9ec6dbc34fc635d9aa75157ba065ed6997bb1272323883f1be4cdd102b5777acbfd510c9779268a68433f10f542e0f4d61a1727d5c31cf7b04ca7ff0edfaf55c3e2c93e3152a25f50ffdd5c4ed5323a4f5d128c8970db1f817f21c13320d2338836d030d5425a5a6d9b515e2a0facce390e3b41c764086d066a7c0fe419a9e267989719cb35e
private theorem part73 : 2 ^ prefix73 % Spec.Ffdh.ffdhe3072Prime = residue73 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue73)
    (e := prefix72) (a := residue72) (b := 3263809848) (n := 32)
    part72 (by decide +kernel) (by decide +kernel)
  rw [show prefix72 * 2 ^ (32 : Nat) + 3263809848 = prefix73 from by decide +kernel] at result
  exact result

private def prefix74 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (32 : Nat))
private def residue74 : Nat := 0x78382f3edb4e223932990ba42cce4282cdbceb0acecdc23068770101f63f0f3e17d0845ffc70bd31718be82f6ab0bd376424284cf4d5f8dc5d861fb11b3fda88e9b5d699d80f2246ab4b6e20fbd7a65560b6fab796b07d8812fc5211f715c3f75b08ffd49787aa902df46ee10c362d522fa3d34e1faaedb8093eba29ae665e2b47a138002f319f650eab3946461aaa17795675dd4880c8ed88c9b102183b27f48d4f12722c8d89ab3f79e86dd01aada5c5f315ccfe8d8a50688275ac9bff404191fd78166666757ec09cbdf59cc9e7373cc0cdeb78ab096ef860902414821a18c797b29449c7ee723f699942b96212b4a454520bc8761dcbf433cd388bd17f9fda18ba7ce41c6bf844420cdf2c1c8fc77f3c4d5b2943da251ac2a8e40d00a232076d49df2130f0fc5ece069548ed473feb69a790998e5bb9fefa764651fe407b021751e815a7428aa55a53eaa0264126fd81328e4a9a1b3f5302a9dc118e1f14b5d39a3a44df26d5c566b3f9a169453ada9b5ea57ccaa44bec599e8e0241ee9d
private theorem part74 : 2 ^ prefix74 % Spec.Ffdh.ffdhe3072Prime = residue74 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue74)
    (e := prefix73) (a := residue73) (b := 1510573641) (n := 32)
    part73 (by decide +kernel) (by decide +kernel)
  rw [show prefix73 * 2 ^ (32 : Nat) + 1510573641 = prefix74 from by decide +kernel] at result
  exact result

private def prefix75 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (0 : Nat))
private def residue75 : Nat := 0xe1b5e2457fcc25a160b475750fc7d8f8565e9e5c5a701e7ba2de31384664bc32611c2ae83050bdece799e1fa9e51b465f459b0ae02cc86d54374514a11ddd844247dc92071dc5403001d20843334d385ad1a832bccbc65ae428c39f827c1bc9dcd0e9675931a439319a30f07eeae03758a92f0cfd26a2df8c4fb5a9b747e7ab222e0a4f0aec3bb24cf5534445d56581be858c1569319f28cc312eb1521b49958f46b5d1e6e40504f270e6fe153fb51fe970a08cdfa7a2de1f71251637f1c228140bf39f9486ffc6bcf2884eaf08cde2dd5656a570410a7707dd35ae39e3644239edfdfc4f5c71d331f080f077e1a76de5cc62075b52a282b7f2ccb2c6a1c9069e62e4fc90ac57a69609097940d53aea37fc417537de5fcd6bf5c6a97de6dd193fa9d63b8adfcab554c06aa897eb685c343901058c4cd8dba191c41413a9096f5f2f07b159466d60d5feb5b4aad5fb45170a4721d63aae331f73184d5035ebecf697f7eca3741ab5825bd220312e941e96f8a3548b12c5a6e2787c067bff0e11a
private theorem part75 : 2 ^ prefix75 % Spec.Ffdh.ffdhe3072Prime = residue75 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue75)
    (e := prefix74) (a := residue74) (b := 3726752930) (n := 32)
    part74 (by decide +kernel) (by decide +kernel)
  rw [show prefix74 * 2 ^ (32 : Nat) + 3726752930 = prefix75 from by decide +kernel] at result
  exact result

private def prefix76 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (96 : Nat))
private def residue76 : Nat := 0x81ef1dd937110418e6fdc307b9b068363e0aa21351de7a460fee127668cdeebe5eea26b79834816572ac6883e206950781e28d5adad4fb03e5401ef4e4a007cc555ebae3918ff95a5981e430d31f2ca606b00da3b2dde20839e0129fdcd01cc2cc235370dee91f2c752115237698e23bfdefa981bdb4dabdb7c5a0b38e94ba7835dfeb8066f11fa7aba78de8c9eff5706c5d5913dedd3da5d4453293c3e2e865377c570edf10c895a5daae59f96affb517cabc1ad281468c5e4cd4c11f1cd1689d7d73d3c6630f0ff554a865e5f4fa51484506f2050843e68bc3610fc70bff9984fea093fe9f7dd39e4a695a88386e8af2d6a934946dc07f1d7f623ebbffee7ff19dd34bb43039beb29464eeb6e541b48621ee58b0dd0fb26c476a26c9ae116bfeb5f2e0e5d994185032132a4bc41f07c03a24d025fabd3bbe4b2ef9475eacc0ec1c894311040c39e07c359dc8761ed230788fa9127d042b3aa8fc8abfe5c5d6ab823b6516348e30d8c1254bf3455d383b7aa0711caaca10115813ad7e09e2dc
private theorem part76 : 2 ^ prefix76 % Spec.Ffdh.ffdhe3072Prime = residue76 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue76)
    (e := prefix75) (a := residue75) (b := 2055119401) (n := 32)
    part75 (by decide +kernel) (by decide +kernel)
  rw [show prefix75 * 2 ^ (32 : Nat) + 2055119401 = prefix76 from by decide +kernel] at result
  exact result

private def prefix77 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (64 : Nat))
private def residue77 : Nat := 0x214c6e7860d81da42b6858d46d6e8ec64f5162c0cb08592c38b8ec239873875364c1afb02387c36ae7ff8695b320cea4de985b5f244d3df14109bd185e31cd6648de92995f58f174a0b0f812da85cddeb313b66befd949885510c633212ad8ad26150361a636e44eaf32b24534a89ed83fb4a114834c35b23a80154b9f3df5152b7ceb5fbbcc0015963cdac943d4428eadfd4e9beff2a0c887c6cca11b1c131249789154ed74bcbdd2b87f22860fce748775f97f4daffd15aafbc7b5207823c68472443338cfa785e6f828b703a1f71cae7d473f740ae13865b8548d370eeaf5359cb0c8d6f5e32509fc3075b04d9e1d23cb715179a4e5d14f078b0cb40a24c30cfd1d2be5e02309a2354cbd0ef2ddee5c387f326c193d79b20dfcf29e35d8d30626e22af239e6cdf7083f63430b0d58537d0007bad4724ce988cd135776562b733884cbd77e6d037d6b09da3375f8647e3e8b2f8ce1b3fab996af9b7f8be62b9c06ecfef8f764732369b5f649b78a8e38ebc5e12d39f337eaad4240ed518dee
private theorem part77 : 2 ^ prefix77 % Spec.Ffdh.ffdhe3072Prime = residue77 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue77)
    (e := prefix76) (a := residue76) (b := 1902880489) (n := 32)
    part76 (by decide +kernel) (by decide +kernel)
  rw [show prefix76 * 2 ^ (32 : Nat) + 1902880489 = prefix77 from by decide +kernel] at result
  exact result

private def prefix78 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (32 : Nat))
private def residue78 : Nat := 0x95e7fb3f4d0e4ccc900310e9983dea6250906d3dbd7fc1e12bb47ea004cbea9726024fd50c2d6e98def88ccd9f045339ebe996b9766181bb0d7841bea2c2e87df3adad770d635f75defcd5365b1e41c99b409e20e37cf9edeb965716e8a4147dd4ec9c979ceb404c69dafbe810c016db72453579e3516335e733700dbb8d5fecf67a8a377e17e173e45caf55daecad2f1dac09e1b8c5456fb6a358262e6480854f70e6e2bbe95fa9d40a5da97a3d910b1782da550fb5357d0be6db25e5870e60ebb4cb5f36316292d6a2f4f1cf48bf04133964420966caf80d525fb2a492f00c15ef381a967fe61f17ac68dafc14253164938f90e845cf3675e3abba738e1882cf7c78bedd186086eddd82ac2d732b543b133f19677ca37da1218af8ccdfb6a353c56142c1db7df69fab2e0dd040e179346a617d216ba2f00de0684b768fa4d528e030676ceaa2f7d3eb3227c33f0cea120771e96a250c670d9987f3547f5a5a9340a24292bc1b7941f827d2a3fabd3de44df8dd4fc79273e9373e6881d6d047
private theorem part78 : 2 ^ prefix78 % Spec.Ffdh.ffdhe3072Prime = residue78 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue78)
    (e := prefix77) (a := residue77) (b := 2994303247) (n := 32)
    part77 (by decide +kernel) (by decide +kernel)
  rw [show prefix77 * 2 ^ (32 : Nat) + 2994303247 = prefix78 from by decide +kernel] at result
  exact result

private def prefix79 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (0 : Nat))
private def residue79 : Nat := 0xae3f771075a3a5ace39a03a911851efa461240a1aeec6b985c7643e4896ae0f09eca4a1477e12086f9a3890ba9ef6006872c22acbc16caf3f8352335f39e7727b82516041782741aa9fed966ba17e523c6c286c6aca2e744b7782653cb8ecbe23810f78c28b4e5c42a3ff5752cce7dc6e53f1798ab0b7491c2c332f23cdf7d89fed5b6bcb50987a882ef575d35f1e3245e7370628d2450f765a3fff9e60b0116bac9eba3019d8bf9416dcfaab095ae2b59cb3588f11149bf5b8f59fdc4858f71d9f8396847b0a617b1016a2f6aeaed9ec174b64a534c0dae55645fd9e5497db0f61c8bd43b02a170694c4a771d641c0841ec633e395d2ff8948ca3af93d0631f4b429107ec2e2d56aaa15b045fec8a7b773aa999aea3f78a0b5c22c78ffa00eea433b530cba46fcf000936196a43461015164fc3ada7c6586f69d4998168aa5b9d852ebfe3f4b82ce3363f4fce39103a629fdc4e5ce11d85bfbe7bd588ddc74a02955a3698351548f42f89f833325162773443604d2fcb2c5185ad5699c12b71
private theorem part79 : 2 ^ prefix79 % Spec.Ffdh.ffdhe3072Prime = residue79 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue79)
    (e := prefix78) (a := residue78) (b := 955950591) (n := 32)
    part78 (by decide +kernel) (by decide +kernel)
  rw [show prefix78 * 2 ^ (32 : Nat) + 955950591 = prefix79 from by decide +kernel] at result
  exact result

private def prefix80 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (96 : Nat))
private def residue80 : Nat := 0x2b6bb57e47a423c4c530c589f063dfef454fe6c9929cd29afa7899b0b611793b57071df6a51dee8c5f12fe5a6c4278debabc694771a6a2f453a3ae54c4d781c7406f3790bfd17d29881b44735919ea33fa7582e7a37398369d756ae90d59ea501e99401f0dedbde6148e3c862696296afb113e37e7120a5fedf63eb8e0a40f76454befbcd87793066d98440514749ac7af5cf5010e443f821422064da4514d65aa2f6375d9bb21bb8c41c491317849cae37aa92c00aefff326e40a03672595b8c9fc2fcfc095a2727f7e25c15b78c844df16d69185d911519aeb47b8f5b351898edf90009d5298a01495041bdf93333405e255957fc0401b191da02aec74e48dbb1e07eaf6cc62ca0b941199810bd16e82191dba39a34d971b74330a8eab13f9e886fbccbceb203f478cba28d02b06313371c0f41e5850d660b0a226097314d3215711b629a0dcd8d0f4e65b4de6d314b226dfa252c014e24fa6e43d1b217a6db3e0497d44f912d1c72d811d74878c5b8d32d6096e7c98dcba84295ae7fda195
private theorem part80 : 2 ^ prefix80 % Spec.Ffdh.ffdhe3072Prime = residue80 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue80)
    (e := prefix79) (a := residue79) (b := 2924953941) (n := 32)
    part79 (by decide +kernel) (by decide +kernel)
  rw [show prefix79 * 2 ^ (32 : Nat) + 2924953941 = prefix80 from by decide +kernel] at result
  exact result

private def prefix81 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (64 : Nat))
private def residue81 : Nat := 0xe53cb72b1865695dad4d97924cefae5a2d0916e90386cc0b131c17d9c2a552ffc2773200ecc7ca5904bafaad3caff5d3e74ae631fe69ff0245100582db20758f73991c022526732078eb0ecffee0cfc49fdff182576167e0d0ef857f5baaab3d6147819556f38384a45a3fba90548bad5f86543b6a51bc649f63d8dedd5648d4371cd1c3bb8092ec681faf7ad992396422b48799e43e034972d1d24b5d3fc8c123e63f419caa098ae8d69cc2efa269f70f805a0291ef9eff3e7e9cd08eb8a78679b7b3a1d2f5e5452f776a9bbe5e17ae512d6bc7d0ae7e702325cef38df3c101107a745f5b7d0705c72e35008deb63fdd806429b0ac874366dc0f761dde75ec83694ac2b6610f00ab328384b1c9774c8e29fb98a91997e98f75b0377953a656ac9553d83bef383c9a93fc92930a1e5e779de4c96d88977a733737ebae0c69f6d673d2a6760a47f193981abf6bc04ebe900a1a109749395c7e6bc8c2f2feafa7c2a70e1358984e4646916887bda80f044ab4e6a56a898610821ad95a71397f68f
private theorem part81 : 2 ^ prefix81 % Spec.Ffdh.ffdhe3072Prime = residue81 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue81)
    (e := prefix80) (a := residue80) (b := 3461282639) (n := 32)
    part80 (by decide +kernel) (by decide +kernel)
  rw [show prefix80 * 2 ^ (32 : Nat) + 3461282639 = prefix81 from by decide +kernel] at result
  exact result

private def prefix82 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (32 : Nat))
private def residue82 : Nat := 0xd816890a0526f9a4e1ab1751c88d0b5334dc166eb4bb8a76cda178b03563193f3a568d2b648e0894115f33443156c1347b3117bda099d339c6418e85b40754149f40050c54b3328c68d982d6444b58ec262fee3a3b7499d2f0ddfb23a78b1e6d738ac1ca7aa89762317f4bbfa03f9de6236324d1ca0f90a46c11d75406be143ea90395438a4fa463f8752b125ffd8dc8404dfa5039f4938f146afd4286353eac76115265ce93e17865e0cdd3c851218a06f4690acef55b98c5b6bf54b4dd92acd18cd088ec59189d99503e002f3d1c7010546d3e04a39fb2e77954db986d8a999c2ccf4043e44598fc0e657fed53209e3e5fe3698cb6bdfae27b6531132980f474a7b996bb43ac4ecfe1b9a07793d7ef7ea682d0d4d9c47f56c7f70f6dbf841bdc2a597a08641f0d5aa1de47f5dc413536b33c1456d4583a248d9255136e9d0b9e95390d4e7d3a78580c5e31aa79e227ced8bac44a29f734f4edd5779066c909fa4a960d57d3766c326bc1a50f5d78a9d8d6c1748688ebdd400dfa50ed237b86
private theorem part82 : 2 ^ prefix82 % Spec.Ffdh.ffdhe3072Prime = residue82 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue82)
    (e := prefix81) (a := residue81) (b := 1949734370) (n := 32)
    part81 (by decide +kernel) (by decide +kernel)
  rw [show prefix81 * 2 ^ (32 : Nat) + 1949734370 = prefix82 from by decide +kernel] at result
  exact result

private def prefix83 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (0 : Nat))
private def residue83 : Nat := 0x967303b91215408301d92bf66a41bda98624309eb31a0a9ce94b2d3359751aef9d952c2451abbe388cc1f068840d318e3df5d7102308832a0356fec5b95faa6e943048310cb8f77c6411ad814d719a5009c814158d80f1fffec91d11690a27626b965dab5efcd082dcc2ffca0a4e93e7f7a723492b15afa6693cdb1324a084746450c710d67dc375c6e7885e59261fd4996fae1752e4a5baf0700f4bef8ea614c9e7621cf14d0babfbde5d5c46c6ad054c9b2eb77a927d984de2c796077ede587d432a56aac37df2e52a90f99317b40ad1f41ef60f82ea43671a6e6cdb9acf261bd9698046ecfcd4db4acdaf85bed44aeb6c55fdc392feec221f40c32b6a1f2880fdcac04c73c7f457b935915b5ab69c357f7f0ee200bce4212abae1359d297003cf2911689bc575bd5c27a201611e5febdc75da2a01afc8d67139411c20056476c8f1e96a964ce9f1512bdb2a2a960d0527f2ee7277a7c488274db50a3d8f1c5348ec1d4ba79d7f39ca123273415c8903326fdd9661a4a612ab320444470c48
private theorem part83 : 2 ^ prefix83 % Spec.Ffdh.ffdhe3072Prime = residue83 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue83)
    (e := prefix82) (a := residue82) (b := 2434473222) (n := 32)
    part82 (by decide +kernel) (by decide +kernel)
  rw [show prefix82 * 2 ^ (32 : Nat) + 2434473222 = prefix83 from by decide +kernel] at result
  exact result

private def prefix84 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (96 : Nat))
private def residue84 : Nat := 0xfed4287b636b3baf96f4fc93e560e3500ea4efb9ee9ed6b9d8585d006752528cc6ba472fe45a35dba4d20d615eb3740d5d8c7d119c2bc59183ebd4c612d403a06ef1329a3e3a1d4bb3497f554bdb4137c18190520c648367ebd50f3996ccd4c891388b761437dec3fd3fc5dc8d4b089879698c96b498d5a2301519ab115486528d229e319f41ee4f85580f3c82db02f5f480978918c4f8acb8951dacebc7720c7102f357048bf21296bc7c65b98dde9e3c0fd2dfa032e39e7bd1d536b7e69e08a92afeec51cd72a9f78e891fe49f156ccdd683d7c930c409901d2b44f903bd229668d3569eb3e84ba4f6f83c5cc060ea7b580e841fa2c6da8e3d600cafca46ce465a7c6f48f9cc4b26403bbf8ccee9f072274c6e444eb04a55b9793406f83fd4af803bf753d3b649de3c20f1d3a2f2e4bfd613eb3c4eff700a0ab8b43f97bccdd68fd444f5b53e4cc2bda56301ec6f98a592ba3bbcc69de776a10ce0842b3413d280646e26c2fe1fb4d140782924d291b8b6da08afc038814f2885b8af4a1044
private theorem part84 : 2 ^ prefix84 % Spec.Ffdh.ffdhe3072Prime = residue84 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue84)
    (e := prefix83) (a := residue83) (b := 3588395211) (n := 32)
    part83 (by decide +kernel) (by decide +kernel)
  rw [show prefix83 * 2 ^ (32 : Nat) + 3588395211 = prefix84 from by decide +kernel] at result
  exact result

private def prefix85 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (64 : Nat))
private def residue85 : Nat := 0x61e6db81ff3632792b23fa8fcb5f98fd8ebe5963596c37d7b41a8b3542d09c0f25063b66c75a3ba32c9a1b290039e7f009acd24f8b20a691c4ed5833ce78d1d1cb0421035856e80f91ce34bf1dba5412085c4fb982cb248726749b81a297f2da15d506ee7170e68686da4d40dfd7104004d4c84c9b5c32bf8e9870b959064e29591821db6ad9fa9d018bea3597708d931a58170af209637e214aee280d9f489e0a63b6b7216d5e9b72a31ecd2c1e5f445426b9e033c91da1a978ce0a6bbbb9e907fcd404c44a8a5c5b3659c4286ed31a06fd96ac2e5634ac92473630d7580bd341c4ab4c9cef70ed4d322ef30e1d7b141f37627b404b7b865cbb5752c719e49e9ce264040463875c6631c9fcaf74df64440d5e0771ee76c4b74a49ff22b904a23e744bc27574cc246ea6083bb4ba54652a2aea20af3dffbfed5c94fe8ab4cbd52e8f2c8872f6a80bfc8a1acbca638ea852f0e28aa7251ebdbe01f1028e13c1abdfff5b2884b4352b081d34fca3fed4bdc68c52a5cdc2ce8987e33d1f81588fa2
private theorem part85 : 2 ^ prefix85 % Spec.Ffdh.ffdhe3072Prime = residue85 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue85)
    (e := prefix84) (a := residue84) (b := 3448173933) (n := 32)
    part84 (by decide +kernel) (by decide +kernel)
  rw [show prefix84 * 2 ^ (32 : Nat) + 3448173933 = prefix85 from by decide +kernel] at result
  exact result

private def prefix86 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (32 : Nat))
private def residue86 : Nat := 0x75c92e2b52f1cffb92b17fb9e71ef0a3bf4251591d6e19a3451c188c8fb890dfaca25111ec29241c86091c9374a431e650b2f5652f54147d1f084e0485abecb6782fe49279baf8aa99dd6cb43c4ad46e3c08d9b10cfc2acde461d90354d2a715fead2ea94a8035c0089e787a65afe62f3d9cd2d0df0d5d2b34698f69a630e1c5618c6890e5403ddf32522fd9e44de120208151fa11c37e69a76f83a4000aa03c829b49ffe617565bf2a92fdc0b038e493a39c00b396ee4886de65375f496030ee916ee8f8abd80eac98e06e322996de6af29048f7e84fcfa804a70ac50134f6e065c72eed23989a2e100da683332badb7c024c1d55a61d3e39340b8d8fd942baeb1e2cd0463732f91bc3f1717ee3c26f25a58203b26211360f939d663db7fb9fd71837b1b1bc567ee71e124660079c95108f4c929e56685ccaa8d70289b9f50c2bae38a8aad98fb5d84bc2522d204270fdb0d82937712d3f4014a51c488e64691356a53bc93900e79db69393af7587d1e42593c013db3d918ad3ec2d8dc1f7c7
private theorem part86 : 2 ^ prefix86 % Spec.Ffdh.ffdhe3072Prime = residue86 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue86)
    (e := prefix85) (a := residue85) (b := 249548065) (n := 32)
    part85 (by decide +kernel) (by decide +kernel)
  rw [show prefix85 * 2 ^ (32 : Nat) + 249548065 = prefix86 from by decide +kernel] at result
  exact result

private def prefix87 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (0 : Nat))
private def residue87 : Nat := 0xc5b17a278ca377cca507d8bd9ac2f8f673ec9b17227de11dc42f98b61dd3c5637480a80ca6e8f278152c4c7963bcb6ea02c3c4b8b70704798385684349d90c30d94293b5800fee04b0b722703d11bab371ba493405cfeea4e9ab9200a29f5f589c845614e2a38ba224c5d581fb837aee685c073a70436e99aa3e4925193186131a12d8f1d9da745487113b12e11ad006f5da5939291ca66214aa5e512cab369142eb1600afe72e7e3e7651973841dd62a52f4089a15e795e2eb269ffe9aaedf157531dcd546418ffd8b845e2ebca929ee355cfad7aeb2b0e55d440b06c01fc55a3de643357235140234ab64c8a295ba5ea28f284cd1a6e41ba9213377be4a941c2a08bf3da4c1d320120d60cbd976e067063c548b560f202125a4bc6dc17e0c124fbd260905918b106f2d90802d15f57de925bf08c95c9ce50cd121a35a2b09da5ec6a6312f223d3e202a79925b10792b7e593dd5c8964158244b7d9f95fce08cf14a0ee25a77b3d61db9451b163d783d5724abb64d14298a90ec9b7c700aa8f
private theorem part87 : 2 ^ prefix87 % Spec.Ffdh.ffdhe3072Prime = residue87 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue87)
    (e := prefix86) (a := residue86) (b := 1793205287) (n := 32)
    part86 (by decide +kernel) (by decide +kernel)
  rw [show prefix86 * 2 ^ (32 : Nat) + 1793205287 = prefix87 from by decide +kernel] at result
  exact result

private def prefix88 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (96 : Nat))
private def residue88 : Nat := 0xdda376d9022aa3505e0ce8ec861b486a470d0e252bcd69a148302e8c86338edbf753168ebebd3cd5f5d8b92e641c3a1f5f9a4e385b965798cb934579c586d8ea970382a97a6baf05213f4a70aadf224c7d6643974a512f0e88006673ca17f7b187de857544493d9155099f8e1865c70662ca0bdc265c692764ccde40b988c36ff4956c53e9998bfbfca115cc932dc785c1c561b5dc9b6a8d6f0b964e2199fd324ec69f1173da1b8c5855cba7a3bff77e91459f43129bf764d2fe44c09854c3312796563e2b5b92b81fe5d4ff2a35fe21c3f4694c9d1a71b51f2d74016a351560a1e6da1453072f5f65daef263c31da73d0382fa57fd2bdd8347f0893bc04f7a1ed2ef1f91b9e912b4a4b8730b1eb7c48b08658a583edd9b81f26d3f15fc5c4a7ae63dfb4f44bb3e96c69320dfeb036f0ec9fff8147723061b07a48b9b6c5a92bbc502347911b4df4f146358ee71c5cbda851b6f450f8fc13763e2f54422567c9234820ae8724f578839e45d47b83e1f8e57a9e1e2dc40aa3c8cc23c4ba8f988a
private theorem part88 : 2 ^ prefix88 % Spec.Ffdh.ffdhe3072Prime = residue88 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue88)
    (e := prefix87) (a := residue87) (b := 90073141) (n := 32)
    part87 (by decide +kernel) (by decide +kernel)
  rw [show prefix87 * 2 ^ (32 : Nat) + 90073141 = prefix88 from by decide +kernel] at result
  exact result

private def prefix89 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (64 : Nat))
private def residue89 : Nat := 0xf3fc25ba315f749f9e50bf110c315c19de3d1e6f72ab008da40c7edbaf3ac1cd1179d3cda1500332e55e25182525286faf57a5dbbffe605860867db36386360d3b9167aa9a48674b23d73238880b128091832369583744caadfbacdfd0c4efd541779a67cffe44649e3855cb2d4f1becc69d1a268ad74bc0a0533a8196ad7ae59e19abdb5c7f655de52a0225215930e2cd6c4429e992fca1273b06727a4eb51ae6d6fbe553605f98f64b4ffa6bfd94e9e4592cbe272db3c12d2e3ff97885f268d7c9aa6aa3000df71fdd7ad38a8ddbbb3321ac87503b74bccaad55cf928af989f10c250741ee90aee0938557059d8f0d6d3b59a353f92e5078d1ff0bce7f7a3668deef301d74fabe9a9674c6b4737af16e2a23f8ed509e77615dc5b3660b3964401d569f4abf96a11fa140a2a190c733981500fd5d97c56867ee1e4c63bdb624254a8fea750e7a480abe49c5d526b8313087f79884efe8b6c524d6a7b03890f48a05291ce6f1970feacf813120b5a337db01f668a3ff70c791c4b53b3cf50ceb
private theorem part89 : 2 ^ prefix89 % Spec.Ffdh.ffdhe3072Prime = residue89 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue89)
    (e := prefix88) (a := residue88) (b := 4247383799) (n := 32)
    part88 (by decide +kernel) (by decide +kernel)
  rw [show prefix88 * 2 ^ (32 : Nat) + 4247383799 = prefix89 from by decide +kernel] at result
  exact result

private def prefix90 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (32 : Nat))
private def residue90 : Nat := 0x23de53d62ea44e2276febeaad5bb01d3b1a26a9e9a91c0fdd38678bf9ec5d0da5dd3fb50132443150846b792d936b6416cafb3692176a6b75188bb7279344dc7eee526075ea0a2c7adb92dc24d74def3eae7842e807585124af30c3f80627868ab53a9767c3401c212cd7454a98bd7645363b3deea842d43888b0999534d595fa8bcecb2ba9be275530fb65efe2e33f7de0dbc286f0f0b81ab1fa2e3af8881910cf2ed877e9c544fec1d2953fddef7ea66a5cdb46c91ba06e46eb0dd266a6e040b9d429fc7bafa2aa1191355fe9b3a79704e53a69533b9213c2262d31745474a58da460d917e8b7518700dfc9db3f10f80220017101eb96417e5e7fc4ac0e527424eb12e4ded7706d50d3eeade4034c7e5b6e2b02ba7ebcdd9f4c1d7aaf7fc9c1852e8e66189ce7b9030244708b5f527e27154919fe065bff2dddf10301a4d5bae67037d04e31b2287c78ee721f3ff09519e7d3c74482cec0be41762708763ebc7815437e7668c0cd6e0d542d280638ce35721874738d6f2e1251e6e566ef219
private theorem part90 : 2 ^ prefix90 % Spec.Ffdh.ffdhe3072Prime = residue90 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue90)
    (e := prefix89) (a := residue89) (b := 2651689079) (n := 32)
    part89 (by decide +kernel) (by decide +kernel)
  rw [show prefix89 * 2 ^ (32 : Nat) + 2651689079 = prefix90 from by decide +kernel] at result
  exact result

private def prefix91 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (0 : Nat))
private def residue91 : Nat := 0xe42e3eaf954016bf5ff979542e85c7a47fdde96dbd961fa761e509edb79a0d1ad7621a56d828cf30eb37810db520b722d0574c2cb3fcb094049229c12d91553b5dcbea721f189da4063f9e9231d0638383ef5a98f628d736867e6226e9842af1aa45557bdf553f74c9aaa3191fa6b6106b1b113b952bbb5d1183e50ed4e3af1519d705be0e3abc124b36f65f1771c2a8d90b011ca084595e7dab85865b211ba71276d082826cd444819b335209d6c6265e795e8100c6eef3703205ee5d7bd4b5fd7cc973413b03915fa9eac3900d426940c2309b765b6c74785951d473e8af5bae163fff62046817de8c55cafbfc62e553a60d1ad0241776980aebb22099a82de2f26cbc6e6ac1f26d11d9d5343a2b2c1ddfd54171d53fcd7e37478e59157668c0c00e119a620b94883c6600b1edb772e22252782b002cad202805f4fa097ffa4bc1b16d71a820d68ec7dfba9c92f8ba8e43442188b42813abbf5622dd12fabbed381ea37c22fb61a4d175025fdaad3b245d1f0627ed6c5ab6278fb3dc0fd257
private theorem part91 : 2 ^ prefix91 % Spec.Ffdh.ffdhe3072Prime = residue91 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue91)
    (e := prefix90) (a := residue90) (b := 535482046) (n := 32)
    part90 (by decide +kernel) (by decide +kernel)
  rw [show prefix90 * 2 ^ (32 : Nat) + 535482046 = prefix91 from by decide +kernel] at result
  exact result

private def prefix92 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (96 : Nat))
private def residue92 : Nat := 0x79cc85042e2b80b8c0ee7ad9f2f57ac53d15fc3c2f54b3a7e4dc2804a604b1bbf6854beeae763fd47c8e028bfdffc8772f96224ba8dd91046eb09950fc726de86c5ea95a11e44a96215b8ef5da3e2bbdf761efdeb512192ce0872b38e8cd26c6d2ff8189e2226ae466b0a980d82d19e33c632b1a25745c1b33aca00cf652413e392bbf37d3a3d66f3653925d8e4f67a8e0a166d7b5ebca6e0d86157d2abace919e355938450e1f98e1e9cd6fda899b0babab93dc33d4dad5ae33aa4a59019f0af061f4c7ff561e83af59675cfd688a629570b2e0f755b049ae2072bc00d352dd6fe57e6880d0380c9d1d00ca0a868597bc0341ad70ed4018c0c340aaa4633c5e52ef5073985f1ed44c6fe7a794d7489327b7cd4a3589a18782fe7022f1c86c99c3132e70ad059756eca98a850cc75b945831b2782fa3290257a0fc9dfc59a923f2c673fa66d722e8e7fa52fa29e27ef96a614d428d09cca57a332afb6ae80e6de8a60decc8fe0d819da2b689be5ebe28fc0a9c83f43ca75bf02946c74c2f46f5
private theorem part92 : 2 ^ prefix92 % Spec.Ffdh.ffdhe3072Prime = residue92 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue92)
    (e := prefix91) (a := residue91) (b := 317853333) (n := 32)
    part91 (by decide +kernel) (by decide +kernel)
  rw [show prefix91 * 2 ^ (32 : Nat) + 317853333 = prefix92 from by decide +kernel] at result
  exact result

private def prefix93 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (64 : Nat))
private def residue93 : Nat := 0x414d29b6674ac8aaedf1c292b96c6049ae25b9ba1763ea89f1cf49a1ecd7f3419cdfd4363fcfe1ef20f9d6ee020a4f883a1e0a060095793a17eb0a59e57c654fd81632911257443c035bad54cd307d060653caa881bd943b0e8b999871eb389a4a8e3bbf38b1cf3fbc1d865a44cdb85a9bce5c94efef927d8f6ce819477eb81e501c08512cb9361bf4c84dddb2694ca58726201caaffdac37997be82f3115cd2539f1ddd8234c0dddbb96667954e156069d6283ecb52369d8ae667a78578960511a1bd07934a8210e0e41cbe1350b3d09e0375bce28453b641b47f0b1af7720c27fa06a8182899db98eb0a883a0b5219633f575b8e0c0043243698dc0a588f6f8b1b25b73490bb5661b61cc1b246c833c20c4d18c23aa32675e25a811a62c0f9d38ce232c0c6e8e560f68ccfe423b7ac0234a5080e3aa96dbe70d4d96e07a08f89f0d6c720efa5b4fd1bffbead395a63f991d05084d69ae41e009f8f2da84987adfa9e72c36a26a88e4d0f1d514c62f20d18a978db8476ff0d11272860fa470
private theorem part93 : 2 ^ prefix93 % Spec.Ffdh.ffdhe3072Prime = residue93 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue93)
    (e := prefix92) (a := residue92) (b := 3009615643) (n := 32)
    part92 (by decide +kernel) (by decide +kernel)
  rw [show prefix92 * 2 ^ (32 : Nat) + 3009615643 = prefix93 from by decide +kernel] at result
  exact result

private def prefix94 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (32 : Nat))
private def residue94 : Nat := 0x29f03d5b1e372ed93c26de8e543eebd6f9806212fccd746086c1241620718c13cfca763cb9863d0dfbebceeee4ff8a5abe4268db0b07d46f633416c3034cef2b7fb65a4f5b5947d32af4b54127f3a908520f47355760c4a9216ec3b01da40aef9c94e340cb453199bcbdaa75cb9d18d7893f3ebff3bfdead7dce1598297094e5e2e61bd30b54f1348d52012d8cc4e4cec163363698b55fe206e8e0b54656829b05c3b2cb7ff2820cb77b0091c08bbdef6c4eca1b5b158a7801f27a243ec3b182f36f3c43cd2fe5e9a4946e1ec4c140b11f3c7881b9e6c92db080dd35bbfbd274f6fc7c7c70886bd81f98e4217d01c2ab6f9158a76548590742334680f73c9bc5ae8d7d2984cf255ac8621d5b56f6f1ab401ee859daa0a8abd53dd058b43737ca446dbdeff16994f1ee1be064f4fe51ac248c5132562c1f69cd6a9b57426f94683603e2f55658f7e017ddd27fb2be874f779e97ca6d67859cca85bdbf66a05f9efc418dace2cdb81d434e966d1f2fb62f62eacc048b01e1dcca3b15701c3557d
private theorem part94 : 2 ^ prefix94 % Spec.Ffdh.ffdhe3072Prime = residue94 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue94)
    (e := prefix93) (a := residue93) (b := 4294967295) (n := 32)
    part93 (by decide +kernel) (by decide +kernel)
  rw [show prefix93 * 2 ^ (32 : Nat) + 4294967295 = prefix94 from by decide +kernel] at result
  exact result

private def prefix95 : Nat := ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (0 : Nat))
private def residue95 : Nat := 0x1
private theorem part95 : 2 ^ prefix95 % Spec.Ffdh.ffdhe3072Prime = residue95 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe3072Prime) (r := residue95)
    (e := prefix94) (a := residue94) (b := 4294967295) (n := 32)
    part94 (by decide +kernel) (by decide +kernel)
  rw [show prefix94 * 2 ^ (32 : Nat) + 4294967295 = prefix95 from by decide +kernel] at result
  exact result

theorem subgroup : 2 ^ ((Spec.Ffdh.ffdhe3072Prime - 1) / 2) % Spec.Ffdh.ffdhe3072Prime = 1 := by
  rw [show (Spec.Ffdh.ffdhe3072Prime - 1) / 2 = prefix95 from by decide +kernel]
  exact part95

end VG.Proof.Ffdh.VettedValidation.Ffdhe3072
