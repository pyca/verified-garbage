module

public import VerifiedGarbage.Spec.Ffdh.VettedGroups
public import VerifiedGarbage.Proof.Ffdh.VettedValidation.Power

/-! Kernel-checked binary-power certificate for the published modp2048 parameters.
Each small block checks its arithmetic; the shared append theorem composes the blocks. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation.Modp2048

open VG.Proof.Ffdh.VettedValidation

private theorem initial : 2 ^ (0 : Nat) % Spec.Ffdh.modp2048Prime = 1 := by decide +kernel

private def prefix0 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (96 : Nat))
private def residue0 : Nat := 0x19fb126e69ffb570574a7318a0be120dc83269b597530de9143c94bdf116c8f0e946b319043524c9c3817d8987b5fb4e0b274d6847c7cbb21c0e5c91f57e344125e3b31ffac02e8de918ea96e8643affdab6e233a3b789240094f93f9c5bd3e08866def30452e210f959c90b253553be892fef89608ead21ddd561fe383a92d4c4bfd4e936fd611399b7b1aa60a053197ba5e4c16f694191041a9dd496fe4cea6ff334fdb0009b2c82c22032de3bf7fb731e8f8e5b97733300dbcf3af18b1f7c8ac716920f8850c000036a7cc491e23832f93473984bde0cc46b59fc74346f5d613c22ac30fd8498680b1647dd1a397628637f7fe20a53d69ee8e0fc460958ff
private theorem part0 : 2 ^ prefix0 % Spec.Ffdh.modp2048Prime = residue0 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue0)
    (e := 0) (a := 1) (b := 2147483647) (n := 31)
    initial (by decide +kernel) (by decide +kernel)
  rw [show 0 * 2 ^ (31 : Nat) + 2147483647 = prefix0 from by decide +kernel] at result
  exact result

private def prefix1 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (64 : Nat))
private def residue1 : Nat := 0x205184a475cebae21fd531c988b0bf2f85d1c04bace18057410a48986b7377f7248e5b1e3ebe0b111b274aba2e13c1672af8611444ef2395c4f70ee7657a0c6dc307bb6ae9f4e05a3d7d3bb7798e0751503358884e7992692bb8c1ae07b1bfc125c7a0815dd1c244253f0caf19fcf0c1108cd8ddd5b65ffc25222d555b1c1536e7d9364eb97d2ba574f7a8357526b2f7857d473aec541468d316bd8a023cafdbd6cddf3069f596a4b5d8edb1f84398a6fa0d13f727b13e6e722fbd6166721e1c47ff405855da4d0129fe9d0ddc4cc85bbf3849774825b93815a1385e4a12a8930751d1da4203ac512167e57b88420f7ae0742d1a5862ebd168e3b7264406310a
private theorem part1 : 2 ^ prefix1 % Spec.Ffdh.modp2048Prime = residue1 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue1)
    (e := prefix0) (a := residue0) (b := 4294967295) (n := 32)
    part0 (by decide +kernel) (by decide +kernel)
  rw [show prefix0 * 2 ^ (32 : Nat) + 4294967295 = prefix1 from by decide +kernel] at result
  exact result

private def prefix2 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (32 : Nat))
private def residue2 : Nat := 0xd9d58471b180d89b4ce0d8489ca3cbff305691e6147b30379b23450bdb04766c3f483024d70a887c774de541eed65d4df268526ee10064e754674bed207c7ed11d7f9e692ba23ba63b5c11c4565722bf313454938df23c9c3a93411769ad8921582f9a5bfa6f4884e44e521e3000dedc84426e5a2ce245bad8625caeab6f8b8a221ab7b3a81cbce51cbdd7e383e484ee0e52af56fda2b4c15977a0ce061ec3bedd8130db8a3aa8bafd638421952fa6b3bb66c3c23a842d41491ce95df682e7d56a32776c0d33c75e86f94604bf73b71407848cfb5b916fd0f96379d9ea68d72d218d8c3201bd377afe4e600534cbccb6fb98228acb7c6da128ed116323ce1b86
private theorem part2 : 2 ^ prefix2 % Spec.Ffdh.modp2048Prime = residue2 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue2)
    (e := prefix1) (a := residue1) (b := 3834113361) (n := 32)
    part1 (by decide +kernel) (by decide +kernel)
  rw [show prefix1 * 2 ^ (32 : Nat) + 3834113361 = prefix2 from by decide +kernel] at result
  exact result

private def prefix3 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (0 : Nat))
private def residue3 : Nat := 0x7aa52163f98f5451666e937a06ae03b1a96cf4f7a399f686cbc25dc1a6843516149e98beb5f94523c71828cec8eab879c53fe0d9405432fde3170a70d0035104eda8a5fdf43b5a0e380c14509af13429717131d368e6d787d6a5afba5e2e2295aa119a7a20222e340fc7b665345a531984003817659116e857f60d49c2aca6aaa8189c6d067d62913f0acaa0bbbed28e9f4edf9a224231a22d9a595c41def4db2f44749e25e7bbb43ea5fe52e81f7def8f57c806d6abdb84bcfd3c8c2f1e227ebcd9d36cef0f9b3625036177099a5ae7965c647d9b8bb97a26cabf03747bf620355e433083b8c2c3b2fdf4575b787899f2c28b22ca709d6379d66336b58fcc0
private theorem part3 : 2 ^ prefix3 % Spec.Ffdh.modp2048Prime = residue3 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue3)
    (e := prefix2) (a := residue2) (b := 280256794) (n := 32)
    part2 (by decide +kernel) (by decide +kernel)
  rw [show prefix2 * 2 ^ (32 : Nat) + 280256794 = prefix3 from by decide +kernel] at result
  exact result

private def prefix4 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (96 : Nat))
private def residue4 : Nat := 0xf4ea9a6cd9d0a9ac316208bdb1229bdf2e99595a3689ddfb37022858ee572e538587d6ffcddb08b1c73102bb9f7de2d9d78849361755e87952e3f6b732dc81de8bb3609963d09ed20e09f5f89db4b5e011ebea58a1a033856034db7d4c9e960e21c8602f5d24234afbed6beff8852b67e19dd7b299ba0ea9078b018f988426566083dbf22352b3c87fa052e2134ec9f24f3b778e0d3725f97d6342720e9a9319984bceb275b09800875c92d043bc4f866fa4cf9f9b2ab3bde21d1c24982a32a49f194c28a7e25e2ddd867de46a0ff6e338993558c4259f099736f89524ac791646749295687fb86286b86eba5017f292472f561ba400abe18870156228d70cf8
private theorem part4 : 2 ^ prefix4 % Spec.Ffdh.modp2048Prime = residue4 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue4)
    (e := prefix3) (a := residue3) (b := 1650667845) (n := 32)
    part3 (by decide +kernel) (by decide +kernel)
  rw [show prefix3 * 2 ^ (32 : Nat) + 1650667845 = prefix4 from by decide +kernel] at result
  exact result

private def prefix5 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (64 : Nat))
private def residue5 : Nat := 0xbd784ef7eef76b1a8c25674ed334e5b2429f72551c9fa4ba7ad48ad585affc56835922c37fc46497ea0af3193c63e703cf8db054bebe2298883424c1719be99fe8fa0a4009fa538e43ec05b991555762b7904b9366ba84b219023f75c39eccc2fcd5a5a2dd7227a0afe392d9bdf67fe7906711194704db74fc98502e8efca2ef42735cc877d97484c7d3faee7cefb27cbd15610ca83d1729399a00a83d6db0cc4374526a47464bbc113e9928b28e76d399205cef9076eda2da83e3ae753a27663a46b1aabf135544a682539df47f119ce5f6b034f5bf3e382723dacd0799f5551ca00b079743ec86dee2008d64dc87873fb1df40f258baa9d17f9cc254f08d57
private theorem part5 : 2 ^ prefix5 % Spec.Ffdh.modp2048Prime = residue5 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue5)
    (e := prefix4) (a := residue4) (b := 3228438120) (n := 32)
    part4 (by decide +kernel) (by decide +kernel)
  rw [show prefix4 * 2 ^ (32 : Nat) + 3228438120 = prefix5 from by decide +kernel] at result
  exact result

private def prefix6 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (32 : Nat))
private def residue6 : Nat := 0xf1e5b6e8c1856d3428f0e28879f27d7b43eaba8c865aca76d3b33d5bc8e42e965771f6cdfde39b45fb49ca75281d5fa89865809c58c11a6373cf868b1dcb340ad005cac4e8f838fc36fd4e8f4570b3167698b8aa2d5b4769aa56ef146371bfdf24b6feff9da4e41cacc2bc4a22de1f9b2f8823e20f2911cc7a51bcbcb0e55de16c3b57e9ed63db7ba2a5e531959ae0eb1a2718921a580b15e0d3aa5d5fe6ed41ca1c6ad980e97bf3ffd462a0d406d2720976b87078e63dd22434741074120119a92f2a057bac76ceaacab5c0ffb99489aaa641e963d427aa39a94e7de488fce15e73b0a422efc5e4dc0f7516922a30af92001ca33eb07698b1099eed57f9ca2c
private theorem part6 : 2 ^ prefix6 % Spec.Ffdh.modp2048Prime = residue6 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue6)
    (e := prefix5) (a := residue5) (b := 2491492100) (n := 32)
    part5 (by decide +kernel) (by decide +kernel)
  rw [show prefix5 * 2 ^ (32 : Nat) + 2491492100 = prefix6 from by decide +kernel] at result
  exact result

private def prefix7 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (0 : Nat))
private def residue7 : Nat := 0x1fe0b1ddb28afe2c7bebace7ad03b069e28401aaff8f8e31b8ab30ee9ca32ea112d88713da89d8a48bd65a86fe45062aa61133c269b0d7d1544d7b0325b0bbe3cb2a1d5ab2f176b4dbadc28571ca7355ee9b3aeebfec9c7cafbf62d5df5cded283d262be51e675269fadb6c1795a9e57514edd1cf288c8479bd41013fe3c01f0f920d8c63ff7ea73489a030ce401342cf5eaa9894636d9e29090b0aa2b19f1964e7e513cc6ca437fbbdb84b57ac069ee8321ac01baf55afe731e9d6afeb6f9ba17fa3e8e840e4946f10e88513eb8c40a8ef35abaa91034fd0e328c3f561c5ddec213b703f706f421ba803fd7ede455807fffa3342587a95876cffb38623a3735
private theorem part7 : 2 ^ prefix7 % Spec.Ffdh.modp2048Prime = residue7 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue7)
    (e := prefix6) (a := residue6) (b := 1161029178) (n := 32)
    part6 (by decide +kernel) (by decide +kernel)
  rw [show prefix6 * 2 ^ (32 : Nat) + 1161029178 = prefix7 from by decide +kernel] at result
  exact result

private def prefix8 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (96 : Nat))
private def residue8 : Nat := 0xe9b671cbd37899868096e1c28bfe7784eeaacaabe5d5aeca86681321dfb0fe2236e60cc0e96b91748834585884e08699d9112eb703ae3d7056c23720849bded56d571dbffa464937d8a557209657a64707c182b6db7e4f50f90f5630ae30a5a60c21353f3205575ae04f4992c1edf9463cc8ab9615439c78800b865f56f93ec10e9d77d1cc18996c6f7c918985f24ceabdc187f00628ecfd5b058dc40fb045f99499dff1f14d71f7a2937b50e2dee9b348b641a7829178ad4addd627e4f70eaf558e409408c9bdfc1b8c2efb5d03a0c0404c574024ff0a873ce78d62269e26313a03e71a36a0e6d7bc8726504a403c99aaddd67fc80360e67d34f9bb39092df1
private theorem part8 : 2 ^ prefix8 % Spec.Ffdh.modp2048Prime = residue8 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue8)
    (e := prefix7) (a := residue7) (b := 17162067) (n := 32)
    part7 (by decide +kernel) (by decide +kernel)
  rw [show prefix7 * 2 ^ (32 : Nat) + 17162067 = prefix8 from by decide +kernel] at result
  exact result

private def prefix9 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (64 : Nat))
private def residue9 : Nat := 0x5f5731e3ca38757c2ebdb96f82aa9c6b4077e86c750bc8ef32859aa26a1d64cbb30be1a56791f4d2d1cb93e271b0fabbf87d5f964e0d2fc10f10a6cc68c2818540ddcf75486576cf62cf5f079926c7c333eb615b4251c8d8c8ac24507d11eacddd50f8c4b75fd8309f3c7280dbde4047b032c4b3bcaff0d8ad0d8aced1477c9d61434d690a30cd2a3a7589e3a71d115cf6ba78493344d70e2f24e55a6b95a5d6f5fba910b20cc6ffe70eca19e2fdb5db8755ba1ab3ad10e0c7d1504fbf313092423e80d809bc63274735f7c19e1708a6ff76f3ad745c6541b95fd17f8fe88a63923ec09f4b42c832221a4952f9ceb7f89ef3765b8ec32f620ca1a7cbb181160a
private theorem part9 : 2 ^ prefix9 % Spec.Ffdh.modp2048Prime = residue9 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue9)
    (e := prefix8) (a := residue8) (b := 495570321) (n := 32)
    part8 (by decide +kernel) (by decide +kernel)
  rw [show prefix8 * 2 ^ (32 : Nat) + 495570321 = prefix9 from by decide +kernel] at result
  exact result

private def prefix10 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (32 : Nat))
private def residue10 : Nat := 0xbf1cd242029638f1b437940f49323a8755593ab4bc4b711c2f00615563c44fa4f430fff15ba36bf9c69ad7e5c4bdf65188ecb43dcfba4416dc028ecb82733aed61b784c2168ad987b7351f088932e1a38d761432d0f9c5bd7e8be46b31bd8626951929071f9d4d1b35f3e0b2f31460f46379dcb86085d299c050131231de2a74ae5812fb589664b10f4328492a2ac2209d492538cb1085f7c551ac09ffe942f506109490a2b1f4ccc1f83d1ba47273926bc396ef81e6542d17a03e17cb9850d8317f2f3b1e3ed2ce6925c1c8fa77c5872ebf3c1076f565a0ca71a5c9fa365f90cea93d90a715f4fdb953bb06157151afa4d86bfbdb7adc9baf2afadc7c9ec0eb
private theorem part10 : 2 ^ prefix10 % Spec.Ffdh.modp2048Prime = residue10 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue10)
    (e := prefix9) (a := residue9) (b := 681903164) (n := 32)
    part9 (by decide +kernel) (by decide +kernel)
  rw [show prefix9 * 2 ^ (32 : Nat) + 681903164 = prefix10 from by decide +kernel] at result
  exact result

private def prefix11 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (0 : Nat))
private def residue11 : Nat := 0xf4fd4327cc2c9ab807342fb2d803cc40c99f86c1dd43c8b6e69cafa883fe56e668c1a0857e18a685ab193f847c615731f4246467f98dc57b97636903121ec9bac28c265b8e1b6ec96a29bf013ea4a489b7a4267cc83de80a298274302f6a1c3fc4d89336bc1893cd6a3e1ebc014c061bd713515ee15078872be12768cfaf48aba872cab35033c77b2c54316a1fa233b25814e191e6c64ede031d0b2913750fcc97e5a218a6e7cd12531dad8f77a552b4a6a6d6dd7ca4c524f494360de0adf1de6c100428c64b9e1da44db9086cb427da99e41283009d985749f08c1827f5f7b32096583e330dcf80442da129c3f44d9ab6c238ce6ac056c67d2d3a8d519f3d1b
private theorem part11 : 2 ^ prefix11 % Spec.Ffdh.modp2048Prime = residue11 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue11)
    (e := prefix10) (a := residue10) (b := 3340370542) (n := 32)
    part10 (by decide +kernel) (by decide +kernel)
  rw [show prefix10 * 2 ^ (32 : Nat) + 3340370542 = prefix11 from by decide +kernel] at result
  exact result

private def prefix12 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (96 : Nat))
private def residue12 : Nat := 0x1560ffcb569cc60c01639171a0d2cb477606ba50419699f9fde600787c3764df1aa1b72d2b7f39f874df351108918d3ade873499af86e577a9be368047efcafd16dd53d1e771a331b0afc44d929848237f2cd6fd73d164bc401bd8ae13a0c0e9ccd8193a06c62d7322017b02c02065999916049dff3ec02c9b30bd630d6f5ad460bcbbb966bfae3140eb6d81e2d8efaac267baf4e18bd84f8677e5d11ad054d8b033f8548e2e402267b3a022af757397b7bb2908faa8279d34e9a2c12cada8899133ad99ebbfd7718437fb5d81bd1e0b9ec62cb4b42bc099275e64c9905bec9d404f77bb5b83fa5dfdf4315302e9186653ac20036732f201475dc5750a6f46ba
private theorem part12 : 2 ^ prefix12 % Spec.Ffdh.modp2048Prime = residue12 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue12)
    (e := prefix11) (a := residue11) (b := 4157246681) (n := 32)
    part11 (by decide +kernel) (by decide +kernel)
  rw [show prefix11 * 2 ^ (32 : Nat) + 4157246681 = prefix12 from by decide +kernel] at result
  exact result

private def prefix13 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (64 : Nat))
private def residue13 : Nat := 0x2401a41ce6cbfd12f9fc08eef302fa1b50bb01703e5ad62a45d08087610a7dc41888c75c52a45a2015e0de6651af7e2bf3f37692a521a0a89beb891559f7369a68071f8f24cb4ccb2c21495534933dae6997e2af21dbe1dc1889c5c62da2704e1dc37d6dcfdc1543fcd182991fd7c211505fae1989ea5e07c9abb633482f31c0fcaf817254188bde581f07e436d628a527099584108d55579e461efcf6d91bee7f3d6b2cf5e74ddc4e3233c62f73464c071525ffcec5757b8caa6845adb6961e34ba34558bc98fd717b64e4d56c300c404f8f0c0010c9fda5d294d818e2751d7335c43a3a28630908bf418475f3222e7742d226d6a9a10d34ad5177f4bc9576e
private theorem part13 : 2 ^ prefix13 % Spec.Ffdh.modp2048Prime = residue13 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue13)
    (e := prefix12) (a := residue12) (b := 3869057421) (n := 32)
    part12 (by decide +kernel) (by decide +kernel)
  rw [show prefix12 * 2 ^ (32 : Nat) + 3869057421 = prefix13 from by decide +kernel] at result
  exact result

private def prefix14 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (32 : Nat))
private def residue14 : Nat := 0xd6029c6e208a831a7d1ca1a6622ddd5cc5b3fe51921cebcd14202776b5d4eb0e60eb749ed567727ab48374fa7e1004a9fe35358d9a0272ff42fffbfe7cfad091a832bc243a24c1413ac4cc3a6351ff1ffd5c36720dba79d5bf7368fa7fa59d4e6eac1da98c75d466238dc785903ca0c6d13aadd318c841882c103ec05ce46825109fe05e60b884ef773c8ee5193e0e05aadf4fb248cd2d63bbcd41d1cc18cdcebc1b8e52aa3118fc51a1e3e79d24dc4cd7aad7d9d49986a17f50c4d474a46500ad503b979e629666232810519ecdff5a1149b4ba6b648ad0ea5660f5a5464b048254e9b1c899fff9ae16c42eb6cc8d116b0a5875e46ef377cf045f2bc9d712e8
private theorem part14 : 2 ^ prefix14 % Spec.Ffdh.modp2048Prime = residue14 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue14)
    (e := prefix13) (a := residue13) (b := 2551547190) (n := 32)
    part13 (by decide +kernel) (by decide +kernel)
  rw [show prefix13 * 2 ^ (32 : Nat) + 2551547190 = prefix14 from by decide +kernel] at result
  exact result

private def prefix15 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (0 : Nat))
private def residue15 : Nat := 0xd301aa955561ef53e669751c15555b286207b7632ce5e593ee119afd1d304e82b77df8ef3f043de5930fa3292315ac2e07c519bacbe108253258f3d39e6fd4e92dc14297fed3881fec96441d0c6ac4d25b91e26b0eb4c32fe7e84f77c124608e94b9fc329679fca77b406597ad20f7875e11bb006f92452e10e7ea3ab8bbd15c73c35fea609d176450ef1839258dd1d82eae9fb2fe99e7263e0c27d47676dad1b72a03f7945b03d4a809271201d4ca7fe3b7a3403f0c36910c55ac93f7c23444c4897d1c9a30a94a491ee8a9d9b13130fbea9d95fcc532ed22e647356dcac6ad0cb59b7ea67f63efdcddd42e3cdd7969fae12d685092fd87ef0c7b08e3a11f59
private theorem part15 : 2 ^ prefix15 % Spec.Ffdh.modp2048Prime = residue15 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue15)
    (e := prefix14) (a := residue14) (b := 4180642331) (n := 32)
    part14 (by decide +kernel) (by decide +kernel)
  rw [show prefix14 * 2 ^ (32 : Nat) + 4180642331 = prefix15 from by decide +kernel] at result
  exact result

private def prefix16 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (96 : Nat))
private def residue16 : Nat := 0xee9971fd746fd379e1c1cbc172a1ea7f781816b9c54cbaeaa08e23c21eeab8217d92c763901cbeb3f32db70a287d2641bcc32b2add07b4f56ae27c9c5e4e0f5b8254baf2d7f6c10bfa2db4a51cb0d08c11103b12783c0a84adbef87139f907c9876d3caa861cd489430aea601f1b2e1b289d72444b6f183427a5c176231f7d400e3486b1318a18939d6ccd2b0d0ab900d3dfe013c984e0bff4896288850d28b9b956a83181c8d5708341f3868285ad983aa6a3d29eff43a3b7b8a3a347031780b878ff9b0755e2d0ed03222234b81d58f2977ce78fce8efcdfe7ee18196e472900c7f97bded416384c9728aee88a97c89dcbfcadc9cf9e3316a3ef8498b67bd4
private theorem part16 : 2 ^ prefix16 % Spec.Ffdh.modp2048Prime = residue16 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue16)
    (e := prefix15) (a := residue15) (b := 2817563318) (n := 32)
    part15 (by decide +kernel) (by decide +kernel)
  rw [show prefix15 * 2 ^ (32 : Nat) + 2817563318 = prefix16 from by decide +kernel] at result
  exact result

private def prefix17 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (64 : Nat))
private def residue17 : Nat := 0x242bdf9935d2c7dcbe0a954b94cedd711e562703253f79f71cf1f4a5adcacd77bd38d6a8f77135f3eedb007582e5dc636b5a3fd430731e618ebdee49c15f56bb53925ac7df8ab0eb017a33c1f0bf6afc5ea44fff7871d6169fadfda9b3ccb626253d2ed43790d03b05d1a0a1f7d868e4da97992ef0c99e3a3aadba676583e43e8c2ae9cf263056c414ee1f29cc34bfe754164932cc85e57b5e3e6ab32abc2f78efa03e82d46e6632164e41caf484985783d18b32be8647283f83c4e6c3a133f833ce9d3bbc7476cfe1afe2f891b80f5a8360e18e9a9b57d07afc625e6e5e1cfd13af7a2e9920430ac007c57b1b7caf31858b1876595de8818dba05208418eeeb
private theorem part17 : 2 ^ prefix17 % Spec.Ffdh.modp2048Prime = residue17 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue17)
    (e := prefix16) (a := residue16) (b := 3064520994) (n := 32)
    part16 (by decide +kernel) (by decide +kernel)
  rw [show prefix16 * 2 ^ (32 : Nat) + 3064520994 = prefix17 from by decide +kernel] at result
  exact result

private def prefix18 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (32 : Nat))
private def residue18 : Nat := 0xbac32bae4915930e60cbeffd08c2094e71874b54e3ea63be8f89f4ceb0cd2b21af6d98d9dcb3117f9419c4b5d3858519aa3844584633688be271e28274e5f6c9eabce4665fe7d5d22ce560bacd4d18969ecc26b9c556445a80695c493a7e4904eb5b87efd7140d3776400fdf30f0ab06de5ff69ed12e9fdbc29b38dd3b521c1c0720c360bcdca614c3032746ad7d7114224e69435fd71ac27cd629fcca1b4ba6a8993545489035c512f6cbfcf4d49c267834022af42cd3bc65d381752b9e94279463c3fcee7a0ccabb0cf581f4532c71e8eafb314dcbafee53a4b95ffa455b448b3b27331af9385b74c496345028e590b978ad8860725bd647d135dd1f195f76
private theorem part18 : 2 ^ prefix18 % Spec.Ffdh.modp2048Prime = residue18 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue18)
    (e := prefix17) (a := residue17) (b := 4064467643) (n := 32)
    part17 (by decide +kernel) (by decide +kernel)
  rw [show prefix17 * 2 ^ (32 : Nat) + 4064467643 = prefix18 from by decide +kernel] at result
  exact result

private def prefix19 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (0 : Nat))
private def residue19 : Nat := 0xac80a73469d01cfdfd26d81e7fecdda97931f93f8c59546f2b2854001097fd21d3942d8798482acec2c9acc797ef10859f6070568d0b4bdada446dbb30471f2010350969e6d290475df2c4fcbe2df1fa968252e9aa71cb9eb8cfb9a2c767613659355928cee61cf98345eed57b0dc7af23aac63ff750ad92ec24ed51cdf2e7f660967ec272e0c6999599b3584d8f903d0a2ec9a9e8631a79dccf04e6e9a97a83401abf612ee8ac4b8f522c2d642472781cc4928a696bf7e78e8cee4f3a9332b101199639323ca0035f2b4bb77d80318928176b7fdd36af68fbd8649d6dfbd88296769fce26fe7b1a4b981bcf53ecfe19b615064805824b960b67fe79eb950582
private theorem part19 : 2 ^ prefix19 % Spec.Ffdh.modp2048Prime = residue19 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue19)
    (e := prefix18) (a := residue18) (b := 825180003) (n := 32)
    part18 (by decide +kernel) (by decide +kernel)
  rw [show prefix18 * 2 ^ (32 : Nat) + 825180003 = prefix19 from by decide +kernel] at result
  exact result

private def prefix20 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (96 : Nat))
private def residue20 : Nat := 0xcadc6e666937be5a13506ea1e1165031e0b53c5cb015c2bbe045fdb28805bafb2c494f0f18511a3390c68abce7ffc935a81161fb316178be1f3bfdfee1506b824762044e99f84b47e7f2d5fe378be0925686a7605a196d40fa09bc0b1d3f076144e4f6eb43d07be760eb450c8d977c0065fe946ca90d5f7d1a7437f5ddccea0a11617a3787c34c671aaa1420fd3d7bf12c4de9ee5d0451d9c2e2af1e831306c49cbbc5474eb21d66da2da1426542e24b816a6bd3bb8694cc5fb81f497ae66a019ffead6231aaccb021130ebaaa9e4c6f79bd93bcefab90c9c88e2da7ff7d90b7d37396c8a5b819e78f28393715116d58bdb5d93df744530cbcc07b3f71076283
private theorem part20 : 2 ^ prefix20 % Spec.Ffdh.modp2048Prime = residue20 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue20)
    (e := prefix19) (a := residue19) (b := 2049319284) (n := 32)
    part19 (by decide +kernel) (by decide +kernel)
  rw [show prefix19 * 2 ^ (32 : Nat) + 2049319284 = prefix20 from by decide +kernel] at result
  exact result

private def prefix21 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (64 : Nat))
private def residue21 : Nat := 0xcd459ccc55da15f7853ac2c9c5e2238afadd63872177635687f206fbc36c806021b5cefd71d6578ead141c05b3ca57ed07bc3a52fc5abfe7b45c1832e884031be8edafe921723ec67902a3e6821ebabc8ef744f67aa7139de638d7a9e381a75f53b2f0dcc705a223eca32ad03a99b1297700c2e2c9d92ec145437998bc7e9305fca65d0f83ee1b2d0217d55d3f448dcc3c83cebcbac9dbb9d5ac40947d3daee395c71411f1a826195311fcfbfd7b137550bea5a059c71a1db69bbcc1069c4305bfa99a6f9b60912a7c514258dd33a9b5e6f944ec22e2569ef0d47571a0953d87f39e02d586bd38e60d286dcab1bbb18bcba1f81c0f34823d9a4c54c71de64c32
private theorem part21 : 2 ^ prefix21 % Spec.Ffdh.modp2048Prime = residue21 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue21)
    (e := prefix20) (a := residue20) (b := 3541825205) (n := 32)
    part20 (by decide +kernel) (by decide +kernel)
  rw [show prefix20 * 2 ^ (32 : Nat) + 3541825205 = prefix21 from by decide +kernel] at result
  exact result

private def prefix22 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (32 : Nat))
private def residue22 : Nat := 0xf3371946f6c6aa0fe6ebd66b4ee9cb5095069905d5aaffb2b3ac374233d969e0dc36e12edc6646220a071c288426b7a05c9a67d2e6f4fbe955443e071696b6a95476aed804b7196d212e84bf99dad13ea7ec90e9a25eaeb5cd0eca861f671f07d11324da98d3a19928ca43d8a85c5ae92744929ff5226ce8aa77b8ad48652af8c844acc3095ece0f759eda8ef1b0eedc3942c13728fa3f9a58ef46715334501023bad57954733aab54d3c569151f0cc7bcb28f054e12401c9477aafbad9bdc4bbd59ed56387cf29f3eab349e0e608e1ead7016e41d40d839578f7d99483c33dee191df019e3c13389afe13db570b92e5afc219f472ba8f09d7d7749d98edebb3
private theorem part22 : 2 ^ prefix22 % Spec.Ffdh.modp2048Prime = residue22 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue22)
    (e := prefix21) (a := residue21) (b := 2248126043) (n := 32)
    part21 (by decide +kernel) (by decide +kernel)
  rw [show prefix21 * 2 ^ (32 : Nat) + 2248126043 = prefix22 from by decide +kernel] at result
  exact result

private def prefix23 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (0 : Nat))
private def residue23 : Nat := 0x8f5ab4601204f4cc97c7704b7512f6bb1eb968a1c5957f2f75a3a1e1167fc3d8026c26fba026fd62ae81518495243e79b0eb1c3be9066ed137afd93948c8fbab4a4c8d82f9155a77c5265035fd7bea35fcfe91860dd78e9170297f808ba42b8efe246c927ef013fab41177b0812bd47576b3bca39ed93875edb4afb88d70d561c9324be603492a8f1d35b85785a970ba7169c000d969429f90fd4b0caf06056972f0a07d408e79c310071df2aadb6cec915d815f7fac302da10a6beba78603967ee5e1b3f68eeed5fe5909efde3e98624c058b1ef1e586187ad7722823ec9ab19f7d8c28ab4cfd7fb76b6a0e387b958a099f58d5dd40d45e8c6395d7b10e61c7
private theorem part23 : 2 ^ prefix23 % Spec.Ffdh.modp2048Prime = residue23 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue23)
    (e := prefix22) (a := residue22) (b := 2047040502) (n := 32)
    part22 (by decide +kernel) (by decide +kernel)
  rw [show prefix22 * 2 ^ (32 : Nat) + 2047040502 = prefix23 from by decide +kernel] at result
  exact result

private def prefix24 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (96 : Nat))
private def residue24 : Nat := 0x733c406c971bc567f23bc5943b8e39ef513f419061361127c16fd87df27cfa90867871c039f2f662e0eeb300e22689d203d8eb51717b9a6dbed0923fc50803799c9d7ffe14c286f8f4cf7fac9e67922bb203f1a32ee659486316d98eecc355ca031204e22b7c8b1da17e097c63947ef8a022a61ee0c32aba61c1d4fc7bcc2b044fbd236186bd1897ddf19920426d4570a22b7f134170d9a91f64aca89df1927cd2f214778bc32472e5f94eb2e08ca258754aeeca36d277560487aa7ab5b92500b58532d57332003b7aca54c8dbedd0a854f847e46fd567ad099e639d9b40d8c91250ba169d24d7cadddf58bd5f26531d55f1c250948b036c2314fdc8f8c44229
private theorem part24 : 2 ^ prefix24 % Spec.Ffdh.modp2048Prime = residue24 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue24)
    (e := prefix23) (a := residue23) (b := 4145821181) (n := 32)
    part23 (by decide +kernel) (by decide +kernel)
  rw [show prefix23 * 2 ^ (32 : Nat) + 4145821181 = prefix24 from by decide +kernel] at result
  exact result

private def prefix25 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (64 : Nat))
private def residue25 : Nat := 0x1b63005cde9fcc88ec6f8851232427505b493a4b29df0808c3f9b88576d7942564836e058dfdf1fef668855ccb569473b80e10d83ee78ab893d6dbf81c79629b7a8f7eaefa81e8a7b038ab8085e6b9a61c0bddb7ad31ea1b69ca2dbae9b0ea62c8e0aa49e389e42c217349875bf9047d7396f5ff4f2b3bc8f57f2aa3a1af99d07fd01adebb8f89b45328a537215314fa690cbee41b62bf4fd557f5918d5eab1be3d7bd256fcdc93f788c51c1c92fbe9339e9e2df574bdb68ee0da18c1fb90d0668d8fc1f3a4d578318eeff3cd06912326f3f789b0993c46af0277855a1d265db79d0b4b7b1f7f3b9959deffe51d5f9d985df2ce05ce01dc5d95f97dd59ed3534
private theorem part25 : 2 ^ prefix25 % Spec.Ffdh.modp2048Prime = residue25 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue25)
    (e := prefix24) (a := residue24) (b := 2906968018) (n := 32)
    part24 (by decide +kernel) (by decide +kernel)
  rw [show prefix24 * 2 ^ (32 : Nat) + 2906968018 = prefix25 from by decide +kernel] at result
  exact result

private def prefix26 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (32 : Nat))
private def residue26 : Nat := 0x109e11760257721a0b0d3bf7a9e4ff7b9d7f6fc2eb41c78059bd9a2095af8b63c6ef2ed556b54e192349384f026f26e0f7138ed735c05f786b799939ad715e8e115d78d7d8c5fd2792be6a659c27614944f849b35cf257b40ace45edae7b7253d4893c0de2dec22416fee1d1ccaa431a70367dd1b0fe3cf42cdb2266257e9a9ca602c74db27f97e043445d44bfa9cc51cc9474ee50a0ca22085803b6be4925f1d9f8f581376da907d982405ceac24025243f420d24d4867e135aeaeb377d762a6e9d2a58b6a070b167de67cd1b37ca47965ed5beaa1c6f1afcb4ea5fb5012ad0a52b4150256f82db65e984da70b5f31eab4e17cbdd3927803c7363e0c5762641
private theorem part26 : 2 ^ prefix26 % Spec.Ffdh.modp2048Prime = residue26 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue26)
    (e := prefix25) (a := residue25) (b := 3612316168) (n := 32)
    part25 (by decide +kernel) (by decide +kernel)
  rw [show prefix25 * 2 ^ (32 : Nat) + 3612316168 = prefix26 from by decide +kernel] at result
  exact result

private def prefix27 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (0 : Nat))
private def residue27 : Nat := 0x59538900cc0ae5d0bd740a0e28fbf5370d44035d19cf78a7ae23b3dce32b0483a3469c1c3bdecdd52de508c6a8cb7e68a32ebf6c782df74549a56ca66f4f48145fa812c246b34e28e3dfaa5e7bc9f3ea3d2877a57e364659a4c962f9a1424e52bf2a2be29ae45ff5c84b3b43e082244ccb822341e4f4b8c7d6505a18d0a436440285dd18e50e46945ae32c854340584a1b774a0d32f83ff618c76f447aab0a4a4566c016f3248ece88ac74f29e553c7b541362c1dbd83306a208b627e82bebaae244fd209cf0f8a0e53c7861f3fcad90da39f4824953bd0d603d48a789c97a4e982ae51884070da2eeaabd3c908d0379f1014861faf3cca635e0df44d76c602d
private theorem part27 : 2 ^ prefix27 % Spec.Ffdh.modp2048Prime = residue27 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue27)
    (e := prefix26) (a := residue26) (b := 3190132723) (n := 32)
    part26 (by decide +kernel) (by decide +kernel)
  rw [show prefix26 * 2 ^ (32 : Nat) + 3190132723 = prefix27 from by decide +kernel] at result
  exact result

private def prefix28 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (96 : Nat))
private def residue28 : Nat := 0xbfa0f21fedd30decec0718321e33b909930dc6f4501a2889c14a2a54b5d8628bcc9c105f60f43c05bcc12ed895cc1437c91a002e4fe5be387ee3c9aadc9bbe2855a6e1c3d57f53ec845a876aef6fa3120bb7c098c2eba6e83b6ce5b1dde33f65e06c1832b5c3e12eada29d7386456ca41bf15b34719dca01bd733715180705648f90b06704399f1d0d7f9c0496a5fab21be7c83c1b3dcd181fedddce6b22d2fd0f7913a017f61eb6f0a43d523d76e3675a6bd01f0213c37179816b3a08944ebfec707026309353625164010c7ffd0e7e2d80cb708b7926aa0543bfa9c5bc1a6f04a8d26f95b3fa30a193be19296e0ebf3ba1b0f55ffa9ac89f58ac86956fb4bb
private theorem part28 : 2 ^ prefix28 % Spec.Ffdh.modp2048Prime = residue28 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue28)
    (e := prefix27) (a := residue27) (b := 613692200) (n := 32)
    part27 (by decide +kernel) (by decide +kernel)
  rw [show prefix27 * 2 ^ (32 : Nat) + 613692200 = prefix28 from by decide +kernel] at result
  exact result

private def prefix29 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (64 : Nat))
private def residue29 : Nat := 0x142be8f8c37927aeefbcd1958bd697bc689105f5f9008c25417e28dbfaf6bc92fcfa2fc8b6771475fe9852f925781cbbfff3b5b33c8b2b866a7f683adb3ae4ccd26042d8048a6a85a10e4954844aae59589ce8605f8eac841bad93dc7b5efdce890765eed215180ff532ecaad347bea31dc69822aa208967ff2a627e320d9e4c3c9ca5e779d897254c3ced6cd906dccb2d16fb56a49f028b55fea7f33e6af5e6324b7063aedf28da6e82f2247eeb9a810b2f04dbd02f641102aba7a38bf0d72e2d1ff3ec7904a681ee9badc002baee70de40a38592f1ddd72c3c45b8dc7969aa0062727b3947ff6d762df4186b9128f18b133d853b77faac511ea773527501ef
private theorem part29 : 2 ^ prefix29 % Spec.Ffdh.modp2048Prime = residue29 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue29)
    (e := prefix28) (a := residue28) (b := 4134677918) (n := 32)
    part28 (by decide +kernel) (by decide +kernel)
  rw [show prefix28 * 2 ^ (32 : Nat) + 4134677918 = prefix29 from by decide +kernel] at result
  exact result

private def prefix30 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (32 : Nat))
private def residue30 : Nat := 0x79b0ed670118ab33f3e49eba045d1b4ce8710c3f3ded09529c383d5bcb82f5ff7abbbc18febd6f282c1bd65a9b9d5e29b8d430affceb1b205e55f681711b86c83bf0e7c895fcdd4c844d467968081ab0d1e439e9f5eaa1e8ff525029d0e459a512e983fab496169fc0aa07d2b3a4eda5fe64c76030de7526609eb4648a0dfef855b120ca4fe071869f316164d63b0d709530f6055d329c08cef4472144c6430691784bf9ae498569fc1cd100a96c730f7a84124941a7a025a8436bf38fd29f5c850c6e5e0459ce2d0e076ee309b37d3b65f6716a1eecc26b20c9ea258ba62bbd484f4752a0bf2f83967779455b01e08cab1a25429aea64a62ded7ee491611aa
private theorem part30 : 2 ^ prefix30 % Spec.Ffdh.modp2048Prime = residue30 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue30)
    (e := prefix29) (a := residue29) (b := 3774889564) (n := 32)
    part29 (by decide +kernel) (by decide +kernel)
  rw [show prefix29 * 2 ^ (32 : Nat) + 3774889564 = prefix30 from by decide +kernel] at result
  exact result

private def prefix31 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (0 : Nat))
private def residue31 : Nat := 0xaa3e4f3d11a0f393a1869a5f3b5a105665b9da5c48a6b0c3414ca92f863e380825a19afead726d9aaba2b4b4f23aad89036e8db9d7d50269b954a891d273fdb27914b1bf9b4eff4754900d649338bc90e04166ba9918d6f1a3a605e15083f5ef852803ac9bb708d9296bbbd30271f8db4d497aef2cdd0a8181e83742f29200bee3f99b7f0415ce13ae27e091f360de6b7d5be3d6ce754a4c7772c427901f11a9168ba91cd790ae79669c2ce64a50c18262eb9c16f8adfa4df26dcbb28a53d1ed11dce5a96e12ea0d42e5580e67f979235870fe0e12f940f99d7b1f4e5b87fb513836d49d59b798b992a7ad5715aef727c51113d833f7cd7e955aa257aa530a09
private theorem part31 : 2 ^ prefix31 % Spec.Ffdh.modp2048Prime = residue31 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue31)
    (e := prefix30) (a := residue30) (b := 1353834370) (n := 32)
    part30 (by decide +kernel) (by decide +kernel)
  rw [show prefix30 * 2 ^ (32 : Nat) + 1353834370 = prefix31 from by decide +kernel] at result
  exact result

private def prefix32 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (96 : Nat))
private def residue32 : Nat := 0xc551e8e2bd9488e184419de4b9c7a5d9084da0c5382adbafa450642e713202853ba01107aaf87cd1e41b4d20ea90da0bb8336395ab5ef4cec055579ba2b71a25cf22dde92205d5cb3989f7dd931cc9c489acdb3d30cdfcbc304e533d9b9bfd1ba47224f86f2ed280376ae21dd9ccb8d7d50fb56ba17f1eeab98731526f7830229c5dc28502405128908ad181974e7776713ea595a4bc0defe39b059e104526d6add06060a967e7301a08a7cabf63d3fabe16544658aa5a8d799aa611209c46e49206db0416884201310215d187859eb7b0642f30461b99bdc84adaf7cc1b61d340172a6de837eb32d1dd2b7afba309fa6d562d2b6fc6e1ba8f663d27968af10a
private theorem part32 : 2 ^ prefix32 % Spec.Ffdh.modp2048Prime = residue32 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue32)
    (e := prefix31) (a := residue31) (b := 3429704731) (n := 32)
    part31 (by decide +kernel) (by decide +kernel)
  rw [show prefix31 * 2 ^ (32 : Nat) + 3429704731 = prefix32 from by decide +kernel] at result
  exact result

private def prefix33 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (64 : Nat))
private def residue33 : Nat := 0x7b7653dbbc94c913b51c79472eb9995eb878ceab5e3c9f4faac165227862962072e151b92d2f381bf481c6f145cb0b9efbf32e1fa582512f71f7f97e15b225c8814359a20a693ed32c4400cfe43814591c343c4ed303fe302fa3dcf72650da419c9fef1ef9eaff1efc19dc5066f6bdd7a5a1c1fb01bf449b68a71bfea540d9e29bac5e88a9b5f1dff546b89b32393fc1b8940c116750d6593e13d615cfb405c6d219d780bbe5a737866533cb952d4ab7940c080eb58992a25eab0ec29b813e390288bec2b9720c8f36714c154593f0a1b0acc03a4febbfbf2eb66def4f69fee2f408222ae5a5dcea03668361de1e5b732dbf2f2e0c5dbbd8b97d8d7b281e39f4
private theorem part33 : 2 ^ prefix33 % Spec.Ffdh.modp2048Prime = residue33 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue33)
    (e := prefix32) (a := residue32) (b := 237693389) (n := 32)
    part32 (by decide +kernel) (by decide +kernel)
  rw [show prefix32 * 2 ^ (32 : Nat) + 237693389 = prefix33 from by decide +kernel] at result
  exact result

private def prefix34 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (32 : Nat))
private def residue34 : Nat := 0x731e996928df3d79d37a1186801d6e733a36d1392de7b9d29d5939fa5c6e4675a49689516289074d0bb58febcf3fe97c9ba8c6f9d8d0589f38a46a2485487a227e655989484338e1922cd1edece5cdbf79fc348b85f730a128fe503c40741042af5e69608ed9342a8adb7395421b2eedb10194ef936fab6250b7978e88bfdfcdd006a86b5dc1bc8991feb0fabf4a6f3515a1ceb33ae2224f59e9858510b1c06ca6961df1bb05ea7c9592a56826283c226fbe2ad4a4dd5c2a8a2d21823f172e0c3b4486e0b03d2b4e5aaeaf8b9f6e96dc27fac7c5eec9b12b8c70f362e48d06ffb51bfb0f0191c6baa3d64c5f0e41f5571a31b9144ba2fb7f605a19d0985860be
private theorem part34 : 2 ^ prefix34 % Spec.Ffdh.modp2048Prime = residue34 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue34)
    (e := prefix33) (a := residue33) (b := 881532884) (n := 32)
    part33 (by decide +kernel) (by decide +kernel)
  rw [show prefix33 * 2 ^ (32 : Nat) + 881532884 = prefix34 from by decide +kernel] at result
  exact result

private def prefix35 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (0 : Nat))
private def residue35 : Nat := 0x5db456ee459509b535bf8703ac8c7706df363483f9a4a99e28199c1f0829ea5242bf43f55feb61eefb8fbcd199f9aac978c75f0816eb75d3bf5fdcd92341f6471ffa05c9bb5e7cd586b473d2bde56f24944630d2699738a1abe9d437acf8585d9ee164658b32843cf4cf85ce128448c1ad3cae32aeded108806445500a83de5a4f639d8ad928d7dd1c286922d44ebffd1b0afba2a2be64a91952b14f417041c6bd12837fa9f961e223979dd61be7b48abf844aed2ca4c03eefa58ec7bbfd840d85cf75650b7ceacc340b163bfe9202311f4dce598e23dc98991efaad227ec1f2400c5e6f91eb740812edb4ef5816a136a1f61a3ce2b059077cb84a1c4269f2ec
private theorem part35 : 2 ^ prefix35 % Spec.Ffdh.modp2048Prime = residue35 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue35)
    (e := prefix34) (a := residue34) (b := 2123524015) (n := 32)
    part34 (by decide +kernel) (by decide +kernel)
  rw [show prefix34 * 2 ^ (32 : Nat) + 2123524015 = prefix35 from by decide +kernel] at result
  exact result

private def prefix36 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (96 : Nat))
private def residue36 : Nat := 0x1a7f3c299355f8b7f95eb4208f931c1efb433d650221ffce5513443d9399abdbdac1e4106649ab33c2ea5b53b74d1409b5dde9bd79e92fc3a0bc1df247537deb0d379c5753a97a5d1d8091c777d2c72a1c0a65bcab3686d2c172e2601420930ccd088e28dfa9770aa86a9eb9248f0decf542843e656ea1aab136682ddd6a7628a8cec4bcccaea47144b076cfdc36352a28ac58e16ee6af1b214aa4889921469266092e357e8ba8e7d8128d534a36d2364b17f6d33164bb0e10c204f1f053f9856c8d8454474f3acd6fc03d3f9c31d948f664a0f16616d3a9ab17a3aed21add30180301f7f26403b80772f857451b9eaaa78c2531b3577f610e846e1125eaa153
private theorem part36 : 2 ^ prefix36 % Spec.Ffdh.modp2048Prime = residue36 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue36)
    (e := prefix35) (a := residue35) (b := 3249712785) (n := 32)
    part35 (by decide +kernel) (by decide +kernel)
  rw [show prefix35 * 2 ^ (32 : Nat) + 3249712785 = prefix36 from by decide +kernel] at result
  exact result

private def prefix37 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (64 : Nat))
private def residue37 : Nat := 0x66c98967f1385ea0666fca635eade74ce6ad3ccf8648e82d8fcef8eb71622984f99d5d120d24d967248b9a99e9482c72fe73e03e5443b498d5db36404f5c0918d39c9168436f888efdedf09de8a09c75741ce392448e42ee9bf51499b2dfd7d10698a92d2fc52d3942a8f848a41788141f50b3cbf0978ac26b6ca86a9cd2bd0720e06b2b1eefd2b9a45102470fb507091d2b6d68bec63e5c304faf06b3cd33f990114c116f5298883247baf238565fe2f53cb09723ac7f514022c018d31966c1d6384e6a3f78fe037954b8e2225f1c3e90d58daf4a4a582abff83086b27de8f2c1d6f7a6fae43e81e58b78abd9c96372c47df0bb0eebe54bb3f3234d660166f5
private theorem part37 : 2 ^ prefix37 % Spec.Ffdh.modp2048Prime = residue37 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue37)
    (e := prefix36) (a := residue36) (b := 3998340811) (n := 32)
    part36 (by decide +kernel) (by decide +kernel)
  rw [show prefix36 * 2 ^ (32 : Nat) + 3998340811 = prefix37 from by decide +kernel] at result
  exact result

private def prefix38 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (32 : Nat))
private def residue38 : Nat := 0xcfaedd48bb0240ada539c7ccc6e79052d78776dddbbf7e15384027b43c55b97284d8f986fc0adcff62ab186c9ffd5c47617dcd26a5461a0a29c1b4f124ef8d796618856ffd6c45f36b2388ce634aef28871ebdcfc577bf442bd29a9a81609da5c5f93615bdd9cf5285f4047131d0139933d3193ca4a430e415e4a134096bbcdf3f7e08cef4aa082550635e798a2c3f14e823df684b15f6a0e77ab40cf0f9757374d56bd51c97eae4df984844a981018bf8be7ec0a2ba48aff006d8ad4eef264aba4b505674a1da102b24cb55a46fbf412dca332c0ebefbfeed095e7f82dc6e990e12e6daa3266a580754c99f7afa7691fb06bc5fb4a1598245fa73cb664a1c5f
private theorem part38 : 2 ^ prefix38 % Spec.Ffdh.modp2048Prime = residue38 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue38)
    (e := prefix37) (a := residue37) (b := 238123435) (n := 32)
    part37 (by decide +kernel) (by decide +kernel)
  rw [show prefix37 * 2 ^ (32 : Nat) + 238123435 = prefix38 from by decide +kernel] at result
  exact result

private def prefix39 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (0 : Nat))
private def residue39 : Nat := 0xd99355d85c18ece5a6bab13c04babb5045d06a74b31e36e70b59e7bba62aa06bfd8a9f87df8a13d0c496867229d6d0492f0c74dd52515bacc0660b6ee27e65970aaffd629adf989aa58f8dab5d6b043e617a7acc0ff13c3e4b5546c921d74aedb92e70cec597b2c2b390830d4629cb96421a35d261230478dea3dfdfa29a90dde1a027c57bedc83d2cbe60c404fdf8eaa8592782ad74dda6756b784497efb4bebfe4e76d8fb1758839d3ecadff095c1d300176b8e150edc2e1500fdb89d8e04e5ab43e23b70584b816583b68db60ca1dc67d36834dc36f97cd5f866d48eda5b8db65d7dd78246b06a056629720643246d785a67fa2f30f005a128e3a7628c312
private theorem part39 : 2 ^ prefix39 % Spec.Ffdh.modp2048Prime = residue39 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue39)
    (e := prefix38) (a := residue38) (b := 272804189) (n := 32)
    part38 (by decide +kernel) (by decide +kernel)
  rw [show prefix38 * 2 ^ (32 : Nat) + 272804189 = prefix39 from by decide +kernel] at result
  exact result

private def prefix40 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (96 : Nat))
private def residue40 : Nat := 0x12d952da5249114ad2913f309ba61e9f7353bbf95b5245498f1c6a9b12517fa787d09542629896af1bac78232df855e5eb6b29d91559281ba8020bf4cc54d2ae0263574fb830631af258febd015d9e8788d643de4ca5aa5d20b1ecb250baec92d2f064cfc4ae5c8da8fe295ad70ebb7aa271739648c1d3bc9418763b16c07082333decffd69227d5d66c09e371cf18339a0ebcc95c4c9488c848bf0caa6f0b8f6a94d79d3927f706680896d7b7fc466672227e4678a9804f15e72eee9c508a63dafec34419a54006769b90a57a7a6af2d4ea759c88d90c448c90586bc0ccb2f6c7bdd3963b6523043caa821e20090af5d9fe439554105d8834d42c46c07bd4b3
private theorem part40 : 2 ^ prefix40 % Spec.Ffdh.modp2048Prime = residue40 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue40)
    (e := prefix39) (a := residue39) (b := 3479868547) (n := 32)
    part39 (by decide +kernel) (by decide +kernel)
  rw [show prefix39 * 2 ^ (32 : Nat) + 3479868547 = prefix40 from by decide +kernel] at result
  exact result

private def prefix41 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (64 : Nat))
private def residue41 : Nat := 0x3ad088f230c453063fbffb6d70f52e9a27f165993a1e037e0262621a62cb812018705e44e12f23c9282eaaae5c2d925b498d772b47eb4c0384301a9174e273abf1d49f0abb3da41144b33b533a2f002ba9b1480ba541bceacb2c82e4f5aef0113edea42d0466e1aadd4ee8e1f2eda4da733f84b7a0f128e013e0a2b6aa5795cf57319d1815655636dd8cc1702b6789e20e6b940dc630694559dab7c013b8253a4242d807105c9d137e25b58602944f6a540b3df6e38208849cf30e75bfdb9454ad65f127141bd91e6040211361f611bbed43cee43d1aedcba45c76fbcccd4339bcc9a5f58de2335dae5d0039e63333bf88922b7e23ebc74c078781dadcf42966
private theorem part41 : 2 ^ prefix41 % Spec.Ffdh.modp2048Prime = residue41 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue41)
    (e := prefix40) (a := residue40) (b := 3091942198) (n := 32)
    part40 (by decide +kernel) (by decide +kernel)
  rw [show prefix40 * 2 ^ (32 : Nat) + 3091942198 = prefix41 from by decide +kernel] at result
  exact result

private def prefix42 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (32 : Nat))
private def residue42 : Nat := 0x3dae2291b614a6e275250ea8bf195301e872783701cfd77552843a64c32463cdf6f5c055b960b1eaad7462648b119ababf69d049950d1909a539fd2dfb72cfdab73996d37c70c5f94311635aef41e2b2eef7547b43980c234cb1ef04c9283052f6207e31b1ad276f29ee21ea2766306d1e865f9d75cf81e15c3d963e151462ff7132a970f43a4b18685949f369a86e3d8ac3ec6998f0393508760370e275c1a0a619427880aba483cdae89f645f724eb9e5b09bcf7c51d94af1e2952e204280752bbdd225e0230397f585f93f11705ebc4bbdca506d22fe38078b365bf44b3a6b413eddaf42e9b1db8fcea65d1239f54ad3f978ef788d338e2fbe7b469c4647a
private theorem part42 : 2 ^ prefix42 % Spec.Ffdh.modp2048Prime = residue42 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue42)
    (e := prefix41) (a := residue41) (b := 3011910311) (n := 32)
    part41 (by decide +kernel) (by decide +kernel)
  rw [show prefix41 * 2 ^ (32 : Nat) + 3011910311 = prefix42 from by decide +kernel] at result
  exact result

private def prefix43 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (0 : Nat))
private def residue43 : Nat := 0x279c516e384e9250f4c958bf7003b527734a8d9477ce146f622dd2a112b3cef2ac104f6089db1cc0c67394ba30c472fc06954018cb85495d158aeaa5fda6844ccce98b9e6f254bf3f96db7806d9cf58ee17bf1fe073e6d52ef9f6ca56c2569d076fcc6eaa75195f62b0ac310089899eb113b540243685756552af69f093ffa23bf4e1248875c9c4b0952164ebea66e06debed0f81421d3e2e742b1e06bd9654529aa214a1f9cdd30d9b2404bffc88e848fb75cbdd8bb60a2328c3286678f7356be450a812e4f441b1fbaa270b0c4ab787cc1db89f344edfe18ca4742271e328479750774e7a932ecf11f6bbd707eb0395a410c15ee80d6a529271ede59d9f6a3
private theorem part43 : 2 ^ prefix43 % Spec.Ffdh.modp2048Prime = residue43 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue43)
    (e := prefix42) (a := residue42) (b := 626936834) (n := 32)
    part42 (by decide +kernel) (by decide +kernel)
  rw [show prefix42 * 2 ^ (32 : Nat) + 626936834 = prefix43 from by decide +kernel] at result
  exact result

private def prefix44 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (96 : Nat))
private def residue44 : Nat := 0x3f3145e3a2525d5c46e2cff7965eb21c140d5cc7cd7beb9329f7381655e5b3238e52ec1cf630e19739c9ea4705b050e110bb14f7929f83af57ba28b1358a166db329c44e5cb9d536b6983f0cf41425ee882fac72136af631cb78c846e649fa7c46cca7e4c720b027ef544ab6edaec2a649a89c478be0ec60c16146ba63a6bda9df2d9839e340824e793a2cb35c01a67264b51df4aabb4c7398b675d53564e9a49b169a03363369becfa2affb7d907fc9466a7f7bc740d54f29ee704cc68cd031369347b7ff43440103331edfa3e6f768599f63769f1e5d7a040af788f8ecfb78bffe7ca92547b3a7c18d90fe73f3f09631e4ce3bd1e182b93b6d2cef2c56c0f4
private theorem part44 : 2 ^ prefix44 % Spec.Ffdh.modp2048Prime = residue44 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue44)
    (e := prefix43) (a := residue43) (b := 2025469444) (n := 32)
    part43 (by decide +kernel) (by decide +kernel)
  rw [show prefix43 * 2 ^ (32 : Nat) + 2025469444 = prefix44 from by decide +kernel] at result
  exact result

private def prefix45 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (64 : Nat))
private def residue45 : Nat := 0x998f7157895f13313c26f069f78389b2fd2b95bc63ca6ece5d0863315e9d2df2cb403c29b5fb3eba8b03ec48d3756379e9aa4bffd766425cc7c545c2d7371d7673c7a1465deac0d310c10c78bb19ca60d06c5a8e5727d833b0c3f23ddc2572cf10875f9ce6e2847c4905aee49cc496e0a5cec1e3db353ddb13e4957f6fbd5a242e061081906c2bb5ebb9fd7e188e4300d8e6e1880c687e7b8df6d844ea4584dd36153048c41be2dff319081b74c71772bd8b70356135bef650a1cb05a2640533e323425326516728e1734dd844a21e8fba642c2141f157a73f9ba7d4a0369a90220b1ce024b818ef720e6275e27a84777c6dd395942659582ece721e9ab6fc32
private theorem part45 : 2 ^ prefix45 % Spec.Ffdh.modp2048Prime = residue45 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue45)
    (e := prefix44) (a := residue44) (b := 1695289534) (n := 32)
    part44 (by decide +kernel) (by decide +kernel)
  rw [show prefix44 * 2 ^ (32 : Nat) + 1695289534 = prefix45 from by decide +kernel] at result
  exact result

private def prefix46 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (32 : Nat))
private def residue46 : Nat := 0xb68d300096a389f7849f57ea92542e8b2af92367e4aef6af23d26734d784c21824ce0d4d58699c7428786ea2be61a2cfe44dade1b19db7be427ff1c6803d59f1104eead5aec111cdbd764fa4d3413accbcf526e4c1b10d2788918d3789ef16691c1c233d777b430810656214c795d87da976b658a4c5d6b74f15e6a5e8f0710c28439cfdea71aa7d61a4467e0f8309cd15e18a70b827b5f0110a2781332d7dd8e9db92827fa7b14c686ebc1a23488ba5be599d974544e505391b10da2991e27870bdfe1c319ec865d9dc60c84b853c1d6a4824ca0fecdb6ceafe739e67d8d125c61de28002d8be1778a54b45611da12cca48b7636484c26c997b9056c6e5fbf8
private theorem part46 : 2 ^ prefix46 % Spec.Ffdh.modp2048Prime = residue46 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue46)
    (e := prefix45) (a := residue45) (b := 424161059) (n := 32)
    part45 (by decide +kernel) (by decide +kernel)
  rw [show prefix45 * 2 ^ (32 : Nat) + 424161059 = prefix46 from by decide +kernel] at result
  exact result

private def prefix47 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (0 : Nat))
private def residue47 : Nat := 0xcf9019e26cd3d8cdcfc91862776b7421eb38893f6076b554ff4ff175d504ee0266ac1d0a14b39fa6d1bc94658f1f84ba3ff7bdd4ef77f98f732891b05f180da3bdfeef21f05049c1a6ab9857c6bad34f49e277011c2a5e29b1101c082bff14a2d743207589d4a44fb4f1bb0b03ced7fe30ccbd2df62980e2a74813ffc7307e2fea3123dddb9baadc4ceeef8111380ba9a33f2b3947bd8b128b95dd651b0d069939cafa432303db347503d0cb8b34fdae018cf910b26ebfec2026b6d3dccb8e5fd10b8373bed68a01b4ec44fa3c115e1132cfae4a88144e4747de242c3f9c3f772ea814aacbbc5a0e16c6b85c3369cbaf83b13883ab4db93ed9e3158021cbe92e
private theorem part47 : 2 ^ prefix47 % Spec.Ffdh.modp2048Prime = residue47 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue47)
    (e := prefix46) (a := residue46) (b := 387671837) (n := 32)
    part46 (by decide +kernel) (by decide +kernel)
  rw [show prefix46 * 2 ^ (32 : Nat) + 387671837 = prefix47 from by decide +kernel] at result
  exact result

private def prefix48 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (96 : Nat))
private def residue48 : Nat := 0x6cd9c2387fa81c6a75edbb3762040deb98b257304c2b411a6839f608f06fe0cda1233407501a71c8b4d1e671346e420364e2dfb8f119b639868df33c9cf3c5391ad641fd53f9264fe1756e9bb02b087bebd7e2766c7b5674aa784643404245e99182a1423e89f6d86c96b4059080cc630c2c40fe8dd19a975081e4fbfa048d0c540e6b031227c05120fae2afe157ae9dfe3c46fe2ef97c169a1b40b81fbe04d2d96ee208df02b98b93e94998e7a0f5d582f4e9dd0d24d85c2d30bb0caec47b6076912a00d0a4d6ca239cc1358e4ce781406f3ac60b2cc1998043f94bb6878f064ea72ad5e29d16ff8fd3dee3cf1be5beb5ebaffe15b4dd950b348eaa62c448f4
private theorem part48 : 2 ^ prefix48 % Spec.Ffdh.modp2048Prime = residue48 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue48)
    (e := prefix47) (a := residue47) (b := 4056890262) (n := 32)
    part47 (by decide +kernel) (by decide +kernel)
  rw [show prefix47 * 2 ^ (32 : Nat) + 4056890262 = prefix48 from by decide +kernel] at result
  exact result

private def prefix49 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (64 : Nat))
private def residue49 : Nat := 0x33ef6fc58cdd32946d56250726796d931a3903f6526517b568cdf0aa3a4e83defb43df98b020efa25ea208ad66d6970ec711ed4bbecb9a602e5c79eafb5fca2aa41a852157de2c0f2944984c0181a86f2545c47ad644c8e73cafe33cd906e6b36cc6f6001fc0eada64a7f6772c6f43db74297624747ee82c9b2f93b2196f1d248ee1dde67ab920977c810c5f3b66474eee6c31fb96a518ce6da94ca35db1b2b23785829a4d01c39198fbd68d4c55d75a6f25023b676ae26ce0b22bffca5f5f1c5cdf4d1ceaa7f1887efd1896a97720f517f678f4e0e1584f7974761e69a5ce458c65c24a36a91cd52798d6140c3478af192de002d36d3e89f39d852a42de9b27
private theorem part49 : 2 ^ prefix49 % Spec.Ffdh.modp2048Prime = residue49 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue49)
    (e := prefix48) (a := residue48) (b := 201802497) (n := 32)
    part48 (by decide +kernel) (by decide +kernel)
  rw [show prefix48 * 2 ^ (32 : Nat) + 201802497 = prefix49 from by decide +kernel] at result
  exact result

private def prefix50 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (32 : Nat))
private def residue50 : Nat := 0x78812cf9b0c2dd28782a346cb7c96a3705dcb80f0e853611ba1675f3c3f5c316aac79f99a80b70857f51ba37739cf432fb6f5be906654d064ca7282f19857277c977765af14f22b1b261b6c31e417c3f90c94bdf01506c93b13b8400b75f90214c23dbb0e053a73de234bf5aa8443ac869bff39a581fcd02b8e75d822898879418013bbd46df016bcc45c9ec879d0b503a4e2eab5513fb9b9ea7e6598e82315b4644a3be02e4081d5cd1772ac1fb324bc5a14e16ee76c181d9e5745eb99fb7b310ec6b5d7cc21859b9138347eca0c1e767ab5f8cf11524502cd7db61c65a82e8bb29ea6bf1fa72405a11f8c269d2f2b7684a19dd60d4ac8f0cf3553acbe57bc9
private theorem part50 : 2 ^ prefix50 % Spec.Ffdh.modp2048Prime = residue50 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue50)
    (e := prefix49) (a := residue49) (b := 3449012689) (n := 32)
    part49 (by decide +kernel) (by decide +kernel)
  rw [show prefix49 * 2 ^ (32 : Nat) + 3449012689 = prefix50 from by decide +kernel] at result
  exact result

private def prefix51 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (0 : Nat))
private def residue51 : Nat := 0xadb462de873d049a0302546994f3e85921526f7ffb6c51585e6bc7900476423f9357c70a0c1fdddddcf382fc6ca2056c6d19b4380a8b9ddc39a189112a2a60144d23d5b56f5a23e4c85f4e09352563e299ab1a784af4254083715273596caa4cb0a228e6635fb6d722da42611703f0eda361817d520cdb764fc2481aba31094b0af0a74aafaeaacffa5e45fb9089d58f75ad916265ba885bd77381d37dcc8ffae08e23af0f19fd44c96662bbeff8eb4af090b833c2583f5834954700681833b2725d80666623cc4e3cd7b33b3434661a486a54ef94f5665e406ae24ac0f2b480e46eb2b5854ea21dca92ada3a5e738607c9b396cdbad47aae2c56cbd09eb751c
private theorem part51 : 2 ^ prefix51 % Spec.Ffdh.modp2048Prime = residue51 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue51)
    (e := prefix50) (a := residue50) (b := 1979961671) (n := 32)
    part50 (by decide +kernel) (by decide +kernel)
  rw [show prefix50 * 2 ^ (32 : Nat) + 1979961671 = prefix51 from by decide +kernel] at result
  exact result

private def prefix52 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (96 : Nat))
private def residue52 : Nat := 0xd7228b3dfdee697c59a5d59c06e712b89534932cba5333efc77063df04388ac177fabcd3f95ee1402fefbae25cf6e1212f2e9b36365bff9faf4de23c97df637cf1ce6437bae21f908593ac9af56ea18d282e6076788516bcfbb64c2b5ef68844f337b26d55fceda6275ef76a376b5dd37b23151140003295c910db61d883bc37c7db1d29fc83614bf7a219e14fb4b47aad1a3d6cd515455921f472ca96816e33366dd5daeaa0cf09a83c8be14a8f6658e5f8aadc9638a686bd200455b598267a244ffeb56d198549e7084a27292c8c13f5ec69a2fbf48da30f663251c489ce3ca0f7c668ff783caff209cd51c7d4e5760a4c4786306e3df0f964011b8df214d6
private theorem part52 : 2 ^ prefix52 % Spec.Ffdh.modp2048Prime = residue52 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue52)
    (e := prefix51) (a := residue51) (b := 3672289016) (n := 32)
    part51 (by decide +kernel) (by decide +kernel)
  rw [show prefix51 * 2 ^ (32 : Nat) + 3672289016 = prefix52 from by decide +kernel] at result
  exact result

private def prefix53 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (64 : Nat))
private def residue53 : Nat := 0x92eb64cd5050256a406ab461df7cda0e3818e98de60201e51e99821cf6a73980f67bd99b3afa0f38d9ea2b449e3564e6f79cd9c32d5b08e5700fb00a18c953edd31a5d310b442a6f7d1c3dbdc50bd11525be61644be5a77913cb490279b5ae8316e137b8b578521180947c9271348c025be00201f8915f8526ac07b4f32d3c58c3a9dccd2b022e7133d5e46d5291985d350f8aa3c929ea4a29297b21d66debee92a5a78da480a0a95d57fbf344b5eb057eea1d4b130fc56ffa061df7b19020d457f2bdbe72fa91d33904475db2d28b4c6fb557124427a889cc6f73bf05cc8360ac677915f8a9f9b25c20e90a472f307cd1ad7e4189a2c4fa4db540be7d521028
private theorem part53 : 2 ^ prefix53 % Spec.Ffdh.modp2048Prime = residue53 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue53)
    (e := prefix52) (a := residue52) (b := 933636452) (n := 32)
    part52 (by decide +kernel) (by decide +kernel)
  rw [show prefix52 * 2 ^ (32 : Nat) + 933636452 = prefix53 from by decide +kernel] at result
  exact result

private def prefix54 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (32 : Nat))
private def residue54 : Nat := 0x73df2098c4171e46966d14ec6739da0dfcf9c34969b95f7c02e4d2e3d223b60d076ea79e54bbe60cbced16ac6b26823b6edbcb8468b991f1f769eb09ef80b542ab1acce7e91f5d8a227e5193b63ee0d378283f49c3fd169f40bdfc98d4fd391ae502fa7686073c71be5d1a4274cd281a38edb92ea1a1db4a20aa18272106fd9a7a0cdd8b477f047353fa28df511e9c30d3e794b0f818bc3c8576ff93b7bc389c332104527cde7c1cdde0db06d4bff5790eb05932536074107b6b488befa74f8a266ea63f65c0d50911f9d6a1cbafcbe6047b494f076a5d307b61b5d516f3aa9d813787a0b0bd742c7c17df53ed47ca952983d69ee9c36db966d2492db4e30d1c
private theorem part54 : 2 ^ prefix54 % Spec.Ffdh.modp2048Prime = residue54 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue54)
    (e := prefix53) (a := residue53) (b := 4011189755) (n := 32)
    part53 (by decide +kernel) (by decide +kernel)
  rw [show prefix53 * 2 ^ (32 : Nat) + 4011189755 = prefix54 from by decide +kernel] at result
  exact result

private def prefix55 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (0 : Nat))
private def residue55 : Nat := 0x16771c9d78799730ae49e22287d5a58a08359df50f8ea43be2752a03e8d94b3c96aca91fa4481b0f40cf01b375b2f5cfe7683c39ffb8f3fb557e60e09543ac1a760dc959551f532217747741e01410629c96f1f589bbc9eb76285acb03e381c76ac3d32f159656a3f3e16cbe24e62b927d979daeff1a578c8dfb5861d8c975c9d668959c3c850f11be025dd3088dcf2a276af2678f34530053400bb829628a744ca27ee28a813be672b73902433bb5668ec61eacfbef995af8ff6024fb19a1ed4435c96e943c56cc1cd89e0b215e730aa183bbc0ad62ec7513f4226a7445a14452b1ce0eb3c2a7b6f247ea82372b0e7889e4d540e0983e78a1126591a0dfb398
private theorem part55 : 2 ^ prefix55 % Spec.Ffdh.modp2048Prime = residue55 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue55)
    (e := prefix54) (a := residue54) (b := 1252789132) (n := 32)
    part54 (by decide +kernel) (by decide +kernel)
  rw [show prefix54 * 2 ^ (32 : Nat) + 1252789132 = prefix55 from by decide +kernel] at result
  exact result

private def prefix56 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (96 : Nat))
private def residue56 : Nat := 0xd8968484d836f0b47a08f1e3ffed1a7cfb60b94e6dae7f5850739e27c5d3837bce1c66f89d3ed4d2470caf48d2394f4740eb86150c0b258fc3a2d37380c53675b701f0db9c334d60a922561d23bddfff588a4be5bb9f6966f1f821a0dc387d800f5ae295182817b0bc0bfd13984d742d9ebaa128e8c40a4b3476ed5138ca1b2289db826a592bd2061a7397434f500ef1fec7d539f280a197fb27a713c276f3a5a83f6627f41952c4f07c55b5afbecfa53ccf01fbca8a37eedade839d7ead4d59b12385dfe0c53415a4a47ef65c24276b0599741de2ac9c1ab89bac5cbf0f8ce6649273543e62bfd51cfc5a35ed7d74f8c3083286ea73f48f1791cf2ab5d339f6
private theorem part56 : 2 ^ prefix56 % Spec.Ffdh.modp2048Prime = residue56 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue56)
    (e := prefix55) (a := residue55) (b := 483042494) (n := 32)
    part55 (by decide +kernel) (by decide +kernel)
  rw [show prefix55 * 2 ^ (32 : Nat) + 483042494 = prefix56 from by decide +kernel] at result
  exact result

private def prefix57 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (64 : Nat))
private def residue57 : Nat := 0xd77869bddec6f68ee2d0c8ee514152b7dac89f055e86ec2fc41dcb2b0e172ac09a9081cd0724de608e5d6bbb20cd1817aef453f2020abb45ce5bf0f4d4ef2483e26bc515a5dce10fcf752fd0713748983f3221ff515b272289cd93fb677d46a59f3cab3412d511fec8348856a5a70b17e0889ba3aea97d592f4f1888abaac05db7c62a74281f7572024d420c48a4f8db463a990d989a497970f88d5e812466b259abccc34a8ecb89b0bbc8bc4f291a91740657b12c4f282ff5cac949ab3a232652e0bfce409f7f79118f04cce7308f14e0e175a1b1d3255c982f56eb298e308218d92e377cc59ed56e7000f6315f6251797b222ef61cae52461561481c3deb1a
private theorem part57 : 2 ^ prefix57 % Spec.Ffdh.modp2048Prime = residue57 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue57)
    (e := prefix56) (a := residue56) (b := 1967830386) (n := 32)
    part56 (by decide +kernel) (by decide +kernel)
  rw [show prefix56 * 2 ^ (32 : Nat) + 1967830386 = prefix57 from by decide +kernel] at result
  exact result

private def prefix58 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (32 : Nat))
private def residue58 : Nat := 0x346e26c6bef01efdb7b4e1d470f64930a75f54238d240fc62cfcef4cf76766990a84e1dee00eb4a5f57ab759359edc799149b5c170a2d3395097f7d11e4fcee62132c889e8682b1ac0360a0d606b1ae4dbeae87205e5a03d0e5d5ba8b955f66ace9a15950040598a5f302b93da7d67e076efa1292382f5b4062934179b27296ad58be92861689e9849671c907efdc19f439105ec3996f6566440c632f4886ca5eeb1d49be7368278adacbc66b8bb5f43fa5da2f54a192b6c1aaab01e1d5f42d212e3afebb929bf85b33f6dbc83b5f62bf899a7958e8d5df8588c039860f1c4e91ff34c6eef5cf26431ce1dbea6cf818848143d4db35181ae8be8e770115b444f
private theorem part58 : 2 ^ prefix58 % Spec.Ffdh.modp2048Prime = residue58 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue58)
    (e := prefix57) (a := residue57) (b := 2330530572) (n := 32)
    part57 (by decide +kernel) (by decide +kernel)
  rw [show prefix57 * 2 ^ (32 : Nat) + 2330530572 = prefix58 from by decide +kernel] at result
  exact result

private def prefix59 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (0 : Nat))
private def residue59 : Nat := 0x6733fd2e54fda4a7a96c5eb2f6c2e723c387cc066cb28c77fc34aa10732a8b5f1e71f861669070f1577bee745413f6e9b112bd32cd63c88871438e66de1bc02f5fd93d1c3a436adac7ea57315e248ce3d80daedcb0ce3cf2d73e39b30b73da0fb6bcab39f13a89f0b8d905af3700d4ace4a71178c7ada75c769c51ff947a4073f7fe8fdbd441d191889940c9dac4fce5c74d673a119ab68f4fdb0925c56d9abd4d1bc5bed6f0c58907e80a2eace4a4b8561b7f0977f6f372cb202809db2438b8f8bb4dcee6b78c5c97aea05cb04a76df897cce320f913d34f809a589f866a0adfbb8f6cc46110907513fb3def3a8e324cfeeaf2cabfe2c126d0c414cc9466aea
private theorem part59 : 2 ^ prefix59 % Spec.Ffdh.modp2048Prime = residue59 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue59)
    (e := prefix58) (a := residue58) (b := 1283261064) (n := 32)
    part58 (by decide +kernel) (by decide +kernel)
  rw [show prefix58 * 2 ^ (32 : Nat) + 1283261064 = prefix59 from by decide +kernel] at result
  exact result

private def prefix60 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (96 : Nat))
private def residue60 : Nat := 0xa4d475727a3005418a98f23ffe4610c9d3c0e594f816e6506f62bbb21aad476567ea4c59c62f07c4bf2126e4b04eff8a9026f30c205d24dfeeb8c2e2c5a5a818eb8829997fd02330058b92717f3be0cd73c2841c7ae540e19f3ae51499a8b67f8b97f4d7d3121fab23867a673443e86a5a6127935ab252d3f6bad7bcf901c163f6f1fca938769790054e727f6cf562edc822f8996ff47c27a4d900cd13913614785b41fa739d94a1fa738e063c9284ed8e59d51bb264c634cddefc9d303349655720ff9986b5340fa3f1c23b62e5b6968cb736ffe1c678cd1231db674b79f3b9d493c03b7093d40754f9004d9b5544db7be4ab3e7f552cec38166e399863095e
private theorem part60 : 2 ^ prefix60 % Spec.Ffdh.modp2048Prime = residue60 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue60)
    (e := prefix59) (a := residue59) (b := 179914541) (n := 32)
    part59 (by decide +kernel) (by decide +kernel)
  rw [show prefix59 * 2 ^ (32 : Nat) + 179914541 = prefix60 from by decide +kernel] at result
  exact result

private def prefix61 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (64 : Nat))
private def residue61 : Nat := 0x8704c9a598ce86f396d31cf734afcf9f437cc3e272f9835733e65ec0454b24c8c63bea9c43652f72eac0e10066604174460c794ec96bf2a62b2111c8c2eba71da2997580d891d7110cf2febefcdd8d9010a161c527a957cedc3e39c4ab213c33d2042d35bbd59b697c5d7c21d37a859d6929b64dddfa91cbf57be5658f45f8e0cb3d24694e6767cbbee75a194318a8f306026ff7c2992fc1faa562e8d48ec9a32679304048ba38780998fadcb878bdf13e77cbe0bcb86bb040522a9e288aff5acdf6ececfb0e7d7af6867aa86664353e85200ee75cf9de1e61f1eb0a5d00d68e8b9f2a7f459f7eb10a9aa9b842918e01d9ad7dedf0b676c3b83c7df036a91871
private theorem part61 : 2 ^ prefix61 % Spec.Ffdh.modp2048Prime = residue61 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue61)
    (e := prefix60) (a := residue60) (b := 1163285812) (n := 32)
    part60 (by decide +kernel) (by decide +kernel)
  rw [show prefix60 * 2 ^ (32 : Nat) + 1163285812 = prefix61 from by decide +kernel] at result
  exact result

private def prefix62 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (32 : Nat))
private def residue62 : Nat := 0x2c319ea7fa9db8a23aea5a9a43bbe9af2c0ee13465db6dadfc449574c504be2355c624d31767ed9f91497285549b6c6521d8c41c3cb9f4c1aefd5bb338a6ae4c475da2747a41926aeb376362415ae2d6644b0a0fabbdd63b8c8bcb58570392e106d461adaeb97b9f38b1d0aaa1153d01862eb66a0bd5f19216d277e5b95c96c40cfa6ca9d198fc90b7ee514bc1795a3d680778ad4c2695f310aa856d097ead33aaca39880f64bfeeb724f42359221691804fe70fed8d6578ad19146e150626af039bc6cf584471b29ba53cfa05281bef4fa265bcdd01d3a805708c92b1292fda70e3a68ccaaa1a49e09840729840be9ed675f75846e00d4a9d6fc5e066c7a29b
private theorem part62 : 2 ^ prefix62 % Spec.Ffdh.modp2048Prime = residue62 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue62)
    (e := prefix61) (a := residue61) (b := 2147483647) (n := 32)
    part61 (by decide +kernel) (by decide +kernel)
  rw [show prefix61 * 2 ^ (32 : Nat) + 2147483647 = prefix62 from by decide +kernel] at result
  exact result

private def prefix63 : Nat := ((Spec.Ffdh.modp2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (0 : Nat))
private def residue63 : Nat := 0x1
private theorem part63 : 2 ^ prefix63 % Spec.Ffdh.modp2048Prime = residue63 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp2048Prime) (r := residue63)
    (e := prefix62) (a := residue62) (b := 4294967295) (n := 32)
    part62 (by decide +kernel) (by decide +kernel)
  rw [show prefix62 * 2 ^ (32 : Nat) + 4294967295 = prefix63 from by decide +kernel] at result
  exact result

theorem subgroup : 2 ^ ((Spec.Ffdh.modp2048Prime - 1) / 2) % Spec.Ffdh.modp2048Prime = 1 := by
  rw [show (Spec.Ffdh.modp2048Prime - 1) / 2 = prefix63 from by decide +kernel]
  exact part63

end VG.Proof.Ffdh.VettedValidation.Modp2048
