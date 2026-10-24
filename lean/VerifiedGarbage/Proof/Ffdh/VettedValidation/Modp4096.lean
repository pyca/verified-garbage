module

public import VerifiedGarbage.Spec.Ffdh.VettedGroups
public import VerifiedGarbage.Proof.Ffdh.VettedValidation.Power

/-! Kernel-checked binary-power certificate for the published modp4096 parameters.
Each small block checks its arithmetic; the shared append theorem composes the blocks. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation.Modp4096

open VG.Proof.Ffdh.VettedValidation

private theorem initial : 2 ^ (0 : Nat) % Spec.Ffdh.modp4096Prime = 1 := by decide +kernel

private def prefix0 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (31 : Nat) * 2 ^ (96 : Nat))
private def residue0 : Nat := 0x23bf5d4d1f3ecedd1e9238a12d243997d52e78e1641f40ca6b6a95a0103bd76b8855f74afacf3ac7f005ec372b6e1989fa35ee6632375c98c94a47e71f4877d054e7d52ed8ba0e8f546205c2f0c3672921f2d715c603ae61dffb22b185ab3e7f4c43cd401770e58eb76a5e2b44af72a112a52f4d9fbabe8f6903c2b54ae41983e7bf5256bcbf0de842a2bf113ced540c7fa14c20e0872f34a29e1e5655fb1efb56b6a7291f5acf0d322dae09d5640f18664c76f4276a974d627ec912fe986a29d969130171a8ed1149cf65b8d4470adaa3061a60442ca75527368473fcb23cbda14cfd1ff892959cdf558cd6608dad2ee212da5c1b37d59f37634cb7fd4f2bd1a3cf3049c5bdcdd2c7b5741a01c420c74f844d8a3e7097832ae231edda25903e05b83f5fdbf5099836da6faf5570e62b09474bc3b4dfc611d22f5a5830d5c6f9fbe3ad847eddf06b88a5bb070ed158c92f7c5324efe0a49daea2ea1142b45c4dba25c93ac068c3882e202c203afa3b009295c3ddbcc42d59bef3216417a6705a80c1bdbedd2f17bb03fd755b0c635527257457cd3551e86f7870c416cc476efcb36d567b0cfe5462c9b759ce8dd41747be2144ce4e01ecb89ddfa6a9c9f9730cc3dce60090b02e731a55167b3e3b533fbf82fdb7ec75a09e4008ede908b4eca0e54ef1ca5e42ca7f9d38bf9a6264da6fca98cc2520e30edbda33c7397f9dfe38
private theorem part0 : 2 ^ prefix0 % Spec.Ffdh.modp4096Prime = residue0 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue0)
    (e := 0) (a := 1) (b := 2147483647) (n := 31)
    initial (by decide +kernel) (by decide +kernel)
  rw [show 0 * 2 ^ (31 : Nat) + 2147483647 = prefix0 from by decide +kernel] at result
  exact result

private def prefix1 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (31 : Nat) * 2 ^ (64 : Nat))
private def residue1 : Nat := 0x7e7a8133b7fb0c2e90001d4d017ad51d3135105591e7d2f5a326fd8f71b251645dae2105eac5cf58c03aa7f4cfd10927891272ef6463efc398e49f1d10e3544964c0ee001b936b143c7dc303f2cd8a9fd009982bb374c222d1164dcb4c311ef7681f73022509914eff9e078aef0fc68ce1414cdb2834dc73a0205033ca058aa598407697528a89ee8c869edd0bf0c9c7ef7f4d67563219103caaf8215c1935c3a5be87a21c10e33a94e773c4b43d7dd95084310d8d5b22b23a8fdea3cec885b9eedce6f13fd049c57a97e9beaf6449465bfbe38dc8dd4d1648a7d156494e3e4765576191d53a201a01ee74587a4a1cbd04ee4726633294ba95f7187d43a63fdc25367cb041011bc8f2f5840ec226b9cf479b7a2c995cd4233037770ba905957940e8f08cb569567230502b53b40e85f40715e948936fadbeb7710d1ea0f1acdff69f4640c10466a4382a31fa305b4e92ceda3a34f671b074fa585bcf175deaf9421aab72fefe36495c2b6d35bfb06dd38035b0d14f3dbbbf82b717d5383f80374536e66ae94dbe3c7e25fc16617e8e1bd0efaba4d533b2107da44aea6496137a729a6e84486687637086854462f374c9e9d574b0eeef161179218e1954822d72194d1a7371a7e9298dd0d831aedea36c5e1b79232b0522cea3aaa8211d23cca05ce5f28bd802b22806bad4bdb44f91c771eb5848a0e4c8c89fd7dc025c98734f
private theorem part1 : 2 ^ prefix1 % Spec.Ffdh.modp4096Prime = residue1 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue1)
    (e := prefix0) (a := residue0) (b := 4294967295) (n := 32)
    part0 (by decide +kernel) (by decide +kernel)
  rw [show prefix0 * 2 ^ (32 : Nat) + 4294967295 = prefix1 from by decide +kernel] at result
  exact result

private def prefix2 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (31 : Nat) * 2 ^ (32 : Nat))
private def residue2 : Nat := 0x7c99668e4616863a666a6547a540e1a51b93197aabc30e54cd073c09e8d8aaa092fe02cab12c79cd9846358d408c09b1f4060772ad985374a356fa8f8dacde5f7ee1161162e2fe75489876d05e5bcc9d3a41d24baa5f70f8da731a42d2e4a79f4ee692160fd4968db9ba6b8b241254e25a822776263841ab5f095380b6b194db082f6da4abbb0b9c0a37fe964dc0b93065ad65d607684f259237276ef9a1770b5461195f5b35c0486240cf05b36bff91e3c052b58b7a6afdcf05c8cea2aa9a575cfd51939b028a663dad075db72ea5ffaa22af22eb1b09525b04a9b6423be299b985d3d5b06ce62cc4bee0b050288731cdf80398891687c1bb6127dfb5504f9244fe183b768434ef57e99caf7a1e2b897cf3722b608a2ac0d8ec9f08401d72c23836a689a5352188b248edd8bb3d1f40d8b23970445f8039694b850221af71cfe0b71df5bf5e72d729c8ebe5f6752ed62929955f07a9531636f9cdcf8627430605fe9a25eae9482320b298b5bd4a5f70f71e1fcee7b2cffeebe7ecf15eda37155fae4fd84784b1cf66d0c7abef22ad749e26153f0ef5966a033d128a2adafe82304846279d983d71425d26ba8d8deded3d8dbbf845964745656806eeec0b2490def7f4f63c730db2b5e4e39cab66b6b27a2fe3cc79a9e6f5146ecf643ae0f2d8676a62c46810c6f38abd9cc7e19bf52892205e80876da5016b7a0be93fd69109
private theorem part2 : 2 ^ prefix2 % Spec.Ffdh.modp4096Prime = residue2 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue2)
    (e := prefix1) (a := residue1) (b := 3834113361) (n := 32)
    part1 (by decide +kernel) (by decide +kernel)
  rw [show prefix1 * 2 ^ (32 : Nat) + 3834113361 = prefix2 from by decide +kernel] at result
  exact result

private def prefix3 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (31 : Nat) * 2 ^ (0 : Nat))
private def residue3 : Nat := 0xe7184bd3fc57742bb3c9167d4b3a7014b10711d8e2404e7988809d38fb7b9f7475b4341dc20464a0439c85c1b0bca1b08f3525383cc5c941622f402c39828655b1a821c77ce50690adf93e9cb21d291dfab9fedc48c9cd1dab5908ff5a7f466157bcc151207277906cf7c002c0db2f701cbb8293eb33e6d66067d6030e21e790835cea92b2391570a692c0f9c240ef08f34c0211b14613c7e8e197ca1a0fffe47b694bb4eb74251b0e9d18b93065a07a28ddef82e15e6c9823596613b2bb55b36d712ef76cfcc16c1193745e95db89c1bd9bdb7ac92bc3420e557a3a21425b20b1784a0e4173b505138f325247cc3fd5f3ee5ff7bd29e7e7ac4e57227cae92d792fc8ac86098187470267e07da940d3ea00bfc7d1488a67b418d3681183fd800d419743ca7ac89d007bfb95bb210ef9320d43b6996bfc03b3af194f8cb2bb4d99cf2e5d0d0e20bcf057b0b13f36c6155e0b0b340581095289f3c6525cfb082221c24f5d9b04a777e9359273472f32a0936ddee6fab48613a8832c02339c1a63cadf6454cd346ba594183e3e35ff893fedb3c2c272838173718bfb4d9f272a9fbb88790d74a397397681b94a8b4ac1f6b4ea0ffbbe54b4fd89800e75a9a863d42c377cf9ed5db4edbc979305461a80ea9e24782e5e721e26b3d599427cd1d894b05d839bc9ef8171ac27e0bee8034b5023f6e74a8966de3d35cafc730e99ad1fe
private theorem part3 : 2 ^ prefix3 % Spec.Ffdh.modp4096Prime = residue3 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue3)
    (e := prefix2) (a := residue2) (b := 280256794) (n := 32)
    part2 (by decide +kernel) (by decide +kernel)
  rw [show prefix2 * 2 ^ (32 : Nat) + 280256794 = prefix3 from by decide +kernel] at result
  exact result

private def prefix4 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (30 : Nat) * 2 ^ (96 : Nat))
private def residue4 : Nat := 0x13463a853cd3e3b802aeb137c8b636244fcd231187a9675480f3ea5771406744e2059122d4248237c250102d31338520c94e8787f9a77062b37ad276456bedb389d965a6570ab1d002dbeb256fec6145bcded84ec7191301d82172bcb97d7b54207d4f613459a62c58db58bb17c8462f220025ebd3e6e48525c79d67215423624239fdf7f2a2d66946e2e2ec96d17da6ed95ff0317ff15a85e8ad8e8d16fd197949d399cccfbc928054451c254fa853dd6476794acc6b8c52fa4c074a1d056d25eb7555d1fe7dd28d03012ddb976fbd5976f5c1adb33c75ac50d33c9d59fc55626ecfa37db4fa2b2814713dbdd7f98d4977a6a890e533ce5624c2fdca43525199291675e6fc388b3cf30d8d70cae9d40cd73fefeca718fd079829590535d4a52b4787ccfeed7d0a2df752968422758e1139a52268a3f31ca950ca82f213e07920a680dc90ba718d19da83b75519ee128afb5930a1a8a147a2621fcf2d819ac084edebaef0edf3fd51d16a2565c1cebe41b7a003d188ed0d01117e8a97c4540926b6d04dba1f99230d2226b19551ff31f1c8d9e98e94bdfd08f99261b2e0cefc061a92ec5ce31689c90e1a7428c7fcbe20edd231e3d59c403d1577d1d69379d092ac1eaf87f474715063508a9b639573e563a80d5ce89a10ada1af5e8533dff6a282e521d712cdfb2b68df23425ba4330682265b2517935438c449f816a84f545
private theorem part4 : 2 ^ prefix4 % Spec.Ffdh.modp4096Prime = residue4 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue4)
    (e := prefix3) (a := residue3) (b := 1650667845) (n := 32)
    part3 (by decide +kernel) (by decide +kernel)
  rw [show prefix3 * 2 ^ (32 : Nat) + 1650667845 = prefix4 from by decide +kernel] at result
  exact result

private def prefix5 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (30 : Nat) * 2 ^ (64 : Nat))
private def residue5 : Nat := 0xd4f4cec26df81d554ee01f36468b6f65cc0364dfe1cf546215f5c7f01a82afce88824f3f25f1753226c6f3a7be71525846e083245c7e105f2956ce6ecac03c0a8ed314bf5f6f5bca11b7e00bb6a6eaaa6f7cb38331a802706faaa778c5028dd620194cd6c598d96a5bcc488f063c0ff6ee82aac6a8d5ac51e31e2241f19f6579c418a0e8971cce06947568da3c72b90f78c28d35d603c4394b4b7fe1eb4e4c9242a667948b08066502aa61b18702409ee0a02e8e15a1d3e003c23a960f4a6567870a39634fe818aff6405c53df05f19211cc6d1c0a3a250036949675c59b321b568e13b8f72f00e6b3fc310277c15377c8f146357856e190f743adea75d55d49bab81deeecae899037b11c0dc42250d8300cce8b174458d88d4d8817f18a38feb5ac73828d0a6e126774b333978bd0b6b56cc03a735bbdc6c2fce5f576b3d622e6f239fd561b13f874af24b9d5cfc01d47b8d1495d6a829a29864136520f47ec28e4df05f1ae845036d372f51b788a9088637a83e06e5a166a2c73ea21156a1a9e2fa37973d899e42750ba4fa85e510100dca738602e94612117fbc99af6b9a780f0e7429f3c6ca0743c1ae36df42092ee3a2bd17c2479e6567c054c9e7c2b6166ff32287f90c4d34f559689b60b4900b8955bdc301c4a624b6dcf1383a6f2c00070c050ebccde25770b1339d992cbb114aad860533f1188da3b2f0762a2f1e6
private theorem part5 : 2 ^ prefix5 % Spec.Ffdh.modp4096Prime = residue5 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue5)
    (e := prefix4) (a := residue4) (b := 3228438120) (n := 32)
    part4 (by decide +kernel) (by decide +kernel)
  rw [show prefix4 * 2 ^ (32 : Nat) + 3228438120 = prefix5 from by decide +kernel] at result
  exact result

private def prefix6 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (30 : Nat) * 2 ^ (32 : Nat))
private def residue6 : Nat := 0x7712b89b74a68482d3c2b33f73843a87b1c635110badb6763fd8e9c41fe4d9b0a7b269a7343fae02208aca32cfd5a8ef0da3910bd310b09d840b777bfdf9488b1f3ef1817e24e3a26fa96c0dfd63f03e5c9162b33d076e9962d54468413ce92a7041fcba67618cc25d56610938d072b212210f804adbd2f46d6d6bacd8be2a5018cc1d52a2986ba0c2f6bc7d42a766992ce99b15e5cd1e90f0f2339e3ea90c0300ea5ffc7098a6b88752f4134be19e129944c25e14db0384dd8d99a7098a5138615a666a65c13c78bfa0fbf46cf8646980ec9d2a2ddcb3b4fe31754746fe5e70825f1e6c850bd2dbeab68c93f2736a3667261acb9fe132400692bfe8c7550c425a8de23051a33821aa21132e6be469d15ef431224b1a0de580b7d5a4ea97a74891f8a23c165311d63158995364004a66e02960b16cf95db95e1c2d34d5870b38b114457c537a4735b13c753ee5fcd369ee563355727d6bcd86bb919de98696b4981685c805095eae649e704d8eb9faf3c41b329222cb07534ffa1c1a192b71be2349bf897d31793c8b5fe0da653b0594f05c9273a080c691b7bbd1423369091e4a232b9601b9effbd2b390c8bd0d2616450d116387ebe3df4b3f90c4481dbfe67ab4c966d9b0e4c64207ff837ac3d9250d9a28225236090a871b7d02cfbc19ff47752e7e564b38d894e8337b865151dcb68f379b65c0296b62b2597e5448f3eb
private theorem part6 : 2 ^ prefix6 % Spec.Ffdh.modp4096Prime = residue6 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue6)
    (e := prefix5) (a := residue5) (b := 2491492100) (n := 32)
    part5 (by decide +kernel) (by decide +kernel)
  rw [show prefix5 * 2 ^ (32 : Nat) + 2491492100 = prefix6 from by decide +kernel] at result
  exact result

private def prefix7 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (30 : Nat) * 2 ^ (0 : Nat))
private def residue7 : Nat := 0x8688efe5def0c35e920cc05a7a22358816eba06d82f80c392d4c05c1f9f8132fc76683f4cc9876e4930020384d45fa3b05c5a3123a0549560e69e55145fdcde6c077b7532a383caad5283a9d9d52d4cc4743d5ffd045ab2213eee18f54eb6f9b91d06d2650dea638b52b0410dbcb1281d197b1308e881b1514b78f68082161d0cd805ce0d1203fb91759e0b55424550c2351d3782e721037404173a26e8bfc805510d4c3e4d2d3aa07e2987d0b8931d88dafdd8b40f7b190221c89fa20e2d6e4e92aedeaaef3329845632405e1cebb7a9d601ad8e5d691305a14064ee960e04d0f9d666f24d2df14149c9d446ac6548d3ba46c8b747f8c8f8bb6ef744065daf58ce641078a95bc50febf1cec4b9047fc7476483e6a8c7ffeaac8c237270156ad42ae365d8fac8769b5604ac11026464649371e6cae4907439b7c777cabe41a4ca92ea43c1049f8ba7ce3f7412c5e6590ada2cc4bcc6836db201779220c6ee412de8aa2425594043c55b51e5a403828ddfb0cc70bbd22a380e1f4a8f991de1d7c08208aae343c05d9b92e79694b82ff2d6f474468a0d01e905a194c1aa8827f4b3438a5e2bb361bfb2f531203cd36dc08f41c55855f8a3f7f6c0dd38f731edd62524928522a872f82bc1755a07769b4ab73524d2596d42650473ddb0ae97d8b1f6f0f65c8ae87b0f6edba142c66f1b8f5f20dff10311aa39a1fbac489ed483eb2
private theorem part7 : 2 ^ prefix7 % Spec.Ffdh.modp4096Prime = residue7 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue7)
    (e := prefix6) (a := residue6) (b := 1161029178) (n := 32)
    part6 (by decide +kernel) (by decide +kernel)
  rw [show prefix6 * 2 ^ (32 : Nat) + 1161029178 = prefix7 from by decide +kernel] at result
  exact result

private def prefix8 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (29 : Nat) * 2 ^ (96 : Nat))
private def residue8 : Nat := 0x9db76ef9dd82ea06c319248f8ce8778dc629870478c5d07ec4126d5d02ca91f09b3aba0ca7f9a6c86b62a97c21b682e59b78adc81f9565132a9dff4b1509bbcdd3b680e9a43da3657b29d7746734c0692c75ab039b2119220f06d2867cc7f3f657499618b8cad78209ead52af09372cc907f7c05a11c50d818934f23efb8957f4b399b7245b7cb02a2906a964cba2483cfdc344fb19c77646d2aa5b386ba0919d09920d388a2189d3a9bb37106ae2e41968aee204fb619beb6d7047979d08902f4a180a72bf98390b7744c97aa06dc0a558554be7ea51aa4047502d3802b5acd20df9e5c796d46f571565cb92fe4b5649170859d23b586a37bfbac5aa1bcf806032c7d450eac4f9a5e2a54938645b659149f881b0ae0dbc49b8d7b4b0edd628f7346b9afefc9502d159899bc2bdfed34b38538c14ae6372d7d2b580d1fb60a07b43b21e5f7a97f5f76b6bfa3e3296ffe13b4fd374d2e3ff69a3a4bce6e1948bd79ea5d4a18fcef5ea5491aba39e4e9aeffcf091cdf32066a70a4f621bce660923cf03d65ded039523658471aa1374a2eb12e61b63412c5646384d065dc7e2b34bdfb9e68f5ccebb9445238ab0dacc735cf9cbda458757f00ccc05abb1c1d5186f39c56e9ed0a47036b6f887637de452e103ef4be101e6df02685c72c789805737b596ac7247b2b9e9761a90bb557b73f18bc95275302f7a04bccd3d402442db8
private theorem part8 : 2 ^ prefix8 % Spec.Ffdh.modp4096Prime = residue8 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue8)
    (e := prefix7) (a := residue7) (b := 17162067) (n := 32)
    part7 (by decide +kernel) (by decide +kernel)
  rw [show prefix7 * 2 ^ (32 : Nat) + 17162067 = prefix8 from by decide +kernel] at result
  exact result

private def prefix9 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (29 : Nat) * 2 ^ (64 : Nat))
private def residue9 : Nat := 0xcc0f970b3b7151fe00481587642e596f1f47c9f9b4bff30036fdf0667d91b370411e7ecfad269a0db53731d55d406788142687c9976cba27371c50b3af1ae183ce810a18d53fa63cc2ec05e741ff8500c8a14509cf0f57dfba82fbd39ac2226978a2f2890b8eae2bc061b451684f2221841a53e93b6cc244d2889a5a6427948cbf0ae96f48a5a421bfc06afd60aa4c149ac074849407298f6ed9d3f2d36ae5027d08f5598467441e9ebd4cf91cc77043c2d494412d76e2412d737a3168b7dad5a2d3da1f12ac7163b1a883d09ba808ea1b10a36f9dde7514258c7b5df3df2b9a97757eff0f10742c028331c92e272aee614d465a27da4cad50b6c0f0b7ae6efa528e1a9359227a012eef05bc48489951315eebd310e1e97cbc89ebb17438da971fad7e15ada0b8fcb2c6246298bc2d6aa0df1b18769cc7059ab942b527e8afb92458e029c6fac9824400d895754fd6e7ab664a3c13175f47424ac5ea6370a6db29c603a4e042a55591a27b4ad1f52977a3c834e5a7dc5d173cd6277f7b069ec6617b8e29219d7188c85e05196e95be0487a84ddef4e47aeab1dc3e8e5969e8d79481661df2d12884dbf35821de1fb5088e2be324d3c94aa2b9a40ee8080a8351ab6cf7ac6280ff60f1ee800bd94b3e95052fa2c5a8f0ee3de31aad204105eef692cd0c765ba915fbebfc80f67e23b02c1986eeb66783d10060fe2fbfeeb2483c
private theorem part9 : 2 ^ prefix9 % Spec.Ffdh.modp4096Prime = residue9 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue9)
    (e := prefix8) (a := residue8) (b := 495570321) (n := 32)
    part8 (by decide +kernel) (by decide +kernel)
  rw [show prefix8 * 2 ^ (32 : Nat) + 495570321 = prefix9 from by decide +kernel] at result
  exact result

private def prefix10 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (29 : Nat) * 2 ^ (32 : Nat))
private def residue10 : Nat := 0x88584b81d2d876e6906626dd1be81c1a2f6150e1aa4a1c5ebf1f8ceca622b3e4812c180b9e635e6d071b98104e7baca925d5c7cf41082ef6ab34712fb43b4839759d546f7d7718ace2a5a438f73e3514c2656daf2798620de03e570cdb342a73ff177028e4af32d9142ea91f08eafbdeede413c980d380eeed9d3cd21e15a56d80829b2812baa5629832ce85b22828136aedab8572d04ec237623ab0f41e861fc5fe02111ab559f5a8fc46adf9e88f335e2a4e032f7a81dd325ed374835ff6c05880201bfc8038517747edb5d73605a0c4f5ac28725fbc0f8fa4670bc009e554d569c1f4c1c06fa552ee246b639cece8ad6531413b546310a3678442bccc849bcfdce95e14153bf3300b606bf2d48f53b46b8ccbc9a87c6ed0aadb06a934ab756ca4b3cae1f9f68c14339de654d464276deb779c9061ec218add2aceb2732eaf761754f25d130997066bd7cec150debe8c9fcd40519813171ccbf938773713e35d55c8eea0f3288c77c4014101dfb6440084f04fcbcf8ffed37e683824a3270d0ca4b4b45100ac54c8993183895d7cc2e47aebaa605e51f904a72a98f58a73f13528a1632299b533a2e54462bdd9c1cabd8b53557a23cf0818cbe9fe0b00ce61b779831c7b9187f3e4aea1316e8f03cdcb47deee059e68583c2011b668401e3ffeb6f361c3aacd16e7ed4118576945449788465f91205228d64e5f7579e37a63
private theorem part10 : 2 ^ prefix10 % Spec.Ffdh.modp4096Prime = residue10 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue10)
    (e := prefix9) (a := residue9) (b := 681903164) (n := 32)
    part9 (by decide +kernel) (by decide +kernel)
  rw [show prefix9 * 2 ^ (32 : Nat) + 681903164 = prefix10 from by decide +kernel] at result
  exact result

private def prefix11 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (29 : Nat) * 2 ^ (0 : Nat))
private def residue11 : Nat := 0x109f20eb65cadb82ddc2c6fb5ff8e099c2fdc1a08031b339efc8c0dc363ffaea72e484842d7a7402a7a70d3d5e9ad9ccaaa46c429dca5012def5c0b81c8f2070cad2b6d686fe16711acc1cb2bb7d8794900baedeeec41d0c0ce35f651d3c4e1f08fbc0e6aaba719f1ae21ef282ac0eb8a701f87be5e95ed1d05b58b030afe9e0262ca8ca3c1ac1b529eb1b48815b8c1d9b7ee764e93d8abd973d2fd7fb27eaa511a41c538a2d309846698efe88aad9dcbf3c1df91c6959f8e0fba51935c570faea1d71703a974217fe7fa227635d688ab2758d466d1a32395bc77057adce33a82e8ce9fd596a7c9e4bb29f29e68726a103004aa43d175aa6218fb8d6b938e6ad5ef803e4b834046ec0d44907e8a409529dbf0eb0cad93931fb0d6465c3df09ffb13894b7353e42753143a8ab5746e0df12c9335d901bcb5d869a39a10f21d1ff959098d1aa731c5737922e679684c73aa7e9083e28551a97bbbda4fd7766b7e3a883d5fecfe94aaa4673ff722d5fc2dccccb754606f089e77b9d9fda0f200496e77665afcfc37013813c8c1a0b44f2ab37b467d90b3680925e5a0966c84e2ec467f4b74b55b04eb74452cef52b09b50fcc6498fefd84369539761172b5d88095524443b79249db15c959a8fe5d178fe04786fc13a0db501109be7851fd128075ea121b78a1feb05836c298458dda12741121b5436d680a9f336b512aa52df365
private theorem part11 : 2 ^ prefix11 % Spec.Ffdh.modp4096Prime = residue11 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue11)
    (e := prefix10) (a := residue10) (b := 3340370542) (n := 32)
    part10 (by decide +kernel) (by decide +kernel)
  rw [show prefix10 * 2 ^ (32 : Nat) + 3340370542 = prefix11 from by decide +kernel] at result
  exact result

private def prefix12 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (28 : Nat) * 2 ^ (96 : Nat))
private def residue12 : Nat := 0xfe345c8689f0becd92f70ab5f10d0b4a146937b034925a56d8d6d910cf1879eed70d7b0a0d0fcd0b1ac5e6803598fe1413891e29265f499e1daec58989b4c09d04d819497447aa752857e76025aeba63a61a59ed102339996aad069f90b11c983e83d2852ed3b43e6675489d853aa247de9f7c69e5c4628b272b59c37252088601bcee12f67b5ddcc185a7f5b311b5992db9fc3228630275debc321ce3854378471f78761006db923fa022892dfe713aaae2f894d5ad8c9fbedec97d136d0880492e41c46aaffb5e7d16a6685c46013bf24a63ff381226bddae153efbe4ec934a8080666f6571df96917cebc5a3c3ba03a9d452cbc11c0fdeb6f324e0cd8babcc9dab3e8df6a098779331d4e3d67f84924e44fceea863f133975b37a358822b4ae9df14f995822c11dd719ba511ab23039df3ee98a6e2444a6139d7b91c0febae974ab2e2566c99bfe063d9c1ac0c2f0ab21b098e82f46d5f1ad66958fb23da115e9b5b563919d2698846539cc32667f0afc7f3bc54f65a9af73fa8ec28ec7c612038dfb7445cff9337e270b7372818cd5740f932f512762e11ac6718f23d94432ca3d1089d71713dae64287a833e67dcfb3cbd7d82a0a68c288932dbd9ecfa29fd57e00149b3c90734d0d1ce842c47b622b5e938104cd22cc46def7520f674d3573132047006ae82ca2df5e3f2a712123d8f34700ed05808a5783a384f3a1e8
private theorem part12 : 2 ^ prefix12 % Spec.Ffdh.modp4096Prime = residue12 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue12)
    (e := prefix11) (a := residue11) (b := 4157246681) (n := 32)
    part11 (by decide +kernel) (by decide +kernel)
  rw [show prefix11 * 2 ^ (32 : Nat) + 4157246681 = prefix12 from by decide +kernel] at result
  exact result

private def prefix13 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (28 : Nat) * 2 ^ (64 : Nat))
private def residue13 : Nat := 0xa46abb651530c1e5dfbf19f2181f513c47c527c1057cfd3ce1fd2d1814557f59fec8597689c95916dec6e010dad9593659b7c1789ddca4974f475be06e7326e34a9fb39841506859832d0ce722f171dc736bc976ee5fcb74073da3389703f3c9d80cb6dcfcfb13091cd209a74d39e3b43c7425c5cc4ce93aed7fe1d4afe4b6cd2fac60c804429b3ef8fcf6217d343392528f96c5a360c44040e1bd9c8bff310ddc88c96335dbb1d005b8fd35d5bec1b4317519c863b9d022fd74dee0d18e64375134f930e416cf2f1db4be1b770f88d0606753537b46d7b31568b4fbe9ce9a0e212c4f863a1da867ab7fd3d14e3934baca78fcb5c342eb27e56804c9a37250ed636fe1ce1f917ed8f4e29a227fa63ebd9ad6ca3fb2e4f96fea5bfec4b25aa4ef26168a4bbc0247453d17c22c11f25a2df01a0752e57f35c7d8d0741fc8d6766a33b2b24c9dd0ddf91d40fd5459c4a02c1b3e48bb6e018a1c3a541b5c99034331839228a1d17e983cb31df38b6e97afa58ce0c217c748be7a440ec32256c7609609a796d7d8cec476c3a0a28e9f17c847706dd658790e3ae654af7d322a637ba9a54fd9dcf63caeab64fc7e8a52563cace5a2f0b7eef9eb9bb939e1c17d96cf3a77fac249ba0c24a7ef5795c6d3831d2e3f31b34a49bebf8bcee2422560d3fff1ea27d9e340f0b8919339bfc82588fdf1d8ddf4ba4a0ad3aad0c7bef779e50361
private theorem part13 : 2 ^ prefix13 % Spec.Ffdh.modp4096Prime = residue13 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue13)
    (e := prefix12) (a := residue12) (b := 3869057421) (n := 32)
    part12 (by decide +kernel) (by decide +kernel)
  rw [show prefix12 * 2 ^ (32 : Nat) + 3869057421 = prefix13 from by decide +kernel] at result
  exact result

private def prefix14 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (28 : Nat) * 2 ^ (32 : Nat))
private def residue14 : Nat := 0xd9c4a9a4e471e06286fa1bed233552264e51e96c1e64c93a65d8c51b7cc26025939337bfa291fdf6acb6bce655887de700474200ea60a2b08bdc16f08e1987ec0ff55e6abdcacb5e6e405f19b7e7cce3638161c538e99a20cf37f3343cc6a252a03a4f0d10327f4cb9a929b7f1bbc7aa2821fa34776776012bdd0666b3267d88b4411b57a0c627b089a3beafeaa1dbccdd998934f99d1b1273fd604741b6edbc286672335d9ca184068b4ba72f4cc56d15f6ad62fd3edb8347daf66d903e4591e88519fafe74c19d9788060775943435fdb12ca0c9b43aa2d8dbce807c331a8d4b0b77fa77b5b9f73db4c7f617f952b9d57ae9a350ac9d85c9162da738f450cbcf5bb3d482f8778e0607ea6da6de33455ab3a8e9d37f5c8c63e8f8742ee6dcfef23433509e7ff3ac0609dcd66eee12c7aec8e759cd26a956450d14675c740a322ff680de1938bb29487ce8ea9b6ca1dd216790e491b33170995054bf8c99411eb8d19f0db4dc88a91d0c1013d0b3221e1c0aaf7cc7325722d6347672cfdf363dbe2125f1d8d6da1ad8f2aef7313d0679ee92e04ae1efdd436414306bce620a017eb37d3c23fa31ff24b80a659714e584ae1ada78501fe2faa44af4f93f01e50eb264d7b974bf54ea76d1497b30904ed75d394a9f460c42856f5db390fb00852441be81f3b81ec938f86d6d1910ec7076ef0ba64f69c6530f6018955cba93c314
private theorem part14 : 2 ^ prefix14 % Spec.Ffdh.modp4096Prime = residue14 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue14)
    (e := prefix13) (a := residue13) (b := 2551547190) (n := 32)
    part13 (by decide +kernel) (by decide +kernel)
  rw [show prefix13 * 2 ^ (32 : Nat) + 2551547190 = prefix14 from by decide +kernel] at result
  exact result

private def prefix15 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (28 : Nat) * 2 ^ (0 : Nat))
private def residue15 : Nat := 0x8e3081948ef7a7e06929adc42ac16f852b392096317016d108b1b15ec9ac70189b3a623ef03377ac761a440bd052a2e91d97d2fc35328d78d3b8e63733bab3d426fba8a5ea36be169fe883bb9ae84a6c49c4e550c5ae3f338f34403e1ab01562f1d75adfe6c5dd0a3dff74fa2ae9f7014a5e7c27e85030a07234cb7c0382ec48f2c1c2c664a691ab4be2b8b6090f5dfccdf44593fdecf4c842030b2d8722318673f09f856ec51c0d3011c53968c89d15f611704147964e636e77ce83412427e974ab15a144ff8520cdccf5b348f961de072e7caa6af3b2cce354deabd3df6c2f7c92cb59b6d1b937ce4b02a18c703e4a61871d9bb8052c231b7f7f2be33eb197cc0aed2503b8d3f6957a1fb1bb7f76d2a8a0d839c58489897d423937b1b185a1efb793550330462ce46bef7b7dbc90d7f3d2170d91d492aecd871e13d9040feac02da65f7eddf9765e8148e1f863ba50813c2caf17c0ed3005e5174aae4b2e6e5dbff5163c7ba9315f0bbb4f039c05032074d027191a9343ca23b1089e2ce4b6a5e83ea7a542cc2ee3e82ad26b34f63d8f3a31fd935924b7221002f7d111562d96d33dad94183fc5497528991427a586777435dec697d5014e167fb9a20fb16bde4d309b9881c692983f607b0e3d2b1468f1ec6479ad2af604560825ac84ad6a1c58b8431ab5ec20a61aad7f0be1b1bbd01804181b39f5bbcedee217ffb5c15f
private theorem part15 : 2 ^ prefix15 % Spec.Ffdh.modp4096Prime = residue15 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue15)
    (e := prefix14) (a := residue14) (b := 4180642331) (n := 32)
    part14 (by decide +kernel) (by decide +kernel)
  rw [show prefix14 * 2 ^ (32 : Nat) + 4180642331 = prefix15 from by decide +kernel] at result
  exact result

private def prefix16 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (27 : Nat) * 2 ^ (96 : Nat))
private def residue16 : Nat := 0x441612bbf7c660fbf00fe28be0390f99aa585a9500683eec22bdbdca62800d1ff387338c8fdb379ba99610b085e50ef8795a40e2e6bd96e57104ae079988c81c2623c333e4eb309bf01ae8c148f81dbf6e67e1c75341ed7a9462e27d6bbe483f5f3b1f43902f697cb8e51a6e4756ab50740823f15a8182fac2b9319ddb9e57bb0e17c6ea4869d36825cd3d8a01ff4b5ba05e611cee864468c6576444d00cb7a0483fce6875766526661279e2b6a157175eba2a8b619eabc297d22cf45d1f484850dc2b1a921089cea70b4a59b5963b9440a3eb1428605dfbe7a550b1241349ef19ce26682adbe2ebbd7318973809423c7d8e749e2f7e5a9341794fefdbd9ac11372f2b1620f69e7c8c808dacf451f76ce819ee1e0748031dedb7249c5d012ea2766a672cf8a80ed519c4c47b51f2af13ce9b662e59192867040570cd8685207c1d9cb9298d39340f67da31018c0343de360f62232c73344921ded8be3667266dcce0474f6c5bb76b83469122fde23e2ec893f7d168e5bb90f066973fe88653101911bde93d72f5cbf4898bfcd8dd20a482b2d1bf97db4a1709ddb113af2d9a062e2605ef7f157a5a56365c6bf585a9d5687b5603ef5fe6996c1c344737d3ca44b3b6365995265375c5a65895270471fbbecddf22bc3c1c3e039d9996abcfaafb3e81842e4992d4d57d5f723b031e06e88573442414168be5d707ac8a00a95c06
private theorem part16 : 2 ^ prefix16 % Spec.Ffdh.modp4096Prime = residue16 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue16)
    (e := prefix15) (a := residue15) (b := 2817563318) (n := 32)
    part15 (by decide +kernel) (by decide +kernel)
  rw [show prefix15 * 2 ^ (32 : Nat) + 2817563318 = prefix16 from by decide +kernel] at result
  exact result

private def prefix17 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (27 : Nat) * 2 ^ (64 : Nat))
private def residue17 : Nat := 0x3ba9368ccb92c1c70ea64b99055237701d8a5a06d98da8a13e1f522f265898d40910b516c340fe34585093cd20f4cebf85b33bfa9a81b1688bd5f592d3ed6373c2ce67a8897c0ba75a4fc291b50d2e0e6026ec45a34201aa5dc1d5aa412ce091f6759f8df4db7ad389a6d50a2a88d75acb269238f30cccc2d3f61a9fdd579b13ff04cdecb9db06fb937f0872c7df0d5489646903eebd8884d01199767e5ba754cffab4e38a5a0cf9c4a013ffcc0aece260ab17d0741a5247e65f0ba7a400a53b965e65ab2600a1d54c3f2547f30a9d926f4ac1f128790c34cefff49ef45358bbd6df6122392687d3e9ac339c72c9157c80415a236b4c53f57c706a945481fbe625ed1beaff64bec98fda8ce0acef1e65f644ffb1785ec1c43f27dbbe4d6e857c556817079ac451a45da1c5d80d86c883a1636309a23854f65f150dacb6633eeff5883e8de5fd736757f9a0e83400a25caba80bfabd70a9bcba28232fcc974464991d89313ded575ab34967cdfd2105931bd42a48c9080d7ea34a4fd8b6e0b4a602732c86c28754425dd78977c811059a3a202f4eab8fecefaa7258e206e2094bd25b37553de1abbbad8c7f224d99c05363b77d5d2d381c5324f287b3f37f9b73b8cf542211d0d39fc1c12a5089f9754756caa6feb0fb8e5517e25bbc6fd319daf3d7c76af6ff882fa45c55b7bdf5c631094f422a67b95354b7e7d585e4add666
private theorem part17 : 2 ^ prefix17 % Spec.Ffdh.modp4096Prime = residue17 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue17)
    (e := prefix16) (a := residue16) (b := 3064520994) (n := 32)
    part16 (by decide +kernel) (by decide +kernel)
  rw [show prefix16 * 2 ^ (32 : Nat) + 3064520994 = prefix17 from by decide +kernel] at result
  exact result

private def prefix18 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (27 : Nat) * 2 ^ (32 : Nat))
private def residue18 : Nat := 0xb915ca551f76a31fd4a0e404b5640022052ee4de61b4a2a95fdf26db19c4c63e6bf65ca009403360388e56b8c390f58211f45aa8456f0d0d1472d3581788a2039295074f96c6c74249ae2d3c318e2bdf0986a4c8695a1a18bb9853c03b0126177e2033d982bcd2d7b9e52cae334adb9634a989b88420c0efcd64f42c65591bbed2bc8d45edf57515e6ee1728da8389c09e683af27123f93da0c7ecf92594340a3a680e2dafd1ee29ab2bda43477fd4a5ac87139210c8304b3cd989898702f6205998c679f288b0c532442f78e0cc47d1fcc9645a5aeea46afe3c60920a52b510de54051c489b796fc7be1f0f4a30df98a88e3b190e662e67bfcf096ee7c2d82b9c274eecd021accfead3f92dcf835c6c28de3a9e4b94ef0896b6aaff5e74275346d7c2e1cfc0df5631748935f93efa53c939457d1a842991fe575de1b1ff394646e02b3bd3c1140beed54a2d93dc689d359e4922ed36d5b8dccb869fc041ffcbbb75c50760edb5cf5a8037a4756fc58e3a6d76085d355560836ac9edce326ba9fcbc78541c7f681cbc703c94f536bd0c6b2a7321871edffe29a660a9107518dc3be8dbe9242eb6df983c5b56aa06b8b480873b4b029cd7b1dd565ee11f0d386088959ec1b84cddabbfdc2211810a327c794d9a392bc1c2cda20ecbf540e7960969cef1fb52fd44dbb15be3200281c84f699bf2cf1ede89018fa7afdff5745bb2
private theorem part18 : 2 ^ prefix18 % Spec.Ffdh.modp4096Prime = residue18 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue18)
    (e := prefix17) (a := residue17) (b := 4064467643) (n := 32)
    part17 (by decide +kernel) (by decide +kernel)
  rw [show prefix17 * 2 ^ (32 : Nat) + 4064467643 = prefix18 from by decide +kernel] at result
  exact result

private def prefix19 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (27 : Nat) * 2 ^ (0 : Nat))
private def residue19 : Nat := 0x4b1e89d3b1ed718f0a74583668627aba5fb3f553521d620b06124ce16957db10c8c68633bac93a6537f9c9ff4aef92df39d3ac15f53d3e9a303d703346cf50fab0611a69f86d8256ad9c255cbb6fbc3bb3ee19cb7e7eaf6a8812d34064daeb862088cdda80e3fcf4ba4cd43bbc5211a17bf690c3ff5409fabe17d2c33d65bb5b088fcc0d01abbe43687a8eb1182ace8a70c4949b86badd249b3e1300d0ba490238b095f07b0bc024e03d4b4f5ed85b42e213c0ab9a2a6eaa14703c7a1c9a97a1603ccd17144d2b4792f46ec8cabb20f97ddf1db91ccb780c7684cdf2fb50d64a44573aa3071408eccea65e878c5a50bf2d3cc4e925327222795f6a07363d80c0ed919d2b14058348d5b6720c7fc2f00a9dc699455e94c37bbcb9bf77043daacb52887df449950317056c482c321a0178381ed98f00f69e1f9208cbc70cf8c6d20b5ebb8fcf74db4a60082bea8eaa85a237889f455899a2370ab89d656abfecb393e66509dc82e2daa552445c2e7989ad4977ea40a34f9405d9a9e0c726d22a91ea039410e224da6348e0655c03723f648f401458fd06da4afb28fb907568ae0fa55b463b0cfa82d1cfb125ced0cc352f8bf1f7146862740dfcc3c15cf970449a3ff80a73ff55d2dd613a807bbadc5fd62935d55548a5445f71c663f90189d77f16101343c6ed081c031ee82bd903c9e0e6f36856f3a4baacf2e45df077c5d821
private theorem part19 : 2 ^ prefix19 % Spec.Ffdh.modp4096Prime = residue19 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue19)
    (e := prefix18) (a := residue18) (b := 825180003) (n := 32)
    part18 (by decide +kernel) (by decide +kernel)
  rw [show prefix18 * 2 ^ (32 : Nat) + 825180003 = prefix19 from by decide +kernel] at result
  exact result

private def prefix20 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (26 : Nat) * 2 ^ (96 : Nat))
private def residue20 : Nat := 0xe6df528363d464c86214c02dc5d30e37887ac02b4652add55b7d91032fec5cf965ea1048495063ca0144ef52d329b275d4c9cf9ad2dd2377ab80799ff9fce93a92cb6776c66bc6476f480bf38c1f1c03b64d20403f7f8113227205d8bc9c72ee37b31015c5100d1f4cb02bcca0d68515143bfd165b50f1f8c25e5ede8d90d51a097939330fa5f9af471b06cc81a976fad574c5cc2deaba6b0f7f2a871f9ea7045a0f19956737f999c2525a9f6428852eb6645ba3fe6392f4188ed5985728410619a3e649cb4ebcc140a7f6eb9051fa53e828327c7e096d0b978703b778b31e2f7b9ab645250f7e6fd7a0b9d0249c0315d1990c397081e44b526a162900c5219cc94260b73be51925152b2a4ddd7e69022e2da4dde06731ab9c716a24ba4b8f6688a1451bdecf5f8040f9c495f73fb0e67559294063757ffe8f54a5f2e8686aaf2ff377e7a4951471aaa295e8356506869d40ee720a8909b7665d669c128bac3b0e8eceb51869a91b4eacc32c59849191466797ac7f18dea51182e2d1fd4dacb8fbe0fedfa121f9192a63336e7291f365475ad7ef4c6175dd505330dbee248591422fefe17bb41f7b81a897b8a38a08e64ea650b5567aa05f71c9c759068ce4ed75a280ba1592af96ef27c9c159e362ad2731bf6933917aa77a7f3ca36a4f284c589daaa6e1cf0ae7090e06145a26dd0c32b17b8beb16a11dc66f9fb39cf315f1
private theorem part20 : 2 ^ prefix20 % Spec.Ffdh.modp4096Prime = residue20 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue20)
    (e := prefix19) (a := residue19) (b := 2049319284) (n := 32)
    part19 (by decide +kernel) (by decide +kernel)
  rw [show prefix19 * 2 ^ (32 : Nat) + 2049319284 = prefix20 from by decide +kernel] at result
  exact result

private def prefix21 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (26 : Nat) * 2 ^ (64 : Nat))
private def residue21 : Nat := 0xb152df8a41a197fb38366e5a95c718f0d849b88fbc01f18f21d5171631c470d517cc7b10e39054b239fe6ee23349d340ef3611696c018a004153d8b8979b1cb15676a544c8ca38077888a5b289393aea00e7b470bb469997323816b0d5664250890cba25150ca6c29a4075415ce243125d6b3c049365919d6afc7a7e90f201852307edc345fa357b7dfa853631c36792dc11915d4ae79c900f56e0dd04529132f538b1ef47a081bb270a42142783806b76342af973c852e2a60007fdc3ebabd97d8ffcb584452214804c33ed76843229b52f81640ddacc69d27d5671ee2f79ca0a3c4ca42708832c95d1b94e738f7488f51692f5ae27688da96bf0b5537d853faa1ec8e68c6b97877a7d62fa040616402709f20f408875e4f81ed6081bf4d6d7b4766985812e898c10baf86c4568887c1b79eae50f405841ff7d60adab25cddb063ff3833545b7b0cbf6edf9de1d29569e2a873f67b9fcdcee68d8f6e1eaae2ce5da952ee928a413ca4afb00de9e9dc27646c5d85e8c461b77e3bf95f0a8ac8645630216ccff62999a1ce9e6035cacc3de9728ee2ac7b214a9ecfe91d6f02f7407b6ee80807cb17d252a9f407748c9d9553466d54fa62a9de0e0070e3dadef1a4bcf87a2f87105032ab4db9df90bcc188b9813d6051395b2805de61efa7696a051987a892b6c1e73b8bd13c21f9766e7394476b96eb74a3e2b773e372261fbbb
private theorem part21 : 2 ^ prefix21 % Spec.Ffdh.modp4096Prime = residue21 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue21)
    (e := prefix20) (a := residue20) (b := 3541825205) (n := 32)
    part20 (by decide +kernel) (by decide +kernel)
  rw [show prefix20 * 2 ^ (32 : Nat) + 3541825205 = prefix21 from by decide +kernel] at result
  exact result

private def prefix22 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (26 : Nat) * 2 ^ (32 : Nat))
private def residue22 : Nat := 0x26098d00bf26f8694d3c291fb0d762935711a0525d7f3fae2f8ad19dace27a9fa9415bb6aa00d4016440db937ea1a6e6eff628439e469c88ec0dd08bf5a65fbab3088784a1b049f035f35e0c60e9aa7ed7be88a099ed48c28c8100f2ba7d1d663c391b96fde9ebe64c54be7888ca11a4575b155fb4db3f744f436dbc77b5c73b300162fc6e2c07996ee9ab3cfcf1ed0fa36aa367806141666d3f98073318c51cc4c1f3dfd1021990d86092aadaa076f443344d86220b279bb80eb9cd44b915fb68f99ee7d5ec79c72b79cbfed1080d661ae900605e31630663f035933c6f3c93c596605293cffea1f8ac4149bc37ec784ef6598b38aac4d0c302db270188b1aeb05c4e6fef2f6cf87d0780e8a33530573202106fbf048dd332d6360b53bdeafbd09eb3834d1d9f396bf0af975e45b7ac086c5534bb0c9e50d216e6f362e237da5943369c108ff2373c493ea4f15ce59b2d5766bf75ea8acb5bca4f01e4e85705af47fbc8e278e93b986caa03be9ca4781fac8f11b48665a63d9131b83a8d38f596de5c0be56be267b9bec88b2dc60625256d12d26b2d14268c726badeb8c033d4f18a1e042e322434e663bc92c8cec8bcd1da2f1baa9a6faf25ed4b0944d9a6fdaf8d2724617534c4173e4d8b48dc0bb0e3f3f2f55ad9fc64159f9f807c2835755c0f181acc495067e49fb6ff44cfa1925a8a97879992b18b6ba7023dc8944e8
private theorem part22 : 2 ^ prefix22 % Spec.Ffdh.modp4096Prime = residue22 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue22)
    (e := prefix21) (a := residue21) (b := 2248126043) (n := 32)
    part21 (by decide +kernel) (by decide +kernel)
  rw [show prefix21 * 2 ^ (32 : Nat) + 2248126043 = prefix22 from by decide +kernel] at result
  exact result

private def prefix23 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (26 : Nat) * 2 ^ (0 : Nat))
private def residue23 : Nat := 0x8c6b9e2daa123f867c655ba722bfbd62239538516b060183431f752e67b5b2d584610727f1906dc772a80fd8777affcf2e016d30bbd354d4d8a66cb58be8d7901659e5d697b91284feebe273df7ac0ee12be6b21dbc0b803a99c89943b495efa57b8479a3fa986df1de033f35747ab2abb382e1a67c684ff7be544893f24b3069dda80f54872d1fabb37350ac621d235449bea1d90f8c83eb95e70e5ed89858bb8a9780fd04f0e0ff5b6e388cb6cf6e2d2f4416b9fbbe1282ea614528cdc327de6d7f9f686ba26349dcbdd36d4825e445bb7b5b268e4dbbaa004ded0cebe2e0003312ba6b8d20a96a62792de2dc222ce37550759f6f5f48ea27ad6048252867e0801a493bf51ddc00389e7d15e28d2546d9df29dfb1ee7a30b0ec855915527040e9ee69ca7ae6561ba4308ccdaf8b37b988ee02ba5d13a28c1fee1a8942c10a04bfa0cca379e76de737bfe4ac5900c9c7a7af3d64aa4286b3e6bd1705518312f6bb2cd661b0e4d4992c94a0778fa3bd461f9d9258d00c6d172353cf4d11d0dcf3f58c4ca40902bad8e61cf4a41800b7b26016363712062efb4095154e0fef6042efef71dbb4e79d2c4ab4502df04562c8030ff05a2a6f2496a81fddc23b61cdf9576911b1e6105bac4ea2f003331829a1100403eed6a88202789b98176c1c1d81a06c7a1d0d05d5865fcd4cd79eae0e248803579b5e7f75707b84499d2c2640a
private theorem part23 : 2 ^ prefix23 % Spec.Ffdh.modp4096Prime = residue23 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue23)
    (e := prefix22) (a := residue22) (b := 2047040502) (n := 32)
    part22 (by decide +kernel) (by decide +kernel)
  rw [show prefix22 * 2 ^ (32 : Nat) + 2047040502 = prefix23 from by decide +kernel] at result
  exact result

private def prefix24 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (25 : Nat) * 2 ^ (96 : Nat))
private def residue24 : Nat := 0x8396abb3a32013a1f6a1d0d0b07c8ab9f4ae5fa5aa6573eb0fa2401ef47eca04ce445cd98ad0feef236c105bcf878409b6f1bc473666fbe68162c9db58e75271dc64465c6c23539c29dc5a32c79a41e32f5ed1e691946daf17817cfd07add8411e6aec6639057f3a64962c5c709abd90c890703b90907816c996b17b93d14ccd1b718f37b4a600414cae2c6a263174e8054ef991a14bc0346c903cb889fe04bfec37bd9f81b8d0068647aab1f9ab8a1a3d474d37f0dbe9c1abe7d6cb9d251377baabc7c36665027a8b6f32ed15b8c8a41a6f9dadae8bc4cef691e2ff65b2e0d13ab13d071d4e1e9b683e8e49ee0b417b2bf066e48876fb0dbca054e75b8ec82c8b12589229a0dd0e5bb9fa727279525d956187f6000a1c2605b3fc189b7958690c28f7ccd9fa3ab5118f9a6830d5105d8749489aaac8b8e64650a53adf31900d5535592b6291e08e9164101350db16697ffae7dab32ea858d30f9c0997f013129fdb4ec69751f0af8149f4531950493379965911b90c1fef3bb7d092b2620be07bdf5c6d50542da46cc0901ea5f1f54d6f5c1fc6dd9e11fa4ff454e5698423e637d25ed3b3805dbf76d878330a4fa76911944556999626e32c90b5b2770896cac46605218c11e77ec5217dcf2fffa21a4b7cbc093ec7ef295c361e0cce924d89362f195722156d92be91b6af16c9b2162f56df1fe7450122664cad2ed228ee7e
private theorem part24 : 2 ^ prefix24 % Spec.Ffdh.modp4096Prime = residue24 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue24)
    (e := prefix23) (a := residue23) (b := 4145821181) (n := 32)
    part23 (by decide +kernel) (by decide +kernel)
  rw [show prefix23 * 2 ^ (32 : Nat) + 4145821181 = prefix24 from by decide +kernel] at result
  exact result

private def prefix25 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (25 : Nat) * 2 ^ (64 : Nat))
private def residue25 : Nat := 0x64fce727682301291300cf06e1fc6b11c38d57bb58c45b6fd886c6515444b9db03e14962eca8b977e96564850a6ab69ebe8f7c99eb00c0431351f666534159173b5a942104eafc6b2fca0c2eb1634dbe90ec82011011608c7fcffc289d4b37e5da4c517aba2c10a7fcf9423185cceb55602cd2c545845c40f9c1015857ae3fcbcda09934db3efeeff9faf56b98526719e89d038b6c5af41fa41370587d69cb3e9be7fa33f4178745b502c631c7bf648ce46b529c39a24523731096e2ebf5d33e4e9384735143d62ada7e2986d19c8da977ff8c89987b2a00e5df2ce8b874496f3737705250976d05230a6a4662df3671e8350ec65c1d5e45b027ab51a0fc35005db40aa55f4ab10781a0f15d00240813e4ef717e12b1ad924173544af8ea84f2b6c6422404b5235325fa9e9222eb73a24fd7056e70f5b25699ab12917ad1145eeaab1e6e71aded0d60914b72a2baaae2b9d47b850849f49505c740e2e01317c4603917888242a7c94c3ac26ded9fee4aba6d830d9602097472bcf359b933c5cd0153857ed376195ff509cf919845568c12cbf5b8cc7452914772628d216363abd1d061c79257c7a1c3341adb10858307b41bdbf97a52063e93d1d271aec64999e1215c4cf91ceceed1c4833b58eb99814297501309f592b6b1e7baafb5e0e73dba20e20c643e357d27236900f9794356d0d78261b2247b37170de6dc7c1a2825
private theorem part25 : 2 ^ prefix25 % Spec.Ffdh.modp4096Prime = residue25 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue25)
    (e := prefix24) (a := residue24) (b := 2906968018) (n := 32)
    part24 (by decide +kernel) (by decide +kernel)
  rw [show prefix24 * 2 ^ (32 : Nat) + 2906968018 = prefix25 from by decide +kernel] at result
  exact result

private def prefix26 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (25 : Nat) * 2 ^ (32 : Nat))
private def residue26 : Nat := 0x3a2db7ae5b255499689a2d0e076bf813f0cd3292c9a470139ecb1d7497f5cad8379da10f5c37c2205c37eddcf1c3ebc3fd9168f1cd56944587f99032ced16abffc8377826f5678ccc4ccd1e555c5d689d993ba0971221a88c0c2cdea8a516557338009f2e5d0219bea0eb5c81329371a05b4288a5a92fd802c11d1bdf0dcc746816c723eb9c9996c755845009a8766468787111b084225af564186033b495151a5725c8a947d2424356f3fb85455a11eced5c7cb4e12668fcabcd783cba95f1b0a81ce45924f3019d77b30d7dede4a876b79faac209164fc4cc335902bfda660e55c5c58cbb7e057d59be4fde8e20c3e755a12c6851ae0464259ee280d2d663cf39d8fc3259721c318b97c8f2882dcf2a102b0681f08f8756dea88e62c9e8c0da18e6f4e80ef9979c0fe5c32b579f019ce79fcc3a99d87d3cf6817d67f34a0f26e54ef5992ce93b5c767c538b847bf8ac0e1956450e1e9cc43699fa9e3da1f1e694bdb4b30dbc4ff5fa850b39ab867eed6eb532fefdad707280326ec85d8d710370f7305337bcb2db334270fd43b998122a59b8063abb1f56ea65f508c4e66bc9d6161e29df7f3e2a98e974fff0cf37fc8a4c3a2dfdff6268b91d8c59147bed001d72958ab63df1c31178ef4d0ad25f1553ca7e69dbc8097296098ef0b9a7e25fd36edbf75e8f829a0f8ad74820ae6cd6126f2e5f80dc00016047ed3dbe9a12a
private theorem part26 : 2 ^ prefix26 % Spec.Ffdh.modp4096Prime = residue26 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue26)
    (e := prefix25) (a := residue25) (b := 3612316168) (n := 32)
    part25 (by decide +kernel) (by decide +kernel)
  rw [show prefix25 * 2 ^ (32 : Nat) + 3612316168 = prefix26 from by decide +kernel] at result
  exact result

private def prefix27 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (25 : Nat) * 2 ^ (0 : Nat))
private def residue27 : Nat := 0xdee217f6d0bead0bbb4f5f4d6bfa9d13a2d9d7b8a55ac31b5a1dacbde7136d6220f709688644e00d0e8f3763d3bb94bef0b6bfc073bb4e042c4183b5bac7f6ae016c33fda57bb592083cf37bad9146dc277f1b971e32a51cf2908bdf3e9ca4b509a1d6963c13fc650008378dec324865de7753849d10457341a86c2ff474148c53d2fe31cf889d2890be276a5e89e13099bfa88e2091f57a43743c2c1ee478e1859c48f01b659187ad17e25c76f12473643bd8a4be93fd7fb5228965606231dd6478b9687e04fa2ba4bf13c9dced3260dfa7877e5a2659e16512517ac57dd026ecb0a9d027dc38430818f766f1a229577259de748981964da89a4329939100c1a9b64050cb76439cd4216ffb4be82664aebd2272a99c258a1e5849c4df242ec5b920a57a670a0bdd805414c4c9e550ee49ddf98c2fe934c96e47e188b4c4bba3193e3911fd01d21f273d133c1266c2d4e0ef8937bc9147a9c586779c6b866e7dae72d3f4669eb2abe1ac05c46f497aeba36a97cd0abda2ccfb02636c3e89dc74ef5eea99a1d44951a2fb4e991b0608296eac7b829001d7f9afa837fee8e16c159fdfa25e1f205c84e3816c9db74901824454f45423b31c123beea50e35c7cd4a81e6ea6006873cd40e27ec3cbf1b4e6326a1f8419143f8c97e58feb626e3eec2073801b95f74ee523156bae518a74299d9a7eacacba41baf68accb56b9ae51cb
private theorem part27 : 2 ^ prefix27 % Spec.Ffdh.modp4096Prime = residue27 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue27)
    (e := prefix26) (a := residue26) (b := 3190132723) (n := 32)
    part26 (by decide +kernel) (by decide +kernel)
  rw [show prefix26 * 2 ^ (32 : Nat) + 3190132723 = prefix27 from by decide +kernel] at result
  exact result

private def prefix28 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (24 : Nat) * 2 ^ (96 : Nat))
private def residue28 : Nat := 0xf3c54b8df6f4924be2c5cf22a1c55a11c0b9385a82d979022aed2be684596b0afc8eaa66df702fb11b7f60b183ca978233cf449a9874e8be2ef3a535196ec69074d30d4c5723eb345c319539eb5d8c80e4d0978161e3cf0380a4b596fc7d708f9c7ed7b2f10192faf41e10a954fe307c28d5bb9c91fbaaae28acff7e54177f6cb903561c3cfab613d697a867735a5295ca2a788adcbedd1a5af484e9b44a8be7a216c6cdb262a2bae2133c25f2cea040afd9211d4a422b3820ea9553d3590ee674f85a7626f10489e281cf74c3a6431fa6ca86b5490cbf32669cac1202fe4fdb96da668e75d865e65c1db7a0c80b2ed7184800d83c990baa9e21bf5600c3a3848aa9d5e35e86c1bd9079bc023b6faffe50a6fdad67da15952a9a417f6b1e6f438dd11ef73038c3df827d4b85e7a8d1cc92b888602563737c5eeb69ff8e66b20917a6490ea26a9d76170bd3d3271f98f1ac1b7d224fa9006699b0a7ae0e31c21d9e313ff8032a29ac2cda9afbe143a64f752090e71f8150bb25bf3dcc9da6690bd1f7e2f9821cee68742ce3151c6d2cf921b99566a54106d19f12ec91df969c94136bad763ff3cefdb00355071533f07f8a559740d8a97e970ac80c1838cde851a5555a378dba81677d8782025bdb1095b4283718d29d2bee74885f50c8973eeddb8249967e8fffdce9e2d4aab5bd34d73325a841a8c005e52ffc919a3e1f0543
private theorem part28 : 2 ^ prefix28 % Spec.Ffdh.modp4096Prime = residue28 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue28)
    (e := prefix27) (a := residue27) (b := 613692200) (n := 32)
    part27 (by decide +kernel) (by decide +kernel)
  rw [show prefix27 * 2 ^ (32 : Nat) + 613692200 = prefix28 from by decide +kernel] at result
  exact result

private def prefix29 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (24 : Nat) * 2 ^ (64 : Nat))
private def residue29 : Nat := 0x2340e7837a9e71fe0e7c0e43ea9fafa8e345633e60cc84173e3cf7394f25bb242e376f7f6959c1e1ee3a8b68ca0a90decf9a27927ee03ba1da23b6ed021e774361e3d2012faa6a14f2b457b3415bf890ed3eadf6f31d961c4654fcf4b725423e72dbd65d6b8974d1b7f586287e325977581d0f4e1dc048d7ec674ec9af97a42cebb2efec83362d414b1fa443a87ab811111cf099bb271c1b48f9e382e1dc9a62838509c5b6052a5d5bb5efef302f2a52d3e2d1558141c7d8c2abb730217714fb31ab602f99f46212ada21fa27c163eb10e75cd6f5f4ca92daa0f9d0af213c84ea8c9b525d9abdeb7f6c1b3fe112d0c11fef3e0b3d879a57cf4c22cbb8a52a1b21e4710d7208cc45c5d8e502444ed22bdd99d4c9e60c3c4c82fcb408b182ea3fdcaa3c4c9476c82fb091156999da6db14aae5f48db7b673fb4ae158dd3a5f6d71aa532540ec7b625acd02b85019b41accd7ffc3bc430e57f93fb5c48f55938d403b00c93eaff3e2727b90cc74d05d66a0c2eceb3acc1163d1b79742a9c8fc8bfc4d9081b74850fde34e5b034dd8bff9d8070521d67809f14bba8c7906d72cc6b8e29a300f4bc49a4c3583533ad6400e1a005f95f1b52ab43337ec4e2934bd7fe2eacc65143ef5e5c411de70e91c88c53c0c320f5a64cdd3aaf2329b6ee73c19de7350db89a2388efafba864b2d190af52f3341372a93fb26b9e720787ad9de61d
private theorem part29 : 2 ^ prefix29 % Spec.Ffdh.modp4096Prime = residue29 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue29)
    (e := prefix28) (a := residue28) (b := 4134677918) (n := 32)
    part28 (by decide +kernel) (by decide +kernel)
  rw [show prefix28 * 2 ^ (32 : Nat) + 4134677918 = prefix29 from by decide +kernel] at result
  exact result

private def prefix30 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (24 : Nat) * 2 ^ (32 : Nat))
private def residue30 : Nat := 0x1b922174e0867daabe4252c098829780abc88b4022c4adfcfc1262d8fe56201f4be156d2f6525ddc387ecbdf74164ba5a77773bca825ec1d57a4e4be914095d88c040c3a7c0984f2a9ae4be0f00cc33deff724774229b8667de97728b34dd89aafb9741757c407c1de6be3eae3f1e50db2028d091e68614da116b009076dbf8906b9408a48b0ea16d1685e3ccb984de1283c99f208d68205adab98edf06700dd8f20b06d44ceb73becb2148071444eb48e6de5edca1e2458e33d3d065a3a4ae5ee250cfa2b24c930b7b35b0e04cf9ff64003305234693344de3b2c072d47e5b995f60033f5fd03bec740954f8045be490bb64421083cab19ba642bc00e59f24d6226d37cc584b98310287c40454b71471df3d9469619f0c72be22e33b6056aae617725f3f0022adcde72c4b1d70a63d5b9d7372766b6879309fda89d1eed5c1686c0b03f5f362d1f60f3dacae630d0c48d6378550e90c0656ffe371804cba4326aee0a76d59c8637be110a816185aec98ab391cd9d4f88fee2d5042d95cc56d26822ceffd7eb7be644939f056694d53b975ab2ec3c2d1ee07007551cc9f403454cbaf71b05a1ee72187c92f5d14fdeafe660265df0fb1bc1d2a6fe5805f9ef4569c2559132abf06d0fdde03853af51671fdae591aa68ff0c2a9b81fcf804f043d92d985673da3377ddd9f7316a6a76a50a80e965f1079e8f5fd3281ab032b2ea
private theorem part30 : 2 ^ prefix30 % Spec.Ffdh.modp4096Prime = residue30 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue30)
    (e := prefix29) (a := residue29) (b := 3774889564) (n := 32)
    part29 (by decide +kernel) (by decide +kernel)
  rw [show prefix29 * 2 ^ (32 : Nat) + 3774889564 = prefix30 from by decide +kernel] at result
  exact result

private def prefix31 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (24 : Nat) * 2 ^ (0 : Nat))
private def residue31 : Nat := 0x6ef8c8fecb1254011494b7b5d11a033ae443a0a4d28692a23a3001d73240cb0990eb22a45ea95bc8ced3c9605135b1c10a40b71eeca769f13792a7cb9d381aaf2a5e1e3308dc54698b5e8289c1aa10d95996c046696cf8c96ddd250da96859986f463ef13442619fb882dfd37598460fc2ed049bf76825c90e48a967cec7e5cc819a675e1ae50920e0d25ea571cb39bad522df01f6346e6f755f0d79a2ba7765d0f3a06f6925888d570e81de794233d7792b03cec2e50b2645d281c780c2848b27da634abffb873a3600e7a60be39177cf25fdd5b45434d80cc304e4c3be1c800e7a7fad13f5cb4c4209bb38e4e5f7fac60e8ce83de5c04e227a76066392e897015981ccd05b891155d2a0f286a950f4e744ca66b182a668b13a5661036269a21052b3512818090a191d363a9d314b9f05dc18b7a06539d8089b67640518a2174bc5f7ef39efe91ed037021f55d47372dd80cdd72073a03ba4cc4029b3b352f4fd9f632a667a1ab125d468907b7832774ea107efe51746efbff05fb7764a95a5ea50df3503531bfa4fca3d492f74c3cb4ea9238897bb37be90139f5a835255f487ab01036adf0c4d620a68ef30b1593766e236892cc39208153a5ab38579bd306acd81b7f1b08df3f43bae1d242cbaededde08fb15d6977b7da7c6b79c9100250ea1f41ddbf05d15dedc8f94752614d2aee67f03c45de5d301d295af5c28fbfd
private theorem part31 : 2 ^ prefix31 % Spec.Ffdh.modp4096Prime = residue31 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue31)
    (e := prefix30) (a := residue30) (b := 1353834370) (n := 32)
    part30 (by decide +kernel) (by decide +kernel)
  rw [show prefix30 * 2 ^ (32 : Nat) + 1353834370 = prefix31 from by decide +kernel] at result
  exact result

private def prefix32 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (23 : Nat) * 2 ^ (96 : Nat))
private def residue32 : Nat := 0xd467117598b70a43d40884b6f174344d705a95ec70609c9b3b25e1bfddcdb91945df8d8dfe3b4b7593665adcdf9f758e9466b007fc4445f2fadf4ebc68f3b0e17c35c80bf79e6b9e1af1d5aef341ab889f1fc029febf6e9bcc700fddf6520143696c44442cb274546526740941aae9ed7013cda669a77fccb4fbf221c339aa77af1830ced87d4739d0440b04b7917d312c76af049df6b5e092c9b6e6c5e020d0abef2e306b36cd69937cedcc980e9defb4e8fb91a164477e4b9e6dbb136efcc6de83cd63195729b0b39f92af1dd7cd0a0eecabed4bcd7e4843f31f2ae4339fbe41d937bd910f003748bc55e484fef9f40d3b1d46a7981c781c10014cbf27fef8baa8328882126f6bcbebecf50e37cf5f47dcd9214bacb3391156f78d3f22d101bb716bbf96a641d2f512adc593cf760fdee4cf668700bfdf4ea1d3228b48cd12c117b27920f4fffe2b37fcae8ebbe1d124586bf5712b215a096923eb6e35f50aa1cc9e293f50c5121ad32ec4481ae88be7480f2e559550c9ce6ec74dcc5ea7d1fae56c61e3e4fdbc02e55bd78a6c50b98158549226b629a7b54bf7c6e54217b1e2270488f0ef48d2061e975394e92c1305c6d322d4b334f7aaea935577955235a6503a0000cdc67b55af7bcbeb90c78b3ed86e492569056b87f9b9ff88f546889469471bd4e88c8f7ff7d65f703a8288eddabb3504293abf36fb273b9ebc6e5d
private theorem part32 : 2 ^ prefix32 % Spec.Ffdh.modp4096Prime = residue32 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue32)
    (e := prefix31) (a := residue31) (b := 3429704731) (n := 32)
    part31 (by decide +kernel) (by decide +kernel)
  rw [show prefix31 * 2 ^ (32 : Nat) + 3429704731 = prefix32 from by decide +kernel] at result
  exact result

private def prefix33 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (23 : Nat) * 2 ^ (64 : Nat))
private def residue33 : Nat := 0xb47fe19be49ceb6cf7845c57c3569729530f074f886f66d2c8b76ec3d802ebb8b428a302c1fff401531e9d81ffd2e4640a0c52d2d42e347b21834e767ab11c89f4844eda1d5d18a3cd2607f8c14e7e9a062555621665e9e8213fe63a0933dd777e075290824d232f51a566cd70c1fc5832f6c9f74967166a4200a19d555ed00692dfb34977c61a7f8e439a94168da5094a60d276ac7a287346ae2cc8abb1e9e05cf5b77e1324a0b6289550d399a2ee2d2869093a72d2dc01412ad589e5e0ff654aa51f6b05b5ab92af4ffb1f7afeb6b2c3c43346584bc7c4863b9861ed6d9b7d48e6c3c938e5e202c4afb0f33bd6eb7f6a961e01961c9913bb7d3de328ec1b4cc2fdcd2d17af31c2806be96f0153741c226dc9606ed69f61aaa847e386a377caf57400a2653f2fbace37d7ff38e2f17329cb98193de06022027690023996933dab80706fb90c106c2c6dac078d3a6bb2eb3fc611cd01fb46fabb64008ee59ff27e0c53bc6c88de25f50808cd1eee22d372c7f2de186c3c63c7acaa1023966493936eb3e16321f0d4de2aa4e5c8c16ef61af057616f2afb6277beb4dae016440f87124aeacc4bf98acac84216a945745ea00ae7854a6030e29d33fba5430c9b26452816f50f3b85d3300c3cfbadead92cdef6ecde868013051a460affafd8379720b6b4c6178eaa624bca8ed6f764bcaf8d591dc77474c2aaf78b189b63e2521f
private theorem part33 : 2 ^ prefix33 % Spec.Ffdh.modp4096Prime = residue33 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue33)
    (e := prefix32) (a := residue32) (b := 237693389) (n := 32)
    part32 (by decide +kernel) (by decide +kernel)
  rw [show prefix32 * 2 ^ (32 : Nat) + 237693389 = prefix33 from by decide +kernel] at result
  exact result

private def prefix34 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (23 : Nat) * 2 ^ (32 : Nat))
private def residue34 : Nat := 0x4c327dff88dccd94084d66bf51d31d13a4e0eb50673cbbec43f541597071cdac1c6ee482fe7029420dc3dca46adcffdd35279b656451a57a230ecc3e48a71eb31ba35d93830ac53047642dc036a5867c8c95b0c625e685fa814cb8db272508cfa3d5f1a239aee69de112740b2b2a44a76db530023e83bbf182c460b2bca1716c87780fd47e2820f9d8d663970fb82c4ac1721cd5df194de6d90ba335c14d0f193ec67192f8afec3ef19c4464ac45f82e04d48a4e9839397b9342a3dd668b1dbc63c97c319f2b2a247c2948f5e22961456e16dbdd9a773050de7d9b3ea0d0f616f8ae0689a926d9db10d4721cef4d17563b285fa1238d38e822d898a8f6334ad95db3b2951002d79f554d5cd77a0ab3cdebe2219eec24a18fd8dcb40fbaeeb07bdcf6ddf061959eba0d6415a7e9f017544f905e70741a142c0b6de1a0dd1848561f4f1f45cdc136b3b61afe6285a5db44eb6a1318636fdab3215c4a9a278119ad589bc5f18d0b5067c0ee5bfd330c8f366ff824b08f1b05d93b5679364588c910a59c103a552efe65236a2fec8918775d89b74c30238e0bba54a4aa3e2fa05f7b7f2ec4f3bc5af1abeff83d2b324051bebbb3b45181a6841372938d81072ecd19ea50d6aed80d73209b64e710144bbaff87914417e716a965e1e602d676ff6645f78c8598d36d3f1d586fd84fde8a97255a3a79a324727742a65c096d8a3ac67f
private theorem part34 : 2 ^ prefix34 % Spec.Ffdh.modp4096Prime = residue34 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue34)
    (e := prefix33) (a := residue33) (b := 881532884) (n := 32)
    part33 (by decide +kernel) (by decide +kernel)
  rw [show prefix33 * 2 ^ (32 : Nat) + 881532884 = prefix34 from by decide +kernel] at result
  exact result

private def prefix35 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (23 : Nat) * 2 ^ (0 : Nat))
private def residue35 : Nat := 0x74bb52979013cd9e653591772a5d5cb4b681b438598830444b6642dd25aea35b4cbcb503a4a247f66ad11f9139a8c159922c8fbfe75c62cb96c70433dd1b7f14fec98a355ae1d1d3ff509101576f117deb818bc94652bbcc42d6ad64f76438a6ca9a8f57f13f87620388ace0ee89975fa24e2f144ab76ff0e0d2260485a8d4c76a7e4310b596c01ee0b5fc69b4387a56557cf95bfbb94c9c1aa67bb509dadae6b0cd839082e7ee0321d7d4e6f8516850f4483fa343e1c32446f5ca073a94424818e59be90ae443441918721138ef3fc2a3374e70a32731a19baaa405152a7573e03129b98fd3213975a29321d1100f0766c4dce40b5ce016edff2dcf38d46e5d08a303e49203146acd88bbd0a120ed21e05be365476bab9e49e64359289f9e4837026c0c97d364f7b6a72ae6a21108e5238937c41a6d08f28daffea632a27579f79c573ff4fccf672f8e9ccf042360fa5da20a2c049eb5d0eaa80f06c7ca93d84d3d683af34ec1f9ab8e27e7439dd2a72a04011a378686b053198fbea48d818794f4487ea9356b54b43b84a7756dd5de6f24ed1fe747d6f5055141760eff11616184f5329080fafe9e8f3aa1d73152084548722b1954e9d0cd069adc0da50d117b912fe0a3b6f76633dc1b446320ffb49e731eae35221c4961c0615b59e81f3f8bb505740b53f1d4afb244ef9a0a3388949539c78779f4af9ad4bcfb9618248a
private theorem part35 : 2 ^ prefix35 % Spec.Ffdh.modp4096Prime = residue35 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue35)
    (e := prefix34) (a := residue34) (b := 2123524015) (n := 32)
    part34 (by decide +kernel) (by decide +kernel)
  rw [show prefix34 * 2 ^ (32 : Nat) + 2123524015 = prefix35 from by decide +kernel] at result
  exact result

private def prefix36 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (22 : Nat) * 2 ^ (96 : Nat))
private def residue36 : Nat := 0xfaf154346c4f5fe1299e43b2dc3bd116a6cbb70e6597e3799ad442d2bc72d1da7ec5ca0d6c52cdbf76935e91c948724888d95b5335fcb175b8eb9030bfbb94a7974a5ee65dc76219f5fce5f2b1ab6b5d62d96909de8686e3218856f0f8db4aaa73a9c510997f64105a287ca3874b73259b0116b517315cca82e795e64d13a5e09e21420636dc8dadd9fdaa1cf290442f0c8c5a19e6938ec330854da748ae54b98325591deca9af09a15e6957a2835d1728c7b7e878b75ae5efe579f50e347c0797a175ba02c5f9b93039ba8d0822b4add3e529490da42e540b4c3d93d375ee768a9abdc1f4707f84fda2151da2bb545512992b65eb7045959e291ed956a8496fb7998ade297704c2566cceb0fc11a27af521211106dc50968521a7a78d706551272ef5d58d8d54b4252f9c688281433616ac74dd7d60241d6bf07d13bb77f8898ac5075bffb72287ced00a9454120618414671d7ca335ad56efba6a536f7352b9688303403d8de8a5232c4ad2e35e06784c9461e80e41bf100bea31714c44f04853c1e0c5f921d6b26eb476f0c5762d35d5be786ce118b77e090a1f9d31482ddbc0cc7073d0da9721aa6b85fe7fe7b18711afc9fff4525d3ec8f087d287732236d0bac8b625f2d6f77dfff0fbe0ff601c475e5bf7a7012a0515938427814debbf64cf3dde6b37cd6f83d0c458fe8ff2d0a59176c3416ed8a5626382e35e6ebea
private theorem part36 : 2 ^ prefix36 % Spec.Ffdh.modp4096Prime = residue36 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue36)
    (e := prefix35) (a := residue35) (b := 3249712785) (n := 32)
    part35 (by decide +kernel) (by decide +kernel)
  rw [show prefix35 * 2 ^ (32 : Nat) + 3249712785 = prefix36 from by decide +kernel] at result
  exact result

private def prefix37 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (22 : Nat) * 2 ^ (64 : Nat))
private def residue37 : Nat := 0x8e221f2870bbf34d16eb5657d325d301ea6c663579ae9f7785053402d3bbf5b764f926c691d80bd5f62905cb35cb5bc506ec7571ac8f47d9237fe864278c097dd772b0e7a83b20d5acf2af6a217f54b4a97ab062b641ecdf81797292c71c652c932f6d1cabe74f36ff90929eeca0d5e1385897589720b74e41451cbef77fa59e27a3ef8792fa7fd9237c7dd4358fd04f8f1e51b25f8e80cd7054b479ab53368d1c30216b5f9537893b6ee3a65b225c2d9b10a772708e532c4f985e9c6abd3b84eb54c85b0e52ee4575220e23152a7e4157fb36278834e0fa10c81dc38332d0e576581c230ca994a7235e42c0cc55fea3e32aef4cb5edfaa7edfb6d94b75bdf6994281df9feb270bfa7d89cab897579691776c0e9e98ca157fdaa647e45518c8556cc6df355ff7d0502a6ca15bdb03134c7b59382ce38dc6378826f70a276c2b73407e4c412c6b9622ff331a5ff92e8e034ac6e7aa1291d46b35bee3b7df0f39adccad4706f72526412746da514d5b4197fdd0cfd35a0bed5260a10f9670fdfe3f6953767d4f922ea9dc1b3c2be92d3178e65a1d6659245d1d34aa4f03dae69635e7d4c96802611d7f11418a7c3491b992bf57b9451ae80e0b06111c54be23716d0f37187d9d9ee2ed4b457306386591abf2325f6ff893c06587ee8f2dfb3f38f476eb771262cc2b15e7ba21c5ca047df8793a7b7b00a63386adf1fea11d713aa
private theorem part37 : 2 ^ prefix37 % Spec.Ffdh.modp4096Prime = residue37 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue37)
    (e := prefix36) (a := residue36) (b := 3998340811) (n := 32)
    part36 (by decide +kernel) (by decide +kernel)
  rw [show prefix36 * 2 ^ (32 : Nat) + 3998340811 = prefix37 from by decide +kernel] at result
  exact result

private def prefix38 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (22 : Nat) * 2 ^ (32 : Nat))
private def residue38 : Nat := 0x7c25a98a1489d78f5fd0e61df7c33a9c03adadd30f21b77e41a69422a8a8ac6b9c2f493b90901c85354f2bf79a8c207915f88258923918834bbeaf55918f73826a91416953ea542200d937af7d0644559b38559b365d09d8ab17c93cd50f7fe811a97023681cfa7035d02138b89d7ed1a240d4d49bdacc549d09acace34c7d4f1ebe979e0e43aaf9aa1acd721ffbb728bbc914e8bccad24fced2c1414d85512a905f0eacc8eb02dfd953f0cd004dd1832a75150f34f6c225d74a205840a36e5f5da5dbf329d5d5f66420142d3dca4e81456d1bb5a6a1ab8df83760876056b6b1bbef4aeae1463b2116902388c226a9ae0eb22c1fc0884fe37dc4e838b2f529b925c707ed2b1c7d0c8d78d6426c97fede852b62a8463877ce9be2cf07ccabe46c436d771f985567685843a37e11897f0535118b8b005b88aac04e0c30a8a00f0ea7db3089f308f4f654bdad46f59261d2cc41c5a7eeab3844903b9ff28a24193fc286d1b69816c539e8b7aaf6fd3e5de4f2801f4163b5962f82962484585cb37d8027cff802d2490d24c2771d62090a4705928c149de2166eecfc98c403d76e83c0d68322fd44bb474649e3737a105b3fc34bcd91f8ef95fdeadff8f38204c3d19b3658d36e6e6fc7bb437eb3203bef0e39c2357d9e5b56a96d0df1b1293e0cf5d684143d5ec39f244f21fa26d00717bbf658176285aa2397c8dcb4f6a412e7e5
private theorem part38 : 2 ^ prefix38 % Spec.Ffdh.modp4096Prime = residue38 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue38)
    (e := prefix37) (a := residue37) (b := 238123435) (n := 32)
    part37 (by decide +kernel) (by decide +kernel)
  rw [show prefix37 * 2 ^ (32 : Nat) + 238123435 = prefix38 from by decide +kernel] at result
  exact result

private def prefix39 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (22 : Nat) * 2 ^ (0 : Nat))
private def residue39 : Nat := 0xaf8eb00a85b8255880053a3f6a4002681aa4f64c2aeeddfea34b7d67372d8257c54649c50bec82004305504e8a6799aa18216f731423976f0a6f47a56af8b112dd7fd05015239c347b0adb58964c5dc5452a3a59c2e3981061b3f706044cf582eff616db3fd36291fd203ac911b1e07732c61c2ec3c0b2fb39f79fd25025f4cc8d905890e1770dfc4e6d241da923a10f2f01930be6b515c2a145f1388597e590b90e763b31a50631aa3fe230a6e94b169883ae07f2773c1fc8669c3b4686279b24cfa1e762a592589ff3b0b96e7e24b5a06a62176bb626beeea19870f40fa09163fa6bf0aee9892c18b329d4243800ccb3f1a7e0d2f6f5e90d702c4705e7edfa767dbfe16849c7ee373979e470c1f79e44d31d3e55addec4aea32e127618ee7714e85c8a2a696142657705e47f176abcbbbb06fe3a35654197220e72fb108e38daf459603999563854131011b636f051e64cf3f7cacce36aa2c0279f8408057f811fb9da95f53781fa8d4c5c38ca8ecb6b085b7b0073fafb6488d14897114af815c792180b21efced10fa6771a5772c25682b01a9aa17f868b497136ba8d4535eee4143521b7c8846c0a5e2b8810974f094ada3546f444f41e6417afd053d5e29aed78da4af5334475631376147da0aecfa8090e6572ce57283ad37a49ca6fe8251086527466c83013752a88f98e2e3e10bbb8e22182514e9efeac89bd855d23
private theorem part39 : 2 ^ prefix39 % Spec.Ffdh.modp4096Prime = residue39 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue39)
    (e := prefix38) (a := residue38) (b := 272804189) (n := 32)
    part38 (by decide +kernel) (by decide +kernel)
  rw [show prefix38 * 2 ^ (32 : Nat) + 272804189 = prefix39 from by decide +kernel] at result
  exact result

private def prefix40 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (21 : Nat) * 2 ^ (96 : Nat))
private def residue40 : Nat := 0xd73b2a51334782c4d9e907b84f304fd8bc65f1e3a2e3060f1b02f7886f116fa4572901c3ca68f1ac90273c5db6e96d50f4c3a66370021dc5e0d1025c4b499d0cd89b054416293884cc7342a9d0b7aba41948427e73e40218aec40a466cfc1a7da3ac09fd95563a96d88cb41b3804e3a29a1fcbfe19e434de7b81cc9830f6c8f22e99c74f44206e7841d231fa1be4653dc5936eede606eb735d046656067e4e09acc22a0e82683b532bfdc6bba9d5de63bc74044f145bd6bc54910ce6afdcb2f941e72ad6e0a51c7c86c6cd49e9c441ef4432f1cda49af64ab7f1a413c98dbcb827d2e1da5437c586b562032aa4b572ed4968b874607c2e28e29ab419f2b5b6bfb2db99dda00573b3786be94966514d018cc578dd9a7f0461185c2bae37f2eabff383f01fe69326c12d4b5301b36246b8fc78e71aba90e8705f7876495bbd5e6ca13fe96bbd2237afd46629798b7e39a75de2841e399547e051be621414e32b7f6219d57c140215ab09facceacbc93cdad9171029943a3acaa262cda57d92eef488302602c84df7c2956c18aafbebd58ed66dc1f8bd9b663abefd1e79dd611558c2a8009e3d709e3faefcaae3e1dc26b39d6ff7e2261efb560543a243d178a4f6b2e2116f8682233895438cbfa3a4ef8cd1d25a007c7103829e296be4a429326ec58348e0fedb131d6a9e4741fdb68b4e2effcfe9769631e085565c99484f6a6e
private theorem part40 : 2 ^ prefix40 % Spec.Ffdh.modp4096Prime = residue40 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue40)
    (e := prefix39) (a := residue39) (b := 3479868547) (n := 32)
    part39 (by decide +kernel) (by decide +kernel)
  rw [show prefix39 * 2 ^ (32 : Nat) + 3479868547 = prefix40 from by decide +kernel] at result
  exact result

private def prefix41 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (21 : Nat) * 2 ^ (64 : Nat))
private def residue41 : Nat := 0x98c1f8c9cf11da87b6d4d1afcb4120c2cb6a9095de95241c63b2ff93b3552dc286c71e53b58d1db2444922ead39ea76d409cf27450d31270b9376880f2776b9456c3eff27de78b9d355784657b242f7cd347c70cf893aecb714207b6e9b7c74752a8e1cb125dc0b17c9a96f6e64e3801246b96e0d1a9a613925f2a3f4734c357248774caa547a40223d0f09d6671057d082bceb02448ed8d37f1dc77dacca88bc90a3f89412c175e66bec6f830caa2f4bd2afd440eb1ce7ca941da9f25c1b973aff40df8453ec2bb0e70397b0c8c1f916ceb3141ad26d186ad29ce5c9d6ff6a0e9e5a64ecf2cafea6a2047dc721e76f1c9fb17dc2a83d213b5f79e7c97c1b2c2edabfa9387733b9cad9dd84c38e925b06571da5db30b6dc1cf5922688b1b0e21d4b1a65406cab7f52e0985541f50e311c945774ebc3030880c8471390bd57eb716fa13ed523e6b27016186a110e7a66dc345a1e3a4804260760ffaedb10710deb6de1d16bbe9ac935ea3e934b2e55a2d07ef4835574287a69b9362f71f3fc2a07e4783d79fab0382a4a4f17bc66653cee0c2f4d63df38f6a2bf08e7baa0a94b90edb8ec4b78772a6e9b585f841ab80c796fb23e51ba4125904c0fbc76abb2b916093757583ecf18169a5cf41b3ab94e8e67032ff4129d5436341b9e063d52baa49299c38bb2086d0457ee75596f7ad7625be5308588f9086d88d51dfbd05fe48
private theorem part41 : 2 ^ prefix41 % Spec.Ffdh.modp4096Prime = residue41 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue41)
    (e := prefix40) (a := residue40) (b := 3091942198) (n := 32)
    part40 (by decide +kernel) (by decide +kernel)
  rw [show prefix40 * 2 ^ (32 : Nat) + 3091942198 = prefix41 from by decide +kernel] at result
  exact result

private def prefix42 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (21 : Nat) * 2 ^ (32 : Nat))
private def residue42 : Nat := 0xb62ec550386a3319f5953eb1bcbfb752322ef0b60842b9a3ff22099829ff8ed172e11939216f05f3721380a9b3b1535f5cba694217b1db75fa472a8985e827f1aed0aad693b5a1df6b9264f876aa389f5ebc6262fa0342f446357fa3ed8f9e26960e4926722f00b9bc3a9295a817530c3c49828886972c8391ce8d5adba9e8bf740bf2c987d453bda3e63391427fd5757a594d8da20a0f9658854b774256e396904f91e7958d119e3da886a7cc37e979801966654dbd931bfee791de3897f1adae8d38e97be5b12bb2ec27e2dc79c4b7b1784322b6ea002212e9adefd730d0db04b9ab3ec3989f2024af8d0c1c68ba3506090165da2a39f5bfdd422f7a10e8ddd4f5f51f5de957f75cf74ceda2d3c332ae4970ab88ed9aa8393eb420b7ff9ce5675d1383603c4816ae95d2d59daa18d9b3cfbfce7342591458d876764043c9a93ab5678572677eacbbabf8fc7649fe9e0b66447dad3913e8f8456663f3050596cff94b56516293fc5bdaa086c5388e6e2df34d4a341f750c535ba68316ebc8881cdf09007b1a7e8328ea9097e43f000ef601fdd304f28ee9649e8a5e3a90be81bce71fb5923f88c24d54d841d5ede9fd32dfb2cceb593c0e97f32dd13727f4d14e01ad143b9ee7f9d4248c3e43ee768a7fdb5ed023af73356763ee8e9e947721a94a8799146f49fe28b7af004b5efc2d60ee72e9bc75626105d089f7cfe1b77f
private theorem part42 : 2 ^ prefix42 % Spec.Ffdh.modp4096Prime = residue42 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue42)
    (e := prefix41) (a := residue41) (b := 3011910311) (n := 32)
    part41 (by decide +kernel) (by decide +kernel)
  rw [show prefix41 * 2 ^ (32 : Nat) + 3011910311 = prefix42 from by decide +kernel] at result
  exact result

private def prefix43 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (21 : Nat) * 2 ^ (0 : Nat))
private def residue43 : Nat := 0x47676874eb5a5bb45f8c2a9b077fe69a9d551522a3c0a15d393a3071ebac17697b50663089d54d216307339cee0da16799fc1fd1c5a8d9202c5b59617ae4f960fe25ddb71200b17cfe4c255a53780caf3f43438c2b33f3b2eb646fc5fd9ef26f45f9edf6e8829dff0d877aa6f96370221bdb13e94f6c16a3012e95f9c40dd7d1fb6fd48c6580bf33203e3176cc0f8432af5459617bd1b967e10cbeb66002c64fe5f3be88a568acf31c0c00a282a40cf3b0f3ea34d16b350a5957cdd22a000e36edee9253737e6bcc632adc49ec40eb92462b72feddd7d15f8c42e3d8fe91a32371f38e8450d83b0d6bb19137c05ec962a79527ad2639d619b64bd40a74e0774edcee8bb13cdd08c13a9375218a0e82afc6be64dad543d4b84491cd82296528036b621e01bd34bb7b2d26ee350f90e3d52ffc2a20144dc988a382ef79315f8a0fa11ca28b86fad294690d3307d9aab3d4fb3d8bb40c24b72922292352ec5511abcd9731d89ead27f908bd4bba6fc182b49bbaa678017ebb2be2ba92463f72ae38721b0e43b8c1eeee2b960ff8459be68f7badb7d084e2f64189a59bcb31383954a82323ba16a4ed9160840cd41242f87a3c9c97c68bee9ecab10f337af10eabbce56b5a07d984c9b1427e94c0b99b645a6dc61e40513c0ec47995177cd0f6fc8ba0511e33b4c4c41f2e91cb53a03c4b586d17f2f6aedeeb5314933c25e51a5a9a
private theorem part43 : 2 ^ prefix43 % Spec.Ffdh.modp4096Prime = residue43 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue43)
    (e := prefix42) (a := residue42) (b := 626936834) (n := 32)
    part42 (by decide +kernel) (by decide +kernel)
  rw [show prefix42 * 2 ^ (32 : Nat) + 626936834 = prefix43 from by decide +kernel] at result
  exact result

private def prefix44 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (20 : Nat) * 2 ^ (96 : Nat))
private def residue44 : Nat := 0xdd4b2c6c2bf59d8b23325b04f7a4ccd6d4c3afcf6b2f5419aab8175ad10c94a161314d7f90b241558beb96d979523525ae8529df529b32ba5ae35ec546d72039201837f5739553677ce9233ee109c5de2393798d77e72eba4b9028d4dd5fe9b66ce67171ad3bfe075473104c97a8af135f1ed767bd97c54734b6ee3e0aea5cd397b3f35d1a9c6ad2daffc8b5a7c74089bdc94664af4e6a7ca485733f2aa367edb90d10d366f81ffaf937239b32b0833d32ebaacfa76bd9796ac2c1bd22b886b61284caace7d111cbb24db013685294a63cd9105702215c090ce1995d643558f0d5b9937a315f8e2bb1a979e97290df753bf2703d2cf025eaf97b34a74225862c00dcd17fe001b888a42f18d460eef3f0c8680fdf51d94ae5c7a04d12f01f48c1516566b15c456fd673375c44f8daf5654539b27b68b08e585fbc3a02dc0925e44f402d54ff57d81f233ac9f0d31211e1c57b731bd053ec33ea4aa8fdaa6a53b178013fbafd2a5bfd8ba895c7807eeaeac4d81901cde951653a590ede2811da6daf9ac40e1ef3f74bae1933fb73f6685939510aec7aac973b0f24ae2e2891fd93a685b62f2b4c136bf765c3c2d7c125f427244d41f1383842743b3f6099128df8ef28f635340e99bd5ad7e23c12cda558cb288e561647f88a13914dc1da45357e4d2e235983651c36aede49a57fb8c8e4dd0bfca87c1c8e3c378eb49550eb2544
private theorem part44 : 2 ^ prefix44 % Spec.Ffdh.modp4096Prime = residue44 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue44)
    (e := prefix43) (a := residue43) (b := 2025469444) (n := 32)
    part43 (by decide +kernel) (by decide +kernel)
  rw [show prefix43 * 2 ^ (32 : Nat) + 2025469444 = prefix44 from by decide +kernel] at result
  exact result

private def prefix45 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (20 : Nat) * 2 ^ (64 : Nat))
private def residue45 : Nat := 0x408bf53f509c5ddb8746f7acdd5da8655364d5681f1aec26e010bbc3a962fa3c7e187fab8b7d145c46888051bfa90467bb8f86cf61df927f18c8c3b1db3fbdc0bc40fda015192ba814673cbb5b725ebbad25fc57a01311c2552c7190a86856f06c5606a1b1cac1a54ed2b95d4e698a07a5b93ad63de43aa2628c82061a5be9c0fdcf0dafbfec9a247c53d2d69f98a2e39b6c095d4c772bcdcf5e9cf7dc1568dd2b733e713fc52ea4dfd9b851480d724f5b42a9cd491f5a8125e609517c8a3996ff625c94eec1f824369cf8c18310879d9dbd1a9900478edca2015d23ff171e4d56172ad451214bc9574e8a6f966bc826859f99e5a3e3d76b09fa63d6af191ed251f8643f5ac37f896a3c72741220bc29e0ded0c06f3c6e80fd22ce0f2d1d352cce8ded5b7e85bc80543c6ac3a232cf82b4247daa33b49d98bf5308c209e20502a4d6decccbdcfd95d7781f7b95aa35442d75ed8646a5bda903fdf4b69f011df76c5090c8a7c2d530dd6a0fccbc93a5d789ac112d7b5be5d5a8e1899beeaf45359f28b9c2ca030197f7ec7cd5f6a8fe2a13d08bda366a68e0762690a2af8a076df496a37bdcd2dea2d3ab03ecff449ab39bf5b5f84d23951991d69dbf30d0794e7ad56cf7db11f31ddd0c79a5f8b4f07f02f2f804a6211d3c942f44bc70b0ea249d671e6a41847d9feb257852aabb8f7679928e9939301304f5bf63539cf30b97
private theorem part45 : 2 ^ prefix45 % Spec.Ffdh.modp4096Prime = residue45 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue45)
    (e := prefix44) (a := residue44) (b := 1695289534) (n := 32)
    part44 (by decide +kernel) (by decide +kernel)
  rw [show prefix44 * 2 ^ (32 : Nat) + 1695289534 = prefix45 from by decide +kernel] at result
  exact result

private def prefix46 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (20 : Nat) * 2 ^ (32 : Nat))
private def residue46 : Nat := 0x3e9f20bbcd68b3d7e047c179e6e2bfbc4f8db8775f77ffdd7ba21f993a7a7a600fdb40c26d37152799579ebe94104c0cf4061c93cf157e9d55e701b87e1a830cf1754aa28b1bb2324f3dba6261ea96bd2dd7ecde9cf518fc21eacc06cd8e80bc8f8349b3b088b5ef7b3ea0aafda3be44a3b30d1c8fdbb69736eef561bf8513d5e05362775f55c6bfb0c8a9ae8661f544fcfca9e4db1d881c803e95e9ac34406ad4e5581670d1cac39c3bc0999c5106f757d56c7359cbb5a5610a3745115dca8004cb4d3fc0380a2995259785f5c74eff5e83f56166b03cad0ca58adbdbaedcb29332beab2298768f0009f1aff5e69ccc313996290f0d9ca2fd914286ec084b9e39d2ae73c5757b61cb475dbe83a03dc76675e6d3fce6db38f68b9e66a561c67511b0056afcfeb47669c0083999f5b0a37dc2cc5391b241e203d4c60be5c4309bab33eebb52ddb1a34678233a3146bb0bc99487deca9acd88fffaa23210f400ad7bbd0c01811ccf24aaaf9b73e69ddf400f51f0677800b8aa68a50d86725630e961e106a4e752d147da7fb9f55d96c0deb418de20b304df07bedfb83edc9ab21cb04c690779eb523ea4db3799c4a436fef94e4920dce1ffa3b1ac08cbc5d1599403690a0d436ca4b87b90c4b9bd77904548eceb9830ab91767d088a68072dcb304c38cfe7c5617da4cb13ad3f67f415dfc4ebcb88712bed8e08390152297278e0
private theorem part46 : 2 ^ prefix46 % Spec.Ffdh.modp4096Prime = residue46 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue46)
    (e := prefix45) (a := residue45) (b := 424161059) (n := 32)
    part45 (by decide +kernel) (by decide +kernel)
  rw [show prefix45 * 2 ^ (32 : Nat) + 424161059 = prefix46 from by decide +kernel] at result
  exact result

private def prefix47 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (20 : Nat) * 2 ^ (0 : Nat))
private def residue47 : Nat := 0xdcdd28ea637dfeadf6ffd74406138ba2b4eab4e62b7871e3e820a8668d0882d6dd7ca4da29fe369a7c259ab397c0302e52f5097ae49cfe94cc67df205cbd04eb5adea308a90a8d2efa0a37f613851ff63b68aa20a646822b9bbd7f6f6de26f7ef0ce516ba4b1e2003dba817f955f0d20f7b44743b8f28cf9de63e3f11bb16e3d92fb4712e6434fad8f5df8a34ad20b715e779b27fc53bc0c9b3eb48f50bd155af2a5f91158a5870fcbe0c2bfdca2f5093c4506cbd4cf7c1cb8524ca1e4d30ea7613c27c4c40bfc9b513e38448266b635ab3d061dc1d1ec94b051f81a2a86ffbe62a83c2e0cbd701d38c21143ad5d5d277cd2e77bb50e3fac45212168fdd4fb93272cb355a933f747fde16b49b88b11bbd5814985ea683311476db2f5cb91860c6797dfbea4ac6daebcde1a5363f800e84323d43ecdf77a43b892c73ac5e19b98024a0ef085b2f2ac63df50cf335c08653ad6b0c81a9656aff6be6fa5238ff91131e6399df3f13816f8468014486e54be9863790df8e9e2df2e3cf97feeb7177d444a28918fa60c7617ef878ea48a500c8eb008a92c922f5995c86053ff5d98e9f9a273b4def04788c5fc66d3d40178c1220b2854fc59f6fdc15e93dc7bf341a73cdc783a7c474c6829c2a04c3b730171b7c0542a994e9b2e5437aed0e7c272d0126ae09ae547cf0fe523e9d4d5e3cab9e2b9b69d58742758d715a32a1d3c141b
private theorem part47 : 2 ^ prefix47 % Spec.Ffdh.modp4096Prime = residue47 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue47)
    (e := prefix46) (a := residue46) (b := 387671837) (n := 32)
    part46 (by decide +kernel) (by decide +kernel)
  rw [show prefix46 * 2 ^ (32 : Nat) + 387671837 = prefix47 from by decide +kernel] at result
  exact result

private def prefix48 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (19 : Nat) * 2 ^ (96 : Nat))
private def residue48 : Nat := 0x94c4b44e0b3142f9ddbe1adb3a52df761f3b16bd1b6ae313d77e7ba23b6340ed24055bcb036e1051f61ee3ce0c5d388856719d7eabb825e1efc369e935e2ef81080346a152172eba8f4d5d27544562a30870c4fb1de4d06bbd190e59eed22c2074708920424f58723422741769fe53bf837221137f22614aa4a83438047e56254500ff34136b620e54a8b2d445cb7909963e066ccfcad16bdc2004a3f06c9ab6f24e3599184c01b1474f3b4a89d1a14672f7a12bfb584a82387caeb68409864894a938997b3b40af70886cb62655cfe3df5d86e793a4bcc4965f4732cb68914c6a2fe3c7a5bc6195456bfd19ad54b38a1e77ae804e90addedba730f5bf34cdc683e15191056f3ad35f6c3fdc2562698a269567471aa5f6fc77b4e1f4c83bf430903b775bfb38190577a94cdafa26ee330c3e26295f1a3c8f3583bd2fdcfb5c75c62281cdd358ef0e23c392c97cb9bf8f153240529133905aaca03855ad57e75abf6c1373e32228781844ce59c87dcf19448079f529e66a0ee928bfe6c06e5c7fdcaae14e63fb67d99c660e8706d787a9fb355ec02dd41ab1f6230edf85b04351541a90527381a924090e5640ae025f793223c3f3135d27b9872b1d0f21b521e45286aafe36ed1d4cbf845f05b3c9cdfec60da1394c97a85db9519a113be107da8e86603e299566e4df756f1f4fdf4f2c284f8289360db486c610afb58dc20477
private theorem part48 : 2 ^ prefix48 % Spec.Ffdh.modp4096Prime = residue48 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue48)
    (e := prefix47) (a := residue47) (b := 4056890262) (n := 32)
    part47 (by decide +kernel) (by decide +kernel)
  rw [show prefix47 * 2 ^ (32 : Nat) + 4056890262 = prefix48 from by decide +kernel] at result
  exact result

private def prefix49 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (19 : Nat) * 2 ^ (64 : Nat))
private def residue49 : Nat := 0x4209efac7e62b064dc73c82658ee15295d3e993cdcff1d6407cda6388eb7239ad36fda9c0fac322329b2b4fd6d0f10cc93eccc8b9c621c967265aa6eb89d57bdc774fc1e86b0daa76cb3c9d2ce29620f3746b216a0ddf9228daa163e452284ac849cc492e05cfdce8d4271d8cbe4cfd2b4eed65b27367e826bcaddf944b61cb5562d6ad364f23b88e25da61b6178852cc644ee52150e52841fce9c883e32ebcc4ae4d84d27b0557ad20504170fcd82766f754d3d1cb3d11ecad47e8f3ea7c00d0478baba79bc4c06917618e327fe0403544ed0a5f38a85f857c04f9bf91746b66c5d26e679141f3f69e8e7737a8ff5b3f40dffe4785eac10780422b4efec32cf4f3971bf335ec2e97e1dd7760d792c85bd78232ca2273d045d902f3982567b4cfa12f9193210767ca7e7d02d9ae07ba2944076b660c033a51866bc01602f312f5445009c9c5722250bc04754d58d2bc56aeb6e80801874f15f9c4d4e458c7bb2175ff70c72f3269d223a887221796f93a77535b0cc99e4920617ffa482eca11de9c56f06e4104ca476037023d5500fd0aeea6e2a9b9d82a65bf0d24d8f78971b9eb0676cbdfb8324ca2fb5a8620fb974fc8cc6a1b842d6beea2a47da2fb8fc8af8bd73c013a44fa384cf1a5230892c6e040ae4e11e911a24cd10153492821b52b024074ed6abb514c1e6f2ac1ca6f7868fdd4e337421b18ba8106e677b27a7cf
private theorem part49 : 2 ^ prefix49 % Spec.Ffdh.modp4096Prime = residue49 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue49)
    (e := prefix48) (a := residue48) (b := 201802497) (n := 32)
    part48 (by decide +kernel) (by decide +kernel)
  rw [show prefix48 * 2 ^ (32 : Nat) + 201802497 = prefix49 from by decide +kernel] at result
  exact result

private def prefix50 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (19 : Nat) * 2 ^ (32 : Nat))
private def residue50 : Nat := 0xd908237dd6d3a38bed2d927fefe571013fe73da419cc374351d016eb851bedf4aa0c82985e7aa26b63b78c01626eda79b9787bd00207da0da214eefde68c288c11bafa025219dabf2010d436584b1f58dcb8bf663c62efa91e4cef3f68012bf09d8533c4834c60299f858b84fbee32088a093b419119acb77d6577a49fa767a56c3139f964181a620f8f782d178bdb37d1ee32b4ac4fac3ddcaa43cf512d2cc8f3f3ae33bdf6d6ca62023bffe3213a5ec23c38a67ce0fd05d8c32f04bc6e3716ffc60570ea926bda53c9639484e679a4e9fd27ce09b230b19be23274f8f0b38b1d51c34ca6b0feb65d3f5a6d41ddddbac4542752e6d3c1d9138ede6e3016f990af4be1b0e6a4ba16ae2767b8cdb096b10609fc4eeeabfff45f876335d62e6a51af47e2ca22349174d2c7e00fa2194830f192cdb3d3d1ea2b8f19acf5a5ee37a4f5555627c4f543a1476598d0a1bf8f64d0b52cb0950eade67ff2c1c82d7140f7e78f4c6b50004f951e4a91df3c11a4c0ac4d6ce7b68ab40317d76756b2faab0369d026923b856ec65332433970f0079bcb712246dd51deb4bf08df7ab254a2bc302508a8e08c75b45a2a3d913b540b4057ddfbf79811ef1d544aec3d38a197bbd6a7797ee59d5bd13d6fd1a977eb960a63d1d988b991382aa480bcb7c3a9ad382f1efacb7aa5be500f80213e09e7da95dd8c5b30d960e2bd561952969cfe81f2
private theorem part50 : 2 ^ prefix50 % Spec.Ffdh.modp4096Prime = residue50 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue50)
    (e := prefix49) (a := residue49) (b := 3449012689) (n := 32)
    part49 (by decide +kernel) (by decide +kernel)
  rw [show prefix49 * 2 ^ (32 : Nat) + 3449012689 = prefix50 from by decide +kernel] at result
  exact result

private def prefix51 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (19 : Nat) * 2 ^ (0 : Nat))
private def residue51 : Nat := 0xc32df7fe5d6f5209dbab0fd06e7cef19dd5690b6fb812dd1b8733b36cf472af1a02f6cd194766b0406bb0f2ceb876aaa9e46dc6a8cd51d8b2de5279b974b566d6841abd805af0e9a77e05257579d89da9cf72948454f44ffca2ae0b8c04cf3654fd907934f6c08dde767c5606118702e7d32f80fd75e0e11799f3441da6b2cf39c17d21edafc948fc452be7b0c1456c263c867788302db5d817df014eb0c30b7b6e58d9e223627d512ba0b9f068d5b2b8c0567cae06f6db39a4b585c34cb1b1429c184c467f867a120ab68311fdb8f09aef905c825cc6cd27e83c62ea9b4a812a20a48c3752e6a10e9cf6541e432ea649dcc9fa1b4adee2e73aff81fe9108d57176e7ed326a1af4c3cc11c3333d492e9c9734c51628b47ab73690c56e466751f0b843873dc07d43de5113086ce530dea22b6c9156553783ad0a67db305b8696160875a94c7682370d60f7136147d997391279e38c90948e9db8287548ffdb9798f02f6bf164d84f5d0b5238882b12412ddfb8a0789b3a9e24e1acda5adb6c5803cb57786af0b7ceab397bb5af99847c56e4187ab01ba2253c5b5121afcb2b0ba0bcee1e986f231594229580ca93b6590e99c3ba7588ce53c34504d17cc6fce8c9cf894def6eeb86197108e1d0fafe7bdbb1a23ec6b17ab57bcb3a62404453b13eae869b05db97dbc03d2d099f9f6e2d89860f56ab85d99b255754f1688510676
private theorem part51 : 2 ^ prefix51 % Spec.Ffdh.modp4096Prime = residue51 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue51)
    (e := prefix50) (a := residue50) (b := 1979961671) (n := 32)
    part50 (by decide +kernel) (by decide +kernel)
  rw [show prefix50 * 2 ^ (32 : Nat) + 1979961671 = prefix51 from by decide +kernel] at result
  exact result

private def prefix52 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (18 : Nat) * 2 ^ (96 : Nat))
private def residue52 : Nat := 0xbff2992b777c36ee39f8659fff9c318e2b47c06d8a4645a477d4bc9c6ba0e6ede39af7b56e85986e96b71b2267e25bd80923fba0356ec07e7d7b2b30b0d8533db5cd9b3cfe87fd03117c34cd060ccd15662d89bcec11bbd57b956df9e380650674eea0b34a200e0b591323dabadc0c966ff2360eb9417782740e8ecffde5c7d78af62d6b236e3570ee509a0411a1cda74e994736dabfcc9015d564fd70291c4eb9346062c1c52c255c7c7879eb3a46a5e6e307517edb00204623549fdcbb29d839747d592a4f2f17e51696db08635d8a9d2aeee28ea7618166e9b7bff793bf485d57ec6df379bf8893c2daff7ed7d5e0f139bd06338cfdcf230e5d22d87cb16fde042e1e2f93c9ab96cfc2d3905de4f2f29bc343f687deb58903401bcfea9298a0405862e817a0734cce9de367786afcdd3c9c4f52d20441a7fb2c03f4d1a3d59a4eff16f986d2746ed262290ac1c9d3127083f3098fa2f166ea2ec263638b89dace41151aa3d97d3e8c8c7b14742a8c406655accf3713f7588964a21bd7cf353a8fd1f6151e2d7fd3d9746d9480675287f5550a36eb3833cc7b5a9e6be6af0b8340eb96e21178af10ae8c21f1f3477fb1213a6d4291723877ee9e8501ca3c23d3d5634f2a9d77769388314d79c134fcf0c637ef4a257f386389de8470b5a6c25258348f3e647ca859e1964f467da4bc34ed047a2802ad7e3c8cc2456652df32
private theorem part52 : 2 ^ prefix52 % Spec.Ffdh.modp4096Prime = residue52 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue52)
    (e := prefix51) (a := residue51) (b := 3672289016) (n := 32)
    part51 (by decide +kernel) (by decide +kernel)
  rw [show prefix51 * 2 ^ (32 : Nat) + 3672289016 = prefix52 from by decide +kernel] at result
  exact result

private def prefix53 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (18 : Nat) * 2 ^ (64 : Nat))
private def residue53 : Nat := 0x3ad5d9495b6d62ae4125b75c147a5d0201a17d6085849334b2dab44b5b165dfbb9a59ce7461b99481c0a19ee42b940a01ab1457769cfe01ef55405be829dcafe53e4e91b8838369cac5f9a6307053d15bcc4db893144adb6fbf6f44ad6acaf77a76b62789290bb59c0e8214063fe927f81bc5856c513cbf7be70112abb92f9d1db65e805f1d75d8f2811fb0e0169db2a4fa096a7919bc5709ef05d3fae4d8dde7bad4d4b6bf3efb9df52ed024909237cbd8d7d90dea171da820cb1681c0917ca6b964b27cf34ae7b1bceab679cc9ce92b65853fb3e08e7a41673ea731e5c788700bb7b3099b2141e64a6510596463cbb30922657a7151d53df907f0e299b8b1532bb6c0cea659fe583d21c2d45da29d30f8bc927cd39f00355c00f19bac6d78ae45231edbb5febe05c76e2f2c2689fc309f6249c2150ddbbded6750e7bba977040dca5f0647e514a677cab3daa11b971fd7ee5baa3ee65756a08e61be6a1e4e36f057aceed6564cceca7ca8d6e5f320547290e38c8df49b40b02155c65fd6c0926d541d0f5329d3263b68d5f9a689ff843665193beb13eec925d33586319c902678b67ed5e1f9026764bdb489e7e198a5565b2504e0c90cbc13ca1833620cf641515024b9f943e36a9fdf58b72d737156fbbb097ecdbd1ea08de784d910d5f6c9932198e2acab4da6c950b7dad6a016e8fb9fd81b15616f9b2d264038d68d2b0
private theorem part53 : 2 ^ prefix53 % Spec.Ffdh.modp4096Prime = residue53 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue53)
    (e := prefix52) (a := residue52) (b := 933636452) (n := 32)
    part52 (by decide +kernel) (by decide +kernel)
  rw [show prefix52 * 2 ^ (32 : Nat) + 933636452 = prefix53 from by decide +kernel] at result
  exact result

private def prefix54 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (18 : Nat) * 2 ^ (32 : Nat))
private def residue54 : Nat := 0xf135814076019adc8c87a913ac41c6c1a71b60a57e7144c64e8748d191bbe2bac79131950ff86721ce0032f898ceffca8415c73df2ac0a391580aeccc968f2a33c67f05f5e3966aefeb9aeb0fa11ea9a37574fab0f20f1a0df02f84c341ce3cf59413482fbfae4cfdb77559390e55b1668608fe7830802f63484523bb9be582f5cfc83a5c7ad96df99153070c49c88b81bc2b41dbcde6764927107b7352446ddb5b08060f5745804393e41d6f780367a9910e5420f60d2e8f7f60638e7ec7357d3c674888be6b4c1ff22d218ea497ca5a90f6ef0d3fa6cfc601fd732619575eee43f994f7e9613bc08a1864e959a29f8964102fe84c8884d79b0c9a172e495a3a3c8bd27149b56ef1efa8f51a83381da2f4556c23c7f050d3c688bf1ff62f29df418a4778b16052ea1a99ff4a5c797042fb6cc7bff68e04e8d6bb0142863f89bf2957bfb31178518ca48311d73ecec1c5d6bb3c44288d31fcac267c873a9c4e5a1ea5eeb1606b72099646efbbf794398165d730f948262e7089975b094b3aeb23bf3f0c0a85af479d53dcdd8ebc40b1d0364e9ac8d5f9095f532ec945cf857f6d6300b80f5285532560a7f32048cb225be2b23f971f1fc9432c23c8bc2e33d306abad775ef139cab7340c53db85dbe08c67ac81aa0954489ea232c25a00655d7dfa956b6be7be6a2c9ee4500354bebb3038188f7588a843d5db7569b6f9e213
private theorem part54 : 2 ^ prefix54 % Spec.Ffdh.modp4096Prime = residue54 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue54)
    (e := prefix53) (a := residue53) (b := 4011189755) (n := 32)
    part53 (by decide +kernel) (by decide +kernel)
  rw [show prefix53 * 2 ^ (32 : Nat) + 4011189755 = prefix54 from by decide +kernel] at result
  exact result

private def prefix55 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (18 : Nat) * 2 ^ (0 : Nat))
private def residue55 : Nat := 0x41614f6d6c436c27bcccc31378e286c3b16fc79aa4c74d1fd382145b0f359eb4a069b17ce30dc8224df8ba3411ef09de44d8071f7281f6e6033dd3adcbdde82794f50d7c5aea0281458a5da934ea85fdaf1acce89c4cbb57e898c2a5c5c83b19a8a64e01df366dca5c0a119af5d630ef5fbf0f583e5eb3ed99b48776d0df786173f6c73daee423c5ae25e1465f66759d152c27c7bd1a237a1a772afb0138f3a9a8ba54d88e0c89c6585545217a159957ff378521f53fca302b368fab31152d64a18feec85c91aa7ea193fa75abb42f5af37baa74331d0922941347ca8993f5857fec32bfcf7a9aae6f52921643aaf9c9eb4165d07e1f2fa02417df2f9bfeb3dd9a55430be2ec7ecbc555c081f7eea4b8c985862289d71fa23a8cdfb7a45ec8237d52fcdfdb6b4c7f99ca0d3775763959d5e05fdeab9c1d47bfe9b4037a9ac1af58a09243d40917589a09dd11cffb94a59f15e2defe76e1b8f48a1960e955ec45ff78a7551dc39f7ca7392fe80b06e6154227c53ac334c2ca264d2d27124487fb5aeccc1ca0fbe0d1671fb45a271cd55ca4660e9b96f500818a1ff15d7fc9e8de5604fcce208ae1d0fbec5e14f2a94a381dc75eea1daf4d79bf9aa99638eb9861ab7267253262843ba5997f623f72c90fde839a5da12bbed405c12e32d6e389339e04d8c34cc47ae445cf66339d8b28b594d1d4b57138e87e0ca82252fe007b36
private theorem part55 : 2 ^ prefix55 % Spec.Ffdh.modp4096Prime = residue55 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue55)
    (e := prefix54) (a := residue54) (b := 1252789132) (n := 32)
    part54 (by decide +kernel) (by decide +kernel)
  rw [show prefix54 * 2 ^ (32 : Nat) + 1252789132 = prefix55 from by decide +kernel] at result
  exact result

private def prefix56 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (17 : Nat) * 2 ^ (96 : Nat))
private def residue56 : Nat := 0xccc33c68afda0125fd5b35fc625dddf9a34351f2771b21994e5b0e42107c60348c9dd9b7aac69819fb46bdbf69db57ac62d27306362a9893737e79b6edf9fc70c8be87b4cdf765b113e38f0d9c4feb8d6217b8e349e3a571ee2d68ffe6326b6549f8dd5098b82461453207bc335a8998a1471f35b63946d3d40a8a8267f87349dcacc8207345cc6a350302cc6f65a6ffe7bfe1b11e1276517657bdaaf02c574aa8b358ce54b4e62b1a01897a1e77673e4d31f145c1ec72ee4dcb75257e7c4c91ab3d66e5c372af90bc3d86c5e04c17cb7d5edb6663f4ffec2b87aa9af3b1f5783b7fa7acef2d3990e84b6183030dad595e7ca0f0b072a0a1f2288de7bb84f0b60d9240b78573e14257e5d30562356c7ba865ed9812c9ea6cbdefc6dd9559747a9b534651afb5e2948e2ecd0b91f831fe56d59b8416c64badd6b7929c7192bdf2e2ee601a3e5cf7aff1e5bebef86376bdd2046bc72aa969164715aa8c1d1b68ce5c1227dfe9c406ffffe4f1ad3fff1e62cbf81604742b8c1da5ffdef8ba7dcc019405506bb86816cbcf8bfe68a15d350d46b3fd0f464c416bbcc7fdb02a26e886ff45bc0130df998ac9b2fc23c6a4de85a585caf25ab149ce0d3aff8bd95d8c56cc22291c3682346ce6915ae1011ccb57bc866cdc38872a33b737ffa83af8904468800dcb56bd69e621ed79b90698b3e2a30a5c01786f5145e6c8e0cf16092b4e
private theorem part56 : 2 ^ prefix56 % Spec.Ffdh.modp4096Prime = residue56 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue56)
    (e := prefix55) (a := residue55) (b := 483042494) (n := 32)
    part55 (by decide +kernel) (by decide +kernel)
  rw [show prefix55 * 2 ^ (32 : Nat) + 483042494 = prefix56 from by decide +kernel] at result
  exact result

private def prefix57 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (17 : Nat) * 2 ^ (64 : Nat))
private def residue57 : Nat := 0x344f87373c8b98b53bab1df210834754797e013d3436257d82c816f4a0c0b2adc416bf358455c58e0a542723ad03e5e7540e8534053c6b678bd4e3e607ce4b0b77ab3ea6459ca7324fba6c884e85a6f909a5a15be532243969bc791607155c715562beca343608a64a1577bdbe9edbceaa86b1a27616dfaa0524e4176652686d2204504ce2eff6e334c124e5a763873e66229e536ac41edb14d9fb9856495dd3aed627d9fa20abdfd188c6855985bc5d1087ddecd78a17351456557b44055e5523d95b7459208ab1ab1f6bbd98654672d717cab13158c1a663005fce4ecf4d2460dfecc90cf353ac1b10630ff7e31f90b590400cf13483c76bc0409559f14362e04832c6f6c660c0ea7e739e5d3583a177d3fb8c5b841e14199cecb313be480a240f5f854c32de1f10a60d5908271d50a35772865e622913903c8e2d91d695f33cf70f6e85bfa1731ce5119cfa9bcd5cef3916d51e24318aa05a711ab54c9ecb5cda5cb6912496bbc78cc92bb87299eca022d8407a45b051c639176c3b8da3c665d62a5694880ca53b781474f856bc44fa82cabeb55363214bbf771cc701ecb58205cae4d0d7a454336fe2f20707ca7e4536613c251fec0dc3c23c90196da123c83a1734f72f37eb07e93d9e294a945eb13ba59ba1a672d5716d4b0c3e49ed693fb820743f49ea4efbd3c31feb53d2a5bf537b944b98cae30c15ea6cbc1a2e9c
private theorem part57 : 2 ^ prefix57 % Spec.Ffdh.modp4096Prime = residue57 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue57)
    (e := prefix56) (a := residue56) (b := 1967830386) (n := 32)
    part56 (by decide +kernel) (by decide +kernel)
  rw [show prefix56 * 2 ^ (32 : Nat) + 1967830386 = prefix57 from by decide +kernel] at result
  exact result

private def prefix58 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (17 : Nat) * 2 ^ (32 : Nat))
private def residue58 : Nat := 0x19ae770954bdbf72d28ae3c164043c22b7392e70e3b2f278d02283b96f9ab64a35fa4b7c505530f236db3882c4a948976e1754ebcd9da19308c4c4986f5141aaf658c10d9526f4f8f8dcfa05ec689068e516ceb41adb931957b7b7c4467778c1266e1a36477f2d90db1b36e63265eeef762d868983cc0366c8740993033816014a6de4e54f6c3998252915d71a078d7c31e4cc7b8e8d4bd0123df70635fcc2af6b8e34c17755aa4f3b2dfb7ae46f388837a4fcf1003aad3171eff56ae88023b2513c009c71ba876cff5b2fc7e1303007aca36cbe46017d9b11d358cbedd18bca84ec959758a3d808168c2c83e7ad342ed60383b61000382834d6a226e3ab104c1a7464692b726969ec2ba37358f2eec21a8a1e603b9d1f25ea05da50ca253194feaa10465ad6f0a647fb35a7da22c7b47b9dfcdc31fa33a21e5451d5638d8509ca250653687f894e6d195c11c978f27b52e174e3c3c2a1b23996f1f6b96ec00086b546cfbbbe3795a36bd7397899547b12cf3f109d4827ae45a8de60e4ad23841d263a14abc900d1300934c45e789e963f4b159750495a4ab0f75eb6fc46a05e2bfb9fef2e7fa4000113eb039b69bbefd26508b1d89d639898c2ff36af009ef80af8e9df6b5462c0d94e29257c2388346f6ecb865eb9dad448f62c2ef9abf5784abde5c0d8b96edb097e44d629c0bf65eba76ef0c172221fb6ea249b74aa847f
private theorem part58 : 2 ^ prefix58 % Spec.Ffdh.modp4096Prime = residue58 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue58)
    (e := prefix57) (a := residue57) (b := 2330530572) (n := 32)
    part57 (by decide +kernel) (by decide +kernel)
  rw [show prefix57 * 2 ^ (32 : Nat) + 2330530572 = prefix58 from by decide +kernel] at result
  exact result

private def prefix59 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (17 : Nat) * 2 ^ (0 : Nat))
private def residue59 : Nat := 0xcbc7370f730377192ab3c4a3cc4f4c386d83b0d32c989d9869d298eb31e54e40b1a5519a3a3275983eaef5c328c4a1fa2af60888cbd38c19ee0ec77d82141bcdc6138a53bc23922d5a0bc97d6ee7f5cdd36c5b298363e2acd68b9814d819baa4f3b414bccc538bf66eec99333b144392e5fa8670944f300ebdd67fb4ad121860bc5a106779a2ccac6b0b3707e88172bb5b00d9ee7db48164368eabc85af9902e1ba0d3dc31a524b9c1dfc3c150bf8088fc0894bb41b7e80706ea2f96a69cfa4ec185b6130081d469832dd30ea5cc06b3b3eaaacfdf23ae75753dd4ce95fe2ef1201e4b768636a1ad7d86ee4e404b9a33fd3f2e1eec78e41ffa506cb8a695b3dd7cd38c67a7a27ec6ec40d111b82c4b82c0b726d0dd49def3eb0e62c14f4aabca48e508fe82ff9a927229dff0cd55c7b36814128dde06f42658798c0b86bf949f6680b8f7e3830d4039867efb801d6d841c6c39d3f6b683d1843f53d83ee1fc463a72cf464782e4d020f0bd3f35046282fb0f9d4e91daebbf1adff7aed01d8b6cbbeb07ec466a86eef86c12cd7add4826158a7ec76b31b4f797e9c09279de32854441d5e724ee56f1e39e122adfd1add1fede11fd14215b17a673cfea785bbf3aa2bfcf9fe638e77f14817aed522dbde35be10935d1bf3c0adc317c4d97f7750c059e94a52711de956ebb41e75428020f290a36f5870f6abce1e52c571d9a8e33
private theorem part59 : 2 ^ prefix59 % Spec.Ffdh.modp4096Prime = residue59 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue59)
    (e := prefix58) (a := residue58) (b := 1283261064) (n := 32)
    part58 (by decide +kernel) (by decide +kernel)
  rw [show prefix58 * 2 ^ (32 : Nat) + 1283261064 = prefix59 from by decide +kernel] at result
  exact result

private def prefix60 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (16 : Nat) * 2 ^ (96 : Nat))
private def residue60 : Nat := 0x5930556c29d8be0592be42d1b9925d86ca1c69191dd4018bbfbcf548c91bfa17b89124a8ffe3b51286847f7f5064b8ec50a9fb6aa44fadbbf7846ac9666ad450cbe5b0c6ec578aa2d985bbbd843460e708576030c6045b6fcffb542ac91893eebca961d73c13c35d71ec0b94da6ac11c78a9bcf01adc2e4bdf83f4607612d9334d36ce6f59d4467f0b72ed48e888f81264665f6593c1f6a1402875f8271084d9b19aa725e112812db6ec2d3118860d6fe8a07c20bc8d59841a78a6866e7cd1b7e79444b245a7a7f6480022b8bc8182524c286473e2e56c683eec67bf37e945d8e11ee0a719e538fd2691cc0b8c44ae0016cef7b5b90210b73e2b32370ff99a8bc27ea8ca00c2f0b4e4d7e06eb2163551fd3588bc35b60d9e3a506f7d02467b502e5ac4a3a719b72a4c0c4ad2a9253b63908f4a3ecb9202734d7cd0e3c93c69988ef2870525d293f2f3adf1b5f4dd5c28ca3b78cf9bc8874399177bc620a1c563e31f14926f135e045f67c58b85e782ccb731edd8720581a1a7db4e23556c50200b57d8a63e612a3112f0d7814b222fff9f7a79c28a7b17ebd9c08eebd4bfbd0123122f508f48a3271d95975e23430bd3d7befed7cdc2a442c784d8ba15824a9a71a067c6c0425c8fe970b62aff25e2e005c6fa55b1504ae22b4b3249c2d5c2fcd38ebe416b0997a35ff416aff9d9b8edf300683bd00c4fe9f96f9e4635160e6c
private theorem part60 : 2 ^ prefix60 % Spec.Ffdh.modp4096Prime = residue60 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue60)
    (e := prefix59) (a := residue59) (b := 179914541) (n := 32)
    part59 (by decide +kernel) (by decide +kernel)
  rw [show prefix59 * 2 ^ (32 : Nat) + 179914541 = prefix60 from by decide +kernel] at result
  exact result

private def prefix61 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (16 : Nat) * 2 ^ (64 : Nat))
private def residue61 : Nat := 0x53460e274fa288a1eb47c63b7a2e66d368151287fddae31fd5cd3c8205e1132e8a69c92a0b02038645e52d33986260f090bcac82aabcc39bf7d3b2e38dd19e86ffe0a7095568ac2b5de618e0819e805ede0883f61dc2ec5bfb69f739fdab81504789e69af95e6579793efa90bd4b2863e7514102c25304ac4a65f03672c090cd245a223032d8c5f2c6e22dca6490612d0ae076a349f4ddf3f2465a2f30cf247f877e69c2ab63962d5c49ee57f082f7d8154e1bd9c3ee1632050df6d6cb6af2e681fc98529be83b68ceadcba76dff35068872926936b18d41efcdf9ca5f9767439951b4e38a9f5dc149f8b388aff3c360f9d1c2adf089706b5c5baeb522d95f0d98361d162e5d87ae04a4a70730c4280811e4fc25aeb2baef54f40214a732cdc04a92f70dfe896346d3ec38aa092e26bbc3f0a04aa09f3930c87f4d017278b9486f6a01692629f17f53c08a323379055d2806fba5f3b07767343c78acd7bd19b3771baa8dc23f9a25165328a28a6a7ae87a2138051b093a7a2c8fe31f084a41c84db7606e7624f89169f6d4008966237f4a3e00c6457e7bd8db6e1a7688b22679f24f538fd5709e69cfd240edf152b4ba59db4cedb2ced914c7cbecde01d2f62db9c7327295fc8c6c12bb64e72b6edbca59cf3cead6e7c9b634c7ca4ab736440e7127fda0b3c5381829598a455a24c33f3322c0213d38a58e43f55e40ec651e8b
private theorem part61 : 2 ^ prefix61 % Spec.Ffdh.modp4096Prime = residue61 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue61)
    (e := prefix60) (a := residue60) (b := 1163223574) (n := 32)
    part60 (by decide +kernel) (by decide +kernel)
  rw [show prefix60 * 2 ^ (32 : Nat) + 1163223574 = prefix61 from by decide +kernel] at result
  exact result

private def prefix62 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (16 : Nat) * 2 ^ (32 : Nat))
private def residue62 : Nat := 0xa16942e031df70023b71d14cc9a210d26578489d86c1ea7b124ebcb25bff1cf3b905377fee8fcdf3e84b6877062dbeb0f36de143912303beae54af53085617157d041d556028a878223c49e329cc68b1d19a0083bc415c758f8d52cf4f7ef1ac6717e59fee2ef4e5d95958b81ddc65270c1207ae0243a4a01b0528dd3848ca5b12801ce520c9301517ffee36d3713ebc5fd50e92dc1fbb7066f3c024c8370932058c154aa00b0cbd236fce0de2fca805faf2dcbcdc917ba8e1886ff67d3bdf28962089ffa8a8d45fb65785a1166dba32bb311e586c3bcf9028f711109b5cfd66ea19a61162b9784f31751367eb60f86eea47e7117ce893951144289ceb247887696a3f40d80fd002983de9464684b6d8b37151ece1294fb7a9757259c81eb89a9ba3dc0021d6c75953e2fdf9af9b27d6e5c5949ba13990b2b7d2051b81f9d5eab509f49b6f16ee4f6a4124612da3486dc5c9079df77bc6666bfae62d07f9171be37db38cc70901303a05a51fb962ac24e83e34442beadcc70a3335a2aabd10d709936fee291e09f5e559ae91e8b45982abf65c2804e4e7dab0cafd0f452be22589a4601665984c521c808a7cb2a470a1bea2683f4a44bd56e6ca388893415a72e6c375f03faa7289623d2c61dfac64ee7e3afdebe136b18b2538732a79d243a8e55572ee5eaf0fdf7f5792d75a208a9529386b1688633809106502639ef34255
private theorem part62 : 2 ^ prefix62 % Spec.Ffdh.modp4096Prime = residue62 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue62)
    (e := prefix61) (a := residue61) (b := 3600386950) (n := 32)
    part61 (by decide +kernel) (by decide +kernel)
  rw [show prefix61 * 2 ^ (32 : Nat) + 3600386950 = prefix62 from by decide +kernel] at result
  exact result

private def prefix63 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (16 : Nat) * 2 ^ (0 : Nat))
private def residue63 : Nat := 0x7c7d2b08b10093b23e23adb960e243a875924912cc6395fc9b4212a95d2827afb269d99d102f8272383c4db6aeb04f60fabcf3c3a892c0bee879f89587e27c859f4f8b9a2a881065c72bae97380ace2a2b6d6630bbbcb80c14cd4273354c3930389098963f1667b3f2f5bce747d47d4424ac734adc77575571cb974f50e6edb069f0e4d597b1d9728919bcc75952345b4705b402905cc34a40490bdf18d38dcb65b4881ddc04a971599da3f3ecd486e54e4467ce031889ffcf1e7df96beec67f2b346e27789f17e3965786f8d00b6be583709bf2c15e73fabd3e52878defa3c16c764ade830b36bc97c0679e9b5fe4f8f9bb76648b704923d9dcca084bacfe033110833fa64cfa310ec8ea8804e56e7e66b73bc082bf352de38483160b25af244c1fa40cc0c9e1f14a578ed0d55568a177dd03ae06258c8665798ea2462c9e8e2ca9d7c328e6c775a96c2fb6fe06a6cb0067c3a98f9c26216a11f94053c229af8118cff399f2a573a5f13b52e7a271c8dcb8de34cf6e088b9032d1b6b93ea1eaa604a99a6a55e9865e0b6ad6565e5f6bfc356928f02003795e2cd2035329c1b528a5bbc5484ed45b753f08630bb98bc00696be5572be6ff0377ba81ea7a81df04e0313e6d60bce7fc7a262c6eee3febbd632acccf1c638e95571b6823787ea9b377627624438bb0612f5945afbfda12a1b09ab4507cf79f10754faa4299fd3b4
private theorem part63 : 2 ^ prefix63 % Spec.Ffdh.modp4096Prime = residue63 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue63)
    (e := prefix62) (a := residue62) (b := 2183675161) (n := 32)
    part62 (by decide +kernel) (by decide +kernel)
  rw [show prefix62 * 2 ^ (32 : Nat) + 2183675161 = prefix63 from by decide +kernel] at result
  exact result

private def prefix64 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (96 : Nat))
private def residue64 : Nat := 0x5658e8cfb642595f26a1150ddb1babaaf3f7d020d5324c098312a4d316f914d7823b6d08d34da6aa0b4d935a850716d2291069c6524fdeb2283bdafbac186ac368908c9a24c683c20787d9d0811cc91f86d26b1d87718cc1ec96af1532c10d15ee37f26ef498cfbe3b43c40bb03d1ea81ee92de86a6842ac95ac4b2e269579d2511470b4cb1c5ec116143650d4b56f7fc77e8ce6455dd9854331ae1e1bab45947b3e6d45da577b97f59a79690420312f4b91ae7b0d483f1023f86a3546f68fccbef3f2a178330700259444e0849c3d5f642ab7fb1d1d07f29fdf72ba0cbcb105b09da4a801fea645a0f0172d8b5702be90a1cbad5154467d6fbe466c36aae5fb510046ffbacf354920c227011012afe32a9bc5e802746bc08ee535b655aa686ecd93fc9670ed312220f975479280b48834e6a8436437c3bdd0fbd7f96dd1965d3c05d76d8e48c0e026024e1a194d519297b0d6766afd0f8eb90c2959d954acd07ef744d9132479e10f6e466613e100772336e89e86020765ab4ca722ec22f455c8ec0fa6cc4613f4857a03a505b461b2dcdbf6b8e41d6c3c2c515aa6e3d68d4cdd82ee1e3ed8f823fae140a13f4829a4520d52c3fbf29607b821694306d95e7790851d407c41473d0d0433c32bb8e8f5144d810df1375602f1a9db33531e2311dcdb76225ef9067d00b7101d48e934d79b165eaef6078c970cf57dabe21d30af
private theorem part64 : 2 ^ prefix64 % Spec.Ffdh.modp4096Prime = residue64 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue64)
    (e := prefix63) (a := residue63) (b := 3559559381) (n := 32)
    part63 (by decide +kernel) (by decide +kernel)
  rw [show prefix63 * 2 ^ (32 : Nat) + 3559559381 = prefix64 from by decide +kernel] at result
  exact result

private def prefix65 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (64 : Nat))
private def residue65 : Nat := 0x98fa426da28af85362d20b5da66f36f9d9a09521db04e16c312e820017116f46036856698b6d74dea6544906c73ed46da967aec6be209f18dc8fd41b7247547fe903629c9e621ccf12805ba76026eabbe67f53226069c77dc60be74a70f3a6e9ae938e69ba8167884f078a86a159bf740a784b3c0a6d636545a5a05a52c1bb6121da71e2751bb5b1cff188ec8e5be4af9f723de89c9ef822ba3b9586f6ef1c52078648feae11e171bec85f4b675c9b8a473dd0aac356dfc6d1ae49c410df2a63f118bbf121732b5c0ce50409ab535a40c6e541231b0ddd834b538fc49090fcad7a22c5e2cb6f7946081fce64b009a65416786731f51f1445a22103173ad17e697bba4f6086dcd0da23ba390ba57f7690f896bf945389656e519d7405943b3786b3eadbde0e7c7b22b4a9f8bbdae59f772dfde4b75a3d6313bdce7b4bac7e202a916bfea5c1bb1e292194aea07cfa03842acc19877ee3786bcc7a18696114690fbf3da9a8e3dac4351400c1812e33cf904fc31cd9e03abab2f1d442797fde94ce50e80b9de0fa596a9c5feb3f8245c33ca655566103211b5848cdde0809bb8c11f091b052a418ee3adb08e458bf45ca3e5da426d5a7c9f33b452b02906e719fdce2b10721412709f9a7b81a66f49f414694daf2093a982c24dfd76d9de0ce91a627be1d04684ea7576e8290a5751b06a826b31e4d76ce7af26991060be8879fe0
private theorem part65 : 2 ^ prefix65 % Spec.Ffdh.modp4096Prime = residue65 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue65)
    (e := prefix64) (a := residue64) (b := 4019084594) (n := 32)
    part64 (by decide +kernel) (by decide +kernel)
  rw [show prefix64 * 2 ^ (32 : Nat) + 4019084594 = prefix65 from by decide +kernel] at result
  exact result

private def prefix66 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (32 : Nat))
private def residue66 : Nat := 0x66ac64d11be393ed78a8b126ccb836c77a4b1ebad87eb8d2ac2b75f9ecf0185a5a166ec9ac392441253897b1b0036d73e51f095955fd040e614edb3d461487d23c0f4d002b8e123cf15b2f064ddb2ed52c3015ab159e184ec49452a9b9099b989c694e486e9a4d8ceda98a1378fc8e904fa544ca5129c426ad5980226c87c11a972c48232322ae6bba116fa66f6b29864f06eef57af84e3b6f92c0dc3d2bfa45ba2cfdc210ae8ac005d5665923c6caf0d52c94534563c1970e2e76d018c2adb684e89832310ad8256cbcd9a78c35d2fad39f913f05ab9ec759b76d7f9955affbe9e0880098ccc0048c4c137e7a3a3f64b5d3b800df8f1611fcc41ae515c30fc0edef2a94b6a563296df1ab7462844318702edb0d815b66c08cdf66a73f6d416b25129848407ce69ecfd8d1482d8e624061f87de41f60ff6032c6fc676ff0b8d1aba655c5c233ad8d1fda21e61865809a73b8b03d99a18677f25a542c07fe1fcd899663f7a0fe458cd9dd798c67ce16ec8899f41a8f421c1572eb99d4d2a963dbaf91ceb49509808e79b87d654bcb90c89a279b7459df5058ee2b253156603d61f6ded1454908c26ae6b08e20fa2c8edd674558f289079719c9492ba0cd1ecd8205f5876bbd1f8b8844cb53dafeb6cea4072149d37e63b1f251c93fd69b9c0ecb1f6cc7ffb55d15805f3ec9d6c25f13434a1a0e6bca0d59e40ed0bb1ce103702b
private theorem part66 : 2 ^ prefix66 % Spec.Ffdh.modp4096Prime = residue66 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue66)
    (e := prefix65) (a := residue65) (b := 1987953282) (n := 32)
    part65 (by decide +kernel) (by decide +kernel)
  rw [show prefix65 * 2 ^ (32 : Nat) + 1987953282 = prefix66 from by decide +kernel] at result
  exact result

private def prefix67 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (0 : Nat))
private def residue67 : Nat := 0x97f05e1ae4d84c35a426513dc7ea05c19fb884f3a4008265823249d257a32249569da90df39225b0a3fc169231cba295ad1da00ccb547e5f8f9ed475c5b22ef6905d0d7f4b25c1bcd2c4659a0b02ca2497184f78dee200bc09bbf19f40d5cb0f1f83716cacc2f8ae0e77fd6fc849e9686c8e19f85cdae0de9196b81ec0b454795cd1684bea8c305727f5626e12412b0a95e246d1809d34e80bbaf1ade94cb5cbf5c81f57aeb37422358152ce5f5c3a89827d383b31b2556a3452c2455a80200b7e349dbc7fcedaf1a007f1ae707a145574270b2ff72dca8ce7624a99283e1e63baaf33c8ebdf0e9f0cb7bd793216311cac3c8b43b3f5ef4f77806a712d240d7859bea78b67afa99aa161688cbb748290b62fff0613011fd1fc57701b26b3cb3c11ff2f61cbc83b3865429dc9bf50e7f69455c3b503af68c5b4ed7bde365f0b0e64c02b5dffbf1a3ead660f59aa785d0e485ac6e2175adbd37326ff488aadf92b04173349a97e7a3df7dd9d778a7282e2a1f0b80367b060240885158f1328113e4752d2b3f8a82bacec2a84e7d27d7a09eadadf0aa7cd11ecf35035183bbeb163941f9d3884a62c366cede848d5edc72fac13c6d601338f70800d544a4a5af2aa0638d3f03a5580f886e8382466878a964627db070761ee3ab4b6f129a8fdf7ba1a0584666a323f6472b7760cf912fe5ded44995757e5df232720c8bcfa9f4bb0
private theorem part67 : 2 ^ prefix67 % Spec.Ffdh.modp4096Prime = residue67 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue67)
    (e := prefix66) (a := residue66) (b := 745404293) (n := 32)
    part66 (by decide +kernel) (by decide +kernel)
  rw [show prefix66 * 2 ^ (32 : Nat) + 745404293 = prefix67 from by decide +kernel] at result
  exact result

private def prefix68 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (96 : Nat))
private def residue68 : Nat := 0x67b1e4b6c7e584537234edcacf2c7659a2f61301aa4bb01784e71858d8076cd88d461c75807c2792cec8c27979cc465809eb71c45a84016f00f491595fe6e6ea2551a0a7e20cca47e4eb140c9aabba68ad808fbd88f01ade0ce06fd1ca444c72a6b97f1bfec1ddd2837cb961fc39a6cc5f60a141d81507991d071756e635382000493570b52c299214ba55a904441cf85b9e2cbe24d6f4f4fd016523929a446ec9d427f0b26c193c6f0d335a46493f64750765fb0a795dd75e7d9ea9dc1ba9a7c9b1be5a31962ad32740af1467c78d01120bbdfc933129884651fbb92791af4aaf613239d9a4b9828e4ccf4330e7468f4b731908070660bca86373d783aa3b577b63587c4353da91f6867cd0927858bfe656bbb1a708084135d23c69b818a0562bcb4074a199aa4a1d1f535cbfe728cff6f471a8f56da71aad3faf5a7735b5c86c60192c0943cc46758028963b17c0b787389f3fe29eb9633c6ff57c61ebc13fd921720a1eea6e8159bf5e802d9b16bdfae8969e0f36544ac0315d4819117480bf11c79a236c0880963a3168296fa51cffd4eea71e80f3d5d8b1bb707d5ae7f71d85bc80d2fc9f75609472e010d24295f0bf8751fccca2153dba001fc77b8eecbfe4aed8ef9bafc08c1be61e9cc9a28c5f47ea82d2f29eb6dc48142283880d81401dd93baa176a2f9a17c9130df25810f9d9ac418cbd874dc18a5aaa7f4e5c36
private theorem part68 : 2 ^ prefix68 % Spec.Ffdh.modp4096Prime = residue68 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue68)
    (e := prefix67) (a := residue67) (b := 1165310123) (n := 32)
    part67 (by decide +kernel) (by decide +kernel)
  rw [show prefix67 * 2 ^ (32 : Nat) + 1165310123 = prefix68 from by decide +kernel] at result
  exact result

private def prefix69 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (64 : Nat))
private def residue69 : Nat := 0xb020a9dbfc750e4cb6858dc1e9b55da77e7bf6921577dfa0a2c5f527ac3484a6c95999d5d1a9c0e6f765544a39ea7c72bdcb83858f3b42f196204103d49c9ae0b9240ee9f7caa7d328e2ee8aaacc984d739f433e3a98329d6a79b05f41868e50d3037941e572a76e047897656c1e65a6b091d7f846a8562740f30017632081a2b744a4d5811e6ad7e4c058a41a19affcb068d66384ebbd8319d21fc64651b0a1b6f561c38f82791e231a14735f53ac95d04bc6fedcba6003879392951f01e6d89a96f71d00b8cf8b710b914eb5ec287a9d803daca25266b6764c45ff0f9ba4482e296a60a45d17390312f4401391a9f51f284bb1a023dfcb2ef9fb3b029000fb807402ed804f776d641001284b2bad9aa8e985fa905ad264930685012f4f773af7ed59f29e69dec02d55e4f87d294d36f60933ea514d1f43d5317a055646017dcd666b677b1bbe7a4ae2478e837d39e42226a71df0834655ce35b8eb64ae8fb6d20f23a488972a89665a5c2d323ecd395d0cb8f730f2db5eefe96149d6fe0b2bc3010fad1320bcfa136a253df5b0f7370c08a8e4a16b2ae682c0e4c29fbb3cadcd570745ec6712775a8aef4e51650f6c7f4c41ae2eaaf66deaf6bd1fb70449e15726f58d456280494a58b1c05865ccb1b296e9ef6fa571ef26acb994387e483cd36767aaa639e08e2408d33346789ebcc419278cf2bbaa54f1567951fd8d656c
private theorem part69 : 2 ^ prefix69 % Spec.Ffdh.modp4096Prime = residue69 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue69)
    (e := prefix68) (a := residue68) (b := 2927822398) (n := 32)
    part68 (by decide +kernel) (by decide +kernel)
  rw [show prefix68 * 2 ^ (32 : Nat) + 2927822398 = prefix69 from by decide +kernel] at result
  exact result

private def prefix70 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (32 : Nat))
private def residue70 : Nat := 0xae95a0b9718f51808a4ec0e69649803b625244a5ea9f6e28d684bdae3e5724ab12d1719c1639af52a5e82f334a3db5fecb9463b7acdc4d2603c29edb98b02de34978add824dc6fb0790af797a886f49e915152b2626e684b3931ef88955df71076a813a21c4fd0cbd816e1dffc766cd80d51c607cdfd27da208f17f3b248ef2a14ca07688b8361b7308d80e5dee08144c93d200c437cebac41b1fc6981bf4b95dab76ce595f866d96a1bda00badfa4b791271814140ce004809a84438c47be5d136e50aacaf4ce8ac5434b3e39566fc12d5b4a93d8caca856eac12e5e86cccf47ca67fde9353e98fdae757278436ccda74e33c98404053facc99140ad71473a0cea8086fe37c2f2f08de32846a626b52cc55d24a10fed1730c1c158dfdc464a9244b8cb0bc311301d647ec99264748eabb945cea98f1e4e9c4cb755ab0db777e4a61d367bcaaecbe574060c3804f3d3ff926dcd357d3383bfa551ff8ac86d3dfa238614b6a9fd9c678a324b770ad15d25e2d3b204aa5d75b3eeb99b323212790e50727d4effe3e0c6fcea4002e569136efed090b2068e35f6c4dc2f815a02cb4a3ab02c6883a04f323ddcfc7109515d1e0276b01f4dcaa02bd4802b88d014a350f819dda1df938007e949dc087c90b4bdecc06f95b03f3355ca30381b2f0e16c2b1798ad59d0dbbf104869157b6cf623151ad874a1a42094e208b3676b28f09d
private theorem part70 : 2 ^ prefix70 % Spec.Ffdh.modp4096Prime = residue70 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue70)
    (e := prefix69) (a := residue69) (b := 3653994434) (n := 32)
    part69 (by decide +kernel) (by decide +kernel)
  rw [show prefix69 * 2 ^ (32 : Nat) + 3653994434 = prefix70 from by decide +kernel] at result
  exact result

private def prefix71 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (0 : Nat))
private def residue71 : Nat := 0x99f6ce330d20623336ab2595576884cd8b217699fa0a1e629c73c550b5605b4744d95ef004641de4a49024ff9dcfb6bf85c476c27aac75b3311158c5117dedf8e5cf9f0a9bfd0304decc28246aec35c878d05139935cf87db9f40f0795f817e0d922ac535a7a833cb2e269b611e2e541765002ceeef1bde6257d09526e642f2fb8a6a16d5531b89ff69aef8bb28eb5ec1af8b2d0b3559fc6d14637ebb64a1cbaa8223d69e03101be61d4c5a809975740491beecd06f907fbf9fecf2269d1ba87ddb093b4e6eaf88ed18c75ce9bfa9d2fcbb5a34166987b49d42fe244763d2006ba93ab31c398c9c4e86d00632bcf9ade0047ca05b76c0252503b399b87cfba2406940ed7bf982b252397a3d0c54da0271a893af3dbff7d9e7990dd4b340d70776f58d668a8c25a86289aede4768151983e36d9f4ede9df99d27e3a4e214b864b38e35b3c571806038c7b728ccd0845184fd209028a790588853544388d08b331daec05046f5087e47d32edbf71b73a60bb2fac874fe9b2500700c82fb33f4ae17c8c95123b2450dc83106b461e07b1075297f412100decb880249c56b02283d7ad6c5a82bf06dc92ee2d7c841226175f2af074a5a28519a682b16dbc9577a4d2a982ab3b9f254bcc3ecaac37981611d41d86757f0aa02a9e13c8bf8076a36f0080e13cca3e523b890d6377dcb8c8979e84dcad9f87fb48ff189097cb3eca7555
private theorem part71 : 2 ^ prefix71 % Spec.Ffdh.modp4096Prime = residue71 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue71)
    (e := prefix70) (a := residue70) (b := 3547394659) (n := 32)
    part70 (by decide +kernel) (by decide +kernel)
  rw [show prefix70 * 2 ^ (32 : Nat) + 3547394659 = prefix71 from by decide +kernel] at result
  exact result

private def prefix72 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (96 : Nat))
private def residue72 : Nat := 0x2d1af038ed593a4d6471d9f3bc3b0ba3df5ea2269d992d6108ae0025190367f885eea7e20d1c75693710de15bf43187ea390226275ffc27970d0c428bca8724bcb645fd213d21aeced4bb6c6fa76581598d7389902b029d15bed3ecf6644731d4e584ce9bb2fbe28feed02030f150ecf447930afead4a453bd4b1e756eaf88cd1768bf406a27825fbde3501fb327767c423a36f4aa523fd279946ad30854074d422d385ed6a69af35c3fe3487594ceb16e701646c3ec8f3b98066f2fb5223af6c9d551573362699882767e69941e064eb87df4c9fd3d7464e50f9a405e461a72151d1ef86f49eb7bca1d7f0969097dee01010d7b75c4ae679135cdb8a33161075346b7bf02aea8f4e9e786befd00aa1f3773b98f3b3ab5f92542269b19fc4c18808d82fb4632597026ed806cd38f2f13c0f207d893bec17dad7d00087477f9c47c70207bdb9d7cd9de8cd3d3f57a7858ee8d03a016da013daf21a1d2999ee68c572ed8bbda46a3f7e818341b1eeb3a7ba5fc5628c913744c46484411e81374ca068a25de2d3c39ee122030ca75c49bfb2aa8604730c9fae53892bc35517c60ec04e26a46f68f29f4e8a2bffbff9a692bdc050e5293f7db00a801e113004646a58cccdcb40593ca3d146e8d87200a272fd5316e4bb3aac595ed87b89f2d51b16be738769c0e2528be909d7ce456e4c2db40c14d9caf2458effdb640fd587616ba
private theorem part72 : 2 ^ prefix72 % Spec.Ffdh.modp4096Prime = residue72 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue72)
    (e := prefix71) (a := residue71) (b := 3589986118) (n := 32)
    part71 (by decide +kernel) (by decide +kernel)
  rw [show prefix71 * 2 ^ (32 : Nat) + 3589986118 = prefix72 from by decide +kernel] at result
  exact result

private def prefix73 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (64 : Nat))
private def residue73 : Nat := 0xab653debe4d0a54de19319b11830ceb0a586d5adb95be1d54e0dbd4b7a3fe510ae3af5da567dc3301f290d6fd064a840d0d76dd5ca4b4da8bedb81cebf767bb00ac3db13146ecbe408cd296b497ed949e344efa92743624e665e5533cfd5602771e37b88fdc754d35ed6a5f0b865e4d0c0b5d2d99c8229b68b54ee3fa9e408ff87ab8ddce6653a0d3dda8fd7ffdab3a9f53b1b1f5f0531a8e768dea8e91e711280a3b20a20dd667aa540f7bfcb94646f85cf08cbc111a9c9cfcedeadc1e53e6b74faa2c257f857dd1e957fa79f21fc28a8bf6734b8317e1a64c5dfb0c87a863dbb4ecfa1000a3f5bc6a0da4e530f1568ea991afe6c5700002399eae65567d58ed4313e8ec95467e41aa8d48dc75ff5a59e399c8c390b660909926e4b7eb363634154dab6ccc6eb60ba133cc5eec6f3a11663b22fc5b96d0bea268d9ceec614465a56894af38b404f031c2ddb5e7dfdb6c4f6ce95030c595f09b0e45dfcc9b0299788f3a1a626c50146ef5cfe79a914732e7607d088dd1bcab9f2d13b669018c285e0ccbd0eb7c9dd3c5d8d2a8843021d1b602551bff81b25c25b8b4ec4d0029e0c32ad4d7ef7224f61fb506152277f03709e5f0c06f376b9de88eb4768201e764432c99a0452374704be52a54165a42b27b96fbc1e6db0ddb8c9b3474d0e46e1df783666a457aecae185b3e68bcb9f17f760a6f885d9bd118614e1201bb78e7a
private theorem part73 : 2 ^ prefix73 % Spec.Ffdh.modp4096Prime = residue73 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue73)
    (e := prefix72) (a := residue72) (b := 1837406699) (n := 32)
    part72 (by decide +kernel) (by decide +kernel)
  rw [show prefix72 * 2 ^ (32 : Nat) + 1837406699 = prefix73 from by decide +kernel] at result
  exact result

private def prefix74 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (32 : Nat))
private def residue74 : Nat := 0x23d62cd856e59ed52fc360c5f5180614f0015b6c8ea66d0ad734ec69530136652e9dae7eb21af0b587973bf20fe153b659a72732b105819fc9368153d0bf553df8271dee66e8384027e7016faaf8f5371b685286fe34e6e49be90c07ca8c10771db51a49a35def369ac41ff1881a67d5fcf7ece2c8f3309e007a1260ddf507be161185932ebb5861c9c28dc03569ff24eb08ed23c127591f4ce537b95fdd58e741484ab041a2dfbcc56c3d53192c063a5d48567016d24771934adac2c437a546c20042f11c1ffe6f321236d7ff8b4494a8e164c76a5efaee3a1bdcc0d3b0fc7dfa8e99f8caeb8d1a91417981f62212122f6752665ceefa44561d29e601be98c562a732b71d7ef17b43b59571ea664d1e7f5d524880202351c9895c84a096b4363ae298b7c445911b82b3f41c37f457c07ae80f0aee9f3854470a834b2f1ac5b87e6ba176f0ac9e76d14a9e43beb9e9ef2dbbff48deb91e3a67beb98f1f0b70c43827282357cd9a4ac3f8387157e646c6f2c399a35c0b45db253617a3efcce5aab941dfebbb182ea85008a12dec81cd78d561f7c84ca8bea3947f1cc23eb1052e49070cf08806bf39d0d59b067294a20e6272e608ad0e9b74bdf9cf3d6d15b1e23146e05c67bee068ef2a30d87d31225e2befec3256f195a3fb4bf8fd86461d0297a0da5f6db1387bcdc496ed1807806489b4489a2f350e5f36366723aeaf44ae
private theorem part74 : 2 ^ prefix74 % Spec.Ffdh.modp4096Prime = residue74 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue74)
    (e := prefix73) (a := residue73) (b := 2403748464) (n := 32)
    part73 (by decide +kernel) (by decide +kernel)
  rw [show prefix73 * 2 ^ (32 : Nat) + 2403748464 = prefix74 from by decide +kernel] at result
  exact result

private def prefix75 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (0 : Nat))
private def residue75 : Nat := 0x6e728da3290115fb564bce41af93d03b6161192557497bc5e766f27b5acc6a26e512e35eacac346be1ca80dcd50ec77da3946d33403e8cc0a88585805a6f38b23513c730f8156827fe25b7c9bb4e8fece4fb27fff90afecb3461fe51c564741c90ff374f60c38ed273e417a07d44c3e0d1eac90c5cea7fcc0c077b5f13ada01481b45289ff36cb2fe28c02843db60f9764901c57d1733663f2de50cfc09b51e5afda4cf88faf3175a88dc0fb619ae61b57f62b307cb8a75467fcb2690ccbd746ad22498b1d1a59c6b1cb0f1950df9247c86db8943572deeff9aad135982602396ff3e10cfceb8d5ce6517664aa330c89f541d11c8bbb7ce973ac15f09d87f88a63482feb943255d09b16576a4dee876c673d381999d2694f068864f7a06a38b0c4ee70fd8aaa81f4c81220237c437bcfb2289224d3c1258f22df3ad0b7a7d39333e41de764021612ef85c28ca35479aa9f8fe4942b898fdb20bf3272077c1416fef63dc27f827811ed44cc6e28f35a260b6851611c8bf4f86290de0119d44e89e26ab5d7da69f36c90b172acc64dfc1213a1e4108c2b81e1728bde8a0dbc81e4df2246e8457e17b87ac38c29fc6456a30c535f15962310570d1f4f395d852ae1c917f3fdbbd61c5e00ea9c83cb597c999936ff7ed10b47f1915e11af74d6625b7444e3a8120504f7507961484fdbdd0ba5450c33c29af78005b1d2e50317fc2d
private theorem part75 : 2 ^ prefix75 % Spec.Ffdh.modp4096Prime = residue75 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue75)
    (e := prefix74) (a := residue74) (b := 621981902) (n := 32)
    part74 (by decide +kernel) (by decide +kernel)
  rw [show prefix74 * 2 ^ (32 : Nat) + 621981902 = prefix75 from by decide +kernel] at result
  exact result

private def prefix76 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (96 : Nat))
private def residue76 : Nat := 0xfeb566c4ea0d860c0d28d9a8b5f4588248a29eaddfd54799457a92a8fdaf9b2ca9594e22b3ad6f44f8c6ace37f61ae1a98d3deccd66c39685ee9585dab71b1ef13ea2831939cd402c51f28a3f48f7be3f9d488d2dfdde9b6c6dfd8dfb9a7c2ce1d88f9b1a62c135bd823e244391820a4af0e8557623665557d3516530c97c35edb39b9378143649cee5a01c35bbfdfd1ab018f25b9bbe9d09bdd5a6980f85ebeec2e9ee95e3a78ad1206720a879347fc0531d16bd9907829ca65a4c40ed8163c63314096e2df037c5ef2ff42f43a27de0fd99a0b2764ef37be7dbfdf83780cb44953b11e4232bd9e6e0eee7f6a61e88b48cd7bbbb988424f240c6a7b075b1601e98ee7050800a2980a89d0d1ed99177cc455ac2bcd5eaf5df6b708099e088112d213cdb0e4a0009a9ab4ac647c4404dcd731d7141ed1b004e21309dfa357c50900a19cdc8350330b17fb4dbe3c41a96ad8ed8d3d20845cb65e493a0403bc0807adee04bf817635e9c2f96976a3cf31056c88df707e10a2d85a2d148a8da28921c542de10feaf9a35bf5a63a958c262d5e4182ea4dba9981066ef73c3a61115381ce3c48702af48e6d4643947608750d717265dcec6dbb325b695cac4b11c04b6de46965d5f5a8313fc35a45bca5d94faaf591c50aaf686b9216c5db80d4859433ae3246e7d7339f3e6a583788c99e45a857c2ce2e7613705e2fd51faed87897c
private theorem part76 : 2 ^ prefix76 % Spec.Ffdh.modp4096Prime = residue76 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue76)
    (e := prefix75) (a := residue75) (b := 3883002131) (n := 32)
    part75 (by decide +kernel) (by decide +kernel)
  rw [show prefix75 * 2 ^ (32 : Nat) + 3883002131 = prefix76 from by decide +kernel] at result
  exact result

private def prefix77 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (64 : Nat))
private def residue77 : Nat := 0x9d5ea9db81cb5e2524b10bd90ebf47904ba5635f9a3c320102ccbc9341483adac109be3c49d5c402d6a4e3cc269aa1c9da1953ea5bec937fdc7cfe895682029b91a48f98932a4a17e72b2b8a8442e45fe1b37962200aaa07b224faf1ca440dc6888ab4a365fa46a713ed1291f5d43b31f189cd64a61b5d055631f42b80a04b0fd1e5c2884b53b5739e2bee951312b91d82418810ba8ad1f66b0398a657c4f017294e6834395fc71ee7a6a59ca919bcb16c92a63bdbd373dd30a4b63b314b1cbdf9e9bf743cef6e853f770126d2693e92dde9334f616ecdd705a22fccf39c62a0606cc3a2fe6605f47daaecd99dbcea9ec6612a27832dda59effd628c3faa7fad69b2c6a8c4680943d1dc5606ed3b609a555000eaa71dab09498b86a7678b94d582565b94f94c5394ac00b9a6d84e2b0f334553d3c04e852c8fc2aea50a435def9791c565060942ac143fb649974a9087fb53fee6bf7a625fcae888820266367414ca30bb4129a532ac1bd9272a8311183b69e1572d58ba677a5936baf0205941e8b8ca88192b7f2c83a2887b54bfcbb24906c31f10fc189dff1764ecf997867cdae9501bdd32cdae12d8f6b9cca60757a53e919eb5970e9ece10fd26fa012788fe20051bed59f4306df06c54178116031d5a36a2a741a53fbbe3fa4d5131ee9134dd5261aabea539a99feeeb65e3a5067180ccf2db838c98a2b449d8d6b7bdb2
private theorem part77 : 2 ^ prefix77 % Spec.Ffdh.modp4096Prime = residue77 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue77)
    (e := prefix76) (a := residue76) (b := 225015605) (n := 32)
    part76 (by decide +kernel) (by decide +kernel)
  rw [show prefix76 * 2 ^ (32 : Nat) + 225015605 = prefix77 from by decide +kernel] at result
  exact result

private def prefix78 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (32 : Nat))
private def residue78 : Nat := 0x1c9ca0727177df0a3fa8935e4131abbc57e251ff91cf54a2615a61fd7146a5a8175efe687c2c96f9f42b045e841e2daed0d4a113c6e9a8e0071204e6f31997a8df5b82abfcdc4d8c18e6e872d3db8bf844f1e9bd4a87ed667a0195e5c80f118f778f11d3b60b484ab37644439a78e1e8add3fd6a982942d809f098a46adb0f088e1cdb6323efacf5f269bbff5c8e0ef43e067ca8ead7eae215f43fe8a99ed1cc8928eff723a83316ee06bb30e07b0d95884d2ec7f26a817f61449fec9914d8ae1d9f269db8ecf13cb4a7d3eccd35a19dc84d4f4bb8b1c5675e70531e12c96445f244914e43515e2cc288de4bdf49821b9fd9ad4ccdf982665107fece0be41481ced72a76bc17e0350a218422b779cc81391e84e41e7ce58d4ec1af3d3cb4b5398aefbba27eed709e07d38237cd63d46a7a656f288546edd4500762d0e539870d8e5e9f9a11fdb7c6656b5b56d32a25f0e9945cb661b080c9a488d0a82e823a9cd9e79d1838a4c75f9919f16a30750b607b44a5644f959072e8e47029918c98ad21a5a709782deed149e37d60721dd7ae567fefd3c8c2ea9cdf5d6113bbb4a39253958d1c796413399453fe10445738f8678b5d755e751008cbddf5eb856d0b85ca966e0cc03edecb5cb8fc0525cea7357dd90dc2b21a687143600b1ee1ad3a22af1ae66f9b53fbc2b202734ad1940661318fe9868d806853cea99185879ddc9
private theorem part78 : 2 ^ prefix78 % Spec.Ffdh.modp4096Prime = residue78 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue78)
    (e := prefix77) (a := residue77) (b := 4170710275) (n := 32)
    part77 (by decide +kernel) (by decide +kernel)
  rw [show prefix77 * 2 ^ (32 : Nat) + 4170710275 = prefix78 from by decide +kernel] at result
  exact result

private def prefix79 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (0 : Nat))
private def residue79 : Nat := 0x301c2ad7b95b9505d2f5a0d6bc944c6b704272307588ef66bba0c54a7ba543b8e13a16547780f0eb19a1476fb1451c7f5ad30cb3415ad74324edee771c75ddad695394488f9aca86a75eee8a0d02b7166032c864b9c1ad3d2c64c8c27573319b7a115d9807addf9f245385bdab7b52b7edc30b8ebdc5d365f59ed321463d0f8e2c653cd199b2aa23467af3e5a0a04816ca47bb882809f42fb80dbb561ff80b85a1b36b784348fd61d979db4e0b5feccd1d008eb93e74cac58b87355bab82e5201f69b7244dfa06603cecef0be21307ff22c8f38a4c44d6701a271901eabe9bef1462e8ef8a618e88a7b574faec7cfd43863a7ce894bd03e3f42310397ad45c1a9f6da9f2bceafdc7a6f79fca8eab846e902b6503a8abfe2abdab7fad33029fcae2acbfa233c4f460adb560afba85ba518996e0baaf768e323c861ccb53211e9c166d5d3424ca3f5d74d503e8ae365ff4ffbd277bd03d9dba73df01ed1b991c03a824f42c8185bfc680d3a453b4c994a85805c5d99cf2a8ef503397aea61e525900e9e585baf8341bfe1acbdd432f43837b4cff35e9034b3df875be2cf4adea4f3dfe92738a8e3a0e4b5109e8a57263c9ad32737dabdc09cc098644e201f84bac314dbc4074ecaca2c32f22a709f7193ae59cc752fb75e9b8ccaeb9f8936dabe23aa632430e2886cfe17358fd5f4dbefc2fd765510a31cae93909274a5334eb1b
private theorem part79 : 2 ^ prefix79 % Spec.Ffdh.modp4096Prime = residue79 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue79)
    (e := prefix78) (a := residue78) (b := 1824850994) (n := 32)
    part78 (by decide +kernel) (by decide +kernel)
  rw [show prefix78 * 2 ^ (32 : Nat) + 1824850994 = prefix79 from by decide +kernel] at result
  exact result

private def prefix80 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (96 : Nat))
private def residue80 : Nat := 0x22c4b75aee0cdac35c7fa71b216161cdb59a2c7ee4b9c8dccc82f60b5cc978961943594703d8b6f7300385db08c22cbb1582305f6a1741d80cedc39943efed1bc2285929ff1081a9b36416e4757913d7aef52d57f28f16f95089010d9d52e32343b421ac22fd10c81e53edaf1cdf3be97cb7a295f24bc096e3c8de69c6b88227b9e5df22268761b5cb737ed6728d883d1c9428a1a2f1c832cec778b20a12f12c2f1d12ee696120d04217dfa4ff5589d51b4d81a1f24635efbfcade5366d60f0723cf39b46e173f70b6957b293ca479ea586b59e8232aedc4950e29fe23b425ec9150aca4f8798cad9a4c4ec75a4c5470f44d1248b994b37b89ef976a785c1c0e9d42449366e521527c9efdc5248413e554c7ee07c16644da752ba4b2521a3ba5287b70c952568fd368150dfe90615669d177f204cde365362045d72f5de03c89b3b357ccb785c92f7c66f45b33c3eb97cf382c59dab17e43e28ae129258226e90a329df179c461a0035d1176048ceaadf768141fd8d91f051de39ae835ce979efa47a83cad9be175ee9e3ceb9ead70732966595bed365ae37879d57772932bcce275bbeedaf398cab4d2eb69934f8bb18814c36985d50d9ee55fa8cc4e31ea96f6134327f79a7cd19b50abfea68193c3b381c0be47908d621e1c160a99b2e654a47ee75aab7a5c4e915372116d1e4a75b0539364d0d169e4abc11ddca1fbd916
private theorem part80 : 2 ^ prefix80 % Spec.Ffdh.modp4096Prime = residue80 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue80)
    (e := prefix79) (a := residue79) (b := 1815806265) (n := 32)
    part79 (by decide +kernel) (by decide +kernel)
  rw [show prefix79 * 2 ^ (32 : Nat) + 1815806265 = prefix80 from by decide +kernel] at result
  exact result

private def prefix81 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (64 : Nat))
private def residue81 : Nat := 0x50bd93e3842d5d187c437303955fae5c435d8dc81f64410946504f00864550b450e8a14c4270db95cf05526d01a9caed138cd72bb52d80f34364b4ae48c787cf39ac20aa7c74ec3e4684615bc73a89b7003843a496a7d1627bf5bfe33c199f98eaee51b18facaff8e33a903a3b5a415b372ffcf7ec81ded76be4da5cba09950f493e20ff8af3defacbe58dde8be2d587571bc1b633958f8c14e20b219954f28c7186ce5889ec016208df6d056547e7d2b4f1c281508f68e75655231dcaae4b76c7737e5344702c8195817eeb5de1567e749737784495acdc9b2c9f3ccae99d52c498051649d93d02d0edb303617d7205f86df9911603ce4f0941b5256e8f1a158513e93aa27f2e0c99c63f2987cbdb85d3d74aaf4935b40d11edea79c7ec8018464495e7561d143e863603784c295f3e4f35439fb5253d9f5ab4421e94f8b36a96d2b89b4d8f889656820140c83bde52d0f5a2f281a47842c428c10d4a96113b57ec2ecb3a3cd17f3d01a95a773d459261641efa9ea2ca9d7f55aad4ddaeb91c93ddb67e6068d5db0305dd0e86db3d8995d2c6001faad52f6ce817996b7574937f0676f7196cc098829c6abe59149cad304f99dacb463c25166dbbf27a95ff4e77eb5cde7f512994b880cda873054514a6d04adb184d0bf353fcb5b585ea2bc8c7533691eab77d9d51f0f9f363ad7580b9ab9e761d974428576923af38fb35a5
private theorem part81 : 2 ^ prefix81 % Spec.Ffdh.modp4096Prime = residue81 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue81)
    (e := prefix80) (a := residue80) (b := 2674144562) (n := 32)
    part80 (by decide +kernel) (by decide +kernel)
  rw [show prefix80 * 2 ^ (32 : Nat) + 2674144562 = prefix81 from by decide +kernel] at result
  exact result

private def prefix82 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (32 : Nat))
private def residue82 : Nat := 0x32063cb793adc8944bfb0732231d001f468ab921f706f7495ff8d517a751b7c183b7dec49214568971c5e363719bf6f9a5745a6d2df7d890fa8d6a80402758b9b2851bde77bf440b52e59b1fbc8227b4b23ba941fc691a25326d3e941f85d613aa42bb2332b2736a8f34bfc8e300318e162f7bfd2df4d314a17f021702861145f7b0d0f288ab9152e55a0cbfd34ee680315e7f10796c274a54a13029a6a5d186855468429fc61c1a438557940a5504a58856573682998070534a4d6069920f77b6f93a00c519400875262eb627d891a07aa375adbdf98a132b144840db74bff3ee0ad9e078df43a4f06a1aab24c5b95513a87fa605433a20729b7d42672d42f2edfa4d7d6cef6e8104cf7a3b3edf8cea1c81d406ca76c5be5e2dea2d3141960ad635a31621acbb3769e733a2c0475327522a0c4d406703eae97e2cd73b6004495e4ff98e7fc65de1f8c109c4c29c552d813c44bfd8877862d8034e043967653d9e868700e3ac2829e459d706a9919df2ec426b94bddc73388df02f8b346065d10d0abd3859e8f68f0c0a814fa1907e61d2e2a853ef728df08a7a0e1609524e448b0b19d200f888d1162ad7608a462fd9a68cbc560ab21e157c43034fb61985df681e2f2d721a6fa56317363fe61a566f30aca7c5640d992fb9ba9457423bb8dded4613a9a76dd184c9a49a140df49c5a3490104cfc76afe7731922422f410670
private theorem part82 : 2 ^ prefix82 % Spec.Ffdh.modp4096Prime = residue82 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue82)
    (e := prefix81) (a := residue81) (b := 688887180) (n := 32)
    part81 (by decide +kernel) (by decide +kernel)
  rw [show prefix81 * 2 ^ (32 : Nat) + 688887180 = prefix82 from by decide +kernel] at result
  exact result

private def prefix83 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (0 : Nat))
private def residue83 : Nat := 0xe1c0721e701df9c9a2c27facdfd9c0d47a14d7f73f827ca89e56ea2e2e03b8edabdb7009469baf290344796bf9861c261a8905ac5d84539548455fc28d8780ccefe836f9c4abbd92eff7b51da3214810ec3ff33b0ab21931cc72e8898b9713732330fcb2e6612ac6b5c0c8762b32a996d63c74ee1f06d49d31f6bd5481f7c37f0cddf35aa3742234dde4ef528e5354b642c617b45c34eeaf3d2c97ebf4decbc8dc5924cb694ce0df8aaeb2ec9a8b7ee1dbcc121f393d68783718f37eec44ee602d16e0ec06a0e64d7119f7f52d703a4bae5855aeb6b0cef51d04c2256c1c7515d2c6bcebc5b0a1348dee99e92520fc675ebd962109d98933785212bc0fd398268e8b537eb1bc504d526daf56b8545993f630c1cdedf2b85a8cd85d2e1c255cabbff72f4b233dd72833ebf6e9b6438558cc10f87bc165957be3d596c07b446c544d3ef73902e44dd87446c1e7c7eea86613e4155479749bef5e0b4c22b1f5c8543805637cc675c1a76abe1cac8e7b57619e186b070471ffeff5162744c84289c43a4762e6baa3af1a1165f496e321f49d30399176642d45f2ee48c6635cf3f7338ea36685a2b22cae3c8deab0c6e6238d59f7ea7ecedb98b001df16016601aceff7d6d51b939dd57eef0d1008a980d2b17da02395a1b771b3ca6f6feabbea444a7b958b7efbf9573d0f78ad5baf98ad2301f1f177f05994a1972cedafb9ff7e8
private theorem part83 : 2 ^ prefix83 % Spec.Ffdh.modp4096Prime = residue83 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue83)
    (e := prefix82) (a := residue82) (b := 196972550) (n := 32)
    part82 (by decide +kernel) (by decide +kernel)
  rw [show prefix82 * 2 ^ (32 : Nat) + 196972550 = prefix83 from by decide +kernel] at result
  exact result

private def prefix84 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (96 : Nat))
private def residue84 : Nat := 0x311125122feb37a39ee5bda1a8cea0ebcb83acf3ee84250b6d23323dd42291fb61d400866bdcc727653a7733de2c93503f64998564a954b87652a6c4ef55c3f029b62720dd985a89622c3941952ea864a934e33e53ba75e9892daf18d76bc192b594e1927e7d9bab044716a7d4494384e268dc8ed737df3629cb66001cf1b5b80947f022eae9881dd60764a23aa7bbe133575736670c4b92afe5844a6d827d6dc50e41976e33cd6f0b8d5d0779ab457f9171e3ca43d4a2cf9e760625e0885072a8bab074945c38b1ea5d0ce68a48fc5658bdc95793661b6bedcd5ba452d3963b569d2fc5251a9c741b5063d078d53cf192479d4d85d34c975362ae70d6fea0c7bc6c8080cc65ddd182990fa3d9ab3127348637bbcd39567ceecc5ceeb5bb959c27be9259948cdc42112330b1caf0e3db21123b26ed0b3651d7bf555195bb83056993925ca9e6d00ad2b9f9cfe0547694fa648cb9ddbd178cb9fd95a9503c6868ff8a29639991a8b13172a588bb74a191bee2208de440cbaf8729a3fe030cc7bf7c59f041c9e3caac5e62219ab70fd82e5d34e4a5dffac80067116fcaecca11e83b1da6b1e4f54165ef8f67371b2f1c63f5532ed38659f6ab417960e3a52712ea61125486ede695bb89669a2393c1a582a1c3b8eedabcebba75f44a747e878cfa260eb7cacf1ed34a88c314ffa646a9e884c155853f0ddac77d8be2170ccdbf05
private theorem part84 : 2 ^ prefix84 % Spec.Ffdh.modp4096Prime = residue84 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue84)
    (e := prefix83) (a := residue83) (b := 1576045483) (n := 32)
    part83 (by decide +kernel) (by decide +kernel)
  rw [show prefix83 * 2 ^ (32 : Nat) + 1576045483 = prefix84 from by decide +kernel] at result
  exact result

private def prefix85 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (64 : Nat))
private def residue85 : Nat := 0xadf56de9ec056e765af7c8e765135b4c534f84c24441ec2105b6df346f733e8a0d901903a830e35c15d9db6965b2ced46328079bf17402c1f82773713062285cac29f7020958fdcc0ca02e8c26b015d84259d52e149c7fd5608ab717f9149b66a84fb34fb1d51c2dc130828f1ff3d0bfe6810d8b9bafd91e0cb939b4eb222b2c3e0721e16124f567c09902f326438333fbac2817f72cafd232a81712b5d5f225887ca3acf0d9b6bce11b9acf8181699bc5ea6b03a6f9d694b719bd9814e650481f983b346ed0ae78665a619c8ce3945d2031c42d803e6f2e4b2b85b98ecca71efc9ff7d73664ba219e825ea2ac9104bb51b1e59ef26135e5950b1f4e2456c3dd9f6ec231206e6b8e0c2d5e5a8b8d6959d783d279d0e79ba72716a28738716fcbf8a59e2b2d4b175e52c16c5b21f8af62152492dc157fdaf5e3afe62840d4b79c847a6c3285f5dbc40f6c77271d541e2f22c756ccf8012f749c544ac8b59d0feda53cc6fc2781c78ab9cba4d478de8ca1b22a7be068b27e6e8850ba5db855fabdb7f78be904bfbd170f368e2f93d6ac1bcad518ec624c51350a398b3c1ef5df3232931d9650c26f224fe6c02fd63f3a160b78f60cf79a13abb102504dfb7ec576b8586db63ec8307594a46ccc079e0bd20329211b89d8150f4660e5d6cb107bd425096049789738238579f8b0db74af00434b0f28cfb1389d4c541fa50d2aa62b
private theorem part85 : 2 ^ prefix85 % Spec.Ffdh.modp4096Prime = residue85 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue85)
    (e := prefix84) (a := residue84) (b := 3174084278) (n := 32)
    part84 (by decide +kernel) (by decide +kernel)
  rw [show prefix84 * 2 ^ (32 : Nat) + 3174084278 = prefix85 from by decide +kernel] at result
  exact result

private def prefix86 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (32 : Nat))
private def residue86 : Nat := 0x29c12b34008aac9e17371c01182089b124f979baf2e61675a33cf086f2071945e325546b5923c813e081bfb78b717216537e7e252a557a43e947e7a1b504e994f0a49cc3443c30f20594ddae802677c92488852cb6968bbe58c1c09962c1a6ccfc0800c921079f3a805f912ebaa5f1aec3ceca31f3dc7ef2c09c34da99f94843409ec6b9960c4163e387538340ce82e255600b3d4a258e79de40ddc29d1135b31298d6cafe6661b9cfa68302b3d8e81894162bef6baebbfa65b0b796ac6341cf2a5f729d9c766432b63501a69929feea31ad667dc8a1633597964351c682407987225527474f56a92dfd09f3e1459cb4be2097c3521b7d8783e40f16a00b52ddd781c0cf729d1b89a2c634cf3c65b51a1fce117913845fe5bf66b57d0e2f3c94a6cd638788e14eb2d6b662ff6d50bad0e04cab3b732062ba602220f66d4a19f56226229164f8088b1dcd2472c30f4ebfaa0a439124cd8c83f0a2a33604e24f8ddd280407e943448639cdcdd28c18d60d2205ab25af8a1a817ab0e0b7de847dfe54da78bce9134b091e430b3d15ebca0ea98b92cbacd583eaf133a39853c3d924c4f4ae96d3cdc95da446b528475cee28266c99528b1c68df665d288197b3a4c5c152fea390f3c33469139ff64f05e608dfbe856d8c9d0b852d99bce71b8dd386babdc355dd95f8391c77c17e3a0bba6e0c347e8f778289f86172e29a41678c09
private theorem part86 : 2 ^ prefix86 % Spec.Ffdh.modp4096Prime = residue86 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue86)
    (e := prefix85) (a := residue85) (b := 998556768) (n := 32)
    part85 (by decide +kernel) (by decide +kernel)
  rw [show prefix85 * 2 ^ (32 : Nat) + 998556768 = prefix86 from by decide +kernel] at result
  exact result

private def prefix87 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (0 : Nat))
private def residue87 : Nat := 0xbb86e7c085ae8a1afe7648d4816604bb7b411c2ca779eade207e08376d06895692b6bd4258431a7ae5f2de9684211e41f2c91dfdc09224a874e0715fff85b4f2c2d83a1473f00a6f5e6d2c6a7e9f22727738d284a75bdf38e387683cd1d5d387a9e370088a32d196cd4733d5018ff76cbfe6866b890e961f6d02245a667d256f62b209951d094fcf00afcc0a56b22962ef78c47f4a84224069861e08b312727535ee3fda41a1d4109ba27eba4d49d4e6bb8e0e5a88b5c3854748f625560701f6370da958c8bd44c920887484176840dc7665a102813c5afc8e68babcc3de2e0554ec0f0ecf85d23911155122d65d030fd866a6759df88ca0109e375a0c3d19f9a97a1b137123b8c810c4b4fece1f35d3adb52328e538414ee1c19462e0a6c0491a6d895e83e5323e994f76733a8c581f63bccef1e51daa7cabfb0519378bf2ec3e8e247f9192f7c44c0b141b78770ff50a2770c00974f8e403e7e445aac2ad8519f65debafe8dbb5bb70e507640ef940b71d00a948a69fc3ae58da0df6c9c46486efdd4cdf32d67c0f015abb86e15efd41ced8b0b608ce0a023d521934c30aacd0af01ba3bdba6e312558f2eedea8d85375adc07f6a51cbbd7ae65c8d6bdc51643aac6ea1926264e47668fa64a0159600619711af4e5766a5f886d4eb712cdca39bd1699288a54f2f5ddb816e0ea3a4d588ab013ec177cb5fc4be1bc2f030bf8
private theorem part87 : 2 ^ prefix87 % Spec.Ffdh.modp4096Prime = residue87 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue87)
    (e := prefix86) (a := residue86) (b := 1567400817) (n := 32)
    part86 (by decide +kernel) (by decide +kernel)
  rw [show prefix86 * 2 ^ (32 : Nat) + 1567400817 = prefix87 from by decide +kernel] at result
  exact result

private def prefix88 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (96 : Nat))
private def residue88 : Nat := 0xf18143ae389cb1ca49acf7f884ee7d4088eb9249cb77f517584163e4014c1de0d81f00f4de725689eef012a6d458c65cd29e58f15680076d466c37cdccfd5931a2095c9dc2c70542134c7cf32713e0862844a0f6c5449e238adaeaad9fdc95ef7faef78b4752f134f796492ea4c80d630d70a85f3f9386781e8ffa444029058eb59966367a7197c509cc8898ff28f5a418dd70795ffd54885c3137bfb11cc01c92d3c876b21c84c0d2bd8556047a967c9b50bc7edb7ed31b1b3f66383aafebc4a9be49be78b160dbbd7232e0ca63b2a2f0ee30304b6c546a45d4ef20eeeff460773f8b8489826d69dba92f3e59edcefd07d7d7d545aa7fc152d36825e9500bb53e92277e07874c9c1a1c6f418ed401177dd21443f995f3cbbe2dd7b5a48e769fecb46d63c4c1e568dbba8e6a05d5a3ee9f91f5ea7733b8e0323a27cdfa1a9ecf648c9da1167db525dc907e16da9feb0081cf3746f96f57a051c2d45efe5937127d4560f6c0273c611978279c3acf8df0d68b49d7af4fd4f0d0546c98751413703b11c2b38227e0f212058b9d89c228e838235452af6308f60ecc4c6acc7d05beea9973db7fb66868fae6e2acf1eaf6d6117f736940c69e30a4619b4edeecee01155bf5acc33c35c71648285919e215a8668d2c89fccb0e051d0ab69ae7fc7cc2311406f0609884c3f0ad042f704892a1c986124f61c7c6f82882701dc9b36c31
private theorem part88 : 2 ^ prefix88 % Spec.Ffdh.modp4096Prime = residue88 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue88)
    (e := prefix87) (a := residue87) (b := 74524624) (n := 32)
    part87 (by decide +kernel) (by decide +kernel)
  rw [show prefix87 * 2 ^ (32 : Nat) + 74524624 = prefix88 from by decide +kernel] at result
  exact result

private def prefix89 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (64 : Nat))
private def residue89 : Nat := 0x35d5698ac5759759e494fdfaef36826deff930a33c769e5a84346e7bc9d13ef0abe1c45df9a743a04bf82a1bef80f517ae964826a8423a0a7ed3b1e902b5c2a9ef016d7fd517c499ae77bdc2199297678d99f85752906ed730c6dcec78642041a926564ab2c65953f9c3623ab50e5a5a2662a01c049a3196d011a3684c38f3f44690c206e2d3a6c94cb7f0b188de9fd105119d1a4b727105733ab585366c82305e2d2c9d398181004f0f4e2f76a57a767e372bc6a95cee2748c7097f8b68bec9133ca6ac1c9fc92dcd713328b06204ff2a3dcbc6450c15d195e6e266fb0d3f09e5ddc66109e88dd290bcc95f8d9429b8ff35936e22e7b17f41b0808c8ed3940d158bc82e0199d316508eb9c8acce7dde327e85bb37160a4b9973e6b536c30e193a53f8762f8c623b37613ce804e30f501778c577a1ba9860a2b9a1d1e106401390caf8b2867618127cd0f80cfcaf0d38d6173eff963a558bd4e61401e496ac9af9fc2e39762a02a13055af00a6e231d118b1dc0ed823848f8af5c8f8db3095dad7314b5ba889512b8870ebe363684464d1bab85c47c2b06f368afa23740c402d137d46afa6e1e30c6db94c8b3200a38334003aab1eb062d115fc2f86091189b76088161ef386697063ff67b0e93ddad0483729b9df653058ef9539481ece5abe77da55789e0794d7d51e84fcc7d4a5f5ebac47386d81ffd97a345bfbc920606c
private theorem part89 : 2 ^ prefix89 % Spec.Ffdh.modp4096Prime = residue89 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue89)
    (e := prefix88) (a := residue88) (b := 980604312) (n := 32)
    part88 (by decide +kernel) (by decide +kernel)
  rw [show prefix88 * 2 ^ (32 : Nat) + 980604312 = prefix89 from by decide +kernel] at result
  exact result

private def prefix90 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (32 : Nat))
private def residue90 : Nat := 0xe1c3ba70f08db006216b6b10862ca925489f1dbf7e3cf5f6b0ede422aa332650de59f10a9934795a5b226757358fba1573419a609f6b6b80a3f5c4248c9e3edc9f4c776829eaedd873912c33f526b7995b63c30e750e910d9015a4ed3e41d205a5a3c88666b362de4864f9feeefca3a3056c2fbc6e2eb2f723aa9fa623c55a2a6784994f9ef07f433c7bde024a10390f87362cdf8eab8f2860c0a708e1272b3bb7c261cb3dd2d3994d81a72e9955656797c42ef444290d8538eff9a79a32a3bac48bc37dbaa619302530f9401223ef116e6e303e00b8bbc1a881ddd0d4ce36931d697efe6605d867d6155f9ebf000dae3e8f869748b968f8e75b2453c23e5929ef2c27b7d0f8075493f5291825d13fdc53a140e9020942cb2f927aa2590c49087dbc6ef97bb017e6c7bdbb5dd58f42151b350744170b6ad3d850db8d0b7351a9af785930a11ef448d81397e3fedb995cdd5743dd3cf43f598fa04cd05178775489508536cb76c38dcdb651c95af591c4059edf908673043e92af9cf268db79198609e7f98e73306ccc3b6350b41be5108ab322d9c8c766a84564b63208dd4ce20dc34e73646ddf2d1c9c47a511e5ddd9a672958875486a7d4bfcb23897206e4e95f4ef708c2ce13a3fd133dbf680dbe8d7fc77a8ee7db5a8ca8ce0660b7a11a7e9c9dd0668425f0f6e75e1c2fab3a58b0a16682cd615993c62573e1e2b0a3c09
private theorem part90 : 2 ^ prefix90 % Spec.Ffdh.modp4096Prime = residue90 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue90)
    (e := prefix89) (a := residue89) (b := 2716708350) (n := 32)
    part89 (by decide +kernel) (by decide +kernel)
  rw [show prefix89 * 2 ^ (32 : Nat) + 2716708350 = prefix90 from by decide +kernel] at result
  exact result

private def prefix91 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (0 : Nat))
private def residue91 : Nat := 0x53be8cd78c3e9bf73c94a82e9c9dfb964f2b8e439e833458d0340d3f400902412404c4ee1d537f84e9a49b9f7978f8e77d8e7101d049e352e67189579dd381adf2b621b2ed1d59ca889d9798055698724b36cf1e02d5c623927dadde2be0f67d926ec5b0dc9d9e11314a8ed9bcce5f791dd3b719c5945d0dba63b44ad91ed4560f557d3fcd49068667addb7a591a5fd35e77aaea1a908366b30c7a6aceb9ca40f2e6696a4f9c9f0f9fecdfc053f38d3d756788c1c125cec3757b8e94dad79ba595957ba20ff35e7188c228fa6160da34a18b1472b6bbed0e7cad030ba94dcdb7a36d47f38b43ec505698709b48949defe31810ac434e9041189b8ccaa7666d35959c5d50e32e10f2fc7b1773b2f2bede0a2a5e3b131822c7dd69bd6ecfca4cfcc7cda02853cf28e544a536baac80601962e5009bcf847a3d6bfd2c27a61cf8af811ea3157e58861bdeb739b20e19c08bdf26b290ceea256ed8db56fcc39aa35b4af82bd361908f3d750e285d24962dfa4dedd5037dba5fb6828e7adc760be521991f7b7919116d739fe3641c01170dea8f4477e1e27dab90f8d94c498134f78eab2601d60fa64f9f735bdab917d2f65055bcfb6c3b53efc1dc013631e58d1d5283da947c489dcee4d10f4c2c852e038147170cd74e3addcdb9dd1679c121eab102a02f6ddeb2200688ef5f37e05c732860bc75b0980d1b7563cd5820859a93cd
private theorem part91 : 2 ^ prefix91 % Spec.Ffdh.modp4096Prime = residue91 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue91)
    (e := prefix90) (a := residue90) (b := 1887340615) (n := 32)
    part90 (by decide +kernel) (by decide +kernel)
  rw [show prefix90 * 2 ^ (32 : Nat) + 1887340615 = prefix91 from by decide +kernel] at result
  exact result

private def prefix92 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (96 : Nat))
private def residue92 : Nat := 0x5f4ba342dd49055fd34142d19b86e47cd600b8af0b6ae830bc449f4b04201999e7fb2672dd9e30e8c087e4f4166ff7b46745ccd2162fe2d5e547aa9a37b9a77bc547a304a8e7095f15d5f1431e23f48468d6eab0acc8f8b5845fedf48fe07260aca30226c3cf505149644a87e45306941a67043d3c39ad6425d68777ca32a1fcdf2a09ae39a7343e7795a70f61eb711f028d380c3a0483fbf10bbe57cf7eefd2b1e652f611a5f32505d1e716ca64b8636796cc5c1000b2410265c0249db18fcdcf5e9bac77a17c13014d40ff745af9c6f87425bb6723583f666ac481d58ab25b854d09c054a152f1c556c07726b4b6d7b5d886e72247ad5cce3c5a09e98b4959df66eb3164c612544ec9528a056d3e63004da831b3c4ddce275afe708f1fea748e13078ee0d78b3c66e1a2c2d590164722e0800a98d4804c0e3a456baec71b82fcb762b83fe03f6e34abad3e002299a406c41d5a9c1156ed25592795ec3d28e89c14a9392c81b675d2ef382b325a9ba1d9b84e879a192c076a1944ff32dfdf03a9985653ae9116316dc2c19bc16e566a8c0e29366882c332de0cde175309b691d8433a5dd36fb7374cb16eb9a85b461390d44d1772f5852da4ee3ab028929aaf5686670e39d5fabced6f01f21063c413fc0f29979a7c089190952fb8069c024f15dd2cfdcbf2209e1c36649409babf1b638d1d8f10f24f171326d5c583a597c0
private theorem part92 : 2 ^ prefix92 % Spec.Ffdh.modp4096Prime = residue92 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue92)
    (e := prefix91) (a := residue91) (b := 633432208) (n := 32)
    part91 (by decide +kernel) (by decide +kernel)
  rw [show prefix91 * 2 ^ (32 : Nat) + 633432208 = prefix92 from by decide +kernel] at result
  exact result

private def prefix93 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (64 : Nat))
private def residue93 : Nat := 0x52125afb74d298320e2cd29acc719242bd4fb4b1a73674be79b4a713f8f65ad548b67746ba97ac3f1661623b5fa0fcbaa1b6ef29d8c59e631d1faafabc7ca667009b334fbcc34d4c96cc7ac419941c428ad028f391eeacbf25ed9169f95873aafc13650d003b409433b063d73f33f06eab7df8a9673a8243f31a7605e718e800c93ee7ceb4d635585e1f656adffcd4a6b240201c5b37b6e1030012c33651420cff60b4946649dc7946fc3a1c7152fdacb090aba9a272238ba39e93619561e5469c2bb508e46a31a492d3d7777f52c3ef1794d13a3280110b9ecf8183e77cf7f4cac2603f8ac6b2301d321456f6b67af4328bf8157d3521e3382f196ae5f94f9d9abab257a2d16319c3413c4261eefd750b7b0bad7bddd1f79e0ec1751ca8a3fa624c8e4bcc2ec4273720dbde13f6c068e7669546a7c117caaccbabe22d1e8b08e00669a027ce5a3c3f2e18cc7b07a49eedbcc31d11683f9a5bc44d661ea390adaf840d1857715bd8c0891becda4e91322a4633cafd04abf06d7dafb0d1446a2865f4db2845ebc76f31804c190a03cefcd046a51c95a30e008daca294e911a8a235b29bff6d717138a0cceea8a7c9eed6efe15ba45814912305ebc8a81087e6cb7ab8e6f1db83a23b31e61860d9501973582ea2bbfec10ecec224ae12a3da786b8e9788065142fb881bd2b939e7dcf49c03e13d58fb546b8ba446423e297cd3d1
private theorem part93 : 2 ^ prefix93 % Spec.Ffdh.modp4096Prime = residue93 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue93)
    (e := prefix92) (a := residue92) (b := 1418757120) (n := 32)
    part92 (by decide +kernel) (by decide +kernel)
  rw [show prefix92 * 2 ^ (32 : Nat) + 1418757120 = prefix93 from by decide +kernel] at result
  exact result

private def prefix94 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (32 : Nat))
private def residue94 : Nat := 0x7243f84ddfea91f1e9ce2ffe63b6915420a3438ab8c91f2e91ea7bb5c6f9ffbb4fd4b9a6346096dbe26167f5208070f3161ccbfdd1e09f298e8226179c2ee62ab47fab1134e41f31df26e75b4de830f1cec1f0c76941d2f7dcc252ea11ce8263258a2db90bf9adf5be687d96227b39b3626dea83842a804290e31192192242606df5800639027f77c5416bad31b11c5551a02fe145fe5d95470202d2912784111d45ef068fe9b6158ed0207f19cb5026c6f6a4bbeffc7ce85cbd51ff324d4e1eb4e365addc23b6ad2803097bf33e8f6474c033e51a46ca32a1bd340e392e2c641a2e6adcb3e27e80d9dcd2078004f34f92ae5e958671c3449c996eb6f4d55c52843300866a075cc3d69ff4eac04990d8f705c30189c13ae02ac04af8cd4a278ff0105725d7fa90b1a0f5b90105462f81e419ff0abb15c122310f12b3e8fb47273054864991fb5b3b8b9235d4b3cf52db893d61bbaa53177b79cb8721e146f670013542346c0a051daeb62314befbb6f9e17382de5b34c0401c0ca03d0fe78cd2f269081c0d985c878b33ab9c906087bc7518f8f787d4e45ab255ec6d107b2649a05eedcd8cd77ea42e852485fdb0fc14adaccc9883997a21e8fc6a822944d0c16ed35cd4913d6f1f224eee19bad5f99494cbcb6b30cb044b6fe4c42d128f78e6b710640eec6e52e5d4c6edd85e1e7c9aa1b9b1fcbcc9f8911f2070c223360a62
private theorem part94 : 2 ^ prefix94 % Spec.Ffdh.modp4096Prime = residue94 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue94)
    (e := prefix93) (a := residue93) (b := 2369330697) (n := 32)
    part93 (by decide +kernel) (by decide +kernel)
  rw [show prefix93 * 2 ^ (32 : Nat) + 2369330697 = prefix94 from by decide +kernel] at result
  exact result

private def prefix95 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (0 : Nat))
private def residue95 : Nat := 0x320843304f5fab1d6723b5cc7d2af977f5ae0dd15c3c455ccfd30aefb8d4cab546972331f14509e85de5d000fa682abacf89a5a91eaa79441473260cfe9616fcb85757138e2c5170e0688c6956851aad58940b09f002bc2fcb027c869940958b1338e366a39ee2b5242ed67849abfbc48808ede0efa240b5cc7ac53e008d5a87e925fa70a36660b8cb8350f2e924f0a33f3bd39b5f0699f1f9c713d00fcbe90f5bccdba66c7dc55e9a4575f28abf3cb42a9a72ee54e7145fa1a48aebe4ec08aaf40f2e9146675cb1ab18264c80d70493e556bcbd3e626ef74d64283e1dd22e35edb98da55eb9929dca6ecf39b55f733e6f91240d075e4e0080f6657f0f8ef7da6caed5a0a5aa282f4bad038f922a6945bde3d4904b94a6db1fa5fc3a0ca826ee07fc1d712736b4344ab2701ef5d8722f604a31ab41cd0074508a0d173f24dec334bac56fbf890247fd728b30a04b4b39a2fbd4685265bba2cb69ddbf4b0eb7d145d2c1540da0e130ff014c0ace99d211143a2972fdf2397aa9b8c2acd688deae92d0fc5f9eb64f34c8d6dcc8f2545c01fd9dbd6429ba601c6295f0acdfe08aace8004d6260fc962fb8d51bb5b0d8ba33a70b399f48be3ad07dc0c078f0dbcdcd1d7f6f32e31ab313131528155d555c806156eb215c3e468897520519cad6eee135d2020fb6624fc4f4d084a3a17bab920541ffb1d97c247c55828ac373d7f0e2
private theorem part95 : 2 ^ prefix95 % Spec.Ffdh.modp4096Prime = residue95 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue95)
    (e := prefix94) (a := residue94) (b := 1405350763) (n := 32)
    part94 (by decide +kernel) (by decide +kernel)
  rw [show prefix94 * 2 ^ (32 : Nat) + 1405350763 = prefix95 from by decide +kernel] at result
  exact result

private def prefix96 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (96 : Nat))
private def residue96 : Nat := 0xd88bd8201a04e6f57dde8b8b0e4c146a548820f7fa999b25ea83381b406de36e601660fc23de7e97591ced7c5a8646c9f8c30ce5c2840749133ed10a4c036b0b0b543889cc073875f58f8c24a358d4cf94c54891a2cf00f46f83c466679b96921e1db939644b4d0d1aae28546a5a9f5dcdfa42253ddd4169e92ac244e6575a0c32a084f27e7fb2ec30f2652180f659c3d495b3970942d761c80941ca5cb96a062def51fb515ea8182dc3054289c8c89188a8ede01efd06b6f36a73c62e275f258f14033eafb691189fa87a72f1a9c7fbbc783640cfa14a24212010f6df057f9d924f2afe85aaf7a01d5386423da221c8839bdfbddd9b719dbfe6e3674f830e17eb12a8cca8bfa58edaec7af1a12429dcfd4e311777f9145a5282faeb68043dfd37a72cd6961edb4aacb82fd41f992c988e45fd22dd02dcaed47697fcc8ff080624eab9313c5e967b18d626b50d89a6448923e6d8bb3465c43fe6804cf8aee9275c66f437ecee4e278a2ce3eb6ebd685842cdad1e1e26e291f2791b6fe6b753b5532fd6ac490a2a3ce4d4408762bcdebe9d99d31e61a47946e4cd07befcccb921f67c57b7b6e644bffbc762e641d48fbf1aa686cfa9234e6f8513a730aa181f769ce9c8a876e81ae119afdd45572df10cfd0ce458865982951ea8492935a0b0d11843aeb4535f571d3f115a2ea0b2e6d8da1196cb96972528099c1b380419acfa
private theorem part96 : 2 ^ prefix96 % Spec.Ffdh.modp4096Prime = residue96 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue96)
    (e := prefix95) (a := residue95) (b := 3292056840) (n := 32)
    part95 (by decide +kernel) (by decide +kernel)
  rw [show prefix95 * 2 ^ (32 : Nat) + 3292056840 = prefix96 from by decide +kernel] at result
  exact result

private def prefix97 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (64 : Nat))
private def residue97 : Nat := 0x5e3758a7f43e7edc0e9a4638ac8c8ca2dd1cb2286af7a822f22e6dd5c579bfb7c1b86dc7827703f82e22aadf31f1100e6ac3a8da0fc2194a52d0f3f2f47be7d155dd362eb07ec6c5f6a8718387e836317efeb517d529325df2057a544889032edc4b43f4da0bfdd10c71baec21c53900731b2cfcaba5f1939d613de441b7791508ae2f56a8031eb77ef0541bddbb622da8300d4f9021e94b463e325647153ab813b6adbf614cdc89299c18040cfe68d422d00c381ca7c553ae5c33d8845d59708bef835265b1fdee025c8094d7654c763f7e6923fa5a7e34af4520008c46f9c29f9b9c209a616c6c1ed6c5628dfd0472c8b907149306d0bb9362fa806a497601014bdd186b594f04c742cc4a7b22c9e2686026d48f8d7e519d5a6aec16b6d2d7aa0d637e1b82d22d1edb6f72313eb7b25d748225af4b4a6e42353d6ef777c54eb57a0ff8156385090a7aabce2577e05f3e22390b7ed7e216888f6ae28351baeb33808f4ef53dcf6db79eb346d816cdab68d209f80867aa69cf6625e95fdd6c96a19c9e597f6c563d99b32275bf133d827f8c1bbee5a87f8db9d636815e70f83059aadf0d765da3cf0a7d15b8a4f539f2361fb715a03f45567677495dbb139438acf79973b32785ddccee7ecc628894370213cf8bd50b89db86d3689fbeb466b62a3780a1441b40e3857960578c4b5e897ffe738121ae5bfd9b5f1c8e4dd5e492
private theorem part97 : 2 ^ prefix97 % Spec.Ffdh.modp4096Prime = residue97 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue97)
    (e := prefix96) (a := residue96) (b := 1591553427) (n := 32)
    part96 (by decide +kernel) (by decide +kernel)
  rw [show prefix96 * 2 ^ (32 : Nat) + 1591553427 = prefix97 from by decide +kernel] at result
  exact result

private def prefix98 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (32 : Nat))
private def residue98 : Nat := 0x677480b2dad361a4f88dee763935cf8f768ddd113e98e2e76d722209267179aa38ed1ca6e7d2c1dab855234049755ae46bca55b727abbf3467e630148ed5e40056ce3a0e5cce0e3e2027a6e9b54a24af830511624cd487159ec3d4ab4f95088e9921f30aa5a25b372acc4f5a94d6f0f64e01dcd71d63199698eb7ae793a132ca6bcbff5bb001faca8ec640f7743ac91c0166661b248d93aa7e4d4231524373683f3b6710550bae23b710a8c7fab6c940c9ccbb3950b79fdcd23f1d15a2144b4dd7e3b19226c3f32a423f5362daeef316596471b1ba7b6be19a639fbc13a7f7d312d49a31c5a443a347ec29e1b27a08cbbebb907f28876e6818dd48cd1be719e4816be3dfc58b9004b8db2435de2d31fe07ea265c495c9567ba47f1ae89e70f8c2b36ba7de6802dac47b382e131a76b9f580da0a6cc6c6073404e17926c762de90964e37b0dee91f97358f1bf7990ce0437470de7ac36d57bbbbff22fbd38689a956419dee5d04de3bd3df1a73b3a80984ef15ffe753fb8e949b7c7323234a372327d59106180c60e371c7843a63afac7416478862ca24775485d6cd18bf3b4140f4b2b7fcbb960391bf69c452b43a25d8b4c62d2a1a8e9d1a388ba706a6816de39f0147a11a80f1aa614ac10bba7ca7e66310dbc1944342a74b89b76acc9ff86a8a960623f95f34e1296dc3c8548cc4dfc5e9d2e2b6aad7cad57489c006e9bce
private theorem part98 : 2 ^ prefix98 % Spec.Ffdh.modp4096Prime = residue98 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue98)
    (e := prefix97) (a := residue97) (b := 1289851788) (n := 32)
    part97 (by decide +kernel) (by decide +kernel)
  rw [show prefix97 * 2 ^ (32 : Nat) + 1289851788 = prefix98 from by decide +kernel] at result
  exact result

private def prefix99 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (0 : Nat))
private def residue99 : Nat := 0xbfb1b5c5778f7ce6cf780a50f2dd2eea2ee36f2f06691854219062d5bea876907b8a4ad00ef4bf6b313c8cf45192550a253c72d1c08dc672d34741f2e5ae2cd9909d8617e329d9fffba6ca30fac622b167fc053680f4f8e8930afe041e0236f41a80bedcc0ea1c67928a29ce184ba9969f0b0ac8584849f25b1dc3d7074fb9510ef3245edb80581f33fd4810cd929ec0cf48f0b3eb2a4599c108a1f784d44bc2dc64e146946c4cd040034d11e748873567fa4586df83f4d7692cb9094d2dd7c39b26ff4ba833f4bec2a623c5d2b1049be0c1e625782f115827fdddd98b4dbc1db6bedc2d963af8cb140cf4c9fcaa0abe0b4c861a4a9db2cfd258d9e1b09df8346c56fb264b1b8d26dfba55bd353b9af69707b44c73cbf1d093c1c76be8c67bd48286120cd355b8932cf3827417373e0dff165b7ab3e78cc74d2113081e1c4e6bf21d02e50d1532873fc043d951f69fb1fa30d5e072dabb037fdcb604c0329c427ff0e1975d716c2b046a15d04de81d4b7038a5b71acc03271b19b974698b056c394a5848b6672a8e6043c138cc8db067b4c502ccc5343328f41ec2ffd8350d1c3f47a9604979fa951f72c74c41fc9e5bc920a84a993572107b3422990bdabf32deea77161637168f0f0bf5bea5d49dbe5bdafb97c2ea097eea4f8572b25c9280f4ca7fbcebad7d459e40315de3ecf1e4c1e1102ce7010406169a3d30901c890d
private theorem part99 : 2 ^ prefix99 % Spec.Ffdh.modp4096Prime = residue99 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue99)
    (e := prefix98) (a := residue98) (b := 897216798) (n := 32)
    part98 (by decide +kernel) (by decide +kernel)
  rw [show prefix98 * 2 ^ (32 : Nat) + 897216798 = prefix99 from by decide +kernel] at result
  exact result

private def prefix100 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (96 : Nat))
private def residue100 : Nat := 0x7fda87a32be646aa00ad374085f438c6d9efac747c24e93a67c32a51c57f08d951be1cf1734cadfa9487fc909223e03dba9ed9d6c1c180e3b5fcd35a15b16300daf9c650a8aa134ec06dd077f7bb57f33fa35813be1f85d2cbbc43d0428ba6be2b380a61b067c9ca335ea6fb04e34e7b5d99215578b86592684923bc5f9e813af1a30f027bd633dd21cd9980adcbff902828f35a030a03b2d57bddd9e0235b91be1269cb3e20c47f05e04cbfdfe36e566b7af262d12bff6eacf924db2dd49a8ced15a6ae6f1697b1fb788daeec222f7b0a742d12d8890d1e9b21224b21f11b93f0f4805070d3a981329828b3bb815f17683326bc18d8fa3c4fded36d9b7ef3d65eda721d5c101c5fd56e6d760af67dd2bf15bb23b1ca45cfa8fb3a8b396cdff3e5f76ab51a5fcfe494d03f34208792b255fb8fbdf27ac41951fded6be6a72215afbb543fea3d1a8eece2aa7151b9b95acdddda0e3832078a63c75095848441f60a5072b82dbf27762791cbc5144af7a70cf9dc698923342fc2523355b94a689d06ae37395b1c8aac0d8babb537d5d5c6d3c265792a05de02f0814563ce9ac6ee652559154614765661dcb47be9bd5a137303e662840080218e1d4160d842ed7cfca7f28c475772fc110a737d0b42880b97383ba8b9548f42d0d47a77c719e6cb5ef00ae14c8aa2e94439ee10f3f99630422b541a72eb4f284bc42cea3168d3a1
private theorem part100 : 2 ^ prefix100 % Spec.Ffdh.modp4096Prime = residue100 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue100)
    (e := prefix99) (a := residue99) (b := 222966810) (n := 32)
    part99 (by decide +kernel) (by decide +kernel)
  rw [show prefix99 * 2 ^ (32 : Nat) + 222966810 = prefix100 from by decide +kernel] at result
  exact result

private def prefix101 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (64 : Nat))
private def residue101 : Nat := 0x453b59f4176e5834b53106a1313dc6583b7933d43fab11722adf05d55c2f64191c8cff2965952679b96d852b7ea6fb692b8fa58e13bf34b02c4f8abcd2cfc48cbea5cbc75db7657028e7971f9d76aa38fadf2b2caf53da0a54193d0eba67738b8334d9b1992669b2eadca44a763b32f95ad0da2c3f4beafc344a7b3a5d195fd37cfca0cd6cd91c7dc2f8c7b1b9552824978a301b62ac9b7f053cd1ffe935034ef1165cbcc858969c701d3f5274fdc9bd494d566338370e8077718d3e9ce5118d6f32594aa46ac86fa974256bb1409a42af57f708f218bf2c532486d66f93e726151b28e0eb786a04a324db1b32b3d824d702bf91e64430bdf0c84d8d22d8a728cdee09e04a0a736152b524572d7efa2703b0ee1a3ec0293c3b569ac2577942780baf7d4be8fb63656927c5eed5c12d808c17587506395bdef614f716a4892f37583eb9db8ef72fb1ceb9b63d0a17370076169c4f1ace8df2ea332033b08cade0cbb8961f45992bd2250dcbcd8fc16e0b03f5d10dfbc78fd11c7d89fbd39ce0b1282e3b28c88dfa0309d488dd5c523ef6fb21970b209343bb327cf0961848694726c558df4b90f3082baea45311bf6e32b755b2b894b3d122fe6de5403924a62307dec11c926712f3aabc3f5d341436f2ede26bbc3e1149fc50668c1c617fb65bc0c6bd9fcad7acec13a2c837ebb68e9239cf2602e364f8bfc16c018932783ea8
private theorem part101 : 2 ^ prefix101 % Spec.Ffdh.modp4096Prime = residue101 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue101)
    (e := prefix100) (a := residue100) (b := 1527416301) (n := 32)
    part100 (by decide +kernel) (by decide +kernel)
  rw [show prefix100 * 2 ^ (32 : Nat) + 1527416301 = prefix101 from by decide +kernel] at result
  exact result

private def prefix102 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (32 : Nat))
private def residue102 : Nat := 0x50cbe66052a2e5f52e896da4268e8e043b23d38faa9101e82dde541b26a115e347b87785ad2d84cfc196d4d21272d08676ab593d613973b7ea1d03a66fefe3787945e5fdc0a8753a2140115dae8b74319316398f5ed0f33ab9aeb2bb8fb93230099a5aca70a8c2a2c15ee42b14b565a6ccce3c3dcacbb96b5be847ef3925c3d9270e38a18277a89fa522820ad96cb42c138aeb86c8f2ffaf77625aec5148d6ac86972eb7d35b8f7d8067656560ba46480676230173f738cb8c7fe3fa68fd82ea26e0635de52f42fef18166c8840f886b7b2419b259ec383d694e06d6fe590afb7988448141a482156ae5088a387ffd88ab39da29839ca1aad5903fd8a02874717230f11c1a77395e0ea1c7598681e41ba5d077f69b2113ffac685777beb169ab2be341d43f6aaeef6cc0f6e7f37e89aa8459d58922c8c4f1a7de69355211ca2639b3a2aa4929f4af17adbb921cf1ceb632ed319dbe8b95fdcfc7ccc7b55555e8f4dd1d81fc7f5235c45a47c3ec9c6794b3ba3aa3b63bded0c3f9c327f789e5ddf03e0d4b6f8d16764003edac70dda8dafbe2e8ebff819f83b3b92f89d11146a857c5c81d4fa7d94a3b84f457b25e73c0c4604e149c075e3fe7d58b8bfed0f06ad90a479b78048e29ac6055a138d28eef537035c23b262e71525471fcad8dc105383e11a0d6546d6c71ebccadecd3038ccb05e059463cdbea3ef873580f2b30ea
private theorem part102 : 2 ^ prefix102 % Spec.Ffdh.modp4096Prime = residue102 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue102)
    (e := prefix101) (a := residue101) (b := 314701029) (n := 32)
    part101 (by decide +kernel) (by decide +kernel)
  rw [show prefix101 * 2 ^ (32 : Nat) + 314701029 = prefix102 from by decide +kernel] at result
  exact result

private def prefix103 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (0 : Nat))
private def residue103 : Nat := 0x4e4642efea89b8c45fe4afef391e734d2fa032c9de68cdffabe5ea807328d7a5619c6cab06ba0617e10b96d8fe56e470569a3d7191577f0a203e20612f5c838f44cde6b463407fb340869773427f98c7c1864e235afe5f94fcc1d8c643cb8ed8cbd853dca8e7750b9ad7dc2d6d75c3c68c0f930bd346a0c5d697299b494edc7dd70e263501bedcec3c169f166255ed4634cdaef1907858b93a48154839daeb43bc2ad61280b1cc7bc7aa3be7acc13cef2602d44df65c29c660e517d7992837f26b0735fe322569366fa38c32f583c1a283bff70344102310c82439c1ade1a78d79cd1cf6c865092472497f90ddfb86f50dde7840a0e067b3099b07e5e5ce645a1cd1ac52b7b7e550892f4f949a208693f12d71a61b0211ca5058d86e1c1875eee93eff8393e9e193822e55eaa4510746c288c5eb114c1161149df2059d21aec5c9a6115e628cd9439825ef612c7e8d57be6d565fa1ebd296a9807ca336e2c96c103dd400fc83f927af7f1555183e3cda745b813859600c2564d1559fb135fc9a2fa0ee5b66e24d8767dc538fc1b316eed24fedd2e6f38e6bac8ea044d1b7d4f95924d06025e1afeaaf8816c5103b296d845c1112df8378b8730ef5bcb1d62bce13b16ffeef97d11ae6057b4a21bfe103afc66f10750c5b5ec9656904b75f6d9e4044052c1f37f3c19f31f70b2aba02e556411ae81ee1863fbca24ee113153f9f
private theorem part103 : 2 ^ prefix103 % Spec.Ffdh.modp4096Prime = residue103 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue103)
    (e := prefix102) (a := residue102) (b := 359278196) (n := 32)
    part102 (by decide +kernel) (by decide +kernel)
  rw [show prefix102 * 2 ^ (32 : Nat) + 359278196 = prefix103 from by decide +kernel] at result
  exact result

private def prefix104 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (96 : Nat))
private def residue104 : Nat := 0x873c9c47b742aeead327ed50b4963272c1c7e1ab6dbf0670a04fc9ba59592cbeed8c3e247129b8423a809a81aad7aef1f3d080fb74d31c588ce146a21bb5deef4b9c754a07148244870b92ff0a68d179b69ca9f4cfb6aea3f09740d2a94eb4c168775c0c5bf41dde861bf8f0f8528b0c874ab404430490fdfe54928b7f0e4ba2f259eeaf72fa4ec1b54e28f499dfa37074cc9467b46d8c79ee328d21873c1187462843642b807a413511c781b4b579f85f7c52768c64834a204b79fb4799388a5b0060e1c98a6004e05792e678d9a8e6661968e4bc633ba0616e3bdea52ea7125cc9a91a39b178743f611c5832ba6da6a7b2919d0c6fd3b82d92cbd792937a8961b3c623d2ac2b26a121a7707a18d1309cbeeafd16ad2a8b90f24f078ce31c58b0fe1b29cee10d99f6e6cf431eff54d246f0b15da6d191532e586c590cd939c78c88315a213bd71942acbc35fbc79794d763d6b163db25178e81bf17396ea5c6f1a09fc77dd11a966f59ff69879e7f2c004e93ed4fdc6ff9b18bc6413ee9da70c8e3d3751e397d16fa2fdb957d2b18a6c77ab6e05a98be9691ba126b4a8e1a7cd7a38ecd7da5fe62cddfaa45d31620bfd5976a08b429f23216e65b602741fd889458ed739c22463dab61cdadb725f3d1efab44b6e7d3032eab3c87f0b13b2a3ba73bb87d5f7e66efd13ef3cd0f454474326c1da1597c808160e193052c1baf4b
private theorem part104 : 2 ^ prefix104 % Spec.Ffdh.modp4096Prime = residue104 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue104)
    (e := prefix103) (a := residue103) (b := 1843257709) (n := 32)
    part103 (by decide +kernel) (by decide +kernel)
  rw [show prefix103 * 2 ^ (32 : Nat) + 1843257709 = prefix104 from by decide +kernel] at result
  exact result

private def prefix105 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (64 : Nat))
private def residue105 : Nat := 0xe43b6e82f251efeef8160b03aea8d073c52357e4926aac1fedd47a01e40461428ed294a01d5f4840506d916237fafb5e68e03eedcc21e1d10e53936a6c4f61b45cc8544c2ab44fa14d6a1cbd720d9016a451d9cbdcb34e7ac6207e5516ee720cae11050e0f98361efe45a72baffee6912cf49e3e5a48c2bd2747ce33467dfee7ee3dd86906ac4d82c441d13ffad953d4f8ddc9704a40555f4201b7def13a26b923ad4d7d6277433cffa2c4db9fff9435de99a4fb774cd297ed210ad5a4f2e93ee83b33dc1e5f2d2132a71e6d95962c7d820145c766f00737077f9e6bf41339c3d9d42c089585a8f579c9c477253c8e24276d3e4f39049146724e073baa3c1db350a0dc3c88b7bdd1e6b5e76892d92f242789a7f33ca9e874c1280cc0c1b42508652563db87677474ac002d364a2a816f8cdd7bfd39871286e6179da2d07f207e22c34f7c3bffab6ee572ed0f6fdd7ca4a5995ef9cb40198f074e7ccefec21d34181371568177a9ee9e45a128a67835cf13208b8e08c1abfd63b11f5f48c50e4e06678067e48d46b072c4dc7f91a7a9fbc3dcf771753885a16182a46fb8f54deee3f670fde081b79b33c92d517b82e2ef8c93910cc3992a4ad97d88f510efc6fe7e342796d5191d5e3d70b4651ba87a22c751ec568519eb38d33c244d21c233609c156ba2a8ae0d5edb4a55a609b1e26102e52b68c2841dc7d9415b4b986eb6a6
private theorem part105 : 2 ^ prefix105 % Spec.Ffdh.modp4096Prime = residue105 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue105)
    (e := prefix104) (a := residue104) (b := 2188330876) (n := 32)
    part104 (by decide +kernel) (by decide +kernel)
  rw [show prefix104 * 2 ^ (32 : Nat) + 2188330876 = prefix105 from by decide +kernel] at result
  exact result

private def prefix106 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (32 : Nat))
private def residue106 : Nat := 0xa7d14fad185ba7f0ef080f50c9f1f17e28e152da596abcebdf6400a6714af09ab96d9c6f1d5ac55ca33bdcf3b05ceb3db6a2b66626e859c26ae3e6f685ba1592069e1ee250cd817a1943c23a963976eeb39e1c0e17dd6756110e4a35e09315712ddda0b593267cd1e7a8fb907f9e961860bf654e35793d541eae50a263c02f7113348c5f4822373db4cb9858c31903927c945c00b98d083eaeaeaf570628f5bfb0b9d1ffc9aaaa36c620c33081b5562fc34de506d059086f96893afead79f7a9679b5ad22d077929243a4a7db4d295a9d70758d83d73e465fc561ba545164b892f4e30cdeb0823437294277786850bd3e5052fa6415cb7459f59235005e09cbde87724af11c9f9fa711b4d2944ed03b3f6d48bf869f9b7956e9c82c85b3cc30df42322a5e3074fb6a6f2989ae77ac6dfad24e272c49a6e381735a771a3d505e64c8c3739ae60c2402c5277db2888e1fd5ffce7a5126219eac4ee10c2075634c91469d3788b0766fc69ed34a9b394c7439641d4994ef0bdf47ea23c11c57876d9899082ff370d339d3d60be974d3349bb840fe7568f19d84c6ed52f6ae3d9e513f2dceda2b9e6ca73c77641127a0148149352fc467c98b1ed0a2403601cddb029ea2f44c41756da020e6830a5e884157f1312c9cfb807b2ca857ac1c7aaf7ab1c0e7ba6a33b5428077f9efcb9d9c82fdd162d40fea73ce0ce314545b6504f3be0
private theorem part106 : 2 ^ prefix106 % Spec.Ffdh.modp4096Prime = residue106 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue106)
    (e := prefix105) (a := residue105) (b := 2538044938) (n := 32)
    part105 (by decide +kernel) (by decide +kernel)
  rw [show prefix105 * 2 ^ (32 : Nat) + 2538044938 = prefix106 from by decide +kernel] at result
  exact result

private def prefix107 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (0 : Nat))
private def residue107 : Nat := 0x8967a8d1a2266dbb6f1ad6737f6ee510806ff1c2f78596777552480d4e6ab2c587e81a59a84f0f0b680b814b025d585dfbb658d7adadf6e51bba7e3adfbeb1c0055d40665484e6508c25d0fe9c9e1bb9ba64f59caf7b1c82eb7cf4ebf809f6f5ca1504a08488e03ff7a3a4d96e222142ff907f209992dc2dc69d29daccaeedd962195a0c023834021c927e02ce833dbba3d35e3692425c8faa8b1d05dab83753790762c46deda0093cc7b0f1dd36bb71d0de3c654ed2a6dcadfbd33c0c957d214763ddd45b21c659611d122ed6643e9c7a1472b4a06be6d73cec689b3611273ada9e6384c3c6deebec3a48611793b2f88d2bc270f8d8371c096b4ab53d08dda8ae39a08e1f7db8a792e67819aa83b7bc424e917a9380251bf37fc8ea06ad563d991b88cc656fe5e630a55907e0257a64910fce924de99dad817994ed7b3565834ab1deb808dc338a0f5b0cf1587dfbdbbce226e501233ec413b3af4e2c3a200c89baab1ae5c4ea042947224209c184cb937416779162c748ba1eaeb13b4de5bea7e6b5ad81b8d1b9c5c89bad61cd4ec9a053cf92db932c24c6450edfb6ac00b4621c86d1b3577c8563525a3c23eadcfde0b08473ed6867a62e415aba6ac763c8b28c2aedece29d4bf678f8ee152512720babc5906fabaad9cd6fee2ffcc4bbd454e6caf2edb4f971e48134bab6a16225ce6f4206f2883cf519e1ba6592c1d609
private theorem part107 : 2 ^ prefix107 % Spec.Ffdh.modp4096Prime = residue107 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue107)
    (e := prefix106) (a := residue106) (b := 266298707) (n := 32)
    part106 (by decide +kernel) (by decide +kernel)
  rw [show prefix106 * 2 ^ (32 : Nat) + 266298707 = prefix107 from by decide +kernel] at result
  exact result

private def prefix108 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (96 : Nat))
private def residue108 : Nat := 0x292ccbbe0f01bd3e3579c29fe2c7de70f733a126488ce2edcf94d1a6b022b887a4295e76f90ed2a159090f17c87c7f3b6f740195303e806f034897a73d26a7b51cc46d002d643c9786329504ee4a9d252f73d395f83fc7fa3ccc3f8b9ff611d454598006444b4ae703f3123b63d731e05de360b969e92d6e742a9a47c400540c1f1ed479090ea99561d5de989f7262f651b03eee025cb78afd3fb1dbb071a6cc8859d852cf02a593fa5c7b9e59a8217a94c7615628760e69a96a789350299d3e6e19096bc255f6cd01b96f53991879f7613a87ae067b5e231e715dbb1418fb248a34beb67b5e4d4a650753557ff94ab3eb75dcdfa1ffdda415583d411b7fd8945fd6b745945f1526d48360621214bf6e804badd96237f00bf51f4368a58776ee8e6ce916dfb1b9322234d8902990b47f3cd2f588747e7be61fc74845e0f5cf241d86a866277cd8193170f3ba8f3d585700a8809057b853e9061802f9692f7dfd3df7f3f12861fb08342ef82f29db5b60968fa4e55216287f36d629eecfeb010fb8a1083f19fcfa5f0904e62ee446ba53f92d41a4f95e5f5006a83a8ae6fefea03d2080aa7cf1ed70b8a294b7cb0dfd2909e751a61ec5524362a5e2ee54d5e42421b4e6f7bd62cf293fa2cbe1eb3e0654c29026feefae3ab38b75a8f9bccc4ed062743481fdf87e92593ecfe199d7cc6785510c25064797a4803226a6ce30f254
private theorem part108 : 2 ^ prefix108 % Spec.Ffdh.modp4096Prime = residue108 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue108)
    (e := prefix107) (a := residue107) (b := 339618979) (n := 32)
    part107 (by decide +kernel) (by decide +kernel)
  rw [show prefix107 * 2 ^ (32 : Nat) + 339618979 = prefix108 from by decide +kernel] at result
  exact result

private def prefix109 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (64 : Nat))
private def residue109 : Nat := 0x59ee1d14c860c576d2fd497709cdd3d9dbfc8b3e62d9a1641822be34dde82cbc5047569d2ce15af382eb48f8eefc4ac49a98a9ee4689bb79b99aaeba8b1987cba8ce9b70865be0101e77953f15052e807fa3b9c03bae319149baa1403ba5f1d81966d1198b70efad698e58147d9e91387576245b730cb2d9c75098e93b986417760e910a9ce51e78aecc4618dd26fca840d9d046d92d21247afd6e57c1c115e23915be1df394acba9bb2ac2e73b1f9dff142306aa351042f2149d3f5051a2cb94cef75a210a7d8cd528dd99b7c7d8828a89b0903da2fe15ca5c140abfaa6a32f8c3e63a2502df9eba10e959b8102aae2ad0a1c2c88dc1a8c86c7eed0d5cd5c49ca94e362fc2a1b117a940980a8fdb3464467931b0273e7f71a786b7c492ea48c4a9fc7205accbf261aac7a9b596a4ade8b9deaa4f9e9f7bf23babdd95f9810efa22dd6362fc0de1c9cd9b3390d05fcf526f932d787f02c98c1aa67c440e27dc9f0f7333249cdfe7d3dc3bddad991c7f79c7632ffe0ec46cc421b24cafc641172c9c9035d8b040f32f9a1a152912b2cc20c0f333607fd704e0d575868b3442d948674e44d5af14c1cbb172c439f4dae8400826d7be840e86de15066af12e027755e413f972338adf5d86190c4b8c74c55c6fdba7ab606febffb2358d139a028733a4b2400beffaea95f23f01a00bbcc99ca45a4b224763544cc63a8ffab271fd1
private theorem part109 : 2 ^ prefix109 % Spec.Ffdh.modp4096Prime = residue109 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue109)
    (e := prefix108) (a := residue108) (b := 2805325870) (n := 32)
    part108 (by decide +kernel) (by decide +kernel)
  rw [show prefix108 * 2 ^ (32 : Nat) + 2805325870 = prefix109 from by decide +kernel] at result
  exact result

private def prefix110 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (32 : Nat))
private def residue110 : Nat := 0xdec981061baa6056ba4829e4063448d105823b25aced6d4876db7daf34b142551f940fd06d16882c690c9cd8e4c746347cc89f276e0979f819f243858c435fb33b0b9eda6e8c8e9cf4e04ad65e9871d80737ba6e52cf4a750d1744306e6cf95ca6406cd842b2c3fe28f2459c5836d8f52a398dfd51f04d154e8f933e2a1e18e311fc3dc22d1d7be46ed71e9e2e30b6f4026c38bd32449bfe8fb3addd8ebc4ab60029093702a3d6495ddd542e96492e48df6c88025011763474c393bdefdd1bb509547d5782836797bd35adbaa0d09aa9db21718e71ee35d75f9ade8845a9a5a07acb0d9766ddc8cf02285499a3a29e82e429256d0a79ea38102d8b28464a8d307414543196b85ac531459c33cecc8f3aaff8c5b4f8660d57ad8801c6603c5b2096f5ebf7c777b582b83e0b7af9eeffc24f27ce3923395f495926cf4762ae4fa71a72c70e4ee5b2a8fe376c84b97ac48df7b747e72366e406bac15942da502825b7d4703810fa15cc426177c0a73a3f3aeb9f5d95c532022be4beb7da04f333afdf197d5a4b285a68b1883647192ed04f35dafe7368d7fbbeeba56717e09c249f0e5e88d024921d4a0634ec6469d33e625a0f643e9bdb4adcdf005658ad56f104ec00a6b5856595b7e597a17a16b0c80a8a8e5406156c2326701114f620c6787fd17e11ab675b895299499de1382ca9eb86c9b7f818f08293f0ee221e452902b2
private theorem part110 : 2 ^ prefix110 % Spec.Ffdh.modp4096Prime = residue110 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue110)
    (e := prefix109) (a := residue109) (b := 3436792615) (n := 32)
    part109 (by decide +kernel) (by decide +kernel)
  rw [show prefix109 * 2 ^ (32 : Nat) + 3436792615 = prefix110 from by decide +kernel] at result
  exact result

private def prefix111 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (0 : Nat))
private def residue111 : Nat := 0xfee2290886773120f11fa3363a6d182d3a4bf4ab03eef179f63b12f478e9956e3484930d4c9000176df7b67a9222a8aa2a2f619afd4a28488bfd35cab3134b92108be3f46e5cbf8ce98135d6fc601fdba4597a49c9dd17704353033449bf0a6ce00fcf52f0a9e781acf7dadc572e8edeefdcdfffba886f039413fef0db0bcb9cfaa2542cc11be1771ccf94841de24c2be2fc64a47a6ccac239cdd6a1e2b6b94f07ffeede9352ac4ba36a2372aa883cb086978c21294e406eaf4b1334a661c9ddbce0b795fbd22cb4baf25eaa03b5b298f00bf0ec9cd7efa54cdce699d6b2549ba9a47fd3e6dd8e197d855853ba2e9ca2a45efd98bbd4f7a4d0a75da0054e28571f15b61839ae4a83e518073a1b5fc2a3c93250ccba09957cfffdb62a9e41180de670621440423778d1d3f1311cb39effc78770fea1e3cc3f52442970b36958264dd928d0527e43c17d9b3435cd9a8bdf600e1900c0dda5256f23ed65b28573975c3a53b515cb14f2616e86e0a9991b076766fe737c2a6ac051f2d082b413c06d7b65ff3ffdcb9e795a03874a4ae00fe571c3ad6bd3eb5033cd7f2b419174ccb25c6059b5802f7e58f268d601750b28d153c3061950e634fdcabb2ac3e6250a5b32e5c132dc688c24c7f155329931e902f6038021ab6c8c9b904bf8f6fe8b58e0287c2e04fd34d01aa884358488c6210536656e1fd537e0667d019a031faf953f
private theorem part111 : 2 ^ prefix111 % Spec.Ffdh.modp4096Prime = residue111 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue111)
    (e := prefix110) (a := residue110) (b := 3494404561) (n := 32)
    part110 (by decide +kernel) (by decide +kernel)
  rw [show prefix110 * 2 ^ (32 : Nat) + 3494404561 = prefix111 from by decide +kernel] at result
  exact result

private def prefix112 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (96 : Nat))
private def residue112 : Nat := 0x5ced2c2e1f1ba53656947c4ec6d0d04544c3832d9fd29259d868c511cb126971dd786964848273bb00acfe550da59555d63bca3147fdfd96e467f3a302a7b8277f780698ab7838532c4e2540a08f4b74d4c2465d731f362a21b7d778317ebcae4d92c27c2c5d8e3d178034ca5fa58e2cece856542d6647a50d88ca5e00bfdceaf24d9bb36d99aad484c792fa8c6b0ad027b6f8ff377dd4cdeb3ffce33d8c4f7ec756ef1746070204d2b20344f4939022c15811e6635499bf067a8a865a41029c6702ffb713b10e6c443b950f3cdd4187d11ef02e504bfc497de4b101cd103d1c4fb237f97912cc19ff4b7e76310dea71b52b3ea062c6c0b09c8aebb09e8a4df27f7297b677e2f9387b44d2d5ad1ba31f7b2d0aaae65eae1daa3eb43ac2f4f564d15e9cceb5553e3c38107963f5b4662cc58c5196a5f5f98028689b8167fb361d9cc5d2183ed95820981f5afd9a0449d8f3e7f01ea711fc70705f4191b9a418de63393132e435b5e4ffd807afea2b77491e00486607d3f51749d122bf65f8393fdfe6ec16b352ea31ec7a99acd922f506ae0f8e8a33be37a67de74fbfff9d6ec5b3c5cfd0423ad039cd007a3523717acc4b0a5185643e826fd4c584ad610e5dc578e03ffb21a0cd56d80efa58e1c0c86efed823a8deeaa065227f4a178d0d07ff6dc9884937d395f93730af7cb79aaa72467fa1e6df7e1a1b032c7262d6692f35
private theorem part112 : 2 ^ prefix112 % Spec.Ffdh.modp4096Prime = residue112 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue112)
    (e := prefix111) (a := residue111) (b := 295555267) (n := 32)
    part111 (by decide +kernel) (by decide +kernel)
  rw [show prefix111 * 2 ^ (32 : Nat) + 295555267 = prefix112 from by decide +kernel] at result
  exact result

private def prefix113 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (64 : Nat))
private def residue113 : Nat := 0x7cceb316621665b8d2d9fe0251f1210f2784ff09975565db5ed27ae7cba087021d42bbd6ef6c6e7e67bb010072d66e6e0280c6d7619ef937e3af63140bec76e0d427445fddaea38ba96d8455619455f3d6bde0216cd247108da299911546b7d387352cca5a0eec3a0454b771bfeb4279921e9646763cd40b47e4630b99ab1de4a6f6ff4830023c92e44b0ebdeb705f7d5412225649ca57b29068000bdb0070ea9d72b0fcc246aecb5d63aa1e3966f86db0b3a8329736a25f282719025c1de7f031f2c5ca42e0ec632ef77c2640789bacc89ae61e242b6d568a05e15c77ea1e90f5b5e8c7406c0cf675cfb63afbd8d6fc533509f98e80e888fddf7fe2fbad8b64b8470a6555c20f006eb3f4caea8b79f7803c9e88ba17d364fc1e3356cff4048f94699cd77ec54a60b5f5c78a9f0e97f9f7997804d42dd16489a8b433368b4ab22f83b99385f6aad0e6e6e4d547a06736b95504a56677922338bbe9e449a36e465c4a3ada792286ce0936ce8a19eba21422a46aa6455e8fd2a068c57881f933e52448cb8ede931cafed47c00585b151519018bdc69f904440eb87d86239432f7d6844dc94970fdb2125c2d3efeab57262bc986f3c08c995cbb5096f9819e15f0b7f487720e504ac48a1822bf5785a8ccbf723fbcea3907d4265afbcf49bc48c0bf1cbdcc790108c881782e121116153c8978ab76ef6168f63b94bef3bed0096c4
private theorem part113 : 2 ^ prefix113 % Spec.Ffdh.modp4096Prime = residue113 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue113)
    (e := prefix112) (a := residue112) (b := 682488822) (n := 32)
    part112 (by decide +kernel) (by decide +kernel)
  rw [show prefix112 * 2 ^ (32 : Nat) + 682488822 = prefix113 from by decide +kernel] at result
  exact result

private def prefix114 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (32 : Nat))
private def residue114 : Nat := 0x9e411c07f74fa9a1db1ee63d862f3f83b50c3d1207920b8bc86bf2699949fed7239711b4278eb14fc779d8a8385fd0779f45d7e6c28e973e585842c9d234de3e2c7db7a44d5b9b85ab1b14e0aa4672b7f55c74f430b9e2cb80d139e9e16782b53acf9f45374b1fe657309bc7f09afe7bd0e5ed3023a0b1b8bc569552363e1cde07bf04b980f8a0cf9f3f907d6d93e59ceddf15159d819176d7b633601aefe44251077a47ee2b849b62ad8680f35ba529b02e76e8320bfaf4d783b119c77d410496b45f8ed577ffdc46faf94645838654f74fbb156d1c57a04f6a77b666ba8baabcb5bff2aa843382b7af6a942b381223f1ab63252e2e6380cc88a9ce4d350082e5ef8c25ec4e67a30392ea793d0a070ea0fdb7f0cb0a7c48b0f690f3b5bc013ebe0117f401622bb45aace4378d6822001b236f1e9faf692a7d78acf997b4a0dbe658109848bb82e7b106eab467b91b9fe3770e01c94bb591da8d540a6d842974c2540da5a5b597119abf123a4df62b971483cac4b0c65a3e0923dd9d6b6ea56dad0dc6ca4c12d25fc0d1001b993ca8ab289992f8dd2edb189f84f0fa4f52553cdbdd7c0743bd954ba36d86c5752dff9632c9555edd3e15838b257b755f790e5b3c02d86dd012a00b5006ac81fb60a38df5a1ead234ffbcb0dc7558943e951e13755a213abbc8410e35b80cad44171326c589566c373c33ffe9ec35930285d3ed
private theorem part114 : 2 ^ prefix114 % Spec.Ffdh.modp4096Prime = residue114 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue114)
    (e := prefix113) (a := residue113) (b := 2410714296) (n := 32)
    part113 (by decide +kernel) (by decide +kernel)
  rw [show prefix113 * 2 ^ (32 : Nat) + 2410714296 = prefix114 from by decide +kernel] at result
  exact result

private def prefix115 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (0 : Nat))
private def residue115 : Nat := 0x42715c2b03ff606fd91f4dbcabe8ded1cd21f0981041938cb66b7511c606281ae5ec5a2ebabc4aac530d571ebad62a1b8c36fb7f196164306192d27a0b73b2a0cb40130182e1f4ad847e7e18fec904725714d90a62fb2073e13dd24589b72aff80c1fffc605af21b6ee5035a20c8f3c252e5b09bbb196bfe5654b607c292f11263cee113d463b3e6415622c7787e6ded12308eac383b50b163eb191f12851cd72281805a6f342ff8d6a6b90cbe3fcd3b50fd78b811b62a9515dde0562ed65b33cedde416c5aeb6279f6e263dfb623c4513ed48d482488f2f3d04e8fbd1362b1bafb4f929ea2efbfb485552a7753819cdb9a403a3b10bb3a0028bce8b2b94d9f02f7ad74dcaa67ebc892f7e6c4c3051cfef2734592c6eb0b980a85966855ca146a9cfdc28370e56397f4e5b81331e34f504eb237c3d049631bec0eccfcb11c36d744ee4cc25368055efd8eba8b3f51d9b96a6125914a9f42d2bb6d169254a08402589d08d15a3e0c8535e13000d764710acbf9dbf259cf3a1dc7c3f767d42d8d46a8a77ef44f259483e0fd2bffa85af8626a6af63bfbb09d54086cad3c0554dff4fe86d15aeaab3e1b609dc6f76371d4b6dc2732f37390a4a4c4bcf5ffc41b43ef073c4d4d11f89a4bd06f26d9398e236d3d4a51be7b960e0d4a8b989344e87dd45136c214d872fbe58ff3ec2c3c6069bad1eb09e94fef19d6e3f005bf0ea7254
private theorem part115 : 2 ^ prefix115 % Spec.Ffdh.modp4096Prime = residue115 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue115)
    (e := prefix114) (a := residue114) (b := 1735486423) (n := 32)
    part114 (by decide +kernel) (by decide +kernel)
  rw [show prefix114 * 2 ^ (32 : Nat) + 1735486423 = prefix115 from by decide +kernel] at result
  exact result

private def prefix116 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (96 : Nat))
private def residue116 : Nat := 0x215896f02d31bbf19a5417a10416ae00191c54ce28d1c00c852ad841d358db9fb9d3cd8a8d63780f232460cea1caab2460938b5557d3a75800ffa99f4df72caa6635550bc41cd92446a8379deb3e727e9d29d89e73f410ed9d0876ddb41e0ed7c9719f4aaf467c68345618dbadd46d1638243c03813268ea85dd15b3da6b33ba67f0446b5092efbd884148a8f5870ad53270315cde3d218b82ef412eeb191e65c63b9a2d7b335404fbb5343729cbb85a2a75dceb3babd8bd3fb70c27e863bcc794bf7410460807d6cd511559d56d56fe782c8c13d863a525dda0d3bb13009fc9ef23c4751e68a5926f2dbee3ddd422ee34edb6c0c660cd75ce7b9cdf5b8a851c3a02503d847f2e4e14dcde830590a4cf33fb91e466e221bc01aa238f469b227506c167f749b02e9667c139d8f233465ac37d03d1608a56ac485032301b5658b9009da451281c349adf8c891faf0625112391b46b8ae9c5966e61899fe8aa3babd0a6cee94b6752da0fb7e3ceb6ed4f7be9f01313b152e37b1e7c59112804c6a3cfa55c0ba1d97240f60a102b9d90059beb3c152688d1bce6e4f8e2f25a89ce713c5d6fa1acac8a1491f13f3d5bad08b0ee16bd872355dd99136b664156b8b19a74c877875152a62b4709ba4d0c3cd9050fda9fe8fe8a1729bfbf1e74ef9e1bb9354e9b95ff58051abc669e7f4129646256ac9de1f3949ed8d9571f7291975c33
private theorem part116 : 2 ^ prefix116 % Spec.Ffdh.modp4096Prime = residue116 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue116)
    (e := prefix115) (a := residue115) (b := 3691900603) (n := 32)
    part115 (by decide +kernel) (by decide +kernel)
  rw [show prefix115 * 2 ^ (32 : Nat) + 3691900603 = prefix116 from by decide +kernel] at result
  exact result

private def prefix117 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (64 : Nat))
private def residue117 : Nat := 0xb89b9d3ba371f8cbab43e9c888d5bb2a142c9b2aeedba64bc5a7002e57949089cf928662f8c0da13a6dd99bfeae3c20e11e234150d7b14e6383391a756d7701730cdc308970c2835e1ac2799247b7b93903657f43f3c8062036c484d52e0b05e84ffda5eb44ebb3e5fb1bc7ee7de9726655a54329e29ea716d014de64b13d8a5166a3425250684a16698e6a811c214ad9aa89c4070d51ec33fde3b9611d374295cf5da498a164204e29d48907a4a8e1cd854cb1848a8cc68f10d48b169b3b22d7d88993e9dc4d4aebc6dd2380099dea7bfcab38bed1d7d62307662f92e9da7cce77658b564a5741cdb440eac17b60d1ce91571f6f6a37e439aa2b80c8ef1a9ef33d5b440a706949b3c63f61c89a0eef0ea5528ee5ad0031613828c921e2aaead0edf70dca48a7115665b5a7319540905ef21e38f5526a5f03a0b5a5444e9969b90ab5c5e4f75269647e0fa352ad188a1a5640e2798d21e2d64922cca4e014f98989eb4dca2fd77bd8e07559827dd15c38e21a46763168e575c2bf3e4622b56383085ca8e07e2dfa2c38265d97250f9bda5eb5848889bdf1587e217fde8bb10a6e1b566af0177f0c016e679e55d89fb38da3aee463fa338890044a8cf4fea6e10a4ce45918bbe42f5a2ff587c0455daec5bba6545bbbd78980d42a67417c23146ec8b314c1838477b958cec4b3e0360b856c61703868bb743f86e7bbfbe7b990b
private theorem part117 : 2 ^ prefix117 % Spec.Ffdh.modp4096Prime = residue117 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue117)
    (e := prefix116) (a := residue116) (b := 280503310) (n := 32)
    part116 (by decide +kernel) (by decide +kernel)
  rw [show prefix116 * 2 ^ (32 : Nat) + 280503310 = prefix117 from by decide +kernel] at result
  exact result

private def prefix118 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (32 : Nat))
private def residue118 : Nat := 0x17086a445b047537ed98d29020fb97c51727f51ad11c20896c0a09ada54dd9d3582325bb59055d56bfe4e306714e0a3cf0a05d4da181f5ab752ae178c9abcee7b10ad09d883e513a8756348d402f662fbe87eba2c8b558e4d11c816d61d66d62a5c5cdb9be77241c28b1615dc5df33dc178148eea84a3b6abada5f8ad792d8a3825d9bc45344eccedc3d27ace37466c7fbe39015fc0a30bb41eabdbd09103647cc737961a91e5a873ea9c761c44531f8288084f537cd96b4f3fed21d637bd3e6e0709cb82d95506ad78a733ebc259490b10208720a2c15fa6e94cc1a34f544e2ee56392061aeeabf56c9588c3d11b919467f2691470dac8edc3b2dc967f8af2066e62f0bac8ce5080f624420ff419a7b620a76452377d968db94b7c2347de6ee852c3ed75c5c873a44ba98f8326d6e34272ca5dc6540ee340cebf4a9a85c82219a1d245a9362adbd08077ba4b428798a3ca5a985d59b77eecf84c29cdf31c8beb0b2c9324b964aab3bf9afbc150ae531230acb97f1538cf69fc54e9e35b7aeae1d59289e92ab7da2826f4cb549fea155953f8987268df9076e1317b8afa2388834539ca0ab089f73c91be1892d76cf75b60f001340c7021e95ad3f0d366776a52f2d87616aaa28a013c919f421e296834a70e63b48db950a7fde8cab11f3bb03f65473237d4a35bcba201f67ff6e848dc6996b0dbe0fa45be37a05aef7843c5
private theorem part118 : 2 ^ prefix118 % Spec.Ffdh.modp4096Prime = residue118 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue118)
    (e := prefix117) (a := residue117) (b := 1745045651) (n := 32)
    part117 (by decide +kernel) (by decide +kernel)
  rw [show prefix117 * 2 ^ (32 : Nat) + 1745045651 = prefix118 from by decide +kernel] at result
  exact result

private def prefix119 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (0 : Nat))
private def residue119 : Nat := 0xd16b3cb83364cb63dbfa6477504ffcec50f8c6924df061c19cfe9c3dc4ba73c2fbf80129777dee6182f27e26e6bd307decf0a05e5aa145b437855b4eed8dbe60f15903993fbe3b509f621d5d88f1a1eee06be279d86b91603a167590555a9c8c3cf9ed09a956990d03527cf070558ad384f85034e5ac7c4d2f88bc7388fa5895e9b02123792f40e8b6ae0aab66b8825daf41ce727fcb68da2e34b2af35099e32b4bdbf6569fdfd267775a307a56cdd2ad128420b9cbecef439e24f350dfca8086d15f9497a359145572efb2fa55b741411aa703dcf78486024edac5a159a5ef9a5015ab65bd7847470584e8ceb9514d152be1501ffd29fc9b5fca6bc6f1c78ced4e51abe9c56f5c177ff9a90ea4f4e24b81d29745bf818ad41378862c08fd834f9acbdd5218622b38bdd87bcaf515c2b5b6d532e140bd2144456664549fd565c50e6575f998d16ab67d2e14b4e3d8cf1317ea222c98d4656853a6a64d6a5b2f8f8104ddd5dab9a1069336cb11d8d3266b89b19e97aaad16ea14eaf6474231f3c4383ab94e1d5ed9a03eed64bc6f06a5a0cb0e78a448b50323edb49a67ef8803539531baae22273eede0e6b54d5ef74e8b6eda5d955f1b45d8c3578718ba033750db01cf0a9904f20d95ffd964e9ae61aeb2d0227185183f28c68250c959abb22504548a7343c80ebc49685dbe805a91b11d8e55c30a6d8e4133d4307c7bff504
private theorem part119 : 2 ^ prefix119 % Spec.Ffdh.modp4096Prime = residue119 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue119)
    (e := prefix118) (a := residue118) (b := 3940035924) (n := 32)
    part118 (by decide +kernel) (by decide +kernel)
  rw [show prefix118 * 2 ^ (32 : Nat) + 3940035924 = prefix119 from by decide +kernel] at result
  exact result

private def prefix120 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (96 : Nat))
private def residue120 : Nat := 0x1d1bd8f192092b88683f7f8a98160b468767e183d4e6d86d682a3fa5d58dd76df4acc6fe998bb4837108fe1593e9abb15730348d9089e40f2f0ac5cc7f142726d1b5d06eeef571d396da9099407fb76c8c68e4ccbb9f3501c449fb80b0b2096c3e99f72492a39faf15ea9877d74ed48cbd9106b33633281bdb7c919454a40940ec1b8a9aef70c1d471e21f824a22baa64111d11d41469c3daf9dd0141f1f8e181efba48411b765c29dfe79c5883315c4f367cee194a469d183f0b15ecb97f8121008deae797b89b0ea3ad827609b602dd68ffbb98aa317ae56cb88141f34d7b6c5caf25ca42318725a1b93af90f28bc95c3aae77dfefba0d6c59e0d3526c5ec06058329a07ca212a7c34fbcc9781c5847eaa57581ba40b121b707b060af33e9426ec3e42c52f620eb56f86f093212276bbf0bd680ab8fac291fac38f1357a30b41b250bfb110b1ae4d134ed781167796f65769184eaf9d6857341cd70957cb179815e778fe0018b11a17d12bab06a30b06dba2e6787773a54a1a5a4b1500360fde16acb4ddd8462685e6c76352b28466234d28b2a242ab44bcdc1c15f2e6caf0cc01a73f21dfe05de8c0ffec2a2f5369dc740dc3c969f3392cd2285bbe3cf8b63fb4be2c0eec2626d24b481a4be092c78c9d3423056aabc1f19a7a31de2843982f6e2e87af0e1fbd3121c99a4f6ce155b2e0f64816661ddb152d08d389b289
private theorem part120 : 2 ^ prefix120 % Spec.Ffdh.modp4096Prime = residue120 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue120)
    (e := prefix119) (a := residue119) (b := 3386537292) (n := 32)
    part119 (by decide +kernel) (by decide +kernel)
  rw [show prefix119 * 2 ^ (32 : Nat) + 3386537292 = prefix120 from by decide +kernel] at result
  exact result

private def prefix121 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (64 : Nat))
private def residue121 : Nat := 0xfd3501459592f461b21d0ab782f4bec623c516d1bd878875805d394114e523ef9503263adc45a6358712735c77fbda352dcc27faf604ba9b47324a01944be144e04a024b07bd39964760da1620bad51ed8f20be94b5998b5ba0787bd0f71a61f36aa1f5a2190104f8f9507719e03c2ed19edd1de8d81c2c15f025ecd2ed4ae434ff4d45514d8663e813ca57ddf680171f69d7c1b6ee11bc13311fc6801f6864ea4913100993148d1c805b2b4648f5094ff9d2ee1a0babdd265e16fc5344fdcdf11d659a9ef1e6bb9d07529684c0fec623fd4360ff9496eeb2a043d31c8e1bc57db636ae994c637996f2a985acc9a98546c77fc4cb0777489a6c7f0b95702a7d538c20b192fc85643e7830973a85cb4d99e06440bfec77eea3ebb5ffd3125ce4754ab5ec65f17df4d28f03e62f6425f95d51f574377b403a44d5093caade03a98df601bc45e5dd7c6d1891f382a4dc2ab3413fa70c86483713ad73d3798428ffd4317167ecdb5db355f1dee68cc95e1484d381008864f7af751c7aa9a43ab89305d7bcf70d45244d5e3fb4b3d9dc21300408df1f26d6f3d471edb2ff6a74e20bc8a3543209016f7fb45e845b4e0856bdb634b5a7864127140a1408d7498663a9fcc36dacab084d3c4ac56f69950878183353a1de1843654f61f3642453ca3c446ec92f2ca738d8d912a9d4dfa12332962777ce76ddb36c28a87d2b77734c6a05
private theorem part121 : 2 ^ prefix121 % Spec.Ffdh.modp4096Prime = residue121 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue121)
    (e := prefix120) (a := residue120) (b := 1187507936) (n := 32)
    part120 (by decide +kernel) (by decide +kernel)
  rw [show prefix120 * 2 ^ (32 : Nat) + 1187507936 = prefix121 from by decide +kernel] at result
  exact result

private def prefix122 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (32 : Nat))
private def residue122 : Nat := 0x9a4b5f703694ed5cd5e84336718406a3392f8830cb08ae7f3cb941d34630cc8c569f1251f75783da03160de5024913625c1cefcfd9ff7927fa751e41c7b18c8a7bf3494f87346e278590343526592ea5d86addac49ff7dc2354387ef229dab2d7cae9094fb01f0bed04e16b536fb12f55ac366a5994e004fe9f1de46898d8db2e7e97b54a0665ede6b6c67e9a0d15b4f8fc54024b9f90a6d561ee21286a0a27c48620dc44e82b9cebc04852e92c3294e44967db50fd9ce6684df38eeb878c440db085c7c3cd77d7fb3b770e117e05ae7055122c2c6f97b5540cf711271f9caa6955938b09fc7b7333465824f3bf0c276b4587ec8ab2cba7a203522caa2bcbd0943b3b9b803f402642aabc620ba057e90a9f1483db01092b6deb4e66406f638a995f538062cba70c79b79e37e1b4eb5567c3a02b1384c59eb49c05eea2d364f661fe305b68102f6ef14377e9b975bb11a95158a46c6e38fdd3e3a2e3bacc26003afe18301b23e3fc700d46c1ef4c93e2daeabcbfb64aabcaed022d7d3b47deade433c573a6ae0cdfb391e7d01d196b4756a85ccf81332614e4a8b565b0ddf81cb0c98438740d7b9719c3aeaaaf70dc6c09286612a14267f4065aa473608b02e6df13cb734c0f49f230c127302da81ca995b4218ca93a513aaec11be6621629ae01ac0d3b49cd51a81dfb8e73b1a2b2caaaf079315d3eeb2405d46117c6c05cad2
private theorem part122 : 2 ^ prefix122 % Spec.Ffdh.modp4096Prime = residue122 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue122)
    (e := prefix121) (a := residue121) (b := 3279936494) (n := 32)
    part121 (by decide +kernel) (by decide +kernel)
  rw [show prefix121 * 2 ^ (32 : Nat) + 3279936494 = prefix122 from by decide +kernel] at result
  exact result

private def prefix123 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (0 : Nat))
private def residue123 : Nat := 0xb2b988a741bccdaf92e05aa12d2ec7fbfcdc0e58af12eef26b2c0a691eba9525b0073d99b57538766f29b73361662269c65da3ed0f8dbbd6f41df95d04d1e8c568cf6d39d58c9b0f342044bd769be38ea5ed67560af9c2f7f71a167eb39fa90766a1d3a3c74ccfc604f1dc0ce06a39545bf12b053beeea9cf96def5aea88eb8af176a5f5100fcc26e03185c463a94d3ccb7e0364de3d7bf4d19ef0919d1256f7d812fb26f34b28587453c651a8e7e0f677dbfcb371a8ebcb88adc0c597faee335ecdbd2a5031848eac87993cfd079084be6170541316278514e70468cec86d958e4a1a456cdc2a0e9b7afd0f3ebffdc45eb6e2b2aca3acc00b312448362f4842e70c65d2342db9a62b50648aba6a77e95cd99da2b22b3f07bb74129f8cf275c8e0b10ea21620cc3144ef6d77945fd32261d7a56d38787a7037c535918e40fd62c05f3f9685b8f9836741cbf404ae5dd20807bfe598a6d0d2e96d80b252fe3da3ebc42a363fc3f4a1f938e292211ee985d0202286392bef1f4bda7322ee900190e741700a30a07b56c8956310911b6276fedf8c171271dd7893ff261e62b644763e20dd29f05bfa5f8c08aa4c5630aa4d5fd4a2bbd5bf6dfb2d4b41d4904a26b5e80b4ffc793ff196300a2af76ab1f2bc7d44a8f84982f0ed75a63fe9596298382976ae253aa64a7e2fc954975f9a4b59d416c60abd344cfbcc9da65a7f773dbd
private theorem part123 : 2 ^ prefix123 % Spec.Ffdh.modp4096Prime = residue123 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue123)
    (e := prefix122) (a := residue122) (b := 1213423687) (n := 32)
    part122 (by decide +kernel) (by decide +kernel)
  rw [show prefix122 * 2 ^ (32 : Nat) + 1213423687 = prefix123 from by decide +kernel] at result
  exact result

private def prefix124 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (96 : Nat))
private def residue124 : Nat := 0x2e5fa1bd69a8759db4d32db7065a9cdbf612870eea074abf193866418ae04ddcdd38b8518dd28ba8c508273d6342afd0736bd629748a3e392ccd504e1005c163158b3c637e041d6dfc223e22ed11028ecfc4c16c075226662be66581529215a97c7e99ba3049782236fb0364d72d132f4cfa3d628a69d6c05fa86920ab64cc6fd8521a1cb4f9900c28dee380c3f5cfb083bbe275752a41614b388f95e1beeab024fa7a686637e483a1ea6e81f6492b34b873631324dcaefb05bfc884e830c2d3abf9c95f3ee506145b4b0e22da9842cab8cd47ca3ef2c1e08391626ed02a8eb4137b4a50fb82b408fb0f488770d7061a3c5fcd001e81ac84f0ba121a6e3d49a93930496a6fbcae456b456680a40998c481579ee3cbea9532aad779d2da74dcb8fb1b99e9b6ab5a36a5115b73084f28509d0dd4b0a149ef0f51e97d081e207c7ccd51e11df040d4420df71b99fb2f4b55c62e3832e34eaa2651bebd744d295899429f78069d7dc242e0837e82cf5a8b4d7d8c8d33b96fc3f2f11be1123305a6f52c15e49c6f13a07844508336e081fbead782534ab564fa21dfc8880702d606bb8f01c62bb0d0065320205106af819083c43dabab68dc8227c43a9b9a2e6d905e800373f46300de7291e5478b5b3b4064ce317571ff433d6c290d3f3dea996dc1a8dbedf6903cf59199482b1ff9fe523688f7120b5e3cc1816475263929212629
private theorem part124 : 2 ^ prefix124 % Spec.Ffdh.modp4096Prime = residue124 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue124)
    (e := prefix123) (a := residue123) (b := 2801408740) (n := 32)
    part123 (by decide +kernel) (by decide +kernel)
  rw [show prefix123 * 2 ^ (32 : Nat) + 2801408740 = prefix124 from by decide +kernel] at result
  exact result

private def prefix125 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (64 : Nat))
private def residue125 : Nat := 0x4bc499bfdad38e3e5a65e51dbbcc42884e7cedaaf0d2e4719e6185a4a507c2dfb212e454d5b351bba6d848b8e3d270464656dd2197d9ff6443c0fecccd7f5a8fac02a8bbabbf9d4d852aebcf910ce7eb0012bbe9c9a96da0198b61d9dd0425012a0a5228c20473e1ba1505424ba044189acd9d644c820ef320c0eb0c20862b4634909480ab61d2714e730fe2653fde156cbea343c790bc6029368c94634f585e505955a04803b084d00bdeb6e62bb8499765af5fbcab4c5b4c9bf6df1a829b51263d1bd63c36e1e37238858a76f6b922a20cd6e41874b589f0b169d40c5d2034cb63824ed8379256e2353d6643b0eca3957cfd39ffb4ea828d2d18b36649648cca97aaae0422c48663303f006fe1733dc3eeaba4978e0a4cbf5bf3fef390083dc4b442a58932b46389b894e75c9f2008137315591c0f935c154afdfe8c47e11bc21bc944ae5bd7f05ceeb2c7896324e112017c74efd9c449f14e3e6bf7e4fc30b47cff81640b3dae306bdf4c0d2deeab167e176e5bcab983f34db39dcfbca74824bd5c5b54a701a38bfa099f16bb7f50fd3fa8f4f89bd6d7423d816a4bbe60d44214cbd68120c9e7bcb92231c56fb8d4538262d57bcf48d3e68e9d6788059c297e54774a349c38e6663bd9725eff96457194f00233a3920cafdfce42104191fb7b3638676e65cadd7d57e211973c23a14ff53e4c04f5893e68071edb6233c6c7
private theorem part125 : 2 ^ prefix125 % Spec.Ffdh.modp4096Prime = residue125 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue125)
    (e := prefix124) (a := residue124) (b := 2583894220) (n := 32)
    part124 (by decide +kernel) (by decide +kernel)
  rw [show prefix124 * 2 ^ (32 : Nat) + 2583894220 = prefix125 from by decide +kernel] at result
  exact result

private def prefix126 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (32 : Nat))
private def residue126 : Nat := 0x75ea93c842113024523d3c3afba44d24c7f75439eee7563fbae731a75e2a77edc31891c85022dd9b31c892ddff54e1bfcb27c83d74f08fbc76880be27662ebcde2b429a2d6479d327d5bcc9d7dafd8fa5c48ed78ce6ef7c8aa8f66a5dc071d317bc206703982b895fc72aa360e3629dfac9994c51c40470948abf0f61055938f00a0d754881ed99f6deb57333680302fd9afbf859ff84bffd55d4467e4920aced89e0dba8677b386cd1de14088670065af3234538280c3d158eabe577827a26fe81705ed9be96c05ce101710b21478ceba915de9df515ef6ed3416a53dca767b3f44572ae97a638b830f51560256b36e15791e9e29077e7014a7cbef38c6096eaa049691953b4d82dab028d37270a07b12b18c096de46d9e3c68da7e5befe75bc69d37337f81e07da70a9b9a7bc52d3f9a24e54feda9b3036997233db46dce2d24d869f1cc107e3a1773c504da57b4ffe93cd117aac9888fc5a0940296698d3acc7354805767a2c68f53b4618b77abe0f7f6039efd0919992258d962ce23b805e76401f08c4a2695a02eb5ca8772f21488e8a49cffaa2c13a96bc559c604a21e484dded65a7ba3b6529cd635d935fcaa0689fa58c5b617f1de60a650e5135f7f80f7aca10afb689f502543683add9b6853a29f67c655156d2f58f8af3568fd96e4578543182c8db62069f93787ec7c88eae70d7f0797a1ca24d6e36b72da647a
private theorem part126 : 2 ^ prefix126 % Spec.Ffdh.modp4096Prime = residue126 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue126)
    (e := prefix125) (a := residue125) (b := 4294967295) (n := 32)
    part125 (by decide +kernel) (by decide +kernel)
  rw [show prefix125 * 2 ^ (32 : Nat) + 4294967295 = prefix126 from by decide +kernel] at result
  exact result

private def prefix127 : Nat := ((Spec.Ffdh.modp4096Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (0 : Nat))
private def residue127 : Nat := 0x1
private theorem part127 : 2 ^ prefix127 % Spec.Ffdh.modp4096Prime = residue127 := by
  have result := powerBlock_append (p := Spec.Ffdh.modp4096Prime) (r := residue127)
    (e := prefix126) (a := residue126) (b := 4294967295) (n := 32)
    part126 (by decide +kernel) (by decide +kernel)
  rw [show prefix126 * 2 ^ (32 : Nat) + 4294967295 = prefix127 from by decide +kernel] at result
  exact result

theorem subgroup : 2 ^ ((Spec.Ffdh.modp4096Prime - 1) / 2) % Spec.Ffdh.modp4096Prime = 1 := by
  rw [show (Spec.Ffdh.modp4096Prime - 1) / 2 = prefix127 from by decide +kernel]
  exact part127

end VG.Proof.Ffdh.VettedValidation.Modp4096
