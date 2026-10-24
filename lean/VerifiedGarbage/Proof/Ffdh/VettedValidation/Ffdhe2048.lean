module

public import VerifiedGarbage.Spec.Ffdh.VettedGroups
public import VerifiedGarbage.Proof.Ffdh.VettedValidation.Power

/-! Kernel-checked binary-power certificate for the published ffdhe2048 parameters.
Each small block checks its arithmetic; the shared append theorem composes the blocks. -/
@[expose] public section
namespace VG.Proof.Ffdh.VettedValidation.Ffdhe2048

open VG.Proof.Ffdh.VettedValidation

private theorem initial : 2 ^ (0 : Nat) % Spec.Ffdh.ffdhe2048Prime = 1 := by decide +kernel

private def prefix0 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (96 : Nat))
private def residue0 : Nat := 0x15af118f78882b63c08cd208dbdf4aa40ceccddb5c75be0929e3f7d53216493eee8f1f4332a2e364557d6002aadae385d2a09213c186eeab400f226816c9993745eb15b4a082349d51fbf7128e1e41b18f3accb2673fbd0b12d808e6b17a26aaa8dccca3a28bdce54bcf544886cceb8b769bad2ba068323a27290b372b9648c8a19fc2b67e4729520718c7444057fedbd2c27f4ef594988876fb431e1618cefcd6a354440dc9011268904291cad4d4aa6f2388b28b14c9b5fbc8668f1f8a7bc5573e5402aaac2f600829c83b4db09f957c5cf90721327e36d22e9f52aa3d4758f444a215d1f14709d63e520d45bce46ad4d6b8db7cf5dbe58a1fd70c6151532c
private theorem part0 : 2 ^ prefix0 % Spec.Ffdh.ffdhe2048Prime = residue0 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue0)
    (e := 0) (a := 1) (b := 2147483647) (n := 31)
    initial (by decide +kernel) (by decide +kernel)
  rw [show 0 * 2 ^ (31 : Nat) + 2147483647 = prefix0 from by decide +kernel] at result
  exact result

private def prefix1 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (64 : Nat))
private def residue1 : Nat := 0x660a89ca4b98e66b03348cecb07014bd7491c39ff02b83080572d5d6f89300f77147b154a110dedfd5b0835ce8ec51ef4d0fc6570de9a5c7c149fe4b8fabb75f558705664f84754fcf400791ff480b1d72952f3edc8872c7e5fe9631c371cf63a8246d81d8fae1c656356abdf8ad49e2ab317a06656270449a29826687a027976083932ec9f9706012d0ac5904d31222d9999797e9222f0f95950d90d92954ae4bfb76af66aea6b41100de5c9c274d83bec8f4b4f8055a5c8d9ce3d27ae9c599062665121c739535bcc3078b66216878fc9af1c8558c4b4e190d6a5cd501452690c32b20dad4b3cd2610ca27561c604ea959b6d66730cb4648905c516d30a9af
private theorem part1 : 2 ^ prefix1 % Spec.Ffdh.ffdhe2048Prime = residue1 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue1)
    (e := prefix0) (a := residue0) (b := 4294967295) (n := 32)
    part0 (by decide +kernel) (by decide +kernel)
  rw [show prefix0 * 2 ^ (32 : Nat) + 4294967295 = prefix1 from by decide +kernel] at result
  exact result

private def prefix2 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (32 : Nat))
private def residue2 : Nat := 0x50058af1e688009c60103448a7d35c51a92edf3455002d4c2af0b4e427e532d197ba9939b347e62c924ffc52558fb74eb208f78fe15ab30eb67f4ff266cce48fc0e793facb5f3ad870473804fe25a467a36931bbcb64fce9bbb3745c01b563aa7b42310fee8dcfd2aac4e1a0fc4780b7591a8d27cd98c7c48a2b4b92cc0d11e4a3aedbab98dab3ba9d6fddf6980c875ec0495c73fed25598161a9dcc818a71ac39ee15a6325da81d378955a79a792fe4690f1f25c9cd063dc3b6765460f958cb031b0c4653a58b26fe98d3296ec0efe0df768e29a37a87f454213e88138840fd724a1b0df020d5ec6a2947e33871f5543fe6ff91a9d0037d7bf0e29a9f1db18
private theorem part2 : 2 ^ prefix2 % Spec.Ffdh.ffdhe2048Prime = residue2 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue2)
    (e := prefix1) (a := residue1) (b := 3606850092) (n := 32)
    part1 (by decide +kernel) (by decide +kernel)
  rw [show prefix1 * 2 ^ (32 : Nat) + 3606850092 = prefix2 from by decide +kernel] at result
  exact result

private def prefix3 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (15 : Nat) * 2 ^ (0 : Nat))
private def residue3 : Nat := 0x1fb71c569a80387b639d2de76f45679628aa34259a4c5eda02d0e1db6a9ee8d040c1cc4f0191c1834033794b090bdaa6206e22c96aba621ad5be9c65cc45705eaf7c452c813ac7a5b7387efdab5c0ec29aa4083a429ba4856aa062a1e4a95762834297f66d918348af3b4c3671e5401d08d6280779c54844c55ac979855f75a3c584ab5cb172df17a657d1076dc199941d67a95d69ade9005f72f3272c432092cf4f1c7d1946f05a1d93459a45ba57f5074dd40758a353552cae1b0bce31a3f97b985b30894545b2e3219e47ac3da225bb5e97610ac7dba3bbe1682c413f5e6332ecbfe3c463cb41cf6a6446de3f1742ab4168c8180b4f19b417165784a4ae4
private theorem part3 : 2 ^ prefix3 % Spec.Ffdh.ffdhe2048Prime = residue3 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue3)
    (e := prefix2) (a := residue2) (b := 1365091661) (n := 32)
    part2 (by decide +kernel) (by decide +kernel)
  rw [show prefix2 * 2 ^ (32 : Nat) + 1365091661 = prefix3 from by decide +kernel] at result
  exact result

private def prefix4 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (96 : Nat))
private def residue4 : Nat := 0x5f8208e0218341033139dbe78af2a4d035404c1815c646bd77af34e36925e0fb823849250f0d90b73a9d49aa514ad5952dc78d4b1ee34db2b17cf14de32c3a3cd3eb6f3230e13d9d2da38e0e3b6930f7e1cef1866c13e813ddb61f0b965ef046820b8032b0c815dee5c074fe674c259cc7d2ece94326a2d2b59537a2b7c40a2cdafe4840072a41dd3725bb9a1a2cfcc8a3158bffe3486a90e006f6d2b0e8e3a64155953e1a3fb502d0adbe33dfee8efdacea9bd212a57d040aef25ec511affe286361a89fa8ef4f9a6151a665160aa18fb3025ad661d85df390424b8b8f6ec9682ef18b18223616e799c7837d4d83b67e445ebfab13f55cc87f426cde7589d55
private theorem part4 : 2 ^ prefix4 % Spec.Ffdh.ffdhe2048Prime = residue4 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue4)
    (e := prefix3) (a := residue3) (b := 1475226384) (n := 32)
    part3 (by decide +kernel) (by decide +kernel)
  rw [show prefix3 * 2 ^ (32 : Nat) + 1475226384 = prefix4 from by decide +kernel] at result
  exact result

private def prefix5 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (64 : Nat))
private def residue5 : Nat := 0xfbbd693d34b690d858a555f9d5afef905998772a29ae32d113448e0d8794d7c29fd0261160907ce0b271eb3a667797b25c71c82657d508651e97f76192a1e9bd8134b514b900fbd9ffd8f46b2b8355469068a4565e04d5d1711c6649644412f9df14f405e7076a3b43bfac4144f3de052a0215783d18df1981fc97c5129474605687f1719a98b1fcdc8a6ac3e268e652aa9636b71429b8915851beff69934f445209517910ac8915f302bda544a37c1f5ad26a3fb6e9bb79874171553751d9f4a8cb688eb87898b293b8acac737281288da82d836b9a2d291181f919de6b7d895f5840fed7bec3dbbce50c6e8af1a075b6ee051d3717e7bb24167ec370b2c3a0
private theorem part5 : 2 ^ prefix5 % Spec.Ffdh.ffdhe2048Prime = residue5 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue5)
    (e := prefix4) (a := residue4) (b := 329162360) (n := 32)
    part4 (by decide +kernel) (by decide +kernel)
  rw [show prefix4 * 2 ^ (32 : Nat) + 329162360 = prefix5 from by decide +kernel] at result
  exact result

private def prefix6 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (32 : Nat))
private def residue6 : Nat := 0x97c011f3393c08bbef645645b65707067f7e59dda6d81fb4673936d5d0e091a496160c97fe23f8317784d5ce9650e235693a4e99fa571d8c1d09aa7152ddcdc1c05ac0af58d7a75fd09632e7e1e4f72de65a43cf86e7bad81c6da99867ef5a92f92ea94f32a6d19b2135e7de63f1d0b35bd89f625c877d74258c40445b343f17071a2c3dd09f037cefc73e7ab0dcba5fdb724b7e7dec22816ae834db89a7501ae131e4fa7f81b9965388b9f7458a8e7331f4f0c4d25be5303eb2db38a2f69b234a5698ad6383f5919b3951a63219575c1b85e8dfbee71d1b5aca4624ac7039c7710eabdbaa0dfb225fd778b0cef52bce1adb7323b633dece7c53becf699cc773
private theorem part6 : 2 ^ prefix6 % Spec.Ffdh.ffdhe2048Prime = residue6 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue6)
    (e := prefix5) (a := residue5) (b := 3965510337) (n := 32)
    part5 (by decide +kernel) (by decide +kernel)
  rw [show prefix5 * 2 ^ (32 : Nat) + 3965510337 = prefix6 from by decide +kernel] at result
  exact result

private def prefix7 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (14 : Nat) * 2 ^ (0 : Nat))
private def residue7 : Nat := 0x5ed2f302381839854bf7e45a6942501f04633fc31011b6d8a0a1a458ee937cf5145d733ba68c1c6e7abc016d42da4d9d3e2088f4b6ecd421adf56c11613dc0d16ac712aa37c11690a7c9d29479ae9ddf573731d1b9f2c2dae5110cbb556926858e94df4f1d97a2ba231135e1d75c0460af24295632ff6023ad119305435b4fafa558664de70eb8b21f39f36f7dde44c7d289a07610e5b50cd519325880729828baf0aaff293c36d04001ce6187c11d5d16fdf3228b62a697752fafa3cc0acaacaa347c8fab58ea095a07191d5b995ab406c490772b1c7ffd13b6f60bc4ff3e7a705b185d9ac6e39c73d430f400d6943d1f53a65c85c561db8b037ae444c213a7
private theorem part7 : 2 ^ prefix7 % Spec.Ffdh.ffdhe2048Prime = residue7 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue7)
    (e := prefix6) (a := residue6) (b := 3877018442) (n := 32)
    part6 (by decide +kernel) (by decide +kernel)
  rw [show prefix6 * 2 ^ (32 : Nat) + 3877018442 = prefix7 from by decide +kernel] at result
  exact result

private def prefix8 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (96 : Nat))
private def residue8 : Nat := 0xbb6fc43161cbc4501b47b076f7ac041257774ced802f7922d1f2d90a70217083ccbdcec30ec1ea10618fbdeb798cff9b7766e8bebabc27cfc0ebb67af160c8acbf0c4a9e749bc11603dfa9eb5e87dc19e33e148b57ef5488c7ab9ed50e3516c791c8ab214888fce71815a96fd19b85c67d2742cc4c61d193648c6af376dad416ad5aa6f4d5298d0afd69ae8c71f4ee9412394b9a31d03d4b1a3ebb2215123998751767dccb7f00915b2c6868b6eb213a0e3e6176fd85f5dea6f7ab3d0211cc8761f0fe4d3841c42b7d3225f490c4693795408023787706f59a95f426fc543acfa45e10902f0e28fed3af434d328e5227eb84d373b50554d45db26f174b5de8f9
private theorem part8 : 2 ^ prefix8 % Spec.Ffdh.ffdhe2048Prime = residue8 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue8)
    (e := prefix7) (a := residue7) (b := 3572538144) (n := 32)
    part7 (by decide +kernel) (by decide +kernel)
  rw [show prefix7 * 2 ^ (32 : Nat) + 3572538144 = prefix8 from by decide +kernel] at result
  exact result

private def prefix9 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (64 : Nat))
private def residue9 : Nat := 0x2f36f432531dbd9e3c19cf8cf93f7655ede90dc48a8763cda0da4d5387217464cc672a2190280edc19a2fbc0ee48cd3716c0dc693d69c6a17b3c1b7b51bb22cf7d9b22c638adeec11845e2e13131654bdd6fcf7786f39390ae4fbe8beec55e212f0a5891305b0b421f74a514426567d029cac6f747b94f8d755f463e17b7a58eec3f9a55da84ec9b03ef1d51c1a9d4766af5e908aba5aa579cf333c498233c02e9ec579ee0d815c5c44550870b481b8a6fa5f2852d912e0006ec58eec017eb94eec224151d5c963f2bc5ebfaaa49f07e475e70db8e5bac47f8805e99dde51a68449133bf3731f36a726a6d572ac3ac7a28d55ba1352b295bb6a4b65f3cf821c9
private theorem part9 : 2 ^ prefix9 % Spec.Ffdh.ffdhe2048Prime = residue9 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue9)
    (e := prefix8) (a := residue8) (b := 2318539261) (n := 32)
    part8 (by decide +kernel) (by decide +kernel)
  rw [show prefix8 * 2 ^ (32 : Nat) + 2318539261 = prefix9 from by decide +kernel] at result
  exact result

private def prefix10 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (32 : Nat))
private def residue10 : Nat := 0x7417796843bb6a6fb34568cb8a2205e60fc30e9a02b6a6ff7138a4fb43f636ad9b0aae0ddfb63b18642b6be93b5d9024b88c119b6dea0b111c751166d650d08a42e9b4cb5becca951114c055e57493f2b73805a36820d876b6380e33517d637f4b229bfb407dfee7583b419569dc2f7d64b8e98ab8fd73d4748bb997cea85edc8e344b8bddf40d4a56bf8ddab5976ad5d012aa1632dbd85b0ff5b42239de1f1d4837a701ff1fd9e8170b76c44e0a79c6c1bf28579c94351d44a2691536c5418ccd22750d1a1bb3b9eb48662d1076898d2d870cc0dffc2e2ff74651c099a0b927d6eb88dc1d51520b81891f15418d17ffbb161c6a7b8f3f594857d70bc8c9750b
private theorem part10 : 2 ^ prefix10 % Spec.Ffdh.ffdhe2048Prime = residue10 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue10)
    (e := prefix9) (a := residue9) (b := 3863596775) (n := 32)
    part9 (by decide +kernel) (by decide +kernel)
  rw [show prefix9 * 2 ^ (32 : Nat) + 3863596775 = prefix10 from by decide +kernel] at result
  exact result

private def prefix11 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (13 : Nat) * 2 ^ (0 : Nat))
private def residue11 : Nat := 0xf72c4282b7b16a210cdfe4db1938ce96024c3add0520a9e5f50f0c1a3bcb3b8c89b4f3002f8fe1ea38a6187d974b1bd434f34742fbf5aad4c0ccdb2f44fda0705c382d2122b07042ec27a0204cac1ca3a5bf6ae5eb8ac7ff45cd64b34a689b97e381510b234c9fe7c942d16cdfe87d7fd3cc3af9323043ec5afb838e41b45726b2867dd9aca54fbdf426df74e609d6344e3fc14ec69459d160bf30fd3716d64ab29792fbb109dc275eb584aa3284eb42213e537fa83dc5b2cacc6cfa85f9fee5139d60024a62d701db22573b052bd55d6281fc64b85ef77e7b6676852688990397ab7f9ef8987fb8283efb4afcce0f0e96ad99e1ce92b56a43c88f9a185186b3
private theorem part11 : 2 ^ prefix11 % Spec.Ffdh.ffdhe2048Prime = residue11 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue11)
    (e := prefix10) (a := residue10) (b := 307076988) (n := 32)
    part10 (by decide +kernel) (by decide +kernel)
  rw [show prefix10 * 2 ^ (32 : Nat) + 307076988 = prefix11 from by decide +kernel] at result
  exact result

private def prefix12 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (96 : Nat))
private def residue12 : Nat := 0x227ceaae446983d1d1b78dfd8a1bb363efe081c7578d15459c14b0dde5bd00dfe5ed7d4c988d5a89d546bacc44f4888b8e23055b0eb3defc28f982524357b8aa8a150ab695a60ae89f75bc2341feb21374cc295652e909671ed6e15ff3ce314d8610bcde244363198d1a7562ba634ec4ef712c31a28b4d1f2a29061ff4ad952c8549da536a46b1668580e4c80ae0892001b2e0041de0e69bace9cb35e131574e87f86df85208df944e7c90d03a9510020fd2e3dbfc610e6500794f3aa87964b323af5ce58b0d1ed033eb16bb8e3c28fdc89ed4dab04a52c548003b4f3ce953c6b5efc41bcf996bdcae1bacb218c453807ce3d74cfe670084e9749319eaa156cc
private theorem part12 : 2 ^ prefix12 % Spec.Ffdh.ffdhe2048Prime = residue12 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue12)
    (e := prefix11) (a := residue11) (b := 3197628849) (n := 32)
    part11 (by decide +kernel) (by decide +kernel)
  rw [show prefix11 * 2 ^ (32 : Nat) + 3197628849 = prefix12 from by decide +kernel] at result
  exact result

private def prefix13 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (64 : Nat))
private def residue13 : Nat := 0x72835d4bfcddaa692567602e3ea43b54a8c413a55e11dc4c426141ecc77adb1a9890348f201878a2bc3a583019f8da72b4540a69e34158774f56676ab370f921b17adc05df0f4ced8402e23bd0ca90b6b0edb55c5b6c152c964f6c4174265fc255c3b1a730888aca382d9fd3bd128f7fb3955d424c9af4922dfb33c79af5e0df911b272c1a526198df436e08375b57e03e774fd4c08f516fe7f51f43bab4307f8d8b6d49802a8111dbdc79fc59929a987e264059507012eb11948361401ae7a7d22e77705816daea0097f69451b93625d2aba49d57af26d14302caca78c9ad1f3ede1701d2ff7a06a18256fe3cc7949283db8aa47acfdeb9d01a916a14cf3675
private theorem part13 : 2 ^ prefix13 % Spec.Ffdh.ffdhe2048Prime = residue13 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue13)
    (e := prefix12) (a := residue12) (b := 2978364140) (n := 32)
    part12 (by decide +kernel) (by decide +kernel)
  rw [show prefix12 * 2 ^ (32 : Nat) + 2978364140 = prefix13 from by decide +kernel] at result
  exact result

private def prefix14 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (32 : Nat))
private def residue14 : Nat := 0x7bd96d033649a696ff2194695efb128a58ab7749a33971deb812aa93e51f299c7c9dd0f3a4593978bb864ea1748856bd42ce8c3cf8b4ded407f7faa4ccec28f4019741aabe2e138882741e7a96a1feec7cb2148cb8db9ee66a5226b71265811c97f830f3b47fea0a05c093034523fc14a5aa53dab14622e48a83a922ffe5fa9da46972b00a0b0f062888f6314184e5881a12426a658770229b11aaaabe9bcf2115085432877364f6993d88711d9948f2c4ba5338ade0861939adaa5bd65e8cc14ff099d56cca3eb652a9c29adcc0abe5bd4b9c5caae8f5239056688db1914457cb5c10a48af4f21821a7be71abb1bb84dd7980d91bbe1281babb2be1af36ffd0
private theorem part14 : 2 ^ prefix14 % Spec.Ffdh.ffdhe2048Prime = residue14 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue14)
    (e := prefix13) (a := residue13) (b := 2067847425) (n := 32)
    part13 (by decide +kernel) (by decide +kernel)
  rw [show prefix13 * 2 ^ (32 : Nat) + 2067847425 = prefix14 from by decide +kernel] at result
  exact result

private def prefix15 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (12 : Nat) * 2 ^ (0 : Nat))
private def residue15 : Nat := 0xf8f54a7126abb2e4e53a9fd8964eb23f7cb1df2cba3fbfb672402db468a09d9d65101e7da1ff1ccbc262a5a66fc76552c545653bfa3c361686c683b0421716049488bd28bfb0c463d604f6013ec9651a758459bfaf15a177188c0819fac1f3c57f396c3a367f092cdae47731b5a342e2b3c4840c7d30d364b415a4f24d890910ef29f98b15ff5eb1ed6114c4920abf36f61caed54d56a5f6fe73a6a7f79250408ab9267c38079d4b5336de50a150b0a2c7714eb0ce82c7037dbb829a39b0869a58a66323121f6fdc2714c200e9b0029f23b3b08aeffbd8cd77ec55e6215098e05984cfb52b7d066241f1cd0fb32f73160895a836ad19896f4a87752a99d020a4
private theorem part15 : 2 ^ prefix15 % Spec.Ffdh.ffdhe2048Prime = residue15 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue15)
    (e := prefix14) (a := residue14) (b := 1466052797) (n := 32)
    part14 (by decide +kernel) (by decide +kernel)
  rw [show prefix14 * 2 ^ (32 : Nat) + 1466052797 = prefix15 from by decide +kernel] at result
  exact result

private def prefix16 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (96 : Nat))
private def residue16 : Nat := 0xbc05e6f8c412b71090d01781de42da46d583346e8243f4404d83130b9838af30d3f26b01235d9ff1d9039492f930f09e1615b4d3991d3a7ca1b87a0fa3d602e72502b67c1c7af6a2a2a93f1d5128175b5d1580eb1d43d068153ab20f08352c561b1dfb7f43627110a378749cfaa28451cacc88c9427d03f83cadee08f1d7bcc743c721c9e05757691872ea97b879bbcd0d2539948a5ef88faaa42f3dedf773a5f61e1f4e48153a90b2bf9612464d4ae44776af2c58b6bcaf8b713c5a29100ff5ff421b94aef13bd8713a5dafaf991ddcb8dc39eea600d4f404b11eab6520f4243e83e645968fcc4e21826bc0c4d1a2473e511140297559201d7cc26a1675807b
private theorem part16 : 2 ^ prefix16 % Spec.Ffdh.ffdhe2048Prime = residue16 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue16)
    (e := prefix15) (a := residue15) (b := 1777307498) (n := 32)
    part15 (by decide +kernel) (by decide +kernel)
  rw [show prefix15 * 2 ^ (32 : Nat) + 1777307498 = prefix16 from by decide +kernel] at result
  exact result

private def prefix17 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (64 : Nat))
private def residue17 : Nat := 0xd753335e89e0ec3591c0724acffdb3310e65e5f0a5e9b8e6be0b3cfc255dd377443b73e6c321532177b919b18f8f7ce6ce21d6dd856eb9eb05e14bdcb0c708dd2afc15a6745aa1ef929165263612d7b426a87b52c6de6f96b759cf948ed8fd7eff71fd88c84c127a122e16c97471bfb90380dd37c5124b161d5265408a0e71fa9b7a6d6951b1c7a783811eea4d00fcd5f7e69b4773cea18bb9916461dc6fed0f37c853f0f6db8703b2e406e5ad7e84d9430a04cd07ec5cc99030130423dd5d6dd38bd590037c70a8028e83fefde318d7de2190afa20bdc97e218b1e09f0f20b2c53f8b33149302ebca98970879487dd5859ead989cb27c4646316e397d7585f8
private theorem part17 : 2 ^ prefix17 % Spec.Ffdh.ffdhe2048Prime = residue17 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue17)
    (e := prefix16) (a := residue16) (b := 3942560432) (n := 32)
    part16 (by decide +kernel) (by decide +kernel)
  rw [show prefix16 * 2 ^ (32 : Nat) + 3942560432 = prefix17 from by decide +kernel] at result
  exact result

private def prefix18 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (32 : Nat))
private def residue18 : Nat := 0xff0b2ad809bccc23ad2489064e2b789cd8e616d657e1cbc8580ebde81c2f4d17c78fc503536e12d68d42c0d4517709b9b380974c4a539a99a9dde40fe8510805e643543943b72c71ce9d011ea4c26ad592e3e578d9fff562929c282f20357984851f2de899ae336f02524439bfa8fca1982b5d20c505028eea22ff7717ca8a4c8f326d50687067f53411471d823e344c9f2687c5898911985bdd632baa129a72a63cc26dd17718728dd14bad85a84ce3e223ab687d28227d0f4a8ff962380318f759c4e7c8cb4cdcf7d92348d4b33a9436b41ab0bb5b331a198554c7d3184a8d2e4faa8c354e6be6822a1c7dd64a65b730d5b293d86af1570afc612a7e7318de
private theorem part18 : 2 ^ prefix18 % Spec.Ffdh.ffdhe2048Prime = residue18 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue18)
    (e := prefix17) (a := residue17) (b := 2451176079) (n := 32)
    part17 (by decide +kernel) (by decide +kernel)
  rw [show prefix17 * 2 ^ (32 : Nat) + 2451176079 = prefix18 from by decide +kernel] at result
  exact result

private def prefix19 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (11 : Nat) * 2 ^ (0 : Nat))
private def residue19 : Nat := 0xb81cdc522e7c220d383630684a5895291edee781bab388eb1e9269e1811e368d54a18eaa9bdf06219c89f6284fa957f51096aaa26b630cb01e6bd35bfbe7dfe7b83b01013ed5460d7ca93d60c2b6531ccf0382a336a1fe5c8b1d2669979c8e0cd5c302d539f6e56333b41fc0d1289449625121a7078f1b8cef5173973b814faaa363b8e7275ea6c9911555ba61a218b4f354691fa4be671577e926773895f33a09ce018f247580971b2e71bcf49e8f3b6b22646e63dbf419ea83b5008990b21e854bbfe37b279c6df06f6ffaef26761222fdc85b68075cc0cae98a27e8595581216135ee87a646c39daf2049d049aca0b74e337eb19cd141eb6ad55f7901d2ef
private theorem part19 : 2 ^ prefix19 % Spec.Ffdh.ffdhe2048Prime = residue19 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue19)
    (e := prefix18) (a := residue18) (b := 2944612200) (n := 32)
    part18 (by decide +kernel) (by decide +kernel)
  rw [show prefix18 * 2 ^ (32 : Nat) + 2944612200 = prefix19 from by decide +kernel] at result
  exact result

private def prefix20 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (96 : Nat))
private def residue20 : Nat := 0x7e4c492999fcfa9cb8a50a117e2ae1ae76361c0cbad9931bd90cba78eddf49b4dfcf69659ef1ec04cc6607bb60f548cee7f546c28975ed836380c28fc5a5227247324eb81a635d4ca753aff7c61fa183f6808081ab72bffa6127046be156b6544c6cd3ee4c98e3434bf012cd28ca1f48f9e0c731904bebbd9bc4a99ba648c0807af2f19b81fa14a91871209aaeac1c68b3b70bac941e8386e7add40b3ad05b3e54a1349263cf7f53e815053ed797519f5c9eca0b893020f46f418eaad13931946f58227ce57a417de0384b27a7527dafc3ea35a7e2bcd358a9c0175b3eae3978d8dfc68848cbfa7f82c3cf4bdfcee18d40f4215e7f2e45922015cc92493ffd41
private theorem part20 : 2 ^ prefix20 % Spec.Ffdh.ffdhe2048Prime = residue20 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue20)
    (e := prefix19) (a := residue19) (b := 1118941866) (n := 32)
    part19 (by decide +kernel) (by decide +kernel)
  rw [show prefix19 * 2 ^ (32 : Nat) + 1118941866 = prefix20 from by decide +kernel] at result
  exact result

private def prefix21 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (64 : Nat))
private def residue21 : Nat := 0x8aaeb825183bd009655d5e80b5571e4d97cc2b4e04c6074ca1358158dd1e19d8fa5a7ad9460152b137a8349c67866063fd3597379bbeaff45897e46eba8ea0cf40eb1cae18fc0e3e197b5f793a0e3dc610a7ccf0d393674d45579e6dabea99107d952a1987719cdcc8820ee5328e18ae8cc09f91a05b1eab4a38f209929bc003dd1183ea7fe7a5d2d1a2081d6e05c13f7ad6eab4eb8033a6f5ffc6b208038fd15b05472040af69064d5192d70ce51bee61f6c45bbd0131c87ea40825922fb8ed3c0d100dbca64bce7f67c527bec5579790d60443fcde4d26ead98ab3fdc645571c4f729692392f8093f02dc0829aae083cddb1401473339877009b81d1a3cd45
private theorem part21 : 2 ^ prefix21 % Spec.Ffdh.ffdhe2048Prime = residue21 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue21)
    (e := prefix20) (a := residue20) (b := 2666958201) (n := 32)
    part20 (by decide +kernel) (by decide +kernel)
  rw [show prefix20 * 2 ^ (32 : Nat) + 2666958201 = prefix21 from by decide +kernel] at result
  exact result

private def prefix22 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (32 : Nat))
private def residue22 : Nat := 0xa10abebd231b19f447fd68598b81afcec4f1117a379cc48b6782d301580737d59647f6bc9067710a2c502ea923876ae9031e37603a29a9899ed6a6125386ad8057dcd8a4d32a02935fcb4bde56c24f65abbd5ffdf01edd98560c460e2337a9f94eabb202943d39d39f4987cf801d1fafff93dbb4c25a263f1c55eeddfad3bb55553060aa1c41a2062e08a926787de2cf8ce2425860841c5e31ec97ba244ea13906d61c875a8076c41e915d8e87cd2877d96f5cdbd51baf8819245fafdbd73c657f56d6a1296b194d38ebf3410cc852487b336ca78dfadb6399dc4443891e8f0b97a1e567e64af100f74a687a53b4d3de4627e219373209c569a4250b9db491e0
private theorem part22 : 2 ^ prefix22 % Spec.Ffdh.ffdhe2048Prime = residue22 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue22)
    (e := prefix21) (a := residue21) (b := 3668674991) (n := 32)
    part21 (by decide +kernel) (by decide +kernel)
  rw [show prefix21 * 2 ^ (32 : Nat) + 3668674991 = prefix22 from by decide +kernel] at result
  exact result

private def prefix23 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (10 : Nat) * 2 ^ (0 : Nat))
private def residue23 : Nat := 0x360aac3100b4c1d57a447a5314cd27464f29021fcdc02298744a386cfa9da4369c0bf1fbd44c1eb6e06bfa6362a1973b10377c0c1c87991fabd8c4fa593ef350e36e062b319ce671560a68d057503ed7fceb7b88eb433205c917eb0bacd55f5cc7d6588607fdeca64c7a0e47826a5fd9dc831d1b147f0196ab34e818990565e1a875feccc0ae91c13ff75c1b26d1955d4142761840183760fae25bf0df941ca7b9790dcdb3e397ca4773c1a2fd7d6287c6ecd68deb689691b12c17f2bec8e49a11990adc690fb9f2abe07a9bfd10a1a701dd348318799c02b2fd25a94ef90ccfad5beddadcf8e3a438db2a01b121f46a9ffb0a4acc1c2c87f4cc08b0d9c4911e
private theorem part23 : 2 ^ prefix23 % Spec.Ffdh.ffdhe2048Prime = residue23 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue23)
    (e := prefix22) (a := residue22) (b := 1068229786) (n := 32)
    part22 (by decide +kernel) (by decide +kernel)
  rw [show prefix22 * 2 ^ (32 : Nat) + 1068229786 = prefix23 from by decide +kernel] at result
  exact result

private def prefix24 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (96 : Nat))
private def residue24 : Nat := 0x7a4fceeb947787900546e717811a047e14119324a6a29a18bfe5db3e17feb246f448217082707b1dd5faf648bd6155f77e391adcc2b32b1b1329a78c5d37971c7598ca468c7eb5c897ab3a7c8e414abd52451f6bd89370005f2fc473f9dae78f1d5ef9adadc1faaf35b367ad8d2ad8f66ab689e11662807968b45fb23db5f6220ff4e8bd763cd407388e3ca1be50b0f38ac348c9dd26df77b7f5f72c102117013c9c2c5c4e01243113c47a149c5a12cbd97974d138c07023a854d59e6db7460554c2c9aaf2d45397dfcd973e141fb93a680d46dc17b988fbcfdffb02aabc22d5f301df1012cae41939300a429813bdedbff55b2fa9cd9bffa2d5fd0d98d67612
private theorem part24 : 2 ^ prefix24 % Spec.Ffdh.ffdhe2048Prime = residue24 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue24)
    (e := prefix23) (a := residue23) (b := 3425142328) (n := 32)
    part23 (by decide +kernel) (by decide +kernel)
  rw [show prefix23 * 2 ^ (32 : Nat) + 3425142328 = prefix24 from by decide +kernel] at result
  exact result

private def prefix25 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (64 : Nat))
private def residue25 : Nat := 0xc38df646a800be146c828b57809c803d64861291b5ad9326a3cea3f0baa82df1ca55488595d7cd980589b6814635298732a120287098451bcc1f70ea08d7fdf2615a87a893806a2b78f173fc960ae6be6b725cc6cca027a32eddc6a729804dc6b08206b257a186bb2c919ecab2c923e6dfaadbc7e9a25f7fda1b4a0369836bb4ed8cb78e9a20ea777d0958e6ec28864711b2064b8d4db161b2dc7311630a9e12e9129d09e2d8e308c000e686636778ec6be1be3232e4b06287460bc2db2bebb48ced1923ccbaf731b2367e49b5193d0727af3037fdb33eb27709ab9af074e034a83d368f35966f175ec6c1737f7b74f2149ee6651f2dcc047560f7619417de38
private theorem part25 : 2 ^ prefix25 % Spec.Ffdh.ffdhe2048Prime = residue25 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue25)
    (e := prefix24) (a := residue24) (b := 1886602683) (n := 32)
    part24 (by decide +kernel) (by decide +kernel)
  rw [show prefix24 * 2 ^ (32 : Nat) + 1886602683 = prefix25 from by decide +kernel] at result
  exact result

private def prefix26 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (32 : Nat))
private def residue26 : Nat := 0x890458c2231f3a42108f5584a90ea6e823bda352d53d5187e2247ed67832980ceefe67fbca75f0e723afcac4be0f484e7ff6df56380746df6385788e76a9f952808efa197be392491461189363cfb09a8f38ad73f6dc6bd42c820f6b7eb397d3180c98d582d63dc5d34760fa290cbce65ac0830fdddda55c75510bf917b79801d5b7950e4b94d73237cbae83d4bd51598b605514e9701ccf6d474e398300b970084a687b2ac529dac4ba669f4d19d64ad853ceafe6a840f4d4ffc670cb0dc3985ca7eac8d3084366cf3a072a22fa0e88d1cd21d68010ea8b0cb3edfb01668f71ad2740021acc281f00898ff00ca500df4d28a2930fe01e6c57f036defcab60d7
private theorem part26 : 2 ^ prefix26 % Spec.Ffdh.ffdhe2048Prime = residue26 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue26)
    (e := prefix25) (a := residue25) (b := 4048766189) (n := 32)
    part25 (by decide +kernel) (by decide +kernel)
  rw [show prefix25 * 2 ^ (32 : Nat) + 4048766189 = prefix26 from by decide +kernel] at result
  exact result

private def prefix27 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (9 : Nat) * 2 ^ (0 : Nat))
private def residue27 : Nat := 0xf4b89fdf556f63baad8f9c637f621dd6b66ebf73031b3002127198e559f13edb1ea2d8ab5f351ec6a46fc2984d575d604a04957d8cfb274addcb6ebbb429e064cc45787736e8aa41012b643aa629711da0b1f621f8d0141aa17064e6d906c632543f961e6b7df1a7752688b0c8cc0bac9c9de8ba20948717f86aa176f12494195e24490eb02ae543df927c7c6721183bda02c02b54f9079a8253f454a2f1e443f0905d4f211656dec575cc4a30371f81f14c9f109486ad12b1d85967c4cede435a0ad36295b618794c1c19a4a6114bd7260b098dc74488a9f15cfe042f7e60361bcb31d3e14cc033825d8bcef21889cb1ed72ad1bf0e306b68947e3b91def288
private theorem part27 : 2 ^ prefix27 % Spec.Ffdh.ffdhe2048Prime = residue27 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue27)
    (e := prefix26) (a := residue26) (b := 2046293049) (n := 32)
    part26 (by decide +kernel) (by decide +kernel)
  rw [show prefix26 * 2 ^ (32 : Nat) + 2046293049 = prefix27 from by decide +kernel] at result
  exact result

private def prefix28 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (96 : Nat))
private def residue28 : Nat := 0xf6cce8877a23dd59847c03a65418e8b3641b43d487054dcc185efcddc3673e1e379045bf4f5544aea87f27ec083a6da1c1ee5fa338061050f9c1f638e2631f6f77f13bf0598af1340593b04c0c174ceee5f2bdcc7fbeecccd7d7c1651d9a05991b0cc36a00d0d90da7ac9a94de0ca43c425e60efd9c6b1d6724a51091b0079ba5a8ef329a44a5353c102812d742e1fb84b932e718b96356d3aac8bc0b64ac935d4b570be78c6957c52a71b4c73aed712b01db67f99724bef36d359c1df27302a043136c093de61704405dd82aac19252dd4d9084394911c90b9500c3cc0bd149e10d22a55a48be1e92589b4d207b24a0fb54cd24449089350a54de75fc8afb9
private theorem part28 : 2 ^ prefix28 % Spec.Ffdh.ffdhe2048Prime = residue28 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue28)
    (e := prefix27) (a := residue27) (b := 251178064) (n := 32)
    part27 (by decide +kernel) (by decide +kernel)
  rw [show prefix27 * 2 ^ (32 : Nat) + 251178064 = prefix28 from by decide +kernel] at result
  exact result

private def prefix29 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (64 : Nat))
private def residue29 : Nat := 0xeaf9eda70beffbfbd41587c8cffff8f226fbe8910411e7019c9b6534f82bde0839ff3e3c0c4cc546677a0a460117c25f74716a22bbfbe59f010e809b6cc0a4a6475121cb4e11a58295c6bc09da2824f5dac9d833c620399eea479f101537e4355c30fbba9cf31cce99cee2d99f82c3149f9442a0f7d75b55735f05cf0b79243ef37c8254f2c5ae7979f825f3f90dd45272e05c0d5b845e3576a358f6264c229c74045aaaf76dd74355ed751f10ab360b57dab00e5cca4679af62b56342cceccfab773aeed3146016a828e9569b35600cc17e5081cd44fc5a484ce2a080019dd830ab53bb45e8986e97bcd3407bef240e2f630c2ea8703879002f91ee9d13b203
private theorem part29 : 2 ^ prefix29 % Spec.Ffdh.ffdhe2048Prime = residue29 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue29)
    (e := prefix28) (a := residue28) (b := 2606166938) (n := 32)
    part28 (by decide +kernel) (by decide +kernel)
  rw [show prefix28 * 2 ^ (32 : Nat) + 2606166938 = prefix29 from by decide +kernel] at result
  exact result

private def prefix30 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (32 : Nat))
private def residue30 : Nat := 0x22471e3c61b521bef07c47ec07050c57adcdc1f396f19758d061c3a0b7430d965708c9c30e5227d71a276292e542f89b8cee540180d47a75d902a27eecc7707db5f17d41943761b1a98ec9e89e5f4b200015d731c212958e753fd8c3e7f2f40a157241dea002d5970bd9bdbf75a1dc04396e91b68929e48d34af10aa99c266d0cbd5f4438c73d6a6f7aea92530c3b47967d1005577df93f72b106ace7bce292d18e3d79cba737bc208bd4196a5cb1d84c8eac855faf263848dd519a001e6f352211ce238f0dc8c26293dbb6ee0ae44088bedfaedb0f847c5298debca1cffadb1302dd5057c84fef6c5d295004c20cf60e1ff2ab956eb751d9bdb529bb622b296
private theorem part30 : 2 ^ prefix30 % Spec.Ffdh.ffdhe2048Prime = residue30 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue30)
    (e := prefix29) (a := residue29) (b := 2555798823) (n := 32)
    part29 (by decide +kernel) (by decide +kernel)
  rw [show prefix29 * 2 ^ (32 : Nat) + 2555798823 = prefix30 from by decide +kernel] at result
  exact result

private def prefix31 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (8 : Nat) * 2 ^ (0 : Nat))
private def residue31 : Nat := 0x1c02ea51341be34733d3d63a4b8c8c20339b56c2dc44180e997517832a7f20b424b640b50d4065607b035f6319f6bde33608815342cbc138a10f8fe821a754a33158a58c35eae5626ba010fdd0971c78b798db2aaa61109a8c5a0a4e5d3158bb28f1b86aa15fffdfa06f87d5ce0662cd6db2e9a67a063bf940ca58749178dd3d44dac599ae57ac5558574507308890b7540456a5de8a25415725f290cfd192077b76a9d6a6b26d68364de06abd0b0481a3d77167b282b6edb3fac84d67430ebfcddcd1a7ea599026954fd6925e0784c962d47a5883940d690eedbec9deeb12d688157ea816443bfb8ae75215563acca035d336f9c03a7b747b724cdc6d546b62
private theorem part31 : 2 ^ prefix31 % Spec.Ffdh.ffdhe2048Prime = residue31 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue31)
    (e := prefix30) (a := residue30) (b := 2753379517) (n := 32)
    part30 (by decide +kernel) (by decide +kernel)
  rw [show prefix30 * 2 ^ (32 : Nat) + 2753379517 = prefix31 from by decide +kernel] at result
  exact result

private def prefix32 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (96 : Nat))
private def residue32 : Nat := 0x28a7cd52f79974e4cc40e08cca3a5de77113e6317238d16186f56325a9aa4f348ba5751a00b422d7766fea73cc9daf681a3c1b0c1f19b3b19aa186b1bd6144387be9bfdb0d8aa312abaa6946cd83fe8e2e91b9c6fa48257bb37aea25cd6dc51808766d206d5e81f2622ba46723a0992eeda8b8a58378d30636117620c289e1c85bf050a0bebaae0e402b594a27d260094722b8b710315cabf6f69b12e4db03821cad20fb657cc7449f722dab3b632875ee1c613af2a3d81220a7562f4b4bea1bc7799d4c79b9a9844ae56c0bd518023dcd6a92db71d85044a2b8076eb7e7db62ca953acad0ae491de4c4a04391f8809745fdc1e3e873842bd13f8d04c93c6c5f
private theorem part32 : 2 ^ prefix32 % Spec.Ffdh.ffdhe2048Prime = residue32 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue32)
    (e := prefix31) (a := residue31) (b := 1577408705) (n := 32)
    part31 (by decide +kernel) (by decide +kernel)
  rw [show prefix31 * 2 ^ (32 : Nat) + 1577408705 = prefix32 from by decide +kernel] at result
  exact result

private def prefix33 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (64 : Nat))
private def residue33 : Nat := 0xa6acc6cae0d413e97af913d28bb7f9d33eef4526579f662ad05fb5c169d9c47ca31cb2d27c78193d4d97a60cb4717a3e3eefd8be6f75b704d904e562a408c44b25a9389db969b0411b077fadbb2d76f71539db25d6c252ab6521b32da858fb14b6f7542681260d71e05c1cdc0df022167e48ee9d321b0d18fd460ad57a93d7cbd8f6e0b9c2269e2077eab657a55781ad00a43852a0d131dbf3cf41f7bb0743b612e8e3241f98dadefe7cd64446f519e42d1cfa9443f9c081d41b5920b365611ef8ac3b23498496a1d644f72202806d8fb4a6275cce5cbbb7e56a89b16965f5659ffe5c09a24efe9f0883312f051aa9d77cb849db70968c1cd24d0ca204311e08
private theorem part33 : 2 ^ prefix33 % Spec.Ffdh.ffdhe2048Prime = residue33 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue33)
    (e := prefix32) (a := residue32) (b := 1502772656) (n := 32)
    part32 (by decide +kernel) (by decide +kernel)
  rw [show prefix32 * 2 ^ (32 : Nat) + 1502772656 = prefix33 from by decide +kernel] at result
  exact result

private def prefix34 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (32 : Nat))
private def residue34 : Nat := 0x8279f1d2dca627925c8e7e5ba14b0605837f952ba963a3bbf17df3685a9120615fcd3f286fd8f76d28b3691ba4d0cafcccd588bd9de354bb0335143a90798d41fa584e40025e1cff98b0ac6fd7454fa0135097f9ad8a63b096e2326ffba95206c95976292d71942aa2b52364858049ceba0c50356e8cbe3d83b0c8271853aef891f7a59d304c483a44d0dd5385b955fb37964add06131bda115e1977d53d93bf80ad7dabbfa911d45937407e6dccf72c82c5db364cff2f45f786337ef5821bf218dce66addf4e8cc1f912121a90d11c04df641cc784ac36c2a46f030f873cc9774ffa0c3287ee45e95511a46709fbcc2e44734ee74bd231e2deb1e0c264ee8c6
private theorem part34 : 2 ^ prefix34 % Spec.Ffdh.ffdhe2048Prime = residue34 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue34)
    (e := prefix33) (a := residue33) (b := 3900986533) (n := 32)
    part33 (by decide +kernel) (by decide +kernel)
  rw [show prefix33 * 2 ^ (32 : Nat) + 3900986533 = prefix34 from by decide +kernel] at result
  exact result

private def prefix35 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (7 : Nat) * 2 ^ (0 : Nat))
private def residue35 : Nat := 0x8b347683407d7f1f7410a33f20cc20be768019abd7d3b2ed5cd91ded1a88bfcebe733953ba07cd3d4fe274836d693e6301655a63034435609ad023a083ba8f28fab8474d429b2aae80d1e8b68b70e6a21e93c691eae1499b3b311ea6029613f6a69f38e9541d85a5d33b78d5240c5d29f732488d921776b1205f261476d798e409b48103a70ac07e72f101f8203f3ebda048b2e34197671283209c3ecfc94a356205915e59783beba6114b39fa51941feba4bc73345ed76d5d0c7a0a427c6c5682bb7ebaa16c12fd4c80d3514f0eae6f6db26742bf529ba7d4d5c919b1708a4fbf18bab987c1f8ae8ab8da214f8bc37e61bddc533c89bb2a9cb8bda821710501
private theorem part35 : 2 ^ prefix35 % Spec.Ffdh.ffdhe2048Prime = residue35 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue35)
    (e := prefix34) (a := residue34) (b := 3647238653) (n := 32)
    part34 (by decide +kernel) (by decide +kernel)
  rw [show prefix34 * 2 ^ (32 : Nat) + 3647238653 = prefix35 from by decide +kernel] at result
  exact result

private def prefix36 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (96 : Nat))
private def residue36 : Nat := 0x34dedf1743373daed52e696f1b36e6fc730ee1c620fdb4ddf23ac79e422e3a3255223718a9830278ecfa3565ace2b47f2eff2c1e7ddd991bd650016a32019a67bacb3ed1cd78d2da9b7f4bac2ee5dae1557c0626f4d70aa6d94a30f0f68cd004770c3fe8ab28f559c109caaa777e31339e8fc7de3e97702c66d6948362449d66cf55be24a5f6dcb425b5df668c47fc6f5233a290d45c8c3c30192c6391be76e18bf3a37d76eafaba030f12bcdf811fee8ffcb0369fc0fb0ae54df4fdc48d1b75b762a85e30331fe4240e84923ec0f19dc47caf0cb44a865a3c4d8d9d7353481014ddf6275dceca71d76314e02633aecc02a801e2052e1a8557e87d6b834bb712
private theorem part36 : 2 ^ prefix36 % Spec.Ffdh.ffdhe2048Prime = residue36 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue36)
    (e := prefix35) (a := residue35) (b := 3702877531) (n := 32)
    part35 (by decide +kernel) (by decide +kernel)
  rw [show prefix35 * 2 ^ (32 : Nat) + 3702877531 = prefix36 from by decide +kernel] at result
  exact result

private def prefix37 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (64 : Nat))
private def residue37 : Nat := 0xba760fd721732526f1797601c62d49ad50a31c6306457287e041a99e0406836c2589416bd38d86c1f9bd49ffa1da348623cf04aa4112b714d8a3546493cde9b0ec18fe6248b3b839b7ec43ec20dece7e965b1f0af1f856d83d8c1fb3bbdabb7c96136140377e6b49051f0d102249bea91803876d0afa30d3a80e8008eada043f135d1b9015115cf6843e03e1e965c8b40cec433634b7cf94a8f01f6dde01a8f86e370d1262a289002e43106fd3b1b60a5a5002e5ebdad7fc6fed726ec4c5302ca7d393f1c7369ea6b9347d1ad8797b2fe4be9eba775d0fe77bd93589a41c0713230c5e05b0d901633ed8140b3071b8377bd83acd0153457371474c5f35e18899
private theorem part37 : 2 ^ prefix37 % Spec.Ffdh.ffdhe2048Prime = residue37 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue37)
    (e := prefix36) (a := residue36) (b := 2959866420) (n := 32)
    part36 (by decide +kernel) (by decide +kernel)
  rw [show prefix36 * 2 ^ (32 : Nat) + 2959866420 = prefix37 from by decide +kernel] at result
  exact result

private def prefix38 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (32 : Nat))
private def residue38 : Nat := 0xa7902a9ccd63d606050597988cad8def1168f01a3791435da05b6c174f24c1e3ebf5da4cf36c62bf1812406c01e859d6fd4374c08fdf7750482fde903bc915a2c22d54276c7fe444ae125b303a53403d93eab213a82205e2bbdeab5ea460dda4ce59d11ae8bca85ac64fa690a8d3b50fb7b5d6580c762a5ea64c64e416bcb0c582ebadea7ce0682c605787fc87f61729a25eb61c4af094d6fba2f8f9fdd3220d8a5cefe0147cce56f33408121cb3a1e7796c99232b3186f04e99b66d51ad8b06d51ed10715bfc6820e6214e2449dda99238cd769398c15de24c4f499e2c2a4cc551b333c9001fad496dbcd0be168e1a370b758c862d0106471c6fec34104c3c3
private theorem part38 : 2 ^ prefix38 % Spec.Ffdh.ffdhe2048Prime = residue38 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue38)
    (e := prefix37) (a := residue37) (b := 245866833) (n := 32)
    part37 (by decide +kernel) (by decide +kernel)
  rw [show prefix37 * 2 ^ (32 : Nat) + 245866833 = prefix38 from by decide +kernel] at result
  exact result

private def prefix39 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (6 : Nat) * 2 ^ (0 : Nat))
private def residue39 : Nat := 0x4996eb3945c0736cea7609b95465458ceaadace87eff12d9376a7c832869315360eab026e1f218d71d94a540abffd870118a702a2ebcde657140a1ee83b23cdcf2e041a62f42f982bcdb087fffac2d4bb4b173713eaeb5bb2db5d855d0c6519dca100fd00bc754b5ca287d1d80b462fbdc68f88ed38c0186ec450e4f15c5db8b57995f8001d434503ae9bfc0f4b255f361fa0a6bbf7e9e7ef7e0689165067877a04712194b24f14e9339b41daf14069b810e28d31db998b3b7064a53d9d53475a2165778aa3e009000ea746e0e14a3d3348ea4a19a65fe5c12d2877ad513c88d1525b924af0d092e29248cc866eeae500f77b7678a126a5da22f713564b5b483
private theorem part39 : 2 ^ prefix39 % Spec.Ffdh.ffdhe2048Prime = residue39 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue39)
    (e := prefix38) (a := residue38) (b := 4011632378) (n := 32)
    part38 (by decide +kernel) (by decide +kernel)
  rw [show prefix38 * 2 ^ (32 : Nat) + 4011632378 = prefix39 from by decide +kernel] at result
  exact result

private def prefix40 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (96 : Nat))
private def residue40 : Nat := 0x9e310e17a2317e3444c9acdd4680e5cd8e565fbeae39c044e92aaf8358e65f127fc6c36c4c41a51a727ec3565fa18bfc2a4f82a60d321fc5b11bddb53eca74194786c9486ab1236684b2b2f957d1b0a7d33abb7be45979889b41da6d72c37473a995933f455dde70abecac6d2339cab11173125644729a58fc473b8b498affd9be5dddbdadc967ec26a14fc78aafd27823342e34fe9724b66e65629d270d6fa9ab8e7edcbc81f7ac9d86de9799875c63791fefc58596dcfa16b3f5097e749c700698e2dbd478e8a6e3ac28c2b41ab4ddeeb3f6f02dd5a5da4fca579ccf77dd8da4f649089b88f4d58aca2e90d23d64acccd3b95b51ff3798ac673b04d09c8a06
private theorem part40 : 2 ^ prefix40 % Spec.Ffdh.ffdhe2048Prime = residue40 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue40)
    (e := prefix39) (a := residue39) (b := 1462466291) (n := 32)
    part39 (by decide +kernel) (by decide +kernel)
  rw [show prefix39 * 2 ^ (32 : Nat) + 1462466291 = prefix40 from by decide +kernel] at result
  exact result

private def prefix41 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (64 : Nat))
private def residue41 : Nat := 0x26bfc6255d8ebc85dc271324c227b695ac0ae2f8bff2304d44ece6dab595890bd61a155287aa0f1d5f8bf1468205d1722c80f3506d31e3ada9d7314861b3579c6495eced989a75989cc2e39cc8f58223d72662c1323263e819a48027a3d50f11956e016953fc38cf7f3aa20717fe4d7b55c79da28808a3005a41ead6c6e745f1a06223ce56379a45dc13be7c2df9ece6f4879cccba90638d2107c508dcb0e65732377601d06269436f7d93d3568c10696746650561673c8fc4aee99621e8a73307f23729738eb9cf9636d4b90823f7da162c9eafca8240c9ddbfd4d9ff1887600d509ddb7b9ca5c2364f24db9722371bd4f391b6511231187d70f91a7c4a0e7f
private theorem part41 : 2 ^ prefix41 % Spec.Ffdh.ffdhe2048Prime = residue41 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue41)
    (e := prefix40) (a := residue40) (b := 2981715340) (n := 32)
    part40 (by decide +kernel) (by decide +kernel)
  rw [show prefix40 * 2 ^ (32 : Nat) + 2981715340 = prefix41 from by decide +kernel] at result
  exact result

private def prefix42 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (32 : Nat))
private def residue42 : Nat := 0x7e6d4ea8da7ea7c932cc523c8e2a65f3dbe8d8e2e0c63f20b7aada48f52d57fd97ed593b7e45c52671b03b34a217dcee389ad726768d1308346592a9705225d65ad5a6ce302144da079f84ecfecd6df30ab3f0f3b77c734e8383bf99c01f8e354820eb08d423185c5a204ac3566d9d195cb237f2e7b6e3d4dc2a7a5cce578f03ba3c9972a27724f106f7bfa33b716eca01c70e29c3cf85b7b644be6d210f5bd95ac1955d8f5407367caecc2d57c17e969d21d657592352797371f0046a036600d6799e85487e6e80b181d29544de234337ff9c5be219a2b32d85f50886a6a013376accbfd6f91d5af04aa96fecd814da026131312774a12cd0c31a5876de626f
private theorem part42 : 2 ^ prefix42 % Spec.Ffdh.ffdhe2048Prime = residue42 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue42)
    (e := prefix41) (a := residue41) (b := 2240009188) (n := 32)
    part41 (by decide +kernel) (by decide +kernel)
  rw [show prefix41 * 2 ^ (32 : Nat) + 2240009188 = prefix42 from by decide +kernel] at result
  exact result

private def prefix43 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (5 : Nat) * 2 ^ (0 : Nat))
private def residue43 : Nat := 0xed9c2ee78a96e241c3d991254b1d460e5879b23437a165c7a521731e092a7a84a21a7a56dd3743ddd247782173587af0a47d342a113373abb809a454267739ff966a6b97a63859fc7ab866109c304df9cc219f8f68c2229a3c9b14b1fd5b7b417778767e1a2ee5dd2199bd2eae5ae2eac4491f93f07b9fdde1b3d523cbdf9178b1e96567020ee0fe49b0b6561d2ebf4ff225a2c5918d04d8d6209c27c8e31baaceaf0ac8372ccecfbc3604c9ae1232da20e2e9d00821d472e9e5fb3f3a1f9dbbda6dd88cd4cb920d35586a9c4ab87fd1def6a1786e1c81d1f4aae2c3a4625d1f20808420138c3e15fb494c3fbe57928bb22bd33ff0c2fa47c9a90234f54a0d
private theorem part43 : 2 ^ prefix43 % Spec.Ffdh.ffdhe2048Prime = residue43 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue43)
    (e := prefix42) (a := residue42) (b := 1996830392) (n := 32)
    part42 (by decide +kernel) (by decide +kernel)
  rw [show prefix42 * 2 ^ (32 : Nat) + 1996830392 = prefix43 from by decide +kernel] at result
  exact result

private def prefix44 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (96 : Nat))
private def residue44 : Nat := 0xc12fb1dc15feb390ff86c3c32fc5caa9c8054a93595efbb85d67e76bd524ca90f43b93a615f969d5b0f433cbfc80abe0837d121d6931e87e94c7089843488cea2b01bad9405fa93a81ca89a7afccdff9956f9289c035e16fa6b084962b2cab65a045efdc4fe03a14adc001d4f82dee6a382a1022c933b121ad939bbddf52e2bea28680b283d79a1deac1bdc6f110cf09661ed1542ead0dac28a43acda5ed8ab5cf72989e023506fb2bdabf7955be7de5a405e14cb817f4904f7a217ec6d76b960ef9a8a4a30a0818b2dde528e8a6df2ea210b95b1acfc50402c972b6b91267f9a23357a8b6142c72fb0d4b6dda63df19b532e6b37fb1c39af68cf10920dc7b8e
private theorem part44 : 2 ^ prefix44 % Spec.Ffdh.ffdhe2048Prime = residue44 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue44)
    (e := prefix43) (a := residue43) (b := 1325497968) (n := 32)
    part43 (by decide +kernel) (by decide +kernel)
  rw [show prefix43 * 2 ^ (32 : Nat) + 1325497968 = prefix44 from by decide +kernel] at result
  exact result

private def prefix45 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (64 : Nat))
private def residue45 : Nat := 0xb9cb6d27c976a3ca232377a471ca7f4db86eeeba27dbf17da5fd683d3eef470e637fbba18c3dca336b38ea75a3f6995f9aec6b3c89a3197c7ba1489ea379ec63d8529e328cb070e9b1780ff745e7d4ba85b6b67e9f96a3f8ed4ff50f19fd626f28a147edb330c633c490e5a65364598d405fcb83b44c7e58d2fad6b601a6728444421305e35edfc4cf2acb25bb0163d19f9222b19096f3a7015ea772331172a55c14927e72b01447ce6b9b6f5e1fde365600f4f06df57d854a2d5b31426080bcf15ec7bca801f9fb5ce956a68885636621fa5ffe06caf86bfe6f0146043c08b7d8312a9b7b82c4d2ff1c1d7ea10864ff980af4846bb4475a51d82442ef3b5df0
private theorem part45 : 2 ^ prefix45 % Spec.Ffdh.ffdhe2048Prime = residue45 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue45)
    (e := prefix44) (a := residue44) (b := 3875271030) (n := 32)
    part44 (by decide +kernel) (by decide +kernel)
  rw [show prefix44 * 2 ^ (32 : Nat) + 3875271030 = prefix45 from by decide +kernel] at result
  exact result

private def prefix46 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (32 : Nat))
private def residue46 : Nat := 0x12664f7cc4c0479a6325558110d31694a4209c51e7f067e059f20a0aeb26839b90e87985f78ce8bc2620e98ce212e9f3058b9185d3fff01f4b1453b38fe04357bd425ed76811535c99240998f67b3143249a9a352766cf269954f65b8fd45707a08a88f2c803f382593837192400aea3c7a3d234429e2badd6f794e5b4cd47efdab07647a7aeef3db817b8e98bb0b5e4c36a17991c48bde2ea0cfea17592178231071fb3d4a7e9a8d4730846e8f28a165c0fc47c48926ecbf5112eb240c842998fdb5115ee83ede142b67ebb7abc663b7c80f3bd3cc2a61eef3a89004da592088349649ff05ddf9d0ab5b1e1d8680a4d97c5c23f71dc6e9902a99cf02719c963
private theorem part46 : 2 ^ prefix46 % Spec.Ffdh.ffdhe2048Prime = residue46 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue46)
    (e := prefix45) (a := residue45) (b := 1612317286) (n := 32)
    part45 (by decide +kernel) (by decide +kernel)
  rw [show prefix45 * 2 ^ (32 : Nat) + 1612317286 = prefix46 from by decide +kernel] at result
  exact result

private def prefix47 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (4 : Nat) * 2 ^ (0 : Nat))
private def residue47 : Nat := 0x65eabb9feeb73060916034c72f9a12bab4b957b647a1188549c839731a4dca9819ef019351d526d2c2dbd9490c961c81ff808d5b108fb2d864ff7eab627c393989cd92a440569193fc6ea8a6e01212bd1d5500427d162e955537e4683497e5df36c8280d44393314ac465b3276c59022de8d2ba41bce349bc00cdb7f599623136136f0d72be8499e8b1a9667962230a1f2483f2afc96abca4096c49d4986b12ccd3c364c9bd6b53590b9f87b7fccb1df94ff2547d07c375ad243f04b2ae7200f3ef12638145f786d7795b6582316dcd1dbf2235a3345414cff2d01ca051b21c707b32b9d067645c44a5b1f24a0703f94c35cfc7cfa3dbd4ac0153a51c344e02b
private theorem part47 : 2 ^ prefix47 % Spec.Ffdh.ffdhe2048Prime = residue47 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue47)
    (e := prefix46) (a := residue46) (b := 2484737968) (n := 32)
    part46 (by decide +kernel) (by decide +kernel)
  rw [show prefix46 * 2 ^ (32 : Nat) + 2484737968 = prefix47 from by decide +kernel] at result
  exact result

private def prefix48 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (96 : Nat))
private def residue48 : Nat := 0x6c98515922124bdccfde0aebcf833f79fe363e58820db90d86519cb97b73418a871a86c858098c4cc21aa4bd724434506218a17a714932f2e94ca0c4fe4aef9515b9137cf8f4a450e9651f4e2acb92f96ecd2ef70469ec2a9c258fb2d57fd1b273f106c3e9498db03e4ed11041a18f3cd0763aea008404c986c067f14040ba178186f72899674a834c1992c8e8a9936be7750fff656eac629eccc4d5d8a0fa41ca9333eb707c7c502bc1f0a4f6b3de8be3b438b3f142e4b25ca8495ef7c6dec6f25191c301ceb31bca57058d15459942bb00e09b1499cf4af38050c5a4885727dc36b6fa5fe08f693317a0522301f6a6fa3c24bcb272aeb9474728134eb8b3cd
private theorem part48 : 2 ^ prefix48 % Spec.Ffdh.ffdhe2048Prime = residue48 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue48)
    (e := prefix47) (a := residue47) (b := 3367599950) (n := 32)
    part47 (by decide +kernel) (by decide +kernel)
  rw [show prefix47 * 2 ^ (32 : Nat) + 3367599950 = prefix48 from by decide +kernel] at result
  exact result

private def prefix49 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (64 : Nat))
private def residue49 : Nat := 0xc616337e08825c8c8fd953bce7e488f010c89eb25f91d317668d8e2658d1706a7048ead3e1cdb3a68de2d6a125c92a462b4f905ede782f30567e8134f9f0d5fc1e935e568b3e93fb6bd5062c53f4558c7cad9d09e89a07f91b66740597c3d828835bfc75cfcbad92cb5d8efde4ae3a0083077c617a94072d23a405565d31cd19422e395e1efc5c49962d9c2e2ce1d902a5f3d51a7c6a7017dd6f59f0c5fd0cd9c9e6f45300245f6650f24bd842bee81b63653cc851be193cd9b30717313232cfe88bebadb8f0bb41948da199e20d5b6890fbdeef38040b6944da8125d410a727b076cd387ede365a834d6e8008f10a282367b41afa2de51ee5c5aa048cb25587
private theorem part49 : 2 ^ prefix49 % Spec.Ffdh.ffdhe2048Prime = residue49 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue49)
    (e := prefix48) (a := residue48) (b := 1958920703) (n := 32)
    part48 (by decide +kernel) (by decide +kernel)
  rw [show prefix48 * 2 ^ (32 : Nat) + 1958920703 = prefix49 from by decide +kernel] at result
  exact result

private def prefix50 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (32 : Nat))
private def residue50 : Nat := 0x87e718979712da37e3349e219daa3da1e7a6fe2b14d3a38a3d86ab2dace14bb6b4171cb431b4a967d0326130272ae624c116f631af7abb1c279e501b10ab1d3d29e8adcde8c52db4965c5564c95685e78dde478187c44b55b6c4ab8ed81f7dbbe2ac3e0d17ce20fcd6458c89cc24e5845d3a2ac4eb06e36f004e55b5a6f99f331bcaf32f1484489609034c7049682f401c99e4960598e44f7085e302a8ab7a2c455cbe39cef433d2945fa46921abf3d215f380ba0efe986601cefe3d491d496aab4f623bf46107bb482f48bccc36f23594f1246b3f4805a92d53b5edce3815157aad57cfcce74e6e2200284c9795c7ae1016e2a07b3b6a52c4fec89d92a89c9c
private theorem part50 : 2 ^ prefix50 % Spec.Ffdh.ffdhe2048Prime = residue50 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue50)
    (e := prefix49) (a := residue49) (b := 3341256985) (n := 32)
    part49 (by decide +kernel) (by decide +kernel)
  rw [show prefix49 * 2 ^ (32 : Nat) + 3341256985 = prefix50 from by decide +kernel] at result
  exact result

private def prefix51 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (3 : Nat) * 2 ^ (0 : Nat))
private def residue51 : Nat := 0xcab3e01f524fa62e4efc3d27b0f9f551272bf91cff1fff3e1b5d0d65e9005f6050c850e4d50212d7ae200da78b6f34d9ac6c73946ff2108337e83dec087db6c1410ff74763803e27b98e07123bccf9e3c4fcb92504b6d7693a422dcdcf6f63ad134f42b4a5a61388ef498efd165731cb8bdb8a57731873af0445fead5aa85abaef7806efa25a899a8094325b6ac239704d582391bd1fcd76ad97d6497757c23a25aeede0ca6245e33c040973a5a2ab6218df6181df210f827c05b0c9ebd81f1a622a1a824a5b5b242ab488f66360fa9aeb603d1b9f8c937dab6d455f33e203b6526011017d19278255a302f3998eb7af2b64744b54385b6b806b8e7af426afdd
private theorem part51 : 2 ^ prefix51 % Spec.Ffdh.ffdhe2048Prime = residue51 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue51)
    (e := prefix50) (a := residue50) (b := 2004435137) (n := 32)
    part50 (by decide +kernel) (by decide +kernel)
  rw [show prefix50 * 2 ^ (32 : Nat) + 2004435137 = prefix51 from by decide +kernel] at result
  exact result

private def prefix52 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (96 : Nat))
private def residue52 : Nat := 0x8067dbc5bc793b8995f048fadc11fcaab890b40aaef9208bcc99482e4d9df148fd478d5dbcca88f80102a49a63adf7d2b5ccec58e5bd060a6d04227716dbdee7d48b06432842b2827f526e51f1264547308bad01359936810c1e2a09f26743f755f3003c6664d2efa0e4602ad9d02f89074653ae2c186611bb7c84803d3e85afd733225786f8472a3b0149c962156107907f42f4982edc0ff34d58adef4a19ca8aefbf5feb30f1bf7c18c805c8d1f99bff80dae0f31f727dbf5ccdee689986973ce3821724d79ba5e4957e537a79198b4f9710393a52f9c5c0d3c4f811657cd7a46bc967c79bc02211abbc697fe277cfbee3b6a59b8d9f83035a65a0f9817aaa
private theorem part52 : 2 ^ prefix52 % Spec.Ffdh.ffdhe2048Prime = residue52 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue52)
    (e := prefix51) (a := residue51) (b := 3791592845) (n := 32)
    part51 (by decide +kernel) (by decide +kernel)
  rw [show prefix51 * 2 ^ (32 : Nat) + 3791592845 = prefix52 from by decide +kernel] at result
  exact result

private def prefix53 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (64 : Nat))
private def residue53 : Nat := 0xcdeeaa80ed1a6a777b2915000ba2ce6cccac2bc07a80db5374d15ee55da93b1deb627d42ee88aec1c9b2a6682a170ff104f24a108f7f33d249b6c9b88b9966562ff80bf030b5b3df59545c637ddc11adb7a421d46a5d657131f25ed9b629e095ec8c07df1a319d2a4149604493189417406764365256d62bfe30970cba428d1df04249bb4a8ba126bb34851df8cd512344230a87d559aec849ba2250f7c73eabe63e9e655d224bae2e51f7b5810c56c6aecb123ea67fd6072fd46bc8b2c9959c87d3c4addea1bf82b891b80be2ba6391239463d43c88567152b1c1ff85cf1b2402f9f732a513831f76223736aeba2369e2088ed739b1e4447916dfcd25526e6b
private theorem part53 : 2 ^ prefix53 % Spec.Ffdh.ffdhe2048Prime = residue53 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue53)
    (e := prefix52) (a := residue52) (b := 2788677305) (n := 32)
    part52 (by decide +kernel) (by decide +kernel)
  rw [show prefix52 * 2 ^ (32 : Nat) + 2788677305 = prefix53 from by decide +kernel] at result
  exact result

private def prefix54 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (32 : Nat))
private def residue54 : Nat := 0x85050c2415d14bc90d76e94ff25dad966f881d5470b78baff980ae9e15648df1e0465bab57f379ec559fb447636efc2287da781d2c725ae02279251c12b35885886ea7008f99965f8852be44488aef6c51795606e30bae2db160681702648256ee58e9b2b5f723ed6d142cafff9f496c8c1704071df0b0fec19c5ec4437d27c26976ecc93a8a58ed7f465f001a59e48a0af7502134e9548b4a3c72749a30a3bbbfea513bb78199cea8e24e69a70675f27dc400eca631d7772e59c2ac5b7df8197274f4f4624e538a34d69f668d7beede7df4e956cc35147ab88a009780a5b46ff26bc8344cdb657530bc95fbd605fd87cebe43f9e5f163c69aa1c82fad9b2a92
private theorem part54 : 2 ^ prefix54 % Spec.Ffdh.ffdhe2048Prime = residue54 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue54)
    (e := prefix53) (a := residue53) (b := 2648374878) (n := 32)
    part53 (by decide +kernel) (by decide +kernel)
  rw [show prefix53 * 2 ^ (32 : Nat) + 2648374878 = prefix54 from by decide +kernel] at result
  exact result

private def prefix55 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (2 : Nat) * 2 ^ (0 : Nat))
private def residue55 : Nat := 0x90677cc03e680f33e7271d80e2ca116e81f681455aa1e586b49dbb660c5e6e1c01100330821f8e86ef096ef130ee4265294de96e00baab5a039c7ec23f390d7bcd54afef4fa1b4147e41ec635448a2e942bf39dbae060bb12f0f3fc457a11ca7b48fed791ea0fb8e467162c8f2bcdd5d6f960aa7be1b2e5ac2a24ca54635b9a246983e096838b0fcd4197cd4ac0f017a911774c4991172ee8d507b349f35e6b0b9486a14bd101f07786a1712c0e21ef0548f33587c3221cd6613bb69af415302ac5ba1a16160a2f6af6095162b680440a8bfbdfffea5eb17ee74c8eeb71f5c4efe96ac4d186c588877b463618c9a6026347060078420db12a049498e61cfec58
private theorem part55 : 2 ^ prefix55 % Spec.Ffdh.ffdhe2048Prime = residue55 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue55)
    (e := prefix54) (a := residue54) (b := 392237058) (n := 32)
    part54 (by decide +kernel) (by decide +kernel)
  rw [show prefix54 * 2 ^ (32 : Nat) + 392237058 = prefix55 from by decide +kernel] at result
  exact result

private def prefix56 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (96 : Nat))
private def residue56 : Nat := 0xc0c786c6f720564a33d07baba55dc171b1554ebcf68ad98dccebb2a92ac049882bcbbf3b0a9bd6263dd9ccf9d413a9d4446b23e2dc5ce21fa566ba434cd090c069468ff3b3b2deea52841d7c553d7d0365b2147d63db5cf21dcbd98247905fead031b4acd967e1f09c6200f41152085027ec6c6566c328b214f072628bcea05f7200ad386688a8dd1d177c296c166a98f31a051394a17387f9332a6fead2da54ab0ef3080ab7740e230a8b7d811607cc037e7115c34b4932b264fc6cfd16666c1b2b36a0938b486f4e712a4e3b070f57d7fb8cdbc83d5d0e2cc531f0349ba26e5c483ae9593bcb4692832ddfdb59d4896afe78ad712f6ec9e15e2ef7f894f37b
private theorem part56 : 2 ^ prefix56 % Spec.Ffdh.ffdhe2048Prime = residue56 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue56)
    (e := prefix55) (a := residue55) (b := 3804723393) (n := 32)
    part55 (by decide +kernel) (by decide +kernel)
  rw [show prefix55 * 2 ^ (32 : Nat) + 3804723393 = prefix56 from by decide +kernel] at result
  exact result

private def prefix57 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (64 : Nat))
private def residue57 : Nat := 0x5604d2acf6d216460e22c7ed5f84d642b91c7ed5e319bc5c7ba4154d9fd6e6019b984c56870ec7b20021ca2e3501a351da0f5d11210239ef17304cb66de26ef561ccc1ff02e34c1f1f1ac7ea3765099df108bcc67e5454d2d70c27ddf74ade6626c1d0a75265e5e5b4a05726d58012f4070c74c4e82e7272a985429fdf9f0084d3de1fec4935f681d71cd060d25ce1eb054c9277214de75ee9339b60df96acb764cba5126e7d3fc0ee09f95abcdd4cfea70aabcd1d9800518b6b8cd00456572ab77a837fa55ee03fd93368461d5254a2515175cbb65d08c7afe2d1b20f435de66cc25d49934b1d3b885544e274e1fa5ccbb8d2a3e31463817eef826aee7f5ccd
private theorem part57 : 2 ^ prefix57 % Spec.Ffdh.ffdhe2048Prime = residue57 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue57)
    (e := prefix56) (a := residue56) (b := 3196797401) (n := 32)
    part56 (by decide +kernel) (by decide +kernel)
  rw [show prefix56 * 2 ^ (32 : Nat) + 3196797401 = prefix57 from by decide +kernel] at result
  exact result

private def prefix58 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (32 : Nat))
private def residue58 : Nat := 0xd6bdaf5a9e8c59a97a47b18345da43f6afe118557a60e9e759a4c0ee7b4457c639ab8ef9e14ff6c6423c17573888a565b698db0e37a5e15b9243585a56e0177794fd7da2f97f9159a0dc74da117881915ce2976569a5ec857c30c95fa6122dfe778e887918f413c6515a04ac6854073cc7b22fce33a61760ac9fc2373e2114903a5a662ba817f447edf3459ac39c62fc671c9ceca8866ed493aec115dbb8576e97424014b378c31e85d8136b38843b1039b5e2a20669291d19b666291e2200c411b1ba9c22449ffc30ed8e3bacf0d72644f825694bcd62d4cb0aebec2ceededb8e4162e5588213299b60e31fe783d9a2cce0a3aa445fe3e94067053b24661eac
private theorem part58 : 2 ^ prefix58 % Spec.Ffdh.ffdhe2048Prime = residue58 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue58)
    (e := prefix57) (a := residue57) (b := 1668916499) (n := 32)
    part57 (by decide +kernel) (by decide +kernel)
  rw [show prefix57 * 2 ^ (32 : Nat) + 1668916499 = prefix58 from by decide +kernel] at result
  exact result

private def prefix59 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (1 : Nat) * 2 ^ (0 : Nat))
private def residue59 : Nat := 0x7cf954c46e2375f1fe31e6d16cc9d4bb705630bccafdea1e5cd02dce88f2818bced40a360fc691281f12a8982f5e5889c1110503f3106da6277a62df293c9bb3987d0d84b85d9220de2eee5d88f07bc934c87275869fb16ead68219194b424bae84ff535337f9fadc16c9911fd95ecda88f5fe6e5ce5e5db432df25b808d03b9af56e284f8b5c1a9f330b0d44a72ed99bb8bd7eee21fda0eac18f1a93ddbee9b19acf6fe47698920b616d564a9f149bd049bb4d3d4bec0a2db70aa906043cb3ccb722ea333ad77a50eb27af5883d4e0c6d42f57469e7def17157055daaa7c6a2d378ac32a7e82f7a0b33d45c8ae32a688fba45384d8778019f3f5b91866cbb2b
private theorem part59 : 2 ^ prefix59 % Spec.Ffdh.ffdhe2048Prime = residue59 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue59)
    (e := prefix58) (a := residue58) (b := 1624864765) (n := 32)
    part58 (by decide +kernel) (by decide +kernel)
  rw [show prefix58 * 2 ^ (32 : Nat) + 1624864765 = prefix59 from by decide +kernel] at result
  exact result

private def prefix60 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (96 : Nat))
private def residue60 : Nat := 0x2f2fc195310f6613782b922a6ef769a3a27cba90cd05ace9d3643591ce4fd4fc295e7182649464cb25e8752a692ec100e72779551275e80134cff3a54014ec366fffcb4ccd5f0ad39f76067d3b04be48808346aa0fa73d77b80f7d05aba902199b330ce3ddb769bc020d7c40098a20d0acbdb50759f596c5bfef9d82942e4386026eb8e6a190f8455996b96010fb300b32c6d6a77a1eec285be76ba33cc2d7401e78b805bebed0dac50a0cad826ba7a961167dc608ea392e0aa96d83e51d4790e41c8f76cefa7797cad32913603fe7e6f35e3e83f6e4999d6a27a2b9f77790e60ba905addde6f124021d1c7b960a079280fae0968697db8bffa8b305304938cf
private theorem part60 : 2 ^ prefix60 % Spec.Ffdh.ffdhe2048Prime = residue60 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue60)
    (e := prefix59) (a := residue59) (b := 1144365340) (n := 32)
    part59 (by decide +kernel) (by decide +kernel)
  rw [show prefix59 * 2 ^ (32 : Nat) + 1144365340 = prefix60 from by decide +kernel] at result
  exact result

private def prefix61 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (64 : Nat))
private def residue61 : Nat := 0xe82a87571771a110e286726fdab40bb929abf06434f6362ca16d2f0cb012fbd27f579a21bd576b39ac26bba6aa718fcaa3dae7558d2624124deba7c792345019aca53831aa457ea6e31c2941d43b2e9281564353506dff070b86e38e2c7a24332fbecb0703820039ae52249e83e59e183ace7585c9b15ea1c00c608a5d7c1f1bf328795e92d052fa81f169607a8731aec166068fcb7eb5252b487b585cff31d523b4a07021909ddca96e59d35339a34ba60a2347b865c1f555311abe2e7b8aac747e8a7b3bb53a4ed4e271bca955d155811730a16de585f6b80aa1f0dc195d71a5f1a157f6b23a4a2fb31c4462581d34d0c871d13b70c264d9cf169841398756
private theorem part61 : 2 ^ prefix61 % Spec.Ffdh.ffdhe2048Prime = residue61 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue61)
    (e := prefix60) (a := residue60) (b := 815017547) (n := 32)
    part60 (by decide +kernel) (by decide +kernel)
  rw [show prefix60 * 2 ^ (32 : Nat) + 815017547 = prefix61 from by decide +kernel] at result
  exact result

private def prefix62 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (32 : Nat))
private def residue62 : Nat := 0xce6d826a45831c2f2ae8feaeea49385b57ede00cabcad5e1bef83e4b757e9dad665a6fe70415e59343c2af7a6a420e96c8af25ac068df1639bf3f6aa826cc42d2ba68b2a3bbe2aeb8c5c9bcd39d5edc5cb6a394574474f6ce7e9e934d5d33c33965ab3c5acb08dc9451431056ee7651a11cb4340c842e9dc3042a0c3c556ac04850db0b0c3783ae389de7c478f6fa7f0ed65f8ad0245e0bc1b19c0cdfc86afb93a67b86fbee8d6f8ac2f64a29eb19bcc37460457951e9f4d697225a27365d42aa87686148a8a060155ea9281b2d910ee9548a45054d46fbb704cd3129a6e7ad6f17362da79e9eed4f5117cd753fffd968ffb6710c3f63a2ae6b4e8e167260f71
private theorem part62 : 2 ^ prefix62 % Spec.Ffdh.ffdhe2048Prime = residue62 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue62)
    (e := prefix61) (a := residue61) (b := 4294967295) (n := 32)
    part61 (by decide +kernel) (by decide +kernel)
  rw [show prefix61 * 2 ^ (32 : Nat) + 4294967295 = prefix62 from by decide +kernel] at result
  exact result

private def prefix63 : Nat := ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) / ((2 ^ (128 : Nat)) ^ (0 : Nat) * 2 ^ (0 : Nat))
private def residue63 : Nat := 0x1
private theorem part63 : 2 ^ prefix63 % Spec.Ffdh.ffdhe2048Prime = residue63 := by
  have result := powerBlock_append (p := Spec.Ffdh.ffdhe2048Prime) (r := residue63)
    (e := prefix62) (a := residue62) (b := 4294967295) (n := 32)
    part62 (by decide +kernel) (by decide +kernel)
  rw [show prefix62 * 2 ^ (32 : Nat) + 4294967295 = prefix63 from by decide +kernel] at result
  exact result

theorem subgroup : 2 ^ ((Spec.Ffdh.ffdhe2048Prime - 1) / 2) % Spec.Ffdh.ffdhe2048Prime = 1 := by
  rw [show (Spec.Ffdh.ffdhe2048Prime - 1) / 2 = prefix63 from by decide +kernel]
  exact part63

end VG.Proof.Ffdh.VettedValidation.Ffdhe2048
