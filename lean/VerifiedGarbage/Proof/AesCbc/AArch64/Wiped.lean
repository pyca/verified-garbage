module

public import VerifiedGarbage.Impl.AesCbc.AArch64.Fn
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.AesCbc.Wipe
public import VerifiedGarbage.Proof.AesCbc.AArch64.Caller
public import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Verified
public import VerifiedGarbage.Proof.AesCbc.AArch64.Neon.Verified
public import VerifiedGarbage.Proof.Framework.AArch64.CallWipe
public import VerifiedGarbage.Proof.Zeroize.AArch64Wide
import VerifiedGarbage.Proof.AesEcb.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.Framework.AArch64.Clears
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAllW
public import VerifiedGarbage.Proof.Framework.AArch64.SideFill
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# AES-CBC on AArch64, zeroing the scratch it writes

Each implementation of `vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` that
writes its `scratch` buffer (all but the ones with the Cryptographic
Extension: the encryption, `Encrypt.code`, and the decryptions in seven
independent states, `Decrypt.code` with SHA-3's `eor3` and `Decrypt.codeAes`) is called by `callWipe`, as the internal function
`vg_aes_cbc_{en,de}crypt_unwiped<suffix>`, which then zeroes the whole of
`scratch` with `vg_zeroize`. Each implementation meets its contract and
leaves each byte of `scratch` unchanged or zero (`*_scrubbed`), which is
the contract of `Spec/Cbc/` (`*_verified`).

The functions as emitted are definitions in `Impl/`
(`Impl.AesCbc.AArch64.Fn`). The encryption with the Cryptographic Extension
(`Fn.encryptAes`) has no frames and writes nothing in `scratch`: its cleanup
only clears the registers it writes (`encryptAes_scrubbed`,
`encryptAes_written`); its decryptions are their own functions
(`Decrypt.codeC_scrubbed`, `Decrypt.codeAesC_scrubbed`). An implementation
that writes in `scratch` is a `CbcImpl`: the code of its encryption and of
its decryption, which the emitted functions call, then wipe `scratch`, then
clear the registers they may write and zero their 32 bytes of stack
(`Fn.encrypt`, `Fn.decryptWiped`; `encryptWiped_scrubbed`,
`decryptWiped_scrubbed`). `CbcImpl.blocks` is the one calling the blocks
functions of a `BlocksImpl`, and `CbcImpl.neon` the one whose decryption is
in AdvSIMD registers (`Neon.decrypt`).
-/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64.Wiped

open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.AesCbc.Wipe

/-- A call of `name`, whose code is `body`, then of `vg_zeroize` on the
2176 bytes of `scratch` (`Impl.AesCbc.AArch64.Fn.wiped`). -/
abbrev wiped (name : String) (body : Prog isa) : Prog isa := Impl.AesCbc.AArch64.Fn.wiped name body

/-- `vg_aes_cbc_encrypt<suffix>`, wiping `scratch`. -/
def encrypt (v : BlocksImpl) : Prog isa :=
  wiped ("vg_aes_cbc_encrypt_unwiped" ++ v.suffix) (Caller.encrypt v)

/-- `vg_aes_cbc_decrypt<suffix>`, wiping `scratch`. -/
def decrypt (v : BlocksImpl) : Prog isa :=
  wiped ("vg_aes_cbc_decrypt_unwiped" ++ v.suffix) (Impl.AesCbc.AArch64.decrypt v.dec)

theorem sat (P : Spec.Cbc.aesSig.Post 64) :
    ∃ s, (Spec.Cbc.aesSig.contract abi (pre 64) P false 32 none).pre s := by
  implies_sat [Spec.Cbc.aesSig, pre, AArch64.abi, AArch64.argRegs] [Proof.AesCbc.AArch64.sat]
    using Proof.AesCbc.AArch64.sat

theorem wiped_verified {P : Spec.Cbc.aesSig.Post 64} {name : String} {body : Prog isa}
    (h : Verified target body (Spec.Cbc.aesSig.contract abi (pre 64) P false 0 none))
    (hd : body.aarch64Depth = 0)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (Spec.Cbc.aesSig.words 64).length →
      (∀ b ∈ Sig.bufs Spec.Cbc.aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cbc.aesSig.words 64) P vs m₁ m' x → Curry.apply (Spec.Cbc.aesSig.words 64) P vs m₂ m' x)
    (hout : ∀ vs m m₁ m₂ x, vs.length = (Spec.Cbc.aesSig.words 64).length →
      (Sig.bufs Spec.Cbc.aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs Spec.Cbc.aesSig.params vs, b.1.Disjoint ⟨vs.getD 5 0, 272 * Elem.u64.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cbc.aesSig.words 64) P vs m m₁ x → Curry.apply (Spec.Cbc.aesSig.words 64) P vs m m₂ x) :
    Verified target (wiped name body)
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 P) false 32 none) :=
  Verified.callWipe' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := [])
    (nm := "scratch") (e := .u64) (k := 272) (n := 2176) (i := 5) h Proof.Zeroize.AArch64.wideVerified
    (by decide) rfl rfl rfl (by decide) (by decide) (by rw [hd]) Proof.Zeroize.AArch64.wide_noDit
    AesEcb.AArch64.zeroize_depth
    (Nat.zero_le _) (pre_local 64) hpost hout (Wipe.wiped 64 P) (sat _)

theorem encrypt_depth (v : BlocksImpl) : (Caller.encrypt v).aarch64Depth = 0 := by
  unfold Caller.encrypt
  split
  · exact AesEcb.AArch64.depth_of_noFrames (by decide)
  · simp only [Impl.AesCbc.AArch64.encrypt, Impl.AesCbc.AArch64.whole, Impl.AesCbc.AArch64.encBody,
      Code.aarch64Depth, AesEcb.AArch64.depth_of_noFrames v.encNoFrames, Nat.max_self]

theorem decrypt_depth (v : BlocksImpl) : (Impl.AesCbc.AArch64.decrypt v.dec).aarch64Depth = 0 := by
  simp only [Impl.AesCbc.AArch64.decrypt, Impl.AesCbc.AArch64.batched, Impl.AesCbc.AArch64.groups,
    Impl.AesCbc.AArch64.decGroup, Impl.AesCbc.AArch64.decBody,
    Code.aarch64Depth, AesEcb.AArch64.depth_of_noFrames v.decNoFrames, Nat.max_self]

theorem encrypt_scrubbed (v : BlocksImpl) :
    Verified target (encrypt v)
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (encPost 64)) false 32 none) :=
  wiped_verified (Proof.AesCbc.encrypt_keyed (Caller.verified v)) (encrypt_depth v)
    (encPost_local 64) (encPost_out 64)

theorem decrypt_scrubbed (v : BlocksImpl) :
    Verified target (decrypt v)
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (decPost 64)) false 32 none) :=
  wiped_verified (Proof.AesCbc.decrypt_keyed (Proof.AesCbc.AArch64.decrypt_verified v))
    (decrypt_depth v) (decPost_local 64) (decPost_out 64)

theorem encrypt_verified (v : BlocksImpl) :
    Verified target (encrypt v) (Spec.Cbc.aesEncryptContract abi 32) :=
  encrypt_scrubbed v

theorem decrypt_verified (v : BlocksImpl) :
    Verified target (decrypt v) (Spec.Cbc.aesDecryptContract abi 32) :=
  decrypt_scrubbed v

theorem args_length : ∀ s vals,
    abi.args ((Spec.Cbc.aesSig.words abi.ptrBits).map (·.bits abi.ptrBits)) = some vals →
      (vals s).length = (Spec.Cbc.aesSig.words abi.ptrBits).length := by
  intro s vals hv
  obtain rfl := Option.some.inj (hv.symm.trans (rfl : abi.args _ = some (regArgs Spec.Cbc.aesSig)))
  exact regArgs_length Spec.Cbc.aesSig s (by decide)

/-- The decryption with SHA-3's `eor3` writes nothing in `scratch`. -/
theorem decryptSha3_scrubbed :
    Verified target Impl.AesCbc.AArch64.Decrypt.code
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (decPost 64)) false 0 none) :=
  Verified.cbc_of_unwritten (Proof.AesCbc.decrypt_keyed Proof.AesCbc.AArch64.Decrypt.verified)
    Proof.AesCbc.AArch64.Decrypt.written args_length

/-- The decryption with the Cryptographic Extension, in seven independent
states, writes nothing in `scratch`. -/
theorem decryptAes_scrubbed :
    Verified target Impl.AesCbc.AArch64.Decrypt.codeAes
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (decPost 64)) false 0 none) :=
  Verified.cbc_of_unwritten (Proof.AesCbc.decrypt_keyed Proof.AesCbc.AArch64.Decrypt.verifiedAes)
    Proof.AesCbc.AArch64.Decrypt.writtenAes args_length

/-- `decryptSha3_scrubbed`, with the vector registers it leaves cleared. -/
theorem decryptSha3C_scrubbed :
    Verified target Proof.AesCbc.AArch64.Decrypt.codeC
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (decPost 64)) false 0 none) :=
  Clears.Verified.withClears decryptSha3_scrubbed (by decide)

/-- `decryptAes_scrubbed`, with the vector registers it leaves cleared. -/
theorem decryptAesC_scrubbed :
    Verified target Proof.AesCbc.AArch64.Decrypt.codeAesC
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (decPost 64)) false 0 none) :=
  Clears.Verified.withClears decryptAes_scrubbed (by decide)

/-- `vg_aes_cbc_decrypt_neon`: the decryption in AdvSIMD registers, wiping
`scratch`. -/
def decryptNeon : Prog isa :=
  wiped "vg_aes_cbc_decrypt_unwiped_neon" Impl.AesCbc.AArch64.Neon.decrypt

theorem decryptNeon_verified :
    Verified target decryptNeon (Spec.Cbc.aesDecryptContract abi 32) :=
  wiped_verified (Proof.AesCbc.decrypt_keyed Proof.AesCbc.AArch64.Neon.verified)
    (AesEcb.AArch64.depth_of_noFrames Proof.AesCbc.AArch64.Neon.decrypt_noFrames)
    (decPost_local 64) (decPost_out 64)

/-! ## Without secret residue -/

/-- A postcondition of a CBC function, `scrubbedPost` of `P`, reads the memory
on return only within the buffers, if `P` does (`hP`). -/
theorem scrubbedOut (P : Spec.Cbc.aesSig.Post 64)
    (hP : ∀ a b c d e f m m₁ m₂ x,
      (∀ i < 240, m₁ (a + BitVec.ofNat 64 i) = m₂ (a + BitVec.ofNat 64 i)) →
      (∀ i < 16, m₂ (c + BitVec.ofNat 64 i) = m₁ (c + BitVec.ofNat 64 i)) →
      (∀ i < e.toNat * 16, m₂ (d + BitVec.ofNat 64 i) = m₁ (d + BitVec.ofNat 64 i)) →
      P a b c d e f m m₁ x → P a b c d e f m m₂ x) :
    ∀ vs m m₁ m₂ x, vs.length = (Spec.Cbc.aesSig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs Spec.Cbc.aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cbc.aesSig.words abi.ptrBits) (scrubbedPost 64 P) vs m m₁ x →
        Curry.apply (Spec.Cbc.aesSig.words abi.ptrBits) (scrubbedPost 64 P) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hb h
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  rw [bufs_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  obtain ⟨h1, h2⟩ := h
  refine ⟨hP a b c d e f m m₁ m₂ x (fun i hi => (AesEcb.agree_of hb.1 i hi).symm)
    (AesEcb.agree_of hb.2.1) (AesEcb.agree_of hb.2.2.1) h1, fun z hz => ?_⟩
  rw [← hb.2.2.2 z hz]
  exact h2 z hz

theorem encryptOk : Scrub.ScrubAllOk (Spec.Cbc.aesEncryptContract abi 32) 32
    (Spec.Cbc.aesSig.retBits abi.ptrBits) := by
  rw [encrypt_eq]
  refine Scrub.scrubAllOk_regs (by decide) (by decide) (Nat.le_refl _) (scrubbedOut _ ?_)
  intro a b c d e f m m₁ m₂ x _ hc hd h key hk
  obtain ⟨h1, h2⟩ := h key hk
  have hb' : Spec.Cbc.blocksAt m₂ d e.toNat = Spec.Cbc.blocksAt m₁ d e.toNat :=
    blocksAt_congr hd
  exact ⟨hb'.trans h1, (AesEcb.bytesAt_congr hc).trans h2⟩

/-- `encryptOk` for the code without frames (`encryptAes_scrubbed`). -/
theorem encryptOk0 : Scrub.ScrubAllOk
    (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (encPost 64)) false 0 none) 0
    (Spec.Cbc.aesSig.retBits abi.ptrBits) := by
  refine Scrub.scrubAllOk_regs0 (by decide) (scrubbedOut _ ?_)
  intro a b c d e f m m₁ m₂ x _ hc hd h key hk
  obtain ⟨h1, h2⟩ := h key hk
  have hb' : Spec.Cbc.blocksAt m₂ d e.toNat = Spec.Cbc.blocksAt m₁ d e.toNat :=
    blocksAt_congr hd
  exact ⟨hb'.trans h1, (AesEcb.bytesAt_congr hc).trans h2⟩

theorem decryptOk : Scrub.ScrubAllOk (Spec.Cbc.aesDecryptContract abi 32) 32
    (Spec.Cbc.aesSig.retBits abi.ptrBits) := by
  rw [decrypt_eq]
  refine Scrub.scrubAllOk_regs (by decide) (by decide) (Nat.le_refl _) (scrubbedOut _ ?_)
  intro a b c d e f m m₁ m₂ x _ hc hd h key hk
  obtain ⟨h1, h2⟩ := h key hk
  have hb' : Spec.Cbc.blocksAt m₂ d e.toNat = Spec.Cbc.blocksAt m₁ d e.toNat :=
    blocksAt_congr hd
  exact ⟨hb'.trans h1, (AesEcb.bytesAt_congr hc).trans h2⟩

/-! ## The functions, as emitted -/

/-- `vg_aes_cbc_encrypt_aes` as emitted (`Impl.AesCbc.AArch64.Fn.encryptAes`):
the code with the AES instructions, which has no frames and writes nothing in
`scratch`, with the registers it writes cleared. -/
theorem encryptAes_scrubbed :
    VerifiedScrubbed target Impl.AesCbc.AArch64.Fn.encryptAes
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (encPost 64)) false 0 none) 0 :=
  Scrub.verifiedScrubbedOf0
    (Verified.cbc_of_unwritten (Proof.AesCbc.encrypt_keyed Proof.AesCbc.AArch64.Encrypt.verified)
      Proof.AesCbc.AArch64.Encrypt.written args_length)
    encryptOk0 (by kernel_rfl) (by kernel_rfl) (.inl rfl)

/-- It writes nothing in `scratch`. -/
theorem encryptAes_written : ∀ s t s', (Proof.AesCbc.encryptRoundsContract AArch64.abi).pre s →
    Exec isa Impl.AesCbc.AArch64.Fn.encryptAes s t s' →
      Sig.writtenWithin AArch64.abi Spec.Cbc.aesSig [("scratch", 0)] s s' :=
  Scrub.written_scrubOf0 (.inl rfl) Proof.AesCbc.AArch64.Encrypt.written

/-- An implementation of AES-CBC that writes in `scratch`: the code of its
encryption and of its decryption, which `vg_aes_cbc_encrypt<suffix>` and
`vg_aes_cbc_decrypt<suffix>` call, then wipe `scratch`
(`Impl.AesCbc.AArch64.Fn.encrypt`, `decryptWiped`). -/
structure CbcImpl where
  suffix : String
  enc : Prog isa
  encOk : Verified target (wiped ("vg_aes_cbc_encrypt_unwiped" ++ suffix) enc) (Spec.Cbc.aesEncryptContract abi 32)
  encSide : Scrub.sideAll (fun i => !i.writesDit) enc = true
  encDepth : enc.aarch64Depth = 0
  dec : Prog isa
  decOk : Verified target (wiped ("vg_aes_cbc_decrypt_unwiped" ++ suffix) dec) (Spec.Cbc.aesDecryptContract abi 32)
  decSide : Scrub.sideAll (fun i => !i.writesDit) dec = true
  decDepth : dec.aarch64Depth = 0

theorem encrypt_side (b : Impl.Aes.AArch64.Blocks)
    (h : Scrub.sideAll (fun i => !i.writesDit) b.code = true) :
    Scrub.sideAll (fun i => !i.writesDit) (Impl.AesCbc.AArch64.encrypt b) = true := by
  rcases b with ⟨n, code, cl, sc⟩
  have e : Impl.AesCbc.AArch64.encrypt ⟨n, code, cl, sc⟩ =
      Code.fillCalls n code (Impl.AesCbc.AArch64.encrypt ⟨"", .block [], cl, sc⟩) := by kernel_rfl
  rw [e]
  exact Scrub.sideAll_fillCalls h (by kernel_rfl)

theorem decrypt_side (b : Impl.Aes.AArch64.Blocks)
    (h : Scrub.sideAll (fun i => !i.writesDit) b.code = true) :
    Scrub.sideAll (fun i => !i.writesDit) (Impl.AesCbc.AArch64.decrypt b) = true := by
  rcases b with ⟨n, code, cl, sc⟩
  have e : Impl.AesCbc.AArch64.decrypt ⟨n, code, cl, sc⟩ =
      Code.fillCalls n code (Impl.AesCbc.AArch64.decrypt ⟨"", .block [], cl, sc⟩) := by kernel_rfl
  rw [e]
  exact Scrub.sideAll_fillCalls h (by kernel_rfl)

/-- The functions calling the blocks functions of `v`. -/
def CbcImpl.blocks (v : BlocksImpl) (h : v.enc.name ≠ "vg_aes_encrypt_blocks_aes") : CbcImpl where
  suffix := v.suffix
  enc := Impl.AesCbc.AArch64.encrypt v.enc
  encOk := by
    have := encrypt_verified v
    rwa [encrypt, Caller.encrypt, ite_eq_right h] at this
  encSide := encrypt_side v.enc (Scrub.sideAll_noDit_of_calleeSide v.encScrub)
  encDepth := by
    have := encrypt_depth v
    rwa [Caller.encrypt, ite_eq_right h] at this
  dec := Impl.AesCbc.AArch64.decrypt v.dec
  decOk := decrypt_verified v
  decSide := decrypt_side v.dec (Scrub.sideAll_noDit_of_calleeSide v.decScrub)
  decDepth := decrypt_depth v

/-- The implementation in AdvSIMD registers: the encryption calling its
blocks function, and its own decryption (`Impl.AesCbc.AArch64.Neon.decrypt`). -/
def CbcImpl.neon (v : BlocksImpl) (h : v.enc.name ≠ "vg_aes_encrypt_blocks_aes") (hs : v.suffix = "_neon") :
    CbcImpl where
  suffix := v.suffix
  enc := Impl.AesCbc.AArch64.encrypt v.enc
  encOk := (CbcImpl.blocks v h).encOk
  encSide := (CbcImpl.blocks v h).encSide
  encDepth := (CbcImpl.blocks v h).encDepth
  dec := Impl.AesCbc.AArch64.Neon.decrypt
  decOk := by rw [hs]; exact decryptNeon_verified
  decSide := by kernel_rfl
  decDepth := Proof.Aes.AArch64.depth_of_noFrames Proof.AesCbc.AArch64.Neon.decrypt_noFrames

private theorem wiped_scrubbed {k : Contract isa} {name : String} {body : Prog isa}
    (hv : Verified target (wiped name body) k) (hok : Scrub.ScrubAllOk k 32 0)
    (hs : Scrub.sideAll (fun i => !i.writesDit) body = true) (hd : body.aarch64Depth = 0) :
    VerifiedScrubbed target (Impl.Scrub.AArch64.scrubOf 32 0 (wiped name body)) k 0 :=
  Scrub.verifiedScrubbedOfFill (n := name) (e := Impl.AesCbc.AArch64.Fn.wiped "" (.block [])) hv hok
    (by kernel_rfl) hs hd (by kernel_rfl) (by decide)
    (Nat.le_of_ble_eq_true (by kernel_rfl)) (.inl rfl)

/-- `vg_aes_cbc_encrypt<suffix>` over `v`, as emitted. -/
theorem encryptWiped_scrubbed (v : CbcImpl) :
    VerifiedScrubbed target (Impl.AesCbc.AArch64.Fn.encrypt v.suffix v.enc)
      (Spec.Cbc.aesEncryptContract abi 32) 0 :=
  wiped_scrubbed v.encOk encryptOk v.encSide v.encDepth

/-- `vg_aes_cbc_decrypt<suffix>` over `v`, as emitted. -/
theorem decryptWiped_scrubbed (v : CbcImpl) :
    VerifiedScrubbed target (Impl.AesCbc.AArch64.Fn.decryptWiped v.suffix v.dec)
      (Spec.Cbc.aesDecryptContract abi 32) 0 :=
  wiped_scrubbed v.decOk decryptOk v.decSide v.decDepth

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.AesCbc.AArch64.Decrypt.codeC_scrubbed :
    VerifiedScrubbed _root_.VG.AArch64.target Impl.AesCbc.AArch64.Fn.decrypt
      (Sig.contract AArch64.abi Spec.Cbc.aesSig (Proof.AesCbc.Wipe.pre 64)   (Proof.AesCbc.Wipe.scrubbedPost 64 (Proof.AesCbc.Wipe.decPost 64))) 0 :=
  ⟨Proof.AesCbc.AArch64.Wiped.decryptSha3C_scrubbed,
    Proof.AesCbc.AArch64.Decrypt.codeC_noResidue _⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.AesCbc.AArch64.Decrypt.codeAesC_scrubbed :
    VerifiedScrubbed _root_.VG.AArch64.target Impl.AesCbc.AArch64.Fn.decryptAes
      (Sig.contract AArch64.abi Spec.Cbc.aesSig (Proof.AesCbc.Wipe.pre 64)   (Proof.AesCbc.Wipe.scrubbedPost 64 (Proof.AesCbc.Wipe.decPost 64))) 0 :=
  ⟨Proof.AesCbc.AArch64.Wiped.decryptAesC_scrubbed,
    Proof.AesCbc.AArch64.Decrypt.codeAesC_noResidue _⟩

end VG.Proof.AesCbc.AArch64.Wiped
