module

public import VerifiedGarbage.Impl.AesEcb.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.AesEcb.Wipe
public import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant
public import VerifiedGarbage.Proof.Framework.X86_64.CallWipe
public import VerifiedGarbage.Proof.Zeroize.X86_64Impl
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr

/-!
# AES-ECB on x86-64

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt`, for each implementation `v`
of the blocks functions (`BlocksImpl`) and `z` of `vg_zeroize`
(`ZeroizeImpl`): where `v`'s function writes nothing in `scratch`
(`v.encWritten = 0`), its code (`encrypt_free`, `Verified.ecb_of_unwritten`);
otherwise a call of it, then of `z` on the first `v.encWritten` bytes of
`scratch`, the only ones it writes (`encrypt_verified`:
`Verified.callWipeTail'`, with the side conditions of
`Proof/AesEcb/Wipe.lean`, with 24 bytes of stack, the frame and the return
address). Likewise for decryption.

Which of these are emitted, for each `v` and `z` (`encryptRegs`,
`decryptRegs`): `v`'s code alone, where it writes nothing in `scratch`,
once (with the `z` of no suffix); the call wiped with `z` where `v` needs
AVX, only with the `z` that needs it (so the instance has `v`'s suffix and
needs no more than `v`'s features); and otherwise the call wiped with each
`z`, named by both suffixes. `v`'s code alone is followed by
`Impl.Scrub.X86_64.scrubSel` (`X86_64.Scrub.verifiedScrubbedSel`) where `v` gives its
residue analysis (`BlocksImpl.ecbEncRes`); every other instance returns
with its whole stack wiped (`Impl.Scrub.X86_64.scrubAll`, at most 24 bytes).
Their postconditions read the memory on return only within the data and
`scratch` (`encryptOut`, `decryptOut`).
-/

@[expose] public section

namespace VG.Proof.AesEcb.X86_64

open VG VG.X86_64 VG.Proof.Aes.X86_64 VG.Proof.Zeroize.X86_64 VG.X86_64.Scrub

theorem enc_verified (v : BlocksImpl) :
    Verified target v.enc.code (Proof.Aes.encryptBlocksRoundsContract abi) :=
  Verified.of_correct v.encOk v.encCt AesNi.encryptBlocks_implies

theorem dec_verified (v : BlocksImpl) :
    Verified target v.dec.code (Proof.Aes.decryptBlocksRoundsContract abi) :=
  Verified.of_correct v.decOk v.decCt AesNi.decryptBlocks_implies

theorem args_length : ∀ s vals,
    abi.args ((Spec.Aes.blocksSig.words abi.ptrBits).map (·.bits abi.ptrBits)) = some vals →
      (vals s).length = (Spec.Aes.blocksSig.words abi.ptrBits).length := by
  intro s vals hv
  obtain rfl := Option.some.inj (hv.symm.trans (rfl : abi.args _ = some (regArgs Spec.Aes.blocksSig)))
  exact regArgs_length Spec.Aes.blocksSig s (by decide)

/-- A state satisfying the ECB contracts' precondition. -/
theorem sat (post : Spec.Aes.blocksSig.Post 64) :
    ∃ s, (Spec.Aes.blocksSig.contract abi (pre 64) post false 24 none).pre s := by
  implies_sat [Spec.Aes.blocksSig, pre, X86_64.abi, X86_64.argRegs] [Proof.Aes.X86_64.blocksSat]
    using Proof.Aes.X86_64.blocksSat

/-- A call of the blocks function `b`, then of `z` on the first `n` bytes of
`scratch` (the fifth argument, in `r8`). -/
def wiped (z : ZeroizeImpl) (n : Nat) (b : Impl.Aes.X86_64.Blocks) : Prog isa :=
  Impl.CallWipe.X86_64.callWipe .r8 n b.name b.code z.name z.code

theorem wiped_spSafe {z : ZeroizeImpl} {n : Nat} {b : Impl.Aes.X86_64.Blocks}
    (h : b.code.all (fun i => !isa.writesSp i) = true) :
    (wiped z n b).all (fun i => !isa.writesSp i) = true :=
  callWipe_spSafe h z.spSafe

/-- `vg_aes_ecb_encrypt` for `v`, where its blocks function writes nothing in
`scratch`: that function's code. -/
theorem encrypt_free (v : BlocksImpl) (h : v.encWritten = 0) :
    Verified target v.enc.code (Spec.AesEcb.encryptContract abi 0) :=
  Verified.ecb_of_unwritten (Proof.Aes.encryptBlocks_keyed (enc_verified v)) (h ▸ v.encWrittenOk)
    args_length

/-- `vg_aes_ecb_decrypt` for `v`, where its blocks function writes nothing in
`scratch`. -/
theorem decrypt_free (v : BlocksImpl) (h : v.decWritten = 0) :
    Verified target v.dec.code (Spec.AesEcb.decryptContract abi 0) :=
  Verified.ecb_of_unwritten (Proof.Aes.decryptBlocks_keyed (dec_verified v)) (h ▸ v.decWrittenOk)
    args_length

/-- `vg_aes_ecb_encrypt` for `v`: its blocks function, then `z` on the bytes
of `scratch` it writes. -/
theorem encrypt_verified (v : BlocksImpl) (z : ZeroizeImpl) :
    Verified target (wiped z v.encWritten v.enc) (Spec.AesEcb.encryptContract abi 24) :=
  Verified.callWipeTail' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (nm := "scratch") (e := .u64) (k := 256)
    (i := 4)
    (Verified.tail_of_written (Proof.Aes.encryptBlocks_keyed (enc_verified v)) v.encWrittenOk args_length)
    z.verified (by decide) rfl rfl rfl (by have := v.encWrittenLe; simp only [Elem.size]; omega_using [this])
    (by have := v.encWrittenLe; omega_using [this]) (by decide) v.encSpSafe (by rw [v.encNoStack]) z.spSafe z.noMx
    (by rw [z.xd]) (Nat.le_refl _) (pre_local 64) (postTail_local 64 _ _) (postTail_out 64 _ v.encWrittenLe)
    (wipedTail 64 _ _) (sat _)

/-- `vg_aes_ecb_decrypt` for `v`, with `z`. -/
theorem decrypt_verified (v : BlocksImpl) (z : ZeroizeImpl) :
    Verified target (wiped z v.decWritten v.dec) (Spec.AesEcb.decryptContract abi 24) :=
  Verified.callWipeTail' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (nm := "scratch") (e := .u64) (k := 256)
    (i := 4)
    (Verified.tail_of_written (Proof.Aes.decryptBlocks_keyed (dec_verified v)) v.decWrittenOk args_length)
    z.verified (by decide) rfl rfl rfl (by have := v.decWrittenLe; simp only [Elem.size]; omega_using [this])
    (by have := v.decWrittenLe; omega_using [this]) (by decide) v.decSpSafe (by rw [v.decNoStack]) z.spSafe z.noMx
    (by rw [z.xd]) (Nat.le_refl _) (pre_local 64) (postTail_local 64 _ _) (postTail_out 64 _ v.decWrittenLe)
    (wipedTail 64 _ _) (sat _)

theorem encrypt_spSafe (v : BlocksImpl) (z : ZeroizeImpl) :
    (wiped z v.encWritten v.enc).all (fun i => !isa.writesSp i) = true := wiped_spSafe v.encSpSafe

theorem decrypt_spSafe (v : BlocksImpl) (z : ZeroizeImpl) :
    (wiped z v.decWritten v.dec).all (fun i => !isa.writesSp i) = true := wiped_spSafe v.decSpSafe

/-- The postcondition of `vg_aes_ecb_encrypt` reads the memory on return only
within the buffers. -/
theorem encryptOut (stack : Nat) :
    Scrub.PostOut (Spec.AesEcb.encryptContract abi stack) (Spec.Aes.blocksSig.retBits 64) := by
  rw [encrypt_eq]
  exact Scrub.postOut_of_local (leak := none) Scrub.ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, rfl⟩ := vs_eq hlen
    rw [bufs_eq] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun key hk => ?_, fun z hz => ?_⟩
    · show Spec.Aes.statesAt m₂ c (d.setWidth abi.ptrBits).toNat = _
      have hd := agree_of hb.2.1
      rw [statesAt_congr fun i hi => hd i (by have := n_le (pb := abi.ptrBits) d; omega_using [hi, this])]
      exact h1 key hk
    · rw [← hb.2.2 z hz]
      exact h2 z hz

/-- The postcondition of `vg_aes_ecb_decrypt` reads the memory on return only
within the buffers. -/
theorem decryptOut (stack : Nat) :
    Scrub.PostOut (Spec.AesEcb.decryptContract abi stack) (Spec.Aes.blocksSig.retBits 64) := by
  rw [decrypt_eq]
  exact Scrub.postOut_of_local (leak := none) Scrub.ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, rfl⟩ := vs_eq hlen
    rw [bufs_eq] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun key hk => ?_, fun z hz => ?_⟩
    · show Spec.Aes.statesAt m₂ c (d.setWidth abi.ptrBits).toNat = _
      have hd := agree_of hb.2.1
      rw [statesAt_congr fun i hi => hd i (by have := n_le (pb := abi.ptrBits) d; omega_using [hi, this])]
      exact h1 key hk
    · rw [← hb.2.2 z hz]
      exact h2 z hz

/-- `vg_aes_ecb_encrypt` as `v`'s encryption alone, where it writes no
scratch space, as emitted (`Impl.AesEcb.X86_64.Fn.plain`). -/
theorem encryptPlain_scrubbed (v : BlocksImpl) (h : v.encWritten = 0) :
    VerifiedScrubbed target (Impl.AesEcb.X86_64.Fn.plain v.level v.enc) (Spec.AesEcb.encryptApi.contract abi 0) 0 :=
  verifiedScrubbedAllSide (api := Spec.AesEcb.encryptApi)
    { code := v.enc.code, verified := encrypt_free v h, spSafe := v.encSpSafe }
    v.level (encryptOut _) (calleeSide_mono (Nat.le_refl _) (Nat.zero_le _) v.encSide) (Nat.le_refl _)

/-- `vg_aes_ecb_decrypt` as `v`'s decryption alone, as emitted. -/
theorem decryptPlain_scrubbed (v : BlocksImpl) (h : v.decWritten = 0) :
    VerifiedScrubbed target (Impl.AesEcb.X86_64.Fn.plain v.level v.dec) (Spec.AesEcb.decryptApi.contract abi 0) 0 :=
  verifiedScrubbedAllSide (api := Spec.AesEcb.decryptApi)
    { code := v.dec.code, verified := decrypt_free v h, spSafe := v.decSpSafe }
    v.level (decryptOut _) (calleeSide_mono (Nat.le_refl _) (Nat.zero_le _) v.decSide) (Nat.le_refl _)

/-- `vg_aes_ecb_encrypt` as `v`'s encryption, then the zeroing with `z` of
the scratch space it writes, as emitted (`Impl.AesEcb.X86_64.Fn.wiped`): its code is its code
over a stub, with `v`'s and `z`'s where it calls them (`Fill`). -/
theorem encryptWiped_scrubbed (v : BlocksImpl) (z : ZeroizeImpl) :
    VerifiedScrubbed target (Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.encWritten v.enc z.name z.code)
      (Spec.AesEcb.encryptApi.contract abi 24) 0 :=
  have := calleeSide_mono (level_join_left v.level z.level) (Nat.le_refl _) v.encSide
  have := calleeSide_mono (level_join_right v.level z.level) (Nat.le_refl _) z.side
  verifiedScrubbedAllFill (api := Spec.AesEcb.encryptApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.CallWipe.X86_64.callWipe .r8 v.encWritten "" (.block []) "" (.block []))
    { code := wiped z v.encWritten v.enc, stack := 24, verified := encrypt_verified v z,
      spSafe := encrypt_spSafe v z }
    _ (encryptOut _) (by unfold wiped; fill_calls) (Nat.zero_le _) (Nat.le_refl _)
    (ha := by rcases v.writtenOk.1 with h | h <;> rw [h] <;> lit_decide)

/-- `vg_aes_ecb_decrypt` as `v`'s decryption, then the zeroing with `z`. -/
theorem decryptWiped_scrubbed (v : BlocksImpl) (z : ZeroizeImpl) :
    VerifiedScrubbed target (Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.decWritten v.dec z.name z.code)
      (Spec.AesEcb.decryptApi.contract abi 24) 0 :=
  have := calleeSide_mono (level_join_left v.level z.level) (Nat.le_refl _) v.decSide
  have := calleeSide_mono (level_join_right v.level z.level) (Nat.le_refl _) z.side
  verifiedScrubbedAllFill (api := Spec.AesEcb.decryptApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.CallWipe.X86_64.callWipe .r8 v.decWritten "" (.block []) "" (.block []))
    { code := wiped z v.decWritten v.dec, stack := 24, verified := decrypt_verified v z,
      spSafe := decrypt_spSafe v z }
    _ (decryptOut _) (by unfold wiped; fill_calls) (Nat.zero_le _) (Nat.le_refl _)
    (ha := by rcases v.writtenOk.2 with h | h <;> rw [h] <;> lit_decide)

/-- The implementations of `vg_aes_ecb_encrypt` over `v` that are emitted
with `z` (see the module's documentation). -/
def encryptRegs (v : BlocksImpl) (z : ZeroizeImpl) : List (Registration Spec.AesEcb.encryptApi target) :=
  if h : v.encWritten = 0 then
    if z.suffix = "" then [{
      suffix := v.suffix
      code := Impl.AesEcb.X86_64.Fn.plain v.level v.enc
      verified := encryptPlain_scrubbed v h
      spSafe := scrubKs_spSafe v.encSpSafe }]
    else []
  else if v.features.contains "avx" then
    if z.features = ["avx"] then [{
      suffix := v.suffix
      code := Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.encWritten v.enc z.name z.code
      verified := encryptWiped_scrubbed v z
      spSafe := scrubKs_spSafe (encrypt_spSafe v z) }]
    else []
  else [{
    suffix := v.suffix ++ z.suffix
    code := Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.encWritten v.enc z.name z.code
    verified := encryptWiped_scrubbed v z
    spSafe := scrubKs_spSafe (encrypt_spSafe v z) }]

/-- The implementations of `vg_aes_ecb_decrypt` over `v` that are emitted with
`z` (see the module's documentation). -/
def decryptRegs (v : BlocksImpl) (z : ZeroizeImpl) : List (Registration Spec.AesEcb.decryptApi target) :=
  if h : v.decWritten = 0 then
    if z.suffix = "" then [{
      suffix := v.suffix
      code := Impl.AesEcb.X86_64.Fn.plain v.level v.dec
      verified := decryptPlain_scrubbed v h
      spSafe := scrubKs_spSafe v.decSpSafe }]
    else []
  else if v.features.contains "avx" then
    if z.features = ["avx"] then [{
      suffix := v.suffix
      code := Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.decWritten v.dec z.name z.code
      verified := decryptWiped_scrubbed v z
      spSafe := scrubKs_spSafe (decrypt_spSafe v z) }]
    else []
  else [{
    suffix := v.suffix ++ z.suffix
    code := Impl.AesEcb.X86_64.Fn.wiped (v.level.join z.level) v.decWritten v.dec z.name z.code
    verified := decryptWiped_scrubbed v z
    spSafe := scrubKs_spSafe (decrypt_spSafe v z) }]

end VG.Proof.AesEcb.X86_64
