module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Impl.Camellia.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Spec.Camellia.Contract
public import VerifiedGarbage.Spec.Camellia.Cbc
public import VerifiedGarbage.Spec.Camellia.Cfb
public import VerifiedGarbage.Spec.Camellia.CfbFinal
public import VerifiedGarbage.Spec.Camellia.Ofb
public import VerifiedGarbage.Spec.Camellia.OfbFinal
public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Camellia.X86_64.KeyVerified
public import VerifiedGarbage.Proof.Camellia.X86_64.Verified
public import VerifiedGarbage.Proof.Camellia.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Camellia.X86_64.FbVerified
public import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalVerified
public import VerifiedGarbage.Proof.Camellia.X86_64.CtrVerified
public import VerifiedGarbage.Proof.Camellia.X86_64.CtrFinal
public import VerifiedGarbage.Spec.Camellia.CtrFinal
import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Camellia.CbcScratch
import VerifiedGarbage.Proof.Camellia.FbScratch
import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
import VerifiedGarbage.Proof.Camellia.X86_64.Lit
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Spec.Camellia.Contract
meta import VerifiedGarbage.Spec.Camellia.Cbc
meta import VerifiedGarbage.Spec.Camellia.Cfb
meta import VerifiedGarbage.Spec.Camellia.CfbFinal
meta import VerifiedGarbage.Spec.Camellia.Ofb
meta import VerifiedGarbage.Spec.Camellia.OfbFinal
meta import VerifiedGarbage.Spec.Camellia.Ctr
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Camellia.X86_64.KeyVerified
meta import VerifiedGarbage.Proof.Camellia.X86_64.Verified
meta import VerifiedGarbage.Proof.Camellia.X86_64.CbcVerified
meta import VerifiedGarbage.Proof.Camellia.X86_64.FbVerified
meta import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalVerified
meta import VerifiedGarbage.Proof.Camellia.X86_64.CtrVerified
meta import VerifiedGarbage.Proof.Camellia.X86_64.CtrFinal
meta import VerifiedGarbage.Spec.Camellia.CtrFinal
meta import VerifiedGarbage.Proof.Camellia.Scratch
meta import VerifiedGarbage.Proof.Camellia.CbcScratch
meta import VerifiedGarbage.Proof.Camellia.FbScratch
meta import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
meta import VerifiedGarbage.Proof.Camellia.X86_64.Lit
meta import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Camellia.ScrubLocal
meta import VerifiedGarbage.Proof.Camellia.ScrubLocal

/-!
# Camellia on x86-64, without secret residue

Key expansion and the ECB, CBC, CFB128, OFB and CTR functions, each followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Their postconditions read the
memory on return only within the buffers (`X86_64.Scrub.PostOut`), as the
frames that keep their working space on the stack already show
(`X86_64.Verified.stackScratchWiped`'s `hpost`).

`vg_camellia_ctr_final`, whose analysis does not succeed, is followed by
`Impl.Scrub.X86_64.scrubWith` with every granule of its stack wiped
(`X86_64.Scrub.withScrubAll`): it calls `vg_camellia_ctr`'s code as the
internal `vg_camellia_ctr_core` (`Impl.Camellia.X86_64.ctrFramed`), which
restores the callee-saved registers from slots of its frame the analysis
loses track of.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Spec.Camellia VG.Proof.Camellia.ScrubLocal

/-! ## Postconditions -/
theorem len_le (x : BitVec 64) (k : Nat) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.le_refl _

theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

theorem expandKeyOut : PostOut (expandKeyContract X86_64.abi 3216) (expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Camellia.expandKeyPostOut_local _)

theorem ecbOut (d : Direction) (stack : Nat) : PostOut (ecbContract X86_64.abi d stack) (ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, dt, ln], _ =>
      simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → blocksAt m₂ dt _ = _
      intro key hk
      rw [blocksAt_of hb.2 (len_le ln 16)]
      exact h key hk

theorem cbcEncryptOut (stack : Nat) :
    PostOut (cbcEncryptChainedContract X86_64.abi stack) (cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cbcDecryptOut (stack : Nat) :
    PostOut (cbcDecryptChainedContract X86_64.abi stack) (cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptOut (stack : Nat) : PostOut (cfbEncryptContract X86_64.abi stack) (cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptOut (stack : Nat) : PostOut (cfbDecryptContract X86_64.abi stack) (cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbOut (stack : Nat) : PostOut (ofbContract X86_64.abi stack) (ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptFinalOut (stack : Nat) :
    PostOut (cfbEncryptFinalContract X86_64.abi stack) (cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptFinalOut (stack : Nat) :
    PostOut (cfbDecryptFinalContract X86_64.abi stack) (cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbFinalOut (stack : Nat) : PostOut (ofbFinalContract X86_64.abi stack) (ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ctrOut (stack : Nat) : PostOut (ctrContract X86_64.abi stack) (ctrSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, ct, dt, ln], _ =>
      simp only [ctrSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ ct 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ctrFinalOut (stack : Nat) :
    PostOut (ctrFinalContract X86_64.abi stack) (ctrFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, ct, dt, ln], _ =>
      simp only [ctrFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ ct 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## The registrations -/

/-- `vg_camellia_expand_key`'s code. -/
abbrev expandKeyCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3216 .rcx 401 Impl.Camellia.X86_64.expandKey

/-- `vg_camellia_ecb_encrypt`'s code. -/
abbrev ecbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r8 401 (Impl.Camellia.X86_64.ecb .encrypt)

/-- `vg_camellia_ecb_decrypt`'s code. -/
abbrev ecbDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r8 401 (Impl.Camellia.X86_64.ecb .decrypt)

/-- `vg_camellia_cbc_encrypt_chained`'s code. -/
abbrev cbcEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cbcEncryptChained

/-- `vg_camellia_cbc_decrypt_chained`'s code. -/
abbrev cbcDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cbcDecryptChained

/-- `vg_camellia_cfb128_encrypt`'s code. -/
abbrev cfbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbEncrypt

/-- `vg_camellia_cfb128_encrypt_final`'s code. -/
abbrev cfbEncryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbEncryptFinal

/-- `vg_camellia_cfb128_decrypt`'s code. -/
abbrev cfbDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbDecrypt

/-- `vg_camellia_cfb128_decrypt_final`'s code. -/
abbrev cfbDecryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbDecryptFinal

/-- `vg_camellia_ofb`'s code. -/
abbrev ofbCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.ofb

/-- `vg_camellia_ofb_final`'s code. -/
abbrev ofbFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.ofbFinal

/-- `vg_camellia_ctr`'s code. -/
abbrev ctrCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.ctr

/-! ## The functions as emitted -/

theorem expandKey_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3216 .rcx 401 Impl.Camellia.X86_64.expandKey).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Camellia.expandKeyApi`'s function as emitted (`Impl.Camellia.X86_64.Fn.expandKey`) meets its contract in
constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed target Impl.Camellia.X86_64.Fn.expandKey (Spec.Camellia.expandKeyApi.contract X86_64.abi 3216) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.expandKeyApi)
    { code := expandKeyCode
      stack := 3216
      verified := Proof.Camellia.X86_64.expandKey_framed
      spSafe := expandKey_codeSp }
    .sse [] expandKeyOut (RScrub.pubOk_nil _) (by taint_decide)

theorem expandKey_spSafe : Impl.Camellia.X86_64.Fn.expandKey.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe expandKey_codeSp

theorem ecbEncrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r8 401 (Impl.Camellia.X86_64.ecb .encrypt)).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Camellia.ecbEncryptApi`'s function as emitted (`Impl.Camellia.X86_64.Fn.ecbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed target Impl.Camellia.X86_64.Fn.ecbEncrypt (Spec.Camellia.ecbEncryptApi.contract X86_64.abi 3216) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ecbEncryptApi)
    { code := ecbEncryptCode
      stack := 3216
      verified := Proof.Camellia.X86_64.ecb_framed .encrypt
      spSafe := ecbEncrypt_codeSp }
    .sse [(0, 1)] (ecbOut .encrypt _) (RScrub.pubOk_nil _) (by taint_decide)

theorem ecbEncrypt_spSafe : Impl.Camellia.X86_64.Fn.ecbEncrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ecbEncrypt_codeSp

theorem ecbDecrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r8 401 (Impl.Camellia.X86_64.ecb .decrypt)).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Camellia.ecbDecryptApi`'s function as emitted (`Impl.Camellia.X86_64.Fn.ecbDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed target Impl.Camellia.X86_64.Fn.ecbDecrypt (Spec.Camellia.ecbDecryptApi.contract X86_64.abi 3216) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ecbDecryptApi)
    { code := ecbDecryptCode
      stack := 3216
      verified := Proof.Camellia.X86_64.ecb_framed .decrypt
      spSafe := ecbDecrypt_codeSp }
    .sse [(0, 1)] (ecbOut .decrypt _) (RScrub.pubOk_nil _) (by taint_decide)

theorem ecbDecrypt_spSafe : Impl.Camellia.X86_64.Fn.ecbDecrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ecbDecrypt_codeSp

theorem cbcEncrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cbcEncryptChained).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Camellia.cbcEncryptChainedApi`'s function as emitted (`Impl.Camellia.X86_64.Fn.cbcEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cbcEncrypt_scrubbed :
    VerifiedScrubbed target Impl.Camellia.X86_64.Fn.cbcEncrypt (Spec.Camellia.cbcEncryptChainedApi.contract X86_64.abi 3288) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cbcEncryptChainedApi)
    { code := cbcEncryptCode
      stack := 3288
      verified := Proof.Camellia.X86_64.cbcEncryptChained_framed
      spSafe := cbcEncrypt_codeSp }
    .sse [(0, 1)] (cbcEncryptOut _) (RScrub.pubOk_nil _) (by taint_decide)

theorem cbcEncrypt_spSafe : Impl.Camellia.X86_64.Fn.cbcEncrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cbcEncrypt_codeSp

theorem cbcDecrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cbcDecryptChained).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Camellia.cbcDecryptChainedApi`'s function as emitted (`Impl.Camellia.X86_64.Fn.cbcDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cbcDecrypt_scrubbed :
    VerifiedScrubbed target Impl.Camellia.X86_64.Fn.cbcDecrypt (Spec.Camellia.cbcDecryptChainedApi.contract X86_64.abi 3288) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cbcDecryptChainedApi)
    { code := cbcDecryptCode
      stack := 3288
      verified := Proof.Camellia.X86_64.cbcDecryptChained_framed
      spSafe := cbcDecrypt_codeSp }
    .sse [(0, 1)] (cbcDecryptOut _) (RScrub.pubOk_nil _) (by taint_decide)

theorem cbcDecrypt_spSafe : Impl.Camellia.X86_64.Fn.cbcDecrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cbcDecrypt_codeSp

theorem cfbEncrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbEncrypt).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Camellia.cfbEncryptApi`'s function as emitted (`Impl.Camellia.X86_64.Fn.cfbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed target Impl.Camellia.X86_64.Fn.cfbEncrypt (Spec.Camellia.cfbEncryptApi.contract X86_64.abi 3288) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cfbEncryptApi)
    { code := cfbEncryptCode
      stack := 3288
      verified := Proof.Camellia.X86_64.cfbEncrypt_framed
      spSafe := cfbEncrypt_codeSp }
    .sse [(0, 1)] (cfbEncryptOut _) (RScrub.pubOk_nil _) (by taint_decide)

theorem cfbEncrypt_spSafe : Impl.Camellia.X86_64.Fn.cfbEncrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbEncrypt_codeSp

theorem cfbEncryptFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbEncryptFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Camellia.cfbEncryptFinalApi`'s function as emitted (`Impl.Camellia.X86_64.Fn.cfbEncryptFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed target Impl.Camellia.X86_64.Fn.cfbEncryptFinal (Spec.Camellia.cfbEncryptFinalApi.contract X86_64.abi 3288) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cfbEncryptFinalApi)
    { code := cfbEncryptFinalCode
      stack := 3288
      verified := Proof.Camellia.X86_64.cfbEncryptFinal_framed
      spSafe := cfbEncryptFinal_codeSp }
    .sse [(0, 1)] (cfbEncryptFinalOut _) (RScrub.pubOk_nil _) (by taint_decide)

theorem cfbEncryptFinal_spSafe : Impl.Camellia.X86_64.Fn.cfbEncryptFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbEncryptFinal_codeSp

theorem cfbDecrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbDecrypt).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Camellia.cfbDecryptApi`'s function as emitted (`Impl.Camellia.X86_64.Fn.cfbDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed target Impl.Camellia.X86_64.Fn.cfbDecrypt (Spec.Camellia.cfbDecryptApi.contract X86_64.abi 3288) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cfbDecryptApi)
    { code := cfbDecryptCode
      stack := 3288
      verified := Proof.Camellia.X86_64.cfbDecrypt_framed
      spSafe := cfbDecrypt_codeSp }
    .sse [(0, 1)] (cfbDecryptOut _) (RScrub.pubOk_nil _) (by taint_decide)

theorem cfbDecrypt_spSafe : Impl.Camellia.X86_64.Fn.cfbDecrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbDecrypt_codeSp

theorem cfbDecryptFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbDecryptFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Camellia.cfbDecryptFinalApi`'s function as emitted (`Impl.Camellia.X86_64.Fn.cfbDecryptFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed target Impl.Camellia.X86_64.Fn.cfbDecryptFinal (Spec.Camellia.cfbDecryptFinalApi.contract X86_64.abi 3288) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cfbDecryptFinalApi)
    { code := cfbDecryptFinalCode
      stack := 3288
      verified := Proof.Camellia.X86_64.cfbDecryptFinal_framed
      spSafe := cfbDecryptFinal_codeSp }
    .sse [(0, 1)] (cfbDecryptFinalOut _) (RScrub.pubOk_nil _) (by taint_decide)

theorem cfbDecryptFinal_spSafe : Impl.Camellia.X86_64.Fn.cfbDecryptFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbDecryptFinal_codeSp

theorem ofb_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.ofb).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Camellia.ofbApi`'s function as emitted (`Impl.Camellia.X86_64.Fn.ofb`) meets its contract in
constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed target Impl.Camellia.X86_64.Fn.ofb (Spec.Camellia.ofbApi.contract X86_64.abi 3288) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ofbApi)
    { code := ofbCode
      stack := 3288
      verified := Proof.Camellia.X86_64.ofb_framed
      spSafe := ofb_codeSp }
    .sse [(0, 1)] (ofbOut _) (RScrub.pubOk_nil _) (by taint_decide)

theorem ofb_spSafe : Impl.Camellia.X86_64.Fn.ofb.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ofb_codeSp

theorem ofbFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.ofbFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Camellia.ofbFinalApi`'s function as emitted (`Impl.Camellia.X86_64.Fn.ofbFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed target Impl.Camellia.X86_64.Fn.ofbFinal (Spec.Camellia.ofbFinalApi.contract X86_64.abi 3288) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ofbFinalApi)
    { code := ofbFinalCode
      stack := 3288
      verified := Proof.Camellia.X86_64.ofbFinal_framed
      spSafe := ofbFinal_codeSp }
    .sse [(0, 1)] (ofbFinalOut _) (RScrub.pubOk_nil _) (by taint_decide)

theorem ofbFinal_spSafe : Impl.Camellia.X86_64.Fn.ofbFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ofbFinal_codeSp

theorem ctr_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.ctr).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Camellia.ctrApi`'s function as emitted (`Impl.Camellia.X86_64.Fn.ctr`) meets its contract in
constant time and returns without secret residue. -/
theorem ctr_scrubbed :
    VerifiedScrubbed target Impl.Camellia.X86_64.Fn.ctr (Spec.Camellia.ctrApi.contract X86_64.abi 3288) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ctrApi)
    { code := ctrCode
      stack := 3288
      verified := Proof.Camellia.X86_64.ctr_framed
      spSafe := ctr_codeSp }
    .sse [(0, 1)] (ctrOut _) (RScrub.pubOk_nil _) (by taint_decide)

theorem ctr_spSafe : Impl.Camellia.X86_64.Fn.ctr.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ctr_codeSp

theorem ctrFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 72 .r9 8 Impl.Camellia.X86_64.ctrFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Camellia.ctrFinalApi`'s function as emitted (`Impl.Camellia.X86_64.Fn.ctrFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem ctrFinal_scrubbed :
    VerifiedScrubbed target Impl.Camellia.X86_64.Fn.ctrFinal (Spec.Camellia.ctrFinalApi.contract X86_64.abi 3368) 0 :=
  verifiedScrubbedAll (api := Spec.Camellia.ctrFinalApi)
    { code := Impl.StackScratch.X86_64.withStackScratchWiped 72 .r9 8 Impl.Camellia.X86_64.ctrFinal
      stack := 3368
      verified := Proof.Camellia.X86_64.ctrFinal_framed
      spSafe := ctrFinal_codeSp }
    .sse (ctrFinalOut _)

theorem ctrFinal_spSafe : Impl.Camellia.X86_64.Fn.ctrFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ctrFinal_codeSp
end VG.Proof.Camellia.X86_64.Scrub
