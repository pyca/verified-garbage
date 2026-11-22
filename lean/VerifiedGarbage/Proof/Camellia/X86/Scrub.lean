module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Proof.Framework.X86.ScrubWiped
public import VerifiedGarbage.Impl.Camellia.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Camellia.Contract
public import VerifiedGarbage.Spec.Camellia.Cbc
public import VerifiedGarbage.Spec.Camellia.Cfb
public import VerifiedGarbage.Spec.Camellia.CfbFinal
public import VerifiedGarbage.Spec.Camellia.Ofb
public import VerifiedGarbage.Spec.Camellia.OfbFinal
public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Spec.Camellia.CtrFinal
public import VerifiedGarbage.Proof.Camellia.X86.KeyVerified
public import VerifiedGarbage.Proof.Camellia.X86.Verified
public import VerifiedGarbage.Proof.Camellia.X86.CbcVerified
public import VerifiedGarbage.Proof.Camellia.X86.FbVerified
public import VerifiedGarbage.Proof.Camellia.X86.FbFinalVerified
public import VerifiedGarbage.Proof.Camellia.X86.CtrVerified
public import VerifiedGarbage.Proof.Camellia.X86.CtrFinal
import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Camellia.ScrubLocal
import VerifiedGarbage.Proof.Camellia.X86.Lit
import VerifiedGarbage.Proof.Camellia.X86.CbcLit
import VerifiedGarbage.Proof.Camellia.X86.FbLit
import VerifiedGarbage.Proof.Camellia.X86.FbFinalLit
import VerifiedGarbage.Proof.Camellia.X86.CtrLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Proof.Framework.X86.ScrubWiped
meta import VerifiedGarbage.Impl.Camellia.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Camellia.Contract
meta import VerifiedGarbage.Spec.Camellia.Cbc
meta import VerifiedGarbage.Spec.Camellia.Cfb
meta import VerifiedGarbage.Spec.Camellia.CfbFinal
meta import VerifiedGarbage.Spec.Camellia.Ofb
meta import VerifiedGarbage.Spec.Camellia.OfbFinal
meta import VerifiedGarbage.Spec.Camellia.Ctr
meta import VerifiedGarbage.Spec.Camellia.CtrFinal
meta import VerifiedGarbage.Proof.Camellia.X86.KeyVerified
meta import VerifiedGarbage.Proof.Camellia.X86.Verified
meta import VerifiedGarbage.Proof.Camellia.X86.CbcVerified
meta import VerifiedGarbage.Proof.Camellia.X86.FbVerified
meta import VerifiedGarbage.Proof.Camellia.X86.FbFinalVerified
meta import VerifiedGarbage.Proof.Camellia.X86.CtrVerified
meta import VerifiedGarbage.Proof.Camellia.X86.CtrFinal
meta import VerifiedGarbage.Proof.Camellia.Scratch
meta import VerifiedGarbage.Proof.Camellia.ScrubLocal
meta import VerifiedGarbage.Proof.Camellia.X86.Lit
meta import VerifiedGarbage.Proof.Camellia.X86.CbcLit
meta import VerifiedGarbage.Proof.Camellia.X86.FbLit
meta import VerifiedGarbage.Proof.Camellia.X86.FbFinalLit
meta import VerifiedGarbage.Proof.Camellia.X86.CtrLit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Camellia on x86 (32-bit), without secret residue

Key expansion and Camellia's ECB, CBC, CFB128, OFB and CTR functions, and the
final pieces of CFB128, OFB and CTR, run with their working space in a frame
on the stack (`withStackScratchWiped`). Key expansion calls nothing in its
frame, which it wipes itself: as emitted (`Impl.Camellia.X86.Fn.expandKey`)
it then clears the registers alone (`X86.Scrub.verifiedScrubbedWiped`). As
emitted, each of the others then zeroes, of the stack its contract reserves
below `esp`, only the 10 to 24 doublewords that the residue analysis
(`X86.rtaint`) finds it may leave different in two runs: the header of its
working space's frame and the frames of the calls of
`vg_camellia_crypt_prepared` below it. It clears the registers a callee may
change, and returns without secret residue (`X86.Scrub.verifiedScrubbedSel`,
the kernel evaluating the analysis of the code with its cleanup:
`taint_decide_ct`). `vg_camellia_ctr_final` calls an implementation of
`vg_camellia_ctr`'s code (`CtrFinal.CtrImpl`), which states the doublewords
it zeroes with it; the baseline's (`CtrFinal.CtrImpl.scalar`) is an internal
function of its own, `vg_camellia_ctr_core` (`Impl.Camellia.X86.ctrFramed`).
Their
postconditions read the memory on return only within their buffers, as on
the other targets (`Proof/Camellia/ScrubLocal.lean`); a length is the low 32
bits of its argument word.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Spec.Camellia VG.Proof.Camellia.ScrubLocal

/-! ## Postconditions -/

theorem len_le (x : BitVec 64) (k : Nat) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.mul_le_mul_right _ (by simp only [ArgWord.ofRaw, BitVec.toNat_setWidth]; exact Nat.mod_le _ _)

theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size := by
  have := len_le x 1
  simpa only [Nat.mul_one, Elem.size] using this

theorem ecbOut (d : Direction) (stack : Nat) : PostOut (ecbContract X86.abi d stack) (ecbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, dt, ln], _ =>
      simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → blocksAt m₂ dt _ = _
      intro key hk
      rw [blocksAt_of hb.2 (len_le ln 16)]
      exact h key hk

theorem cbcEncryptOut (stack : Nat) : PostOut (cbcEncryptChainedContract X86.abi stack) (cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cbcDecryptOut (stack : Nat) : PostOut (cbcDecryptChainedContract X86.abi stack) (cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptOut (stack : Nat) : PostOut (cfbEncryptContract X86.abi stack) (cfbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptOut (stack : Nat) : PostOut (cfbDecryptContract X86.abi stack) (cfbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbOut (stack : Nat) : PostOut (ofbContract X86.abi stack) (ofbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (cfbEncryptFinalContract X86.abi stack) (cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (cfbDecryptFinalContract X86.abi stack) (cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbFinalOut (stack : Nat) : PostOut (ofbFinalContract X86.abi stack) (ofbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ctrOut (stack : Nat) : PostOut (ctrContract X86.abi stack) (ctrSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, ct, dt, ln], _ =>
      simp only [ctrSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ ct 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ctrFinalOut (stack : Nat) : PostOut (ctrFinalContract X86.abi stack) (ctrFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, ct, dt, ln], _ =>
      simp only [ctrFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ ct 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## The functions as emitted -/

/-- `Spec.Camellia.expandKeyApi` as emitted (`Impl.Camellia.X86.Fn.expandKey`) meets its contract
in constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Fn.expandKey (Spec.Camellia.expandKeyContract X86.abi 2708) 0 :=
  verifiedScrubbedWiped (sig := Spec.Camellia.expandKeySig) (nm := "scratch") (e := .u64) (n := 336)
    (pre := Spec.Camellia.expandKeyPre X86.abi.ptrBits) (post := Spec.Camellia.expandKeyPost X86.abi.ptrBits)
    (bytes := 2708) (words := 672)
    (by rw [← Proof.Camellia.expandKeyScratchContract_eq]; exact Proof.Camellia.X86.expandKey_verified)
    (by decide) (by decide) (by lit_decide)
    (Proof.Camellia.expandKeyPre_local _) (Proof.Camellia.expandKeyPost_local _)
    (Proof.Camellia.expandKeyPostOut_local _) Proof.Camellia.X86.expandKeyFrameSat_pre rfl

/-- `Spec.Camellia.ecbEncryptApi` as emitted (`Impl.Camellia.X86.Fn.ecbEncrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Fn.ecbEncrypt (Spec.Camellia.ecbContract X86.abi (Proof.Camellia.X86.specDir Impl.Camellia.X86.Dir.encrypt) 2728) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ecbEncryptApi) (W := 2728)
    { code := Impl.StackScratch.X86.withStackScratchWiped 2712 4 672 (Impl.Camellia.X86.ecb .encrypt)
      verified := Proof.Camellia.X86.ecb_framed .encrypt }
    Impl.Camellia.X86.Fn.ecbWords (ecbOut .encrypt _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.ecbDecryptApi` as emitted (`Impl.Camellia.X86.Fn.ecbDecrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Fn.ecbDecrypt (Spec.Camellia.ecbContract X86.abi (Proof.Camellia.X86.specDir Impl.Camellia.X86.Dir.decrypt) 2728) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ecbDecryptApi) (W := 2728)
    { code := Impl.StackScratch.X86.withStackScratchWiped 2712 4 672 (Impl.Camellia.X86.ecb .decrypt)
      verified := Proof.Camellia.X86.ecb_framed .decrypt }
    Impl.Camellia.X86.Fn.ecbWords (ecbOut .decrypt _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.cbcEncryptChainedApi` as emitted (`Impl.Camellia.X86.Fn.cbcEncryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Fn.cbcEncryptChained (Spec.Camellia.cbcEncryptChainedContract X86.abi 2772) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cbcEncryptChainedApi) (W := 2772)
    { code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cbcEncryptChained
      verified := Proof.Camellia.X86.Cbc.cbcEncryptChained_framed }
    Impl.Camellia.X86.Fn.modeWords (cbcEncryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.cbcDecryptChainedApi` as emitted (`Impl.Camellia.X86.Fn.cbcDecryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Fn.cbcDecryptChained (Spec.Camellia.cbcDecryptChainedContract X86.abi 2772) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cbcDecryptChainedApi) (W := 2772)
    { code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cbcDecryptChained
      verified := Proof.Camellia.X86.Cbc.cbcDecryptChained_framed }
    Impl.Camellia.X86.Fn.modeWords (cbcDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.cfbEncryptApi` as emitted (`Impl.Camellia.X86.Fn.cfbEncrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Fn.cfbEncrypt (Spec.Camellia.cfbEncryptContract X86.abi 2772) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cfbEncryptApi) (W := 2772)
    { code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbEncrypt
      verified := Proof.Camellia.X86.Fb.cfbEncrypt_framed }
    Impl.Camellia.X86.Fn.modeWords (cfbEncryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.cfbDecryptApi` as emitted (`Impl.Camellia.X86.Fn.cfbDecrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Fn.cfbDecrypt (Spec.Camellia.cfbDecryptContract X86.abi 2772) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cfbDecryptApi) (W := 2772)
    { code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbDecrypt
      verified := Proof.Camellia.X86.Fb.cfbDecrypt_framed }
    Impl.Camellia.X86.Fn.modeWords (cfbDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.cfbEncryptFinalApi` as emitted (`Impl.Camellia.X86.Fn.cfbEncryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Fn.cfbEncryptFinal (Spec.Camellia.cfbEncryptFinalContract X86.abi 2772) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cfbEncryptFinalApi) (W := 2772)
    { code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbEncryptFinal
      verified := Proof.Camellia.X86.FbFinal.cfbEncryptFinal_framed }
    Impl.Camellia.X86.Fn.modeWords (cfbEncryptFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.cfbDecryptFinalApi` as emitted (`Impl.Camellia.X86.Fn.cfbDecryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Fn.cfbDecryptFinal (Spec.Camellia.cfbDecryptFinalContract X86.abi 2772) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.cfbDecryptFinalApi) (W := 2772)
    { code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbDecryptFinal
      verified := Proof.Camellia.X86.FbFinal.cfbDecryptFinal_framed }
    Impl.Camellia.X86.Fn.modeWords (cfbDecryptFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.ofbApi` as emitted (`Impl.Camellia.X86.Fn.ofb`) meets its contract
in constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Fn.ofb (Spec.Camellia.ofbContract X86.abi 2772) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ofbApi) (W := 2772)
    { code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.ofb
      verified := Proof.Camellia.X86.Fb.ofb_framed }
    Impl.Camellia.X86.Fn.modeWords (ofbOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.ofbFinalApi` as emitted (`Impl.Camellia.X86.Fn.ofbFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Fn.ofbFinal (Spec.Camellia.ofbFinalContract X86.abi 2772) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ofbFinalApi) (W := 2772)
    { code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.ofbFinal
      verified := Proof.Camellia.X86.FbFinal.ofbFinal_framed }
    Impl.Camellia.X86.Fn.modeWords (ofbFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.ctrApi` as emitted (`Impl.Camellia.X86.Fn.ctr`) meets its contract
in constant time and returns without secret residue. -/
theorem ctr_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.Fn.ctr (Spec.Camellia.ctrContract X86.abi 2772) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ctrApi) (W := 2772)
    { code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.ctr
      verified := Proof.Camellia.X86.Ctr.ctr_framed }
    Impl.Camellia.X86.Fn.modeWords (ctrOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Camellia.ctrFinalApi` as emitted (`Impl.Camellia.X86.Fn.ctrFinal`), calling the
implementation `c` of `vg_camellia_ctr`'s code, meets its contract in constant time and returns
without secret residue. -/
theorem ctrFinal_scrubbed (c : CtrFinal.CtrImpl) :
    VerifiedScrubbed X86.target (Impl.Camellia.X86.Fn.ctrFinal c.name c.code c.words)
      (Spec.Camellia.ctrFinalContract X86.abi 2856) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ctrFinalApi) (W := 2856)
    { code := Impl.StackScratch.X86.withStackScratchWiped 60 5 8 (Impl.Camellia.X86.ctrFinal c.name c.code)
      verified := Proof.Camellia.X86.CtrFinal.ctrFinal_framed c
      spSafe := Proof.Camellia.X86.CtrFinal.ctrFinal_framed_spSafe c }
    c.words (ctrFinalOut _) c.wordsOk c.residue

/-- `spSafe` of the function as emitted, which its registration states. -/
theorem ctrFinal_spSafeF (c : CtrFinal.CtrImpl) :
    (Impl.Camellia.X86.Fn.ctrFinal c.name c.code c.words).all (fun i => !isa.writesSp i) = true :=
  scrubSel_spSafe (Proof.Camellia.X86.CtrFinal.ctrFinal_framed_spSafe c)

end VG.Proof.Camellia.X86.Scrub

namespace VG.Proof.Camellia.X86.CtrFinal.CtrImpl

open VG.X86 VG.X86.Scrub

/-- `vg_camellia_ctr`'s code in the baseline ISA, its working space in a
frame of its own: `vg_camellia_ctr_core`, with the doublewords
`vg_camellia_ctr_final` zeroes calling it
(`Impl.Camellia.X86.Fn.ctrFinalWords`). -/
def scalar : CtrImpl where
  name := "vg_camellia_ctr_core"
  code := Impl.Camellia.X86.ctrFramed
  ok := ctrFramed_sk.1
  ct := ctrFramed_sk.2.1
  nosp := ctr_nosp
  stack := Nat.le_of_eq ctr_stack
  spSafe := Code.all_of_spTest (by unfold Impl.Camellia.X86.ctrFramed; lit_decide)
  suffix := ""
  features := []
  words := Impl.Camellia.X86.Fn.ctrFinalWords
  wordsOk := by decide
  residue := by exact ⟨_, by taint_decide_ct⟩

end VG.Proof.Camellia.X86.CtrFinal.CtrImpl
