module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
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

/-!
# Camellia on x86 (32-bit), without secret residue

Key expansion and Camellia's ECB, CBC, CFB128, OFB and CTR functions, and the
final pieces of CFB128, OFB and CTR, run with their working space in a frame
on the stack (`withStackScratchWiped`), and are scrubbed with
`X86.Scrub.scrubFOf`, which zeroes the stack their contracts reserve below
`esp` (their frames and the calls of `vg_camellia_crypt_prepared` in them)
and clears the registers a callee may change. What the scrub needs of the
code is one Boolean (`X86.Scrub.scrubFSide`), proved by evaluating the code
once (`lit_decide`). `vg_camellia_ctr_final` calls `vg_camellia_ctr`'s code
as an internal function of its own, `vg_camellia_ctr_core`. Their
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

theorem expandKeyOut (stack : Nat) : PostOut (expandKeyContract X86.abi stack) (expandKeySig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Camellia.expandKeyPostOut_local _)

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

/-! ## The registrations -/

/-- `Spec.Camellia.expandKeyApi`. -/
def expandKeyReg : Registration Spec.Camellia.expandKeyApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 2708 3 672 Impl.Camellia.X86.expandKey
      verified := Proof.Camellia.X86.expandKey_framed }
    (expandKeyOut _)

/-- `Spec.Camellia.ecbEncryptApi`. -/
def ecbEncryptReg : Registration Spec.Camellia.ecbEncryptApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 2712 4 672 (Impl.Camellia.X86.ecb .encrypt)
      verified := Proof.Camellia.X86.ecb_framed .encrypt }
    (ecbOut .encrypt _)

/-- `Spec.Camellia.ecbDecryptApi`. -/
def ecbDecryptReg : Registration Spec.Camellia.ecbDecryptApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 2712 4 672 (Impl.Camellia.X86.ecb .decrypt)
      verified := Proof.Camellia.X86.ecb_framed .decrypt }
    (ecbOut .decrypt _)

/-- `Spec.Camellia.cbcEncryptChainedApi`. -/
def cbcEncryptChainedReg : Registration Spec.Camellia.cbcEncryptChainedApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cbcEncryptChained
      verified := Proof.Camellia.X86.Cbc.cbcEncryptChained_framed }
    (cbcEncryptOut _)

/-- `Spec.Camellia.cbcDecryptChainedApi`. -/
def cbcDecryptChainedReg : Registration Spec.Camellia.cbcDecryptChainedApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cbcDecryptChained
      verified := Proof.Camellia.X86.Cbc.cbcDecryptChained_framed }
    (cbcDecryptOut _)

/-- `Spec.Camellia.cfbEncryptApi`. -/
def cfbEncryptReg : Registration Spec.Camellia.cfbEncryptApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbEncrypt
      verified := Proof.Camellia.X86.Fb.cfbEncrypt_framed }
    (cfbEncryptOut _)

/-- `Spec.Camellia.cfbDecryptApi`. -/
def cfbDecryptReg : Registration Spec.Camellia.cfbDecryptApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbDecrypt
      verified := Proof.Camellia.X86.Fb.cfbDecrypt_framed }
    (cfbDecryptOut _)

/-- `Spec.Camellia.cfbEncryptFinalApi`. -/
def cfbEncryptFinalReg : Registration Spec.Camellia.cfbEncryptFinalApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbEncryptFinal
      verified := Proof.Camellia.X86.FbFinal.cfbEncryptFinal_framed }
    (cfbEncryptFinalOut _)

/-- `Spec.Camellia.cfbDecryptFinalApi`. -/
def cfbDecryptFinalReg : Registration Spec.Camellia.cfbDecryptFinalApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbDecryptFinal
      verified := Proof.Camellia.X86.FbFinal.cfbDecryptFinal_framed }
    (cfbDecryptFinalOut _)

/-- `Spec.Camellia.ofbApi`. -/
def ofbReg : Registration Spec.Camellia.ofbApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.ofb
      verified := Proof.Camellia.X86.Fb.ofb_framed }
    (ofbOut _)

/-- `Spec.Camellia.ofbFinalApi`. -/
def ofbFinalReg : Registration Spec.Camellia.ofbFinalApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.ofbFinal
      verified := Proof.Camellia.X86.FbFinal.ofbFinal_framed }
    (ofbFinalOut _)

/-- `Spec.Camellia.ctrApi`. -/
def ctrReg : Registration Spec.Camellia.ctrApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.ctr
      verified := Proof.Camellia.X86.Ctr.ctr_framed }
    (ctrOut _)

/-- `Spec.Camellia.ctrFinalApi`. -/
def ctrFinalReg : Registration Spec.Camellia.ctrFinalApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 60 5 8 Impl.Camellia.X86.ctrFinal
      verified := Proof.Camellia.X86.CtrFinal.ctrFinal_framed
      spSafe := Proof.Camellia.X86.CtrFinal.ctrFinal_framed_spSafe }
    (ctrFinalOut _)

end VG.Proof.Camellia.X86.Scrub
