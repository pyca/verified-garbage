module

public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Spec.Cast5.Cbc
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Cast5.CfbFinal
public import VerifiedGarbage.Spec.Cast5.OfbFinal
public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Proof.Cast5.CfbFinal
public import VerifiedGarbage.Proof.Cast5.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Cast5.RISCV64.EcbVerified
public import VerifiedGarbage.Proof.Cast5.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Cast5.RISCV64.FbFinalVerified
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Cast5.ScrubLocal

/-!
# CAST5 on RISC-V, without secret residue

The eleven CAST5 functions, each followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.scrubOf`), which clears the caller-saved registers and the
stack its frames used: none for key expansion and ECB, whose working space
is their caller's `scratch`, and the 128-byte frame of the modes, which holds
the chaining block. Their postconditions read the memory on return only
within the buffers (`RISCV64.Scrub.PostOut`): the schedule, the data and the
chaining block, as on x86-64 (`Proof/Cast5/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Aes.ScrubLocal VG.Proof.Cast5.ScrubLocal

/-- The data's length, under the tables' ABI. -/
theorem lenC (x : BitVec 64) (k : Nat) :
    ((ArgWord.int (RISCV64.abi.withConsts Impl.Cast5.ecbConsts).ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.le_refl _

theorem len1C (x : BitVec 64) :
    ((ArgWord.int (RISCV64.abi.withConsts Impl.Cast5.ecbConsts).ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Cast5.expandKeyContract (RISCV64.abi.withConsts Impl.Cast5.keyConsts) stack)
      (Spec.Cast5.expandKeySig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [k, kl, sch, sc], _ =>
      simp only [Spec.Cast5.expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show Spec.Cast5.scheduleAt m₂ sch = _
      rw [scheduleAt_of hb.2.1]
      exact h

theorem ecbOut (d : Spec.Cast5.Direction) (stack : Nat) :
    PostOut (Spec.Cast5.ecbContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) d stack)
      (Spec.Cast5.ecbSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, dt, ln, sc], _ =>
      simp only [Spec.Cast5.ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key → Spec.Cast5.blocksAt m₂ dt _ = _
      intro key hk
      rw [blocksAt_of0 hb.2.1 (lenC ln 8)]
      exact h key hk

theorem cbcEncryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cbcEncryptChainedContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cbcChainedSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cbcDecryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cbcDecryptChainedContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cbcChainedSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbEncryptContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbDecryptContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbOut (stack : Nat) :
    PostOut (Spec.Cast5.ofbContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.ofbSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbEncryptFinalContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbFinalSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1C ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbDecryptFinalContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbFinalSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1C ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.ofbFinalContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.ofbFinalSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1C ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## The registrations -/

/-- `Spec.Cast5.expandKeyApi`. -/
def expandKeyReg : Registration Spec.Cast5.expandKeyApi RISCV64.target :=
  scrubOf { code := Impl.Cast5.RISCV64.expandKey, verified := Proof.Cast5.RISCV64.expandKey_verified }
    (expandKeyOut _)

/-- `Spec.Cast5.ecbEncryptApi`. -/
def ecbEncryptReg : Registration Spec.Cast5.ecbEncryptApi RISCV64.target :=
  scrubOf { code := Impl.Cast5.RISCV64.ecbEncrypt, verified := Proof.Cast5.ecbEncrypt_keyed Proof.Cast5.RISCV64.ecbEncrypt_verified }
    (ecbOut .encrypt _)

/-- `Spec.Cast5.ecbDecryptApi`. -/
def ecbDecryptReg : Registration Spec.Cast5.ecbDecryptApi RISCV64.target :=
  scrubOf { code := Impl.Cast5.RISCV64.ecbDecrypt, verified := Proof.Cast5.ecbDecrypt_keyed Proof.Cast5.RISCV64.ecbDecrypt_verified }
    (ecbOut .decrypt _)

/-- `Spec.Cast5.cbcEncryptChainedApi`. -/
def cbcEncryptChainedReg : Registration Spec.Cast5.cbcEncryptChainedApi RISCV64.target :=
  scrubOf { code := Impl.Cast5.RISCV64.cbcEncryptChained, verified := Proof.Cast5.cbcEncryptChained_keyed Proof.Cast5.RISCV64.Modes.cbcEncryptChained_verified }
    (cbcEncryptOut _)

/-- `Spec.Cast5.cbcDecryptChainedApi`. -/
def cbcDecryptChainedReg : Registration Spec.Cast5.cbcDecryptChainedApi RISCV64.target :=
  scrubOf { code := Impl.Cast5.RISCV64.cbcDecryptChained, verified := Proof.Cast5.cbcDecryptChained_keyed Proof.Cast5.RISCV64.Modes.cbcDecryptChained_verified }
    (cbcDecryptOut _)

/-- `Spec.Cast5.cfbEncryptApi`. -/
def cfbEncryptReg : Registration Spec.Cast5.cfbEncryptApi RISCV64.target :=
  scrubOf { code := Impl.Cast5.RISCV64.cfbEncrypt, verified := Proof.Cast5.cfbEncrypt_keyed Proof.Cast5.RISCV64.Modes.cfbEncrypt_verified }
    (cfbEncryptOut _)

/-- `Spec.Cast5.cfbDecryptApi`. -/
def cfbDecryptReg : Registration Spec.Cast5.cfbDecryptApi RISCV64.target :=
  scrubOf { code := Impl.Cast5.RISCV64.cfbDecrypt, verified := Proof.Cast5.cfbDecrypt_keyed Proof.Cast5.RISCV64.Modes.cfbDecrypt_verified }
    (cfbDecryptOut _)

/-- `Spec.Cast5.cfbEncryptFinalApi`. -/
def cfbEncryptFinalReg : Registration Spec.Cast5.cfbEncryptFinalApi RISCV64.target :=
  scrubOf { code := Impl.Cast5.RISCV64.cfbEncryptFinal, verified := Proof.Cast5.cfbEncryptFinal_keyed Proof.Cast5.RISCV64.Modes.cfbEncryptFinal_verified }
    (cfbEncryptFinalOut _)

/-- `Spec.Cast5.cfbDecryptFinalApi`. -/
def cfbDecryptFinalReg : Registration Spec.Cast5.cfbDecryptFinalApi RISCV64.target :=
  scrubOf { code := Impl.Cast5.RISCV64.cfbDecryptFinal, verified := Proof.Cast5.cfbDecryptFinal_keyed Proof.Cast5.RISCV64.Modes.cfbDecryptFinal_verified }
    (cfbDecryptFinalOut _)

/-- `Spec.Cast5.ofbApi`. -/
def ofbReg : Registration Spec.Cast5.ofbApi RISCV64.target :=
  scrubOf { code := Impl.Cast5.RISCV64.ofb, verified := Proof.Cast5.ofb_keyed Proof.Cast5.RISCV64.Modes.ofb_verified }
    (ofbOut _)

/-- `Spec.Cast5.ofbFinalApi`. -/
def ofbFinalReg : Registration Spec.Cast5.ofbFinalApi RISCV64.target :=
  scrubOf { code := Impl.Cast5.RISCV64.ofbFinal, verified := Proof.Cast5.ofbFinal_keyed Proof.Cast5.RISCV64.Modes.ofbFinal_verified }
    (ofbFinalOut _)

end VG.Proof.Cast5.RISCV64.Scrub
