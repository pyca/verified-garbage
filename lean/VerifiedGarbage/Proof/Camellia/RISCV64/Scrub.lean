module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Camellia.Contract
public import VerifiedGarbage.Spec.Camellia.Cbc
public import VerifiedGarbage.Spec.Camellia.Cfb
public import VerifiedGarbage.Spec.Camellia.CfbFinal
public import VerifiedGarbage.Spec.Camellia.Ofb
public import VerifiedGarbage.Spec.Camellia.OfbFinal
public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Spec.Camellia.CtrFinal
public import VerifiedGarbage.Proof.Camellia.RISCV64.CtrFinal
public import VerifiedGarbage.Proof.Camellia.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.Camellia.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Camellia.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Camellia.RISCV64.Verified
public import VerifiedGarbage.Proof.Camellia.ScrubLocal
import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Camellia.CbcScratch
import VerifiedGarbage.Proof.Camellia.FbScratch
import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Camellia.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Camellia.RISCV64.Lit
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit

meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Camellia.Contract
meta import VerifiedGarbage.Spec.Camellia.Cbc
meta import VerifiedGarbage.Spec.Camellia.Cfb
meta import VerifiedGarbage.Spec.Camellia.CfbFinal
meta import VerifiedGarbage.Spec.Camellia.Ofb
meta import VerifiedGarbage.Spec.Camellia.OfbFinal
meta import VerifiedGarbage.Spec.Camellia.Ctr
meta import VerifiedGarbage.Spec.Camellia.CtrFinal
meta import VerifiedGarbage.Proof.Camellia.RISCV64.CtrFinal
meta import VerifiedGarbage.Proof.Camellia.RISCV64.FbFinalVerified
meta import VerifiedGarbage.Proof.Camellia.RISCV64.KeyVerified
meta import VerifiedGarbage.Proof.Camellia.RISCV64.ModesVerified
meta import VerifiedGarbage.Proof.Camellia.RISCV64.Verified
meta import VerifiedGarbage.Proof.Camellia.ScrubLocal
meta import VerifiedGarbage.Proof.Camellia.Scratch
meta import VerifiedGarbage.Proof.Camellia.CbcScratch
meta import VerifiedGarbage.Proof.Camellia.FbScratch
meta import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Camellia.RISCV64.FbFinalLit
meta import VerifiedGarbage.Proof.Camellia.RISCV64.Lit
meta import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
/-!
# Camellia on RISC-V, without secret residue

Each function, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within their buffers (`RISCV64.Scrub.PostOut`), as on x86-64
(`Proof/Camellia/X86_64/Scrub.lean`).

ECB's functions instead clear only the runs of doublewords that the residue
analysis (`RISCV64.rtaint`) finds may differ between two runs
(`RISCV64.Scrub.withScrubSel`, `scrubSel_noResidue`). Their code wipes most of
its own scratch space, which leaves few such doublewords, or none.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64.Scrub

open VG.Spec.Camellia VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Camellia.ScrubLocal

/-! ## Postconditions -/
theorem len_le (x : BitVec 64) (k : Nat) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.le_refl _

theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

theorem expandKeyOut : PostOut (expandKeyContract RISCV64.abi 3216) (expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Camellia.expandKeyPostOut_local _)

theorem ecbOut (d : Direction) (stack : Nat) : PostOut (ecbContract RISCV64.abi d stack) (ecbSig.retBits 64) :=
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
    PostOut (cbcEncryptChainedContract RISCV64.abi stack) (cbcChainedSig.retBits 64) :=
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
    PostOut (cbcDecryptChainedContract RISCV64.abi stack) (cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptOut (stack : Nat) : PostOut (cfbEncryptContract RISCV64.abi stack) (cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptOut (stack : Nat) : PostOut (cfbDecryptContract RISCV64.abi stack) (cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbOut (stack : Nat) : PostOut (ofbContract RISCV64.abi stack) (ofbSig.retBits 64) :=
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
    PostOut (cfbEncryptFinalContract RISCV64.abi stack) (cfbFinalSig.retBits 64) :=
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
    PostOut (cfbDecryptFinalContract RISCV64.abi stack) (cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbFinalOut (stack : Nat) : PostOut (ofbFinalContract RISCV64.abi stack) (ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ctrOut (stack : Nat) : PostOut (ctrContract RISCV64.abi stack) (ctrSig.retBits 64) :=
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
    PostOut (ctrFinalContract RISCV64.abi stack) (ctrFinalSig.retBits 64) :=
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

/-- `Spec.Camellia.ecbEncryptApi`. -/
def ecbEncryptReg : Registration Spec.Camellia.ecbEncryptApi RISCV64.target :=
  withScrubSel { code := Impl.StackScratch.RISCV64.withStackScratchWiped 3200 .a4 400 (Impl.Camellia.RISCV64.ecb .encrypt), verified := Proof.Camellia.RISCV64.ecb_framed .encrypt } []
    (ecbOut .encrypt _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (ecbOut .encrypt _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 3200 .a4 400 (Impl.Camellia.RISCV64.ecb .encrypt)) 3200 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.Camellia.ecbDecryptApi`. -/
def ecbDecryptReg : Registration Spec.Camellia.ecbDecryptApi RISCV64.target :=
  withScrubSel { code := Impl.StackScratch.RISCV64.withStackScratchWiped 3200 .a4 400 (Impl.Camellia.RISCV64.ecb .decrypt), verified := Proof.Camellia.RISCV64.ecb_framed .decrypt } []
    (ecbOut .decrypt _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (ecbOut .decrypt _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 3200 .a4 400 (Impl.Camellia.RISCV64.ecb .decrypt)) 3200 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.Camellia.cbcEncryptChainedApi`. -/
def cbcEncryptChainedReg : Registration Spec.Camellia.cbcEncryptChainedApi RISCV64.target :=
  withScrub { code := Impl.Camellia.RISCV64.cbcEncryptChained, verified := Proof.Camellia.RISCV64.Modes.cbcEncryptChained_verified }
    (cbcEncryptOut _)

/-- `Spec.Camellia.cbcDecryptChainedApi`. -/
def cbcDecryptChainedReg : Registration Spec.Camellia.cbcDecryptChainedApi RISCV64.target :=
  withScrub { code := Impl.Camellia.RISCV64.cbcDecryptChained, verified := Proof.Camellia.RISCV64.Modes.cbcDecryptChained_verified }
    (cbcDecryptOut _)

/-- `Spec.Camellia.cfbEncryptApi`. -/
def cfbEncryptReg : Registration Spec.Camellia.cfbEncryptApi RISCV64.target :=
  withScrub { code := Impl.Camellia.RISCV64.cfbEncrypt, verified := Proof.Camellia.RISCV64.Modes.cfbEncrypt_verified }
    (cfbEncryptOut _)

/-- `Spec.Camellia.cfbDecryptApi`. -/
def cfbDecryptReg : Registration Spec.Camellia.cfbDecryptApi RISCV64.target :=
  withScrub { code := Impl.Camellia.RISCV64.cfbDecrypt, verified := Proof.Camellia.RISCV64.Modes.cfbDecrypt_verified }
    (cfbDecryptOut _)

/-- `Spec.Camellia.cfbEncryptFinalApi`. -/
def cfbEncryptFinalReg : Registration Spec.Camellia.cfbEncryptFinalApi RISCV64.target :=
  withScrub { code := Impl.Camellia.RISCV64.cfbEncryptFinal, verified := Proof.Camellia.RISCV64.Modes.cfbEncryptFinal_verified }
    (cfbEncryptFinalOut _)

/-- `Spec.Camellia.cfbDecryptFinalApi`. -/
def cfbDecryptFinalReg : Registration Spec.Camellia.cfbDecryptFinalApi RISCV64.target :=
  withScrub { code := Impl.Camellia.RISCV64.cfbDecryptFinal, verified := Proof.Camellia.RISCV64.Modes.cfbDecryptFinal_verified }
    (cfbDecryptFinalOut _)

/-- `Spec.Camellia.ctrApi`. -/
def ctrReg : Registration Spec.Camellia.ctrApi RISCV64.target :=
  withScrub { code := Impl.Camellia.RISCV64.ctr, verified := Proof.Camellia.RISCV64.Modes.ctr_verified }
    (ctrOut _)

/-- `Spec.Camellia.ofbApi`. -/
def ofbReg : Registration Spec.Camellia.ofbApi RISCV64.target :=
  withScrub { code := Impl.Camellia.RISCV64.ofb, verified := Proof.Camellia.RISCV64.Modes.ofb_verified }
    (ofbOut _)

/-- `Spec.Camellia.ofbFinalApi`. -/
def ofbFinalReg : Registration Spec.Camellia.ofbFinalApi RISCV64.target :=
  withScrub { code := Impl.Camellia.RISCV64.ofbFinal, verified := Proof.Camellia.RISCV64.Modes.ofbFinal_verified }
    (ofbFinalOut _)

end VG.Proof.Camellia.RISCV64.Scrub
