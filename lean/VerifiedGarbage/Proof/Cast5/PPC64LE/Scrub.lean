module

public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Spec.Cast5.Cbc
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Cast5.CfbFinal
public import VerifiedGarbage.Spec.Cast5.OfbFinal
public import VerifiedGarbage.Proof.Framework.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubWiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Proof.Cast5.CfbFinal
public import VerifiedGarbage.Proof.Cast5.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Cast5.PPC64LE.EcbVerified
public import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalVerified
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Cast5.ModeScratch
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# CAST5 on PPC64LE, without secret residue

Key expansion and ECB, which have no frames, are followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.withScrub`), which wipes no
stack for them. The CBC, CFB64 and OFB functions zero their whole frame
themselves before they release it (`withStackScratchWiped`), and have no
frames of their own inside it, so they need only the clearing of the volatile
registers they write after them (`PPC64LE.Scrub.withScrubWiped`). Their
postconditions read the memory on return only within their buffers, as
x86-64's proofs show (`Proof/Cast5/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.Aes.ScrubLocal

/-! ## Locality -/

section

variable {m₁ m₂ : Mem} {p : Addr} {L : Nat}

private theorem blocksAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n * 8 ≤ L) :
    Spec.Cast5.blocksAt m₂ p n = Spec.Cast5.blocksAt m₁ p n := by
  simp only [Spec.Cast5.blocksAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  apply Vector.ext
  intro j hj
  simp only [Spec.Cast5.blockAt, Vector.getElem_ofFn]
  rw [VG.Offset.add_add]
  exact agree_le h hn _ (by omega_using [this, hj])

private theorem cbcBlocksAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n * 8 ≤ L) :
    Spec.Cast5.cbcBlocksAt m₂ p n = Spec.Cast5.cbcBlocksAt m₁ p n := by
  simp only [Spec.Cast5.cbcBlocksAt, blocksAt_of0 h hn]

private theorem scheduleAt_of (h : ∀ a, Region.Contains ⟨p, 128⟩ a 1 → m₁ a = m₂ a) :
    Spec.Cast5.scheduleAt m₂ p = Spec.Cast5.scheduleAt m₁ p :=
  Proof.Cast5.scheduleAt_congr (agree_le h (Nat.le_refl _))

end

/-- The data's length, under the tables' ABI. -/
theorem lenC (x : BitVec 64) (k : Nat) :
    ((ArgWord.int (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts).ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.le_refl _

theorem len1C (x : BitVec 64) :
    ((ArgWord.int (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts).ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Cast5.expandKeyContract (PPC64LE.abi.withConsts Impl.Cast5.keyConsts) stack)
      (Spec.Cast5.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [k, kl, sch, sc], _ =>
      simp only [Spec.Cast5.expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show Spec.Cast5.scheduleAt m₂ sch = _
      rw [scheduleAt_of hb.2.1]
      exact h

theorem ecbOut (d : Spec.Cast5.Direction) (stack : Nat) :
    PostOut (Spec.Cast5.ecbContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) d stack)
      (Spec.Cast5.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, dt, ln, sc], _ =>
      simp only [Spec.Cast5.ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key → Spec.Cast5.blocksAt m₂ dt _ = _
      intro key hk
      rw [blocksAt_of0 hb.2.1 (lenC ln 8)]
      exact h key hk

theorem cbcEncryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cbcEncryptChainedContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
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
    PostOut (Spec.Cast5.cbcDecryptChainedContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
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
    PostOut (Spec.Cast5.cfbEncryptContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
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
    PostOut (Spec.Cast5.cfbDecryptContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
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
    PostOut (Spec.Cast5.ofbContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.ofbSig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
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
    PostOut (Spec.Cast5.cfbEncryptFinalContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
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
    PostOut (Spec.Cast5.cfbDecryptFinalContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
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
    PostOut (Spec.Cast5.ofbFinalContract (PPC64LE.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
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
def expandKeyReg : Registration Spec.Cast5.expandKeyApi PPC64LE.target :=
  withScrub { code := Impl.Cast5.PPC64LE.expandKey, verified := Proof.Cast5.PPC64LE.expandKey_verified } (expandKeyOut _)

/-- `Spec.Cast5.ecbEncryptApi`. -/
def ecbEncryptReg : Registration Spec.Cast5.ecbEncryptApi PPC64LE.target :=
  withScrub { code := Impl.Cast5.PPC64LE.ecbEncrypt, verified := Proof.Cast5.ecbEncrypt_keyed Proof.Cast5.PPC64LE.ecbEncrypt_verified } (ecbOut .encrypt _)

/-- `Spec.Cast5.ecbDecryptApi`. -/
def ecbDecryptReg : Registration Spec.Cast5.ecbDecryptApi PPC64LE.target :=
  withScrub { code := Impl.Cast5.PPC64LE.ecbDecrypt, verified := Proof.Cast5.ecbDecrypt_keyed Proof.Cast5.PPC64LE.ecbDecrypt_verified } (ecbOut .decrypt _)

/-- `Spec.Cast5.cbcEncryptChainedApi`. -/
def cbcEncryptChainedReg : Registration Spec.Cast5.cbcEncryptChainedApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cbcEncryptChained
      verified := Proof.Cast5.cbcEncryptChained_keyed Proof.Cast5.PPC64LE.Modes.cbcEncryptChained_framed }
    208 .r8 22 Impl.Cast5.PPC64LE.cbcEncryptChained rfl (cbcEncryptOut _)

/-- `Spec.Cast5.cbcDecryptChainedApi`. -/
def cbcDecryptChainedReg : Registration Spec.Cast5.cbcDecryptChainedApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cbcDecryptChained
      verified := Proof.Cast5.cbcDecryptChained_keyed Proof.Cast5.PPC64LE.Modes.cbcDecryptChained_framed }
    208 .r8 22 Impl.Cast5.PPC64LE.cbcDecryptChained rfl (cbcDecryptOut _)

/-- `Spec.Cast5.cfbEncryptApi`. -/
def cfbEncryptReg : Registration Spec.Cast5.cfbEncryptApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbEncrypt
      verified := Proof.Cast5.cfbEncrypt_keyed Proof.Cast5.PPC64LE.Modes.cfbEncrypt_framed }
    208 .r8 22 Impl.Cast5.PPC64LE.cfbEncrypt rfl (cfbEncryptOut _)

/-- `Spec.Cast5.cfbDecryptApi`. -/
def cfbDecryptReg : Registration Spec.Cast5.cfbDecryptApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbDecrypt
      verified := Proof.Cast5.cfbDecrypt_keyed Proof.Cast5.PPC64LE.Modes.cfbDecrypt_framed }
    208 .r8 22 Impl.Cast5.PPC64LE.cfbDecrypt rfl (cfbDecryptOut _)

/-- `Spec.Cast5.cfbEncryptFinalApi`. -/
def cfbEncryptFinalReg : Registration Spec.Cast5.cfbEncryptFinalApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbEncryptFinal
      verified := Proof.Cast5.cfbEncryptFinal_keyed Proof.Cast5.PPC64LE.FbFinal.cfbEncryptFinal_framed }
    208 .r8 22 Impl.Cast5.PPC64LE.cfbEncryptFinal rfl (cfbEncryptFinalOut _)

/-- `Spec.Cast5.cfbDecryptFinalApi`. -/
def cfbDecryptFinalReg : Registration Spec.Cast5.cfbDecryptFinalApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbDecryptFinal
      verified := Proof.Cast5.cfbDecryptFinal_keyed Proof.Cast5.PPC64LE.FbFinal.cfbDecryptFinal_framed }
    208 .r8 22 Impl.Cast5.PPC64LE.cfbDecryptFinal rfl (cfbDecryptFinalOut _)

/-- `Spec.Cast5.ofbApi`. -/
def ofbReg : Registration Spec.Cast5.ofbApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.ofb
      verified := Proof.Cast5.ofb_keyed Proof.Cast5.PPC64LE.Modes.ofb_framed }
    208 .r8 22 Impl.Cast5.PPC64LE.ofb rfl (ofbOut _)

/-- `Spec.Cast5.ofbFinalApi`. -/
def ofbFinalReg : Registration Spec.Cast5.ofbFinalApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.ofbFinal
      verified := Proof.Cast5.ofbFinal_keyed Proof.Cast5.PPC64LE.FbFinal.ofbFinal_framed }
    208 .r8 22 Impl.Cast5.PPC64LE.ofbFinal rfl (ofbFinalOut _)

/-- These are scrubbed: the side conditions of `withScrub` and `withScrubWiped` hold.
Key expansion's code is too long for `decide` to walk here; the emitter, which
refuses a function off `ci/residue_allowlist.txt` without a proof, checks it. -/
example : ecbEncryptReg.residue.isSome ∧
    ecbDecryptReg.residue.isSome ∧
    cbcEncryptChainedReg.residue.isSome ∧
    cbcDecryptChainedReg.residue.isSome ∧
    cfbEncryptReg.residue.isSome ∧
    cfbDecryptReg.residue.isSome ∧
    cfbEncryptFinalReg.residue.isSome ∧
    cfbDecryptFinalReg.residue.isSome ∧
    ofbReg.residue.isSome ∧
    ofbFinalReg.residue.isSome := by decide

end VG.Proof.Cast5.PPC64LE.Scrub
