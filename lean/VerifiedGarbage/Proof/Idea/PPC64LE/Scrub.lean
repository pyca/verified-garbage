module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Idea.Contract
public import VerifiedGarbage.Spec.Idea.Cbc
public import VerifiedGarbage.Spec.Idea.Cfb
public import VerifiedGarbage.Spec.Idea.CfbFinal
public import VerifiedGarbage.Spec.Idea.Ofb
public import VerifiedGarbage.Spec.Idea.OfbFinal
public import VerifiedGarbage.Proof.Idea.PPC64LE.Ecb
public import VerifiedGarbage.Proof.Idea.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Idea.PPC64LE.Invert
public import VerifiedGarbage.Proof.Idea.PPC64LE.Key
public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Idea.ScrubLocal
import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit

/-!
# IDEA on PPC64LE, without secret residue

Key expansion, key inversion and ECB, which have no frames, are followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.scrubOf`), which wipes no
stack for them. The CBC, CFB64 and OFB functions zero their whole frame
themselves before they release it (`withStackScratchWiped`), and have no
frames of their own inside it, so they need only the clearing of the
volatile registers after them (`PPC64LE.Scrub.scrubWipedOf`). Their
postconditions read the memory on return only within their buffers, as on
RISC-V (`Proof/Idea/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Idea.PPC64LE.Scrub

open VG.Spec.Idea VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.Idea.ScrubLocal

/-! ## Postconditions -/
theorem len_le (ln : BitVec 64) (k : Nat) :
    ((ArgWord.int abi.ptrBits).ofRaw ln).toNat * k ≤ ln.toNat * k :=
  Nat.le_refl _

theorem len_le1 (ln : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw ln).toNat ≤ ln.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

theorem expandKeyOut (stack : Nat) : PostOut (expandKeyContract PPC64LE.abi stack) (expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show scheduleAt m₂ sc = _
    rw [scheduleAt_of hb.2]
    exact h

theorem invertKeyOut (stack : Nat) : PostOut (invertKeyContract PPC64LE.abi stack) (invertKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨inv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [invertKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show scheduleAt m₂ inv = _
    rw [scheduleAt_of hb.2]
    exact h

theorem ecbOut (stack : Nat) : PostOut (ecbContract PPC64LE.abi stack) (ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show blocksAt m₂ dt _ = _
    rw [blocksAt_of hb.2 (len_le ln 8)]
    exact h

theorem cbcEncryptOut (stack : Nat) : PostOut (cbcEncryptChainedContract PPC64LE.abi stack) (cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cbcDecryptOut (stack : Nat) : PostOut (cbcDecryptChainedContract PPC64LE.abi stack) (cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbEncryptOut (stack : Nat) : PostOut (cfbEncryptContract PPC64LE.abi stack) (cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbDecryptOut (stack : Nat) : PostOut (cfbDecryptContract PPC64LE.abi stack) (cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem ofbOut (stack : Nat) : PostOut (ofbContract PPC64LE.abi stack) (ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (cfbEncryptFinalContract PPC64LE.abi stack) (cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [bytesAt_of hb.2.2 (len_le1 ln), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (cfbDecryptFinalContract PPC64LE.abi stack) (cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [bytesAt_of hb.2.2 (len_le1 ln), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem ofbFinalOut (stack : Nat) : PostOut (ofbFinalContract PPC64LE.abi stack) (ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [bytesAt_of hb.2.2 (len_le1 ln), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

/-! ## The registrations -/

/-- `Spec.Idea.expandKeyApi`. -/
def expandKeyReg : Registration Spec.Idea.expandKeyApi PPC64LE.target :=
  scrubOf { code := Impl.Idea.PPC64LE.expandKey, verified := Proof.Idea.PPC64LE.expandKey_verified }
    0 ⟨false, false, [.r10, .r11, .r12], false, []⟩ (expandKeyOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Idea.invertKeyApi`. -/
def invertKeyReg : Registration Spec.Idea.invertKeyApi PPC64LE.target :=
  scrubOf { code := Impl.Idea.PPC64LE.invertKey, verified := Proof.Idea.PPC64LE.invertKey_verified }
    0 ⟨true, false, [.r5, .r6, .r7, .r8, .r9, .r11, .r12], false, []⟩ (invertKeyOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Idea.ecbApi`. -/
def ecbReg : Registration Spec.Idea.ecbApi PPC64LE.target :=
  scrubOf { code := Impl.Idea.PPC64LE.ecb, verified := Proof.Idea.PPC64LE.ecb_verified }
    0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩ (ecbOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Idea.cbcEncryptChainedApi`. -/
def cbcEncryptChainedReg : Registration Spec.Idea.cbcEncryptChainedApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cbcEncryptChained
      verified := Proof.Idea.PPC64LE.cbcEnc_framed Proof.Idea.PPC64LE.Modes.cbcEncryptChained_verified }
    96 .r7 8 Impl.Idea.PPC64LE.cbcEncryptChained
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (cbcEncryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.cbcDecryptChainedApi`. -/
def cbcDecryptChainedReg : Registration Spec.Idea.cbcDecryptChainedApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cbcDecryptChained
      verified := Proof.Idea.PPC64LE.cbcDec_framed Proof.Idea.PPC64LE.Modes.cbcDecryptChained_verified }
    96 .r7 8 Impl.Idea.PPC64LE.cbcDecryptChained
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (cbcDecryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.cfbEncryptApi`. -/
def cfbEncryptReg : Registration Spec.Idea.cfbEncryptApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cfbEncrypt
      verified := Proof.Idea.PPC64LE.cfbEnc_framed Proof.Idea.PPC64LE.Modes.cfbEncrypt_verified }
    96 .r7 8 Impl.Idea.PPC64LE.cfbEncrypt
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (cfbEncryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.cfbDecryptApi`. -/
def cfbDecryptReg : Registration Spec.Idea.cfbDecryptApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cfbDecrypt
      verified := Proof.Idea.PPC64LE.cfbDec_framed Proof.Idea.PPC64LE.Modes.cfbDecrypt_verified }
    96 .r7 8 Impl.Idea.PPC64LE.cfbDecrypt
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (cfbDecryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.cfbEncryptFinalApi`. -/
def cfbEncryptFinalReg : Registration Spec.Idea.cfbEncryptFinalApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cfbEncryptFinal
      verified := Proof.Idea.PPC64LE.FbFinal.cfbEncryptFinal_framed }
    96 .r7 8 Impl.Idea.PPC64LE.cfbEncryptFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (cfbEncryptFinalOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.cfbDecryptFinalApi`. -/
def cfbDecryptFinalReg : Registration Spec.Idea.cfbDecryptFinalApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cfbDecryptFinal
      verified := Proof.Idea.PPC64LE.FbFinal.cfbDecryptFinal_framed }
    96 .r7 8 Impl.Idea.PPC64LE.cfbDecryptFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (cfbDecryptFinalOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.ofbApi`. -/
def ofbReg : Registration Spec.Idea.ofbApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.ofb
      verified := Proof.Idea.PPC64LE.ofb_framed Proof.Idea.PPC64LE.Modes.ofb_verified }
    96 .r7 8 Impl.Idea.PPC64LE.ofb
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (ofbOut _) (by dsimp only; lit_decide)

/-- `Spec.Idea.ofbFinalApi`. -/
def ofbFinalReg : Registration Spec.Idea.ofbFinalApi PPC64LE.target :=
  scrubWipedOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.ofbFinal
      verified := Proof.Idea.PPC64LE.FbFinal.ofbFinal_framed }
    96 .r7 8 Impl.Idea.PPC64LE.ofbFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (ofbFinalOut _) (by dsimp only; lit_decide)

end VG.Proof.Idea.PPC64LE.Scrub
