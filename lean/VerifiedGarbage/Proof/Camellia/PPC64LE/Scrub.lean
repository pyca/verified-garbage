module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubWiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Camellia.CbcScratch
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Camellia-CBC on PPC64LE, without secret residue

CBC encryption and decryption zero their whole frame themselves before they
release it (`withStackScratchWiped`), so they need only the clearing of the
volatile registers after them (`PPC64LE.Scrub.withScrubWiped`), with no stack
wiped. Their postconditions read the memory on return only within the data
and the IV (`cbcEncOut`, `cbcDecOut`).
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

section

variable {m₁ m₂ : Mem} {p : Addr}

private theorem bytesAt_congr' {k : Nat}
    (h : ∀ i < k, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p k = Spec.Aes.bytesAt m₁ p k := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

private theorem cbcBlocksAt_congr {n : Nat}
    (h : ∀ i < 16 * n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Cbc.blocksAt m₂ p n = Spec.Cbc.blocksAt m₁ p n := by
  simp only [Spec.Cbc.blocksAt]
  refine List.map_congr_left fun i hi => bytesAt_congr' fun j hj => ?_
  have := List.mem_range.mp hi
  rw [Offset.add_add]
  exact h _ (by omega_arith)

end

/-- CBC encryption's postcondition reads the memory on return only within
the data and the IV. -/
theorem cbcEncOut (stack : Nat) :
    PostOut (Spec.Camellia.cbcEncryptChainedContract abi stack) (Spec.Camellia.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
    replace hlen := Nat.succ.inj hlen
    iterate 2
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      replace hlen := Nat.succ.inj hlen
    obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.Camellia.cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := Proof.Camellia.agree_of hb.2.2
    have hv := Proof.Camellia.agree_of hb.2.1
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.cbcChainedSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₁ r at h
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.cbcChainedSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ 64)
    intro key hk
    erw [cbcBlocksAt_congr (n := (n.setWidth 64).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr' hv]
    exact h key hk

/-- CBC decryption's postcondition reads the memory on return only within
the data and the IV. -/
theorem cbcDecOut (stack : Nat) :
    PostOut (Spec.Camellia.cbcDecryptChainedContract abi stack) (Spec.Camellia.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
    replace hlen := Nat.succ.inj hlen
    iterate 2
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      replace hlen := Nat.succ.inj hlen
    obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.Camellia.cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := Proof.Camellia.agree_of hb.2.2
    have hv := Proof.Camellia.agree_of hb.2.1
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.cbcChainedSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₁ r at h
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.cbcChainedSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ 64)
    intro key hk
    erw [cbcBlocksAt_congr (n := (n.setWidth 64).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr' hv]
    exact h key hk

def cbcEncReg : Registration Spec.Camellia.cbcEncryptChainedApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cbcEncryptChained
      verified := Proof.Camellia.PPC64LE.cbcEnc_framed Proof.Camellia.PPC64LE.Modes.cbcEncryptChained_verified }
    3408 .r8 422 Impl.Camellia.PPC64LE.cbcEncryptChained rfl (cbcEncOut _)

def cbcDecReg : Registration Spec.Camellia.cbcDecryptChainedApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cbcDecryptChained
      verified := Proof.Camellia.PPC64LE.cbcDec_framed Proof.Camellia.PPC64LE.Modes.cbcDecryptChained_verified }
    3408 .r8 422 Impl.Camellia.PPC64LE.cbcDecryptChained rfl (cbcDecOut _)

/-- Both are scrubbed: `withScrubWiped`'s side conditions hold. -/
example : cbcEncReg.residue.isSome ∧ cbcDecReg.residue.isSome := by decide

end VG.Proof.Camellia.PPC64LE.Scrub
