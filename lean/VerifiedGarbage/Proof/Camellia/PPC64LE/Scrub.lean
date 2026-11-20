module

public import VerifiedGarbage.Impl.Camellia.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Camellia.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.Verified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Camellia.CbcScratch
public import VerifiedGarbage.Proof.Camellia.PPC64LE.CtrFinal
public import VerifiedGarbage.Spec.Camellia.CtrFinal
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Camellia on PPC64LE, without secret residue

Key expansion and the ECB, CBC, CFB128, OFB and CTR functions zero their
whole frame themselves before they release it (`withStackScratchWiped`), and
have no frames of their own inside it, so they need only the clearing of the
volatile registers after them (`PPC64LE.Scrub.verifiedScrubbedWiped`), with no stack
wiped. Their postconditions read the memory on return only within their
buffers (`cbcEncOut`, …).

`vg_camellia_ctr_final` runs `vg_camellia_ctr`'s code, as
`vg_camellia_ctr_core` (`Impl.Camellia.PPC64LE.ctrCall`), inside its own
frame, so its body has a frame inside the one it wipes: the tail after it
wipes the whole stack both frames use, the 3520 bytes of its contract's
`stack`, and clears the volatile registers (`PPC64LE.Scrub.verifiedScrubbed`).
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

/-- Key expansion's postcondition reads the memory on return only within
the schedule. -/
theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Camellia.expandKeyContract abi stack) (Spec.Camellia.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Camellia.expandKeyPostOut_local _)

/-- ECB's postcondition reads the memory on return only within the data. -/
theorem ecbOut (direction : Spec.Camellia.Direction) (stack : Nat) :
    PostOut (Spec.Camellia.ecbContract abi direction stack) (Spec.Camellia.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.Camellia.ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := Proof.Camellia.agree_of hb.2
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.ecbSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64] _ _ m m₁ r at h
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.ecbSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64] _ _ m m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw, Spec.Camellia.ecbPost] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ 64)
    intro key hk
    exact (Proof.Camellia.blocksAt_congr (n := (n.setWidth 64).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega_arith)).trans (h key hk)

/-- CFB128 encryption's postcondition reads the memory on return only within
the data and the IV. -/
theorem cfbEncOut (stack : Nat) :
    PostOut (Spec.Camellia.cfbEncryptContract abi stack) (Spec.Camellia.cfbSig.retBits 64) :=
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
    simp only [Spec.Camellia.cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := Proof.Camellia.agree_of hb.2.2
    have hv := Proof.Camellia.agree_of hb.2.1
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.cfbSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₁ r at h
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.cfbSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw, Spec.Camellia.cfbEncryptPost] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ 64)
    intro key hk
    erw [cbcBlocksAt_congr (n := (n.setWidth 64).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr' hv]
    exact h key hk

/-- CFB128 decryption's postcondition reads the memory on return only within
the data and the IV. -/
theorem cfbDecOut (stack : Nat) :
    PostOut (Spec.Camellia.cfbDecryptContract abi stack) (Spec.Camellia.cfbSig.retBits 64) :=
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
    simp only [Spec.Camellia.cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := Proof.Camellia.agree_of hb.2.2
    have hv := Proof.Camellia.agree_of hb.2.1
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.cfbSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₁ r at h
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.cfbSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw, Spec.Camellia.cfbDecryptPost] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ 64)
    intro key hk
    erw [cbcBlocksAt_congr (n := (n.setWidth 64).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr' hv]
    exact h key hk

/-- OFB's postcondition reads the memory on return only within the data and
the IV. -/
theorem ofbOut (stack : Nat) :
    PostOut (Spec.Camellia.ofbContract abi stack) (Spec.Camellia.ofbSig.retBits 64) :=
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
    simp only [Spec.Camellia.ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := Proof.Camellia.agree_of hb.2.2
    have hv := Proof.Camellia.agree_of hb.2.1
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.ofbSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₁ r at h
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.ofbSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw, Spec.Camellia.ofbPost] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ 64)
    intro key hk
    erw [cbcBlocksAt_congr (n := (n.setWidth 64).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr' hv]
    exact h key hk

/-- CTR's postcondition reads the memory on return only within the data and
the counter block. -/
theorem ctrOut (stack : Nat) :
    PostOut (Spec.Camellia.ctrContract abi stack) (Spec.Camellia.ctrSig.retBits 64) :=
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
    simp only [Spec.Camellia.ctrSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := Proof.Camellia.agree_of hb.2.2
    have hv := Proof.Camellia.agree_of hb.2.1
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.ctrSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₁ r at h
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.ctrSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw, Spec.Camellia.ctrPost] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ 64)
    intro key hk
    erw [cbcBlocksAt_congr (n := (n.setWidth 64).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega_arith), bytesAt_congr' hv]
    exact h key hk

/-- CTR's of a message's last piece postcondition reads the memory on return
only within the data and the counter block. -/
theorem ctrFinalOut (stack : Nat) :
    PostOut (Spec.Camellia.ctrFinalContract abi stack) (Spec.Camellia.ctrFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, _, data, len], _ =>
      simp only [Spec.Camellia.ctrFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      have hd := Proof.Camellia.agree_of hb.2.2
      have hc := Proof.Camellia.agree_of hb.2.1
      change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.ctrFinalSig.retBits 64) → Prop)
        [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₁ r at h
      change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.ctrFinalSig.retBits 64) → Prop)
        [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw, Spec.Ctr.CryptFinal] at h ⊢
      have := Nat.mod_le len.toNat (2 ^ 64)
      intro key hk
      obtain ⟨h1, h2⟩ := h key hk
      exact ⟨(bytesAt_congr' fun i hi => hd i (by
        change i < (BitVec.setWidth 64 len : BitVec 64).toNat at hi
        rw [BitVec.toNat_setWidth] at hi; omega_arith)).trans h1, (bytesAt_congr' hc).trans h2⟩

/-- CFB128 encryption's of a partial last segment postcondition reads the
memory on return only within the data and the IV. -/
theorem cfbEncFinalOut (stack : Nat) :
    PostOut (Spec.Camellia.cfbEncryptFinalContract abi stack) (Spec.Camellia.cfbFinalSig.retBits 64) :=
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
    simp only [Spec.Camellia.cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := Proof.Camellia.agree_of hb.2.2
    have hv := Proof.Camellia.agree_of hb.2.1
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.cfbFinalSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₁ r at h
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.cfbFinalSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw, Spec.Cfb.EncryptFinal] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ 64)
    intro key hk
    erw [bytesAt_congr' (k := (n.setWidth 64).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega_using [this, hi]), bytesAt_congr' hv]
    exact h key hk

/-- CFB128 decryption's of a partial last segment postcondition reads the
memory on return only within the data and the IV. -/
theorem cfbDecFinalOut (stack : Nat) :
    PostOut (Spec.Camellia.cfbDecryptFinalContract abi stack) (Spec.Camellia.cfbFinalSig.retBits 64) :=
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
    simp only [Spec.Camellia.cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := Proof.Camellia.agree_of hb.2.2
    have hv := Proof.Camellia.agree_of hb.2.1
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.cfbFinalSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₁ r at h
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.cfbFinalSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw, Spec.Cfb.DecryptFinal] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ 64)
    intro key hk
    erw [bytesAt_congr' (k := (n.setWidth 64).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega_using [this, hi]), bytesAt_congr' hv]
    exact h key hk

/-- OFB's of a partial last block postcondition reads the memory on return
only within the data and the IV. -/
theorem ofbFinalOut (stack : Nat) :
    PostOut (Spec.Camellia.ofbFinalContract abi stack) (Spec.Camellia.ofbFinalSig.retBits 64) :=
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
    simp only [Spec.Camellia.ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := Proof.Camellia.agree_of hb.2.2
    have hv := Proof.Camellia.agree_of hb.2.1
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.ofbFinalSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₁ r at h
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Camellia.ofbFinalSig.retBits 64) → Prop)
      [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr, ArgWord.int 64] _ _ m m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw, Spec.Ofb.CryptFinal] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ 64)
    intro key hk
    erw [bytesAt_congr' (k := (n.setWidth 64).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega_using [this, hi]), bytesAt_congr' hv]
    exact h key hk

/-- `vg_camellia_cbc_encrypt_chained` as emitted
(`Impl.Camellia.PPC64LE.Fn.cbcEnc`) meets its contract in constant time and
returns without secret residue. -/
theorem cbcEnc_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Camellia.PPC64LE.Fn.cbcEnc
      (Spec.Camellia.cbcEncryptChainedContract PPC64LE.abi 3408) 0 :=
  verifiedScrubbedWiped (api := Spec.Camellia.cbcEncryptChainedApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cbcEncryptChained
      verified := Proof.Camellia.PPC64LE.cbcEnc_framed Proof.Camellia.PPC64LE.Modes.cbcEncryptChained_verified }
    3408 .r8 422 Impl.Camellia.PPC64LE.cbcEncryptChained
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18,
       .v19]⟩ rfl (cbcEncOut _) (by dsimp only; lit_decide)

/-- `vg_camellia_cbc_decrypt_chained` as emitted
(`Impl.Camellia.PPC64LE.Fn.cbcDec`) meets its contract in constant time and
returns without secret residue. -/
theorem cbcDec_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Camellia.PPC64LE.Fn.cbcDec
      (Spec.Camellia.cbcDecryptChainedContract PPC64LE.abi 3408) 0 :=
  verifiedScrubbedWiped (api := Spec.Camellia.cbcDecryptChainedApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cbcDecryptChained
      verified := Proof.Camellia.PPC64LE.cbcDec_framed Proof.Camellia.PPC64LE.Modes.cbcDecryptChained_verified }
    3408 .r8 422 Impl.Camellia.PPC64LE.cbcDecryptChained
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18,
       .v19]⟩ rfl (cbcDecOut _) (by dsimp only; lit_decide)

/-- `vg_camellia_expand_key` as emitted (`Impl.Camellia.PPC64LE.Fn.expandKey`)
meets its contract in constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Camellia.PPC64LE.Fn.expandKey
      (Spec.Camellia.expandKeyContract PPC64LE.abi 3344) 0 :=
  verifiedScrubbedWiped (api := Spec.Camellia.expandKeyApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3344 .r6 414 Impl.Camellia.PPC64LE.expandKey
      verified := Proof.Camellia.PPC64LE.expandKey_framed }
    3344 .r6 414 Impl.Camellia.PPC64LE.expandKey
    ⟨true, true, [.r4, .r6, .r7, .r8, .r9, .r11, .r12], false, []⟩ rfl (expandKeyOut _) (by dsimp only; lit_decide)

/-- `vg_camellia_ecb_encrypt` as emitted (`Impl.Camellia.PPC64LE.Fn.ecbEnc`) meets
its contract in constant time and returns without secret residue. -/
theorem ecbEnc_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Camellia.PPC64LE.Fn.ecbEnc
      (Spec.Camellia.ecbContract PPC64LE.abi (Proof.Camellia.PPC64LE.specDir Impl.Camellia.PPC64LE.Dir.encrypt) 3344) 0 :=
  verifiedScrubbedWiped (api := Spec.Camellia.ecbEncryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3344 .r7 414 (Impl.Camellia.PPC64LE.ecb .encrypt)
      verified := Proof.Camellia.PPC64LE.ecb_framed .encrypt }
    3344 .r7 414 (Impl.Camellia.PPC64LE.ecb .encrypt)
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (ecbOut .encrypt _) (by dsimp only; lit_decide)

/-- `vg_camellia_ecb_decrypt` as emitted (`Impl.Camellia.PPC64LE.Fn.ecbDec`) meets
its contract in constant time and returns without secret residue. -/
theorem ecbDec_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Camellia.PPC64LE.Fn.ecbDec
      (Spec.Camellia.ecbContract PPC64LE.abi (Proof.Camellia.PPC64LE.specDir Impl.Camellia.PPC64LE.Dir.decrypt) 3344) 0 :=
  verifiedScrubbedWiped (api := Spec.Camellia.ecbDecryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3344 .r7 414 (Impl.Camellia.PPC64LE.ecb .decrypt)
      verified := Proof.Camellia.PPC64LE.ecb_framed .decrypt }
    3344 .r7 414 (Impl.Camellia.PPC64LE.ecb .decrypt)
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩ rfl (ecbOut .decrypt _) (by dsimp only; lit_decide)

/-- `vg_camellia_cfb128_encrypt` as emitted (`Impl.Camellia.PPC64LE.Fn.cfbEnc`)
meets its contract in constant time and returns without secret residue. -/
theorem cfbEnc_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Camellia.PPC64LE.Fn.cfbEnc
      (Spec.Camellia.cfbEncryptContract PPC64LE.abi 3408) 0 :=
  verifiedScrubbedWiped (api := Spec.Camellia.cfbEncryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cfbEncrypt
      verified := Proof.Camellia.PPC64LE.cfbEnc_framed Proof.Camellia.PPC64LE.Modes.cfbEncrypt_verified }
    3408 .r8 422 Impl.Camellia.PPC64LE.cfbEncrypt
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18,
       .v19]⟩ rfl (cfbEncOut _) (by dsimp only; lit_decide)

/-- `vg_camellia_cfb128_decrypt` as emitted (`Impl.Camellia.PPC64LE.Fn.cfbDec`)
meets its contract in constant time and returns without secret residue. -/
theorem cfbDec_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Camellia.PPC64LE.Fn.cfbDec
      (Spec.Camellia.cfbDecryptContract PPC64LE.abi 3408) 0 :=
  verifiedScrubbedWiped (api := Spec.Camellia.cfbDecryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cfbDecrypt
      verified := Proof.Camellia.PPC64LE.cfbDec_framed Proof.Camellia.PPC64LE.Modes.cfbDecrypt_verified }
    3408 .r8 422 Impl.Camellia.PPC64LE.cfbDecrypt
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18,
       .v19]⟩ rfl (cfbDecOut _) (by dsimp only; lit_decide)

/-- `vg_camellia_cfb128_encrypt_final` as emitted
(`Impl.Camellia.PPC64LE.Fn.cfbEncFinal`) meets its contract in constant time
and returns without secret residue. -/
theorem cfbEncFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Camellia.PPC64LE.Fn.cfbEncFinal
      (Spec.Camellia.cfbEncryptFinalContract PPC64LE.abi 3408) 0 :=
  verifiedScrubbedWiped (api := Spec.Camellia.cfbEncryptFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cfbEncryptFinal
      verified := Proof.Camellia.PPC64LE.FbFinal.cfbEncryptFinal_framed }
    3408 .r8 422 Impl.Camellia.PPC64LE.cfbEncryptFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18,
       .v19]⟩ rfl (cfbEncFinalOut _) (by dsimp only; lit_decide)

/-- `vg_camellia_cfb128_decrypt_final` as emitted
(`Impl.Camellia.PPC64LE.Fn.cfbDecFinal`) meets its contract in constant time
and returns without secret residue. -/
theorem cfbDecFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Camellia.PPC64LE.Fn.cfbDecFinal
      (Spec.Camellia.cfbDecryptFinalContract PPC64LE.abi 3408) 0 :=
  verifiedScrubbedWiped (api := Spec.Camellia.cfbDecryptFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cfbDecryptFinal
      verified := Proof.Camellia.PPC64LE.FbFinal.cfbDecryptFinal_framed }
    3408 .r8 422 Impl.Camellia.PPC64LE.cfbDecryptFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18,
       .v19]⟩ rfl (cfbDecFinalOut _) (by dsimp only; lit_decide)

/-- `vg_camellia_ofb` as emitted (`Impl.Camellia.PPC64LE.Fn.ofb`) meets its
contract in constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Camellia.PPC64LE.Fn.ofb
      (Spec.Camellia.ofbContract PPC64LE.abi 3408) 0 :=
  verifiedScrubbedWiped (api := Spec.Camellia.ofbApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.ofb
      verified := Proof.Camellia.PPC64LE.ofb_framed Proof.Camellia.PPC64LE.Modes.ofb_verified }
    3408 .r8 422 Impl.Camellia.PPC64LE.ofb
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18,
       .v19]⟩ rfl (ofbOut _) (by dsimp only; lit_decide)

/-- `vg_camellia_ofb_final` as emitted (`Impl.Camellia.PPC64LE.Fn.ofbFinal`) meets
its contract in constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Camellia.PPC64LE.Fn.ofbFinal
      (Spec.Camellia.ofbFinalContract PPC64LE.abi 3408) 0 :=
  verifiedScrubbedWiped (api := Spec.Camellia.ofbFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.ofbFinal
      verified := Proof.Camellia.PPC64LE.FbFinal.ofbFinal_framed }
    3408 .r8 422 Impl.Camellia.PPC64LE.ofbFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18,
       .v19]⟩ rfl (ofbFinalOut _) (by dsimp only; lit_decide)

/-- `vg_camellia_ctr` as emitted (`Impl.Camellia.PPC64LE.Fn.ctr`) meets its
contract in constant time and returns without secret residue. -/
theorem ctr_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Camellia.PPC64LE.Fn.ctr
      (Spec.Camellia.ctrContract PPC64LE.abi 3408) 0 :=
  verifiedScrubbedWiped (api := Spec.Camellia.ctrApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.ctr
      verified := Proof.Camellia.PPC64LE.ctr_framed Proof.Camellia.PPC64LE.Modes.ctr_verified }
    3408 .r8 422 Impl.Camellia.PPC64LE.ctr
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18,
       .v19]⟩ rfl (ctrOut _) (by dsimp only; lit_decide)

/-- `vg_camellia_ctr_final` as emitted (`Impl.Camellia.PPC64LE.Fn.ctrFinal`) meets
its contract in constant time and returns without secret residue. -/
theorem ctrFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Camellia.PPC64LE.Fn.ctrFinal
      (Spec.Camellia.ctrFinalContract PPC64LE.abi 3520) 0 :=
  verifiedScrubbed (api := Spec.Camellia.ctrFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 112 .r8 10 Impl.Camellia.PPC64LE.ctrFinal
      verified := Proof.Camellia.PPC64LE.CtrFinal.ctrFinal_framed }
    3520 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18,
       .v19]⟩
    (ctrFinalOut _) (by dsimp only; lit_decide)

end VG.Proof.Camellia.PPC64LE.Scrub
