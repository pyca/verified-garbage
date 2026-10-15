module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! Relative positions of the wrapper, callee stack, nonce, and call arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

def randomStackBase (extra : Nat) (s : State) : Addr :=
  s.sp - BitVec.ofNat 64 (extra + 256)

theorem random_frameBase (extra : Nat) (s : State) :
    randomBase s = off (randomStackBase extra s) extra := by
  unfold randomBase Random.frameBytes randomStackBase off
  rw [Nat.add_comm extra 256, BitVec.ofNat_add,
    ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem random_nonceBase (extra : Nat) (s : State) :
    off (randomBase s) Random.oNonce = off (randomStackBase extra s) (extra + 200) := by
  rw [random_frameBase extra s]
  simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]
  rfl

theorem random_calleeBase (extra : Nat) (s : State) :
    randomBase s - BitVec.ofNat 64 extra = randomStackBase extra s := by
  rw [random_frameBase extra s]
  exact BitVec.add_sub_cancel _ _

theorem randomStackBase_toNat {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    (randomStackBase extra s).toNat = (s.sp).toNat - (extra + 256) := by
  have hl := h.stackLower
  have hb := (s.sp).isLt
  simp only [randomStackBase, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem randomStack_offset_toNat {extra : Nat} {s : State} (h : RandomSignABI extra s)
    {d : Nat} (hd : d ≤ extra + 256) :
    (off (randomStackBase extra s) d).toNat = (randomStackBase extra s).toNat + d := by
  have hl := h.stackLower
  have hb := (s.sp).isLt
  have hk := randomStackBase_toNat h
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end VG.Proof.Dsa.AArch64
