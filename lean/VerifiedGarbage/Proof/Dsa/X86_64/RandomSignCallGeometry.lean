module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlKem.Arith

/-! Relative positions of the wrapper, callee stack, nonce, and call arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

def randomStackBase (extra : Nat) (s : State) : Addr :=
  s.gpr .rsp - BitVec.ofNat 64 (extra + 256)

theorem random_callBase (extra : Nat) (s : State) :
    randomBase s - 8 = off (randomStackBase extra s) extra := by
  unfold randomBase Random.frameBytes randomStackBase off
  rw [BitVec.sub_sub, show BitVec.ofNat 64 248 + 8 = BitVec.ofNat 64 256 from rfl,
    Nat.add_comm extra 256, BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem random_frameBase (extra : Nat) (s : State) :
    randomBase s = off (randomStackBase extra s) (extra + 8) := by
  have hc := random_callBase extra s
  have he := congrArg (fun x : Addr => x + 8) hc
  rw [BitVec.sub_add_cancel] at he
  rw [he]
  simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  rfl

theorem random_nonceBase (extra : Nat) (s : State) :
    off (randomBase s) Random.oNonce = off (randomStackBase extra s) (extra + 208) := by
  rw [random_frameBase extra s]
  simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]
  rfl

theorem random_calleeBase (extra : Nat) (s : State) :
    randomBase s - 8 - BitVec.ofNat 64 extra = randomStackBase extra s := by
  rw [random_callBase extra s]
  exact BitVec.add_sub_cancel _ _

theorem randomStackBase_toNat {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    (randomStackBase extra s).toNat = (s.gpr .rsp).toNat - (extra + 256) := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  simp only [randomStackBase, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem randomStack_offset_toNat {extra : Nat} {s : State} (h : RandomSignABI extra s)
    {d : Nat} (hd : d ≤ extra + 256) :
    (off (randomStackBase extra s) d).toNat = (randomStackBase extra s).toNat + d := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  have hk := randomStackBase_toNat h
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end VG.Proof.Dsa.X86_64
