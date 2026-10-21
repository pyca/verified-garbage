module

public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Proof.Bignum.Arm.CompareWords
import VerifiedGarbage.Proof.Bignum.WordEquality32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! Readable packed-array bounds and the comparison's integer interpretation. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Bignum.Arm

theorem Ws.compareAddress {s : State} {B : BitVec 32} {Z w N j i : Nat}
    (h : Ws s B Z w N) (hj : j < N) (hi : i < w) :
    State.addr ((B + BitVec.ofNat 32 (arr w j)) + BitVec.ofNat 32 (4 * i)) =
      off (State.addr B) (arr w j + 4 * i) := by
  rw [Offset.add_add]
  exact h.addr (by have := h.arr_fit hj; simp only [S] at this; omega)

theorem Ws.compareCtx {s : State} {B : BitVec 32} {Z w N a b : Nat}
    (h : Ws s B Z w N) (ha : a < N) (hb : b < N) :
    WordCompareCtx s (B + BitVec.ofNat 32 (arr w a)) (B + BitVec.ofNat 32 (arr w b)) w := by
  refine ⟨by have := h.wle; omega, ?_, ?_⟩
  · intro i hi
    rw [h.compareAddress ha hi]
    exact h.read (by have := h.arr_fit ha; simp only [S] at this; omega)
  · intro i hi
    rw [h.compareAddress hb hi]
    exact h.read (by have := h.arr_fit hb; simp only [S] at this; omega)

theorem Ws.compareEqual {s : State} {B : BitVec 32} {Z w N a b : Nat} {m : Mem}
    (h : Ws s B Z w N) (ha : a < N) (hb : b < N) :
    (∀ i < w,
      m.readW (State.addr ((B + BitVec.ofNat 32 (arr w a)) + BitVec.ofNat 32 (4 * i))) 32 =
      m.readW (State.addr ((B + BitVec.ofNat 32 (arr w b)) + BitVec.ofNat 32 (4 * i))) 32) ↔
      num m B w a = num m B w b := by
  rw [num, num, VG.Proof.Bignum.val32_eq_iff_words]
  constructor
  · intro eq i hi
    have atI := eq i hi
    rwa [h.compareAddress ha hi, h.compareAddress hb hi] at atI
  · intro eq i hi
    rw [h.compareAddress ha hi, h.compareAddress hb hi]
    exact eq i hi

end VG.Proof.Rsa.Arm.Keys
