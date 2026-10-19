module
public import VerifiedGarbage.Impl.Bignum.Arm.SubRow
public import VerifiedGarbage.Proof.Bignum.Arm.SubState

import VerifiedGarbage.Proof.Bignum.Arm.SubCompare
import VerifiedGarbage.Proof.Bignum.Arm.SubRow

/-! # Keep pointer postconditions together with the exact subtraction comparison -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem subCompareRow_ok (s : State) {base : BitVec 32} {size o a b n : Nat}
    (ctx : SubCtx s base size o a b n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hp10 : s.gpr .r10 = base + BitVec.ofNat 32 a)
    (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (count : s.gpr .lr = BitVec.ofNat 32 n) (borrow : s.gpr .r11 = 0) :
    WP isa subRow s fun t =>
      t.gpr .r11 = (if val32 s.mem (State.addr base) a n < val32 s.mem (State.addr base) b n then 1 else 0) ∧
      SubInv s base o a b n n t :=
  WP.mono ((subCompare_ok s ctx hn hp0 hp10 hp12 count borrow).and
    (subRow_ok s ctx hn hp0 hp10 hp12 count (by rw [borrow]; decide))) (fun _ h => ⟨h.1.1, h.2⟩)

end VG.Proof.Bignum.Arm
