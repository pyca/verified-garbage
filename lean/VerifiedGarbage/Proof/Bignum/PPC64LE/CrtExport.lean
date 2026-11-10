module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The RSA private-key operation on PPC64LE: `X`'s arrays

`xb_ok`: the base of `X`'s array `j`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

theorem xb_cons (rd : Reg) (j : Nat) : xb rd (j + 1) = xb rd j ++ ([.add rd rd .r28] : List Instr) := by
  simp only [xb, List.replicate_succ', List.cons_append]

/-- `xb rd j`, `X`'s array 0 at `r27` and its arrays' size in `r28`. -/
theorem xb_ok {t : State} {B : Addr} {w : Nat} {rd : Reg} (hrd : rd ≠ .r0) (hrd28 : rd ≠ .r28)
    (h27 : t.gpr .r27 = off B (slot w 0)) (h28 : t.gpr .r28 = BitVec.ofNat 64 (8 * (w + 2))) :
    ∀ j, WP isa (.block (xb rd j)) t fun t' =>
      (t'.gpr rd = off B (slot w j) ∧ t'.mem = t.mem) ∧ Keep [rd] t t'
  | 0 => by
    apply WP.of_runBlock
    simp only [xb, List.replicate_zero, runBlock_cons, exec_addi (show Reg.r27 ≠ .r0 by decide)
      (show 0 < 2 ^ 15 by decide), runStep_some, runBlock_nil, BitVec.add_zero, h27]
    exact ⟨_, rfl, ⟨by simp [gpr_write], rfl⟩, Keep.write _ _ _⟩
  | j + 1 => by
    rw [xb_cons, WP.block_append_iff]
    refine WP.mono (xb_ok hrd hrd28 h27 h28 j) fun t₁ ⟨⟨h1, m1⟩, k1⟩ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_add, runStep_some, runBlock_nil, h1,
      (k1.gpr .r28 (by simpa using Ne.symm hrd28)).trans h28]
    refine ⟨_, rfl, ⟨?_, m1⟩, (k1.trans (Keep.write _ _ _)).mono (by simp)⟩
    rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e, off_add, show slot w (j + 1) = slot w j + 8 * (w + 2) by
      unfold slot; rw [Nat.add_mul, Nat.one_mul]; omega_arith]

end VG.Proof.Bignum.PPC64LE.Crt
