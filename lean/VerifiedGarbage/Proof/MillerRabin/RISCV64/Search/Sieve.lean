module

public import VerifiedGarbage.Impl.MillerRabin.RISCV64.Search
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A prime search on RISC-V: comparisons

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Search/GeFlag.lean`): `geFlag_ok`,
`d := 1` if `a ≥ b`, else 0 (`sltu`, then `xori 1`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Search

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (wv Frm word writeW_outside word_writeW_self)
open VG.Proof.Mont (off)

/-! ## Words of the working space read through stores -/

/-! ## Comparisons -/

theorem ge_val (x y : BitVec 64) :
    (if x < y then (1 : BitVec 64) else 0) ^^^ BitVec.ofInt 64 1 = BitVec.ofNat 64 (if y.toNat ≤ x.toNat then 1 else 0) := by
  by_cases h : x < y
  · have h' : ¬ y.toNat ≤ x.toNat := by rw [BitVec.lt_def] at h; omega
    simp only [h, h', ↓reduceIte]; decide
  · have h' : y.toNat ≤ x.toNat := by rw [BitVec.lt_def] at h; omega
    simp only [h, h', ↓reduceIte]; decide

/-- `geFlag d a b`: `d := 1` if `a ≥ b` (unsigned), else 0. -/
theorem geFlag_ok {s : State} {d a b : Reg} {x y : Nat} (ha : s.gpr a = BitVec.ofNat 64 x)
    (hb : s.gpr b = BitVec.ofNat 64 y) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    WP isa (.block (geFlag d a b)) s fun t =>
      (t.gpr d = BitVec.ofNat 64 (if y ≤ x then 1 else 0) ∧ t.mem = s.mem) ∧ Keep [d] s t := by
  refine WP.keep _ ?_ (by simp [geFlag, writesOnly, Code.allInstrs, dstOf]) (by rfl)
  apply WP.of_runBlock
  simp only [geFlag, runBlock_cons, runStep_some, runBlock_nil, exec_sltu, exec_logicImm (show imm12 1 by decide),
    gpr_write, mem_write, ↓reduceIte, ha, hb, Option.some.injEq, exists_eq_left', and_true]
  rw [ge_val, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

/-! ## The bit-serial remainder -/

/-! ## The sieve -/

end VG.Proof.MillerRabin.RISCV64.Search
