module

public import VerifiedGarbage.Proof.Poly1305.RISCV64.State
public import VerifiedGarbage.Proof.Poly1305.RISCV64.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Poly1305.Spec
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.State
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Poly1305.RISCV64.Reduce
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Reduce

/-!
# Poly1305 on RISC-V: `blocks`

As on AArch64 (`Proof/Poly1305/AArch64/Radix64/Blocks.lean`): the loop
invariant says that the accumulator in the registers is that of the message
on entry followed by the blocks absorbed so far, modulo `p`; the epilogue
reduces and stores it. The code writes only temporaries and argument
registers, and the memory only in the state's accumulator.
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.Poly1305.RISCV64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

/-- The registers the code writes: no preserved register, nor `ra`. -/
def written : List Reg :=
  [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-- The absorbing of a block, with the key from `Keys`. -/
theorem absorb_key_ok (s : State) (b : Reg) (off : Nat) (pad : Bool) (wide : Bool) {R : Nat}
    (hk : Keys R s)
    (ho : off + 15 < 2048)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 off) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 (off + 8)) 8)
    (hal : wide = true → (s.gpr b + BitVec.ofNat 64 off).toNat % 8 = 0)
    (hb : b ∉ absorbRegs := by decide) :
    WP isa (.block (absorb b off pad wide)) s fun s' =>
      (Bounds s → hv s' % P =
        ((hv s + (word s.mem (s.gpr b) off + 2 ^ 64 * word s.mem (s.gpr b) (off + 8) +
          2 ^ 128 * pad.toNat)) * R) % P ∧ Bounds s') ∧ Keeps absorbRegs s s' := by
  obtain ⟨q, hr0, hr1, hq, hs1, hr⟩ := hk
  simpa only [← hr, Bounds] using absorb_ok s b off pad wide hr0 hr1 hq hs1 ho h0 h8 hal hb

/-! ## The precondition -/

/-- The value of block `i`, with the `0x01` byte appended: its two words and `2¹²⁸`. -/
theorem block_value (m : Mem) (p : Addr) :
    word m p 0 + 2 ^ 64 * word m p (0 + 8) + 2 ^ 128 * true.toNat =
      leNum (bytesAt m p 16 ++ [0x01]) := by
  rw [Poly1305.leNum_append, Poly1305.length_bytesAt, leNum_key]
  have h1 : leNum [(0x01 : Byte)] = 1 := rfl
  rw [h1, Bool.toNat_true, show (256 : Nat) ^ 16 = 2 ^ 128 from rfl]

end VG.Proof.Poly1305.RISCV64
