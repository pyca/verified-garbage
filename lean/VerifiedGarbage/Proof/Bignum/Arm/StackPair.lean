module
public import Batteries.Logic
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.X25519.Arm.Instr

import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Load two distinct registers from public stack slots -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem stackPair_ok (s : State) (r q : Reg) (d e : Nat) (neq : r ≠ q)
    (hd : d < 4096) (he : e < 4096)
    (fitD : s.sp.toNat + d < 2 ^ 32) (fitE : s.sp.toNat + e < 2 ^ 32)
    (readD : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) d) 4)
    (readE : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) e) 4) :
    WP isa (.block [.ldrSp r d, .ldrSp q e]) s fun t =>
      t.gpr r = s.mem.readW (off (State.addr s.sp) d) 32 ∧
      t.gpr q = s.mem.readW (off (State.addr s.sp) e) 32 ∧
      t.mem = s.mem ∧ Rest [r, q] s t := by
  refine wp_loadStack (a := off (State.addr s.sp) d) hd (addr_add fitD) readD fun u a => ?_
  refine wp_loadStack (a := off (State.addr s.sp) e) he (by rw [a.sp]; exact addr_add fitE)
    (by rw [a.rd, a.wr]; exact readE) fun t b => WP.block_nil ?_
  exact ⟨(b.other r neq).trans a.gpr, by rw [b.gpr, a.mem], b.mem.trans a.mem,
    (a.rest (by simp)).trans (b.rest (by simp))⟩

end VG.Proof.Bignum.Arm
