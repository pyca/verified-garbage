module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Mont.Words
public import Batteries.Logic
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # Save private RSA output and scratch pointers in the call frame -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd wp_str wp_mov op2_reg)

theorem crt_entry_ok (s : State) {base : BitVec 32}
    (fit : s.sp.toNat + 108 ≤ 2 ^ 32)
    (stack : (⟨State.addr s.sp, 56⟩ : Region) ∈ s.wr)
    (argRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 104) 4)
    (arg : s.mem.readW (off (State.addr s.sp) 104) 32 = base) :
    WP isa (.block CrtFn.entry) s fun t =>
      t.gpr .r0 = base ∧ t.gpr .r4 = s.gpr .r2 ∧ t.gpr .r6 = s.gpr .r3 ∧
      t.mem = (s.mem.writeW (off (State.addr s.sp) 4) (s.gpr .r0)).writeW (State.addr s.sp) base ∧
      Rest [.r0, .r4, .r6, .r12] s t := by
  unfold CrtFn.entry
  refine wp_stackAddr (by decide) fun u h => ?_
  have ptr : u.gpr .r12 = s.sp := by simpa only [BitVec.add_zero] using h.gpr
  refine wp_str (a := off (State.addr s.sp) 4) (by decide)
    (by rw [ptr]; exact addr_add (by omega))
    (by rw [h.wr]; exact ⟨_, stack, Offset.contains_base _ (by decide) (by decide)⟩) fun v j => ?_
  have outside := writeW32_outside s.mem (State.addr s.sp) (d := 4) (s.gpr .r0) (by decide)
  have memV : v.mem = s.mem.writeW (off (State.addr s.sp) 4) (s.gpr .r0) := by
    rw [j.mem, h.mem, h.other .r0 (by decide)]
  have argV : v.mem.readW (off (State.addr s.sp) 104) 32 = base := by
    rw [memV, outside_read32 outside (by decide) (by decide)]; exact arg
  refine wp_loadStack (a := off (State.addr s.sp) 104) (by decide)
    (by rw [j.sp, h.sp]; exact addr_add (by omega))
    (by rw [j.rd, j.wr, h.rd, h.wr]; exact argRead) fun z l => ?_
  have baseZ : z.gpr .r0 = base := l.gpr.trans argV
  refine wp_str (a := State.addr s.sp) (by decide)
    (by rw [l.other .r12 (by decide), j.gpr, ptr]; simp)
    (by rw [l.wr, j.wr, h.wr]; exact ⟨_, stack, by simp [Region.Contains]⟩) fun a q => ?_
  refine wp_mov (op2_reg _ _) fun b r => ?_
  refine wp_mov (op2_reg _ _) fun t f => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [f.other .r0 (by decide), r.other .r0 (by decide), q.gpr, baseZ]
  · rw [f.other .r4 (by decide), r.gpr, q.gpr, l.other .r2 (by decide), j.gpr, h.other .r2 (by decide)]
  · rw [f.gpr, r.other .r3 (by decide), q.gpr, l.other .r3 (by decide), j.gpr, h.other .r3 (by decide)]
  · rw [f.mem, r.mem, q.mem, baseZ, l.mem, memV]
  · exact (h.rest (by simp)).trans ((j.rest _).trans ((l.rest (by simp)).trans
      ((q.rest _).trans ((r.rest (by simp)).trans (f.rest (by simp))))))

end VG.Proof.Bignum.Arm
