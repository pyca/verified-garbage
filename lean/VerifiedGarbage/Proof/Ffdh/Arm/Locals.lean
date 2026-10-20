module

public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.PcStack
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! The FFDH frame retains public pointers and lengths across RSA arithmetic. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

structure Locals (base : BitVec 32) (len : Nat) (s : State) : Prop where
  space : Workspace s s.sp 72
  separate : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr base, 8 * len⟩

theorem Locals.after {base : BitVec 32} {len : Nat} {s t : State} {rs : List Reg}
    (h : Locals base len s) (rest : Rest rs s t) : Locals base len t := by
  refine ⟨?_, ?_⟩
  · rw [rest.sp]; exact h.space.congr rest.wr
  · rw [rest.sp]; exact h.separate

theorem Locals.read {base : BitVec 32} {len d : Nat} {s : State}
    (h : Locals base len s) (fit : d + 4 ≤ 72) :
    InRegions (s.rd ++ s.wr) (off (State.addr s.sp) d) 4 := h.space.read fit

theorem localLoad_ok (s : State) {base : BitVec 32} {len d : Nat} (r : Reg)
    (h : Locals base len s) (fit : d + 4 ≤ 72) :
    WP isa (.block [.ldrSp r d]) s fun t =>
      t.gpr r = s.mem.readW (off (State.addr s.sp) d) 32 ∧ t.mem = s.mem ∧ Rest [r] s t := by
  refine wp_loadStack (a := off (State.addr s.sp) d) (by omega)
    (addr_add (by have := h.space.nowrap; omega)) (h.read fit) fun t loaded => WP.block_nil ?_
  exact ⟨loaded.gpr, loaded.mem, loaded.rest (by simp)⟩

theorem localStore_ok (s : State) {base : BitVec 32} {len d : Nat} (r : Reg)
    (h : Locals base len s) (fit : d + 4 ≤ 72) (notTemp : r ≠ .r12) :
    WP isa (.block [.addSp .r12 0, .str r .r12 d]) s fun t =>
      t.mem = s.mem.writeW (off (State.addr s.sp) d) (s.gpr r) ∧
      Frame [⟨off (State.addr s.sp) d, 4⟩] s.mem t.mem ∧ Rest [.r12] s t := by
  refine wp_stackAddr (by decide) fun u addr => ?_
  refine wp_str (a := off (State.addr s.sp) d) (by omega)
    (by rw [addr.gpr, BitVec.add_zero]; exact addr_add (by have := h.space.nowrap; omega))
    (by rw [addr.wr]; exact h.space.write fit) fun t stored => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off (State.addr s.sp) d) (s.gpr r) := by
    rw [stored.mem, addr.mem, addr.other r notTemp]
  refine ⟨mem, ?_, (addr.rest (by simp)).trans (stored.rest _)⟩
  rw [mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

end VG.Proof.Ffdh.Arm
