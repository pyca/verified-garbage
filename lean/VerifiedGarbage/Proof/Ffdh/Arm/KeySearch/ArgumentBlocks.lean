module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Small native blocks used to place the selected attempt's stack arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem argumentHead_ok (s : State) {base x y : BitVec 32} {n : Nat}
    (h : Controller base s) (xvalue : lowWord s.mem base 5 = x)
    (yvalue : lowWord s.mem base 6 = y) (width : lowWord s.mem base 2 = BitVec.ofNat 32 n) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 5, VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 2,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 6, VG.Impl.Ffdh.Arm.KeySearch.ldf .r3 2, .addSp .r12 0]) s fun t =>
      (t.gpr .r0 = x ∧ t.gpr .r1 = BitVec.ofNat 32 n ∧ t.gpr .r2 = y ∧
        t.gpr .r3 = BitVec.ofNat 32 n ∧ t.gpr .r12 = s.sp ∧ t.mem = s.mem) ∧
      Rest [.r0, .r1, .r2, .r3, .r12] s t := by
  refine withRest [.r0, .r1, .r2, .r3, .r12] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 5,
        VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 2, VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 6,
        VG.Impl.Ffdh.Arm.KeySearch.ldf .r3 2, .addSp .r12 0] : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.KeySearch.ldf lowWord at *
  ffrun [h.addr (by decide : 5 < 16), h.addr (by decide : 6 < 16), h.addr (by decide : 2 < 16),
    h.read (by decide : 5 < 16), h.read (by decide : 6 < 16), h.read (by decide : 2 < 16),
    xvalue, yvalue, width, BitVec.add_zero]

theorem argumentCopyAt_ok (s : State) {base value : BitVec 32} {offset d bytes : Nat}
    (h : Controller base s) (sourceFit : offset + 4 ≤ 128)
    (stack : Workspace s s.sp bytes) (fit : d + 4 ≤ bytes)
    (stackBase : s.gpr .r12 = s.sp)
    (source : s.mem.readW (off (State.addr base) offset) 32 = value)
    (small : d < 4096 := by omega) :
    WP isa (.block [.ldr .r9 .r4 offset, .str .r9 .r12 d]) s fun t =>
      t.mem = s.mem.writeW (off (State.addr s.sp) d) value ∧ Rest [.r9] s t := by
  refine withRest [.r9] ?_ (by
    intro r hr i hi
    simp only [instrs, List.mem_cons, List.not_mem_nil, or_false] at hi
    have ne : r ≠ .r9 := by simpa only [List.mem_singleton] using hr
    rcases hi with rfl | rfl <;> simp [clobbers, dstOf, Ne.symm ne]) (by rfl)
  have address : State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := stack.nowrap; omega)
  have sourceAddress : State.addr (base + BitVec.ofNat 32 offset) = off (State.addr base) offset :=
    VG.Arm.addr_add (by have := h.space.nowrap; omega)
  ffrun [(by omega : offset < 4096), small, h.ptr, sourceAddress, h.space.read sourceFit,
    stackBase, address, stack.write fit, source]

theorem argumentCopy_ok (s : State) {base value : BitVec 32} {j d bytes : Nat}
    (h : Controller base s) (slot : j < 16) (stack : Workspace s s.sp bytes) (fit : d + 4 ≤ bytes)
    (stackBase : s.gpr .r12 = s.sp) (source : lowWord s.mem base j = value)
    (small : d < 4096 := by omega) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 j, .str .r9 .r12 d]) s fun t =>
      t.mem = s.mem.writeW (off (State.addr s.sp) d) value ∧ Rest [.r9] s t := by
  exact argumentCopyAt_ok s h (by omega) stack fit stackBase source small

theorem argumentStore_ok (s : State) {value : BitVec 32} {d bytes : Nat} (r : Reg)
    (stack : Workspace s s.sp bytes) (fit : d + 4 ≤ bytes) (stackBase : s.gpr .r12 = s.sp)
    (source : s.gpr r = value) (small : d < 4096 := by omega) :
    WP isa (.block [.str r .r12 d]) s fun t =>
      t.mem = s.mem.writeW (off (State.addr s.sp) d) value ∧ Rest [] s t := by
  refine withRest [] ?_ (by
    intro q _ i hi
    simp only [instrs, List.mem_singleton] at hi
    subst i
    rfl) (by rfl)
  have address : State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := stack.nowrap; omega)
  ffrun [small, stackBase, address, stack.write fit, source]

end VG.Proof.Ffdh.Arm.KeySearch
