module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCallWith
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithLaw
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallEntry
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Callable Montgomery multiplication preserves the ARM procedure-call ABI -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wOf numAt Operand Keeps)

theorem montCallWithFn_ok (arithmetic : Prog isa) (law : CallArithmeticLaw arithmetic) (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : CallInput base len w o a b s) (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    WP isa (MontCallWith.code arithmetic) s fun t => abiPreserved s t ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem := by
  have nowrap := h.workspace.nowrap
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have eq := h.pushed_eq
  have framePush := FrameStack.pushed_frameA (rs := MontCall.savedRegs) h.stackFit
  unfold MontCallWith.code
  refine WP.frame (by decide) h.stackFit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (call_entry_ok s h hb.1) ?_
  rintro u ⟨ready, memU, restU⟩
  rw [WP.seq_iff]
  have savedPush := call_push_saved s h.stackFit
  have stackRead : InRegions (u.rd ++ u.wr) (State.addr u.sp) 4 := by
    rw [restU.rd, restU.wr, restU.sp]
    refine ⟨⟨State.addr (callPushed s).sp, 40⟩, List.mem_append_right _ List.mem_cons_self, ?_⟩
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  have stackSep : Region.Disjoint ⟨State.addr u.sp, 4⟩ ⟨State.addr base, 8 * len⟩ := by
    rw [restU.sp]
    exact h.stackWorkspace.sub_left (Region.sub_prefix (by decide))
  have savedBase : u.mem.readW (State.addr u.sp) 32 = base := by
    rw [memU, restU.sp]
    change (callPushed s).mem.readW (State.addr (s.sp - 40)) 32 = base
    simpa only [BitVec.add_zero] using (savedPush (.r0, 0) (by decide)).trans h.ptr
  have callReady : CallBodyReady base len w o a b u := ⟨ready, stackRead, stackSep, savedBase⟩
  have body := law.correct u callReady ho ha hb
  refine WP.mono body ?_
  rintro v ⟨lt, value, keeps, frameBody, restV⟩
  have spV : v.sp = s.sp - BitVec.ofNat 32 40 := restV.sp.trans restU.sp
  have wrV : v.wr = (callPushed s).wr := restV.wr.trans restU.wr
  rw [memU] at lt value keeps frameBody
  have saved : Spill.Saved v.mem (State.addr v.sp) s.gpr callAllSaved := by
    rw [spV]
    have savedPush : Spill.Saved (callPushed s).mem (State.addr (s.sp - BitVec.ofNat 32 40)) s.gpr callAllSaved :=
      call_push_saved s h.stackFit
    exact savedPush.frame (lo := 0) (hi := 40) (by decide) frameBody (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simpa only [FrameStack.belowA, BitVec.add_zero, Nat.sub_zero] using h.stackWorkspace)
  have stackFit : v.sp.toNat + 40 ≤ 2 ^ 32 := by
    rw [spV, FrameStack.sub_toNat' h.stackFit]
    have := s.sp.isLt
    omega
  have writable : (⟨State.addr v.sp, 40⟩ : Region) ∈ v.wr := by
    rw [wrV, spV]
    exact List.mem_cons_self
  refine WP.mono (call_restore_ok v s.gpr stackFit ⟨_, List.mem_append_right _ writable, Region.contains_self _ _⟩ saved) ?_
  rintro t ⟨restored, memT, restT⟩
  have spT : t.sp = s.sp - BitVec.ofNat 32 40 := restT.sp.trans spV
  have oldM := eq.number fits (by decide : 0 < 8)
  have oldA := eq.number fits ha.1
  have oldB := eq.number fits hb.1
  rw [oldM] at lt
  rw [oldM, oldA, oldB] at value
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro r hr
    have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    rw [popped_gpr ne]
    have member : r ∈ callCalleeSaved.map Prod.fst := by
      simpa only [callCalleeSaved, List.map_cons, List.map_nil, preserved] using hr
    obtain ⟨p, hp, eqr⟩ := List.mem_map.mp member
    rw [← eqr]
    exact restored p hp
  · rw [popped_sp, spT]
    exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, memT]; exact lt
  · rw [popped_mem, memT]; exact value
  · intro i hi separate
    rw [popped_mem, memT, keeps i hi separate]
    exact framePush.bytes (R := ⟨State.addr base, 8 * len⟩)
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stackWorkspace.symm)
      (by change 8 * len ≤ 2 ^ 64; omega) hi

end VG.Proof.Bignum.Arm
