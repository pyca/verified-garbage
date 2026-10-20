module

public import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
public import VerifiedGarbage.Proof.Ffdh.Arm.Entered
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! Public incoming argument words survive writes to the native local frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure IncomingWord (value : BitVec 32) (d : Nat) (s : State) : Prop where
  fits : s.sp.toNat + d + 4 ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) d) 4
  word : s.mem.readW (off (State.addr s.sp) d) 32 = value

theorem IncomingWord.after {value : BitVec 32} {d : Nat} {s t : State} {rs : List Reg}
    (h : IncomingWord value d s) (large : 72 ≤ d)
    (frame : Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem) (rest : Rest rs s t) : IncomingWord value d t := by
  refine ⟨by rw [rest.sp]; exact h.fits, ?_, ?_⟩
  · rw [rest.rd, rest.wr, rest.sp]; exact h.readable
  · rw [rest.sp]
    have word := frame.readW (w := 32) (r := ⟨off (State.addr s.sp) d, 4⟩) (Region.contains_self _ _)
      (by intro r hr; rw [List.mem_singleton] at hr; subst r
          exact Offset.disjoint_base _ large (by have := h.fits; omega)) (by decide)
    exact word.trans h.word

theorem wp_load_incoming {s : State} {is : List Instr} {Q : State → Prop} {value : BitVec 32} {d : Nat}
    (r : Reg) (h : IncomingWord value d s) (small : d < 4096)
    (next : ∀ t, t.gpr r = value → t.mem = s.mem → Rest [r] s t → WP isa (.block is) t Q) :
    WP isa (.block (.ldrSp r d :: is)) s Q := by
  refine wp_loadStack (a := off (State.addr s.sp) d) small
    (addr_add (by have := h.fits; omega)) h.readable fun t loaded => ?_
  exact next t (loaded.gpr.trans h.word) loaded.mem (loaded.rest (by simp))

theorem wp_retain_incoming {s : State} {is : List Instr} {Q : State → Prop} {p : Inputs}
    {slots : List Nat} {d target : Nat} (r : Reg) (ne : r ≠ .r12)
    (h : ArgumentMemory p slots s) (stable : stableSlots slots = true)
    (incoming : IncomingWord (p.slotValue target) d s) (small : d < 4096)
    (aligned : target % 4 = 0) (fit : target + 4 ≤ 72) (stackBase : s.gpr .r12 = s.sp)
    (next : ∀ t, ArgumentMemory p (target :: slots) t →
      Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem → Rest [r] s t →
      t.gpr r = p.slotValue target → t.gpr .r12 = t.sp → WP isa (.block is) t Q) :
    WP isa (.block (.ldrSp r d :: .str r .r12 target :: is)) s Q := by
  refine wp_load_incoming r incoming small fun u value mem rest => ?_
  have argsU := h.of_mem mem rest
  have stackU := (rest.gpr .r12 (by simpa only [List.mem_singleton] using Ne.symm ne)).trans
    (stackBase.trans rest.sp.symm)
  refine wp_store_arg r target argsU stable aligned fit value stackU fun t argsT frameT restT => ?_
  have allRest := rest.trans (restT.mono (by simp))
  have finalValue := (restT.gpr r (by simp)).trans value
  have stackT := (restT.gpr .r12 (by simp)).trans (stackU.trans restT.sp.symm)
  apply next t argsT _ allRest finalValue stackT
  rw [rest.sp, mem] at frameT
  exact frameT

theorem enteredIncoming (s : State) {i : Nat} {value : BitVec 32}
    (stackFit : 128 ≤ s.sp.toNat) (argFit : s.sp.toNat + 4 * i + 4 ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4)
    (separate : (FrameStack.belowA s.sp 128).Disjoint ⟨stackArgAddr s i, 4⟩)
    (word : stackArg s i = value) : IncomingWord value (128 + 4 * i) (entered s) := by
  have nativeRoom : (entered s).sp.toNat + (128 + 4 * i) < 2 ^ 32 := by
    rw [entered_nat s stackFit]; omega
  have nativeAddr : off (State.addr (entered s).sp) (128 + 4 * i) = stackArgAddr s i := by
    change State.addr (entered s).sp + BitVec.ofNat 64 (128 + 4 * i) = _
    rw [← VG.Arm.addr_add nativeRoom, entered_sp, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    rfl
  refine ⟨by rw [entered_nat s stackFit]; omega, ?_, ?_⟩
  · rw [nativeAddr]; exact entered_read read
  · rw [nativeAddr]
    have old := (entered_frame s stackFit).readW (w := 32) (r := ⟨stackArgAddr s i, 4⟩)
      (Region.contains_self _ _) (by
        intro r hr
        rw [List.mem_singleton] at hr
        subst r
        exact separate.symm.sub_right (saved_sub_reserved s stackFit)) (by decide)
    exact old.trans word

end VG.Proof.Ffdh.Arm
