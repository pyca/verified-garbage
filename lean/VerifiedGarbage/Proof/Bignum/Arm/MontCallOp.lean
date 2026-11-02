module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.CallStack
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallEntry
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Framework.Arm.CallF

import VerifiedGarbage.Proof.Bignum.Arm.MontCallArgs
import VerifiedGarbage.Proof.Bignum.Arm.MontCallArgsReady
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.PlainSimp
/-! Shared callable products preserve the caller's arithmetic workspace,
allowing the callee's saved registers below the caller's stack pointer. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/MontCallInvoke.lean`, which only this module imported.
section

/-! Invoke a shared arithmetic kernel with its permissions restricted to
the RSA workspace and its fifth argument. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.Rsa.Mont (numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

def CallResult (base : BitVec 32) (len w o a b : Nat) (s t : State) : Prop :=
  numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
  numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
    numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
  Keeps (State.addr base) len w o s.mem t.mem

theorem montCallInvoke_ok (name : String) (callee : Prog isa)
    {base : BitVec 32} {len w o a b : Nat}
    (correct : ∀ s, CallInput base len w o a b s →
      WP isa callee s fun t => abiPreserved s t ∧ CallResult base len w o a b s t)
    (stack : armStack callee ≤ 40) (s : State) (h : CallInput base len w o a b s) :
    WP isa (.call name callee) s fun t =>
      CallResult base len w o a b s t ∧
      Frame [⟨State.addr base, 8 * len⟩, belowA s.sp 40] s.mem t.mem ∧ Rest roundClobbers s t := by
  let rd : List Region := [⟨State.addr s.sp, 4⟩]
  let wr : List Region := [⟨State.addr base, 8 * len⟩]
  let k : Contract isa := {
    pre := CallInput base len w o a b
    post := CallResult base len w o a b
    pub := fun _ _ => True }
  have pre : k.pre (s.callEntry.withRegions rd wr) := by
    refine ⟨⟨h.workspace.nowrap, by simp only [State.withRegions_wr, wr, List.mem_singleton]⟩,
      h.layout, h.width, ?_, ?_, ?_, h.bArg, h.inverse, h.operand, h.stackFit, ?_, h.stackWorkspace, h.stackArg⟩
    · exact (State.callEntry_gpr s (by decide)).trans h.ptr
    · exact (State.callEntry_gpr s (by decide)).trans h.outIndex
    · exact (State.callEntry_gpr s (by decide)).trans h.aIndex
    · exact ⟨_, List.mem_append_left _ List.mem_cons_self, Region.contains_self _ _⟩
  have coversWr : Covers wr s.wr := Covers.one ⟨_, h.workspace.writable, Region.contains_self _ _⟩
  have coversRd : Covers rd (s.rd ++ s.wr) := Covers.one h.argRead
  refine WP.callF (k := k) correct pre
    (Covers.append_left coversRd (Covers.right coversWr)) coversWr (by have := h.stackFit; omega) ?_
  intro t rdEq wrEq spEq frame _ result
  refine ⟨result, FrameStack.Frame.belowA_mono frame stack h.stackFit, ?_⟩
  exact ⟨by intro r hr; exact False.elim (hr (by cases r <;> simp [roundClobbers])),
    rdEq, wrEq, spEq⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CallArithmeticReady.lean`, which only this module imported.
section

/-! Arithmetic readiness survives a callee's permitted writes below the stack. -/
section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand Keeps)
open VG.Proof.X25519.Arm (Rest)
theorem ArithmeticReady.after_call {s t : State} {base : BitVec 32} {len w o : Nat}
    (h : ArithmeticReady base len w s) (cs : CallStack base len s) (ho : o ≠ 0)
    (keeps : Keeps (State.addr base) len w o s.mem t.mem)
    (frame : Frame [⟨State.addr base, 8 * len⟩, FrameStack.belowA s.sp 48] s.mem t.mem)
    (rest : Rest roundClobbers s t) (ptr : t.gpr .r0 = base) :
    ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have kl := keeps_layout h.layout (by rw [h.width]; exact keeps)
  have oldM := keeps_array_num keeps fits op0 (Ne.symm ho)
  have oldLow := keeps_array_word (d := 0) (bits := 64) keeps fits op0 (Ne.symm ho) (by omega)
  simp only [Nat.add_zero] at oldLow
  refine ⟨⟨h.workspace.congr rest.wr, kl.2, kl.1.trans h.width, ptr, ?_, ?_, ?_, ?_, ?_⟩, oldM⟩
  · change ((t.mem.readW (off (State.addr base) (arrAt w 0)) 64).toNat *
      (t.mem.readW (off (State.addr base) 56) 64).toNat + 1) % 2 ^ 64 = 0
    rw [oldLow, keeps_header_readW keeps size (d := 56) (bits := 64) (by decide)]
    exact h.inverse
  · rw [oldM]; exact h.modulus
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · rw [rest.sp]
    have sep : Region.Disjoint ⟨State.addr s.sp, 4⟩ (FrameStack.belowA s.sp 48) := by
      rw [FrameStack.belowA, FrameStack.addr_sub' cs.fit]
      exact (Offset.below_disjoint _ (by decide)).symm
    exact (frame.readW (r := ⟨State.addr s.sp, 4⟩) (Region.contains_self _ _)
      (by intro r hr
          rcases List.mem_cons.mp hr with hr | hr
          · subst r; exact h.stackSep
          · have er := List.mem_singleton.mp hr; subst r; exact sep) (by decide)).trans h.saved

end VG.Proof.Bignum.Arm
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem montCallOp_ok (name : String) (callee : Prog isa)
    {base : BitVec 32} {len w o a b : Nat}
    (correct : ∀ s, CallInput base len w o a b s →
      WP isa callee s fun t => abiPreserved s t ∧ CallResult base len w o a b s t)
    (stack : armStack callee ≤ 40) (s : State)
    (h : ArithmeticReady base len w s) (cs : CallStack base len s)
    (ho : Operand o) (ha : Operand a) (hb : Operand b) (ho0 : o ≠ 0)
    (operand : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) :
    WP isa (MontCall.op name callee o a b) s fun t =>
      ArithmeticReady base len w t ∧ CallStack base len t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩, belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have endM := array_end_le (w := w) (j := 0) (k := 8) (by decide)
  let A := allocated 8 s
  have fit8 : 8 ≤ s.sp.toNat := by have := cs.fit; omega
  have argSub : Region.Sub ⟨State.addr A.sp, 4⟩ (belowA s.sp 48) :=
    fun x hx => belowA_sub (a := 8) (by decide) cs.fit x (Region.sub_prefix (by decide) x hx)
  have argSep : Region.Disjoint ⟨State.addr A.sp, 4⟩ ⟨State.addr base, 8 * len⟩ :=
    cs.separate.sub_left argSub
  have argsWs : Workspace A base (8 * len) :=
    ⟨h.workspace.nowrap, List.mem_cons_of_mem _ h.workspace.writable⟩
  have argsWrite : InRegions A.wr (State.addr A.sp) 4 :=
    ⟨⟨State.addr A.sp, 8⟩, List.mem_cons_self, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide⟩
  have argsFit : A.sp.toNat + 8 ≤ 2 ^ 32 := by
    change (s.sp - BitVec.ofNat 32 8).toNat + 8 ≤ 2 ^ 32
    rw [sub_toNat' fit8]; have := s.sp.isLt; omega
  unfold MontCall.op
  rw [WP.seq_iff]
  apply WP.alloc (by decide) fit8
  rw [WP.seq_iff]
  refine WP.mono (montCallArgs_ok A argsWs (by omega) h.ptr argsFit argsWrite ho.1 ha.1 hb.1) ?_
  rintro u ⟨ptrU, outU, aU, memU, frameU, restU⟩
  change u.mem = s.mem.writeW (State.addr A.sp) (BitVec.ofNat 32 b) at memU
  change Frame [⟨State.addr A.sp, 4⟩] s.mem u.mem at frameU
  have eq := WorkspaceEq.of_frame (by have := h.workspace.nowrap; omega : 8 * len < 2 ^ 64)
    frameU (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact argSep.symm)
  have input := montCallArgs_input s u h cs hb operand eq ptrU outU aU memU restU
  refine WP.mono (montCallInvoke_ok name callee correct stack u input) ?_
  rintro v ⟨⟨bound, value, keeps⟩, frameV, restV⟩
  have restUV : Rest roundClobbers A v :=
    (restU.mono (by intro r _; cases r <;> simp [roundClobbers])).trans restV
  have frameArgs : Frame [⟨State.addr base, 8 * len⟩, belowA s.sp 48] s.mem u.mem :=
    frameU.sub fun r hr => by
      have er := List.mem_singleton.mp hr; subst r
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), argSub⟩
  have frameCall : Frame [⟨State.addr base, 8 * len⟩, belowA s.sp 48] u.mem v.mem :=
    frameV.sub fun r hr => by
      rcases List.mem_cons.mp hr with hr | hr
      · subst r; exact ⟨_, List.mem_cons_self, fun _ hx => hx⟩
      · have er := List.mem_singleton.mp hr; subst r
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
        rw [restU.sp]
        exact belowA_inner (a := 40) (k := 8) (by decide) cs.fit
  have frame := frameArgs.trans frameCall
  have keepsAll : Keeps (State.addr base) len w o s.mem v.mem := by
    intro i hi separate
    exact (keeps i hi separate).trans (frameU.bytes (R := ⟨State.addr base, 8 * len⟩)
      (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact argSep.symm)
      (by change 8 * len ≤ 2 ^ 64; have := h.workspace.nowrap; omega) hi)
  rw [eq.number fits (by decide : 0 < 8)] at bound value
  rw [eq.number fits ha.1, eq.number fits hb.1] at value
  have freeRest : Rest roundClobbers s (freed 8 v) := by
    refine ⟨by intro r hr; exact False.elim (hr (by cases r <;> simp [roundClobbers])), restUV.rd, ?_, ?_⟩
    · change v.wr.tail = s.wr; rw [restUV.wr]; rfl
    · change v.sp + BitVec.ofNat 32 8 = s.sp
      rw [restUV.sp]; exact BitVec.sub_add_cancel _ _
  have saved : (freed 8 v).mem.readW (State.addr (freed 8 v).sp) 32 = base := by
    rw [freeRest.sp]
    have sep : Region.Disjoint ⟨State.addr s.sp, 4⟩ (belowA s.sp 48) := by
      rw [belowA, addr_sub' cs.fit]
      exact (Offset.below_disjoint _ (by decide)).symm
    exact (frame.readW (r := ⟨State.addr s.sp, 4⟩) (Region.contains_self _ _)
      (by intro r hr
          rcases List.mem_cons.mp hr with hr | hr
          · subst r; exact h.stackSep
          · have er := List.mem_singleton.mp hr; subst r; exact sep) (by decide)).trans h.saved
  refine WP.mono (restoreBase_ok (freed 8 v)
    (by rw [freeRest.rd, freeRest.wr, freeRest.sp]; exact h.stackRead) saved) ?_
  rintro t ⟨ptrT, memT, restT⟩
  change t.mem = v.mem at memT
  have rest := freeRest.trans (restT.mono (by intro r _; cases r <;> simp [roundClobbers]))
  rw [← memT] at keepsAll frame bound value
  obtain ⟨ready, modulus⟩ := h.after_call cs ho0 keepsAll frame rest ptrT
  exact ⟨ready, cs.of_rest rest, modulus, bound, value, keepsAll, frame, rest⟩

end VG.Proof.Bignum.Arm
