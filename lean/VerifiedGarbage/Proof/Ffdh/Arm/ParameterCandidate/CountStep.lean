module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyOps
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyView
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Ffdh.Arm.ParameterCandidate.CountTail`, which only this module used -/

section

/-! Increment the native halving count and test the new exponent's low bit. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)
open VG.Proof.Rsa.Arm.Keys (num arr S)

theorem halfCountTail_ok {s : State} {base : BitVec 32} {capacity w count : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 count)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountTail) s fun t =>
      (t.mem = s.mem.writeW (State.addr (s.sp + 60#32)) (BitVec.ofNat 32 (count + 1)) ∧
        t.z = decide (num s.mem (base + 96#32) (2 * w + 2) 29 % 2 = 0)) ∧
      Rest [.r0, .r1, .r12] s t := by
  have read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 60#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega_using [this])]
    exact stack.read (by decide)
  have write : InRegions s.wr (State.addr (s.sp + 60#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega_using [this])]
    exact stack.write (by decide)
  let B := base + 96#32
  let d := arr (2 * w + 2) 29
  have nativeAddr : State.addr (B + BitVec.ofNat 32 d) = off (State.addr B) d :=
    ready.addr (by have := ready.arr_fit (j := 29) (by decide); simp only [S] at this; omega_using [this])
  have realRead : InRegions (s.rd ++ s.wr) (State.addr (B + BitVec.ofNat 32 d)) 4 := by
    rw [nativeAddr]
    rw [VG.Arm.addr_add (ready.baseShiftFits workspace)]
    unfold off
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, keyView_array]
    exact workspace.read (by have := ready.arrayFit (j := 29) (by decide); omega_using [this])
  have stackSep : (⟨State.addr (s.sp + 60#32), 4⟩ : Region).Disjoint
      ⟨State.addr (B + BitVec.ofNat 32 d), 4⟩ := by
    have a : State.addr (B + BitVec.ofNat 32 d) = off (State.addr base) (Proof.Rsa.Mont.arrAt w 29) := by
      rw [nativeAddr, VG.Arm.addr_add (ready.baseShiftFits workspace)]
      unfold off
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, keyView_array]
    rw [a, VG.Arm.addr_add (by have := stack.nowrap; omega_using [this])]
    exact separate.sub_left (Offset.sub_base _ (by decide : 60 + 4 ≤ 72)) |>.sub_right
      (Offset.sub_base _ (by have := ready.arrayFit (j := 29) (by decide); omega_using [this]))
  have lowUnchanged : (s.mem.writeW (State.addr (s.sp + 60#32)) (BitVec.ofNat 32 (count + 1))).readW
      (State.addr (B + BitVec.ofNat 32 d)) 32 = s.mem.readW (State.addr (B + BitVec.ofNat 32 d)) 32 :=
    Mem.readW_writeW_sep stackSep.symm (by decide)
  have ptrValue : BitVec.ofNat 32 29 * BitVec.ofNat 32 (S (2 * w + 2)) + B + 160 = B + BitVec.ofNat 32 d :=
    VG.Proof.Rsa.Arm.Keys.ptr_val B 29 (S (2 * w + 2))
  change BitVec.ofNat 32 29 * BitVec.ofNat 32 (S (2 * w + 2)) + B +
    BitVec.ofNat 32 VG.Impl.Rsa.Arm.Keys.hdr = B + BitVec.ofNat 32 d at ptrValue
  have r7 : s.gpr .r7 = BitVec.ofNat 32 (S (2 * w + 2)) := ready.r7
  have r8 : s.gpr .r8 = B := ready.r8
  have plus : BitVec.ofNat 32 count + 1 = BitVec.ofNat 32 (count + 1) := by
    change BitVec.ofNat 32 count + BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_add_ofNat count 1
  have parity : (s.mem.readW (State.addr (B + BitVec.ofNat 32 d)) 32 &&& 1 == 0) =
      decide (num s.mem B (2 * w + 2) 29 % 2 = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [← BitVec.toNat_inj, VG.Proof.Rsa.Arm.Keys.bv_and_one, nativeAddr,
      ← VG.Proof.Rsa.Arm.Keys.num_mod2 s.mem B (by omega_using [] : 0 < 2 * w + 2)]
    rfl
  refine withRest_all [.r0, .r1, .r12] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountTail VG.Impl.Ffdh.Arm.ParameterCandidate.save
    VG.Impl.Rsa.Arm.Keys.ptr
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, read, write, saved, plus, r7, r8,
    ptrValue, realRead, lowUnchanged]
  change (_ - 0#32 == 0#32) = _
  rw [BitVec.sub_zero]
  exact parity

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! One native exponent-halving iteration, with the exact count and parity. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.Keys (num opRegs)

private theorem zeroCarry (s : State) :
    WP isa (.block [.mov .r11 (.imm 0)]) s fun t =>
      t.gpr .r11 = 0#32 ∧ t.mem = s.mem ∧ Rest [.r11] s t := by
  refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_
  exact ⟨u.gpr, u.mem, u.rest (by simp)⟩

theorem halfCountStep_ok {s : State} {base : BitVec 32} {capacity w count : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (data : MontData base capacity w s.mem) (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 count)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountStep s fun t =>
      KeyReady base capacity w t ∧ MontData base capacity w t.mem ∧
      num t.mem (base + 96#32) (2 * w + 2) 29 = num s.mem (base + 96#32) (2 * w + 2) 29 / 2 ∧
      t.mem.readW (State.addr (t.sp + 60#32)) 32 = BitVec.ofNat 32 (count + 1) ∧
      t.z = decide (num s.mem (base + 96#32) (2 * w + 2) 29 / 2 % 2 = 0) ∧
      (∀ j, j < 30 → j ≠ 29 → num t.mem (base + 96#32) (2 * w + 2) j =
        num s.mem (base + 96#32) (2 * w + 2) j) ∧
      (∀ d, d + 8 ≤ 256 → t.mem.readW (off (State.addr base) d) 64 =
        s.mem.readW (off (State.addr base) d) 64) ∧
      Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩] s.mem t.mem ∧
      Rest opRegs s t := by
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountStep, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (zeroCarry s) ?_)
  rintro u ⟨carryU, memU, restU⟩
  have readyU := ready.rest restU (by decide) (by decide) (by decide)
  have workspaceU := workspace.congr restU.wr
  refine WP.seq (WP.mono (keyHalf_ok workspaceU readyU (j := 29) (by decide) (by rw [carryU]; decide)) ?_)
  rintro v ⟨readyV, keepV, valueV, restV⟩
  rw [carryU, memU, show (0#32).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero] at valueV
  have frameV := key_keep_workspace workspaceU readyU (by simp) keepV
  have dataV := (MontData.after_key_keep (by rw [memU]; exact data) workspaceU readyU
    (by simp) (by simp) keepV).1
  have restUV : Rest opRegs s v := (restU.mono (by simp [opRegs])).trans restV
  have stackV : Workspace v v.sp 72 := by rw [restUV.sp]; exact stack.congr restUV.wr
  have countSep : (⟨State.addr (s.sp + 60#32), 4⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩ := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega_using [this])]
    exact separate.sub_left (Offset.sub_base _ (by decide : 60 + 4 ≤ 72))
  have countV : v.mem.readW (State.addr (v.sp + 60#32)) 32 = BitVec.ofNat 32 count := by
    rw [restUV.sp, frameV.readW (r := ⟨State.addr (s.sp + 60#32), 4⟩)
      (Region.contains_self _ _) (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact countSep) (by decide), memU]
    exact saved
  refine WP.seq (WP.mono (halfCountTail_ok (workspace.congr restUV.wr) readyV stackV countV
    (by rw [restUV.sp]; exact separate)) ?_)
  rintro t ⟨⟨memT, zeroT⟩, restT⟩
  have tailFrame : Frame [⟨State.addr (v.sp + 60#32), 4⟩] v.mem t.mem := by
    rw [memT]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  have equal : WorkspaceEq (State.addr base) (8 * capacity) v.mem t.mem :=
    WorkspaceEq.of_frame (by have := workspace.nowrap; omega_using [this]) tailFrame (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      rw [restUV.sp]
      exact countSep.symm)
  have numberT := (key_number_of_workspaceEq (workspace.congr restUV.wr) readyV equal (j := 29) (by decide)).trans valueV
  have rest := restUV.trans (restT.mono (by simp [opRegs]))
  have frameV' : Frame [⟨State.addr base, 8 * capacity⟩] s.mem v.mem := by rw [← memU]; exact frameV
  refine WP.block_nil ⟨readyV.rest restT (by decide) (by decide) (by decide), dataV.after_workspaceEq equal,
    numberT, ?_, ?_, ?_, ?_, (frameV'.mono (by simp)).trans (tailFrame.mono (by simp only [restUV.sp]; simp)), rest⟩
  · rw [restT.sp, memT, Mem.readW_writeW_self32]
  · rw [valueV] at zeroT
    exact zeroT
  · intro j bound different
    rw [key_number_of_workspaceEq (workspace.congr restUV.wr) readyV equal bound,
      keepV.num (j := j) (by simpa using different.symm) (by simp) (readyU.fit64 bound), memU]
  · intro d bound
    have fits := readyV.arrayFit (j := 0) (by decide)
    simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fits
    rw [equal.word (bits := 64) (by omega_using [bound, fits]), key_keep_header workspaceU readyU (by simp) bound keepV, memU]

end VG.Proof.Ffdh.Arm.ParameterCandidate
