module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyOps
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CountTail
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

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
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
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
    WorkspaceEq.of_frame (by have := workspace.nowrap; omega) tailFrame (by
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
    rw [equal.word (bits := 64) (by omega), key_keep_header workspaceU readyU (by simp) bound keepV, memU]

end VG.Proof.Ffdh.Arm.ParameterCandidate
