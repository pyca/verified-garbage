module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CountLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyOps
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SaveWord
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Initialize the native decomposition with N−1 and a zero halving count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.Keys (num opRegs)

theorem expCountInit_ok {s : State} {base : BitVec 32} {capacity w n : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (data : MontData base capacity w s.mem) (stack : Workspace s s.sp 72)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (number : num s.mem (base + 96#32) (2 * w + 2) 0 = n) (large : 1 < n) (odd : n % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.expCountInit s
      (CountInv s base capacity w (n - 1) 0 (n - 1)) := by
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.expCountInit, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (keyCopy_ok workspace ready (o := 29) (a := 0) (by decide) (by decide) (by decide)) ?_)
  rintro u ⟨readyU, keepU, numberU, restU⟩
  rw [number] at numberU
  have workspaceU := workspace.congr restU.wr
  refine WP.seq (WP.mono (keyClrLow_ok workspaceU readyU (j := 29) (by decide)) ?_)
  rintro v ⟨readyV, keepV, numberV, restV⟩
  rw [numberU] at numberV
  have valueV : num v.mem (base + 96#32) (2 * w + 2) 29 = n - 1 := by omega
  have restUV := restU.trans restV
  have workspaceV := workspace.congr restUV.wr
  have stackV : Workspace v v.sp 72 := by rw [restUV.sp]; exact stack.congr restUV.wr
  have keep := keepU.trans keepV
  have frameV := key_keep_workspace workspace ready (by simp) keep
  have dataV := (data.after_key_keep workspace ready (by simp) (by simp) keep).1
  refine WP.seq (WP.mono (saveWord_ok stackV (d := 60) (by decide) 0#32 (by decide)) ?_)
  rintro t ⟨memT, restT⟩
  have equal : WorkspaceEq (State.addr base) (8 * capacity) v.mem t.mem := by
    rw [memT]
    exact stackWrite_workspaceEq workspaceV stackV (by rw [restUV.sp]; exact separate) (by decide) _
  have frameT : Frame [⟨State.addr (s.sp + 60#32), 4⟩] v.mem t.mem := by
    rw [memT, restUV.sp]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  have rest : Rest opRegs s t := restUV.trans (restT.mono (by simp [opRegs]))
  refine WP.block_nil ⟨workspace.congr rest.wr, readyV.rest restT (by decide) (by decide) (by decide),
    dataV.after_workspaceEq equal, ?_, ?_, ?_, by omega, by omega, by simp, rfl, ?_, ?_, ?_,
    (frameV.mono (by simp)).trans (frameT.mono (by simp)), rest⟩
  · rw [rest.sp]; exact stack.congr rest.wr
  · rw [rest.sp]; exact separate
  · exact (key_number_of_workspaceEq workspaceV readyV equal (j := 29) (by decide)).trans valueV
  · rw [restT.sp, memT, Mem.readW_writeW_self32]
  · intro j bound different
    rw [key_number_of_workspaceEq workspaceV readyV equal bound,
      keep.num (j := j) (by simpa using different.symm) (by simp) (ready.fit64 bound)]
  · intro d bound
    have fits := readyV.arrayFit (j := 0) (by decide)
    simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fits
    rw [equal.word (bits := 64) (by omega), key_keep_header workspace ready (by simp) bound keep]

end VG.Proof.Ffdh.Arm.ParameterCandidate
