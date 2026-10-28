module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontArrays
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontStride
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Compose the native RSA array view and compact-round header constants. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.Keys (num)
open VG.Spec.Rsa.Mont (numAt)

theorem montKeySetup_ok {s : State} {base : BitVec 32} {capacity k : Nat}
    (workspace : Workspace s base (8 * capacity))
    (data : MontData base capacity (Spec.Rsa.modulusWords k) s.mem)
    (minLength : 64 ≤ k) (maxLength : k ≤ 1024) (space : Spec.Rsa.scratchWords k ≤ capacity)
    (readBase : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (saved : s.mem.readW (State.addr s.sp) 32 = base)
    (rSmall : numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 1 ≤
      numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 0) :
    WP isa (.seq (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.keyContext ++
      VG.Impl.Ffdh.Arm.ParameterCandidate.keyStride)) VG.Impl.Ffdh.Arm.ParameterCandidate.montKeyArrays)
      s fun t =>
      KeyReady base capacity (Spec.Rsa.modulusWords k) t ∧
      MontData base capacity (Spec.Rsa.modulusWords k) t.mem ∧
      num t.mem (base + 96#32) (2 * Spec.Rsa.modulusWords k + 2) 0 =
        numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 9 =
        numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 1 ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 10 =
        numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 -
          numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 1 ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 =
        numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 ∧
      t.mem.readW (off (State.addr base) 224) 64 = BitVec.ofNat 64 (8 * (Spec.Rsa.modulusWords k + 2)) ∧
      (∀ j, j < 30 → j ∉ [0, 1, 9, 10] → numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) j =
        numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) j) ∧
      Frame [⟨State.addr base, 8 * capacity⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (keyContext_ready s workspace data minLength maxLength space readBase saved) ?_
  rintro u ⟨readyU, ptrU, memU, restU⟩
  have dataU : MontData base capacity (Spec.Rsa.modulusWords k) u.mem := memU ▸ data
  have workspaceU := workspace.congr restU.wr
  refine WP.mono (keyStride_ok workspaceU readyU dataU ptrU) ?_
  rintro v ⟨readyV, dataV, strideV, valuesV, frameV, restV⟩
  have frameV' : Frame [⟨State.addr base, 8 * capacity⟩] s.mem v.mem := by
    rw [← memU]
    refine frameV.sub ?_
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    refine ⟨⟨State.addr base, 8 * capacity⟩, by simp, Offset.sub_base _ ?_⟩
    have fit := readyU.arrayFit (j := 0) (by decide)
    simp only [Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fit
    omega
  have valueV (j : Nat) (bound : j < 35) : numAt v.mem (State.addr base) (Spec.Rsa.modulusWords k) j =
      numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) j := by rw [valuesV j bound, memU]
  refine WP.mono (montKeyArrays_ok (workspaceU.congr restV.wr) readyV dataV (by
    rw [valueV 1 (by decide), valueV 0 (by decide)]; exact rSmall)) ?_
  rintro t ⟨readyT, dataT, keepT, nT, _, rT, minusT, numberT, restT⟩
  rw [valueV 0 (by decide)] at nT numberT minusT
  rw [valueV 1 (by decide)] at rT minusT
  have frameT := key_keep_workspace (workspaceU.congr restV.wr) readyV (by simp) keepT
  have strideT := key_keep_header (workspaceU.congr restV.wr) readyV (by simp) (by decide : 224 + 8 ≤ 256) keepT
  refine ⟨readyT, dataT, nT, rT, minusT, numberT, strideT.trans strideV, ?_, frameV'.trans frameT,
    (restU.mono (by simp [roundClobbers])).trans ((restV.mono (by simp [roundClobbers])).trans
      (restT.mono (by simp [roundClobbers, VG.Proof.Rsa.Arm.Keys.opRegs])))⟩
  intro j bound outside
  have unchanged : ∀ a ∈ [0, 1, 9, 10], a ≠ j := by
    intro a member same
    exact outside (same ▸ member)
  rw [key_keep_number (workspaceU.congr restV.wr) readyV bound unchanged keepT, valueV j (by omega)]

end VG.Proof.Ffdh.Arm.ParameterCandidate
