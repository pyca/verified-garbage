module

public import VerifiedGarbage.Impl.Ffdh.Arm.Arithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.PcStack
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady

import VerifiedGarbage.Proof.Ffdh.Arm.CandidatePrepare
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontArrays
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontStride
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Impl.Bignum.Arm.MontOp
import VerifiedGarbage.Impl.Bignum.Arm.R2
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.MontEncode
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
/-! Complete native Montgomery preparation for each safe-prime phase,
composing the same arithmetic and array routines that RSA uses. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/MontKeySetup.lean`, which only this module imported.
section

/-! Compose the native RSA array view and compact-round header constants. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.Keys (num)
open VG.Proof.Rsa.Mont (numAt)

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
    simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fit
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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/MontOne.lean`, which only this module imported.
section

/-! Reuse RSA's Montgomery encoding proof to produce the compact round's
representation of one. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem montOne_ok {s : State} {base : BitVec 32} {capacity w n : Nat}
    (ready : ArithmeticReady base capacity w s)
    (modulus : numAt s.mem (State.addr base) w 0 = n) (odd : n % 2 = 1)
    (r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % n) :
    WP isa (.seq (VG.Impl.Bignum.Arm.smallConst 1 1) (VG.Impl.Bignum.Arm.montOp 1 1 4)) s fun t =>
      ArithmeticReady base capacity w t ∧ numAt t.mem (State.addr base) w 0 = n ∧
      numAt t.mem (State.addr base) w 1 = 2 ^ (64 * w) % n ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % n ∧
      Frame [⟨State.addr base, 8 * capacity⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * capacity := ready.width ▸ ready.layout.2.2.1
  have op (j : Nat) (bound : j = 0 ∨ j = 1 ∨ j = 4) : Operand j := by
    rcases bound with rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [WP.seq_iff]
  refine WP.mono (smallConst_ok s 1 ready (o := 1) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨readyU, oneU, _, keepsU, frameU, restU⟩
  change numAt u.mem (State.addr base) w 1 = 1 at oneU
  have modulusU := (keeps_array_num keepsU fits (op 0 (by simp)) (by decide)).trans modulus
  have r2U := (keeps_array_num keepsU fits (op 4 (by simp)) (by decide)).trans r2
  refine WP.mono (montEncode_ok u readyU (op 1 (by simp)) (op 1 (by simp)) (by decide)
    modulusU odd r2U) ?_
  rintro t ⟨readyT, modulusT, oneT, keepsT, frameT, restT⟩
  rw [oneU, Nat.one_mul] at oneT
  exact ⟨readyT, modulusT, oneT, (keeps_array_num keepsT fits (op 4 (by simp)) (by decide)).trans r2U,
    frameU.trans frameT, restU.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (numAt)

structure MontPrepInput (base src : BitVec 32) (capacity k : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * capacity)
  stack : PcStack base (s.mem.readW (off (State.addr s.sp) 4) 32) src capacity k s
  minLength : 64 ≤ k
  maxLength : k ≤ 1024
  space : Spec.Rsa.publicScratchWords k ≤ capacity
  sourceFits : src.toNat + k ≤ Nat.pow 2 32
  readable : InRegions (s.rd ++ s.wr) (State.addr src) k
  separate : (⟨State.addr src, k⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩
  large : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)
  odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) % 2 = 1
  normalized : k % 8 = 1 ∨ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)


private theorem prepareHead_ok {s : State} {base src : BitVec 32} {capacity k : Nat}
    (h : MontPrepInput base src capacity k s) :
    WP isa (.block [.ldrSp .r0 0, .ldrSp .r6 12]) s fun t =>
      (t.gpr .r0 = base ∧ t.gpr .r6 = BitVec.ofNat 32 k ∧ t.mem = s.mem) ∧ Rest [.r0, .r6] s t := by
  have read0 := h.stack.read (d := 0) (by decide)
  simp only [off, BitVec.add_zero] at read0
  have read12 := h.stack.read (d := 12) (by decide)
  have addr12 : State.addr (s.sp + 12#32) = off (State.addr s.sp) 12 :=
    VG.Arm.addr_add (by have := h.stack.nowrap; omega)
  refine withRest_all [.r0, .r6] ?_ (by rfl) (by rfl)
  ffrun [BitVec.add_zero, addr12, read0, read12, h.stack.savedBase, h.stack.savedCount]

theorem montPrep_ok {s : State} {base src : BitVec 32} {capacity k : Nat}
    (h : MontPrepInput base src capacity k s) (space : Spec.Rsa.scratchWords k ≤ capacity) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.montPrep s fun t =>
      KeyReady base capacity (Spec.Rsa.modulusWords k) t ∧
      MontData base capacity (Spec.Rsa.modulusWords k) t.mem ∧
      VG.Proof.Rsa.Arm.Keys.num t.mem (base + 96#32) (2 * Spec.Rsa.modulusWords k + 2) 0 =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 9 =
        Nat.pow 2 (64 * Spec.Rsa.modulusWords k) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 10 =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) -
          Nat.pow 2 (64 * Spec.Rsa.modulusWords k) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 4 =
        Nat.pow 2 (128 * Spec.Rsa.modulusWords k) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      t.mem.readW (off (State.addr base) 224) 64 = BitVec.ofNat 64 (8 * (Spec.Rsa.modulusWords k + 2)) ∧
      Frame [⟨State.addr base, 8 * capacity⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.montPrep, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (prepareHead_ok h) ?_)
  rintro u ⟨⟨ptrU, countU, memU⟩, restU⟩
  have inputU : PrepareInput base src capacity k u := by
    refine ⟨h.workspace.congr restU.wr, ?_, ptrU, countU, h.minLength, h.maxLength,
      h.space, h.sourceFits, ?_, h.separate, ?_, ?_⟩
    · have frame : Frame [⟨State.addr base, 8 * capacity⟩] s.mem u.mem := by rw [memU]; exact Frame.refl _ _
      simpa only [memU, restU.sp] using h.stack.after_workspace frame restU
    · rw [restU.rd, restU.wr]; exact h.readable
    · rw [memU]; exact h.large
    · rw [memU]; exact h.odd
  refine WP.seq (WP.mono (candidatePrepare_ok u inputU (by rw [memU]; exact h.normalized)) ?_)
  rintro v ⟨readyV, nV, r2V, frameV, restV⟩
  rw [memU] at nV r2V frameV
  refine WP.seq (WP.mono (montOne_ok readyV nV h.odd r2V) ?_)
  rintro a ⟨readyA, nA, rA, r2A, frameA, restA⟩
  refine WP.seq (WP.mono (montKeySetup_ok readyA.workspace (MontData.of_ready readyA)
    h.minLength h.maxLength space readyA.stackRead readyA.saved (by
      rw [nA, rA]
      exact Nat.le_of_lt (Nat.mod_lt _ (by have := h.large; omega)))) ?_)
  rintro t ⟨readyT, dataT, nT, rT, minusT, numberT, strideT, arraysT, frameT, restT⟩
  rw [nA] at nT minusT numberT
  rw [rA] at rT minusT
  exact WP.block_nil ⟨readyT, dataT, nT, rT, minusT, numberT,
    (arraysT 4 (by decide) (by decide)).trans r2A, strideT,
    frameV.trans (frameA.trans frameT), (restU.mono (by simp [roundClobbers])).trans
      (restV.trans (restA.trans restT))⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
