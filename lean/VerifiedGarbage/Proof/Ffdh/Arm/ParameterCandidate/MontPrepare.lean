module

import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
public import VerifiedGarbage.Impl.Ffdh.Arm.Arithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.PcStack
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Rsa.Mont
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontKeySetup
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontOne
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Complete native Montgomery preparation for each safe-prime phase,
composing the same arithmetic and array routines that RSA uses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Spec.Rsa.Mont (numAt)

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


private theorem prepareHead_ok {s : State} {base src : BitVec 32} {capacity k : Nat}
    (h : MontPrepInput base src capacity k s) :
    WP isa (.block [.ldrSp .r0 0, .ldrSp .r6 12]) s fun t =>
      (t.gpr .r0 = base ∧ t.gpr .r6 = BitVec.ofNat 32 k ∧ t.mem = s.mem) ∧ Rest [.r0, .r6] s t := by
  have read0 := h.stack.read (d := 0) (by decide)
  simp only [off, BitVec.add_zero] at read0
  have read12 := h.stack.read (d := 12) (by decide)
  have addr12 : State.addr (s.sp + 12#32) = off (State.addr s.sp) 12 :=
    VG.Arm.addr_add (by have := h.stack.nowrap; omega)
  refine withRest [.r0, .r6] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block [.ldrSp .r0 0, .ldrSp .r6 12] : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have x := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
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
  refine WP.seq (WP.mono (prepare_ok u inputU) ?_)
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
