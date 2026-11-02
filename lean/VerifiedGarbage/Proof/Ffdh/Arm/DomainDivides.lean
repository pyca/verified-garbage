module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecks
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperand
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! Divisibility is checked by reducing the full-width p modulo q. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

theorem domainDivides_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots)
    (hasQ : p.hasQ = true) (large : 1 < p.Q) (odd : p.Q % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckDomain.divides s fun t => Context p slots t ∧
      t.gpr .r11 = (if p.P % p.Q = 1 then 1 else 0) ∧
      Frame (prepareAtWrites p s) s.mem t.mem ∧ VG.Proof.X25519.Arm.Rest roundClobbers s t := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have qStack : Region.Disjoint ⟨State.addr p.q, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.toArgumentMemory.domainSliceStack (by have := p.minLength; omega)
      (by rw [p.domainLength, hasQ]; simp only [ite_true]; omega)
  rw [VG.Impl.Ffdh.Arm.Domain.CheckDomain.divides, WP.seq_iff]
  refine WP.mono (prepareAt_ok s 60 h stable h60 h32 h0 (h.qBytes hasQ) (p.qLength hasQ) qStack large odd) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok u 1 24 32 contextU stable h24 h32 readyU (by decide) (by decide) contextU.pBytes
    (by rw [p.pLength]; have := p.minLength; omega) (by rw [p.pLength]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.k = _; rw [p.pLength])) ?_
  rintro v ⟨_, readyV, valueV, keepsV, frameV, restV⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := readyV.width ▸ readyV.layout.2.2.1
  have modV := (keeps_array_num keepsV fits op0 (by decide)).trans modU
  have r2V := (keeps_array_num keepsV fits op4 (by decide)).trans r2U
  rw [WP.seq_iff]
  refine WP.mono (smallConst_ok v 1 readyV (by decide : 7 < 8) (by decide) (by decide) (by decide)) ?_
  rintro w ⟨readyW, one, _, keepsW, frameW, restW⟩
  have modW := (keeps_array_num keepsW fits op0 (by decide)).trans modV
  have r2W := (keeps_array_num keepsW fits op4 (by decide)).trans r2V
  rw [WP.seq_iff]
  refine WP.mono (reduceOperand_ok w readyW op1 (by decide) (by decide) modW odd r2W one) ?_
  rintro x ⟨readyX, _, reduced, _, frameX, restX⟩
  rw [keeps_array_num keepsW fits op1 (by decide), valueV] at reduced
  refine WP.mono (isOne_ok x readyX op1 (by decide)) ?_
  rintro t ⟨readyT, flag, _, frameT, restT⟩
  rw [reduced] at flag
  have frame : Frame (prepareAtWrites p s) s.mem t.mem := by
    have work := ((frameV.trans frameW).trans frameX).trans frameT
    exact frameU.trans (work.mono (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact List.mem_cons_self))
  have rest := (((restU.trans restV).trans restW).trans restX).trans restT
  have contextT : Context p slots t := by
    have frameWork := ((frameV.trans frameW).trans frameX).trans frameT
    exact contextU.after_workspace frameWork (((restV.trans restW).trans restX).trans restT) readyT.ptr
      (fun d hd => (stableSlots_at stable hd).1)
  exact ⟨contextT, flag, frame, rest⟩

end VG.Proof.Ffdh.Arm
