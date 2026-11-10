module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowHalf
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowCopyCT
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWideCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.SubModArray
import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperand
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # Reducing a full-width number in the narrow workspace is constant-time -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)

/-- The narrow workspace prepared for a modulus `M`, and a full-width one to copy from. -/
def CrtHalfReady (g : CrtGeometry) (bs : Fin 7 → List Byte) (child : BitVec 32) (slot v M : Nat)
    (s : State) : Prop :=
  CrtCopyCtx g bs child slot v s ∧ numAt s.mem (State.addr (crtN g.base g.words)) v 0 = M ∧ M % 2 = 1 ∧
    numAt s.mem (State.addr (crtN g.base g.words)) v 4 = 2 ^ (128 * v) % M ∧ g.words ≤ 2 * v

theorem CrtHalfReady.after {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v M o : Nat} {rs : List Reg} (h : CrtHalfReady g bs child slot v M s)
    (ready : ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t)
    (keeps : Keeps (State.addr (crtN g.base g.words)) (workspaceWords g.words) v o s.mem t.mem)
    (ho : o = 1 ∨ o = 5 ∨ o = 6 ∨ o = 7)
    (frame : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem)
    (rest : Rest rs s t) : CrtHalfReady g bs child slot v M t := by
  have fits : arrAt v 8 ≤ 8 * workspaceWords g.words := h.1.ready.width ▸ h.1.ready.layout.2.2.1
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  exact ⟨h.1.after_narrow ready frame rest,
    (keeps_array_num keeps fits op0 (by omega)).trans h.2.1, h.2.2.1,
    (keeps_array_num keeps fits op4 (by omega)).trans h.2.2.2.1, h.2.2.2.2⟩

theorem CrtHalfReady.r2_lt {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v M : Nat} (h : CrtHalfReady g bs child slot v M s) :
    numAt s.mem (State.addr (crtN g.base g.words)) v 4 < numAt s.mem (State.addr (crtN g.base g.words)) v 0 := by
  have positive := h.1.ready.modulus
  rw [h.2.1] at positive ⊢
  rw [h.2.2.2.1]
  exact Nat.mod_lt _ (by omega)

theorem crt_reduceHalf_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {child : BitVec 32}
    {slot v j M1 M2 : Nat} (hj : j < 8) :
    RelCT isa (fun s t => CrtHalfReady g bs1 child slot v M1 s ∧ CrtHalfReady g bs2 child slot v M2 t ∧ s.sp = t.sp)
      (reduceHalf slot j) (fun _ _ => True) := by
  let N := State.addr (crtN g.base g.words)
  let H := fun (bs : Fin 7 → List Byte) (M : Nat) (s : State) => CrtHalfReady g bs child slot v M s
  let H3 := fun (bs : Fin 7 → List Byte) (M : Nat) (s : State) => H bs M s ∧ numAt s.mem N v 7 = 1
  let H4 := fun (bs : Fin 7 → List Byte) (M : Nat) (s : State) => H3 bs M s ∧ numAt s.mem N v 1 < numAt s.mem N v 0
  let H5 := fun (bs : Fin 7 → List Byte) (M : Nat) (s : State) => H4 bs M s ∧ numAt s.mem N v 5 = 0
  let R := fun (s : State) => ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s
  have op : ∀ q, q = 0 ∨ q = 1 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 → Operand q := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have fits (s : State) {bs : Fin 7 → List Byte} {M : Nat} (h : H bs M s) :
      arrAt v 8 ≤ 8 * workspaceWords g.words := h.1.ready.width ▸ h.1.ready.layout.2.2.1
  have hv (s : State) {bs : Fin 7 → List Byte} {M : Nat} (h : H bs M s) : 2 ≤ v := h.1.ready.width ▸ h.1.ready.layout.1
  -- The steps' preconditions in each run.
  have w1 (s : State) {bs : Fin 7 → List Byte} {M : Nat} (h : H bs M s) :
      WP isa (clearOperandBuffer 72) s (H bs M) :=
    (clearArrayWide_ok s h.1.ready (o := 1) (by decide) (by decide)).mono
      fun _ k => h.after k.1 k.2.2.1 (by simp) k.2.2.2.1 k.2.2.2.2
  have w2 (s : State) {bs : Fin 7 → List Byte} {M : Nat} (h : H bs M s) : WP isa (copyHigh slot j 1) s (H bs M) :=
    (crt_copyHigh_ok s h.1 hj (by decide) (by decide) h.2.2.2.2).mono
      fun _ k => h.after k.1 k.2.2.1 (by simp) k.2.2.2.1 k.2.2.2.2
  have w3 (s : State) {bs : Fin 7 → List Byte} {M : Nat} (h : H bs M s) : WP isa (smallConst 7 1) s (H3 bs M) :=
    (smallConst_ok s (o := 7) 1 h.1.ready (by decide) (by decide) (by decide) (by decide)).mono
      fun _ k => ⟨h.after k.1 k.2.2.2.1 (by simp) k.2.2.2.2.1 k.2.2.2.2.2, k.2.1⟩
  have w4 (s : State) {bs : Fin 7 → List Byte} {M : Nat} (h : H3 bs M s) : WP isa (montOp 1 1 4) s (H4 bs M) := by
    refine (montOp_ok s h.1.1.ready (op 1 (by simp)) (op 1 (by simp)) (op 4 (by simp)) (by decide) h.1.r2_lt).mono ?_
    rintro t ⟨ready, mod, bound, _, keeps, frame, rest⟩
    exact ⟨⟨h.1.after ready keeps (by simp) frame rest,
      (keeps_array_num keeps (fits s h.1) (op 7 (by simp)) (by decide)).trans h.2⟩, by rw [mod]; exact bound⟩
  have w5 (s : State) {bs : Fin 7 → List Byte} {M : Nat} (h : H4 bs M s) : WP isa (clearOperandBuffer 104) s (H5 bs M) := by
    refine (clearArrayWide_ok s h.1.1.1.ready (o := 5) (by decide) (by decide)).mono ?_
    rintro t ⟨ready, cleared, keeps, frame, rest⟩
    have mod := keeps_array_num keeps (fits s h.1.1) (op 0 (by simp)) (by decide)
    exact ⟨⟨⟨h.1.1.after ready keeps (by simp) frame rest,
      (keeps_array_num keeps (fits s h.1.1) (op 7 (by simp)) (by decide)).trans h.1.2⟩,
      by rw [mod, keeps_array_num keeps (fits s h.1.1) (op 1 (by simp)) (by decide)]; exact h.2⟩,
      numAt_of_cleared cleared⟩
  have w6 (s : State) {bs : Fin 7 → List Byte} {M : Nat} (h : H5 bs M s) : WP isa (subModArray 6 5 1) s (H3 bs M) := by
    refine (subModArray_ok s h.1.1.1.1.ready (o := 6) (a := 5) (b := 1) (op 6 (by simp)) (op 5 (by simp))
      (op 1 (by simp)) (by decide) (by decide) (by decide)
      (by rw [h.2]; have := h.1.1.1.1.ready.modulus; omega) h.1.2).mono ?_
    rintro t ⟨ready, _, keeps, frame, rest⟩
    exact ⟨h.1.1.1.after ready keeps (by simp) frame rest,
      (keeps_array_num keeps (fits s h.1.1.1) (op 7 (by simp)) (by decide)).trans h.1.1.2⟩
  have w7 (s : State) {bs : Fin 7 → List Byte} {M : Nat} (h : H3 bs M s) : WP isa (copyLow slot j 5) s (H3 bs M) := by
    refine (crt_copyLow_ok s h.1.1 hj (by decide) (by decide)).mono ?_
    rintro t ⟨ready, _, keeps, frame, rest⟩
    exact ⟨h.1.after ready keeps (by simp) frame rest,
      (keeps_array_num keeps (fits s h.1) (op 7 (by simp)) (by decide)).trans h.2⟩
  have w8 (s : State) {bs : Fin 7 → List Byte} {M : Nat} (h : H3 bs M s) : WP isa (reduceOperand 5) s R :=
    (reduceOperand_ok s h.1.1.ready (op 5 (by simp)) (by decide) (by decide) h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.2).mono
      fun _ k => k.1
  -- Each step in both runs.
  have size : ∀ (s : State) {bs : Fin 7 → List Byte} {M : Nat}, H bs M s → 128 ≤ 8 * workspaceWords g.words := by
    intro s bs M h
    have := fits s h
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega
  have fit3 : ∀ (s : State) {bs : Fin 7 → List Byte} {M : Nat}, H bs M s →
      arrAt v 3 + 32 ≤ 8 * workspaceWords g.words := by
    intro s bs M h
    have := Nat.le_trans (array_end_le (w := v) (by decide : 3 < 8)) (fits s h)
    have := hv s h
    omega
  intro s₁ s₂ tr1 tr2 u₁ u₂ hh e1 e2
  have sz := size s₁ hh.1
  have f3 := fit3 s₁ hh.1
  have c9 : RelCT isa (fun s t => R s ∧ R t ∧ s.sp = t.sp) (subModArray 1 5 6) (fun _ _ => True) :=
    subModArray_ct (by decide) (by decide) (by decide) (by decide) sz
  have c8 : RelCT isa (fun s t => H3 bs1 M1 s ∧ H3 bs2 M2 t ∧ s.sp = t.sp) (reduceOperand 5) (fun _ _ => True) :=
    (reduceOperand_ct (op 5 (by simp)) (by decide) (by decide) f3).mono
      (fun s t h => ⟨⟨h.1.1.1.ready, h.1.1.r2_lt, by rw [h.1.2]; exact h.1.1.1.ready.modulus⟩,
        ⟨h.2.1.1.1.ready, h.2.1.1.r2_lt, by rw [h.2.1.2]; exact h.2.1.1.1.ready.modulus⟩, h.2.2⟩)
      (fun _ _ _ => trivial)
  have c7 : RelCT isa (fun s t => H3 bs1 M1 s ∧ H3 bs2 M2 t ∧ s.sp = t.sp) (copyLow slot j 5) (fun _ _ => True) :=
    (crt_copyLow_ct hj (by decide)).mono (fun _ _ h => ⟨h.1.1.1, h.2.1.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have c6 : RelCT isa (fun s t => H5 bs1 M1 s ∧ H5 bs2 M2 t ∧ s.sp = t.sp) (subModArray 6 5 1) (fun _ _ => True) :=
    (subModArray_ct (by decide) (by decide) (by decide) (by decide) sz).mono
      (fun _ _ h => ⟨h.1.1.1.1.1.ready, h.2.1.1.1.1.1.ready, h.2.2⟩) (fun _ _ _ => trivial)
  have c5 : RelCT isa (fun s t => H4 bs1 M1 s ∧ H4 bs2 M2 t ∧ s.sp = t.sp) (clearOperandBuffer (64 + 8 * 5))
      (fun _ _ => True) :=
    (clearArrayWide_ct (by decide) sz).mono (fun _ _ h => ⟨h.1.1.1.1.ready, h.2.1.1.1.1.ready, h.2.2⟩)
      (fun _ _ _ => trivial)
  have c4 : RelCT isa (fun s t => H3 bs1 M1 s ∧ H3 bs2 M2 t ∧ s.sp = t.sp) (montOp 1 1 4) (fun _ _ => True) :=
    (montOp_ct (op 1 (by simp)) (op 1 (by simp)) (op 4 (by simp)) f3).mono
      (fun _ _ h => ⟨⟨h.1.1.1.ready, h.1.1.r2_lt⟩, ⟨h.2.1.1.1.ready, h.2.1.1.r2_lt⟩, h.2.2⟩) (fun _ _ _ => trivial)
  have c3 : RelCT isa (fun s t => H bs1 M1 s ∧ H bs2 M2 t ∧ s.sp = t.sp) (smallConst 7 1) (fun _ _ => True) :=
    (smallConst_ct (o := 7) 1 (by decide) (by decide) (by decide)).mono
      (fun _ _ h => ⟨h.1.1.ready, h.2.1.1.ready, h.2.2⟩) (fun _ _ _ => trivial)
  have c2 : RelCT isa (fun s t => H bs1 M1 s ∧ H bs2 M2 t ∧ s.sp = t.sp) (copyHigh slot j 1) (fun _ _ => True) :=
    (crt_copyHigh_ct hj (by decide)).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have c1 : RelCT isa (fun s t => H bs1 M1 s ∧ H bs2 M2 t ∧ s.sp = t.sp) (clearOperandBuffer (64 + 8 * 1))
      (fun _ _ => True) :=
    (clearArrayWide_ct (by decide) sz).mono (fun _ _ h => ⟨h.1.1.ready, h.2.1.1.ready, h.2.2⟩) (fun _ _ _ => trivial)
  have all := crt_seq_ct c1 (fun s h => w1 s h) (fun s h => w1 s h)
    (crt_seq_ct c2 (fun s h => w2 s h) (fun s h => w2 s h)
      (crt_seq_ct c3 (fun s h => w3 s h) (fun s h => w3 s h)
        (crt_seq_ct c4 (fun s h => w4 s h) (fun s h => w4 s h)
          (crt_seq_ct c5 (fun s h => w5 s h) (fun s h => w5 s h)
            (crt_seq_ct c6 (fun s h => w6 s h) (fun s h => w6 s h)
              (crt_seq_ct c7 (fun s h => w7 s h) (fun s h => w7 s h)
                (crt_seq_ct c8 (fun s h => w8 s h) (fun s h => w8 s h) c9)))))))
  exact all s₁ s₂ tr1 tr2 u₁ u₂ hh e1 e2

end VG.Proof.Bignum.Arm
