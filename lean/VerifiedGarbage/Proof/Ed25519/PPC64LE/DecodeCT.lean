module

import VerifiedGarbage.Proof.Ed25519.PPC64LE.Decode
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ed25519.PPC64LE.FieldTest
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointTable
import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Decode
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.FieldTest
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointTable
meta import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.RecoverSign
public import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# Ed25519 on PPC64LE: a decoding leaks only its encoding

Two runs of `pointDecode` on the same encoding, with the same working space
and stack pointer, leak the same trace (`pointDecode_ct`). The taint analysis
(`taint_decide`) checks each piece between the branches: memory is secret to
it, so the branches on `r5` are related by correctness instead: in both runs
`r5` is zero exactly when the same fact about the encoding holds (`RelCT.ite`).
Each relation says that both runs satisfy the same predicate of public values
(`Both`), as ARMv7's proofs do.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P Fe)
open VG.Spec.Ed25519 (decodeLE bytesAt)
open VG.Proof.Ed25519 (rootU rootV rootX)

/-- Both runs satisfy `A`. -/
abbrev Both (A : State → Prop) (s₁ s₂ : State) : Prop := A s₁ ∧ A s₂

theorem ctBoth {A B : State → Prop} {c : Prog isa} (h : RelCT isa (Both A) c fun _ _ => True)
    (hw : ∀ s, A s → WP isa c s B) : RelCT isa (Both A) c (Both B) :=
  (h.wp (F₁ := B) (F₂ := B) fun _ _ hp => ⟨hw _ hp.1, hw _ hp.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- Code the taint analysis checks, with the registers of `rs` and `sp` agreeing. -/
theorem ctRegs (rs : List Reg) {A : State → Prop} {c : Prog isa}
    (hr : ∀ s₁ s₂, A s₁ → A s₂ → s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) {hc : Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa (Both A) c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ hp => ⟨(hr _ _ hp.1 hp.2).1, fun r h => (hr _ _ hp.1 hp.2).2 r (by simpa using h)⟩) h

theorem eval_zero_agree {s₁ s₂ : State} {r : Reg} {p : Prop} (h₁ : s₁.gpr r = 0 ↔ p) (h₂ : s₂.gpr r = 0 ↔ p) :
    isa.eval (.zero .d r) s₁ = isa.eval (.zero .d r) s₂ := by
  rw [eval_zero, eval_zero]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact h₁.trans h₂.symm

/-- The working space at `r6` and the stack pointer. -/
def Pin (b sp : Addr) (s : State) : Prop := Ctx8 b s ∧ s.sp = sp

theorem Pin.regs {b sp : Addr} {s₁ s₂ : State} (h₁ : Pin b sp s₁) (h₂ : Pin b sp s₂) :
    s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r6], s₁.gpr r = s₂.gpr r :=
  ⟨h₁.2.trans h₂.2.symm, fun r hr => by rw [List.mem_singleton.mp hr, h₁.1.r6, h₂.1.r6]⟩

theorem Pin.of_rest {b sp : Addr} {s t : State} {R : List Reg} (h : Pin b sp s) (hr : Rest R s t)
    (h6 : Reg.r6 ∉ R) : Pin b sp t :=
  ⟨h.1.of_rest hr h6, by rw [hr.sp, h.2]⟩

section
variable {b sp : Addr}

theorem recoverInvalid_ct : RelCT isa (Both (Pin b sp)) recoverInvalid fun _ _ => True :=
  ctRegs [.r6] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)

/-- Before the sign is applied: `x` in slot 0, the sign at `SIGN`. -/
def AdjPre (b sp : Addr) (x : Fe) (sg : Bool) (s : State) : Prop :=
  Pin b sp s ∧ env s.mem b 0 = x ∧ SignAt b sg s.mem

theorem recoverAdjust_ct (x : Fe) (sg : Bool) :
    RelCT isa (Both (AdjPre b sp x sg)) recoverAdjustSign fun _ _ => True := by
  unfold recoverAdjustSign
  have h1 := ctBoth (ctRegs [.r6] (A := AdjPre b sp x sg) (c := .block (freeze 0 ++ recoverParity))
    (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide))
    (B := fun t => Pin b sp t ∧ (t.gpr .r5 = 0 ↔ ((x.val % 2 == 1) == sg) = true)) fun s h =>
      WP.mono (adjParity_ok h.1.1 h.2.2) fun t ⟨k, _, e⟩ => ⟨h.1.of_rest k.rest (by decide), by rw [← h.2.1]; exact e⟩
  refine RelCT.seq h1 (RelCT.seq (Q := fun _ _ => True) (R := Both (Pin b sp))
    (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_) ?_)
  · exact RelCT.block_nil fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩
  · exact (ctBoth (ctRegs [.r6] (A := Pin b sp) (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide))
      fun s h => WP.mono (fieldCode_ok _ h.1.ctx) fun t ⟨k, _⟩ => h.of_rest k.rest (by decide)).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  · exact ctRegs [.r6] (fun _ _ h₁ h₂ => h₁.regs h₂) (by taint_decide)

theorem recoverSign_ct (x : Fe) (sg : Bool) :
    RelCT isa (Both (AdjPre b sp x sg)) recoverSign fun _ _ => True := by
  unfold recoverSign
  have h1 := ctBoth (ctRegs [.r6] (A := AdjPre b sp x sg) (c := fieldZero 0)
    (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide))
    (B := fun t => AdjPre b sp x sg t ∧ (t.gpr .r5 = 0 ↔ x = 0)) fun s h =>
      WP.mono (fieldZero_ok h.1.1.ctx 0) fun t ⟨r, f, e⟩ =>
        ⟨⟨h.1.of_rest r (by decide), by rw [env_FR f, h.2.1], h.2.2.frame (frame_FR f)⟩,
          by rw [e, ← h.2.1, Fin.ext_iff]; exact Iff.rfl⟩
  refine RelCT.seq h1 (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_)
  · unfold signTest
    have h2 := ctBoth (ctRegs [.r6] (A := AdjPre b sp x sg) (c := .block [.load .d .r5 .r6 SIGN])
      (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide))
      (B := fun t => AdjPre b sp x sg t ∧ t.gpr .r5 = BitVec.ofNat 64 sg.toNat) fun s h =>
        wp_ldd (a := b + BitVec.ofNat 64 SIGN) (by decide) (by decide) (by rw [h.1.1.r6])
          (h.1.1.ctx.inR (by decide)) fun t u => WP.block_nil
            ⟨⟨h.1.of_rest (u.rest (ws := [.r5]) (by decide)) (by decide), by rw [u.mem]; exact h.2.1,
              by rw [u.mem]; exact h.2.2⟩, by rw [u.gpr]; exact h.2.2⟩
    refine RelCT.seq (h2.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)
      (RelCT.ite (fun _ _ h => by rw [eval_nonzero, eval_nonzero, h.1.2, h.2.2]) ?_ ?_)
    · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) fun _ _ h => h
    · exact (recoverAdjust_ct x sg).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  · exact (recoverAdjust_ct x sg).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h

/-- Before the candidate: `y` in slot 1, the sign at `SIGN`. -/
def RPPre (b sp : Addr) (y : Fe) (sg : Bool) (s : State) : Prop :=
  Pin b sp s ∧ env s.mem b 1 = y ∧ SignAt b sg s.mem

theorem recoverPoint_ct (y : Fe) (sg : Bool) :
    RelCT isa (Both (RPPre b sp y sg)) recoverPoint fun _ _ => True := by
  unfold recoverPoint
  -- The candidate, and `v x²` against `u` and `-u`.
  let C (t : State) : Prop := Pin b sp t ∧ SignAt b sg t.mem ∧ env t.mem b 0 = rootX y ∧
    env t.mem b 11 = rootV y * rootX y * rootX y ∧ env t.mem b 6 = rootU y ∧ env t.mem b 12 = 0 - rootU y
  have h1 := ctBoth (ctRegs [.r6] (A := RPPre b sp y sg) (c := recoverCandidate)
    (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide)) (B := C) fun s h =>
      WP.mono (recoverCandidate_ok h.1.1) fun t ⟨k, x0, _, x6, _, x11, x12⟩ =>
        ⟨h.1.of_rest k.rest (by decide), h.2.2.frame k.frame, by rw [x0, h.2.1], by rw [x11, h.2.1],
          by rw [x6, h.2.1], by rw [x12, h.2.1]⟩
  have hC (t : State) (h : C t) {u : State} (k : Keep b t u) {c : Slot}
      (e : env u.mem b = evalOps [.sub 21 11 c] (env t.mem b)) : C u :=
    ⟨h.1.of_rest k.rest (by decide), h.2.1.frame k.frame, by rw [e]; exact h.2.2.1, by rw [e]; exact h.2.2.2.1,
      by rw [e]; exact h.2.2.2.2.1, by rw [e]; exact h.2.2.2.2.2⟩
  have h6 := ctBoth (ctRegs [.r6] (A := C) (c := fieldEqual 11 6) (fun _ _ h₁ h₂ => h₁.1.regs h₂.1)
    (by taint_decide)) (B := fun t => C t ∧ (t.gpr .r5 = 0 ↔ rootV y * rootX y * rootX y = rootU y)) fun s h =>
      WP.mono (fieldEqual_ok h.1.1.ctx 11 6) fun t ⟨k, e, z⟩ =>
        ⟨hC s h k e, by rw [z, h.2.2.2.1, h.2.2.2.2.1]⟩
  have h12 := ctBoth (ctRegs [.r6] (A := C) (c := fieldEqual 11 12) (fun _ _ h₁ h₂ => h₁.1.regs h₂.1)
    (by taint_decide)) (B := fun t => C t ∧ (t.gpr .r5 = 0 ↔ rootV y * rootX y * rootX y = 0 - rootU y))
      fun s h => WP.mono (fieldEqual_ok h.1.1.ctx 11 12) fun t ⟨k, e, z⟩ =>
        ⟨hC s h k e, by rw [z, h.2.2.2.1, h.2.2.2.2.2]⟩
  have hA (t : State) (h : C t) : AdjPre b sp (rootX y) sg t := ⟨h.1, h.2.2.1, h.2.1⟩
  refine RelCT.seq h1 (RelCT.seq h6 (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_))
  · exact (recoverSign_ct (rootX y) sg).mono (fun _ _ h => ⟨hA _ h.1.1.1, hA _ h.1.2.1⟩) fun _ _ h => h
  refine RelCT.seq (h12.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)
    (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_)
  · have hF := ctBoth (ctRegs [.r6] (A := C) (c := fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mulc 0 0 18])
      (fun _ _ h₁ h₂ => h₁.1.regs h₂.1) (by taint_decide))
      (B := AdjPre b sp (rootX y * Spec.Ed25519.sqrtM1) sg) fun s h =>
        WP.mono (fieldCode_ok _ h.1.1.ctx) fun t ⟨k, e⟩ =>
          ⟨h.1.of_rest k.rest (by decide), by rw [e, ← h.2.2.1]; rfl, h.2.1.frame k.frame⟩
    exact RelCT.seq (hF.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h) (recoverSign_ct _ sg)
  · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) fun _ _ h => h

/-- Before a decoding: the encoding `bs` at `r14`. -/
def DecPre (b sp q : Addr) (bs : List Byte) (s : State) : Prop :=
  Pin b sp s ∧ s.gpr .r14 = q ∧ (∀ k < 8, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (0 + 4 * k)) 4) ∧
    (⟨q + BitVec.ofNat 64 0, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 (offset 1), 32⟩ ∧ bytesAt s.mem q 32 = bs

/-- **A decoding leaks only its encoding.** -/
theorem pointDecode_ct (q : Addr) (bs : List Byte) :
    RelCT isa (Both (DecPre b sp q bs)) pointDecode fun _ _ => True := by
  unfold pointDecode
  have h1 := ctBoth (ctRegs [.r6, .r14] (A := DecPre b sp q bs) (c := pointDecodeLoad)
    (fun _ _ h₁ h₂ => ⟨h₁.1.2.trans h₂.1.2.symm, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.1.r6, h₂.1.1.r6]
      · rw [h₁.2.1, h₂.2.1]⟩) (by taint_decide))
    (B := fun t => RPPre b sp (Proof.X25519.toFe (decodeLE bs % 2 ^ 255)) (decodeLE bs / 2 ^ 255 == 1) t ∧
      (t.gpr .r5 = 0 ↔ decodeLE bs % 2 ^ 255 < P)) fun s h =>
      WP.mono (pointDecodeLoad_ok h.1.1 h.2.1 h.2.2.1 h.2.2.2.1) fun t ⟨k, sg, y, z⟩ => by
        rw [h.2.2.2.2] at sg y z
        exact ⟨⟨h.1.of_rest k.rest (by decide), y, sg⟩, z⟩
  refine RelCT.seq h1 (RelCT.ite (fun _ _ h => eval_zero_agree h.1.2 h.2.2) ?_ ?_)
  · exact (recoverPoint_ct _ _).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  · exact recoverInvalid_ct.mono (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) fun _ _ h => h

end

end VG.Proof.Ed25519.PPC64LE
