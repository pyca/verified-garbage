module

public import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationTrace
public import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Omega

/-! # Calls of the shared public-key validator -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.PublicValidation
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.PublicValidation
open VG.Proof.X25519.Arm (Rest wp_mov wp_movw wp_ldr op2_reg)

theorem head_ok {s : State} {base : Addr} {size : Nat} (W : Ws s base size) (big : 68 ≤ size)
    (pLen qLen : Nat) :
    WP isa (.block [.mov .r11 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 2048,
      .ldr .r2 .r12 (Impl.Dsa.Arm.Layout.field .p), .movw .r3 (BitVec.ofNat 16 (3 * pLen + qLen))]) s
      fun u => u.gpr .r11 = s.gpr .r12 ∧ u.gpr .r0 = s.gpr .r12 ∧
        Rest [.r0, .r1, .r2, .r3, .r11] s u ∧ u.mem = s.mem := by
  refine wp_mov (op2_reg s .r12) fun s₁ U₁ => wp_mov (op2_reg s₁ .r12) fun s₂ U₂ =>
    wp_movw fun s₃ U₃ => ?_
  have W₃ := ((W.of_upd U₁ (by decide)).of_upd U₂ (by decide)).of_upd U₃ (by decide)
  refine wp_ldr (by decide) (W₃.ea12 (by change 64 < size; omega)) (W₃.read (by exact big)) fun s₄ U₄ => wp_movw fun u U₅ => WP.block_nil ?_
  exact ⟨by rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide), U₁.gpr],
    by rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide), U₂.gpr, U₁.other _ (by decide)],
    ((((U₁.rest (by decide)).trans (U₂.rest (by decide))).trans (U₃.rest (by decide))).trans
      (U₄.rest (by decide))).trans (U₅.rest (by decide)), by rw [U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]⟩

theorem call_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Impl.Dsa.Arm.PublicValidation.call pLen qLen) s fun t =>
      maskW base t = maskW base s &&& VG.Proof.Ecdsa.Arm.mask32 (publicChecks P Q G Y) ∧
      localVal base t Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 ∧ Run base s t := by
  unfold Impl.Dsa.Arm.PublicValidation.call
  refine WP.seq (WP.mono (head_ok S.ws (by have := S.big; omega) pLen qLen) fun u ⟨h11, h0, R, M⟩ => ?_)
  have E : Pow.Entry u.callEntry base size :=
    ⟨by rw [State.callEntry_gpr _ (by decide), h0, S.ws.wb], by rw [State.callEntry_wr, R.wr]; exact S.ws.wr,
      S.ws.nowrap⟩
  have Mu : u.callEntry.mem = s.mem := M
  have Ru : u.callEntry.rd = s.rd := R.rd
  have Wu : u.callEntry.wr = s.wr := R.wr
  obtain ⟨tr, v, Ex, F, V, O, Regs, SP, RD, WR⟩ := body_ok E S.big S.wp S.wq S.qp S.q32
    (input_mem Ip Mu Ru Wu) (input_mem Iq Mu Ru Wu) (input_mem Ig Mu Ru Wu) (input_mem Iy Mu Ru Wu)
    hP hPo hQ hQo
  have Ret : isa.ret u.callEntry v = some v := by
    have L := Regs .lr (by decide)
    simp only [isa, ret, L, ite_true]
  have v11 : v.gpr .r11 = s.gpr .r12 := by rw [Regs _ (by decide), State.callEntry_gpr _ (by decide), h11]
  refine WP.seq ⟨_, v, .call (call_callEntry u) Ex Ret,
    wp_mov (op2_reg v .r11) fun t U => WP.block_nil ⟨?_, ?_, ?_⟩⟩
  · rw [show maskW base t = maskW base v from congrArg (fun m => m.readW (off base 116) 32) U.mem, F]
    rw [show maskW base u.callEntry = maskW base s from congrArg (fun m => m.readW (off base 116) 32) Mu]
  · rw [localVal, U.mem]; exact V
  · refine ⟨⟨fun r hr => ?_, by rw [U.rd, RD, Ru], by rw [U.wr, WR, Wu], by rw [U.sp, SP, State.callEntry_sp, R.sp]⟩, ?_⟩
    · have hr12 : r = .r12 := by revert hr; cases r <;> decide
      subst r
      rw [U.gpr, v11]
    · rw [U.mem, ← Mu]
      exact O

/-- The same pointer schedule gives the same trace, including nested calls. -/
theorem call_trace {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat}
    {ins : List (Impl.Dsa.Layout.Pointer × Nat)} {val₁ val₂ : Impl.Dsa.Layout.Pointer → Nat}
    {s₁ s₂ : State} (X : Pair base size₁ size₂ pLen qLen nP nQ ins val₁ val₂ s₁ s₂)
    (mp : (.input .p, pLen) ∈ ins) (mq : (.input .q, qLen) ∈ ins) (mg : (.input .g, pLen) ∈ ins)
    (my : (.input .y, pLen) ∈ ins)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q))) (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (Impl.Dsa.Arm.PublicValidation.call pLen qLen) s₁ s₂ := by
  have w₁ := X.C₁.S.ws
  have w₂ := X.C₂.S.ws
  unfold Impl.Dsa.Arm.PublicValidation.call
  refine SameTrace.seq (SameTrace.of_relCT (erased_relCT (τ := wsT false false)
      (σ := Taint.ofRegs [])
      (c₀ := .block [.mov .r11 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 0,
        .ldr .r2 .r12 (Impl.Dsa.Arm.Layout.field .p), .movw .r3 0])
      (.block []) rfl (Taint.noBase_ofRegs _) (by decide))
      (Taint.agree_ofRegs fun r hr => by
        simp only [wsRegs, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.mem_singleton] at hr
        subst r; exact Ws.r12_eq w₁ w₂))
    (head_ok w₁ (by have := X.C₁.S.big; omega) pLen qLen)
    (head_ok w₂ (by have := X.C₂.S.big; omega) pLen qLen)
    fun u₁ u₂ ⟨_, h0₁, R₁, M₁⟩ ⟨_, h0₂, R₂, M₂⟩ => ?_
  have E₁ : Pow.Entry u₁.callEntry base size₁ :=
    ⟨by rw [State.callEntry_gpr _ (by decide), h0₁, w₁.wb], by rw [State.callEntry_wr, R₁.wr]; exact w₁.wr, w₁.nowrap⟩
  have E₂ : Pow.Entry u₂.callEntry base size₂ :=
    ⟨by rw [State.callEntry_gpr _ (by decide), h0₂, w₂.wb], by rw [State.callEntry_wr, R₂.wr]; exact w₂.wr, w₂.nowrap⟩
  have subset : ∀ i ∈ inputs pLen qLen, i ∈ ins := by
    intro i hi
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> with_reducible assumption
  have I₁ : ∀ i ∈ inputs pLen qLen, Input u₁.callEntry base size₁ i.1 i.2 (val₁ i.1) := by
    intro i hi
    have I := X.C₁.I i (subset i hi)
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact input_mem I M₁ R₁.rd R₁.wr
  have I₂ : ∀ i ∈ inputs pLen qLen, Input u₂.callEntry base size₂ i.1 i.2 (val₂ i.1) := by
    intro i hi
    have I := X.C₂.I i (subset i hi)
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact input_mem I M₂ R₂.rd R₂.wr
  have PE : ∀ i ∈ inputs pLen qLen, PtrEq base u₁.callEntry u₂.callEntry i.1 := by
    intro i hi
    have H := X.E i (subset i hi)
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simpa only [PtrEq, pointerValue, State.callEntry_mem, M₁, M₂] using H
  have T := body_trace E₁ E₂ X.C₁.S.big X.C₂.S.big X.C₁.S.wp X.C₁.S.wq X.C₁.S.qp X.C₁.S.q32 I₁ I₂ PE D₁ D₂
  intro tr₁ tr₂ t₁ t₂ Ex₁ Ex₂
  cases Ex₁ with
  | seq C₁ B₁ =>
    cases Ex₂ with
    | seq C₂ B₂ =>
      cases C₁ with
      | call A₁ H₁ Ret₁ =>
        cases C₂ with
        | call A₂ H₂ Ret₂ =>
          rw [call_callEntry, Option.some.injEq] at A₁ A₂
          subst A₁; subst A₂
          have HT := T _ _ _ _ H₁ H₂
          have BT := SameTrace.of_relCT
            (relCT_of_check (τ := Taint.ofRegs []) (σ := Taint.ofRegs []) (h := .block []) (by decide))
            (Taint.agree_ofRegs fun _ h => nomatch h) _ _ _ _ B₁ B₂
          simp only [List.map_nil, List.nil_append, List.append_nil, HT, BT]

end VG.Proof.Dsa.Arm.PublicValidation
