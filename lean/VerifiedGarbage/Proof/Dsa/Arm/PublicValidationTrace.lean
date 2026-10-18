module

public import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCorrect
public import VerifiedGarbage.Proof.Dsa.Arm.KeyTrace
import VerifiedGarbage.Proof.Framework.Omega

/-! # Constant-time traces of the callable public-key checks -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.PublicValidation
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.PublicValidation
open VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (wp_mov op2_reg)

theorem save_ok {s : State} {base : Addr} {size : Nat}
    (E : Pow.Entry s base size) (big : 204 ≤ size) :
    WP isa (.block save) s fun t => Ws t base size ∧
      (∀ f, f ≠ Field.mask → pointerValue base t (.input f) = pointerValue base s (.input f)) ∧
      (∀ f len v, Input s base size (.input f) len v → Input t base size (.input f) len v) := by
  unfold save
  refine wp_mov (op2_reg s .r0) fun s₁ U => ?_
  have W : Ws s₁ base size := ⟨by rw [U.gpr]; exact E.wb, U.wr ▸ E.wr, E.nowrap⟩
  refine WP.mono (Pow.stores_ok slots W (slots_fit big) (by unfold Pow.Apart; decide)) fun t ⟨_, O, R⟩ => ?_
  refine ⟨W.of_rest R (by decide), ?_, fun f len v I => input_stores (input_mem I U.mem U.rd U.wr) R O⟩
  intro f hf
  rw [pointerValue_keep (p := .input f) (R.gpr .r12 (by decide)) O (by decide) hf]
  simp only [pointerValue, U.mem]

def inputs (pLen qLen : Nat) : List (Pointer × Nat) :=
  [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen), (.input .y, pLen)]

theorem body_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ pLen qLen nP nQ : Nat}
    {val₁ val₂ : Pointer → Nat}
    (E₁ : Pow.Entry s₁ base size₁) (E₂ : Pow.Entry s₂ base size₂)
    (b₁ : 15712 < size₁) (b₂ : 15712 < size₂)
    (wp : Width pLen nP) (wq : Width qLen nQ) (qp : qLen ≤ pLen) (q32 : qLen ≤ 32)
    (I₁ : ∀ i ∈ inputs pLen qLen, Input s₁ base size₁ i.1 i.2 (val₁ i.1))
    (I₂ : ∀ i ∈ inputs pLen qLen, Input s₂ base size₂ i.1 i.2 (val₂ i.1))
    (PE : ∀ i ∈ inputs pLen qLen, PtrEq base s₁ s₂ i.1)
    (D₁ : DomainOk (val₁ (.input .p)) (val₁ (.input .q)))
    (D₂ : DomainOk (val₂ (.input .p)) (val₂ (.input .q))) :
    SameTrace isa (body pLen qLen) s₁ s₂ := by
  have R0 : s₁.gpr .r0 = s₂.gpr .r0 := by
    apply BitVec.eq_of_toNat_eq
    have H := E₁.wb.trans E₂.wb.symm
    have H' := congrArg BitVec.toNat H
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using H'
  unfold body
  refine SameTrace.seq (SameTrace.of_relCT
    (relCT_of_check (τ := Taint.ofRegs [.r0]) (σ := wsT false false) (h := .block []) (by decide))
    (Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact R0))
    (save_ok E₁ (by omega)) (save_ok E₂ (by omega)) fun t₁ t₂ ⟨W₁, P₁, J₁⟩ ⟨W₂, P₂, J₂⟩ => ?_
  have X : Pair base size₁ size₂ pLen qLen nP nQ (inputs pLen qLen) val₁ val₂ t₁ t₂ := by
    refine ⟨⟨⟨W₁, b₁, wp, wq, qp, q32⟩, ?_⟩, ⟨⟨W₂, b₂, wp, wq, qp, q32⟩, ?_⟩, ?_⟩
    · intro i hi
      simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact J₁ _ _ _ (I₁ (.input .p, pLen) (by simp [inputs]))
      · exact J₁ _ _ _ (I₁ (.input .q, qLen) (by simp [inputs]))
      · exact J₁ _ _ _ (I₁ (.input .g, pLen) (by simp [inputs]))
      · exact J₁ _ _ _ (I₁ (.input .y, pLen) (by simp [inputs]))
    · intro i hi
      simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact J₂ _ _ _ (I₂ (.input .p, pLen) (by simp [inputs]))
      · exact J₂ _ _ _ (I₂ (.input .q, qLen) (by simp [inputs]))
      · exact J₂ _ _ _ (I₂ (.input .g, pLen) (by simp [inputs]))
      · exact J₂ _ _ _ (I₂ (.input .y, pLen) (by simp [inputs]))
    · intro i hi
      have H := PE i hi
      simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> unfold PtrEq at * <;>
        rw [P₁ _ (by decide), P₂ _ (by decide)] <;> exact H
  have mp : (.input .p, pLen) ∈ inputs pLen qLen := by simp [inputs]
  have mq : (.input .q, qLen) ∈ inputs pLen qLen := by simp [inputs]
  have mg : (.input .g, pLen) ∈ inputs pLen qLen := by simp [inputs]
  have my : (.input .y, pLen) ∈ inputs pLen qLen := by simp [inputs]
  refine SameTrace.seq (publicKey_trace X mp mq mg my D₁ D₂)
    (publicKey_ok X.C₁.S (X.C₁.inp mp) (X.C₁.inp mq) (X.C₁.inp mg) (X.C₁.inp my) D₁.hP D₁.hPo D₁.hQ D₁.hQo)
    (publicKey_ok X.C₂.S (X.C₂.inp mp) (X.C₂.inp mq) (X.C₂.inp mg) (X.C₂.inp my) D₂.hP D₂.hPo D₂.hQ D₂.hQo)
    fun u₁ u₂ ⟨_, _, R₁⟩ ⟨_, _, R₂⟩ => ?_
  exact SameTrace.of_relCT
    (relCT_of_check (τ := wsT false false) (σ := Taint.ofRegs []) (h := .block []) (by decide))
    (Taint.agree_ofRegs fun r hr => by
      simp only [wsRegs, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.mem_singleton] at hr
      subst r
      exact Ws.r12_eq (R₁.ws W₁) (R₂.ws W₂))

end VG.Proof.Dsa.Arm.PublicValidation
