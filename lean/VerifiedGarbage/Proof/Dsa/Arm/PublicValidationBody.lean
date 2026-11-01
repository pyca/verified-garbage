module

public import VerifiedGarbage.Impl.Dsa.Arm.PublicValidation
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.Arm.Session
import VerifiedGarbage.Proof.Dsa.Arm.PublicKey
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # Register saves around shared ARM public-key validation -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.PublicValidation
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.PublicValidation
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

theorem slots_fit {size : Nat} (hz : 204 ≤ size) : Pow.Fit size slots := by
  intro x hx
  simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by omega⟩

theorem slots_words : ∀ r ∈ Pow.words slots, 168 ≤ r.1 ∧ r.1 + r.2 ≤ 204 := by decide

theorem input_mem {s t : State} {base : Addr} {size len v : Nat} {f : Impl.Dsa.Layout.Field}
    (I : Input s base size (.input f) len v) (M : t.mem = s.mem) (R : t.rd = s.rd) (W : t.wr = s.wr) :
    Input t base size (.input f) len v := by
  have P : pointerValue base t (.input f) = pointerValue base s (.input f) := by simp only [pointerValue, M]
  exact ⟨⟨I.ok, by rw [P]; exact I.fits, by rw [P, R, W]; exact I.reads,
    by rw [P]; exact I.apart⟩, by rw [P]; exact I.outside, by rw [operand, P, M]; exact I.value⟩

theorem input_stores {s t : State} {base : Addr} {size len v : Nat} {p : Impl.Dsa.Layout.Pointer}
    (I : Input s base size p len v) (R : Rest [] s t) (O : Outs base (Pow.words slots) s.mem t.mem) :
    Input t base size p len v := by
  have H : ∀ r ∈ Pow.words slots, r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1 := by decide
  have P := pointerValue_keep (R.gpr .r12 (by decide)) O H I.ok
  refine ⟨I.toReady.keep_rest R (O := O) (hO := H), by rw [P]; exact I.outside, ?_⟩
  rw [operand, P, I.toReady.bytes O (by decide)]
  exact I.value

theorem words_scratch : ∀ r ∈ Pow.words slots,
    ∃ r' ∈ scratch, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := by
  intro r hr
  have H := slots_words r hr
  exact ⟨(168, 36), by simp [scratch], by omega, by omega⟩

theorem run_scratch : ∀ r ∈ runRanges,
    ∃ r' ∈ scratch, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 :=
  fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩

theorem body_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y : Nat}
    (E : Pow.Entry s base size) (big : 15712 < size)
    (wp : Width pLen nP) (wq : Width qLen nQ) (qp : qLen ≤ pLen) (q32 : qLen ≤ 32)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (body pLen qLen) s fun t =>
      maskW base t = maskW base s &&& VG.Proof.Ecdsa.Arm.mask32 (publicChecks P Q G Y) ∧
      localVal base t Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 ∧
      Outs base scratch s.mem t.mem ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold body save
  refine WP.seq (wp_mov (op2_reg s .r0) fun s₁ U => ?_)
  have W₁ : Ws s₁ base size := ⟨by rw [U.gpr]; exact E.wb, U.wr ▸ E.wr, E.nowrap⟩
  refine WP.mono (Pow.stores_ok slots W₁ (slots_fit (by omega)) (by unfold Pow.Apart; decide)) fun s₂ ⟨Saved, O, R⟩ => ?_
  have S₂ : Sched s₂ base size pLen qLen nP nQ := ⟨W₁.of_rest R (by decide), big, wp, wq, qp, q32⟩
  refine WP.seq (WP.mono (publicKey_ok S₂
    (input_stores (input_mem Ip U.mem U.rd U.wr) R O)
    (input_stores (input_mem Iq U.mem U.rd U.wr) R O)
    (input_stores (input_mem Ig U.mem U.rd U.wr) R O)
    (input_stores (input_mem Iy U.mem U.rd U.wr) R O) hP hPo hQ hQo) fun s₃ ⟨F, V, Run⟩ => ?_)
  refine WP.mono (Pow.loads_ok slots (Run.ws S₂.ws) (slots_fit (by omega)) (by decide) (by decide))
    fun t ⟨L, R₄, M⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have K := maskW_keep O (by
      intro r hr
      have H := slots_words r hr
      exact .inr (by omega))
    rw [show maskW base t = maskW base s₃ from congrArg (fun m => m.readW (off base 116) 32) M,
      F, K]
    rw [show maskW base s₁ = maskW base s from congrArg (fun m => m.readW (off base 116) 32) U.mem]
  · rw [localVal, M]; exact V
  · rw [M, ← U.mem]
    exact (Pow.outs_within O words_scratch).trans (Pow.outs_within Run.mem run_scratch)
  · intro r hr
    have hr' : r ∈ slots.map (·.1) := hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr'
    have H := slots_words _ (List.mem_map_of_mem (f := fun x => (x.2, 4)) hx)
    rw [L x hx, Run.saved x.2 (by omega) (by omega), Saved x hx, U.other _ (by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  · rw [R₄.sp, Run.rest.sp, R.sp, U.sp]
  · rw [R₄.rd, Run.rest.rd, R.rd, U.rd]
  · rw [R₄.wr, Run.rest.wr, R.wr, U.wr]

end VG.Proof.Dsa.Arm.PublicValidation
