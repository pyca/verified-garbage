module

import VerifiedGarbage.Proof.Dsa.Arm.ContextCall
public import VerifiedGarbage.Proof.Dsa.Arm.RegisterSave
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Exponent
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Timing
public import VerifiedGarbage.Proof.Dsa.SameTrace
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# DSA's exponentiation as a function on 32-bit ARM: its code

`vg_dsa_pow_{n}_{e}` (`Impl/Dsa/Arm/Pow.lean`) saves the registers it uses
in the header (`stores_ok`), sets up the context and exponentiates, and
loads them back (`loads_ok`): `body_ok`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Pow

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Pow
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_str wp_ldr op2_reg)

theorem exponent_scratch {n e : Nat} (he : e ≤ 2 * n) :
    ∀ r ∈ exponentRanges n e, ∃ r' ∈ scratch n, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 :=
  within_scratch (by
    simp only [exponentRanges, productRanges, List.cons_append, List.nil_append, List.forall_mem_cons,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, contextBytes, slot, stride, maskO]
    omega_arith)

/-- `b ^ x mod m` into slot 9, for the modulus in slot 0, the base in slot 8
and the exponent of `e` words in slot 11; the registers the calling
convention keeps are restored. -/
theorem body_ok {s : State} {base : Addr} {size n e m : Nat} (E : Entry s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n)
    (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (body n e) s fun t =>
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) ^ val32 s.mem base (slot n 11) e % m ∧
      Outs base (scratch n) s.mem t.mem ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨c44, c4960⟩ := contextBytes_bounds hn48
  have nw := E.nowrap
  have s0 := slot_bound (n := n) (i := 0) (by decide)
  have s8 := slot_bound (n := n) (i := 8) (by decide)
  have s11 := slot_bound (n := n) (i := 11) (by decide)
  have h0 := slot_header n 0
  have h8 := slot_header n 8
  have h11 := slot_header n 11
  unfold body save
  refine WP.seq (wp_mov (op2_reg s .r0) fun s₁ u₁ => ?_)
  have w₁ : Ws s₁ base size := ⟨by rw [u₁.gpr]; exact E.wb, u₁.wr ▸ E.wr, nw⟩
  refine WP.mono (stores_ok slots w₁ (slots_fit (by omega_arith)) slots_apart) fun s₂ ⟨S₂, O₂, R₂⟩ => ?_
  have w₂ := w₁.of_rest R₂ (by decide)
  have away : ∀ {d k : Nat}, 44 ≤ d → d + 4 * k ≤ 2 ^ 64 →
      val32 s₂.mem base d k = val32 s.mem base d k := fun hd hd' => by
    rw [O₂.val32 (fun r hr => .inr (by have := slots_words r hr; omega_arith)) hd', u₁.mem]
  have hv₂ : val32 s₂.mem base (slot n 0) (2 * n) = m := by
    rw [away (by omega_arith) (by simp only [contextBytes, slot, stride] at *; omega_arith)]; exact hv
  refine WP.seq (WP.mono (Context.call_ok w₂ (by omega_arith) hn hn48 hv₂ hm1 hodd)
    fun s₃ ⟨c₃, one₃, rr₃, O₃, R₃⟩ => ?_)
  refine WP.seq (WP.mono (exponentiate_ok c₃ he hen (by omega_arith) one₃ rr₃) fun s₄ ⟨c₄, V₄, O₄, R₄⟩ => ?_)
  refine WP.mono (loads_ok slots c₄.ws (slots_fit (by omega_arith)) slots_r12 slots_nodup) fun t ⟨L, R₅, M₅⟩ =>
    ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have k₃ : ∀ {d k : Nat}, (∀ r ∈ Context.callRanges n, d + 4 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) → d + 4 * k ≤ 2 ^ 64 →
        val32 s₃.mem base d k = val32 s₂.mem base d k := fun h h' => O₃.val32 h h'
    rw [show val32 t.mem base (slot n 9) (2 * n) = val32 s₄.mem base (slot n 9) (2 * n) by rw [M₅], V₄,
      k₃ (by simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
        implies_true, and_true, slot, stride]; omega_arith) (by omega_arith),
      k₃ (by simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
        implies_true, and_true, slot, stride]; omega_arith) (by omega_arith),
      away (by omega_arith) (by omega_arith), away (by omega_arith) (by omega_arith)]
  · have O₂' : Outs base (scratch n) s.mem s₂.mem := by rw [← u₁.mem]; exact outs_within O₂ (words_scratch n)
    rw [M₅]
    exact (O₂'.trans (outs_within O₃ (setup_scratch hn))).trans (outs_within O₄ (exponent_scratch hen))
  · rw [← slots_regs] at hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    have hx12 := slots_r12 x hx
    have hw := slots_words _ (List.mem_map_of_mem (f := fun x => (x.2, 4)) hx)
    simp only at hw
    rw [L x hx,
      outs_readW O₄ (by
        simp only [exponentRanges, productRanges, List.cons_append, List.nil_append, List.forall_mem_cons,
          List.not_mem_nil, false_imp_iff, implies_true, and_true, slot, stride, maskO]
        omega_arith) (by omega_arith),
      outs_readW O₃ (by
        simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
          slot, stride]
        omega_arith) (by omega_arith),
      S₂ x hx, u₁.other _ hx12]
  · rw [R₅.sp, R₄.sp, R₃.sp, R₂.sp, u₁.sp]
  · rw [R₅.rd, R₄.rd, R₃.rd, R₂.rd, u₁.rd]
  · rw [R₅.wr, R₄.wr, R₃.wr, R₂.wr, u₁.wr]

/-! ## The function -/

/-- The function's contract in this file's terms: the working space at `r0`,
of `r1` words, and the numbers as `val32` reads them. -/
def powK (n e : Nat) : Contract isa where
  pre s :=
    let base := State.addr (s.gpr .r0)
    let M := val32 s.mem base (slot n 0) (2 * n)
    s.rd = [] ∧ s.wr = [⟨base, (s.gpr .r1).toNat * 8⟩] ∧ (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32 ∧
      contextBytes n ≤ (s.gpr .r1).toNat * 8 ∧ M % 2 = 1 ∧ 1 < M
  post s t :=
    let base := State.addr (s.gpr .r0)
    val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) ^ val32 s.mem base (slot n 11) e % val32 s.mem base (slot n 0) (2 * n) ∧
      Outs base (scratch n) s.mem t.mem
  pub s t := s.gpr .r0 = t.gpr .r0

theorem powK_correct {n e : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n) (s : State)
    (h : (powK n e).pre s) :
    ∃ tr t, Exec isa (body n e) s tr t ∧ abiPreserved s t ∧ (powK n e).post s t := by
  obtain ⟨-, hwr, hnw, hz, hodd, hm1⟩ := h
  have E : Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) :=
    ⟨rfl, ⟨_, Nat.le_refl _, by omega_arith, by rw [hwr]; exact List.mem_singleton_self _⟩,
      by rw [VG.Proof.X25519.Arm.addr_toNat]; exact hnw⟩
  obtain ⟨tr, t, ex, V, O, P, hsp, -, -⟩ := body_ok E hz hn hn48 he hen rfl hm1 hodd
  exact ⟨tr, t, ex, ⟨P, hsp⟩, V, O⟩

/-- Saving the outer helper's registers leaves its arguments in memory. -/
theorem saveHead_ok {s : State} {base : Addr} {size : Nat} (E : Entry s base size) (hz : 44 ≤ size) :
    WP isa (.block save) s fun u => Ws u base size ∧
      Outs base (words slots) s.mem u.mem ∧ Rest [.r12] s u := by
  unfold save
  refine wp_mov (op2_reg s .r0) fun u₁ U => ?_
  have W : Ws u₁ base size := ⟨by rw [U.gpr]; exact E.wb, U.wr ▸ E.wr, E.nowrap⟩
  refine WP.mono (stores_ok slots W (slots_fit hz) slots_apart) fun u ⟨_, O, R⟩ =>
    ⟨W.of_rest R (by decide), by rw [← U.mem]; exact O,
      (U.rest (by decide)).trans (R.mono (by decide))⟩

/-- Context setup may call a helper; its outputs recover the public workspace
before the remainder's taint proof resumes. -/
theorem savedSetup_trace {n : Nat} {s₁ s₂ : State} {base : Addr} {size₁ size₂ : Nat} {rest : Prog isa}
    (E₁ : Entry s₁ base size₁) (E₂ : Entry s₂ base size₂)
    (Z₁ : contextBytes n ≤ size₁) (Z₂ : contextBytes n ≤ size₂) (hn : 0 < n) (hn48 : n ≤ 48)
    (O₁ : val32 s₁.mem base (modS n) (2 * n) % 2 = 1) (M₁ : 1 < val32 s₁.mem base (modS n) (2 * n))
    (O₂ : val32 s₂.mem base (modS n) (2 * n) % 2 = 1) (M₂ : 1 < val32 s₂.mem base (modS n) (2 * n))
    (H : RelCT isa (VG.Arm.Taint.Agree (wsT false false)) rest (fun _ _ => True)) :
    SameTrace isa (.seq (.block save) (.seq (Impl.Dsa.Arm.Context.call n) rest)) s₁ s₂ := by
  have c44 := (contextBytes_bounds hn48).1
  have Eq : s₁.gpr .r0 = s₂.gpr .r0 := by
    apply BitVec.eq_of_toNat_eq
    have H := congrArg BitVec.toNat (E₁.wb.trans E₂.wb.symm)
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using H
  refine SameTrace.seq (SameTrace.of_relCT
    (relCT_of_check (τ := VG.Arm.Taint.ofRegs [.r0]) (σ := wsT false false) (h := .block []) (by decide))
    (VG.Arm.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Eq))
    (saveHead_ok E₁ (by omega_arith)) (saveHead_ok E₂ (by omega_arith)) fun u₁ u₂ ⟨W₁, Q₁, _⟩ ⟨W₂, Q₂, _⟩ => ?_
  have mod : ∀ {s u : State}, Outs base (words slots) s.mem u.mem →
      val32 u.mem base (modS n) (2 * n) = val32 s.mem base (modS n) (2 * n) := fun O =>
    O.val32 (fun r hr => .inr (by
      have := slots_words r hr; simp only [modS, slot, stride]; omega_arith)) (by
      have := E₁.nowrap; simp only [modS, contextBytes, slot, stride] at *; omega_arith)
  refine SameTrace.seq (Context.call_trace W₁ W₂ Z₁ Z₂ hn hn48
    (by rw [mod Q₁]; exact O₁) (by rw [mod Q₁]; exact M₁)
    (by rw [mod Q₂]; exact O₂) (by rw [mod Q₂]; exact M₂))
    (Context.call_ok W₁ Z₁ hn hn48 rfl (by rw [mod Q₁]; exact M₁) (by rw [mod Q₁]; exact O₁))
    (Context.call_ok W₂ Z₂ hn hn48 rfl (by rw [mod Q₂]; exact M₂) (by rw [mod Q₂]; exact O₂))
    fun v₁ v₂ ⟨C₁, _⟩ ⟨C₂, _⟩ => ?_
  exact SameTrace.of_relCT H (VG.Arm.Taint.agree_ofRegs fun r hr => by
    simp only [wsRegs, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.mem_singleton] at hr
    subst r
    exact BitVec.eq_of_toNat_eq (by rw [C₁.ws.wb_toNat, C₂.ws.wb_toNat]))

theorem powK_ct (n e : Nat) (hn : 0 < n) (hn48 : n ≤ 48) :
    ConstantTime isa (powK n e).pre (powK n e).pub (body n e) := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ Eq => ?_
  have E : ∀ {s : State}, (powK n e).pre s → Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) := by
    intro s H
    exact ⟨rfl, ⟨_, Nat.le_refl _, by have := H.2.2.1; omega_arith, by rw [H.2.1]; simp⟩,
      by simpa only [VG.Proof.X25519.Arm.addr_toNat] using H.2.2.1⟩
  have E₂ : Entry s₂ (State.addr (s₁.gpr .r0)) ((s₂.gpr .r1).toNat * 8) := by rw [Eq]; exact E h₂
  unfold body
  refine savedSetup_trace (E h₁) E₂ h₁.2.2.2.1 h₂.2.2.2.1 hn hn48
    h₁.2.2.2.2.1 h₁.2.2.2.2.2 ?_ ?_ ?_
  · rw [Eq]; exact h₂.2.2.2.2.1
  · rw [Eq]; exact h₂.2.2.2.2.2
  · refine RelCT.seq (exponentiate_relCT false false n e) ?_
    exact (relCT_of_check (σ := VG.Arm.Taint.ofRegs []) (h := .block []) (by decide)).mono (fun _ _ h => h)
      fun _ _ _ => trivial

end VG.Proof.Dsa.Arm.Pow
