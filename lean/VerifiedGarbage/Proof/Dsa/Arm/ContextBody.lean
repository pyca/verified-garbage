module

public import VerifiedGarbage.Proof.Dsa.Arm.RegisterSave
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Timing
public import VerifiedGarbage.Proof.Framework.Arm.TaintErase
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ContextInit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Proof.Dsa.SameTrace
meta import VerifiedGarbage.Proof.Dsa.Arm.RegisterSave
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Timing
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.ContextInit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.ModPowContract
meta import VerifiedGarbage.Proof.Dsa.SameTrace

/-! # Correctness and contract of shared ARMv7 Montgomery setup -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.Context
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Context
open VG.Proof.Dsa.ModPow (numAt Keeps)
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

variable {umaal : Bool}

theorem slots_eq (n : Nat) : slots n =
    [(.r4, resS n), (.r5, resS n + 4), (.r6, resS n + 8), (.r7, resS n + 12),
      (.r8, resS n + 16), (.r9, resS n + 20), (.r10, resS n + 24), (.lr, resS n + 28)] := by
  simp [slots, regs]

theorem slots_fit {n size : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (hz : contextBytes n ≤ size) :
    Pow.Fit size (slots n) := by
  intro x hx
  simp only [slots_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    constructor <;> simp only [resS, contextBytes, slot, stride] at * <;> omega_arith

theorem slots_apart (n : Nat) : Pow.Apart (slots n) := by
  simp [Pow.Apart, slots_eq] <;> omega_arith

theorem slots_r12 (n : Nat) : ∀ x ∈ slots n, x.1 ≠ .r12 := by simp [slots_eq]
theorem slots_nodup (n : Nat) : ((slots n).map (·.1)).Nodup := by simp [slots_eq]

theorem slots_words {n : Nat} : ∀ r ∈ Pow.words (slots n), resS n ≤ r.1 ∧ r.1 + r.2 ≤ resS n + 32 := by
  simp only [Pow.words, slots_eq, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil,
    false_imp_iff, implies_true, and_true]
  omega_arith

/-- The registers saved, with the working space in `r12`. -/
theorem save_ok {s : State} {base : Addr} {size n : Nat} (E : Pow.Entry s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48) :
    WP isa (.block (save n)) s fun t => Ws t base size ∧
      (∀ x ∈ slots n, t.mem.readW (off base x.2) 32 = s.gpr x.1) ∧
      Outs base (Pow.words (slots n)) s.mem t.mem ∧ Rest [.r12] s t := by
  unfold save
  refine wp_mov (op2_reg s .r0) fun s₁ U => ?_
  have W₁ : Ws s₁ base size := ⟨by rw [U.gpr]; exact E.wb, U.wr ▸ E.wr, E.nowrap⟩
  refine WP.mono (Pow.stores_ok (slots n) W₁ (slots_fit hn hn48 hz) (slots_apart n)) fun t ⟨S, O, R⟩ =>
    ⟨W₁.of_rest R (by decide), fun x hx => by rw [S x hx, U.other _ (slots_r12 n x hx)], by rw [← U.mem]; exact O,
      (U.rest (by decide)).trans (R.mono (by decide))⟩

/-- The saves leave the modulus as it was. -/
theorem save_modulus {s t : State} {base : Addr} {size n : Nat} (E : Pow.Entry s base size)
    (hz : contextBytes n ≤ size) (O : Outs base (Pow.words (slots n)) s.mem t.mem) :
    val32 t.mem base (slot n 0) (2 * n) = val32 s.mem base (slot n 0) (2 * n) :=
  O.val32 (fun r hr => .inl (by have := slots_words r hr; simp only [resS, slot, stride] at *; omega_arith))
    (by have := E.nowrap; simp only [contextBytes, slot, stride] at *; omega_arith)

theorem body_ok {s : State} {base : Addr} {size n m : Nat} (E : Pow.Entry s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48)
    (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (body umaal n) s fun t => Context n m base size t ∧
      val32 t.mem base (oneS n) (2 * n) = 1 ∧
      val32 t.mem base (rrS n) (2 * n) = 2 ^ (128 * n) % m ∧
      Outs base (scratch n) s.mem t.mem ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold body
  refine WP.seq (WP.mono (save_ok E hz hn hn48) fun s₂ ⟨W₂, S, O, R⟩ => ?_)
  have V₂ : val32 s₂.mem base (slot n 0) (2 * n) = m := (save_modulus E hz O).trans hv
  refine WP.seq (WP.mono (contextSetup_ok W₂ hn hz
    (by simp only [contextBytes, slot, stride]; omega_arith) (by omega_arith) V₂ hm1 hodd)
    fun s₃ ⟨C, One, RR, O₃, R₃⟩ => ?_)
  refine WP.mono (Pow.loads_ok (slots n) C.ws (slots_fit hn hn48 hz) (slots_r12 n) (slots_nodup n))
    fun t ⟨L, R₄, M⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨C.ws.of_rest R₄ (by simp [slots_eq]), C.size_le, C.small, C.n0,
      by rw [M]; exact C.modulus, C.gt_one, by rw [M]; exact C.inverse⟩
  · rw [M]; exact One
  · rw [M]; exact RR
  · rw [M]
    refine (Pow.outs_within O fun r hr => ⟨(resS n, 32), by simp [scratch], (slots_words r hr).1,
      (slots_words r hr).2⟩).trans (O₃.mono ?_)
    intro r hr
    simpa only [scratch, setupRanges, oneS, rrS, tmpS, accS] using List.mem_cons_of_mem (resS n, 32) hr
  · intro r hr
    by_cases h11 : r = .r11
    · subst r
      rw [R₄.gpr _ (by simp [slots_eq]), R₃.gpr _ (by decide), R.gpr _ (by decide)]
    · have hr' : r ∈ (slots n).map (·.1) := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [slots_eq, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr'
      rw [L x hx, Pow.outs_readW O₃ (fun a ha => by
          have := slots_words (x.2, 4) (List.mem_map_of_mem (f := fun x => (x.2, 4)) hx)
          simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl <;>
            simp only [resS, slot, stride] at * <;> omega_arith)
        (by have := (slots_fit hn hn48 hz) x hx; have := E.nowrap; omega_arith), S x hx]
  · rw [R₄.sp, R₃.sp, R.sp]
  · rw [R₄.rd, R₃.rd, R.rd]
  · rw [R₄.wr, R₃.wr, R.wr]

/-- Internal form of the contract, retaining the word-level output facts.
Its time may depend on the working space's address and on the modulus, some
of whose bits choose where the setup's doublings start (`rSquared`). -/
def setupK (n : Nat) : Contract isa where
  pre s :=
    let base := State.addr (s.gpr .r0)
    let M := val32 s.mem base (modS n) (2 * n)
    s.rd = [] ∧ s.wr = [⟨base, (s.gpr .r1).toNat * 8⟩] ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32 ∧
      contextBytes n ≤ (s.gpr .r1).toNat * 8 ∧ M % 2 = 1 ∧ 1 < M
  post s t :=
    let base := State.addr (s.gpr .r0)
    let M := val32 s.mem base (modS n) (2 * n)
    (M * w32 t.mem base invO + 1) % 2 ^ 16 = 0 ∧
      val32 t.mem base (oneS n) (2 * n) = 1 ∧
      val32 t.mem base (rrS n) (2 * n) = 2 ^ (128 * n) % M ∧
      Outs base (scratch n) s.mem t.mem
  pub s t := s.gpr .r0 = t.gpr .r0 ∧
    val32 s.mem (State.addr (s.gpr .r0)) (modS n) (2 * n) = val32 t.mem (State.addr (t.gpr .r0)) (modS n) (2 * n)

theorem setupK_correct {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (s : State) (h : (setupK n).pre s) :
    ∃ tr t, Exec isa (body umaal n) s tr t ∧ abiPreserved s t ∧ (setupK n).post s t := by
  obtain ⟨-, hwr, hnw, hz, ho, hm⟩ := h
  have E : Pow.Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) :=
    ⟨rfl, ⟨_, Nat.le_refl _, by omega_arith, by rw [hwr]; exact List.mem_singleton_self _⟩,
      by rw [VG.Proof.X25519.Arm.addr_toNat]; exact hnw⟩
  obtain ⟨tr, t, Ex, C, One, RR, O, P, SP, -, -⟩ := body_ok E hz hn hn48 rfl hm ho
  exact ⟨tr, t, Ex, ⟨P, SP⟩, C.inverse, One, RR, O⟩

/-- The working space's base, the same in two runs. -/
theorem agreeBase {s₁ s₂ : State} {base : Addr} {size₁ size₂ : Nat} (h₁ : Ws s₁ base size₁) (h₂ : Ws s₂ base size₂) :
    VG.Arm.Taint.Agree (wsT false false) s₁ s₂ :=
  Taint.agree_ofRegs fun r hr => by
    simp only [wsRegs, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.mem_singleton] at hr
    subst r
    exact BitVec.eq_of_toNat_eq (by rw [h₁.wb_toNat, h₂.wb_toNat])

theorem save_relCT (n : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (Taint.ofRegs [.r0])) (.block (save n)) (VG.Arm.Taint.Agree (wsT false false)) := by
  obtain ⟨h, H⟩ : ∃ h, (VG.Taint.check taintU (Taint.ofRegs [.r0]) (.block (save 1)) h).map
      (taintU.le (wsT false false)) = some true := ⟨_, by taint_decide⟩
  exact erased_relCT h (by simp only [save, slots_eq]; rfl) (Taint.noBase_ofRegs _) H

theorem restore_relCT (n : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT false false)) (.block (restore n)) (fun _ _ => True) := by
  obtain ⟨h, H⟩ : ∃ h, (VG.Taint.check taintU (wsT false false) (.block (restore 1)) h).map
      (taintU.le (Taint.ofRegs [])) = some true := ⟨_, by taint_decide⟩
  exact (erased_relCT h (by simp only [restore, slots_eq]; rfl) (wsT_noBase _ _) H).mono (fun _ _ h => h)
    fun _ _ _ => trivial

/-- Where the doublings start, and what follows, in two runs with the same
modulus: each test reads the same bit in both. -/
theorem start_trace {base : Addr} {size₁ size₂ n m : Nat} (h128 : 128 * n < 2 ^ 16) :
    ∀ (ks : List Nat) {s₁ s₂ : State}, (∀ k ∈ ks, 0 < k) → Dyn.Context n m base size₁ s₁ →
      Dyn.Context n m base size₂ s₂ → SameTrace isa (.seq (start n ks) (raise umaal n)) s₁ s₂
  | [], _, _, _, c₁, c₂ =>
    SameTrace.of_relCT (RelCT.seq (fromOne_relCT n) (raise_relCT n)) (agreeBase c₁.ws c₂.ws)
  | k :: ks, s₁, s₂, hk, c₁, c₂ => by
    have hw : 2 * n - k < 2 * n := by have k0 := hk k List.mem_cons_self; have n0 := c₁.n0; omega_arith
    rw [start]
    refine SameTrace.assoc_left (SameTrace.seq (SameTrace.of_relCT (topTest_relCT n _) (agreeBase c₁.ws c₂.ws))
      (topTest_ok c₁ hw) (topTest_ok c₂ hw) fun x₁ x₂ ⟨z₁, M₁, R₁⟩ ⟨z₂, M₂, R₂⟩ => ?_)
    obtain d₁ := c₁.after_test M₁ R₁
    obtain d₂ := c₂.after_test M₂ R₂
    refine SameTrace.seq_ite (by rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, z₁, z₂])
      (fun _ => SameTrace.of_relCT (RelCT.seq (fromTop_relCT n _) (raise_relCT n)) (agreeBase d₁.ws d₂.ws))
      (fun _ => start_trace h128 ks (fun k hk' => hk k (List.mem_cons_of_mem _ hk')) d₁ d₂)

/-- Two runs from the same working space, with the same modulus, leak the
same trace: some of its bits choose where the doublings start (`rSquared`),
and every other address and branch is public. -/
theorem body_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ n m : Nat}
    (E₁ : Pow.Entry s₁ base size₁) (E₂ : Pow.Entry s₂ base size₂)
    (hz₁ : contextBytes n ≤ size₁) (hz₂ : contextBytes n ≤ size₂) (hn : 0 < n) (hn48 : n ≤ 48)
    (hv₁ : val32 s₁.mem base (slot n 0) (2 * n) = m) (hv₂ : val32 s₂.mem base (slot n 0) (2 * n) = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1) :
    SameTrace isa (body umaal n) s₁ s₂ := by
  have h16 : contextBytes n < 2 ^ 16 := by simp only [contextBytes, slot, stride]; omega_arith
  have R0 : s₁.gpr .r0 = s₂.gpr .r0 := by
    apply BitVec.eq_of_toNat_eq
    have H := congrArg BitVec.toNat (E₁.wb.trans E₂.wb.symm)
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using H
  unfold body
  refine SameTrace.seq (SameTrace.of_relCT (save_relCT n) (Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact R0))
    (save_ok E₁ hz₁ hn hn48) (save_ok E₂ hz₂ hn hn48) fun u₁ u₂ ⟨W₁, _, O₁, _⟩ ⟨W₂, _, O₂, _⟩ => ?_
  obtain V₁ := (save_modulus E₁ hz₁ O₁).trans hv₁
  obtain V₂ := (save_modulus E₂ hz₂ O₂).trans hv₂
  refine SameTrace.seq ?_ (contextSetup_ok (umaal := umaal) W₁ hn hz₁ h16 (by omega_arith) V₁ hm1 hodd)
    (contextSetup_ok (umaal := umaal) W₂ hn hz₂ h16 (by omega_arith) V₂ hm1 hodd) fun v₁ v₂ ⟨C₁, _⟩ ⟨C₂, _⟩ =>
      SameTrace.of_relCT (restore_relCT n) (agreeBase C₁.ws C₂.ws)
  unfold contextSetup
  refine SameTrace.assoc (SameTrace.seq (SameTrace.of_relCT (setupHead_relCT n) (agreeBase W₁ W₂))
    (setupHead_ok W₁ hn hz₁ h16 V₁ hm1 hodd) (setupHead_ok W₂ hn hz₂ h16 V₂ hm1 hodd)
    fun t₁ t₂ ⟨c₁, _⟩ ⟨c₂, _⟩ => ?_)
  unfold rSquared
  exact start_trace (by omega_arith) tops (by decide) c₁ c₂

theorem setupK_ct (n : Nat) (hn : 0 < n) (hn48 : n ≤ 48) :
    ConstantTime isa (setupK n).pre (setupK n).pub (body umaal n) := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ ⟨e0, em⟩ => ?_
  have E : ∀ {s : State}, (setupK n).pre s → Pow.Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) :=
    fun {s} H => ⟨rfl, ⟨_, Nat.le_refl _, by have := H.2.2.1; omega_arith, by rw [H.2.1]; exact List.mem_singleton_self _⟩,
      by rw [VG.Proof.X25519.Arm.addr_toNat]; exact H.2.2.1⟩
  have E₂ : Pow.Entry s₂ (State.addr (s₁.gpr .r0)) ((s₂.gpr .r1).toNat * 8) := by rw [e0]; exact E h₂
  rw [← e0] at em
  exact body_trace (E h₁) E₂ h₁.2.2.2.1 h₂.2.2.2.1 hn hn48 rfl em.symm h₁.2.2.2.2.2 h₁.2.2.2.2.1

end VG.Proof.Dsa.Arm.Context
