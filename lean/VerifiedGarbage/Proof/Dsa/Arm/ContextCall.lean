module

public import VerifiedGarbage.Proof.Dsa.Arm.ContextBody
public import VerifiedGarbage.Proof.Dsa.SameTrace
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # Calls of shared ARMv7 Montgomery setup -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.Context
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Context
open VG.Proof.X25519.Arm (Rest wp_mov wp_movw op2_reg)

abbrev callRanges (n : Nat) := Impl.Dsa.Arm.Context.scratch n

theorem body_noCalls (n : Nat) : (body n).noCalls = true := by
  simp only [body, contextSetup, one, powerTwo, addD, addDigits, csubD, Dynamic.zeros, ptrLoop,
    Code.noCalls, Bool.and_self]

theorem call_noFrames (n : Nat) : (Impl.Dsa.Arm.Context.call n).noFrames = true := by
  simp only [Impl.Dsa.Arm.Context.call, Code.noFrames, Bool.true_and, Bool.and_true]
  exact Code.noFrames_of_noCalls (body_noCalls n)

theorem head_ok {s : State} (n : Nat) : WP isa (.block (head n)) s fun u =>
    u.gpr .r4 = s.gpr .r12 ∧ u.gpr .r0 = s.gpr .r12 ∧
      u.gpr .r1 = (BitVec.ofNat 16 (contextBytes n / 8)).setWidth 32 ∧
      Rest [.r0, .r1, .r4] s u ∧ u.mem = s.mem :=
  wp_mov (op2_reg s .r12) fun u₁ U₁ => wp_mov (op2_reg u₁ .r12) fun u₂ U₂ => wp_movw fun u U₃ =>
    WP.block_nil ⟨by rw [U₃.other _ (by decide), U₂.other _ (by decide), U₁.gpr],
      by rw [U₃.other _ (by decide), U₂.gpr, U₁.other _ (by decide)], U₃.gpr,
      ((U₁.rest (by decide)).trans (U₂.rest (by decide))).trans (U₃.rest (by decide)),
      by rw [U₃.mem, U₂.mem, U₁.mem]⟩

theorem entry_pre {s u : State} {base : Addr} {size n : Nat} (hs : Ws s base size)
    (hz : contextBytes n ≤ size) (hn48 : n ≤ 48)
    (h0 : u.gpr .r0 = s.gpr .r12) (h1 : u.gpr .r1 = (BitVec.ofNat 16 (contextBytes n / 8)).setWidth 32)
    (hm : u.mem = s.mem) (ho : val32 s.mem base (modS n) (2 * n) % 2 = 1)
    (hM : 1 < val32 s.mem base (modS n) (2 * n)) :
    (setupK n).pre (u.callEntry.withRegions [] [⟨base, contextBytes n⟩]) := by
  have b0 : State.addr (u.callEntry.gpr .r0) = base := by rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  have l1 : (u.callEntry.gpr .r1).toNat * 8 = contextBytes n := by
    rw [State.callEntry_gpr _ (by decide), h1]; exact Pow.words_eq hn48
  simp only [setupK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_mem, State.callEntry_mem, b0, l1, hm]
  refine ⟨trivial, trivial, ?_, Nat.le_refl _, ho, hM⟩
  rw [State.callEntry_gpr _ (by decide), h0, hs.wb_toNat]
  have := hs.nowrap
  omega

theorem call_ok {s : State} {base : Addr} {size n m : Nat} (hs : Ws s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48)
    (hv : val32 s.mem base (modS n) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (Impl.Dsa.Arm.Context.call n) s fun t => Context n m base size t ∧
      val32 t.mem base (oneS n) (2 * n) = 1 ∧
      val32 t.mem base (rrS n) (2 * n) = 2 ^ (128 * n) % m ∧
      Outs base (scratch n) s.mem t.mem ∧ Rest (.lr :: dclob) s t := by
  unfold Impl.Dsa.Arm.Context.call
  refine WP.seq (WP.mono (head_ok n) fun u ⟨h4, h0, h1, R₁, M₁⟩ => ?_)
  have W₁ := hs.of_rest R₁ (by decide)
  refine WP.seq (WP.call (k := setupK n) (setupK_correct hn hn48)
    (entry_pre hs hz hn48 h0 h1 M₁ (by rw [hv]; exact hodd) (by rw [hv]; exact hm1))
    (Covers.right (Pow.covers_ctx W₁ hz)) (Pow.covers_ctx W₁ hz)
    (fun v RD WR SP _ P _ post => ?_) (body_noCalls n))
  have B : State.addr (u.callEntry.gpr .r0) = base := by rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  simp only [setupK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, B, M₁, hv] at post
  obtain ⟨Inv, One, RR, O⟩ := post
  have V4 : v.gpr .r4 = s.gpr .r12 := by rw [P _ (by decide) (by decide), h4]
  refine wp_mov (op2_reg v .r4) fun t U => WP.block_nil ?_
  have W : Ws t base size := ⟨by rw [U.gpr, V4, hs.wb], by rw [U.wr, WR]; exact W₁.wr, hs.nowrap⟩
  have Mod : val32 t.mem base (modS n) (2 * n) = m := by
    rw [U.mem, O.val32 (fun r hr => by
      simp only [scratch, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [modS, oneS, rrS, tmpS, accS, resS, slot, stride] <;> omega)
      (by have := hs.nowrap; simp only [modS, contextBytes, slot, stride] at *; omega)]
    exact hv
  refine ⟨⟨W, hz, by simp only [contextBytes, slot, stride]; omega, hn, Mod, hm1,
    by rw [U.mem]; exact Inv⟩, by rw [U.mem]; exact One, by rw [U.mem]; exact RR,
    by rw [U.mem]; exact O, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro r hr
    have H : r = .r11 ∨ r = .r12 := by revert hr; cases r <;> decide
    rcases H with rfl | rfl
    · rw [U.other _ (by decide), P _ (by decide) (by decide), R₁.gpr _ (by decide)]
    · rw [U.gpr, V4]
  · rw [U.rd, RD, R₁.rd]
  · rw [U.wr, WR, R₁.wr]
  · rw [U.sp, SP, R₁.sp]

theorem call_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ n : Nat}
    (W₁ : Ws s₁ base size₁) (W₂ : Ws s₂ base size₂) (Z₁ : contextBytes n ≤ size₁)
    (Z₂ : contextBytes n ≤ size₂) (hn : 0 < n) (hn48 : n ≤ 48)
    (O₁ : val32 s₁.mem base (modS n) (2 * n) % 2 = 1) (M₁ : 1 < val32 s₁.mem base (modS n) (2 * n))
    (O₂ : val32 s₂.mem base (modS n) (2 * n) % 2 = 1) (M₂ : 1 < val32 s₂.mem base (modS n) (2 * n)) :
    SameTrace isa (Impl.Dsa.Arm.Context.call n) s₁ s₂ := by
  have nothing : ∀ a b : State, VG.Arm.Taint.Agree (Taint.ofRegs []) a b :=
    fun _ _ => Taint.agree_ofRegs fun _ h => nomatch h
  unfold Impl.Dsa.Arm.Context.call
  refine SameTrace.seq (SameTrace.of_relCT
    (erased_relCT (τ := Taint.ofRegs []) (σ := Taint.ofRegs [])
      (c₀ := .block [.mov .r4 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 0])
      (.block []) rfl (Taint.noBase_ofRegs _) (by decide)) (nothing _ _))
    (head_ok n) (head_ok n) fun u₁ u₂ ⟨_, h0₁, h1₁, R₁, H₁⟩ ⟨_, h0₂, h1₂, R₂, H₂⟩ => ?_
  refine SameTrace.of_relCT (P := fun a b => a = u₁ ∧ b = u₂) (RelCT.seq
    (RelCT.call (setupK_correct hn hn48) (setupK_ct n) [] [⟨base, contextBytes n⟩] ?_)
    ((relCT_of_check (τ := Taint.ofRegs []) (σ := Taint.ofRegs []) (h := .block []) (by decide)).mono
      (fun _ _ _ => nothing _ _) fun _ _ _ => trivial)) ⟨rfl, rfl⟩
  rintro a b ⟨rfl, rfl⟩
  refine ⟨entry_pre W₁ Z₁ hn48 h0₁ h1₁ H₁ O₁ M₁, entry_pre W₂ Z₂ hn48 h0₂ h1₂ H₂ O₂ M₂, ?_,
    Covers.right (Pow.covers_ctx (W₁.of_rest R₁ (by decide)) Z₁), Pow.covers_ctx (W₁.of_rest R₁ (by decide)) Z₁,
    Covers.right (Pow.covers_ctx (W₂.of_rest R₂ (by decide)) Z₂), Pow.covers_ctx (W₂.of_rest R₂ (by decide)) Z₂⟩
  simp only [setupK, State.withRegions_gpr]
  rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h0₁, h0₂]
  exact BitVec.eq_of_toNat_eq (by rw [W₁.wb_toNat, W₂.wb_toNat])

end VG.Proof.Dsa.Arm.Context
