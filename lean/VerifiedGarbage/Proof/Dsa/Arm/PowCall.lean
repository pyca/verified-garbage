module

public import VerifiedGarbage.Proof.Dsa.Arm.Pow
public import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA's exponentiation as a function on 32-bit ARM: its calls

A call (`Impl.Dsa.Arm.Pow.call`) of `vg_dsa_pow_{n}_{e}` from code whose
working space is at `r12`: it passes the context's bytes as the function's
working space, which its contract (`powK`) narrows the call to, and takes
`r12` back from `r11` (`call_ok`). Two runs of a call from the same working
space leak the same trace (`call_trace`), by the function's own constant
time (`powK_ct`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Pow

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Pow
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_movw op2_reg)

theorem body_noFrames (n e : Nat) : (body n e).noFrames = true := by
  simp only [body, Impl.Dsa.Arm.Context.call, Impl.Dsa.Arm.Context.body, contextSetup, exponentiate, exponentStep, exponentBody, exponentProduct, Dynamic.mul, rowD,
    digitRowD, mulRowD, csubD, Dynamic.zeros, ptrLoop, one, powerTwo, addD, addDigits, selectW, Code.noFrames,
    Bool.and_self]

/-- The arguments of a call, `r11` keeping `r12`. -/
theorem head_ok {s : State} (n : Nat) :
    WP isa (.block [.mov .r11 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 (BitVec.ofNat 16 (contextBytes n / 8))])
      s fun u => u.gpr .r11 = s.gpr .r12 ∧ u.gpr .r0 = s.gpr .r12 ∧
        u.gpr .r1 = (BitVec.ofNat 16 (contextBytes n / 8)).setWidth 32 ∧ Rest [.r0, .r1, .r11] s u ∧
        u.mem = s.mem :=
  wp_mov (op2_reg s .r12) fun u₁ v₁ => wp_mov (op2_reg u₁ .r12) fun u₂ v₂ => wp_movw fun u v₃ =>
    WP.block_nil ⟨by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr],
      by rw [v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide)], v₃.gpr,
      ((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans (v₃.rest (by decide)),
      by rw [v₃.mem, v₂.mem, v₁.mem]⟩

/-- On entry to the function, its precondition, narrowed to the context. -/
theorem entry_pre {s u : State} {base : Addr} {size n e : Nat} (hs : Ws s base size) (hz : contextBytes n ≤ size)
    (hn48 : n ≤ 48) (h0 : u.gpr .r0 = s.gpr .r12) (h1 : u.gpr .r1 = (BitVec.ofNat 16 (contextBytes n / 8)).setWidth 32)
    (hm : u.mem = s.mem) (hodd : val32 s.mem base (slot n 0) (2 * n) % 2 = 1)
    (hm1 : 1 < val32 s.mem base (slot n 0) (2 * n)) :
    (powK n e).pre (u.callEntry.withRegions [] [⟨base, contextBytes n⟩]) := by
  have b0 : State.addr (u.callEntry.gpr .r0) = base := by
    rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  have l1 : (u.callEntry.gpr .r1).toNat * 8 = contextBytes n := by
    rw [State.callEntry_gpr _ (by decide), h1]; exact words_eq hn48
  simp only [powK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem, b0, l1, hm]
  refine ⟨trivial, trivial, ?_, Nat.le_refl _, hodd, hm1⟩
  rw [State.callEntry_gpr _ (by decide), h0, hs.wb_toNat]
  have := hs.nowrap
  omega

/-- A call: `b ^ x mod m` into slot 9, as `body_ok`, with `r12` kept and
the registers the calling convention keeps. -/
theorem call_ok {s : State} {base : Addr} {size n e m : Nat} (hs : Ws s base size) (hz : contextBytes n ≤ size)
    (hn : 0 < n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n)
    (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (Impl.Dsa.Arm.Pow.call n e) s fun t => Ws t base size ∧
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) ^ val32 s.mem base (slot n 11) e % m ∧
      Outs base (scratch n) s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .r11, .lr] s t := by
  unfold Impl.Dsa.Arm.Pow.call
  refine WP.seq (WP.mono (head_ok n) fun u ⟨h11, h0, h1, R₁, M₁⟩ => ?_)
  have w₁ := hs.of_rest R₁ (by decide)
  refine WP.seq (WP.callCalls (k := powK n e) (powK_correct hn hn48 he hen)
    (entry_pre hs hz hn48 h0 h1 M₁ (by rw [hv]; exact hodd) (by rw [hv]; exact hm1))
    (Covers.right (covers_ctx w₁ hz)) (covers_ctx w₁ hz) (fun v hrd hwr hsp _ P _ post => ?_) (body_noFrames n e))
  have b0 : State.addr (u.callEntry.gpr .r0) = base := by rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  simp only [powK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, b0, M₁, hv] at post
  obtain ⟨V, O⟩ := post
  have v11 : v.gpr .r11 = s.gpr .r12 := by rw [P _ (by decide) (by decide), h11]
  refine wp_mov (op2_reg v .r11) fun t v₂ => WP.block_nil ⟨⟨?_, ?_, hs.nowrap⟩, ?_, ?_, ?_⟩
  · rw [v₂.gpr, v11, hs.wb]
  · rw [v₂.wr, hwr]; exact w₁.wr
  · rw [v₂.mem]; exact V
  · rw [v₂.mem]; exact O
  · refine ⟨fun r hr => ?_, by rw [v₂.rd, hrd, R₁.rd], by rw [v₂.wr, hwr, R₁.wr], by rw [v₂.sp, hsp, R₁.sp]⟩
    by_cases h12 : r = .r12
    · subst h12; rw [v₂.gpr, v11]
    · rw [v₂.other _ h12]
      have hp : r ∈ preserved ∧ r ≠ .lr ∧ r ∉ [.r0, .r1, .r11] := by revert hr h12; cases r <;> decide
      rw [P _ hp.1 hp.2.1, R₁.gpr _ hp.2.2]

/-- Two calls from the same working space leak the same trace. -/
theorem call_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ n e : Nat} (hs₁ : Ws s₁ base size₁)
    (hs₂ : Ws s₂ base size₂) (hz₁ : contextBytes n ≤ size₁) (hz₂ : contextBytes n ≤ size₂)
    (hn : 0 < n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n)
    (ho₁ : val32 s₁.mem base (slot n 0) (2 * n) % 2 = 1) (hm₁ : 1 < val32 s₁.mem base (slot n 0) (2 * n))
    (ho₂ : val32 s₂.mem base (slot n 0) (2 * n) % 2 = 1) (hm₂ : 1 < val32 s₂.mem base (slot n 0) (2 * n)) :
    SameTrace isa (Impl.Dsa.Arm.Pow.call n e) s₁ s₂ := by
  have nothing : ∀ a b : State, VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs []) a b :=
    fun _ _ => VG.Arm.Taint.agree_ofRegs fun _ h => nomatch h
  unfold Impl.Dsa.Arm.Pow.call
  refine SameTrace.seq (SameTrace.of_relCT (erased_relCT (τ := VG.Arm.Taint.ofRegs [])
      (σ := VG.Arm.Taint.ofRegs []) (c₀ := .block [.mov .r11 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 0])
      (.block []) rfl (Taint.noBase_ofRegs _) (by decide)) (nothing _ _)) (head_ok n) (head_ok n)
    fun u₁ u₂ ⟨_, h0₁, h1₁, R₁, M₁⟩ ⟨_, h0₂, h1₂, R₂, M₂⟩ => ?_
  have w₁ := hs₁.of_rest R₁ (by decide)
  have w₂ := hs₂.of_rest R₂ (by decide)
  refine SameTrace.of_relCT (P := fun a b => a = u₁ ∧ b = u₂) (RelCT.seq
    (RelCT.call (powK_correct hn hn48 he hen) (powK_ct n e hn hn48) [] [⟨base, contextBytes n⟩] ?_)
    ((relCT_of_check (τ := VG.Arm.Taint.ofRegs []) (σ := VG.Arm.Taint.ofRegs []) (h := .block [])
      (by decide)).mono (fun _ _ _ => nothing _ _) fun _ _ _ => trivial)) ⟨rfl, rfl⟩
  rintro a b ⟨rfl, rfl⟩
  refine ⟨entry_pre hs₁ hz₁ hn48 h0₁ h1₁ M₁ ho₁ hm₁, entry_pre hs₂ hz₂ hn48 h0₂ h1₂ M₂ ho₂ hm₂, ?_,
    Covers.right (covers_ctx w₁ hz₁), covers_ctx w₁ hz₁, Covers.right (covers_ctx w₂ hz₂), covers_ctx w₂ hz₂⟩
  simp only [powK, State.withRegions_gpr]
  rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h0₁, h0₂]
  exact BitVec.eq_of_toNat_eq (by rw [hs₁.wb_toNat, hs₂.wb_toNat])

end VG.Proof.Dsa.Arm.Pow
