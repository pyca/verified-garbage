module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.State
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Framework.Omega

/-! # A batch's update at a run-time width

`fourRows_ok`: both value rows and both coefficient rows (`InvBatch.fourRows_ok`), then
`update_ok`: the rows copied into the next state (`InvBatch.update_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff, WP.seq_iff] at h
  exact WP.seq_iff.mpr (WP.mono h fun _ hu => WP.seq_iff.mpr hu)

/-- Writes within arrays 0 and 1, arrays 11 to 14, or the sign slot are the rows' writes. -/
theorem rowWrites_cover {W : List (Nat × Nat)} {m m' : Mem}
    (hW : ∀ w ∈ W, (rv (kw len) (a 0) ≤ w.1 ∧ w.1 + w.2 ≤ rv (kw len) (a 0) + 2 * (8 * nw len + 8)) ∨
      (rv (kw len) (a 11) ≤ w.1 ∧ w.1 + w.2 ≤ rv (kw len) (a 11) + 4 * (8 * nw len + 8)) ∨
      (signSlot ≤ w.1 ∧ w.1 + w.2 ≤ signSlot + 4))
    (O : Unch B W m m') : Unch B (rowWrites len) m m' :=
  O.cover fun w hw => by
    rcases hW w hw with h | h | h
    · exact ⟨(rv (kw len) (a 0), 2 * (8 * nw len + 8)), by simp [rowWrites], h.1, h.2⟩
    · exact ⟨(rv (kw len) (a 11), 4 * (8 * nw len + 8)), by simp [rowWrites], h.1, h.2⟩
    · exact ⟨(signSlot, 4), by simp [rowWrites], h.1, h.2⟩

/-- The four matrix rows, `InvBatch.fourRows_ok`. -/
theorem fourRows_ok {s : State} (h : Bx L s B Z len N) (he : nw len % 2 = 0) {p iv cap : Nat}
    {T : Divstep.MSt} {st : Divstep.W32.IState} (hr : RowInput len B p iv T st s)
    (hp : 0 < p) (hinv : (p * iv + 1) % 2 ^ 32 = 0)
    (huv : |T.u| + |T.v| ≤ 2 ^ 30) (hqr : |T.q| + |T.r| ≤ 2 ^ 30)
    (hf : |st.f| ≤ cap) (hg : |st.g| ≤ cap) (capBound : cap < 2 ^ (32 * nw len + 1))
    (divF : 2 ^ 30 ∣ T.u * st.f + T.v * st.g) (divG : 2 ^ 30 ∣ T.q * st.f + T.r * st.g)
    (ha : |st.a| ≤ p) (hb : |st.b| ≤ p) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ z, Bx L z B Z len N →
      (val32 z.mem B (rv (kw len) (a 0)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
        ((T.u * st.f + T.v * st.g) / 2 ^ 30) % 2 ^ (32 * (nw len + 1)) →
      (val32 z.mem B (rv (kw len) (a 1)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
        ((T.q * st.f + T.r * st.g) / 2 ^ 30) % 2 ^ (32 * (nw len + 1)) →
      (val32 z.mem B (rv (kw len) (a 13)) (nw len) : Int) = Divstep.W32.mred p iv (T.u * st.a + T.v * st.b) →
      (val32 z.mem B (rv (kw len) (a 14)) (nw len) : Int) = Divstep.W32.mred p iv (T.q * st.a + T.r * st.b) →
      RowInput len B p iv T st z → Keeps wordClob s z → Unch B (rowWrites len) s.mem z.mem →
      WP isa rest z Q) :
    WP isa (.seq (linear L (win + 12) (win + 16) (a 11) (a 4) (a 5) (a 12) 1) <|
      .seq (shr30 L (a 0) (a 11)) <|
      .seq (linear L (win + 20) (win + 24) (a 11) (a 4) (a 5) (a 12) 1) <|
      .seq (shr30 L (a 1) (a 11)) <|
      .seq (linear L (win + 12) (win + 16) (a 11) (a 6) (a 7) (a 12) 0) <|
      .seq (reduce L (a 13)) <|
      .seq (linear L (win + 20) (win + 24) (a 11) (a 6) (a 7) (a 12) 0) <|
      .seq (reduce L (a 14)) rest) s Q := by
  have hn := h.nowrap
  have hf16 := h.fits16
  have hpos := h.ws.kw_pos
  have ke := kw_eq len
  have e48 : signSlot = 48 := rfl
  have r0 := rv_a len 0; have r1 := rv_a len 1; have r11 := rv_a len 11; have r12 := rv_a len 12
  have r13 := rv_a len 13; have r14 := rv_a len 14
  -- The first value row.
  refine seq_assoc (WP.seq (WP.mono (fgRow_ok h he (j := 0) (by decide) (by decide) (by decide)
    hr.matrix.u hr.matrix.v huv hr.f hr.g hf hg capBound divF) fun s₁ ⟨H₁, F₁, K₁, U₁⟩ => ?_))
  have C₁ : Unch B (rowWrites len) s.mem s₁.mem := rowWrites_cover (by
    intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> simp only <;> omega) U₁
  have h₁ := hr.keep h C₁
  -- The second.
  refine seq_assoc (WP.seq (WP.mono (fgRow_ok H₁ he (j := 1) (by decide) (by decide) (by decide)
    h₁.matrix.q h₁.matrix.r hqr h₁.f h₁.g hf hg capBound divG) fun s₂ ⟨H₂, G₂, K₂, U₂⟩ => ?_))
  have C₂ : Unch B (rowWrites len) s₁.mem s₂.mem := rowWrites_cover (by
    intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> simp only <;> omega) U₂
  have h₂ := h₁.keep H₁ C₂
  -- The coefficient rows.
  refine seq_assoc (WP.seq (WP.mono (abRow_ok H₂ (j := 13) (by decide) (by decide) (by decide) (by decide)
    hp h₂.modulus (by rw [h₂.inverse]; exact hinv) h₂.matrix.u h₂.matrix.v huv h₂.ca h₂.cb ha hb)
    fun s₃ ⟨H₃, A₃, K₃, U₃⟩ => ?_))
  have C₃ : Unch B (rowWrites len) s₂.mem s₃.mem := rowWrites_cover (by
    intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> simp only <;> omega) U₃
  have h₃ := h₂.keep H₂ C₃
  rw [h₂.inverse] at A₃
  refine seq_assoc (WP.seq (WP.mono (abRow_ok H₃ (j := 14) (by decide) (by decide) (by decide) (by decide)
    hp h₃.modulus (by rw [h₃.inverse]; exact hinv) h₃.matrix.q h₃.matrix.r hqr h₃.ca h₃.cb ha hb)
    fun z ⟨Hz, B₄, K₄, U₄⟩ => ?_))
  have C₄ : Unch B (rowWrites len) s₃.mem z.mem := rowWrites_cover (by
    intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> simp only <;> omega) U₄
  have h₄ := h₃.keep H₃ C₄
  rw [h₃.inverse] at B₄
  refine k z Hz ?_ ?_ ?_ B₄ h₄ ?_ ?_
  · rw [Outs.val32 U₄ (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> simp only <;> omega) (by omega),
      Outs.val32 U₃ (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> simp only <;> omega) (by omega),
      Outs.val32 U₂ (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp only <;> omega) (by omega)]
    exact F₁
  · rw [Outs.val32 U₄ (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> simp only <;> omega) (by omega),
      Outs.val32 U₃ (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> simp only <;> omega) (by omega)]
    exact G₂
  · rw [Outs.val32 U₄ (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> simp only <;> omega) (by omega)]
    exact A₃
  · exact (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      (K₄.mono (by decide))
  · intro x hx
    exact (C₄ x hx).trans ((C₃ x hx).trans ((C₂ x hx).trans (C₁ x hx)))

end VG.Proof.Rsa.X86.InvBatchRt
