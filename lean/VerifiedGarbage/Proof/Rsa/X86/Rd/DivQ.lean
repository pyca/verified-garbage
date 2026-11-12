module

public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Step
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Step
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Quot
import VerifiedGarbage.Proof.Bignum.WordStepNorm32
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr

/-! # Prime recovery's division by words on i686: a step with its digit

`RecoverDetRt.stepQ` is `WordModRt.step` with the step's quotient digit kept:
after `mulSub`, the estimate `q̂` less one where `T = r 2^32 + u - q̂ m` is
negative, which is `⌊(r 2^32 + u) / m⌋` (`digit_of_sign`), into the header
word `sQd` (`stepQ_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.WordRt
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc)
open VG.Impl.Rsa.X86.WordModRt (oD oV oD1 oQ oU0 oU2 oSteps oDig h0)

/-- The step's digit: the estimate less one where the two's complement `T₁` of `Y - q̂ M` is
negative. -/
theorem digit_of_sign {W Y M qh T1 b : Nat} (hM0 : 0 < M) (hMW : 2 * M < W / 2)
    (hge : Y / M ≤ qh) (hle : qh ≤ Y / M + 1) (hT1 : T1 < W) (hb : b < 2) (h1 : T1 + qh * M = Y + W * b) :
    (W / 2 ≤ T1 → 1 ≤ qh) ∧ qh - (if W / 2 ≤ T1 then 1 else 0) = Y / M := by
  have dm := Nat.div_add_mod Y M
  have ml := Nat.mod_lt Y hM0
  generalize Y / M = q at *
  generalize Y % M = r at *
  rcases Nat.eq_or_lt_of_le hge with rfl | hlt
  · -- `q̂ = q`: `T₁ = r`, non-negative.
    rw [Nat.mul_comm q M] at h1
    have : b = 0 := by
      rcases (show b = 0 ∨ b = 1 by omega) with e | e
      · exact e
      · subst e; omega
    subst this
    have : T1 = r := by omega
    subst this
    refine ⟨fun h => by omega, ?_⟩
    simp only [show ¬ (W / 2 ≤ T1) by omega, ite_false, Nat.sub_zero]
  · -- `q̂ = q + 1`: `T₁ = W + r - M`, negative.
    have e : qh = q + 1 := by omega
    subst e
    have em : (q + 1) * M = M * q + M := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    rw [em] at h1
    have : b = 1 := by
      rcases (show b = 0 ∨ b = 1 by omega) with e | e
      · subst e; omega
      · exact e
    subst this
    have hneg : W / 2 ≤ T1 := by omega
    refine ⟨fun _ => by omega, ?_⟩
    simp only [hneg, ite_true]
    omega

variable {B : Addr} {Z len N : Nat}

open VG.Impl.Rsa.X86.RecoverDetRt (sQd)

/-- The step's digit block: `sQd := q̂ - [T < 0]`, from `T`'s top word `W'` (its sign) and `q̂` in
`oQ`. -/
theorem digitQ_ok {s : State} (h : RtWs VG.Impl.Rsa.X86.RecoverRt.wid s B Z len N) {ml a t : Nat}
    (hm : MLen s B Z ml a) (ht : t < N) (hw : wq a ≤ kw len) {Q top : Nat}
    (hQ : slot s.mem B oQ = Q) (hT : w32 s.mem B (arr (kw len) t + 4 * wq a) = top)
    (hQ1 : 2 ^ 31 ≤ top → 1 ≤ Q) (hQ32 : Q < 2 ^ 32) :
    WP isa (.block (arrPtr VG.Impl.Rsa.X86.RecoverRt.wid .ebp t .edx ++ (VG.Impl.Rsa.X86.WordModRt.width4 ml .eax ++
      ([.alu .add .ebp (.reg .eax), .mov .eax (.mem (at_ .ebp 0)), .alu .add .eax (.reg .eax),
        .alu .sbb .eax (.reg .eax), .alu .add .eax (.mem (sc oQ)), .store (sc sQd) .eax] : List Instr)))) s fun v =>
      RtWs VG.Impl.Rsa.X86.RecoverRt.wid v B Z len N ∧ Keep B (kw len) [] [sQd] s.mem v.mem ∧
      slot v.mem B sQd = Q - (if 2 ^ 31 ≤ top then 1 else 0) ∧ Keeps [.eax, .edx, .ebp] s v := by
  have nw := h.ws.workspace.nowrap
  have ft := h.ws.arr_fit ht
  have hdr := h.ws.hdr_le
  have kb := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  simp only [S] at ft
  refine arrPtr_ok (lenSrc h) h.lenLe h.edi (r := .ebp) (t := .edx) (j := t) (by decide) (by decide)
    (by omega) fun u₁ U₁ m₁ p₁ _ => ?_
  have hm₁ : MLen u₁ B Z ml a := hm.keep U₁ (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine width4_ok hm₁ fun u₂ U₂ m₂ e₂ => ?_
  refine wp_addS rfl fun u₃ U₃ _ => ?_
  have p₂ : PtrAt u₂ B .ebp (arr (kw len) t) := by rw [PtrAt, U₂.1 _ (by decide)]; exact p₁
  have p₃ : PtrAt u₃ B .ebp (arr (kw len) t + 4 * wq a) := by
    have le := hm.le
    rw [PtrAt, U₃.gpr, ptr_add p₂, e₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have m₃ : u₃.mem = s.mem := by rw [U₃.mem, m₂, m₁]
  refine wp_movS (readSrc_ptr (h.rt.of_wr (by rw [U₃.wr, U₂.2.2, U₁.2.2])) p₃ (d := 0) (by omega))
    fun u₄ U₄ _ => ?_
  have v₄ : (u₄.gpr .eax).toNat = top := by rw [U₄.gpr, m₃, Nat.add_zero, ← hT]
  refine wp_addS rfl fun u₅ U₅ c₅ => ?_
  refine VG.X86.Wp.wp_sbb_self c₅ fun u₆ U₆ => ?_
  have q₆ : readSrc u₆ (.mem (sc oQ)) = some (BitVec.ofNat 32 Q) := by
    have := readHdr (Z := Z) (w := kw len) (N := N) (h.ws.rest (rs := [.eax, .edx, .ebp])
      ((U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans ((U₃.keeps.mono (by decide)).trans
        ((U₄.keeps.mono (by decide)).trans ((U₅.keeps.mono (by decide)).trans (U₆.keeps.mono (by decide))))))))
      (d := oQ) (by decide)
    rw [this, U₆.mem, U₅.mem, U₄.mem, m₃, hQ]
  refine wp_addS q₆ fun u₇ U₇ _ => ?_
  have K₇ : Keeps [.eax, .edx, .ebp] s u₇ := (U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans
    ((U₃.keeps.mono (by decide)).trans ((U₄.keeps.mono (by decide)).trans ((U₅.keeps.mono (by decide)).trans
      ((U₆.keeps.mono (by decide)).trans (U₇.keeps.mono (by decide)))))))
  have m₇ : u₇.mem = s.mem := by rw [U₇.mem, U₆.mem, U₅.mem, U₄.mem, m₃]
  refine storeHdr (h.ws.rest K₇) (by decide) .eax fun v k₈ e₈ K₈ _ _ => WP.block_nil ?_
  have Kv : Keeps [.eax, .edx, .ebp] s v := K₇.trans (K₈.mono (by simp))
  have kv : Keep B (kw len) [] [sQd] s.mem v.mem := by rw [← m₇]; exact k₈
  refine ⟨h.keep Kv (by decide) (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws kv (by simp)
    (by simp only [List.mem_singleton, forall_eq]; decide)), kv, ?_, Kv⟩
  rw [e₈, U₇.gpr, U₆.gpr]
  by_cases hneg : 2 ^ 31 ≤ top
  · have cv : decide (2 ^ 32 ≤ (u₄.gpr .eax).toNat + (u₄.gpr .eax).toNat) = true :=
      decide_eq_true (by rw [v₄]; omega)
    have q1 := hQ1 hneg
    simp only [cv, ite_true, hneg]
    rw [BitVec.toNat_add, BitVec.toNat_allOnes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hQ32]
    omega
  · have cv : decide (2 ^ 32 ≤ (u₄.gpr .eax).toNat + (u₄.gpr .eax).toNat) = false :=
      decide_eq_false (by rw [v₄]; omega)
    simp only [cv, hneg, Bool.false_eq_true, ite_false, Nat.sub_zero]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hQ32]
    simpa using hQ32

/-- `stepQ`: `step`, and its quotient digit `⌊(r 2^32 + u) / m⌋` into `sQd`. -/
theorem stepQ_ok {s : State} (h : RtWs VG.Impl.Rsa.X86.RecoverRt.wid s B Z len N) {ml a r m t : Nat} (hm : MLen s B Z ml a)
    (hr : r < N) (hmN : m < N) (ht : t < N) (hrt : r ≠ t) (hmt : m ≠ t)
    (h4 : 4 ≤ wq a) (hw : wq a ≤ kw len) {M R : Nat}
    (hM : val32 s.mem B (arr (kw len) m) (wq a) = M) (hR : val32 s.mem B (arr (kw len) r) (wq a) = R)
    (hRM : R < M) (H : StepHdr s.mem B M (wq a)) :
    WP isa (VG.Impl.Rsa.X86.RecoverDetRt.stepQ ml r m t) s fun v =>
      RtWs VG.Impl.Rsa.X86.RecoverRt.wid v B Z len N ∧
      Keep B (kw len) [r, t] [oMask, oSteps, oQ, oU0, oU2, sQd] s.mem v.mem ∧
      val32 v.mem B (arr (kw len) r) (wq a) = (R * 2 ^ 32 + slot s.mem B oDig) % M ∧
      slot v.mem B sQd = (R * 2 ^ 32 + slot s.mem B oDig) / M ∧
      slot v.mem B oSteps = slot s.mem B oSteps ∧
      (∀ i, wq a ≤ i → i < kw len + 2 → mw v.mem B (kw len) r i = mw s.mem B (kw len) r i) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := by
  have nw := h.ws.workspace.nowrap
  have fr := h.ws.arr_fit hr
  have fm := h.ws.arr_fit hmN
  have ft := h.ws.arr_fit ht
  have hdr := h.ws.hdr_le
  simp only [S] at fr fm ft
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  have ws := h.rt
  have r160 : 160 ≤ arr (kw len) r := by simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega
  have m160 : 160 ≤ arr (kw len) m := by simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega
  obtain ⟨k, hk⟩ : ∃ k, wq a = k + 3 := ⟨wq a - 3, by omega⟩
  -- `r`'s top three words.
  have hx3 := VG.Proof.Bignum.WordTop32.val32_top3 s.mem B (arr (kw len) r) k
  rw [← hk, hR] at hx3
  obtain ⟨u0, hu0⟩ : ∃ u0, u0 = w32 s.mem B (arr (kw len) r + 4 * k) := ⟨_, rfl⟩
  obtain ⟨u1, hu1⟩ : ∃ u1, u1 = w32 s.mem B (arr (kw len) r + 4 * (k + 1)) := ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ u2, u2 = w32 s.mem B (arr (kw len) r + 4 * (k + 2)) := ⟨_, rfl⟩
  rw [← hu0, ← hu1, ← hu2] at hx3
  have hu0' : u0 < 2 ^ 32 := by rw [hu0]; exact (s.mem.readW _ 32).isLt
  have hu1' : u1 < 2 ^ 32 := by rw [hu1]; exact (s.mem.readW _ 32).isLt
  have hu2' : u2 < 2 ^ 32 := by rw [hu2]; exact (s.mem.readW _ 32).isLt
  have hlow := val32_lt s.mem B (arr (kw len) r) k
  obtain ⟨u, hu⟩ : ∃ u, u = slot s.mem B oDig := ⟨_, rfl⟩
  have hu32 : u < 2 ^ 32 := by rw [hu]; exact (s.mem.readW _ 32).isLt
  rw [← hu]
  -- `U`, `D` and the estimates.
  have hU : u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0 = (R * 2 ^ 32 + u) / 2 ^ (32 * k + 32) := by
    rw [div_low hu32, hx3]
    generalize val32 s.mem B (arr (kw len) r) k = lo at hlow
    generalize hG : 2 ^ (32 * k) = G at hlow
    have hG0 : 0 < G := by rw [← hG]; exact Nat.two_pow_pos _
    rw [show lo + G * u0 + G * 2 ^ 32 * (u1 + 2 ^ 32 * u2) = lo + G * (u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) by
      rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl]; grind,
      Nat.add_mul_div_left _ _ hG0, Nat.div_eq_of_lt hlow]
    omega
  obtain ⟨d, hdd⟩ : ∃ d, d = M / 2 ^ (32 * (wq a - 1)) := ⟨_, rfl⟩
  have hD : d * 2 ^ 32 + slot s.mem B oD1 = M / 2 ^ (32 * k + 32) := by
    rw [H.d1, hdd, show 32 * (wq a - 1) = 32 * k + 32 + 32 by omega, show 32 * (wq a - 2) = 32 * k + 32 by omega,
      Nat.pow_add (2 : Nat) (32 * k + 32), ← Nat.div_div_eq_div_mul]
    exact Nat.div_add_mod' _ _
  have hd1 : 2 ^ 31 ≤ d := by rw [hdd]; exact H.dn
  have hd2 : d < 2 ^ 32 := by
    rw [hdd, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
      show 32 + 32 * (wq a - 1) = 32 * wq a by omega]; exact H.lt
  have hYM : R * 2 ^ 32 + u < M * 2 ^ 32 := by
    have := Nat.mul_le_mul_right (2 ^ 32) (show R + 1 ≤ M by omega); rw [Nat.add_mul, Nat.one_mul] at this; omega
  have hq := VG.Proof.Bignum.WordStep32.qhat3_div (Y := R * 2 ^ 32 + u) (M := M) (P := 1) (K := 32 * k)
    (by decide) hYM (by rw [Nat.mul_one, ← hD, show (d * 2 ^ 32 + slot s.mem B oD1) / 2 ^ 32 = d by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt (s.mem.readW _ 32).isLt,
        Nat.zero_add]]; exact hd1)
  simp only [Nat.mul_one] at hq
  rw [← hU, ← hD] at hq
  obtain ⟨hUD, hq1, hq2, hge, hle⟩ := hq
  have eU2 : (u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / 2 ^ 32 = u2 * 2 ^ 32 + u1 := by
    rw [show u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0 = (u2 * 2 ^ 32 + u1) * 2 ^ 32 + u0 by
      rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl]; grind,
      Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hu0', Nat.zero_add]
  have eD2 : (d * 2 ^ 32 + slot s.mem B oD1) / 2 ^ 32 = d := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt (s.mem.readW _ 32).isLt, Nat.zero_add]
  rw [eU2, eD2] at hq1 hq2
  have hud : u2 ≤ d := by
    have e1 : u2 = R / 2 ^ (32 * (wq a - 1)) := by
      have h1 : (u2 * 2 ^ 32 + u1) / 2 ^ 32 = u2 := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hu1', Nat.zero_add]
      rw [← h1, ← eU2, hU, div_low hu32, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← Nat.pow_add,
        ← Nat.pow_add, show 32 * k + 32 + 32 = 32 * (wq a - 1) by omega]
    rw [e1, hdd]; exact Nat.div_le_div_right (Nat.le_of_lt hRM)
  -- `r`'s top words, `quot` and `refine3`.
  have hb₀ : arr (kw len) r + 4 * k + 12 ≤ Z := by omega
  unfold VG.Impl.Rsa.X86.RecoverDetRt.stepQ
  simp only [VG.Impl.Rsa.X86.Keys.seqs, List.append_assoc]
  refine WP.seq (topPtr_ok h hm hr (r := .ebx) (t := .ecx) (i := 3) (by decide) (by decide) (by decide)
    (by decide) (by omega) (by omega) fun u₀ K₀ m₀ p₀ _ => ?_)
  have di₀ : PtrAt u₀ B .edi 0 := by
    rw [PtrAt, K₀.1 _ (by decide), h.edi, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  have px : PtrAt u₀ B .ebx (arr (kw len) r + 4 * k) := by
    rw [show arr (kw len) r + 4 * k = arr (kw len) r + 4 * wq a - 4 * 3 by omega]; exact p₀
  refine topWords_ok (ws.of_keeps K₀) di₀ px hb₀ (by rw [oU2_val]; omega) fun t₁ m₁ bp₁ ax₁ K₁ => ?_
  rw [m₀, show arr (kw len) r + 4 * k + 8 = arr (kw len) r + 4 * (k + 2) by omega, ← hu0, ← hu2] at m₁
  rw [m₀, show arr (kw len) r + 4 * k + 4 = arr (kw len) r + 4 * (k + 1) by omega, ← hu1] at bp₁
  rw [m₀, show arr (kw len) r + 4 * k + 8 = arr (kw len) r + 4 * (k + 2) by omega, ← hu2] at ax₁
  have K₀₁ : Keeps [.eax, .ebx, .ecx, .ebp] s t₁ := (K₀.mono (by decide)).trans (K₁.mono (by decide))
  have di₁ : PtrAt t₁ B .edi 0 := by rw [PtrAt, K₁.1 _ (by decide)]; exact di₀
  have O₁ : Outside B oU0 8 s.mem t₁.mem := by
    rw [m₁]
    exact ((writeW32_outside _ B _ (d := oU0) (by rw [oU0_val]; omega)).mono (by omega) (by rw [oU0_val]; omega)).trans
      ((writeW32_outside _ B _ (d := oU2) (by rw [oU2_val]; omega)).mono (by decide) (by decide))
  have w₁ : ∀ o, o + 4 ≤ oU0 → w32 t₁.mem B o = w32 s.mem B o := fun o ho =>
    O₁.w32 (d := o) (.inl ho) (by rw [oU0_val] at ho; omega)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86.R2Words.WP.keeps [.eax, .ebx, .ecx, .edx, .esi]
    (VG.Proof.Bignum.X86.R2Words.quot_ok (h := h0) (ws.of_keeps K₀₁) di₁ (by simp only [h0]; omega) ax₁ bp₁
      (d := d) (by rw [w₁ _ (by decide)]; exact H.d.trans hdd.symm)
      (by rw [w₁ _ (by decide), hdd]; exact H.v) hd1 hd2 hud hu1') rfl)
    fun s₁ ⟨⟨hq₁, O₁', C₁, K₁'⟩, KK⟩ => ?_
  rw [VG.Proof.Bignum.WordTop32.qhat_min hud hu1' (by omega)] at hq₁
  have bp₂ : s₁.gpr .ebp = BitVec.ofNat 32 u1 := (KK.1 _ (by decide)).trans bp₁
  have K₀s₁ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s s₁ := (K₀₁.mono (by decide)).trans K₁'
  have di₂ : PtrAt s₁ B .edi 0 := by rw [PtrAt, K₁'.1 _ (by decide)]; exact di₁
  have wU0 : w32 s₁.mem B oU0 = u0 := by
    rw [O₁'.w32 (d := oU0) (.inr (by decide)) (by rw [oU0_val]; omega), m₁,
      w32_write_ne (size := Z) nw (by rw [oU2_val]; omega) (by rw [oU0_val]; omega) (by decide), w32_write_self,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu0']
  have wU2 : w32 s₁.mem B oU2 = u2 := by
    rw [O₁'.w32 (d := oU2) (.inr (by decide)) (by rw [oU2_val]; omega), m₁, w32_write_self,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu2']
  have wD : w32 s₁.mem B oD = d := by
    rw [O₁'.w32 (d := oD) (.inl (by decide)) (by decide), w₁ _ (by decide)]; exact H.d.trans hdd.symm
  have wD1 : w32 s₁.mem B oD1 = slot s.mem B oD1 := by
    rw [O₁'.w32 (d := oD1) (.inr (by decide)) (by decide), O₁.w32 (.inr (by decide)) (by decide)]
  refine WP.mono (VG.Proof.Bignum.X86.R2Words.refine3_ok (h := h0) (ws.of_keeps K₀s₁) di₂
    (by simp only [h0]; omega) (U := u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) (D := d * 2 ^ 32 + slot s.mem B oD1)
    (by rw [show VG.Impl.Bignum.X86.R2Words.oU2 h0 = oU2 from rfl, wU2, bp₂,
      show VG.Impl.Bignum.X86.R2Words.oU0 h0 = oU0 from rfl, wU0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu1'])
    (by rw [show VG.Impl.Bignum.X86.R2Words.oD h0 = oD from rfl, wD,
      show VG.Impl.Bignum.X86.R2Words.oD1 h0 = oD1 from rfl, wD1])
    (by omega) hUD (by rw [hq₁]; exact hq1) (by rw [hq₁]; exact hq2)) fun s₂ ⟨m₂, K₂⟩ => ?_
  generalize hQ : min ((u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / (d * 2 ^ 32 + slot s.mem B oD1)) (2 ^ 32 - 1) = Q
    at m₂ hge hle
  have hQlt : Q < 2 ^ 32 := by rw [← hQ]; exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  have O₂ : Outside B oQ 4 s₁.mem s₂.mem := by rw [m₂]; exact writeW32_outside _ B _ (by decide)
  have Ohdr : Outside B oMask 20 s.mem s₂.mem :=
    ((O₁.mono (by decide) (by decide)).trans (O₁'.mono (by decide) (by decide))).trans (O₂.mono (by decide) (by decide))
  have K₀₂ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s s₂ := K₀s₁.trans K₂
  have Z₂ : Outside B 0 Z s.mem s₂.mem := Ohdr.mono (Nat.zero_le _) (by rw [oMask_val]; omega)
  have h₂ : RtWs VG.Impl.Rsa.X86.RecoverRt.wid s₂ B Z len N := h.keep K₀₂ (by decide) (by decide) Z₂
  have hm₂ : MLen s₂ B Z ml a := hm.keep K₀₂ (by decide) Z₂
  have M₂ : val32 s₂.mem B (arr (kw len) m) (wq a) = M := by
    rw [Ohdr.val32 (.inr (by rw [oMask_val]; omega)) (by omega), hM]
  have R₂ : val32 s₂.mem B (arr (kw len) r) (wq a) = R := by
    rw [Ohdr.val32 (.inr (by rw [oMask_val]; omega)) (by omega), hR]
  have wQ : slot s₂.mem B oQ = Q := by
    rw [slot, m₂, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hQlt]
  have wDig : slot s₂.mem B oDig = u := by
    rw [slot, Ohdr.w32 (.inr (by decide)) (by decide), hu]
  -- `t = r 2^32 + u - Q m`.
  refine WP.seq (WP.mono (mulSub_ok h₂ hm₂ hr hmN ht hrt hmt (by omega) hw) fun s₃ ⟨h₃, k₃, ⟨b, hb, hv₃⟩, K₃⟩ => ?_)
  rw [wQ, M₂, R₂, wDig] at hv₃
  have Z₃ := VG.Proof.Rsa.X86.KeyRt.keep_outside h₂.ws k₃ (by simpa using ht) (by simp)
  have hm₃ : MLen s₃ B Z ml a := hm₂.keep K₃ (by decide) Z₃
  have M₃ : val32 s₃.mem B (arr (kw len) m) (wq a) = M := by
    rw [← M₂]; exact val32_congr fun i hi =>
      k₃.word (i := i) (by simp only [S]; omega) (by simpa using hmt.symm) (by simp) (h₂.ws.fit64 hmN)
  -- The digit.
  have tb : ∀ mm : Mem, (2 ^ 31 ≤ w32 mm B (arr (kw len) t + 4 * wq a)) ↔
      2 ^ (32 * (wq a + 1)) / 2 ≤ val32 mm B (arr (kw len) t) (wq a + 1) := fun mm => by
    rw [val32_succ]
    exact (VG.Proof.Bignum.WordTop32.topBit_iff (val32_lt _ _ _ _) (mm.readW _ 32).isLt).symm
  have hMW : 2 * M < 2 ^ (32 * (wq a + 1)) / 2 := by
    have := H.lt
    rw [show 32 * (wq a + 1) = 32 * wq a + 32 by omega, Nat.pow_add]; omega
  have hv₃' : val32 s₃.mem B (arr (kw len) t) (wq a + 1) + Q * M = R * 2 ^ 32 + u + 2 ^ (32 * (wq a + 1)) * b := by
    omega
  have dig := digit_of_sign (W := 2 ^ (32 * (wq a + 1))) (by omega) hMW hge hle (val32_lt _ _ _ _) hb hv₃'
  have wQ₃ : slot s₃.mem B oQ = Q := by
    rw [k₃.slot (e := oQ) (by decide) (by simp), wQ]
  refine WP.seq (WP.mono (digitQ_ok h₃ hm₃ ht hw (Q := Q) wQ₃ rfl
    (fun hn => dig.1 ((tb _).mp hn)) hQlt) fun s₃' ⟨h₃', k₃', d₃', K₃'⟩ => ?_)
  have Z₃' := VG.Proof.Rsa.X86.KeyRt.keep_outside (js := []) (ds := [sQd]) h₃.ws k₃' (by simp) (by simp only [List.mem_singleton, forall_eq]; decide)
  have hm₃' : MLen s₃' B Z ml a := hm₃.keep K₃' (by decide) Z₃'
  have M₃' : val32 s₃'.mem B (arr (kw len) m) (wq a) = M := by
    rw [← M₃]; exact val32_congr fun i hi =>
      k₃'.word (i := i) (by simp only [S]; omega) (by simp) (by simp only [List.mem_singleton, forall_eq]; decide)
        (h₃.ws.fit64 hmN)
  have T₃' : val32 s₃'.mem B (arr (kw len) t) (wq a + 1) = val32 s₃.mem B (arr (kw len) t) (wq a + 1) :=
    val32_congr fun i hi =>
      k₃'.word (i := i) (by simp only [S]; omega) (by simp) (by simp only [List.mem_singleton, forall_eq]; decide)
        (h₃.ws.fit64 ht)
  have tw₃' : w32 s₃'.mem B (arr (kw len) t + 4 * wq a) = w32 s₃.mem B (arr (kw len) t + 4 * wq a) :=
    k₃'.word (i := wq a) (by simp only [S]; omega) (by simp) (by simp only [List.mem_singleton, forall_eq]; decide)
      (h₃.ws.fit64 ht)
  have sQd₃' : slot s₃'.mem B sQd = (R * 2 ^ 32 + u) / M := by
    rw [d₃', ← dig.2]
    congr 1
    by_cases hn : 2 ^ 31 ≤ w32 s₃.mem B (arr (kw len) t + 4 * wq a)
    · simp only [hn, (tb _).mp hn, ite_true]
    · simp only [hn, show ¬ (2 ^ (32 * (wq a + 1)) / 2 ≤ val32 s₃.mem B (arr (kw len) t) (wq a + 1)) from
        fun c => hn ((tb _).mpr c), ite_false]
  -- `t := t + m` if negative.
  refine WP.seq (WP.mono (addBack_ok h₃' hm₃' hmN ht hmt (by omega) hw) fun s₄ ⟨h₄, k₄, ⟨c, hc, hv₄⟩, K₄⟩ => ?_)
  rw [M₃', T₃', tw₃'] at hv₄
  have Z₄ := VG.Proof.Rsa.X86.KeyRt.keep_outside h₃'.ws k₄ (by simpa using ht) (by simp)
  have hm₄ : MLen s₄ B Z ml a := hm₃'.keep K₄ (by decide) Z₄
  have hv₄' : val32 s₄.mem B (arr (kw len) t) (wq a + 1) + 2 ^ (32 * (wq a + 1)) * c =
      val32 s₃.mem B (arr (kw len) t) (wq a + 1) +
        if 2 ^ (32 * (wq a + 1)) / 2 ≤ val32 s₃.mem B (arr (kw len) t) (wq a + 1) then M else 0 := by
    simp only [tb] at hv₄; exact hv₄
  have hT := VG.Proof.Bignum.WordStep32.wordStepQ1_div (W := 2 ^ (32 * (wq a + 1))) (Y := R * 2 ^ 32 + u)
    (by omega) hMW hge hle (val32_lt _ _ _ _) hb (by omega) (val32_lt _ _ _ _) hc hv₄'
  -- `t` back into `r`.
  refine WP.mono (copyBack_ok h₄ hm₄ hr ht hrt (by omega) hw) fun v ⟨hv, kv, ev, Ov, Kv⟩ => ?_
  have top0 : w32 s₄.mem B (arr (kw len) t + 4 * wq a) = 0 := by
    have hr' : (R * 2 ^ 32 + u) % M < 2 ^ (32 * wq a) := Nat.lt_trans (Nat.mod_lt _ (by omega)) H.lt
    rw [← hT, val32_succ] at hr'
    by_contra hc
    have := Nat.mul_le_mul_left (2 ^ (32 * wq a)) (show 1 ≤ w32 s₄.mem B (arr (kw len) t + 4 * wq a) by omega)
    omega
  have Ksv : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := K₀₂.trans (K₃.trans ((K₃'.mono (by decide)).trans (K₄.trans Kv)))
  have nQ : ∀ d ∈ [sQd], d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by simp only [List.mem_singleton, forall_eq]; decide
  refine ⟨hv, ?_, ?_, ?_, ?_, ?_, Ksv⟩
  · exact (keep_of_five (js := [r, t]) (ds := [oMask, oSteps, oQ, oU0, oU2, sQd]) Ohdr (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans ((k₃.mono (by simp) (by simp)).trans
        ((k₃'.mono (by simp) (by simp)).trans ((k₄.mono (by simp) (by simp)).trans (kv.mono (by simp) (by simp)))))
  · rw [ev, ← hT, val32_succ, top0, Nat.mul_zero, Nat.add_zero]
  · rw [kv.slot (e := sQd) (by decide) (by simp), k₄.slot (e := sQd) (by decide) (by simp), sQd₃']
  · rw [kv.slot (e := oSteps) (by decide) (by simp), k₄.slot (e := oSteps) (by decide) (by simp),
      k₃'.slot (e := oSteps) (by decide) (by simp only [List.mem_singleton, forall_eq]; decide),
      k₃.slot (e := oSteps) (by decide) (by simp)]
    show w32 s₂.mem B oSteps = w32 s.mem B oSteps
    have e1 : w32 s₂.mem B oSteps = w32 s₁.mem B oSteps := O₂.w32 (.inl (by decide)) (by decide)
    have e2 : w32 s₁.mem B oSteps = w32 t₁.mem B oSteps := C₁
    rw [e1, e2, O₁.w32 (.inl (by decide)) (by decide)]
  · intro i hi1 hi2
    rw [mw, Ov.w32 (.inr (by omega)) (by omega)]
    rw [k₄.word (i := i) (by simp only [S]; omega) (by simpa using hrt.symm) (by simp) (h₃'.ws.fit64 hr),
      k₃'.word (i := i) (by simp only [S]; omega) (by simp) nQ (h₃.ws.fit64 hr),
      k₃.word (i := i) (by simp only [S]; omega) (by simpa using hrt.symm) (by simp) (h₂.ws.fit64 hr),
      Ohdr.w32 (.inr (by rw [oMask_val]; omega)) (by omega)]

/-! ## The seed for a dividend of `W` or `W + 1` words -/

/-- The dividend's words: `W`, and one more where `extra`. -/
abbrev xn (len : Nat) (extra : Bool) : Nat := kw len + extra.toNat

/-- `bytesB`, plus 4 where `extra`: `r = 4 X`. -/
theorem xBytesX_ok {s : State} {is : List Instr} {Q : State → Prop} (h : RtWs VG.Impl.Rsa.X86.RecoverRt.wid s B Z len N)
    {extra : Bool} {r : Reg}
    (k : ∀ t, Keeps [r] s t → t.mem = s.mem → (t.gpr r).toNat = 4 * xn len extra → WP isa (.block is) t Q) :
    WP isa (.block (bytesB VG.Impl.Rsa.X86.RecoverRt.wid r ++
      ((if extra then [.alu .add r (.imm 4)] else []) ++ is))) s Q := by
  have hw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  refine VG.Proof.Rsa.X86.KeyRt.bytesB_ok (lenSrc h) h.lenLe fun t K m e => ?_
  cases extra with
  | false => simpa [xn] using k t K m (by simpa [xn] using e)
  | true =>
    simp only [ite_true, List.cons_append, List.nil_append]
    refine wp_addS rfl fun u U _ => k u (K.trans U.keeps) (U.mem.trans m) ?_
    rw [U.gpr, BitVec.toNat_add, e]; simp only [xn, Bool.toNat_true]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega

open VG.Impl.Rsa.X86.KeyRt (restoreEdi bytesB) in
/-- `seedX ml x r extra`: `seed` for a dividend of `W + 1` words (`extra`) or `W`. -/
theorem seedX_ok {s : State} (h : RtWs VG.Impl.Rsa.X86.RecoverRt.wid s B Z len N) {ml a x r : Nat} {extra : Bool} (hm : MLen s B Z ml a)
    (hx : x < N) (hr : r < N) (hxr : r ≠ x)
    (h3 : 3 ≤ wq a) (hw : wq a ≤ kw len) :
    WP isa (VG.Impl.Rsa.X86.RecoverDetRt.seedX ml x r extra) s fun v => RtWs VG.Impl.Rsa.X86.RecoverRt.wid v B Z len N ∧
      Keep B (kw len) [r] [oSteps] s.mem v.mem ∧
      val32 v.mem B (arr (kw len) r) (kw len + 1) =
        val32 s.mem B (arr (kw len) x) (xn len extra) / 2 ^ (32 * (xn len extra - (wq a - 1))) ∧
      slot v.mem B oSteps = xn len extra - wq a + 1 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := by
  have nw := h.ws.workspace.nowrap
  have fr := h.ws.arr_fit hr
  have fx := h.ws.arr_fit (j := x) hx
  have hdr := h.ws.hdr_le
  have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  simp only [S] at fr fx
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  have ws := h.rt
  have xnb : kw len ≤ xn len extra ∧ xn len extra ≤ kw len + 1 := by cases extra <;> simp [xn]
  have hX : wq a ≤ xn len extra := by omega
  have hX4 : arr (kw len) x + 4 * xn len extra + 4 ≤ arr (kw len) x + 4 * (kw len + 2) := by omega
  have sepr : arr (kw len) r + 4 * (kw len + 2) ≤ arr (kw len) x ∨
      arr (kw len) x + 4 * xn len extra + 4 ≤ arr (kw len) r := by
    rcases Nat.lt_or_gt_of_ne hxr with hlt | hgt
    · have := VG.Proof.Rsa.X86.Keys.arr_end (w := kw len) hlt; simp only [S] at this; omega
    · have := VG.Proof.Rsa.X86.Keys.arr_end (w := kw len) hgt
      simp only [S] at this ⊢; right; omega
  unfold VG.Impl.Rsa.X86.RecoverDetRt.seedX
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok h hr) fun u₁ ⟨h₁, k₁, z₁, K₁⟩ => ?_)
  have xk : ∀ o, arr (kw len) x ≤ o → o + 4 ≤ arr (kw len) x + 4 * xn len extra + 4 →
      w32 u₁.mem B o = w32 s.mem B o := fun o h1 h2 => by
    have := VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws k₁ (by simpa using hr) (by simp)
    have O : Outside B (arr (kw len) r) (4 * (kw len + 2)) s.mem u₁.mem := fun y hy =>
      k₁ y fun q hq => by
        simp only [VG.Proof.Rsa.X86.Keys.ranges, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false, S] at hq
        subst hq; exact hy
    exact O.w32 (by omega) (by omega)
  -- The pointers.
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (arrPtr_ok (lenSrc h₁) h₁.lenLe h₁.edi (r := .esi) (t := .edx) (j := x) (by decide) (by decide)
    (by omega) fun u₂ K₂ m₂ p₂ _ => ?_)
  refine xBytesX_ok (h₁.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)) (extra := extra)
    (r := .ecx) fun u₃ K₃ m₃ e₃ => wp_addS rfl fun u₄ U₄ _ => ?_
  have hm₁ : MLen u₁ B Z ml a := hm.keep K₁ (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws k₁
    (by simpa using hr) (by simp))
  have K₂₄ : Keeps [.ecx, .edx, .esi] u₁ u₄ := ((K₂.mono (by decide)).trans (K₃.mono (by decide))).trans
    (U₄.keeps.mono (by decide))
  have m₄ : u₄.mem = u₁.mem := by rw [U₄.mem, m₃, m₂]
  refine width4_ok (hm₁.keep K₂₄ (by decide) (by rw [m₄]; exact Outside.refl _ _ _ _)) fun u₅ K₅ m₅ e₅ => ?_
  refine wp_subS rfl fun u₆ U₆ _ => wp_subS rfl fun u₇ U₇ _ => ?_
  have K₂₇ : Keeps [.ecx, .edx, .esi] u₁ u₇ := (K₂₄.trans (K₅.mono (by decide))).trans
    ((U₆.keeps.mono (by decide)).trans (U₇.keeps.mono (by decide)))
  have m₇ : u₇.mem = u₁.mem := by rw [U₇.mem, U₆.mem, m₅, m₄]
  have edi₇ : (u₇.gpr .edi).toNat = B.toNat := by rw [K₂₇.1 _ (by decide)]; exact h₁.edi
  have esi₇ : PtrAt u₇ B .esi (arr (kw len) x + 4 * (xn len extra - (wq a - 1))) := by
    have hw4 : (BitVec.ofNat 32 (4 * wq a)).toNat = 4 * wq a := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hm.le; omega)
    have p₄ : (u₄.gpr .esi).toNat = B.toNat + (arr (kw len) x + 4 * xn len extra) := by
      rw [U₄.gpr, BitVec.toNat_add, e₃, show (u₃.gpr .esi) = u₂.gpr .esi from K₃.1 _ (by decide), p₂]
      have := B.isLt
      omega
    rw [PtrAt, U₇.gpr, BitVec.toNat_sub, U₆.gpr, U₆.other .esi (by decide), K₅.1 .esi (by decide), p₄, e₅,
      BitVec.toNat_sub, hw4, show (4 : BitVec 32).toNat = 4 from rfl]
    have := B.isLt
    omega
  have hl₇ := (lenSrc h₁).keep K₂₇ (by decide) m₇
  refine arrPtr_ok hl₇ h₁.lenLe edi₇ (r := .ebp) (t := .edx) (j := r) (by decide) (by decide) (by omega)
    fun u₈ K₈ m₈ p₈ _ => ?_
  have K₂₈ : Keeps [.ecx, .edx, .esi, .ebp] u₁ u₈ := (K₂₇.mono (by decide)).trans (K₈.mono (by decide))
  have m₈' : u₈.mem = u₁.mem := by rw [m₈, m₇]
  refine width4_ok (hm₁.keep K₂₈ (by decide) (by rw [m₈']; exact Outside.refl _ _ _ _)) fun u₉ K₉ m₉ e₉ =>
    wp_subZ rfl fun u₁₀ U₁₀ z₁₀ => WP.block_nil ?_
  have K₁₀ : Keeps [.ecx, .edx, .esi, .ebp, .edi] u₁ u₁₀ := ((K₂₈.mono (by decide)).trans (K₉.mono (by decide))).trans
    (U₁₀.keeps.mono (by decide))
  have m₁₀ : u₁₀.mem = u₁.mem := by rw [U₁₀.mem, m₉, m₈']
  have hw4 : (BitVec.ofNat 32 (4 * wq a)).toNat = 4 * wq a := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hm.le; omega)
  have di₁₀ : (u₁₀.gpr .edi).toNat = 4 * (wq a - 1) := by
    rw [U₁₀.gpr, BitVec.toNat_sub, e₉, hw4, show (4 : BitVec 32).toNat = 4 from rfl]; omega
  have zf : u₁₀.zf = some false := by
    rw [z₁₀, ← U₁₀.gpr]
    congr 1
    rw [beq_eq_false_iff_ne]
    intro hc
    have := congrArg BitVec.toNat hc
    rw [di₁₀] at this; simp at this; omega
  refine WP.seq (WP.ite false zf (fun f => absurd f (by decide)) fun _ => ?_)
  -- The copy.
  have g : SubGeo B Z (arr (kw len) r) (arr (kw len) r) (arr (kw len) x + 4 * (xn len extra - (wq a - 1)))
      (wq a - 1) :=
    ⟨nw, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have I₀ : CopyI u₁₀ B (arr (kw len) r) (arr (kw len) x + 4 * (xn len extra - (wq a - 1))) (wq a - 1) 0 u₁₀ :=
    ⟨by rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₁₀.other _ (by decide), K₉.1 _ (by decide), K₈.1 _ (by decide)];
        exact esi₇,
      by rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₁₀.other _ (by decide), K₉.1 _ (by decide)]; exact p₈,
      by apply BitVec.eq_of_toNat_eq; rw [di₁₀, Nat.sub_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
      Keeps.refl _ _, Outside.refl _ _ _ _, by simp [val32]⟩
  have wsu := ws.of_keeps K₁ |>.of_keeps K₁₀
  refine WP.mono (WP.loop (M := isa)
    (Q := fun u => CopyI u₁₀ B (arr (kw len) r) (arr (kw len) x + 4 * (xn len extra - (wq a - 1))) (wq a - 1)
      (wq a - 1) u)
    (fun n u => ∃ j, n = wq a - 1 - j ∧ j < wq a - 1 ∧
      CopyI u₁₀ B (arr (kw len) r) (arr (kw len) x + 4 * (xn len extra - (wq a - 1))) (wq a - 1) j u) ?_ _ u₁₀
      ⟨0, rfl, by omega, I₀⟩) fun u I => ?_
  · rintro n u ⟨j, rfl, hj, I⟩
    refine WP.mono (copyStep_ok wsu g hj I) fun u' ⟨z, I'⟩ => ?_
    by_cases e : j + 1 = wq a - 1
    · exact .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], e ▸ I'⟩
    · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], wq a - 1 - (j + 1),
        by omega, j + 1, rfl, by omega, I'⟩
  -- The steps' count.
  have K₁u : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] u₁ u := (K₁₀.mono (by decide)).trans I.keep
  have O₁u : Outside B (arr (kw len) r) (4 * (wq a - 1)) u₁.mem u.mem := by rw [← m₁₀]; exact I.out
  have Z₁u : Outside B 0 Z u₁.mem u.mem := O₁u.mono (Nat.zero_le _) (by omega)
  have ca := h₁.wsArg.keep K₁u (by decide) Z₁u
  simp only [restoreEdi, List.cons_append, List.nil_append]
  refine wp_movS ca.readSrc fun v₁ V₁ _ => ?_
  have K₁v₁ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] u₁ v₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .esi, .ebp])
      ((K₁u.trans (V₁.keeps.mono (by decide))).mono (by decide)) (V₁.gpr.trans h₁.edi_eq.symm)
  have hv₁ : RtWs VG.Impl.Rsa.X86.RecoverRt.wid v₁ B Z len N := h₁.keep K₁v₁ (by decide) (by decide) (by rw [V₁.mem]; exact Z₁u)
  refine xBytesX_ok hv₁ (extra := extra) (r := .eax) fun v₂ K₂' m₂' e₂' => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun v₃ V₃ => ?_
  have hm₃ : MLen v₃ B Z ml a := hm₁.keep ((K₁v₁.trans (K₂'.mono (by decide))).trans (V₃.keeps.mono (by decide)))
    (by decide) (by rw [V₃.mem, m₂', V₁.mem]; exact Z₁u)
  refine width4_ok hm₃ fun v₄ K₄' m₄' e₄' => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun v₅ V₅ => ?_
  refine wp_subS rfl fun v₆ V₆ _ => wp_addS rfl fun v₇ V₇ _ => ?_
  have K₁v₇ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] u₁ v₇ :=
    (K₁v₁.trans (K₂'.mono (by decide))).trans (((V₃.keeps.mono (by decide)).trans (K₄'.mono (by decide))).trans
      (((V₅.keeps.mono (by decide)).trans (V₆.keeps.mono (by decide))).trans (V₇.keeps.mono (by decide))))
  have m₇' : v₇.mem = u.mem := by rw [V₇.mem, V₆.mem, V₅.mem, m₄', V₃.mem, m₂', V₁.mem]
  have hv₇ : RtWs VG.Impl.Rsa.X86.RecoverRt.wid v₇ B Z len N := h₁.keep K₁v₇ (by decide) (by decide) (by rw [m₇']; exact Z₁u)
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.storeSlot_ok hv₇ (d := oSteps) (by decide) .eax)
    fun v ⟨hv, kv, ev, Kv⟩ => ?_
  have hXk : xn len extra ≤ 2 * kw len := by omega
  have eax₇ : (v₇.gpr .eax).toNat = xn len extra - wq a + 1 := by
    have h3' : (v₃.gpr .eax).toNat = xn len extra := by
      rw [V₃.gpr, BitVec.toNat_ushiftRight, e₂', Nat.shiftRight_eq_div_pow]; omega
    have h5' : (v₅.gpr .ecx).toNat = wq a := by
      rw [V₅.gpr, BitVec.toNat_ushiftRight, e₄', hw4, Nat.shiftRight_eq_div_pow]; omega
    rw [V₇.gpr, BitVec.toNat_add, V₆.gpr, BitVec.toNat_sub, h5', V₅.other .eax (by decide),
      K₄'.1 .eax (by decide), h3', show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v :=
    (K₁.mono (by decide)).trans (K₁v₇.trans (Kv.mono (by decide)))
  refine ⟨hv, ?_, ?_, by rw [ev, eax₇], Kall⟩
  · refine (k₁.mono (by simp) (by simp)).trans (Keep.trans ?_ (kv.mono (by simp) (by simp)))
    rw [m₇']
    exact Keep.of_arr (d := 0) (by simpa using O₁u) (by simp only [S]; omega) (by simp)
  · -- The words of `r`.
    have fitr := h.ws.fit64 hr
    have hk : val32 v.mem B (arr (kw len) r) (kw len + 1) = val32 u.mem B (arr (kw len) r) (kw len + 1) := by
      rw [← m₇']
      exact val32_congr fun i hi => kv.word (j := r) (i := i) (by simp only [S]; omega) (by simp) (by decide) fitr
    rw [hk, show kw len + 1 = (wq a - 1) + (kw len + 2 - wq a) by omega, val32_append, I.val, m₁₀]
    have hi : val32 u.mem B (arr (kw len) r + 4 * (wq a - 1)) (kw len + 2 - wq a) = 0 := by
      rw [O₁u.val32 (.inr (by omega)) (by omega), ← val32_high,
        show wq a - 1 + (kw len + 2 - wq a) = kw len + 1 by omega, z₁, Nat.zero_div]
    have hlo : val32 u₁.mem B (arr (kw len) x + 4 * (xn len extra - (wq a - 1))) (wq a - 1) =
        val32 s.mem B (arr (kw len) x + 4 * (xn len extra - (wq a - 1))) (wq a - 1) :=
      val32_congr fun i hi => xk _ (by omega) (by omega)
    rw [hi, Nat.mul_zero, Nat.add_zero, hlo, ← val32_high,
      show xn len extra - (wq a - 1) + (wq a - 1) = xn len extra by omega]


/-! ## The loop, with the quotient -/

/-- A quotient step: `⌊⌊X / 2^(32 k)⌋ / M⌋` from `⌊⌊X / 2^(32 (k + 1))⌋ / M⌋` and the step's digit. -/
theorem quo_step (X M k : Nat) (hM : 0 < M) :
    X / 2 ^ (32 * k) / M = X / 2 ^ (32 * (k + 1)) / M * 2 ^ 32 +
      (X / 2 ^ (32 * (k + 1)) % M * 2 ^ 32 + X / 2 ^ (32 * k) % 2 ^ 32) / M := by
  have e1 : X / 2 ^ (32 * k) = X / 2 ^ (32 * (k + 1)) * 2 ^ 32 + X / 2 ^ (32 * k) % 2 ^ 32 := by
    have : X / 2 ^ (32 * (k + 1)) = X / 2 ^ (32 * k) / 2 ^ 32 := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show 32 * k + 32 = 32 * (k + 1) by omega]
    rw [this]; exact (Nat.div_add_mod' _ _).symm
  generalize X / 2 ^ (32 * (k + 1)) = Y at e1 ⊢
  generalize X / 2 ^ (32 * k) % 2 ^ 32 = u at e1 ⊢
  rw [e1]
  have dm := Nat.div_add_mod Y M
  conv => lhs; rw [← dm]
  rw [show (M * (Y / M) + Y % M) * 2 ^ 32 + u = (Y % M * 2 ^ 32 + u) + Y / M * 2 ^ 32 * M by
    rw [Nat.add_mul]; grind, Nat.add_mul_div_right _ _ hM, Nat.add_comm]

/-- What `wordDivQ`'s loop keeps, after `i` of its `Sc` steps, from `s₀` (after `seedX`): the
remainder as `wordMod`'s, the dividend's words below `Sc - i` and from `Sc` on, and above them the
quotient so far. -/
structure LoopQ (s₀ : State) (B : Addr) (Z len N ml a x r t : Nat) (M X₀ Sc i : Nat) (u : State) : Prop where
  ws : RtWs VG.Impl.Rsa.X86.RecoverRt.wid u B Z len N
  ml : MLen u B Z ml a
  keep : Keep B (kw len) [r, t, x] [oMask, oSteps, oQ, oU0, oU2, oDig, sQd] s₀.mem u.mem
  rest : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s₀ u
  val : val32 u.mem B (arr (kw len) r) (wq a) = X₀ / 2 ^ (32 * (Sc - i)) % M
  high : ∀ j, wq a ≤ j → j < kw len + 1 → mw u.mem B (kw len) r j = 0
  steps : slot u.mem B oSteps = Sc - i
  xlo : ∀ j < Sc - i, w32 u.mem B (arr (kw len) x + 4 * j) = w32 s₀.mem B (arr (kw len) x + 4 * j)
  xq : val32 u.mem B (arr (kw len) x + 4 * (Sc - i)) i = X₀ / 2 ^ (32 * (Sc - i)) / M
  xhi : ∀ j, Sc ≤ j → j < kw len + 2 → w32 u.mem B (arr (kw len) x + 4 * j) = w32 s₀.mem B (arr (kw len) x + 4 * j)


/-- `ebx` at the dividend's word `S - 1`, `S` the steps left (`oSteps`). -/
theorem xPtr_ok {s : State} (h : RtWs VG.Impl.Rsa.X86.RecoverRt.wid s B Z len N) {x St : Nat} (hx : x < N)
    (hS : slot s.mem B oSteps = St) (hS1 : 1 ≤ St) (hSx : St ≤ kw len + 2) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Keeps [.eax, .ebx, .edx] s u → u.mem = s.mem →
      PtrAt u B .ebx (arr (kw len) x + 4 * (St - 1)) → WP isa (.block is) u Q) :
    WP isa (.block (arrPtr VG.Impl.Rsa.X86.RecoverRt.wid .ebx x .edx ++ (([.mov .eax (.mem (sc oSteps)),
      .alu .sub .eax (.imm 1), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
      .alu .add .ebx (.reg .eax)] : List Instr) ++ is))) s Q := by
  have nw := h.ws.workspace.nowrap
  have fx := h.ws.arr_fit hx
  have hdr := h.ws.hdr_le
  have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  simp only [S] at fx
  refine arrPtr_ok (lenSrc h) h.lenLe h.edi (r := .ebx) (t := .edx) (j := x) (by decide) (by decide)
    (by omega) fun u₁ K₁ m₁ p₁ _ => ?_
  have h₁ := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  simp only [List.cons_append]
  refine wp_movS (readHdr h₁.ws (d := oSteps) (by decide)) fun u₂ U₂ _ => wp_subS rfl fun u₃ U₃ _ =>
    wp_addS rfl fun u₄ U₄ _ => wp_addS rfl fun u₅ U₅ _ => wp_addS rfl fun u₆ U₆ _ => ?_
  have e₂ : (u₂.gpr .eax).toNat = St := by
    rw [U₂.gpr, m₁, hS, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e₅ : (u₅.gpr .eax).toNat = 4 * (St - 1) := by
    rw [U₅.gpr, BitVec.toNat_add, U₄.gpr, BitVec.toNat_add, U₃.gpr, BitVec.toNat_sub, e₂,
      show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  refine k u₆ ((K₁.mono (by decide)).trans (((U₂.keeps.mono (by decide)).trans (U₃.keeps.mono (by decide))).trans
      (((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide))).trans (U₆.keeps.mono (by decide)))))
    (by rw [U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, m₁]) ?_
  rw [PtrAt, U₆.gpr, BitVec.toNat_add, U₅.other .ebx (by decide), U₄.other .ebx (by decide),
    U₃.other .ebx (by decide), U₂.other .ebx (by decide), p₁, e₅]
  have := B.isLt; omega

/-- `digitStepQ`: a step of `wordDivQ`'s loop, its digit stored over the dividend's word it brought
down. -/
theorem digitStepQ_ok {s₀ u : State} {ml a x r m t : Nat} {extra : Bool} {M X₀ Sc i : Nat}
    (hx : x < N) (hr : r < N) (hmN : m < N) (ht : t < N) (hrt : r ≠ t) (hmt : m ≠ t)
    (hrm : r ≠ m) (hxr : r ≠ x) (hxt : t ≠ x) (hxm : m ≠ x)
    (h4 : 4 ≤ wq a) (hw : wq a ≤ kw len)
    (hX : val32 s₀.mem B (arr (kw len) x) (xn len extra) = X₀) (hM : val32 s₀.mem B (arr (kw len) m) (wq a) = M)
    (H : StepHdr s₀.mem B M (wq a)) (hS : Sc = xn len extra - wq a + 1) (hi : i < Sc)
    (I : LoopQ s₀ B Z len N ml a x r t M X₀ Sc i u) :
    WP isa (VG.Impl.Rsa.X86.RecoverDetRt.digitStepQ ml x r m t) u fun v =>
      LoopQ s₀ B Z len N ml a x r t M X₀ Sc (i + 1) v ∧ v.zf = some (decide (i + 1 = Sc)) := by
  have h := I.ws
  have nw := h.ws.workspace.nowrap
  have fx := h.ws.arr_fit hx
  have hdr := h.ws.hdr_le
  have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  simp only [S] at fx
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  have xnb : kw len ≤ xn len extra ∧ xn len extra ≤ kw len + 1 := by cases extra <;> simp [xn]
  have nQ : ∀ d ∈ [sQd], d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by simp only [List.mem_singleton, forall_eq]; decide
  have Mu : val32 u.mem B (arr (kw len) m) (wq a) = M := by
    rw [← hM]
    exact val32_congr fun j hj => I.keep.word (j := m) (i := j) (by simp only [S]; omega)
      (by simp; omega) (by decide) (h.ws.fit64 hmN)
  have Hu : StepHdr u.mem B M (wq a) := H.keep (I.keep.slot (by decide) (by decide))
    (I.keep.slot (by decide) (by decide)) (I.keep.slot (by decide) (by decide))
  have hk : Sc - i - 1 < xn len extra := by omega
  have hM0 : 0 < M := by have := H.dn; rcases Nat.eq_zero_or_pos M with e | e <;> simp_all
  -- The digit.
  unfold VG.Impl.Rsa.X86.RecoverDetRt.digitStepQ
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (xPtr_ok h hx I.steps (by omega) (by omega) fun u₆ K₁₆ m₆ p₆ => ?_)
  refine wp_movS (readSrc_ptr (h.rt.of_keeps K₁₆) p₆ (d := 0) (by omega)) fun u₇ U₇ _ => ?_
  have K₁₇ : Keeps [.eax, .ebx, .edx] u u₇ := K₁₆.trans (U₇.keeps.mono (by decide))
  have h₇ := h.keep K₁₇ (by decide) (by decide) (by rw [U₇.mem, m₆]; exact Outside.refl _ _ _ _)
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.storeSlot_ok h₇ (d := oDig) (by decide) .eax) fun u₈ ⟨h₈, k₈, e₈, K₈⟩ => ?_
  have Z₈ := VG.Proof.Rsa.X86.KeyRt.keep_outside h₇.ws k₈ (by simp) (by decide)
  have K₀₈ : Keeps [.eax, .ebx, .edx] u u₈ := K₁₇.trans (K₈.mono (by simp))
  have Zu₈ : Outside B 0 Z u.mem u₈.mem := by rw [U₇.mem, m₆] at Z₈; exact Z₈
  have hm₈ : MLen u₈ B Z ml a := I.ml.keep K₀₈ (by decide) Zu₈
  have k₀₈ : Keep B (kw len) [] [oDig] u.mem u₈.mem := by rw [U₇.mem, m₆] at k₈; exact k₈
  have dig : slot u₈.mem B oDig = X₀ / 2 ^ (32 * (Sc - i - 1)) % 2 ^ 32 := by
    rw [e₈, U₇.gpr, m₆, Nat.add_zero]
    change w32 u.mem B (arr (kw len) x + 4 * (Sc - i - 1)) = _
    rw [I.xlo _ (by omega), ← hX]
    exact w32_of_val32 s₀.mem B hk
  have R₈ : val32 u₈.mem B (arr (kw len) r) (wq a) = X₀ / 2 ^ (32 * (Sc - i)) % M := by
    rw [← I.val]
    exact val32_congr fun j hj => k₀₈.word (j := r) (i := j) (by simp only [S]; omega) (by simp) (by decide)
      (h.ws.fit64 hr)
  have M₈ : val32 u₈.mem B (arr (kw len) m) (wq a) = M := by
    rw [← Mu]
    exact val32_congr fun j hj => k₀₈.word (j := m) (i := j) (by simp only [S]; omega) (by simp) (by decide)
      (h.ws.fit64 hmN)
  have H₈ : StepHdr u₈.mem B M (wq a) := Hu.keep (k₀₈.slot (by decide) (by decide))
    (k₀₈.slot (by decide) (by decide)) (k₀₈.slot (by decide) (by decide))
  -- The step.
  refine WP.seq (WP.mono (stepQ_ok h₈ hm₈ hr hmN ht hrt hmt h4 hw M₈ R₈ (Nat.mod_lt _ hM0) H₈)
    fun v₁ ⟨hv₁, kv₁, ev₁, qv₁, sv₁, hiv₁, Kv₁⟩ => ?_)
  rw [dig] at ev₁ qv₁
  have st : slot v₁.mem B oSteps = Sc - i := by rw [sv₁, k₀₈.slot (by decide) (by decide)]; exact I.steps
  -- The digit stored.
  refine WP.seq (xPtr_ok hv₁ hx st (by omega) (by omega) fun w₆ KW₆ mw₆ pw₆ => ?_)
  refine wp_movS (readHdr (hv₁.ws.rest KW₆) (d := sQd) (by decide)) fun w₇ W₇ _ => ?_
  have KW₇ : Keeps [.eax, .ebx, .edx] v₁ w₇ := KW₆.trans (W₇.keeps.mono (by decide))
  have wsw := (hv₁.rt.of_keeps KW₇)
  have pw₇ : PtrAt w₇ B .ebx (arr (kw len) x + 4 * (Sc - i - 1)) := by
    rw [PtrAt, W₇.other _ (by decide)]; exact pw₆
  refine wp_storeS (ea_ptr wsw pw₇ (d := 0) (by omega)) (ws_write wsw (by omega)) fun w₈ MW₈ => WP.block_nil ?_
  -- The digit's value.
  obtain ⟨D, hD⟩ : ∃ D, D = (X₀ / 2 ^ (32 * (Sc - i)) % M * 2 ^ 32 + X₀ / 2 ^ (32 * (Sc - i - 1)) % 2 ^ 32) / M :=
    ⟨_, rfl⟩
  rw [← hD] at qv₁
  have hDlt : D < 2 ^ 32 := by
    rw [hD, Nat.div_lt_iff_lt_mul hM0]
    have := Nat.mod_lt (X₀ / 2 ^ (32 * (Sc - i))) hM0
    have := Nat.mod_lt (X₀ / 2 ^ (32 * (Sc - i - 1))) (show 0 < 2 ^ 32 by decide)
    have : (X₀ / 2 ^ (32 * (Sc - i)) % M + 1) * 2 ^ 32 ≤ M * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have g₇ : w₇.gpr .eax = BitVec.ofNat 32 D := by rw [W₇.gpr, mw₆, qv₁]
  have m₈ : w₈.mem = v₁.mem.writeW (off B (arr (kw len) x + 4 * (Sc - i - 1))) (BitVec.ofNat 32 D) := by
    rw [MW₈.mem, W₇.mem, mw₆, g₇, Nat.add_zero]
  have Ox := writeW32_outside v₁.mem B (d := arr (kw len) x + 4 * (Sc - i - 1)) (BitVec.ofNat 32 D) (by omega)
  rw [← m₈] at Ox
  have kx : Keep B (kw len) [x] [] v₁.mem w₈.mem :=
    Keep.of_arr (d := 4 * (Sc - i - 1)) Ox (by simp only [S]; omega) (by simp)
  have KW₈ : Keeps [.eax, .ebx, .edx] v₁ w₈ := KW₇.trans ((MW₈.keeps []).mono (by simp))
  have hw₈ := hv₁.keep KW₈ (by decide) (by decide)
    (VG.Proof.Rsa.X86.KeyRt.keep_outside hv₁.ws kx (by simpa using hx) (by simp))
  have st₈ : slot w₈.mem B oSteps = Sc - i := by
    rw [kx.slot (e := oSteps) (by decide) (by simp)]; exact st
  -- The count down.
  refine wp_movS (readSrc_sc hw₈.ws.workspace (d := oSteps) (by rw [oSteps_val']; omega)) fun v₂ V₂ _ =>
    wp_subZ rfl fun v₃ V₃ z₃ => ?_
  have K₁₃ : Keeps [.eax] w₈ v₃ := (V₂.keeps.mono (by decide)).trans (V₃.keeps.mono (by decide))
  have hv₃ := hw₈.keep K₁₃ (by decide) (by decide) (by rw [V₃.mem, V₂.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeSlotZ_ok hv₃ (d := oSteps) (by decide) .eax) fun v ⟨hv, kv, ev, Kv, zv⟩ => ?_
  have e₂' : (v₂.gpr .eax).toNat = Sc - i := by rw [V₂.gpr]; exact st₈
  have e₃' : (v₃.gpr .eax).toNat = Sc - i - 1 := by
    rw [V₃.gpr, BitVec.toNat_sub, e₂', show (1 : BitVec 32).toNat = 1 from rfl]; omega
  have Kuv : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] u v :=
    (K₀₈.mono (by decide)).trans (Kv₁.trans ((KW₈.mono (by decide)).trans ((K₁₃.mono (by decide)).trans
      (Kv.mono (by simp)))))
  have kv' : Keep B (kw len) [] [oSteps] w₈.mem v.mem := by rw [V₃.mem, V₂.mem] at kv; exact kv
  have kuv : Keep B (kw len) [r, t, x] [oMask, oSteps, oQ, oU0, oU2, oDig, sQd] u.mem v.mem :=
    (((k₀₈.mono (by simp) (by simp)).trans (kv₁.mono (by simp) (by simp))).trans (kx.mono (by simp) (by simp))).trans
      (kv'.mono (by simp) (by simp))
  have Zuv := VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws kuv (by simp; omega) (by decide)
  -- The dividend's words through the step.
  have xw : ∀ j, j < kw len + 2 → j ≠ Sc - i - 1 →
      w32 v.mem B (arr (kw len) x + 4 * j) = w32 u.mem B (arr (kw len) x + 4 * j) := fun j hj hne => by
    rw [kv'.word (j := x) (i := j) (by simp only [S]; omega) (by simp) (by decide) (h.ws.fit64 hx),
      Ox.w32 (by omega) (by omega),
      kv₁.word (j := x) (i := j) (by simp only [S]; omega) (by simp; omega) (by decide) (h.ws.fit64 hx),
      k₀₈.word (j := x) (i := j) (by simp only [S]; omega) (by simp) (by decide) (h.ws.fit64 hx)]
  have xd : w32 v.mem B (arr (kw len) x + 4 * (Sc - i - 1)) = D := by
    rw [kv'.word (j := x) (i := Sc - i - 1) (by simp only [S]; omega) (by simp) (by decide) (h.ws.fit64 hx), m₈,
      w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hDlt]
  refine ⟨⟨hv, I.ml.keep Kuv (by decide) Zuv, I.keep.trans kuv, I.rest.trans Kuv, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have ev : val32 v.mem B (arr (kw len) r) (wq a) = val32 v₁.mem B (arr (kw len) r) (wq a) := by
      refine val32_congr fun j hj => ?_
      rw [kv'.word (j := r) (i := j) (by simp only [S]; omega) (by simp) (by decide) (h.ws.fit64 hr)]
      exact kx.word (j := r) (i := j) (by simp only [S]; omega) (by simpa using hxr.symm) (by simp) (h.ws.fit64 hr)
    rw [ev, ev₁, show Sc - (i + 1) = Sc - i - 1 by omega]
    have e : X₀ / 2 ^ (32 * (Sc - i)) = X₀ / 2 ^ (32 * (Sc - i - 1)) / 2 ^ 32 := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show 32 * (Sc - i - 1) + 32 = 32 * (Sc - i) by omega]
    rw [e]; exact step_mod
  · intro j hj1 hj2
    rw [mw, kv'.word (j := r) (i := j) (by simp only [S]; omega) (by simp) (by decide) (h.ws.fit64 hr),
      kx.word (j := r) (i := j) (by simp only [S]; omega) (by simpa using hxr.symm) (by simp) (h.ws.fit64 hr)]
    rw [← mw, hiv₁ j hj1 (by omega), mw, k₀₈.word (j := r) (i := j) (by simp only [S]; omega) (by simp)
      (by decide) (h.ws.fit64 hr)]
    exact I.high j hj1 hj2
  · rw [ev, e₃']; omega
  · intro j hj
    rw [xw j (by omega) (by omega)]; exact I.xlo j (by omega)
  · rw [show Sc - (i + 1) = Sc - i - 1 by omega, show i + 1 = 1 + i by omega, val32_append,
      show arr (kw len) x + 4 * (Sc - i - 1) + 4 * 1 = arr (kw len) x + 4 * (Sc - i) by omega]
    have hi' : val32 v.mem B (arr (kw len) x + 4 * (Sc - i)) i = val32 u.mem B (arr (kw len) x + 4 * (Sc - i)) i := by
      refine val32_congr fun j hj => ?_
      rw [show arr (kw len) x + 4 * (Sc - i) + 4 * j = arr (kw len) x + 4 * (Sc - i + j) by omega]
      exact xw _ (by omega) (by omega)
    rw [hi', I.xq]
    simp only [val32, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
    rw [xd, hD, quo_step X₀ M (Sc - i - 1) hM0, show Sc - i - 1 + 1 = Sc - i by omega]
    omega
  · intro j hj1 hj2
    rw [xw j hj2 (by omega)]; exact I.xhi j hj1 hj2
  · rw [zv, z₃]
    congr 1
    have hSb : Sc - i < 2 ^ 32 := by omega
    have hv2 : v₂.gpr .eax = BitVec.ofNat 32 (Sc - i) :=
      BitVec.eq_of_toNat_eq (by rw [e₂', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hSb])
    rw [hv2]
    by_cases e : i + 1 = Sc
    · rw [decide_eq_true e, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hSb]; simp; omega
    · rw [decide_eq_false e, beq_eq_false_iff_ne]
      intro hc
      have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hSb] at this; simp at this; omega

/-- `wordDivQ ml x r m t extra`: `[r] = X mod M'` and the dividend's low `Sc = X' - W' + 1` words
`⌊X / M'⌋`, its words from `Sc` on kept, for the dividend `X` (`X'` words: `W`, or `W + 1` where
`extra`) and `M'` the divisor's `W'` words with the top bit of its word `W' - 1` set, written back
to `m`. -/
theorem wordDivQ_ok {s : State} (h : RtWs VG.Impl.Rsa.X86.RecoverRt.wid s B Z len N) {ml a x r m t : Nat}
    {extra : Bool} (hm : MLen s B Z ml a) (hx : x < N) (hr : r < N) (hmN : m < N) (ht : t < N)
    (hrt : r ≠ t) (hmt : m ≠ t) (hrm : r ≠ m) (hxr : r ≠ x) (hxt : t ≠ x) (hxm : m ≠ x)
    (h4 : 4 ≤ wq a) (hw : wq a ≤ kw len) :
    WP isa (VG.Impl.Rsa.X86.RecoverDetRt.wordDivQ ml x r m t extra) s fun v =>
      RtWs VG.Impl.Rsa.X86.RecoverRt.wid v B Z len N ∧
      Keep B (kw len) [m, r, t, x] [oD, oD1, oV, oMask, oSteps, oQ, oU0, oU2, oDig, sQd] s.mem v.mem ∧
      (∀ i, i < kw len + 2 → i ≠ wq a - 1 → mw v.mem B (kw len) m i = mw s.mem B (kw len) m i) ∧
      mw v.mem B (kw len) m (wq a - 1) = mw s.mem B (kw len) m (wq a - 1) % 2 ^ 31 + 2 ^ 31 ∧
      num v.mem B (kw len) r =
        val32 s.mem B (arr (kw len) x) (xn len extra) % val32 v.mem B (arr (kw len) m) (wq a) ∧
      val32 v.mem B (arr (kw len) x) (xn len extra - wq a + 1) =
        val32 s.mem B (arr (kw len) x) (xn len extra) / val32 v.mem B (arr (kw len) m) (wq a) ∧
      (∀ j, xn len extra - wq a + 1 ≤ j → j < kw len + 2 →
        w32 v.mem B (arr (kw len) x + 4 * j) = w32 s.mem B (arr (kw len) x + 4 * j)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := by
  have nw := h.ws.workspace.nowrap
  have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  have xnb : kw len ≤ xn len extra ∧ xn len extra ≤ kw len + 1 := by cases extra <;> simp [xn]
  have fx := h.ws.arr_fit hx
  simp only [S] at fx
  unfold VG.Impl.Rsa.X86.RecoverDetRt.wordDivQ
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  -- The divisor's top bit, `d`, `d₁` and `v`.
  refine WP.seq (WP.mono (orTop_ok h hm hmN (by omega) hw) fun u₁ ⟨h₁, k₁, w₁, t₁, d₁, d1₁, K₁⟩ => ?_)
  obtain ⟨Mn, hMn⟩ : ∃ Mn, Mn = val32 u₁.mem B (arr (kw len) m) (wq a) := ⟨_, rfl⟩
  have hMsplit : Mn = val32 u₁.mem B (arr (kw len) m) (wq a - 1) +
      2 ^ (32 * (wq a - 1)) * mw u₁.mem B (kw len) m (wq a - 1) := by
    rw [hMn, show wq a = wq a - 1 + 1 by omega, val32_succ, Nat.add_sub_cancel]
  have htop : mw u₁.mem B (kw len) m (wq a - 1) < 2 ^ 32 := (u₁.mem.readW _ 32).isLt
  have hdiv : Mn / 2 ^ (32 * (wq a - 1)) = mw u₁.mem B (kw len) m (wq a - 1) := by
    rw [hMsplit, Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (val32_lt _ _ _ _),
      Nat.add_zero]
  have hdn : 2 ^ 31 ≤ Mn / 2 ^ (32 * (wq a - 1)) := by rw [hdiv, t₁]; omega
  refine WP.seq (WP.mono (recip_ok h₁ (d := Mn / 2 ^ (32 * (wq a - 1))) (by rw [hdiv]; exact d₁) hdn
    (by rw [hdiv]; exact htop)) fun u₂ ⟨h₂, k₂, v₂, K₂⟩ => ?_)
  have Hd : StepHdr u₂.mem B Mn (wq a) := by
    refine ⟨?_, hdn, ?_, v₂, by rw [hMn]; exact val32_lt _ _ _ _⟩
    · rw [k₂.slot (by decide) (by decide), d₁, hdiv]
    · rw [k₂.slot (by decide) (by decide), d1₁, ← w₁ (wq a - 2) (by omega) (by omega), hMn]
      exact w32_of_val32 u₁.mem B (by omega)
  have K₀₂ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₂ := (K₁.mono (by decide)).trans K₂
  have k₀₂ : Keep B (kw len) [m] [oD, oD1, oV] s.mem u₂.mem :=
    (k₁.mono (by simp) (by simp)).trans (k₂.mono (by simp) (by simp))
  have Z₀₂ := VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws k₀₂ (by simpa using hmN) (by decide)
  have hm₂ : MLen u₂ B Z ml a := hm.keep K₀₂ (by decide) Z₀₂
  -- `r` seeded with the dividend's top words.
  refine WP.seq (WP.mono (seedX_ok h₂ hm₂ hx hr hxr (extra := extra) (by omega) hw) fun u₃ ⟨h₃, k₃, v₃, st₃, K₃⟩ => ?_)
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, X₀ = val32 s.mem B (arr (kw len) x) (xn len extra) := ⟨_, rfl⟩
  have xs₂ : ∀ j, j < kw len + 2 → w32 u₂.mem B (arr (kw len) x + 4 * j) = w32 s.mem B (arr (kw len) x + 4 * j) :=
    fun j hj => k₀₂.word (j := x) (i := j) (by simp only [S]; omega) (by simpa using hxm) (by decide)
      (h.ws.fit64 hx)
  have xs₃ : ∀ j, j < kw len + 2 → w32 u₃.mem B (arr (kw len) x + 4 * j) = w32 s.mem B (arr (kw len) x + 4 * j) :=
    fun j hj => by
      rw [k₃.word (j := x) (i := j) (by simp only [S]; omega) (by simpa using hxr) (by decide)
        (h.ws.fit64 hx)]
      exact xs₂ j hj
  have X₂ : val32 u₂.mem B (arr (kw len) x) (xn len extra) = X₀ := by
    rw [hX₀]; exact val32_congr fun j hj => xs₂ j (by omega)
  have X₃ : val32 u₃.mem B (arr (kw len) x) (xn len extra) = X₀ := by
    rw [hX₀]; exact val32_congr fun j hj => xs₃ j (by omega)
  have M₃ : val32 u₃.mem B (arr (kw len) m) (wq a) = Mn := by
    rw [hMn]
    exact val32_congr fun j hj => ((k₂.mono (js' := [r]) (ds' := [oV, oSteps]) (by simp) (by simp)).trans
      (k₃.mono (by simp) (by simp))).word (j := m) (i := j) (by simp only [S]; omega) (by simpa using hrm)
      (by decide) (h.ws.fit64 hmN)
  have H₃ : StepHdr u₃.mem B Mn (wq a) := Hd.keep (k₃.slot (by decide) (by decide))
    (k₃.slot (by decide) (by decide)) (k₃.slot (by decide) (by decide))
  have hXlt : X₀ < 2 ^ (32 * xn len extra) := by rw [hX₀]; exact val32_lt _ _ _ _
  have hseed : val32 u₃.mem B (arr (kw len) r) (kw len + 1) < 2 ^ (32 * (wq a - 1)) := by
    rw [v₃, X₂, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
      show 32 * (wq a - 1) + 32 * (xn len extra - (wq a - 1)) = 32 * xn len extra by omega]
    exact hXlt
  have hMlow : 2 ^ (32 * (wq a - 1)) ≤ Mn := by
    rw [hMsplit, t₁]
    have := Nat.mul_le_mul_left (2 ^ (32 * (wq a - 1))) (show 1 ≤ mw s.mem B (kw len) m (wq a - 1) % 2 ^ 31 + 2 ^ 31 by omega)
    omega
  have hz : ∀ j, wq a - 1 ≤ j → j < kw len + 1 → w32 u₃.mem B (arr (kw len) r + 4 * j) = 0 :=
    fun j h1 h2 => val32_word_zero (n := kw len + 1) h2 h1 hseed
  have hr0 : val32 u₃.mem B (arr (kw len) r) (wq a) = val32 u₃.mem B (arr (kw len) r) (kw len + 1) := by
    rw [show kw len + 1 = wq a + (kw len + 1 - wq a) by omega, val32_append,
      val32_zero_of (n := kw len + 1 - wq a) fun j hj => by
        rw [show arr (kw len) r + 4 * wq a + 4 * j = arr (kw len) r + 4 * (wq a + j) by omega]
        exact hz _ (by omega) (by omega),
      Nat.mul_zero, Nat.add_zero]
  obtain ⟨Sc, hSc⟩ : ∃ Sc, Sc = xn len extra - wq a + 1 := ⟨_, rfl⟩
  have topq : X₀ / 2 ^ (32 * Sc) < Mn := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    refine Nat.lt_of_lt_of_le hXlt ?_
    have := Nat.mul_le_mul_right (2 ^ (32 * Sc)) hMlow
    rw [← Nat.pow_add, show 32 * (wq a - 1) + 32 * Sc = 32 * xn len extra by omega] at this
    exact this
  have I₀ : LoopQ u₃ B Z len N ml a x r t Mn X₀ Sc 0 u₃ := by
    refine ⟨h₃, hm₂.keep K₃ (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside h₂.ws k₃ (by simpa using hr)
      (by decide)), Keep.refl _ _ _ _ _, Keeps.refl _ _, ?_, ?_, ?_, fun _ _ => rfl, ?_, fun _ _ _ => rfl⟩
    · rw [hr0, Nat.sub_zero, show Sc = xn len extra - (wq a - 1) by omega, ← X₂, ← v₃,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hseed hMlow)]
    · intro j hj1 hj2; exact hz j (by omega) hj2
    · rw [st₃, hSc, Nat.sub_zero]
    · rw [Nat.sub_zero, Nat.div_eq_of_lt topq]; rfl
  -- The steps.
  have fitm := h.ws.fit64 hmN
  refine WP.loop (M := isa) (fun n u => ∃ i, n = Sc - i ∧ i < Sc ∧ LoopQ u₃ B Z len N ml a x r t Mn X₀ Sc i u)
    ?_ Sc u₃ ⟨0, by omega, by omega, I₀⟩
  rintro n u ⟨i, rfl, hi, I⟩
  refine WP.mono (digitStepQ_ok hx hr hmN ht hrt hmt hrm hxr hxt hxm h4 hw X₃ M₃ H₃ hSc hi I)
    fun v ⟨I', z⟩ => ?_
  have km : ∀ j, j < kw len + 2 → mw v.mem B (kw len) m j = mw u₃.mem B (kw len) m j := fun j hj =>
    I'.keep.word (j := m) (i := j) (by simp only [S]; omega) (by simp; omega) (by decide) fitm
  have km₃ : ∀ j, j < kw len + 2 → mw u₃.mem B (kw len) m j = mw u₁.mem B (kw len) m j := fun j hj =>
    ((k₂.mono (js' := [r]) (ds' := [oV, oSteps]) (by simp) (by simp)).trans
      (k₃.mono (by simp) (by simp))).word (j := m) (i := j) (by simp only [S]; omega) (by simpa using hrm)
      (by decide) fitm
  by_cases e : i + 1 = Sc
  · have Mv : val32 v.mem B (arr (kw len) m) (wq a) = Mn := by
      rw [← M₃]
      exact val32_congr fun j hj => km j (by omega)
    refine .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], I'.ws, ?_, ?_, ?_, ?_, ?_,
      ?_, (K₀₂.mono (by decide)).trans ((K₃.mono (by decide)).trans I'.rest)⟩
    · exact ((k₀₂.mono (by simp) (by simp)).trans (k₃.mono (by simp) (by simp))).trans
        (I'.keep.mono (by simp) (by simp))
    · intro j hj hne
      rw [km j hj, km₃ j hj]; exact w₁ j hj hne
    · rw [km _ (by omega), km₃ _ (by omega)]; exact t₁
    · rw [Mv, VG.Proof.Rsa.X86.Keys.num, show kw len = wq a + (kw len - wq a) by omega, val32_append,
        val32_zero_of (n := kw len - wq a) fun j hj => by
          rw [show arr (wq a + (kw len - wq a)) r + 4 * wq a + 4 * j = arr (wq a + (kw len - wq a)) r + 4 * (wq a + j)
            by omega]
          have := I'.high (wq a + j) (by omega) (by omega)
          rw [mw, show wq a + (kw len - wq a) = kw len by omega] at *
          exact this,
        Nat.mul_zero, Nat.add_zero, show wq a + (kw len - wq a) = kw len by omega, I'.val, e, Nat.sub_self,
        Nat.mul_zero, Nat.pow_zero, Nat.div_one, hX₀]
    · have := I'.xq
      rw [e, Nat.sub_self, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one] at this
      rw [Mv, ← hSc, this, hX₀]
    · intro j hj1 hj2
      rw [I'.xhi j (by omega) hj2]; exact xs₃ j hj2
  · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], Sc - (i + 1), by omega,
      i + 1, rfl, by omega, I'⟩

end VG.Proof.Rsa.X86.Recover
