module

public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Add
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Step
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Quot
import VerifiedGarbage.Proof.Bignum.WordStepNorm32
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the word steps' proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # `WordModRt` on i686: a step `r := (r 2^32 + u) mod m`

From `d`, `d₁` (`m`'s top two words, `d ≥ 2^31`) and `v` in the header, the
digit `u` at `oDig` and `r < m`, `step` leaves `(r 2^32 + u) mod m` in `r`
(`step_ok`): the 3-by-2 estimate from the top three words of `r 2^32 + u`,
which are `r`'s (`WordStep32.qhat3_div`), `mulSub`, one add-back and the copy
back (`WordStep32.wordStepQ1_div`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.WordRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc)
open VG.Impl.Rsa.X86.WordModRt (oD oV oD1 oQ oU0 oU2 oSteps oDig h0)

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem oU0_val : oU0 = 80 := rfl
theorem oU2_val : oU2 = 84 := rfl
theorem oSteps_val : oSteps = 72 := rfl

/-- `topWords`, from `ebx` at word `W' - 3` of `r`: `u₀` (word `W' - 3`) and `u₂` (word `W' - 1`)
into the header, `u₁` (word `W' - 2`) into `ebp` and `u₂` into `eax`. -/
theorem topWords_ok {s : State} {is : List Instr} {Q : State → Prop} (ws : Ws s B Z) (di : PtrAt s B .edi 0)
    {x : Nat} (pb : PtrAt s B .ebx x) (hx : x + 12 ≤ Z) (hh : oU2 + 4 ≤ x)
    (kk : ∀ t, t.mem = (s.mem.writeW (off B oU0) (BitVec.ofNat 32 (w32 s.mem B x))).writeW (off B oU2)
        (BitVec.ofNat 32 (w32 s.mem B (x + 8))) →
      t.gpr .ebp = BitVec.ofNat 32 (w32 s.mem B (x + 4)) → t.gpr .eax = BitVec.ofNat 32 (w32 s.mem B (x + 8)) →
      Keeps [.eax, .ebp] s t → WP isa (.block is) t Q) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.topWords ++ is)) s Q := by
  have nw := ws.nowrap
  rw [oU2_val] at hh
  simp only [VG.Impl.Rsa.X86.WordModRt.topWords, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_ptr ws pb (d := 0) (by omega)) fun t₁ U₁ _ => ?_
  have di₁ : PtrAt t₁ B .edi 0 := by rw [PtrAt, U₁.other _ (by decide)]; exact di
  have ws₁ := ws.of_wr U₁.wr
  refine wp_storeS (ea_ptr ws₁ di₁ (d := oU0) (by rw [oU0_val]; omega)) (ws_write ws₁ (by rw [oU0_val]; omega))
    fun t₂ M₂ => ?_
  have ws₂ := ws₁.of_wr M₂.wr
  have pb₂ : PtrAt t₂ B .ebx x := by rw [PtrAt, M₂.gpr, U₁.other _ (by decide)]; exact pb
  have di₂ : PtrAt t₂ B .edi 0 := by rw [PtrAt, M₂.gpr]; exact di₁
  refine wp_movS (readSrc_ptr ws₂ pb₂ (d := 4) (by omega)) fun t₃ U₃ _ => ?_
  have ws₃ := ws₂.of_wr U₃.wr
  have pb₃ : PtrAt t₃ B .ebx x := by rw [PtrAt, U₃.other _ (by decide)]; exact pb₂
  refine wp_movS (readSrc_ptr ws₃ pb₃ (d := 8) (by omega)) fun t₄ U₄ _ => ?_
  have ws₄ := ws₃.of_wr U₄.wr
  have di₄ : PtrAt t₄ B .edi 0 := by rw [PtrAt, U₄.other _ (by decide), U₃.other _ (by decide)]; exact di₂
  refine wp_storeS (ea_ptr ws₄ di₄ (d := oU2) (by rw [oU2_val]; omega)) (ws_write ws₄ (by rw [oU2_val]; omega))
    fun t₅ M₅ => ?_
  have m₂ : t₂.mem = s.mem.writeW (off B oU0) (BitVec.ofNat 32 (w32 s.mem B x)) := by
    rw [M₂.mem, U₁.mem, U₁.gpr, Nat.zero_add, Nat.add_zero]; simp [w32]
  have r₄ : ∀ d, d + 4 ≤ x + 12 → x ≤ d → w32 t₂.mem B d = w32 s.mem B d := fun d h1 h2 => by
    rw [m₂, w32_write_ne (size := Z) nw (by rw [oU0_val]; omega) (by omega) (by rw [oU0_val]; omega)]
  have eax₄ : t₄.gpr .eax = BitVec.ofNat 32 (w32 s.mem B (x + 8)) := by
    rw [U₄.gpr, U₃.mem]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← r₄ (x + 8) (by omega) (by omega)]; simp only [w32]
    exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
  refine kk t₅ ?_ ?_ ?_ ?_
  · rw [M₅.mem, U₄.mem, U₃.mem, m₂, Nat.zero_add, eax₄]
  · rw [M₅.gpr, U₄.other _ (by decide), U₃.gpr]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← r₄ (x + 4) (by omega) (by omega)]; simp only [w32]
    exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
  · rw [M₅.gpr, eax₄]
  · exact ((U₁.keeps.mono (by decide)).trans (M₂.keeps _)).trans
      (((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide))).trans (M₅.keeps _))

/-- The mask word `R2Words`' `quot` writes, at base `h0`. -/
abbrev oMask : Nat := VG.Impl.Bignum.X86.R2Words.oMask h0

theorem oMask_val : oMask = 68 := rfl

/-- What `step` needs in the header: `m`'s top two words, `d ≥ 2^31` and `d₁`, and the reciprocal. -/
structure StepHdr (mem : Mem) (B : Addr) (M W : Nat) : Prop where
  d : slot mem B oD = M / 2 ^ (32 * (W - 1))
  dn : 2 ^ 31 ≤ M / 2 ^ (32 * (W - 1))
  d1 : slot mem B oD1 = M / 2 ^ (32 * (W - 2)) % 2 ^ 32
  v : slot mem B oV = (2 ^ 64 - 1) / (M / 2 ^ (32 * (W - 1))) - 2 ^ 32
  lt : M < 2 ^ (32 * W)

theorem StepHdr.keep {m m' : Mem} {M W : Nat} (h : StepHdr m B M W)
    (hd : slot m' B oD = slot m B oD) (hd1 : slot m' B oD1 = slot m B oD1) (hv : slot m' B oV = slot m B oV) :
    StepHdr m' B M W := ⟨hd.trans h.d, h.dn, hd1.trans h.d1, hv.trans h.v, h.lt⟩

theorem div_low {R u K : Nat} (hu : u < 2 ^ 32) : (R * 2 ^ 32 + u) / 2 ^ (K + 32) = R / 2 ^ K := by
  rw [Nat.pow_add, Nat.mul_comm (2 ^ K), ← Nat.div_div_eq_div_mul,
    show (R * 2 ^ 32 + u) / 2 ^ 32 = R by rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide),
      Nat.div_eq_of_lt hu, Nat.zero_add]]

/-- Five header words changed: `Keep` of them. -/
theorem keep_of_five {w : Nat} {js ds : List Nat} {m m' : Mem} {e : Nat} (h : Outside B e 20 m m')
    (h0 : e ∈ ds) (h1 : e + 4 ∈ ds) (h2 : e + 8 ∈ ds) (h3 : e + 12 ∈ ds) (h4 : e + 16 ∈ ds) :
    Keep B w js ds m m' := by
  intro x hx
  have mem : ∀ d ∈ ds, (d, 4) ∈ VG.Proof.Rsa.X86.Keys.ranges w js ds := fun d hd => by
    simp only [VG.Proof.Rsa.X86.Keys.ranges, List.mem_append, List.mem_map]; exact .inr ⟨d, hd, rfl⟩
  have a0 := hx _ (mem _ h0); have a1 := hx _ (mem _ h1); have a2 := hx _ (mem _ h2)
  have a3 := hx _ (mem _ h3); have a4 := hx _ (mem _ h4)
  exact h x (by simp only at a0 a1 a2 a3 a4; omega)

/-- A step: `r := (r 2^32 + u) mod m`, over `W' ≥ 4` words, for the digit `u` at `oDig`, `r < m`,
and `StepHdr`. -/
theorem step_ok {s : State} (h : RtWs L s B Z len N) {ml a r m t : Nat} (hm : MLen s B Z ml a)
    (hr : r < N) (hmN : m < N) (ht : t < N) (hrt : r ≠ t) (hmt : m ≠ t)
    (h4 : 4 ≤ wq a) (hw : wq a ≤ kw len) {M R : Nat}
    (hM : val32 s.mem B (arr (kw len) m) (wq a) = M) (hR : val32 s.mem B (arr (kw len) r) (wq a) = R)
    (hRM : R < M) (H : StepHdr s.mem B M (wq a)) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.step L ml r m t) s fun v => RtWs L v B Z len N ∧
      Keep B (kw len) [r, t] [oMask, oSteps, oQ, oU0, oU2] s.mem v.mem ∧
      val32 v.mem B (arr (kw len) r) (wq a) = (R * 2 ^ 32 + slot s.mem B oDig) % M ∧
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
  have hx3 := VG.Proof.Bignum.X86.R2Words.val32_top3 s.mem B (arr (kw len) r) k
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
  unfold VG.Impl.Rsa.X86.WordModRt.step
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs, List.append_assoc]
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
  rw [VG.Proof.Bignum.X86.R2Words.qhat_min hud hu1' (by omega)] at hq₁
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
  have h₂ : RtWs L s₂ B Z len N := h.keep K₀₂ (by decide) (by decide) Z₂
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
  -- `t := t + m` if negative.
  refine WP.seq (WP.mono (addBack_ok h₃ hm₃ hmN ht hmt (by omega) hw) fun s₄ ⟨h₄, k₄, ⟨c, hc, hv₄⟩, K₄⟩ => ?_)
  rw [M₃] at hv₄
  have Z₄ := VG.Proof.Rsa.X86.KeyRt.keep_outside h₃.ws k₄ (by simpa using ht) (by simp)
  have hm₄ : MLen s₄ B Z ml a := hm₃.keep K₄ (by decide) Z₄
  have tb : ∀ mm : Mem, (2 ^ 31 ≤ w32 mm B (arr (kw len) t + 4 * wq a)) ↔
      2 ^ (32 * (wq a + 1)) / 2 ≤ val32 mm B (arr (kw len) t) (wq a + 1) := fun mm => by
    rw [val32_succ]
    exact (VG.Proof.Bignum.X86.R2Words.topBit_iff (val32_lt _ _ _ _) (mm.readW _ 32).isLt).symm
  have hv₄' : val32 s₄.mem B (arr (kw len) t) (wq a + 1) + 2 ^ (32 * (wq a + 1)) * c =
      val32 s₃.mem B (arr (kw len) t) (wq a + 1) +
        if 2 ^ (32 * (wq a + 1)) / 2 ≤ val32 s₃.mem B (arr (kw len) t) (wq a + 1) then M else 0 := by
    simp only [tb] at hv₄; exact hv₄
  have hMW : 2 * M < 2 ^ (32 * (wq a + 1)) / 2 := by
    have := H.lt
    rw [show 32 * (wq a + 1) = 32 * wq a + 32 by omega, Nat.pow_add]; omega
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
  have Ksv : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := K₀₂.trans (K₃.trans (K₄.trans Kv))
  refine ⟨hv, ?_, ?_, ?_, ?_, Ksv⟩
  · exact (keep_of_five (js := [r, t]) (ds := [oMask, oSteps, oQ, oU0, oU2]) Ohdr (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans ((k₃.mono (by simp) (by simp)).trans
        ((k₄.mono (by simp) (by simp)).trans (kv.mono (by simp) (by simp))))
  · rw [ev, ← hT, val32_succ, top0, Nat.mul_zero, Nat.add_zero]
  · have k34 := k₃.trans k₄
    rw [kv.slot (e := oSteps) (by decide) (by simp), k34.slot (e := oSteps) (by decide) (by simp)]
    show w32 s₂.mem B oSteps = w32 s.mem B oSteps
    have e1 : w32 s₂.mem B oSteps = w32 s₁.mem B oSteps := O₂.w32 (.inl (by decide)) (by decide)
    have e2 : w32 s₁.mem B oSteps = w32 t₁.mem B oSteps := C₁
    rw [e1, e2, O₁.w32 (.inl (by decide)) (by decide)]
  · intro i hi1 hi2
    rw [mw, Ov.w32 (.inr (by omega)) (by omega)]
    rw [k₄.word (i := i) (by simp only [S]; omega) (by simpa using hrt.symm) (by simp) (h₃.ws.fit64 hr),
      k₃.word (i := i) (by simp only [S]; omega) (by simpa using hrt.symm) (by simp) (h₂.ws.fit64 hr),
      Ohdr.w32 (.inr (by rw [oMask_val]; omega)) (by omega)]

end VG.Proof.Rsa.X86.WordRt
