module

public import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks

/-!
# `vg_rsa_crt_values` on x86-64: the loads and the check of `p q = n`

The loads of `n`, `p`, `q` and `d` (`cvLoads_ok`), and the mask of
`p q = n` (`cvCheck_ok`), comparing the full product including its high words.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-- `p q = n` for an odd `n`, as `pqCheck` checks it. -/
theorem pq_iff {N P Q : Nat} (hN : N % 2 = 1) :
    (P % 2 = 1 ∧ N / P = Q ∧ N % P = 0) ↔ P * Q = N := by
  constructor
  · rintro ⟨hp, hq, hr⟩
    have := Nat.div_add_mod N P
    rw [hq, hr, Nat.add_zero] at this
    exact this
  · intro h
    have hp : P % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one P with hP | hP
      · rw [← h, Nat.mul_mod, hP, Nat.zero_mul] at hN; exact absurd hN (by decide)
      · exact hP
    have hP0 : 0 < P := by omega_arith
    refine ⟨hp, ?_, ?_⟩
    · rw [← h, Nat.mul_div_cancel_left _ hP0]
    · rw [← h, Nat.mul_mod_right]

/-- The memory word of the mask. -/
abbrev mword (m : Mem) (B : Addr) : BitVec 64 := word m B (8 * Impl.Bignum.X86_64.Public.sMask)

/-- `CvS` and the mask, after a store to the mask's slot. -/
theorem CvS.mask {I : CvIn} {m₀ : Mem} {s t : State} (h : CvS I m₀ s) {v : BitVec 64}
    (hm : t.mem = s.mem.writeW (off I.B (8 * Impl.Bignum.X86_64.Public.sMask)) v) {regs : List Reg}
    (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : CvS I m₀ t ∧ mword t.mem I.B = v ∧
      ∀ j < 16, wv t.mem I.B (slot (wk I.k) j) (wk I.k + 2) = wv s.mem I.B (slot (wk I.k) j) (wk I.k + 2) := by
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have ho := writeW_outside s.mem I.B v (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by omega_arith)
  rw [← hm] at ho
  refine ⟨h.step (Frm.of_outside ho (List.mem_singleton_self _)) (fun r hr => ?_) (fun r hr => ?_) k hr,
    by rw [hm]; exact word_writeW_self _ _ _ _, fun j hj => ho.wv (Or.inr ?_) (by have := h.ws.sl hj; omega_arith)⟩
  · rw [List.mem_singleton.mp hr]; exact Or.inr (Or.inl rfl)
  · rw [List.mem_singleton.mp hr]; simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith
  · have := hdr_lt_slot (wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith

/-- The bounds on the lengths. -/
structure CvLens (I : CvIn) : Prop where
  k1 : 64 ≤ I.k
  k2 : I.k ≤ 1024
  pl1 : 1 ≤ I.pl
  pl2 : I.pl < I.k
  ql1 : 1 ≤ I.ql
  ql2 : I.ql < I.k
  dl1 : 1 ≤ I.dl
  dl2 : I.dl ≤ I.k
  nl : I.nb.length = I.k
  pbl : I.pb.length = I.pl
  qbl : I.qb.length = I.ql
  dbl : I.db.length = I.dl
  z : 128 * I.k ≤ I.Z

/-- An array other than the one that changed. -/
theorem outside_arr {m m' : Mem} {B : Addr} {Z w j i n L : Nat} (ho : Outside B (slot w j) L m m')
    (hL : L ≤ 8 * (w + 2)) (hij : i ≠ j) (hn : n ≤ w + 2) (hi : i < 16) (hZ : slot w 16 ≤ Z)
    (hB : B.toNat + Z ≤ 2 ^ 64) : wv m' B (slot w i) n = wv m B (slot w i) n :=
  ho.wv (by have := slot_far (w := w) hij; omega_arith) (by have := Nat.le_trans (slot_lt (w := w) hi) hZ; omega_arith)

/-- The loads of `n`, `p`, `q` and `d` into their arrays. -/
theorem cvLoads_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) :
    WP isa (seqs (loadA aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
      (loadA aP sP sPl ++ (loadA aQ sQ sQl ++ loadA aD sD sDl)))) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      wv t.mem I.B (slot (wk I.k) aN) (wk I.k) = Spec.Rsa.os2ip I.nb ∧
      wv t.mem I.B (slot (wk I.k) aP) (wk I.k) = Spec.Rsa.os2ip I.pb ∧
      wv t.mem I.B (slot (wk I.k) aQ) (wk I.k) = Spec.Rsa.os2ip I.qb ∧
      wv t.mem I.B (slot (wk I.k) aD) (wk I.k) = Spec.Rsa.os2ip I.db := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have k1 := L.k1
  have k2 := L.k2
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have hm : ∀ {m m' : Mem} {j : Nat}, Outside I.B (slot (wk I.k) j) (8 * (wk I.k + 2)) m m' →
      mword m' I.B = mword m I.B := fun {_ _ j} o =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith))
      (by have := hdr_lt_slot (wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h.ws (by decide) (by decide)
    (by decide) h.args.n h.args.k h.n L.nl (by omega_arith) (by unfold wk; omega_arith)) fun s₁ ⟨hv₁, o₁, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h₁.ws (by decide) (by decide)
    (by decide) h₁.args.p h₁.args.pl h₁.p L.pbl L.pl1 (by have := L.pl2; unfold wk; omega_arith)) fun s₂ ⟨hv₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.arr (by decide) (Nat.le_refl _) o₂ k₂ (by decide)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h₂.ws (by decide) (by decide)
    (by decide) h₂.args.q h₂.args.ql h₂.q L.qbl L.ql1 (by have := L.ql2; unfold wk; omega_arith)) fun s₃ ⟨hv₃, o₃, k₃⟩ => ?_)
  have h₃ := h₂.arr (by decide) (Nat.le_refl _) o₃ k₃ (by decide)
  refine WP.mono (loadA_ok h₃.ws (by decide) (by decide) (by decide) h₃.args.d h₃.args.dl h₃.d L.dbl L.dl1
    (by have := L.dl2; unfold wk; omega_arith)) fun t ⟨hv₄, o₄, k₄⟩ => ?_
  have h₄ := h₃.arr (by decide) (Nat.le_refl _) o₄ k₄ (by decide)
  refine ⟨h₄, ?_, ?_, ?_, ?_, hv₄⟩
  · rw [hm o₄, hm o₃, hm o₂, hm o₁]
  · rw [outside_arr o₄ (Nat.le_refl _) (by decide) (by omega_arith) (by decide) hZ hn,
      outside_arr o₃ (Nat.le_refl _) (by decide) (by omega_arith) (by decide) hZ hn,
      outside_arr o₂ (Nat.le_refl _) (by decide) (by omega_arith) (by decide) hZ hn]; exact hv₁
  · rw [outside_arr o₄ (Nat.le_refl _) (by decide) (by omega_arith) (by decide) hZ hn,
      outside_arr o₃ (Nat.le_refl _) (by decide) (by omega_arith) (by decide) hZ hn]; exact hv₂
  · rw [outside_arr o₄ (Nat.le_refl _) (by decide) (by omega_arith) (by decide) hZ hn]; exact hv₃

/-- The registers for the product; no operand value determines an address. -/
theorem productSetup_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block productSetup) s fun t =>
      t.gpr .r11 = off B (slot w aP) ∧ t.gpr .r9 = off B (slot w aQ) ∧
      t.gpr .r8 = off B (slot w aU) ∧ t.gpr .r10 = BitVec.ofNat 64 w ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.mem = s.mem ∧
      Keep [.r12, .r9, .r11, .rax, .r8, .r10] s t := by
  rw [show productSetup = ws ++ ((base aP .r11 ++ (base aQ .rax ++ base aU .r8)) ++
    ([.mov .r9 (.reg .rax), .mov .r10 (.reg .r12)] : List Instr)) by
      simp only [productSetup, List.append_assoc]]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base3_ok aP aQ aU (r₁ := .r11) (r₂ := .rax) (r₃ := .r8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide) (by decide)) fun t₂ ⟨h11, ha, h8, hm₂, k₂⟩ => ?_
  refine WP.mono (WP.keep [.r9, .r10] (Q := fun t => t.gpr .r9 = off B (slot w aQ) ∧
    t.gpr .r10 = BitVec.ofNat 64 w ∧ t.mem = t₂.mem) (by
    xrun [ha, (k₂.gpr (by decide) : t₂.gpr .r12 = _), h12]) rfl) fun t ⟨⟨h9', h10, hm₃⟩, k₃⟩ => ?_
  exact ⟨(k₃.gpr (by decide)).trans h11, h9', (k₃.gpr (by decide)).trans h8, h10,
    (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12), hm₃.trans (hm₂.trans hm₁),
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- The product computation at the modulus width, from a cleared accumulator. -/
theorem product_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    (hz : wv s.mem B (slot w aU) (2 * w + 2) = 0) :
    WP isa (.seq (.block productSetup) Impl.Rsa.X86_64.Crt.mulRows) s fun t =>
      wv t.mem B (slot w aU) (2 * w + 2) = wv s.mem B (slot w aP) w * wv s.mem B (slot w aQ) w ∧
      Outside B (slot w aU) (8 * (2 * w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw := h.w2
  have h1 := h.w1
  have hA : slot w aU + 8 * (2 * w + 2) ≤ Z := by
    have := h.sl (show 4 < 16 by decide)
    simp only [slot, aU] at *
    omega
  refine WP.seq (WP.mono (productSetup_ok h) fun s₁ ⟨h11, h9, h8, h10, h12, hm, k₁⟩ => ?_)
  refine WP.mono (mulRows_ok (h.scr.congr k₁.2.2) h11 h9 h10 h12 h8 (by omega) (by omega)
    (by omega) (by simpa only [Nat.two_mul] using hA)
    (by have := h.sl (show aP < 16 by decide); omega)
    (by have := h.sl (show aQ < 16 by decide); omega)
    (Or.inl (by simp [slot, aP, aU]; omega)) (Or.inr (by simp [slot, aQ, aU]; omega))
    (by rw [← Nat.two_mul, hm, hz]; exact Nat.two_pow_pos _)) fun t ⟨hv, ho, k₂⟩ => ?_
  simp only [← Nat.two_mul, hm, hz, Nat.zero_add] at hv ho
  exact ⟨hv, ho, (k₁.trans k₂).mono (by decide)⟩

/-- A product occupies the first `2 w + 2` words of arrays 2 and 3. -/
theorem CvS.product {I : CvIn} {m₀ : Mem} {s t : State} (h : CvS I m₀ s)
    (ho : Outside I.B (slot (wk I.k) aU) (8 * (2 * wk I.k + 2)) s.mem t.mem)
    {rs : List Reg} (hk : Keep rs s t) (hr : .rdi ∉ rs ∧ .rsp ∉ rs) : CvS I m₀ t :=
  h.step (Frm.of_outside ho (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := h.ws.sl (show 4 < 16 by decide)
    dsimp only
    simp only [slot, aU] at *
    omega) hk hr

/-- The mask of `p q = n` from the full product, including its high words. -/
theorem cvCheck_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (_L : CvLens I) {c : Bool}
    (hc : mword s.mem I.B = mask c) :
    WP isa (seqs pqCheck) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mask (c && decide (wv s.mem I.B (slot (wk I.k) aP) (wk I.k) *
        wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) = wv s.mem I.B (slot (wk I.k) aN) (wk I.k))) ∧
      ∀ j, j = aP ∨ j = aQ ∨ j = aD → wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) := by
  let w := wk I.k
  have hw := h.ws.w2
  have h1 := h.ws.w1
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have outside_keep : ∀ {m m' : Mem}, Outside I.B (slot w aU) (8 * (2 * w + 2)) m m' →
      ∀ j, j = aN ∨ j = aP ∨ j = aQ ∨ j = aD →
        wv m' I.B (slot w j) w = wv m I.B (slot w j) w := by
    intro m m' ho j hj
    apply ho.wv
    · rcases hj with rfl | rfl | rfl | rfl <;> simp [slot, aU, aN, aP, aQ, aD] <;> omega
    · have hj16 : j < 16 := by rcases hj with rfl | rfl | rfl | rfl <;> decide
      have hh := h.ws.sl hj16
      change slot w j + 8 * (w + 2) ≤ I.Z at hh
      omega
  have outside_mask : ∀ {m m' : Mem}, Outside I.B (slot w aU) (8 * (2 * w + 2)) m m' →
      mword m' I.B = mword m I.B := fun {_ _} ho =>
    ho.word (Or.inl (by simp [slot, hdrBytes, aU, Impl.Bignum.X86_64.Public.sMask, sFn]; omega))
      (by have := h.ws.h256; change 184 ≤ 2 ^ 64; decide)
  unfold pqCheck
  rw [List.append_assoc]
  refine wp_seqs_append (by simp [Impl.Rsa.X86_64.Crt.zeroAccs]) (by simp) (WP.mono
    (zeroAccs_ok h.ws.good.1 h.ws.good.2 (by omega)) fun s₁ ⟨hz₁, o₁, k₁⟩ => ?_)
  have h₁ := h.product o₁ k₁ (by decide)
  refine wp_seqs_append (by simp) (by simp [Impl.Rsa.X86_64.Crt.eqCheck])
    (WP.mono (product_ok h₁.ws (wv_zero hz₁)) fun s₃ ⟨hv₃, o₃, k₃⟩ => ?_)
  have h₃ := h₁.product o₃ k₃ (by decide)
  refine WP.mono (eqCheck_ok h₃.ws.good.1 h₃.ws.good.2 (by omega) (by omega)) fun t ⟨hm₄, o₄, k₄⟩ => ?_
  have h₄ := h₃.step (Frm.of_outside o₄ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inr (Or.inl rfl))
    (fun r hr => by rw [List.mem_singleton.mp hr]; have := h.ws.h256; change 184 ≤ I.Z; omega) k₄ (by decide)
  have hk₁ := outside_keep o₁
  have hk₃ := outside_keep o₃
  have product : wv s₃.mem I.B (slot w aU) (2 * w + 2) =
      wv s.mem I.B (slot w aP) w * wv s.mem I.B (slot w aQ) w := by
    rw [hv₃, hk₁ _ (Or.inr (Or.inl rfl)), hk₁ _ (Or.inr (Or.inr (Or.inl rfl)))]
  have hm₃ : mword s₃.mem I.B = mask c := by rw [outside_mask o₃, outside_mask o₁, hc]
  refine ⟨h₄, ?_, fun j hj => ?_⟩
  · change word t.mem I.B (8 * Impl.Bignum.X86_64.Public.sMask) = _
    rw [hm₄, show Impl.Bignum.X86_64.Public.aAcc = aU from rfl, ← show mword s₃.mem I.B = word s₃.mem I.B (8 * Impl.Bignum.X86_64.Public.sMask) from rfl,
      hm₃, product, hk₃ _ (Or.inl rfl), hk₁ _ (Or.inl rfl), mask_and']
  · have hj16 : j < 16 := by rcases hj with rfl | rfl | rfl <;> decide
    rw [o₄.wv (Or.inr (by have := hdr_lt_slot w j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega))
      (by have := h.ws.sl hj16; omega), hk₃ _ (Or.inr hj), hk₁ _ (Or.inr hj)]

/-- `decA j`: the low word of `[j]` minus one. -/
theorem decA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16) :
    WP isa (.block (decA j)) s fun t =>
      t.mem = s.mem.writeW (off B (slot w j)) (VG.Proof.Bignum.word s.mem B (slot w j) - 1) ∧
        Keep [.r12, .r9, .rbx, .rax] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  unfold decA
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨_, e9, n₁, j₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok j (r := .rbx) (by decide) ((j₁.gpr (by decide)).trans h.rdi) e9)
    fun t₂ ⟨hbx, n₂, j₂⟩ => ?_
  have hs₂ := h.scr.congr (j₁.trans j₂).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B (slot w j))
    (VG.Proof.Bignum.word s.mem B (slot w j) - 1)) (by
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.ld (d := slot w j) (by omega_arith), hs₂.st (d := slot w j) (by omega_arith), n₂, n₁]) rfl)
    fun t ⟨mt, j₃⟩ => ⟨mt, ((j₁.trans j₂).trans j₃).mono (by simp)⟩

/-- `divisor j ++ [divmod]`: `[aV] := d mod ([j] - 1)`, for an odd `[j]`. -/
theorem cvDivPart_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {j : Nat} (hj : j = aP ∨ j = aQ) :
    WP isa (seqs (divisor j ++ [divmod aU aV aC aT])) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (wv s.mem I.B (slot (wk I.k) j) (wk I.k) % 2 = 1 → 1 < wv s.mem I.B (slot (wk I.k) j) (wk I.k) →
        wv t.mem I.B (slot (wk I.k) aV) (wk I.k + 1) =
          wv s.mem I.B (slot (wk I.k) aD) (wk I.k) % (wv s.mem I.B (slot (wk I.k) j) (wk I.k) - 1)) ∧
      ∀ i, i = aP ∨ i = aQ ∨ i = aD ∨ i = aX₁ ∨ i = aX₂ →
        wv t.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have k1 := L.k1
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have hj16 : j < 16 := by rcases hj with rfl | rfl <;> decide
  have hjC : j ≠ aC := by rcases hj with rfl | rfl <;> decide
  have hjU : j ≠ aU := by rcases hj with rfl | rfl <;> decide
  have hmw : ∀ {m m' : Mem} {i L' : Nat}, Outside I.B (slot (wk I.k) i) L' m m' → L' ≤ 8 * (wk I.k + 2) →
      mword m' I.B = mword m I.B := fun {_ _ i _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) i (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith))
      (by omega_arith)
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, Outside I.B (slot (wk I.k) j) Ln m m' → Ln ≤ 8 * (wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (slot (wk I.k) i) (wk I.k) = wv m I.B (slot (wk I.k) i) (wk I.k) :=
    fun o hL hij hi => outside_arr o hL hij (by omega_arith) hi hZ hn
  simp only [divisor, List.cons_append, List.nil_append]
  -- `[c] := [j]`, minus one.
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := aC) (by decide)) fun s₁ ⟨_, o₁, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₁.ws (o := aC) (a := j) (by decide) hj16 (Ne.symm hjC)) fun s₂ ⟨c₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.arr (by decide) (by omega_arith) o₂ k₂ (by decide)
  rw [ot o₁ (Nat.le_refl _) hjC hj16] at c₂
  -- The low word.
  have sC := h.ws.sl (j := aC) (by decide)
  refine WP.seq (WP.mono (decA_ok h₂.ws (j := aC) (by decide)) fun s₃ ⟨m₃, k₃⟩ => ?_)
  have o₃ := writeW_outside s₂.mem I.B (VG.Proof.Bignum.word s₂.mem I.B (slot (wk I.k) aC) - 1)
    (d := slot (wk I.k) aC) (by omega_arith)
  rw [← m₃] at o₃
  have h₃ := h₂.arr (by decide) (by omega_arith) o₃ k₃ (by decide)
  -- `[c] = [j] - 1` for an odd `[j]`.
  have vC₃ : wv s₂.mem I.B (slot (wk I.k) aC) (wk I.k) % 2 = 1 →
      wv s₃.mem I.B (slot (wk I.k) aC) (wk I.k) = wv s₂.mem I.B (slot (wk I.k) aC) (wk I.k) - 1 := by
    have w1 := h.ws.w1
    have e3 := wv_low (m := s₃.mem) (B := I.B) (e := slot (wk I.k) aC) (w := wk I.k) (by omega_arith)
    have e2 := wv_low (m := s₂.mem) (B := I.B) (e := slot (wk I.k) aC) (w := wk I.k) (by omega_arith)
    have hw3 : VG.Proof.Bignum.word s₃.mem I.B (slot (wk I.k) aC) =
        VG.Proof.Bignum.word s₂.mem I.B (slot (wk I.k) aC) - 1 := by
      rw [m₃, word_writeW_self]
    have hup : wv s₃.mem I.B (slot (wk I.k) aC + 8) (wk I.k - 1) = wv s₂.mem I.B (slot (wk I.k) aC + 8) (wk I.k - 1) := by
      rw [m₃]; exact (writeW_outside s₂.mem I.B _ (by omega_arith)).wv (Or.inr (by omega_arith)) (by omega_arith)
    intro ho
    rw [e2] at ho ⊢
    have hodd : (VG.Proof.Bignum.word s₂.mem I.B (slot (wk I.k) aC)).toNat % 2 = 1 := by omega_arith
    have hsub : (VG.Proof.Bignum.word s₂.mem I.B (slot (wk I.k) aC) - 1).toNat =
        (VG.Proof.Bignum.word s₂.mem I.B (slot (wk I.k) aC)).toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega_arith)]; rfl
    rw [e3, hup, hw3, hsub]
    omega_arith
  rw [c₂] at vC₃
  -- `[u] := d`.
  refine WP.seq (WP.mono (zeroA_ok h₃.ws (j := aU) (by decide)) fun s₄ ⟨_, o₄, k₄⟩ => ?_)
  have h₄ := h₃.arr (by decide) (Nat.le_refl _) o₄ k₄ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₄.ws (o := aU) (a := aD) (by decide) (by decide) (by decide)) fun s₅ ⟨c₅, o₅, k₅⟩ => ?_)
  have h₅ := h₄.arr (by decide) (by omega_arith) o₅ k₅ (by decide)
  -- `divmod`.
  simp only [seqs]
  refine WP.mono (divmod_ok h₅.ws.scr h₅.ws.rdi h₅.ws.hw h₅.ws.hS (by have := h₅.ws.w1; omega_arith) h₅.ws.w2 hZ
    (iQ := aU) (iR := aV) (iD := aC) (iT := aT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨_, f₆, k₆, hv₆⟩ => ?_
  have ht := h₅.step f₆ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> exact h.ws.sl (by decide)) k₆ (by decide)
  have f6 : ∀ i, i < 16 → i ≠ aU → i ≠ aV → i ≠ aT →
      wv t.mem I.B (slot (wk I.k) i) (wk I.k) = wv s₅.mem I.B (slot (wk I.k) i) (wk I.k) := fun i hi h1 h2 h3 =>
    f₆.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · have := slot_far (w := wk I.k) h1; omega_arith
      · have := slot_far (w := wk I.k) h2; omega_arith
      · have := slot_far (w := wk I.k) h3; omega_arith) (by have := h.ws.sl hi; omega_arith)
  have back : ∀ i, i < 16 → i ≠ aC → i ≠ aU → wv s₅.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k) :=
    fun i hi h1 h2 => by
      rw [ot o₅ (by omega_arith) h2 hi, ot o₄ (Nat.le_refl _) h2 hi, ot o₃ (by omega_arith) h1 hi, ot o₂ (by omega_arith) h1 hi,
        ot o₁ (Nat.le_refl _) h1 hi]
  refine ⟨ht, ?_, fun ho h1 => ?_, fun i hi => ?_⟩
  · have e6 : mword t.mem I.B = mword s₅.mem I.B := f₆.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · have := hdr_lt_slot (wk I.k) aU (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith
      · have := hdr_lt_slot (wk I.k) aV (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith
      · have := hdr_lt_slot (wk I.k) aT (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith) (by omega_arith)
    exact e6.trans ((hmw o₅ (by omega_arith)).trans ((hmw o₄ (Nat.le_refl _)).trans ((hmw o₃ (by omega_arith)).trans
      ((hmw o₂ (by omega_arith)).trans (hmw o₁ (Nat.le_refl _))))))
  · have hC : wv s₅.mem I.B (slot (wk I.k) aC) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) - 1 := by
      rw [ot o₅ (by omega_arith) (by decide) (by decide), ot o₄ (Nat.le_refl _) (by decide) (by decide)]
      exact vC₃ ho
    have hU : wv s₅.mem I.B (slot (wk I.k) aU) (wk I.k) = wv s.mem I.B (slot (wk I.k) aD) (wk I.k) := by
      rw [c₅, ot o₄ (Nat.le_refl _) (by decide) (by decide), ot o₃ (by omega_arith) (by decide) (by decide),
        ot o₂ (by omega_arith) (by decide) (by decide), ot o₁ (Nat.le_refl _) (by decide) (by decide)]
    have hpos : 0 < wv s₅.mem I.B (slot (wk I.k) aC) (wk I.k) := by
      rw [hC]; omega_arith
    rw [(hv₆ hpos).1, hU, hC]
  · have hi16 : i < 16 := by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [f6 i hi16 (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide),
      back i hi16 (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)]

end VG.Proof.Rsa.X86_64
