import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Pieces
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdE

/-!
# An RSA key from its primes on AArch64: the primes

The loads of `p`, `q` and `e` (`loads_k`), `p` and `q` ordered (`order_k`),
and `p − 1` and `q − 1` (`decTo_k`); together, from `KS` to `KPrimes`
(`front_k`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-! ## The loads -/

/-- `p`, `q` (`pl` octets each) into `aPa` and `aQa`, and `e` into `kEv`. -/
theorem loads_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (L : KLens I) :
    WP isa (seqs (loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++
      ([.block [sth .x3 kEv]] : List (Prog isa)))))) s
      fun t => KS I s₀ t ∧ KF I.B I.W [.arr aPa, .arr aQa, .hdr kEv] s.mem t.mem ∧
        av I t.mem aPa = I.P₀ ∧ av I t.mem aQa = I.Q₀ ∧ word t.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E := by
  have hZ := h.hZ
  have hW := L.W
  have hpl1 := L.pl1
  have hpl8 := L.pl8
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h.ws (j := aPa) (by decide)
    (by decide) (by decide) h.args.pp h.args.pl h.p L.pbl (by omega) (by omega)) fun s₁ ⟨v₁, o₁, _, _, k₁⟩ => ?_)
  have f₁ := KF.arr1 (B := I.B) (W := I.W) (j := aPa) o₁ (Nat.le_refl _) (Nat.le_refl _)
  have h₁ := h.step f₁ (all_mut_arr (by decide)) k₁
  refine wp_seqs_append (by simp [loadA]) (by simp [loadE]) (WP.mono (loadA_ok h₁.ws (j := aQa) (by decide)
    (by decide) (by decide) h₁.args.qp h₁.args.pl h₁.q L.qbl (by omega) (by omega)) fun s₂ ⟨v₂, o₂, _, _, k₂⟩ => ?_)
  have f₂ := KF.arr1 (B := I.B) (W := I.W) (j := aQa) o₂ (Nat.le_refl _) (Nat.le_refl _)
  have h₂ := h₁.step f₂ (all_mut_arr (by decide)) k₂
  refine wp_seqs_append (by simp [loadE]) (by simp) (WP.mono (loadE_ok h₂.ws h₂.args.e
    (by rw [h₂.args.el, L.ebl]) (by rw [L.ebl]; exact L.el1) (by rw [L.ebl]; exact L.el8) h₂.e)
    fun s₃ ⟨hx3, m₃, k₃⟩ => ?_)
  have h₃ := h₂.regs m₃ k₃
  simp only [seqs]
  have hst := h₃.ws.scr.st (d := 8 * kEv) (by have := h₃.ws.h256; unfold kEv sFn; omega)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₃.mem.writeW (off I.B (8 * kEv))
    (BitVec.ofNat 64 I.E)) (by
      have hx3' : s₃.gpr .x3 = BitVec.ofNat 64 I.E := by
        show _ = BitVec.ofNat 64 (Spec.Rsa.os2ip I.eb); rw [← hx3, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      brun [h₃.ws.x0, hdr_enc (show kEv < 32 by decide), hst, hx3']) rfl rfl rfl) fun t ⟨hm, k₄⟩ => ?_
  obtain ⟨ht, f₄, hw⟩ := h₃.hdrW (i := kEv) (by unfold kEv sFn; omega) hm k₄
  refine ⟨ht, ((f₁.trans f₂).trans (by rw [← m₃]; exact f₄)).mono (by simp), ?_, ?_, hw⟩
  · rw [f₄.av (by decide) (j := aPa) (by decide) (by decide) hZ, m₃,
      f₂.av (by decide) (j := aPa) (by decide) (by decide) hZ]; exact v₁
  · rw [f₄.av (by decide) (j := aQa) (by decide) (by decide) hZ, m₃]; exact v₂

/-! ## The order -/

/-- `order`: `p` and `q` swapped if `p < q`. -/
theorem order_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (seqs order) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aPa, .arr aQa] s.mem t.mem ∧
      av I t.mem aPa = (if av I s.mem aPa < av I s.mem aQa then av I s.mem aQa else av I s.mem aPa) ∧
      av I t.mem aQa = (if av I s.mem aPa < av I s.mem aQa then av I s.mem aPa else av I s.mem aQa) := by
  have hn := h.ws.scr.nowrap
  have sP := h.ws.sl (j := aPa) (by decide)
  have sQ := h.ws.sl (j := aQa) (by decide)
  have sp := slot_sep (w := I.W) (j := aPa) (k := aQa) (by decide)
  unfold order
  refine wp_seqs_append (by simp [ltA, cmpA]) (by simp) (WP.mono (ltA_k h (a := aPa) (b := aQa) (by decide)
    (by decide)) fun s₁ ⟨h₁, m₁, h15, _, k₁⟩ => ?_)
  simp only [seqs]
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (wsMov_ok h₁.ws) fun s₂ ⟨⟨h12, h11, h14, m₂, _⟩, k₂⟩ =>
    WP.mono (base2_ok aPa aQa .x16 .x17 ((k₂.gpr .x0 (by decide)).trans h₁.ws.x0) h11)
      fun s₃ ⟨⟨h16, h17, m₃, _⟩, k₃⟩ => ?_))
  have k23 := k₂.trans k₃
  refine WP.mono (cswap_ok (h₁.ws.scr.congr k23.wr) h16 h17 ((k23.gpr .x15 (by decide)).trans h15)
    ((k₃.gpr .x14 (by decide)).trans h14) (by have := h.ws.w1; omega) (by have := h.ws.w2; omega) (by omega)
    (by omega) (by omega)) fun t ⟨hX, hY, hf, k₄⟩ => ?_
  have hm : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  rw [hm] at hX hY hf
  have f : KF I.B I.W [.arr aPa, .arr aQa] s.mem t.mem :=
    KF.of_frm hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨.arr aPa, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
      · exact ⟨.arr aQa, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
  refine ⟨h.step f (all_mut_arrs (js := [aPa, aQa]) (by decide)) ((k₁.trans k23).trans k₄), f, ?_, ?_⟩
  · dsimp only [av]; rw [hX]; split <;> simp_all
  · dsimp only [av]; rw [hY]; split <;> simp_all

/-! ## Minus one -/

theorem dec_arith {x y L : Nat} {b : Bool} (hx : x < L)
    (hv : x + (if (!decide (y = 0)) = true then 1 else 0) = y + L * b.toNat) : x = y - 1 := by
  by_cases hz : y = 0
  · simp only [hz, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, Nat.add_zero, Nat.zero_add] at hv
    cases b <;> simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero] at hv <;> omega
  · simp only [hz, decide_false, Bool.not_false, ite_true] at hv
    cases b <;> simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero] at hv <;> omega

/-- `decTo`'s last part: `[o] := [o] − ([aC] & x15)` over `W` words. -/
theorem subC_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {o : Nat} (ho : o < 16) (hoC : o ≠ aC) {c : Bool}
    (h15 : s.gpr .x15 = mask c) :
    WP isa (seqs [.block (ws ++ ([movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] : List Instr) ++ base o .x16 ++ base aC .x17 ++
        base o .x8), countLoop .x14 subMBody]) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr o] s.mem t.mem ∧
      (∃ b : Bool, av I t.mem o + (if c then av I s.mem aC else 0) = av I s.mem o + 2 ^ (64 * I.W) * b.toNat) ∧
      atop I t.mem o = atop I s.mem o := by
  have hn := h.ws.scr.nowrap
  have so := h.ws.sl ho
  have sC := h.ws.sl (j := aC) (by decide)
  have pC := slot_sep (w := I.W) hoC
  simp only [seqs]
  rw [show ws ++ ([movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] : List Instr) ++ base o .x16 ++ base aC .x17 ++ base o .x8 =
    (ws ++ ([movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] : List Instr)) ++ (base o .x16 ++ base aC .x17 ++ base o .x8) by
      simp only [List.append_assoc]]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (ltHead_ok h.ws) fun s₁ ⟨⟨_, h11, _, h14, hc, m₁⟩, k₁⟩ =>
    WP.mono (base3_ok o aC o .x16 .x17 .x8 ((k₁.gpr .x0 (by decide)).trans h.ws.x0) h11)
      fun s₂ ⟨⟨h16, h17, h8, m₂, c₂⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  refine WP.mono (subM_ok (N := I.W) (h.ws.scr.congr k12.wr) h16 h17 h8 ((k₂.gpr .x14 (by decide)).trans h14)
    ((k12.gpr .x15 (by decide)).trans h15) (c₂.trans hc) (by have := h.ws.w1; omega) (by have := h.ws.w2; omega)
    (by omega) (by omega) (by omega) (.inl rfl) (by omega)) fun t ⟨hv, o', k₃⟩ => ?_
  rw [m₂, m₁] at hv o'
  have f := KF.arr1 (B := I.B) (W := I.W) (j := o) o' (Nat.le_refl _) (by omega)
  exact ⟨h.step f (all_mut_arr ho) (k12.trans k₃), f, ⟨_, hv⟩, o'.word (Or.inr (Nat.le_refl _)) (by omega)⟩

/-- `decTo o j`: `[o] := [j] − 1` (0 for 0), with word `W` zero. -/
theorem decTo_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {o j : Nat} (ho : o < 16) (hj : j < 16)
    (hoj : o ≠ j) (hoC : o ≠ aC) (hjC : j ≠ aC) :
    WP isa (seqs (decTo o j)) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr o, .arr aC] s.mem t.mem ∧
      av I t.mem o = av I s.mem j - 1 ∧ atop I t.mem o = 0 := by
  have hZ := h.hZ
  have hok : [Rc.arr aC].all Rc.ok = true := by decide
  have e : decTo o j = [zeroA o, copyA o j] ++ (constA 0 ++ (neMask j aC ++ (constA 1 ++
      [.block (ws ++ ([movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] : List Instr) ++ base o .x16 ++ base aC .x17 ++
        base o .x8), countLoop .x14 subMBody]))) := by
    simp only [decTo, List.append_assoc]
  rw [e]
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (zc_k h ho hj hoj) fun s₁ ⟨h₁, f₁, v₁, t₁⟩ => ?_)
  refine wp_seqs_append (by simp [constA]) (by simp [neMask, eqA]) (WP.mono (constA_k h₁ (x := 0) (by decide))
    fun s₂ ⟨h₂, f₂, c₂, _⟩ => ?_)
  have cz : av I s₂.mem aC = 0 := av_of_full c₂ (Nat.two_pow_pos _)
  refine wp_seqs_append (by simp [neMask, eqA]) (by simp [constA]) (WP.mono (neMask_k h₂ (a := j) (b := aC) hj
    (by decide)) fun s₃ ⟨h₃, m₃, h15, _, k₃⟩ => ?_)
  have vj : av I s₂.mem j = av I s.mem j := by
    rw [f₂.av hok hj (by simp [hjC]) hZ]
    exact f₁.av (by simp [Rc.ok, ho]) hj (by simp [hoj.symm]) hZ
  rw [cz, vj] at h15
  refine wp_seqs_append (by simp [constA]) (by simp) (WP.mono (constA_k h₃ (x := 1) (by decide))
    fun s₄ ⟨h₄, f₄, c₄, k₄⟩ => ?_)
  have c1 : av I s₄.mem aC = 1 := av_of_full c₄ (Nat.one_lt_two_pow (by have := h.ws.w1; omega))
  refine WP.mono (subC_k h₄ (o := o) ho hoC (c := !decide (av I s.mem j = 0))
    (by rw [k₄.gpr .x15 (by decide), h15])) fun t ⟨ht, f₅, hb, t₅⟩ => ?_
  obtain ⟨b, hv⟩ := hb
  have vo : av I s₄.mem o = av I s.mem j := by
    rw [f₄.av hok ho (by simp [hoC]) hZ, m₃, f₂.av hok ho (by simp [hoC]) hZ]; exact v₁
  have tO : atop I s₄.mem o = 0 := by
    rw [f₄.at hok ho (by simp [hoC]) hZ, m₃, f₂.at hok ho (by simp [hoC]) hZ]; exact t₁
  refine ⟨ht, (((f₁.trans f₂).trans (by rw [← m₃]; exact f₄)).trans f₅).mono (by simp), ?_, by rw [t₅]; exact tO⟩
  rw [c1, vo] at hv
  exact dec_arith (wv_lt t.mem I.B (slot I.W o) I.W) hv

/-! ## From the loads to `p − 1` and `q − 1` -/

theorem lt_of_os2ip_len {bs : List Byte} {n : Nat} (h : bs.length = n) : Spec.Rsa.os2ip bs < 2 ^ (8 * n) := by
  have := VG.Proof.Bignum.os2ip_lt bs
  rw [h, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  exact this

/-- The parts the front changes. -/
abbrev csF : List Rc := [.arr aPa, .arr aQa, .hdr kEv, .arr aPm, .arr aQm, .arr aC]

/-- From the loads to `p − 1` and `q − 1`. -/
theorem front_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (L : KLens I) :
    WP isa (seqs (loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++
      (([.block [sth .x3 kEv]] : List (Prog isa)) ++ (order ++ (decTo aPm aPa ++ decTo aQm aQa))))))) s
      fun t => KPrimes I s₀ t ∧ KF I.B I.W csF s.mem t.mem ∧ atop I t.mem aPm = 0 ∧ atop I t.mem aQm = 0 := by
  have hZ := h.hZ
  -- The loads.
  rw [show loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++
      (([.block [sth .x3 kEv]] : List (Prog isa)) ++ (order ++ (decTo aPm aPa ++ decTo aQm aQa))))) =
      (loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ ([.block [sth .x3 kEv]] : List (Prog isa))))) ++
        (order ++ (decTo aPm aPa ++ decTo aQm aQa)) by simp only [List.append_assoc]]
  refine wp_seqs_append (by simp [loadA]) (by simp [order, ltA, cmpA]) (WP.mono (loads_k h L)
    fun s₁ ⟨h₁, f₁, vP₁, vQ₁, ev₁⟩ => ?_)
  -- The order.
  refine wp_seqs_append (by simp [order, ltA, cmpA]) (by simp [decTo]) (WP.mono (order_k h₁)
    fun s₂ ⟨h₂, f₂, vP₂, vQ₂⟩ => ?_)
  rw [vP₁, vQ₁] at vP₂ vQ₂
  -- `p − 1`, `q − 1`.
  refine wp_seqs_append (by simp [decTo]) (by simp [decTo]) (WP.mono (decTo_k h₂ (o := aPm) (j := aPa) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, vPm₃, tPm₃⟩ => ?_)
  refine WP.mono (decTo_k h₃ (o := aQm) (j := aQa) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨ht, f₄, vQm₄, tQm₄⟩ => ?_
  have hok3 : [Rc.arr aPm, Rc.arr aC].all Rc.ok = true := by decide
  have hok4 : [Rc.arr aQm, Rc.arr aC].all Rc.ok = true := by decide
  refine ⟨⟨ht, ?_, ?_, ?_, ?_, ?_⟩, (((f₁.trans f₂).trans f₃).trans f₄).mono (by simp), ?_, tQm₄⟩
  · rw [f₄.av hok4 (by decide) (by decide) hZ, f₃.av hok3 (by decide) (by decide) hZ, vP₂]
  · rw [f₄.av hok4 (by decide) (by decide) hZ, f₃.av hok3 (by decide) (by decide) hZ, vQ₂]
  · rw [f₄.av hok4 (by decide) (by decide) hZ, vPm₃, vP₂]
  · rw [vQm₄, f₃.av hok3 (by decide) (by decide) hZ, vQ₂]
  · rw [f₄.word hok4 (by decide) (by decide), f₃.word hok3 (by decide) (by decide),
      f₂.word (by decide) (by decide) (by decide), ev₁]
  · rw [f₄.at hok4 (by decide) (by decide) hZ, tPm₃]

/-! ## Bounds on the inputs -/

theorem KLens.P_lt {I : KIn} (L : KLens I) : I.P < 2 ^ (64 * (I.pl / 8)) := by
  have hw8 : 8 * I.pl = 64 * (I.pl / 8) := by have := L.pl8; omega
  have hP₀ : I.P₀ < 2 ^ (64 * (I.pl / 8)) := by rw [← hw8]; exact lt_of_os2ip_len L.pbl
  have hQ₀ : I.Q₀ < 2 ^ (64 * (I.pl / 8)) := by rw [← hw8]; exact lt_of_os2ip_len L.qbl
  simp only [KIn.P] at hP₀ hQ₀ ⊢; split <;> omega

theorem KLens.Q_lt {I : KIn} (L : KLens I) : I.Q < 2 ^ (64 * (I.pl / 8)) := by
  have hw8 : 8 * I.pl = 64 * (I.pl / 8) := by have := L.pl8; omega
  have hP₀ : I.P₀ < 2 ^ (64 * (I.pl / 8)) := by rw [← hw8]; exact lt_of_os2ip_len L.pbl
  have hQ₀ : I.Q₀ < 2 ^ (64 * (I.pl / 8)) := by rw [← hw8]; exact lt_of_os2ip_len L.qbl
  simp only [KIn.Q] at hP₀ hQ₀ ⊢; split <;> omega

theorem KLens.E_lt {I : KIn} (L : KLens I) : I.E < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (lt_of_os2ip_len L.ebl) (Nat.pow_le_pow_right (by decide) (by have := L.el8; omega))

theorem KLens.L_lt {I : KIn} (L : KLens I) : I.L < 2 ^ (64 * I.W) := by
  have hW := L.W
  have hPw := L.P_lt
  have hQw := L.Q_lt
  have h1 : I.L ≤ (I.P - 1) * (I.Q - 1) ∨ I.L = 0 := by
    rcases Nat.eq_zero_or_pos ((I.P - 1) * (I.Q - 1)) with h0 | h0
    · right; simp only [KIn.L]
      rcases Nat.mul_eq_zero.mp h0 with h' | h' <;> simp [h']
    · left; exact Nat.le_of_dvd h0 (Nat.lcm_dvd_mul _ _)
  have h2 : (I.P - 1) * (I.Q - 1) < 2 ^ (64 * I.W) := by
    rw [hW, show 64 * (2 * (I.pl / 8)) = 64 * (I.pl / 8) + 64 * (I.pl / 8) by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) (Nat.two_pow_pos _)
  rcases h1 with h1 | h1
  · omega
  · rw [h1]; exact Nat.two_pow_pos _

end VG.Proof.RsaKeyGen.AArch64.Key
