import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.DPart

/-! ## Small -/
section

/-!
# An RSA key from its primes on x86-64: `d` too small

`smallMask`: ZF clear exactly when `d` exists and `d ≤ 2^(64 w)`
(`smallMask_k`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- Word `k` of a number written, from zero. -/
theorem wv_set {m : Mem} {B : Addr} {d N k : Nat} (v : BitVec 64) (hz : word m B (d + 8 * k) = 0)
    (hd : d + 8 * N ≤ 2 ^ 64) (hk : k < N) : ∀ n ≤ N,
    wv (m.writeW (off B (d + 8 * k)) v) B d n = wv m B d n + (if k < n then 2 ^ (64 * k) * v.toNat else 0)
  | 0, _ => by simp [wv]
  | n + 1, hn => by
    rw [wv, wv, wv_set v hz hd hk n (by omega)]
    by_cases hkn : n = k
    · subst hkn; rw [word_writeW_self, hz]; simp
    · rw [(writeW_outside m B v (d := d + 8 * k) (by omega)).word (by omega) (by omega)]
      by_cases hk' : k < n
      · simp [hk', show k < n + 1 by omega]; omega
      · simp [hk', show ¬ k < n + 1 by omega]

/-- `smallMask`: ZF clear iff `kOk` and `[aDd] ≤ 2^(64 w)`, for `W = 2 w`. -/
theorem smallMask_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {w : Nat} (hW : I.W = 2 * w) {ok : Bool}
    (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa (seqs smallMask) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem ∧
      t.zf = some (!(decide (av I s.mem aDd ≤ 2 ^ (64 * w)) && ok)) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  have hw1 : 1 ≤ w := by have := h.ws.w1; omega
  have hw2 := h.ws.w2
  have sC := h.ws.sl (j := aC) (by decide)
  unfold smallMask
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp) (WP.mono (constA_k h 1) fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  -- Word `w` of `[aC]` set: `[aC] = 2^(64 w) + 1`.
  refine wp_seqs_append (by simp) (by simp [ltA]) ?_
  simp only [seqs]
  refine WP.mono (Q := fun (t : State) => t.mem = s₁.mem.writeW (off I.B (slot I.W aC + 8 * w)) (1 : BitVec 64) ∧
    Keep [.r12, .r9, .rbx, .rax, .rdx] s₁ t) ?_ fun (s₂ : State) ⟨m₂, k₂⟩ => ?_
  · rw [WP.block_append_iff]
    refine WP.mono h₁.ws.ws_ok fun u₁ ⟨h12, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aC (r := .rbx) (by decide) ((ku₁.gpr (by decide)).trans h₁.ws.rdi) h9)
      fun u₂ ⟨hbx, mu₂, ku₂⟩ => ?_
    have hs₂ := h₁.ws.scr.congr (ku₁.trans ku₂).2.2
    have h12₂ : u₂.gpr .r12 = BitVec.ofNat 64 I.W := (ku₂.gpr (by decide)).trans h12
    refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = s₁.mem.writeW (off I.B (slot I.W aC + 8 * w)) (1 : BitVec 64)) (by
      have ew : BitVec.ofNat 64 I.W >>> 1 = BitVec.ofNat 64 w := by
        rw [ofNat_shr1 (by omega)]; congr 1; omega
      xrun [State.ea, ix, h12₂, ew, addr0 hbx rfl, hs₂.st (d := slot I.W aC + 8 * w) (by omega), mu₂, mu₁]
      rfl) rfl) fun t ⟨hm, k⟩ => ⟨hm, ((ku₁.trans ku₂).trans k).mono (by simp)⟩
  have o₂ := writeW_outside s₁.mem I.B (1 : BitVec 64) (d := slot I.W aC + 8 * w) (by omega)
  rw [← m₂] at o₂
  have f₂ := KF.arr1 (I := I) (j := aC) o₂ (by omega) (by omega)
  have h₂ := h₁.step f₂ (all_mut_arr (by decide)) k₂ (by decide)
  have c₂ : av I s₂.mem aC = 2 ^ (64 * w) + 1 := by
    have hz : word s₁.mem I.B (slot I.W aC + 8 * w) = 0 := by
      have e := VG.Proof.Rsa.X86_64.wv_low (m := s₁.mem) (B := I.B) (e := slot I.W aC) (w := I.W + 2) (by omega)
      rw [c₁] at e
      have h0 : wv s₁.mem I.B (slot I.W aC + 8) (I.W + 2 - 1) = 0 := by
        rcases Nat.eq_zero_or_pos (wv s₁.mem I.B (slot I.W aC + 8) (I.W + 2 - 1)) with h0 | h0
        · exact h0
        · have := Nat.le_mul_of_pos_right (2 ^ 64) h0
          simp only [show (1 : BitVec 32).toNat = 1 from rfl] at e; omega
      have := (wv_eq_zero_iff _ _ _ _).mp h0 (w - 1) (by omega)
      rwa [show slot I.W aC + 8 + 8 * (w - 1) = slot I.W aC + 8 * w by omega] at this
    have hv1 : av I s₁.mem aC = 1 := av_of_full c₁ (two_le_pow h (by decide))
    dsimp only [av] at hv1 ⊢
    rw [m₂, wv_set (1 : BitVec 64) hz (by omega) (by omega) I.W (Nat.le_refl _), hv1, ite_eq_left (by omega)]
    simp; omega
  have vD : av I s₂.mem aDd = av I s.mem aDd := by
    rw [f₂.av (by decide) (by decide) (by decide) hZ, f₁.av (by decide) (by decide) (by decide) hZ]
  refine wp_seqs_append (by simp [ltA]) (by simp) (WP.mono (ltA_k h₂ (a := aDd) (b := aC) (by decide) (by decide))
    fun s₃ ⟨h₃, m₃, hbp, _, _, _, k₃⟩ => ?_)
  rw [vD, c₂] at hbp
  simp only [seqs]
  have hok₃ : word s₃.mem I.B (8 * kOk) = mask ok := by
    rw [m₃, f₂.word (by decide) (by decide) (by decide), f₁.word (by decide) (by decide) (by decide), hok]
  have hld := h₃.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.zf = some (!(decide (av I s.mem aDd ≤ 2 ^ (64 * w)) && ok)) ∧
    t.mem = s₃.mem) (by
      xrun [State.ea, hdr, h₃.ws.rdi, hdrOff, hld, hbp, hok₃, mask_and']
      have hd : decide (av I s.mem aDd < 2 ^ (64 * w) + 1) = decide (av I s.mem aDd ≤ 2 ^ (64 * w)) :=
        decide_eq_decide.mpr Nat.lt_succ_iff
      rw [Bool.and_self, hd]
      cases (decide (av I s.mem aDd ≤ 2 ^ (64 * w)) && ok) <;> decide) rfl) fun t ⟨⟨hz, m⟩, k⟩ => by
    have f₂' : KF I.B I.W [.arr aC] s₁.mem t.mem := by rw [m, m₃]; exact f₂
    exact ⟨h₃.step (cs := []) (by rw [m]; exact KF.refl _ _ _) rfl k (by decide), (f₁.trans f₂').mono (by simp), hz⟩

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## Qinv -/
section

/-!
# An RSA key from its primes on x86-64: `qInv`

`qinvPart`: the inverse of `q` modulo `M = p` (3 unless `p` is odd and at
least 3) into `aX₂`, and `kOk &= ` the mask of `gcd(q, M) = 1`
(`qinvPart_k`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem qinvPart_eq : qinvPart = [zeroA aU, copyA aU aQa] ++ (constA 3 ++ (ltA aPa aC ++
    (([.block (([.mov .rcx (.reg .rbp), .alu .xor .rcx (.imm (BitVec.ofInt 32 (-1)))] : List Instr) ++ oddMask aPa ++
        ([.alu .and .rax (.reg .rcx), .mov .rbp (.reg .rax)] : List Instr)), zeroA aM, copyA aM aPa] : List (Prog isa)) ++
    (selC aM ++ (invFrom aM ++ ([inverse aU aV aX₁ aX₂ aM aT] ++ gcdIsOne)))))) := by
  simp only [qinvPart, gcdIsOne, List.append_assoc]

/-- The modulus of `qInv`: `p` if it is odd and at least 3, else 3. -/
abbrev qMod (P : Nat) : Nat := if (decide (P % 2 = 1) && !decide (P < 3)) = true then P else 3

/-- The parts `qinvPart` changes. -/
abbrev csQ : List Rc :=
  [.arr aU, .arr aC, .arr aM, .arr aV, .arr aX₁, .arr aX₂, .arr aT, .hdr sMo, .hdr kOk]

/-- `qinvPart`, for `[aPa] = P` and `[aQa] = Q`. -/
theorem qinvPart_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {P Q : Nat} {ok : Bool}
    (hP : av I s.mem aPa = P) (hQ : av I s.mem aQa = Q) (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa (seqs qinvPart) s fun t => KS I m₀ t ∧ KF I.B I.W csQ s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (decide (Nat.gcd Q (qMod P) = 1) && ok) ∧
      ((qMod P : Nat) : Int) ∣ (av I t.mem aX₂ : Int) * Q - Nat.gcd Q (qMod P) ∧ av I t.mem aX₂ < qMod P := by
  have hZ := h.hZ
  rw [qinvPart_eq]
  -- `[aU] := q`.
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (zc_k h (o := aU) (a := aQa) (by decide) (by decide)
    (by decide)) fun s₁ ⟨h₁, f₁, v₁, t₁⟩ => ?_)
  rw [hQ] at v₁
  refine wp_seqs_append (by simp [constA]) (by simp [ltA]) (WP.mono (constA_k h₁ 3) fun s₂ ⟨h₂, f₂, c₂, _⟩ => ?_)
  have c3 : av I s₂.mem aC = 3 := av_of_full c₂ (two_le_pow h (by decide))
  have vP₂ : av I s₂.mem aPa = P := by
    rw [f₂.av (by decide) (by decide) (by decide) hZ, f₁.av (by decide) (by decide) (by decide) hZ, hP]
  refine wp_seqs_append (by simp [ltA]) (by simp) (WP.mono (ltA_k h₂ (a := aPa) (b := aC) (by decide) (by decide))
    fun s₃ ⟨h₃, m₃, hbp₃, _, _, _, k₃⟩ => ?_)
  rw [vP₂, c3] at hbp₃
  generalize hpv : (decide (P % 2 = 1) && !decide (P < 3)) = pv
  -- `rbp := ` the mask of `p` odd and at least 3; `[aM] := p`.
  refine wp_seqs_append (by simp) (by simp [selC]) ?_
  simp only [seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono (WP.keep [.rcx]
    (Q := fun t => t.gpr .rcx = mask (!decide (P < 3)) ∧ t.mem = s₃.mem) (by xrun [hbp₃, sxM1, maskNot]) rfl)
    fun s₄ ⟨⟨hcx₄, m₄⟩, k₄⟩ => ?_)))
  have h₄ := h₃.step (cs := []) (by rw [m₄]; exact KF.refl _ _ _) rfl k₄ (by decide)
  refine WP.mono (oddMask_k h₄ (j := aPa) (by decide)) fun s₅ ⟨m₅, hax, _, _, k₅⟩ => ?_
  rw [m₄, m₃, vP₂] at hax
  have hcx₅ : s₅.gpr .rcx = mask (!decide (P < 3)) := by rw [k₅.gpr (by decide), hcx₄]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.gpr .rbp = mask pv ∧ t.mem = s₅.mem) (by
    xrun [hax, hcx₅, mask_and']; rw [hpv]) rfl) fun s₆ ⟨⟨hbp₆, m₆⟩, k₆⟩ => ?_
  have h₆ := h₄.step (cs := []) (by rw [m₆, m₅]; exact KF.refl _ _ _) rfl (k₅.trans k₆) (by decide)
  have hm₆ : s₆.mem = s₂.mem := by rw [m₆, m₅, m₄, m₃]
  refine WP.seq (WP.mono (zeroA_k h₆ (j := aM) (by decide)) fun s₇ ⟨h₇, f₇, _, k₇⟩ =>
    WP.mono (copyA_k h₇ (o := aM) (a := aPa) (by decide) (by decide) (by decide)) fun s₈ ⟨h₈, f₈, v₈, _, k₈⟩ => ?_)
  have vP₆ : av I s₆.mem aPa = P := by rw [hm₆, vP₂]
  rw [f₇.av (by decide) (by decide) (by decide) hZ, vP₆] at v₈
  have vC₈ : av I s₈.mem aC = 3 := by
    rw [f₈.av (by decide) (by decide) (by decide) hZ, f₇.av (by decide) (by decide) (by decide) hZ, hm₆, c3]
  -- `[aM] := M`.
  refine wp_seqs_append (by simp [selC]) (by simp [invFrom]) (WP.mono (selC_k h₈ (j := aM) (by decide) (by decide)
    (c := pv) (by rw [k₈.gpr (by decide), k₇.gpr (by decide), hbp₆])) fun s₉ ⟨h₉, f₉, v₉, _, _⟩ => ?_)
  rw [v₈, vC₈] at v₉
  have hM : (if pv = true then P else 3) = qMod P := by rw [← hpv]
  rw [hM] at v₉
  have hMo : qMod P % 2 = 1 ∧ 1 < qMod P := by
    unfold qMod
    by_cases hc : (decide (P % 2 = 1) && !decide (P < 3)) = true
    · rw [ite_eq_left hc]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hc
      omega
    · rw [ite_eq_right hc]; decide
  -- The inverse.
  refine wp_seqs_append (by simp [invFrom]) (by simp) (WP.mono (invFrom_k h₉ (j := aM) (by decide) (by decide))
    fun s₁₀ ⟨h₁₀, f₁₀, vV₁₀, vX₁₁₀, vX₂₁₀⟩ => ?_)
  have hok10 : [Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂].all Rc.ok = true := by decide
  have vM₁₀ : av I s₁₀.mem aM = qMod P := by rw [f₁₀.av hok10 (by decide) (by decide) hZ, v₉]
  have pU : av I s₁₀.mem aU = Q ∧ atop I s₁₀.mem aU = 0 := by
    have hK : ∀ {m m' : Mem} {cs : List Rc}, KF I.B I.W cs m m' → cs.all Rc.ok = true → .arr aU ∉ cs →
        av I m' aU = av I m aU ∧ atop I m' aU = atop I m aU := fun f ok hn =>
      ⟨f.av ok (by decide) hn hZ, f.at ok (by decide) hn hZ⟩
    obtain ⟨a1, b1⟩ := hK f₁₀ hok10 (by decide)
    obtain ⟨a2, b2⟩ := hK f₉ (by decide) (by decide)
    obtain ⟨a3, b3⟩ := hK f₈ (by decide) (by decide)
    obtain ⟨a4, b4⟩ := hK f₇ (by decide) (by decide)
    obtain ⟨a5, b5⟩ := hK f₂ (by decide) (by decide)
    rw [hm₆] at a4 b4
    exact ⟨by rw [a1, a2, a3, a4, a5, v₁], by rw [b1, b2, b3, b4, b5, t₁]⟩
  refine wp_seqs_append (by simp) (by simp [gcdIsOne, constA]) ?_
  simp only [seqs]
  refine WP.mono (inverse_k h₁₀ (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aM) (iT := aT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) pU.2 (by rw [vV₁₀, v₉, vM₁₀]) vX₁₁₀ vX₂₁₀) fun s₁₁ ⟨h₁₁, f₁₁, hinv⟩ => ?_
  rw [vM₁₀, pU.1] at hinv
  obtain ⟨hg₁₁, hdv₁₁, hx₁₁⟩ := hinv hMo.1 hMo.2
  have hokI : [Rc.arr aU, Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT, Rc.hdr sMo].all Rc.ok = true := by decide
  have ok₁₁ : word s₁₁.mem I.B (8 * kOk) = mask ok := by
    rw [f₁₁.word hokI (by decide) (by decide), f₁₀.word hok10 (by decide) (by decide),
      f₉.word (by decide) (by decide) (by decide), f₈.word (by decide) (by decide) (by decide),
      f₇.word (by decide) (by decide) (by decide), hm₆, f₂.word (by decide) (by decide) (by decide),
      f₁.word (by decide) (by decide) (by decide), hok]
  refine WP.mono (gcdIsOne_k h₁₁ ok₁₁) fun t ⟨ht, f₁₂, ok₁₂⟩ => ?_
  rw [hg₁₁] at ok₁₂ hdv₁₁
  have vX : av I t.mem aX₂ = av I s₁₁.mem aX₂ := f₁₂.av (by decide) (by decide) (by decide) hZ
  have f₂₆ : KF I.B I.W [.arr aC] s₁.mem s₆.mem := by rw [hm₆]; exact f₂
  refine ⟨ht, ?_, ok₁₂, by rw [vX]; exact hdv₁₁, by rw [vX]; exact hx₁₁⟩
  exact ((((((((f₁.trans f₂₆).trans f₇).trans f₈).trans f₉).trans f₁₀).trans f₁₁).trans f₁₂)).mono (by simp)

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## Crt -/
section

/-!
# An RSA key from its primes on x86-64: `dP` and `dQ`

`divisorOf j`: `[aM] := [j]`, or 1 for 0 (`divisorOf_k`); `crtPart`:
`dP = d mod (p − 1)` into `aX₁` and `dQ = d mod (q − 1)` into `aV`
(`crtPart_k`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- A divisor: `x`, or 1 for 0. -/
abbrev dv (x : Nat) : Nat := if x = 0 then 1 else x

theorem divisorOf_eq (j : Nat) : divisorOf j = [zeroA aM, copyA aM j] ++ (constA 0 ++ (eqMask j aC ++
    ([.block (ws ++ base aM .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rbp (.imm 1), .alu .or .rax (.reg .rbp),
      .store (at0 .rbx) .rax] : List Instr))] : List (Prog isa)))) := by
  simp only [divisorOf, List.append_assoc]

/-- `divisorOf j`. -/
theorem divisorOf_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16) (hjM : j ≠ aM)
    (hjC : j ≠ aC) :
    WP isa (seqs (divisorOf j)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aM, .arr aC] s.mem t.mem ∧
      av I t.mem aM = dv (av I s.mem j) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  have sM := h.ws.sl (j := aM) (by decide)
  rw [divisorOf_eq]
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (zc_k h (o := aM) (a := j) (by decide) hj hjM.symm)
    fun s₁ ⟨h₁, f₁, v₁, _⟩ => ?_)
  refine wp_seqs_append (by simp [constA]) (by simp [eqMask, eqA]) (WP.mono (constA_k h₁ 0) fun s₂ ⟨h₂, f₂, c₂, _⟩ => ?_)
  have c0 : av I s₂.mem aC = 0 := av_of_full c₂ (Nat.two_pow_pos _)
  have vj : av I s₂.mem j = av I s.mem j := by
    rw [f₂.av (by decide) hj (by simp [hjC]) hZ, f₁.av (by decide) hj (by simp [hjM]) hZ]
  have vM₂ : av I s₂.mem aM = av I s.mem j := by rw [f₂.av (by decide) (by decide) (by decide) hZ, v₁]
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) (WP.mono (eqMask_k h₂ (a := j) (b := aC) hj (by decide))
    fun s₃ ⟨h₃, m₃, hbp₃, _⟩ => ?_)
  rw [vj, c0] at hbp₃
  simp only [seqs]
  refine WP.mono (Q := fun (t : State) => t.mem = s₃.mem.writeW (off I.B (slot I.W aM))
      (if decide (av I s.mem j = 0) then word s₃.mem I.B (slot I.W aM) ||| 1 else word s₃.mem I.B (slot I.W aM)) ∧
      Keep [.r12, .r9, .rbx, .rax, .rbp] s₃ t) ?_ fun (t : State) ⟨m₄, k₄⟩ => ?_
  · rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono h₃.ws.ws_ok fun u₁ ⟨_, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aM (r := .rbx) (by decide) ((ku₁.gpr (by decide)).trans h₃.ws.rdi) h9)
      fun u₂ ⟨hbx, mu₂, ku₂⟩ => ?_
    have hs₂ := h₃.ws.scr.congr (ku₁.trans ku₂).2.2
    have hbp : u₂.gpr .rbp = mask (decide (av I s.mem j = 0)) := by rw [(ku₁.trans ku₂).gpr (by decide), hbp₃]
    have hmu : u₂.mem = s₃.mem := by rw [mu₂, mu₁]
    refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.mem = s₃.mem.writeW (off I.B (slot I.W aM))
      (if decide (av I s.mem j = 0) then word s₃.mem I.B (slot I.W aM) ||| 1 else word s₃.mem I.B (slot I.W aM))) (by
        xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
          hs₂.ld (d := slot I.W aM) (by omega), hs₂.st (d := slot I.W aM) (by omega), hbp, hmu]
        rw [or_and1_mask]) rfl) fun t ⟨hm, k⟩ => ⟨hm, ((ku₁.trans ku₂).trans k).mono (by simp)⟩
  have o₄ := writeW_outside s₃.mem I.B (if decide (av I s.mem j = 0) then word s₃.mem I.B (slot I.W aM) ||| 1 else
    word s₃.mem I.B (slot I.W aM)) (d := slot I.W aM) (by omega)
  rw [← m₄] at o₄
  have f₄ := KF.arr1 (I := I) (j := aM) o₄ (Nat.le_refl _) (by omega)
  refine ⟨h₃.step f₄ (all_mut_arr (by decide)) k₄ (by decide), ((f₁.trans f₂).trans (by rw [← m₃]; exact f₄)).mono
    (by simp), ?_⟩
  have vM₃ : av I s₃.mem aM = av I s.mem j := by rw [m₃, vM₂]
  rw [m₄, av_or1 hw1 (by omega) (fun hc => by rw [vM₃]; simpa using hc), vM₃]
  by_cases hz : av I s.mem j = 0 <;> simp [hz, dv]

/-- The parts `crtPart` changes. -/
abbrev csC : List Rc := [.arr aM, .arr aC, .arr aU, .arr aV, .arr aT, .arr aX₁]

/-- `crtPart`: `[aX₁] := d mod dv(P − 1)`, `[aV] := d mod dv(Q − 1)`, for `[aDd] = d`,
`[aPm] = P − 1` and `[aQm] = Q − 1`. -/
theorem crtPart_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {d a b : Nat} (hd : av I s.mem aDd = d)
    (ha : av I s.mem aPm = a) (hb : av I s.mem aQm = b) :
    WP isa (seqs crtPart) s fun t => KS I m₀ t ∧ KF I.B I.W csC s.mem t.mem ∧
      av I t.mem aX₁ = d % dv a ∧ av I t.mem aV = d % dv b := by
  have hZ := h.hZ
  have hdv : ∀ x, 0 < dv x := fun x => by unfold dv; split <;> omega
  have hdW : ∀ {x}, x < 2 ^ (64 * I.W) → dv x < 2 ^ (64 * I.W) := fun hx => by
    unfold dv; split
    · exact Nat.one_lt_two_pow (by have := h.ws.w1; omega)
    · exact hx
  unfold crtPart
  simp only [List.append_assoc]
  -- `dP`.
  refine wp_seqs_append (by simp [divisorOf]) (by simp) (WP.mono (divisorOf_k h (j := aPm) (by decide) (by decide)
    (by decide)) fun s₁ ⟨h₁, f₁, v₁⟩ => ?_)
  rw [ha] at v₁
  have hok1 : [Rc.arr aM, Rc.arr aC].all Rc.ok = true := by decide
  have vD₁ : av I s₁.mem aDd = d := by rw [f₁.av hok1 (by decide) (by decide) hZ, hd]
  refine wp_seqs_append (by simp) (by simp [divisorOf]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₁ (j := aU) (by decide)) fun s₂ ⟨h₂, f₂, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₂ (o := aU) (a := aDd) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, v₃, _, _⟩ =>
      WP.seq (WP.mono (divmod_k h₃ (iQ := aU) (iR := aV) (iD := aM) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨h₄, f₄, d₄⟩ =>
        WP.seq (WP.mono (zeroA_k h₄ (j := aX₁) (by decide)) fun s₅ ⟨h₅, f₅, _, _⟩ =>
          WP.mono (copyA_k h₅ (o := aX₁) (a := aV) (by decide) (by decide) (by decide))
            fun s₆ ⟨h₆, f₆, v₆, _, _⟩ => ?_))))
  have vM₃ : av I s₃.mem aM = dv a := by
    rw [f₃.av (by decide) (by decide) (by decide) hZ, f₂.av (by decide) (by decide) (by decide) hZ, v₁]
  have vU₃ : av I s₃.mem aU = d := by rw [v₃, f₂.av (by decide) (by decide) (by decide) hZ, vD₁]
  rw [vM₃, vU₃] at d₄
  have hR := (d₄ (hdv a)).1
  have hlt : d % dv a < dv a := Nat.mod_lt _ (hdv a)
  have vM₁W : dv a < 2 ^ (64 * I.W) := by rw [← v₁]; exact wv_lt _ _ _ _
  have vX₆ : av I s₆.mem aX₁ = d % dv a := by
    rw [v₆, f₅.av (by decide) (by decide) (by decide) hZ, ← hR]
    exact wv_low_of_lt (by omega) (by rw [hR]; omega)
  have hok4 : [Rc.arr aU, Rc.arr aV, Rc.arr aT].all Rc.ok = true := by decide
  have pres6 : ∀ j, j < 16 → j ≠ aU → j ≠ aV → j ≠ aT → j ≠ aX₁ → av I s₆.mem j = av I s₁.mem j :=
    fun j hj h1 h2 h3 h4 => by
      rw [f₆.av (by decide) hj (by simp [h4]) hZ, f₅.av (by decide) hj (by simp [h4]) hZ,
        f₄.av hok4 hj (by simp [h1, h2, h3]) hZ, f₃.av (by decide) hj (by simp [h1]) hZ,
        f₂.av (by decide) hj (by simp [h1]) hZ]
  have vQm₆ : av I s₆.mem aQm = b := by
    rw [pres6 aQm (by decide) (by decide) (by decide) (by decide) (by decide), f₁.av hok1 (by decide) (by decide) hZ, hb]
  have vD₆ : av I s₆.mem aDd = d := by
    rw [pres6 aDd (by decide) (by decide) (by decide) (by decide) (by decide), vD₁]
  -- `dQ`.
  refine wp_seqs_append (by simp [divisorOf]) (by simp) (WP.mono (divisorOf_k h₆ (j := aQm) (by decide) (by decide)
    (by decide)) fun s₇ ⟨h₇, f₇, v₇⟩ => ?_)
  rw [vQm₆] at v₇
  have vD₇ : av I s₇.mem aDd = d := by rw [f₇.av hok1 (by decide) (by decide) hZ, vD₆]
  have vX₇ : av I s₇.mem aX₁ = d % dv a := by rw [f₇.av hok1 (by decide) (by decide) hZ, vX₆]
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₇ (j := aU) (by decide)) fun s₈ ⟨h₈, f₈, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₈ (o := aU) (a := aDd) (by decide) (by decide) (by decide)) fun s₉ ⟨h₉, f₉, v₉, _, _⟩ =>
      WP.mono (divmod_k h₉ (iQ := aU) (iR := aV) (iD := aM) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨ht, f₁₀, d₁₀⟩ => ?_))
  have vM₉ : av I s₉.mem aM = dv b := by
    rw [f₉.av (by decide) (by decide) (by decide) hZ, f₈.av (by decide) (by decide) (by decide) hZ, v₇]
  have vU₉ : av I s₉.mem aU = d := by rw [v₉, f₈.av (by decide) (by decide) (by decide) hZ, vD₇]
  rw [vM₉, vU₉] at d₁₀
  have hR' := (d₁₀ (hdv b)).1
  have vMb : dv b < 2 ^ (64 * I.W) := by rw [← v₇]; exact wv_lt _ _ _ _
  refine ⟨ht, ?_, ?_, ?_⟩
  · exact (((((((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).trans f₆).trans f₇).trans f₈).trans f₉).trans
      f₁₀).mono (by simp)
  · rw [f₁₀.av hok4 (by decide) (by decide) hZ, f₉.av (by decide) (by decide) (by decide) hZ,
      f₈.av (by decide) (by decide) (by decide) hZ, vX₇]
  · rw [← hR']
    exact wv_low_of_lt (by omega) (by rw [hR']; exact Nat.lt_trans (Nat.mod_lt _ (hdv b)) vMb)

end VG.Proof.RsaKeyGen.X86_64.Key

end
