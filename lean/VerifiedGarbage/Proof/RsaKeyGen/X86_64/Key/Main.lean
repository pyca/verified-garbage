import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Out

/-!
# An RSA key from its primes on x86-64: from the loads to `smallMask`

`front_k`: after the head, the loads, the order, `p − 1` and `q − 1`,
`L = lcm(p − 1, q − 1)`, `d` and ZF (`Front`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate (loadE)

/-- The inputs as numbers: `p`, `q`, `e`, ordered, and `L`. -/
abbrev KIn.P₀ (I : KIn) : Nat := Spec.Rsa.os2ip I.pb
abbrev KIn.Q₀ (I : KIn) : Nat := Spec.Rsa.os2ip I.qb
abbrev KIn.E (I : KIn) : Nat := Spec.Rsa.os2ip I.eb
abbrev KIn.P (I : KIn) : Nat := if I.P₀ < I.Q₀ then I.Q₀ else I.P₀
abbrev KIn.Q (I : KIn) : Nat := if I.P₀ < I.Q₀ then I.P₀ else I.Q₀
abbrev KIn.L (I : KIn) : Nat := Nat.lcm (I.P - 1) (I.Q - 1)

/-- The lengths. -/
structure KLens (I : KIn) : Prop where
  pl1 : 32 ≤ I.pl
  pl2 : I.pl ≤ 512
  pl8 : I.pl % 8 = 0
  pbl : I.pb.length = I.pl
  qbl : I.qb.length = I.pl
  ebl : I.eb.length = I.el
  el1 : 1 ≤ I.el
  el8 : I.el ≤ 8

/-- What holds after `smallMask`. -/
structure Front (I : KIn) (m₀ : Mem) (t : State) : Prop where
  ks : KS I m₀ t
  vP : av I t.mem aPa = I.P
  vQ : av I t.mem aQa = I.Q
  vPm : av I t.mem aPm = I.P - 1
  vQm : av I t.mem aQm = I.Q - 1
  ev : word t.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E
  d : DRes I I.E I.L t.mem
  zf : ∃ ok : Bool, word t.mem I.B (8 * kOk) = mask ok ∧ ((∃ d, Spec.Rsa.inverse I.E I.L = some d) ↔ ok = true) ∧
    t.zf = some (!(decide (av I t.mem aDd ≤ 2 ^ (8 * I.pl)) && ok))

theorem KLens.W {I : KIn} (L : KLens I) : I.W = 2 * (I.pl / 8) := by
  have := L.pl8; simp only [KIn.W]; omega

theorem lt_of_os2ip_len {bs : List Byte} {n : Nat} (h : bs.length = n) : Spec.Rsa.os2ip bs < 2 ^ (8 * n) := by
  have := VG.Proof.Rsa.lt_of_os2ip bs
  rw [h, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  exact this

/-- From the loads to `smallMask`. -/
theorem front_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (L : KLens I) :
    WP isa (seqs ((loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ ([.block [.store (hdr kEv) .rbx]] : List (Prog isa))))) ++
      (order ++ (decTo aPm aPa ++ (decTo aQm aQa ++ (lcmPart ++ ([dPart] ++ smallMask))))))) s
      fun t => Front I m₀ t ∧ InScr I.B I.Z s.mem t.mem := by
  have hZ := h.hZ
  have hW := L.W
  have hw8 : 8 * I.pl = 64 * (I.pl / 8) := by have := L.pl8; omega
  have hP₀ : I.P₀ < 2 ^ (64 * (I.pl / 8)) := by rw [← hw8]; exact lt_of_os2ip_len L.pbl
  have hQ₀ : I.Q₀ < 2 ^ (64 * (I.pl / 8)) := by rw [← hw8]; exact lt_of_os2ip_len L.qbl
  have hE : I.E < 2 ^ 64 := by
    have := lt_of_os2ip_len L.ebl
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by have := L.el8; omega))
  -- The loads.
  refine wp_seqs_append (by simp [loadA]) (by simp [order, ltA]) (WP.mono (loads_k h L.pbl L.qbl L.ebl
    (by have := L.pl1; omega) (by rw [hW]; have := L.pl8; omega) L.el1 L.el8) fun s₁ ⟨h₁, f₁, vP₁, vQ₁, ev₁⟩ => ?_)
  -- The order.
  refine wp_seqs_append (by simp [order, ltA]) (by simp [decTo]) (WP.mono (order_k h₁) fun s₂ ⟨h₂, f₂, vP₂, vQ₂⟩ => ?_)
  rw [vP₁, vQ₁] at vP₂ vQ₂
  -- `p − 1`, `q − 1`.
  refine wp_seqs_append (by simp [decTo]) (by simp [decTo]) (WP.mono (decTo_k h₂ (o := aPm) (j := aPa) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, vPm₃, _⟩ => ?_)
  refine wp_seqs_append (by simp [decTo]) (by simp [lcmPart, phi]) (WP.mono (decTo_k h₃ (o := aQm) (j := aQa)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨h₄, f₄, vQm₄, _⟩ => ?_)
  have hok3 : [Rc.arr aPm, Rc.arr aC].all Rc.ok = true := by decide
  have hok4 : [Rc.arr aQm, Rc.arr aC].all Rc.ok = true := by decide
  have vP₄ : av I s₄.mem aPa = I.P := by
    rw [f₄.av hok4 (by decide) (by decide) hZ, f₃.av hok3 (by decide) (by decide) hZ, vP₂]
  have vQ₄ : av I s₄.mem aQa = I.Q := by
    rw [f₄.av hok4 (by decide) (by decide) hZ, f₃.av hok3 (by decide) (by decide) hZ, vQ₂]
  rw [vP₂] at vPm₃
  rw [f₃.av hok3 (by decide) (by decide) hZ, vQ₂] at vQm₄
  have vPm₄ : av I s₄.mem aPm = I.P - 1 := by rw [f₄.av hok4 (by decide) (by decide) hZ, vPm₃]
  have hPw : I.P < 2 ^ (64 * (I.pl / 8)) := by
    simp only [KIn.P, KIn.P₀, KIn.Q₀] at hP₀ hQ₀ ⊢; split <;> omega
  have hQw : I.Q < 2 ^ (64 * (I.pl / 8)) := by
    simp only [KIn.Q, KIn.P₀, KIn.Q₀] at hP₀ hQ₀ ⊢; split <;> omega
  -- `L`.
  refine wp_seqs_append (by simp [lcmPart, phi]) (by simp) (WP.mono (lcm_k h₄ hW vPm₄ vQm₄ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hPw)
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hQw))
    fun s₅ ⟨h₅, f₅, vL₅⟩ => ?_)
  have hokL : [Rc.arr aL, Rc.arr aU, Rc.arr aV, Rc.arr aC, Rc.arr aM, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT, Rc.arr aR,
    Rc.hdr sMo, Rc.hdr kOk].all Rc.ok = true := by decide
  have hokE : [Rc.arr aPa, Rc.arr aQa, Rc.hdr kEv].all Rc.ok = true := by decide
  have ev₅ : word s₅.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E := by
    rw [f₅.word hokL (by decide) (by decide), f₄.word hok4 (by decide) (by decide),
      f₃.word hok3 (by decide) (by decide), f₂.word (by decide) (by decide) (by decide), ev₁]
  have hLW : I.L < 2 ^ (64 * I.W) := by
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
  -- `d`.
  refine wp_seqs_append (by simp) (by simp [smallMask, constA]) ?_
  simp only [seqs]
  refine WP.mono (dPart_k h₅ hE ev₅ vL₅ hLW) fun s₆ ⟨h₆, f₆, d₆⟩ => ?_
  obtain ⟨ok, ok₆, iff₆, dd₆⟩ := d₆
  -- ZF.
  refine WP.mono (smallMask_k h₆ hW ok₆) fun t ⟨ht, f₇, zf₇⟩ => ?_
  have hokD : csD.all Rc.ok = true := by decide
  have hok7 : [Rc.arr aC].all Rc.ok = true := by decide
  have pres : ∀ j, j < 16 → Rc.arr j ∉ csD → Rc.arr j ∉ [Rc.arr aC] → Rc.arr j ∉ [Rc.arr aL, Rc.arr aU, Rc.arr aV,
      Rc.arr aC, Rc.arr aM, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT, Rc.arr aR, Rc.hdr sMo, Rc.hdr kOk] →
      av I t.mem j = av I s₄.mem j := fun j hj h1 h2 h3 => by
    rw [f₇.av hok7 hj h2 hZ, f₆.av hokD hj h1 hZ, f₅.av hokL hj h3 hZ]
  have okt : word t.mem I.B (8 * kOk) = mask ok := by rw [f₇.word hok7 (by decide) (by decide), ok₆]
  have hD : av I t.mem aDd = av I s₆.mem aDd := f₇.av hok7 (by decide) (by decide) hZ
  have hi : InScr I.B I.Z s.mem t.mem := fun x hx => (ht.inScr x hx).trans (h.inScr x hx).symm
  refine ⟨⟨ht, ?_, ?_, ?_, ?_, ?_, ⟨ok, okt, iff₆, fun d hd => by rw [hD]; exact dd₆ d hd⟩,
    ⟨ok, okt, iff₆, by rw [zf₇, ← hD, show 64 * (I.pl / 8) = 8 * I.pl by omega]⟩⟩, hi⟩
  · rw [pres aPa (by decide) (by decide) (by decide) (by decide), vP₄]
  · rw [pres aQa (by decide) (by decide) (by decide) (by decide), vQ₄]
  · rw [pres aPm (by decide) (by decide) (by decide) (by decide), vPm₄]
  · rw [pres aQm (by decide) (by decide) (by decide) (by decide), vQm₄]
  · rw [f₇.word hok7 (by decide) (by decide), f₆.word hokD (by decide) (by decide), ev₅]

end VG.Proof.RsaKeyGen.X86_64.Key
