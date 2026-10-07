import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Loop

/-!
# X25519 on x86-64, inversion by divsteps: a batch

A batch (`dbatch`) takes the state of the working area (`DMem`) to the next
`dbatchV` and counts down the batches (`dbatch_ok`), changing only the area
`[512, 768)`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

/-- The working area holds the state `t`. -/
structure DMem (m : Mem) (base : Addr) (t : DSt) : Prop where
  D : word m base dsD = t.D
  f : fe m base dsF = t.f
  g : fe m base dsG = t.g
  a : fe m base dsA = t.a
  b : fe m base dsB = t.b

/-- `r8–r11 = [o]`. -/
theorem loads4_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 32 ≤ 4096) :
    WP isa (.block (loads o .r8 .r9 .r10 .r11)) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = fe s.mem base o ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  drun [loads, State.load64, ea_sc, hs.rdi, inR hs (show o + 8 ≤ 4096 by omega),
    inR hs (show o + 8 + 8 ≤ 4096 by omega), inR hs (show o + 16 + 8 ≤ 4096 by omega),
    inR hs (show o + 24 + 8 ≤ 4096 by omega), RegUpd.gpr_setReg_self]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3, h4⟩ := hr
  simp only [RegUpd.gpr_setReg, h1, h2, h3, h4, ↓reduceIte]

/-- `[dst] = [src]`. -/
theorem copy4_ok {s : State} {base : Addr} (hs : Scr s base) {dst src : Nat} (hd : dst + 32 ≤ 4096)
    (hsrc : src + 32 ≤ 4096) :
    WP isa (.block (copy4 dst src)) s fun t =>
      fe t.mem base dst = fe s.mem base src ∧ Outside base dst 32 s.mem t.mem ∧
      (∀ r, r ∉ [.r8, .r9, .r10, .r11] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hs.nowrap
  rw [copy4, WP.block_append_iff]
  refine WP.mono (loads4_ok hs hsrc) fun s₁ ⟨e1, k1⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps k1 (by decide)) (by unfold Slot; omega)) fun t ⟨mt, gt, rt, wt⟩ =>
    ⟨?_, ?_, fun r hr => (gt r).trans (k1.1 r hr), rt.trans k1.2.2.1, wt.trans k1.2.2.2⟩
  · rw [mt, fe_st4 _ _ (by omega), e1]
  · rw [mt, k1.2.1]; exact st4_outside _ _ (by omega) _ _ _ _

/-- The count of batches less one. -/
theorem batchEnd_ok (s : State) {j : Nat} (hj : 1 ≤ j) (hj' : j ≤ 10) (hc : s.gpr .rbp = BitVec.ofNat 64 (256 * j)) :
    WP isa (.block batchEnd) s fun t =>
      t.gpr .rbp = BitVec.ofNat 64 (256 * (j - 1)) ∧ t.zf = some (decide (j - 1 = 0)) ∧ Keeps [.rbp] s t := by
  have e : BitVec.ofNat 64 (256 * j) - BitVec.signExtend 64 (256 : BitVec 32) = BitVec.ofNat 64 (256 * (j - 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (BitVec.signExtend 64 (256 : BitVec 32)).toNat = 256 by decide]
    omega
  apply WP.of_runBlock
  simp only [batchEnd, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg, RegUpd.zf_setReg, RegUpd.zf_arithFlags, RegUpd.gpr_arithFlags, ite_true,
    Option.some.injEq, exists_eq_left', hc, e]
  refine ⟨trivial, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [ofNat_eq_zero (show 256 * (j - 1) < 2 ^ 64 by omega)]
    simp only [decide_eq_decide]
    omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem dbatch_eq : dbatch = .seq dsteps (.block (fRow dsU dsV dsNF ++ (fRow dsQ dsR dsG ++ (copy4 dsF dsNF ++
    (aRow dsU dsV dsNA ++ (aRow dsQ dsR dsB ++ (copy4 dsA dsNA ++ batchEnd))))))) := by
  simp only [dbatch, List.append_assoc]

theorem wOf_eq {m : Mem} {base : Addr} {t : DSt} (h : DMem m base t) :
    wOf m base = Divstep.wsteps 59 ⟨t.D, BitVec.ofNat 64 t.f, BitVec.ofNat 64 t.g, 1, 0, 0, 1⟩ := by
  rw [wOf, ← ofNat_fe m base dsF, ← ofNat_fe m base dsG, h.D, h.f, h.g]

/-- Writes within the working area. -/
theorem Outside.wide {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (h1 : 512 ≤ o)
    (h2 : o + n ≤ 768) : Outside base 512 256 m m' := fun x hx => h x (by omega)

/-- A batch. -/
theorem dbatch_ok {s : State} {base : Addr} (hs : Scr s base) {t₀ : DSt} (hm : DMem s.mem base t₀) {j : Nat}
    (hj : 1 ≤ j) (hj10 : j ≤ 10) (hc : s.gpr .rbp = BitVec.ofNat 64 (256 * j)) :
    WP isa dbatch s fun u =>
      DMem u.mem base (dbatchV t₀) ∧ u.gpr .rbp = BitVec.ofNat 64 (256 * (j - 1)) ∧
      u.zf = some (decide (j - 1 = 0)) ∧ Outside base 512 256 s.mem u.mem ∧
      (∀ r, r ∉ dsClob → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  have hn := hs.nowrap
  rw [dbatch_eq]
  refine WP.seq (WP.mono (dsteps_ok hs hj10 hc) fun s₁ ⟨eD, eU, eV, eQ, eR, O1, b1, g1, r1, w1⟩ => ?_)
  have hs₁ : Scr s₁ base := ⟨(g1 _ (by decide)).trans hs.rdi, w1 ▸ hs.wr, hs.nowrap⟩
  rw [wOf_eq hm] at eD eU eV eQ eR
  rw [WP.block_append_iff]
  refine WP.mono (fRow_ok hs₁ (by decide) (by decide) (by decide)) fun s₂ ⟨f2, O2, g2, r2, w2⟩ => ?_
  have hs₂ : Scr s₂ base := ⟨(g2 _ (by decide)).trans hs₁.rdi, w2 ▸ hs₁.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (fRow_ok hs₂ (by decide) (by decide) (by decide)) fun s₃ ⟨f3, O3, g3, r3, w3⟩ => ?_
  have hs₃ : Scr s₃ base := ⟨(g3 _ (by decide)).trans hs₂.rdi, w3 ▸ hs₂.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (copy4_ok hs₃ (by decide) (by decide)) fun s₄ ⟨f4, O4, g4, r4, w4⟩ => ?_
  have hs₄ : Scr s₄ base := ⟨(g4 _ (by decide)).trans hs₃.rdi, w4 ▸ hs₃.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (aRow_ok hs₄ (by decide) (by decide) (by decide)) fun s₅ ⟨f5, O5, g5, r5, w5⟩ => ?_
  have hs₅ : Scr s₅ base := ⟨(g5 _ (by decide)).trans hs₄.rdi, w5 ▸ hs₄.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (aRow_ok hs₅ (by decide) (by decide) (by decide)) fun s₆ ⟨f6, O6, g6, r6, w6⟩ => ?_
  have hs₆ : Scr s₆ base := ⟨(g6 _ (by decide)).trans hs₅.rdi, w6 ▸ hs₅.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (copy4_ok hs₆ (by decide) (by decide)) fun s₇ ⟨f7, O7, g7, r7, w7⟩ => ?_
  have hs₇ : Scr s₇ base := ⟨(g7 _ (by decide)).trans hs₆.rdi, w7 ▸ hs₆.wr, hs.nowrap⟩
  have nb : Reg.rbp ∉ rowClob := by decide
  have c7 : s₇.gpr .rbp = BitVec.ofNat 64 (256 * j) := by
    rw [g7 _ (by decide), g6 _ nb, g5 _ nb, g4 _ (by decide), g3 _ nb, g2 _ nb, b1]
  refine WP.mono (batchEnd_ok s₇ hj hj10 c7) fun u ⟨cu, zu, ku⟩ =>
    ⟨⟨?_, ?_, ?_, ?_, ?_⟩, cu, zu, ?_, fun r hr => ?_, ?_, ?_⟩
  all_goals try rw [ku.2.1]
  · rw [O7.word (by decide) (by decide), O6.word (by decide) (by decide),
      O5.word (by decide) (by decide), O4.word (by decide) (by decide), O3.word (by decide) (by decide),
      O2.word (by decide) (by decide), eD]
    rfl
  · rw [O7.fe (by decide) (by decide), O6.fe (by decide) (by decide), O5.fe (by decide) (by decide), f4, O3.fe (by decide) (by decide), f2, eU, eV, O1.fe (by decide) (by decide), O1.fe (by decide) (by decide), hm.f, hm.g]
    rfl
  · rw [O7.fe (by decide) (by decide), O6.fe (by decide) (by decide), O5.fe (by decide) (by decide), O4.fe (by decide) (by decide), f3, O2.word (by decide) (by decide), O2.word (by decide) (by decide), eQ, eR, O2.fe (by decide) (by decide), O2.fe (by decide) (by decide),
      O1.fe (by decide) (by decide), O1.fe (by decide) (by decide), hm.f, hm.g]
    rfl
  · rw [f7, O6.fe (by decide) (by decide), f5, O4.word (by decide) (by decide), O4.word (by decide) (by decide), O3.word (by decide) (by decide), O3.word (by decide) (by decide), O2.word (by decide) (by decide), O2.word (by decide) (by decide), eU, eV, O4.fe (by decide) (by decide), O4.fe (by decide) (by decide),
      O3.fe (by decide) (by decide), O3.fe (by decide) (by decide), O2.fe (by decide) (by decide), O2.fe (by decide) (by decide), O1.fe (by decide) (by decide), O1.fe (by decide) (by decide), hm.a, hm.b]
    rfl
  · rw [O7.fe (by decide) (by decide), f6, O5.word (by decide) (by decide), O5.word (by decide) (by decide), O4.word (by decide) (by decide), O4.word (by decide) (by decide), O3.word (by decide) (by decide), O3.word (by decide) (by decide), O2.word (by decide) (by decide), O2.word (by decide) (by decide), eQ, eR,
      O5.fe (by decide) (by decide), O5.fe (by decide) (by decide), O4.fe (by decide) (by decide), O4.fe (by decide) (by decide), O3.fe (by decide) (by decide), O3.fe (by decide) (by decide), O2.fe (by decide) (by decide), O2.fe (by decide) (by decide), O1.fe (by decide) (by decide), O1.fe (by decide) (by decide), hm.a, hm.b]
    rfl
  · exact (O1.wide (by decide) (by decide)).trans <| (O2.wide (by decide) (by decide)).trans <| (O3.wide (by decide) (by decide)).trans <|
      (O4.wide (by decide) (by decide)).trans <| (O5.wide (by decide) (by decide)).trans <| (O6.wide (by decide) (by decide)).trans (O7.wide (by decide) (by decide))
  · have h' : r ≠ .rbp := by intro h; subst h; exact hr (by decide)
    have hr' : r ∉ rowClob := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have h8 : r ∉ [Reg.r8, .r9, .r10, .r11] := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> decide)
    rw [ku.1 r (by simp only [List.mem_singleton]; exact h'), g7 r h8, g6 r hr', g5 r hr', g4 r h8, g3 r hr',
      g2 r hr', g1 r hr]
  · rw [ku.2.2.1, r7, r6, r5, r4, r3, r2, r1]
  · rw [ku.2.2.2, w7, w6, w5, w4, w3, w2, w1]

end VG.Proof.X25519.X86_64
