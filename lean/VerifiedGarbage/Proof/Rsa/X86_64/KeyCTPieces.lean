import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTDefs

/-!
# `vg_rsa_check_key` on x86-64: constant time of the pieces

Each piece of the checks is constant time from `KK` and keeps it: its header
loads by the taint analysis from `rdi`, the rest from the registers they
pin (`hdr_ct`), and `KK` after it from its correctness lemma (`loadK`,
`ltK`, …).
-/

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask)

/-- The base of array `j`. -/
abbrev kb (p : KPub) (j : Nat) : BitVec 64 := off p.B (slot p.w j)

theorem KK.ctx {p : KPub} {t : State} (h : KK p t) :
    ∃ s minv N, KCtx s t p.B p.Z p.w minv N ∧ KS p s := h

/-- What a piece's header loads read, from `KK`. -/
theorem KK.lds {p : KPub} {t : State} (h : KK p t) : t.gpr .rdi = p.B ∧
    (∀ i < 32, InRegions (t.rd ++ t.wr) (off p.B (8 * i)) 8) ∧
    word t.mem p.B (8 * sW) = BitVec.ofNat 64 p.w ∧ (∀ j < 8, word t.mem p.B (8 * sArr j) = kb p j) := by
  obtain ⟨_, _, _, c, _⟩ := h
  exact ⟨c.good.rdi, (show KK p t from ⟨_, _, _, c, ‹_›⟩).hl, c.good.hdr.hw, c.good.hdr.harr⟩

/-! ## Loading a number -/

theorem loadNumK_ct {j sp sl : Nat} (hj : j < 8) (hjN : j ≠ aN) (hj1 : j ≠ aOne) (hsp : sp < 32) (hsl : sl < 32)
    (hsp' : sp ≠ sMask) (hsl' : sl ≠ sMask) (fp : KPub → Addr) (fl : KPub → Nat)
    (hf : ∀ p s, KS p s → word s.mem p.B (8 * sp) = fp p ∧ word s.mem p.B (8 * sl) = BitVec.ofNat 64 (fl p) ∧
      (∃ bs, Src s p.B p.Z (fp p) bs ∧ bs.length = fl p) ∧ 1 ≤ fl p ∧ fl p ≤ 8 * p.w)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hZ : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r8 (.mem (hdr (sArr j))), .mov .r12 (.mem (hdr sW))])
      hc₁).isSome = true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rsi (.mem (hdr sp)), .mov .rcx (.mem (hdr sl)),
      .mov .rbx (.mem (hdr (sArr j)))]) hc₂).isSome = true) :
    RelCT isa (Two KK) (seqs (loadNum j sp sl)) (Two KK) := by
  refine kk_ct ?_ fun p s h => ?_
  · simp only [loadNum, seqs]
    refine RelCT.seq ((zeroArrK_ct hj hjN hj1 hZ).mono (fun _ _ h => h) fun _ _ h => two_mono (fun _ _ h => h.1) h)
      (hdr_ct pins_kk (rs := [.rsi, .rcx, .rbx]) (fun p => [(.rsi, fp p), (.rcx, BitVec.ofNat 64 (fl p)), (.rbx, kb p j)]) (fun _ => rfl) hT
        (by taint_decide) fun p s h => ?_)
    obtain ⟨hdi, hl, -, hb⟩ := h.lds
    obtain ⟨s₀, _, _, c, hs⟩ := h
    obtain ⟨hp, hpl, -⟩ := hf p s₀ hs
    rw [← c.hdr sp hsp hsp'] at hp
    rw [← c.hdr sl hsl hsl'] at hpl
    exact WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = fp p ∧ t.gpr .rcx = BitVec.ofNat 64 (fl p) ∧
        t.gpr .rbx = kb p j)
      (by xrun [State.ea, hdr, hdi, hdrOff, hl sp hsp, hl sl hsl, hl (sArr j) (by unfold sArr; omega), hp, hpl,
        hb j hj]) rfl)
      fun t ⟨⟨a, b, c⟩, _⟩ => regsAre_cons a (regsAre_cons b (regsAre_cons c regsAre_nil))
  · obtain ⟨s₀, minv, N, c, hs⟩ := h
    obtain ⟨hp, hl, ⟨bs, hsrc, hbl⟩, h1, h2⟩ := hf p s₀ hs
    rw [← hbl] at hl h1 h2
    exact WP.mono (loadK c hj hjN hj1 hsp hsl hsp' hsl' hp hl hsrc h1 h2) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩

/-! ## Masks -/

theorem ltMaskK_ct {a b : Nat} (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr a))),
      .mov .r10 (.mem (hdr (sArr b))), .mov32 .rbp (.imm 0)]) hc).isSome = true) :
    RelCT isa (Two KK) (seqs (ltMask a b)) (Two KK) := by
  refine kk_ct ?_ fun p s h => ?_
  · simp only [ltMask, seqs]
    refine hdr_ct pins_kk (rs := [.rdi, .r12, .rbx, .r10]) (fun p => [(.rdi, p.B), (.r12, BitVec.ofNat 64 p.w), (.rbx, kb p a), (.r10, kb p b)])
      (fun _ => rfl) hT (by taint_decide) fun p s h => ?_
    obtain ⟨hdi, hl, hw, hb'⟩ := h.lds
    exact WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
        t.gpr .rbx = kb p a ∧ t.gpr .r10 = kb p b)
      (by xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr a) (by unfold sArr; omega),
        hl (sArr b) (by unfold sArr; omega), hw, hb' a ha, hb' b hb]) rfl)
      fun t ⟨⟨x, y, z⟩, k⟩ => regsAre_cons ((k.gpr (by decide)).trans hdi)
        (regsAre_cons x (regsAre_cons y (regsAre_cons z regsAre_nil)))
  · obtain ⟨s₀, minv, N, c, hs⟩ := h
    exact WP.mono (ltK c ha hb) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩

theorem eqOneK_ct : RelCT isa (Two KK) (seqs eqOne) (Two KK) := by
  refine kk_ct ?_ fun p s h => ?_
  · simp only [eqOne, seqs]
    refine hdr_ct pins_kk (rs := [.rdi, .r12, .rbx, .r10]) (fun p => [(.rdi, p.B), (.r12, BitVec.ofNat 64 p.w), (.rbx, kb p aR), (.r10, kb p aOne)])
      (fun _ => rfl) (by taint_decide) (by taint_decide) fun p s h => ?_
    obtain ⟨hdi, hl, hw, hb'⟩ := h.lds
    exact WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
        t.gpr .rbx = kb p aR ∧ t.gpr .r10 = kb p aOne)
      (by xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr aR) (by decide),
        hl (sArr aOne) (by decide), hw, hb' aR (by decide), hb' aOne (by decide)]) rfl)
      fun t ⟨⟨x, y, z⟩, k⟩ => regsAre_cons ((k.gpr (by decide)).trans hdi)
        (regsAre_cons x (regsAre_cons y (regsAre_cons z regsAre_nil)))
  · obtain ⟨s₀, minv, N, c, hs⟩ := h
    exact WP.mono (eqOneK c) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩

theorem eqCheckK_ct : RelCT isa (Two KK) (seqs VG.Impl.Rsa.X86_64.Crt.eqCheck) (Two KK) := by
  refine kk_ct ?_ fun p s h => ?_
  · simp only [VG.Impl.Rsa.X86_64.Crt.eqCheck, seqs]
    refine hdr_ct pins_kk (rs := [.rdi, .r12, .rbx, .r10]) (fun p => [(.rdi, p.B), (.r12, BitVec.ofNat 64 p.w), (.rbx, kb p aAcc), (.r10, kb p aN)])
      (fun _ => rfl) (by taint_decide) (by taint_decide) fun p s h => ?_
    obtain ⟨hdi, hl, hw, hb'⟩ := h.lds
    exact WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
        t.gpr .rbx = kb p aAcc ∧ t.gpr .r10 = kb p aN)
      (by xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr aAcc) (by decide),
        hl (sArr aN) (by decide), hw, hb' aAcc (by decide), hb' aN (by decide)]) rfl)
      fun t ⟨⟨x, y, z⟩, k⟩ => regsAre_cons ((k.gpr (by decide)).trans hdi)
        (regsAre_cons x (regsAre_cons y (regsAre_cons z regsAre_nil)))
  · obtain ⟨s₀, minv, N, c, hs⟩ := h
    exact WP.mono (eqCheckK c) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩

theorem decMK_ct : RelCT isa (Two KK) (seqs decM) (Two KK) := by
  refine kk_ct ?_ fun p s h => ?_
  · simp only [decM, seqs]
    refine hdr_ct pins_kk (rs := [.r12, .rbx]) (fun p => [(.r12, BitVec.ofNat 64 p.w), (.rbx, kb p aM)])
      (fun _ => rfl) (by taint_decide) (by taint_decide) fun p s h => ?_
    obtain ⟨hdi, hl, hw, hb'⟩ := h.lds
    exact WP.mono (WP.keep [.r12, .rbx, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
        t.gpr .rbx = kb p aM)
      (by xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr aM) (by decide), hw,
        hb' aM (by decide)]) rfl)
      fun t ⟨⟨x, y⟩, _⟩ => regsAre_cons x (regsAre_cons y regsAre_nil)
  · obtain ⟨s₀, minv, N, c, hs⟩ := h
    exact WP.mono (decK c) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩

/-! ## Products -/

theorem mulEK_ct : RelCT isa (Two KK) (seqs mulE) (Two KK) := by
  refine kk_ct ?_ fun p s h => ?_
  · simp only [mulE, seqs]
    refine RelCT.assoc (RelCT.seq (zeroArrK_ct (j := aAcc) (by decide) (by decide) (by decide) (by taint_decide))
      (hdr_ct (Φ := fun p t => KK p t ∧ t.gpr .r12 = BitVec.ofNat 64 p.w)
        (pins_of (fun p _ => p.B) fun _ _ h r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h.1.rdi)
        (rs := [.r12, .r9, .r8]) (fun p => [(.r12, BitVec.ofNat 64 p.w), (.r9, kb p aX), (.r8, kb p aAcc)])
        (fun _ => rfl) (by taint_decide) (by taint_decide) fun p s h => ?_))
    obtain ⟨hdi, hl, -, hb'⟩ := h.1.lds
    have hl' : InRegions (s.rd ++ s.wr) (off p.B (8 * sEv)) 8 := hl sEv (by decide)
    exact WP.mono (WP.keep [.rcx, .r9, .r8] (Q := fun t => t.gpr .r9 = kb p aX ∧ t.gpr .r8 = kb p aAcc)
      (by xrun [State.ea, hdr, hdi, hdrOff, hl', hl (sArr aX) (by decide), hl (sArr aAcc) (by decide),
        hb' aX (by decide), hb' aAcc (by decide)]) rfl)
      fun t ⟨⟨x, y⟩, k⟩ => regsAre_cons ((k.gpr (by decide)).trans h.2) (regsAre_cons x (regsAre_cons y regsAre_nil))
  · obtain ⟨s₀, minv, N, c, hs⟩ := h
    exact WP.mono (mulEK c) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩

theorem zeroAccsK_ok {p : KPub} {s : State} (h : KK p s) : WP isa (seqs VG.Impl.Rsa.X86_64.Crt.zeroAccs) s (KK p) := by
  obtain ⟨s₀, minv, N, c, hs⟩ := h
  have hn := c.good.scr.nowrap
  have := c.w2
  have sl := slot_eq p.w
  refine WP.mono (zeroAccs_ok c.good c.hZ (by omega)) fun t ⟨_, ho, k⟩ => ⟨s₀, minv, N, c.arr (js := [aAcc, aTmp])
    (fun x hx => ho x (by
      have h1 := hx aAcc (by simp); have h2 := hx aTmp (by simp)
      rw [sl] at h1 h2; simp only [aAcc, aTmp] at h1 h2; rw [sl]; simp only [aAcc]; omega))
    (by decide) (by decide) (by decide) k, hs⟩

theorem mulXRK_ct : RelCT isa (Two KK) (seqs mulXR) (Two KK) := by
  refine kk_ct ?_ fun p s h => ?_
  · unfold mulXR
    refine RelCT.seqs_append (by simp [VG.Impl.Rsa.X86_64.Crt.zeroAccs]) (by simp)
      (RelCT.seq (two_post (two_map (fun p : KPub => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun _ _ h => h.goodW) zeroAccs_ct)
        fun _ _ h => zeroAccsK_ok h) ?_)
    simp only [seqs]
    refine hdr_ct pins_kk (rs := [.r11, .r10, .r9, .r12, .r8]) (fun p => [(.r11, kb p aX), (.r10, BitVec.ofNat 64 p.w), (.r9, kb p aR),
      (.r12, BitVec.ofNat 64 p.w), (.r8, kb p aAcc)]) (fun _ => rfl) (by taint_decide) (by taint_decide) fun p s h => ?_
    obtain ⟨hdi, hl, hw, hb'⟩ := h.lds
    exact WP.mono (WP.keep [.r11, .r10, .r9, .r12, .r8] (Q := fun t => t.gpr .r11 = kb p aX ∧
        t.gpr .r10 = BitVec.ofNat 64 p.w ∧ t.gpr .r9 = kb p aR ∧ t.gpr .r12 = BitVec.ofNat 64 p.w ∧
        t.gpr .r8 = kb p aAcc)
      (by xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr aX) (by decide), hl (sArr aR) (by decide),
        hl (sArr aAcc) (by decide), hw, hb' aX (by decide), hb' aR (by decide), hb' aAcc (by decide)]) rfl)
      fun t ⟨⟨a, b, c, d, e⟩, _⟩ => regsAre_cons a (regsAre_cons b (regsAre_cons c (regsAre_cons d
        (regsAre_cons e regsAre_nil))))
  · obtain ⟨s₀, minv, N, c, hs⟩ := h
    exact WP.mono (mulXRK c) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩

/-! ## Remainders -/

theorem reduceK_ct {cnt : List Instr} (cn : Nat → Nat)
    (hcnt : ∀ (t : State) (w : Nat), t.gpr .r13 = BitVec.ofNat 64 w →
      WP isa (.block cnt) t fun t' => t'.gpr .r13 = BitVec.ofNat 64 (cn w) ∧ t'.mem = t.mem ∧ Keep [.r13] t t')
    (hok : ∀ p s, KK p s → WP isa (seqs (reduce cnt)) s (KK p))
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (([.mov .rbx (.mem (hdr (sArr aR))),
      .mov .r10 (.mem (hdr (sArr aM))), .mov .r8 (.mem (hdr (sArr aX))), .mov .r12 (.mem (hdr sW)),
      .mov .rsi (.mem (hdr (sArr aT))), .mov .r9 (.mem (hdr (sArr aAcc))), .mov .r13 (.reg .r12)] : List Instr) ++
      cnt)) hc₁).isSome = true)
    (hB : (taint.check (Taint.ofRegs [.rbx, .r10, .r8, .r12, .rsi, .r9, .r13]) (.loop wordStep .ne) hc₂).isSome = true) :
    RelCT isa (Two KK) (seqs (reduce cnt)) (Two KK) := by
  refine kk_ct ?_ hok
  simp only [reduce, seqs]
  refine RelCT.seq ((zeroArrK_ct (j := aR) (by decide) (by decide) (by decide) (by taint_decide)).mono
    (fun _ _ h => h) fun _ _ h => two_mono (fun _ _ h => h.1) h)
    (hdr_ct pins_kk (rs := [.rbx, .r10, .r8, .r12, .rsi, .r9, .r13]) (fun p => [(.rbx, kb p aR), (.r10, kb p aM), (.r8, kb p aX), (.r12, BitVec.ofNat 64 p.w),
      (.rsi, kb p aT), (.r9, kb p aAcc), (.r13, BitVec.ofNat 64 (cn p.w))]) (fun _ => rfl) hT hB fun p s h => ?_)
  obtain ⟨hdi, hl, hw, hb'⟩ := h.lds
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rbx, .r10, .r8, .r12, .rsi, .r9, .r13] (Q := fun t => t.gpr .rbx = kb p aR ∧
      t.gpr .r10 = kb p aM ∧ t.gpr .r8 = kb p aX ∧ t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.gpr .rsi = kb p aT ∧
      t.gpr .r9 = kb p aAcc ∧ t.gpr .r13 = BitVec.ofNat 64 p.w)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr aR) (by decide), hl (sArr aM) (by decide),
      hl (sArr aX) (by decide), hl (sArr aT) (by decide), hl (sArr aAcc) (by decide), hw, hb' aR (by decide),
      hb' aM (by decide), hb' aX (by decide), hb' aT (by decide), hb' aAcc (by decide)]) rfl)
    fun t ⟨⟨a, b, c, d, e, f, g⟩, _⟩ => ?_
  refine WP.mono (hcnt t p.w g) fun t' ⟨g', _, k⟩ => ?_
  exact regsAre_cons ((k.gpr (by decide)).trans a) (regsAre_cons ((k.gpr (by decide)).trans b)
    (regsAre_cons ((k.gpr (by decide)).trans c) (regsAre_cons ((k.gpr (by decide)).trans d)
    (regsAre_cons ((k.gpr (by decide)).trans e) (regsAre_cons ((k.gpr (by decide)).trans f)
    (regsAre_cons g' regsAre_nil))))))

theorem reduceEK_ct : RelCT isa (Two KK) (seqs (reduce cntE)) (Two KK) :=
  reduceK_ct (· + 2) (fun t _ h => cntE_ok t h)
    (fun _ _ h => let ⟨s₀, minv, N, c, hs⟩ := h; WP.mono (reduceEK c) fun _ ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩)
    (by taint_decide) (by taint_decide)

theorem reduceXRK_ct : RelCT isa (Two KK) (seqs (reduce cntXR)) (Two KK) :=
  reduceK_ct (fun w => 2 * w + 2) (fun t _ h => cntXR_ok t h)
    (fun _ _ h => let ⟨s₀, minv, N, c, hs⟩ := h; WP.mono (reduceXRK c) fun _ ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩)
    (by taint_decide) (by taint_decide)

end VG.Proof.Rsa.X86_64.Key
