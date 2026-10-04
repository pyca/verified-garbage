import VerifiedGarbage.Proof.Ecdsa.X86.Scalar

/-!
# ECDSA on x86 (32-bit): the result

`finish` reads `out` from its argument, writes `r ‖ s` big-endian to it, or
zeros, by the flag's mask, returns the flag's low bit and restores `ebx`,
`esi`, `ebp` and `edi` (`finish_ok`). The stores are outside the working
space, so it keeps its numbers and the saved registers
(`Outside.unch_far`).
-/

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- The bytes of a range apart from the one that changed. -/
theorem bytesAt_keep {q p : Addr} {len k : Nat} {m m' : Mem} (h : Outside q 0 len m m')
    (hd : Region.Disjoint ⟨p, k⟩ ⟨q, len⟩) (hl : len ≤ 2 ^ 64) (hk : k ≤ 2 ^ 64) :
    Spec.Ecdsa.bytesAt m' p k = Spec.Ecdsa.bytesAt m p k := by
  simp only [Spec.Ecdsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact keep_of_disjoint' h hd hl hi hk

/-- A range changed at `p + d` is one changed at offset `d` of `p`. -/
theorem _root_.VG.Proof.Mont.Outside.shift {p : Addr} {d len : Nat} {m m' : Mem}
    (h : Outside (p + BitVec.ofNat 64 d) 0 len m m') (hd : d + len ≤ 2 ^ 64) : Outside p d len m m' :=
  fun x hx => h x (Or.inr (by
    show 0 + len ≤ (x - (p + BitVec.ofNat 64 d)).toNat
    rcases Nat.lt_or_ge (x - (p + BitVec.ofNat 64 d)).toNat len with hlt | hge
    · have := (Offset.lt_iff x p hd).mp hlt
      simp only [ofs] at hx
      omega
    · omega))

theorem mask_bit (b : Bool) : (mask32 (b = true) &&& 1 : BitVec 32) = if b then 1 else 0 := by
  cases b <;> decide

theorem saved_lt : ∀ p ∈ Cfg.saved, p.2 + 4 ≤ 16 := by decide

theorem finish_eq (c : Cfg) : c.finish = .mov .ecx (.mem (sc (c.sl FLAG))) :: .mov .ebx (.mem (Cfg.argOp 0)) ::
    (storeBE c.n .ebx 0 (c.sl RR) ++ (storeBE c.n .ebx (8 * c.n) (c.sl SS) ++
    (([.mov .eax (.reg .ecx), .alu .and .eax (.imm 1)] : List Instr) ++ Cfg.restore))) := by
  simp only [Cfg.finish, List.append_assoc, List.cons_append, List.nil_append]

/-- `r = [edx + d]`, with `edx = edi`. -/
theorem restoreLd {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hx : s.gpr .edx = s.gpr .edi) {d : Nat} (hd : d + 4 ≤ size) :
    readSrc s (.mem (at_ .edx d)) = some (s.mem.readW (off base d) 32) := by
  show s.load32 _ = _
  rw [hs.ea_reg (k := 0) (by rw [hx, BitVec.add_zero]) (by omega), Nat.zero_add, State.load32,
    ite_eq_left_iff.mpr fun h => absurd (hs.read hd) h]

/-- The flag's low bit (the mask in `ecx`) to `eax`, and the callee-saved
registers restored from the working space. -/
theorem tail_ok {base : Addr} {s : State} (hs : Scr s base size) {g : Reg → BitVec 32}
    (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hc : s.gpr .ecx = mask32 (b = true)) :
    WP isa (.block (([.mov .eax (.reg .ecx), .alu .and .eax (.imm 1)] : List Instr) ++ Cfg.restore)) s
      fun s' => s'.mem = s.mem ∧ s'.gpr .eax = (if b then 1 else 0) ∧
        (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = g rd.1) ∧
        (∀ r, r ∉ [.eax, .ebx, .edx, .esi, .edi, .ebp] → s'.gpr r = s.gpr r) := by
  have hsz : size = 8192 := rfl
  refine wp_movS rfl fun s₅ u₅ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₆ u₆ => ?_
  have k₆ : Keeps [.eax] s s₆ := u₅.keeps.trans u₆.keeps
  have hs₆ := hs.of_keeps k₆ (by decide)
  have eax₆ : s₆.gpr .eax = if b then 1 else 0 := by
    rw [u₆.gpr, u₅.gpr, hc]
    simp only [ite_true]
    exact mask_bit b
  have hm₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem]
  simp only [Cfg.restore]
  refine wp_movS rfl fun s₇ u₇ _ => ?_
  have hs₇ := hs₆.of_keeps u₇.keeps (by decide)
  have hx₇ : s₇.gpr .edx = s₇.gpr .edi := by rw [u₇.gpr, u₇.other _ (by decide)]
  refine wp_movS (restoreLd hs₇ hx₇ (d := 0) (by omega)) fun s₈ u₈ _ => ?_
  have hs₈ := hs₇.of_keeps u₈.keeps (by decide)
  have hx₈ : s₈.gpr .edx = s₈.gpr .edi := by rw [u₈.other _ (by decide), u₈.other _ (by decide), hx₇]
  refine wp_movS (restoreLd hs₈ hx₈ (d := 4) (by omega)) fun s₉ u₉ _ => ?_
  have hs₉ := hs₈.of_keeps u₉.keeps (by decide)
  have hx₉ : s₉.gpr .edx = s₉.gpr .edi := by rw [u₉.other _ (by decide), u₉.other _ (by decide), hx₈]
  refine wp_movS (restoreLd hs₉ hx₉ (d := 12) (by omega)) fun s₁₀ u₁₀ _ => ?_
  have hs₁₀ := hs₉.of_keeps u₁₀.keeps (by decide)
  have hx₁₀ : s₁₀.gpr .edx = s₁₀.gpr .edi := by
    rw [u₁₀.other _ (by decide), u₁₀.other _ (by decide), hx₉]
  refine wp_movS (restoreLd hs₁₀ hx₁₀ (d := 8) (by omega)) fun s₁₁ u₁₁ _ => WP.block_nil ?_
  have hm₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, hm₆]
  refine ⟨by rw [u₁₁.mem, hm₁₀], ?_, fun rd hrd => ?_, fun r hr => ?_⟩
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), eax₆]
  · have hsv' := fun rd (h : rd ∈ Cfg.saved) => (congrArg (fun m => Mem.readW m (off base rd.2) 32) hm₁₀).trans
      (hsv rd h)
    simp only [Cfg.saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.mem]
      exact (congrArg (fun m => Mem.readW m _ 32) (show s₆.mem = s₁₀.mem by rw [hm₁₀, hm₆])).trans
        (hsv' (.ebx, 0) (by simp [Cfg.saved]))
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.mem, u₇.mem]
      exact (congrArg (fun m => Mem.readW m _ 32) (show s₆.mem = s₁₀.mem by rw [hm₁₀, hm₆])).trans
        (hsv' (.esi, 4) (by simp [Cfg.saved]))
    · rw [u₁₁.gpr, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
      exact (congrArg (fun m => Mem.readW m _ 32) (show s₆.mem = s₁₀.mem by rw [hm₁₀, hm₆])).trans
        (hsv' (.edi, 8) (by simp [Cfg.saved]))
    · rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.mem, u₈.mem, u₇.mem]
      exact (congrArg (fun m => Mem.readW m _ 32) (show s₆.mem = s₁₀.mem by rw [hm₁₀, hm₆])).trans
        (hsv' (.ebp, 12) (by simp [Cfg.saved]))
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [u₁₁.other _ h5, u₁₀.other _ h6, u₉.other _ h4, u₈.other _ h2, u₇.other _ h3, k₆.1 _ (by simp [h1])]

/-- The result, the return value and the callee-saved registers. -/
theorem finish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {o32 : BitVec 32}
    (hout : readSrc s (.mem (Cfg.argOp 0)) = some o32) (hofit : o32.toNat + 16 * c.n ≤ 2 ^ 32)
    (hw : (⟨o32.setWidth 64, 16 * c.n⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨o32.setWidth 64, 16 * c.n⟩ ⟨base, size⟩)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hf : flagW c base s = mask32 (b = true)) :
    WP isa (.block c.finish) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (o32.setWidth 64) (16 * c.n) =
        (if b then toBytes (8 * c.n) (sv c base s RR) ++ toBytes (8 * c.n) (sv c base s SS)
          else List.replicate (16 * c.n) 0) ∧
      s'.gpr .eax = (if b then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] → s'.gpr r = s.gpr r) ∧
      Outside (o32.setWidth 64) 0 (16 * c.n) s.mem s'.mem := by
  have h7 := hc.n7
  have hn0 := hc.n0
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hRR := sl_le c h7 (i := RR) (by decide)
  have hSS := sl_le c h7 (i := SS) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  generalize hout64 : o32.setWidth 64 = out at hw hd ⊢
  have h0 : ∀ e, out + BitVec.ofNat 64 0 + BitVec.ofNat 64 e = out + BitVec.ofNat 64 e := fun e =>
    congrArg (· + BitVec.ofNat 64 e) (BitVec.add_zero out)
  have h8 : ∀ e, out + BitVec.ofNat 64 (8 * c.n) + BitVec.ofNat 64 e =
      out + BitVec.ofNat 64 (8 * c.n + e) := fun e => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hdsc : ∀ {a d : Nat}, a + 8 * c.n ≤ size → d + 8 * c.n ≤ 16 * c.n →
      Region.Disjoint ⟨off base a, 8 * c.n⟩ ⟨out + BitVec.ofNat 64 d, 8 * c.n⟩ := fun ha hd' =>
    (hd.symm.sub_left (Offset.sub_base base ha)).sub_right (Offset.sub_base out hd')
  have hscd : ∀ {d : Nat}, d + 8 * c.n ≤ 16 * c.n →
      Region.Disjoint ⟨base, size⟩ ⟨out + BitVec.ofNat 64 d, 8 * c.n⟩ := fun hd' =>
    hd.symm.sub_right (Offset.sub_base out hd')
  rw [finish_eq]
  refine wp_movS (readSrc_sc hs (d := c.sl FLAG) (by omega)) fun s₁ u₁ _ => ?_
  refine wp_movS (show readSrc s₁ (.mem (Cfg.argOp 0)) = some o32 by
    have hea : s₁.ea (Cfg.argOp 0) = s.ea (Cfg.argOp 0) := by
      show addr (s₁.gpr .esp) _ = addr (s.gpr .esp) _
      rw [u₁.other _ (by decide)]
    rw [← hout]; show s₁.load32 _ = s.load32 _
    rw [State.load32, State.load32, hea, u₁.rd, u₁.wr, u₁.mem]) fun s₂ u₂ _ => ?_
  have k₂ : Keeps [.ebx, .ecx] s s₂ := (u₁.keeps.mono (by decide)).widen u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  have hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have hc₂ : s₂.gpr .ecx = mask32 (b = true) := by
    rw [u₂.other _ (by decide), u₁.gpr, ← flagW, hf]
  refine WP.block_append (WP.mono (storeBE_ok hs₂ (dst := .ebx) (d := 0) (a := c.sl RR) (by decide) b
    hc₂ hRR (by rw [u₂.gpr]; omega) (fun e he => ⟨_, by rw [k₂.2.2]; exact hw, by
      rw [u₂.gpr, hout64, h0]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [u₂.gpr, hout64]; exact hdsc hRR (by omega))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  rw [u₂.gpr, hout64] at e₃ O₃
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have U₃ := O₃.unch_far (hscd (d := 0) (by omega))
  have hebx₃ : s₃.gpr .ebx = o32 := by rw [k₃.1 _ (by decide), u₂.gpr]
  have hc₃ : s₃.gpr .ecx = mask32 (b = true) := by rw [k₃.1 _ (by decide), hc₂]
  have ss₃ : wordsVal s₃.mem base (c.sl SS) c.n = sv c base s SS := by
    rw [U₃.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hm₂]
  refine WP.block_append (WP.mono (storeBE_ok hs₃ (dst := .ebx) (d := 8 * c.n) (a := c.sl SS) (by decide) b
    hc₃ hSS (by rw [hebx₃]; omega) (fun e he => ⟨_, by rw [k₃.2.2, k₂.2.2]; exact hw, by
      rw [hebx₃, hout64, h8]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hebx₃, hout64]; exact hdsc hSS (by omega))) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_)
  rw [hebx₃, hout64] at e₄ O₄
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have U₄ := O₄.unch_far (hscd (d := 8 * c.n) (by omega))
  have first : Spec.Ecdsa.bytesAt s₄.mem out (8 * c.n) =
      if b then toBytes (8 * c.n) (sv c base s RR) else List.replicate (8 * c.n) 0 := by
    rw [bytesAt_keep O₄ (Offset.base_disjoint out (Nat.le_refl _) (by omega)) (by omega) (by omega)]
    have e₃' := e₃
    rw [(BitVec.add_zero out : out + BitVec.ofNat 64 0 = out)] at e₃'
    rw [e₃', hm₂]
  have hsv₄ : ∀ rd ∈ Cfg.saved, s₄.mem.readW (off base rd.2) 32 = g rd.1 := by
    intro rd hrd
    have := saved_lt rd hrd
    have h16 : ∀ w ∈ [(size, 2 ^ 64)], rd.2 + 4 ≤ w.1 ∨ w.1 + w.2 ≤ rd.2 := fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; exact .inl (by omega)
    rw [Unch.readW32 U₄ h16 (by omega), Unch.readW32 U₃ h16 (by omega), hm₂, hsv rd hrd]
  refine WP.mono (tail_ok hs₄ hsv₄ b (by rw [k₄.1 _ (by decide), hc₃]))
    fun s' ⟨hm', eax', saved', others'⟩ => ⟨?_, eax', saved', fun r hr => ?_, ?_⟩
  · rw [hm', show 16 * c.n = 8 * c.n + 8 * c.n by omega, bytesAt_add, first, e₄, ss₃]
    cases b
    · simp only [Bool.false_eq_true, ite_false, List.replicate_append_replicate]
    · simp only [ite_true]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7'⟩ := hr
    rw [others' _ (by simp [h1, h2, h4, h5, h6, h7']), k₄.1 _ (by simp [h1]),
      k₃.1 _ (by simp [h1]), k₂.1 _ (by simp [h2, h3])]
  · rw [hm', ← hm₂]
    exact ((O₃.shift (by omega)).mono (Nat.zero_le _) (by omega)).trans
      ((O₄.shift (by omega)).mono (Nat.zero_le _) (by omega))

end VG.Proof.Ecdsa.X86
