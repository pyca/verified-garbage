import VerifiedGarbage.Proof.Rsa.X86_64.RpCT6

/-!
# `vg_rsa_recover_primes` on x86-64: constant time, the factors

`y - 1`, `p = gcd(y - 1, n)`, `q = n / p`, the larger first, and the
masked stores (`fin_ct`): every loop counts a public number of words, and
the stores' pointers and lengths are pinned by correctness.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)

namespace Rp

/-- Between the pieces of `fin`: the inputs, the mask, and `X`. -/
def FX (X : RpIn → State → Prop) (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem) (c : Bool), I.pub = p ∧ RpS I m₀ s ∧ RpLens I ∧ RpOuts I ∧
    word s.mem I.B (8 * sMask) = mask c ∧ X I s

theorem FX.ws {X : RpIn → State → Prop} {p : RpP} {s : State} (h : FX X p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨I, m₀, c, rfl, S, -⟩ := h
  exact S.ws

/-- `FX` after a piece that changes only arrays and slots of `rSlot` other
than `sMask`. -/
theorem FX.step {X Y : RpIn → State → Prop} {p : RpP} {s t : State} (h : FX X p s) {js hs : List Nat}
    (hf : Frm p.B (rg (wk p.k) js hs) s.mem t.mem) (hjs : ∀ j ∈ js, j < 16) (hhs : ∀ i ∈ hs, rSlot i = true)
    (hm : sMask ∉ hs) {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs)
    (hX : ∀ I : RpIn, I.pub = p → X I s → Y I t) : FX Y p t := by
  obtain ⟨I, m₀, c, e, S, L, O, hmk, hx⟩ := h
  subst e
  dsimp only [RpIn.pub] at hf
  exact ⟨I, m₀, c, rfl, S.step hf hjs hhs k hr, L, O, by rw [hf.rg_word (by decide) hm]; exact hmk, hX I rfl hx⟩

theorem pins_FM {X : RpIn → State → Prop} : Pins (FX X) [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]

theorem zeroA_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {j : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc).isSome = true)
    (hw : ∀ x s, Φ x s → WP isa (zeroA j) s (Ψ x)) : RelCT isa (Two Φ) (zeroA j) (Two Ψ) :=
  ws_ct B Z w hws ht hw

/-! ## `y - 1` -/

/-- With the constants. -/
def XC (I : RpIn) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (r t : Nat), Cst s I.B I.Z (wk I.k) minv I.N I.el r t

/-- `u` zero. -/
def XU (I : RpIn) (s : State) : Prop := wv s.mem I.B (slot (wk I.k) fU) (wk I.k + 2) = 0

/-- `u`'s top word zero. -/
def XT (I : RpIn) (s : State) : Prop := word s.mem I.B (slot (wk I.k) fU + 8 * wk I.k) = 0

theorem finA_ct (M : Mont) : RelCT isa (Two GR3) (seqs [.block [.mov .rax (.mem (hdr sC3)), .store (hdr sMask) .rax],
    M.mm aY aY aOne, zeroA fU, .block (ws ++ base aY .r8 ++ base aOne .r10 ++ base fU .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr)),
    wordLoop 0 subBody]) (Two (FX XT)) := by
  simp only [seqs]
  refine RelCT.seq (R := Two (FX XC)) (blk_gct RpP.B RpP.Z (fun p => wk p.k)
    (fun _ _ ⟨_, _, _, _, _, e, S, _⟩ => e ▸ S.ws) (by taint_decide) fun p s h => ?_) ?_
  · obtain ⟨I, m₀, minv, res, cnt, rfl, S, L, O, hv, hc, hgo, hc3, hy⟩ := h
    dsimp only [RpIn.pub]
    have h256 := hc.ws.h256
    refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = s.mem.writeW (off I.B (8 * sMask))
        (mask res.isSome)) (by
      xrun [State.ea, hdr, hc.ws.rdi, hdrOff, hc.ws.scr.ld (d := 8 * sC3) (by simp only [sC3, sFn]; omega),
        hc.ws.scr.st (d := 8 * sMask) (by simp only [sMask, sFn]; omega), hc3]) rfl) fun u ⟨m₁, k₁⟩ => ?_
    have hf₁ : Frm I.B (rg (wk I.k) [] [sMask]) s.mem u.mem := by
      rw [m₁]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sMask, sFn]; omega)) _ _
        (List.mem_singleton_self _)
    exact ⟨I, m₀, res.isSome, rfl, S.step hf₁ (by decide) (by decide) k₁ (by decide), L, O,
      by rw [m₁, word_writeW_self], minv, _, _, hc.congr hf₁ (by decide) (by decide) k₁ (by decide)⟩
  refine RelCT.seq (R := Two (FX fun _ _ => True)) (mm_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) M
    (o := aY) (a := aY) (b := aOne) (by unfold MmUse; decide) fun p s h => ?_) ?_
  · have h' := h
    obtain ⟨I, m₀, c, rfl, S, L, O, hmk, minv, r, t, hc⟩ := h'
    have hg := hc.good
    have hw2 := hc.ws.w2
    exact WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega) (o := aY) (a := aY) (b := aOne) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
      (by rw [hc.hone, hc.hn]; have := hc.n1; omega)) fun u ⟨_, _, _, ha, k⟩ =>
      h.step (Frm.rg_of_arrays ha [aAcc, aTmp, aY] [] (by decide)) (by decide) (by simp) (by simp) k (by decide)
        fun _ _ _ => trivial
  refine RelCT.seq (R := Two (FX XU)) (zeroA_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws)
    (by taint_decide) fun p s h => WP.mono (zeroA_ok h.ws (j := fU) (by decide)) fun u ⟨z, o, k⟩ =>
      h.step (Frm.rg_of_out o (Nat.le_refl _) [fU] [] (by decide)) (by decide) (by simp) (by simp) k (by decide)
        fun I e _ => by subst e; exact z) ?_
  have e : (.seq (.block (ws ++ base aY .r8 ++ base aOne .r10 ++ base fU .rsi ++ [.mov32 .rbp (.imm 0)]))
      (wordLoop 0 subBody) : Prog isa) = .seq (.block (ws ++ (base aY .r8 ++ (base aOne .r10 ++
        (base fU .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr)))))) (wordLoop 0 subBody) := by
    simp only [List.append_assoc]
  rw [e]
  refine ws_ct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide) fun p s h => ?_
  rw [← e]
  have hw := h.ws
  have hn0 := hw.scr.nowrap
  have hZ := hw.hZ
  have hw1 := hw.w1
  have hw2 := hw.w2
  refine WP.seq (WP.mono (subSet_ok hw aY aOne fU) fun t ⟨h12, h8, h10, hsi, hbp, m₄, k₄⟩ => ?_)
  have sY := hw.sl (j := aY) (by decide)
  have sO := hw.sl (j := aOne) (by decide)
  have sU := hw.sl (j := fU) (by decide)
  refine WP.mono (sub_ok (hw.scr.congr k₄.2.2) h8 h10 hsi h12 hbp (by omega) (by omega) (by omega) (by omega)
    (by omega) (by have := slot_far (w := wk p.k) (show fU ≠ aY by decide); omega)
    (by have := slot_far (w := wk p.k) (show fU ≠ aOne by decide); omega)) fun u ⟨_, _, _, o₅, k₅⟩ => ?_
  rw [m₄] at o₅
  have hf : Frm p.B (rg (wk p.k) [fU] []) s.mem u.mem := Frm.rg_of_out o₅ (by omega) _ _ (by decide)
  refine h.step hf (by decide) (by simp) (by simp) (k₄.trans k₅) (by decide) fun I e z => ?_
  subst e
  dsimp only [RpIn.pub] at *
  show word u.mem I.B (slot (wk I.k) fU + 8 * wk I.k) = 0
  rw [o₅.word (Or.inr (by omega)) (by omega)]
  exact word_above_zero (n := wk I.k) (L := wk I.k + 2) (by omega) (by rw [z]; exact Nat.two_pow_pos _)

/-! ## `p = gcd(u, n)` and `q = n / p` -/

/-- `v = n`. -/
def XV (I : RpIn) (s : State) : Prop :=
  XT I s ∧ wv s.mem I.B (slot (wk I.k) fV) (wk I.k) = wv s.mem I.B (slot (wk I.k) aN) (wk I.k)

/-- `x₁ = 0` (`o`) or `x₁ = 1`, and `x₂ = 0` if `z`. -/
def XW (o z : Bool) (I : RpIn) (s : State) : Prop :=
  XV I s ∧ (o = false → wv s.mem I.B (slot (wk I.k) fX₁) (wk I.k + 2) = 0) ∧
    (o = true → wv s.mem I.B (slot (wk I.k) fX₁) (wk I.k) = 1) ∧
    (z = true → wv s.mem I.B (slot (wk I.k) fX₂) (wk I.k + 2) = 0)

/-- The facts after a piece that writes only array `j`. -/
theorem xv_keep {I : RpIn} {s t : State} (hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64) {js : List Nat}
    (hf : Frm I.B (rg (wk I.k) js []) s.mem t.mem) (hU : fU ∉ js) (hV : fV ∉ js) (hN : aN ∉ js)
    (h : XV I s) : XV I t := by
  obtain ⟨ht, hv⟩ := h
  refine ⟨?_, ?_⟩
  · show word t.mem I.B (slot (wk I.k) fU + 8 * wk I.k) = 0
    rw [hf.rg_wordA hZ16 (by simp) (by decide) hU (by omega)]; exact ht
  · rw [hf.rg_wv hZ16 (by simp) (by decide) hV (by omega), hf.rg_wv hZ16 (by simp) (by decide) hN (by omega)]
    exact hv

theorem inverse_gct {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (([.mov .r11 (.reg .r12)] : List Instr) ++
      (List.replicate 7 (.alu .add .r11 (.reg .r11)) ++ ([.mov32 .r13 (.imm 0)] : List Instr))))
      (.loop (VG.Impl.Rsa.X86_64.Keys.invStep fU fV fX₁ fX₂ aN fT) .ne)) hc).isSome = true) :
    RelCT isa (Two (FX (XW true true))) (inverse fU fV fX₁ fX₂ aN fT) (Two (FX fun _ _ => True)) := by
  have e : inverse fU fV fX₁ fX₂ aN fT = .seq (.block (ws ++ ([.mov .r11 (.reg .r12)] ++
      (List.replicate 7 (.alu .add .r11 (.reg .r11)) ++ [.mov32 .r13 (.imm 0)]))))
      (.loop (VG.Impl.Rsa.X86_64.Keys.invStep fU fV fX₁ fX₂ aN fT) .ne) := by
    simp only [inverse, invInit, List.append_assoc]
  rw [e]
  refine ws_ct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun p s h => ?_
  rw [← e]
  have hw := h.ws
  have hZ16 : slot (wk p.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
  have h' := h
  obtain ⟨I, m₀, c, e, S, L, O, hmk, ⟨u0, vm⟩, -, x1, x2⟩ := h'
  subst e
  dsimp only [RpIn.pub] at hw hZ16
  have hw1 := hw.w1
  have hw2 := hw.w2
  have vX₂ : wv s.mem I.B (slot (wk I.k) fX₂) (wk I.k) = 0 := by
    have := wv_add s.mem I.B (slot (wk I.k) fX₂) (wk I.k) 2; have := x2 rfl; omega
  refine WP.mono (inverse_ok hw.scr hw.rdi hw.hw hw.hS (by omega) hw2 hw.hZ
    (iU := fU) (iV := fV) (iX₁ := fX₁) (iX₂ := fX₂) (iM := aN) (iT := fT) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    u0 vm (x1 rfl) vX₂) fun u ⟨_, f', k, _⟩ => ?_
  have f : Frm I.B (rg (wk I.k) [fU, fV, fX₁, fX₂, fT] [sMo]) s.mem u.mem := f'.widen (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (by omega)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (Nat.le_refl _)
    · exact rg_cover_hdr _ (by decide))
  exact h.step f (by decide) (by decide) (by decide) k (by decide) fun _ _ _ => trivial

theorem divmod_gct {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base fR .r8 ++ (([.mov .r11 (.reg .r12)] : List Instr) ++
      (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++ ([.mov32 .r13 (.imm 0)] : List Instr)))))
      (.seq zeroAccLoop (.loop (VG.Impl.Rsa.X86_64.Keys.divStep fQ fR fV fT) .ne))) hc).isSome = true) :
    RelCT isa (Two (FX fun _ _ => True)) (divmod fQ fR fV fT) (Two (FX fun _ _ => True)) := by
  have e : divmod fQ fR fV fT = .seq (.block (ws ++ (base fR .r8 ++ ([.mov .r11 (.reg .r12)] ++
      (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++ [.mov32 .r13 (.imm 0)])))))
      (.seq zeroAccLoop (.loop (VG.Impl.Rsa.X86_64.Keys.divStep fQ fR fV fT) .ne)) := by
    simp only [divmod, divInit, seqs, List.append_assoc]
  rw [e]
  refine ws_ct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun p s h => ?_
  rw [← e]
  have hw := h.ws
  refine WP.mono (divmod_ok hw.scr hw.rdi hw.hw hw.hS (by have := hw.w1; omega) hw.w2 hw.hZ (iQ := fQ) (iR := fR)
    (iD := fV) (iT := fT) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun u ⟨_, f', k, _⟩ => ?_
  have f : Frm p.B (rg (wk p.k) [fQ, fR, fT] []) s.mem u.mem := f'.widen (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (Nat.le_refl _)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (Nat.le_refl _)
    · exact rg_cover_arr _ (by decide) (Nat.le_refl _) (Nat.le_refl _))
  exact h.step f (by decide) (by simp) (by simp) k (by decide) fun _ _ _ => trivial

theorem finB_ct : RelCT isa (Two (FX XT)) (seqs [zeroA fV, copyA fV aN, zeroA fX₁, .block (setOneA fX₁),
    zeroA fX₂, inverse fU fV fX₁ fX₂ aN fT, zeroA fQ, copyA fQ aN, divmod fQ fR fV fT])
    (Two (FX fun _ _ => True)) := by
  have hB : ∀ (X : RpIn → State → Prop) p s, FX X p s → Ws s p.B p.Z (wk p.k) := fun _ _ _ h => h.ws
  simp only [seqs]
  -- `v = n`.
  refine RelCT.seq (R := Two (FX XT)) (zeroA_gct RpP.B RpP.Z (fun p => wk p.k) (hB _) (by taint_decide)
    fun p s h => WP.mono (zeroA_ok h.ws (j := fV) (by decide)) fun u ⟨_, o, k⟩ =>
      h.step (Frm.rg_of_out o (Nat.le_refl _) [fV] [] (by decide)) (by decide) (by simp) (by simp) k (by decide)
        fun I e ht => by
          subst e
          have hw := h.ws
          dsimp only [RpIn.pub] at o hw
          have hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
          show word u.mem I.B (slot (wk I.k) fU + 8 * wk I.k) = 0
          rw [(Frm.rg_of_out o (Nat.le_refl _) [fV] [] (by decide)).rg_wordA hZ16 (by simp) (by decide) (by decide)
            (by omega)]
          exact ht) ?_
  refine RelCT.seq (R := Two (FX XV)) (copyA_gct RpP.B RpP.Z (fun p => wk p.k) (hB _) (by taint_decide)
    fun p s h => ?_) ?_
  · have hw := h.ws
    have hZ16 : slot (wk p.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
    refine WP.mono (copyA_ok hw (o := fV) (a := aN) (by decide) (by decide) (by decide)) fun u ⟨cv, o, k⟩ => ?_
    have hf : Frm p.B (rg (wk p.k) [fV] []) s.mem u.mem := Frm.rg_of_out o (by omega) _ _ (by decide)
    refine h.step hf (by decide) (by simp) (by simp) k (by decide) fun I e ht => ?_
    subst e; dsimp only [RpIn.pub] at hf cv hZ16
    refine ⟨?_, ?_⟩
    · show word u.mem I.B (slot (wk I.k) fU + 8 * wk I.k) = 0
      rw [hf.rg_wordA hZ16 (by simp) (by decide) (by decide) (by omega)]; exact ht
    · rw [cv, hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]
  -- `x₁ = 1`, `x₂ = 0`.
  refine RelCT.seq (R := Two (FX (XW false false))) (zeroA_gct RpP.B RpP.Z (fun p => wk p.k) (hB _)
    (by taint_decide) fun p s h => ?_) ?_
  · have hw := h.ws
    have hZ16 : slot (wk p.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
    refine WP.mono (zeroA_ok hw (j := fX₁) (by decide)) fun u ⟨z, o, k⟩ => ?_
    have hf : Frm p.B (rg (wk p.k) [fX₁] []) s.mem u.mem := Frm.rg_of_out o (Nat.le_refl _) _ _ (by decide)
    refine h.step hf (by decide) (by simp) (by simp) k (by decide) fun I e hv => ?_
    subst e; dsimp only [RpIn.pub] at hf z hZ16
    refine ⟨xv_keep hZ16 hf (by decide) (by decide) (by decide) hv, fun _ => z, ?_, ?_⟩ <;> intro e <;> cases e
  refine RelCT.seq (R := Two (FX (XW true false))) ?_ ?_
  · have e : setOneA fX₁ = ws ++ (base fX₁ .rbx ++ ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] :
        List Instr)) := by
      simp only [setOneA, List.append_assoc]
    rw [e]
    refine ws_block_ct RpP.B RpP.Z (fun p => wk p.k) (hB _) (by taint_decide) fun p s h => ?_
    rw [← e]
    have hw := h.ws
    have hn := hw.scr.nowrap
    have hZ16 : slot (wk p.k) 16 ≤ 2 ^ 64 := by have := hw.hZ; omega
    have sX₁ := hw.sl (j := fX₁) (by decide)
    have hw1 := hw.w1
    refine WP.mono (setOneA_ok hw (j := fX₁) (by decide)) fun u ⟨m, k⟩ => ?_
    have hf : Frm p.B (rg (wk p.k) [fX₁] []) s.mem u.mem := by
      rw [m]; exact Frm.rg_of_out (writeW_outside _ _ _ (by omega)) (by omega) _ _ (by decide)
    refine h.step hf (by decide) (by simp) (by simp) k (by decide) fun I e hv => ?_
    subst e; dsimp only [RpIn.pub] at hf m hZ16 hn sX₁ hw1
    refine ⟨xv_keep hZ16 hf (by decide) (by decide) (by decide) hv.1, ?_, fun _ => ?_, ?_⟩
    · intro e; cases e
    · rw [m]; exact wv_set_one (by omega) (hv.2.1 rfl) (by omega)
    · intro e; cases e
  refine RelCT.seq (R := Two (FX (XW true true))) (zeroA_gct RpP.B RpP.Z (fun p => wk p.k) (hB _)
    (by taint_decide) fun p s h => ?_) ?_
  · have hw := h.ws
    have hZ16 : slot (wk p.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
    refine WP.mono (zeroA_ok hw (j := fX₂) (by decide)) fun u ⟨z, o, k⟩ => ?_
    have hf : Frm p.B (rg (wk p.k) [fX₂] []) s.mem u.mem := Frm.rg_of_out o (Nat.le_refl _) _ _ (by decide)
    refine h.step hf (by decide) (by simp) (by simp) k (by decide) fun I e hv => ?_
    subst e; dsimp only [RpIn.pub] at hf z hZ16
    refine ⟨xv_keep hZ16 hf (by decide) (by decide) (by decide) hv.1, ?_, fun _ => ?_, fun _ => z⟩
    · intro e; cases e
    rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hv.2.2.1 rfl
  -- The inverse, and `q = n / v`.
  refine RelCT.seq (inverse_gct (by taint_decide)) (RelCT.seq (R := Two (FX fun _ _ => True))
    (zeroA_gct RpP.B RpP.Z (fun p => wk p.k) (hB _) (by taint_decide) fun p s h =>
      WP.mono (zeroA_ok h.ws (j := fQ) (by decide)) fun u ⟨_, o, k⟩ =>
        h.step (Frm.rg_of_out o (Nat.le_refl _) [fQ] [] (by decide)) (by decide) (by simp) (by simp) k (by decide)
          fun _ _ _ => trivial) (RelCT.seq (R := Two (FX fun _ _ => True))
    (copyA_gct RpP.B RpP.Z (fun p => wk p.k) (hB _) (by taint_decide) fun p s h =>
      WP.mono (copyA_ok h.ws (o := fQ) (a := aN) (by decide) (by decide) (by decide)) fun u ⟨_, o, k⟩ =>
        h.step (Frm.rg_of_out o (by omega) [fQ] [] (by decide)) (by decide) (by simp) (by simp) k (by decide)
          fun _ _ _ => trivial) (divmod_gct (by taint_decide))))

/-! ## The larger first, and the stores -/

theorem finC_ct : RelCT isa (Two (FX fun _ _ => True)) (seqs [.block (ws ++ base fV .rbx ++ base fQ .r10 ++
    ([.mov32 .rbp (.imm 0)] : List Instr)), wordLoop 0 ltBody, .block [.mov .r15 (.reg .rbp)], wordLoop 0 cswapBody])
    (Two (FX fun _ _ => True)) := by
  have e : seqs [.block (ws ++ base fV .rbx ++ base fQ .r10 ++ [.mov32 .rbp (.imm 0)]), wordLoop 0 ltBody,
      .block [.mov .r15 (.reg .rbp)], wordLoop 0 cswapBody] = .seq (.block (ws ++ (base fV .rbx ++ (base fQ .r10 ++
        ([.mov32 .rbp (.imm 0)] : List Instr))))) (.seq (wordLoop 0 ltBody) (.seq (.block [.mov .r15 (.reg .rbp)])
          (wordLoop 0 cswapBody))) := by
    simp only [seqs, List.append_assoc]
  rw [e]
  refine ws_ct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide) fun p s h => ?_
  rw [← e]
  exact WP.mono (finC_ok h.ws) fun u ⟨f, k, _⟩ => h.step f (by decide) (by simp) (by simp) k (by decide)
    fun _ _ _ => trivial

/-- Before the stores: the working space, the arguments and the mask. -/
def GSr (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (c : Bool), I.pub = p ∧ Ws s I.B I.Z (wk I.k) ∧
    RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD I.sv ∧ s.wr = I.W ∧ RpLens I ∧ RpOuts I ∧
    word s.mem I.B (8 * sMask) = mask c

theorem GSr.ws {p : RpP} {s : State} (h : GSr p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨I, c, rfl, h, -⟩ := h
  exact h

theorem pins_GSr : Pins GSr [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]

theorem storeR_ct {j sPtr : Nat} (hj : j < 16) (hP : sPtr < 32) (ptr : RpP → Addr)
    (hA : ∀ p s, GSr p s → word s.mem p.B (8 * sPtr) = ptr p ∧
      (∀ i < p.k, InRegions p.W (ptr p + BitVec.ofNat 64 i) 1) ∧
      (∀ i < p.k, p.Z ≤ ofs p.B (ptr p + BitVec.ofNat 64 i)))
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK)), .mov .r15 (.mem (hdr sMask))] : List Instr))) hc).isSome
      = true) :
    RelCT isa (Two GSr) (seqs (storeA j sPtr Impl.Bignum.X86_64.Public.sK sMask)) (Two GSr) :=
  pin_ct [.rdi] [.rdi, .rbx, .rsi, .rcx] (fun p => ioVal p.B (off p.B (slot (wk p.k) j)) (ptr p) p.k) pins_GSr ht
    (fun p s h => by
      obtain ⟨hp, -⟩ := hA p s h
      have h' := h
      obtain ⟨I, c, rfl, hw, ha, -⟩ := h'
      exact WP.mono (storeBlk_ok hw hP (by decide) hp ha.k) fun t ⟨hbx, hsi, hcx, hdi⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact hbx
        · exact hsi
        · exact hcx)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hwr, hsep⟩ := hA p s h
      obtain ⟨I, c, rfl, hw, ha, hW, L, O, hm⟩ := h
      dsimp only [RpIn.pub] at hp hwr hsep ⊢
      have hn := hw.scr.nowrap
      have h256 := hw.h256
      have hk1 := L.k1
      have hk2 := L.k2
      refine WP.mono (storeA_ws hw hj hP (by decide) hp ha.k hm (by omega) (by unfold wk; omega)
        (fun i hi => by rw [hW]; exact hwr i hi) hsep) fun t ⟨_, _, ht, hf, k⟩ => ?_
      have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) :=
        fun i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
      exact ⟨I, c, rfl, ht, ha.congr fun i hi => fw i (by unfold rArg at hi; omega), k.2.2.trans hW, L, O,
        (fw _ (by decide)).trans hm⟩

/-- `fin` leaks the same in runs that agree on the public data. -/
theorem fin_ct (M : Mont) : RelCT isa (Two GR3) (seqs (fin M.mm)) fun _ _ => True := by
  rw [show fin M.mm = [.block [.mov .rax (.mem (hdr sC3)), .store (hdr sMask) .rax], M.mm aY aY aOne, zeroA fU,
      .block (ws ++ base aY .r8 ++ base aOne .r10 ++ base fU .rsi ++ [.mov32 .rbp (.imm 0)]),
      wordLoop 0 subBody] ++ ([zeroA fV, copyA fV aN, zeroA fX₁, .block (setOneA fX₁), zeroA fX₂,
        inverse fU fV fX₁ fX₂ aN fT, zeroA fQ, copyA fQ aN, divmod fQ fR fV fT] ++
      ([.block (ws ++ base fV .rbx ++ base fQ .r10 ++ [.mov32 .rbp (.imm 0)]), wordLoop 0 ltBody,
        .block [.mov .r15 (.reg .rbp)], wordLoop 0 cswapBody] ++
      (storeA fV sP Impl.Bignum.X86_64.Public.sK sMask ++ (storeA fQ sQ Impl.Bignum.X86_64.Public.sK sMask ++
        ([.block retMask] : List (Prog isa)))))) by simp only [fin, List.append_assoc, List.cons_append,
          List.nil_append]]
  refine (ct_app (by simp) (by simp) (finA_ct M) (ct_app (by simp) (by simp) finB_ct (ct_app (by simp)
    (by simp [storeA]) finC_ct (?_ : RelCT isa (Two (FX fun _ _ => True)) _ (Two fun (_ : RpP) (_ : State) => True))))).mono
      (fun _ _ h => h) fun _ _ _ => trivial
  refine RelCT.seqs_append (by simp [storeA]) (by simp [storeA]) (RelCT.seq (R := Two GSr) ?_ ?_)
  · refine (storeR_ct (by decide) (by decide) RpP.pP (fun p s h => ?_) (by taint_decide)).mono
      (fun _ _ h => two_mono (fun p s ⟨I, m₀, c, e, S, L, O, hm, _⟩ => ⟨I, c, e, S.ws, S.args, S.wr, L, O, hm⟩) h)
      fun _ _ h => h
    obtain ⟨I, c, rfl, -, ha, -, L, O, -⟩ := h
    exact ⟨ha.p, O.p, O.sp⟩
  refine RelCT.seqs_append (by simp [storeA]) (by simp) (RelCT.seq (R := Two GSr)
    (storeR_ct (by decide) (by decide) RpP.pQ (fun p s h => ?_) (by taint_decide)) ?_)
  · obtain ⟨I, c, rfl, -, ha, -, L, O, -⟩ := h
    exact ⟨ha.q, O.q, O.sq⟩
  exact (two_taint [.rdi] pins_GSr (by taint_decide)).mono (fun _ _ h => h) fun _ _ _ => ⟨default, trivial, trivial⟩

end Rp

end VG.Proof.Rsa.X86_64
