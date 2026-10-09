import VerifiedGarbage.Proof.X448.X86.BitsInput
import VerifiedGarbage.Proof.X448.X86.Finish
import VerifiedGarbage.Proof.X448.X86.Ladder
import VerifiedGarbage.Proof.X448.X86.FinalSwap
import VerifiedGarbage.Proof.X448.X86.Inv
import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.TCB.X86.Target

/-!
# X448 on x86 (32-bit): the whole function

The contract the proof is written against (the facts of `Spec.X448.x448Contract`
it uses, stated for x86 (32-bit)), and the correctness of `vg_x448` against it:
every write is in the working space but the result's, so the arguments are read
unchanged, the callee-saved registers restored from the working space, and the
return address kept.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega

theorem bytesAt_outside {base p : Addr} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hp : ∀ i < 56, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    Spec.X448.bytesAt m' p 56 = Spec.X448.bytesAt m p 56 := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact hp i hi

theorem far_output {base p : Addr} (hd : (⟨p, 56⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < 8192) : 56 ≤ ofs p (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192) (by omega) (by omega))
  simp only [Region.Contains]
  change ofs p (off base i) + 1 ≤ 56
  omega

theorem E_outside {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (i : Index)
    (hi : slot i.val + 112 ≤ o ∨ o + n ≤ slot i.val) : E m' base i = E m base i := by
  simp only [E, F]
  rw [h.fe hi (by have := i.isLt; simp only [slot]; omega)]

section
variable (σ : State)
/-- The working space, the scalar and the u-coordinate, as the specification
decodes them on entry. -/
abbrev bs : Addr := (arg σ 3).setWidth 64
abbrev kOf : Nat := Spec.X448.decodeScalar448 (Spec.X448.bytesAt σ.mem ((arg σ 1).setWidth 64) 56)
abbrev uOf : Spec.X448.Fe :=
  toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt σ.mem ((arg σ 2).setWidth 64) 56))
end

/-- After `setup`, from the entry state `σ`. -/
def S1 (σ s : State) : Prop :=
  Scr s (bs σ) ∧ BoundedEnv s.mem (bs σ) ∧ Keeps setupRegs σ s ∧
    Outside (bs σ) 0 8192 σ.mem s.mem ∧ Saved (bs σ) σ.gpr s.mem ∧
    E s.mem (bs σ) 0 = uOf σ ∧ E s.mem (bs σ) 1 = 1 ∧ E s.mem (bs σ) 2 = 0 ∧
    E s.mem (bs σ) 3 = E s.mem (bs σ) 0 ∧ E s.mem (bs σ) 4 = 1 ∧ word s.mem (bs σ) SWAP = 0

theorem setup_stage {σ : State} (hp : Pre σ) : WP isa (.block setup) σ (S1 σ) := by
  have hr : ∀ j < 56, InRegions (σ.rd ++ σ.wr) (off ((arg σ 2).setWidth 64) j) 1 := fun j hj =>
    ⟨pointR σ, by rw [hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  exact setup_ok hp rfl rfl hr fun j hj => far hp.point_sc hj (by decide)

/-- Before the ladder, from the entry state `σ`. -/
structure Mid (σ s : State) : Prop where
  pre : Pre σ
  sp : s.gpr .esp = σ.gpr .esp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  saved : Saved (bs σ) σ.gpr s.mem
  out : Outside (bs σ) 0 8192 σ.mem s.mem
  bits : ∀ t < 448, s.mem (off (bs σ) (BITS + t)) = BitVec.ofNat 8 (bit (kOf σ) t)
  start : ∀ s', s'.gpr .esi = BitVec.ofNat 32 448 → (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) →
    s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → LInv (bs σ) (kOf σ) (uOf σ) s s' 448

theorem bits_stage {σ s₁ : State} (hp : Pre σ) (h : S1 σ s₁) : WP isa bits s₁ (Mid σ) := by
  obtain ⟨hs₁, b₁, k₁, o₁, sv₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁⟩ := h
  have kd : ∀ j < 56, 8192 ≤ ofs (bs σ) (off ((arg σ 1).setWidth 64) j) :=
    fun j hj => far hp.scalar_sc hj (by decide)
  refine WP.mono (bits_ok hp (k₁.1 _ (by decide)) k₁.2.1 k₁.2.2 rfl o₁ hs₁ kd)
    fun s₂ ⟨k₂, o₂, bits₂⟩ => ?_
  have k02 := k₁.then k₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have e₂ : ∀ i : Index, E s₂.mem (bs σ) i = E s₁.mem (bs σ) i := by
    intro i; exact E_outside o₂ i (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
  have b₂ : BoundedEnv s₂.mem (bs σ) := by
    intro i j hj
    rw [o₂.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) hj]
    exact b₁ i j hj
  have kb := bytesAt_outside o₁ kd
  have sp₂ : s₂.gpr .esp = σ.gpr .esp := k02.1 _ (by decide)
  have stk₂ : callStk s₂ = stkR σ := by
    simp only [callStk, below, sp₂]
    rw [VG.X86.Taint.sub_setWidth hp.sp_room]
  have hc₂ : CallCtx s₂ (bs σ) := ⟨by rw [sp₂]; exact hp.sp_room, by rw [stk₂]; exact hp.stk_sc.symm⟩
  refine ⟨hp, sp₂, k02.2.1, k02.2.2, sv₁.outside o₂ (by decide), o₁.trans (o₂.mono (by decide) (by decide)),
    fun t ht => by rw [bits₂ t ht, kb], fun s' hb hg hm hr hw => ⟨
      ⟨by rw [hg _ (by decide)]; exact hs₂.edi, hw ▸ hs₂.wr,
        by rw [hg _ (by decide)]; exact hs₂.nowrap⟩, hc₂.keep (hg _ (by decide)), hm ▸ b₂,
      ⟨fun r h => hg r (fun e => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
      hb, hm ▸ WsOut2.refl _ _ _ _ _ _,
      by rw [hm, e₂ 0, x1₁], by rw [hm, e₂ 1, x2₁]; rfl,
      by rw [hm, e₂ 2, z2₁]; rfl, by rw [hm, e₂ 3, x3₁, x1₁]; rfl,
      by rw [hm, e₂ 4, z3₁]; rfl,
      by rw [hm, o₂.word (d := SWAP) (by decide) (by decide), sw₁]; rfl⟩⟩

/-- What code using at most the 20 bytes of stack below `esp` writes outside
the working space and the result. -/
theorem xframe {σ s : State} (hp : Pre σ) {c : Prog isa} (hc : NoSp c) (hu : stackUse c ≤ 20)
    (hsp : s.gpr .esp = σ.gpr .esp) (hw : s.wr = σ.wr) (hf : XFrame σ s.mem) {Q : State → Prop}
    (h : WP isa c s Q) : WP isa c s fun t => Q t ∧ XFrame σ t.mem := by
  refine WP.mono (WP.withFrame hc (by rw [hsp]; exact Nat.le_trans hu hp.sp_room) h) fun t ⟨q, f⟩ => ⟨q, ?_⟩
  refine hf.trans (f.sub fun r hr => ?_)
  rw [hw, hp.wr] at hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · refine ⟨stkR σ, by simp, ?_⟩
    rw [hsp, show stkR σ = below (σ.gpr .esp) 20 by
      simp only [below]; rw [VG.X86.Taint.sub_setWidth hp.sp_room]]
    exact below_sub hu hp.sp_room

/-- In the ladder, `n` iterations from its end, which started in `s₂`, from
the entry state `σ`. -/
def Lad (σ s₂ s : State) (n : Nat) : Prop :=
  Mid σ s₂ ∧ LInv (bs σ) (kOf σ) (uOf σ) s₂ s n ∧ XFrame σ s.mem

theorem Lad.sp {σ s₂ s : State} {n : Nat} (h : Lad σ s₂ s n) : s.gpr .esp = σ.gpr .esp :=
  (h.2.1.regs.1 _ (by decide)).trans h.1.sp

theorem Lad.wr {σ s₂ s : State} {n : Nat} (h : Lad σ s₂ s n) : s.wr = σ.wr :=
  h.2.1.regs.2.2.trans h.1.wr

theorem ladder_stage {σ s : State} (h : Mid σ s) : WP isa ladder s fun t => Lad σ s t 0 := by
  refine WP.mono (xframe h.pre (NoSp.of_all (by lit_decide)) (by lit_decide) h.sp h.wr
    (XFrame.of_outside h.out) (ladder_ok h.bits h.start)) fun t ⟨l, f⟩ => ⟨h, l, f⟩

/-- The swap the ladder leaves. -/
abbrev swOf (σ : State) : Bool := decide ((ladderAfter (kOf σ) (uOf σ) 0).swap = 1)

/-- After the last swap, from the end `s₄` of the ladder. -/
def Sw (σ s₂ s₄ s : State) : Prop :=
  Lad σ s₂ s₄ 0 ∧ Keep (bs σ) s₄ s ∧ BoundedEnv s.mem (bs σ) ∧
    E s.mem (bs σ) = opSwap 2 4 (swOf σ) (opSwap 1 3 (swOf σ) (E s₄.mem (bs σ))) ∧ XFrame σ s.mem

theorem lastSwap_stage {σ s₂ s : State} (h : Lad σ s₂ s 0) : WP isa (.block lastSwap) s (Sw σ s₂ s) := by
  obtain ⟨m, L, f⟩ := h
  refine WP.mono (xframe m.pre (c := .block lastSwap) (NoSp.of_all (by lit_decide)) (Nat.zero_le 20)
    (Lad.sp ⟨m, L, f⟩) (Lad.wr ⟨m, L, f⟩) f
    (lastSwap_ok L.scr L.bounded
    (by have := ladderAfter_swap_le (kOf σ) (uOf σ) (n := 0) (by decide); omega) L.swap))
    fun t ⟨⟨k, b, e⟩, f'⟩ => ⟨⟨m, L, f⟩, k, b, e, f'⟩

theorem Sw.fin {σ s₂ s₄ s : State} (h : Sw σ s₂ s₄ s) :
    Scr s (bs σ) ∧ CallCtx s (bs σ) ∧ s.gpr .esp = σ.gpr .esp ∧ s.wr = σ.wr := by
  obtain ⟨l, k, -⟩ := h
  exact ⟨k.scr l.2.1.scr, k.ctx l.2.1.ctx, (k.regs.1 _ (by decide)).trans l.sp, k.regs.2.2.trans l.wr⟩

/-- After the inversion, from its start `s₅`. -/
def Iv (σ s₂ s₄ s₅ s : State) : Prop :=
  Sw σ s₂ s₄ s₅ ∧ IKeep (bs σ) s₅ s ∧ BoundedEnv s.mem (bs σ) ∧
    E s.mem (bs σ) = invEnv (E s₅.mem (bs σ)) ∧ XFrame σ s.mem

theorem invert_stage {σ s₂ s₄ s : State} (h : Sw σ s₂ s₄ s) :
    WP isa Impl.X448.X86.invert s (Iv σ s₂ s₄ s) := by
  obtain ⟨hs, hc, sp, wr⟩ := h.fin
  refine WP.mono (xframe h.1.1.pre (NoSp.of_all (by lit_decide)) (by lit_decide) sp wr h.2.2.2.2
    (invert_ok hs hc h.2.2.1)) fun t ⟨⟨k, b', e⟩, f'⟩ => ⟨h, k, b', e, f'⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa x448 s₀ fun s' => abiPreserved s₀ s' ∧ Proof.X448.x448X86.post s₀ s' := by
  rw [x448]
  refine WP.seq (WP.mono (setup_stage hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (bits_stage hp h₁) fun s₂ m => ?_)
  refine WP.seq (WP.mono (ladder_stage m) fun s₄ l => ?_)
  refine WP.seq (WP.mono (lastSwap_stage l) fun s₅ w => ?_)
  refine WP.seq (WP.mono (invert_stage w) fun s₆ v => ?_)
  obtain ⟨_, k₆, b₆, e₆, o₆⟩ := v
  obtain ⟨hs₅, hc₅, sp₅, wr₅⟩ := w.fin
  obtain ⟨⟨m', L, -⟩, k₅, -, e₅, -⟩ := w
  have sv₆ := ((m'.saved.wsout2 L.mem (by decide) (by decide)).wsout2 k₅.mem (by decide)
    (by decide)).wsout2 k₆.mem (by decide) (by decide)
  have sp₆ : s₆.gpr .esp = s₀.gpr .esp := (k₆.regs.1 _ (by decide)).trans sp₅
  have rd₆ : s₆.rd = s₀.rd :=
    k₆.regs.2.1.trans (k₅.regs.2.1.trans (L.regs.2.1.trans m'.rd))
  have wr₆ : s₆.wr = s₀.wr := k₆.regs.2.2.trans wr₅
  refine WP.mono (finish_ok hp sp₆ rd₆ wr₆ rfl o₆ (k₆.scr hs₅) (k₆.ctx hc₅) b₆
    (fun j hj => far_output hp.out_sc hj) sv₆) fun s' ⟨restored, kf, fm, result⟩ => ?_
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact restored (.ebx, 0) (by decide)
      · exact restored (.esi, 4) (by decide)
      · exact restored (.edi, 8) (by decide)
      · exact restored (.ebp, 12) (by decide)
      · exact (kf.1 _ (by decide)).trans sp₆
    · have frame : Frame [scR (arg s₀ 3), outR s₀, stkR s₀] s₀.mem s'.mem := by
        refine o₆.trans (fm.mono ?_)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · refine Or.inr (Or.inr ?_)
          simp only [callStk, below, sp₆]
          rw [VG.X86.Taint.sub_setWidth hp.sp_room]
      have ret : (retR s₀).Contains ((s₀.gpr .esp).setWidth 64) 4 := by
        simpa only [BitVec.add_zero] using
          Offset.contains_base ((s₀.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide) (by decide)
      exact frame.readW ret
        (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact hp.ret_sc
            · exact hp.ret_out
            · exact hp.stk_ret.symm) (by decide)
  · change Spec.X448.bytesAt s'.mem ((arg s₀ 0).setWidth 64) 56 = _
    rw [result, x448_eq]
    apply congrArg Spec.X448.encodeUCoordinate
    rw [e₆, invEnv_x2, invEnv_eval, e₅]
    simp (config := {decide := true}) only [opSwap, Function.update_apply, ite_true, ite_false]
    rw [L.x2, L.x3, L.z2, L.z3, cswap_fst, cswap_fst]

end VG.Proof.X448.X86
