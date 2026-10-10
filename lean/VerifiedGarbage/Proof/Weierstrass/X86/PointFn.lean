import VerifiedGarbage.Proof.Weierstrass.X86.PointFprog

/-!
# Complete point addition and doubling as functions, on x86 (32-bit): correctness

`fn S dbl` (`Impl/Weierstrass/X86/Point.lean`), from a state that its
precondition describes (`PrePt`: the working space the argument, writable,
the arguments, the return address and the stack its calls use apart from
it, and every coordinate it reads below the prime), returns with the
callee-saved registers and the return address kept, the working space
changed only at `O` and in the own working space, and `O`'s coordinates
below the prime, standing for `rcbAdd` of what the constants and the
operands stand for (`fn_ok`).
-/

namespace VG.Proof.Weierstrass.X86.Point

open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass.X86.Point
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Mont

/-- The numbers of the layout, for `omega`. -/
theorem lay_nums {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) :
    Spec.Weierstrass.Point.ownAt k + 64 + 6 * Spec.Weierstrass.Point.elemBytes k = own k ∧ own k + 64 * k = 4096 ∧ Spec.Weierstrass.Point.elemBytes k = 8 * k ∧
    Spec.Weierstrass.Point.b3At k + Spec.Weierstrass.Point.elemBytes k = Spec.Weierstrass.Point.ownAt k ∧ Spec.Weierstrass.Point.aAt k + Spec.Weierstrass.Point.elemBytes k = Spec.Weierstrass.Point.b3At k ∧
    Spec.Weierstrass.Point.qAt k + 3 * Spec.Weierstrass.Point.elemBytes k = Spec.Weierstrass.Point.aAt k ∧ Spec.Weierstrass.Point.pAt k + 3 * Spec.Weierstrass.Point.elemBytes k = Spec.Weierstrass.Point.qAt k ∧
    Spec.Weierstrass.Point.oAt k + 3 * Spec.Weierstrass.Point.elemBytes k = Spec.Weierstrass.Point.pAt k ∧ 1000 ≤ Spec.Weierstrass.Point.oAt k := by
  unfold Spec.Weierstrass.Point.oAt Spec.Weierstrass.Point.pAt Spec.Weierstrass.Point.qAt Spec.Weierstrass.Point.aAt Spec.Weierstrass.Point.b3At Spec.Weierstrass.Point.ownAt Spec.Weierstrass.Point.elemBytes own Spec.Weierstrass.Mont.ownAt
    Spec.Weierstrass.Mont.ownBytes
  omega

/-- The slots the function reads first lie below its own working space. -/
theorem enc_rIds {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) :
    ∀ x ∈ rIds, enc k dbl x + 8 * k ≤ Spec.Weierstrass.Point.ownAt k := by
  have := lay_nums hk3 hk6
  intro x hx
  simp only [rIds, List.mem_cons, List.not_mem_nil, or_false] at hx
  cases dbl <;> rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [enc, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Bool.false_eq_true] <;> omega

/-- The slots `enc` gives are laid out as the program needs, and those it
writes lie apart from the saved `lr` and within `O` or the own working
space. -/
theorem enc_lay {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) : LayR k 17 wIds (enc k dbl) := by
  have := lay_nums hk3 hk6
  refine ⟨fun x hx => ?_, fun w hw x hx hne => ?_⟩
  · rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 ∨ x = 10 ∨ x = 11 ∨ x = 12 ∨ x = 13 ∨ x = 14 ∨ x = 15 ∨ x = 16 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases dbl <;>
      simp only [enc, Impl.Weierstrass.X86.Point.tmpAt, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Bool.false_eq_true] <;> omega
  · simp only [wIds, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 ∨ x = 10 ∨ x = 11 ∨ x = 12 ∨ x = 13 ∨ x = 14 ∨ x = 15 ∨ x = 16 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases dbl <;>
      simp only [enc, Impl.Weierstrass.X86.Point.tmpAt, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Bool.false_eq_true] at hne ⊢ <;> omega

theorem enc_wIds {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) :
    ∀ w ∈ wIds, (enc k dbl w + 8 * k ≤ Spec.Weierstrass.Point.ownAt k ∨ Spec.Weierstrass.Point.ownAt k + 4 ≤ enc k dbl w) ∧
      ((Spec.Weierstrass.Point.oAt k ≤ enc k dbl w ∧ enc k dbl w + 8 * k ≤ Spec.Weierstrass.Point.pAt k) ∨
        (Spec.Weierstrass.Point.ownAt k ≤ enc k dbl w ∧ enc k dbl w + 8 * k ≤ 4096)) := by
  have := lay_nums hk3 hk6
  intro w hw
  simp only [wIds, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [enc, Impl.Weierstrass.X86.Point.tmpAt, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub, Nat.mul_zero, Nat.mul_one, Nat.add_zero] <;> omega

/-- Changes within ranges are within any ranges that contain them. -/
theorem outs_sub {base : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Outs base rs' m m' :=
  fun x hx => h x fun r hr => by
    obtain ⟨r', hr', h1, h2⟩ := hs r hr
    have := hx r' hr'
    omega

/-- A 32-bit word apart from the ranges. -/
theorem outs_readW32 {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Outs base W m m')
    {d : Nat} (hd : ∀ w ∈ W, d + 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  (Mem.readW_congr fun i hi => (h _ fun w hw' => by
    rw [ofs_off base (by omega)]; have := hd w hw'; omega).symm).symm

/-- The precondition of the function, on the state: the working space its
argument, writable, apart from the argument, the return address and the
stack its calls use, and the numbers it reads below `m`. -/
structure PrePt (k m : Nat) (dbl : Bool) (s : State) : Prop where
  scr : ArgP s (wsOf s)
  ret_ws : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨wsOf s, 8192⟩
  k3 : 3 ≤ k
  k6 : k ≤ 6
  lt : ∀ x ∈ rIds, wordsVal s.mem (wsOf s) (enc k dbl x) k < m

/-- `[ws + d]`, through a register holding the argument. -/
theorem addr_ws {s : State} {base : Addr} (hs : ArgP s base) {d : Nat} (hd : d < 8192) :
    addr (arg s 0) d = off base d := by
  rw [addr_eq (by have := hs.arg_toNat; have := hs.nowrap; omega), hs.ws]

/-- The environment of the entry: what the numbers of the slots stand for. -/
def E₀ (k m : Nat) [NeZero m] (dbl : Bool) (s : State) (x : Nat) : Fin m :=
  toM m (2 ^ (64 * k)) (wordsVal s.mem (wsOf s) (enc k dbl x) k)

theorem rIds_lt : ∀ x ∈ rIds, x < 17 := by decide

theorem out_valid : ∀ j < 3, j ∈ validAfter (rcb sId pId qId oId) rIds := by decide

/-- The function: the callee-saved registers and the return address kept,
the working space changed only at `O` and in the own working space, and
`O`'s coordinates below the prime, standing for `rcbAdd` of what the
constants and the operands stand for. -/
theorem fn_ok {S : Spec.Weierstrass.Mont.Modulus} [NeZero S.m] (hF : FnOk S) (hodd : S.m % 2 = 1)
    {dbl : Bool} {s : State} (hp : PrePt S.k S.m dbl s) :
    WP isa (Impl.Weierstrass.X86.Point.fn S dbl) s fun s' => abiPreserved s s' ∧
      Outs (wsOf s) [(Spec.Weierstrass.Point.oAt S.k, 3 * Spec.Weierstrass.Point.elemBytes S.k),
        (Spec.Weierstrass.Point.ownAt S.k, 4096 - Spec.Weierstrass.Point.ownAt S.k), outW] s.mem s'.mem ∧
      (∀ j < 3, wordsVal s'.mem (wsOf s) (enc S.k dbl j) S.k < S.m) ∧
      (toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (wsOf s) (enc S.k dbl 0) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (wsOf s) (enc S.k dbl 1) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (wsOf s) (enc S.k dbl 2) S.k)) =
        VG.Proof.Weierstrass.rcbAdd (E₀ S.k S.m dbl s 9) (E₀ S.k S.m dbl s 10) (E₀ S.k S.m dbl s 3)
          (E₀ S.k S.m dbl s 4) (E₀ S.k S.m dbl s 5) (E₀ S.k S.m dbl s 6) (E₀ S.k S.m dbl s 7)
          (E₀ S.k S.m dbl s 8) := by
  have hl := lay_nums hp.k3 hp.k6
  have hR := enc_rIds hp.k3 hp.k6 dbl
  have hW := enc_wIds hp.k3 hp.k6 dbl
  have hs := hp.scr
  have hn := hs.nowrap
  have hsv : Impl.Weierstrass.X86.Point.saveAt S.k + 4 < 8192 := by simp only [Impl.Weierstrass.X86.Point.saveAt]; omega
  rw [Impl.Weierstrass.X86.Point.fn]
  -- `edi` saved, and `edi = ws`.
  refine WP.seq (wp_ldm (b := .esp) rfl ⟨_, List.mem_append_left _ hs.rd, by
      rw [argAddr0_eq]; exact Region.contains_self _ _⟩ fun s₀ u₀ => ?_)
  rw [argAddr0_eq] at u₀
  have eax₀ : s₀.gpr .eax = arg s 0 := u₀.gpr
  refine wp_stm (b := .eax) eax₀ ⟨_, by rw [u₀.wr]; exact hs.wr, by
      rw [addr_ws hs (by omega)]; exact Offset.contains_base _ (by omega) (by omega)⟩ fun s₁ u₁ =>
    wp_mov fun s₂ u₂ => WP.block_nil ?_
  rw [addr_ws hs (by omega)] at u₁
  have m₁ : s₂.mem = s.mem.writeW (off (wsOf s) (Impl.Weierstrass.X86.Point.saveAt S.k)) (s.gpr .edi) := by
    rw [u₂.mem, u₁.mem, u₀.mem, u₀.other _ (by decide)]
  have g₁ : ∀ r, r ≠ .eax → r ≠ .edi → s₂.gpr r = s.gpr r := fun r h h' => by
    rw [u₂.other _ h', u₁.gpr, u₀.other _ h]
  have edi₂ : s₂.gpr .edi = arg s 0 := by rw [u₂.gpr, u₁.gpr, eax₀]
  have O₁ : Outside (wsOf s) (Impl.Weierstrass.X86.Point.saveAt S.k) 4 s.mem s₂.mem := by
    rw [m₁]; exact writeW32_outside _ _ _ (by omega)
  have F₁ : Frame [⟨wsOf s, 8192⟩, below (s.gpr .esp) 20] s.mem s₂.mem := by
    rw [m₁]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Offset.contains_base _ (by omega) (by omega))
  have esp₂ : s₂.gpr .esp = s.gpr .esp := g₁ _ (by decide) (by decide)
  have hs₁ : ScrP s₂ (wsOf s) := by
    have e : argAddr s₂ 0 = argAddr s 0 := by simp only [argAddr, esp₂]
    have harg : arg s₂ 0 = arg s 0 := by
      simp only [arg, e]
      refine F₁.readW (r := ⟨argAddr s 0, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.args_ws
      · exact args_below hs.stk.1 hs.sp_fit
    exact ⟨⟨by rw [harg], by rw [u₂.rd, u₁.rd, u₀.rd, e]; exact hs.rd,
      by rw [u₂.wr, u₁.wr, u₀.wr]; exact hs.wr, hs.nowrap, by rw [esp₂]; exact hs.stk,
      by rw [esp₂]; exact hs.sp_fit, by rw [e]; exact hs.args_ws⟩, by rw [edi₂]⟩
  have hI : InvR S.k 17 (enc S.k dbl) (wsOf s) S.m rIds (E₀ S.k S.m dbl s) s₂ := by
    have heq : ∀ x ∈ rIds, wordsVal s₂.mem (wsOf s) (enc S.k dbl x) S.k =
        wordsVal s.mem (wsOf s) (enc S.k dbl x) S.k := fun x hx =>
      Outs.wordsVal (Outs.of_outside O₁ (List.mem_singleton_self _)) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact .inl (by have := hR x hx; simp only [Impl.Weierstrass.X86.Point.saveAt]; omega))
        (by have := hR x hx; omega)
    exact ⟨hs₁, rIds_lt, fun x hx => by rw [heq x hx]; exact hp.lt x hx,
      fun x hx => by rw [heq x hx]; rfl⟩
  refine WP.seq (WP.mono (rcbB_ok hF rfl (enc_lay hp.k3 hp.k6 dbl) (unitMod_pow_two hodd _) hI)
    fun s₃ ⟨K, I₂, hEq⟩ => ?_)
  -- `edi` restored.
  have hs₂ := I₂.scr
  have edi₃ : s₃.gpr .edi = arg s 0 := by
    apply BitVec.eq_of_toNat_eq
    have h1 := congrArg BitVec.toNat hs₂.edi
    have h2 := hs.arg_toNat
    have b1 := (s₃.gpr .edi).isLt
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at h1
    omega
  refine wp_ldm (b := .edi) edi₃ ⟨_, List.mem_append_right _ hs₂.wr, by
      rw [addr_ws hs (by omega)]; exact Offset.contains_base _ (by omega) (by omega)⟩ fun s₄ u₄ =>
    WP.block_nil ?_
  rw [addr_ws hs (by omega)] at u₄
  have m₄ : s₄.mem = s₃.mem := u₄.mem
  -- The saved word survives the program.
  have hsaved : s₃.mem.readW (off (wsOf s) (Impl.Weierstrass.X86.Point.saveAt S.k)) 32 = s.gpr .edi := by
    have h := outs_readW32 K.mem (d := Impl.Weierstrass.X86.Point.saveAt S.k) (fun r hr => by
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with ⟨x, hx, rfl⟩ | rfl | rfl
      · rcases (hW x hx).1 with h | h <;> [exact .inr (by simp only [Impl.Weierstrass.X86.Point.saveAt]; omega);
          exact .inl (by simp only [Impl.Weierstrass.X86.Point.saveAt]; omega)]
      · exact .inl (by simp only [Impl.Weierstrass.X86.Point.saveAt]; omega)
      · exact .inl (by simp only [Impl.Weierstrass.X86.Point.saveAt]; omega)) (by omega)
    rw [h, m₁, Mem.readW_writeW_self32]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, fun j hj => ?_, ?_⟩
  · -- The callee-saved registers.
    by_cases hb : r = .edi
    · subst hb
      rw [u₄.gpr, hsaved]
    · have hr' : r ∉ [Reg.eax, .ecx, .edx] := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp_all
      rw [u₄.other _ hb, K.gpr r hr', g₁ r (by simp_all) hb]
  · -- The return address.
    rw [m₄]
    refine (F₁.trans (by rw [← esp₂]; exact K.fr)).readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩)
      (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ret_ws
    · have h20 := hs.stk.1
      have hsp := hs.sp_fit
      exact Region.disjoint_of_le (.inr (by
        show (below (s.gpr .esp) 20).base.toNat + 20 ≤ ((s.gpr .esp).setWidth 64).toNat
        rw [below_toNat _ h20, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega))
        (by show ((s.gpr .esp).setWidth 64).toNat + 4 ≤ _; rw [BitVec.toNat_setWidth]; omega)
        (by show (below (s.gpr .esp) 20).base.toNat + 20 ≤ _; rw [below_toNat _ h20]; omega)
  · -- The memory.
    rw [m₄]
    refine (outs_sub (rs := [(Impl.Weierstrass.X86.Point.saveAt S.k, 4)]) (Outs.of_outside O₁ (List.mem_singleton_self _)) fun r hr => ?_).trans
      (outs_sub K.mem fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by simp only [Impl.Weierstrass.X86.Point.saveAt]; omega,
        by simp only [Impl.Weierstrass.X86.Point.saveAt]; omega⟩
    · simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with ⟨x, hx, rfl⟩ | rfl | rfl
      · rcases (hW x hx).2 with h | h
        · exact ⟨_, List.mem_cons_self, h.1, by dsimp only; omega⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.1, by dsimp only; omega⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by dsimp only; omega, by dsimp only; omega⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), Nat.le_refl _, Nat.le_refl _⟩
  · rw [m₄]; exact I₂.lt j (out_valid j hj)
  · rw [m₄, I₂.val 0 (out_valid 0 (by decide)), I₂.val 1 (out_valid 1 (by decide)),
      I₂.val 2 (out_valid 2 (by decide))]
    exact hEq

end VG.Proof.Weierstrass.X86.Point
