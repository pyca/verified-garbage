import VerifiedGarbage.Proof.MlKem.X86.Mul
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Impl.MlDsa.X86.Round.Round
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlDsa.Round.Ones
import VerifiedGarbage.Proof.MlKem.X86.AddSub
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Round.Arith`. -/
section

/-!
# ML-DSA on x86 (32-bit): what the rounding code computes

Continuation-style rules for the pieces of `Impl/MlDsa/X86/Round/Round.lean`:
`condAdd` leaves `condAddN r x k` (`condAdd_spec`), `hbRaw g` leaves `⌊(a + γ₂ -
1)/(2γ₂)⌋` (`hbRaw_spec`, by `hbF_eq` of `Proof/MlDsa/Round/Decompose.lean`)
and `hb g` its remainder modulo `m` (`hb_spec`), each changing only the
registers it names (`Only`).
-/

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_)
open VG.Spec.MlDsa (q gamma2s)
open VG.Proof.MlDsa.Round (hbF hbM q_eq mem_gamma2s hbF_le hbF_eq)
open VG.Proof.MlKem.X86 (Only wp_cons wp_mul execMul_eax execMul_other toNat_ofNat32 eq_ofNat_of_toNat)

theorem updOnly {s s' : State} {d : Reg} {v : BitVec 32} (h : Upd s s' d v) : Only [d] s s' :=
  ⟨fun r hr => h.other r (by simpa using hr), h.mem, h.rd, h.wr⟩

theorem Fupd.only {s s' : State} (h : Fupd s s') (ds : List Reg) : Only ds s s' :=
  ⟨fun r _ => by rw [h.gpr], h.mem, h.rd, h.wr⟩

theorem Only.gpr_of {ds : List Reg} {s s' : State} (h : Only ds s s') {r : Reg} (hr : r ∉ ds) :
    s'.gpr r = s.gpr r := h.gpr r hr

/-- Two `Only`s, as one over a list that contains both. -/
theorem Only.comp {ds es fs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Only ds s₁ s₂) (h₂ : Only es s₂ s₃)
    (hd : ∀ r ∈ ds, r ∈ fs := by decide) (he : ∀ r ∈ es, r ∈ fs := by decide) : Only fs s₁ s₃ :=
  (h₁.trans h₂).mono fun r hr => by
    rcases List.mem_append.mp hr with h | h
    · exact hd r h
    · exact he r h

/-- `sub d, [b + o]`, and the flags. -/
theorem wp_subm {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.gpr d - s.mem.readW (addr B o) 32) →
      s'.cf = some (decide ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat)) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (by simp [exec, execAlu, readSrc_mem hb hin]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `sub d, r`, and the carry. -/
theorem wp_subr {is : List Instr} {s : State} {Q : State → Prop} {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d - s.gpr r) → s'.cf = some (decide ((s.gpr d).toNat < (s.gpr r).toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `cmp d, [b + o]`: ZF is `d = [b + o]`. -/
theorem wp_cmpm {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Fupd s s' → s'.zf = some (s.gpr d - s.mem.readW (addr B o) 32 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (s' := arithFlags s (s.gpr d - s.mem.readW (addr B o) 32)
      ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat)
      (subOverflow (s.gpr d) (s.mem.readW (addr B o) 32) (s.gpr d - s.mem.readW (addr B o) 32)))
    (by simp [exec, execAlu, readSrc_mem hb hin]) (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl)

/-- `mul r` of values whose product is less than `2³²`: `eax` is the product. -/
theorem wp_mulSmall {is : List Instr} {s : State} {Q : State → Prop} {r : Reg}
    (hp : (s.gpr .eax).toNat * (s.gpr r).toNat < 2 ^ 32)
    (k : ∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = (s.gpr .eax).toNat * (s.gpr r).toNat →
      WP isa (.block is) s' Q) :
    WP isa (.block (.mul r :: is)) s Q :=
  wp_mul (k _ (VG.Proof.MlKem.X86.execMul_only r s) (by rw [execMul_eax, toNat_ofNat32 hp]))

/-! ## Conditional addition -/

/-- What `condAdd` computes: `r - x`, plus `k` if that borrows. -/
def condAddN (r x k : Nat) : Nat := if r < x then r + k - x else r - x

theorem condAdd_val (r x k : BitVec 32) (hx : x.toNat ≤ r.toNat + k.toNat) :
    (r - x + ((if decide (r.toNat < x.toNat) = true then BitVec.allOnes 32 else 0) &&& k)).toNat =
      VG.Proof.MlDsa.X86.Round.condAddN r.toNat x.toNat k.toNat := by
  unfold VG.Proof.MlDsa.X86.Round.condAddN
  have := r.isLt; have := x.isLt; have := k.isLt
  by_cases h : r.toNat < x.toNat
  · simp only [h, decide_true, ite_true, BitVec.allOnes_and, BitVec.toNat_add, BitVec.toNat_sub]
    omega
  · have e : r - x + ((if decide (r.toNat < x.toNat) = true then BitVec.allOnes 32 else 0) &&& k) = r - x := by
      simp [h]
    rw [e, BitVec.toNat_sub, ite_eq_right h]
    omega

/-- `condAdd r x t k`, from `x` read as `X`: `r ← condAddN r X k`, changing only `r`, `t` and the
flags. -/
theorem condAdd_spec {r t : Reg} (hrt : r ≠ t) {x : Src} {k X : BitVec 32} {is : List Instr} {s : State}
    {P : State → Prop} (hx : readSrc s x = some X) (hX : X.toNat ≤ (s.gpr r).toNat + k.toNat)
    (c : ∀ s', Only [r, t] s s' → (s'.gpr r).toNat = VG.Proof.MlDsa.X86.Round.condAddN (s.gpr r).toNat X.toNat k.toNat →
      WP isa (.block is) s' P) :
    WP isa (.block (condAdd r x t k ++ is)) s P := by
  have htr : t ≠ r := fun e => hrt e.symm
  rw [condAdd, List.cons_append]
  refine cons (s' := (arithFlags s (s.gpr r - X) ((s.gpr r).toNat < X.toNat) (subOverflow (s.gpr r) X
    (s.gpr r - X))).setReg r (s.gpr r - X)) (by simp only [exec, execAlu, hx, Option.bind_some]) ?_
  have u₁ := Upd.flags s r (s.gpr r - X) ((s.gpr r).toNat < X.toNat) (subOverflow (s.gpr r) X (s.gpr r - X))
    (s.gpr r - X)
  have c₁ : ((arithFlags s (s.gpr r - X) ((s.gpr r).toNat < X.toNat) (subOverflow (s.gpr r) X
      (s.gpr r - X))).setReg r (s.gpr r - X)).cf = some (decide ((s.gpr r).toNat < X.toNat)) := rfl
  generalize (arithFlags s (s.gpr r - X) ((s.gpr r).toNat < X.toNat) (subOverflow (s.gpr r) X
    (s.gpr r - X))).setReg r (s.gpr r - X) = s₁ at u₁ c₁ ⊢
  refine wp_sbb_self c₁ fun s₂ u₂ => wp_andi fun s₃ u₃ => wp_add fun s₄ u₄ _ => c s₄ ?_ ?_
  · refine ⟨fun y hy => ?_, u₄.mem.trans (u₃.mem.trans (u₂.mem.trans u₁.mem)),
      u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd)), u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr))⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [u₄.other y hy.1, u₃.other y hy.2, u₂.other y hy.2, u₁.other y hy.1]
  · rw [u₄.gpr, u₃.other r hrt, u₃.gpr, u₂.gpr, u₂.other r hrt, u₁.gpr]
    exact VG.Proof.MlDsa.X86.Round.condAdd_val _ _ _ hX

/-! ## `Decompose` -/

theorem dMul_eq (g : Nat) : dMul g = Proof.MlDsa.Round.hbMul g := rfl
theorem dAdd_eq (g : Nat) : dAdd g = Proof.MlDsa.Round.hbAdd g := rfl
theorem dShift_eq (g : Nat) : dShift g = Proof.MlDsa.Round.hbShift g := rfl

theorem dMod_eq {g : Nat} (h : g ∈ gamma2s) : dMod g = hbM g := by
  rcases mem_gamma2s h with rfl | rfl <;> rfl

theorem dShift_range (g : Nat) : 1 ≤ dShift g ∧ dShift g ≤ 31 := by unfold dShift; split <;> decide

theorem ofNat_small {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k).toNat = k := toNat_ofNat32 h

/-- `hbRaw g` leaves `hbF g a` in `eax` from `a < q` there, changing only `eax`, `edx` and the flags. -/
theorem hbRaw_spec {g : Nat} (hg : g ∈ gamma2s) {is : List Instr} {s : State} {P : State → Prop} {a : Nat}
    (ha : (s.gpr .eax).toNat = a) (haq : a < q)
    (c : ∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = hbF g a → WP isa (.block is) s' P) :
    WP isa (.block (hbRaw g ++ is)) s P := by
  rw [VG.Proof.MlDsa.Round.q_eq] at haq
  have hM : dMul g ≤ 11275 := by unfold dMul; split <;> decide
  have hA : dAdd g ≤ 2 ^ 23 := by unfold dAdd; split <;> decide
  simp only [hbRaw, List.cons_append, List.nil_append]
  refine wp_addi fun s₁ u₁ => wp_shr (by decide) fun s₂ u₂ _ => wp_movi fun s₃ u₃ => ?_
  have e₁ : (s₁.gpr .eax).toNat = a + 127 := by
    rw [u₁.gpr, BitVec.toNat_add, ha]; simp; omega
  have e₂ : (s₂.gpr .eax).toNat = (a + 127) / 128 := by
    rw [u₂.gpr, BitVec.toNat_ushiftRight, e₁, Nat.shiftRight_eq_div_pow]
  have e₃ : (s₃.gpr .eax).toNat = (a + 127) / 128 := by rw [u₃.other _ (by decide), e₂]
  have m₃ : (s₃.gpr .edx).toNat = dMul g := by rw [u₃.gpr]; exact VG.Proof.MlDsa.X86.Round.ofNat_small (by omega)
  have hp : (a + 127) / 128 * dMul g ≤ 65473 * 11275 := Nat.mul_le_mul (by omega) hM
  refine VG.Proof.MlDsa.X86.Round.wp_mulSmall (by rw [e₃, m₃]; omega) fun s₄ o₄ v₄ => wp_addi fun s₅ u₅ =>
    wp_shr (VG.Proof.MlDsa.X86.Round.dShift_range g) fun s₆ u₆ _ => c s₆ ?_ ?_
  · refine ((((VG.Proof.MlDsa.X86.Round.updOnly u₁ |>.trans (VG.Proof.MlDsa.X86.Round.updOnly u₂)).trans (VG.Proof.MlDsa.X86.Round.updOnly u₃)).trans o₄).trans
      ((VG.Proof.MlDsa.X86.Round.updOnly u₅).trans (VG.Proof.MlDsa.X86.Round.updOnly u₆))).mono ?_
    intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (((h | h) | h) | h | h) | h | h <;> simp [h]
  · rw [u₆.gpr, BitVec.toNat_ushiftRight, u₅.gpr, BitVec.toNat_add, v₄, e₃, m₃, VG.Proof.MlDsa.X86.Round.ofNat_small (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, hbF_eq hg (by rw [VG.Proof.MlDsa.Round.q_eq]; exact haq), VG.Proof.MlDsa.X86.Round.dMul_eq,
      VG.Proof.MlDsa.X86.Round.dAdd_eq, VG.Proof.MlDsa.X86.Round.dShift_eq]

/-- `hb g` leaves `hbF g a % hbM g` (the `r₁` of `Decompose(a)`) in `eax` from `a < q` there,
changing only `eax`, `edx` and the flags. -/
theorem hb_spec {g : Nat} (hg : g ∈ gamma2s) {is : List Instr} {s : State} {P : State → Prop} {a : Nat}
    (ha : (s.gpr .eax).toNat = a) (haq : a < q)
    (c : ∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = hbF g a % hbM g → WP isa (.block is) s' P) :
    WP isa (.block (hb g ++ is)) s P := by
  rw [hb, List.append_assoc]
  refine VG.Proof.MlDsa.X86.Round.hbRaw_spec hg ha haq fun s₁ o₁ v₁ => ?_
  have hf := hbF_le hg haq
  have hm : 16 ≤ hbM g ∧ hbM g ≤ 44 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  have hk : (BitVec.ofNat 32 (dMod g)).toNat = hbM g := by rw [VG.Proof.MlDsa.X86.Round.dMod_eq hg]; exact VG.Proof.MlDsa.X86.Round.ofNat_small (by omega)
  refine VG.Proof.MlDsa.X86.Round.condAdd_spec (by decide) (X := BitVec.ofNat 32 (dMod g)) rfl (by rw [hk, v₁]; omega)
    fun s₂ o₂ v₂ => c s₂ ((o₁.trans o₂).mono fun r hr => ?_) ?_
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (h | h) | (h | h) <;> simp [h]
  · rw [v₂, v₁, hk]
    unfold VG.Proof.MlDsa.X86.Round.condAddN
    split
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

end VG.Proof.MlDsa.X86.Round

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Round.Common`. -/
section

/-!
# ML-DSA on x86 (32-bit): what the rounding functions share

The arguments of a leaf (`Impl.MlKem.X86.leaf`) after its push (`arg_P0`), the
coefficients of the polynomials at pointers advanced by 4 per iteration
(`ea_cf`), and the coefficients of input polynomials, which the functions
never write (`in_keep`).
-/

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_)
open VG.Spec.MlDsa (q gamma2s coeffAt Reduced)
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_frame n_eq mem_gamma2s)
open VG.Proof.MlKem.X86 (E0 P0 P0_esp P0_wr frameR retR saveRegs_len ea_add toNat_ofNat32)

/-- The stack below the return address, as the contracts state it. -/
abbrev stkR (s₀ : State) : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩

/-- The pointer argument `i`, as an address. -/
abbrev pA (s₀ : State) (i : Nat) : Addr := (arg s₀ i).setWidth 64

/-- The `n` argument words. -/
abbrev aR (s₀ : State) (n : Nat) : Region := ⟨argAddr s₀ 0, 4 * n⟩

theorem stk_eq {s₀ : State} (h : 16 ≤ (E0 s₀).toNat) : VG.Proof.MlDsa.X86.Round.stkR s₀ = frameR s₀ := by
  simp only [VG.Proof.MlDsa.X86.Round.stkR, frameR, below]; rw [Taint.sub_setWidth h]

/-- The push changes nothing of a region apart from the frame. -/
theorem P0_mem {s₀ : State} (h : 16 ≤ (E0 s₀).toNat) : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := Impl.MlKem.X86.saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact h)
  rw [saveRegs_len] at hf
  exact hf

theorem arg_contains {s₀ : State} {n i : Nat} (hi : i < n) (hfit : (E0 s₀).toNat + 4 + 4 * n ≤ 2 ^ 32) :
    (VG.Proof.MlDsa.X86.Round.aR s₀ n).Contains (argAddr s₀ i) 4 := by
  simp only [argAddr, Region.Contains, E0] at hfit ⊢
  bv_omega

/-- Argument `i` of `n`, after the leaf's push: its address `[esp + 20 + 4i]`, and its value. -/
theorem arg_P0 {s₀ : State} {n i : Nat} (hi : i < n) (hsp : 16 ≤ (E0 s₀).toNat)
    (hfit : (E0 s₀).toNat + 4 + 4 * n ≤ 2 ^ 32) (hin : VG.Proof.MlDsa.X86.Round.aR s₀ n ∈ s₀.rd ++ s₀.wr)
    (hstk : (VG.Proof.MlDsa.X86.Round.stkR s₀).Disjoint (VG.Proof.MlDsa.X86.Round.aR s₀ n)) :
    ((P0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i ∧
      InRegions ((P0 s₀).rd ++ (P0 s₀).wr) (argAddr s₀ i) 4 ∧
      (P0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have hc := VG.Proof.MlDsa.X86.Round.arg_contains hi hfit
  refine ⟨?_, ⟨VG.Proof.MlDsa.X86.Round.aR s₀ n, ?_, hc⟩, ?_⟩
  · rw [P0_esp]; simp only [argAddr, E0]; congr 1; bv_omega
  · rw [pushed_rd, P0_wr]
    rcases List.mem_append.mp hin with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  · exact (VG.Proof.MlDsa.X86.Round.P0_mem hsp).readW hc (by simpa [← VG.Proof.MlDsa.X86.Round.stk_eq hsp] using hstk.symm) (by decide)

/-- Coefficient `k` at the pointer `x + 4k`. -/
theorem ea_cf {x : BitVec 32} (hx : x.toNat + 1024 ≤ 2 ^ 32) {k : Nat} (hk : k < 256) :
    (x + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 = VG.Proof.MlDsa.Round.coeffAddr (x.setWidth 64) k := by
  rw [ea_add (by omega), Nat.add_zero]

/-- A polynomial apart from the frame and the regions written keeps its coefficients. -/
theorem in_keep {s₀ : State} {W : List Region} {m : Mem} (hsp : 16 ≤ (E0 s₀).toNat)
    (hf : Frame W (P0 s₀).mem m) {p : Addr} (hstk : (VG.Proof.MlDsa.X86.Round.stkR s₀).Disjoint (pR p))
    (hw : ∀ r ∈ W, (pR p).Disjoint r) {k : Nat} (hk : k < 256) :
    coeffAt m p k = coeffAt s₀.mem p k := by
  rw [VG.Proof.MlDsa.Round.coeffAt_frame hf hw (by rw [VG.Proof.MlDsa.Round.n_eq]; exact hk), VG.Proof.MlDsa.Round.coeffAt_frame (VG.Proof.MlDsa.X86.Round.P0_mem hsp) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [← VG.Proof.MlDsa.X86.Round.stk_eq hsp]; exact hstk.symm) (by rw [VG.Proof.MlDsa.Round.n_eq]; exact hk)]

theorem inRd {s : State} {a : Addr} (h : InRegions s.wr a 4) : InRegions (s.rd ++ s.wr) a 4 :=
  let ⟨r, hr, c⟩ := h; ⟨r, List.mem_append_right _ hr, c⟩

/-- `x - k` is zero exactly when `x = k`. -/
theorem sub_beq_zero' (x k : BitVec 32) : (x - k == 0) = (x == k) := by
  by_cases h : x = k
  · subst h; simp
  · have : x - k ≠ 0 := fun e => h (by bv_omega)
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]

theorem gamma_cases {g : BitVec 32} (hg : g.toNat ∈ gamma2s) :
    (g == BitVec.ofNat 32 g32) = true ∧ g.toNat = g32 ∨ (g == BitVec.ofNat 32 g32) = false ∧ g.toNat = g88 := by
  rcases mem_gamma2s hg with e | e
  · refine .inr ⟨?_, e⟩
    rw [beq_eq_false_iff_ne]; intro h; rw [h] at e; exact absurd e (by decide)
  · refine .inl ⟨?_, e⟩
    rw [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (e.trans rfl)

theorem g32_mem : g32 ∈ gamma2s := by decide
theorem g88_mem : g88 ∈ gamma2s := by decide

end VG.Proof.MlDsa.X86.Round

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Round.Bits`. -/
section

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_high_bits` and `vg_mldsa_low_bits`

Both compare `γ₂` with `(q - 1)/32` and run, for the value they found, the
loop `cntLoop` of a core that computes `eax ← V a` from the coefficient `a =
[esi]` (`Core1`: `hbCore_spec`, `lbCore_spec`) and `cntTail`, which stores it
to `[edi]`. The loop is proven once for any core (`bits_piece`), with the
value `V s₀` of the entry state, as `γ₂` is (`E s₀` holds in the branch).
-/

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_ leaf)
open VG.Spec.MlDsa (q gamma2s coeffAt Reduced polyAt PolyIs NatPolyIs highBits lowBits ofInt
  highBitsContract lowBitsContract bitsSig)
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_frame coeffAt_writeW n_eq hbF hbM hbF_le
  hbM_mul mem_gamma2s q_eq highBits_eq lowBits_val polyAt_val natPolyIs_of_toNat polyIs_of_toNat map_get)
open VG.Proof.MlKem.X86 (Only E0 P0 P0_esp P0_wr frameR retR LeafPost LeafEnd Piece satState wp_movm
  toNat_ofNat32 eq_ofNat_of_toNat ptr_next cnt_next cnt_ne)

/-! ## The cores -/

/-- `core` leaves `V a` in `eax` from `a = [esi]` (`a < q`), changing only `eax`, `edx`, `ebx` and
the flags. -/
def Core1 (core : List Instr) (V : Nat → Nat) : Prop :=
  ∀ (is : List Instr) (s : State) (P : State → Prop) (a : Nat), a < q →
    InRegions (s.rd ++ s.wr) (s.ea (at_ .esi 0)) 4 → (s.mem.readW (s.ea (at_ .esi 0)) 32).toNat = a →
    (∀ s', Only [.eax, .edx, .ebx] s s' → (s'.gpr .eax).toNat = V a → WP isa (.block is) s' P) →
    WP isa (.block (core ++ is)) s P

/-- The `r₁` of `Decompose`. -/
def hbV (g a : Nat) : Nat := hbF g a % hbM g

/-- The `r₀` of `Decompose`, modulo `q`. -/
def lbV (g a : Nat) : Nat := VG.Proof.MlDsa.X86.Round.condAddN a (hbF g a % hbM g * (2 * g)) q

theorem hbCore_spec {g : Nat} (hg : g ∈ gamma2s) : VG.Proof.MlDsa.X86.Round.Core1 (hbCore g) (VG.Proof.MlDsa.X86.Round.hbV g) := by
  intro is s P a ha hin hv c
  rw [hbCore, List.cons_append]
  refine wp_movm hin (VG.Proof.MlDsa.X86.Round.hb_spec hg (a := a) (by simp [State.setReg, hv]) ha fun s₁ o₁ v₁ => c s₁ ?_ v₁)
  exact (VG.Proof.MlKem.X86.Only.setReg s .eax _ |>.trans o₁).mono fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp [h]

theorem lbCore_eq (g : Nat) (is : List Instr) : lbCore g ++ is =
    .mov .eax (.mem (at_ .esi 0)) :: .mov .ebx (.reg .eax) :: (hb g ++
      (.mov .edx (.imm (BitVec.ofNat 32 (2 * g))) :: .mul .edx :: (condAdd .ebx (.reg .eax) .edx qImm ++
        (.mov .eax (.reg .ebx) :: is)))) := by
  simp only [lbCore, List.cons_append, List.nil_append, List.append_assoc]

theorem lbCore_spec {g : Nat} (hg : g ∈ gamma2s) : VG.Proof.MlDsa.X86.Round.Core1 (lbCore g) (VG.Proof.MlDsa.X86.Round.lbV g) := by
  intro is s P a ha hin hv c
  rw [VG.Proof.MlDsa.X86.Round.lbCore_eq]
  have hM := hbM_mul hg
  have hgl : 2 * g ≤ 523776 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  refine wp_movm hin (wp_mov fun s₁ u₁ => VG.Proof.MlDsa.X86.Round.hb_spec hg (a := a) ?_ ha fun s₂ o₂ v₂ => wp_movi fun s₃ u₃ => ?_)
  · rw [u₁.other _ (by decide)]; simp [State.setReg, hv]
  have hlt : hbF g a % hbM g < hbM g := Nat.mod_lt _ (by rcases mem_gamma2s hg with rfl | rfl <;> decide)
  have hle : hbF g a % hbM g * (2 * g) ≤ q - 1 := by
    rw [← hM]; exact Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
  have e₃ : (s₃.gpr .eax).toNat = hbF g a % hbM g := by rw [u₃.other _ (by decide), v₂]
  have m₃ : (s₃.gpr .edx).toNat = 2 * g := by rw [u₃.gpr]; exact toNat_ofNat32 (by omega)
  refine VG.Proof.MlDsa.X86.Round.wp_mulSmall (r := .edx) (by rw [e₃, m₃]; exact Nat.lt_of_le_of_lt hle (by rw [q_eq]; decide)) fun s₄ o₄ v₄ => ?_
  have b₄ : (s₄.gpr .ebx).toNat = a := by
    rw [o₄.gpr _ (by decide), u₃.other _ (by decide), o₂.gpr _ (by decide), u₁.gpr]
    simp [State.setReg, hv]
  refine VG.Proof.MlDsa.X86.Round.condAdd_spec (by decide) (X := s₄.gpr .eax) rfl
    (by rw [v₄, e₃, m₃, b₄, show qImm.toNat = q from rfl]; omega)
    fun s₅ o₅ v₅ => wp_mov fun s₆ u₆ => c s₆ ?_ ?_
  · refine ((((((VG.Proof.MlKem.X86.Only.setReg s .eax _).trans (VG.Proof.MlDsa.X86.Round.updOnly u₁)).trans o₂).trans
      (VG.Proof.MlDsa.X86.Round.updOnly u₃)).trans o₄).trans (o₅.trans (VG.Proof.MlDsa.X86.Round.updOnly u₆))).mono fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (((((h | h) | h | h) | h) | h | h) | (h | h) | h) <;> simp [h]
  · rw [u₆.gpr, v₅, b₄, v₄, e₃, m₃, VG.Proof.MlDsa.X86.Round.lbV]
    rfl

/-! ## The precondition -/

section
variable (s₀ : State)
/-- The input `r`. -/
abbrev rP : BitVec 32 := arg s₀ 0
/-- The output. -/
abbrev oP : BitVec 32 := arg s₀ 2
end

structure BitsPre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 12 ≤ 2 ^ 32
  rd : s₀.rd = [pR (VG.Proof.MlDsa.X86.Round.pA s₀ 0)]
  wr : s₀.wr = [pR (VG.Proof.MlDsa.X86.Round.pA s₀ 2), VG.Proof.MlDsa.X86.Round.aR s₀ 3]
  r_o : (pR (VG.Proof.MlDsa.X86.Round.pA s₀ 0)).Disjoint (pR (VG.Proof.MlDsa.X86.Round.pA s₀ 2))
  r_a : (pR (VG.Proof.MlDsa.X86.Round.pA s₀ 0)).Disjoint (VG.Proof.MlDsa.X86.Round.aR s₀ 3)
  o_a : (pR (VG.Proof.MlDsa.X86.Round.pA s₀ 2)).Disjoint (VG.Proof.MlDsa.X86.Round.aR s₀ 3)
  ret_r : (retR s₀).Disjoint (pR (VG.Proof.MlDsa.X86.Round.pA s₀ 0))
  ret_o : (retR s₀).Disjoint (pR (VG.Proof.MlDsa.X86.Round.pA s₀ 2))
  ret_a : (retR s₀).Disjoint (VG.Proof.MlDsa.X86.Round.aR s₀ 3)
  stk_r : (VG.Proof.MlDsa.X86.Round.stkR s₀).Disjoint (pR (VG.Proof.MlDsa.X86.Round.pA s₀ 0))
  stk_o : (VG.Proof.MlDsa.X86.Round.stkR s₀).Disjoint (pR (VG.Proof.MlDsa.X86.Round.pA s₀ 2))
  stk_a : (VG.Proof.MlDsa.X86.Round.stkR s₀).Disjoint (VG.Proof.MlDsa.X86.Round.aR s₀ 3)
  r_fit : (VG.Proof.MlDsa.X86.Round.rP s₀).toNat + 1024 ≤ 2 ^ 32
  o_fit : (VG.Proof.MlDsa.X86.Round.oP s₀).toNat + 1024 ≤ 2 ^ 32
  g2 : (arg s₀ 1).toNat ∈ gamma2s
  r_red : Reduced s₀.mem (VG.Proof.MlDsa.X86.Round.pA s₀ 0)

theorem BitsPre.of_hb {s₀ : State} (h : (highBitsContract X86.abi 16).pre s₀) : VG.Proof.MlDsa.X86.Round.BitsPre s₀ := by
  sig_pre [highBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem BitsPre.of_lb {s₀ : State} (h : (lowBitsContract X86.abi 16).pre s₀) : VG.Proof.MlDsa.X86.Round.BitsPre s₀ := by
  sig_pre [lowBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-- The public data: the stack pointer, the pointers and `γ₂`. -/
def BitsPub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2

/-! ## The prologue -/

/-- After `bitsInit`. -/
structure BS1 (s₀ s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = VG.Proof.MlDsa.X86.Round.rP s₀
  edi : s.gpr .edi = VG.Proof.MlDsa.X86.Round.oP s₀
  zf : s.zf = some (arg s₀ 1 == BitVec.ofNat 32 g32)

theorem init_piece : Piece VG.Proof.MlDsa.X86.Round.BitsPre VG.Proof.MlDsa.X86.Round.BitsPub (fun s₀ s => s = P0 s₀) VG.Proof.MlDsa.X86.Round.BS1 (.block bitsInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) (by taint_decide)
  · subst e
    have hin : VG.Proof.MlDsa.X86.Round.aR s₀ 3 ∈ s₀.rd ++ s₀.wr := by simp [hp.wr]
    obtain ⟨a₀, i₀, v₀⟩ := VG.Proof.MlDsa.X86.Round.arg_P0 (i := 0) (by omega) hp.sp hp.sp' hin hp.stk_a
    obtain ⟨a₁, i₁, v₁⟩ := VG.Proof.MlDsa.X86.Round.arg_P0 (i := 1) (by omega) hp.sp hp.sp' hin hp.stk_a
    obtain ⟨a₂, i₂, v₂⟩ := VG.Proof.MlDsa.X86.Round.arg_P0 (i := 2) (by omega) hp.sp hp.sp' hin hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd, Nat.reduceMul] at a₀ a₁ a₂
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, bitsInit, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags, Option.map_some,
      Option.bind_some, a₀, a₁, a₂, i₀, i₁, i₂, v₀, v₁, v₂, Option.some.injEq,
      exists_eq_left']
    exact ⟨by simp, rfl, rfl, rfl, by simp, by simp, by rw [VG.Proof.MlDsa.X86.Round.sub_beq_zero']⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

/-! ## The loop -/

/-- After `k` coefficients, with the values `V`. -/
structure BInv (V : Nat → Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = VG.Proof.MlDsa.X86.Round.rP s₀ + BitVec.ofNat 32 (4 * k)
  edi : s.gpr .edi = VG.Proof.MlDsa.X86.Round.oP s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  frame : Frame [pR (VG.Proof.MlDsa.X86.Round.pA s₀ 2)] (P0 s₀).mem s.mem
  out : ∀ i < k, coeffAt s.mem (VG.Proof.MlDsa.X86.Round.pA s₀ 2) i = BitVec.ofNat 32 (V (coeffAt s₀.mem (VG.Proof.MlDsa.X86.Round.pA s₀ 0) i).toNat)

theorem addr_cf {x : BitVec 32} (hx : x.toNat + 1024 ≤ 2 ^ 32) {k : Nat} (hk : k < 256) :
    addr (x + BitVec.ofNat 32 (4 * k)) 0 = coeffAddr (x.setWidth 64) k := VG.Proof.MlDsa.X86.Round.ea_cf hx hk

theorem bits_step {core : List Instr} {V : Nat → Nat} (hc : VG.Proof.MlDsa.X86.Round.Core1 core V)
    {s₀ : State} (hp : VG.Proof.MlDsa.X86.Round.BitsPre s₀) {k : Nat} (hk : k < 256) {s : State} (h : VG.Proof.MlDsa.X86.Round.BInv V s₀ k s) :
    WP isa (.block (core ++ cntTail)) s fun s' =>
      VG.Proof.MlDsa.X86.Round.BInv V s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have ef : s.ea (at_ .esi 0) = coeffAddr (VG.Proof.MlDsa.X86.Round.pA s₀ 0) k := by rw [State.ea, at_, h.esi]; exact VG.Proof.MlDsa.X86.Round.ea_cf hp.r_fit hk
  have hin : InRegions (s.rd ++ s.wr) (coeffAddr (VG.Proof.MlDsa.X86.Round.pA s₀ 0) k) 4 := by
    rw [h.rd, h.wr, pushed_rd, P0_wr, hp.rd]
    exact ⟨_, by simp, coeff_contains _ (by rw [n_eq]; exact hk)⟩
  have hkeep : coeffAt s.mem (VG.Proof.MlDsa.X86.Round.pA s₀ 0) k = coeffAt s₀.mem (VG.Proof.MlDsa.X86.Round.pA s₀ 0) k :=
    VG.Proof.MlDsa.X86.Round.in_keep hp.sp h.frame hp.stk_r (by simpa using hp.r_o) hk
  have ha := hp.r_red k (by rw [n_eq]; exact hk)
  refine hc _ s _ _ ha (by rw [ef]; exact hin) (by rw [ef, ← VG.Proof.MlDsa.Round.coeffAt_eq, hkeep])
    fun s₁ o₁ v₁ => ?_
  have edi₁ : s₁.gpr .edi = VG.Proof.MlDsa.X86.Round.oP s₀ + BitVec.ofNat 32 (4 * k) := by rw [o₁.gpr _ (by decide), h.edi]
  have out : InRegions s₁.wr (addr (VG.Proof.MlDsa.X86.Round.oP s₀ + BitVec.ofNat 32 (4 * k)) 0) 4 := by
    rw [VG.Proof.MlDsa.X86.Round.addr_cf hp.o_fit hk, o₁.wr, h.wr, P0_wr, hp.wr]
    exact ⟨_, by simp, coeff_contains _ (by rw [n_eq]; exact hk)⟩
  refine wp_stm edi₁ out fun s₂ m₂ => wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ =>
    wp_subi fun s₅ u₅ _ z₅ => WP.block_nil_iff.mpr ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, o₁.gpr _ (by decide),
      h.esp]
  · rw [u₅.rd, u₄.rd, u₃.rd, m₂.rd, o₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, m₂.wr, o₁.wr, h.wr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, m₂.gpr, o₁.gpr _ (by decide), h.esi]
    exact ptr_next _ _ 4
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), m₂.gpr, edi₁]
    exact ptr_next _ _ 4
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, o₁.gpr _ (by decide), h.ecx]
    exact cnt_next hk
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, VG.Proof.MlDsa.X86.Round.addr_cf hp.o_fit hk, o₁.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ (by rw [n_eq]; exact hk))
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, VG.Proof.MlDsa.X86.Round.addr_cf hp.o_fit hk, o₁.mem,
      coeffAt_writeW _ _ (by rw [n_eq]; omega) (by rw [n_eq]; exact hk)]
    by_cases e : k = i
    · subst e
      rw [ite_eq_left rfl]
      exact eq_ofNat_of_toNat v₁
    · rw [ite_eq_right e]; exact h.out i (by omega)
  · simp only [eval, z₅, Option.map_some]
    rw [u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, o₁.gpr _ (by decide), h.ecx]
    exact cnt_ne hk (by decide)

theorem bits_piece {core : List Instr} {V : Nat → Nat} (hc : VG.Proof.MlDsa.X86.Round.Core1 core V)
    (E : State → Prop) {hh : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (core ++ cntTail)) hh).isSome = true) :
    Piece VG.Proof.MlDsa.X86.Round.BitsPre VG.Proof.MlDsa.X86.Round.BitsPub (fun s₀ s => VG.Proof.MlDsa.X86.Round.BS1 s₀ s ∧ E s₀) (fun s₀ s => VG.Proof.MlDsa.X86.Round.BInv V s₀ 256 s ∧ E s₀)
      (cntLoop (core ++ cntTail)) := by
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Round.BInv V s₀ 0 s ∧ E s₀) ?_ ?_
  · refine Piece.taint [] (fun s₀ s hp ⟨h, he⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by taint_decide)
    refine wp_movi fun s₁ u₁ => WP.block_nil_iff.mpr ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega)⟩, he⟩
    · rw [u₁.other _ (by decide), h.esp]
    · rw [u₁.rd, h.rd]
    · rw [u₁.wr, h.wr]
    · rw [u₁.other _ (by decide), h.esi]; simp
    · rw [u₁.other _ (by decide), h.edi]; simp
    · rw [u₁.gpr]; rfl
    · rw [u₁.mem, h.mem]; exact Frame.refl _ _
  · exact Piece.countLoop (by decide) (fun k s₀ s => VG.Proof.MlDsa.X86.Round.BInv V s₀ k s ∧ E s₀) [.esp, .esi, .edi, .ecx]
      (fun k hk s₀ s hp ⟨h, he⟩ => (VG.Proof.MlDsa.X86.Round.bits_step hc hp hk h).mono fun _ ⟨h', c'⟩ => ⟨⟨h', he⟩, c'⟩)
      (fun k _ s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
        · rw [h.esi, h'.esi, VG.Proof.MlDsa.X86.Round.rP, VG.Proof.MlDsa.X86.Round.rP, hq.2.1]
        · rw [h.edi, h'.edi, VG.Proof.MlDsa.X86.Round.oP, VG.Proof.MlDsa.X86.Round.oP, hq.2.2.2]
        · rw [h.ecx, h'.ecx]) ht

/-! ## The functions -/

/-- `γ₂` is `(q - 1)/32`: the branch the code takes. -/
def isG32 (s₀ : State) : Bool := arg s₀ 1 == BitVec.ofNat 32 g32

/-- Both branches, for the core `core g` computing `Vf g`. -/
theorem body_piece {core : Nat → List Instr} {Vf : Nat → Nat → Nat} (hc : ∀ g ∈ gamma2s, VG.Proof.MlDsa.X86.Round.Core1 (core g) (Vf g))
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (core g32 ++ cntTail)) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (core g88 ++ cntTail)) h₂).isSome = true) :
    Piece VG.Proof.MlDsa.X86.Round.BitsPre VG.Proof.MlDsa.X86.Round.BitsPub (fun s₀ s => s = P0 s₀) (fun s₀ s => VG.Proof.MlDsa.X86.Round.BInv (Vf (arg s₀ 1).toNat) s₀ 256 s)
      (.seq (.block bitsInit) (.ite .e (cntLoop (core g32 ++ cntTail)) (cntLoop (core g88 ++ cntTail)))) := by
  refine Piece.seq VG.Proof.MlDsa.X86.Round.init_piece (Piece.ite VG.Proof.MlDsa.X86.Round.isG32 (fun s₀ s _ h => h.zf) (fun s₀ s₀' _ _ hq => by
    simp only [VG.Proof.MlDsa.X86.Round.isG32, hq.2.2.1]) ?_ ?_)
  · refine (VG.Proof.MlDsa.X86.Round.bits_piece (hc g32 VG.Proof.MlDsa.X86.Round.g32_mem) (fun s₀ => VG.Proof.MlDsa.X86.Round.isG32 s₀ = true) t₁).mono (fun _ _ _ h => h)
      fun s₀ s hp ⟨h, he⟩ => ?_
    rcases VG.Proof.MlDsa.X86.Round.gamma_cases hp.g2 with ⟨_, e⟩ | ⟨e', _⟩
    · rw [e]; exact h
    · rw [VG.Proof.MlDsa.X86.Round.isG32, e'] at he; exact absurd he (by decide)
  · refine (VG.Proof.MlDsa.X86.Round.bits_piece (hc g88 VG.Proof.MlDsa.X86.Round.g88_mem) (fun s₀ => VG.Proof.MlDsa.X86.Round.isG32 s₀ = false) t₂).mono (fun _ _ _ h => h)
      fun s₀ s hp ⟨h, he⟩ => ?_
    rcases VG.Proof.MlDsa.X86.Round.gamma_cases hp.g2 with ⟨e', _⟩ | ⟨_, e⟩
    · rw [VG.Proof.MlDsa.X86.Round.isG32, e'] at he; exact absurd he (by decide)
    · rw [e]; exact h

theorem leaf_piece {core : Nat → List Instr} {Vf : Nat → Nat → Nat} (hc : ∀ g ∈ gamma2s, VG.Proof.MlDsa.X86.Round.Core1 (core g) (Vf g))
    (hsp : NoSp (.seq (.block bitsInit) (.ite .e (cntLoop (core g32 ++ cntTail)) (cntLoop (core g88 ++ cntTail)))))
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (core g32 ++ cntTail)) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (core g88 ++ cntTail)) h₂).isSome = true) :
    Piece VG.Proof.MlDsa.X86.Round.BitsPre VG.Proof.MlDsa.X86.Round.BitsPub (fun s₀ s => s = s₀)
      (fun s₀ s' => LeafPost (fun s => VG.Proof.MlDsa.X86.Round.BInv (Vf (arg s₀ 1).toNat) s₀ 256 s) s₀ s')
      (leaf (.seq (.block bitsInit) (.ite .e (cntLoop (core g32 ++ cntTail)) (cntLoop (core g88 ++ cntTail))))) :=
  Piece.leaf (fun s₀ => [pR (VG.Proof.MlDsa.X86.Round.pA s₀ 2)]) hsp (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← VG.Proof.MlDsa.X86.Round.stk_eq hp.sp]; exact hp.stk_o, hp.ret_o⟩)
    (fun _ _ _ _ hq => hq.1)
    ((VG.Proof.MlDsa.X86.Round.body_piece hc t₁ t₂).mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem hbV_lt {g : Nat} (hg : g ∈ gamma2s) (a : Nat) : VG.Proof.MlDsa.X86.Round.hbV g a < 2 ^ 32 := by
  have := Nat.mod_lt (hbF g a) (show hbM g > 0 by rcases mem_gamma2s hg with rfl | rfl <;> decide)
  have : hbM g ≤ 44 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  unfold VG.Proof.MlDsa.X86.Round.hbV; omega

theorem lbV_lt {g : Nat} {a : Nat} (ha : a < q) : VG.Proof.MlDsa.X86.Round.lbV g a < 2 ^ 32 := by
  have hq : q = 8380417 := rfl
  unfold VG.Proof.MlDsa.X86.Round.lbV VG.Proof.MlDsa.X86.Round.condAddN; split <;> omega

/-- Memory with the arguments `0x400`, `(q - 1)/32` and `0` at `0x5004`. -/
def bitsSatMem : Mem := fun a => if a = 0x5005 then 4 else if a = 0x5009 then 0xff else if a = 0x500a then 3 else 0

theorem bitsSat_zero (a : Addr) (ha : a.toNat < 0x5000) : VG.Proof.MlDsa.X86.Round.bitsSatMem a = 0 := by
  simp only [VG.Proof.MlDsa.X86.Round.bitsSatMem]
  rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)]

theorem reduced_zero {m : Mem} (hm : ∀ a : Addr, a.toNat < 0x5000 → m a = 0) (p : Nat)
    (hp : p + 1024 ≤ 0x5000) : Reduced m (BitVec.ofNat 64 p) := fun i hi => by
  rw [VG.Proof.MlDsa.Arith.coeffAt_congr (m' := m) (m := fun _ => 0) (fun k hk => hm _ (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)) hi]
  simp [VG.Spec.MlDsa.coeffAt, Mem.readW, Mem.read]

theorem highBits_verified : Verified X86.target highBits (highBitsContract X86.abi 16) := by
  refine Piece.verified (((VG.Proof.MlDsa.X86.Round.leaf_piece (fun g hg => VG.Proof.MlDsa.X86.Round.hbCore_spec hg) (NoSp.of_all (by decide +kernel))
    (by taint_decide) (by taint_decide)).pre_mono (fun _ h => BitsPre.of_hb h) fun s s' _ _ h => by
      sig_pub [highBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [highBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    have hp := BitsPre.of_hb h₀
    refine natPolyIs_of_toNat fun i hi => ?_
    rw [hinv.out i hi, map_get _ _ hi, highBits_eq hp.g2, polyAt_val hp.r_red hi, toNat_ofNat32 (VG.Proof.MlDsa.X86.Round.hbV_lt hp.g2 _)]
    rfl
  · let st := satState VG.Proof.MlDsa.X86.Round.bitsSatMem [⟨0x400, 1024⟩] [⟨0, 1024⟩, ⟨0x5004, 12⟩]
    have a0 : arg st 0 = 0x400 := by decide
    have a1 : arg st 1 = 261888 := by decide
    have a2 : arg st 2 = 0 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [highBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, VG.Proof.MlDsa.X86.Round.reduced_zero VG.Proof.MlDsa.X86.Round.bitsSat_zero 0x400 (by decide)⟩
    all_goals first
      | exact Region.disjoint_of_sep (by decide)
      | decide

theorem lowBits_verified : Verified X86.target lowBits (lowBitsContract X86.abi 16) := by
  refine Piece.verified (((VG.Proof.MlDsa.X86.Round.leaf_piece (fun g hg => VG.Proof.MlDsa.X86.Round.lbCore_spec hg) (NoSp.of_all (by decide +kernel))
    (by taint_decide) (by taint_decide)).pre_mono (fun _ h => BitsPre.of_lb h) fun s s' _ _ h => by
      sig_pub [lowBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [lowBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    have hp := BitsPre.of_lb h₀
    refine polyIs_of_toNat fun i hi => ?_
    have ha := hp.r_red i hi
    rw [hinv.out i hi, map_get _ _ hi, lowBits_val hp.g2, polyAt_val hp.r_red hi, toNat_ofNat32 (VG.Proof.MlDsa.X86.Round.lbV_lt ha)]
    rfl
  · let st := satState VG.Proof.MlDsa.X86.Round.bitsSatMem [⟨0x400, 1024⟩] [⟨0, 1024⟩, ⟨0x5004, 12⟩]
    have a0 : arg st 0 = 0x400 := by decide
    have a1 : arg st 1 = 261888 := by decide
    have a2 : arg st 2 = 0 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [lowBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, VG.Proof.MlDsa.X86.Round.reduced_zero VG.Proof.MlDsa.X86.Round.bitsSat_zero 0x400 (by decide)⟩
    all_goals first
      | exact Region.disjoint_of_sep (by decide)
      | decide

end VG.Proof.MlDsa.X86.Round

end
