module

import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.Arith.Mem
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.MlKem.X86.Leaf
public import VerifiedGarbage.Proof.MlDsa.Round.Mem
public import VerifiedGarbage.Impl.MlDsa.X86.Round.Round
public import VerifiedGarbage.Proof.MlKem.X86.Common
public import VerifiedGarbage.Proof.MlDsa.Round.Decompose
meta import VerifiedGarbage.Proof.MlKem.X86.Leaf
meta import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Impl.MlDsa.X86.Round.Round
meta import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlKem.X86.Red
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.MlKem.X86.Red
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `MlDsa.X86.Round.Arith`, which this module and modules that import it used -/

section

/-!
# ML-DSA on x86 (32-bit): what the rounding code computes

Continuation-style rules for the pieces of `Impl/MlDsa/X86/Round/Round.lean`:
`condAdd` leaves `condAddN r x k` (`condAdd_spec`), `hbRaw g` leaves `⌊(a + γ₂ -
1)/(2γ₂)⌋` (`hbRaw_spec`, by `hbF_eq` of `Proof/MlDsa/Round/Decompose.lean`)
and `hb g` its remainder modulo `m` (`hb_spec`), each changing only the
registers it names (`Only`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_)
open VG.Spec.MlDsa (q)
open VG.Proof.MlDsa (gamma2s)
open VG.Proof.MlDsa.Round (hbF hbM q_eq mem_gamma2s hbF_le hbF_eq)
open VG.Proof.MlKem.X86 (Only wp_cons wp_mul execMul_eax execMul_other toNat_ofNat32 eq_ofNat_of_toNat)

theorem updOnly {s s' : State} {d : Reg} {v : BitVec 32} (h : Upd s s' d v) : Only [d] s s' :=
  ⟨fun r hr => h.other r (by simpa using hr), h.mem, h.rd, h.wr⟩

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
    (by simp [exec, execAlu, readSrc_mem hb hin]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

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
      condAddN r.toNat x.toNat k.toNat := by
  unfold condAddN
  have := r.isLt; have := x.isLt; have := k.isLt
  by_cases h : r.toNat < x.toNat
  · simp only [h, decide_true, ite_true, BitVec.allOnes_and, BitVec.toNat_add, BitVec.toNat_sub]
    omega_using [hx, h]
  · have e : r - x + ((if decide (r.toNat < x.toNat) = true then BitVec.allOnes 32 else 0) &&& k) = r - x := by
      simp [h]
    rw [e, BitVec.toNat_sub, ite_eq_right h]
    omega_using [h]

/-- `condAdd r x t k`, from `x` read as `X`: `r ← condAddN r X k`, changing only `r`, `t` and the
flags. -/
theorem condAdd_spec {r t : Reg} (hrt : r ≠ t) {x : Src} {k X : BitVec 32} {is : List Instr} {s : State}
    {P : State → Prop} (hx : readSrc s x = some X) (hX : X.toNat ≤ (s.gpr r).toNat + k.toNat)
    (c : ∀ s', Only [r, t] s s' → (s'.gpr r).toNat = condAddN (s.gpr r).toNat X.toNat k.toNat →
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
    exact condAdd_val _ _ _ hX

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
  rw [q_eq] at haq
  have hM : dMul g ≤ 11275 := by unfold dMul; split <;> decide
  have hA : dAdd g ≤ 2 ^ 23 := by unfold dAdd; split <;> decide
  simp only [hbRaw, List.cons_append, List.nil_append]
  refine wp_addi fun s₁ u₁ => wp_shr (by decide) fun s₂ u₂ _ => wp_movi fun s₃ u₃ => ?_
  have e₁ : (s₁.gpr .eax).toNat = a + 127 := by
    rw [u₁.gpr, BitVec.toNat_add, ha]; simp; omega_using [haq]
  have e₂ : (s₂.gpr .eax).toNat = (a + 127) / 128 := by
    rw [u₂.gpr, BitVec.toNat_ushiftRight, e₁, Nat.shiftRight_eq_div_pow]
  have e₃ : (s₃.gpr .eax).toNat = (a + 127) / 128 := by rw [u₃.other _ (by decide), e₂]
  have m₃ : (s₃.gpr .edx).toNat = dMul g := by rw [u₃.gpr]; exact ofNat_small (by omega_using [hM])
  have hp : (a + 127) / 128 * dMul g ≤ 65473 * 11275 := Nat.mul_le_mul (by omega_using [haq]) hM
  refine wp_mulSmall (by rw [e₃, m₃]; omega_using [hp]) fun s₄ o₄ v₄ => wp_addi fun s₅ u₅ =>
    wp_shr (dShift_range g) fun s₆ u₆ _ => c s₆ ?_ ?_
  · refine ((((updOnly u₁ |>.trans (updOnly u₂)).trans (updOnly u₃)).trans o₄).trans
      ((updOnly u₅).trans (updOnly u₆))).mono ?_
    intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (((h | h) | h) | h | h) | h | h <;> simp [h]
  · rw [u₆.gpr, BitVec.toNat_ushiftRight, u₅.gpr, BitVec.toNat_add, v₄, e₃, m₃, ofNat_small (by omega_using [hA]),
      Nat.mod_eq_of_lt (by omega_using [hA, hp]), Nat.shiftRight_eq_div_pow, hbF_eq hg (by rw [q_eq]; exact haq), dMul_eq,
      dAdd_eq, dShift_eq]

/-- `hb g` leaves `hbF g a % hbM g` (the `r₁` of `Decompose(a)`) in `eax` from `a < q` there,
changing only `eax`, `edx` and the flags. -/
theorem hb_spec {g : Nat} (hg : g ∈ gamma2s) {is : List Instr} {s : State} {P : State → Prop} {a : Nat}
    (ha : (s.gpr .eax).toNat = a) (haq : a < q)
    (c : ∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = hbF g a % hbM g → WP isa (.block is) s' P) :
    WP isa (.block (hb g ++ is)) s P := by
  rw [hb, List.append_assoc]
  refine hbRaw_spec hg ha haq fun s₁ o₁ v₁ => ?_
  have hf := hbF_le hg haq
  have hm : 16 ≤ hbM g ∧ hbM g ≤ 44 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  have hk : (BitVec.ofNat 32 (dMod g)).toNat = hbM g := by rw [dMod_eq hg]; exact ofNat_small (by omega_using [hm])
  refine condAdd_spec (by decide) (X := BitVec.ofNat 32 (dMod g)) rfl (by rw [hk, v₁]; omega_using [])
    fun s₂ o₂ v₂ => c s₂ ((o₁.trans o₂).mono fun r hr => ?_) ?_
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (h | h) | (h | h) <;> simp [h]
  · rw [v₂, v₁, hk]
    unfold condAddN
    split
    · rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_using []
    · rw [Nat.mod_eq_sub_mod (by omega_arith), Nat.mod_eq_of_lt (by omega_using [hf, hm])]

end VG.Proof.MlDsa.X86.Round

end

end

/-! ### `MlDsa.X86.Round.Common`, which this module and modules that import it used -/

section

/-!
# ML-DSA on x86 (32-bit): what the rounding functions share

The arguments of a leaf (`Impl.MlKem.X86.leaf`) after its push (`arg_P0`), the
coefficients of the polynomials at pointers advanced by 4 per iteration
(`ea_cf`), and the coefficients of input polynomials, which the functions
never write (`in_keep`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_)
open VG.Spec.MlDsa (q)
open VG.Proof.MlDsa (gamma2s coeffAt Reduced)
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_frame n_eq mem_gamma2s)
open VG.Proof.MlKem.X86 (E0 P0 P0_esp P0_wr frameR retR saveRegs_len ea_add toNat_ofNat32)

/-- The stack below the return address, as the contracts state it. -/
abbrev stkR (s₀ : State) : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩

/-- The pointer argument `i`, as an address. -/
abbrev pA (s₀ : State) (i : Nat) : Addr := (arg s₀ i).setWidth 64

/-- The `n` argument words. -/
abbrev aR (s₀ : State) (n : Nat) : Region := ⟨argAddr s₀ 0, 4 * n⟩

theorem stk_eq {s₀ : State} (h : 16 ≤ (E0 s₀).toNat) : stkR s₀ = frameR s₀ := by
  simp only [stkR, frameR, below]; rw [Taint.sub_setWidth h]

/-- The push changes nothing of a region apart from the frame. -/
theorem P0_mem {s₀ : State} (h : 16 ≤ (E0 s₀).toNat) : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := Impl.MlKem.X86.saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact h)
  rw [saveRegs_len] at hf
  exact hf

theorem arg_contains {s₀ : State} {n i : Nat} (hi : i < n) (hfit : (E0 s₀).toNat + 4 + 4 * n ≤ 2 ^ 32) :
    (aR s₀ n).Contains (argAddr s₀ i) 4 := by
  simp only [argAddr, Region.Contains, E0] at hfit ⊢
  bv_omega

/-- Argument `i` of `n`, after the leaf's push: its address `[esp + 20 + 4i]`, and its value. -/
theorem arg_P0 {s₀ : State} {n i : Nat} (hi : i < n) (hsp : 16 ≤ (E0 s₀).toNat)
    (hfit : (E0 s₀).toNat + 4 + 4 * n ≤ 2 ^ 32) (hin : aR s₀ n ∈ s₀.rd ++ s₀.wr)
    (hstk : (stkR s₀).Disjoint (aR s₀ n)) :
    ((P0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i ∧
      InRegions ((P0 s₀).rd ++ (P0 s₀).wr) (argAddr s₀ i) 4 ∧
      (P0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have hc := arg_contains hi hfit
  refine ⟨?_, ⟨aR s₀ n, ?_, hc⟩, ?_⟩
  · rw [P0_esp]; simp only [argAddr, E0]; congr 1; bv_omega
  · rw [pushed_rd, P0_wr]
    rcases List.mem_append.mp hin with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  · exact (P0_mem hsp).readW hc (by simpa [← stk_eq hsp] using hstk.symm) (by decide)

/-- Coefficient `k` at the pointer `x + 4k`. -/
theorem ea_cf {x : BitVec 32} (hx : x.toNat + 1024 ≤ 2 ^ 32) {k : Nat} (hk : k < 256) :
    (x + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (x.setWidth 64) k := by
  rw [ea_add (by omega_using [hx, hk]), Nat.add_zero]

/-- A polynomial apart from the frame and the regions written keeps its coefficients. -/
theorem in_keep {s₀ : State} {W : List Region} {m : Mem} (hsp : 16 ≤ (E0 s₀).toNat)
    (hf : Frame W (P0 s₀).mem m) {p : Addr} (hstk : (stkR s₀).Disjoint (pR p))
    (hw : ∀ r ∈ W, (pR p).Disjoint r) {k : Nat} (hk : k < 256) :
    coeffAt m p k = coeffAt s₀.mem p k := by
  rw [coeffAt_frame hf hw (by rw [n_eq]; exact hk), coeffAt_frame (P0_mem hsp) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [← stk_eq hsp]; exact hstk.symm) (by rw [n_eq]; exact hk)]

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

end

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_high_bits` and `vg_mldsa_low_bits`

Both compare `γ₂` with `(q - 1)/32` and run, for the value they found, the
loop `cntLoop` of a core that computes `eax ← V a` from the coefficient `a =
[esi]` (`Core1`: `hbCore_spec`, `lbCore_spec`) and `cntTail`, which stores it
to `[edi]`. The loop is proven once for any core (`bits_piece`), with the
value `V s₀` of the entry state, as `γ₂` is (`E s₀` holds in the branch).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_ leaf)
open VG.Spec.MlDsa (q highBits lowBits ofInt)
open VG.Proof.MlDsa (gamma2s coeffAt Reduced polyAt PolyIs NatPolyIs highBitsContract lowBitsContract bitsSig)
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
def lbV (g a : Nat) : Nat := condAddN a (hbF g a % hbM g * (2 * g)) q

theorem hbCore_spec {g : Nat} (hg : g ∈ gamma2s) : Core1 (hbCore g) (hbV g) := by
  intro is s P a ha hin hv c
  rw [hbCore, List.cons_append]
  refine wp_movm hin (hb_spec hg (a := a) (by simp [State.setReg, hv]) ha fun s₁ o₁ v₁ => c s₁ ?_ v₁)
  exact (VG.Proof.MlKem.X86.Only.setReg s .eax _ |>.trans o₁).mono fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp [h]

theorem lbCore_eq (g : Nat) (is : List Instr) : lbCore g ++ is =
    .mov .eax (.mem (at_ .esi 0)) :: .mov .ebx (.reg .eax) :: (hb g ++
      (.mov .edx (.imm (BitVec.ofNat 32 (2 * g))) :: .mul .edx :: (condAdd .ebx (.reg .eax) .edx qImm ++
        (.mov .eax (.reg .ebx) :: is)))) := by
  simp only [lbCore, List.cons_append, List.nil_append, List.append_assoc]

theorem lbCore_spec {g : Nat} (hg : g ∈ gamma2s) : Core1 (lbCore g) (lbV g) := by
  intro is s P a ha hin hv c
  rw [lbCore_eq]
  have hM := hbM_mul hg
  have hgl : 2 * g ≤ 523776 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  refine wp_movm hin (wp_mov fun s₁ u₁ => hb_spec hg (a := a) ?_ ha fun s₂ o₂ v₂ => wp_movi fun s₃ u₃ => ?_)
  · rw [u₁.other _ (by decide)]; simp [State.setReg, hv]
  have hlt : hbF g a % hbM g < hbM g := Nat.mod_lt _ (by rcases mem_gamma2s hg with rfl | rfl <;> decide)
  have hle : hbF g a % hbM g * (2 * g) ≤ q - 1 := by
    rw [← hM]; exact Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
  have e₃ : (s₃.gpr .eax).toNat = hbF g a % hbM g := by rw [u₃.other _ (by decide), v₂]
  have m₃ : (s₃.gpr .edx).toNat = 2 * g := by rw [u₃.gpr]; exact toNat_ofNat32 (by omega_using [hgl])
  refine wp_mulSmall (r := .edx) (by rw [e₃, m₃]; exact Nat.lt_of_le_of_lt hle (by rw [q_eq]; decide)) fun s₄ o₄ v₄ => ?_
  have b₄ : (s₄.gpr .ebx).toNat = a := by
    rw [o₄.gpr _ (by decide), u₃.other _ (by decide), o₂.gpr _ (by decide), u₁.gpr]
    simp [State.setReg, hv]
  refine condAdd_spec (by decide) (X := s₄.gpr .eax) rfl
    (by rw [v₄, e₃, m₃, b₄, show qImm.toNat = q from rfl]; omega_using [hle])
    fun s₅ o₅ v₅ => wp_mov fun s₆ u₆ => c s₆ ?_ ?_
  · refine ((((((VG.Proof.MlKem.X86.Only.setReg s .eax _).trans (updOnly u₁)).trans o₂).trans
      (updOnly u₃)).trans o₄).trans (o₅.trans (updOnly u₆))).mono fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (((((h | h) | h | h) | h) | h | h) | (h | h) | h) <;> simp [h]
  · rw [u₆.gpr, v₅, b₄, v₄, e₃, m₃, lbV]
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
  rd : s₀.rd = [pR (pA s₀ 0)]
  wr : s₀.wr = [pR (pA s₀ 2), aR s₀ 3]
  r_o : (pR (pA s₀ 0)).Disjoint (pR (pA s₀ 2))
  r_a : (pR (pA s₀ 0)).Disjoint (aR s₀ 3)
  o_a : (pR (pA s₀ 2)).Disjoint (aR s₀ 3)
  ret_r : (retR s₀).Disjoint (pR (pA s₀ 0))
  ret_o : (retR s₀).Disjoint (pR (pA s₀ 2))
  ret_a : (retR s₀).Disjoint (aR s₀ 3)
  stk_r : (stkR s₀).Disjoint (pR (pA s₀ 0))
  stk_o : (stkR s₀).Disjoint (pR (pA s₀ 2))
  stk_a : (stkR s₀).Disjoint (aR s₀ 3)
  r_fit : (rP s₀).toNat + 1024 ≤ 2 ^ 32
  o_fit : (oP s₀).toNat + 1024 ≤ 2 ^ 32
  g2 : (arg s₀ 1).toNat ∈ gamma2s
  r_red : Reduced s₀.mem (pA s₀ 0)

theorem BitsPre.of_hb {s₀ : State} (h : (highBitsContract X86.abi 16).pre s₀) : BitsPre s₀ := by
  sig_pre [highBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem BitsPre.of_lb {s₀ : State} (h : (lowBitsContract X86.abi 16).pre s₀) : BitsPre s₀ := by
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
  esi : s.gpr .esi = rP s₀
  edi : s.gpr .edi = oP s₀
  zf : s.zf = some (arg s₀ 1 == BitVec.ofNat 32 g32)

theorem init_piece : Piece BitsPre BitsPub (fun s₀ s => s = P0 s₀) BS1 (.block bitsInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) (by native_taint_decide)
  · subst e
    have hin : aR s₀ 3 ∈ s₀.rd ++ s₀.wr := by simp [hp.wr]
    obtain ⟨a₀, i₀, v₀⟩ := arg_P0 (i := 0) (by omega_using []) hp.sp hp.sp' hin hp.stk_a
    obtain ⟨a₁, i₁, v₁⟩ := arg_P0 (i := 1) (by omega_using []) hp.sp hp.sp' hin hp.stk_a
    obtain ⟨a₂, i₂, v₂⟩ := arg_P0 (i := 2) (by omega_using []) hp.sp hp.sp' hin hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd, Nat.reduceMul] at a₀ a₁ a₂
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, bitsInit, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags, Option.map_some,
      Option.bind_some, a₀, a₁, a₂, i₀, i₁, i₂, v₀, v₁, v₂, Option.some.injEq,
      exists_eq_left']
    exact ⟨by simp, rfl, rfl, rfl, by simp, by simp, by rw [sub_beq_zero']⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

/-! ## The loop -/

/-- After `k` coefficients, with the values `V`. -/
structure BInv (V : Nat → Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = rP s₀ + BitVec.ofNat 32 (4 * k)
  edi : s.gpr .edi = oP s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  frame : Frame [pR (pA s₀ 2)] (P0 s₀).mem s.mem
  out : ∀ i < k, coeffAt s.mem (pA s₀ 2) i = BitVec.ofNat 32 (V (coeffAt s₀.mem (pA s₀ 0) i).toNat)

theorem addr_cf {x : BitVec 32} (hx : x.toNat + 1024 ≤ 2 ^ 32) {k : Nat} (hk : k < 256) :
    addr (x + BitVec.ofNat 32 (4 * k)) 0 = coeffAddr (x.setWidth 64) k := ea_cf hx hk

theorem bits_step {core : List Instr} {V : Nat → Nat} (hc : Core1 core V)
    {s₀ : State} (hp : BitsPre s₀) {k : Nat} (hk : k < 256) {s : State} (h : BInv V s₀ k s) :
    WP isa (.block (core ++ cntTail)) s fun s' =>
      BInv V s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have ef : s.ea (at_ .esi 0) = coeffAddr (pA s₀ 0) k := by rw [State.ea, at_, h.esi]; exact ea_cf hp.r_fit hk
  have hin : InRegions (s.rd ++ s.wr) (coeffAddr (pA s₀ 0) k) 4 := by
    rw [h.rd, h.wr, pushed_rd, P0_wr, hp.rd]
    exact ⟨_, by simp, coeff_contains _ (by rw [n_eq]; exact hk)⟩
  have hkeep : coeffAt s.mem (pA s₀ 0) k = coeffAt s₀.mem (pA s₀ 0) k :=
    in_keep hp.sp h.frame hp.stk_r (by simpa using hp.r_o) hk
  have ha := hp.r_red k (by rw [n_eq]; exact hk)
  refine hc _ s _ _ ha (by rw [ef]; exact hin) (by rw [ef, ← VG.Proof.MlDsa.Round.coeffAt_eq, hkeep])
    fun s₁ o₁ v₁ => ?_
  have edi₁ : s₁.gpr .edi = oP s₀ + BitVec.ofNat 32 (4 * k) := by rw [o₁.gpr _ (by decide), h.edi]
  have out : InRegions s₁.wr (addr (oP s₀ + BitVec.ofNat 32 (4 * k)) 0) 4 := by
    rw [addr_cf hp.o_fit hk, o₁.wr, h.wr, P0_wr, hp.wr]
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
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, addr_cf hp.o_fit hk, o₁.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ (by rw [n_eq]; exact hk))
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, addr_cf hp.o_fit hk, o₁.mem,
      coeffAt_writeW _ _ (by rw [n_eq]; omega_using [hk, hi]) (by rw [n_eq]; exact hk)]
    by_cases e : k = i
    · subst e
      rw [ite_eq_left rfl]
      exact eq_ofNat_of_toNat v₁
    · rw [ite_eq_right e]; exact h.out i (by omega_using [hi, e])
  · simp only [eval, z₅, Option.map_some]
    rw [u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, o₁.gpr _ (by decide), h.ecx]
    exact cnt_ne hk (by decide)

theorem bits_piece {core : List Instr} {V : Nat → Nat} (hc : Core1 core V)
    (E : State → Prop) {hh : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (core ++ cntTail)) hh).isSome = true) :
    Piece BitsPre BitsPub (fun s₀ s => BS1 s₀ s ∧ E s₀) (fun s₀ s => BInv V s₀ 256 s ∧ E s₀)
      (cntLoop (core ++ cntTail)) := by
  refine Piece.seq (B := fun s₀ s => BInv V s₀ 0 s ∧ E s₀) ?_ ?_
  · refine Piece.taint [] (fun s₀ s hp ⟨h, he⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by native_taint_decide)
    refine wp_movi fun s₁ u₁ => WP.block_nil_iff.mpr ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega_using [])⟩, he⟩
    · rw [u₁.other _ (by decide), h.esp]
    · rw [u₁.rd, h.rd]
    · rw [u₁.wr, h.wr]
    · rw [u₁.other _ (by decide), h.esi]; simp
    · rw [u₁.other _ (by decide), h.edi]; simp
    · rw [u₁.gpr]; rfl
    · rw [u₁.mem, h.mem]; exact Frame.refl _ _
  · exact Piece.countLoop (by decide) (fun k s₀ s => BInv V s₀ k s ∧ E s₀) [.esp, .esi, .edi, .ecx]
      (fun k hk s₀ s hp ⟨h, he⟩ => (bits_step hc hp hk h).mono fun _ ⟨h', c'⟩ => ⟨⟨h', he⟩, c'⟩)
      (fun k _ s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
        · rw [h.esi, h'.esi, rP, rP, hq.2.1]
        · rw [h.edi, h'.edi, oP, oP, hq.2.2.2]
        · rw [h.ecx, h'.ecx]) ht

/-! ## The functions -/

/-- `γ₂` is `(q - 1)/32`: the branch the code takes. -/
def isG32 (s₀ : State) : Bool := arg s₀ 1 == BitVec.ofNat 32 g32

/-- Both branches, for the core `core g` computing `Vf g`. -/
theorem body_piece {core : Nat → List Instr} {Vf : Nat → Nat → Nat} (hc : ∀ g ∈ gamma2s, Core1 (core g) (Vf g))
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (core g32 ++ cntTail)) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (core g88 ++ cntTail)) h₂).isSome = true) :
    Piece BitsPre BitsPub (fun s₀ s => s = P0 s₀) (fun s₀ s => BInv (Vf (arg s₀ 1).toNat) s₀ 256 s)
      (.seq (.block bitsInit) (.ite .e (cntLoop (core g32 ++ cntTail)) (cntLoop (core g88 ++ cntTail)))) := by
  refine Piece.seq init_piece (Piece.ite isG32 (fun s₀ s _ h => h.zf) (fun s₀ s₀' _ _ hq => by
    simp only [isG32, hq.2.2.1]) ?_ ?_)
  · refine (bits_piece (hc g32 g32_mem) (fun s₀ => isG32 s₀ = true) t₁).mono (fun _ _ _ h => h)
      fun s₀ s hp ⟨h, he⟩ => ?_
    rcases gamma_cases hp.g2 with ⟨_, e⟩ | ⟨e', _⟩
    · rw [e]; exact h
    · rw [isG32, e'] at he; exact absurd he (by decide)
  · refine (bits_piece (hc g88 g88_mem) (fun s₀ => isG32 s₀ = false) t₂).mono (fun _ _ _ h => h)
      fun s₀ s hp ⟨h, he⟩ => ?_
    rcases gamma_cases hp.g2 with ⟨e', _⟩ | ⟨_, e⟩
    · rw [isG32, e'] at he; exact absurd he (by decide)
    · rw [e]; exact h

theorem leaf_piece {core : Nat → List Instr} {Vf : Nat → Nat → Nat} (hc : ∀ g ∈ gamma2s, Core1 (core g) (Vf g))
    (hsp : NoSp (.seq (.block bitsInit) (.ite .e (cntLoop (core g32 ++ cntTail)) (cntLoop (core g88 ++ cntTail)))))
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (core g32 ++ cntTail)) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (core g88 ++ cntTail)) h₂).isSome = true) :
    Piece BitsPre BitsPub (fun s₀ s => s = s₀)
      (fun s₀ s' => LeafPost (fun s => BInv (Vf (arg s₀ 1).toNat) s₀ 256 s) s₀ s')
      (leaf (.seq (.block bitsInit) (.ite .e (cntLoop (core g32 ++ cntTail)) (cntLoop (core g88 ++ cntTail))))) :=
  Piece.leaf (fun s₀ => [pR (pA s₀ 2)]) hsp (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega_using [this]⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← stk_eq hp.sp]; exact hp.stk_o, hp.ret_o⟩)
    (fun _ _ _ _ hq => hq.1)
    ((body_piece hc t₁ t₂).mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem hbV_lt {g : Nat} (hg : g ∈ gamma2s) (a : Nat) : hbV g a < 2 ^ 32 := by
  have := Nat.mod_lt (hbF g a) (show hbM g > 0 by rcases mem_gamma2s hg with rfl | rfl <;> decide)
  have : hbM g ≤ 44 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  unfold hbV; omega_arith

theorem lbV_lt {g : Nat} {a : Nat} (ha : a < q) : lbV g a < 2 ^ 32 := by
  have hq : q = 8380417 := rfl
  unfold lbV condAddN; split <;> omega_using [ha, hq]

/-- Memory with the arguments `0x400`, `(q - 1)/32` and `0` at `0x5004`. -/
def bitsSatMem : Mem := fun a => if a = 0x5005 then 4 else if a = 0x5009 then 0xff else if a = 0x500a then 3 else 0

theorem bitsSat_zero (a : Addr) (ha : a.toNat < 0x5000) : bitsSatMem a = 0 := by
  simp only [bitsSatMem]
  rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha]),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha]),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha])]

theorem reduced_zero {m : Mem} (hm : ∀ a : Addr, a.toNat < 0x5000 → m a = 0) (p : Nat)
    (hp : p + 1024 ≤ 0x5000) : Reduced m (BitVec.ofNat 64 p) := fun i hi => by
  rw [VG.Proof.MlDsa.Arith.coeffAt_congr (m' := m) (m := fun _ => 0) (fun k hk => hm _ (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_using [hp, hk])) hi]
  simp [VG.Proof.MlDsa.coeffAt, Mem.readW, Mem.read]

theorem highBits_verified : Verified X86.target highBits (highBitsContract X86.abi 16) := by
  refine Piece.verified (((leaf_piece (fun g hg => hbCore_spec hg) (NoSp.of_all (by decide +kernel))
    (by native_taint_decide) (by native_taint_decide)).pre_mono (fun _ h => BitsPre.of_hb h) fun s s' _ _ h => by
      sig_pub [highBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [highBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    have hp := BitsPre.of_hb h₀
    refine natPolyIs_of_toNat fun i hi => ?_
    rw [Proof.MlDsa.Arith.coeffAt_frame hm (fun r hr => by rw [List.mem_singleton.mp hr]; rw [← stk_eq hp.sp]; exact hp.stk_o.symm) hi, hinv.out i hi, map_get _ _ hi, highBits_eq hp.g2, polyAt_val hp.r_red hi, toNat_ofNat32 (hbV_lt hp.g2 _)]
    rfl
  · let st := satState bitsSatMem [⟨0x400, 1024⟩] [⟨0, 1024⟩, ⟨0x5004, 12⟩]
    have a0 : arg st 0 = 0x400 := by decide
    have a1 : arg st 1 = 261888 := by decide
    have a2 : arg st 2 = 0 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [highBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, reduced_zero bitsSat_zero 0x400 (by decide)⟩
    all_goals first
      | exact Region.disjoint_of_sep (by decide)
      | decide

theorem lowBits_verified : Verified X86.target lowBits (lowBitsContract X86.abi 16) := by
  refine Piece.verified (((leaf_piece (fun g hg => lbCore_spec hg) (NoSp.of_all (by decide +kernel))
    (by native_taint_decide) (by native_taint_decide)).pre_mono (fun _ h => BitsPre.of_lb h) fun s s' _ _ h => by
      sig_pub [lowBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [lowBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    have hp := BitsPre.of_lb h₀
    refine Proof.MlDsa.Arith.polyIs_frame hm (fun r hr => by rw [List.mem_singleton.mp hr]; rw [← stk_eq hp.sp]; exact hp.stk_o.symm) ?_
    refine polyIs_of_toNat fun i hi => ?_
    have ha := hp.r_red i hi
    rw [hinv.out i hi, map_get _ _ hi, lowBits_val hp.g2, polyAt_val hp.r_red hi, toNat_ofNat32 (lbV_lt ha)]
    rfl
  · let st := satState bitsSatMem [⟨0x400, 1024⟩] [⟨0, 1024⟩, ⟨0x5004, 12⟩]
    have a0 : arg st 0 = 0x400 := by decide
    have a1 : arg st 1 = 261888 := by decide
    have a2 : arg st 2 = 0 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [lowBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, reduced_zero bitsSat_zero 0x400 (by decide)⟩
    all_goals first
      | exact Region.disjoint_of_sep (by decide)
      | decide

end VG.Proof.MlDsa.X86.Round
