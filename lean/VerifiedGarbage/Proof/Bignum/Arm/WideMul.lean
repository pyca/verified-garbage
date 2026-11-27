module

public import VerifiedGarbage.Impl.Bignum.Arm.WideMul
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Bignum.Arm.WideValue`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.WideMath`, which this module and modules that import it used -/

section

/-! # Bounds and recombination for four half-word products -/

@[expose] public section

namespace VG.Proof.Bignum.Arm

/-- A half-word product plus a half-word carry fits in a machine word. -/
theorem half_product_carry_lt {a b c : Nat}
    (ha : a < 65536) (hb : b < 65536) (hc : c < 65536) :
    a * b + c < 2 ^ 32 := by
  have := Nat.mul_le_mul (show a ≤ 65535 by omega_using [ha]) (show b ≤ 65535 by omega_using [hb])
  omega_using [hc, this]

/-- Bounds for every addition used to assemble the product. -/
theorem wide_bounds {a0 a1 b0 b1 : Nat}
    (ha0 : a0 < 65536) (ha1 : a1 < 65536)
    (hb0 : b0 < 65536) (hb1 : b1 < 65536) :
    let p := a0 * b0
    let t := a1 * b0 + p / 65536
    let u := a0 * b1 + t % 65536
    p < 2 ^ 32 ∧ t < 2 ^ 32 ∧ u < 2 ^ 32 ∧
      a1 * b1 + t / 65536 + u / 65536 < 2 ^ 32 := by
  dsimp only
  have hp := half_product_carry_lt ha0 hb0 (c := 0) (by decide)
  have ht := half_product_carry_lt ha1 hb0 (c := a0 * b0 / 65536) (by omega_using [hp])
  have hu := half_product_carry_lt ha0 hb1 (c := (a1 * b0 + a0 * b0 / 65536) % 65536)
    (Nat.mod_lt _ (by decide))
  have hh := Nat.mul_le_mul (show a1 ≤ 65535 by omega_using [ha1]) (show b1 ≤ 65535 by omega_using [hb1])
  exact ⟨by omega_using [hp], ht, hu, by omega_using [ht, hu, hh]⟩

/-- The carry-split construction is the exact full product, not just its
low word. -/
theorem wide_product (a0 a1 b0 b1 : Nat) :
    let p := a0 * b0
    let t := a1 * b0 + p / 65536
    let u := a0 * b1 + t % 65536
    p % 65536 + (u % 65536) * 65536 +
      (a1 * b1 + t / 65536 + u / 65536) * 2 ^ 32 =
      (a0 + a1 * 65536) * (b0 + b1 * 65536) := by
  dsimp only
  have hp := Nat.mod_add_div (a0 * b0) 65536
  have ht := Nat.mod_add_div (a1 * b0 + a0 * b0 / 65536) 65536
  have hu := Nat.mod_add_div (a0 * b1 + (a1 * b0 + a0 * b0 / 65536) % 65536) 65536
  grind

end VG.Proof.Bignum.Arm

end

end

/-! # The word-level value of ARMv7's full product -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (mask16 toNat_and_mask16 toNat_shr toNat_shl toNat_add_lt toNat_mul_lt)

/-- Four 16-bit partial products give the exact 64-bit result. All
intermediate additions are bounded before interpreting the word operations. -/
theorem wide_value (x y : BitVec 32) :
    let a0 := x &&& mask16
    let a1 := x >>> 16
    let b0 := y &&& mask16
    let b1 := y >>> 16
    let p := a0 * b0
    let t := a1 * b0 + (p >>> 16)
    let u := a0 * b1 + (t &&& mask16)
    ((p &&& mask16) + (u <<< 16)).toNat +
      (a1 * b1 + (t >>> 16) + (u >>> 16)).toNat * 2 ^ 32 = x.toNat * y.toNat := by
  let a0 := x &&& mask16
  let a1 := x >>> 16
  let b0 := y &&& mask16
  let b1 := y >>> 16
  let p := a0 * b0
  let t := a1 * b0 + (p >>> 16)
  let u := a0 * b1 + (t &&& mask16)
  change ((p &&& mask16) + (u <<< 16)).toNat +
    (a1 * b1 + (t >>> 16) + (u >>> 16)).toNat * 2 ^ 32 = _
  have ha0 : a0.toNat < 65536 := by rw [toNat_and_mask16]; omega_using []
  have ha1 : a1.toNat < 65536 := by rw [toNat_shr]; have := x.isLt; omega_using []
  have hb0 : b0.toNat < 65536 := by rw [toNat_and_mask16]; omega_using []
  have hb1 : b1.toNat < 65536 := by rw [toNat_shr]; have := y.isLt; omega_using []
  have hx : a0.toNat + a1.toNat * 65536 = x.toNat := by
    rw [toNat_and_mask16, toNat_shr]; omega_using []
  have hy : b0.toNat + b1.toNat * 65536 = y.toNat := by
    rw [toNat_and_mask16, toNat_shr]; omega_using []
  obtain ⟨hp, ht, hu, hh⟩ := wide_bounds ha0 ha1 hb0 hb1
  have pval : p.toNat = a0.toNat * b0.toNat := toNat_mul_lt hp
  have ab : a1.toNat * b0.toNat < 2 ^ 32 := by omega_using [ht]
  have tval : t.toNat = a1.toNat * b0.toNat + a0.toNat * b0.toNat / 65536 := by
    change (a1 * b0 + (p >>> 16)).toNat = _
    rw [toNat_add_lt (by rw [toNat_mul_lt ab, toNat_shr p 16, pval]; exact ht),
      toNat_mul_lt ab, toNat_shr p 16, pval]
  have ac : a0.toNat * b1.toNat < 2 ^ 32 := by omega_using [hu]
  have uval : u.toNat = a0.toNat * b1.toNat +
      (a1.toNat * b0.toNat + a0.toNat * b0.toNat / 65536) % 65536 := by
    change (a0 * b1 + (t &&& mask16)).toNat = _
    rw [toNat_add_lt (by rw [toNat_mul_lt ac, toNat_and_mask16 t, tval]; exact hu),
      toNat_mul_lt ac, toNat_and_mask16 t, tval]
  have ad : a1.toNat * b1.toNat < 2 ^ 32 := by omega_using [hh]
  have hval : (a1 * b1 + (t >>> 16)).toNat = a1.toNat * b1.toNat +
      (a1.toNat * b0.toNat + a0.toNat * b0.toNat / 65536) / 65536 := by
    rw [toNat_add_lt (by rw [toNat_mul_lt ad, toNat_shr t 16, tval]; omega_using [ha0, ha1, hb0, hb1, hx, hy, hp, ht, hu, hh, pval, ab, tval, ac, uval, ad]),
      toNat_mul_lt ad, toNat_shr t 16, tval]
  rw [toNat_add_lt (x := a1 * b1 + _) (by rw [hval, toNat_shr u 16, uval]; exact hh),
    hval, toNat_shr u 16, uval]
  rw [BitVec.toNat_add, toNat_and_mask16 p, pval, toNat_shl u 16, uval]
  have he := wide_product a0.toNat a1.toNat b0.toNat b1.toNat
  rw [hx, hy] at he
  have hlo : (a0.toNat * b0.toNat % 65536 +
      (a0.toNat * b1.toNat + (a1.toNat * b0.toNat + a0.toNat * b0.toNat / 65536) % 65536) * 2 ^ 16 % 2 ^ 32) % 2 ^ 32 =
      a0.toNat * b0.toNat % 65536 +
        (a0.toNat * b1.toNat + (a1.toNat * b0.toNat + a0.toNat * b0.toNat / 65536) % 65536) % 65536 * 65536 := by omega_using []
  rw [hlo]
  exact he

end VG.Proof.Bignum.Arm

end

end

/-! # ARMv7 full-width multiplication: instruction-level correctness -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

/-- The non-register state is untouched, as are registers outside `rs`. -/
structure Preserves (rs : List Reg) (s t : State) : Prop where
  regs : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  n : t.n = s.n
  z : t.z = s.z
  c : t.c = s.c
  v : t.v = s.v
  unknowns : t.unknowns = s.unknowns
  syms : t.syms = s.syms

theorem Preserves.refl (rs : List Reg) (s : State) : Preserves rs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Preserves.setReg {rs : List Reg} {s t : State} (h : Preserves rs s t)
    {r : Reg} (hr : r ∈ rs) (x : BitVec 32) : Preserves rs s (t.setReg r x) := by
  refine ⟨?_, h.mem, h.sp, h.rd, h.wr, h.n, h.z, h.c, h.v, h.unknowns, h.syms⟩
  intro q hq
  rw [gpr_setReg_of_ne _ _ (by intro e; exact hq (e ▸ hr))]
  exact h.regs q hq

theorem Preserves.trans {rs : List Reg} {s t u : State}
    (h : Preserves rs s t) (k : Preserves rs t u) : Preserves rs s u :=
  ⟨fun r hr => (k.regs r hr).trans (h.regs r hr), k.mem.trans h.mem,
    k.sp.trans h.sp, k.rd.trans h.rd, k.wr.trans h.wr, k.n.trans h.n,
    k.z.trans h.z, k.c.trans h.c, k.v.trans h.v,
    k.unknowns.trans h.unknowns, k.syms.trans h.syms⟩

abbrev clobbers : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9]
abbrev mask : BitVec 32 := (0xffff : BitVec 16).setWidth 32

theorem splitWords_ok (s : State) :
    WP isa (.block splitWords) s fun t =>
      t.gpr .r3 = s.gpr .r1 &&& mask ∧ t.gpr .r4 = s.gpr .r1 >>> 16 ∧
      t.gpr .r5 = s.gpr .r2 &&& mask ∧ t.gpr .r6 = s.gpr .r2 >>> 16 ∧
      t.gpr .r9 = mask ∧ Preserves clobbers s t := by
  apply WP.of_runBlock
  simp only [splitWords, runBlock_cons, runStep_some, isa, exec,
    Op2.eval, Option.map_some, gpr_setReg, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat first
    | apply Preserves.setReg (hr := by simp [clobbers])
    | exact Preserves.refl _ _


theorem lowProduct_ok (s : State) :
    WP isa (.block lowProduct) s fun t =>
      t.gpr .r7 = s.gpr .r3 * s.gpr .r5 ∧
      t.gpr .r8 = s.gpr .r4 * s.gpr .r5 + ((s.gpr .r3 * s.gpr .r5) >>> 16) ∧
      Preserves [.r7, .r8] s t := by
  apply WP.of_runBlock
  simp only [lowProduct, runBlock_cons, runStep_some, isa, exec,
    Op2.eval, gpr_setReg, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  repeat first
    | apply Preserves.setReg (hr := by simp)
    | exact Preserves.refl _ _

theorem crossProduct_ok (s : State) :
    WP isa (.block crossProduct) s fun t =>
      t.gpr .r4 = s.gpr .r4 * s.gpr .r6 + (s.gpr .r8 >>> 16) ∧
      t.gpr .r3 = s.gpr .r3 * s.gpr .r6 + (s.gpr .r8 &&& s.gpr .r9) ∧
      Preserves [.r3, .r4, .r5] s t := by
  apply WP.of_runBlock
  simp only [crossProduct, runBlock_cons, runStep_some, isa, exec,
    Op2.eval, Option.map_some, gpr_setReg, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  repeat first
    | apply Preserves.setReg (hr := by simp)
    | exact Preserves.refl _ _

theorem packProduct_ok (s : State) :
    WP isa (.block packProduct) s fun t =>
      t.gpr .r4 = s.gpr .r4 + (s.gpr .r3 >>> 16) ∧
      t.gpr .r3 = (s.gpr .r7 &&& s.gpr .r9) + (s.gpr .r3 <<< 16) ∧
      Preserves [.r3, .r4, .r7] s t := by
  apply WP.of_runBlock
  simp only [packProduct, runBlock_cons, isa, exec, Op2.eval]
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  repeat first
    | apply Preserves.setReg (hr := by simp)
    | exact Preserves.refl _ _


theorem Preserves.mono {rs rs' : List Reg} {s t : State}
    (h : Preserves rs s t) (hr : ∀ r ∈ rs, r ∈ rs') : Preserves rs' s t :=
  { h with regs := fun r hn => h.regs r (fun hmem => hn (hr r hmem)) }

/-- The whole instruction sequence computes a full 32-by-32-bit product,
without changing memory, flags, stack or the input registers. -/
theorem wideMul_ok (s : State) :
    WP isa (.block wideMul) s fun t =>
      (t.gpr .r3).toNat + (t.gpr .r4).toNat * 2 ^ 32 =
        (s.gpr .r1).toNat * (s.gpr .r2).toNat ∧ Preserves clobbers s t := by
  rw [wideMul, List.append_assoc, List.append_assoc]
  apply WP.block_append_iff.mpr
  refine WP.mono (splitWords_ok s) ?_
  rintro s1 ⟨a0, a1, b0, b1, mask1, frame1⟩
  apply WP.block_append_iff.mpr
  refine WP.mono (lowProduct_ok s1) ?_
  rintro s2 ⟨p, cross, frame2⟩
  apply WP.block_append_iff.mpr
  refine WP.mono (crossProduct_ok s2) ?_
  rintro s3 ⟨hi, mid, frame3⟩
  refine WP.mono (packProduct_ok s3) ?_
  rintro s4 ⟨hi4, lo4, frame4⟩
  refine ⟨?_, frame1.trans ((frame2.mono ?_).trans ((frame3.mono ?_).trans (frame4.mono ?_)))⟩
  · rw [lo4, hi4, hi, mid, frame3.regs .r7 (by simp), frame3.regs .r9 (by simp),
      frame2.regs .r3 (by simp), frame2.regs .r4 (by simp), frame2.regs .r6 (by simp),
      frame2.regs .r9 (by simp), p, cross, a0, a1, b0, b1, mask1]
    exact wide_value _ _
  all_goals decide

end VG.Proof.Bignum.Arm
