module

public import VerifiedGarbage.Impl.Bignum.Arm.WideMul
public import VerifiedGarbage.Proof.Bignum.Arm.WideValue
public import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
  all_goals intro r hr; cases r <;> simp_all [clobbers]

/-- No branches or memory addresses depend on either operand. -/
theorem wideMul_ct : ConstantTime isa (fun _ => True) (fun _ _ => True) (.block wideMul) := by
  refine ConstantTime.of_silent fun s tr t _ h => ?_
  rw [Exec.block_iff] at h
  cases h
  rfl

end VG.Proof.Bignum.Arm
