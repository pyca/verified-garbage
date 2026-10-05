import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Common
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.MlDsa.Arm.Arith.AddSub

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Arith.Basic`. -/
section

/-!
# ML-DSA on 32-bit ARM: the values of the arithmetic modulo `q`

What the pieces of code of `Impl/MlDsa/Arm/Arith/Common.lean` compute, as
functions on words (`bred`, `bfix`, `bcsub`, `bmulz`), and their values
(`bcsub_mulz`: `csub` after `mulz` is the product modulo `q`), from the
arithmetic of `Proof/MlDsa/Arith/Mul32.lean`; and the symbolic execution of
`mulz`, once for any state (`mulz_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Arith

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

/-! ## Words -/

/-- `q` as a word. -/
abbrev Qw : BitVec 32 := 8380417

theorem loadQ_val : ((0x7F : BitVec 16) ++ ((0xE001 : BitVec 16).setWidth 32).extractLsb' 0 16 : BitVec 32) = VG.Proof.MlDsa.Arm.Arith.Qw := by
  decide

/-- What `red d t Q` leaves in `d`. -/
def bred (x : BitVec 32) : BitVec 32 := x - x >>> 23 * VG.Proof.MlDsa.Arm.Arith.Qw

/-- What `fixup d t Q` leaves in `d`. -/
def bfix (y : BitVec 32) : BitVec 32 := y + y >>> 31 * VG.Proof.MlDsa.Arm.Arith.Qw

/-- What `csub d t Q` leaves in `d`. -/
def bcsub (x : BitVec 32) : BitVec 32 := VG.Proof.MlDsa.Arm.Arith.bfix (x - VG.Proof.MlDsa.Arm.Arith.Qw)

/-- What `mulz acc b t` leaves in `acc`, for the pieces `z₂`, `z₁`, `z₀`. -/
def bmulz (b z₂ z₁ z₀ : BitVec 32) : BitVec 32 := VG.Proof.MlDsa.Arm.Arith.bred (b * z₀ + VG.Proof.MlDsa.Arm.Arith.bred (b * z₁ + VG.Proof.MlDsa.Arm.Arith.bred (b * z₂) <<< 7) <<< 7)

theorem bred_toNat (x : BitVec 32) : (VG.Proof.MlDsa.Arm.Arith.bred x).toNat = red23 x.toNat := by
  unfold VG.Proof.MlDsa.Arm.Arith.bred red23
  rw [q_eq]
  bv_omega

theorem bcsub_toNat {x : BitVec 32} (h : x.toNat < 2 * q) : (VG.Proof.MlDsa.Arm.Arith.bcsub x).toNat = x.toNat % q := by
  unfold VG.Proof.MlDsa.Arm.Arith.bcsub VG.Proof.MlDsa.Arm.Arith.bfix
  rw [q_eq] at *
  by_cases h' : x.toNat < 8380417
  · rw [Nat.mod_eq_of_lt h']; bv_omega
  · bv_omega

/-- `fixup (a - b)`: the difference of reduced values, reduced. -/
theorem bfix_sub {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (VG.Proof.MlDsa.Arm.Arith.bfix (a - b)).toNat = (a.toNat + q - b.toNat) % q := by
  unfold VG.Proof.MlDsa.Arm.Arith.bfix
  rw [q_eq] at *
  by_cases h' : b.toNat ≤ a.toNat
  · bv_omega
  · bv_omega

/-- `csub (a + b)`: the sum of reduced values, reduced. -/
theorem bcsub_add {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (VG.Proof.MlDsa.Arm.Arith.bcsub (a + b)).toNat = (a.toNat + b.toNat) % q := by
  have : (a + b).toNat = a.toNat + b.toNat := by rw [q_eq] at *; bv_omega
  rw [VG.Proof.MlDsa.Arm.Arith.bcsub_toNat (by omega), this]

theorem pieces_toNat (a : BitVec 32) :
    (a >>> 14).toNat = a.toNat / 16384 ∧ ((a <<< 18) >>> 25).toNat = a.toNat / 128 % 128 ∧
      ((a <<< 25) >>> 25).toNat = a.toNat % 128 := by
  refine ⟨?_, ?_, ?_⟩ <;> bv_omega

theorem bmulz_toNat {b a : BitVec 32} (hb : b.toNat < q) (ha : a.toNat < 2 ^ 23) :
    (VG.Proof.MlDsa.Arm.Arith.bmulz b (a >>> 14) ((a <<< 18) >>> 25) ((a <<< 25) >>> 25)).toNat = mulzN b.toNat a.toNat := by
  obtain ⟨p2, p1, p0⟩ := VG.Proof.MlDsa.Arm.Arith.pieces_toNat a
  obtain ⟨h1, h2, h3, -⟩ := mulzN_bounds hb ha
  have m2 : (b * (a >>> 14)).toNat = b.toNat * (a.toNat / 16384) := by
    rw [BitVec.toNat_mul, p2, Nat.mod_eq_of_lt h1]
  have e1 : (VG.Proof.MlDsa.Arm.Arith.bred (b * (a >>> 14))).toNat = mulz1 b.toNat a.toNat := by rw [VG.Proof.MlDsa.Arm.Arith.bred_toNat, m2]; rfl
  have s1 : (b * ((a <<< 18) >>> 25) + VG.Proof.MlDsa.Arm.Arith.bred (b * (a >>> 14)) <<< 7).toNat =
      b.toNat * (a.toNat / 128 % 128) + mulz1 b.toNat a.toNat * 128 := by
    have hr : mulz1 b.toNat a.toNat ≤ redMax := red23_le h1
    unfold redMax at hr
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_shiftLeft, e1, p1, Nat.shiftLeft_eq,
      show (2 : Nat) ^ 7 = 128 from rfl]
    have hm : b.toNat * (a.toNat / 128 % 128) < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (a := mulz1 b.toNat a.toNat * 128) (by omega)]
    exact Nat.mod_eq_of_lt h2
  have e2 : (VG.Proof.MlDsa.Arm.Arith.bred (b * ((a <<< 18) >>> 25) + VG.Proof.MlDsa.Arm.Arith.bred (b * (a >>> 14)) <<< 7)).toNat = mulz2 b.toNat a.toNat := by
    rw [VG.Proof.MlDsa.Arm.Arith.bred_toNat, s1]; rfl
  have s2 : (b * ((a <<< 25) >>> 25) + VG.Proof.MlDsa.Arm.Arith.bred (b * ((a <<< 18) >>> 25) + VG.Proof.MlDsa.Arm.Arith.bred (b * (a >>> 14)) <<< 7) <<< 7).toNat =
      b.toNat * (a.toNat % 128) + mulz2 b.toNat a.toNat * 128 := by
    have hr : mulz2 b.toNat a.toNat ≤ redMax := red23_le h2
    unfold redMax at hr
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_shiftLeft, e2, p0, Nat.shiftLeft_eq,
      show (2 : Nat) ^ 7 = 128 from rfl]
    have hm : b.toNat * (a.toNat % 128) < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (a := mulz2 b.toNat a.toNat * 128) (by omega)]
    exact Nat.mod_eq_of_lt h3
  unfold VG.Proof.MlDsa.Arm.Arith.bmulz
  rw [VG.Proof.MlDsa.Arm.Arith.bred_toNat, s2]; rfl

/-- `csub` after `mulz`: the product of `b` and `a`, reduced. -/
theorem bcsub_mulz {b a : BitVec 32} (hb : b.toNat < q) (ha : a.toNat < q) :
    (VG.Proof.MlDsa.Arm.Arith.bcsub (VG.Proof.MlDsa.Arm.Arith.bmulz b (a >>> 14) ((a <<< 18) >>> 25) ((a <<< 25) >>> 25))).toNat = b.toNat * a.toNat % q := by
  have ha' : a.toNat < 2 ^ 23 := by rw [q_eq] at ha; omega
  have := (mulzN_bounds hb ha').2.2.2
  rw [VG.Proof.MlDsa.Arm.Arith.bcsub_toNat (by rw [VG.Proof.MlDsa.Arm.Arith.bmulz_toNat hb ha']; exact Nat.lt_of_le_of_lt this redMax_lt), VG.Proof.MlDsa.Arm.Arith.bmulz_toNat hb ha',
    mulzN_mod]

/-- `mulz` is less than `2q`. -/
theorem bmulz_le {b a : BitVec 32} (hb : b.toNat < q) (ha : a.toNat < q) :
    (VG.Proof.MlDsa.Arm.Arith.bmulz b (a >>> 14) ((a <<< 18) >>> 25) ((a <<< 25) >>> 25)).toNat ≤ redMax := by
  have ha' : a.toNat < 2 ^ 23 := by rw [q_eq] at ha; omega
  rw [VG.Proof.MlDsa.Arm.Arith.bmulz_toNat hb ha']; exact (mulzN_bounds hb ha').2.2.2

/-- A word is the element of `ℤ_q` it represents, once reduced. -/
theorem ofNat_val_eq {v : BitVec 32} {x : Zq} (h : v.toNat = x.val) : v = BitVec.ofNat 32 x.val := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega)]

theorem toNat_val (x : Zq) : (BitVec.ofNat 32 x.val).toNat = x.val := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega)]

/-! ## Registers kept -/

/-- `s'` has the registers `rs`, and the regions and stack pointer, of `s`. -/
structure Keep (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r ∈ rs, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem keep_iff {rs : List Reg} {s s' : State} :
    VG.Proof.MlDsa.Arm.Arith.Keep rs s s' ↔ (∀ r ∈ rs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨fun h => ⟨h.gpr, h.rd, h.wr, h.sp⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- The lemmas that prove `Keep` after a symbolic execution (`run_block`). -/
macro "keep_simp" : tactic => `(tactic| (
  set_option linter.unusedSimpArgs false in
  simp (config := {decide := true}) only [keep_iff, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    implies_true, and_self, and_true, true_and, ite_true, ite_false]))

theorem Keep.refl (rs : List Reg) (s : State) : VG.Proof.MlDsa.Arm.Arith.Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keep.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlDsa.Arm.Arith.Keep rs s₁ s₂) (h₂ : VG.Proof.MlDsa.Arm.Arith.Keep rs s₂ s₃) :
    VG.Proof.MlDsa.Arm.Arith.Keep rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.MlDsa.Arm.Arith.Keep rs s s') (hs : ∀ r ∈ rs', r ∈ rs) :
    VG.Proof.MlDsa.Arm.Arith.Keep rs' s s' :=
  ⟨fun r hr => h.gpr r (hs r hr), h.rd, h.wr, h.sp⟩

/-! ## `mulz`, symbolically -/

/-- What `mulz .r9 .r8 .r12` does: `r9` becomes the product, `r12` is
clobbered, and nothing else changes. -/
theorem mulz_ok {s : State} {b z₂ z₁ z₀ : BitVec 32} (h4 : s.gpr .r4 = VG.Proof.MlDsa.Arm.Arith.Qw) (h5 : s.gpr .r5 = z₂)
    (h6 : s.gpr .r6 = z₁) (h7 : s.gpr .r7 = z₀) (h8 : s.gpr .r8 = b) :
    WP isa (.block (mulz .r9 .r8 .r12)) s fun s' =>
      s'.gpr .r9 = VG.Proof.MlDsa.Arm.Arith.bmulz b z₂ z₁ z₀ ∧ (∀ r, r ≠ .r9 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [mulz, red, VG.Proof.MlDsa.Arm.Arith.bmulz, VG.Proof.MlDsa.Arm.Arith.bred, h4, h5, h6, h7, h8]
  exact ⟨trivial, fun r h9 h12 => by simp [h9, h12], trivial⟩

end VG.Proof.MlDsa.Arm.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_add` and `vg_mldsa_sub`

One symbolic execution of each loop body, for any pointers (`addBody_ok`,
`subBody_ok`); the loop invariant says which coefficients of `f` are done
(`Inv`); the arithmetic is `fixS_add` and `fixS_sub`.
-/

namespace VG.Proof.MlDsa.Arm.Arith.AddSub

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr inRegions_of)

/-! ## Values -/

/-- What `fixupS r t` leaves in `r`. -/
def fixS (u : BitVec 32) : BitVec 32 := u + (u >>> 31) <<< 23 - (u >>> 31) <<< 13 + u >>> 31

/-- `fixupS (a + b - q)`: the sum of reduced values, reduced. -/
theorem fixS_add {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (VG.Proof.MlDsa.Arm.Arith.AddSub.fixS (a + b - 0x800000 + 0x2000 - 1)).toNat = (a.toNat + b.toNat) % q := by
  unfold VG.Proof.MlDsa.Arm.Arith.AddSub.fixS
  rw [q_eq] at *
  by_cases h : a.toNat + b.toNat < 8380417
  · rw [Nat.mod_eq_of_lt h]; bv_omega
  · bv_omega

/-- `fixupS (a - b)`: the difference of reduced values, reduced. -/
theorem fixS_sub {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (VG.Proof.MlDsa.Arm.Arith.AddSub.fixS (a - b)).toNat = (a.toNat + q - b.toNat) % q := by
  unfold VG.Proof.MlDsa.Arm.Arith.AddSub.fixS
  rw [q_eq] at *
  by_cases h : b.toNat ≤ a.toNat
  · bv_omega
  · bv_omega

/-! ## The loop bodies -/

/-- What an iteration of either loop does, but for the value stored. -/
def Step (s : State) (x y c v : BitVec 32) (s' : State) : Prop :=
  s'.gpr .r0 = x + 4 ∧ s'.gpr .r1 = y + 4 ∧ s'.gpr .r2 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
    s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0)) v ∧
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r

section
variable {s : State} {x y c : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = c)
  (ia : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
  (ib : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4)
  (oa : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 ia ib oa

theorem addBody_ok :
    WP isa (.block VG.Impl.MlDsa.Arm.Arith.addBody) s (VG.Proof.MlDsa.Arm.Arith.AddSub.Step s x y c (VG.Proof.MlDsa.Arm.Arith.AddSub.fixS (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 +
      s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32 - 0x800000 + 0x2000 - 1))) := by
  run_block [VG.Impl.MlDsa.Arm.Arith.addBody, VG.Impl.MlDsa.Arm.Arith.subQ, fixupS, VG.Impl.MlDsa.Arm.Arith.accTail, VG.Proof.MlDsa.Arm.Arith.AddSub.Step, VG.Proof.MlDsa.Arm.Arith.AddSub.fixS, h0, h1, h2, ia, ib, oa, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

theorem subBody_ok :
    WP isa (.block VG.Impl.MlDsa.Arm.Arith.subBody) s (VG.Proof.MlDsa.Arm.Arith.AddSub.Step s x y c (VG.Proof.MlDsa.Arm.Arith.AddSub.fixS (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 -
      s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32))) := by
  run_block [VG.Impl.MlDsa.Arm.Arith.subBody, fixupS, VG.Impl.MlDsa.Arm.Arith.accTail, VG.Proof.MlDsa.Arm.Arith.AddSub.Step, VG.Proof.MlDsa.Arm.Arith.AddSub.fixS, h0, h1, h2, ia, ib, oa, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev pf : BitVec 32 := s₀.gpr .r0
abbrev pg : BitVec 32 := s₀.gpr .r1
abbrev F : Addr := State.addr (VG.Proof.MlDsa.Arm.Arith.AddSub.pf s₀)
abbrev G : Addr := State.addr (VG.Proof.MlDsa.Arm.Arith.AddSub.pg s₀)

end

/-- The precondition of both functions. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (VG.Proof.MlDsa.Arm.Arith.AddSub.G s₀)]
  wr : s₀.wr = [polyRegion (VG.Proof.MlDsa.Arm.Arith.AddSub.F s₀)]
  disj : (polyRegion (VG.Proof.MlDsa.Arm.Arith.AddSub.F s₀)).Disjoint (polyRegion (VG.Proof.MlDsa.Arm.Arith.AddSub.G s₀))
  fitF : (VG.Proof.MlDsa.Arm.Arith.AddSub.pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitG : (VG.Proof.MlDsa.Arm.Arith.AddSub.pg s₀).toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s₀.mem (VG.Proof.MlDsa.Arm.Arith.AddSub.F s₀)
  redG : Reduced s₀.mem (VG.Proof.MlDsa.Arm.Arith.AddSub.G s₀)

/-- After `i` iterations, writing `out j` to coefficient `j`. -/
structure Inv (out : Nat → BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = VG.Proof.MlDsa.Arm.Arith.AddSub.pf s₀ + BitVec.ofNat 32 (4 * i)
  r1 : s.gpr .r1 = VG.Proof.MlDsa.Arm.Arith.AddSub.pg s₀ + BitVec.ofNat 32 (4 * i)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (256 - i))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (VG.Proof.MlDsa.Arm.Arith.AddSub.F s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (VG.Proof.MlDsa.Arm.Arith.AddSub.F s₀) j = if j < i then out j else coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.AddSub.F s₀) j

theorem ptr_succ (p : BitVec 32) (k i : Nat) :
    p + BitVec.ofNat 32 (k * i) + BitVec.ofNat 32 k = p + BitVec.ofNat 32 (k * (i + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]

/-- One iteration, from the value the body stores. -/
theorem inv_step {out : Nat → BitVec 32} {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Arith.AddSub.Pre s₀) {i : Nat} (hi : i < 256)
    {s : State} (h : VG.Proof.MlDsa.Arm.Arith.AddSub.Inv out s₀ i s) {body : List Instr}
    (hb : ∀ {x y c : BitVec 32}, s.gpr .r0 = x → s.gpr .r1 = y → s.gpr .r2 = c →
      InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
      InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4 →
      InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4 →
      WP isa (.block body) s (VG.Proof.MlDsa.Arm.Arith.AddSub.Step s x y c (out i))) :
    WP isa (.block body) s fun s' => VG.Proof.MlDsa.Arm.Arith.AddSub.Inv out s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 256) := by
  have fF := hp.fitF
  have fG := hp.fitG
  have eF : State.addr (VG.Proof.MlDsa.Arm.Arith.AddSub.pf s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (VG.Proof.MlDsa.Arm.Arith.AddSub.F s₀) i :=
    addr_ptr _ _ _ (by omega)
  have eG : State.addr (VG.Proof.MlDsa.Arm.Arith.AddSub.pg s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (VG.Proof.MlDsa.Arm.Arith.AddSub.G s₀) i :=
    addr_ptr _ _ _ (by omega)
  have cF := coeff_contains (VG.Proof.MlDsa.Arm.Arith.AddSub.F s₀) (i := i) hi
  have cG := coeff_contains (VG.Proof.MlDsa.Arm.Arith.AddSub.G s₀) (i := i) hi
  refine WP.mono (hb h.r0 h.r1 h.r2 ?_ ?_ ?_) fun s' ⟨r0, r1, r2, z, m, rd, wr, sp, pres⟩ => ⟨⟨?_, ?_, ?_,
    rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [eF, h.rd, h.wr, hp.rd, hp.wr]; exact inRegions_of (by simp) cF
  · rw [eG, h.rd, h.wr, hp.rd, hp.wr]; exact inRegions_of (by simp) cG
  · rw [eF, h.wr, hp.wr]; exact inRegions_of (by simp) cF
  · rw [r0]; exact VG.Proof.MlDsa.Arm.Arith.AddSub.ptr_succ _ 4 i
  · rw [r1]; exact VG.Proof.MlDsa.Arm.Arith.AddSub.ptr_succ _ 4 i
  · rw [r2]; exact count_sub (k := 1) hi
  · rw [m, eF]
    exact h.frame.writeW (List.mem_singleton_self _) _ cF
  · intro j hj
    rw [m, eF, coeffAt_writeW _ _ hj hi, h.coeff j hj]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right hij]
      by_cases hj' : j < i
      · rw [ite_eq_left hj', ite_eq_left (by omega)]
      · rw [ite_eq_right hj', ite_eq_right (by omega)]
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

/-- The whole loop. -/
theorem loop_ok {out : Nat → BitVec 32} {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Arith.AddSub.Pre s₀) {body : List Instr}
    (hb : ∀ i < 256, ∀ s, VG.Proof.MlDsa.Arm.Arith.AddSub.Inv out s₀ i s → ∀ {x y c : BitVec 32}, s.gpr .r0 = x → s.gpr .r1 = y →
      s.gpr .r2 = c → InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
      InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4 →
      InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4 →
      WP isa (.block body) s (VG.Proof.MlDsa.Arm.Arith.AddSub.Step s x y c (out i))) :
    WP isa (.seq (.block [.mov .r2 (.imm 256)]) (.loop (.block body) .ne)) s₀ (VG.Proof.MlDsa.Arm.Arith.AddSub.Inv out s₀ 256) := by
  refine WP.seq (WP.of_runBlock ?_)
  refine ⟨_, runBlock_cons.trans (by rfl), wp_loop_ne (VG.Proof.MlDsa.Arm.Arith.AddSub.Inv out s₀) (N := 256) (by decide)
    (fun i hi s h => VG.Proof.MlDsa.Arm.Arith.AddSub.inv_step hp hi h (hb i hi s h)) (fun _ h => h) ?_⟩
  refine ⟨by simp [State.setReg], by simp [State.setReg], rfl, rfl, rfl, rfl,
    fun r hr => ?_, Frame.refl _ _, fun j _ => rfl⟩
  simp only [State.setReg]
  rw [ite_eq_right]
  intro e; subst e; simp [preserved] at hr

/-! ## Correctness -/

/-- The value stored in coefficient `j` by `vg_mldsa_add`. -/
def addOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((VG.Spec.MlDsa.add (polyAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.AddSub.F s₀)) (polyAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.AddSub.G s₀)))[j]!).val

/-- The value stored in coefficient `j` by `vg_mldsa_sub`. -/
def subOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((VG.Spec.MlDsa.sub (polyAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.AddSub.F s₀)) (polyAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.AddSub.G s₀)))[j]!).val

/-- What an iteration reads: coefficient `i` of each polynomial, as on entry. -/
theorem reads {out : Nat → BitVec 32} {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Arith.AddSub.Pre s₀) {i : Nat} (hi : i < 256) {s : State}
    (h : VG.Proof.MlDsa.Arm.Arith.AddSub.Inv out s₀ i s) {x y : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) :
    s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.AddSub.F s₀) i ∧
      s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.AddSub.G s₀) i := by
  have fF := hp.fitF
  have fG := hp.fitG
  rw [← h0, ← h1, h.r0, h.r1, addr_ptr _ _ _ (by omega), addr_ptr _ _ _ (by omega)]
  refine ⟨?_, ?_⟩
  · show coeffAt s.mem (VG.Proof.MlDsa.Arm.Arith.AddSub.F s₀) i = _
    rw [h.coeff i hi, ite_eq_right (Nat.lt_irrefl i)]
  · show coeffAt s.mem (VG.Proof.MlDsa.Arm.Arith.AddSub.G s₀) i = _
    exact coeffAt_frame h.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm) hi

theorem add_hb {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Arith.AddSub.Pre s₀) : ∀ i < 256, ∀ s, VG.Proof.MlDsa.Arm.Arith.AddSub.Inv (VG.Proof.MlDsa.Arm.Arith.AddSub.addOut s₀) s₀ i s →
    ∀ {x y c : BitVec 32}, s.gpr .r0 = x → s.gpr .r1 = y → s.gpr .r2 = c →
      InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
      InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4 →
      InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4 →
      WP isa (.block VG.Impl.MlDsa.Arm.Arith.addBody) s (VG.Proof.MlDsa.Arm.Arith.AddSub.Step s x y c (VG.Proof.MlDsa.Arm.Arith.AddSub.addOut s₀ i)) := by
  intro i hi s h x y c h0 h1 h2 ia ib oa
  obtain ⟨ea, eb⟩ := VG.Proof.MlDsa.Arm.Arith.AddSub.reads hp hi h h0 h1
  refine WP.mono (VG.Proof.MlDsa.Arm.Arith.AddSub.addBody_ok h0 h1 h2 ia ib oa) fun s' hs => ?_
  rw [ea, eb] at hs
  refine (?_ : _ = VG.Proof.MlDsa.Arm.Arith.AddSub.addOut s₀ i) ▸ hs
  refine VG.Proof.MlDsa.Arm.Arith.ofNat_val_eq ?_
  rw [VG.Proof.MlDsa.Arm.Arith.AddSub.fixS_add (hp.redF i hi) (hp.redG i hi), add_get _ _ hi, val_add', polyAt_val hp.redF hi,
    polyAt_val hp.redG hi]

theorem sub_hb {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Arith.AddSub.Pre s₀) : ∀ i < 256, ∀ s, VG.Proof.MlDsa.Arm.Arith.AddSub.Inv (VG.Proof.MlDsa.Arm.Arith.AddSub.subOut s₀) s₀ i s →
    ∀ {x y c : BitVec 32}, s.gpr .r0 = x → s.gpr .r1 = y → s.gpr .r2 = c →
      InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
      InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4 →
      InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4 →
      WP isa (.block VG.Impl.MlDsa.Arm.Arith.subBody) s (VG.Proof.MlDsa.Arm.Arith.AddSub.Step s x y c (VG.Proof.MlDsa.Arm.Arith.AddSub.subOut s₀ i)) := by
  intro i hi s h x y c h0 h1 h2 ia ib oa
  obtain ⟨ea, eb⟩ := VG.Proof.MlDsa.Arm.Arith.AddSub.reads hp hi h h0 h1
  refine WP.mono (VG.Proof.MlDsa.Arm.Arith.AddSub.subBody_ok h0 h1 h2 ia ib oa) fun s' hs => ?_
  rw [ea, eb] at hs
  refine (?_ : _ = VG.Proof.MlDsa.Arm.Arith.AddSub.subOut s₀ i) ▸ hs
  refine VG.Proof.MlDsa.Arm.Arith.ofNat_val_eq ?_
  rw [VG.Proof.MlDsa.Arm.Arith.AddSub.fixS_sub (hp.redF i hi) (hp.redG i hi), sub_get _ _ hi, val_sub', polyAt_val hp.redF hi,
    polyAt_val hp.redG hi, Nat.add_sub_assoc (by have := hp.redG i hi; omega)]

/-- The loop's result: `f` is `out` of each coefficient. -/
theorem polyIs_of_inv {out : Nat → BitVec 32} {s₀ s : State} {g : Poly}
    (h : VG.Proof.MlDsa.Arm.Arith.AddSub.Inv out s₀ 256 s) (hg : ∀ j < 256, out j = BitVec.ofNat 32 (g[j]!).val) :
    PolyIs s.mem (VG.Proof.MlDsa.Arm.Arith.AddSub.F s₀) g :=
  polyIs_of_toNat fun j hj => by rw [h.coeff j hj, ite_eq_left hj, hg j hj, VG.Proof.MlDsa.Arm.Arith.toNat_val]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlDsa.addContract Arm.abi).pre s) : VG.Proof.MlDsa.Arm.Arith.AddSub.Pre s := by
  sig_pre [Spec.MlDsa.addContract, Spec.MlDsa.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem pre_of_sub {s : State} (h : (Spec.MlDsa.subContract Arm.abi).pre s) : VG.Proof.MlDsa.Arm.Arith.AddSub.Pre s := by
  sig_pre [Spec.MlDsa.subContract, Spec.MlDsa.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem reduced_zero (p : Addr) : Reduced (fun _ => 0) p := fun i _ => by
  rw [coeffAt_eq]
  have : Mem.readW (fun _ => (0 : Byte)) (coeffAddr p i) 32 = 0 := by
    simp [Mem.readW, Mem.read]
  rw [this]; decide

/-- The taint analysis, with the registers `rs` public. -/
theorem ctRegs {k : Contract isa} (rs : List Reg)
    (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    ConstantTime isa k.pre k.pub c :=
  VG.Taint.constantTime (A := VG.Arm.taint) (Taint.ofRegs rs)
    (fun s₁ s₂ _ _ hp => Taint.agree_ofRegs (hpub s₁ s₂ hp)) h

theorem add_verified : Verified Arm.target Impl.MlDsa.Arm.Arith.add (Spec.MlDsa.addContract Arm.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlDsa.Arm.Arith.AddSub.ctRegs [.r0, .r1] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := VG.Proof.MlDsa.Arm.Arith.AddSub.pre_of hs
    obtain ⟨t, s', he, h⟩ := VG.Proof.MlDsa.Arm.Arith.AddSub.loop_ok hp (VG.Proof.MlDsa.Arm.Arith.AddSub.add_hb hp)
    refine ⟨t, s', he, ⟨h.pres, h.sp⟩, ?_⟩
    sig_post [Spec.MlDsa.addContract, Spec.MlDsa.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact VG.Proof.MlDsa.Arm.Arith.AddSub.polyIs_of_inv h fun j _ => rfl
  · sig_pub [Spec.MlDsa.addContract, Spec.MlDsa.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · refine ⟨VG.Proof.MlDsa.Arm.Arith.AddSub.satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.addContract, Spec.MlDsa.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact VG.Proof.MlDsa.Arm.Arith.AddSub.reduced_zero _

theorem sub_verified : Verified Arm.target Impl.MlDsa.Arm.Arith.sub (Spec.MlDsa.subContract Arm.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlDsa.Arm.Arith.AddSub.ctRegs [.r0, .r1] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := VG.Proof.MlDsa.Arm.Arith.AddSub.pre_of_sub hs
    obtain ⟨t, s', he, h⟩ := VG.Proof.MlDsa.Arm.Arith.AddSub.loop_ok hp (VG.Proof.MlDsa.Arm.Arith.AddSub.sub_hb hp)
    refine ⟨t, s', he, ⟨h.pres, h.sp⟩, ?_⟩
    sig_post [Spec.MlDsa.subContract, Spec.MlDsa.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact VG.Proof.MlDsa.Arm.Arith.AddSub.polyIs_of_inv h fun j _ => rfl
  · sig_pub [Spec.MlDsa.subContract, Spec.MlDsa.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · refine ⟨VG.Proof.MlDsa.Arm.Arith.AddSub.satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.subContract, Spec.MlDsa.accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact VG.Proof.MlDsa.Arm.Arith.AddSub.reduced_zero _

end VG.Proof.MlDsa.Arm.Arith.AddSub

end
