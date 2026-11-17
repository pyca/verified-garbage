module

public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.MlKem.Arm.Common
public import VerifiedGarbage.Proof.MlDsa.Arith.Mul32
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Common

/-!
# ML-DSA on 32-bit ARM: the values of the arithmetic modulo `q`

What the pieces of code of `Impl/MlDsa/Arm/Arith/Common.lean` compute, as
functions on words (`bred`, `bcsub`, `bquot`, `bmulq`, `bmulz`), and their
values (`bmulz_toNat`: `mulz` is `mulzN`, congruent to the product and less
than `2q`), from the arithmetic of `Proof/MlDsa/Arith/Mul32.lean`; and the
symbolic execution of `mulz`, once for any state (`mulz_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Arith

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

/-! ## Words -/

/-- `q` as a word. -/
abbrev Qw : BitVec 32 := 8380417

theorem loadQ_val : ((0x7F : BitVec 16) ++ ((0xE001 : BitVec 16).setWidth 32).extractLsb' 0 16 : BitVec 32) = Qw := by
  decide

/-- `-q` as a word. -/
abbrev Nw : BitVec 32 := 4286586879

theorem loadNQ_val : ((0xFF80 : BitVec 16) ++ ((0x1FFF : BitVec 16).setWidth 32).extractLsb' 0 16 : BitVec 32) = Nw := by
  decide

/-- What `red d t N` leaves in `d`. -/
def bred (x : BitVec 32) : BitVec 32 := x >>> 23 * Nw + x

/-- What `csub d t Q` leaves in `d`. -/
def bcsub (x : BitVec 32) : BitVec 32 := (x - Qw) >>> 31 * Qw + (x - Qw)

/-- What `quot zp z` leaves in `zp`. -/
def bquot (z : BitVec 32) : BitVec 32 := (z + z >>> 10) >>> 7

/-- What `mulq acc b z zp t N` leaves in `acc`. -/
def bmulq (b z zp : BitVec 32) : BitVec 32 := (b >>> 8 * zp) >>> 8 * Nw + b * z

/-- What `mulz acc b t` leaves in `acc`, for `z` and `zp` in `r6` and `r7`. -/
def bmulz (b z zp : BitVec 32) : BitVec 32 := bred (bmulq (bred b) z zp)

theorem bred_toNat (x : BitVec 32) : (bred x).toNat = red23 x.toNat := by
  unfold bred red23
  rw [q_eq]
  bv_omega

theorem bcsub_toNat {x : BitVec 32} (h : x.toNat < 2 * q) : (bcsub x).toNat = x.toNat % q := by
  unfold bcsub
  rw [q_eq] at *
  by_cases h' : x.toNat < 8380417
  · rw [Nat.mod_eq_of_lt h']; bv_omega
  · bv_omega

theorem bquot_toNat {z : BitVec 32} (hz : z.toNat < q) : (bquot z).toNat = quotN z.toNat := by
  unfold bquot quotN
  rw [q_eq] at hz
  bv_omega

/-- The low 32 bits of `X - Q · q`, computed as `Q · (2³² - q) + X`. -/
theorem sub_mul_low {X Q : Nat} (h : Q * q ≤ X) (hl : X - Q * q < 2 ^ 32) :
    (Q * 4286586879 % 2 ^ 32 + X % 2 ^ 32) % 2 ^ 32 = X - Q * q := by
  rw [q_eq] at h hl ⊢
  rw [← Nat.add_mod, show Q * 4286586879 + X = X - Q * 8380417 + Q * 2 ^ 32 by omega_using [h],
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]

theorem bmulq_toNat {b z : BitVec 32} (hb : b.toNat ≤ redMax) (hz : z.toNat < q) :
    (bmulq b z (bquot z)).toNat = mulqN b.toNat z.toNat := by
  obtain ⟨h1, h2, h3⟩ := mulqN_bounds hb hz
  have eP : ((b >>> 8 * bquot z) >>> 8).toNat = b.toNat / 256 * quotN z.toNat / 256 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ushiftRight, bquot_toNat hz, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt h1]
  unfold bmulq
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul, eP, show Nw.toNat = 4286586879 from rfl]
  exact sub_mul_low h2 (by unfold mulqN at h3; omega_using [h3])

theorem bmulz_toNat (b : BitVec 32) {z : BitVec 32} (hz : z.toNat < q) :
    (bmulz b z (bquot z)).toNat = mulzN b.toNat z.toNat := by
  unfold bmulz mulzN
  rw [bred_toNat, bmulq_toNat (by rw [bred_toNat]; exact red23_le b.isLt) hz, bred_toNat]

/-- A word is the element of `ℤ_q` it represents, once reduced. -/
theorem ofNat_val_eq {v : BitVec 32} {x : Zq} (h : v.toNat = x.val) : v = BitVec.ofNat 32 x.val := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega_using [h])]

theorem toNat_val (x : Zq) : (BitVec.ofNat 32 x.val).toNat = x.val := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega_using [this])]

/-! ## Registers kept -/

/-- `s'` has the registers `rs`, and the regions and stack pointer, of `s`. -/
structure Keep (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r ∈ rs, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem keep_iff {rs : List Reg} {s s' : State} :
    Keep rs s s' ↔ (∀ r ∈ rs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨fun h => ⟨h.gpr, h.rd, h.wr, h.sp⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- The lemmas that prove `Keep` after a symbolic execution (`run_block`). -/
macro "keep_simp" : tactic => `(tactic| plain_simp_names (
                   set_option linter.unusedSimpArgs false in
                   simp (config := {decide := true}) only [keep_iff, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
                     implies_true, and_self, and_true, true_and, ite_true, ite_false]))

theorem Keep.refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keep.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂) (h₂ : Keep rs s₂ s₃) :
    Keep rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s') (hs : ∀ r ∈ rs', r ∈ rs) :
    Keep rs' s s' :=
  ⟨fun r hr => h.gpr r (hs r hr), h.rd, h.wr, h.sp⟩

/-! ## `mulz`, symbolically -/

/-- What `mulz .r10 .r9 .r12` does: `r10` becomes the product, `r9` and `r12`
are clobbered, and nothing else changes. -/
theorem mulz_ok {s : State} {b z zp : BitVec 32} (h4 : s.gpr .r4 = Nw) (h6 : s.gpr .r6 = z) (h7 : s.gpr .r7 = zp)
    (h9 : s.gpr .r9 = b) :
    WP isa (.block (mulz .r10 .r9 .r12)) s fun s' =>
      s'.gpr .r10 = bmulz b z zp ∧ (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [mulz, red, mulq, bmulz, bmulq, bred, h4, h6, h7, h9]
  exact ⟨trivial, fun r h9 h10 h12 => by simp [h9, h10, h12], trivial⟩

end VG.Proof.MlDsa.Arm.Arith
