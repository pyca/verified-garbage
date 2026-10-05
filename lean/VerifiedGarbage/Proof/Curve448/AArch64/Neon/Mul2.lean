import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Lanes
import VerifiedGarbage.Proof.X448.AArch64.PointwiseSmall
import VerifiedGarbage.Impl.Curve448.AArch64.Neon
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Range
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import VerifiedGarbage.Proof.Framework.PowLit
import Mathlib.Algebra.BigOperators.Group.List.Basic
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Field
import VerifiedGarbage.Proof.X448.Encoding

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Neon.Exec`. -/
section

/-!
# The vector loads and stores of `Neon.mul2`

Untrusted: everything here is checked by Lean. `nw m base d` is the 32-bit
word at offset `d` of the working space; vector loads and stores move four of
them at once.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon
open VG.Proof.X448.AArch64 (Scr off ofs Outside)

/-- The 32-bit word at offset `d`. -/
abbrev nw (m : Mem) (base : Addr) (d : Nat) : Nat := (m.readW (VG.Proof.X448.AArch64.off base d) 32).toNat

theorem off_add (base : Addr) (d e : Nat) : VG.Proof.X448.AArch64.off base d + BitVec.ofNat 64 e = VG.Proof.X448.AArch64.off base (d + e) := by
  simp only [VG.Proof.X448.AArch64.off, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem exec_ldq {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) (t : Nat) {d : Nat} (h16 : d % 16 = 0)
    (hd : d + 16 ≤ 8192) : isa.exec (ldq t d) s = some (s.setV (V t) (s.mem.read (VG.Proof.X448.AArch64.off base d) 16)) := by
  have hr := hs.read (d := d) (n := 16) hd
  simp only [ldq, exec, addr, show d % 16 = 0 ∧ d < 4096 * 16 from ⟨h16, by omega⟩, and_self, ite_true,
    Option.bind_some, State.load, hs.x3]
  rw [ite_eq_left_iff.mpr fun h => absurd hr h]
  rfl

theorem vword_ld (m : Mem) (base : Addr) (d : Nat) {c : Nat} (hc : c < 4) :
    (vword (m.read (VG.Proof.X448.AArch64.off base d) 16) c).toNat = VG.Proof.Curve448.AArch64.Neon.nw m base (d + 4 * c) := by
  rw [vword_read16 _ _ hc, VG.Proof.Curve448.AArch64.Neon.off_add]

/-- `s` with memory `m`. -/
def setMem (s : State) (m : Mem) : State := { s with mem := m }

@[simp] theorem setMem_mem (s : State) (m : Mem) : (VG.Proof.Curve448.AArch64.Neon.setMem s m).mem = m := rfl
@[simp] theorem setMem_v (s : State) (m : Mem) : (VG.Proof.Curve448.AArch64.Neon.setMem s m).v = s.v := rfl
@[simp] theorem setMem_gpr (s : State) (m : Mem) : (VG.Proof.Curve448.AArch64.Neon.setMem s m).gpr = s.gpr := rfl
@[simp] theorem setMem_rd (s : State) (m : Mem) : (VG.Proof.Curve448.AArch64.Neon.setMem s m).rd = s.rd := rfl
@[simp] theorem setMem_wr (s : State) (m : Mem) : (VG.Proof.Curve448.AArch64.Neon.setMem s m).wr = s.wr := rfl
@[simp] theorem setMem_sp (s : State) (m : Mem) : (VG.Proof.Curve448.AArch64.Neon.setMem s m).sp = s.sp := rfl
@[simp] theorem setMem_c (s : State) (m : Mem) : (VG.Proof.Curve448.AArch64.Neon.setMem s m).c = s.c := rfl

theorem exec_stq {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) (t : Nat) {d : Nat} (h16 : d % 16 = 0)
    (hd : d + 16 ≤ 8192) :
    isa.exec (stq t d) s = some (VG.Proof.Curve448.AArch64.Neon.setMem s (s.mem.write (VG.Proof.X448.AArch64.off base d) 16 (s.v (V t)))) := by
  have hw := hs.write (d := d) (n := 16) hd
  simp only [stq, exec, addr, show d % 16 = 0 ∧ d < 4096 * 16 from ⟨h16, by omega⟩, and_self, ite_true,
    Option.bind_some, State.store, hs.x3]
  rw [ite_eq_left_iff.mpr fun h => absurd hw h]
  rfl

theorem nw_st (m : Mem) (base : Addr) (d : Nat) (v : BitVec 128) {c : Nat} (hc : c < 4) :
    VG.Proof.Curve448.AArch64.Neon.nw (m.write (VG.Proof.X448.AArch64.off base d) 16 v) base (d + 4 * c) = (vword v c).toNat := by
  rw [VG.Proof.Curve448.AArch64.Neon.nw, ← VG.Proof.Curve448.AArch64.Neon.off_add, write16_word _ _ _ hc]

theorem st_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 128) (h : d + 16 ≤ 8192) :
    VG.Proof.X448.AArch64.Outside base d 16 m (m.write (VG.Proof.X448.AArch64.off base d) 16 v) := by
  intro x hx
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [VG.Proof.X448.AArch64.ofs] at hx
  omega

theorem Outside.nw {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.AArch64.Outside base o n m m') {d : Nat}
    (hd : d + 4 ≤ o ∨ o + n ≤ d) (hd' : d + 4 ≤ 8192) : VG.Proof.Curve448.AArch64.Neon.nw m' base d = VG.Proof.Curve448.AArch64.Neon.nw m base d :=
  congrArg BitVec.toNat
    (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)]; omega)).symm).symm

theorem nw_st_other (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 128) (h : d + 16 ≤ 8192)
    (h' : d' + 4 ≤ 8192) (hd : d' + 4 ≤ d ∨ d + 16 ≤ d') : VG.Proof.Curve448.AArch64.Neon.nw (m.write (VG.Proof.X448.AArch64.off base d) 16 v) base d' = VG.Proof.Curve448.AArch64.Neon.nw m base d' :=
  Outside.nw (VG.Proof.Curve448.AArch64.Neon.st_outside m base v h) hd h'

theorem scr_of {s t : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) (hg : t.gpr = s.gpr) (hw : t.wr = s.wr) :
    VG.Proof.X448.AArch64.Scr t base := ⟨by rw [hg]; exact hs.x3, by rw [hg]; exact hs.mask, hw ▸ hs.wr, hs.nowrap⟩

/-- Read vector registers through the writes after them (distinctness from the context). -/
macro "vred" : tactic =>
  `(tactic| simp (disch := assumption) only [RegUpd.v_setV_self, RegUpd.v_setV_of_ne, RegUpd.mem_setV,
    setMem_mem, setMem_v])

/-- `Scr` of a state the vector code built from one where it holds. -/
macro "scr" : tactic =>
  `(tactic| exact scr_of (by assumption) (by simp only [RegUpd.gpr_setV, setMem_gpr])
    (by simp only [RegUpd.wr_setV, setMem_wr]))

end VG.Proof.Curve448.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Neon.Convert`. -/
section

/-!
# Splitting two elements' limbs into radix-2²⁸ vectors

Untrusted: everything here is checked by Lean. `convert x₁ x₂ dst` stores, as
word `c` of vector `i` at `dst`, the low 28 bits of limb `i` of element `c`
(`c < 2`) or the rest of limb `i` of element `c - 2`.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon
open VG.Proof.X448.AArch64 (Scr off ofs Outside word limbs)

/-- Word `c` of vector `i` of two elements' radix-2²⁸ limbs. -/
def split (f₁ f₂ : Nat → Nat) (i c : Nat) : Nat :=
  if c = 0 then f₁ i % 2 ^ 28 else if c = 1 then f₂ i % 2 ^ 28 else if c = 2 then f₁ i / 2 ^ 28 else f₂ i / 2 ^ 28

theorem V_ne : ∀ a < 32, ∀ b < 32, a ≠ b → V a ≠ V b := by decide

/-! ## Lanes of the conversion's operations -/

theorem lo28 (x m : BitVec 128) (hm : ∀ e < 2, (vdword m e).toNat = 2 ^ 28 - 1) (e : Nat) (he : e < 2) :
    (vdword (x &&& m) e).toNat = (vdword x e).toNat % 2 ^ 28 := by
  rw [vdword_and, BitVec.toNat_and, hm e he, Nat.and_two_pow_sub_one_eq_mod]

theorem ushr28 (y x : BitVec 128) (e : Nat) (he : e < 2) :
    (vdword (VArr.d2.map2 (fun w a b => VShiftOp.eval .ushr 28 w a b) y x) e).toNat = (vdword x e).toNat / 2 ^ 28 := by
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · rw [map2_0]; simp [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · rw [map2_1]; simp [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem vword_0 (x : BitVec 128) : (vword x 0).toNat = (vdword x 0).toNat % 2 ^ 32 := vword_lo x 0
theorem vword_2 (x : BitVec 128) : (vword x 2).toNat = (vdword x 1).toNat % 2 ^ 32 := vword_lo x 1

/-- The four words of `uzp1 r, lo, hi`, for `lo` and `hi` the low and high parts of `x`. -/
theorem uzp_words (lo hi : BitVec 128) (c : Nat) (hc : c < 4) :
    (vword (VPermOp.eval .uzp1 .s4 lo hi) c).toNat =
      if c = 0 then (vdword lo 0).toNat % 2 ^ 32 else if c = 1 then (vdword lo 1).toNat % 2 ^ 32
      else if c = 2 then (vdword hi 0).toNat % 2 ^ 32 else (vdword hi 1).toNat % 2 ^ 32 := by
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [uzp1_0, VG.Proof.Curve448.AArch64.Neon.vword_0]; rfl
  · rw [uzp1_1, VG.Proof.Curve448.AArch64.Neon.vword_2]; rfl
  · rw [uzp1_2, VG.Proof.Curve448.AArch64.Neon.vword_0]; rfl
  · rw [uzp1_3, VG.Proof.Curve448.AArch64.Neon.vword_2]; rfl


/-! ## Execution -/

theorem scr_setV {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) (r : VReg) (x : BitVec 128) :
    VG.Proof.X448.AArch64.Scr (s.setV r x) base := ⟨hs.x3, hs.mask, hs.wr, hs.nowrap⟩

theorem scr_mem {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) (m : Mem) : VG.Proof.X448.AArch64.Scr { s with
                                                                                     mem := m } base :=
  ⟨hs.x3, hs.mask, hs.wr, hs.nowrap⟩

theorem exec_vo_of {op : VOp} {s : State} {d : VReg} {x : BitVec 128} (h : op.eval s = some (d, x)) :
    isa.exec (vo op) s = some (s.setV d x) := by
  show (op.eval s).map (fun p => s.setV p.1 p.2) = _
  rw [h]; rfl

/-- One step of `convert`: limbs `2k` and `2k + 1` of both elements. -/
def convChunk (x₁ x₂ dst X Y P Q k : Nat) : List Instr :=
  [ldq X (x₁ + 16 * k), ldq Y (x₂ + 16 * k),
    vo (.perm .trn1 .d2 (V P) (V X) (V Y)), vo (.perm .trn2 .d2 (V Q) (V X) (V Y)),
    vo (.logic .and (V X) (V P) (V 30)), vo (.shift .ushr .d2 (V Y) (V P) 28),
    vo (.perm .uzp1 .s4 (V P) (V X) (V Y)), stq P (dst + 16 * (2 * k)),
    vo (.logic .and (V X) (V Q) (V 30)), vo (.shift .ushr .d2 (V Y) (V Q) 28),
    vo (.perm .uzp1 .s4 (V Q) (V X) (V Y)), stq Q (dst + 16 * (2 * k + 1))]

theorem convert_eq (x₁ x₂ dst X Y P Q : Nat) :
    convert x₁ x₂ dst X Y P Q = (List.range 4).flatMap (VG.Proof.Curve448.AArch64.Neon.convChunk x₁ x₂ dst X Y P Q) := rfl

/-- A vector holding limbs `2k` of two elements (lanes 0 and 1), split. -/
theorem split_words {lo hi : BitVec 128} {a b : Nat}
    (hlo : ∀ e < 2, (vdword lo e).toNat = (if e = 0 then a else b) % 2 ^ 28)
    (hhi : ∀ e < 2, (vdword hi e).toNat = (if e = 0 then a else b) / 2 ^ 28)
    (ha : a < 2 ^ 60) (hb : b < 2 ^ 60) (c : Nat) (hc : c < 4) :
    (vword (VPermOp.eval .uzp1 .s4 lo hi) c).toNat =
      if c = 0 then a % 2 ^ 28 else if c = 1 then b % 2 ^ 28 else if c = 2 then a / 2 ^ 28 else b / 2 ^ 28 := by
  rw [VG.Proof.Curve448.AArch64.Neon.uzp_words lo hi c hc, hlo 0 (by decide), hlo 1 (by decide), hhi 0 (by decide), hhi 1 (by decide)]
  simp only [ite_true, show (1 : Nat) ≠ 0 by decide, ite_false]
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [ite_true, ite_false, show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
      show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide,
      show (3 : Nat) ≠ 2 by decide] <;> omega


theorem limb_ld (m : Mem) (base : Addr) (x k : Nat) (e : Nat) (he : e < 2) :
    (vdword (m.read (VG.Proof.X448.AArch64.off base (x + 16 * k)) 16) e).toNat = limbs m base x (2 * k + e) := by
  rw [vdword_read16 _ _ he, VG.Proof.Curve448.AArch64.Neon.off_add]
  simp only [limbs, VG.Proof.X448.AArch64.word]
  congr 3
  omega

/-- What one step of `convert` does. -/
theorem convChunk_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {x₁ x₂ dst X Y P Q k : Nat} (hk : k < 4)
    (h₁ : x₁ % 16 = 0) (h₁' : x₁ + 64 ≤ 8192) (h₂ : x₂ % 16 = 0) (h₂' : x₂ + 64 ≤ 8192)
    (hd : dst % 16 = 0) (hd' : dst + 128 ≤ 8192)
    (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1)
    (nXY : V X ≠ V Y) (nXP : V X ≠ V P) (nXQ : V X ≠ V Q) (nYP : V Y ≠ V P) (nYQ : V Y ≠ V Q)
    (nPQ : V P ≠ V Q) (n30 : ∀ r ∈ [X, Y, P, Q], V r ≠ V 30)
    (hl₁ : ∀ i < 8, limbs s.mem base x₁ i < 2 ^ 60) (hl₂ : ∀ i < 8, limbs s.mem base x₂ i < 2 ^ 60) :
    WP isa (.block (VG.Proof.Curve448.AArch64.Neon.convChunk x₁ x₂ dst X Y P Q k)) s fun t =>
      (∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t.mem base (dst + 16 * (2 * k) + 4 * c) =
        VG.Proof.Curve448.AArch64.Neon.split (limbs s.mem base x₁) (limbs s.mem base x₂) (2 * k) c) ∧
      (∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t.mem base (dst + 16 * (2 * k + 1) + 4 * c) =
        VG.Proof.Curve448.AArch64.Neon.split (limbs s.mem base x₁) (limbs s.mem base x₂) (2 * k + 1) c) ∧
      VG.Proof.X448.AArch64.Outside base (dst + 32 * k) 32 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, r ∉ [V X, V Y, V P, V Q] → t.v r = s.v r) := by
  have e1 : x₁ + 16 * k + 16 ≤ 8192 := by omega
  have e2 : x₂ + 16 * k + 16 ≤ 8192 := by omega
  have a1 : (x₁ + 16 * k) % 16 = 0 := by omega
  have a2 : (x₂ + 16 * k) % 16 = 0 := by omega
  have dP : (dst + 16 * (2 * k)) % 16 = 0 := by omega
  have dQ : (dst + 16 * (2 * k + 1)) % 16 = 0 := by omega
  have dP' : dst + 16 * (2 * k) + 16 ≤ 8192 := by omega
  have dQ' : dst + 16 * (2 * k + 1) + 16 ≤ 8192 := by omega
  simp only [VG.Proof.Curve448.AArch64.Neon.convChunk]
  -- the loads
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_ldq hs X a1 e1, ?_⟩
  have hs1 := VG.Proof.Curve448.AArch64.Neon.scr_setV hs (V X) (s.mem.read (VG.Proof.X448.AArch64.off base (x₁ + 16 * k)) 16)
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_ldq hs1 Y a2 e2, ?_⟩
  generalize hA : s.mem.read (VG.Proof.X448.AArch64.off base (x₁ + 16 * k)) 16 = A at *
  simp only [RegUpd.mem_setV] at *
  generalize hB : s.mem.read (VG.Proof.X448.AArch64.off base (x₂ + 16 * k)) 16 = B
  have hs2 := VG.Proof.Curve448.AArch64.Neon.scr_setV hs1 (V Y) B
  have m30X : V 30 ≠ V X := (n30 X (by simp)).symm
  have m30Y : V 30 ≠ V Y := (n30 Y (by simp)).symm
  have m30P : V 30 ≠ V P := (n30 P (by simp)).symm
  have m30Q : V 30 ≠ V Q := (n30 Q (by simp)).symm
  have nYX := nXY.symm
  have nPX := nXP.symm
  have nQX := nXQ.symm
  have nPY := nYP.symm
  have nQY := nYQ.symm
  have nQP := nPQ.symm
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_stq (base := base) ?h1 P dP dP', ?_⟩
  case h1 => scr
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_stq (base := base) ?h2 Q dQ dQ', ?_⟩
  case h2 => scr
  vred
  refine WP.block_nil_iff.mpr ?_
  simp only [VG.Proof.Curve448.AArch64.Neon.setMem_mem, VG.Proof.Curve448.AArch64.Neon.setMem_gpr, VG.Proof.Curve448.AArch64.Neon.setMem_rd, VG.Proof.Curve448.AArch64.Neon.setMem_wr, VG.Proof.Curve448.AArch64.Neon.setMem_v, RegUpd.gpr_setV, RegUpd.rd_setV,
    RegUpd.wr_setV]
  generalize hT1 : VPermOp.eval .trn1 .d2 A B = T1
  generalize hT2 : VPermOp.eval .trn2 .d2 A B = T2
  generalize hH1 : VArr.d2.map2 (fun w x y => VShiftOp.ushr.eval 28 w x y) B T1 = H1
  generalize hvP : VPermOp.eval .uzp1 .s4 (T1 &&& s.v (V 30)) H1 = vP
  generalize hvQ : VPermOp.eval .uzp1 .s4 (T2 &&& s.v (V 30))
    (VArr.d2.map2 (fun w x y => VShiftOp.ushr.eval 28 w x y) H1 T2) = vQ
  have lA : ∀ e < 2, (vdword A e).toNat = limbs s.mem base x₁ (2 * k + e) := fun e he => by
    rw [← hA]; exact VG.Proof.Curve448.AArch64.Neon.limb_ld _ _ _ _ _ he
  have lB : ∀ e < 2, (vdword B e).toNat = limbs s.mem base x₂ (2 * k + e) := fun e he => by
    rw [← hB]; exact VG.Proof.Curve448.AArch64.Neon.limb_ld _ _ _ _ _ he
  have wP : ∀ c < 4, (vword vP c).toNat = VG.Proof.Curve448.AArch64.Neon.split (limbs s.mem base x₁) (limbs s.mem base x₂) (2 * k) c := by
    intro c hc
    rw [← hvP, VG.Proof.Curve448.AArch64.Neon.split_words (a := limbs s.mem base x₁ (2 * k)) (b := limbs s.mem base x₂ (2 * k))
      (fun e he => by
        rw [VG.Proof.Curve448.AArch64.Neon.lo28 _ _ hM e he, ← hT1]
        rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
        · rw [trn1_0, lA 0 (by decide)]; rfl
        · rw [trn1_1, lB 0 (by decide)]; rfl)
      (fun e he => by
        rw [← hH1, VG.Proof.Curve448.AArch64.Neon.ushr28 _ _ e he, ← hT1]
        rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
        · rw [trn1_0, lA 0 (by decide)]; rfl
        · rw [trn1_1, lB 0 (by decide)]; rfl)
      (hl₁ _ (by omega)) (hl₂ _ (by omega)) c hc]
    rfl
  have wQ : ∀ c < 4, (vword vQ c).toNat = VG.Proof.Curve448.AArch64.Neon.split (limbs s.mem base x₁) (limbs s.mem base x₂) (2 * k + 1) c := by
    intro c hc
    rw [← hvQ, VG.Proof.Curve448.AArch64.Neon.split_words (a := limbs s.mem base x₁ (2 * k + 1)) (b := limbs s.mem base x₂ (2 * k + 1))
      (fun e he => by
        rw [VG.Proof.Curve448.AArch64.Neon.lo28 _ _ hM e he, ← hT2]
        rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
        · rw [trn2_0, lA 1 (by decide)]; rfl
        · rw [trn2_1, lB 1 (by decide)]; rfl)
      (fun e he => by
        rw [VG.Proof.Curve448.AArch64.Neon.ushr28 _ _ e he, ← hT2]
        rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
        · rw [trn2_0, lA 1 (by decide)]; rfl
        · rw [trn2_1, lB 1 (by decide)]; rfl)
      (hl₁ _ (by omega)) (hl₂ _ (by omega)) c hc]
    rfl
  refine ⟨fun c hc => ?_, fun c hc => ?_, ?_, trivial, trivial, trivial, fun r hr => ?_⟩
  · rw [VG.Proof.Curve448.AArch64.Neon.nw_st_other _ _ _ dQ' (by omega) (by omega), VG.Proof.Curve448.AArch64.Neon.nw_st _ _ _ _ hc, wP c hc]
  · rw [VG.Proof.Curve448.AArch64.Neon.nw_st _ _ _ _ hc, wQ c hc]
  · exact ((VG.Proof.Curve448.AArch64.Neon.st_outside _ base _ dP').mono (by omega) (by omega)).trans
      ((VG.Proof.Curve448.AArch64.Neon.st_outside _ base _ dQ').mono (by omega) (by omega))
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r1, r2, r3, r4⟩ := hr
    simp only [RegUpd.v_setV_of_ne _ _ r1, RegUpd.v_setV_of_ne _ _ r2, RegUpd.v_setV_of_ne _ _ r3,
      RegUpd.v_setV_of_ne _ _ r4, VG.Proof.Curve448.AArch64.Neon.setMem_v]


theorem split_congr {f₁ f₂ g₁ g₂ : Nat → Nat} {i : Nat} (h₁ : f₁ i = g₁ i) (h₂ : f₂ i = g₂ i) (c : Nat) :
    VG.Proof.Curve448.AArch64.Neon.split f₁ f₂ i c = VG.Proof.Curve448.AArch64.Neon.split g₁ g₂ i c := by
  simp only [VG.Proof.Curve448.AArch64.Neon.split, h₁, h₂]

theorem limbs_outside {base : Addr} {m m' : Mem} {o n x : Nat} (h : VG.Proof.X448.AArch64.Outside base o n m m')
    (hx : x + 64 ≤ o ∨ o + n ≤ x) (hx' : x + 64 ≤ 8192) {i : Nat} (hi : i < 8) :
    limbs m' base x i = limbs m base x i :=
  congrArg BitVec.toNat (h.word (by omega) (by omega))

/-- `convert x₁ x₂ dst`: the radix-2²⁸ vectors of `[x₁]` and `[x₂]` at `dst`. -/
theorem convert_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {x₁ x₂ dst X Y P Q : Nat}
    (h₁ : x₁ % 16 = 0) (h₁' : x₁ + 64 ≤ 8192) (h₂ : x₂ % 16 = 0) (h₂' : x₂ + 64 ≤ 8192)
    (hd : dst % 16 = 0) (hd' : dst + 128 ≤ 8192) (s₁ : x₁ + 64 ≤ dst ∨ dst + 128 ≤ x₁)
    (s₂ : x₂ + 64 ≤ dst ∨ dst + 128 ≤ x₂)
    (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1)
    (nXY : V X ≠ V Y) (nXP : V X ≠ V P) (nXQ : V X ≠ V Q) (nYP : V Y ≠ V P) (nYQ : V Y ≠ V Q)
    (nPQ : V P ≠ V Q) (n30 : ∀ r ∈ [X, Y, P, Q], V r ≠ V 30)
    (hl₁ : ∀ i < 8, limbs s.mem base x₁ i < 2 ^ 60) (hl₂ : ∀ i < 8, limbs s.mem base x₂ i < 2 ^ 60) :
    WP isa (.block (convert x₁ x₂ dst X Y P Q)) s fun t =>
      (∀ i < 8, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t.mem base (dst + 16 * i + 4 * c) =
        VG.Proof.Curve448.AArch64.Neon.split (limbs s.mem base x₁) (limbs s.mem base x₂) i c) ∧
      VG.Proof.X448.AArch64.Outside base dst 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, r ∉ [V X, V Y, V P, V Q] → t.v r = s.v r) := by
  rw [VG.Proof.Curve448.AArch64.Neon.convert_eq]
  let inv := fun n (t : State) =>
    (∀ i < 2 * n, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t.mem base (dst + 16 * i + 4 * c) =
      VG.Proof.Curve448.AArch64.Neon.split (limbs s.mem base x₁) (limbs s.mem base x₂) i c) ∧
    VG.Proof.X448.AArch64.Outside base dst 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ r : VReg, r ∉ [V X, V Y, V P, V Q] → t.v r = s.v r)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) inv (fun n t hn ⟨tw, tO, tg, tr, twr, tv⟩ => ?_) 4
    (by decide) s ⟨fun _ h => absurd h (by omega), Outside.refl _ _ _ _, rfl, rfl, rfl, fun _ _ => rfl⟩)
    fun t ht => ⟨fun i hi => ht.1 i (by omega), ht.2⟩
  have ht : VG.Proof.X448.AArch64.Scr t base := VG.Proof.Curve448.AArch64.Neon.scr_of hs tg twr
  have t30 : t.v (V 30) = s.v (V 30) := tv _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨(n30 X (by simp)).symm, (n30 Y (by simp)).symm, (n30 P (by simp)).symm, (n30 Q (by simp)).symm⟩)
  have l₁ : ∀ i < 8, limbs t.mem base x₁ i = limbs s.mem base x₁ i := fun i hi => VG.Proof.Curve448.AArch64.Neon.limbs_outside tO s₁ h₁' hi
  have l₂ : ∀ i < 8, limbs t.mem base x₂ i = limbs s.mem base x₂ i := fun i hi => VG.Proof.Curve448.AArch64.Neon.limbs_outside tO s₂ h₂' hi
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.convChunk_ok ht hn h₁ h₁' h₂ h₂' hd hd' (by rw [t30]; exact hM) nXY nXP nXQ nYP nYQ nPQ n30
    (fun i hi => by rw [l₁ i hi]; exact hl₁ i hi) (fun i hi => by rw [l₂ i hi]; exact hl₂ i hi))
    fun u ⟨uP, uQ, uo, ug, ur, uw, uv⟩ => ⟨fun i hi c hc => ?_, tO.trans (uo.mono (by omega) (by omega)),
      ug.trans tg, ur.trans tr, uw.trans twr, fun r hr => (uv r hr).trans (tv r hr)⟩
  rcases (show i < 2 * n ∨ i = 2 * n ∨ i = 2 * n + 1 by omega) with h | rfl | rfl
  · rw [VG.Proof.Curve448.AArch64.Neon.Outside.nw uo (by omega) (by omega)]
    exact tw i h c hc
  · rw [uP c hc]; exact VG.Proof.Curve448.AArch64.Neon.split_congr (l₁ _ (by omega)) (l₂ _ (by omega)) c
  · rw [uQ c hc]; exact VG.Proof.Curve448.AArch64.Neon.split_congr (l₁ _ (by omega)) (l₂ _ (by omega)) c

end VG.Proof.Curve448.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Neon.Macs`. -/
section

/-!
# The products of a half

Untrusted: everything here is checked by Lean. Running a half's products
leaves, in lane `e` of each target register, its starting value (zero for a
register the half starts) plus the products of the half aimed at it, modulo
2⁶⁴.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon
open VG.Proof.X448.AArch64 (Scr off ofs Outside)

/-- The words of a product: `0` and `1`, or `2` and `3` for the `2` forms. -/
abbrev hp (hi : Bool) : Nat := if hi then 2 else 0

/-- Lane `e` of a product of `a` vector `A p.i` and `b` vector `B p.bv`. -/
def prodVal (A B : Nat → BitVec 128) (p : Prod) (e : Nat) : Nat :=
  (vword (A p.i) (VG.Proof.Curve448.AArch64.Neon.hp p.hi + e)).toNat * (vword (B p.bv) (VG.Proof.Curve448.AArch64.Neon.hp p.hi + e)).toNat

/-- The products of `ps` aimed at register `r`, in lane `e`. -/
def prodSum (A B : Nat → BitVec 128) (tgt : Nat → Nat) (ps : List Prod) (r e : Nat) : Int :=
  ((ps.filter fun p => tgt p.pos == r).map fun p => (VG.Proof.Curve448.AArch64.Neon.prodVal A B p e : Int)).sum

theorem prodSum_nil (A B : Nat → BitVec 128) (tgt : Nat → Nat) (r e : Nat) : VG.Proof.Curve448.AArch64.Neon.prodSum A B tgt [] r e = 0 := rfl

theorem prodSum_append (A B : Nat → BitVec 128) (tgt : Nat → Nat) (ps qs : List Prod) (r e : Nat) :
    VG.Proof.Curve448.AArch64.Neon.prodSum A B tgt (ps ++ qs) r e = VG.Proof.Curve448.AArch64.Neon.prodSum A B tgt ps r e + VG.Proof.Curve448.AArch64.Neon.prodSum A B tgt qs r e := by
  simp [VG.Proof.Curve448.AArch64.Neon.prodSum, List.filter_append]

theorem prodSum_single (A B : Nat → BitVec 128) (tgt : Nat → Nat) (p : Prod) (r e : Nat) :
    VG.Proof.Curve448.AArch64.Neon.prodSum A B tgt [p] r e = if tgt p.pos = r then (VG.Proof.Curve448.AArch64.Neon.prodVal A B p e : Int) else 0 := by
  by_cases h : tgt p.pos = r <;> simp [VG.Proof.Curve448.AArch64.Neon.prodSum, h]

/-- Lane `e` of a register, as an integer. -/
abbrev lane (x : BitVec 128) (e : Nat) : Int := ((vdword x e).toNat : Int)

/-- The vector registers a half's products may write. -/
def written (tgt : Nat → Nat) (ps : List Prod) : List Nat := 27 :: ps.map fun p => tgt p.pos


theorem vdword_ofVDwords (a b : BitVec 64) {e : Nat} (he : e < 2) :
    vdword (ofVDwords a b) e = if e = 0 then a else b := by
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · rw [vdword_ofVDwords_0]; rfl
  · rw [vdword_ofVDwords_1]; rfl

abbrev M64 : Int := 2 ^ 64

theorem lane_lt (x : BitVec 128) (e : Nat) : VG.Proof.Curve448.AArch64.Neon.lane x e < VG.Proof.Curve448.AArch64.Neon.M64 := by
  have := (vdword x e).isLt; simp only [VG.Proof.Curve448.AArch64.Neon.lane, VG.Proof.Curve448.AArch64.Neon.M64]; omega

theorem lane_nonneg (x : BitVec 128) (e : Nat) : 0 ≤ VG.Proof.Curve448.AArch64.Neon.lane x e := Int.natCast_nonneg _

/-- One product: `umull` the first time a register it starts is aimed at, `umlal` after. -/
theorem mac_lane (t : State) (tgt : Nat → Nat) (fresh seen : List Nat) (p : Prod) :
    ∃ x, isa.exec (mac tgt fresh seen p) t = some (t.setV (V (tgt p.pos)) x) ∧ ∀ e < 2,
      VG.Proof.Curve448.AArch64.Neon.lane x e % VG.Proof.Curve448.AArch64.Neon.M64 = ((if tgt p.pos ∈ fresh ∧ tgt p.pos ∉ seen then 0 else VG.Proof.Curve448.AArch64.Neon.lane (t.v (V (tgt p.pos))) e) +
        (vword (t.v (V (23 + p.i))) (VG.Proof.Curve448.AArch64.Neon.hp p.hi + e)).toNat * (vword (t.v (V 27)) (VG.Proof.Curve448.AArch64.Neon.hp p.hi + e)).toNat) % VG.Proof.Curve448.AArch64.Neon.M64 := by
  by_cases hc : tgt p.pos ∈ fresh ∧ tgt p.pos ∉ seen
  · have hm : mac tgt fresh seen p = vo (.umull p.hi (V (tgt p.pos)) (V (23 + p.i)) (V 27)) := by
      simp only [mac, hc, not_false_eq_true, and_self, ite_true]
    rw [hm]
    refine ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, fun e he => ?_⟩
    simp only [VG.Proof.Curve448.AArch64.Neon.lane, VG.Proof.Curve448.AArch64.Neon.vdword_ofVDwords _ _ he, hc, not_false_eq_true, and_self, ite_true, Int.zero_add]
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl <;>
      simp only [ite_true, show (1 : Nat) ≠ 0 by decide, ite_false, umull_lane, Int.natCast_mul]
  · have hm : mac tgt fresh seen p = vo (.umlal p.hi (V (tgt p.pos)) (V (23 + p.i)) (V 27)) := by
      simp only [mac, hc, ite_false]
    rw [hm]
    refine ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, fun e he => ?_⟩
    simp only [VG.Proof.Curve448.AArch64.Neon.lane, VG.Proof.Curve448.AArch64.Neon.vdword_ofVDwords _ _ he, hc, ite_false]
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl <;>
      simp only [ite_true, show (1 : Nat) ≠ 0 by decide, ite_false, umlal_lane] <;>
      rw [Int.natCast_emod, Int.natCast_add, Int.natCast_mul, Int.natCast_pow] <;>
      exact Int.emod_emod_of_dvd _ (Int.dvd_refl _)


/-- The invariant of a half's products, after `done`. -/
structure MInv (s : State) (A B : Nat → BitVec 128) (tgt : Nat → Nat) (fresh : List Nat)
    (done : List Prod) (seen : List Nat) (cur : Option Nat) (t : State) : Prop where
  mem : t.mem = s.mem
  gpr : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  a : ∀ i < 4, t.v (V (23 + i)) = A i
  b : ∀ bv, cur = some bv → t.v (V 27) = B bv
  seenIff : ∀ r, r ∈ seen ↔ ∃ p ∈ done, tgt p.pos = r
  acc : ∀ r < 23, (r ∉ fresh ∨ r ∈ seen) → ∀ e < 2,
    VG.Proof.Curve448.AArch64.Neon.lane (t.v (V r)) e % VG.Proof.Curve448.AArch64.Neon.M64 = ((if r ∈ fresh then 0 else VG.Proof.Curve448.AArch64.Neon.lane (s.v (V r)) e) + VG.Proof.Curve448.AArch64.Neon.prodSum A B tgt done r e) % VG.Proof.Curve448.AArch64.Neon.M64
  other : ∀ r : VReg, (∀ n ∈ VG.Proof.Curve448.AArch64.Neon.written tgt done, r ≠ V n) → t.v r = s.v r

theorem prodSum_unseen {A B : Nat → BitVec 128} {tgt : Nat → Nat} {done : List Prod} {r : Nat}
    (h : ¬ ∃ p ∈ done, tgt p.pos = r) (e : Nat) : VG.Proof.Curve448.AArch64.Neon.prodSum A B tgt done r e = 0 := by
  simp only [VG.Proof.Curve448.AArch64.Neon.prodSum]
  rw [List.filter_eq_nil_iff.mpr fun p hp => by simpa using fun e' => h ⟨p, hp, e'⟩]
  rfl

theorem mod_add_mod (a b : Int) : (a % VG.Proof.Curve448.AArch64.Neon.M64 + b) % VG.Proof.Curve448.AArch64.Neon.M64 = (a + b) % VG.Proof.Curve448.AArch64.Neon.M64 := Int.emod_add_emod _ _ _

/-- The products `ps`, with the `b` vector reloaded when it changes. -/
theorem withLoads_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) (h : Nat) (tgt : Nat → Nat) (fresh : List Nat)
    (A B : Nat → BitVec 128) (hB : ∀ bv < 9, B bv = s.mem.read (VG.Proof.X448.AArch64.off base (bOff h bv)) 16)
    (hoff : ∀ bv < 9, bOff h bv % 16 = 0 ∧ bOff h bv + 16 ≤ 8192) :
    ∀ (ps done : List Prod) (seen : List Nat) (cur : Option Nat) (t : State),
      (∀ p ∈ ps, p.i < 4 ∧ p.bv < 9 ∧ tgt p.pos < 23) →
      VG.Proof.Curve448.AArch64.Neon.MInv s A B tgt fresh done seen cur t →
      WP isa (.block (withLoads h tgt fresh ps seen cur)) t fun u =>
        ∃ seen' cur', VG.Proof.Curve448.AArch64.Neon.MInv s A B tgt fresh (done ++ ps) seen' cur' u := by
  intro ps
  induction ps with
  | nil => intro done seen cur t _ hi; exact WP.block_nil ⟨seen, cur, by simpa using hi⟩
  | cons p ps ih =>
    intro done seen cur t hps hi
    obtain ⟨pi, pb, pt⟩ := hps p List.mem_cons_self
    have hps' : ∀ q ∈ ps, q.i < 4 ∧ q.bv < 9 ∧ tgt q.pos < 23 := fun q hq => hps q (List.mem_cons_of_mem _ hq)
    simp only [withLoads]
    rw [WP.block_append_iff]
    -- load the `b` vector if it changed
    have load : WP isa (.block (if cur = some p.bv then [] else [ldq 27 (bOff h p.bv)])) t fun t1 =>
        VG.Proof.Curve448.AArch64.Neon.MInv s A B tgt fresh done seen (some p.bv) t1 := by
      split
      · rename_i hc
        exact WP.block_nil { hi with b := fun bv e => hi.b bv (hc ▸ e) }
      · refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_ldq (VG.Proof.Curve448.AArch64.Neon.scr_of hs hi.gpr hi.wr) 27 (hoff _ pb).1 (hoff _ pb).2, ?_⟩
        refine WP.block_nil ?_
        exact {
          mem := hi.mem, gpr := hi.gpr, rd := hi.rd, wr := hi.wr,
          a := fun i hi' => by
            rw [RegUpd.v_setV_of_ne _ _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))]; exact hi.a i hi'
          b := fun bv e => by
            simp only [Option.some.injEq] at e; subst e
            rw [RegUpd.v_setV_self, hi.mem, hB _ pb]
          seenIff := hi.seenIff,
          acc := fun r hr hrs e he => by
            rw [RegUpd.v_setV_of_ne _ _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))]; exact hi.acc r hr hrs e he
          other := fun r hr => by
            rw [RegUpd.v_setV_of_ne _ _ (hr 27 (by simp [VG.Proof.Curve448.AArch64.Neon.written]))]; exact hi.other r hr }
    refine WP.mono load fun t1 h1 => ?_
    -- the product
    obtain ⟨x, hx, lx⟩ := VG.Proof.Curve448.AArch64.Neon.mac_lane t1 tgt fresh seen p
    refine WP.block_cons_iff.mpr ⟨_, hx, ?_⟩
    have d23 : ∀ i < 4, V (tgt p.pos) ≠ V (23 + i) := fun i hi' => VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
    have d27 : V (tgt p.pos) ≠ V 27 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
    refine WP.mono (ih (done ++ [p]) (tgt p.pos :: seen) (some p.bv) (t1.setV (V (tgt p.pos)) x) hps' {
      mem := h1.mem, gpr := h1.gpr, rd := h1.rd, wr := h1.wr,
      a := fun i hi' => by rw [RegUpd.v_setV_of_ne _ _ (d23 i hi').symm]; exact h1.a i hi'
      b := fun bv e => by
        simp only [Option.some.injEq] at e; subst e
        rw [RegUpd.v_setV_of_ne _ _ d27.symm]; exact h1.b _ rfl
      seenIff := fun r => by
        simp only [List.mem_cons, h1.seenIff, List.mem_append, List.not_mem_nil, or_false]
        constructor
        · rintro (rfl | ⟨q, hq, e⟩)
          · exact ⟨p, Or.inr rfl, rfl⟩
          · exact ⟨q, Or.inl hq, e⟩
        · rintro ⟨q, hq | rfl, e⟩
          · exact Or.inr ⟨q, hq, e⟩
          · exact Or.inl e.symm
      acc := fun r hr hrs e he => by
        rw [VG.Proof.Curve448.AArch64.Neon.prodSum_append, VG.Proof.Curve448.AArch64.Neon.prodSum_single]
        by_cases hrd : r = tgt p.pos
        · subst hrd
          rw [RegUpd.v_setV_self, lx e he, ite_eq_left rfl]
          have pv : ((vword (t1.v (V (23 + p.i))) (VG.Proof.Curve448.AArch64.Neon.hp p.hi + e)).toNat : Int) *
              ((vword (t1.v (V 27)) (VG.Proof.Curve448.AArch64.Neon.hp p.hi + e)).toNat : Int) = (VG.Proof.Curve448.AArch64.Neon.prodVal A B p e : Int) := by
            rw [h1.a _ pi, h1.b _ rfl, VG.Proof.Curve448.AArch64.Neon.prodVal]; push_cast; rfl
          rw [pv]
          by_cases hf : tgt p.pos ∈ fresh ∧ tgt p.pos ∉ seen
          · rw [ite_eq_left hf, ite_eq_left hf.1,
              VG.Proof.Curve448.AArch64.Neon.prodSum_unseen (fun hq => hf.2 ((h1.seenIff _).mpr hq))]
            simp
          · rw [ite_eq_right hf]
            have hc : tgt p.pos ∉ fresh ∨ tgt p.pos ∈ seen := by
              by_cases h' : tgt p.pos ∈ fresh
              · exact Or.inr (by by_contra h''; exact hf ⟨h', h''⟩)
              · exact Or.inl h'
            rw [← VG.Proof.Curve448.AArch64.Neon.mod_add_mod, h1.acc _ hr hc e he, VG.Proof.Curve448.AArch64.Neon.mod_add_mod, Int.add_assoc]
        · rw [RegUpd.v_setV_of_ne _ _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) hrd),
            ite_eq_right (Ne.symm hrd), Int.add_zero]
          refine h1.acc r hr ?_ e he
          rcases hrs with h' | h'
          · exact Or.inl h'
          · exact Or.inr ((List.mem_cons.mp h').resolve_left hrd)
      other := fun r hr => by
        rw [RegUpd.v_setV_of_ne _ _ (hr (tgt p.pos) (by simp [VG.Proof.Curve448.AArch64.Neon.written]))]
        exact h1.other r fun n hn => hr n (by
          simp only [VG.Proof.Curve448.AArch64.Neon.written, List.mem_cons, List.map_append, List.mem_append, List.mem_map] at hn ⊢
          rcases hn with hn | ⟨q, hq, e⟩
          · exact Or.inl hn
          · exact Or.inr (Or.inl ⟨q, hq, e⟩)) }) fun u ⟨seen', cur', hu⟩ =>
      ⟨seen', cur', by simpa only [List.append_assoc, List.singleton_append] using hu⟩


theorem prods_facts : ∀ p ∈ prods, p.i < 4 ∧ p.bv < 9 := by decide

/-- A half product: the `a` vectors, then the products. -/
theorem half_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {h : Nat} (tgt : Nat → Nat) (fresh : List Nat)
    (ht : ∀ p ∈ prods, tgt p.pos < 23)
    (ha : ∀ i < 4, (aHalf h + 16 * i) % 16 = 0 ∧ aHalf h + 16 * i + 16 ≤ 8192)
    (hoff : ∀ bv < 9, bOff h bv % 16 = 0 ∧ bOff h bv + 16 ≤ 8192) :
    WP isa (.block (VG.Impl.Curve448.AArch64.Neon.half h tgt fresh)) s fun u =>
      u.mem = s.mem ∧ u.gpr = s.gpr ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      (∀ r < 23, (r ∉ fresh ∨ ∃ p ∈ prods, tgt p.pos = r) → ∀ e < 2,
        VG.Proof.Curve448.AArch64.Neon.lane (u.v (V r)) e % VG.Proof.Curve448.AArch64.Neon.M64 = ((if r ∈ fresh then 0 else VG.Proof.Curve448.AArch64.Neon.lane (s.v (V r)) e) +
          VG.Proof.Curve448.AArch64.Neon.prodSum (fun i => s.mem.read (VG.Proof.X448.AArch64.off base (aHalf h + 16 * i)) 16)
            (fun bv => s.mem.read (VG.Proof.X448.AArch64.off base (bOff h bv)) 16) tgt prods r e) % VG.Proof.Curve448.AArch64.Neon.M64) ∧
      (∀ r : VReg, (∀ n ∈ [23, 24, 25, 26, 27], r ≠ V n) → (∀ p ∈ prods, r ≠ V (tgt p.pos)) → u.v r = s.v r) := by
  simp only [VG.Impl.Curve448.AArch64.Neon.half, List.map, List.range, List.range.loop, List.cons_append, List.nil_append]
  let A := fun i => s.mem.read (VG.Proof.X448.AArch64.off base (aHalf h + 16 * i)) 16
  let B := fun bv => s.mem.read (VG.Proof.X448.AArch64.off base (bOff h bv)) 16
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_ldq hs 23 (ha 0 (by decide)).1 (ha 0 (by decide)).2, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_ldq (base := base) ?g1 24 (ha 1 (by decide)).1 (ha 1 (by decide)).2, ?_⟩
  case g1 => scr
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_ldq (base := base) ?g2 25 (ha 2 (by decide)).1 (ha 2 (by decide)).2, ?_⟩
  case g2 => scr
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_ldq (base := base) ?g3 26 (ha 3 (by decide)).1 (ha 3 (by decide)).2, ?_⟩
  case g3 => scr
  simp only [RegUpd.mem_setV]
  generalize ht4 : ((((s.setV (V 23) (A 0)).setV (V 24) (A 1)).setV (V 25) (A 2)).setV (V 26) (A 3)) = t4
  have v4 : ∀ r : VReg, (∀ n ∈ [23, 24, 25, 26], r ≠ V n) → t4.v r = s.v r := by
    intro r hr
    rw [← ht4]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
    rw [RegUpd.v_setV_of_ne _ _ hr.2.2.2, RegUpd.v_setV_of_ne _ _ hr.2.2.1, RegUpd.v_setV_of_ne _ _ hr.2.1,
      RegUpd.v_setV_of_ne _ _ hr.1]
  have i0 : VG.Proof.Curve448.AArch64.Neon.MInv t4 A B tgt fresh [] [] none t4 := {
    mem := rfl, gpr := rfl, rd := rfl, wr := rfl,
    a := fun i hi => by
      rw [← ht4]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp (config := {decide := true}) only [RegUpd.v_setV, ite_true, ite_false]
    b := fun _ e => by cases e
    seenIff := fun r => by simp
    acc := fun r hr hrs e he => by
      have hf : r ∉ fresh := by simpa using hrs
      simp [VG.Proof.Curve448.AArch64.Neon.prodSum, hf]
    other := fun _ _ => rfl }
  have hB : ∀ bv < 9, B bv = t4.mem.read (VG.Proof.X448.AArch64.off base (bOff h bv)) 16 := fun bv _ => by rw [← ht4]; rfl
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.withLoads_ok (VG.Proof.Curve448.AArch64.Neon.scr_of hs (by rw [← ht4]; rfl) (by rw [← ht4]; rfl)) h tgt fresh A B hB hoff prods [] [] none t4
    (fun p hp => ⟨(VG.Proof.Curve448.AArch64.Neon.prods_facts p hp).1, (VG.Proof.Curve448.AArch64.Neon.prods_facts p hp).2, ht p hp⟩) i0) fun u ⟨seen, cur, hu⟩ => ?_
  have m4 : t4.mem = s.mem := by rw [← ht4]; rfl
  refine ⟨hu.mem.trans m4, hu.gpr.trans (by rw [← ht4]; rfl), hu.rd.trans (by rw [← ht4]; rfl),
    hu.wr.trans (by rw [← ht4]; rfl), fun r hr hrs e he => ?_, fun r h1 h2 => ?_⟩
  · have hrs' : r ∉ fresh ∨ r ∈ seen := by
      rcases hrs with h' | ⟨p, hp, e'⟩
      · exact Or.inl h'
      · exact Or.inr ((hu.seenIff r).mpr ⟨p, by simpa using hp, e'⟩)
    rw [hu.acc r hr hrs' e he, List.nil_append, v4 _ (fun n hn => VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by simp at hn; omega)
      (by simp at hn; omega))]
  · rw [hu.other r (fun n hn => by
        simp only [VG.Proof.Curve448.AArch64.Neon.written, List.nil_append, List.mem_cons, List.mem_map] at hn
        rcases hn with rfl | ⟨p, hp, rfl⟩
        · exact h1 27 (by simp)
        · exact h2 p hp),
      v4 r (fun n hn => h1 n (by simp at hn ⊢; omega))]

end VG.Proof.Curve448.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Neon.Arith`. -/
section

/-!
# Lanes of the 64-bit lane arithmetic

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64

theorem lane_map2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) {e : Nat} (he : e < 2) :
    vdword (VArr.d2.map2 f x y) e = f 64 (vdword x e) (vdword y e) := by
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · exact map2_0 f x y
  · exact map2_1 f x y

theorem lane_add (x y : BitVec 128) {e : Nat} (he : e < 2) :
    VG.Proof.Curve448.AArch64.Neon.lane (VArr.d2.map2 (fun _ a b => a + b) x y) e % VG.Proof.Curve448.AArch64.Neon.M64 = (VG.Proof.Curve448.AArch64.Neon.lane x e + VG.Proof.Curve448.AArch64.Neon.lane y e) % VG.Proof.Curve448.AArch64.Neon.M64 := by
  simp only [VG.Proof.Curve448.AArch64.Neon.lane, VG.Proof.Curve448.AArch64.Neon.lane_map2 _ _ _ he, BitVec.toNat_add]
  have h64 : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := rfl
  rw [Int.natCast_emod, Int.natCast_add, h64]
  exact Int.emod_emod_of_dvd _ (Int.dvd_refl _)

theorem lane_sub (x y : BitVec 128) {e : Nat} (he : e < 2) :
    VG.Proof.Curve448.AArch64.Neon.lane (VArr.d2.map2 (fun _ a b => a - b) x y) e % VG.Proof.Curve448.AArch64.Neon.M64 = (VG.Proof.Curve448.AArch64.Neon.lane x e - VG.Proof.Curve448.AArch64.Neon.lane y e) % VG.Proof.Curve448.AArch64.Neon.M64 := by
  simp only [VG.Proof.Curve448.AArch64.Neon.lane, VG.Proof.Curve448.AArch64.Neon.lane_map2 _ _ _ he, BitVec.toNat_sub, VG.Proof.Curve448.AArch64.Neon.M64]
  have := (vdword y e).isLt
  have h64 : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := rfl
  rw [Int.natCast_emod, Int.natCast_add, Int.ofNat_sub (Nat.le_of_lt this), h64,
    Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
  omega

theorem lane_ushr (y x : BitVec 128) (sh : Nat) {e : Nat} (he : e < 2) :
    (vdword (VArr.d2.map2 (fun w a b => VShiftOp.eval .ushr sh w a b) y x) e).toNat = (vdword x e).toNat / 2 ^ sh := by
  rw [VG.Proof.Curve448.AArch64.Neon.lane_map2 _ _ _ he]
  simp [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem lane_shl (y x : BitVec 128) (sh : Nat) {e : Nat} (he : e < 2) :
    (vdword (VArr.d2.map2 (fun w a b => VShiftOp.eval .shl sh w a b) y x) e).toNat =
      (vdword x e).toNat * 2 ^ sh % 2 ^ 64 := by
  rw [VG.Proof.Curve448.AArch64.Neon.lane_map2 _ _ _ he]
  simp [VShiftOp.eval, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem lane_and (x m : BitVec 128) {k : Nat} (hm : ∀ e < 2, (vdword m e).toNat = 2 ^ k - 1) {e : Nat} (he : e < 2) :
    (vdword (x &&& m) e).toNat = (vdword x e).toNat % 2 ^ k := by
  rw [vdword_and, BitVec.toNat_and, hm e he, Nat.and_two_pow_sub_one_eq_mod]

end VG.Proof.Curve448.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Neon.Folds`. -/
section

/-!
# Combining the halves' coefficients

Untrusted: everything here is checked by Lean. `foldS` turns the coefficients
`S_q` into `S_d - S_{d+8}` (in `v_d`) and `-S_d` (in `v_{d+8}`); `foldU` adds
`U_{d+8}` (in `v_{16+d}`) to both.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon

/-- Lane `e` of vector register `r` is `f r e`, modulo 2⁶⁴. -/
abbrev LaneEq (t : State) (r : Nat) (x : Nat → Int) : Prop := ∀ e < 2, VG.Proof.Curve448.AArch64.Neon.lane (t.v (V r)) e % VG.Proof.Curve448.AArch64.Neon.M64 = x e % VG.Proof.Curve448.AArch64.Neon.M64

def foldSChunk (d : Nat) : List Instr :=
  [vo (.mov (V 28) (V (d + 8))), vo (.sub .d2 (V (d + 8)) (V 31) (V d)), vo (.sub .d2 (V d) (V d) (V 28))]

theorem foldS_eq : foldS = (List.range 7).flatMap VG.Proof.Curve448.AArch64.Neon.foldSChunk ++ [vo (.sub .d2 (V 15) (V 31) (V 7))] := rfl

theorem cong_sub {x y a b : Int} (hx : x % VG.Proof.Curve448.AArch64.Neon.M64 = a % VG.Proof.Curve448.AArch64.Neon.M64) (hy : y % VG.Proof.Curve448.AArch64.Neon.M64 = b % VG.Proof.Curve448.AArch64.Neon.M64) :
    (x - y) % VG.Proof.Curve448.AArch64.Neon.M64 = (a - b) % VG.Proof.Curve448.AArch64.Neon.M64 := by rw [Int.sub_emod, hx, hy, ← Int.sub_emod]

theorem cong_add {x y a b : Int} (hx : x % VG.Proof.Curve448.AArch64.Neon.M64 = a % VG.Proof.Curve448.AArch64.Neon.M64) (hy : y % VG.Proof.Curve448.AArch64.Neon.M64 = b % VG.Proof.Curve448.AArch64.Neon.M64) :
    (x + y) % VG.Proof.Curve448.AArch64.Neon.M64 = (a + b) % VG.Proof.Curve448.AArch64.Neon.M64 := by rw [Int.add_emod, hx, hy, ← Int.add_emod]

theorem cong_neg {x a : Int} (hx : x % VG.Proof.Curve448.AArch64.Neon.M64 = a % VG.Proof.Curve448.AArch64.Neon.M64) : (0 - x) % VG.Proof.Curve448.AArch64.Neon.M64 = (-a) % VG.Proof.Curve448.AArch64.Neon.M64 := by
  rw [VG.Proof.Curve448.AArch64.Neon.cong_sub (x := 0) (a := 0) rfl hx, Int.zero_sub]

theorem lane_zero (e : Nat) : VG.Proof.Curve448.AArch64.Neon.lane (0 : BitVec 128) e = 0 := by simp [VG.Proof.Curve448.AArch64.Neon.lane, vdword]

theorem foldSChunk_ok {s : State} {d : Nat} (hd : d < 7) {a b : Nat → Int} (ha : VG.Proof.Curve448.AArch64.Neon.LaneEq s d a)
    (hb : VG.Proof.Curve448.AArch64.Neon.LaneEq s (d + 8) b) (h31 : s.v (V 31) = 0) :
    WP isa (.block (VG.Proof.Curve448.AArch64.Neon.foldSChunk d)) s fun t =>
      VG.Proof.Curve448.AArch64.Neon.LaneEq t d (fun e => a e - b e) ∧ VG.Proof.Curve448.AArch64.Neon.LaneEq t (d + 8) (fun e => - a e) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r : VReg, r ≠ V 28 → r ≠ V d → r ≠ V (d + 8) → t.v r = s.v r) := by
  have n1 : V 28 ≠ V d := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n2 : V 28 ≠ V (d + 8) := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n3 : V (d + 8) ≠ V d := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n4 : V 31 ≠ V 28 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n5 : V 31 ≠ V (d + 8) := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n6 : V d ≠ V 28 := n1.symm
  have n7 : V d ≠ V (d + 8) := n3.symm
  have n8 : V (d + 8) ≠ V 28 := n2.symm
  have n9 : V 28 ≠ V 31 := n4.symm
  simp only [VG.Proof.Curve448.AArch64.Neon.foldSChunk]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_nil_iff.mpr ⟨fun e he => ?_, fun e he => ?_, rfl, rfl, rfl, rfl, fun r h1 h2 h3 => ?_⟩
  · rw [RegUpd.v_setV_self, VG.Proof.Curve448.AArch64.Neon.lane_sub _ _ he]
    exact VG.Proof.Curve448.AArch64.Neon.cong_sub (ha e he) (hb e he)
  · rw [RegUpd.v_setV_of_ne _ _ n3, RegUpd.v_setV_self, VG.Proof.Curve448.AArch64.Neon.lane_sub _ _ he, h31, VG.Proof.Curve448.AArch64.Neon.lane_zero]
    exact VG.Proof.Curve448.AArch64.Neon.cong_neg (ha e he)
  · rw [RegUpd.v_setV_of_ne _ _ h2, RegUpd.v_setV_of_ne _ _ h3, RegUpd.v_setV_of_ne _ _ h1]

theorem foldS_ok {s : State} (x : Nat → Nat → Int) (hx : ∀ q < 15, VG.Proof.Curve448.AArch64.Neon.LaneEq s q (x q)) (h31 : s.v (V 31) = 0) :
    WP isa (.block foldS) s fun t =>
      (∀ d < 8, VG.Proof.Curve448.AArch64.Neon.LaneEq t d (fun e => x d e - (if d < 7 then x (d + 8) e else 0))) ∧
      (∀ d < 8, VG.Proof.Curve448.AArch64.Neon.LaneEq t (d + 8) (fun e => - x d e)) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ (∀ r : VReg, (∀ n < 16, r ≠ V n) → r ≠ V 28 → t.v r = s.v r) := by
  rw [VG.Proof.Curve448.AArch64.Neon.foldS_eq, WP.block_append_iff]
  let inv := fun n (t : State) =>
    (∀ d < 7, VG.Proof.Curve448.AArch64.Neon.LaneEq t d (fun e => x d e - (if d < n then x (d + 8) e else 0))) ∧
    (∀ d < 7, VG.Proof.Curve448.AArch64.Neon.LaneEq t (d + 8) (fun e => if d < n then - x d e else x (d + 8) e)) ∧
    VG.Proof.Curve448.AArch64.Neon.LaneEq t 7 (x 7) ∧ t.v (V 31) = 0 ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ r : VReg, (∀ n < 16, r ≠ V n) → r ≠ V 28 → t.v r = s.v r)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv (fun n t hn ⟨ta, tb, t7, t31, tm, tg, tr, tw, tv⟩ => ?_)
    7 (by decide) s ⟨fun d hd e he => by simp [hx d (by omega) e he], fun d hd e he => by simp [hx (d + 8) (by omega) e he],
      hx 7 (by decide), h31, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩) fun t ⟨ta, tb, t7, t31, tm, tg, tr, tw, tv⟩ => ?_
  · refine WP.mono (VG.Proof.Curve448.AArch64.Neon.foldSChunk_ok hn (ta n hn) (tb n hn) t31) fun u ⟨ua, ub, um, ug, ur, uw, uv⟩ =>
      ⟨fun d hd e he => ?_, fun d hd e he => ?_, ?_, ?_, um.trans tm, ug.trans tg, ur.trans tr, uw.trans tw,
        fun r h1 h2 => (uv r h2 (h1 n (by omega)) (h1 (n + 8) (by omega))).trans (tv r h1 h2)⟩
    · rcases (show d = n ∨ d ≠ n by omega) with rfl | hne
      · rw [ua e he]; simp
      · rw [uv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) hne)
          (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)), ta d hd e he]
        simp only [show (d < n + 1) = (d < n) from propext (by omega)]
    · rcases (show d = n ∨ d ≠ n by omega) with rfl | hne
      · rw [ub e he]; simp
      · rw [uv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
          (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)), tb d hd e he]
        simp only [show (d < n + 1) = (d < n) from propext (by omega)]
    · intro e he
      rw [uv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
        (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)), t7 e he]
    · rw [uv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
        (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)), t31]
  · refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, WP.block_nil_iff.mpr
      ⟨fun d hd e he => ?_, fun d hd e he => ?_, tm, tg, tr, tw, fun r h1 h2 => ?_⟩⟩
    · rw [RegUpd.v_setV_of_ne _ _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))]
      rcases (show d < 7 ∨ d = 7 by omega) with h | rfl
      · rw [ta d h e he]
      · rw [t7 e he]; simp
    · rcases (show d < 7 ∨ d = 7 by omega) with h | rfl
      · rw [RegUpd.v_setV_of_ne _ _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)), tb d h e he]; simp [h]
      · rw [RegUpd.v_setV_self, VG.Proof.Curve448.AArch64.Neon.lane_sub _ _ he, t31, VG.Proof.Curve448.AArch64.Neon.lane_zero]
        exact VG.Proof.Curve448.AArch64.Neon.cong_neg (t7 e he)
    · rw [RegUpd.v_setV_of_ne _ _ (h1 15 (by decide)), tv r h1 h2]

/-- After `U`: `U_{d+8}`, in `v_{16+d}`, into `v_d` and `v_{d+8}`. -/
def foldUChunk (d : Nat) : List Instr :=
  [vo (.add .d2 (V d) (V d) (V (16 + d))), vo (.add .d2 (V (d + 8)) (V (d + 8)) (V (16 + d)))]

theorem foldU_eq : foldU = (List.range 7).flatMap VG.Proof.Curve448.AArch64.Neon.foldUChunk := rfl

theorem foldU_ok {s : State} (x y : Nat → Nat → Int) (hx : ∀ k < 16, VG.Proof.Curve448.AArch64.Neon.LaneEq s k (x k))
    (hy : ∀ d < 7, VG.Proof.Curve448.AArch64.Neon.LaneEq s (16 + d) (y d)) :
    WP isa (.block foldU) s fun t =>
      (∀ k < 16, VG.Proof.Curve448.AArch64.Neon.LaneEq t k (fun e => x k e + (if k < 7 then y k e else if 8 ≤ k ∧ k < 15 then y (k - 8) e else 0))) ∧
      t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, (∀ n < 16, r ≠ V n) → t.v r = s.v r) := by
  rw [VG.Proof.Curve448.AArch64.Neon.foldU_eq]
  let inv := fun n (t : State) =>
    (∀ k < 16, VG.Proof.Curve448.AArch64.Neon.LaneEq t k (fun e => x k e + (if k < n then y k e else if 8 ≤ k ∧ k < 8 + n then y (k - 8) e else 0))) ∧
    (∀ d < 7, VG.Proof.Curve448.AArch64.Neon.LaneEq t (16 + d) (y d)) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ r : VReg, (∀ n < 16, r ≠ V n) → t.v r = s.v r)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv (fun n t hn ⟨ta, ty, tm, tg, tr, tw, tv⟩ => ?_)
    7 (by decide) s ⟨fun k hk e he => by simp [hx k hk e he, show ¬ (8 ≤ k ∧ k < 8) by omega], hy, rfl, rfl, rfl,
      rfl, fun _ _ => rfl⟩)
    fun t ⟨ta, _, tm, tg, tr, tw, tv⟩ => ⟨fun k hk e he => by rw [ta k hk e he], tm, tg, tr, tw, tv⟩
  simp only [VG.Proof.Curve448.AArch64.Neon.foldUChunk]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, WP.block_nil_iff.mpr
    ⟨fun k hk e he => ?_, fun d hd e he => ?_, tm, tg, tr, tw, fun r h1 => ?_⟩⟩
  · have hn8 : V (n + 8) ≠ V n := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
    have hU8 : V (16 + n) ≠ V n := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
    rcases (show k = n + 8 ∨ k = n ∨ (k ≠ n ∧ k ≠ n + 8) by omega) with rfl | rfl | ⟨k1, k2⟩
    · rw [RegUpd.v_setV_self, VG.Proof.Curve448.AArch64.Neon.lane_add _ _ he, RegUpd.v_setV_of_ne _ _ hn8,
        RegUpd.v_setV_of_ne _ _ hU8]
      rw [VG.Proof.Curve448.AArch64.Neon.cong_add (ta _ hk e he) (ty n hn e he)]
      congr 1
      by_cases h : n + 8 < n <;> simp [h] <;> split <;> omega
    · rw [RegUpd.v_setV_of_ne _ _ hn8.symm, RegUpd.v_setV_self, VG.Proof.Curve448.AArch64.Neon.lane_add _ _ he,
        VG.Proof.Curve448.AArch64.Neon.cong_add (ta _ hk e he) (ty k hn e he)]
      congr 1
      simp only [show k < k + 1 from by omega, ite_true, show ¬ k < k from by omega, ite_false]
      split <;> omega
    · rw [RegUpd.v_setV_of_ne _ _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) k2),
        RegUpd.v_setV_of_ne _ _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) k1), ta k hk e he]
      congr 2
      by_cases h1 : k < n <;> by_cases h2 : k < n + 1 <;> by_cases h3 : 8 ≤ k ∧ k < 8 + n <;>
        by_cases h4 : 8 ≤ k ∧ k < 8 + (n + 1) <;> simp [h1, h2, h3, h4] <;> omega
  · rw [RegUpd.v_setV_of_ne _ _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)),
      RegUpd.v_setV_of_ne _ _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)), ty d hd e he]
  · rw [RegUpd.v_setV_of_ne _ _ (h1 _ (by omega)), RegUpd.v_setV_of_ne _ _ (h1 _ (by omega)), tv r h1]

end VG.Proof.Curve448.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Neon.Carries`. -/
section

/-!
# The coefficients' carries

Untrusted: everything here is checked by Lean. Two chains carry in radix
2²⁸, `0 → 7` and `8 → 15`; their last carries go to coefficients 8 and 0, by
`2⁴⁴⁸ = 2²²⁴ + 1`. With coefficients small enough, every lane holds its exact
value.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon

/-- The carry into coefficient `b + k` of the chain from `b`. -/
def cin (r : Nat → Nat) (b : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (r (b + k) + VG.Proof.Curve448.AArch64.Neon.cin r b k) / 2 ^ 28

/-- The value of coefficient `b + k` with its carry. -/
abbrev cval (r : Nat → Nat) (b k : Nat) : Nat := r (b + k) + VG.Proof.Curve448.AArch64.Neon.cin r b k

abbrev C7 (r : Nat → Nat) : Nat := VG.Proof.Curve448.AArch64.Neon.cval r 0 7 / 2 ^ 28
abbrev C15 (r : Nat → Nat) : Nat := VG.Proof.Curve448.AArch64.Neon.cval r 8 7 / 2 ^ 28

/-- The limbs after the carries. -/
def limbs28 (r : Nat → Nat) (k : Nat) : Nat :=
  if k < 8 then VG.Proof.Curve448.AArch64.Neon.cval r 0 k % 2 ^ 28 + (if k = 0 then VG.Proof.Curve448.AArch64.Neon.C15 r else 0)
  else VG.Proof.Curve448.AArch64.Neon.cval r 8 (k - 8) % 2 ^ 28 + (if k = 8 then VG.Proof.Curve448.AArch64.Neon.C7 r + VG.Proof.Curve448.AArch64.Neon.C15 r else 0)

/-- Lane `e` of vector register `r` is exactly `x e`. -/
abbrev LaneIs (t : State) (r : Nat) (x : Nat → Nat) : Prop := ∀ e < 2, (vdword (t.v (V r)) e).toNat = x e

theorem cin_le {r : Nat → Nat} {b : Nat} (hr : ∀ k < 8, r (b + k) < 2 ^ 64 - 2 ^ 40) : ∀ k ≤ 8, VG.Proof.Curve448.AArch64.Neon.cin r b k < 2 ^ 36 := by
  intro k hk
  induction k with
  | zero => simp [VG.Proof.Curve448.AArch64.Neon.cin]
  | succ k ih =>
    simp only [VG.Proof.Curve448.AArch64.Neon.cin]
    have := ih (by omega)
    have := hr k (by omega)
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    omega

/-- One step of a chain: carry out of `v_{b+k}` (through `v_t`) into `v_{b+k+1}`. -/
def chainStep (b k t : Nat) : List Instr :=
  [vo (.shift .ushr .d2 (V t) (V (b + k)) 28), vo (.logic .and (V (b + k)) (V (b + k)) (V 30)),
    vo (.add .d2 (V (b + k + 1)) (V (b + k + 1)) (V t))]

theorem chainStep_ok {s : State} {b k t : Nat} (hk : b + k + 1 < 16) (ht : 28 ≤ t ∧ t < 30)
    (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1) {x y : Nat → Nat}
    (hx : VG.Proof.Curve448.AArch64.Neon.LaneIs s (b + k) x) (hy : VG.Proof.Curve448.AArch64.Neon.LaneIs s (b + k + 1) y) (hxy : ∀ e < 2, y e + x e / 2 ^ 28 < 2 ^ 64) :
    WP isa (.block (VG.Proof.Curve448.AArch64.Neon.chainStep b k t)) s fun u =>
      VG.Proof.Curve448.AArch64.Neon.LaneIs u (b + k) (fun e => x e % 2 ^ 28) ∧ VG.Proof.Curve448.AArch64.Neon.LaneIs u (b + k + 1) (fun e => y e + x e / 2 ^ 28) ∧
      u.mem = s.mem ∧ u.gpr = s.gpr ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      (∀ r : VReg, r ≠ V t → r ≠ V (b + k) → r ≠ V (b + k + 1) → u.v r = s.v r) := by
  have n1 : V t ≠ V (b + k) := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n2 : V t ≠ V (b + k + 1) := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n3 : V (b + k) ≠ V (b + k + 1) := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n4 : V 30 ≠ V t := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n5 : V 30 ≠ V (b + k) := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n1' := n1.symm
  have n2' := n2.symm
  have n3' := n3.symm
  simp only [VG.Proof.Curve448.AArch64.Neon.chainStep]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_nil_iff.mpr ⟨fun e he => ?_, fun e he => ?_, rfl, rfl, rfl, rfl, fun r h1 h2 h3 => ?_⟩
  · rw [RegUpd.v_setV_of_ne _ _ n3, RegUpd.v_setV_self, VG.Proof.Curve448.AArch64.Neon.lane_and _ _ hM he, hx e he]
  · rw [RegUpd.v_setV_self, VG.Proof.Curve448.AArch64.Neon.lane_map2 _ _ _ he, BitVec.toNat_add, VG.Proof.Curve448.AArch64.Neon.lane_map2 _ _ _ he]
    simp only [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hx e he, hy e he]
    exact Nat.mod_eq_of_lt (hxy e he)
  · rw [RegUpd.v_setV_of_ne _ _ h3, RegUpd.v_setV_of_ne _ _ h2, RegUpd.v_setV_of_ne _ _ h1]

def wrap : List Instr :=
  [vo (.shift .ushr .d2 (V 28) (V 7) 28), vo (.logic .and (V 7) (V 7) (V 30)),
    vo (.shift .ushr .d2 (V 29) (V 15) 28), vo (.logic .and (V 15) (V 15) (V 30)),
    vo (.add .d2 (V 8) (V 8) (V 28)), vo (.add .d2 (V 8) (V 8) (V 29)), vo (.add .d2 (V 0) (V 0) (V 29))]

theorem carries_eq : carries = (List.range 7).flatMap (fun k => VG.Proof.Curve448.AArch64.Neon.chainStep 0 k 28 ++ VG.Proof.Curve448.AArch64.Neon.chainStep 8 k 29) ++ VG.Proof.Curve448.AArch64.Neon.wrap := rfl

/-- Coefficient `b + k` of a chain after `n` steps. -/
def chainAt (r : Nat → Nat) (b n k : Nat) : Nat :=
  if k < n then VG.Proof.Curve448.AArch64.Neon.cval r b k % 2 ^ 28 else if k = n then VG.Proof.Curve448.AArch64.Neon.cval r b k else r (b + k)

theorem chainAt_zero (r : Nat → Nat) (b k : Nat) : VG.Proof.Curve448.AArch64.Neon.chainAt r b 0 k = r (b + k) := by
  rcases k with _ | k <;> simp [VG.Proof.Curve448.AArch64.Neon.chainAt, VG.Proof.Curve448.AArch64.Neon.cval, VG.Proof.Curve448.AArch64.Neon.cin]

/-- The chains, before the last carries. -/
theorem chainLoop_ok {s : State} (r : Nat → Nat → Nat) (hr : ∀ k < 16, VG.Proof.Curve448.AArch64.Neon.LaneIs s k (fun e => r e k))
    (hb : ∀ e < 2, ∀ k < 16, r e k < 2 ^ 64 - 2 ^ 40) (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1) :
    WP isa (.block ((List.range 7).flatMap (fun k => VG.Proof.Curve448.AArch64.Neon.chainStep 0 k 28 ++ VG.Proof.Curve448.AArch64.Neon.chainStep 8 k 29))) s fun t =>
      (∀ k < 8, VG.Proof.Curve448.AArch64.Neon.LaneIs t k (fun e => VG.Proof.Curve448.AArch64.Neon.chainAt (r e) 0 7 k)) ∧ (∀ k < 8, VG.Proof.Curve448.AArch64.Neon.LaneIs t (8 + k) (fun e => VG.Proof.Curve448.AArch64.Neon.chainAt (r e) 8 7 k)) ∧
      t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ e < 2, (vdword (t.v (V 30)) e).toNat = 2 ^ 28 - 1) ∧
      (∀ v : VReg, (∀ n < 16, v ≠ V n) → v ≠ V 28 → v ≠ V 29 → t.v v = s.v v) := by
  have ci : ∀ e < 2, ∀ b ∈ [0, 8], ∀ k ≤ 8, VG.Proof.Curve448.AArch64.Neon.cin (r e) b k < 2 ^ 36 := fun e he b hb' k hk =>
    VG.Proof.Curve448.AArch64.Neon.cin_le (fun k hk => hb e he _ (by simp at hb'; omega)) k hk
  let inv := fun n (t : State) =>
    (∀ k < 8, VG.Proof.Curve448.AArch64.Neon.LaneIs t k (fun e => VG.Proof.Curve448.AArch64.Neon.chainAt (r e) 0 n k)) ∧ (∀ k < 8, VG.Proof.Curve448.AArch64.Neon.LaneIs t (8 + k) (fun e => VG.Proof.Curve448.AArch64.Neon.chainAt (r e) 8 n k)) ∧
    t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ e < 2, (vdword (t.v (V 30)) e).toNat = 2 ^ 28 - 1) ∧
    (∀ v : VReg, (∀ n < 16, v ≠ V n) → v ≠ V 28 → v ≠ V 29 → t.v v = s.v v)
  have i0 : inv 0 s := ⟨fun k hk e he => by dsimp only; rw [VG.Proof.Curve448.AArch64.Neon.chainAt_zero, Nat.zero_add]; exact hr k (by omega) e he,
    fun k hk e he => by dsimp only; rw [VG.Proof.Curve448.AArch64.Neon.chainAt_zero]; exact hr (8 + k) (by omega) e he,
    rfl, rfl, rfl, rfl, hM, fun _ _ _ _ => rfl⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv (fun n t hn ⟨t0, t8, tm, tg, tr, tw, tM, tv⟩ => ?_) 7
    (by decide) s i0) fun t ht => ht
  · rw [WP.block_append_iff]
    have cn : ∀ e < 2, ∀ b ∈ [0, 8], VG.Proof.Curve448.AArch64.Neon.chainAt (r e) b n n = VG.Proof.Curve448.AArch64.Neon.cval (r e) b n := fun e _ b _ => by
      simp [VG.Proof.Curve448.AArch64.Neon.chainAt]
    have cn1 : ∀ e < 2, ∀ b ∈ [0, 8], VG.Proof.Curve448.AArch64.Neon.chainAt (r e) b n (n + 1) = r e (b + (n + 1)) := fun e _ b _ => by
      simp [VG.Proof.Curve448.AArch64.Neon.chainAt, show ¬ (n + 1 < n) by omega]
    have bnd : ∀ e < 2, ∀ b ∈ [0, 8], r e (b + (n + 1)) + VG.Proof.Curve448.AArch64.Neon.cval (r e) b n / 2 ^ 28 < 2 ^ 64 := fun e he b hb' => by
      have h1 := ci e he b hb' (n + 1) (by omega)
      have h2 := hb e he (b + (n + 1)) (by simp at hb'; omega)
      simp only [VG.Proof.Curve448.AArch64.Neon.cin] at h1
      simp only [VG.Proof.Curve448.AArch64.Neon.cval]
      omega
    refine WP.mono (VG.Proof.Curve448.AArch64.Neon.chainStep_ok (b := 0) (k := n) (t := 28) (by omega) (by omega) tM
      (fun e he => by rw [Nat.zero_add, t0 n (by omega) e he]; dsimp only; rw [cn e he 0 (by simp)])
      (fun e he => by rw [Nat.zero_add, t0 (n + 1) (by omega) e he]; dsimp only; rw [cn1 e he 0 (by simp)])
      (fun e he => bnd e he 0 (by simp))) fun u ⟨ua, ub, um, ug, ur, uw, uv⟩ => ?_
    simp only [Nat.zero_add] at ua ub uv
    have u8 : ∀ k < 8, u.v (V (8 + k)) = t.v (V (8 + k)) := fun k hk =>
      uv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
        (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
    have uM : ∀ e < 2, (vdword (u.v (V 30)) e).toNat = 2 ^ 28 - 1 := fun e he => by
      rw [uv _ (by decide) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))]
      exact tM e he
    refine WP.mono (VG.Proof.Curve448.AArch64.Neon.chainStep_ok (b := 8) (k := n) (t := 29) (by omega) (by omega) uM
      (fun e he => by rw [u8 n (by omega), t8 n (by omega) e he]; dsimp only; rw [cn e he 8 (by simp)])
      (fun e he => by
        rw [show 8 + n + 1 = 8 + (n + 1) by omega, u8 (n + 1) (by omega), t8 (n + 1) (by omega) e he]
        dsimp only; rw [cn1 e he 8 (by simp)])
      (fun e he => bnd e he 8 (by simp))) fun w ⟨wa, wb, wm, wg, wr, ww, wv⟩ => ?_
    have w0 : ∀ k < 8, w.v (V k) = u.v (V k) := fun k hk =>
      wv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
        (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
    refine ⟨fun k hk e he => ?_, fun k hk e he => ?_, wm.trans (um.trans tm), wg.trans (ug.trans tg),
      wr.trans (ur.trans tr), ww.trans (uw.trans tw), fun e he => ?_, fun v h1 h2 h3 => ?_⟩
    · rw [w0 k hk]
      rcases (show k < n ∨ k = n ∨ k = n + 1 ∨ n + 1 < k by omega) with h | rfl | rfl | h
      · rw [uv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
          (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)), t0 k hk e he]
        simp [VG.Proof.Curve448.AArch64.Neon.chainAt, h, show k < n + 1 by omega]
      · rw [ua e he]; simp [VG.Proof.Curve448.AArch64.Neon.chainAt]
      · rw [ub e he]; simp [VG.Proof.Curve448.AArch64.Neon.chainAt, VG.Proof.Curve448.AArch64.Neon.cval, VG.Proof.Curve448.AArch64.Neon.cin]
      · rw [uv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
          (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)), t0 k hk e he]
        simp [VG.Proof.Curve448.AArch64.Neon.chainAt, show ¬ k < n by omega, show k ≠ n by omega, show ¬ k < n + 1 by omega, show k ≠ n + 1 by omega]
    · rcases (show k < n ∨ k = n ∨ k = n + 1 ∨ n + 1 < k by omega) with h | rfl | rfl | h
      · rw [wv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
          (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)), u8 k hk, t8 k hk e he]
        simp [VG.Proof.Curve448.AArch64.Neon.chainAt, h, show k < n + 1 by omega]
      · rw [wa e he]; simp [VG.Proof.Curve448.AArch64.Neon.chainAt]
      · rw [show 8 + (n + 1) = 8 + n + 1 by omega, wb e he]; simp [VG.Proof.Curve448.AArch64.Neon.chainAt, VG.Proof.Curve448.AArch64.Neon.cval, VG.Proof.Curve448.AArch64.Neon.cin]
      · rw [wv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
          (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)), u8 k hk, t8 k hk e he]
        simp [VG.Proof.Curve448.AArch64.Neon.chainAt, show ¬ k < n by omega, show k ≠ n by omega, show ¬ k < n + 1 by omega, show k ≠ n + 1 by omega]
    · rw [wv _ (by decide) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))]
      exact uM e he
    · rw [wv _ h3 (h1 _ (by omega)) (h1 _ (by omega)), uv _ h2 (h1 _ (by omega)) (h1 _ (by omega)), tv v h1 h2 h3]

/-- The last carries: `C7` into coefficient 8, `C15` into 0 and 8. -/
theorem wrap_ok {t : State} (r : Nat → Nat → Nat) (hb : ∀ e < 2, ∀ k < 16, r e k < 2 ^ 64 - 2 ^ 40)
    (t0 : ∀ k < 8, VG.Proof.Curve448.AArch64.Neon.LaneIs t k (fun e => VG.Proof.Curve448.AArch64.Neon.chainAt (r e) 0 7 k)) (t8 : ∀ k < 8, VG.Proof.Curve448.AArch64.Neon.LaneIs t (8 + k) (fun e => VG.Proof.Curve448.AArch64.Neon.chainAt (r e) 8 7 k))
    (tM : ∀ e < 2, (vdword (t.v (V 30)) e).toNat = 2 ^ 28 - 1) :
    WP isa (.block VG.Proof.Curve448.AArch64.Neon.wrap) t fun u =>
      (∀ k < 16, VG.Proof.Curve448.AArch64.Neon.LaneIs u k (fun e => VG.Proof.Curve448.AArch64.Neon.limbs28 (r e) k)) ∧ u.mem = t.mem ∧ u.gpr = t.gpr ∧ u.rd = t.rd ∧
      u.wr = t.wr ∧ (∀ v : VReg, (∀ n < 16, v ≠ V n) → v ≠ V 28 → v ≠ V 29 → u.v v = t.v v) := by
  have ci : ∀ e < 2, ∀ b ∈ [0, 8], ∀ k ≤ 8, VG.Proof.Curve448.AArch64.Neon.cin (r e) b k < 2 ^ 36 := fun e he b hb' k hk =>
    VG.Proof.Curve448.AArch64.Neon.cin_le (fun k hk => hb e he _ (by simp at hb'; omega)) k hk
  have c7 : ∀ e < 2, VG.Proof.Curve448.AArch64.Neon.cval (r e) 0 7 / 2 ^ 28 < 2 ^ 36 := fun e he => by
    have := ci e he 0 (by simp) 8 (by omega); simp only [VG.Proof.Curve448.AArch64.Neon.cin] at this; exact this
  have c15 : ∀ e < 2, VG.Proof.Curve448.AArch64.Neon.cval (r e) 8 7 / 2 ^ 28 < 2 ^ 36 := fun e he => by
    have := ci e he 8 (by simp) 8 (by omega); simp only [VG.Proof.Curve448.AArch64.Neon.cin] at this; exact this
  have n0_7 : V 0 ≠ V 7 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n0_8 : V 0 ≠ V 8 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n0_15 : V 0 ≠ V 15 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n0_28 : V 0 ≠ V 28 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n0_29 : V 0 ≠ V 29 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n0_30 : V 0 ≠ V 30 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n7_0 : V 7 ≠ V 0 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n7_8 : V 7 ≠ V 8 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n7_15 : V 7 ≠ V 15 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n7_28 : V 7 ≠ V 28 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n7_29 : V 7 ≠ V 29 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n7_30 : V 7 ≠ V 30 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n8_0 : V 8 ≠ V 0 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n8_7 : V 8 ≠ V 7 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n8_15 : V 8 ≠ V 15 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n8_28 : V 8 ≠ V 28 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n8_29 : V 8 ≠ V 29 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n8_30 : V 8 ≠ V 30 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n15_0 : V 15 ≠ V 0 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n15_7 : V 15 ≠ V 7 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n15_8 : V 15 ≠ V 8 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n15_28 : V 15 ≠ V 28 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n15_29 : V 15 ≠ V 29 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n15_30 : V 15 ≠ V 30 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n28_0 : V 28 ≠ V 0 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n28_7 : V 28 ≠ V 7 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n28_8 : V 28 ≠ V 8 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n28_15 : V 28 ≠ V 15 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n28_29 : V 28 ≠ V 29 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n28_30 : V 28 ≠ V 30 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n29_0 : V 29 ≠ V 0 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n29_7 : V 29 ≠ V 7 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n29_8 : V 29 ≠ V 8 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n29_15 : V 29 ≠ V 15 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n29_28 : V 29 ≠ V 28 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n29_30 : V 29 ≠ V 30 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n30_0 : V 30 ≠ V 0 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n30_7 : V 30 ≠ V 7 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n30_8 : V 30 ≠ V 8 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n30_15 : V 30 ≠ V 15 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n30_28 : V 30 ≠ V 28 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n30_29 : V 30 ≠ V 29 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have l7 : ∀ e < 2, (vdword (t.v (V 7)) e).toNat = VG.Proof.Curve448.AArch64.Neon.cval (r e) 0 7 := fun e he => by
    rw [t0 7 (by omega) e he]; simp [VG.Proof.Curve448.AArch64.Neon.chainAt]
  have l15 : ∀ e < 2, (vdword (t.v (V 15)) e).toNat = VG.Proof.Curve448.AArch64.Neon.cval (r e) 8 7 := fun e he => by
    rw [t8 7 (by omega) e he]; simp [VG.Proof.Curve448.AArch64.Neon.chainAt]
  have l0 : ∀ e < 2, (vdword (t.v (V 0)) e).toNat = VG.Proof.Curve448.AArch64.Neon.cval (r e) 0 0 % 2 ^ 28 := fun e he => by
    rw [t0 0 (by omega) e he]; simp [VG.Proof.Curve448.AArch64.Neon.chainAt]
  have l8 : ∀ e < 2, (vdword (t.v (V 8)) e).toNat = VG.Proof.Curve448.AArch64.Neon.cval (r e) 8 0 % 2 ^ 28 := fun e he => by
    rw [t8 0 (by omega) e he]; simp [VG.Proof.Curve448.AArch64.Neon.chainAt]
  simp only [VG.Proof.Curve448.AArch64.Neon.wrap]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, WP.block_nil_iff.mpr ?_⟩
  refine ⟨fun k hk e he => ?_, by simp only [RegUpd.mem_setV], by simp only [RegUpd.gpr_setV],
    by simp only [RegUpd.rd_setV], by simp only [RegUpd.wr_setV], fun v h1 h2 h3 => ?_⟩
  · rcases (show k = 0 ∨ k = 7 ∨ k = 8 ∨ k = 15 ∨ (0 < k ∧ k < 7) ∨ (8 < k ∧ k < 15) by omega)
      with rfl | rfl | rfl | rfl | ⟨k1, k2⟩ | ⟨k1, k2⟩
    · vred
      rw [VG.Proof.Curve448.AArch64.Neon.lane_map2 _ _ _ he, BitVec.toNat_add, l0 e he, VG.Proof.Curve448.AArch64.Neon.ushr28 _ _ _ he, l15 e he]
      simp only [VG.Proof.Curve448.AArch64.Neon.limbs28, show (0 : Nat) < 8 by decide, ite_true]
      have := c15 e he
      exact Nat.mod_eq_of_lt (by omega)
    · vred
      rw [VG.Proof.Curve448.AArch64.Neon.lane_and _ _ tM he, l7 e he]
      simp [VG.Proof.Curve448.AArch64.Neon.limbs28]
    · vred
      rw [VG.Proof.Curve448.AArch64.Neon.lane_map2 _ _ _ he, BitVec.toNat_add, VG.Proof.Curve448.AArch64.Neon.lane_map2 _ _ _ he,
        BitVec.toNat_add, l8 e he, VG.Proof.Curve448.AArch64.Neon.ushr28 _ _ _ he, l7 e he, VG.Proof.Curve448.AArch64.Neon.ushr28 _ _ _ he, l15 e he]
      have := c7 e he; have := c15 e he
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [VG.Proof.Curve448.AArch64.Neon.limbs28, show ¬ (8 : Nat) < 8 by decide, ite_false, ite_true, Nat.sub_self, VG.Proof.Curve448.AArch64.Neon.C7, VG.Proof.Curve448.AArch64.Neon.C15]
      omega
    · vred
      rw [VG.Proof.Curve448.AArch64.Neon.lane_and _ _ tM he, l15 e he]
      simp [VG.Proof.Curve448.AArch64.Neon.limbs28]
    · have hv : ∀ n ∈ [0, 7, 8, 15, 28, 29], V k ≠ V n := fun n hn =>
        VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by simp at hn; omega) (by simp at hn; omega)
      rw [RegUpd.v_setV_of_ne _ _ (hv 0 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 8 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 8 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 15 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 29 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 7 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 28 (by simp)), t0 k (by omega) e he]
      simp [VG.Proof.Curve448.AArch64.Neon.chainAt, VG.Proof.Curve448.AArch64.Neon.limbs28, show k < 7 by omega, show k < 8 by omega, show k ≠ 0 by omega]
    · have hv : ∀ n ∈ [0, 7, 8, 15, 28, 29], V k ≠ V n := fun n hn =>
        VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by simp at hn; omega) (by simp at hn; omega)
      rw [RegUpd.v_setV_of_ne _ _ (hv 0 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 8 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 8 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 15 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 29 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 7 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 28 (by simp)), show k = 8 + (k - 8) by omega, t8 (k - 8) (by omega) e he]
      simp [VG.Proof.Curve448.AArch64.Neon.chainAt, VG.Proof.Curve448.AArch64.Neon.limbs28, show k - 8 < 7 by omega, show ¬ (8 + (k - 8) < 8) by omega]
      intro h; omega
  · rw [RegUpd.v_setV_of_ne _ _ (h1 0 (by decide)), RegUpd.v_setV_of_ne _ _ (h1 8 (by decide)),
      RegUpd.v_setV_of_ne _ _ (h1 8 (by decide)), RegUpd.v_setV_of_ne _ _ (h1 15 (by decide)),
      RegUpd.v_setV_of_ne _ _ h3, RegUpd.v_setV_of_ne _ _ (h1 7 (by decide)), RegUpd.v_setV_of_ne _ _ h2]

theorem carries_ok {s : State} (r : Nat → Nat → Nat) (hr : ∀ k < 16, VG.Proof.Curve448.AArch64.Neon.LaneIs s k (fun e => r e k))
    (hb : ∀ e < 2, ∀ k < 16, r e k < 2 ^ 64 - 2 ^ 40) (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1) :
    WP isa (.block carries) s fun t =>
      (∀ k < 16, VG.Proof.Curve448.AArch64.Neon.LaneIs t k (fun e => VG.Proof.Curve448.AArch64.Neon.limbs28 (r e) k)) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ (∀ v : VReg, (∀ n < 16, v ≠ V n) → v ≠ V 28 → v ≠ V 29 → t.v v = s.v v) := by
  rw [VG.Proof.Curve448.AArch64.Neon.carries_eq, WP.block_append_iff]
  exact WP.mono (VG.Proof.Curve448.AArch64.Neon.chainLoop_ok r hr hb hM) fun t ⟨t0, t8, tm, tg, tr, tw, tM, tv⟩ =>
    WP.mono (VG.Proof.Curve448.AArch64.Neon.wrap_ok r hb t0 t8 tM) fun u ⟨ul, um, ug, ur, uw, uv⟩ =>
      ⟨ul, um.trans tm, ug.trans tg, ur.trans tr, uw.trans tw, fun v h1 h2 h3 => (uv v h1 h2 h3).trans (tv v h1 h2 h3)⟩

/-! ## The value -/

/-- `Σ_{k<n} f k xᵏ`. -/
def psum (f : Nat → Nat) (x : Int) : Nat → Int
  | 0 => 0
  | n + 1 => VG.Proof.Curve448.AArch64.Neon.psum f x n + f n * x ^ n

/-- A chain keeps the value: its limbs and its last carry are its coefficients. -/
theorem chain_val (r : Nat → Nat) (b : Nat) (n : Nat) :
    VG.Proof.Curve448.AArch64.Neon.psum (fun k => VG.Proof.Curve448.AArch64.Neon.cval r b k % 2 ^ 28) (2 ^ 28) n + VG.Proof.Curve448.AArch64.Neon.cin r b n * (2 ^ 28 : Int) ^ n =
      VG.Proof.Curve448.AArch64.Neon.psum (fun k => r (b + k)) (2 ^ 28) n := by
  induction n with
  | zero => simp [VG.Proof.Curve448.AArch64.Neon.psum, VG.Proof.Curve448.AArch64.Neon.cin]
  | succ n ih =>
    simp only [VG.Proof.Curve448.AArch64.Neon.psum, VG.Proof.Curve448.AArch64.Neon.cin]
    have e' : VG.Proof.Curve448.AArch64.Neon.cval r b n % 2 ^ 28 + (VG.Proof.Curve448.AArch64.Neon.cval r b n / 2 ^ 28) * 2 ^ 28 = r (b + n) + VG.Proof.Curve448.AArch64.Neon.cin r b n := by
      simp only [VG.Proof.Curve448.AArch64.Neon.cval]; omega
    have e : ((VG.Proof.Curve448.AArch64.Neon.cval r b n % 2 ^ 28 : Nat) : Int) + ((VG.Proof.Curve448.AArch64.Neon.cval r b n / 2 ^ 28 : Nat) : Int) * 2 ^ 28 =
        (r (b + n) : Int) + VG.Proof.Curve448.AArch64.Neon.cin r b n := by exact_mod_cast e'
    rw [← ih]
    have : ((VG.Proof.Curve448.AArch64.Neon.cval r b n % 2 ^ 28 : Nat) : Int) * (2 ^ 28) ^ n + ((VG.Proof.Curve448.AArch64.Neon.cval r b n / 2 ^ 28 : Nat) : Int) * (2 ^ 28) ^ (n + 1) =
        ((r (b + n) : Int) + VG.Proof.Curve448.AArch64.Neon.cin r b n) * (2 ^ 28) ^ n := by rw [← e]; ring
    linarith

theorem limbs28_val (r : Nat → Nat) :
    VG.Proof.Curve448.AArch64.Neon.psum (VG.Proof.Curve448.AArch64.Neon.limbs28 r) (2 ^ 28) 16 = VG.Proof.Curve448.AArch64.Neon.psum r (2 ^ 28) 16 - (VG.Proof.Curve448.AArch64.Neon.C15 r : Int) * ((2 ^ 28) ^ 16 - (2 ^ 28) ^ 8 - 1) := by
  have h0 := VG.Proof.Curve448.AArch64.Neon.chain_val r 0 8
  have h8 := VG.Proof.Curve448.AArch64.Neon.chain_val r 8 8
  have c7 : VG.Proof.Curve448.AArch64.Neon.cin r 0 8 = VG.Proof.Curve448.AArch64.Neon.C7 r := rfl
  have c15 : VG.Proof.Curve448.AArch64.Neon.cin r 8 8 = VG.Proof.Curve448.AArch64.Neon.C15 r := rfl
  rw [c7] at h0
  rw [c15] at h8
  simp only [VG.Proof.Curve448.AArch64.Neon.psum, VG.Proof.Curve448.AArch64.Neon.limbs28, Nat.zero_add] at h0 h8 ⊢
  simp only [show (0 : Nat) < 8 by decide, show (1 : Nat) < 8 by decide, show (2 : Nat) < 8 by decide,
    show (3 : Nat) < 8 by decide, show (4 : Nat) < 8 by decide, show (5 : Nat) < 8 by decide,
    show (6 : Nat) < 8 by decide, show (7 : Nat) < 8 by decide, show ¬ (8 : Nat) < 8 by decide,
    show ¬ (9 : Nat) < 8 by decide, show ¬ (10 : Nat) < 8 by decide, show ¬ (11 : Nat) < 8 by decide,
    show ¬ (12 : Nat) < 8 by decide, show ¬ (13 : Nat) < 8 by decide, show ¬ (14 : Nat) < 8 by decide,
    show ¬ (15 : Nat) < 8 by decide, ite_true, ite_false, Nat.reduceSub, Nat.cast_add,
    ] at ⊢
  simp only [show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 0 by decide,
    show (4 : Nat) ≠ 0 by decide, show (5 : Nat) ≠ 0 by decide, show (6 : Nat) ≠ 0 by decide,
    show (7 : Nat) ≠ 0 by decide, show (9 : Nat) ≠ 8 by decide, show (10 : Nat) ≠ 8 by decide,
    show (11 : Nat) ≠ 8 by decide, show (12 : Nat) ≠ 8 by decide, show (13 : Nat) ≠ 8 by decide,
    show (14 : Nat) ≠ 8 by decide, show (15 : Nat) ≠ 8 by decide, ite_false,
    Nat.cast_zero, Int.add_zero] at ⊢
  linear_combination h0 + (2 ^ 28) ^ 8 * h8

end VG.Proof.Curve448.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Neon.Math`. -/
section

/-!
# The arithmetic of `Neon.mul2`'s products

Untrusted: everything here is checked by Lean. Coefficient `q` of the product
of two eight-limb halves is `cv x y q`; Karatsuba's identity for `φ = x⁸`
(`x = 2²⁸`) combines three of them into sixteen coefficients `kara a b k`,
which represent the product of the sixteen-limb operands modulo
`p = x¹⁶ - x⁸ - 1` (`kara_val`), and are at most the sum of their positive
terms (`kara_nonneg`, `kara_le`).
-/

namespace VG.Proof.Curve448.AArch64.Neon

/-- Coefficient `q` of the product of the eight-limb halves `x` and `y`. -/
def cv (x y : Nat → Nat) : Nat → Nat
  | 0 => x 0 * y 0
  | 1 => x 0 * y 1 + x 1 * y 0
  | 2 => x 0 * y 2 + x 1 * y 1 + x 2 * y 0
  | 3 => x 0 * y 3 + x 1 * y 2 + x 2 * y 1 + x 3 * y 0
  | 4 => x 0 * y 4 + x 1 * y 3 + x 2 * y 2 + x 3 * y 1 + x 4 * y 0
  | 5 => x 0 * y 5 + x 1 * y 4 + x 2 * y 3 + x 3 * y 2 + x 4 * y 1 + x 5 * y 0
  | 6 => x 0 * y 6 + x 1 * y 5 + x 2 * y 4 + x 3 * y 3 + x 4 * y 2 + x 5 * y 1 + x 6 * y 0
  | 7 => x 0 * y 7 + x 1 * y 6 + x 2 * y 5 + x 3 * y 4 + x 4 * y 3 + x 5 * y 2 + x 6 * y 1 + x 7 * y 0
  | 8 => x 1 * y 7 + x 2 * y 6 + x 3 * y 5 + x 4 * y 4 + x 5 * y 3 + x 6 * y 2 + x 7 * y 1
  | 9 => x 2 * y 7 + x 3 * y 6 + x 4 * y 5 + x 5 * y 4 + x 6 * y 3 + x 7 * y 2
  | 10 => x 3 * y 7 + x 4 * y 6 + x 5 * y 5 + x 6 * y 4 + x 7 * y 3
  | 11 => x 4 * y 7 + x 5 * y 6 + x 6 * y 5 + x 7 * y 4
  | 12 => x 5 * y 7 + x 6 * y 6 + x 7 * y 5
  | 13 => x 6 * y 7 + x 7 * y 6
  | 14 => x 7 * y 7
  | _ => 0

/-- The halves of a sixteen-limb operand, and their sum. -/
def hl (a : Nat → Nat) (h : Nat) (i : Nat) : Nat :=
  match h with
  | 0 => a i
  | 1 => a (8 + i)
  | _ => a i + a (8 + i)

abbrev S (a b : Nat → Nat) (q : Nat) : Nat := VG.Proof.Curve448.AArch64.Neon.cv (VG.Proof.Curve448.AArch64.Neon.hl a 0) (VG.Proof.Curve448.AArch64.Neon.hl b 0) q
abbrev T (a b : Nat → Nat) (q : Nat) : Nat := VG.Proof.Curve448.AArch64.Neon.cv (VG.Proof.Curve448.AArch64.Neon.hl a 1) (VG.Proof.Curve448.AArch64.Neon.hl b 1) q
abbrev U (a b : Nat → Nat) (q : Nat) : Nat := VG.Proof.Curve448.AArch64.Neon.cv (VG.Proof.Curve448.AArch64.Neon.hl a 2) (VG.Proof.Curve448.AArch64.Neon.hl b 2) q

/-- Karatsuba's coefficients. -/
def kara (a b : Nat → Nat) (k : Nat) : Int :=
  if k < 8 then (VG.Proof.Curve448.AArch64.Neon.S a b k : Int) + VG.Proof.Curve448.AArch64.Neon.T a b k + VG.Proof.Curve448.AArch64.Neon.U a b (k + 8) - VG.Proof.Curve448.AArch64.Neon.S a b (k + 8)
  else (VG.Proof.Curve448.AArch64.Neon.T a b k : Int) + VG.Proof.Curve448.AArch64.Neon.U a b (k - 8) + VG.Proof.Curve448.AArch64.Neon.U a b k - VG.Proof.Curve448.AArch64.Neon.S a b (k - 8)

theorem conv8 (X x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 : Int) :
    (x0 * X ^ 0 + x1 * X ^ 1 + x2 * X ^ 2 + x3 * X ^ 3 + x4 * X ^ 4 + x5 * X ^ 5 + x6 * X ^ 6 + x7 * X ^ 7) * (y0 * X ^ 0 + y1 * X ^ 1 + y2 * X ^ 2 + y3 * X ^ 3 + y4 * X ^ 4 + y5 * X ^ 5 + y6 * X ^ 6 + y7 * X ^ 7) = (x0 * y0) * X ^ 0 + (x0 * y1 + x1 * y0) * X ^ 1 + (x0 * y2 + x1 * y1 + x2 * y0) * X ^ 2 + (x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0) * X ^ 3 + (x0 * y4 + x1 * y3 + x2 * y2 + x3 * y1 + x4 * y0) * X ^ 4 + (x0 * y5 + x1 * y4 + x2 * y3 + x3 * y2 + x4 * y1 + x5 * y0) * X ^ 5 + (x0 * y6 + x1 * y5 + x2 * y4 + x3 * y3 + x4 * y2 + x5 * y1 + x6 * y0) * X ^ 6 + (x0 * y7 + x1 * y6 + x2 * y5 + x3 * y4 + x4 * y3 + x5 * y2 + x6 * y1 + x7 * y0) * X ^ 7 + (x1 * y7 + x2 * y6 + x3 * y5 + x4 * y4 + x5 * y3 + x6 * y2 + x7 * y1) * X ^ 8 + (x2 * y7 + x3 * y6 + x4 * y5 + x5 * y4 + x6 * y3 + x7 * y2) * X ^ 9 + (x3 * y7 + x4 * y6 + x5 * y5 + x6 * y4 + x7 * y3) * X ^ 10 + (x4 * y7 + x5 * y6 + x6 * y5 + x7 * y4) * X ^ 11 + (x5 * y7 + x6 * y6 + x7 * y5) * X ^ 12 + (x6 * y7 + x7 * y6) * X ^ 13 + (x7 * y7) * X ^ 14 := by
  ring

theorem kara_comb (X S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 U0 U1 U2 U3 U4 U5 U6 U7 U8 U9 U10 U11 U12 U13 U14 : Int) :
    (S0 * X ^ 0 + S1 * X ^ 1 + S2 * X ^ 2 + S3 * X ^ 3 + S4 * X ^ 4 + S5 * X ^ 5 + S6 * X ^ 6 + S7 * X ^ 7 + S8 * X ^ 8 + S9 * X ^ 9 + S10 * X ^ 10 + S11 * X ^ 11 + S12 * X ^ 12 + S13 * X ^ 13 + S14 * X ^ 14) + X ^ 8 * ((U0 * X ^ 0 + U1 * X ^ 1 + U2 * X ^ 2 + U3 * X ^ 3 + U4 * X ^ 4 + U5 * X ^ 5 + U6 * X ^ 6 + U7 * X ^ 7 + U8 * X ^ 8 + U9 * X ^ 9 + U10 * X ^ 10 + U11 * X ^ 11 + U12 * X ^ 12 + U13 * X ^ 13 + U14 * X ^ 14) - (S0 * X ^ 0 + S1 * X ^ 1 + S2 * X ^ 2 + S3 * X ^ 3 + S4 * X ^ 4 + S5 * X ^ 5 + S6 * X ^ 6 + S7 * X ^ 7 + S8 * X ^ 8 + S9 * X ^ 9 + S10 * X ^ 10 + S11 * X ^ 11 + S12 * X ^ 12 + S13 * X ^ 13 + S14 * X ^ 14) - (T0 * X ^ 0 + T1 * X ^ 1 + T2 * X ^ 2 + T3 * X ^ 3 + T4 * X ^ 4 + T5 * X ^ 5 + T6 * X ^ 6 + T7 * X ^ 7 + T8 * X ^ 8 + T9 * X ^ 9 + T10 * X ^ 10 + T11 * X ^ 11 + T12 * X ^ 12 + T13 * X ^ 13 + T14 * X ^ 14)) + X ^ 16 * (T0 * X ^ 0 + T1 * X ^ 1 + T2 * X ^ 2 + T3 * X ^ 3 + T4 * X ^ 4 + T5 * X ^ 5 + T6 * X ^ 6 + T7 * X ^ 7 + T8 * X ^ 8 + T9 * X ^ 9 + T10 * X ^ 10 + T11 * X ^ 11 + T12 * X ^ 12 + T13 * X ^ 13 + T14 * X ^ 14) - ((S0 + T0 + U8 - S8) * X ^ 0 + (S1 + T1 + U9 - S9) * X ^ 1 + (S2 + T2 + U10 - S10) * X ^ 2 + (S3 + T3 + U11 - S11) * X ^ 3 + (S4 + T4 + U12 - S12) * X ^ 4 + (S5 + T5 + U13 - S13) * X ^ 5 + (S6 + T6 + U14 - S14) * X ^ 6 + (S7 + T7 + 0 - 0) * X ^ 7 + (T8 + U0 + U8 - S0) * X ^ 8 + (T9 + U1 + U9 - S1) * X ^ 9 + (T10 + U2 + U10 - S2) * X ^ 10 + (T11 + U3 + U11 - S3) * X ^ 11 + (T12 + U4 + U12 - S4) * X ^ 12 + (T13 + U5 + U13 - S5) * X ^ 13 + (T14 + U6 + U14 - S6) * X ^ 14 + (0 + U7 + 0 - S7) * X ^ 15) =
      (X ^ 16 - X ^ 8 - 1) * ((T0 * X ^ 0 + T1 * X ^ 1 + T2 * X ^ 2 + T3 * X ^ 3 + T4 * X ^ 4 + T5 * X ^ 5 + T6 * X ^ 6 + T7 * X ^ 7 + T8 * X ^ 8 + T9 * X ^ 9 + T10 * X ^ 10 + T11 * X ^ 11 + T12 * X ^ 12 + T13 * X ^ 13 + T14 * X ^ 14) + (U8 * X ^ 0 + U9 * X ^ 1 + U10 * X ^ 2 + U11 * X ^ 3 + U12 * X ^ 4 + U13 * X ^ 5 + U14 * X ^ 6) - (S8 * X ^ 0 + S9 * X ^ 1 + S10 * X ^ 2 + S11 * X ^ 3 + S12 * X ^ 4 + S13 * X ^ 5 + S14 * X ^ 6)) := by
  ring

theorem halves (X : Int) (a : Nat → Nat) : (a 0 : Int) * X ^ 0 + (a 1 : Int) * X ^ 1 + (a 2 : Int) * X ^ 2 + (a 3 : Int) * X ^ 3 + (a 4 : Int) * X ^ 4 + (a 5 : Int) * X ^ 5 + (a 6 : Int) * X ^ 6 + (a 7 : Int) * X ^ 7 + (a 8 : Int) * X ^ 8 + (a 9 : Int) * X ^ 9 + (a 10 : Int) * X ^ 10 + (a 11 : Int) * X ^ 11 + (a 12 : Int) * X ^ 12 + (a 13 : Int) * X ^ 13 + (a 14 : Int) * X ^ 14 + (a 15 : Int) * X ^ 15 = ((a 0 : Int) * X ^ 0 + (a 1 : Int) * X ^ 1 + (a 2 : Int) * X ^ 2 + (a 3 : Int) * X ^ 3 + (a 4 : Int) * X ^ 4 + (a 5 : Int) * X ^ 5 + (a 6 : Int) * X ^ 6 + (a 7 : Int) * X ^ 7) + X ^ 8 * ((a 8 : Int) * X ^ 0 + (a 9 : Int) * X ^ 1 + (a 10 : Int) * X ^ 2 + (a 11 : Int) * X ^ 3 + (a 12 : Int) * X ^ 4 + (a 13 : Int) * X ^ 5 + (a 14 : Int) * X ^ 6 + (a 15 : Int) * X ^ 7) := by ring

theorem prodS (X : Int) (a b : Nat → Nat) : ((a 0 : Int) * X ^ 0 + (a 1 : Int) * X ^ 1 + (a 2 : Int) * X ^ 2 + (a 3 : Int) * X ^ 3 + (a 4 : Int) * X ^ 4 + (a 5 : Int) * X ^ 5 + (a 6 : Int) * X ^ 6 + (a 7 : Int) * X ^ 7) * ((b 0 : Int) * X ^ 0 + (b 1 : Int) * X ^ 1 + (b 2 : Int) * X ^ 2 + (b 3 : Int) * X ^ 3 + (b 4 : Int) * X ^ 4 + (b 5 : Int) * X ^ 5 + (b 6 : Int) * X ^ 6 + (b 7 : Int) * X ^ 7) = (VG.Proof.Curve448.AArch64.Neon.S a b 0 : Int) * X ^ 0 + (VG.Proof.Curve448.AArch64.Neon.S a b 1 : Int) * X ^ 1 + (VG.Proof.Curve448.AArch64.Neon.S a b 2 : Int) * X ^ 2 + (VG.Proof.Curve448.AArch64.Neon.S a b 3 : Int) * X ^ 3 + (VG.Proof.Curve448.AArch64.Neon.S a b 4 : Int) * X ^ 4 + (VG.Proof.Curve448.AArch64.Neon.S a b 5 : Int) * X ^ 5 + (VG.Proof.Curve448.AArch64.Neon.S a b 6 : Int) * X ^ 6 + (VG.Proof.Curve448.AArch64.Neon.S a b 7 : Int) * X ^ 7 + (VG.Proof.Curve448.AArch64.Neon.S a b 8 : Int) * X ^ 8 + (VG.Proof.Curve448.AArch64.Neon.S a b 9 : Int) * X ^ 9 + (VG.Proof.Curve448.AArch64.Neon.S a b 10 : Int) * X ^ 10 + (VG.Proof.Curve448.AArch64.Neon.S a b 11 : Int) * X ^ 11 + (VG.Proof.Curve448.AArch64.Neon.S a b 12 : Int) * X ^ 12 + (VG.Proof.Curve448.AArch64.Neon.S a b 13 : Int) * X ^ 13 + (VG.Proof.Curve448.AArch64.Neon.S a b 14 : Int) * X ^ 14 := by
  rw [VG.Proof.Curve448.AArch64.Neon.conv8 X (a 0 : Int) (a 1 : Int) (a 2 : Int) (a 3 : Int) (a 4 : Int) (a 5 : Int) (a 6 : Int) (a 7 : Int) (b 0 : Int) (b 1 : Int) (b 2 : Int) (b 3 : Int) (b 4 : Int) (b 5 : Int) (b 6 : Int) (b 7 : Int)]
  simp only [VG.Proof.Curve448.AArch64.Neon.S, VG.Proof.Curve448.AArch64.Neon.cv, VG.Proof.Curve448.AArch64.Neon.hl]; push_cast; ring

theorem prodT (X : Int) (a b : Nat → Nat) : ((a 8 : Int) * X ^ 0 + (a 9 : Int) * X ^ 1 + (a 10 : Int) * X ^ 2 + (a 11 : Int) * X ^ 3 + (a 12 : Int) * X ^ 4 + (a 13 : Int) * X ^ 5 + (a 14 : Int) * X ^ 6 + (a 15 : Int) * X ^ 7) * ((b 8 : Int) * X ^ 0 + (b 9 : Int) * X ^ 1 + (b 10 : Int) * X ^ 2 + (b 11 : Int) * X ^ 3 + (b 12 : Int) * X ^ 4 + (b 13 : Int) * X ^ 5 + (b 14 : Int) * X ^ 6 + (b 15 : Int) * X ^ 7) = (VG.Proof.Curve448.AArch64.Neon.T a b 0 : Int) * X ^ 0 + (VG.Proof.Curve448.AArch64.Neon.T a b 1 : Int) * X ^ 1 + (VG.Proof.Curve448.AArch64.Neon.T a b 2 : Int) * X ^ 2 + (VG.Proof.Curve448.AArch64.Neon.T a b 3 : Int) * X ^ 3 + (VG.Proof.Curve448.AArch64.Neon.T a b 4 : Int) * X ^ 4 + (VG.Proof.Curve448.AArch64.Neon.T a b 5 : Int) * X ^ 5 + (VG.Proof.Curve448.AArch64.Neon.T a b 6 : Int) * X ^ 6 + (VG.Proof.Curve448.AArch64.Neon.T a b 7 : Int) * X ^ 7 + (VG.Proof.Curve448.AArch64.Neon.T a b 8 : Int) * X ^ 8 + (VG.Proof.Curve448.AArch64.Neon.T a b 9 : Int) * X ^ 9 + (VG.Proof.Curve448.AArch64.Neon.T a b 10 : Int) * X ^ 10 + (VG.Proof.Curve448.AArch64.Neon.T a b 11 : Int) * X ^ 11 + (VG.Proof.Curve448.AArch64.Neon.T a b 12 : Int) * X ^ 12 + (VG.Proof.Curve448.AArch64.Neon.T a b 13 : Int) * X ^ 13 + (VG.Proof.Curve448.AArch64.Neon.T a b 14 : Int) * X ^ 14 := by
  rw [VG.Proof.Curve448.AArch64.Neon.conv8 X (a 8 : Int) (a 9 : Int) (a 10 : Int) (a 11 : Int) (a 12 : Int) (a 13 : Int) (a 14 : Int) (a 15 : Int) (b 8 : Int) (b 9 : Int) (b 10 : Int) (b 11 : Int) (b 12 : Int) (b 13 : Int) (b 14 : Int) (b 15 : Int)]
  simp only [VG.Proof.Curve448.AArch64.Neon.T, VG.Proof.Curve448.AArch64.Neon.cv, VG.Proof.Curve448.AArch64.Neon.hl]; push_cast; ring

theorem prodU (X : Int) (a b : Nat → Nat) : (((a 0 + a 8) : Int) * X ^ 0 + ((a 1 + a 9) : Int) * X ^ 1 + ((a 2 + a 10) : Int) * X ^ 2 + ((a 3 + a 11) : Int) * X ^ 3 + ((a 4 + a 12) : Int) * X ^ 4 + ((a 5 + a 13) : Int) * X ^ 5 + ((a 6 + a 14) : Int) * X ^ 6 + ((a 7 + a 15) : Int) * X ^ 7) * (((b 0 + b 8) : Int) * X ^ 0 + ((b 1 + b 9) : Int) * X ^ 1 + ((b 2 + b 10) : Int) * X ^ 2 + ((b 3 + b 11) : Int) * X ^ 3 + ((b 4 + b 12) : Int) * X ^ 4 + ((b 5 + b 13) : Int) * X ^ 5 + ((b 6 + b 14) : Int) * X ^ 6 + ((b 7 + b 15) : Int) * X ^ 7) = (VG.Proof.Curve448.AArch64.Neon.U a b 0 : Int) * X ^ 0 + (VG.Proof.Curve448.AArch64.Neon.U a b 1 : Int) * X ^ 1 + (VG.Proof.Curve448.AArch64.Neon.U a b 2 : Int) * X ^ 2 + (VG.Proof.Curve448.AArch64.Neon.U a b 3 : Int) * X ^ 3 + (VG.Proof.Curve448.AArch64.Neon.U a b 4 : Int) * X ^ 4 + (VG.Proof.Curve448.AArch64.Neon.U a b 5 : Int) * X ^ 5 + (VG.Proof.Curve448.AArch64.Neon.U a b 6 : Int) * X ^ 6 + (VG.Proof.Curve448.AArch64.Neon.U a b 7 : Int) * X ^ 7 + (VG.Proof.Curve448.AArch64.Neon.U a b 8 : Int) * X ^ 8 + (VG.Proof.Curve448.AArch64.Neon.U a b 9 : Int) * X ^ 9 + (VG.Proof.Curve448.AArch64.Neon.U a b 10 : Int) * X ^ 10 + (VG.Proof.Curve448.AArch64.Neon.U a b 11 : Int) * X ^ 11 + (VG.Proof.Curve448.AArch64.Neon.U a b 12 : Int) * X ^ 12 + (VG.Proof.Curve448.AArch64.Neon.U a b 13 : Int) * X ^ 13 + (VG.Proof.Curve448.AArch64.Neon.U a b 14 : Int) * X ^ 14 := by
  rw [VG.Proof.Curve448.AArch64.Neon.conv8 X ((a 0 + a 8) : Int) ((a 1 + a 9) : Int) ((a 2 + a 10) : Int) ((a 3 + a 11) : Int) ((a 4 + a 12) : Int) ((a 5 + a 13) : Int) ((a 6 + a 14) : Int) ((a 7 + a 15) : Int) ((b 0 + b 8) : Int) ((b 1 + b 9) : Int) ((b 2 + b 10) : Int) ((b 3 + b 11) : Int) ((b 4 + b 12) : Int) ((b 5 + b 13) : Int) ((b 6 + b 14) : Int) ((b 7 + b 15) : Int)]
  simp only [VG.Proof.Curve448.AArch64.Neon.U, VG.Proof.Curve448.AArch64.Neon.cv, VG.Proof.Curve448.AArch64.Neon.hl]; push_cast; ring

theorem kara_sum (X : Int) (a b : Nat → Nat) :
    ((a 0 : Int) * X ^ 0 + (a 1 : Int) * X ^ 1 + (a 2 : Int) * X ^ 2 + (a 3 : Int) * X ^ 3 + (a 4 : Int) * X ^ 4 + (a 5 : Int) * X ^ 5 + (a 6 : Int) * X ^ 6 + (a 7 : Int) * X ^ 7 + (a 8 : Int) * X ^ 8 + (a 9 : Int) * X ^ 9 + (a 10 : Int) * X ^ 10 + (a 11 : Int) * X ^ 11 + (a 12 : Int) * X ^ 12 + (a 13 : Int) * X ^ 13 + (a 14 : Int) * X ^ 14 + (a 15 : Int) * X ^ 15) * ((b 0 : Int) * X ^ 0 + (b 1 : Int) * X ^ 1 + (b 2 : Int) * X ^ 2 + (b 3 : Int) * X ^ 3 + (b 4 : Int) * X ^ 4 + (b 5 : Int) * X ^ 5 + (b 6 : Int) * X ^ 6 + (b 7 : Int) * X ^ 7 + (b 8 : Int) * X ^ 8 + (b 9 : Int) * X ^ 9 + (b 10 : Int) * X ^ 10 + (b 11 : Int) * X ^ 11 + (b 12 : Int) * X ^ 12 + (b 13 : Int) * X ^ 13 + (b 14 : Int) * X ^ 14 + (b 15 : Int) * X ^ 15) - (VG.Proof.Curve448.AArch64.Neon.kara a b 0 * X ^ 0 + VG.Proof.Curve448.AArch64.Neon.kara a b 1 * X ^ 1 + VG.Proof.Curve448.AArch64.Neon.kara a b 2 * X ^ 2 + VG.Proof.Curve448.AArch64.Neon.kara a b 3 * X ^ 3 + VG.Proof.Curve448.AArch64.Neon.kara a b 4 * X ^ 4 + VG.Proof.Curve448.AArch64.Neon.kara a b 5 * X ^ 5 + VG.Proof.Curve448.AArch64.Neon.kara a b 6 * X ^ 6 + VG.Proof.Curve448.AArch64.Neon.kara a b 7 * X ^ 7 + VG.Proof.Curve448.AArch64.Neon.kara a b 8 * X ^ 8 + VG.Proof.Curve448.AArch64.Neon.kara a b 9 * X ^ 9 + VG.Proof.Curve448.AArch64.Neon.kara a b 10 * X ^ 10 + VG.Proof.Curve448.AArch64.Neon.kara a b 11 * X ^ 11 + VG.Proof.Curve448.AArch64.Neon.kara a b 12 * X ^ 12 + VG.Proof.Curve448.AArch64.Neon.kara a b 13 * X ^ 13 + VG.Proof.Curve448.AArch64.Neon.kara a b 14 * X ^ 14 + VG.Proof.Curve448.AArch64.Neon.kara a b 15 * X ^ 15) =
      (X ^ 16 - X ^ 8 - 1) * (((VG.Proof.Curve448.AArch64.Neon.T a b 0 : Int) * X ^ 0 + (VG.Proof.Curve448.AArch64.Neon.T a b 1 : Int) * X ^ 1 + (VG.Proof.Curve448.AArch64.Neon.T a b 2 : Int) * X ^ 2 + (VG.Proof.Curve448.AArch64.Neon.T a b 3 : Int) * X ^ 3 + (VG.Proof.Curve448.AArch64.Neon.T a b 4 : Int) * X ^ 4 + (VG.Proof.Curve448.AArch64.Neon.T a b 5 : Int) * X ^ 5 + (VG.Proof.Curve448.AArch64.Neon.T a b 6 : Int) * X ^ 6 + (VG.Proof.Curve448.AArch64.Neon.T a b 7 : Int) * X ^ 7 + (VG.Proof.Curve448.AArch64.Neon.T a b 8 : Int) * X ^ 8 + (VG.Proof.Curve448.AArch64.Neon.T a b 9 : Int) * X ^ 9 + (VG.Proof.Curve448.AArch64.Neon.T a b 10 : Int) * X ^ 10 + (VG.Proof.Curve448.AArch64.Neon.T a b 11 : Int) * X ^ 11 + (VG.Proof.Curve448.AArch64.Neon.T a b 12 : Int) * X ^ 12 + (VG.Proof.Curve448.AArch64.Neon.T a b 13 : Int) * X ^ 13 + (VG.Proof.Curve448.AArch64.Neon.T a b 14 : Int) * X ^ 14) + ((VG.Proof.Curve448.AArch64.Neon.U a b 8 : Int) * X ^ 0 + (VG.Proof.Curve448.AArch64.Neon.U a b 9 : Int) * X ^ 1 + (VG.Proof.Curve448.AArch64.Neon.U a b 10 : Int) * X ^ 2 + (VG.Proof.Curve448.AArch64.Neon.U a b 11 : Int) * X ^ 3 + (VG.Proof.Curve448.AArch64.Neon.U a b 12 : Int) * X ^ 4 + (VG.Proof.Curve448.AArch64.Neon.U a b 13 : Int) * X ^ 5 + (VG.Proof.Curve448.AArch64.Neon.U a b 14 : Int) * X ^ 6) - ((VG.Proof.Curve448.AArch64.Neon.S a b 8 : Int) * X ^ 0 + (VG.Proof.Curve448.AArch64.Neon.S a b 9 : Int) * X ^ 1 + (VG.Proof.Curve448.AArch64.Neon.S a b 10 : Int) * X ^ 2 + (VG.Proof.Curve448.AArch64.Neon.S a b 11 : Int) * X ^ 3 + (VG.Proof.Curve448.AArch64.Neon.S a b 12 : Int) * X ^ 4 + (VG.Proof.Curve448.AArch64.Neon.S a b 13 : Int) * X ^ 5 + (VG.Proof.Curve448.AArch64.Neon.S a b 14 : Int) * X ^ 6)) := by
  have hA := VG.Proof.Curve448.AArch64.Neon.halves X a
  have hB := VG.Proof.Curve448.AArch64.Neon.halves X b
  have h1 := VG.Proof.Curve448.AArch64.Neon.prodS X a b
  have h2 := VG.Proof.Curve448.AArch64.Neon.prodT X a b
  have h3 := VG.Proof.Curve448.AArch64.Neon.prodU X a b
  have hk := VG.Proof.Curve448.AArch64.Neon.kara_comb X (VG.Proof.Curve448.AArch64.Neon.S a b 0) (VG.Proof.Curve448.AArch64.Neon.S a b 1) (VG.Proof.Curve448.AArch64.Neon.S a b 2) (VG.Proof.Curve448.AArch64.Neon.S a b 3) (VG.Proof.Curve448.AArch64.Neon.S a b 4) (VG.Proof.Curve448.AArch64.Neon.S a b 5) (VG.Proof.Curve448.AArch64.Neon.S a b 6) (VG.Proof.Curve448.AArch64.Neon.S a b 7) (VG.Proof.Curve448.AArch64.Neon.S a b 8) (VG.Proof.Curve448.AArch64.Neon.S a b 9) (VG.Proof.Curve448.AArch64.Neon.S a b 10) (VG.Proof.Curve448.AArch64.Neon.S a b 11) (VG.Proof.Curve448.AArch64.Neon.S a b 12) (VG.Proof.Curve448.AArch64.Neon.S a b 13) (VG.Proof.Curve448.AArch64.Neon.S a b 14) (VG.Proof.Curve448.AArch64.Neon.T a b 0) (VG.Proof.Curve448.AArch64.Neon.T a b 1) (VG.Proof.Curve448.AArch64.Neon.T a b 2) (VG.Proof.Curve448.AArch64.Neon.T a b 3) (VG.Proof.Curve448.AArch64.Neon.T a b 4) (VG.Proof.Curve448.AArch64.Neon.T a b 5) (VG.Proof.Curve448.AArch64.Neon.T a b 6) (VG.Proof.Curve448.AArch64.Neon.T a b 7) (VG.Proof.Curve448.AArch64.Neon.T a b 8) (VG.Proof.Curve448.AArch64.Neon.T a b 9) (VG.Proof.Curve448.AArch64.Neon.T a b 10) (VG.Proof.Curve448.AArch64.Neon.T a b 11) (VG.Proof.Curve448.AArch64.Neon.T a b 12) (VG.Proof.Curve448.AArch64.Neon.T a b 13) (VG.Proof.Curve448.AArch64.Neon.T a b 14) (VG.Proof.Curve448.AArch64.Neon.U a b 0) (VG.Proof.Curve448.AArch64.Neon.U a b 1) (VG.Proof.Curve448.AArch64.Neon.U a b 2) (VG.Proof.Curve448.AArch64.Neon.U a b 3) (VG.Proof.Curve448.AArch64.Neon.U a b 4) (VG.Proof.Curve448.AArch64.Neon.U a b 5) (VG.Proof.Curve448.AArch64.Neon.U a b 6) (VG.Proof.Curve448.AArch64.Neon.U a b 7) (VG.Proof.Curve448.AArch64.Neon.U a b 8) (VG.Proof.Curve448.AArch64.Neon.U a b 9) (VG.Proof.Curve448.AArch64.Neon.U a b 10) (VG.Proof.Curve448.AArch64.Neon.U a b 11) (VG.Proof.Curve448.AArch64.Neon.U a b 12) (VG.Proof.Curve448.AArch64.Neon.U a b 13) (VG.Proof.Curve448.AArch64.Neon.U a b 14)
  have e15 : VG.Proof.Curve448.AArch64.Neon.S a b 15 = 0 ∧ VG.Proof.Curve448.AArch64.Neon.T a b 15 = 0 ∧ VG.Proof.Curve448.AArch64.Neon.U a b 15 = 0 := ⟨rfl, rfl, rfl⟩
  simp only [VG.Proof.Curve448.AArch64.Neon.kara, show (0 : Nat) < 8 by decide, show (1 : Nat) < 8 by decide, show (2 : Nat) < 8 by decide,
    show (3 : Nat) < 8 by decide, show (4 : Nat) < 8 by decide, show (5 : Nat) < 8 by decide,
    show (6 : Nat) < 8 by decide, show (7 : Nat) < 8 by decide, show ¬ (8 : Nat) < 8 by decide,
    show ¬ (9 : Nat) < 8 by decide, show ¬ (10 : Nat) < 8 by decide, show ¬ (11 : Nat) < 8 by decide,
    show ¬ (12 : Nat) < 8 by decide, show ¬ (13 : Nat) < 8 by decide, show ¬ (14 : Nat) < 8 by decide,
    show ¬ (15 : Nat) < 8 by decide, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, e15.1, e15.2.1, e15.2.2,
    Nat.cast_zero] at hk ⊢
  rw [hA, hB]
  linear_combination hk + h1 * (1 - X ^ 8) + h2 * (X ^ 16 - X ^ 8) + h3 * X ^ 8

theorem cv_mono {x y x' y' : Nat → Nat} (hx : ∀ i < 8, x i ≤ x' i) (hy : ∀ i < 8, y i ≤ y' i) (q : Nat) :
    VG.Proof.Curve448.AArch64.Neon.cv x y q ≤ VG.Proof.Curve448.AArch64.Neon.cv x' y' q := by
  have m : ∀ i j, i < 8 → j < 8 → x i * y j ≤ x' i * y' j := fun i j hi hj =>
    Nat.mul_le_mul (hx i hi) (hy j hj)
  rcases q with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | q
  all_goals simp only [VG.Proof.Curve448.AArch64.Neon.cv]
  all_goals first
    | exact Nat.le_refl _
    | (repeat' apply Nat.add_le_add) <;> exact m _ _ (by decide) (by decide)

theorem S_le_U (a b : Nat → Nat) (q : Nat) : VG.Proof.Curve448.AArch64.Neon.S a b q ≤ VG.Proof.Curve448.AArch64.Neon.U a b q :=
  VG.Proof.Curve448.AArch64.Neon.cv_mono (fun _ _ => Nat.le_add_right _ _) (fun _ _ => Nat.le_add_right _ _) q

theorem kara_nonneg (a b : Nat → Nat) (k : Nat) : 0 ≤ VG.Proof.Curve448.AArch64.Neon.kara a b k := by
  unfold VG.Proof.Curve448.AArch64.Neon.kara
  split
  · have := VG.Proof.Curve448.AArch64.Neon.S_le_U a b (k + 8); omega
  · have := VG.Proof.Curve448.AArch64.Neon.S_le_U a b (k - 8); omega

/-- Bounds on the radix-2²⁸ limbs of an operand below `Ib` in radix 2⁵⁶. -/
def lmax (k : Nat) : Nat := if k % 2 = 0 then 2 ^ 28 - 1 else 3 * 2 ^ 28

theorem kara_le {a b : Nat → Nat} (ha : ∀ k < 16, a k ≤ VG.Proof.Curve448.AArch64.Neon.lmax k) (hb : ∀ k < 16, b k ≤ VG.Proof.Curve448.AArch64.Neon.lmax k) {k : Nat}
    (hk : k < 16) : VG.Proof.Curve448.AArch64.Neon.kara a b k < 2 ^ 64 - 2 ^ 40 := by
  have hm : ∀ h < 3, ∀ i < 8, VG.Proof.Curve448.AArch64.Neon.hl a h i ≤ VG.Proof.Curve448.AArch64.Neon.hl VG.Proof.Curve448.AArch64.Neon.lmax h i ∧ VG.Proof.Curve448.AArch64.Neon.hl b h i ≤ VG.Proof.Curve448.AArch64.Neon.hl VG.Proof.Curve448.AArch64.Neon.lmax h i := by
    intro h hh i hi
    rcases (show h = 0 ∨ h = 1 ∨ h = 2 by omega) with rfl | rfl | rfl <;> simp only [VG.Proof.Curve448.AArch64.Neon.hl]
    · exact ⟨ha i (by omega), hb i (by omega)⟩
    · exact ⟨ha _ (by omega), hb _ (by omega)⟩
    · exact ⟨Nat.add_le_add (ha i (by omega)) (ha _ (by omega)), Nat.add_le_add (hb i (by omega)) (hb _ (by omega))⟩
  have bS : ∀ q, VG.Proof.Curve448.AArch64.Neon.S a b q ≤ VG.Proof.Curve448.AArch64.Neon.S VG.Proof.Curve448.AArch64.Neon.lmax VG.Proof.Curve448.AArch64.Neon.lmax q := fun q =>
    VG.Proof.Curve448.AArch64.Neon.cv_mono (fun i hi => (hm 0 (by decide) i hi).1) (fun i hi => (hm 0 (by decide) i hi).2) q
  have bT : ∀ q, VG.Proof.Curve448.AArch64.Neon.T a b q ≤ VG.Proof.Curve448.AArch64.Neon.T VG.Proof.Curve448.AArch64.Neon.lmax VG.Proof.Curve448.AArch64.Neon.lmax q := fun q =>
    VG.Proof.Curve448.AArch64.Neon.cv_mono (fun i hi => (hm 1 (by decide) i hi).1) (fun i hi => (hm 1 (by decide) i hi).2) q
  have bU : ∀ q, VG.Proof.Curve448.AArch64.Neon.U a b q ≤ VG.Proof.Curve448.AArch64.Neon.U VG.Proof.Curve448.AArch64.Neon.lmax VG.Proof.Curve448.AArch64.Neon.lmax q := fun q =>
    VG.Proof.Curve448.AArch64.Neon.cv_mono (fun i hi => (hm 2 (by decide) i hi).1) (fun i hi => (hm 2 (by decide) i hi).2) q
  have num : ∀ k < 8, VG.Proof.Curve448.AArch64.Neon.S VG.Proof.Curve448.AArch64.Neon.lmax VG.Proof.Curve448.AArch64.Neon.lmax k + VG.Proof.Curve448.AArch64.Neon.T VG.Proof.Curve448.AArch64.Neon.lmax VG.Proof.Curve448.AArch64.Neon.lmax k + VG.Proof.Curve448.AArch64.Neon.U VG.Proof.Curve448.AArch64.Neon.lmax VG.Proof.Curve448.AArch64.Neon.lmax (k + 8) < 2 ^ 64 - 2 ^ 40 ∧
      VG.Proof.Curve448.AArch64.Neon.T VG.Proof.Curve448.AArch64.Neon.lmax VG.Proof.Curve448.AArch64.Neon.lmax (k + 8) + VG.Proof.Curve448.AArch64.Neon.U VG.Proof.Curve448.AArch64.Neon.lmax VG.Proof.Curve448.AArch64.Neon.lmax k + VG.Proof.Curve448.AArch64.Neon.U VG.Proof.Curve448.AArch64.Neon.lmax VG.Proof.Curve448.AArch64.Neon.lmax (k + 8) < 2 ^ 64 - 2 ^ 40 := by decide
  unfold VG.Proof.Curve448.AArch64.Neon.kara
  split
  · have := num k (by omega); have := bS k; have := bT k; have := bU (k + 8); omega
  · have := num (k - 8) (by omega); have := bT k; have := bU (k - 8); have := bU k
    rw [show k - 8 + 8 = k by omega] at *
    omega

end VG.Proof.Curve448.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Neon.Pairs`. -/
section

/-!
# Which limbs each product multiplies

Untrusted: everything here is checked by Lean. Product `p` of a half multiplies
half-limb `ia p` of the first operand by half-limb `ib p` of the second, at
coefficient `ia p + ib p`; the products at coefficient `q` are, up to order,
the terms of `cv x y q` (`perm_q`, by evaluation).
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG.Impl.Curve448.AArch64.Neon

def ia (p : Prod) : Nat := 2 * p.i + (if p.hi then 1 else 0)
def ib (p : Prod) : Nat :=
  if p.bv < 4 then 2 * p.bv + (if p.hi then 1 else 0) else 2 * (p.bv - 4) + (if p.hi then 1 else 0) - 1

/-- The terms `(i, q - i)` of coefficient `q`. -/
def pairsQ (q : Nat) : List (Nat × Nat) :=
  ((List.range 8).filter fun i => i ≤ q ∧ q - i < 8).map fun i => (i, q - i)

theorem prods_pos : ∀ p ∈ prods, p.pos = VG.Proof.Curve448.AArch64.Neon.ia p + VG.Proof.Curve448.AArch64.Neon.ib p ∧ VG.Proof.Curve448.AArch64.Neon.ia p < 8 ∧ VG.Proof.Curve448.AArch64.Neon.ib p < 8 ∧
    (p.bv ≥ 4 → (p.hi = false → p.bv ≠ 4) ∧ (p.hi = true → p.bv ≠ 8)) := by decide

theorem perm_q : ∀ q < 15, List.Perm ((prods.filter fun p => p.pos == q).map fun p => (VG.Proof.Curve448.AArch64.Neon.ia p, VG.Proof.Curve448.AArch64.Neon.ib p)) (VG.Proof.Curve448.AArch64.Neon.pairsQ q) := by
  decide

theorem cv_pairs (x y : Nat → Nat) : ∀ q < 15, VG.Proof.Curve448.AArch64.Neon.cv x y q = ((VG.Proof.Curve448.AArch64.Neon.pairsQ q).map fun ij => x ij.1 * y ij.2).sum := by
  intro q hq
  rcases q with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | q
  all_goals first | omega | (simp [VG.Proof.Curve448.AArch64.Neon.cv, VG.Proof.Curve448.AArch64.Neon.pairsQ, List.range, List.range.loop]; try ring_nf)

end VG.Proof.Curve448.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Neon.Halves`. -/
section

/-!
# A half's products are its coefficients

Untrusted: everything here is checked by Lean. With the first operand's half
in vectors at `aHalf h` and the second's (and its shifted copy) at `bOff h`,
lane `e` of the products aimed at a register is coefficient `q` of the product
of the halves, `cv`.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon
open VG.Proof.X448.AArch64 (Scr off)

/-- The memory words of a half: element `c % 2`'s half-limb `2i + c / 2` in word `c` of vector `i`,
and the shifted copy of the second operand. -/
structure HalfMem (m : Mem) (base : Addr) (h : Nat) (X Y : Nat → Nat → Nat) : Prop where
  a : ∀ i < 4, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw m base (aHalf h + 16 * i + 4 * c) = X (c % 2) (2 * i + c / 2)
  b : ∀ j < 4, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw m base (bHalf h + 16 * j + 4 * c) = Y (c % 2) (2 * j + c / 2)
  sh : ∀ j < 5, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw m base (NBP + 80 * h + 16 * j + 4 * c) =
    if c < 2 then (if j = 0 then 0 else Y (c % 2) (2 * j - 1)) else (if j = 4 then 0 else Y (c % 2) (2 * j))

theorem prodVal_eq {m : Mem} {base : Addr} {h : Nat} {X Y : Nat → Nat → Nat} (hm : VG.Proof.Curve448.AArch64.Neon.HalfMem m base h X Y)
    {p : Prod} (hpm : p ∈ prods) {e : Nat} (he : e < 2) :
    VG.Proof.Curve448.AArch64.Neon.prodVal (fun i => m.read (VG.Proof.X448.AArch64.off base (aHalf h + 16 * i)) 16) (fun bv => m.read (VG.Proof.X448.AArch64.off base (bOff h bv)) 16) p e =
      X e (VG.Proof.Curve448.AArch64.Neon.ia p) * Y e (VG.Proof.Curve448.AArch64.Neon.ib p) := by
  obtain ⟨-, -, -, hz⟩ := VG.Proof.Curve448.AArch64.Neon.prods_pos p hpm
  obtain ⟨pi, pb⟩ := VG.Proof.Curve448.AArch64.Neon.prods_facts p hpm
  have hc : VG.Proof.Curve448.AArch64.Neon.hp p.hi + e < 4 := by unfold VG.Proof.Curve448.AArch64.Neon.hp; split <;> omega
  simp only [VG.Proof.Curve448.AArch64.Neon.prodVal]
  rw [VG.Proof.Curve448.AArch64.Neon.vword_ld _ _ _ hc, VG.Proof.Curve448.AArch64.Neon.vword_ld _ _ _ hc, hm.a _ pi _ hc]
  have e1 : (VG.Proof.Curve448.AArch64.Neon.hp p.hi + e) % 2 = e := by unfold VG.Proof.Curve448.AArch64.Neon.hp; split <;> omega
  have e2 : (VG.Proof.Curve448.AArch64.Neon.hp p.hi + e) / 2 = if p.hi then 1 else 0 := by unfold VG.Proof.Curve448.AArch64.Neon.hp; split <;> omega
  rw [e1, e2]
  congr 1
  unfold bOff VG.Proof.Curve448.AArch64.Neon.ib
  split
  · rename_i hb; rw [hm.b _ hb _ hc, e1, e2]
  · rename_i hb
    rw [show NBP + 80 * h + 16 * (p.bv - 4) + 4 * (VG.Proof.Curve448.AArch64.Neon.hp p.hi + e) = NBP + 80 * h + 16 * (p.bv - 4) + 4 * (VG.Proof.Curve448.AArch64.Neon.hp p.hi + e)
      from rfl, hm.sh _ (by omega) _ hc, e1]
    cases hhi : p.hi
    · have := (hz (by omega)).1 hhi
      simp only [VG.Proof.Curve448.AArch64.Neon.hp, Bool.false_eq_true, ite_false, Nat.zero_add, Nat.add_zero, show e < 2 from he, ite_true,
        show p.bv - 4 ≠ 0 by omega]
    · have := (hz (by omega)).2 hhi
      simp only [VG.Proof.Curve448.AArch64.Neon.hp, ite_true, show ¬ (2 + e < 2) by omega, ite_false, show p.bv - 4 ≠ 4 by omega,
        Nat.add_sub_cancel]

theorem cast_sum {α : Type} (l : List α) (f : α → Nat) :
    (((l.map f).sum : Nat) : Int) = (l.map fun x => (f x : Int)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.sum_cons, ih]

theorem prodSum_cv {m : Mem} {base : Addr} {h : Nat} {X Y : Nat → Nat → Nat} (hm : VG.Proof.Curve448.AArch64.Neon.HalfMem m base h X Y)
    {tgt : Nat → Nat} {r q : Nat} (hq : q < 15) (ht : ∀ p ∈ prods, tgt p.pos = r ↔ p.pos = q) {e : Nat} (he : e < 2) :
    VG.Proof.Curve448.AArch64.Neon.prodSum (fun i => m.read (VG.Proof.X448.AArch64.off base (aHalf h + 16 * i)) 16) (fun bv => m.read (VG.Proof.X448.AArch64.off base (bOff h bv)) 16)
      tgt prods r e = VG.Proof.Curve448.AArch64.Neon.cv (X e) (Y e) q := by
  simp only [VG.Proof.Curve448.AArch64.Neon.prodSum]
  rw [List.filter_congr (q := fun p => p.pos == q) fun p hp => by simp [ht p hp],
    List.map_congr_left (g := fun p => ((X e (VG.Proof.Curve448.AArch64.Neon.ia p) * Y e (VG.Proof.Curve448.AArch64.Neon.ib p) : Nat) : Int)) fun p hp => by
      rw [VG.Proof.Curve448.AArch64.Neon.prodVal_eq hm (List.mem_filter.mp hp).1 he],
    VG.Proof.Curve448.AArch64.Neon.cv_pairs _ _ q hq]
  have hperm := (VG.Proof.Curve448.AArch64.Neon.perm_q q hq).map (fun ij : Nat × Nat => ((X e ij.1 * Y e ij.2 : Nat) : Int))
  rw [List.map_map] at hperm
  rw [show (fun p => ((X e (VG.Proof.Curve448.AArch64.Neon.ia p) * Y e (VG.Proof.Curve448.AArch64.Neon.ib p) : Nat) : Int)) =
    (fun ij : Nat × Nat => ((X e ij.1 * Y e ij.2 : Nat) : Int)) ∘ (fun p => (VG.Proof.Curve448.AArch64.Neon.ia p, VG.Proof.Curve448.AArch64.Neon.ib p)) from rfl, hperm.sum_eq]
  rw [VG.Proof.Curve448.AArch64.Neon.cast_sum]

end VG.Proof.Curve448.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Neon.Prep`. -/
section

/-!
# The constants, the operand sums and the shifted second operands

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon
open VG.Proof.X448.AArch64 (Scr off ofs Outside)

/-! ## Constants -/

theorem consts_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) :
    WP isa (.block VG.Impl.Curve448.AArch64.Neon.consts) s fun t =>
      (∀ e < 2, (vdword (t.v (V 30)) e).toNat = 2 ^ 28 - 1) ∧ t.v (V 31) = 0 ∧ t.mem = s.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr = s.gpr ∧
      (∀ r : VReg, r ≠ V 30 → r ≠ V 31 → t.v r = s.v r) ∧ VG.Proof.X448.AArch64.Scr t base := by
  refine WP.of_runBlock ⟨_, by
    simp only [VG.Impl.Curve448.AArch64.Neon.consts, runBlock_cons, runStep_some, runBlock_nil, exec, vo, VOp.eval,
      Option.map_some]; rfl, ?_⟩
  refine ⟨fun e he => ?_, ?_, rfl, rfl, rfl, by simp only [RegUpd.gpr_setV], fun r h1 h2 => ?_,
    VG.Proof.Curve448.AArch64.Neon.scr_of hs (by simp only [RegUpd.gpr_setV]) rfl⟩
  · simp only [RegUpd.v_setV_of_ne _ _ (show V 30 ≠ V 31 by decide), RegUpd.v_setV_self]
    rw [VG.Proof.Curve448.AArch64.Neon.vdword_ofVDwords _ _ he]
    split <;> rw [hs.mask] <;> rfl
  · simp only [RegUpd.v_setV_self]
  · simp only [RegUpd.v_setV_of_ne _ _ h2, RegUpd.v_setV_of_ne _ _ h1]

/-! ## Sums -/

/-- One step of `sums`: vector `i` of `a₀ + a₁` and of `b₀ + b₁`. -/
def sumChunk (i : Nat) : List Instr :=
  [ldq 0 (NA + 16 * i), ldq 1 (NA + 16 * (i + 4)), vo (.add .s4 (V 0) (V 0) (V 1)), stq 0 (NAS + 16 * i),
    ldq 2 (NB + 16 * i), ldq 3 (NB + 16 * (i + 4)), vo (.add .s4 (V 2) (V 2) (V 3)), stq 2 (NBS + 16 * i)]

theorem sums_eq : sums = (List.range 4).flatMap VG.Proof.Curve448.AArch64.Neon.sumChunk := rfl

theorem vword_add (x y : BitVec 128) {c : Nat} (hc : c < 4) :
    (vword (VArr.s4.map2 (fun _ a b => a + b) x y) c).toNat = ((vword x c).toNat + (vword y c).toNat) % 2 ^ 32 := by
  rw [vword_map2 _ _ _ hc, BitVec.toNat_add]

theorem sumChunk_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {i : Nat} (hi : i < 4) :
    WP isa (.block (VG.Proof.Curve448.AArch64.Neon.sumChunk i)) s fun t =>
      (∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t.mem base (NAS + 16 * i + 4 * c) =
        (VG.Proof.Curve448.AArch64.Neon.nw s.mem base (NA + 16 * i + 4 * c) + VG.Proof.Curve448.AArch64.Neon.nw s.mem base (NA + 16 * (i + 4) + 4 * c)) % 2 ^ 32) ∧
      (∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t.mem base (NBS + 16 * i + 4 * c) =
        (VG.Proof.Curve448.AArch64.Neon.nw s.mem base (NB + 16 * i + 4 * c) + VG.Proof.Curve448.AArch64.Neon.nw s.mem base (NB + 16 * (i + 4) + 4 * c)) % 2 ^ 32) ∧
      VG.Proof.X448.AArch64.Outside base NAS 128 s.mem t.mem ∧
      ((∀ d, d + 4 ≤ 8192 → (d + 4 ≤ NAS + 16 * i ∨ NAS + 16 * i + 16 ≤ d) →
        (d + 4 ≤ NBS + 16 * i ∨ NBS + 16 * i + 16 ≤ d) → VG.Proof.Curve448.AArch64.Neon.nw t.mem base d = VG.Proof.Curve448.AArch64.Neon.nw s.mem base d)) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, r ∉ [V 0, V 1, V 2, V 3] → t.v r = s.v r) := by
  have hNA : NA = 4096 := rfl
  have hNB : NB = 4224 := rfl
  have hNAS : NAS = 4352 := rfl
  have hNBS : NBS = 4416 := rfl
  have n01 : V 0 ≠ V 1 := by decide
  have n10 : V 1 ≠ V 0 := by decide
  have n02 : V 0 ≠ V 2 := by decide
  have n20 : V 2 ≠ V 0 := by decide
  have n03 : V 0 ≠ V 3 := by decide
  have n30 : V 3 ≠ V 0 := by decide
  have n12 : V 1 ≠ V 2 := by decide
  have n21 : V 2 ≠ V 1 := by decide
  have n13 : V 1 ≠ V 3 := by decide
  have n31 : V 3 ≠ V 1 := by decide
  have n23 : V 2 ≠ V 3 := by decide
  have n32 : V 3 ≠ V 2 := by decide
  simp only [VG.Proof.Curve448.AArch64.Neon.sumChunk]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_ldq hs 0 (by omega) (by omega), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_ldq (base := base) ?g1 1 (by omega) (by omega), ?_⟩
  case g1 => scr
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_stq (base := base) ?g2 0 (by omega) (by omega), ?_⟩
  case g2 => scr
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_ldq (base := base) ?g3 2 (by omega) (by omega), ?_⟩
  case g3 => scr
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_ldq (base := base) ?g4 3 (by omega) (by omega), ?_⟩
  case g4 => scr
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_stq (base := base) ?g5 2 (by omega) (by omega), ?_⟩
  case g5 => scr
  refine WP.block_nil_iff.mpr ?_
  vred
  simp only [VG.Proof.Curve448.AArch64.Neon.setMem_gpr, VG.Proof.Curve448.AArch64.Neon.setMem_rd, VG.Proof.Curve448.AArch64.Neon.setMem_wr, RegUpd.gpr_setV, RegUpd.rd_setV, RegUpd.wr_setV]
  generalize hm1 : s.mem.write (VG.Proof.X448.AArch64.off base (NAS + 16 * i)) 16 _ = m1
  have o1 : VG.Proof.X448.AArch64.Outside base (NAS + 16 * i) 16 s.mem m1 := hm1 ▸ VG.Proof.Curve448.AArch64.Neon.st_outside _ _ _ (by omega)
  have r1 : ∀ d, d + 4 ≤ 8192 → (d + 4 ≤ NAS + 16 * i ∨ NAS + 16 * i + 16 ≤ d) → VG.Proof.Curve448.AArch64.Neon.nw m1 base d = VG.Proof.Curve448.AArch64.Neon.nw s.mem base d :=
    fun d h1 h2 => Outside.nw o1 h2 h1
  refine ⟨fun c hc => ?_, fun c hc => ?_, ?_, fun d h1 h2 h3 => ?_, trivial, trivial, trivial, fun r hr => ?_⟩
  · rw [VG.Proof.Curve448.AArch64.Neon.nw_st_other _ _ _ (by omega) (by omega) (by omega), ← hm1, VG.Proof.Curve448.AArch64.Neon.nw_st _ _ _ _ hc, VG.Proof.Curve448.AArch64.Neon.vword_add _ _ hc,
      VG.Proof.Curve448.AArch64.Neon.vword_ld _ _ _ hc, VG.Proof.Curve448.AArch64.Neon.vword_ld _ _ _ hc]
  · rw [VG.Proof.Curve448.AArch64.Neon.nw_st _ _ _ _ hc, VG.Proof.Curve448.AArch64.Neon.vword_add _ _ hc, VG.Proof.Curve448.AArch64.Neon.vword_ld _ _ _ hc, VG.Proof.Curve448.AArch64.Neon.vword_ld _ _ _ hc, r1 _ (by omega) (by omega),
      r1 _ (by omega) (by omega)]
  · exact (o1.mono (by omega) (by omega)).trans ((VG.Proof.Curve448.AArch64.Neon.st_outside _ base _ (by omega)).mono (by omega) (by omega))
  · rw [VG.Proof.Curve448.AArch64.Neon.nw_st_other _ _ _ (by omega) h1 h3, r1 d h1 h2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r0, r1', r2, r3⟩ := hr
    simp only [VG.Proof.Curve448.AArch64.Neon.setMem_v, RegUpd.v_setV_of_ne _ _ r0, RegUpd.v_setV_of_ne _ _ r1', RegUpd.v_setV_of_ne _ _ r2,
      RegUpd.v_setV_of_ne _ _ r3]

theorem sums_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) :
    WP isa (.block sums) s fun t =>
      (∀ i < 4, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t.mem base (NAS + 16 * i + 4 * c) =
        (VG.Proof.Curve448.AArch64.Neon.nw s.mem base (NA + 16 * i + 4 * c) + VG.Proof.Curve448.AArch64.Neon.nw s.mem base (NA + 16 * (i + 4) + 4 * c)) % 2 ^ 32) ∧
      (∀ i < 4, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t.mem base (NBS + 16 * i + 4 * c) =
        (VG.Proof.Curve448.AArch64.Neon.nw s.mem base (NB + 16 * i + 4 * c) + VG.Proof.Curve448.AArch64.Neon.nw s.mem base (NB + 16 * (i + 4) + 4 * c)) % 2 ^ 32) ∧
      VG.Proof.X448.AArch64.Outside base NAS 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, r ∉ [V 0, V 1, V 2, V 3] → t.v r = s.v r) := by
  have hNA : NA = 4096 := rfl
  have hNB : NB = 4224 := rfl
  have hNAS : NAS = 4352 := rfl
  have hNBS : NBS = 4416 := rfl
  rw [VG.Proof.Curve448.AArch64.Neon.sums_eq]
  let inv := fun n (t : State) =>
    (∀ i < n, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t.mem base (NAS + 16 * i + 4 * c) =
      (VG.Proof.Curve448.AArch64.Neon.nw s.mem base (NA + 16 * i + 4 * c) + VG.Proof.Curve448.AArch64.Neon.nw s.mem base (NA + 16 * (i + 4) + 4 * c)) % 2 ^ 32) ∧
    (∀ i < n, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t.mem base (NBS + 16 * i + 4 * c) =
      (VG.Proof.Curve448.AArch64.Neon.nw s.mem base (NB + 16 * i + 4 * c) + VG.Proof.Curve448.AArch64.Neon.nw s.mem base (NB + 16 * (i + 4) + 4 * c)) % 2 ^ 32) ∧
    VG.Proof.X448.AArch64.Outside base NAS 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ r : VReg, r ∉ [V 0, V 1, V 2, V 3] → t.v r = s.v r)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) inv (fun n t hn ⟨ta, tb, tO, tg, tr, tw, tv⟩ => ?_) 4
    (by decide) s ⟨fun _ h => absurd h (by omega), fun _ h => absurd h (by omega), Outside.refl _ _ _ _,
      rfl, rfl, rfl, fun _ _ => rfl⟩) fun t ht => ht
  have ht : VG.Proof.X448.AArch64.Scr t base := VG.Proof.Curve448.AArch64.Neon.scr_of hs tg tw
  have same : ∀ d, d + 4 ≤ 8192 → (d + 4 ≤ NAS ∨ NAS + 128 ≤ d) → VG.Proof.Curve448.AArch64.Neon.nw t.mem base d = VG.Proof.Curve448.AArch64.Neon.nw s.mem base d :=
    fun d h1 h2 => Outside.nw tO h2 h1
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.sumChunk_ok ht hn) fun u ⟨ua, ub, uO, uk, ug, ur, uw, uv⟩ =>
    ⟨fun i hi c hc => ?_, fun i hi c hc => ?_, tO.trans (uO.mono (by omega) (by omega)), ug.trans tg, ur.trans tr,
      uw.trans tw, fun r hr => (uv r hr).trans (tv r hr)⟩
  · rcases (show i < n ∨ i = n by omega) with h | rfl
    · rw [uk _ (by omega) (by omega) (by omega)]; exact ta i h c hc
    · rw [ua c hc, same _ (by omega) (by omega), same _ (by omega) (by omega)]
  · rcases (show i < n ∨ i = n by omega) with h | rfl
    · rw [uk _ (by omega) (by omega) (by omega)]; exact tb i h c hc
    · rw [ub c hc, same _ (by omega) (by omega), same _ (by omega) (by omega)]

/-! ## Shifted second operands -/

/-- Word `c` of shifted vector `j` of half `h`, from the words `w` of memory. -/
def shw (w : Nat → Nat) (h j c : Nat) : Nat :=
  if c < 2 then (if j = 0 then 0 else w (bHalf h + 16 * (j - 1) + 4 * (c + 2)))
  else (if j = 4 then 0 else w (bHalf h + 16 * j + 4 * (c - 2)))

def shiftChunk (h : Nat) : List Instr :=
  [ldq 0 (bHalf h + 16 * 0), ldq 1 (bHalf h + 16 * 1), ldq 2 (bHalf h + 16 * 2), ldq 3 (bHalf h + 16 * 3),
    vo (.ext (V 4) (V 31) (V 0) 8), vo (.ext (V 5) (V 0) (V 1) 8), vo (.ext (V 6) (V 1) (V 2) 8),
    vo (.ext (V 7) (V 2) (V 3) 8), vo (.ext (V 8) (V 3) (V 31) 8),
    stq 4 (NBP + 80 * h + 16 * 0), stq 5 (NBP + 80 * h + 16 * 1), stq 6 (NBP + 80 * h + 16 * 2),
    stq 7 (NBP + 80 * h + 16 * 3), stq 8 (NBP + 80 * h + 16 * 4)]

theorem shifted_eq : shifted = (List.range 3).flatMap VG.Proof.Curve448.AArch64.Neon.shiftChunk := rfl

theorem bHalf_lt (h : Nat) : NB ≤ bHalf h ∧ bHalf h + 64 ≤ NBS + 64 ∧ bHalf h % 16 = 0 := by
  unfold bHalf NB NBS NA; split <;> omega

theorem ext_words (n m : BitVec 128) (c : Nat) (hc : c < 4) :
    (vword (extv n m) c).toNat = if c < 2 then (vword n (c + 2)).toNat else (vword m (c - 2)).toNat := by
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [ext8_0]; rfl
  · rw [ext8_1]; rfl
  · rw [ext8_2]; rfl
  · rw [ext8_3]; rfl

theorem shw_0 (w : Nat → Nat) (h c : Nat) :
    VG.Proof.Curve448.AArch64.Neon.shw w h 0 c = if c < 2 then 0 else w (bHalf h + 16 * 0 + 4 * (c - 2)) := by simp [VG.Proof.Curve448.AArch64.Neon.shw]
theorem shw_1 (w : Nat → Nat) (h c : Nat) :
    VG.Proof.Curve448.AArch64.Neon.shw w h 1 c = if c < 2 then w (bHalf h + 16 * 0 + 4 * (c + 2)) else w (bHalf h + 16 * 1 + 4 * (c - 2)) := by
  simp [VG.Proof.Curve448.AArch64.Neon.shw]
theorem shw_2 (w : Nat → Nat) (h c : Nat) :
    VG.Proof.Curve448.AArch64.Neon.shw w h 2 c = if c < 2 then w (bHalf h + 16 * 1 + 4 * (c + 2)) else w (bHalf h + 16 * 2 + 4 * (c - 2)) := by
  simp [VG.Proof.Curve448.AArch64.Neon.shw]
theorem shw_3 (w : Nat → Nat) (h c : Nat) :
    VG.Proof.Curve448.AArch64.Neon.shw w h 3 c = if c < 2 then w (bHalf h + 16 * 2 + 4 * (c + 2)) else w (bHalf h + 16 * 3 + 4 * (c - 2)) := by
  simp [VG.Proof.Curve448.AArch64.Neon.shw]
theorem shw_4 (w : Nat → Nat) (h c : Nat) :
    VG.Proof.Curve448.AArch64.Neon.shw w h 4 c = if c < 2 then w (bHalf h + 16 * 3 + 4 * (c + 2)) else 0 := by simp [VG.Proof.Curve448.AArch64.Neon.shw]

theorem shiftChunk_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {h : Nat} (hh : h < 3)
    (h31 : s.v (V 31) = 0) :
    WP isa (.block (VG.Proof.Curve448.AArch64.Neon.shiftChunk h)) s fun t =>
      (∀ j < 5, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t.mem base (NBP + 80 * h + 16 * j + 4 * c) = VG.Proof.Curve448.AArch64.Neon.shw (VG.Proof.Curve448.AArch64.Neon.nw s.mem base) h j c) ∧
      VG.Proof.X448.AArch64.Outside base (NBP + 80 * h) 80 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, r ∉ [V 0, V 1, V 2, V 3, V 4, V 5, V 6, V 7, V 8] → t.v r = s.v r) := by
  have hNBP : NBP = 4480 := rfl
  obtain ⟨b1, b2, b3⟩ := VG.Proof.Curve448.AArch64.Neon.bHalf_lt h
  have hNB : NB = 4224 := rfl
  have hNBS : NBS = 4416 := rfl
  have ne : ∀ a < 32, ∀ b < 32, a ≠ b → V a ≠ V b := VG.Proof.Curve448.AArch64.Neon.V_ne
  have n0_31 := ne 0 (by decide) 31 (by decide) (by decide)
  have n31_0 := ne 31 (by decide) 0 (by decide) (by decide)
  simp only [VG.Proof.Curve448.AArch64.Neon.shiftChunk]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_ldq hs 0 (by omega) (by omega), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_ldq (base := base) ?g1 1 (by omega) (by omega), ?_⟩
  case g1 => scr
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_ldq (base := base) ?g2 2 (by omega) (by omega), ?_⟩
  case g2 => scr
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_ldq (base := base) ?g3 3 (by omega) (by omega), ?_⟩
  case g3 => scr
  simp only [RegUpd.mem_setV]
  generalize hL : s.mem.read (VG.Proof.X448.AArch64.off base (bHalf h + 16 * 0)) 16 = L0
  generalize hL1 : s.mem.read (VG.Proof.X448.AArch64.off base (bHalf h + 16 * 1)) 16 = L1
  generalize hL2 : s.mem.read (VG.Proof.X448.AArch64.off base (bHalf h + 16 * 2)) 16 = L2
  generalize hL3 : s.mem.read (VG.Proof.X448.AArch64.off base (bHalf h + 16 * 3)) 16 = L3
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  simp (config := {decide := true}) only [RegUpd.v_setV, ite_true, ite_false, h31]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_stq (base := base) ?g4 4 (by omega) (by omega), ?_⟩
  case g4 => scr
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_stq (base := base) ?g5 5 (by omega) (by omega), ?_⟩
  case g5 => scr
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_stq (base := base) ?g6 6 (by omega) (by omega), ?_⟩
  case g6 => scr
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_stq (base := base) ?g7 7 (by omega) (by omega), ?_⟩
  case g7 => scr
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_stq (base := base) ?g8 8 (by omega) (by omega), ?_⟩
  case g8 => scr
  refine WP.block_nil_iff.mpr ?_
  simp (config := {decide := true}) only [RegUpd.v_setV, VG.Proof.Curve448.AArch64.Neon.setMem_v, VG.Proof.Curve448.AArch64.Neon.setMem_mem, RegUpd.mem_setV, ite_true,
    ite_false, VG.Proof.Curve448.AArch64.Neon.setMem_gpr, VG.Proof.Curve448.AArch64.Neon.setMem_rd, VG.Proof.Curve448.AArch64.Neon.setMem_wr, RegUpd.gpr_setV, RegUpd.rd_setV, RegUpd.wr_setV,
    show ∀ x y : BitVec 128, BitVec.extractLsb' 0 128 ((y ++ x) >>> (8 * 8)) = extv x y from fun _ _ => rfl]
  have w0 : ∀ c < 4, (vword (0 : BitVec 128) c).toNat = 0 := fun c _ => by simp [vword]
  have wL : ∀ k < 4, ∀ c < 4, (vword (s.mem.read (VG.Proof.X448.AArch64.off base (bHalf h + 16 * k)) 16) c).toNat =
      VG.Proof.Curve448.AArch64.Neon.nw s.mem base (bHalf h + 16 * k + 4 * c) := fun k _ c hc => VG.Proof.Curve448.AArch64.Neon.vword_ld _ _ _ hc
  rw [← hL] at *
  rw [← hL1, ← hL2, ← hL3]
  generalize hm : s.mem.write (VG.Proof.X448.AArch64.off base (NBP + 80 * h + 16 * 0)) 16 _ = m0
  have E : ∀ (x y : BitVec 128) (c : Nat), c < 4 → (vword (extv x y) c).toNat =
      if c < 2 then (vword x (c + 2)).toNat else (vword y (c - 2)).toNat := fun x y c hc => VG.Proof.Curve448.AArch64.Neon.ext_words x y c hc
  refine ⟨fun j hj c hc => ?_, ?_, trivial, trivial, trivial, fun r hr => ?_⟩
  · rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · rw [VG.Proof.Curve448.AArch64.Neon.nw_st_other _ _ _ (by omega) (by omega) (by omega), VG.Proof.Curve448.AArch64.Neon.nw_st_other _ _ _ (by omega) (by omega) (by omega),
        VG.Proof.Curve448.AArch64.Neon.nw_st_other _ _ _ (by omega) (by omega) (by omega), VG.Proof.Curve448.AArch64.Neon.nw_st_other _ _ _ (by omega) (by omega) (by omega),
        ← hm, VG.Proof.Curve448.AArch64.Neon.nw_st _ _ _ _ hc, E _ _ c hc, VG.Proof.Curve448.AArch64.Neon.shw_0]
      split
      · exact w0 _ (by omega)
      · exact wL 0 (by decide) _ (by omega)
    · rw [VG.Proof.Curve448.AArch64.Neon.nw_st_other _ _ _ (by omega) (by omega) (by omega), VG.Proof.Curve448.AArch64.Neon.nw_st_other _ _ _ (by omega) (by omega) (by omega),
        VG.Proof.Curve448.AArch64.Neon.nw_st_other _ _ _ (by omega) (by omega) (by omega), VG.Proof.Curve448.AArch64.Neon.nw_st _ _ _ _ hc, E _ _ c hc, VG.Proof.Curve448.AArch64.Neon.shw_1]
      split
      · exact wL 0 (by decide) _ (by omega)
      · exact wL 1 (by decide) _ (by omega)
    · rw [VG.Proof.Curve448.AArch64.Neon.nw_st_other _ _ _ (by omega) (by omega) (by omega), VG.Proof.Curve448.AArch64.Neon.nw_st_other _ _ _ (by omega) (by omega) (by omega),
        VG.Proof.Curve448.AArch64.Neon.nw_st _ _ _ _ hc, E _ _ c hc, VG.Proof.Curve448.AArch64.Neon.shw_2]
      split
      · exact wL 1 (by decide) _ (by omega)
      · exact wL 2 (by decide) _ (by omega)
    · rw [VG.Proof.Curve448.AArch64.Neon.nw_st_other _ _ _ (by omega) (by omega) (by omega), VG.Proof.Curve448.AArch64.Neon.nw_st _ _ _ _ hc, E _ _ c hc, VG.Proof.Curve448.AArch64.Neon.shw_3]
      split
      · exact wL 2 (by decide) _ (by omega)
      · exact wL 3 (by decide) _ (by omega)
    · rw [VG.Proof.Curve448.AArch64.Neon.nw_st _ _ _ _ hc, E _ _ c hc, VG.Proof.Curve448.AArch64.Neon.shw_4]
      split
      · exact wL 3 (by decide) _ (by omega)
      · exact w0 _ (by omega)
  · rw [← hm]
    exact ((VG.Proof.Curve448.AArch64.Neon.st_outside _ base _ (by omega)).mono (by omega) (by omega)).trans
      (((VG.Proof.Curve448.AArch64.Neon.st_outside _ base _ (by omega)).mono (by omega) (by omega)).trans
      (((VG.Proof.Curve448.AArch64.Neon.st_outside _ base _ (by omega)).mono (by omega) (by omega)).trans
      (((VG.Proof.Curve448.AArch64.Neon.st_outside _ base _ (by omega)).mono (by omega) (by omega)).trans
      ((VG.Proof.Curve448.AArch64.Neon.st_outside _ base _ (by omega)).mono (by omega) (by omega)))))
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8⟩ := hr
    simp only [r0, r1, r2, r3, r4, r5, r6, r7, r8, ite_false]

theorem shifted_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) (h31 : s.v (V 31) = 0) :
    WP isa (.block shifted) s fun t =>
      (∀ h < 3, ∀ j < 5, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t.mem base (NBP + 80 * h + 16 * j + 4 * c) = VG.Proof.Curve448.AArch64.Neon.shw (VG.Proof.Curve448.AArch64.Neon.nw s.mem base) h j c) ∧
      VG.Proof.X448.AArch64.Outside base NBP 240 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, r ∉ [V 0, V 1, V 2, V 3, V 4, V 5, V 6, V 7, V 8] → t.v r = s.v r) := by
  have hNBP : NBP = 4480 := rfl
  have hNB : NB = 4224 := rfl
  have hNBS : NBS = 4416 := rfl
  rw [VG.Proof.Curve448.AArch64.Neon.shifted_eq]
  let inv := fun n (t : State) =>
    (∀ h < n, ∀ j < 5, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t.mem base (NBP + 80 * h + 16 * j + 4 * c) = VG.Proof.Curve448.AArch64.Neon.shw (VG.Proof.Curve448.AArch64.Neon.nw s.mem base) h j c) ∧
    VG.Proof.X448.AArch64.Outside base NBP 240 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ r : VReg, r ∉ [V 0, V 1, V 2, V 3, V 4, V 5, V 6, V 7, V 8] → t.v r = s.v r)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 3) inv (fun n t hn ⟨ta, tO, tg, tr, tw, tv⟩ => ?_) 3
    (by decide) s ⟨fun _ h => absurd h (by omega), Outside.refl _ _ _ _, rfl, rfl, rfl, fun _ _ => rfl⟩)
    fun t ht => ht
  have ht : VG.Proof.X448.AArch64.Scr t base := VG.Proof.Curve448.AArch64.Neon.scr_of hs tg tw
  have t31 : t.v (V 31) = 0 := by rw [tv _ (by decide)]; exact h31
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.shiftChunk_ok ht hn t31) fun u ⟨ua, uO, ug, ur, uw, uv⟩ =>
    ⟨fun h hh j hj c hc => ?_, tO.trans (uO.mono (by omega) (by omega)), ug.trans tg, ur.trans tr,
      uw.trans tw, fun r hr => (uv r hr).trans (tv r hr)⟩
  rcases (show h < n ∨ h = n by omega) with hl | rfl
  · rw [Outside.nw uO (by omega) (by omega)]; exact ta h hl j hj c hc
  · rw [ua j hj c hc]
    obtain ⟨b1, b2, b3⟩ := VG.Proof.Curve448.AArch64.Neon.bHalf_lt h
    have same : ∀ d, d + 4 ≤ NBP → VG.Proof.Curve448.AArch64.Neon.nw t.mem base d = VG.Proof.Curve448.AArch64.Neon.nw s.mem base d := fun d hd =>
      Outside.nw tO (Or.inl hd) (by omega)
    unfold VG.Proof.Curve448.AArch64.Neon.shw
    split <;> split <;> first | rfl | exact same _ (by omega)

end VG.Proof.Curve448.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Neon.NFinish`. -/
section

/-!
# The radix-2⁵⁶ results

Untrusted: everything here is checked by Lean. The sixteen radix-2²⁸ limbs
become eight radix-2⁵⁶ limbs, limbs 0 and 4 carry into 1 and 5, and the
two elements' limbs are stored.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon
open VG.Proof.X448.AArch64 (Scr off ofs Outside word limbs)

theorem read16_write (m : Mem) (p : Addr) (v : BitVec 128) : (m.write p 16 v).read p 16 = v := by
  have := Mem.readW_writeW_self m p 16 v (by decide)
  simpa [Mem.readW, Mem.writeW] using this

theorem word_st (m : Mem) (base : Addr) (d : Nat) (v : BitVec 128) {e : Nat} (he : e < 2) :
    VG.Proof.X448.AArch64.word (m.write (VG.Proof.X448.AArch64.off base d) 16 v) base (d + 8 * e) = vdword v e := by
  simp only [VG.Proof.X448.AArch64.word]
  rw [← VG.Proof.Curve448.AArch64.Neon.off_add, ← vdword_read16 _ _ he, VG.Proof.Curve448.AArch64.Neon.read16_write]

def combineChunk (i : Nat) : List Instr :=
  [vo (.shift .shl .d2 (V (16 + i)) (V (2 * i + 1)) 28), vo (.add .d2 (V (16 + i)) (V (16 + i)) (V (2 * i)))]

def m56 : List Instr :=
  [vo (.shift .shl .d2 (V 31) (V 30) 28), vo (.add .d2 (V 31) (V 31) (V 30))]

def carry56 (i : Nat) : List Instr :=
  [vo (.shift .ushr .d2 (V 28) (V i) 56), vo (.logic .and (V i) (V i) (V 31)),
    vo (.add .d2 (V (i + 1)) (V (i + 1)) (V 28))]

def outChunk (o₁ o₂ k : Nat) : List Instr :=
  [vo (.perm .trn1 .d2 (V 8) (V (16 + 2 * k)) (V (17 + 2 * k))),
    vo (.perm .trn2 .d2 (V 9) (V (16 + 2 * k)) (V (17 + 2 * k))), stq 8 (o₁ + 16 * k), stq 9 (o₂ + 16 * k)]

theorem finish_eq (o₁ o₂ : Nat) :
    VG.Impl.Curve448.AArch64.Neon.finish o₁ o₂ = (List.range 8).flatMap VG.Proof.Curve448.AArch64.Neon.combineChunk ++ VG.Proof.Curve448.AArch64.Neon.m56 ++ ([16, 20].flatMap VG.Proof.Curve448.AArch64.Neon.carry56) ++
      (List.range 4).flatMap (VG.Proof.Curve448.AArch64.Neon.outChunk o₁ o₂) := rfl

theorem combineChunk_ok {s : State} {i : Nat} (hi : i < 8) {lo hi' : Nat → Nat}
    (hl : VG.Proof.Curve448.AArch64.Neon.LaneIs s (2 * i) lo) (hh : VG.Proof.Curve448.AArch64.Neon.LaneIs s (2 * i + 1) hi') (hlo : ∀ e < 2, lo e < 2 ^ 63)
    (hhi : ∀ e < 2, hi' e < 2 ^ 28) :
    WP isa (.block (VG.Proof.Curve448.AArch64.Neon.combineChunk i)) s fun t =>
      VG.Proof.Curve448.AArch64.Neon.LaneIs t (16 + i) (fun e => lo e + 2 ^ 28 * hi' e) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ (∀ r : VReg, r ≠ V (16 + i) → t.v r = s.v r) := by
  have n1 : V (2 * i + 1) ≠ V (16 + i) := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n2 : V (2 * i) ≠ V (16 + i) := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  simp only [VG.Proof.Curve448.AArch64.Neon.combineChunk]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, WP.block_nil_iff.mpr ⟨fun e he => ?_,
    by simp only [RegUpd.mem_setV], by simp only [RegUpd.gpr_setV], by simp only [RegUpd.rd_setV],
    by simp only [RegUpd.wr_setV], fun r hr => ?_⟩⟩
  · rw [RegUpd.v_setV_self, VG.Proof.Curve448.AArch64.Neon.lane_map2 _ _ _ he, BitVec.toNat_add, RegUpd.v_setV_self, VG.Proof.Curve448.AArch64.Neon.lane_shl _ _ _ he,
      RegUpd.v_setV_of_ne _ _ n2, hl e he, hh e he]
    have := hlo e he; have := hhi e he
    rw [Nat.mod_eq_of_lt (by omega : hi' e * 2 ^ 28 < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    dsimp only
    omega
  · rw [RegUpd.v_setV_of_ne _ _ hr, RegUpd.v_setV_of_ne _ _ hr]

theorem combine_ok {s : State} (L : Nat → Nat → Nat) (hL : ∀ k < 16, VG.Proof.Curve448.AArch64.Neon.LaneIs s k (L k))
    (he : ∀ i < 8, ∀ e < 2, L (2 * i) e < 2 ^ 63) (ho : ∀ i < 8, ∀ e < 2, L (2 * i + 1) e < 2 ^ 28) :
    WP isa (.block ((List.range 8).flatMap VG.Proof.Curve448.AArch64.Neon.combineChunk)) s fun t =>
      (∀ i < 8, VG.Proof.Curve448.AArch64.Neon.LaneIs t (16 + i) (fun e => L (2 * i) e + 2 ^ 28 * L (2 * i + 1) e)) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r : VReg, (∀ i < 8, r ≠ V (16 + i)) → t.v r = s.v r) := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.Curve448.AArch64.Neon.LaneIs t (16 + i) (fun e => L (2 * i) e + 2 ^ 28 * L (2 * i + 1) e)) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r : VReg, (∀ i < n, r ≠ V (16 + i)) → t.v r = s.v r)
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨ti, tm, tg, tr, tw, tv⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (by omega), rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  have keep : ∀ k < 16, t.v (V k) = s.v (V k) := fun k hk =>
    tv _ fun i hi => VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.combineChunk_ok hn (fun e he' => by rw [keep _ (by omega)]; exact hL _ (by omega) e he')
    (fun e he' => by rw [keep _ (by omega)]; exact hL _ (by omega) e he') (he n hn) (ho n hn))
    fun u ⟨ua, um, ug, ur, uw, uv⟩ => ⟨fun i hi => ?_, um.trans tm, ug.trans tg, ur.trans tr, uw.trans tw,
      fun r hr => (uv r (hr n (by omega))).trans (tv r fun i hi => hr i (by omega))⟩
  rcases (show i < n ∨ i = n by omega) with h | rfl
  · intro e he'
    rw [uv _ (VG.Proof.Curve448.AArch64.Neon.V_ne (16 + i) (by omega) (16 + n) (by omega) (by omega))]
    exact ti i h e he'
  · exact ua

theorem m56_ok {s : State} (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1) :
    WP isa (.block VG.Proof.Curve448.AArch64.Neon.m56) s fun t =>
      (∀ e < 2, (vdword (t.v (V 31)) e).toNat = 2 ^ 56 - 1) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr = s.gpr ∧ (∀ r : VReg, r ≠ V 31 → t.v r = s.v r) := by
  have n : V 30 ≠ V 31 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  simp only [VG.Proof.Curve448.AArch64.Neon.m56]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, WP.block_nil_iff.mpr ⟨fun e he => ?_,
    by simp only [RegUpd.mem_setV], by simp only [RegUpd.rd_setV], by simp only [RegUpd.wr_setV],
    by simp only [RegUpd.gpr_setV], fun r hr => ?_⟩⟩
  · rw [RegUpd.v_setV_self, VG.Proof.Curve448.AArch64.Neon.lane_map2 _ _ _ he, BitVec.toNat_add, RegUpd.v_setV_of_ne _ _ n, RegUpd.v_setV_self,
      VG.Proof.Curve448.AArch64.Neon.lane_shl _ _ _ he, hM e he]
    decide
  · rw [RegUpd.v_setV_of_ne _ _ hr, RegUpd.v_setV_of_ne _ _ hr]

theorem carry56_ok {s : State} {i : Nat} (hi : i = 16 ∨ i = 20)
    (hM : ∀ e < 2, (vdword (s.v (V 31)) e).toNat = 2 ^ 56 - 1) {x y : Nat → Nat}
    (hx : VG.Proof.Curve448.AArch64.Neon.LaneIs s i x) (hy : VG.Proof.Curve448.AArch64.Neon.LaneIs s (i + 1) y) (hxy : ∀ e < 2, y e + x e / 2 ^ 56 < 2 ^ 64) :
    WP isa (.block (VG.Proof.Curve448.AArch64.Neon.carry56 i)) s fun t =>
      VG.Proof.Curve448.AArch64.Neon.LaneIs t i (fun e => x e % 2 ^ 56) ∧ VG.Proof.Curve448.AArch64.Neon.LaneIs t (i + 1) (fun e => y e + x e / 2 ^ 56) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, r ≠ V 28 → r ≠ V i → r ≠ V (i + 1) → t.v r = s.v r) := by
  have n1 : V 28 ≠ V i := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n2 : V 28 ≠ V (i + 1) := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n3 : V i ≠ V (i + 1) := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n4 : V 31 ≠ V 28 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n5 : V 31 ≠ V i := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n1' := n1.symm
  have n2' := n2.symm
  have n3' := n3.symm
  simp only [VG.Proof.Curve448.AArch64.Neon.carry56]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, WP.block_nil_iff.mpr ⟨fun e he => ?_, fun e he => ?_,
    by simp only [RegUpd.mem_setV], by simp only [RegUpd.gpr_setV], by simp only [RegUpd.rd_setV],
    by simp only [RegUpd.wr_setV], fun r h1 h2 h3 => ?_⟩⟩
  · rw [RegUpd.v_setV_of_ne _ _ n3, RegUpd.v_setV_self, VG.Proof.Curve448.AArch64.Neon.lane_and _ _ hM he, hx e he]
  · rw [RegUpd.v_setV_self, VG.Proof.Curve448.AArch64.Neon.lane_map2 _ _ _ he, BitVec.toNat_add, RegUpd.v_setV_of_ne _ _ n3',
      RegUpd.v_setV_of_ne _ _ n2', RegUpd.v_setV_of_ne _ _ n1, RegUpd.v_setV_self, VG.Proof.Curve448.AArch64.Neon.lane_ushr _ _ _ he, hx e he,
      hy e he]
    exact Nat.mod_eq_of_lt (hxy e he)
  · rw [RegUpd.v_setV_of_ne _ _ h3, RegUpd.v_setV_of_ne _ _ h2, RegUpd.v_setV_of_ne _ _ h1]

theorem outChunk_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o₁ o₂ k : Nat} (hk : k < 4)
    (h₁ : o₁ % 16 = 0) (h₁' : o₁ + 64 ≤ 8192) (h₂ : o₂ % 16 = 0) (h₂' : o₂ + 64 ≤ 8192)
    (h12 : o₁ + 64 ≤ o₂ ∨ o₂ + 64 ≤ o₁) :
    WP isa (.block (VG.Proof.Curve448.AArch64.Neon.outChunk o₁ o₂ k)) s fun t =>
      (∀ j < 2, VG.Proof.X448.AArch64.word t.mem base (o₁ + 8 * (2 * k + j)) = vdword (s.v (V (16 + (2 * k + j)))) 0) ∧
      (∀ j < 2, VG.Proof.X448.AArch64.word t.mem base (o₂ + 8 * (2 * k + j)) = vdword (s.v (V (16 + (2 * k + j)))) 1) ∧
      VG.Proof.X448.AArch64.Outside2 base (o₁ + 16 * k) 16 (o₂ + 16 * k) 16 s.mem t.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r : VReg, r ≠ V 8 → r ≠ V 9 → t.v r = s.v r) := by
  have n89 : V 8 ≠ V 9 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have n98 := n89.symm
  have a8 : V (16 + 2 * k) ≠ V 8 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have b8 : V (17 + 2 * k) ≠ V 8 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have a9 : V (16 + 2 * k) ≠ V 9 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  have b9 : V (17 + 2 * k) ≠ V 9 := VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)
  simp only [VG.Proof.Curve448.AArch64.Neon.outChunk]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_stq (base := base) ?g1 8 (by omega) (by omega), ?_⟩
  case g1 => scr
  vred
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Curve448.AArch64.Neon.exec_stq (base := base) ?g2 9 (by omega) (by omega), ?_⟩
  case g2 => scr
  refine WP.block_nil_iff.mpr ⟨fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, fun r h8 h9 => ?_⟩
  · simp only [VG.Proof.Curve448.AArch64.Neon.setMem_mem]
    rw [VG.Proof.X448.AArch64.Outside.word (VG.Proof.Curve448.AArch64.Neon.st_outside _ base _ (by omega)) (by omega) (by omega),
      show o₁ + 8 * (2 * k + j) = o₁ + 16 * k + 8 * j by omega, VG.Proof.Curve448.AArch64.Neon.word_st _ _ _ _ hj]
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · rw [trn1_0]; rfl
    · rw [trn1_1, show 17 + 2 * k = 16 + (2 * k + 1) by omega]
  · simp only [VG.Proof.Curve448.AArch64.Neon.setMem_mem, VG.Proof.Curve448.AArch64.Neon.setMem_v]
    rw [show o₂ + 8 * (2 * k + j) = o₂ + 16 * k + 8 * j by omega, VG.Proof.Curve448.AArch64.Neon.word_st _ _ _ _ hj, RegUpd.v_setV_self]
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · rw [trn2_0]; rfl
    · rw [trn2_1, show 17 + 2 * k = 16 + (2 * k + 1) by omega]
  · simp only [VG.Proof.Curve448.AArch64.Neon.setMem_mem]
    intro p hp hq
    rw [VG.Proof.Curve448.AArch64.Neon.st_outside _ base _ (by omega) p hq, VG.Proof.Curve448.AArch64.Neon.st_outside _ base _ (by omega) p hp]
  · simp only [VG.Proof.Curve448.AArch64.Neon.setMem_gpr, RegUpd.gpr_setV]
  · simp only [VG.Proof.Curve448.AArch64.Neon.setMem_rd, RegUpd.rd_setV]
  · simp only [VG.Proof.Curve448.AArch64.Neon.setMem_wr, RegUpd.wr_setV]
  · simp only [VG.Proof.Curve448.AArch64.Neon.setMem_v, RegUpd.v_setV_of_ne _ _ h9, RegUpd.v_setV_of_ne _ _ h8]

/-- The radix-2⁵⁶ limbs of the sixteen limbs `L`, before the last carries. -/
abbrev w56 (L : Nat → Nat) (i : Nat) : Nat := L (2 * i) + 2 ^ 28 * L (2 * i + 1)

/-- The results: limbs 0 and 4 carried into 1 and 5. -/
def out56 (L : Nat → Nat) (i : Nat) : Nat :=
  if i = 0 then VG.Proof.Curve448.AArch64.Neon.w56 L 0 % 2 ^ 56 else if i = 1 then VG.Proof.Curve448.AArch64.Neon.w56 L 1 + VG.Proof.Curve448.AArch64.Neon.w56 L 0 / 2 ^ 56
  else if i = 4 then VG.Proof.Curve448.AArch64.Neon.w56 L 4 % 2 ^ 56 else if i = 5 then VG.Proof.Curve448.AArch64.Neon.w56 L 5 + VG.Proof.Curve448.AArch64.Neon.w56 L 4 / 2 ^ 56 else VG.Proof.Curve448.AArch64.Neon.w56 L i

theorem finishN_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o₁ o₂ : Nat} (L : Nat → Nat → Nat)
    (hL : ∀ k < 16, VG.Proof.Curve448.AArch64.Neon.LaneIs s k (fun e => L e k))
    (he : ∀ e < 2, ∀ i < 8, L e (2 * i) < 2 ^ 40) (ho : ∀ e < 2, ∀ i < 8, L e (2 * i + 1) < 2 ^ 28)
    (h₁ : o₁ % 16 = 0) (h₁' : o₁ + 64 ≤ 8192) (h₂ : o₂ % 16 = 0) (h₂' : o₂ + 64 ≤ 8192)
    (h12 : o₁ + 64 ≤ o₂ ∨ o₂ + 64 ≤ o₁) (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1) :
    WP isa (.block (VG.Impl.Curve448.AArch64.Neon.finish o₁ o₂)) s fun t =>
      (∀ i < 8, limbs t.mem base o₁ i = VG.Proof.Curve448.AArch64.Neon.out56 (L 0) i) ∧ (∀ i < 8, limbs t.mem base o₂ i = VG.Proof.Curve448.AArch64.Neon.out56 (L 1) i) ∧
      VG.Proof.X448.AArch64.Outside2 base o₁ 64 o₂ 64 s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr = s.gpr := by
  rw [VG.Proof.Curve448.AArch64.Neon.finish_eq, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.combine_ok (fun k e => L e k) hL (fun i hi e he' => by have := he e he' i hi; omega)
    (fun i hi e he' => ho e he' i hi)) fun t ⟨tw, tm, tg, tr, twr, tv⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.m56_ok (fun e he' => by
    rw [tv _ (fun i _ => VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))]; exact hM e he')) fun u ⟨uM, um, ur, uw, ug, uv⟩ => ?_
  have hu : ∀ i < 8, VG.Proof.Curve448.AArch64.Neon.LaneIs u (16 + i) (fun e => VG.Proof.Curve448.AArch64.Neon.w56 (L e) i) := fun i hi e he' => by
    rw [uv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))]; exact tw i hi e he'
  rw [WP.block_append_iff]
  -- the last carries
  have b0 : ∀ e < 2, ∀ i < 8, VG.Proof.Curve448.AArch64.Neon.w56 (L e) i < 2 ^ 57 := fun e he' i hi => by
    have := he e he' i hi; have := ho e he' i hi; simp only [VG.Proof.Curve448.AArch64.Neon.w56]; omega
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.carry56_ok (i := 16) (Or.inl rfl) uM (hu 0 (by decide)) (hu 1 (by decide))
    (fun e he' => by have := b0 e he' 1 (by decide); have := b0 e he' 0 (by decide); omega))
    fun v ⟨va, vb, vm, vg, vr, vw, vv⟩ => ?_
  have vM : ∀ e < 2, (vdword (v.v (V 31)) e).toNat = 2 ^ 56 - 1 := fun e he' => by
    rw [vv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
      (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))]; exact uM e he'
  have v4 : VG.Proof.Curve448.AArch64.Neon.LaneIs v 20 (fun e => VG.Proof.Curve448.AArch64.Neon.w56 (L e) 4) := fun e he' => by
    rw [vv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
      (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))]; exact hu 4 (by decide) e he'
  have v5 : VG.Proof.Curve448.AArch64.Neon.LaneIs v 21 (fun e => VG.Proof.Curve448.AArch64.Neon.w56 (L e) 5) := fun e he' => by
    rw [vv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
      (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))]; exact hu 5 (by decide) e he'
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.carry56_ok (i := 20) (Or.inr rfl) vM v4 v5
    (fun e he' => by have := b0 e he' 5 (by decide); have := b0 e he' 4 (by decide); omega))
    fun w ⟨wa, wb, wm, wg, wr, ww, wv⟩ => ?_
  -- the results
  have wl : ∀ i < 8, VG.Proof.Curve448.AArch64.Neon.LaneIs w (16 + i) (fun e => VG.Proof.Curve448.AArch64.Neon.out56 (L e) i) := by
    intro i hi e he'
    rcases (show i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5 ∨ (i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 4 ∧ i ≠ 5) by omega)
      with rfl | rfl | rfl | rfl | ⟨i0, i1, i4, i5⟩
    · rw [wv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
        (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)), va e he']; simp [VG.Proof.Curve448.AArch64.Neon.out56]
    · rw [wv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
        (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)), vb e he']; simp [VG.Proof.Curve448.AArch64.Neon.out56]
    · rw [wa e he']; simp [VG.Proof.Curve448.AArch64.Neon.out56]
    · rw [wb e he']; simp [VG.Proof.Curve448.AArch64.Neon.out56]
    · rw [wv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
        (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)),
        vv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)) (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
        (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega)), hu i hi e he']
      simp [VG.Proof.Curve448.AArch64.Neon.out56, i0, i1, i4, i5]
  have gw : w.gpr = s.gpr := by rw [wg, vg, ug, tg]
  have hw : VG.Proof.X448.AArch64.Scr w base := VG.Proof.Curve448.AArch64.Neon.scr_of hs gw (by rw [ww, vw, uw, twr])
  let inv := fun n (x : State) =>
    (∀ i < 2 * n, (VG.Proof.X448.AArch64.word x.mem base (o₁ + 8 * i)).toNat = VG.Proof.Curve448.AArch64.Neon.out56 (L 0) i) ∧
    (∀ i < 2 * n, (VG.Proof.X448.AArch64.word x.mem base (o₂ + 8 * i)).toNat = VG.Proof.Curve448.AArch64.Neon.out56 (L 1) i) ∧
    VG.Proof.X448.AArch64.Outside2 base o₁ 64 o₂ 64 w.mem x.mem ∧ x.gpr = w.gpr ∧ x.rd = w.rd ∧ x.wr = w.wr ∧
    (∀ i < 8, x.v (V (16 + i)) = w.v (V (16 + i)))
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) inv (fun n x hn ⟨x1, x2, xo, xg, xr, xw, xv⟩ => ?_) 4
    (by decide) w ⟨fun _ h => absurd h (by omega), fun _ h => absurd h (by omega),
      VG.Proof.X448.AArch64.Outside2.refl _ _ _ _ _ _, rfl, rfl, rfl, fun _ _ => rfl⟩)
    fun x ⟨x1, x2, xo, xg, xr, xw, _⟩ => ⟨fun i hi => x1 i (by omega), fun i hi => x2 i (by omega), ?_,
      by rw [xr, wr, vr, ur, tr], by rw [xw, ww, vw, uw, twr], by rw [xg, gw]⟩
  · have hx : VG.Proof.X448.AArch64.Scr x base := ⟨by rw [xg]; exact hw.x3, by rw [xg]; exact hw.mask, xw ▸ hw.wr, hw.nowrap⟩
    refine WP.mono (VG.Proof.Curve448.AArch64.Neon.outChunk_ok hx hn h₁ h₁' h₂ h₂' h12) fun y ⟨y1, y2, yo, yg, yr, yw, yv⟩ =>
      ⟨fun i hi => ?_, fun i hi => ?_, xo.trans fun p hp hq => yo p (by omega) (by omega), yg.trans xg,
        yr.trans xr, yw.trans xw, fun i hi => (yv _ (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))
          (VG.Proof.Curve448.AArch64.Neon.V_ne _ (by omega) _ (by omega) (by omega))).trans (xv i hi)⟩
    · rcases (show i < 2 * n ∨ i = 2 * n ∨ i = 2 * n + 1 by omega) with h | rfl | rfl
      · rw [VG.Proof.X448.AArch64.Outside2.word (fun p hp hq => yo p hp hq) (by omega) (by omega) (by omega)]
        exact x1 i h
      · rw [show o₁ + 8 * (2 * n) = o₁ + 8 * (2 * n + 0) by omega, y1 0 (by decide), xv _ (by omega)]
        exact wl _ (by omega) 0 (by decide)
      · rw [y1 1 (by decide), xv _ (by omega)]
        exact wl _ (by omega) 0 (by decide)
    · rcases (show i < 2 * n ∨ i = 2 * n ∨ i = 2 * n + 1 by omega) with h | rfl | rfl
      · rw [VG.Proof.X448.AArch64.Outside2.word (fun p hp hq => yo p hp hq) (by omega) (by omega) (by omega)]
        exact x2 i h
      · rw [show o₂ + 8 * (2 * n) = o₂ + 8 * (2 * n + 0) by omega, y2 0 (by decide), xv _ (by omega)]
        exact wl _ (by omega) 1 (by decide)
      · rw [y2 1 (by decide), xv _ (by omega)]
        exact wl _ (by omega) 1 (by decide)
  · intro p hp hq
    rw [xo p hp hq, wm, vm, um, tm]

end VG.Proof.Curve448.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Neon.Value`. -/
section

/-!
# The value and bounds of `mul2`'s results

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG.Proof.X448.Wide (valN)
open VG.Proof.X448 (toFe toFe_mul)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

/-- The radix-2²⁸ limbs of radix-2⁵⁶ limbs `f`. -/
def l28 (f : Nat → Nat) (k : Nat) : Nat := if k % 2 = 0 then f (k / 2) % 2 ^ 28 else f (k / 2) / 2 ^ 28

theorem psum_l28 (f : Nat → Nat) : VG.Proof.Curve448.AArch64.Neon.psum (VG.Proof.Curve448.AArch64.Neon.l28 f) (2 ^ 28) 16 = (VG.Proof.X448.Wide.valN f 8 : Int) := by
  have h : ∀ i, (f i : Int) % 268435456 + (f i : Int) / 268435456 * 268435456 = f i := fun i =>
    Int.emod_add_ediv_mul _ _
  simp only [VG.Proof.Curve448.AArch64.Neon.psum, VG.Proof.Curve448.AArch64.Neon.l28, VG.Proof.X448.Wide.valN, VG.Proof.X448.Wide.radix, Nat.reduceMod, Nat.reduceDiv, ite_true, ite_false,
    one_ne_zero]
  push_cast
  linear_combination h 0 + (72057594037927936 : Int) ^ 1 * h 1 + (72057594037927936 : Int) ^ 2 * h 2 + (72057594037927936 : Int) ^ 3 * h 3 + (72057594037927936 : Int) ^ 4 * h 4 + (72057594037927936 : Int) ^ 5 * h 5 + (72057594037927936 : Int) ^ 6 * h 6 + (72057594037927936 : Int) ^ 7 * h 7

theorem val_out56 (L : Nat → Nat) : (VG.Proof.X448.Wide.valN (VG.Proof.Curve448.AArch64.Neon.out56 L) 8 : Int) = VG.Proof.Curve448.AArch64.Neon.psum L (2 ^ 28) 16 := by
  simp only [VG.Proof.X448.Wide.valN, VG.Proof.Curve448.AArch64.Neon.out56, VG.Proof.Curve448.AArch64.Neon.psum, VG.Proof.X448.Wide.radix, VG.Proof.Curve448.AArch64.Neon.w56]
  simp only [show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide,
    show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide, show (4 : Nat) ≠ 0 by decide,
    show (4 : Nat) ≠ 1 by decide, show (5 : Nat) ≠ 0 by decide, show (5 : Nat) ≠ 1 by decide,
    show (5 : Nat) ≠ 4 by decide, show (6 : Nat) ≠ 0 by decide, show (6 : Nat) ≠ 1 by decide,
    show (6 : Nat) ≠ 4 by decide, show (6 : Nat) ≠ 5 by decide, show (7 : Nat) ≠ 0 by decide,
    show (7 : Nat) ≠ 1 by decide, show (7 : Nat) ≠ 4 by decide, show (7 : Nat) ≠ 5 by decide, ite_true, ite_false]
  push_cast
  have h0 := Int.emod_add_ediv_mul ((L 0 : Int) + 268435456 * L 1) 72057594037927936
  have h4 := Int.emod_add_ediv_mul ((L 8 : Int) + 268435456 * L 9) 72057594037927936
  linear_combination h0 + (72057594037927936 : Int) ^ 4 * h4

theorem sum_l28 (f : Nat → Nat) : (VG.Proof.Curve448.AArch64.Neon.l28 f 0 : Int) * (2 ^ 28 : Int) ^ 0 + (VG.Proof.Curve448.AArch64.Neon.l28 f 1 : Int) * (2 ^ 28 : Int) ^ 1 + (VG.Proof.Curve448.AArch64.Neon.l28 f 2 : Int) * (2 ^ 28 : Int) ^ 2 + (VG.Proof.Curve448.AArch64.Neon.l28 f 3 : Int) * (2 ^ 28 : Int) ^ 3 + (VG.Proof.Curve448.AArch64.Neon.l28 f 4 : Int) * (2 ^ 28 : Int) ^ 4 + (VG.Proof.Curve448.AArch64.Neon.l28 f 5 : Int) * (2 ^ 28 : Int) ^ 5 + (VG.Proof.Curve448.AArch64.Neon.l28 f 6 : Int) * (2 ^ 28 : Int) ^ 6 + (VG.Proof.Curve448.AArch64.Neon.l28 f 7 : Int) * (2 ^ 28 : Int) ^ 7 + (VG.Proof.Curve448.AArch64.Neon.l28 f 8 : Int) * (2 ^ 28 : Int) ^ 8 + (VG.Proof.Curve448.AArch64.Neon.l28 f 9 : Int) * (2 ^ 28 : Int) ^ 9 + (VG.Proof.Curve448.AArch64.Neon.l28 f 10 : Int) * (2 ^ 28 : Int) ^ 10 + (VG.Proof.Curve448.AArch64.Neon.l28 f 11 : Int) * (2 ^ 28 : Int) ^ 11 + (VG.Proof.Curve448.AArch64.Neon.l28 f 12 : Int) * (2 ^ 28 : Int) ^ 12 + (VG.Proof.Curve448.AArch64.Neon.l28 f 13 : Int) * (2 ^ 28 : Int) ^ 13 + (VG.Proof.Curve448.AArch64.Neon.l28 f 14 : Int) * (2 ^ 28 : Int) ^ 14 + (VG.Proof.Curve448.AArch64.Neon.l28 f 15 : Int) * (2 ^ 28 : Int) ^ 15 = (VG.Proof.X448.Wide.valN f 8 : Int) := by
  have := VG.Proof.Curve448.AArch64.Neon.psum_l28 f
  simp only [VG.Proof.Curve448.AArch64.Neon.psum, Int.zero_add] at this
  exact this

theorem kara_ex (X : Int) (a b : Nat → Nat) :
    ∃ W : Int, ((a 0 : Int) * X ^ 0 + (a 1 : Int) * X ^ 1 + (a 2 : Int) * X ^ 2 + (a 3 : Int) * X ^ 3 + (a 4 : Int) * X ^ 4 + (a 5 : Int) * X ^ 5 + (a 6 : Int) * X ^ 6 + (a 7 : Int) * X ^ 7 + (a 8 : Int) * X ^ 8 + (a 9 : Int) * X ^ 9 + (a 10 : Int) * X ^ 10 + (a 11 : Int) * X ^ 11 + (a 12 : Int) * X ^ 12 + (a 13 : Int) * X ^ 13 + (a 14 : Int) * X ^ 14 + (a 15 : Int) * X ^ 15) * ((b 0 : Int) * X ^ 0 + (b 1 : Int) * X ^ 1 + (b 2 : Int) * X ^ 2 + (b 3 : Int) * X ^ 3 + (b 4 : Int) * X ^ 4 + (b 5 : Int) * X ^ 5 + (b 6 : Int) * X ^ 6 + (b 7 : Int) * X ^ 7 + (b 8 : Int) * X ^ 8 + (b 9 : Int) * X ^ 9 + (b 10 : Int) * X ^ 10 + (b 11 : Int) * X ^ 11 + (b 12 : Int) * X ^ 12 + (b 13 : Int) * X ^ 13 + (b 14 : Int) * X ^ 14 + (b 15 : Int) * X ^ 15) - (VG.Proof.Curve448.AArch64.Neon.kara a b 0 * X ^ 0 + VG.Proof.Curve448.AArch64.Neon.kara a b 1 * X ^ 1 + VG.Proof.Curve448.AArch64.Neon.kara a b 2 * X ^ 2 + VG.Proof.Curve448.AArch64.Neon.kara a b 3 * X ^ 3 + VG.Proof.Curve448.AArch64.Neon.kara a b 4 * X ^ 4 + VG.Proof.Curve448.AArch64.Neon.kara a b 5 * X ^ 5 + VG.Proof.Curve448.AArch64.Neon.kara a b 6 * X ^ 6 + VG.Proof.Curve448.AArch64.Neon.kara a b 7 * X ^ 7 + VG.Proof.Curve448.AArch64.Neon.kara a b 8 * X ^ 8 + VG.Proof.Curve448.AArch64.Neon.kara a b 9 * X ^ 9 + VG.Proof.Curve448.AArch64.Neon.kara a b 10 * X ^ 10 + VG.Proof.Curve448.AArch64.Neon.kara a b 11 * X ^ 11 + VG.Proof.Curve448.AArch64.Neon.kara a b 12 * X ^ 12 + VG.Proof.Curve448.AArch64.Neon.kara a b 13 * X ^ 13 + VG.Proof.Curve448.AArch64.Neon.kara a b 14 * X ^ 14 + VG.Proof.Curve448.AArch64.Neon.kara a b 15 * X ^ 15) = (X ^ 16 - X ^ 8 - 1) * W := ⟨_, VG.Proof.Curve448.AArch64.Neon.kara_sum X a b⟩

/-- The value of a result of `mul2`: the product of the operands, modulo `p`. -/
theorem mul2_val (fa fb r : Nat → Nat) (hr : ∀ k < 16, (r k : Int) = VG.Proof.Curve448.AArch64.Neon.kara (VG.Proof.Curve448.AArch64.Neon.l28 fa) (VG.Proof.Curve448.AArch64.Neon.l28 fb) k) :
    VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (VG.Proof.Curve448.AArch64.Neon.out56 (VG.Proof.Curve448.AArch64.Neon.limbs28 r)) 8) = VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN fa 8) * VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN fb 8) := by
  apply VG.Proof.X448.toFe_mul
  have hP : ((VG.Spec.X448.P : Nat) : Int) = (2 ^ 28) ^ 16 - (2 ^ 28) ^ 8 - 1 := by
    have h := VG.Proof.X448.full_eq
    simp only [VG.Proof.X448.full, VG.Proof.X448.half, VG.Proof.X448.radix] at h
    have h' : (((2 ^ 28) ^ 16 : Nat) : Int) = (VG.Spec.X448.P : Nat) + (((2 ^ 28) ^ 8 : Nat) : Int) + 1 := by
      rw [h]; push_cast; ring
    push_cast at h'
    linarith
  obtain ⟨W, hW⟩ := VG.Proof.Curve448.AArch64.Neon.kara_ex (2 ^ 28) (VG.Proof.Curve448.AArch64.Neon.l28 fa) (VG.Proof.Curve448.AArch64.Neon.l28 fb)
  rw [VG.Proof.Curve448.AArch64.Neon.sum_l28 fa, VG.Proof.Curve448.AArch64.Neon.sum_l28 fb] at hW
  have e1 := VG.Proof.Curve448.AArch64.Neon.val_out56 (VG.Proof.Curve448.AArch64.Neon.limbs28 r)
  have e2 := VG.Proof.Curve448.AArch64.Neon.limbs28_val r
  simp only [VG.Proof.Curve448.AArch64.Neon.psum] at e1 e2
  rw [hr 0 (by decide), hr 1 (by decide), hr 2 (by decide), hr 3 (by decide), hr 4 (by decide), hr 5 (by decide), hr 6 (by decide), hr 7 (by decide), hr 8 (by decide), hr 9 (by decide), hr 10 (by decide), hr 11 (by decide), hr 12 (by decide), hr 13 (by decide), hr 14 (by decide), hr 15 (by decide)] at e2
  generalize (2 ^ 28 : Int) = X at *
  have key : (VG.Proof.X448.Wide.valN (VG.Proof.Curve448.AArch64.Neon.out56 (VG.Proof.Curve448.AArch64.Neon.limbs28 r)) 8 : Int) =
      (VG.Proof.X448.Wide.valN fa 8 : Int) * (VG.Proof.X448.Wide.valN fb 8 : Int) + (X ^ 16 - X ^ 8 - 1) * (-W - VG.Proof.Curve448.AArch64.Neon.C15 r) := by
    linear_combination e1 + e2 - hW
  have : ((VG.Proof.X448.Wide.valN (VG.Proof.Curve448.AArch64.Neon.out56 (VG.Proof.Curve448.AArch64.Neon.limbs28 r)) 8 : Nat) : Int) % (VG.Spec.X448.P : Nat) =
      ((VG.Proof.X448.Wide.valN fa 8 * VG.Proof.X448.Wide.valN fb 8 : Nat) : Int) % (VG.Spec.X448.P : Nat) := by
    rw [key, hP, Int.add_mul_emod_self_left, Nat.cast_mul]
  rw [← Int.natCast_emod, ← Int.natCast_emod] at this
  exact Int.ofNat_inj.mp this

theorem carries_lt {r : Nat → Nat} (hr : ∀ k < 16, r k < 2 ^ 64 - 2 ^ 40) :
    VG.Proof.Curve448.AArch64.Neon.cval r 0 7 / 2 ^ 28 < 2 ^ 36 ∧ VG.Proof.Curve448.AArch64.Neon.cval r 8 7 / 2 ^ 28 < 2 ^ 36 :=
  ⟨VG.Proof.Curve448.AArch64.Neon.cin_le (b := 0) (r := r) (fun k hk => hr (0 + k) (by omega)) 8 (by omega),
    VG.Proof.Curve448.AArch64.Neon.cin_le (b := 8) (r := r) (fun k hk => hr (8 + k) (by omega)) 8 (by omega)⟩

theorem limbs28_lt {r : Nat → Nat} (hr : ∀ k < 16, r k < 2 ^ 64 - 2 ^ 40) {k : Nat} (hk : k < 16) :
    VG.Proof.Curve448.AArch64.Neon.limbs28 r k < 2 ^ 28 + (if k = 0 then 2 ^ 36 else 0) + (if k = 8 then 2 ^ 37 else 0) := by
  obtain ⟨c7, c15⟩ := VG.Proof.Curve448.AArch64.Neon.carries_lt hr
  have c7' : VG.Proof.Curve448.AArch64.Neon.C7 r < 2 ^ 36 := c7
  have c15' : VG.Proof.Curve448.AArch64.Neon.C15 r < 2 ^ 36 := c15
  unfold VG.Proof.Curve448.AArch64.Neon.limbs28
  split
  · have := Nat.mod_lt (VG.Proof.Curve448.AArch64.Neon.cval r 0 k) (show 2 ^ 28 > 0 by decide)
    split <;> split <;> omega
  · have := Nat.mod_lt (VG.Proof.Curve448.AArch64.Neon.cval r 8 (k - 8)) (show 2 ^ 28 > 0 by decide)
    split <;> split <;> omega

theorem limbs28_bound {r : Nat → Nat} (hr : ∀ k < 16, r k < 2 ^ 64 - 2 ^ 40) :
    (∀ i < 8, VG.Proof.Curve448.AArch64.Neon.limbs28 r (2 * i + 1) < 2 ^ 28) ∧ (∀ i < 8, VG.Proof.Curve448.AArch64.Neon.limbs28 r (2 * i) < 2 ^ 40) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := VG.Proof.Curve448.AArch64.Neon.limbs28_lt hr (k := 2 * i + 1) (by omega)
    rw [ite_eq_right (by omega), ite_eq_right (by omega)] at this; omega
  · have := VG.Proof.Curve448.AArch64.Neon.limbs28_lt hr (k := 2 * i) (by omega)
    split at this <;> split at this <;> omega

theorem out56_bound {r : Nat → Nat} (hr : ∀ k < 16, r k < 2 ^ 64 - 2 ^ 40) : ∀ i < 8, VG.Proof.Curve448.AArch64.Neon.out56 (VG.Proof.Curve448.AArch64.Neon.limbs28 r) i < Mb := by
  have l : ∀ k < 16, VG.Proof.Curve448.AArch64.Neon.limbs28 r k < 2 ^ 28 + (if k = 0 then 2 ^ 36 else 0) + (if k = 8 then 2 ^ 37 else 0) :=
    fun k hk => VG.Proof.Curve448.AArch64.Neon.limbs28_lt hr hk
  have l0 := l 0 (by decide); have l1 := l 1 (by decide); have l2 := l 2 (by decide); have l3 := l 3 (by decide)
  have l4 := l 4 (by decide); have l5 := l 5 (by decide); have l6 := l 6 (by decide); have l7 := l 7 (by decide)
  have l8 := l 8 (by decide); have l9 := l 9 (by decide); have l10 := l 10 (by decide)
  have l11 := l 11 (by decide); have l12 := l 12 (by decide); have l13 := l 13 (by decide)
  have l14 := l 14 (by decide); have l15 := l 15 (by decide)
  simp at l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15
  have d0 : (VG.Proof.Curve448.AArch64.Neon.limbs28 r 0 + 2 ^ 28 * VG.Proof.Curve448.AArch64.Neon.limbs28 r 1) / 2 ^ 56 < 2 := Nat.div_lt_of_lt_mul (by omega)
  have d4 : (VG.Proof.Curve448.AArch64.Neon.limbs28 r 8 + 2 ^ 28 * VG.Proof.Curve448.AArch64.Neon.limbs28 r 9) / 2 ^ 56 < 2 := Nat.div_lt_of_lt_mul (by omega)
  intro i hi
  simp only [Mb, VG.Proof.Curve448.AArch64.Neon.out56, VG.Proof.Curve448.AArch64.Neon.w56]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [ite_true, ite_false, Nat.mul_zero,
      Nat.zero_add, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd, show (1 : Nat) ≠ 0 by decide,
      show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 0 by decide,
      show (3 : Nat) ≠ 1 by decide, show (2 : Nat) ≠ 4 by decide, show (2 : Nat) ≠ 5 by decide,
      show (3 : Nat) ≠ 4 by decide, show (3 : Nat) ≠ 5 by decide, show (4 : Nat) ≠ 0 by decide, show (4 : Nat) ≠ 1 by decide,
      show (5 : Nat) ≠ 0 by decide, show (5 : Nat) ≠ 1 by decide, show (5 : Nat) ≠ 4 by decide,
      show (6 : Nat) ≠ 0 by decide, show (6 : Nat) ≠ 1 by decide, show (6 : Nat) ≠ 4 by decide,
      show (6 : Nat) ≠ 5 by decide, show (7 : Nat) ≠ 0 by decide, show (7 : Nat) ≠ 1 by decide,
      show (7 : Nat) ≠ 4 by decide, show (7 : Nat) ≠ 5 by decide] <;>
    first
    | exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
    | (simp only [Nat.reducePow] at d0 d4 ⊢; omega)

end VG.Proof.Curve448.AArch64.Neon

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Neon.Mul2`. -/
section

/-!
# Two field multiplications in AdvSIMD

Untrusted: everything here is checked by Lean. `mul2 o₁ a₁ b₁ o₂ a₂ b₂`
writes products of `[a₁]` and `[b₁]`, and of `[a₂]` and `[b₂]`, to `o₁` and
`o₂`, with limbs below `Mb`, for operand limbs below `Ib`.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon
open VG.Proof.X448.AArch64 (Scr off ofs Outside Outside2 word limbs)
open VG.Proof.X448.Wide (valN valN_congr)
open VG.Proof.X448 (toFe)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

/-- The two elements' operands, as functions of the element. -/
abbrev pick (f₁ f₂ : Nat → Nat) (e : Nat) : Nat → Nat := if e = 0 then f₁ else f₂

theorem split_l28 (f₁ f₂ : Nat → Nat) (i c : Nat) (hc : c < 4) :
    VG.Proof.Curve448.AArch64.Neon.split f₁ f₂ i c = VG.Proof.Curve448.AArch64.Neon.l28 (VG.Proof.Curve448.AArch64.Neon.pick f₁ f₂ (c % 2)) (2 * i + c / 2) := by
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp [VG.Proof.Curve448.AArch64.Neon.split, VG.Proof.Curve448.AArch64.Neon.l28, VG.Proof.Curve448.AArch64.Neon.pick, show (2 * i + 1) % 2 = 1 by omega, show (2 * i + 1) / 2 = i by omega]

theorem l28_lt {f : Nat → Nat} (hf : ∀ i < 8, f i < Ib) {k : Nat} (hk : k < 16) : VG.Proof.Curve448.AArch64.Neon.l28 f k ≤ VG.Proof.Curve448.AArch64.Neon.lmax k := by
  unfold VG.Proof.Curve448.AArch64.Neon.l28 VG.Proof.Curve448.AArch64.Neon.lmax
  split
  · have := Nat.mod_lt (f (k / 2)) (show 2 ^ 28 > 0 by decide); omega
  · have := hf (k / 2) (by omega)
    simp only [Ib] at this
    rw [Nat.div_le_iff_le_mul_add_pred (by decide)]
    omega

/-- The preparation: constants, the radix-2²⁸ vectors, their sums and the shifted copies. -/
def prep (a₁ b₁ a₂ b₂ : Nat) : List Instr :=
  VG.Impl.Curve448.AArch64.Neon.consts ++ convert a₁ a₂ NA 0 1 2 3 ++ convert b₁ b₂ NB 4 5 6 7 ++ sums ++ shifted

theorem lmax_le (k : Nat) : VG.Proof.Curve448.AArch64.Neon.lmax k ≤ 3 * 2 ^ 28 := by unfold VG.Proof.Curve448.AArch64.Neon.lmax; split <;> omega

/-- The words of the operands after the preparation, as `HalfMem` wants them. -/
theorem halfMem_of {m : Mem} {base : Addr} {LA LB : Nat → Nat → Nat}
    (hla : ∀ e < 2, ∀ k < 16, LA e k ≤ VG.Proof.Curve448.AArch64.Neon.lmax k) (hlb : ∀ e < 2, ∀ k < 16, LB e k ≤ VG.Proof.Curve448.AArch64.Neon.lmax k)
    (hA : ∀ i < 8, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw m base (NA + 16 * i + 4 * c) = LA (c % 2) (2 * i + c / 2))
    (hB : ∀ i < 8, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw m base (NB + 16 * i + 4 * c) = LB (c % 2) (2 * i + c / 2))
    (hAS : ∀ i < 4, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw m base (NAS + 16 * i + 4 * c) =
      (LA (c % 2) (2 * i + c / 2) + LA (c % 2) (8 + (2 * i + c / 2))) % 2 ^ 32)
    (hBS : ∀ i < 4, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw m base (NBS + 16 * i + 4 * c) =
      (LB (c % 2) (2 * i + c / 2) + LB (c % 2) (8 + (2 * i + c / 2))) % 2 ^ 32)
    (hSh : ∀ h < 3, ∀ j < 5, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw m base (NBP + 80 * h + 16 * j + 4 * c) =
      if c < 2 then (if j = 0 then 0 else VG.Proof.Curve448.AArch64.Neon.hl (LB (c % 2)) h (2 * j - 1)) else (if j = 4 then 0 else VG.Proof.Curve448.AArch64.Neon.hl (LB (c % 2)) h (2 * j)))
    {h : Nat} (hh : h < 3) :
    VG.Proof.Curve448.AArch64.Neon.HalfMem m base h (fun e => VG.Proof.Curve448.AArch64.Neon.hl (LA e) h) (fun e => VG.Proof.Curve448.AArch64.Neon.hl (LB e) h) := by
  have hNA : NA = 4096 := rfl
  have hNB : NB = 4224 := rfl
  have hNAS : NAS = 4352 := rfl
  have hNBS : NBS = 4416 := rfl
  refine ⟨fun i hi c hc => ?_, fun j hj c hc => ?_, fun j hj c hc => hSh h hh j hj c hc⟩
  · rcases (show h = 0 ∨ h = 1 ∨ h = 2 by omega) with rfl | rfl | rfl
    · simp only [aHalf, VG.Proof.Curve448.AArch64.Neon.hl]; exact hA i (by omega) c hc
    · simp only [aHalf, VG.Proof.Curve448.AArch64.Neon.hl]
      rw [show NA + 64 + 16 * i + 4 * c = NA + 16 * (i + 4) + 4 * c by omega, hA (i + 4) (by omega) c hc]
      congr 1; omega
    · simp only [aHalf, VG.Proof.Curve448.AArch64.Neon.hl]
      rw [hAS i hi c hc, Nat.mod_eq_of_lt]
      have := hla (c % 2) (by omega) (2 * i + c / 2) (by omega)
      have := hla (c % 2) (by omega) (8 + (2 * i + c / 2)) (by omega)
      have := VG.Proof.Curve448.AArch64.Neon.lmax_le (2 * i + c / 2); have := VG.Proof.Curve448.AArch64.Neon.lmax_le (8 + (2 * i + c / 2))
      omega
  · rcases (show h = 0 ∨ h = 1 ∨ h = 2 by omega) with rfl | rfl | rfl
    · simp only [bHalf, VG.Proof.Curve448.AArch64.Neon.hl]; exact hB j (by omega) c hc
    · simp only [bHalf, VG.Proof.Curve448.AArch64.Neon.hl]
      rw [show NB + 64 + 16 * j + 4 * c = NB + 16 * (j + 4) + 4 * c by omega, hB (j + 4) (by omega) c hc]
      congr 1; omega
    · simp only [bHalf, VG.Proof.Curve448.AArch64.Neon.hl]
      rw [hBS j hj c hc, Nat.mod_eq_of_lt]
      have := hlb (c % 2) (by omega) (2 * j + c / 2) (by omega)
      have := hlb (c % 2) (by omega) (8 + (2 * j + c / 2)) (by omega)
      have := VG.Proof.Curve448.AArch64.Neon.lmax_le (2 * j + c / 2); have := VG.Proof.Curve448.AArch64.Neon.lmax_le (8 + (2 * j + c / 2))
      omega

theorem halfB_of {m : Mem} {base : Addr} {LB : Nat → Nat → Nat} (hlb : ∀ e < 2, ∀ k < 16, LB e k ≤ VG.Proof.Curve448.AArch64.Neon.lmax k)
    (hB : ∀ i < 8, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw m base (NB + 16 * i + 4 * c) = LB (c % 2) (2 * i + c / 2))
    (hBS : ∀ i < 4, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw m base (NBS + 16 * i + 4 * c) =
      (LB (c % 2) (2 * i + c / 2) + LB (c % 2) (8 + (2 * i + c / 2))) % 2 ^ 32) :
    ∀ h < 3, ∀ j < 4, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw m base (bHalf h + 16 * j + 4 * c) = VG.Proof.Curve448.AArch64.Neon.hl (LB (c % 2)) h (2 * j + c / 2) := by
  have hNB : NB = 4224 := rfl
  have hNBS : NBS = 4416 := rfl
  intro h hh j hj c hc
  rcases (show h = 0 ∨ h = 1 ∨ h = 2 by omega) with rfl | rfl | rfl
  · simp only [bHalf, VG.Proof.Curve448.AArch64.Neon.hl]; exact hB j (by omega) c hc
  · simp only [bHalf, VG.Proof.Curve448.AArch64.Neon.hl]
    rw [show NB + 64 + 16 * j + 4 * c = NB + 16 * (j + 4) + 4 * c by omega, hB (j + 4) (by omega) c hc]
    congr 1; omega
  · simp only [bHalf, VG.Proof.Curve448.AArch64.Neon.hl]
    rw [hBS j hj c hc, Nat.mod_eq_of_lt]
    have := hlb (c % 2) (by omega) (2 * j + c / 2) (by omega)
    have := hlb (c % 2) (by omega) (8 + (2 * j + c / 2)) (by omega)
    have := VG.Proof.Curve448.AArch64.Neon.lmax_le (2 * j + c / 2); have := VG.Proof.Curve448.AArch64.Neon.lmax_le (8 + (2 * j + c / 2))
    omega

theorem sh_of {m : Mem} {base : Addr} {LB : Nat → Nat → Nat}
    (hb : ∀ h < 3, ∀ j < 4, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw m base (bHalf h + 16 * j + 4 * c) = VG.Proof.Curve448.AArch64.Neon.hl (LB (c % 2)) h (2 * j + c / 2)) :
    ∀ h < 3, ∀ j < 5, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.shw (VG.Proof.Curve448.AArch64.Neon.nw m base) h j c =
      if c < 2 then (if j = 0 then 0 else VG.Proof.Curve448.AArch64.Neon.hl (LB (c % 2)) h (2 * j - 1)) else (if j = 4 then 0 else VG.Proof.Curve448.AArch64.Neon.hl (LB (c % 2)) h (2 * j)) := by
  intro h hh j hj c hc
  unfold VG.Proof.Curve448.AArch64.Neon.shw
  split
  · split
    · rfl
    · rw [hb h hh (j - 1) (by omega) (c + 2) (by omega), show (c + 2) % 2 = c % 2 by omega]
      congr 1; omega
  · split
    · rfl
    · rw [hb h hh j (by omega) (c - 2) (by omega), show (c - 2) % 2 = c % 2 by omega]
      congr 1; omega

/-- Element `e`'s radix-2²⁸ limbs of `[x₁]` (`e = 0`) or `[x₂]`. -/
abbrev L28 (m : Mem) (base : Addr) (x₁ x₂ : Nat) (e : Nat) : Nat → Nat :=
  VG.Proof.Curve448.AArch64.Neon.l28 (VG.Proof.Curve448.AArch64.Neon.pick (limbs m base x₁) (limbs m base x₂) e)

theorem L28_le {m : Mem} {base : Addr} {x₁ x₂ : Nat} (h₁ : ∀ i < 8, limbs m base x₁ i < Ib)
    (h₂ : ∀ i < 8, limbs m base x₂ i < Ib) : ∀ e < 2, ∀ k < 16, VG.Proof.Curve448.AArch64.Neon.L28 m base x₁ x₂ e k ≤ VG.Proof.Curve448.AArch64.Neon.lmax k := by
  intro e he k hk
  simp only [VG.Proof.Curve448.AArch64.Neon.L28, VG.Proof.Curve448.AArch64.Neon.pick]
  split
  · exact VG.Proof.Curve448.AArch64.Neon.l28_lt h₁ hk
  · exact VG.Proof.Curve448.AArch64.Neon.l28_lt h₂ hk

theorem L28_congr {m m' : Mem} {base : Addr} {x₁ x₂ : Nat} (h₁ : ∀ i < 8, limbs m' base x₁ i = limbs m base x₁ i)
    (h₂ : ∀ i < 8, limbs m' base x₂ i = limbs m base x₂ i) {e k : Nat} (hk : k < 16) :
    VG.Proof.Curve448.AArch64.Neon.L28 m' base x₁ x₂ e k = VG.Proof.Curve448.AArch64.Neon.L28 m base x₁ x₂ e k := by
  simp only [VG.Proof.Curve448.AArch64.Neon.L28, VG.Proof.Curve448.AArch64.Neon.l28, VG.Proof.Curve448.AArch64.Neon.pick]
  split <;> split <;> simp only [h₁ (k / 2) (by omega), h₂ (k / 2) (by omega)]

theorem prep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {a₁ b₁ a₂ b₂ : Nat}
    (ha₁ : a₁ % 16 = 0 ∧ a₁ + 64 ≤ NA) (hb₁ : b₁ % 16 = 0 ∧ b₁ + 64 ≤ NA)
    (ha₂ : a₂ % 16 = 0 ∧ a₂ + 64 ≤ NA) (hb₂ : b₂ % 16 = 0 ∧ b₂ + 64 ≤ NA)
    (la₁ : ∀ i < 8, limbs s.mem base a₁ i < Ib) (lb₁ : ∀ i < 8, limbs s.mem base b₁ i < Ib)
    (la₂ : ∀ i < 8, limbs s.mem base a₂ i < Ib) (lb₂ : ∀ i < 8, limbs s.mem base b₂ i < Ib) :
    WP isa (.block (VG.Proof.Curve448.AArch64.Neon.prep a₁ b₁ a₂ b₂)) s fun t =>
      (∀ h < 3, VG.Proof.Curve448.AArch64.Neon.HalfMem t.mem base h (fun e => VG.Proof.Curve448.AArch64.Neon.hl (VG.Proof.Curve448.AArch64.Neon.L28 s.mem base a₁ a₂ e) h) (fun e => VG.Proof.Curve448.AArch64.Neon.hl (VG.Proof.Curve448.AArch64.Neon.L28 s.mem base b₁ b₂ e) h)) ∧
      (∀ e < 2, (vdword (t.v (V 30)) e).toNat = 2 ^ 28 - 1) ∧ t.v (V 31) = 0 ∧
      VG.Proof.X448.AArch64.Outside base NA 640 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hNA : NA = 4096 := rfl
  have hNB : NB = 4224 := rfl
  have hNAS : NAS = 4352 := rfl
  have hNBS : NBS = 4416 := rfl
  have hNBP : NBP = 4480 := rfl
  have nn : ∀ a < 32, ∀ b < 32, a ≠ b → V a ≠ V b := VG.Proof.Curve448.AArch64.Neon.V_ne
  have lt60 : ∀ x ∈ [a₁, b₁, a₂, b₂], ∀ i < 8, limbs s.mem base x i < Ib → limbs s.mem base x i < 2 ^ 60 :=
    fun _ _ _ _ h => by simp only [Ib] at h; omega
  simp only [VG.Proof.Curve448.AArch64.Neon.prep, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.consts_ok hs) fun t1 ⟨hM, h31, m1, rd1, wr1, g1, v1, s1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.convert_ok s1 ha₁.1 (by omega) ha₂.1 (by omega) (by decide) (by decide) (Or.inl (by omega))
    (Or.inl (by omega)) hM (nn 0 (by decide) 1 (by decide) (by decide)) (nn 0 (by decide) 2 (by decide) (by decide))
    (nn 0 (by decide) 3 (by decide) (by decide)) (nn 1 (by decide) 2 (by decide) (by decide))
    (nn 1 (by decide) 3 (by decide) (by decide)) (nn 2 (by decide) 3 (by decide) (by decide))
    (fun r hr => nn r (by simp at hr; omega) 30 (by decide) (by simp at hr; omega))
    (fun i hi => by rw [m1]; exact lt60 a₁ (by simp) i hi (la₁ i hi))
    (fun i hi => by rw [m1]; exact lt60 a₂ (by simp) i hi (la₂ i hi)))
    fun t2 ⟨A2, o2, g2, r2, w2, v2⟩ => ?_
  have s2 : VG.Proof.X448.AArch64.Scr t2 base := VG.Proof.Curve448.AArch64.Neon.scr_of s1 g2 w2
  have M2 : ∀ e < 2, (vdword (t2.v (V 30)) e).toNat = 2 ^ 28 - 1 := fun e he => by
    rw [v2 _ (by decide)]; exact hM e he
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.convert_ok s2 hb₁.1 (by omega) hb₂.1 (by omega) (by decide) (by decide) (Or.inl (by omega))
    (Or.inl (by omega)) M2 (nn 4 (by decide) 5 (by decide) (by decide)) (nn 4 (by decide) 6 (by decide) (by decide))
    (nn 4 (by decide) 7 (by decide) (by decide)) (nn 5 (by decide) 6 (by decide) (by decide))
    (nn 5 (by decide) 7 (by decide) (by decide)) (nn 6 (by decide) 7 (by decide) (by decide))
    (fun r hr => nn r (by simp at hr; omega) 30 (by decide) (by simp at hr; omega))
    (fun i hi => by rw [VG.Proof.Curve448.AArch64.Neon.limbs_outside o2 (Or.inl (by omega)) (by omega) hi, m1]
                    exact lt60 b₁ (by simp) i hi (lb₁ i hi))
    (fun i hi => by rw [VG.Proof.Curve448.AArch64.Neon.limbs_outside o2 (Or.inl (by omega)) (by omega) hi, m1]
                    exact lt60 b₂ (by simp) i hi (lb₂ i hi)))
    fun t3 ⟨B3, o3, g3, r3, w3, v3⟩ => ?_
  have s3 : VG.Proof.X448.AArch64.Scr t3 base := VG.Proof.Curve448.AArch64.Neon.scr_of s2 g3 w3
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.sums_ok s3) fun t4 ⟨AS4, BS4, o4, g4, r4, w4, v4⟩ => ?_
  have s4 : VG.Proof.X448.AArch64.Scr t4 base := VG.Proof.Curve448.AArch64.Neon.scr_of s3 g4 w4
  have h31' : t4.v (V 31) = 0 := by rw [v4 _ (by decide), v3 _ (by decide), v2 _ (by decide)]; exact h31
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.shifted_ok s4 h31') fun t5 ⟨Sh5, o5, g5, r5, w5, v5⟩ => ?_
  -- the words of the vectors
  have LAe : ∀ e < 2, ∀ k < 16, VG.Proof.Curve448.AArch64.Neon.L28 s.mem base a₁ a₂ e k ≤ VG.Proof.Curve448.AArch64.Neon.lmax k := VG.Proof.Curve448.AArch64.Neon.L28_le la₁ la₂
  have LBe : ∀ e < 2, ∀ k < 16, VG.Proof.Curve448.AArch64.Neon.L28 s.mem base b₁ b₂ e k ≤ VG.Proof.Curve448.AArch64.Neon.lmax k := VG.Proof.Curve448.AArch64.Neon.L28_le lb₁ lb₂
  have A2' : ∀ i < 8, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t2.mem base (NA + 16 * i + 4 * c) = VG.Proof.Curve448.AArch64.Neon.L28 s.mem base a₁ a₂ (c % 2) (2 * i + c / 2) :=
    fun i hi c hc => by rw [A2 i hi c hc, VG.Proof.Curve448.AArch64.Neon.split_l28 _ _ _ _ hc, m1]
  have B3' : ∀ i < 8, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t3.mem base (NB + 16 * i + 4 * c) = VG.Proof.Curve448.AArch64.Neon.L28 s.mem base b₁ b₂ (c % 2) (2 * i + c / 2) :=
    fun i hi c hc => by
      rw [B3 i hi c hc, VG.Proof.Curve448.AArch64.Neon.split_l28 _ _ _ _ hc]
      refine (VG.Proof.Curve448.AArch64.Neon.L28_congr (m := s.mem) (fun i' hi' => ?_) (fun i' hi' => ?_) (by omega))
      · rw [VG.Proof.Curve448.AArch64.Neon.limbs_outside o2 (Or.inl (by omega)) (by omega) hi', m1]
      · rw [VG.Proof.Curve448.AArch64.Neon.limbs_outside o2 (Or.inl (by omega)) (by omega) hi', m1]
  have A3 : ∀ i < 8, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t3.mem base (NA + 16 * i + 4 * c) = VG.Proof.Curve448.AArch64.Neon.L28 s.mem base a₁ a₂ (c % 2) (2 * i + c / 2) :=
    fun i hi c hc => by rw [Outside.nw o3 (by omega) (by omega)]; exact A2' i hi c hc
  have hA : ∀ i < 8, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t5.mem base (NA + 16 * i + 4 * c) = VG.Proof.Curve448.AArch64.Neon.L28 s.mem base a₁ a₂ (c % 2) (2 * i + c / 2) :=
    fun i hi c hc => by
      rw [Outside.nw o5 (by omega) (by omega), Outside.nw o4 (by omega) (by omega)]; exact A3 i hi c hc
  have B4 : ∀ i < 8, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t4.mem base (NB + 16 * i + 4 * c) = VG.Proof.Curve448.AArch64.Neon.L28 s.mem base b₁ b₂ (c % 2) (2 * i + c / 2) :=
    fun i hi c hc => by rw [Outside.nw o4 (by omega) (by omega)]; exact B3' i hi c hc
  have hB : ∀ i < 8, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t5.mem base (NB + 16 * i + 4 * c) = VG.Proof.Curve448.AArch64.Neon.L28 s.mem base b₁ b₂ (c % 2) (2 * i + c / 2) :=
    fun i hi c hc => by rw [Outside.nw o5 (by omega) (by omega)]; exact B4 i hi c hc
  have AS : ∀ i < 4, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t4.mem base (NAS + 16 * i + 4 * c) =
      (VG.Proof.Curve448.AArch64.Neon.L28 s.mem base a₁ a₂ (c % 2) (2 * i + c / 2) + VG.Proof.Curve448.AArch64.Neon.L28 s.mem base a₁ a₂ (c % 2) (8 + (2 * i + c / 2))) % 2 ^ 32 :=
    fun i hi c hc => by
      rw [AS4 i hi c hc, A3 i (by omega) c hc, A3 (i + 4) (by omega) c hc, show 2 * (i + 4) + c / 2 = 8 + (2 * i + c / 2)
        by omega]
  have BS : ∀ i < 4, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t4.mem base (NBS + 16 * i + 4 * c) =
      (VG.Proof.Curve448.AArch64.Neon.L28 s.mem base b₁ b₂ (c % 2) (2 * i + c / 2) + VG.Proof.Curve448.AArch64.Neon.L28 s.mem base b₁ b₂ (c % 2) (8 + (2 * i + c / 2))) % 2 ^ 32 :=
    fun i hi c hc => by
      rw [BS4 i hi c hc, B3' i (by omega) c hc, B3' (i + 4) (by omega) c hc, show 2 * (i + 4) + c / 2 = 8 + (2 * i + c / 2)
        by omega]
  have hb4 := VG.Proof.Curve448.AArch64.Neon.halfB_of LBe B4 BS
  have hSh : ∀ h < 3, ∀ j < 5, ∀ c < 4, VG.Proof.Curve448.AArch64.Neon.nw t5.mem base (NBP + 80 * h + 16 * j + 4 * c) =
      if c < 2 then (if j = 0 then 0 else VG.Proof.Curve448.AArch64.Neon.hl (VG.Proof.Curve448.AArch64.Neon.L28 s.mem base b₁ b₂ (c % 2)) h (2 * j - 1))
      else (if j = 4 then 0 else VG.Proof.Curve448.AArch64.Neon.hl (VG.Proof.Curve448.AArch64.Neon.L28 s.mem base b₁ b₂ (c % 2)) h (2 * j)) :=
    fun h hh j hj c hc => by rw [Sh5 h hh j hj c hc, VG.Proof.Curve448.AArch64.Neon.sh_of hb4 h hh j hj c hc]
  refine ⟨fun h hh => VG.Proof.Curve448.AArch64.Neon.halfMem_of LAe LBe hA hB (fun i hi c hc => by
      rw [Outside.nw o5 (by omega) (by omega)]; exact AS i hi c hc)
    (fun i hi c hc => by rw [Outside.nw o5 (by omega) (by omega)]; exact BS i hi c hc) hSh hh,
    fun e he => by rw [v5 _ (by decide), v4 _ (by decide), v3 _ (by decide), v2 _ (by decide)]; exact hM e he,
    by rw [v5 _ (by decide), v4 _ (by decide), v3 _ (by decide), v2 _ (by decide)]; exact h31,
    ?_, by rw [g5, g4, g3, g2, g1], by rw [r5, r4, r3, r2, rd1], by rw [w5, w4, w3, w2, wr1]⟩
  rw [m1] at o2
  exact (((o2.mono (by omega) (by omega)).trans (o3.mono (by omega) (by omega))).trans
    (o4.mono (by omega) (by omega))).trans (o5.mono (by omega) (by omega))

/-- The target of `U`'s coefficients. -/
abbrev tgtU (p : Nat) : Nat := if p < 8 then p + 8 else 16 + (p - 8)

theorem prods_pos_lt : ∀ p ∈ prods, p.pos < 15 := by decide
theorem prods_hit : ∀ q < 15, ∃ p ∈ prods, p.pos = q := by decide

theorem half_offsets (h : Nat) (hh : h < 3) :
    (∀ i < 4, (aHalf h + 16 * i) % 16 = 0 ∧ aHalf h + 16 * i + 16 ≤ 8192) ∧
    (∀ bv < 9, bOff h bv % 16 = 0 ∧ bOff h bv + 16 ≤ 8192) := by
  rcases (show h = 0 ∨ h = 1 ∨ h = 2 by omega) with rfl | rfl | rfl <;> decide

/-- A half's coefficient `q`, in register `tgt q`, from the `HalfMem` words. -/
theorem half_lanes {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {h : Nat} (hh : h < 3)
    {X Y : Nat → Nat → Nat} (hm : VG.Proof.Curve448.AArch64.Neon.HalfMem s.mem base h X Y) (tgt : Nat → Nat) (fresh : List Nat)
    (ht : ∀ p ∈ prods, tgt p.pos < 23) (hinj : ∀ q < 15, ∀ q' < 15, tgt q = tgt q' → q = q') :
    WP isa (.block (VG.Impl.Curve448.AArch64.Neon.half h tgt fresh)) s fun u =>
      u.mem = s.mem ∧ u.gpr = s.gpr ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      (∀ q < 15, ∀ e < 2, VG.Proof.Curve448.AArch64.Neon.lane (u.v (V (tgt q))) e % VG.Proof.Curve448.AArch64.Neon.M64 =
        ((if tgt q ∈ fresh then 0 else VG.Proof.Curve448.AArch64.Neon.lane (s.v (V (tgt q))) e) + VG.Proof.Curve448.AArch64.Neon.cv (X e) (Y e) q) % VG.Proof.Curve448.AArch64.Neon.M64) ∧
      (∀ r : VReg, (∀ n ∈ [23, 24, 25, 26, 27], r ≠ V n) → (∀ q < 15, r ≠ V (tgt q)) → u.v r = s.v r) := by
  obtain ⟨ha, hoff⟩ := VG.Proof.Curve448.AArch64.Neon.half_offsets h hh
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.half_ok hs tgt fresh ht ha hoff) fun u ⟨um, ug, ur, uw, ua, uv⟩ =>
    ⟨um, ug, ur, uw, fun q hq e he => ?_, fun r h1 h2 => uv r h1 fun p hp => h2 p.pos (VG.Proof.Curve448.AArch64.Neon.prods_pos_lt p hp)⟩
  have hp := VG.Proof.Curve448.AArch64.Neon.prods_hit q hq
  rw [ua (tgt q) (by obtain ⟨p, pm, rfl⟩ := hp; exact ht p pm) (Or.inr (by
      obtain ⟨p, pm, e'⟩ := hp; exact ⟨p, pm, by rw [e']⟩)) e he,
    VG.Proof.Curve448.AArch64.Neon.prodSum_cv hm hq (fun p pm => ⟨fun e' => hinj _ (VG.Proof.Curve448.AArch64.Neon.prods_pos_lt p pm) _ hq e', fun e' => by rw [e']⟩) he]

/-- From the operands' halves to Karatsuba's coefficients. -/
def prodsCode : List Instr :=
  VG.Impl.Curve448.AArch64.Neon.half 0 (fun p => p) (List.range 15) ++ foldS ++ VG.Impl.Curve448.AArch64.Neon.half 1 (fun p => p) [] ++
    VG.Impl.Curve448.AArch64.Neon.half 2 VG.Proof.Curve448.AArch64.Neon.tgtU ((List.range 7).map (16 + ·)) ++ foldU

theorem tgtU_lo {q : Nat} (hq : q < 8) : VG.Proof.Curve448.AArch64.Neon.tgtU q = q + 8 := ite_eq_left hq
theorem tgtU_hi {q : Nat} (hq : 8 ≤ q) : VG.Proof.Curve448.AArch64.Neon.tgtU q = 16 + (q - 8) := ite_eq_right (by omega)
theorem tgtU_inj : ∀ q < 15, ∀ q' < 15, VG.Proof.Curve448.AArch64.Neon.tgtU q = VG.Proof.Curve448.AArch64.Neon.tgtU q' → q = q' := by decide
theorem tgtU_lt : ∀ q < 15, VG.Proof.Curve448.AArch64.Neon.tgtU q < 23 := by decide
theorem tgtU_fresh : ∀ k < 16, k ∉ (List.range 7).map (16 + ·) := by decide
theorem fresh_mem : ∀ d < 7, 16 + d ∈ (List.range 7).map (16 + ·) := by decide

theorem not_tmp {k : Nat} (hk : k < 23) : ∀ n ∈ [23, 24, 25, 26, 27], V k ≠ V n :=
  fun n hn => VG.Proof.Curve448.AArch64.Neon.V_ne k (by omega) n (by simp at hn; omega) (by simp at hn; omega)

theorem lane_step {s u : State} {r : Nat} {x c : Nat → Int} (hx : VG.Proof.Curve448.AArch64.Neon.LaneEq s r x)
    (hu : ∀ e < 2, VG.Proof.Curve448.AArch64.Neon.lane (u.v (V r)) e % VG.Proof.Curve448.AArch64.Neon.M64 = (VG.Proof.Curve448.AArch64.Neon.lane (s.v (V r)) e + c e) % VG.Proof.Curve448.AArch64.Neon.M64) :
    VG.Proof.Curve448.AArch64.Neon.LaneEq u r (fun e => x e + c e) := fun e he => (hu e he).trans (VG.Proof.Curve448.AArch64.Neon.cong_add (hx e he) rfl)

theorem kara_fold (a b : Nat → Nat) {k : Nat} (hk : k < 16) :
    (if k < 8 then (VG.Proof.Curve448.AArch64.Neon.S a b k : Int) - (if k < 7 then (VG.Proof.Curve448.AArch64.Neon.S a b (k + 8) : Int) else 0) else -(VG.Proof.Curve448.AArch64.Neon.S a b (k - 8) : Int)) +
      (if k < 15 then (VG.Proof.Curve448.AArch64.Neon.T a b k : Int) else 0) + (if 8 ≤ k then (VG.Proof.Curve448.AArch64.Neon.U a b (k - 8) : Int) else 0) +
      (if k < 7 then (VG.Proof.Curve448.AArch64.Neon.U a b (k + 8) : Int) else if 8 ≤ k ∧ k < 15 then (VG.Proof.Curve448.AArch64.Neon.U a b (k - 8 + 8) : Int) else 0) =
      VG.Proof.Curve448.AArch64.Neon.kara a b k := by
  have s15 : VG.Proof.Curve448.AArch64.Neon.S a b 15 = 0 := rfl
  have t15 : VG.Proof.Curve448.AArch64.Neon.T a b 15 = 0 := rfl
  have u15 : VG.Proof.Curve448.AArch64.Neon.U a b 15 = 0 := rfl
  rcases (by omega : k < 7 ∨ k = 7 ∨ (8 ≤ k ∧ k < 15) ∨ k = 15) with h | rfl | h | rfl
  · simp (disch := omega) only [VG.Proof.Curve448.AArch64.Neon.kara, ite_eq_left, ite_eq_right]; omega
  · simp only [VG.Proof.Curve448.AArch64.Neon.kara, s15, u15]; simp
  · have e : k - 8 + 8 = k := by omega
    simp (disch := omega) only [VG.Proof.Curve448.AArch64.Neon.kara, ite_eq_left, ite_eq_right, e]; omega
  · simp only [VG.Proof.Curve448.AArch64.Neon.kara, t15, u15]; simp; omega

theorem prods_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {X Y : Nat → Nat → Nat}
    (hm : ∀ h < 3, VG.Proof.Curve448.AArch64.Neon.HalfMem s.mem base h (fun e => VG.Proof.Curve448.AArch64.Neon.hl (X e) h) (fun e => VG.Proof.Curve448.AArch64.Neon.hl (Y e) h)) (h31 : s.v (V 31) = 0) :
    WP isa (.block VG.Proof.Curve448.AArch64.Neon.prodsCode) s fun t =>
      (∀ k < 16, VG.Proof.Curve448.AArch64.Neon.LaneEq t k (fun e => VG.Proof.Curve448.AArch64.Neon.kara (X e) (Y e) k)) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ (∀ r : VReg, (∀ n < 29, r ≠ V n) → t.v r = s.v r) := by
  simp only [VG.Proof.Curve448.AArch64.Neon.prodsCode, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.half_lanes hs (by decide) (hm 0 (by decide)) (fun p => p) (List.range 15)
    (fun p hp => by have := VG.Proof.Curve448.AArch64.Neon.prods_pos_lt p hp; omega) (fun _ _ _ _ h => h)) fun t1 ⟨m1, g1, r1, w1, l1, v1⟩ => ?_
  have hx1 : ∀ q < 15, VG.Proof.Curve448.AArch64.Neon.LaneEq t1 q (fun e => (VG.Proof.Curve448.AArch64.Neon.S (X e) (Y e) q : Int)) := fun q hq e he => by
    rw [l1 q hq e he, ite_eq_left (List.mem_range.2 hq), Int.zero_add]
  have h31' : t1.v (V 31) = 0 := by
    rw [v1 _ (fun n hn => VG.Proof.Curve448.AArch64.Neon.V_ne 31 (by decide) n (by simp at hn; omega) (by simp at hn; omega))
      (fun q hq => VG.Proof.Curve448.AArch64.Neon.V_ne 31 (by decide) q (by omega) (by omega)), h31]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.foldS_ok _ hx1 h31') fun t2 ⟨f1, f2, m2, g2, r2, w2, v2⟩ => ?_
  have hx2 : ∀ k < 16, VG.Proof.Curve448.AArch64.Neon.LaneEq t2 k (fun e => if k < 8 then (VG.Proof.Curve448.AArch64.Neon.S (X e) (Y e) k : Int) -
      (if k < 7 then (VG.Proof.Curve448.AArch64.Neon.S (X e) (Y e) (k + 8) : Int) else 0) else -(VG.Proof.Curve448.AArch64.Neon.S (X e) (Y e) (k - 8) : Int)) := fun k hk e he => by
    dsimp only
    by_cases h8 : k < 8
    · rw [ite_eq_left h8]; exact f1 k h8 e he
    · rw [ite_eq_right h8]; have := f2 (k - 8) (by omega) e he; rwa [Nat.sub_add_cancel (by omega)] at this
  have s2 : VG.Proof.X448.AArch64.Scr t2 base := VG.Proof.Curve448.AArch64.Neon.scr_of hs (g2.trans g1) (w2.trans w1)
  have hm2 : ∀ h < 3, VG.Proof.Curve448.AArch64.Neon.HalfMem t2.mem base h (fun e => VG.Proof.Curve448.AArch64.Neon.hl (X e) h) (fun e => VG.Proof.Curve448.AArch64.Neon.hl (Y e) h) := by
    rw [m2, m1]; exact hm
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.half_lanes s2 (by decide) (hm2 1 (by decide)) (fun p => p) []
    (fun p hp => by have := VG.Proof.Curve448.AArch64.Neon.prods_pos_lt p hp; omega) (fun _ _ _ _ h => h)) fun t3 ⟨m3, g3, r3, w3, l3, v3⟩ => ?_
  have hx3 : ∀ k < 16, VG.Proof.Curve448.AArch64.Neon.LaneEq t3 k (fun e => (if k < 8 then (VG.Proof.Curve448.AArch64.Neon.S (X e) (Y e) k : Int) -
      (if k < 7 then (VG.Proof.Curve448.AArch64.Neon.S (X e) (Y e) (k + 8) : Int) else 0) else -(VG.Proof.Curve448.AArch64.Neon.S (X e) (Y e) (k - 8) : Int)) +
      (if k < 15 then (VG.Proof.Curve448.AArch64.Neon.T (X e) (Y e) k : Int) else 0)) := fun k hk => by
    by_cases h15 : k < 15
    · refine VG.Proof.Curve448.AArch64.Neon.lane_step (hx2 k hk) fun e he => ?_
      rw [l3 k h15 e he, ite_eq_right (List.not_mem_nil), ite_eq_left h15]
    · obtain rfl : k = 15 := by omega
      intro e he
      dsimp only
      rw [v3 _ (VG.Proof.Curve448.AArch64.Neon.not_tmp (by decide)) (fun q hq => VG.Proof.Curve448.AArch64.Neon.V_ne 15 (by decide) q (by omega) (by omega)), ite_eq_right h15,
        Int.add_zero]
      exact hx2 15 hk e he
  have s3 : VG.Proof.X448.AArch64.Scr t3 base := VG.Proof.Curve448.AArch64.Neon.scr_of s2 g3 w3
  have hm3 : ∀ h < 3, VG.Proof.Curve448.AArch64.Neon.HalfMem t3.mem base h (fun e => VG.Proof.Curve448.AArch64.Neon.hl (X e) h) (fun e => VG.Proof.Curve448.AArch64.Neon.hl (Y e) h) := by
    rw [m3]; exact hm2
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.half_lanes s3 (by decide) (hm3 2 (by decide)) VG.Proof.Curve448.AArch64.Neon.tgtU _
    (fun p hp => VG.Proof.Curve448.AArch64.Neon.tgtU_lt _ (VG.Proof.Curve448.AArch64.Neon.prods_pos_lt p hp)) VG.Proof.Curve448.AArch64.Neon.tgtU_inj) fun t4 ⟨m4, g4, r4, w4, l4, v4⟩ => ?_
  have hx4 : ∀ k < 16, VG.Proof.Curve448.AArch64.Neon.LaneEq t4 k (fun e => ((if k < 8 then (VG.Proof.Curve448.AArch64.Neon.S (X e) (Y e) k : Int) -
      (if k < 7 then (VG.Proof.Curve448.AArch64.Neon.S (X e) (Y e) (k + 8) : Int) else 0) else -(VG.Proof.Curve448.AArch64.Neon.S (X e) (Y e) (k - 8) : Int)) +
      (if k < 15 then (VG.Proof.Curve448.AArch64.Neon.T (X e) (Y e) k : Int) else 0)) + (if 8 ≤ k then (VG.Proof.Curve448.AArch64.Neon.U (X e) (Y e) (k - 8) : Int) else 0)) :=
      fun k hk => by
    by_cases h8 : 8 ≤ k
    · refine VG.Proof.Curve448.AArch64.Neon.lane_step (hx3 k hk) fun e he => ?_
      have := l4 (k - 8) (by omega) e he
      rw [VG.Proof.Curve448.AArch64.Neon.tgtU_lo (by omega), Nat.sub_add_cancel h8, ite_eq_right (VG.Proof.Curve448.AArch64.Neon.tgtU_fresh k hk)] at this
      rw [this, ite_eq_left h8]
    · intro e he
      dsimp only
      rw [v4 _ (VG.Proof.Curve448.AArch64.Neon.not_tmp (by omega)) (fun q hq => VG.Proof.Curve448.AArch64.Neon.V_ne k (by omega) _ (by have := VG.Proof.Curve448.AArch64.Neon.tgtU_lt q hq; omega)
          (by unfold VG.Proof.Curve448.AArch64.Neon.tgtU; split <;> omega)), ite_eq_right h8, Int.add_zero]
      exact hx3 k hk e he
  have hy4 : ∀ d < 7, VG.Proof.Curve448.AArch64.Neon.LaneEq t4 (16 + d) (fun e => (VG.Proof.Curve448.AArch64.Neon.U (X e) (Y e) (d + 8) : Int)) := fun d hd e he => by
    have := l4 (d + 8) (by omega) e he
    rw [VG.Proof.Curve448.AArch64.Neon.tgtU_hi (by omega), Nat.add_sub_cancel, ite_eq_left (VG.Proof.Curve448.AArch64.Neon.fresh_mem d hd), Int.zero_add] at this
    exact this
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.foldU_ok _ _ hx4 hy4) fun t5 ⟨l5, m5, g5, r5, w5, v5⟩ =>
    ⟨fun k hk e he => (l5 k hk e he).trans (by dsimp only; rw [VG.Proof.Curve448.AArch64.Neon.kara_fold _ _ hk]), m5.trans (m4.trans (m3.trans (m2.trans m1))),
      g5.trans (g4.trans (g3.trans (g2.trans g1))), r5.trans (r4.trans (r3.trans (r2.trans r1))),
      w5.trans (w4.trans (w3.trans (w2.trans w1))), fun r hr => ?_⟩
  have tmp : ∀ n ∈ [23, 24, 25, 26, 27], r ≠ V n := fun n hn => hr n (by simp at hn; omega)
  rw [v5 r (fun n hn => hr n (by omega)), v4 r tmp (fun q hq => hr _ (by have := VG.Proof.Curve448.AArch64.Neon.tgtU_lt q hq; omega)),
    v3 r tmp (fun q hq => hr _ (by omega)), v2 r (fun n hn => hr n (by omega)) (hr 28 (by decide)),
    v1 r tmp (fun q hq => hr _ (by omega))]

theorem mul2_eq (o₁ a₁ b₁ o₂ a₂ b₂ : Nat) :
    mul2 o₁ a₁ b₁ o₂ a₂ b₂ = VG.Proof.Curve448.AArch64.Neon.prep a₁ b₁ a₂ b₂ ++ (VG.Proof.Curve448.AArch64.Neon.prodsCode ++ (carries ++ VG.Impl.Curve448.AArch64.Neon.finish o₁ o₂)) := by
  simp only [mul2, VG.Proof.Curve448.AArch64.Neon.prep, VG.Proof.Curve448.AArch64.Neon.prodsCode, List.append_assoc]

theorem toNat_lt {x : Int} (h : x < 2 ^ 64 - 2 ^ 40) : x.toNat < 2 ^ 64 - 2 ^ 40 := by omega

theorem lane_exact {t : State} {k : Nat} {x : Int} (h0 : 0 ≤ x) (h1 : x < 2 ^ 64 - 2 ^ 40) {e : Nat}
    (h : VG.Proof.Curve448.AArch64.Neon.lane (t.v (V k)) e % VG.Proof.Curve448.AArch64.Neon.M64 = x % VG.Proof.Curve448.AArch64.Neon.M64) : (vdword (t.v (V k)) e).toNat = x.toNat := by
  have hl := VG.Proof.Curve448.AArch64.Neon.lane_lt (t.v (V k)) e
  rw [Int.emod_eq_of_lt (by simp [VG.Proof.Curve448.AArch64.Neon.lane]) hl, Int.emod_eq_of_lt h0 (by simp only [VG.Proof.Curve448.AArch64.Neon.M64]; omega)] at h
  simp only [VG.Proof.Curve448.AArch64.Neon.lane] at h; omega

theorem limbs28_even {r : Nat → Nat} (hr : ∀ k < 16, r k < 2 ^ 64 - 2 ^ 40) {i : Nat} (hi : i < 8) :
    VG.Proof.Curve448.AArch64.Neon.limbs28 r (2 * i) < 2 ^ 40 := by
  have := VG.Proof.Curve448.AArch64.Neon.limbs28_lt hr (show 2 * i < 16 by omega)
  split at this <;> split at this <;> omega

theorem limbs28_odd {r : Nat → Nat} (hr : ∀ k < 16, r k < 2 ^ 64 - 2 ^ 40) {i : Nat} (hi : i < 8) :
    VG.Proof.Curve448.AArch64.Neon.limbs28 r (2 * i + 1) < 2 ^ 28 := by
  have := VG.Proof.Curve448.AArch64.Neon.limbs28_lt hr (show 2 * i + 1 < 16 by omega)
  split at this <;> split at this <;> omega

theorem mul2_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o₁ a₁ b₁ o₂ a₂ b₂ : Nat}
    (ha₁ : a₁ % 16 = 0 ∧ a₁ + 64 ≤ NA) (hb₁ : b₁ % 16 = 0 ∧ b₁ + 64 ≤ NA)
    (ha₂ : a₂ % 16 = 0 ∧ a₂ + 64 ≤ NA) (hb₂ : b₂ % 16 = 0 ∧ b₂ + 64 ≤ NA)
    (ho₁ : o₁ % 16 = 0 ∧ o₁ + 64 ≤ NA) (ho₂ : o₂ % 16 = 0 ∧ o₂ + 64 ≤ NA) (h12 : o₁ + 64 ≤ o₂ ∨ o₂ + 64 ≤ o₁)
    (la₁ : ∀ i < 8, limbs s.mem base a₁ i < Ib) (lb₁ : ∀ i < 8, limbs s.mem base b₁ i < Ib)
    (la₂ : ∀ i < 8, limbs s.mem base a₂ i < Ib) (lb₂ : ∀ i < 8, limbs s.mem base b₂ i < Ib) :
    WP isa (.block (mul2 o₁ a₁ b₁ o₂ a₂ b₂)) s fun t =>
      (∀ i < 8, limbs t.mem base o₁ i < Mb) ∧ (∀ i < 8, limbs t.mem base o₂ i < Mb) ∧
      VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (limbs t.mem base o₁) 8) =
        VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (limbs s.mem base a₁) 8) * VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (limbs s.mem base b₁) 8) ∧
      VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (limbs t.mem base o₂) 8) =
        VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (limbs s.mem base a₂) 8) * VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (limbs s.mem base b₂) 8) ∧
      (∀ x, (VG.Proof.X448.AArch64.ofs base x < o₁ ∨ o₁ + 64 ≤ VG.Proof.X448.AArch64.ofs base x) → (VG.Proof.X448.AArch64.ofs base x < o₂ ∨ o₂ + 64 ≤ VG.Proof.X448.AArch64.ofs base x) →
        (VG.Proof.X448.AArch64.ofs base x < NA ∨ NA + 640 ≤ VG.Proof.X448.AArch64.ofs base x) → t.mem x = s.mem x) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hNA : NA = 4096 := rfl
  rw [VG.Proof.Curve448.AArch64.Neon.mul2_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.prep_ok hs ha₁ hb₁ ha₂ hb₂ la₁ lb₁ la₂ lb₂) fun t1 ⟨hm, hM, h31, o1, g1, r1, w1⟩ => ?_
  have s1 : VG.Proof.X448.AArch64.Scr t1 base := VG.Proof.Curve448.AArch64.Neon.scr_of hs g1 w1
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.prods_ok s1 (X := fun e => VG.Proof.Curve448.AArch64.Neon.L28 s.mem base a₁ a₂ e) (Y := fun e => VG.Proof.Curve448.AArch64.Neon.L28 s.mem base b₁ b₂ e) hm h31)
    fun t2 ⟨l2, m2, g2, r2, w2, v2⟩ => ?_
  have kb : ∀ e < 2, ∀ k < 16, VG.Proof.Curve448.AArch64.Neon.kara (VG.Proof.Curve448.AArch64.Neon.L28 s.mem base a₁ a₂ e) (VG.Proof.Curve448.AArch64.Neon.L28 s.mem base b₁ b₂ e) k < 2 ^ 64 - 2 ^ 40 :=
    fun e he k hk => VG.Proof.Curve448.AArch64.Neon.kara_le (VG.Proof.Curve448.AArch64.Neon.L28_le la₁ la₂ e he) (VG.Proof.Curve448.AArch64.Neon.L28_le lb₁ lb₂ e he) hk
  have hb : ∀ e < 2, ∀ k < 16, (VG.Proof.Curve448.AArch64.Neon.kara (VG.Proof.Curve448.AArch64.Neon.L28 s.mem base a₁ a₂ e) (VG.Proof.Curve448.AArch64.Neon.L28 s.mem base b₁ b₂ e) k).toNat < 2 ^ 64 - 2 ^ 40 :=
    fun e he k hk => VG.Proof.Curve448.AArch64.Neon.toNat_lt (kb e he k hk)
  have hr : ∀ k < 16, VG.Proof.Curve448.AArch64.Neon.LaneIs t2 k (fun e => (VG.Proof.Curve448.AArch64.Neon.kara (VG.Proof.Curve448.AArch64.Neon.L28 s.mem base a₁ a₂ e) (VG.Proof.Curve448.AArch64.Neon.L28 s.mem base b₁ b₂ e) k).toNat) :=
    fun k hk e he => VG.Proof.Curve448.AArch64.Neon.lane_exact (VG.Proof.Curve448.AArch64.Neon.kara_nonneg _ _ _) (kb e he k hk) (l2 k hk e he)
  have hM2 : ∀ e < 2, (vdword (t2.v (V 30)) e).toNat = 2 ^ 28 - 1 := by
    rw [v2 _ (fun n hn => VG.Proof.Curve448.AArch64.Neon.V_ne 30 (by decide) n (by omega) (by omega))]; exact hM
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.carries_ok _ hr hb hM2) fun t3 ⟨l3, m3, g3, r3, w3, v3⟩ => ?_
  have s3 : VG.Proof.X448.AArch64.Scr t3 base := VG.Proof.Curve448.AArch64.Neon.scr_of (VG.Proof.Curve448.AArch64.Neon.scr_of s1 g2 w2) g3 w3
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.finishN_ok s3 _ l3 (fun e he i hi => VG.Proof.Curve448.AArch64.Neon.limbs28_even (hb e he) hi)
    (fun e he i hi => VG.Proof.Curve448.AArch64.Neon.limbs28_odd (hb e he) hi) ho₁.1 (by omega) ho₂.1 (by omega) h12 (by
      rw [v3 _ (fun n _ => VG.Proof.Curve448.AArch64.Neon.V_ne 30 (by decide) n (by omega) (by omega)) (by decide) (by decide)]; exact hM2))
    fun t4 ⟨f1, f2, o4, r4, w4, g4⟩ => ?_
  have val : ∀ e < 2, ∀ {fa fb : Nat → Nat}, VG.Proof.Curve448.AArch64.Neon.L28 s.mem base a₁ a₂ e = VG.Proof.Curve448.AArch64.Neon.l28 fa → VG.Proof.Curve448.AArch64.Neon.L28 s.mem base b₁ b₂ e = VG.Proof.Curve448.AArch64.Neon.l28 fb →
      VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (VG.Proof.Curve448.AArch64.Neon.out56 (VG.Proof.Curve448.AArch64.Neon.limbs28 fun k => (VG.Proof.Curve448.AArch64.Neon.kara (VG.Proof.Curve448.AArch64.Neon.L28 s.mem base a₁ a₂ e) (VG.Proof.Curve448.AArch64.Neon.L28 s.mem base b₁ b₂ e) k).toNat)) 8) =
        VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN fa 8) * VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN fb 8) := fun e he fa fb ea eb =>
    VG.Proof.Curve448.AArch64.Neon.mul2_val fa fb _ fun k _ => by rw [Int.toNat_of_nonneg (VG.Proof.Curve448.AArch64.Neon.kara_nonneg _ _ _), ea, eb]
  refine ⟨fun i hi => (f1 i hi).symm ▸ VG.Proof.Curve448.AArch64.Neon.out56_bound (hb 0 (by decide)) i hi,
    fun i hi => (f2 i hi).symm ▸ VG.Proof.Curve448.AArch64.Neon.out56_bound (hb 1 (by decide)) i hi,
    (congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr f1)).trans (val 0 (by decide) rfl rfl),
    (congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr f2)).trans (val 1 (by decide) rfl rfl),
    fun x x1 x2 x3 => ?_, g4.trans (g3.trans (g2.trans g1)),
    r4.trans (r3.trans (r2.trans r1)), w4.trans (w3.trans (w2.trans w1))⟩
  rw [o4 x x1 x2, m3, m2]
  exact o1 x x3

end VG.Proof.Curve448.AArch64.Neon

end
