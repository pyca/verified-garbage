import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.AbsorbBlock
import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Boundary
import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64

theorem low_xor (a b : BitVec 128) :
    vdword (a ^^^ b) 0 = vdword a 0 ^^^ vdword b 0 := by
  simp only [vdword, BitVec.extractLsb'_xor]

theorem low_and (a b : BitVec 128) :
    vdword (a &&& b) 0 = vdword a 0 &&& vdword b 0 := by
  simp only [vdword, BitVec.extractLsb'_and]

theorem low_not (a : BitVec 128) : vdword (~~~a) 0 = ~~~(vdword a 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_not, Nat.mul_zero,
    Nat.zero_add, hi, decide_true, Bool.true_and, show i < 128 by omega]

theorem low_ext8 (a : BitVec 128) :
    vdword (((a ++ a) >>> (8 * 8)).extractLsb' 0 128) 0 = vdword a 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, Nat.mul_zero, Nat.zero_add, Nat.mul_one, hi,
    show i < 128 by omega, show 8 * 8 + i < 128 by omega,
    decide_true, Bool.true_and, ite_true]

theorem exec_vop (s : VG.AArch64.State) (op : VOp) :
    exec (.vop op) s = (VOp.eval s op).map (fun p => s.setV p.1 p.2) := rfl

theorem chi_low (a b c : BitVec 128) :
    vdword (a ^^^ (c &&& ~~~b)) 0 =
      (vdword b 0 ^^^ 0xffffffffffffffff) &&& vdword c 0 ^^^ vdword a 0 := by
  rw [VG.Proof.Sha3.AArch64.Sha3.Vector.low_xor, VG.Proof.Sha3.AArch64.Sha3.Vector.low_and, VG.Proof.Sha3.AArch64.Sha3.Vector.low_not]
  change _ = (vdword b 0 ^^^ BitVec.allOnes 64) &&& vdword c 0 ^^^ vdword a 0
  rw [BitVec.xor_allOnes, BitVec.and_comm, BitVec.xor_comm]

theorem chi_xor_low (a b c r : BitVec 128) :
    vdword ((a ^^^ (c &&& ~~~b)) ^^^ r) 0 =
      ((vdword b 0 ^^^ 0xffffffffffffffff) &&& vdword c 0 ^^^ vdword a 0) ^^^ vdword r 0 := by
  rw [VG.Proof.Sha3.AArch64.Sha3.Vector.low_xor, VG.Proof.Sha3.AArch64.Sha3.Vector.chi_low]

theorem rotl_mod (a : BitVec 64) (k : Nat) (hk : k < 64) :
    a.rotateRight ((64 - k) % 64) = Proof.Sha3.rotl a k := by
  by_cases h : k = 0
  · subst h
    simp only [Proof.Sha3.rotl, Nat.sub_zero, Nat.mod_self, ite_true]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]
  · simp only [Proof.Sha3.rotl, h, ite_false, Nat.mod_eq_of_lt (by omega : 64 - k < 64)]

theorem exec_umov_low (s : VG.AArch64.State) (d : Reg) (n : VReg) :
    exec (.umov .x d n 0) s = some (s.write .x d (vdword (s.v n) 0)) := rfl

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Semantics`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector

abbrev Low := VReg → BitVec 64

def low (s : VG.AArch64.State) : VG.Proof.Sha3.AArch64.Sha3.Vector.Low := fun r => vdword (s.v r) 0

/-- Canonical state, with no assumption about the upper vector lanes. -/
def Lanes (s : VG.AArch64.State) (A : Spec.Sha3.State) : Prop :=
  ∀ i (hi : i < 25), VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg i) = A[i]

/-- Scalar and memory fields untouched by a vector-only block. -/
structure Keep (s s' : VG.AArch64.State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.refl (s : VG.AArch64.State) : VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s s := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {s₀ s₁ s₂ : VG.AArch64.State} (h : VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s₀ s₁) (k : VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s₁ s₂) : VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s₀ s₂ :=
  ⟨k.gpr.trans h.gpr, k.mem.trans h.mem, k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp⟩

/-- A property of the first 25 numbers, one at a time. -/
theorem forall_lt_25 {P : Nat → Prop}
    (h : P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 ∧ P 6 ∧ P 7 ∧ P 8 ∧ P 9 ∧ P 10 ∧ P 11 ∧ P 12 ∧
      P 13 ∧ P 14 ∧ P 15 ∧ P 16 ∧ P 17 ∧ P 18 ∧ P 19 ∧ P 20 ∧ P 21 ∧ P 22 ∧ P 23 ∧ P 24) :
    ∀ i < 25, P i := by
  intro i hi
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := h
  match i, hi with
  | 0, _ => exact h0 | 1, _ => exact h1 | 2, _ => exact h2 | 3, _ => exact h3 | 4, _ => exact h4
  | 5, _ => exact h5 | 6, _ => exact h6 | 7, _ => exact h7 | 8, _ => exact h8 | 9, _ => exact h9
  | 10, _ => exact h10 | 11, _ => exact h11 | 12, _ => exact h12 | 13, _ => exact h13
  | 14, _ => exact h14 | 15, _ => exact h15 | 16, _ => exact h16 | 17, _ => exact h17
  | 18, _ => exact h18 | 19, _ => exact h19 | 20, _ => exact h20 | 21, _ => exact h21
  | 22, _ => exact h22 | 23, _ => exact h23 | 24, _ => exact h24
  | _ + 25, h => exact absurd h (by omega)

def put (σ : VG.Proof.Sha3.AArch64.Sha3.Vector.Low) (d : VReg) (w : BitVec 64) : VG.Proof.Sha3.AArch64.Sha3.Vector.Low := fun r => if r = d then w else σ r

def opLow (σ : VG.Proof.Sha3.AArch64.Sha3.Vector.Low) : Op → VG.Proof.Sha3.AArch64.Sha3.Vector.Low
  | .xor d n m => VG.Proof.Sha3.AArch64.Sha3.Vector.put σ d (σ n ^^^ σ m)
  | .eor3 d n m a => VG.Proof.Sha3.AArch64.Sha3.Vector.put σ d (σ n ^^^ σ m ^^^ σ a)
  | .rax1 d n m => VG.Proof.Sha3.AArch64.Sha3.Vector.put σ d (σ n ^^^ (σ m).rotateLeft 1)
  | .xar d n m k => VG.Proof.Sha3.AArch64.Sha3.Vector.put σ d ((σ n ^^^ σ m).rotateRight k.val)
  | .bcax d n m a => VG.Proof.Sha3.AArch64.Sha3.Vector.put σ d (σ n ^^^ (σ m &&& ~~~(σ a)))

def opState (s : VG.AArch64.State) : Op → VG.AArch64.State
  | .xor d n m => s.setV d (s.v n ^^^ s.v m)
  | .eor3 d n m a => s.setV d (s.v n ^^^ s.v m ^^^ s.v a)
  | .rax1 d n m => s.setV d (VArr.d2.map2 (fun _ x y => x ^^^ y.rotateLeft 1) (s.v n) (s.v m))
  | .xar d n m k => s.setV d (VArr.d2.map2 (fun _ x y => (x ^^^ y).rotateRight k.val) (s.v n) (s.v m))
  | .bcax d n m a => s.setV d (s.v n ^^^ (s.v m &&& ~~~(s.v a)))

theorem op_exec (s : VG.AArch64.State) (op : Op) : exec op.instr s = some (VG.Proof.Sha3.AArch64.Sha3.Vector.opState s op) := by
  cases op <;> simp only [Op.instr, VG.Proof.Sha3.AArch64.Sha3.Vector.exec_vop, VOp.eval, VG.Proof.Sha3.AArch64.Sha3.Vector.opState, Option.map_some]
  rename_i k
  simp only [k.isLt, ite_true, Option.map_some]

theorem op_keep (s : VG.AArch64.State) (op : Op) : VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s (VG.Proof.Sha3.AArch64.Sha3.Vector.opState s op) := by
  cases op <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem low_setV (s : VG.AArch64.State) (d : VReg) (v : BitVec 128) :
    VG.Proof.Sha3.AArch64.Sha3.Vector.low (s.setV d v) = VG.Proof.Sha3.AArch64.Sha3.Vector.put (VG.Proof.Sha3.AArch64.Sha3.Vector.low s) d (vdword v 0) := by
  funext r
  simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.low, VG.Proof.Sha3.AArch64.Sha3.Vector.put, RegUpd.v_setV]
  split <;> rfl

theorem op_low (s : VG.AArch64.State) (op : Op) : VG.Proof.Sha3.AArch64.Sha3.Vector.low (VG.Proof.Sha3.AArch64.Sha3.Vector.opState s op) = VG.Proof.Sha3.AArch64.Sha3.Vector.opLow (VG.Proof.Sha3.AArch64.Sha3.Vector.low s) op := by
  cases op <;> simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.opState, VG.Proof.Sha3.AArch64.Sha3.Vector.low_setV, VG.Proof.Sha3.AArch64.Sha3.Vector.opLow, VG.Proof.Sha3.AArch64.Sha3.Vector.low_xor, VG.Proof.Sha3.AArch64.Sha3.Vector.low_and, VG.Proof.Sha3.AArch64.Sha3.Vector.low_not,
    VArr.map2, vdword_ofVDwords_0, VG.Proof.Sha3.AArch64.Sha3.Vector.low]

def runLow (ops : List Op) (σ : VG.Proof.Sha3.AArch64.Sha3.Vector.Low) : VG.Proof.Sha3.AArch64.Sha3.Vector.Low := ops.foldl VG.Proof.Sha3.AArch64.Sha3.Vector.opLow σ

theorem ops_ok (ops : List Op) (s : VG.AArch64.State) :
    WP isa (.block (ops.map Op.instr)) s fun s' => VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s s' ∧ VG.Proof.Sha3.AArch64.Sha3.Vector.low s' = VG.Proof.Sha3.AArch64.Sha3.Vector.runLow ops (VG.Proof.Sha3.AArch64.Sha3.Vector.low s) := by
  induction ops generalizing s with
  | nil => exact wp_nil ⟨Keep.refl s, rfl⟩
  | cons op ops ih =>
    refine WP.cons (VG.Proof.Sha3.AArch64.Sha3.Vector.op_exec s op) ((ih (VG.Proof.Sha3.AArch64.Sha3.Vector.opState s op)).mono fun s' h => ?_)
    refine ⟨(VG.Proof.Sha3.AArch64.Sha3.Vector.op_keep s op).trans h.1, ?_⟩
    simpa only [VG.Proof.Sha3.AArch64.Sha3.Vector.runLow, List.foldl_cons, VG.Proof.Sha3.AArch64.Sha3.Vector.op_low] using h.2

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Theta`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3 (C D)

def dreg (x : Nat) : VReg := [VReg.v29, .v30, .v31, .v27, .v28].getD x .v29

def ALanes (σ : VG.Proof.Sha3.AArch64.Sha3.Vector.Low) (A : Spec.Sha3.State) : Prop :=
  ∀ i (hi : i < 25), σ (vreg i) = A[i]

def DLanes (σ : VG.Proof.Sha3.AArch64.Sha3.Vector.Low) (A : Spec.Sha3.State) : Prop :=
  ∀ x < 5, σ (VG.Proof.Sha3.AArch64.Sha3.Vector.dreg x) = D A x

theorem theta_preserves (σ : VG.Proof.Sha3.AArch64.Sha3.Vector.Low) (r : VReg) (hr : ∀ x < 7, r ≠ vreg (25 + x)) :
    VG.Proof.Sha3.AArch64.Sha3.Vector.runLow theta σ r = σ r := by
  have h25 := hr 0 (by decide)
  have h26 := hr 1 (by decide)
  have h27 := hr 2 (by decide)
  have h28 := hr 3 (by decide)
  have h29 := hr 4 (by decide)
  have h30 := hr 5 (by decide)
  have h31 := hr 6 (by decide)
  simp only [vreg, List.getD_cons_succ, List.getD_cons_zero] at h25 h26 h27 h28 h29 h30 h31
  simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.runLow, theta, List.foldl_cons, List.foldl_nil, VG.Proof.Sha3.AArch64.Sha3.Vector.opLow, VG.Proof.Sha3.AArch64.Sha3.Vector.put,
    h25, h26, h27, h28, h29, h30, h31, ite_false]

theorem theta_lanes (σ : VG.Proof.Sha3.AArch64.Sha3.Vector.Low) (A : Spec.Sha3.State) (h : VG.Proof.Sha3.AArch64.Sha3.Vector.ALanes σ A) :
    VG.Proof.Sha3.AArch64.Sha3.Vector.ALanes (VG.Proof.Sha3.AArch64.Sha3.Vector.runLow theta σ) A := by
  intro i hi
  rw [VG.Proof.Sha3.AArch64.Sha3.Vector.theta_preserves]
  · exact h i hi
  · exact (show ∀ i < 25, ∀ x < 7, vreg i ≠ vreg (25 + x) by decide) i hi

/-- The five correction words use RAX1's rotate-left by one. -/
theorem theta_d (σ : VG.Proof.Sha3.AArch64.Sha3.Vector.Low) (A : Spec.Sha3.State) (h : VG.Proof.Sha3.AArch64.Sha3.Vector.ALanes σ A) (x : Nat) (hx : x < 5) :
    VG.Proof.Sha3.AArch64.Sha3.Vector.runLow theta σ (VG.Proof.Sha3.AArch64.Sha3.Vector.dreg x) = D A x := by
  have ha : ∀ i (hi : i < 25), σ (vreg i) = A[i]! := fun i hi => (h i hi).trans
    (VG.Proof.Sha3.getElem!_eq A hi).symm
  obtain rfl | rfl | rfl | rfl | rfl : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by omega
  all_goals
    simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.runLow, theta, List.foldl_cons, List.foldl_nil, VG.Proof.Sha3.AArch64.Sha3.Vector.opLow, VG.Proof.Sha3.AArch64.Sha3.Vector.put, VG.Proof.Sha3.AArch64.Sha3.Vector.dreg,
      List.getD_cons_succ, List.getD_cons_zero, reduceCtorEq, ite_true, ite_false]
  all_goals
    have h0 := ha 0 (by decide)
    have h1 := ha 1 (by decide)
    have h2 := ha 2 (by decide)
    have h3 := ha 3 (by decide)
    have h4 := ha 4 (by decide)
    have h5 := ha 5 (by decide)
    have h6 := ha 6 (by decide)
    have h7 := ha 7 (by decide)
    have h8 := ha 8 (by decide)
    have h9 := ha 9 (by decide)
    have h10 := ha 10 (by decide)
    have h11 := ha 11 (by decide)
    have h12 := ha 12 (by decide)
    have h13 := ha 13 (by decide)
    have h14 := ha 14 (by decide)
    have h15 := ha 15 (by decide)
    have h16 := ha 16 (by decide)
    have h17 := ha 17 (by decide)
    have h18 := ha 18 (by decide)
    have h19 := ha 19 (by decide)
    have h20 := ha 20 (by decide)
    have h21 := ha 21 (by decide)
    have h22 := ha 22 (by decide)
    have h23 := ha 23 (by decide)
    have h24 := ha 24 (by decide)
    simp only [vreg, List.getD_cons_succ, List.getD_cons_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24
    simp only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,
      D, C, VG.Proof.Sha3.rotateLeft_eq _ (by decide : 0 < 1) (by decide : 1 < 64),
      Nat.reduceAdd, Nat.reduceMod]
    rw [BitVec.xor_comm]
    congr 1 <;> ac_rfl

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Rho`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Impl.Sha3 (rhoOff piSrc)
open VG.Proof.Sha3 (B rotl)

def BLanes (σ : VG.Proof.Sha3.AArch64.Sha3.Vector.Low) (A : Spec.Sha3.State) : Prop :=
  ∀ i < 25, σ (breg i) = B A (i % 5) (i / 5)

theorem rho_lanes (σ : VG.Proof.Sha3.AArch64.Sha3.Vector.Low) (A : Spec.Sha3.State) (hA : VG.Proof.Sha3.AArch64.Sha3.Vector.ALanes σ A) (hD : VG.Proof.Sha3.AArch64.Sha3.Vector.DLanes σ A) :
    VG.Proof.Sha3.AArch64.Sha3.Vector.BLanes (VG.Proof.Sha3.AArch64.Sha3.Vector.runLow rhoPi σ) A := by
  have ha : ∀ i (hi : i < 25), σ (vreg i) = A[i]! := fun i hi => (hA i hi).trans
    (VG.Proof.Sha3.getElem!_eq A hi).symm
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide)
  have a4 := ha 4 (by decide)
  have a5 := ha 5 (by decide)
  have a6 := ha 6 (by decide)
  have a7 := ha 7 (by decide)
  have a8 := ha 8 (by decide)
  have a9 := ha 9 (by decide)
  have a10 := ha 10 (by decide)
  have a11 := ha 11 (by decide)
  have a12 := ha 12 (by decide)
  have a13 := ha 13 (by decide)
  have a14 := ha 14 (by decide)
  have a15 := ha 15 (by decide)
  have a16 := ha 16 (by decide)
  have a17 := ha 17 (by decide)
  have a18 := ha 18 (by decide)
  have a19 := ha 19 (by decide)
  have a20 := ha 20 (by decide)
  have a21 := ha 21 (by decide)
  have a22 := ha 22 (by decide)
  have a23 := ha 23 (by decide)
  have a24 := ha 24 (by decide)
  simp only [vreg, List.getD_cons_succ, List.getD_cons_zero] at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
  have d0 := hD 0 (by decide)
  have d1 := hD 1 (by decide)
  have d2 := hD 2 (by decide)
  have d3 := hD 3 (by decide)
  have d4 := hD 4 (by decide)
  simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.dreg, List.getD_cons_succ, List.getD_cons_zero] at d0 d1 d2 d3 d4
  -- One `simp` for all the lanes, which simplifies `runLow rhoPi σ` once.
  refine VG.Proof.Sha3.AArch64.Sha3.Vector.forall_lt_25 ?_
  simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.runLow, rhoPi, List.foldl_cons, List.foldl_nil, VG.Proof.Sha3.AArch64.Sha3.Vector.opLow, VG.Proof.Sha3.AArch64.Sha3.Vector.put, breg,
      List.getD_cons_succ, List.getD_cons_zero, reduceCtorEq, ite_true, ite_false,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, d0,d1,d2,d3,d4,
      B, piSrc, rhoOff, rotl, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul,
      Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero, reduceCtorEq, ite_true, ite_false, and_self]

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Chi`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3 (B)

def chiWord (A : Spec.Sha3.State) (i : Nat) : BitVec 64 :=
  B A (i % 5) (i / 5) ^^^
    (B A ((i % 5 + 2) % 5) (i / 5) &&& ~~~(B A ((i % 5 + 1) % 5) (i / 5)))

def CLanes (σ : VG.Proof.Sha3.AArch64.Sha3.Vector.Low) (A : Spec.Sha3.State) : Prop := ∀ i < 25, σ (vreg i) = VG.Proof.Sha3.AArch64.Sha3.Vector.chiWord A i

theorem chi_lanes (σ : VG.Proof.Sha3.AArch64.Sha3.Vector.Low) (A : Spec.Sha3.State) (hB : VG.Proof.Sha3.AArch64.Sha3.Vector.BLanes σ A) :
    VG.Proof.Sha3.AArch64.Sha3.Vector.CLanes (VG.Proof.Sha3.AArch64.Sha3.Vector.runLow chi σ) A := by
  have b0 := hB 0 (by decide)
  have b1 := hB 1 (by decide)
  have b2 := hB 2 (by decide)
  have b3 := hB 3 (by decide)
  have b4 := hB 4 (by decide)
  have b5 := hB 5 (by decide)
  have b6 := hB 6 (by decide)
  have b7 := hB 7 (by decide)
  have b8 := hB 8 (by decide)
  have b9 := hB 9 (by decide)
  have b10 := hB 10 (by decide)
  have b11 := hB 11 (by decide)
  have b12 := hB 12 (by decide)
  have b13 := hB 13 (by decide)
  have b14 := hB 14 (by decide)
  have b15 := hB 15 (by decide)
  have b16 := hB 16 (by decide)
  have b17 := hB 17 (by decide)
  have b18 := hB 18 (by decide)
  have b19 := hB 19 (by decide)
  have b20 := hB 20 (by decide)
  have b21 := hB 21 (by decide)
  have b22 := hB 22 (by decide)
  have b23 := hB 23 (by decide)
  have b24 := hB 24 (by decide)
  simp only [breg, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceMod, Nat.reduceDiv] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24
  -- One `simp` for all the lanes, which simplifies `runLow chi σ` once.
  refine VG.Proof.Sha3.AArch64.Sha3.Vector.forall_lt_25 ?_
  simp only [and_self, VG.Proof.Sha3.AArch64.Sha3.Vector.runLow, chi, List.foldl_cons, List.foldl_nil, VG.Proof.Sha3.AArch64.Sha3.Vector.opLow, VG.Proof.Sha3.AArch64.Sha3.Vector.put, vreg,
      List.getD_cons_succ, List.getD_cons_zero, reduceCtorEq, ite_true, ite_false,
      b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, VG.Proof.Sha3.AArch64.Sha3.Vector.chiWord, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd]

theorem chiWord_out (A : Spec.Sha3.State) (rc : BitVec 64) (i : Nat) (hi : i < 25) :
    (if i = 0 then VG.Proof.Sha3.AArch64.Sha3.Vector.chiWord A i ^^^ rc else VG.Proof.Sha3.AArch64.Sha3.Vector.chiWord A i) =
      (VG.Proof.Sha3.outState A rc)[i] := by
  simp only [VG.Proof.Sha3.outState, Vector.getElem_ofFn, VG.Proof.Sha3.out, VG.Proof.Sha3.AArch64.Sha3.Vector.chiWord]
  have hz : i % 5 = 0 ∧ i / 5 = 0 ↔ i = 0 := by omega
  simp only [hz]
  have hn (v : BitVec 64) : v ^^^ 0xffffffffffffffff = ~~~v := BitVec.xor_allOnes
  simp only [hn, BitVec.and_comm, BitVec.xor_comm]

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Constant`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector

/-- The scalar/memory fields preserved by all rounds. -/
structure CoreKeep (s s' : VG.AArch64.State) : Prop where
  gpr : ∀ r, r ≠ .x16 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem CoreKeep.refl (s : VG.AArch64.State) : VG.Proof.Sha3.AArch64.Sha3.Vector.CoreKeep s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem CoreKeep.trans {s₀ s₁ s₂ : VG.AArch64.State}
    (h : VG.Proof.Sha3.AArch64.Sha3.Vector.CoreKeep s₀ s₁) (k : VG.Proof.Sha3.AArch64.Sha3.Vector.CoreKeep s₁ s₂) : VG.Proof.Sha3.AArch64.Sha3.Vector.CoreKeep s₀ s₂ :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.mem.trans h.mem,
    k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp⟩

theorem Keep.core {s s' : VG.AArch64.State} (h : VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s s') : VG.Proof.Sha3.AArch64.Sha3.Vector.CoreKeep s s' :=
  ⟨fun r _ => congrFun h.gpr r, h.mem, h.rd, h.wr, h.sp⟩

def movkValue (w : BitVec 64) (v : BitVec 16) (hw : Nat) : BitVec 64 :=
  (w &&& ~~~((65535 : BitVec 64) <<< (16 * hw))) ||| (v.setWidth 64 <<< (16 * hw))

def constantLow (v : BitVec 64) : BitVec 64 :=
  let w := (v.extractLsb' 0 16).setWidth 64 <<< (16 * 0)
  let w := if v.extractLsb' 16 16 = 0 then w else VG.Proof.Sha3.AArch64.Sha3.Vector.movkValue w (v.extractLsb' 16 16) 1
  let w := if v.extractLsb' 32 16 = 0 then w else VG.Proof.Sha3.AArch64.Sha3.Vector.movkValue w (v.extractLsb' 32 16) 2
  if v.extractLsb' 48 16 = 0 then w else VG.Proof.Sha3.AArch64.Sha3.Vector.movkValue w (v.extractLsb' 48 16) 3

/-- A finite, kernel-checked fact about the 24 public round constants. -/
theorem constantLow_RC : ∀ r < 24, VG.Proof.Sha3.AArch64.Sha3.Vector.constantLow (Spec.Sha3.RC r) = Spec.Sha3.RC r := by
  decide +kernel

theorem constant_ok (v : BitVec 64) (s : VG.AArch64.State) :
    WP isa (.block (constant v)) s fun s' =>
      VG.Proof.Sha3.AArch64.Sha3.Vector.CoreKeep s s' ∧ s'.v = s.v ∧ s'.gpr .x16 = VG.Proof.Sha3.AArch64.Sha3.Vector.constantLow v := by
  by_cases h1 : v.extractLsb' 16 16 = 0 <;>
    by_cases h2 : v.extractLsb' 32 16 = 0 <;>
    by_cases h3 : v.extractLsb' 48 16 = 0
  all_goals
    simp only [constant, h1, h2, h3, ite_true, ite_false,
      List.cons_append, List.nil_append]
    repeat' apply WP.cons rfl
    apply wp_nil
    refine ⟨⟨?_, rfl, rfl, rfl, rfl⟩, rfl, ?_⟩
    · intro r hr
      simp only [RegUpd.gpr_write, hr, ite_false]
    · simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.constantLow, h1, h2, h3, ite_true, ite_false, VG.Proof.Sha3.AArch64.Sha3.Vector.movkValue,
        RegUpd.gpr_write_self, State.read, Size.bits, BitVec.setWidth_eq]

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector

/-- The 65 register-resident vector operations before iota. -/
theorem core_ok (s : VG.AArch64.State) (A : Spec.Sha3.State) (hA : VG.Proof.Sha3.AArch64.Sha3.Vector.Lanes s A) :
    WP isa (.block ((theta ++ rhoPi ++ chi).map Op.instr)) s fun s' =>
      VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s s' ∧ VG.Proof.Sha3.AArch64.Sha3.Vector.CLanes (VG.Proof.Sha3.AArch64.Sha3.Vector.low s') A := by
  refine (VG.Proof.Sha3.AArch64.Sha3.Vector.ops_ok (theta ++ rhoPi ++ chi) s).mono fun s' h => ⟨h.1, ?_⟩
  rw [h.2]
  have ht := VG.Proof.Sha3.AArch64.Sha3.Vector.theta_lanes (VG.Proof.Sha3.AArch64.Sha3.Vector.low s) A hA
  have hd : VG.Proof.Sha3.AArch64.Sha3.Vector.DLanes (VG.Proof.Sha3.AArch64.Sha3.Vector.runLow theta (VG.Proof.Sha3.AArch64.Sha3.Vector.low s)) A := VG.Proof.Sha3.AArch64.Sha3.Vector.theta_d (VG.Proof.Sha3.AArch64.Sha3.Vector.low s) A hA
  have hr := VG.Proof.Sha3.AArch64.Sha3.Vector.rho_lanes (VG.Proof.Sha3.AArch64.Sha3.Vector.runLow theta (VG.Proof.Sha3.AArch64.Sha3.Vector.low s)) A ht hd
  have hc := VG.Proof.Sha3.AArch64.Sha3.Vector.chi_lanes (VG.Proof.Sha3.AArch64.Sha3.Vector.runLow rhoPi (VG.Proof.Sha3.AArch64.Sha3.Vector.runLow theta (VG.Proof.Sha3.AArch64.Sha3.Vector.low s))) A hr
  simpa only [VG.Proof.Sha3.AArch64.Sha3.Vector.runLow, List.foldl_append] using hc

theorem iota_ok (s : VG.AArch64.State) (A : Spec.Sha3.State) (rc : BitVec 64)
    (hA : VG.Proof.Sha3.AArch64.Sha3.Vector.CLanes (VG.Proof.Sha3.AArch64.Sha3.Vector.low s) A) (hc : s.gpr .x16 = rc) :
    WP isa (.block iota) s fun s' => VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s s' ∧ VG.Proof.Sha3.AArch64.Sha3.Vector.Lanes s' (VG.Proof.Sha3.outState A rc) := by
  unfold iota
  refine WP.cons rfl (WP.cons rfl (wp_nil ⟨⟨rfl,rfl,rfl,rfl,rfl⟩, ?_⟩))
  intro i hi
  rw [← VG.Proof.Sha3.AArch64.Sha3.Vector.chiWord_out A rc i hi]
  have h0 : vreg i = .v0 ↔ i = 0 :=
    (show ∀ i < 25, vreg i = .v0 ↔ i = 0 by decide) i hi
  have h26 : vreg i ≠ .v26 := (show ∀ i < 25, vreg i ≠ .v26 by decide) i hi
  simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.low, RegUpd.v_setV, reduceCtorEq, ite_false, ite_true, hc]
  simp only [h0, h26, ite_false]
  split
  · rename_i he
    subst i
    simpa only [VG.Proof.Sha3.AArch64.Sha3.Vector.low, vreg, List.getD_cons_zero, VG.Proof.Sha3.AArch64.Sha3.Vector.low_xor, vdword_ofVDwords_0] using congrArg (· ^^^ rc) (hA 0 (by decide))
  · exact hA i hi

theorem round_ok (r : Nat) (hr : r < 24) (s : VG.AArch64.State) (A : Spec.Sha3.State)
    (hA : VG.Proof.Sha3.AArch64.Sha3.Vector.Lanes s A) :
    WP isa (.block (round r)) s fun s' => VG.Proof.Sha3.AArch64.Sha3.Vector.CoreKeep s s' ∧ VG.Proof.Sha3.AArch64.Sha3.Vector.Lanes s' (Spec.Sha3.rnd A r) := by
  unfold round
  rw [show constant (Spec.Sha3.RC r) ++ theta.map Op.instr ++ rhoPi.map Op.instr ++
      chi.map Op.instr ++ iota =
      constant (Spec.Sha3.RC r) ++ (theta ++ rhoPi ++ chi).map Op.instr ++ iota by
        simp only [List.map_append, List.append_assoc]]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (VG.Proof.Sha3.AArch64.Sha3.Vector.constant_ok (Spec.Sha3.RC r) s).mono fun s₁ h₁ => ?_
  have ha₁ : VG.Proof.Sha3.AArch64.Sha3.Vector.Lanes s₁ A := by
    intro i hi
    change vdword (s₁.v (vreg i)) 0 = _
    rw [h₁.2.1]
    exact hA i hi
  refine (VG.Proof.Sha3.AArch64.Sha3.Vector.core_ok s₁ A ha₁).mono fun s₂ h₂ => ?_
  have hrc : s₂.gpr .x16 = Spec.Sha3.RC r := by
    rw [h₂.1.gpr, h₁.2.2, VG.Proof.Sha3.AArch64.Sha3.Vector.constantLow_RC r hr]
  refine (VG.Proof.Sha3.AArch64.Sha3.Vector.iota_ok s₂ A (Spec.Sha3.RC r) h₂.2 hrc).mono fun s' h₃ => ?_
  refine ⟨h₁.1.trans (h₂.1.core.trans h₃.1.core), ?_⟩
  simpa only [VG.Proof.Sha3.outState_eq] using h₃.2

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Rounds`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector

theorem rounds_list_ok (rs : List Nat) (hrs : ∀ r ∈ rs, r < 24)
    (s : VG.AArch64.State) (A : Spec.Sha3.State) (hA : VG.Proof.Sha3.AArch64.Sha3.Vector.Lanes s A) :
    WP isa (.block (rs.flatMap round)) s fun s' =>
      VG.Proof.Sha3.AArch64.Sha3.Vector.CoreKeep s s' ∧ VG.Proof.Sha3.AArch64.Sha3.Vector.Lanes s' (rs.foldl Spec.Sha3.rnd A) := by
  induction rs generalizing s A with
  | nil => exact wp_nil ⟨CoreKeep.refl s, hA⟩
  | cons r rs ih =>
    rw [List.flatMap_cons, List.foldl_cons, WP.block_append_iff]
    refine (VG.Proof.Sha3.AArch64.Sha3.Vector.round_ok r (hrs r (by simp)) s A hA).mono fun s₁ h₁ => ?_
    refine (ih (fun r hr => hrs r (by simp only [List.mem_cons]; exact Or.inr hr))
      s₁ (Spec.Sha3.rnd A r) h₁.2).mono fun s' h₂ => ?_
    exact ⟨h₁.1.trans h₂.1, h₂.2⟩

/-- All 24 rounds preserve scalar ABI fields and compute Keccak-f[1600].
The boundary restores v8–v15 after serializing these result lanes. -/
theorem rounds_ok (s : VG.AArch64.State) (A : Spec.Sha3.State) (hA : VG.Proof.Sha3.AArch64.Sha3.Vector.Lanes s A) :
    WP isa (.block rounds) s fun s' => VG.Proof.Sha3.AArch64.Sha3.Vector.CoreKeep s s' ∧ VG.Proof.Sha3.AArch64.Sha3.Vector.Lanes s' (Spec.Sha3.keccakF A) :=
  VG.Proof.Sha3.AArch64.Sha3.Vector.rounds_list_ok (List.range 24) (fun _ h => List.mem_range.mp h) s A hA

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.BoundaryCommon`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3 (laneAddr)

structure Ptrs (s s' : VG.AArch64.State) : Prop where
  x0 : s'.gpr .x0 = s.gpr .x0
  x1 : s'.gpr .x1 = s.gpr .x1
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Ptrs.refl (s : VG.AArch64.State) : VG.Proof.Sha3.AArch64.Sha3.Vector.Ptrs s s := ⟨rfl,rfl,rfl,rfl,rfl⟩
theorem Ptrs.trans {s t u : VG.AArch64.State} (h : VG.Proof.Sha3.AArch64.Sha3.Vector.Ptrs s t) (k : VG.Proof.Sha3.AArch64.Sha3.Vector.Ptrs t u) : VG.Proof.Sha3.AArch64.Sha3.Vector.Ptrs s u :=
  ⟨k.x0.trans h.x0,k.x1.trans h.x1,k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩
theorem Keep.ptrs {s t : VG.AArch64.State} (h : VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s t) : VG.Proof.Sha3.AArch64.Sha3.Vector.Ptrs s t :=
  ⟨congrFun h.gpr _,congrFun h.gpr _,h.rd,h.wr,h.sp⟩
theorem CoreKeep.ptrs {s t : VG.AArch64.State} (h : VG.Proof.Sha3.AArch64.Sha3.Vector.CoreKeep s t) : VG.Proof.Sha3.AArch64.Sha3.Vector.Ptrs s t :=
  ⟨h.gpr _ (by decide),h.gpr _ (by decide),h.rd,h.wr,h.sp⟩

theorem vreg_inj : ∀ i < 32, ∀ j < 32, vreg i = vreg j ↔ i = j := by decide

theorem exec_ldrq {s : VG.AArch64.State} {t : VReg} {n : Reg} {off : Nat}
    (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec,addr,ho,and_self,ite_true,Option.bind_some,State.load,h,Option.map_some]

theorem exec_strq {s : VG.AArch64.State} {t : VReg} {n : Reg} {off : Nat}
    (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s = some {s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t)} := by
  simp only [exec,addr,ho,and_self,ite_true,Option.bind_some,State.store,h]

theorem read_write16 (m : Mem) (p : Addr) (v : BitVec 128) :
    (m.write p 16 v).read p 16 = v := by
  simpa only [Mem.readW,Mem.writeW,Nat.reduceMul,Nat.reduceDiv,BitVec.setWidth_eq] using
    Mem.readW_writeW_self m p 16 v (by decide)

def Saved (s₀ : VG.AArch64.State) (m : Mem) : Prop :=
  ∀ i < 8, m.read (s₀.gpr .x1 + BitVec.ofNat 64 (16*i)) 16 = s₀.v (vreg (8+i))

theorem scratch_contains (s : VG.AArch64.State) {i : Nat} (hi : i < 8) :
    (⟨s.gpr .x1,512⟩ : Region).Contains (s.gpr .x1 + BitVec.ofNat 64 (16*i)) 16 :=
  Offset.contains_base _ (by omega) (by omega)

theorem state_pair_contains (s : VG.AArch64.State) {i : Nat} (hi : i < 12) :
    (⟨s.gpr .x0,200⟩ : Region).Contains (s.gpr .x0 + BitVec.ofNat 64 (16*i)) 16 :=
  Offset.contains_base _ (by omega) (by omega)

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Load`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3 (laneAddr)

theorem pair_low (m : Mem) (p : Addr) (i : Nat) :
    vdword (m.read (p + BitVec.ofNat 64 (16*i)) 16) 0 = m.readW (laneAddr p (2*i)) 64 := by
  rw [vdword_read16 _ _ (by decide)]
  simp only [laneAddr,Nat.mul_zero,BitVec.add_zero,show 8*(2*i)=16*i by omega]

theorem pair_high (m : Mem) (p : Addr) (i : Nat) :
    vdword (m.read (p + BitVec.ofNat 64 (16*i)) 16) 1 = m.readW (laneAddr p (2*i+1)) 64 := by
  rw [vdword_read16 _ _ (by decide)]
  simp only [laneAddr,Nat.mul_one,BitVec.add_assoc,← BitVec.ofNat_add,
    show 16*i+8=8*(2*i+1) by omega]

theorem loadPair_ok (s : VG.AArch64.State) (i : Nat) (hi : i < 12)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (loadPair i)) s fun s' => VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s s' ∧ ∀ j < 25,
      VG.Proof.Sha3.AArch64.Sha3.Vector.low s' (vreg j) = if j = 2*i+1 then s.mem.readW (laneAddr (s.gpr .x0) (2*i+1)) 64
        else if j = 2*i then s.mem.readW (laneAddr (s.gpr .x0) (2*i)) 64 else VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg j) := by
  unfold loadPair
  let q := s.mem.read (s.gpr .x0 + BitVec.ofNat 64 (16*i)) 16
  refine WP.cons (VG.Proof.Sha3.AArch64.Sha3.Vector.exec_ldrq ⟨by omega,by omega⟩ hin) (WP.cons
    (s' := (s.setV (vreg (2*i)) q).setV (vreg (2*i+1)) (((q ++ q) >>> (8*8)).extractLsb' 0 128))
    ?_ (wp_nil ?_))
  · simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.exec_vop,VOp.eval,show 8 < 16 by decide,ite_true,Option.map_some,RegUpd.v_setV_self,q]
  · refine ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,fun j hj => ?_⟩
    rw [VG.Proof.Sha3.AArch64.Sha3.Vector.low_setV]
    simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.put]
    rw [VG.Proof.Sha3.AArch64.Sha3.Vector.low_setV]
    simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.put,VG.Proof.Sha3.AArch64.Sha3.Vector.vreg_inj j (by omega) (2*i+1) (by omega),
      VG.Proof.Sha3.AArch64.Sha3.Vector.vreg_inj j (by omega) (2*i) (by omega),q,VG.Proof.Sha3.AArch64.Sha3.Vector.pair_low]
    rw [VG.Proof.Sha3.AArch64.Sha3.Vector.low_ext8, VG.Proof.Sha3.AArch64.Sha3.Vector.pair_high]

structure LoadInv (s₀ : VG.AArch64.State) (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s₀ s
  lanes : ∀ j < 2*k, VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg j) = s₀.mem.readW (laneAddr (s₀.gpr .x0) j) 64

theorem load_ok (s₀ : VG.AArch64.State)
    (hp : ∀ i < 12, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 (16*i)) 16)
    (hl : InRegions (s₀.rd ++ s₀.wr) (laneAddr (s₀.gpr .x0) 24) 8) :
    WP isa (.block load) s₀ fun s' => VG.Proof.Sha3.AArch64.Sha3.Vector.Ptrs s₀ s' ∧ s'.mem = s₀.mem ∧
      VG.Proof.Sha3.AArch64.Sha3.Vector.Lanes s' (Spec.Sha3.stateAt s₀.mem (s₀.gpr .x0)) := by
  have hh : WP isa (.block ((List.range 12).flatMap loadPair)) s₀ (VG.Proof.Sha3.AArch64.Sha3.Vector.LoadInv s₀ 12) := by
    refine wp_range_flatMap (M := isa) (VG.Proof.Sha3.AArch64.Sha3.Vector.LoadInv s₀) (fun i s hi hs => ?_)
      12 (Nat.le_refl _) s₀ ⟨Keep.refl _,fun _ h => absurd h (by omega)⟩
    refine (VG.Proof.Sha3.AArch64.Sha3.Vector.loadPair_ok s i hi (by rw [hs.keep.rd,hs.keep.wr,hs.keep.gpr]; exact hp i hi)).mono
      fun s' ⟨hk,ha⟩ => ⟨hs.keep.trans hk,fun j hj => ?_⟩
    rw [ha j (by omega)]
    split
    · rename_i he; subst j
      rw [hs.keep.mem,hs.keep.gpr]
    · split
      · rename_i he; subst j
        rw [hs.keep.mem,hs.keep.gpr]
      · exact hs.lanes j (by omega)
  rw [load,WP.block_append_iff]
  refine hh.mono fun s hs => ?_
  unfold loadLast
  refine WP.cons (exec_ldr_x (by decide) ?_) (WP.cons rfl (wp_nil ?_))
  · rw [hs.keep.rd,hs.keep.wr,hs.keep.gpr]
    exact hl
  · refine ⟨?_,hs.keep.mem,fun j hj => ?_⟩
    · constructor <;> simp only [reduceCtorEq, ↓reduceIte, RegUpd.gpr_setV,RegUpd.gpr_write,
        RegUpd.rd_setV,RegUpd.rd_write,RegUpd.wr_setV,RegUpd.wr_write,
        RegUpd.sp_setV,RegUpd.sp_write,hs.keep.gpr,hs.keep.rd,hs.keep.wr,hs.keep.sp]
    · simp only [Spec.Sha3.stateAt,Vector.getElem_ofFn,VG.Proof.Sha3.AArch64.Sha3.Vector.low,RegUpd.v_setV,
        RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq]
      have he : vreg j = .v24 ↔ j = 24 := VG.Proof.Sha3.AArch64.Sha3.Vector.vreg_inj j (by omega) 24 (by decide)
      simp only [he]
      split
      · rename_i he; subst j
        rw [vdword_ofVDwords_0,hs.keep.mem,hs.keep.gpr]
      · exact hs.lanes j (by omega)

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.AbsorbBlock`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3 (laneAddr)

/-- Word-wise description of XORing a whole number of input words. -/
def xorWords (A : Spec.Sha3.State) (m : Mem) (p : Addr) (n : Nat) : Spec.Sha3.State :=
  Vector.ofFn fun i => A[i] ^^^ (if i.val < n then m.readW (laneAddr p i.val) 64 else 0)

theorem xorWords_get (A : Spec.Sha3.State) (m : Mem) (p : Addr) (n j : Nat) (hj : j < 25) :
    (VG.Proof.Sha3.AArch64.Sha3.Vector.xorWords A m p n)[j] = A[j] ^^^ (if j < n then m.readW (laneAddr p j) 64 else 0) := by
  simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.xorWords, Vector.getElem_ofFn, Fin.getElem_fin]

theorem xorWords_eq (A : Spec.Sha3.State) (m : Mem) (p : Addr) (n : Nat) :
    VG.Proof.Sha3.AArch64.Sha3.Vector.xorWords A m p n = Spec.Sha3.xorBytes A (Spec.Sha3.bytesAt m p (8*n)) := by
  apply VG.Proof.Sha3.ext_bytes
  intro j hj
  rw [VG.Proof.Sha3.byteOf_xorBytes _ _ hj, VG.Proof.Sha3.byteOf_eq' _ hj,
    VG.Proof.Sha3.byteOf_eq' _ hj]
  simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.xorWords,Vector.getElem_ofFn,BitVec.extractLsb'_xor]
  congr 1
  by_cases hn : j < 8*n
  · have hw : j/8 < n := by omega
    simp only [hw,ite_true,Mem.readW,BitVec.setWidth_eq]
    rw [Mem.extractLsb'_read _ _ (by omega : j%8 < 64/8)]
    simp only [Spec.Sha3.bytesAt,List.getD_eq_getElem?_getD,List.getElem?_map,
      List.getElem?_range hn,Option.map_some,Option.getD_some,laneAddr,
      BitVec.add_assoc,← BitVec.ofNat_add,show 8*(j/8)+j%8=j by omega]
  · have hw : ¬ j/8 < n := by omega
    have he : (List.range (8*n))[j]? = none := List.getElem?_eq_none (by rw [List.length_range]; omega)
    simp only [hw,ite_false,Spec.Sha3.bytesAt,
      List.getD_eq_getElem?_getD,List.getElem?_map,he,Option.map_none,Option.getD_none]
    exact BitVec.extractLsb'_zero

structure BlockKeep (s s' : VG.AArch64.State) : Prop where
  gpr : ∀ r, r ≠ .x17 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.block {s s' : VG.AArch64.State} (h : VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s s') : VG.Proof.Sha3.AArch64.Sha3.Vector.BlockKeep s s' :=
  ⟨fun r _ => congrFun h.gpr r,h.mem,h.rd,h.wr,h.sp⟩

theorem BlockKeep.trans {s t u : VG.AArch64.State} (h : VG.Proof.Sha3.AArch64.Sha3.Vector.BlockKeep s t) (k : VG.Proof.Sha3.AArch64.Sha3.Vector.BlockKeep t u) :
    VG.Proof.Sha3.AArch64.Sha3.Vector.BlockKeep s u := ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr),k.mem.trans h.mem,
      k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩

theorem state_not_temps : ∀ i < 25, vreg i ≠ .v25 ∧ vreg i ≠ .v26 := by decide

theorem absorbPair_ok (s : VG.AArch64.State) (i : Nat) (hi : i < 12)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (absorbPair i)) s fun s' => VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s s' ∧ ∀ j < 25,
      VG.Proof.Sha3.AArch64.Sha3.Vector.low s' (vreg j) = if j = 2*i+1 then VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg j) ^^^ s.mem.readW (laneAddr (s.gpr .x3) j) 64
        else if j = 2*i then VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg j) ^^^ s.mem.readW (laneAddr (s.gpr .x3) j) 64 else VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg j) := by
  unfold absorbPair
  refine WP.cons (VG.Proof.Sha3.AArch64.Sha3.Vector.exec_ldrq ⟨by omega,by omega⟩ hin)
    (WP.cons rfl (WP.cons rfl (WP.cons rfl (wp_nil ?_))))
  refine ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,fun j hj => ?_⟩
  have he := VG.Proof.Sha3.AArch64.Sha3.Vector.state_not_temps (2*i) (by omega)
  have ho := VG.Proof.Sha3.AArch64.Sha3.Vector.state_not_temps (2*i+1) (by omega)
  have hd : vreg (2*i+1) ≠ vreg (2*i) := by
    rw [ne_eq,VG.Proof.Sha3.AArch64.Sha3.Vector.vreg_inj _ (by omega) _ (by omega)]; omega
  have hde : vreg (2*i) ≠ vreg (2*i+1) := Ne.symm hd
  have hjt := VG.Proof.Sha3.AArch64.Sha3.Vector.state_not_temps j hj
  by_cases hjo : j = 2*i+1
  · subst j
    simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.low,RegUpd.v_setV,ho.1,ho.2,he.1,he.2,Ne.symm he.2,hd,reduceCtorEq,ite_true,ite_false,VG.Proof.Sha3.AArch64.Sha3.Vector.low_xor]
    rw [VG.Proof.Sha3.AArch64.Sha3.Vector.low_ext8,VG.Proof.Sha3.AArch64.Sha3.Vector.pair_high]
  · by_cases hje : j = 2*i
    · subst j
      simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.low,RegUpd.v_setV,ho.1,ho.2,he.1,he.2,hde,reduceCtorEq,hjo,
        ite_true,ite_false,VG.Proof.Sha3.AArch64.Sha3.Vector.low_xor]
      rw [VG.Proof.Sha3.AArch64.Sha3.Vector.pair_low]
    · have he' : vreg j ≠ vreg (2*i) := by rw [ne_eq,VG.Proof.Sha3.AArch64.Sha3.Vector.vreg_inj _ (by omega) _ (by omega)]; exact hje
      have ho' : vreg j ≠ vreg (2*i+1) := by rw [ne_eq,VG.Proof.Sha3.AArch64.Sha3.Vector.vreg_inj _ (by omega) _ (by omega)]; exact hjo
      simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.low,RegUpd.v_setV,he',ho',hjt.1,hjt.2,hjo,hje,ite_false]

theorem absorbWord_ok (s : VG.AArch64.State) (i : Nat) (hi : i < 25)
    (hin : InRegions (s.rd ++ s.wr) (laneAddr (s.gpr .x3) i) 8) :
    WP isa (.block (absorbWord i)) s fun s' => VG.Proof.Sha3.AArch64.Sha3.Vector.BlockKeep s s' ∧ ∀ j < 25,
      VG.Proof.Sha3.AArch64.Sha3.Vector.low s' (vreg j) = if j = i then VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg j) ^^^ s.mem.readW (laneAddr (s.gpr .x3) j) 64
        else VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg j) := by
  unfold absorbWord
  refine WP.cons (exec_ldr_x ⟨by omega,by omega⟩ hin) (WP.cons rfl (WP.cons rfl (wp_nil ?_)))
  refine ⟨⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩,fun j hj => ?_⟩
  · simp only [RegUpd.gpr_setV,RegUpd.gpr_write,hr,ite_false]
  · have hn := (VG.Proof.Sha3.AArch64.Sha3.Vector.state_not_temps i hi).1
    have hjn := (VG.Proof.Sha3.AArch64.Sha3.Vector.state_not_temps j hj).1
    by_cases he : j = i
    · subst j
      simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.low,RegUpd.v_setV,RegUpd.v_write,RegUpd.gpr_write_self,hn,ite_true,ite_false,
        Size.bits,BitVec.setWidth_eq,VG.Proof.Sha3.AArch64.Sha3.Vector.low_xor,vdword_ofVDwords_0]
    · have hr : vreg j ≠ vreg i := by rw [ne_eq,VG.Proof.Sha3.AArch64.Sha3.Vector.vreg_inj _ (by omega) _ (by omega)]; exact he
      simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.low,RegUpd.v_setV,RegUpd.v_write,hr,hjn,he,ite_false]

structure AbsorbInv (s₀ : VG.AArch64.State) (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s₀ s
  lanes : ∀ j < 25, VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg j) = if j < 2*k
    then VG.Proof.Sha3.AArch64.Sha3.Vector.low s₀ (vreg j) ^^^ s₀.mem.readW (laneAddr (s₀.gpr .x3) j) 64 else VG.Proof.Sha3.AArch64.Sha3.Vector.low s₀ (vreg j)

theorem absorbPairs_ok (s₀ : VG.AArch64.State) (k : Nat) (hk : k ≤ 12)
    (hin : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x3 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((List.range k).flatMap absorbPair)) s₀ (VG.Proof.Sha3.AArch64.Sha3.Vector.AbsorbInv s₀ k) := by
  refine wp_range_flatMap (M := isa) (VG.Proof.Sha3.AArch64.Sha3.Vector.AbsorbInv s₀) (fun i s hi hs => ?_) k (Nat.le_refl _) s₀
    ⟨Keep.refl _,fun _ _ => by simp only [Nat.mul_zero,Nat.not_lt_zero,ite_false]⟩
  refine (VG.Proof.Sha3.AArch64.Sha3.Vector.absorbPair_ok s i (by omega) (by rw [hs.keep.rd,hs.keep.wr,hs.keep.gpr]; exact hin i hi)).mono
    fun s' ⟨hp,ha⟩ => ⟨hs.keep.trans hp,fun j hj => ?_⟩
  rw [ha j hj,hs.lanes j hj,hs.keep.mem,hs.keep.gpr]
  by_cases ho : j = 2*i+1
  · subst j
    simp only [ite_true,show ¬2*i+1 < 2*i by omega,show 2*i+1 < 2*(i+1) by omega,ite_false]
  · by_cases he : j = 2*i
    · subst j
      simp only [ho,ite_false,ite_true,Nat.lt_irrefl,show 2*i < 2*(i+1) by omega]
    · have hjk : j < 2*i ↔ j < 2*(i+1) := by omega
      simp only [ho,he,ite_false,hjk]

theorem absorbWords_ok (s₀ : VG.AArch64.State) (A : Spec.Sha3.State) (hA : VG.Proof.Sha3.AArch64.Sha3.Vector.Lanes s₀ A)
    (n : Nat) (hn : n ≤ 25)
    (hin : Covers [⟨s₀.gpr .x3,8*n⟩] (s₀.rd ++ s₀.wr)) :
    WP isa (.block (absorbWords n)) s₀ fun s' => VG.Proof.Sha3.AArch64.Sha3.Vector.BlockKeep s₀ s' ∧
      VG.Proof.Sha3.AArch64.Sha3.Vector.Lanes s' (VG.Proof.Sha3.AArch64.Sha3.Vector.xorWords A s₀.mem (s₀.gpr .x3) n) := by
  rw [absorbWords,WP.block_append_iff]
  refine (VG.Proof.Sha3.AArch64.Sha3.Vector.absorbPairs_ok s₀ (n/2) (by omega) (fun i hi => ?_)).mono fun s hs => ?_
  · exact hin _ _ ⟨⟨s₀.gpr .x3,8*n⟩,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  · by_cases ho : n%2=1
    · simp only [ho,ite_true]
      refine (VG.Proof.Sha3.AArch64.Sha3.Vector.absorbWord_ok s (n-1) (by omega) ?_).mono fun s' ⟨hb,hl⟩ => ?_
      · rw [hs.keep.rd,hs.keep.wr,hs.keep.gpr]
        exact hin _ _ ⟨⟨s₀.gpr .x3,8*n⟩,by simp,Offset.contains_base _ (by omega) (by omega)⟩
      · refine ⟨hs.keep.block.trans hb,fun j hj => ?_⟩
        rw [hl j hj,hs.lanes j hj,hs.keep.mem,hs.keep.gpr]
        rw [VG.Proof.Sha3.AArch64.Sha3.Vector.xorWords_get, hA j hj]
        by_cases he : j = n-1
        · subst j
          simp only [ite_true,show ¬n-1 < 2*(n/2) by omega,show n-1 < n by omega,ite_false]
        · have hjn : j < 2*(n/2) ↔ j < n := by omega
          simp only [he,ite_false,hjn]
          by_cases hjn' : j < n
          · simp only [hjn',ite_true]
          · simp only [hjn',ite_false]; exact BitVec.xor_zero.symm
    · simp only [ho,ite_false]
      refine wp_nil ⟨hs.keep.block,fun j hj => ?_⟩
      rw [hs.lanes j hj,show 2*(n/2)=n by omega,hA j hj]
      rw [VG.Proof.Sha3.AArch64.Sha3.Vector.xorWords_get]
      by_cases hjn : j < n
      · simp only [hjn,ite_true]
      · simp only [hjn,ite_false]; exact BitVec.xor_zero.symm

/-- XOR one complete rate block without serializing the SIMD state. -/
theorem absorbBlock_ok (s : VG.AArch64.State) (A : Spec.Sha3.State) (hA : VG.Proof.Sha3.AArch64.Sha3.Vector.Lanes s A)
    (rate : Nat) (hr : rate ∈ Spec.Sha3.rates)
    (hin : Covers [⟨s.gpr .x3,rate⟩] (s.rd ++ s.wr)) :
    WP isa (.block (absorbBlock rate)) s fun s' => VG.Proof.Sha3.AArch64.Sha3.Vector.BlockKeep s s' ∧
      VG.Proof.Sha3.AArch64.Sha3.Vector.Lanes s' (Spec.Sha3.xorBytes A (Spec.Sha3.bytesAt s.mem (s.gpr .x3) rate)) := by
  have hb : rate/8 ≤ 25 ∧ 8*(rate/8)=rate := by
    simp only [Spec.Sha3.rates,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  refine (VG.Proof.Sha3.AArch64.Sha3.Vector.absorbWords_ok s A hA (rate/8) hb.1 ?_).mono fun s' h => ⟨h.1,?_⟩
  · rwa [hb.2]
  · simpa only [VG.Proof.Sha3.AArch64.Sha3.Vector.xorWords_eq,hb.2] using h.2

#assert_standard_axioms VG.Proof.Sha3.AArch64.Sha3.Vector.absorbBlock_ok

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit`. -/
section

namespace VG.Impl.Sha3.AArch64.Sha3.Vector
materialize_code VG.Impl.Sha3.AArch64.Sha3.Vector.permute
end VG.Impl.Sha3.AArch64.Sha3.Vector

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Save`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector

structure SaveInv (s₀ : VG.AArch64.State) (k : Nat) (s : VG.AArch64.State) : Prop where
  ptr : VG.Proof.Sha3.AArch64.Sha3.Vector.Ptrs s₀ s
  vec : s.v = s₀.v
  frame : Frame [⟨s₀.gpr .x1,512⟩] s₀.mem s.mem
  vals : ∀ i < k, s.mem.read (s₀.gpr .x1 + BitVec.ofNat 64 (16*i)) 16 = s₀.v (vreg (8+i))

theorem save_ok (s₀ : VG.AArch64.State) (hp : Pre s₀) :
    WP isa (.block save) s₀ fun s' =>
      VG.Proof.Sha3.AArch64.Sha3.Vector.Ptrs s₀ s' ∧ s'.v = s₀.v ∧ Frame [⟨s₀.gpr .x1,512⟩] s₀.mem s'.mem ∧ VG.Proof.Sha3.AArch64.Sha3.Vector.Saved s₀ s'.mem := by
  have hh : WP isa (.block save) s₀ (VG.Proof.Sha3.AArch64.Sha3.Vector.SaveInv s₀ 8) := by
    refine wp_range_flatMap (M := isa) (VG.Proof.Sha3.AArch64.Sha3.Vector.SaveInv s₀) (fun i s hi hs => ?_)
      8 (Nat.le_refl _) s₀ ⟨Ptrs.refl _,rfl,Frame.refl _ _,fun _ h => absurd h (by omega)⟩
    unfold saveReg
    refine WP.cons (VG.Proof.Sha3.AArch64.Sha3.Vector.exec_strq ⟨by omega,by omega⟩ ?_) (wp_nil ?_)
    · rw [hs.ptr.wr,hs.ptr.x1]
      exact hp.in_wr (.inr rfl) (VG.Proof.Sha3.AArch64.Sha3.Vector.scratch_contains s₀ hi)
    · refine ⟨⟨hs.ptr.x0,hs.ptr.x1,hs.ptr.rd,hs.ptr.wr,hs.ptr.sp⟩,hs.vec,?_,fun j hj => ?_⟩
      · change Frame _ _ (s.mem.write _ 16 _)
        rw [hs.ptr.x1]
        exact hs.frame.write (by simp) _ (VG.Proof.Sha3.AArch64.Sha3.Vector.scratch_contains s₀ hi)
      · change (s.mem.write _ 16 _).read _ 16 = _
        rw [hs.ptr.x1,hs.vec]
        by_cases he : j = i
        · subst j
          exact VG.Proof.Sha3.AArch64.Sha3.Vector.read_write16 _ _ _
        · rw [Mem.read_write_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
          exact hs.vals j (by omega)
  exact hh.mono fun s' h => ⟨h.ptr,h.vec,h.frame,h.vals⟩

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Store`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3 (laneAddr lane_contains lane_sep)

theorem zip1_pair (a b : BitVec 128) :
    VPermOp.eval .zip1 .d2 a b = ofVDwords (vdword a 0) (vdword b 0) := by
  simp [VPermOp.eval,VArr.lanes,VArr.ofLanes]

structure StoreKeep (s s' : VG.AArch64.State) : Prop where
  ptr : VG.Proof.Sha3.AArch64.Sha3.Vector.Ptrs s s'
  lanes : ∀ j < 25, VG.Proof.Sha3.AArch64.Sha3.Vector.low s' (vreg j) = VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg j)

theorem StoreKeep.refl (s : VG.AArch64.State) : VG.Proof.Sha3.AArch64.Sha3.Vector.StoreKeep s s := ⟨Ptrs.refl _,fun _ _ => rfl⟩
theorem StoreKeep.trans {s t u : VG.AArch64.State} (h : VG.Proof.Sha3.AArch64.Sha3.Vector.StoreKeep s t) (k : VG.Proof.Sha3.AArch64.Sha3.Vector.StoreKeep t u) : VG.Proof.Sha3.AArch64.Sha3.Vector.StoreKeep s u :=
  ⟨h.ptr.trans k.ptr,fun j hj => (k.lanes j hj).trans (h.lanes j hj)⟩

theorem storePair_ok (s : VG.AArch64.State) (i : Nat) (hi : i < 12)
    (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (storePair i)) s fun s' => VG.Proof.Sha3.AArch64.Sha3.Vector.StoreKeep s s' ∧
      s'.mem = s.mem.write (s.gpr .x0 + BitVec.ofNat 64 (16*i)) 16
        (ofVDwords (VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg (2*i))) (VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg (2*i+1)))) := by
  unfold storePair
  refine WP.cons (s' := s.setV .v25 (ofVDwords (VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg (2*i))) (VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg (2*i+1)))))
    ?_ (WP.cons (VG.Proof.Sha3.AArch64.Sha3.Vector.exec_strq ⟨by omega,by omega⟩ hout) (wp_nil ?_))
  · simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.exec_vop,VOp.eval,VG.Proof.Sha3.AArch64.Sha3.Vector.zip1_pair,Option.map_some,VG.Proof.Sha3.AArch64.Sha3.Vector.low]
  · refine ⟨⟨⟨rfl,rfl,rfl,rfl,rfl⟩,fun j hj => ?_⟩,?_⟩
    · change VG.Proof.Sha3.AArch64.Sha3.Vector.low (s.setV .v25 _) (vreg j) = _
      rw [VG.Proof.Sha3.AArch64.Sha3.Vector.low_setV]
      have hn : vreg j ≠ .v25 := (show ∀ j < 25, vreg j ≠ .v25 by decide) j hj
      simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.put,hn,ite_false]
    · simp only [RegUpd.gpr_setV,RegUpd.mem_setV,RegUpd.v_setV_self]

structure StoreInv (s₀ : VG.AArch64.State) (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : VG.Proof.Sha3.AArch64.Sha3.Vector.StoreKeep s₀ s
  frame : Frame [⟨s₀.gpr .x0,200⟩] s₀.mem s.mem
  vals : ∀ j < 2*k, s.mem.readW (laneAddr (s₀.gpr .x0) j) 64 = VG.Proof.Sha3.AArch64.Sha3.Vector.low s₀ (vreg j)

theorem storePairs_ok (s₀ : VG.AArch64.State)
    (hout : ∀ i < 12, InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((List.range 12).flatMap storePair)) s₀ (VG.Proof.Sha3.AArch64.Sha3.Vector.StoreInv s₀ 12) := by
  refine wp_range_flatMap (M := isa) (VG.Proof.Sha3.AArch64.Sha3.Vector.StoreInv s₀) (fun i s hi hs => ?_)
    12 (Nat.le_refl _) s₀ ⟨StoreKeep.refl _,Frame.refl _ _,fun _ h => absurd h (by omega)⟩
  refine (VG.Proof.Sha3.AArch64.Sha3.Vector.storePair_ok s i hi (by rw [hs.keep.ptr.wr,hs.keep.ptr.x0]; exact hout i hi)).mono
    fun s' ⟨hk,hm⟩ => ⟨hs.keep.trans hk,?_,fun j hj => ?_⟩
  · rw [hm,hs.keep.ptr.x0]
    exact hs.frame.write (by simp) _ (VG.Proof.Sha3.AArch64.Sha3.Vector.state_pair_contains s₀ hi)
  · rw [hm,hs.keep.ptr.x0,write16_dwords]
    have he : s₀.gpr .x0 + BitVec.ofNat 64 (16*i) = laneAddr (s₀.gpr .x0) (2*i) := by
      simp only [laneAddr,show 8*(2*i)=16*i by omega]
    have ho : s₀.gpr .x0 + BitVec.ofNat 64 (16*i) + BitVec.ofNat 64 8 = laneAddr (s₀.gpr .x0) (2*i+1) := by
      simp only [laneAddr,BitVec.add_assoc,← BitVec.ofNat_add,show 16*i+8=8*(2*i+1) by omega]
    rw [ho,he]
    by_cases hodd : j = 2*i+1
    · subst j
      rw [Mem.readW_writeW_self64,hs.keep.lanes _ (by omega)]
    · rw [Mem.readW_writeW_sep (lane_sep _ (by omega) (by omega) hodd) (by decide)]
      by_cases heven : j = 2*i
      · subst j
        rw [Mem.readW_writeW_self64,hs.keep.lanes _ (by omega)]
      · rw [Mem.readW_writeW_sep (lane_sep _ (by omega) (by omega) heven) (by decide)]
        exact hs.vals j (by omega)

theorem store_ok (s₀ : VG.AArch64.State) (A : Spec.Sha3.State) (hA : VG.Proof.Sha3.AArch64.Sha3.Vector.Lanes s₀ A)
    (hout : ∀ i < 12, InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 (16*i)) 16)
    (hlast : InRegions s₀.wr (laneAddr (s₀.gpr .x0) 24) 8) :
    WP isa (.block store) s₀ fun s' => VG.Proof.Sha3.AArch64.Sha3.Vector.Ptrs s₀ s' ∧
      Frame [⟨s₀.gpr .x0,200⟩] s₀.mem s'.mem ∧ Spec.Sha3.stateAt s'.mem (s₀.gpr .x0) = A := by
  rw [store,WP.block_append_iff]
  refine (VG.Proof.Sha3.AArch64.Sha3.Vector.storePairs_ok s₀ hout).mono fun s hs => ?_
  unfold storeLast
  refine WP.cons (VG.Proof.Sha3.AArch64.Sha3.Vector.exec_umov_low s .x17 .v24) (WP.cons (exec_str_x (by decide) ?_) (wp_nil ?_))
  · simpa only [reduceCtorEq, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, BitVec.reduceEq, ite_true, not_false_eq_true, not_true_eq_false, Bool.not_true, Bool.not_false, and_self, false_implies, implies_true, Nat.reduceBEq, Nat.reduceBNe, decide_true, decide_false, BitVec.reduceSignExtend, RegUpd.gpr_write,RegUpd.wr_write,ite_false,
      hs.keep.ptr.wr,hs.keep.ptr.x0] using hlast
  · refine ⟨?_,?_,?_⟩
    · constructor <;> simp only [reduceCtorEq, ↓reduceIte, RegUpd.gpr_write,
        RegUpd.rd_write,RegUpd.wr_write,RegUpd.sp_write,
        hs.keep.ptr.x0,hs.keep.ptr.x1,hs.keep.ptr.rd,hs.keep.ptr.wr,hs.keep.ptr.sp]
    · change Frame _ _ ((s.write .x .x17 _).mem.writeW _ ((s.write .x .x17 _).gpr .x17))
      simp only [reduceCtorEq, ↓reduceIte, RegUpd.mem_write,RegUpd.gpr_write,
        Size.bits,BitVec.setWidth_eq,hs.keep.ptr.x0]
      change Frame [⟨s₀.gpr .x0,200⟩] s₀.mem
        (s.mem.writeW (laneAddr (s₀.gpr .x0) 24) (VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg 24)))
      exact hs.frame.writeW (r := ⟨s₀.gpr .x0,200⟩) (by simp) (VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg 24))
        (lane_contains (s₀.gpr .x0) (by decide : 24 < 25))
    · apply Vector.ext
      intro j hj
      simp only [reduceCtorEq, ↓reduceIte, Spec.Sha3.stateAt,Vector.getElem_ofFn,
        RegUpd.mem_write,RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,hs.keep.ptr.x0]
      change (s.mem.writeW (laneAddr (s₀.gpr .x0) 24) (VG.Proof.Sha3.AArch64.Sha3.Vector.low s (vreg 24))).readW _ 64 = A[j]
      by_cases he : j = 24
      · subst j
        rw [Mem.readW_writeW_self64,hs.keep.lanes 24 (by decide)]
        exact hA 24 (by decide)
      · rw [Mem.readW_writeW_sep (lane_sep _ hj (by decide) he) (by decide),hs.vals j (by omega)]
        exact hA j hj

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Restore`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector

structure RestoreInv (orig s₀ : VG.AArch64.State) (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s₀ s
  vals : ∀ i < k, s.v (vreg (8+i)) = orig.v (vreg (8+i))

theorem restore_ok (orig s₀ : VG.AArch64.State) (hs : VG.Proof.Sha3.AArch64.Sha3.Vector.Saved orig s₀.mem)
    (hptr : s₀.gpr .x1 = orig.gpr .x1)
    (hin : ∀ i < 8, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x1 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block restore) s₀ fun s' => VG.Proof.Sha3.AArch64.Sha3.Vector.Keep s₀ s' ∧
      ∀ r ∈ VG.AArch64.preservedV, (s'.v r).extractLsb' 0 64 = (orig.v r).extractLsb' 0 64 := by
  have hh : WP isa (.block restore) s₀ (VG.Proof.Sha3.AArch64.Sha3.Vector.RestoreInv orig s₀ 8) := by
    refine wp_range_flatMap (M := isa) (VG.Proof.Sha3.AArch64.Sha3.Vector.RestoreInv orig s₀) (fun i s hi hr => ?_)
      8 (Nat.le_refl _) s₀ ⟨Keep.refl _,fun _ h => absurd h (by omega)⟩
    unfold restoreReg
    refine WP.cons (VG.Proof.Sha3.AArch64.Sha3.Vector.exec_ldrq ⟨by omega,by omega⟩ ?_) (wp_nil ?_)
    · rw [hr.keep.rd,hr.keep.wr,hr.keep.gpr]
      exact hin i hi
    · refine ⟨hr.keep.trans ⟨rfl,rfl,rfl,rfl,rfl⟩,fun j hj => ?_⟩
      rw [RegUpd.v_setV]
      simp only [VG.Proof.Sha3.AArch64.Sha3.Vector.vreg_inj (8+j) (by omega) (8+i) (by omega),Nat.add_left_cancel_iff]
      by_cases he : j = i
      · subst j
        simp only [ite_true,hr.keep.mem,hr.keep.gpr,hptr]
        exact hs i hi
      · rw [ite_eq_right (by omega)]
        exact hr.vals j (by omega)
  refine hh.mono fun s' h => ⟨h.keep,fun r hr => ?_⟩
  have hv : ∀ r ∈ VG.AArch64.preservedV, ∃ i : Fin 8, r = vreg (8+i.val) := by decide
  obtain ⟨i,rfl⟩ := hv r hr
  exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (h.vals i.val i.isLt)

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Permute`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Spec.Sha3 (stateAt keccakF)

/-- Saves do not alter the disjoint 200-byte Keccak state. -/
theorem state_frame (s₀ s : VG.AArch64.State) (hp : Pre s₀) (hptr : s.gpr .x0 = s₀.gpr .x0)
    (hf : Frame [⟨s₀.gpr .x1,512⟩] s₀.mem s.mem) :
    stateAt s.mem (s.gpr .x0) = stateAt s₀.mem (s₀.gpr .x0) := by
  rw [hptr]
  apply Vector.ext
  intro i hi
  simp only [stateAt,Vector.getElem_ofFn]
  exact hf.readW (VG.Proof.Sha3.lane_contains _ hi) (by simpa using hp.st_scr) (by decide)

theorem correct (s₀ : VG.AArch64.State) (hp : Pre s₀) :
    WP isa permute s₀ fun s' => s'.sp = s₀.sp ∧
      (∀ r ∈ VG.AArch64.preservedV, (s'.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) ∧
      VG.Proof.Sha3.permuteAArch64.post s₀ s' := by
  unfold permute
  rw [WP.block_append_iff,WP.block_append_iff,WP.block_append_iff,WP.block_append_iff]
  refine (VG.Proof.Sha3.AArch64.Sha3.Vector.save_ok s₀ hp).mono fun s₁ h₁ => ?_
  refine (VG.Proof.Sha3.AArch64.Sha3.Vector.load_ok s₁ (fun i hi => ?_) ?_).mono fun s₂ h₂ => ?_
  · rw [h₁.1.rd,h₁.1.wr,h₁.1.x0]
    exact hp.in_all (hp.in_wr (.inl rfl) (VG.Proof.Sha3.AArch64.Sha3.Vector.state_pair_contains s₀ hi))
  · rw [h₁.1.rd,h₁.1.wr,h₁.1.x0]
    exact hp.in_all (hp.lane_in (.inl rfl) (by decide : 24 < 25))
  · have ha : VG.Proof.Sha3.AArch64.Sha3.Vector.Lanes s₂ (stateAt s₀.mem (s₀.gpr .x0)) := by
      rw [VG.Proof.Sha3.AArch64.Sha3.Vector.state_frame s₀ s₁ hp h₁.1.x0 h₁.2.2.1] at h₂
      exact h₂.2.2
    refine (VG.Proof.Sha3.AArch64.Sha3.Vector.rounds_ok s₂ _ ha).mono fun s₃ h₃ => ?_
    have p₃ := h₁.1.trans (h₂.1.trans h₃.1.ptrs)
    have m₃ : s₃.mem = s₁.mem := h₃.1.mem.trans h₂.2.1
    refine (VG.Proof.Sha3.AArch64.Sha3.Vector.store_ok s₃ _ h₃.2 (fun i hi => ?_) ?_).mono fun s₄ h₄ => ?_
    · rw [p₃.wr,p₃.x0]
      exact hp.in_wr (.inl rfl) (VG.Proof.Sha3.AArch64.Sha3.Vector.state_pair_contains s₀ hi)
    · rw [p₃.wr,p₃.x0]
      exact hp.lane_in (.inl rfl) (by decide : 24 < 25)
    · have p₄ := p₃.trans h₄.1
      have hs₄ : VG.Proof.Sha3.AArch64.Sha3.Vector.Saved s₀ s₄.mem := by
        intro i hi
        rw [h₄.2.1.read (VG.Proof.Sha3.AArch64.Sha3.Vector.scratch_contains s₀ hi) ?_ (by decide),m₃]
        · exact h₁.2.2.2 i hi
        · simpa only [List.mem_singleton,p₃.x0,forall_eq] using hp.st_scr.symm
      refine (VG.Proof.Sha3.AArch64.Sha3.Vector.restore_ok s₀ s₄ hs₄ p₄.x1 (fun i hi => ?_)).mono fun s' h₅ => ?_
      · rw [p₄.rd,p₄.wr,p₄.x1]
        exact hp.in_all (hp.in_wr (.inr rfl) (VG.Proof.Sha3.AArch64.Sha3.Vector.scratch_contains s₀ hi))
      · refine ⟨h₅.1.sp.trans p₄.sp,h₅.2,?_⟩
        change stateAt s'.mem (s₀.gpr .x0) = _
        rw [h₅.1.mem]
        simpa only [p₃.x0] using h₄.2.2

theorem permute_preserved : ∀ r ∈ preserved, ∀ i ∈ instrs permute, dstOf i ≠ some r := by
  have h : ((instrs permute).all fun i => preserved.all fun r => dstOf i != some r) = true := by
    rw [← Code.allInstrs_eq]
    lit_decide
  intro r hr i hi
  have hh := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using hh

theorem permute_noCalls : permute.noCalls = true := by lit_decide
theorem permute_noFrames : permute.noFrames = true := by lit_decide

theorem permute_correct (s : VG.AArch64.State) (hs : VG.Proof.Sha3.permuteAArch64.pre s) :
    ∃ t s', Exec isa permute s t s' ∧ abiPreserved s s' ∧ VG.Proof.Sha3.permuteAArch64.post s s' := by
  obtain ⟨t,s',he,hsp,hv,hpost⟩ := VG.Proof.Sha3.AArch64.Sha3.Vector.correct s (pre_of s hs)
  exact ⟨t,s',he,⟨fun r hr => Exec.gpr (VG.Proof.Sha3.AArch64.Sha3.Vector.permute_preserved r hr) he (.inl VG.Proof.Sha3.AArch64.Sha3.Vector.permute_noCalls),hsp,hv⟩,hpost⟩

theorem permute_ct : ConstantTime isa VG.Proof.Sha3.permuteAArch64.pre VG.Proof.Sha3.permuteAArch64.pub permute := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1,h2,hsp⟩
  refine ⟨hsp,fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;> with_reducible assumption

theorem permute_verified :
    Verified AArch64.target permute (Spec.Sha3.permuteContract AArch64.abi) :=
  Verified.of_correct VG.Proof.Sha3.AArch64.Sha3.Vector.permute_correct VG.Proof.Sha3.AArch64.Sha3.Vector.permute_ct (by
    sig_implies [Spec.Sha3.permuteContract,Spec.Sha3.permuteSig,VG.Proof.Sha3.permuteAArch64,
      AArch64.abi,AArch64.argRegs] [VG.Proof.Sha3.AArch64.satState] using VG.Proof.Sha3.AArch64.satState)

/-- Core and boundary instructions, excluding the emitted return. -/
theorem permute_instruction_count : (instrs permute).length = 1723 := by lit_decide

#assert_standard_axioms VG.Proof.Sha3.AArch64.Sha3.Vector.permute_verified

end VG.Proof.Sha3.AArch64.Sha3.Vector

end
