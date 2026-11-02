module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.Arith
public import VerifiedGarbage.Proof.MlDsa.Round.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.Arith
meta import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# ML-DSA on RISCV64: `vg_mldsa_power2round`

One symbolic execution of the loop body, for any pointers (`body_ok`), which
writes `(a + 4095) >> 13` to `t1` and `((a + 4095) mod 2¹³) - 4095`, plus
`q` if negative, to `t0` (`p2r1_val`, `p2r0_val`, through
`power2Round_eq`); the loop invariant says which coefficients are done
(`Inv`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Round.Power2Round

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Round
open VG.Impl.MlKem.RISCV64 (fixup)
open VG.Impl.MlDsa.RISCV64.Arith (loadImm)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_writeW polyAt_val polyIs_of_toNat natPolyIs_of_toNat
  map_get coeffAt_frame power2Round_eq power2Round_t0 reduced_zero)
open VG.Proof.MlDsa.RISCV64.Round
open VG.Proof.MlDsa.RISCV64.Arith (loadImm_q)
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_succ align4_add)

/-! ## Values -/

theorem p2r1_val {a : BitVec 64} (ha : a.toNat < q) :
    ((a + 4095) >>> 13).toNat = (a.toNat + 4095) / 8192 := by
  rw [VG.Proof.MlDsa.Round.q_eq] at ha
  bv_omega

/-- What `power2Round` leaves for `t0`, before `fixup`. -/
def p2rLow (a : BitVec 64) : BitVec 64 :=
  a + (4095 : BitVec 64) - ((a + (4095 : BitVec 64)) >>> 13) <<< 13 - (4095 : BitVec 64)

theorem p2r0_val {a : BitVec 64} (ha : a.toNat < q) :
    (fixk 8380417 (p2rLow a)).toNat =
      if (a.toNat + 4095) % 8192 < 4095 then (a.toNat + 4095) % 8192 + q - 4095
      else (a.toNat + 4095) % 8192 - 4095 := by
  rw [VG.Proof.MlDsa.Round.q_eq] at ha ⊢
  have t : (4095 : BitVec 64).toNat = 4095 := by simp
  have h1 : (a + 4095).toNat = a.toNat + 4095 := by rw [BitVec.toNat_add, t]; omega
  have h2 : ((a + 4095) >>> 13 <<< 13).toNat = (a.toNat + 4095) / 8192 * 8192 := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, h1, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega)
  have hx : (a + (4095 : BitVec 64) - ((a + (4095 : BitVec 64)) >>> 13) <<< 13).toNat = (a.toNat + 4095) % 8192 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1, h2]; omega), h1, h2]; omega
  have := fixk_diff (k := 8380417) (by decide)
    (a := a + (4095 : BitVec 64) - ((a + (4095 : BitVec 64)) >>> 13) <<< 13) (b := 4095)
    (by rw [hx]; omega) (by rw [hx, t]; exact Nat.le_add_left _ _) (by rw [t]; decide)
  rw [hx, t] at this
  exact this

/-! ## The loop body -/

/-- What an iteration does, for the values stored. -/
def Step (s : State) (x y z c : BitVec 64) (v w : BitVec 32) (s' : State) : Prop :=
  s'.gpr .a0 = x + 4 ∧ s'.gpr .a1 = y + 4 ∧ s'.gpr .a2 = z + 4 ∧ s'.gpr .a3 = c - 1 ∧
    s'.gpr .a4 = s.gpr .a4 ∧ s'.gpr .t2 = s.gpr .t2 ∧
    s'.mem = (s.mem.writeW y v).writeW z w ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
    s'.gpr .ra = s.gpr .ra ∧
    ∀ r ∈ preserved, s'.gpr r = s.gpr r

section
variable {s : State} {x y z c : BitVec 64} (h3 : s.gpr .a0 = x) (h4 : s.gpr .a1 = y) (h5 : s.gpr .a2 = z)
  (h6 : s.gpr .a3 = c) (h7 : s.gpr .a4 = 8380417) (h12 : s.gpr .t2 = 4095)
  (ia : InRegions (s.rd ++ s.wr) x 4) (ob : InRegions s.wr y 4) (oc : InRegions s.wr z 4)
  (ax : x.toNat % 4 = 0) (ay : y.toNat % 4 = 0) (az : z.toNat % 4 = 0)
include h3 h4 h5 h6 h7 h12 ia ob oc ax ay az

theorem body_ok :
    WP isa (.block p2rBody) s (Step s x y z c
      ((((s.mem.readW x 32).setWidth 64 + 4095) >>> 13).setWidth 32)
      ((fixk 8380417 (p2rLow ((s.mem.readW x 32).setWidth 64))).setWidth 32)) := by
  crun [p2rBody, fixup, Step, fixk, p2rLow, h3, h4, h5, h6, h7, h12, ia, ob, oc, ax, ay, az, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev T : Addr := s₀.gpr .a0
abbrev T1 : Addr := s₀.gpr .a1
abbrev T0 : Addr := s₀.gpr .a2

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [pR (T s₀)]
  wr : s₀.wr = [pR (T1 s₀), pR (T0 s₀)]
  dt1 : (pR (T s₀)).Disjoint (pR (T1 s₀))
  dt0 : (pR (T s₀)).Disjoint (pR (T0 s₀))
  d01 : (pR (T1 s₀)).Disjoint (pR (T0 s₀))
  fit : (T s₀).toNat + 1024 ≤ 2 ^ 64
  fit1 : (T1 s₀).toNat + 1024 ≤ 2 ^ 64
  fit0 : (T0 s₀).toNat + 1024 ≤ 2 ^ 64
  red : Reduced s₀.mem (T s₀)
  al : (T s₀).toNat % 4 = 0
  al1 : (T1 s₀).toNat % 4 = 0
  al0 : (T0 s₀).toNat % 4 = 0

/-- After `i` iterations, writing `o1 j` and `o0 j` to coefficient `j` of
`t1` and `t0`. -/
structure Inv (o1 o0 : Nat → BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .a0 = T s₀ + BitVec.ofNat 64 (4 * i)
  r4 : s.gpr .a1 = T1 s₀ + BitVec.ofNat 64 (4 * i)
  r5 : s.gpr .a2 = T0 s₀ + BitVec.ofNat 64 (4 * i)
  r6 : s.gpr .a3 = BitVec.ofNat 64 (256 - i)
  r7 : s.gpr .a4 = 8380417
  r12 : s.gpr .t2 = 4095
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.gpr .ra = s₀.gpr .ra
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [pR (T1 s₀), pR (T0 s₀)] s₀.mem s.mem
  c1 : ∀ j < 256, j < i → coeffAt s.mem (T1 s₀) j = o1 j
  c0 : ∀ j < 256, j < i → coeffAt s.mem (T0 s₀) j = o0 j

/-- The coefficient of `t` an iteration reads is as on entry. -/
theorem read_t {o1 o0 : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {s : State}
    (h : Inv o1 o0 s₀ i s) : s.mem.readW (T s₀ + BitVec.ofNat 64 (4 * i)) 32 = coeffAt s₀.mem (T s₀) i :=
  coeffAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dt1
    · exact hp.dt0) hi

theorem inv_step {o1 o0 : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256)
    {s : State} (h : Inv o1 o0 s₀ i s)
    (hv : ∀ {a : BitVec 64}, a = (coeffAt s₀.mem (T s₀) i).setWidth 64 →
      ((a + 4095) >>> 13).setWidth 32 = o1 i ∧ (fixk 8380417 (p2rLow a)).setWidth 32 = o0 i) :
    WP isa (.block p2rBody) s fun s' => Inv o1 o0 s₀ (i + 1) s' ∧ (s'.gpr .a3 != 0) = decide (i + 1 ≠ 256) := by
  have cT := coeff_contains (T s₀) (i := i) hi
  have c1 := coeff_contains (T1 s₀) (i := i) hi
  have c0 := coeff_contains (T0 s₀) (i := i) hi
  obtain ⟨v1, v0⟩ := hv (a := (s.mem.readW (T s₀ + BitVec.ofNat 64 (4 * i)) 32).setWidth 64)
    (by rw [read_t hp hi h])
  refine WP.mono (body_ok h.r3 h.r4 h.r5 h.r6 h.r7 h.r12 ?_ ?_ ?_ (align4_add hp.al i) (align4_add hp.al1 i)
    (align4_add hp.al0 i))
    fun s' ⟨r3, r4, r5, r6, r7, r12, m, rd, wr, sp, lr, pres⟩ => ⟨⟨?_, ?_, ?_, ?_,
    r7.trans h.r7, r12.trans h.r12, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, lr.trans h.lr,
    fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_, ?_⟩, ?_⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cT⟩
  · rw [h.wr, hp.wr]; exact ⟨_, by simp, c1⟩
  · rw [h.wr, hp.wr]; exact ⟨pR (T0 s₀), by simp, c0⟩
  · rw [r3]; exact ptr_succ _ 4 i
  · rw [r4]; exact ptr_succ _ 4 i
  · rw [r5]; exact ptr_succ _ 4 i
  · rw [r6]; exact count_sub hi
  · rw [m]
    exact (h.frame.writeW (List.mem_cons_self ..) _ c1).writeW (by simp) _ c0
  · intro j hj hji
    have dj : (pR (T1 s₀)).Disjoint (pR (T0 s₀)) := hp.d01
    rw [m, show T1 s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (T1 s₀) i from rfl,
      show T0 s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (T0 s₀) i from rfl,
      VG.Proof.MlDsa.Round.coeffAt_writeW_disjoint _ (hp.d01) (coeff_contains _ hi) (i := j) (by omega),
      coeffAt_writeW _ _ hj hi]
    by_cases e : i = j
    · subst e; rw [ite_eq_left rfl, v1]
    · rw [ite_eq_right e]; exact h.c1 j hj (by omega)
  · intro j hj hji
    rw [m, show T0 s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (T0 s₀) i from rfl,
      coeffAt_writeW _ _ hj hi]
    by_cases e : i = j
    · subst e; rw [ite_eq_left rfl, v0]
    · rw [ite_eq_right e, VG.Proof.MlDsa.Round.coeffAt_writeW_disjoint _ hp.d01.symm (coeff_contains _ hi)
        (i := j) (by omega)]
      exact h.c0 j hj (by omega)
  · rw [r6, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]; exact count_nz hi (by decide)

theorem loop_ok {o1 o0 : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀)
    (hv : ∀ i < 256, ∀ {a : BitVec 64}, a = (coeffAt s₀.mem (T s₀) i).setWidth 64 →
      ((a + 4095) >>> 13).setWidth 32 = o1 i ∧ (fixk 8380417 (p2rLow a)).setWidth 32 = o0 i) :
    WP isa power2Round s₀ (Inv o1 o0 s₀ 256) := by
  refine WP.seq ?_
  simp only [loadQ, loadImm_q, loadImm_4095, List.cons_append, List.nil_append]
  crun []
  refine wp_loop_nz (Inv o1 o0 s₀) (N := 256) (by decide)
    (fun i hi s h => inv_step hp hi h (hv i hi)) (fun _ h => h) ?_
  refine ⟨by simp, by simp, by simp, by simp, by simp; decide, by simp; decide,
    rfl, rfl, rfl, by simp, fun r hr => ?_, Frame.refl _ _, fun j _ h => absurd h (by omega),
    fun j _ h => absurd h (by omega)⟩
  have : r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .t2 := by revert r hr; decide
  simp [this.1, this.2.1, this.2.2]

/-! ## Correctness -/

/-- The values stored. -/
def o1 (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (((polyAt s₀.mem (T s₀)).map fun c => (power2Round c).1.toNat)[j]!)

def o0 (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (((polyAt s₀.mem (T s₀)).map fun c => ofInt (power2Round c).2)[j]!).val

theorem vals {s₀ : State} (hp : Pre s₀) : ∀ i < 256, ∀ {a : BitVec 64}, a = (coeffAt s₀.mem (T s₀) i).setWidth 64 →
    ((a + 4095) >>> 13).setWidth 32 = o1 s₀ i ∧ (fixk 8380417 (p2rLow a)).setWidth 32 = o0 s₀ i := by
  intro i hi a ha
  have hr := hp.red i hi
  have hat : a.toNat = (coeffAt s₀.mem (T s₀) i).toNat := by
    rw [ha, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (coeffAt s₀.mem (T s₀) i).isLt; omega)
  have hpv := polyAt_val hp.red (i := i) hi
  have hq : a.toNat < q := by rw [hat]; exact hr
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, p2r1_val hq, o1, map_get _ _ hi, power2Round_eq, hpv, ← hat, BitVec.toNat_ofNat]
    simp only [Int.toNat_natCast]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, p2r0_val hq, o0, map_get _ _ hi, power2Round_t0, hpv, ← hat, BitVec.toNat_ofNat]

theorem o1_toNat (s₀ : State) {j : Nat} (hj : j < 256) :
    (o1 s₀ j).toNat = ((polyAt s₀.mem (T s₀)).map fun c => (power2Round c).1.toNat)[j]! := by
  rw [o1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  rw [map_get _ _ hj, power2Round_eq]
  simp only [Int.toNat_natCast]
  have : ((polyAt s₀.mem (T s₀))[j]!).val < 8380417 := Fin.isLt _
  omega

theorem o0_toNat (s₀ : State) {j : Nat} :
    (o0 s₀ j).toNat = (((polyAt s₀.mem (T s₀)).map fun c => ofInt (power2Round c).2)[j]!).val := by
  rw [o0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.lt_trans (Fin.isLt _) (by decide)

theorem pre_of {s : State} (h : (Proof.MlDsa.power2RoundContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]

theorem verified : Verified RISCV64.target power2Round (Proof.MlDsa.power2RoundContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.RISCV64.Add.ctRegs [.a0, .a1, .a2] (fun s₁ s₂ h => ?_)
    (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := loop_ok hp (vals hp)
    refine ⟨t, s', he, ⟨h.pres, h.sp, h.lr⟩, ?_⟩
    sig_post [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, RISCV64.abi, RISCV64.argRegs]
    refine ⟨natPolyIs_of_toNat fun j hj => ?_, polyIs_of_toNat fun j hj => ?_⟩
    · rw [h.c1 j hj hj]; exact o1_toNat s hj
    · rw [h.c0 j hj hj]; exact o0_toNat s
  · sig_pub [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, RISCV64.abi, RISCV64.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  · sig_pub [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, RISCV64.abi, RISCV64.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Round.Power2Round
