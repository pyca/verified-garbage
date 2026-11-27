module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Top
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.KeyGen.Inst
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Samp
import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Verified
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.BitPack
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejNttCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Pro
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.RejBounded
public import VerifiedGarbage.Proof.MlDsa.Sample.RejBounded
public import VerifiedGarbage.Proof.MlDsa.Sample.HalfByte
public import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Pro
meta import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.RejBounded
meta import VerifiedGarbage.Proof.MlDsa.Sample.RejBounded
meta import VerifiedGarbage.Proof.MlDsa.Sample.HalfByte
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.Arith
public import VerifiedGarbage.Proof.MlDsa.Round.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.Arith
meta import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! ### `MlDsa.PPC64LE.Round.Power2Round`, which only this module used -/

section

/-!
# ML-DSA on PPC64LE: `vg_mldsa_power2round`

One symbolic execution of the loop body, for any pointers (`body_ok`), which
writes `(a + 4095) >> 13` to `t1` and `((a + 4095) mod 2¹³) - 4095`, plus
`q` if negative, to `t0` (`p2r1_val`, `p2r0_val`, through
`power2Round_eq`); the loop invariant says which coefficients are done
(`Inv`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Round.Power2Round

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Round
open VG.Impl.MlKem.PPC64LE (fixup)
open VG.Impl.MlDsa.PPC64LE.Arith (loadImm loadQ)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_writeW polyAt_val polyIs_of_toNat natPolyIs_of_toNat
  map_get coeffAt_frame power2Round_eq power2Round_t0 reduced_zero)
open VG.Proof.MlDsa.PPC64LE.Round
open VG.Proof.MlKem.PPC64LE (wp_loop_nz count_sub count_nz ptr_succ)

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
  have h1 : (a + 4095).toNat = a.toNat + 4095 := by rw [BitVec.toNat_add, t]; omega_using [ha]
  have h2 : ((a + 4095) >>> 13 <<< 13).toNat = (a.toNat + 4095) / 8192 * 8192 := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, h1, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega_using [ha])
  have hx : (a + (4095 : BitVec 64) - ((a + (4095 : BitVec 64)) >>> 13) <<< 13).toNat = (a.toNat + 4095) % 8192 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1, h2]; omega_using []), h1, h2]; omega_using []
  have := fixk_diff (k := 8380417) (by decide)
    (a := a + (4095 : BitVec 64) - ((a + (4095 : BitVec 64)) >>> 13) <<< 13) (b := 4095)
    (by rw [hx]; omega_using []) (by rw [hx, t]; exact Nat.le_add_left _ _) (by rw [t]; decide)
  rw [hx, t] at this
  exact this

/-! ## The loop body -/

/-- What an iteration does, for the values stored. -/
def Step (s : State) (x y z c : BitVec 64) (v w : BitVec 32) (s' : State) : Prop :=
  s'.gpr .r3 = x + 4 ∧ s'.gpr .r4 = y + 4 ∧ s'.gpr .r5 = z + 4 ∧ s'.gpr .r6 = c - 1 ∧
    s'.gpr .r7 = s.gpr .r7 ∧
    s'.mem = (s.mem.writeW y v).writeW z w ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧
    ∀ r ∈ preserved, s'.gpr r = s.gpr r

section
variable {s : State} {x y z c : BitVec 64} (h3 : s.gpr .r3 = x) (h4 : s.gpr .r4 = y) (h5 : s.gpr .r5 = z)
  (h6 : s.gpr .r6 = c) (h7 : s.gpr .r7 = 8380417)
  (ia : InRegions (s.rd ++ s.wr) x 4) (ob : InRegions s.wr y 4) (oc : InRegions s.wr z 4)
include h3 h4 h5 h6 h7 ia ob oc

theorem body_ok :
    WP isa (.block p2rBody) s (Step s x y z c
      ((((s.mem.readW x 32).setWidth 64 + 4095) >>> 13).setWidth 32)
      ((fixk 8380417 (p2rLow ((s.mem.readW x 32).setWidth 64))).setWidth 32)) := by
  crun [p2rBody, fixup, Step, fixk, p2rLow, h3, h4, h5, h6, h7, ia, ob, oc, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev T : Addr := s₀.gpr .r3
abbrev T1 : Addr := s₀.gpr .r4
abbrev T0 : Addr := s₀.gpr .r5

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

/-- After `i` iterations, writing `o1 j` and `o0 j` to coefficient `j` of
`t1` and `t0`. -/
structure Inv (o1 o0 : Nat → BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = T s₀ + BitVec.ofNat 64 (4 * i)
  r4 : s.gpr .r4 = T1 s₀ + BitVec.ofNat 64 (4 * i)
  r5 : s.gpr .r5 = T0 s₀ + BitVec.ofNat 64 (4 * i)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (256 - i)
  r7 : s.gpr .r7 = 8380417
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
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
    WP isa (.block p2rBody) s fun s' => Inv o1 o0 s₀ (i + 1) s' ∧ (s'.gpr .r6 != 0) = decide (i + 1 ≠ 256) := by
  have cT := coeff_contains (T s₀) (i := i) hi
  have c1 := coeff_contains (T1 s₀) (i := i) hi
  have c0 := coeff_contains (T0 s₀) (i := i) hi
  obtain ⟨v1, v0⟩ := hv (a := (s.mem.readW (T s₀ + BitVec.ofNat 64 (4 * i)) 32).setWidth 64)
    (by rw [read_t hp hi h])
  refine WP.mono (body_ok h.r3 h.r4 h.r5 h.r6 h.r7 ?_ ?_ ?_)
    fun s' ⟨r3, r4, r5, r6, r7, m, rd, wr, sp, lr, pres⟩ => ⟨⟨?_, ?_, ?_, ?_,
    r7.trans h.r7, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, lr.trans h.lr,
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
    · rw [ite_eq_right e]; exact h.c1 j hj (by omega_using [hji, e])
  · intro j hj hji
    rw [m, show T0 s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (T0 s₀) i from rfl,
      coeffAt_writeW _ _ hj hi]
    by_cases e : i = j
    · subst e; rw [ite_eq_left rfl, v0]
    · rw [ite_eq_right e, VG.Proof.MlDsa.Round.coeffAt_writeW_disjoint _ hp.d01.symm (coeff_contains _ hi)
        (i := j) (by omega)]
      exact h.c0 j hj (by omega_using [hji, e])
  · rw [r6, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]; exact count_nz hi (by decide)

theorem loop_ok {o1 o0 : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀)
    (hv : ∀ i < 256, ∀ {a : BitVec 64}, a = (coeffAt s₀.mem (T s₀) i).setWidth 64 →
      ((a + 4095) >>> 13).setWidth 32 = o1 i ∧ (fixk 8380417 (p2rLow a)).setWidth 32 = o0 i) :
    WP isa power2Round s₀ (Inv o1 o0 s₀ 256) := by
  refine WP.seq (WP.cons (exec_li (by decide)) (WP.cons exec_lis (WP.cons exec_ori (wp_nil ?_))))
  refine wp_loop_nz (Inv o1 o0 s₀) (N := 256) (by decide)
    (fun i hi s h => inv_step hp hi h (hv i hi)) (fun _ h => h) ?_
  refine ⟨by simp [State.write], by simp [State.write], by simp [State.write], by simp [State.write], ?_,
    rfl, rfl, rfl, rfl, fun r hr => ?_, Frame.refl _ _, fun j _ h => absurd h (by omega_using []),
    fun j _ h => absurd h (by omega_using [])⟩
  · simp only [State.write, reduceCtorEq, ite_false, ite_true]
    exact VG.Proof.MlDsa.PPC64LE.Arith.loadImm_val (by decide)
  · have : r ≠ .r6 ∧ r ≠ .r7 := by revert r hr; decide
    simp [State.write, this.1, this.2]

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
    rw [ha, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (coeffAt s₀.mem (T s₀) i).isLt; omega_using [])
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

theorem pre_of {s : State} (h : (Proof.MlDsa.power2RoundContract PPC64LE.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]

theorem verified : Verified PPC64LE.target power2Round (Proof.MlDsa.power2RoundContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.PPC64LE.Add.ctRegs [.r3, .r4, .r5] (fun s₁ s₂ h => ?_)
    (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := loop_ok hp (vals hp)
    refine ⟨t, s', he, ⟨h.pres, h.sp, h.lr⟩, ?_⟩
    sig_post [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, PPC64LE.abi, PPC64LE.argRegs]
    refine ⟨natPolyIs_of_toNat fun j hj => ?_, polyIs_of_toNat fun j hj => ?_⟩
    · rw [h.c1 j hj hj]; exact o1_toNat s hj
    · rw [h.c0 j hj hj]; exact o0_toNat s
  · sig_pub [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, PPC64LE.abi, PPC64LE.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  · sig_pub [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, PPC64LE.abi, PPC64LE.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Round.Power2Round

end

end

/-! ### `MlDsa.PPC64LE.Sample.RejBounded`, which only this module used -/

section

/-! ### `MlDsa.PPC64LE.Sample.RejBoundedCT`, which only this module used -/

section

/-! ### `MlDsa.PPC64LE.Sample.RejBoundedRun`, which this module and modules that import it used -/

section

/-! ### `MlDsa.PPC64LE.Sample.RejBoundedBody`, which this module and modules that import it used -/

section

/-!
# ML-DSA on PPC64LE: an iteration of `vg_mldsa_rej_bounded_poly`

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/RejBoundedBody.lean`), but each
half-byte is tried the same way: its coefficient computed without a branch
(`rbF`, the coefficient of `CoeffFromHalfByte` modulo `q` on the accepted
half-bytes, `rbF_eq`, by evaluation) and `r12` the test of whether it is
accepted and `j < 256` (`accH`), both from `half_ok`; then `accept` stores the
coefficient if so (`try_ok`), which is what `tryJ` does to the coefficients.
An iteration tries the low and then the high half-byte of its byte, which is
what `rbStep` does (`rbStep_tryJ`, `body_ok`). Between the pieces, `Base`
holds: the environment, the XOF output, the pointer `r3` to the byte of
iteration `t`, the count `r6`, `q` in `r7`, and the coefficients `L` stored
(`At`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Proof.MlDsa.Sample (hbTry rbStep rbFold Stored zw ifT ifF hbTry_length halfByteOk_le rbFold_snoc rbFold_append rbFold_full
  rbFold_length_le rbB rbC hbTry_eq halfByteOk_eq)
open VG.Proof.MlKem.PPC64LE (ptr_add count_sub count_nz)
open VG.Proof.MlKem.PPC64LE.Sample (read_one toNat_setWidth8)
open VG.Spec.MlDsa (Zq q ofInt halfByteOk)
open VG.Spec.Sha3 (bytesAt)

/-! ## A half-byte -/

/-- Nonzero exactly when the half-byte `x` is less than `B` and `j < 256`, as
`testJ` computes it. -/
def accH (x : BitVec 64) (B : Nat) (j : BitVec 64) : BitVec 64 :=
  (x - BitVec.ofNat 64 B) >>> 63 &&& (j - BitVec.ofNat 64 256) >>> 63

theorem accH_val {b B j : Nat} (hb : b < 16) (hB : B ≤ 15) (hj : j ≤ 256) :
    accH (BitVec.ofNat 64 b) B (BitVec.ofNat 64 j) = if b < B ∧ j < 256 then 1 else 0 := by
  unfold accH
  by_cases h1 : b < B <;> by_cases h2 : j < 256
  · have e1 : (BitVec.ofNat 64 b - BitVec.ofNat 64 B) >>> 63 = 1 := by bv_omega
    have e2 : (BitVec.ofNat 64 j - BitVec.ofNat 64 256) >>> 63 = 1 := by bv_omega
    rw [e1, e2]; simp [h1, h2]
  · have e2 : (BitVec.ofNat 64 j - BitVec.ofNat 64 256) >>> 63 = 0 := by bv_omega
    rw [e2]; simp [h1, h2]
  · have e1 : (BitVec.ofNat 64 b - BitVec.ofNat 64 B) >>> 63 = 0 := by bv_omega
    rw [e1]; simp [h1, h2]
  · have e1 : (BitVec.ofNat 64 b - BitVec.ofNat 64 B) >>> 63 = 0 := by bv_omega
    rw [e1]; simp [h1, h2]

/-- `x - 10` if `10 ≤ x`, as `csub 10` computes it. -/
def cs10 (x : BitVec 64) : BitVec 64 :=
  x - BitVec.ofNat 64 10 + (x - BitVec.ofNat 64 10) >>> 63 <<< 3 + (x - BitVec.ofNat 64 10) >>> 63 <<< 1

/-- `x - 5` if `5 ≤ x`, as `csub 5` computes it. -/
def cs5 (x : BitVec 64) : BitVec 64 :=
  x - BitVec.ofNat 64 5 + (x - BitVec.ofNat 64 5) >>> 63 <<< 2 + (x - BitVec.ofNat 64 5) >>> 63

/-- `v + q` if `v` is negative, as `addQNeg` computes it. -/
def aq (v : BitVec 64) : BitVec 64 := v + v >>> 63 * BitVec.ofNat 64 8380417

/-- What `rbVal η` computes of the half-byte `x`. -/
def rbF : Nat → BitVec 64 → BitVec 64
  | 2, x => aq (BitVec.ofNat 64 2 - cs5 (cs10 x))
  | _, x => aq (BitVec.ofNat 64 4 - x)

theorem rbF_eq2 : ∀ b < 15, (rbF 2 (BitVec.ofNat 64 b)).setWidth 32 = zw (ofInt (rbC 2 b)) := by decide

theorem rbF_eq4 : ∀ b < 9, (rbF 4 (BitVec.ofNat 64 b)).setWidth 32 = zw (ofInt (rbC 4 b)) := by decide

theorem rbF_eq {η : Nat} (hη : η = 2 ∨ η = 4) {b : Nat} (hb : b < rbB η) :
    (rbF η (BitVec.ofNat 64 b)).setWidth 32 = zw (ofInt (rbC η b)) := by
  rcases hη with rfl | rfl
  · exact rbF_eq2 b hb
  · exact rbF_eq4 b hb

theorem rbB_two : rbB 2 = 15 := rfl

theorem csub_ten : csub 10 = [.subi .r9 .r9 10, .lsr .d .r11 .r9 63, .lsl .r10 .r11 3, .add .r9 .r9 .r10,
    .lsl .r10 .r11 1, .add .r9 .r9 .r10] := rfl

theorem csub_five : csub 5 = [.subi .r9 .r9 5, .lsr .d .r11 .r9 63, .lsl .r10 .r11 2, .add .r9 .r9 .r10,
    .add .r9 .r9 .r11] := rfl

theorem rbB_four : rbB 4 = 9 := rfl

theorem rbB_le {η : Nat} : rbB η ≤ 15 := by unfold rbB; split <;> omega_using []

/-- The block of a half-byte: `r10` its coefficient, `r12` the test. -/
theorem half_run {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) (h7 : s.gpr .r7 = BitVec.ofNat 64 8380417) :
    WP isa (.block (rbHalf η)) s fun t =>
      t.gpr .r10 = rbF η (s.gpr .r9) ∧ t.gpr .r12 = accH (s.gpr .r9) (rbB η) (s.gpr .r5) ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rcases hη with rfl | rfl
  · prun [rbHalf, testJ, rbVal, csub_ten, csub_five, addQNeg, rbBound, rbB_two, rbF, cs10, cs5, aq, accH, List.cons_append,
      List.nil_append, List.append_assoc, exec_mul, ↓reduceIte, h7]
    simp only [true_and, and_true]
    intro r a b c d
    simp only [RegUpd.gpr_write, a, b, c, d, ite_false]
  · prun [rbHalf, testJ, rbVal, addQNeg, rbBound, rbB_four, rbF, aq, accH, List.cons_append, List.nil_append,
      List.append_assoc, exec_mul, ↓reduceIte, h7]
    simp only [true_and, and_true]
    intro r _ b c d
    simp only [RegUpd.gpr_write, b, c, d, ite_false]

/-! ## The invariant between the pieces -/

/-- The call, from its entry state: `seed = r3`, `eta = r4`, `a = r5`,
`scratch = r6`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r3, 66, σ.gpr .r6, σ.gpr .r5⟩

/-- `η`, the low 32 bits of `r4`. -/
abbrev etaOf (σ : State) : Nat := ((σ.gpr .r4).setWidth 32).toNat

/-- The XOF output a loop uses: `n` bytes of `H(ρ)`. -/
abbrev X (n : Nat) (σ : State) : List Byte := Spec.MlDsa.H ((spOf σ).msg σ) n

theorem X_length (n : Nat) (σ : State) : (X n σ).length = n := Proof.MlDsa.Sample.H_length _ _

/-- The byte of iteration `t`. -/
abbrev zAt (X : List Byte) (t : Nat) : Byte := X.getD t 0

/-- Iteration `t`, with the coefficients `L` stored, for the XOF output `X`. -/
structure Base (σ : State) (X : List Byte) (t : Nat) (L : List Zq) (s : State) : Prop where
  env : Env (spOf σ) σ s
  xlen : X.length ≤ 544
  out : bytesAt s.mem ((spOf σ).at' 840) X.length = X
  r3 : s.gpr .r3 = σ.gpr .r6 + BitVec.ofNat 64 (840 + t)
  r6 : s.gpr .r6 = BitVec.ofNat 64 (X.length - t)
  r7 : s.gpr .r7 = BitVec.ofNat 64 8380417
  r27 : s.gpr .r27 = zx (σ.gpr .r4)
  r28 : s.gpr .r28 = BitVec.ofNat 64 66
  r29 : s.gpr .r29 = σ.gpr .r3
  at' : At (spOf σ) L s

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- `Base` through a block that writes no memory and only `r8`–`r12`. -/
theorem Base.keep {X : List Byte} {t : Nat} {L : List Zq} {s s' : State} (h : Base σ X t L s)
    (hm : s'.mem = s.mem)
    (g : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) (rd : s'.rd = s.rd)
    (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : Base σ X t L s' := by
  have gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr =>
    g r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide))
  exact ⟨h.env.regs hp hm gp rd wr sp, h.xlen, by rw [hm]; exact h.out, (g _ (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h.r3, (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.r6,
    (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.r7,
    (gp _ (by decide)).trans h.r27, (gp _ (by decide)).trans h.r28, (gp _ (by decide)).trans h.r29,
    ⟨(g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.at'.r4,
      (g _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.at'.r5, h.at'.len,
      by rw [hm]; exact h.at'.st⟩⟩

end

/-! ## A try -/

/-- The half-byte `b` tried while `j < 256`: what a half-byte of the loop does. -/
def tryJ (η : Nat) (L : List Zq) (b : Nat) : List Zq := if L.length < 256 then hbTry η L b else L

theorem tryJ_length (η : Nat) (L : List Zq) (b : Nat) :
    (tryJ η L b).length = if L.length < 256 then L.length + halfByteOk η b else L.length := by
  unfold tryJ; split <;> simp only [hbTry_length]

/-- An iteration, as two tries. -/
theorem rbStep_tryJ (η : Nat) (L : List Zq) (z : Byte) :
    rbStep η L z = tryJ η (tryJ η L (z.toNat % 16)) (z.toNat / 16) := by
  unfold rbStep tryJ
  by_cases h : L.length < 256
  · rw [ifT (show L.length < Spec.MlDsa.n from h), ifT h]
  · rw [ifF (show ¬ L.length < Spec.MlDsa.n from h), ifF h, ifF h]

/-- After the block of the half-byte `b`: its coefficient in `r10`, the test
in `r12`, `r8` = `v`. -/
structure H1 (η : Nat) (σ : State) (X : List Byte) (t : Nat) (L : List Zq) (b : Nat) (v : BitVec 64)
    (s : State) : Prop where
  base : Base σ X t L s
  r8 : s.gpr .r8 = v
  r10 : s.gpr .r10 = rbF η (BitVec.ofNat 64 b)
  r12 : s.gpr .r12 = accH (BitVec.ofNat 64 b) (rbB η) (BitVec.ofNat 64 L.length)

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

theorem half_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} {L : List Zq} {b : Nat} {s : State}
    (h : Base σ X t L s) (h9 : s.gpr .r9 = BitVec.ofNat 64 b) :
    WP isa (.block (rbHalf η)) s (H1 η σ X t L b (s.gpr .r8)) :=
  WP.mono (half_run hη s h.r7) fun s' ⟨g10, g12, g, m, rd, wr, sp⟩ =>
    ⟨h.keep hp m (fun r _ a b c d => g r a b c d) rd wr sp, g .r8 (by decide) (by decide) (by decide) (by decide),
      by rw [g10, h9], by rw [g12, h9, h.at'.r5]⟩

/-- `accept` after the block of a half-byte: what `tryJ` does. -/
theorem try_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} {L : List Zq} {b : Nat} (hb : b < 16)
    {v : BitVec 64} {s : State} (h : H1 η σ X t L b v s) :
    WP isa (accept .r10) s fun s' => Base σ X t (tryJ η L b) s' ∧ s'.gpr .r8 = v := by
  have l := h.base
  have hlen := l.at'.len
  have ea := accH_val hb (rbB_le (η := η)) hlen
  rw [← h.r12] at ea
  unfold tryJ
  rw [hbTry_eq hη]
  by_cases hz : s.gpr .r12 = 0
  · have hn : ¬ (b < rbB η ∧ L.length < 256) := fun hc => by rw [hz, ifT hc] at ea; exact absurd ea (by decide)
    have e : (if L.length < 256 then (if b < rbB η then L ++ [ofInt (rbC η b)] else L) else L) = L := by
      by_cases hl : L.length < 256
      · rw [ifT hl, ifF (fun hc => hn ⟨hc, hl⟩)]
      · rw [ifF hl]
    rw [e]
    exact WP.mono (accept_skip hz) fun s' e' => by subst e'; exact ⟨l, h.r8⟩
  · have hy : b < rbB η ∧ L.length < 256 := by
      by_contra hc; rw [ifF hc] at ea; exact hz ea
    rw [ifT hy.2, ifT hy.1]
    refine WP.mono (accept_store hp l.env l.at' hy.2 (x := ofInt (rbC η b)) (by rw [h.r10]; exact rbF_eq hη hy.1) hz)
      fun s' ⟨at', env', rr, hf⟩ => ⟨⟨env', l.xlen, ?_, (rr _ (by decide) (by decide)).trans l.r3,
        (rr _ (by decide) (by decide)).trans l.r6, (rr _ (by decide) (by decide)).trans l.r7,
        (rr _ (by decide) (by decide)).trans l.r27, (rr _ (by decide) (by decide)).trans l.r28,
        (rr _ (by decide) (by decide)).trans l.r29, at'⟩,
        (rr _ (by decide) (by decide)).trans h.r8⟩
    rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := X.length) (by have := l.xlen; omega_using [this]))).symm) (by have := l.xlen; omega_using [this])]
    exact l.out

/-! ## An iteration -/

/-- The byte of iteration `t`. -/
theorem byte_ok {X : List Byte} {t : Nat} (ht : t < X.length) {L : List Zq} {s : State} (h : Base σ X t L s) :
    InRegions (s.rd ++ s.wr) (s.gpr .r3) 1 ∧ s.mem (s.gpr .r3) = zAt X t := by
  rw [h.r3]
  have := h.xlen
  refine ⟨by rw [← BitVec.add_zero (σ.gpr .r6 + _), ptr_add]; exact inScrRd hp h.env.wr (by omega_using [ht, this]), ?_⟩
  have := congrArg (fun L => L.getD t 0) h.out
  rw [MlKem.bytesAt_getD _ _ (by omega_using [ht]), ptr_add] at this
  exact this

omit hp in
/-- The low half-byte of a byte, as the code computes it. -/
theorem lo_eq (z : Byte) : z.setWidth 64 <<< 60 >>> 60 = BitVec.ofNat 64 (z.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  have := z.isLt
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, toNat_setWidth8, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega_using []

omit hp in
/-- The high half-byte of a byte, as the code computes it. -/
theorem hi_eq (z : Byte) : z.setWidth 64 >>> 4 = BitVec.ofNat 64 (z.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  have := z.isLt
  rw [BitVec.toNat_ushiftRight, toNat_setWidth8, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_using []

/-- The load of the byte and its low half-byte. -/
theorem lo_ok {X : List Byte} {t : Nat} (ht : t < X.length) {L : List Zq} {s : State} (h : Base σ X t L s) :
    WP isa (.block [.lbz .r8 .r3 0, .lsl .r9 .r8 60, .lsr .d .r9 .r9 60]) s fun s' =>
      Base σ X t L s' ∧ s'.gpr .r8 = (zAt X t).setWidth 64 ∧
        s'.gpr .r9 = BitVec.ofNat 64 ((zAt X t).toNat % 16) := by
  obtain ⟨i0, v0⟩ := byte_ok hp ht h
  have hk : WP isa (.block [.lbz .r8 .r3 0, .lsl .r9 .r8 60, .lsr .d .r9 .r9 60]) s fun s' =>
      s'.gpr .r8 = (zAt X t).setWidth 64 ∧ s'.gpr .r9 = (zAt X t).setWidth 64 <<< 60 >>> 60 ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    prun [exec_lbz, read_one, i0, v0]
    simp only [true_and, and_true]
    intro r a b
    simp only [RegUpd.gpr_write, a, b, ite_false]
  refine WP.mono hk fun s' ⟨g8, g9, g, m, rd, wr, sp⟩ =>
    ⟨h.keep hp m (fun r a b _ _ _ => g r a b) rd wr sp, g8, by rw [g9, lo_eq]⟩

/-- The load of the byte and the block of its low half-byte. -/
theorem loHalf_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} (ht : t < X.length) {L : List Zq}
    {s : State} (h : Base σ X t L s) :
    WP isa (.block (([.lbz .r8 .r3 0, .lsl .r9 .r8 60, .lsr .d .r9 .r9 60] : List Instr) ++ rbHalf η)) s
      (H1 η σ X t L ((zAt X t).toNat % 16) ((zAt X t).setWidth 64)) := by
  rw [WP.block_append_iff]
  exact WP.mono (lo_ok hp ht h) fun s1 ⟨b1, e8, e9⟩ => e8 ▸ half_ok hp hη b1 e9

/-- The block of the high half-byte, from the byte in `r8`. -/
theorem hiHalf_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} {L : List Zq} {s : State}
    (h : Base σ X t L s) (h8 : s.gpr .r8 = (zAt X t).setWidth 64) :
    WP isa (.block (.lsr .d .r9 .r8 4 :: rbHalf η)) s
      (H1 η σ X t L ((zAt X t).toNat / 16) ((zAt X t).setWidth 64)) := by
  rw [← List.singleton_append, WP.block_append_iff]
  have hk : WP isa (.block [.lsr .d .r9 .r8 4]) s fun s4 => s4 = s.write .r9 (s.gpr .r8 >>> 4) := by prun []
  refine WP.mono hk fun s4 e4 => ?_
  subst e4
  have b4 : Base σ X t L (s.write .r9 (s.gpr .r8 >>> 4)) :=
    h.keep hp rfl (fun r _ a _ _ _ => RegUpd.gpr_write_of_ne _ _ a) rfl rfl rfl
  have h9 : (s.write .r9 (s.gpr .r8 >>> 4)).gpr .r9 = BitVec.ofNat 64 ((zAt X t).toNat / 16) := by
    rw [RegUpd.gpr_write_self, h8, hi_eq]
  have e : (s.write .r9 (s.gpr .r8 >>> 4)).gpr .r8 = (zAt X t).setWidth 64 := by
    rw [RegUpd.gpr_write_of_ne _ _ (by decide), h8]
  exact e ▸ half_ok hp hη b4 h9

/-- The tries of an iteration, from its start, then `rest`. -/
theorem tries_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} (ht : t < X.length) {L : List Zq}
    {s : State} (h : Base σ X t L s) {rest : Prog isa} {Q : State → Prop}
    (hr : ∀ s', Base σ X t (rbStep η L (zAt X t)) s' → WP isa rest s' Q) :
    WP isa (.seq (.block (([.lbz .r8 .r3 0, .lsl .r9 .r8 60, .lsr .d .r9 .r9 60] : List Instr) ++ rbHalf η))
      (.seq (accept .r10) (.seq (.block (.lsr .d .r9 .r8 4 :: rbHalf η)) (.seq (accept .r10) rest)))) s Q := by
  rw [rbStep_tryJ] at hr
  refine WP.seq (WP.mono (loHalf_ok hp hη ht h) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (try_ok hp hη (Nat.mod_lt _ (by decide)) h2) fun s3 ⟨b3, f8⟩ => ?_)
  refine WP.seq (WP.mono (hiHalf_ok hp hη b3 f8) fun s5 h5 => ?_)
  exact WP.seq (WP.mono (try_ok hp hη (by have := (zAt X t).isLt; omega_using []) h5) fun s6 h6 => hr s6 h6.1)

omit hp in
/-- The test of the step: `r12` nonzero iff bytes are left and `j < 256`. -/
theorem exit_val {N t j : Nat} (ht : t < N) (hN : N < 2 ^ 63) (hj : j ≤ 256) :
    (BitVec.ofNat 64 (N - (t + 1)) * ((BitVec.ofNat 64 j - BitVec.ofNat 64 256) >>> 63) != 0) =
      decide (t + 1 ≠ N ∧ j < 256) := by
  by_cases hj' : j < 256
  · have e : (BitVec.ofNat 64 j - BitVec.ofNat 64 256) >>> 63 = 1 := by bv_omega
    rw [e, show ∀ x : BitVec 64, x * 1 = x from fun x => by bv_omega, count_nz ht (by omega_using [hN])]
    simp [hj']
  · have e : (BitVec.ofNat 64 j - BitVec.ofNat 64 256) >>> 63 = 0 := by bv_omega
    rw [e, show ∀ x : BitVec 64, x * 0 = 0 from fun x => by bv_omega]
    simp [hj']

/-- The step, to iteration `t + 1`: `r12` zero iff it was the last or `j = 256`. -/
theorem step_ok {X : List Byte} {t : Nat} (ht : t < X.length) {L : List Zq} {s : State} (h : Base σ X t L s) :
    WP isa (.block stepBlk) s fun s' =>
      Base σ X (t + 1) L s' ∧ (s'.gpr .r12 != 0) = decide (t + 1 ≠ X.length ∧ L.length < 256) := by
  have hk : WP isa (.block stepBlk) s fun s' =>
      s'.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 1 ∧ s'.gpr .r6 = s.gpr .r6 - BitVec.ofNat 64 1 ∧
      s'.gpr .r12 = (s.gpr .r6 - BitVec.ofNat 64 1) * ((s.gpr .r5 - BitVec.ofNat 64 256) >>> 63) ∧
      (∀ r, r ≠ .r3 → r ≠ .r6 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    prun [stepBlk, exec_mul]
    simp only [true_and, and_true]
    intro r a b c d
    simp only [RegUpd.gpr_write, a, b, c, d, ite_false]
  have hx := h.xlen
  refine WP.mono hk fun s' ⟨r3, r6, r12, g, m, rd, wr, sp⟩ => ⟨⟨?_, h.xlen, by rw [m]; exact h.out, ?_, ?_,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.r7,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.r27,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.r28,
    (g _ (by decide) (by decide) (by decide) (by decide)).trans h.r29,
    ⟨(g _ (by decide) (by decide) (by decide) (by decide)).trans h.at'.r4,
      (g _ (by decide) (by decide) (by decide) (by decide)).trans h.at'.r5, h.at'.len, by rw [m]; exact h.at'.st⟩⟩, ?_⟩
  · exact h.env.regs hp m (fun r hr => g r (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide))) rd wr sp
  · rw [r3, h.r3, ptr_add, Nat.add_assoc]
  · rw [r6, h.r6]; exact count_sub ht
  · rw [r12, h.r6, h.at'.r5, count_sub ht]; exact exit_val ht (by omega_using [hx]) h.at'.len

end

/-- The coefficients after `t` iterations. -/
abbrev Lf (η : Nat) (X : List Byte) (t : Nat) : List Zq := rbFold η [] (X.take t)

theorem take_succ' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem Lf_succ (η : Nat) {X : List Byte} {t : Nat} (ht : t < X.length) :
    Lf η X (t + 1) = rbStep η (Lf η X t) (zAt X t) := by
  simp only [Lf]
  rw [take_succ' _ (by omega_using [ht]), rbFold_snoc]

/-- After the last byte, or once there are 256 coefficients, the bytes left
change nothing. -/
theorem Lf_stop {η : Nat} {X : List Byte} {t N : Nat} (htN : t ≤ N) (h : t = N ∨ (Lf η X t).length = 256) :
    Lf η X N = Lf η X t := by
  rcases h with rfl | h
  · rfl
  simp only [Lf] at h ⊢
  have e : X.take N = X.take t ++ (X.take N).drop t := by
    have := List.take_append_drop t (X.take N)
    rw [List.take_take, Nat.min_eq_left htN] at this
    exact this.symm
  rw [e, rbFold_append, rbFold_full h]

/-- An iteration: what `rbStep` does to the coefficients. -/
theorem body_ok {σ : State} (hp : SpOk (spOf σ) σ) {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte}
    {t : Nat} (ht : t < X.length) {s : State} (h : Base σ X t (Lf η X t) s) :
    WP isa (rbBody η) s fun s' => Base σ X (t + 1) (Lf η X (t + 1)) s' ∧
      (s'.gpr .r12 != 0) = decide (t + 1 ≠ X.length ∧ (Lf η X (t + 1)).length < 256) := by
  rw [Lf_succ η ht]
  exact tries_ok hp hη ht h fun _ h' => step_ok hp ht h'

end VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

end

end

/-!
# ML-DSA on PPC64LE: `vg_mldsa_rej_bounded_poly`, correctness

As on 32-bit ARM (`Proof/MlDsa/Arm/KeyGen/Inst.lean`). The function
runs in pieces: the prologue (`J0`, with `η` zero-extended in `r27`), the
sponge, whose output is `H(ρ, n)` (`J6`), the branch on `η` (`sel_ok`), and
the loop for `η`, iteration `t` of which starts from `Base` with the
coefficients `rbFold` samples from the first `t` bytes of output stored
(`loop_ok`): a try (`rbTry_ok`), with 272 bytes, then, if it did not sample 256
coefficients (`jtest_ok`), with 544; then the end returns whether there are
256 (`correct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Proof.MlDsa.Sample (Stored stored_nil H_eq rbFold ifT ifF rbFold_length_le)
open VG.Proof.MlKem.PPC64LE (wp_loop_nz)
open VG.Spec.MlDsa (Zq H)
open VG.Spec.Sha3 (bytesAt)

/-- `J6` for `n` bytes, and `η` zero-extended in `r27`. -/
structure SJ (n : Nat) (σ s : State) : Prop where
  j6 : ∃ s₀, J6 136 n (spOf σ) σ s₀ s
  r27 : s.gpr .r27 = zx (σ.gpr .r4)

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- The loop's setup, after the sponge. -/
theorem init_ok {n : Nat} (hn : n ≤ 544) {s : State} (h : SJ n σ s) :
    WP isa (.block (([.addi .r3 .r31 840, mov .r4 .r30, .li .r5 0, .li .r6 n] : List Instr) ++ loadQ)) s
      (Base σ (X n σ) 0 []) := by
  obtain ⟨⟨s₀, h⟩, e27⟩ := h
  have g30 := h.j0.env.r30
  have g31 := h.j0.env.r31
  have hn' : n < 32768 := by omega_using [hn]
  have hk : WP isa (.block (([.addi .r3 .r31 840, mov .r4 .r30, .li .r5 0, .li .r6 n] : List Instr) ++ loadQ)) s
      fun s' => s'.gpr .r3 = σ.gpr .r6 + BitVec.ofNat 64 (840 + 0) ∧ s'.gpr .r4 = σ.gpr .r5 ∧
        s'.gpr .r5 = BitVec.ofNat 64 0 ∧ s'.gpr .r6 = BitVec.ofNat 64 n ∧
        s'.gpr .r7 = BitVec.ofNat 64 8380417 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    prun [loadQ, List.cons_append, List.nil_append, exec_lis, exec_ori, loadQ_val, g30, g31, hn']
    simp only [true_and, and_true]
    pres_tac
  refine WP.mono hk fun s' ⟨g3, g4, g5, g6, g7, gp, m, rd, wr, sp⟩ => ⟨h.j0.env.regs hp m gp rd wr sp,
    by rw [X_length]; exact hn, by rw [m, X_length, h.out]; exact (H_eq _ _).symm, g3, by rw [X_length, Nat.sub_zero]; exact g6, g7,
    (gp _ (by decide)).trans e27, (gp _ (by decide)).trans h.j0.r28, (gp _ (by decide)).trans h.j0.r29, ?_⟩
  exact ⟨by rw [g4]; exact (BitVec.add_zero _).symm, g5, by simp, stored_nil _ _⟩

/-- The loop for `η`, over `n` bytes: it stops after the last byte or once
there are 256 coefficients, which are then those of all `n` bytes. -/
theorem loop_ok {η : Nat} (hη : η = 2 ∨ η = 4) {n : Nat} (hn0 : 0 < n) (hn : n ≤ 544) {s : State}
    (h : SJ n σ s) : WP isa (rbLoop η n) s fun s' => ∃ t, Base σ (X n σ) t (Lf η (X n σ) n) s' := by
  refine WP.seq (WP.mono (init_ok hp hn h) fun s0 h0 => ?_)
  refine WP.loop (M := isa) (c := .nonzero .d .r12) (fun m s => ∃ i, i < n ∧ m = n - i ∧
    Base σ (X n σ) i (Lf η (X n σ) i) s ∧ (Lf η (X n σ) i).length < 256) ?_ n s0
    ⟨0, hn0, rfl, by simpa [Lf, rbFold] using h0, by simp [Lf, rbFold]⟩
  rintro m s ⟨i, hi, rfl, hs, -⟩
  refine WP.mono (body_ok hp hη (X := X n σ) (by rw [X_length]; exact hi) hs) fun s' ⟨hs', hz⟩ => ?_
  rw [X_length] at hz
  have ev : isa.eval (.nonzero .d .r12) s' =
      some (decide (i + 1 ≠ n ∧ (Lf η (X n σ) (i + 1)).length < 256)) := by rw [eval_nonzero, hz]
  by_cases hc : i + 1 ≠ n ∧ (Lf η (X n σ) (i + 1)).length < 256
  · exact .inr ⟨by rw [ev, decide_eq_true hc], n - (i + 1), by omega_using [hi], i + 1, by omega_using [hi, hc], rfl, hs', hc.2⟩
  · refine .inl ⟨by rw [ev, decide_eq_false hc], i + 1, ?_⟩
    have hle := rbFold_length_le (η := η) (a := []) (by simp) ((X n σ).take (i + 1))
    rw [Lf_stop (show i + 1 ≤ n by omega_using [hi]) (by
      by_cases e : i + 1 = n
      · exact .inl e
      · have h1 := not_and.mp hc e
        have hle' : (Lf η (X n σ) (i + 1)).length ≤ 256 := hle
        exact .inr (by omega_using [h1, hle']))]
    exact hs'

omit hp in
/-- The test of `η = 2`. -/
theorem eta_test (x : BitVec 64) : (zx x - BitVec.ofNat 64 2 == 0) = decide ((x.setWidth 32).toNat = 2) := by
  have e := zx_toNat x
  by_cases h : (x.setWidth 32).toNat = 2
  · have : zx x - BitVec.ofNat 64 2 = 0 := by bv_omega
    rw [this, decide_eq_true h]; rfl
  · have : zx x - BitVec.ofNat 64 2 ≠ 0 := by bv_omega
    rw [decide_eq_false h]; exact beq_eq_false_iff_ne.mpr this

/-- The test of `η = 2`, which keeps `J6`. -/
theorem cmp_ok {n : Nat} {s : State} (h : SJ n σ s) :
    WP isa (.block [.subi .r12 .r27 2]) s fun s' => SJ n σ s' ∧ s'.gpr .r12 = zx (σ.gpr .r4) - BitVec.ofNat 64 2 := by
  obtain ⟨⟨s₀, j6⟩, e27⟩ := h
  have hk : WP isa (.block [.subi .r12 .r27 2]) s fun s' => s' = s.write .r12 (s.gpr .r27 - BitVec.ofNat 64 2) := by
    prun []
  refine WP.mono hk fun s' e' => ?_
  subst e'
  have gp : ∀ r ∈ preserved, (s.write .r12 (s.gpr .r27 - BitVec.ofNat 64 2)).gpr r = s.gpr r := by pres_tac
  exact ⟨⟨⟨s₀, j6.j0.regs hp rfl gp rfl rfl rfl, fun r hr => (gp r hr).trans (j6.gp r hr), j6.out⟩,
    (gp .r27 (by decide)).trans e27⟩, by rw [RegUpd.gpr_write_self, e27]⟩

/-- The branch on `η`, and the loop for it. -/
theorem sel_ok (hη : etaOf σ = 2 ∨ etaOf σ = 4) {n : Nat} (hn0 : 0 < n) (hn : n ≤ 544) {s : State}
    (h : SJ n σ s) :
    WP isa (.seq (.block [.subi .r12 .r27 2]) (.ite (.zero .d .r12) (rbLoop 2 n) (rbLoop 4 n))) s
      fun s' => ∃ t, Base σ (X n σ) t (Lf (etaOf σ) (X n σ) n) s' := by
  refine WP.seq (WP.mono (cmp_ok hp h) fun s1 ⟨h1, e12⟩ => ?_)
  refine WP.ite _ (by rw [eval_zero, e12, eta_test]) (fun he => ?_) (fun he => ?_)
  · simp only [decide_eq_true_eq] at he
    rw [show etaOf σ = 2 from he]
    exact loop_ok hp (.inl rfl) hn0 hn h1
  · simp only [decide_eq_false_iff_not] at he
    rw [show etaOf σ = 4 from hη.resolve_left he]
    exact loop_ok hp (.inr rfl) hn0 hn h1

/-- A try with `n` bytes, from the registers of the sponge's arguments and
`η` in `r27`. -/
theorem rbTry_ok (hη : etaOf σ = 2 ∨ etaOf σ = 4) {n : Nat} (hn0 : 0 < n) (hn : n ≤ 544) {s : State}
    (j0 : J0 (spOf σ) σ s) (e27 : s.gpr .r27 = zx (σ.gpr .r4)) :
    WP isa (rbTry n) s fun s' => ∃ t, Base σ (X n σ) t (Lf (etaOf σ) (X n σ) n) s' :=
  WP.seq (WP.mono (sponge_ok hp (rate := 136) (outlen := n) (by decide) (by omega_using [hn]) j0) fun _ h =>
    sel_ok hp hη hn0 hn ⟨⟨s, h⟩, (h.gp .r27 (by decide)).trans e27⟩)

/-- The test of `j = 256`. -/
theorem jtest_ok {X : List Byte} {t : Nat} {L : List Zq} {s : State} (h : Base σ X t L s) :
    WP isa (.block [.subi .r12 .r5 256]) s fun s' => Base σ X t L s' ∧
      isa.eval (.zero .d .r12) s' = some (decide (L.length = 256)) := by
  have hk : WP isa (.block [.subi .r12 .r5 256]) s fun s' => s' = s.write .r12 (s.gpr .r5 - BitVec.ofNat 64 256) := by
    prun []
  refine WP.mono hk fun s' e' => ?_
  subst e'
  refine ⟨h.keep hp rfl (fun r _ _ _ _ a => RegUpd.gpr_write_of_ne _ _ a) rfl rfl rfl, ?_⟩
  rw [eval_zero, RegUpd.gpr_write_self, h.at'.r5]
  have hl := h.at'.len
  by_cases e : L.length = 256
  · rw [e]; rfl
  · rw [decide_eq_false e]
    exact congrArg some (beq_eq_false_iff_ne.mpr (by bv_omega))

/-- The coefficients the function samples: those of the first 272 bytes if
there are 256 of them, and those of 544 bytes otherwise. -/
abbrev Lr (η : Nat) (σ : State) : List Zq :=
  if (Lf η (X 272 σ) 272).length = 256 then Lf η (X 272 σ) 272 else Lf η (X 544 σ) 544

/-- The whole function: `r3` whether 256 coefficients were sampled, those
stored, and the calling convention. -/
theorem correct (hη : etaOf σ = 2 ∨ etaOf σ = 4) :
    WP isa rejBounded σ fun s' =>
      s'.gpr .r3 = (if (Lr (etaOf σ) σ).length = 256 then 1 else 0) ∧
      Stored s'.mem (σ.gpr .r5) (Lr (etaOf σ) σ) ∧ abiPreserved σ s' := by
  unfold rejBounded
  refine WP.seq (WP.mono (pro_rb hp rfl rfl rfl rfl) fun s₀ ⟨j0, e27⟩ => ?_)
  refine WP.seq (WP.mono (rbTry_ok hp hη (n := 272) (by decide) (by decide) j0 e27) fun s1 ⟨t1, h1⟩ => ?_)
  have fin : ∀ {X t s}, Base σ X t (Lr (etaOf σ) σ) s →
      WP isa (.block (retJ ++ epi)) s fun s' =>
        s'.gpr .r3 = (if (Lr (etaOf σ) σ).length = 256 then 1 else 0) ∧
        Stored s'.mem (σ.gpr .r5) (Lr (etaOf σ) σ) ∧ abiPreserved σ s' := fun h3 =>
    WP.mono (retEpi_ok hp h3.env h3.at'.r5 h3.at'.len) fun s' ⟨r3, hm, ha⟩ =>
      ⟨r3, by rw [hm]; exact h3.at'.st, ha⟩
  refine WP.seq (WP.seq (WP.mono (jtest_ok hp h1) fun s2 ⟨h2, ev⟩ =>
    WP.ite _ ev (fun he => ?_) (fun he => ?_)))
  · simp only [decide_eq_true_eq] at he
    refine WP.block_nil (fin (X := X 272 σ) (t := t1) ?_)
    rw [Lr, ifT he]; exact h2
  · simp only [decide_eq_false_iff_not] at he
    exact WP.mono (rbTry_ok hp hη (n := 544) (by decide) (by decide) ⟨h2.env, h2.r29, h2.r28⟩ h2.r27)
      fun s3 ⟨_, h3⟩ => fin (by rw [Lr, ifF he]; exact h3)

end

end VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

end

end

/-!
# ML-DSA on PPC64LE: the loop of `vg_mldsa_rej_bounded_poly`, constant time

As on 32-bit ARM (`Proof/MlDsa/Arm/KeyGen/Inst.lean`). Two runs of
the loop for `η`, whose XOF outputs `X₁` and `X₂` have their half-bytes
accepted alike (`hbOks`, which the leak of the contract determines), leak the
same: at iteration `t`, both runs have sampled as many coefficients
(`rbFold_length_congr`), and the byte to read has its half-bytes accepted
alike, so the tests in `r12` agree (`acc_eq`), and with them the branches of
`accept` and the addresses of its stores; the coefficients themselves are
computed by code that the taint analysis proves leaks nothing of them but the
address of the byte read (`load_ct`, `hi_ct`). What each run is at each point
comes from the correctness proof (`relct_wp`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Proof.MlDsa.Sample (hbTry rbStep rbFold hbOks rbFold_length_congr rbB halfByteOk_eq halfByteOk_le
  rbFold_length_le)
open VG.Proof.MlKem.PPC64LE (relct_noMem)
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)
open VG.Spec.MlDsa (Zq halfByteOk)

/-! ## The blocks, for any `η` -/

/-- The load of the byte and the block of its low half-byte. -/
theorem load_ct {η : Nat} (hη : η = 2 ∨ η = 4) {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h3 : ∀ a b, R a b → a.gpr .r3 = b.gpr .r3) :
    RelCT isa R (.block (([.lbz .r8 .r3 0, .lsl .r9 .r8 60, .lsr .d .r9 .r9 60] : List Instr) ++ rbHalf η)) fun _ _ => True := by
  rcases hη with rfl | rfl <;>
  exact taint_block [.r3] hsp (fun a b hab r hr => by rw [List.mem_singleton] at hr; subst hr; exact h3 a b hab)
    (by taint_decide)

/-- The block of the high half-byte. -/
theorem hi_ct {η : Nat} (hη : η = 2 ∨ η = 4) {R : State → State → Prop} :
    RelCT isa R (.block (.lsr .d .r9 .r8 4 :: rbHalf η)) fun _ _ => True := by
  rcases hη with rfl | rfl <;> exact relct_noMem rfl

/-- The tests of two half-bytes accepted alike, with as many coefficients. -/
theorem acc_eq {η : Nat} (hη : η = 2 ∨ η = 4) {b₁ b₂ j : Nat} (hb₁ : b₁ < 16) (hb₂ : b₂ < 16) (hj : j ≤ 256)
    (hok : halfByteOk η b₁ = halfByteOk η b₂) :
    accH (BitVec.ofNat 64 b₁) (rbB η) (BitVec.ofNat 64 j) = accH (BitVec.ofNat 64 b₂) (rbB η) (BitVec.ofNat 64 j) := by
  rw [accH_val hb₁ rbB_le hj, accH_val hb₂ rbB_le hj]
  rw [halfByteOk_eq hη, halfByteOk_eq hη] at hok
  by_cases h₁ : b₁ < rbB η <;> by_cases h₂ : b₂ < rbB η <;> simp only [h₁, h₂, ite_true, ite_false] at hok ⊢ <;>
    first | rfl | exact absurd hok (by decide)

/-! ## The loop -/

section
variable {σ₁ σ₂ : State} (hp₁ : SpOk (spOf σ₁) σ₁) (hp₂ : SpOk (spOf σ₂) σ₂) (hsp : σ₁.sp = σ₂.sp)
  (h5 : σ₁.gpr .r5 = σ₂.gpr .r5) (h6 : σ₁.gpr .r6 = σ₂.gpr .r6) {η : Nat} (hη : η = 2 ∨ η = 4)
  {X₁ X₂ : List Byte}

theorem base_sp {t₁ t₂ : Nat} {L₁ L₂ : List Zq} {a b : State} (ha : Base σ₁ X₁ t₁ L₁ a) (hb : Base σ₂ X₂ t₂ L₂ b)
    (hsp : σ₁.sp = σ₂.sp) : a.sp = b.sp := by
  rw [ha.env.sp, hb.env.sp, hsp]

theorem base_r4 {t₁ t₂ : Nat} {L₁ L₂ : List Zq} {a b : State} (ha : Base σ₁ X₁ t₁ L₁ a) (hb : Base σ₂ X₂ t₂ L₂ b)
    (h5 : σ₁.gpr .r5 = σ₂.gpr .r5) (hl : L₁.length = L₂.length) : a.gpr .r4 = b.gpr .r4 := by
  rw [ha.at'.r4, hb.at'.r4, hl]; exact congrArg (· + _) h5

include hp₁ hp₂ hsp h5 hη in
/-- A try, in two runs with as many coefficients and half-bytes accepted
alike. -/
theorem try_ct {t : Nat} {L₁ L₂ : List Zq} (hl : L₁.length = L₂.length) {b₁ b₂ : Nat} (hb₁ : b₁ < 16)
    (hb₂ : b₂ < 16) (hok : halfByteOk η b₁ = halfByteOk η b₂) {v₁ v₂ : BitVec 64} :
    RelCT isa (fun a b => H1 η σ₁ X₁ t L₁ b₁ v₁ a ∧ H1 η σ₂ X₂ t L₂ b₂ v₂ b) (accept .r10)
      fun a b => (Base σ₁ X₁ t (tryJ η L₁ b₁) a ∧ a.gpr .r8 = v₁) ∧
        (Base σ₂ X₂ t (tryJ η L₂ b₂) b ∧ b.gpr .r8 = v₂) :=
  relct_wp (accept_ct (fun a b hab => base_sp hab.1.base hab.2.base hsp)
    (fun a b hab => by rw [hab.1.r12, hab.2.r12, hl, acc_eq hη hb₁ hb₂ (hl ▸ hab.2.base.at'.len) hok])
    fun a b hab => base_r4 hab.1.base hab.2.base h5 hl)
    fun a b hab => ⟨try_ok hp₁ hη hb₁ hab.1, try_ok hp₂ hη hb₂ hab.2⟩

variable {N : Nat} (hX₁ : X₁.length = N) (hX₂ : X₂.length = N) (oks : X₁.map (hbOks η) = X₂.map (hbOks η))

include oks in
theorem len_eq (t : Nat) : (Lf η X₁ t).length = (Lf η X₂ t).length :=
  rbFold_length_congr rfl (by rw [List.map_take, List.map_take, oks])

include hX₁ hX₂ oks in
theorem ok_eq {t : Nat} (ht : t < N) : hbOks η (zAt X₁ t) = hbOks η (zAt X₂ t) := by
  have h := congrArg (fun L => L[t]?) oks
  simp only [List.getElem?_map, List.getElem?_eq_getElem (show t < X₁.length by omega_arith),
    List.getElem?_eq_getElem (show t < X₂.length by omega_arith), Option.map_some, Option.some.injEq] at h
  rw [zAt, zAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show t < X₁.length by omega_arith), List.getElem?_eq_getElem (show t < X₂.length by omega_arith)]
  exact h

theorem tryJ_length_congr {L₁ L₂ : List Zq} (hl : L₁.length = L₂.length) {b₁ b₂ : Nat}
    (hok : halfByteOk η b₁ = halfByteOk η b₂) : (tryJ η L₁ b₁).length = (tryJ η L₂ b₂).length := by
  rw [tryJ_length, tryJ_length, hl, hok]

include hp₁ hp₂ hsp h5 h6 hη hX₁ hX₂ oks in
/-- An iteration, in two runs. -/
theorem body_ct {t : Nat} (ht : t < N) :
    RelCT isa (fun a b => Base σ₁ X₁ t (Lf η X₁ t) a ∧ Base σ₂ X₂ t (Lf η X₂ t) b) (rbBody η)
      fun a b => (Base σ₁ X₁ (t + 1) (Lf η X₁ (t + 1)) a ∧
          (a.gpr .r12 != 0) = decide (t + 1 ≠ N ∧ (Lf η X₁ (t + 1)).length < 256)) ∧
        (Base σ₂ X₂ (t + 1) (Lf η X₂ (t + 1)) b ∧
          (b.gpr .r12 != 0) = decide (t + 1 ≠ N ∧ (Lf η X₂ (t + 1)).length < 256)) := by
  refine relct_wp ?_ fun a b hab => ⟨by
      have k := body_ok hp₁ hη (X := X₁) (by rw [hX₁]; exact ht) hab.1; rwa [hX₁] at k, by
      have k := body_ok hp₂ hη (X := X₂) (by rw [hX₂]; exact ht) hab.2; rwa [hX₂] at k⟩
  have hl := len_eq oks t
  have hok := ok_eq hX₁ hX₂ oks ht
  simp only [hbOks, Prod.mk.injEq] at hok
  have hlo₁ : (zAt X₁ t).toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  have hlo₂ : (zAt X₂ t).toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  have hhi₁ : (zAt X₁ t).toNat / 16 < 16 := by have := (zAt X₁ t).isLt; omega_arith
  have hhi₂ : (zAt X₂ t).toNat / 16 < 16 := by have := (zAt X₂ t).isLt; omega_arith
  -- the byte and its low half-byte
  refine RelCT.seq (R := fun a b =>
      H1 η σ₁ X₁ t (Lf η X₁ t) ((zAt X₁ t).toNat % 16) ((zAt X₁ t).setWidth 64) a ∧
      H1 η σ₂ X₂ t (Lf η X₂ t) ((zAt X₂ t).toNat % 16) ((zAt X₂ t).setWidth 64) b)
    (relct_wp (load_ct hη (fun a b hab => base_sp hab.1 hab.2 hsp) fun a b hab => by
      rw [hab.1.r3, hab.2.r3, h6]) fun a b hab => ⟨loHalf_ok hp₁ hη (hX₁ ▸ ht) hab.1, loHalf_ok hp₂ hη (hX₂ ▸ ht) hab.2⟩) ?_
  -- its try
  refine RelCT.seq (try_ct hp₁ hp₂ hsp h5 hη hl hlo₁ hlo₂ hok.1) ?_
  -- the high half-byte
  have hl' := tryJ_length_congr (η := η) hl hok.1
  refine RelCT.seq (R := fun a b =>
      H1 η σ₁ X₁ t (tryJ η (Lf η X₁ t) ((zAt X₁ t).toNat % 16)) ((zAt X₁ t).toNat / 16) ((zAt X₁ t).setWidth 64) a ∧
      H1 η σ₂ X₂ t (tryJ η (Lf η X₂ t) ((zAt X₂ t).toNat % 16)) ((zAt X₂ t).toNat / 16) ((zAt X₂ t).setWidth 64) b)
    (relct_wp (hi_ct hη) fun a b hab => ⟨hiHalf_ok hp₁ hη hab.1.1 hab.1.2, hiHalf_ok hp₂ hη hab.2.1 hab.2.2⟩) ?_
  -- its try, and the step
  exact RelCT.seq (try_ct hp₁ hp₂ hsp h5 hη hl' hhi₁ hhi₂ hok.2) (relct_noMem rfl)

include hp₁ hp₂ hsp h5 h6 hη hX₁ hX₂ oks in
/-- The loop, until the last byte or 256 coefficients, which are then those
of all `N` bytes. -/
theorem loop_ct (hN : 0 < N) :
    RelCT isa (fun a b => Base σ₁ X₁ 0 (Lf η X₁ 0) a ∧ Base σ₂ X₂ 0 (Lf η X₂ 0) b) (.loop (rbBody η) (.nonzero .d .r12))
      fun a b => ∃ t, Base σ₁ X₁ t (Lf η X₁ N) a ∧ Base σ₂ X₂ t (Lf η X₂ N) b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rbBody η) (c := .nonzero .d .r12)
    (Q := fun a b => ∃ t, Base σ₁ X₁ t (Lf η X₁ N) a ∧ Base σ₂ X₂ t (Lf η X₂ N) b)
    (fun n a b => ∃ t, t < N ∧ n = N - t ∧ Base σ₁ X₁ t (Lf η X₁ t) a ∧ Base σ₂ X₂ t (Lf η X₂ t) b)
    (fun n => ?_) N) (fun a b hab => ⟨0, hN, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < N ∧ n = N - t ∧ Base σ₁ X₁ t (Lf η X₁ t) a ∧
      Base σ₂ X₂ t (Lf η X₂ t) b) (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < N
  · by_cases hn : n = N - t
    · have hl := len_eq oks (t + 1)
      refine RelCT.mono (P := fun a b => Base σ₁ X₁ t (Lf η X₁ t) a ∧ Base σ₂ X₂ t (Lf η X₂ t) b)
        (body_ct hp₁ hp₂ hsp h5 h6 hη hX₁ hX₂ oks ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · rw [eval_nonzero, eval_nonzero, z₁, z₂, hl]
      · have hc : ¬ (t + 1 ≠ N ∧ (Lf η X₁ (t + 1)).length < 256) := by
          have e' : (a.gpr .r12 != 0) = false := by rw [eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        have hle₁ : (Lf η X₁ (t + 1)).length ≤ 256 := rbFold_length_le (by simp) _
        have hstop : t + 1 = N ∨ (Lf η X₁ (t + 1)).length = 256 := by
          by_cases e : t + 1 = N
          · exact .inl e
          · exact .inr (by have := not_and.mp hc e; omega_using [hle₁, this])
        refine ⟨t + 1, ?_, ?_⟩
        · rw [Lf_stop (by omega_using [ht]) hstop]; exact i₁
        · rw [Lf_stop (by omega_using [ht]) (hstop.imp id fun h => hl ▸ h)]; exact i₂
      · have hc : t + 1 ≠ N ∧ (Lf η X₁ (t + 1)).length < 256 := by
          have e' : (a.gpr .r12 != 0) = true := by rw [eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨N - (t + 1), by omega_arith, t + 1, by omega_arith, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

end

end VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

end

end

/-!
# ML-DSA on PPC64LE: `vg_mldsa_rej_bounded_poly`, constant time and `Verified`

As on 32-bit ARM (`Proof/MlDsa/Arm/KeyGen/Inst.lean`). Two runs from
entry states that agree on the public data (the pointers, the low 32 bits of
`η`, the stack pointer, and which half-bytes of the XOF output are accepted,
`rejBoundedLeak`) leak the same trace (`all_ct`): the prologue and the blocks
around the loops by the taint analysis, each try (`rbTry_ct`) by `sponge_ct`,
the branch on `η` because `η` zero-extended is the same in both runs, and the
loop iteration by iteration (`loop_ct`), since the half-bytes of the first
544 bytes of output are accepted alike (`leak_hbOks`); so the tries sample as
many coefficients, and the test of whether the first sampled 256 agrees.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Proof.MlDsa.Sample (hbOks leak_hbOks rejBounded_some rejBounded_none stored_polyIs ifT ifF rbFold
  H_length)
open VG.Proof.MlKem.PPC64LE (relct_noMem relct_nil)
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)
open VG.Spec.MlDsa (H rejBoundedLeak)
open VG.Proof.MlDsa (rejBoundedContract rejBoundedSig)
open VG.Spec.Sha3 (bytesAt)

theorem zx_congr {x y : BitVec 64} (h : x.setWidth 32 = y.setWidth 32) : zx x = zx y :=
  BitVec.eq_of_toNat_eq (by rw [zx_toNat, zx_toNat, h])

theorem Lf_zero (η : Nat) (X : List Byte) : Lf η X 0 = [] := by simp [Lf, rbFold]

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  hp₁ : SpOk (spOf σ₁) σ₁
  hp₂ : SpOk (spOf σ₂) σ₂
  hη : etaOf σ₁ = 2 ∨ etaOf σ₁ = 4
  sp : σ₁.sp = σ₂.sp
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3
  r4 : (σ₁.gpr .r4).setWidth 32 = (σ₂.gpr .r4).setWidth 32
  r5 : σ₁.gpr .r5 = σ₂.gpr .r5
  r6 : σ₁.gpr .r6 = σ₂.gpr .r6
  leak : rejBoundedLeak (etaOf σ₁) ((spOf σ₁).msg σ₁) = rejBoundedLeak (etaOf σ₂) ((spOf σ₂).msg σ₂)

section
variable {σ₁ σ₂ : State} (h : Two σ₁ σ₂)
include h

theorem sp_eq : spOf σ₂ = spOf σ₁ := by simp only [spOf, h.r3, h.r5, h.r6]

theorem eta_eq : etaOf σ₂ = etaOf σ₁ := by simp only [etaOf, h.r4]

theorem oks (n : Nat) (hn : n ≤ 544) : (X n σ₁).map (hbOks (etaOf σ₁)) = (X n σ₂).map (hbOks (etaOf σ₁)) := by
  have hl := h.leak
  rw [eta_eq h] at hl
  exact leak_hbOks hl (B := n) (Nat.le_trans hn (by decide))

/-- The loop for `η` over `n` bytes, from the sponge's output. -/
theorem rbLoop_ct {η : Nat} (hη : η = 2 ∨ η = 4) {n : Nat} (hn0 : 0 < n) (hn : n ≤ 544)
    (ho : (X n σ₁).map (hbOks η) = (X n σ₂).map (hbOks η)) :
    RelCT isa (fun a b => SJ n σ₁ a ∧ SJ n σ₂ b) (rbLoop η n)
      fun a b => ∃ t, Base σ₁ (X n σ₁) t (Lf η (X n σ₁) n) a ∧ Base σ₂ (X n σ₂) t (Lf η (X n σ₂) n) b := by
  refine RelCT.seq (R := fun (a b : State) => Base σ₁ (X n σ₁) 0 (Lf η (X n σ₁) 0) a ∧
      Base σ₂ (X n σ₂) 0 (Lf η (X n σ₂) 0) b)
    (relct_wp (relct_noMem rfl) fun a b ⟨ha, hb⟩ => ⟨?_, ?_⟩)
    (loop_ct h.hp₁ h.hp₂ h.sp h.r5 h.r6 hη (X_length n σ₁) (X_length n σ₂) ho hn0)
  · rw [Lf_zero]; exact init_ok h.hp₁ hn ha
  · rw [Lf_zero]; exact init_ok h.hp₂ hn hb

/-- A try with `n` bytes: the sponge, the branch on `η`, and the loop. -/
theorem rbTry_ct {n : Nat} (hn0 : 0 < n) (hn : n ≤ 544) :
    RelCT isa (fun a b => (J0 (spOf σ₁) σ₁ a ∧ a.gpr .r27 = zx (σ₁.gpr .r4)) ∧
      (J0 (spOf σ₁) σ₂ b ∧ b.gpr .r27 = zx (σ₁.gpr .r4))) (rbTry n)
      fun a b => ∃ t, Base σ₁ (X n σ₁) t (Lf (etaOf σ₁) (X n σ₁) n) a ∧
        Base σ₂ (X n σ₂) t (Lf (etaOf σ₁) (X n σ₂) n) b := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  have eP := sp_eq h
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ hp₂
  have ez : zx (σ₂.gpr .r4) = zx (σ₁.gpr .r4) := zx_congr h.r4.symm
  -- the sponge
  refine RelCT.seq (R := fun (a b : State) => SJ n σ₁ a ∧
      ((∃ y, J6 136 n (spOf σ₁) σ₂ y b) ∧ b.gpr .r27 = zx (σ₁.gpr .r4)))
    (relct_wp (RelCT.mono (sponge_ct hp₁ hp₂' h.sp (rate := 136) (outlen := n) (by decide) (by omega_using [hn]))
      (fun a b hab => ⟨hab.1.1, hab.2.1⟩) fun _ _ h => h) fun a b hab =>
      ⟨WP.mono (sponge_ok hp₁ (by decide) (by omega_using [hn]) hab.1.1) fun _ x => ⟨⟨_, x⟩, (x.gp .r27 (by decide)).trans hab.1.2⟩,
        WP.mono (sponge_ok hp₂' (by decide) (by omega_using [hn]) hab.2.1) fun _ x =>
          ⟨⟨_, x⟩, (x.gp .r27 (by decide)).trans hab.2.2⟩⟩) ?_
  -- the branch on `η`, and the loop
  refine RelCT.seq (R := fun (a b : State) => (SJ n σ₁ a ∧ a.gpr .r12 = zx (σ₁.gpr .r4) - BitVec.ofNat 64 2) ∧
      (SJ n σ₂ b ∧ b.gpr .r12 = zx (σ₁.gpr .r4) - BitVec.ofNat 64 2))
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨cmp_ok hp₁ hab.1, ?_⟩) ?_
  · obtain ⟨⟨y, hy⟩, e27⟩ := hab.2
    have sj : SJ n σ₂ b := ⟨⟨y, by rw [eP]; exact hy⟩, e27.trans ez.symm⟩
    exact WP.mono (cmp_ok hp₂ sj) fun s' ⟨hs, e⟩ => ⟨hs, e.trans (by rw [ez])⟩
  have ho := oks h n hn
  have hz : ∀ a b, ((SJ n σ₁ a ∧ a.gpr .r12 = zx (σ₁.gpr .r4) - BitVec.ofNat 64 2) ∧
      (SJ n σ₂ b ∧ b.gpr .r12 = zx (σ₁.gpr .r4) - BitVec.ofNat 64 2)) →
      isa.eval (.zero .d .r12) a = some (decide (etaOf σ₁ = 2)) ∧
        isa.eval (.zero .d .r12) b = isa.eval (.zero .d .r12) a :=
    fun a b hab => ⟨by rw [eval_zero, hab.1.2, eta_test], by rw [eval_zero, eval_zero, hab.1.2, hab.2.2]⟩
  rcases h.hη with e | e
  · rw [e] at ho ⊢
    refine RelCT.ite (fun a b hab => (hz a b hab).2.symm)
      (RelCT.mono (rbLoop_ct h (η := 2) (.inl rfl) hn0 hn ho) (fun a b hab => ⟨hab.1.1.1, hab.1.2.1⟩)
        fun _ _ h => h)
      (RelCT.of_false fun a b ⟨hab, he⟩ => by rw [(hz a b hab).1, e] at he; exact absurd he (by decide))
  · rw [e] at ho ⊢
    refine RelCT.ite (fun a b hab => (hz a b hab).2.symm)
      (RelCT.of_false fun a b ⟨hab, he⟩ => by rw [(hz a b hab).1, e] at he; exact absurd he (by decide))
      (RelCT.mono (rbLoop_ct h (η := 4) (.inr rfl) hn0 hn ho) (fun a b hab => ⟨hab.1.1.1, hab.1.2.1⟩)
        fun _ _ h => h)

/-- The whole function. -/
theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.PPC64LE.Sample.rejBounded fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  have eP := sp_eq h
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ hp₂
  have ez : zx (σ₂.gpr .r4) = zx (σ₁.gpr .r4) := zx_congr h.r4.symm
  -- the prologue
  refine RelCT.seq (R := fun (a b : State) => (J0 (spOf σ₁) σ₁ a ∧ a.gpr .r27 = zx (σ₁.gpr .r4)) ∧
      (J0 (spOf σ₁) σ₂ b ∧ b.gpr .r27 = zx (σ₁.gpr .r4)))
    (relct_wp (pro_rb_ct (fun a b hab => by rw [hab.1, hab.2]; exact h.sp)
      fun a b hab => by rw [hab.1, hab.2]; exact h.r6) fun a b hab => ⟨?_, ?_⟩) ?_
  · rw [hab.1]; exact pro_rb hp₁ rfl rfl rfl rfl
  · rw [hab.2]; exact WP.mono (pro_rb hp₂' h.r3.symm h.r5.symm h.r6.symm rfl) fun _ x => ⟨x.1, x.2.trans ez⟩
  -- the try with 272 bytes
  refine RelCT.seq (rbTry_ct h (n := 272) (by decide) (by decide)) (RelCT.exists_ fun t => ?_)
  -- the test of `j = 256`, and the try with 544 bytes if it fails
  refine RelCT.seq (R := fun (a b : State) => (∃ X t L, Base σ₁ X t L a) ∧ (∃ X t L, Base σ₂ X t L b)) ?_ ?_
  · refine RelCT.seq (R := fun (a b : State) =>
        (Base σ₁ (X 272 σ₁) t (Lf (etaOf σ₁) (X 272 σ₁) 272) a ∧
          isa.eval (.zero .d .r12) a = some (decide ((Lf (etaOf σ₁) (X 272 σ₁) 272).length = 256))) ∧
        (Base σ₂ (X 272 σ₂) t (Lf (etaOf σ₁) (X 272 σ₂) 272) b ∧
          isa.eval (.zero .d .r12) b = some (decide ((Lf (etaOf σ₁) (X 272 σ₂) 272).length = 256))))
      (relct_wp (relct_noMem rfl) fun a b hab => ⟨jtest_ok hp₁ hab.1, jtest_ok hp₂ hab.2⟩) ?_
    have hl := len_eq (oks h 272 (by decide)) 272
    refine RelCT.ite (fun a b hab => by rw [hab.1.2, hab.2.2, hl]) ?_ ?_
    · exact RelCT.mono relct_nil (fun _ _ h => h) fun a b hab => ⟨⟨_, _, _, hab.1.1.1⟩, ⟨_, _, _, hab.1.2.1⟩⟩
    · refine RelCT.mono (rbTry_ct h (n := 544) (by decide) (by decide)) (fun a b hab => ⟨?_, ?_⟩)
        fun a b ⟨_, hab⟩ => ⟨⟨_, _, _, hab.1⟩, ⟨_, _, _, hab.2⟩⟩
      · exact ⟨⟨hab.1.1.1.env, hab.1.1.1.r29, hab.1.1.1.r28⟩, hab.1.1.1.r27⟩
      · have b₂ := hab.1.2.1
        exact ⟨eP ▸ ⟨b₂.env, b₂.r29, b₂.r28⟩, b₂.r27.trans ez⟩
  -- the end
  exact retEpi_ct (fun a b ⟨⟨_, _, _, ha⟩, ⟨_, _, _, hb⟩⟩ => base_sp ha hb h.sp)
    fun a b ⟨⟨_, _, _, ha⟩, ⟨_, _, _, hb⟩⟩ => by rw [ha.env.r31, hb.env.r31]; exact h.r6

end

/-! ## `Verified` -/

/-- The precondition, as `SpOk` and `η`. -/
theorem pre_of {s : State} (h : (rejBoundedContract PPC64LE.abi 48).pre s) :
    SpOk (spOf s) s ∧ (etaOf s = 2 ∨ etaOf s = 4) := by
  sig_pre [rejBoundedContract, rejBoundedSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, d1, d2, d3, b1, b2, b3, -, fa, fscr, he⟩ := h
  exact ⟨⟨by rw [h1]; exact List.mem_singleton_self _, h2, d1, d2, d3, b1, b2, b3,
    show (66 : Nat) < 2 ^ 64 by decide, fa, fscr, h0⟩, he⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 2 | .r5 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

namespace VG.Proof.MlDsa.PPC64LE.Sample

open VG VG.PPC64LE
open VG.Proof.MlDsa.Sample (rbFold rejBounded_some rejBounded_none stored_polyIs ifT ifF)
open VG.Proof.MlDsa (rejBoundedContract rejBoundedSig)
open RejBounded

theorem rejBounded_verified :
    Verified PPC64LE.target Impl.MlDsa.PPC64LE.Sample.rejBounded (rejBoundedContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨satState, ?_⟩⟩
  · obtain ⟨hp, hη⟩ := pre_of hs
    obtain ⟨t, s', he, h3, hst, ha⟩ := correct hp hη
    refine ⟨t, s', he, ha, ?_⟩
    have key : ∀ n, Lf (etaOf s) (X n s) n = rbFold (etaOf s) [] (X n s) := fun n => by
      simp only [Lf]; rw [List.take_of_length_le (by rw [X_length])]
    sig_post [rejBoundedContract, rejBoundedSig, PPC64LE.abi, PPC64LE.argRegs]
    rw [h3]
    by_cases h1 : (Lf (etaOf s) (X 272 s) 272).length = 256
    · have eL : Lr (etaOf s) s = rbFold (etaOf s) [] (X 272 s) := by rw [Lr, ifT h1, key]
      rw [key] at h1
      rw [eL] at hst ⊢
      rw [ifT h1]
      obtain ⟨hred, hpoly⟩ := stored_polyIs hst h1
      exact ⟨fun _ => hred, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejBounded := 272 }, by
        show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 272 _) = _
        exact (rejBounded_some _ h1).trans (congrArg some hpoly.symm)⟩⟩
    · have eL : Lr (etaOf s) s = rbFold (etaOf s) [] (X 544 s) := by rw [Lr, ifF h1, key]
      rw [eL] at hst ⊢
      by_cases hf : (rbFold (etaOf s) [] (X 544 s)).length = 256
      · rw [ifT hf]
        obtain ⟨hred, hpoly⟩ := stored_polyIs hst hf
        exact ⟨fun _ => hred, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejBounded := 544 }, by
          show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 544 _) = _
          exact (rejBounded_some _ hf).trans (congrArg some hpoly.symm)⟩⟩
      · rw [ifF hf]
        exact ⟨fun h1 => absurd h1 (by decide), .inr ⟨rfl, by
          show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 481 _) = none
          exact (congrArg (Option.map _) (rejBounded_none _ (B := 544) (by decide) hf)).trans rfl⟩⟩
  · obtain ⟨hp₁, hη⟩ := pre_of h₁
    obtain ⟨hp₂, -⟩ := pre_of h₂
    sig_pub [rejBoundedContract, rejBoundedSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hl, h3, h4, h5, h6⟩ := hpub
    exact (all_ct ⟨hp₁, hp₂, hη, hsp, h3, h4, h5, h6, hl⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · sig_apply_check
    · decide +kernel
    · sig_reduce [rejBoundedContract, rejBoundedSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Sample

end

end

/-!
# ML-DSA key generation on PPC64LE, with this library's primitives

The PPC64LE implementations of the primitives (`prims`) are verified with at
most 96 bytes of stack, and their frames use no more (`prims_ok`), so key
generation with them is verified with 96 (`keyGen44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen

theorem prims_ok : PrimsOk prims 96 where
  ntt := ⟨⟨96, by decide, VNtt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨96, by decide, VNtt.iverified⟩, by decide +kernel⟩
  mul := ⟨⟨0, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨0, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  add := ⟨⟨0, by decide, Arith.AddSub.add_verified⟩, by decide +kernel⟩
  rejNtt := ⟨⟨48, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  rejBounded := ⟨⟨48, by decide, Sample.rejBounded_verified⟩, by decide +kernel⟩
  power2Round := ⟨⟨0, by decide, Round.Power2Round.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitPack := ⟨⟨0, by decide, Pack.bitPack_verified⟩, by decide +kernel⟩

theorem keyGen44_sat : (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 PPC64LE.abi 96).pre (keyGenSat Spec.MlDsa.mlDsa44) := by
  sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, PPC64LE.abi, PPC64LE.argRegs, keyGenSat]

theorem keyGen44_verified :
    Verified PPC64LE.target keyGen44 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 PPC64LE.abi 96) :=
  keyGen_verified prims_ok (by decide) _ (.inl rfl) keyGen44_sat

theorem keyGen65_sat : (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 PPC64LE.abi 96).pre (keyGenSat Spec.MlDsa.mlDsa65) := by
  sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, PPC64LE.abi, PPC64LE.argRegs, keyGenSat]

theorem keyGen65_verified :
    Verified PPC64LE.target keyGen65 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 PPC64LE.abi 96) :=
  keyGen_verified prims_ok (by decide) _ (.inr (.inl rfl)) keyGen65_sat

theorem keyGen87_sat : (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 PPC64LE.abi 96).pre (keyGenSat Spec.MlDsa.mlDsa87) := by
  sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, PPC64LE.abi, PPC64LE.argRegs, keyGenSat]

theorem keyGen87_verified :
    Verified PPC64LE.target keyGen87 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 PPC64LE.abi 96) :=
  keyGen_verified prims_ok (by decide) _ (.inr (.inr rfl)) keyGen87_sat

end VG.Proof.MlDsa.PPC64LE.KeyGen
