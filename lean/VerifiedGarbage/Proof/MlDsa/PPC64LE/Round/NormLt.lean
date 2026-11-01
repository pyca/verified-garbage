module

import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.Arith
public import VerifiedGarbage.Proof.MlDsa.Round.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.Arith
meta import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Round
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.MlDsa.Contract

/-!
# ML-DSA on PPC64LE: `vg_mldsa_norm_lt`

One symbolic execution of the loop body, for any pointer (`body_ok`), which
ands into `r9` the bit `ok a` (`ok_toNat`: 1 exactly when `a < bound` or
`q - a < bound`, `normZq_lt`); the invariant says `r9` is 1 exactly when
every coefficient so far is in bounds (`Inv`), and `normRq_lt` turns that
into the norm.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Round.NormLt

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Round
open VG.Impl.MlDsa.PPC64LE.Arith (loadImm loadQ)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (pR coeff_contains polyAt_val normZq_lt normRq_lt reduced_zero)
open VG.Proof.MlKem.PPC64LE (wp_loop_nz count_sub count_nz ptr_succ)

/-! ## Values -/

/-- The bit the body ands in, for the coefficient `a` and the bound `b`. -/
def ok (a b : BitVec 64) : BitVec 64 := (a - b) >>> 63 ||| (8380417 - a - b) >>> 63

theorem ok_toNat {a b : BitVec 64} (ha : a.toNat < q) (hb : b.toNat < 2 ^ 32) :
    ok a b = if a.toNat < b.toNat ∨ q - a.toNat < b.toNat then 1 else 0 := by
  rw [VG.Proof.MlDsa.Round.q_eq] at ha ⊢
  unfold ok
  split <;> rename_i h
  · rcases h with h | h
    · have : (a - b) >>> 63 = 1 := by bv_omega
      rw [this]
      have : (8380417 - a - b) >>> 63 = 0 ∨ (8380417 - a - b) >>> 63 = 1 := by bv_omega
      rcases this with e | e <;> rw [e] <;> decide
    · have : (8380417 - a - b) >>> 63 = 1 := by bv_omega
      rw [this]
      have : (a - b) >>> 63 = 0 ∨ (a - b) >>> 63 = 1 := by bv_omega
      rcases this with e | e <;> rw [e] <;> decide
  · have h1 : (a - b) >>> 63 = 0 := by bv_omega
    have h2 : (8380417 - a - b) >>> 63 = 0 := by bv_omega
    rw [h1, h2]; decide

/-! ## The loop body -/

section
variable {s : State} {x c v : BitVec 64} (h3 : s.gpr .r3 = x) (h5 : s.gpr .r5 = 8380417) (h9 : s.gpr .r9 = v)
  (h10 : s.gpr .r10 = c) (ia : InRegions (s.rd ++ s.wr) x 4)
include h3 h5 h9 h10 ia

theorem body_ok :
    WP isa (.block nlBody) s fun s' =>
      s'.gpr .r3 = x + 4 ∧ s'.gpr .r10 = c - 1 ∧ s'.gpr .r4 = s.gpr .r4 ∧ s'.gpr .r5 = 8380417 ∧
      s'.gpr .r9 = v &&& ok ((s.mem.readW x 32).setWidth 64) (s.gpr .r4) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  crun [nlBody, ok, h3, h5, h9, h10, ia, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  simp [Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev Fp : Addr := s₀.gpr .r3
abbrev B : BitVec 64 := (s₀.gpr .r4).setWidth 32 |>.setWidth 64

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [pR (Fp s₀)]
  wr : s₀.wr = []
  fit : (Fp s₀).toNat + 1024 ≤ 2 ^ 64
  red : Reduced s₀.mem (Fp s₀)

/-- All of the first `i` coefficients are in bounds. -/
def AllOk (s₀ : State) (i : Nat) : Prop :=
  ∀ j < i, normZq (polyAt s₀.mem (Fp s₀))[j]! < (B s₀).toNat

instance (s₀ : State) (i : Nat) : Decidable (AllOk s₀ i) := by unfold AllOk; infer_instance

/-- After `i` iterations. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = Fp s₀ + BitVec.ofNat 64 (4 * i)
  r4 : s.gpr .r4 = B s₀
  r5 : s.gpr .r5 = 8380417
  r9 : s.gpr .r9 = if AllOk s₀ i then 1 else 0
  r10 : s.gpr .r10 = BitVec.ofNat 64 (256 - i)
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r

theorem ite_and_ite (a b : Prop) [Decidable a] [Decidable b] :
    ((if a then 1 else 0 : BitVec 64) &&& if b then 1 else 0) = if a ∧ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

theorem allOk_succ (s₀ : State) {i : Nat} (hi : i < 256) :
    AllOk s₀ (i + 1) ↔ AllOk s₀ i ∧ normZq (polyAt s₀.mem (Fp s₀))[i]! < (B s₀).toNat := by
  unfold AllOk
  constructor
  · intro h; exact ⟨fun j hj => h j (by omega), h i (by omega)⟩
  · intro ⟨h, h'⟩ j hj
    by_cases e : j = i
    · subst e; exact h'
    · exact h j (by omega)

theorem inv_step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {s : State} (h : Inv s₀ i s) :
    WP isa (.block nlBody) s fun s' => Inv s₀ (i + 1) s' ∧ (s'.gpr .r10 != 0) = decide (i + 1 ≠ 256) := by
  have cF := coeff_contains (Fp s₀) (i := i) hi
  refine WP.mono (body_ok h.r3 h.r5 h.r9 h.r10 (by rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cF⟩))
    fun s' ⟨r3, r10, r4, r5, r9, m, rd, wr, sp, lr, pres⟩ => ⟨⟨?_, r4.trans h.r4, r5, ?_, ?_, m.trans h.mem,
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, lr.trans h.lr, fun r hr => (pres r hr).trans (h.pres r hr)⟩, ?_⟩
  · rw [r3]; exact ptr_succ _ 4 i
  · have hv := polyAt_val hp.red (i := i) hi
    have ha : ((s.mem.readW (Fp s₀ + BitVec.ofNat 64 (4 * i)) 32).setWidth 64).toNat =
        ((polyAt s₀.mem (Fp s₀))[i]!).val := by
      rw [h.mem, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (coeffAt s₀.mem (Fp s₀) i).isLt; omega)]
      exact hv.symm
    have hb : (s.gpr .r4).toNat < 2 ^ 32 := by
      rw [h.r4, B, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by decide))
    rw [r9, ok_toNat (by rw [ha]; exact Fin.isLt _) hb, ha, h.r4]
    have e := allOk_succ s₀ hi
    rw [normZq_lt] at e
    rw [ite_and_ite]
    by_cases hc : AllOk s₀ (i + 1)
    · rw [ite_eq_left hc, ite_eq_left (e.mp hc)]
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc (e.mpr h'))]
  · rw [r10]; exact count_sub hi
  · rw [r10, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]; exact count_nz hi (by decide)

/-- The result, after the loop. -/
def Post (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
    s.gpr .r3 = if AllOk s₀ 256 then 1 else 0

theorem exit_ok {s₀ s : State} (h : Inv s₀ 256 s) : WP isa (.block [.logic .or .r3 .r9 .r9]) s (Post s₀) := by
  refine WP.cons exec_logic (wp_nil ⟨?_, h.sp, h.lr, ?_⟩)
  · intro r hr
    have : ¬r = .r3 := by revert r hr; decide
    rw [RegUpd.gpr_write_of_ne _ _ this]; exact h.pres r hr
  · rw [RegUpd.gpr_write_self, BitVec.or_self]; exact h.r9

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa normLt s₀ (Post s₀) := by
  refine WP.seq (WP.cons (exec_lsr_w (by decide)) (WP.cons (exec_li (by decide)) (WP.cons (exec_li (by decide))
    (WP.cons exec_lis (WP.cons exec_ori (wp_nil ?_))))))
  refine WP.seq (wp_loop_nz (Inv s₀) (N := 256) (by decide) (fun i hi s h => inv_step hp hi h)
    (fun s h => exit_ok h) ?_)
  refine ⟨by simp [State.write], by simp [State.write, B], ?_, ?_, by simp [State.write], rfl, rfl, rfl, rfl, rfl,
    fun r hr => ?_⟩
  · simp only [State.write, reduceCtorEq, ite_false, ite_true]
    exact VG.Proof.MlDsa.PPC64LE.Arith.loadImm_val (by decide)
  · have : AllOk s₀ 0 := fun j hj => absurd hj (Nat.not_lt_zero j)
    simp [State.write, this]
  · have : r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r9 ∧ r ≠ .r10 := by revert r hr; decide
    simp [State.write, this.1, this.2.1, this.2.2.1, this.2.2.2]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.normLtContract PPC64LE.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := []

theorem verified : Verified PPC64LE.target normLt (Proof.MlDsa.normLtContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.PPC64LE.Add.ctRegs [.r3] (fun s₁ s₂ h => ?_)
    (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := correct hp
    refine ⟨t, s', he, ⟨h.1, h.2.1, h.2.2.1⟩, ?_⟩
    sig_post [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, PPC64LE.abi, PPC64LE.argRegs]
    rw [h.2.2.2]
    have e : AllOk s 256 ↔ normRq [polyAt s.mem (Fp s)] < (B s).toNat := by
      rw [normRq_lt]; rfl
    have eb : (B s).toNat = ((s.gpr .r4).setWidth 32).toNat := by
      simp only [B, BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
    rw [eb] at e
    by_cases hc : AllOk s 256
    · rw [ite_eq_left hc, ite_eq_left (e.mp hc)]; rfl
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc (e.mpr h'))]; rfl
  · sig_pub [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, PPC64LE.abi, PPC64LE.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.2.1
  · sig_pub [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, PPC64LE.abi, PPC64LE.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Round.NormLt
