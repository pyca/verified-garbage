module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Spec.MlDsa
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Spec.MlDsa
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Straight
meta import VerifiedGarbage.Proof.Framework.RISCV64.Straight
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# ML-DSA on RISC-V: `vg_mldsa_add` and `vg_mldsa_sub`

ML-KEM's loops (`Proof/MlKem/RISCV64/Add.lean`) with `q = 8380417` in `a5`:
one symbolic execution of each loop body, for any pointers (`addBody_ok`,
`subBody_ok`); the loop invariant says which coefficients of `f` are done
(`Inv`); the arithmetic is `fixd_add` and `fixd_sub`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Arith.AddSub

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Arith
open VG.Impl.MlKem.RISCV64 (fixup accTail addBody subBody)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.RISCV64.Arith
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_succ align4_add toNat_setWidth64)

/-! ## The loop bodies -/

/-- What an iteration of either loop does, but for the value stored. -/
def Step (s : State) (x y c : BitVec 64) (v : BitVec 32) (s' : State) : Prop :=
  s'.gpr .a0 = x + 4 ∧ s'.gpr .a1 = y + 4 ∧ s'.gpr .a2 = c - 1 ∧ s'.gpr .a5 = s.gpr .a5 ∧
    s'.mem = s.mem.writeW x v ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .ra = s.gpr .ra ∧
    ∀ r ∈ preserved, s'.gpr r = s.gpr r

section
variable {s : State} {x y c : BitVec 64} (h3 : s.gpr .a0 = x) (h4 : s.gpr .a1 = y) (h5 : s.gpr .a2 = c)
  (h8 : s.gpr .a5 = 8380417)
  (ia : InRegions (s.rd ++ s.wr) x 4) (ib : InRegions (s.rd ++ s.wr) y 4) (oa : InRegions s.wr x 4)
  (ax : x.toNat % 4 = 0) (ay : y.toNat % 4 = 0)
include h3 h4 h5 h8 ia ib oa ax ay

theorem addBody_ok :
    WP isa (.block addBody) s (Step s x y c ((fixd ((s.mem.readW x 32).setWidth 64 +
      (s.mem.readW y 32).setWidth 64 - 8380417)).setWidth 32)) := by
  crun [addBody, fixup, accTail, Step, fixd, h3, h4, h5, h8, ia, ib, oa, ax, ay, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

theorem subBody_ok :
    WP isa (.block subBody) s (Step s x y c ((fixd ((s.mem.readW x 32).setWidth 64 -
      (s.mem.readW y 32).setWidth 64)).setWidth 32)) := by
  crun [subBody, fixup, accTail, Step, fixd, h3, h4, h5, h8, ia, ib, oa, ax, ay, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev F : Addr := s₀.gpr .a0
abbrev G : Addr := s₀.gpr .a1

end

/-- The precondition of both functions. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (G s₀)]
  wr : s₀.wr = [polyRegion (F s₀)]
  disj : (polyRegion (F s₀)).Disjoint (polyRegion (G s₀))
  fitF : (F s₀).toNat + 1024 ≤ 2 ^ 64
  fitG : (G s₀).toNat + 1024 ≤ 2 ^ 64
  redF : Reduced s₀.mem (F s₀)
  redG : Reduced s₀.mem (G s₀)
  alF : (F s₀).toNat % 4 = 0
  alG : (G s₀).toNat % 4 = 0

/-- After `i` iterations, writing `out j` to coefficient `j`. -/
structure Inv (out : Nat → BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = F s₀ + BitVec.ofNat 64 (4 * i)
  a1 : s.gpr .a1 = G s₀ + BitVec.ofNat 64 (4 * i)
  a2 : s.gpr .a2 = BitVec.ofNat 64 (256 - i)
  a5 : s.gpr .a5 = 8380417
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  ra : s.gpr .ra = s₀.gpr .ra
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (F s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (F s₀) j = if j < i then out j else coeffAt s₀.mem (F s₀) j

/-- One iteration, from the value the body stores. -/
theorem inv_step {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256)
    {s : State} (h : Inv out s₀ i s) {body : List Instr}
    (hb : ∀ {x y c : BitVec 64}, s.gpr .a0 = x → s.gpr .a1 = y → s.gpr .a2 = c →
      InRegions (s.rd ++ s.wr) x 4 → InRegions (s.rd ++ s.wr) y 4 → InRegions s.wr x 4 →
      x.toNat % 4 = 0 → y.toNat % 4 = 0 → WP isa (.block body) s (Step s x y c (out i))) :
    WP isa (.block body) s fun s' => Inv out s₀ (i + 1) s' ∧ (s'.gpr .a2 != 0) = decide (i + 1 ≠ 256) := by
  have cF := coeff_contains (F s₀) (i := i) hi
  have cG := coeff_contains (G s₀) (i := i) hi
  refine WP.mono (hb h.a0 h.a1 h.a2 ?_ ?_ ?_ (align4_add hp.alF i)
    (align4_add hp.alG i)) fun s' ⟨r3, r4, r5, r8, m, rd, wr, sp, ra, pres⟩ => ⟨⟨?_, ?_, ?_,
    r8.trans h.a5, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ra.trans h.ra,
    fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cF⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cG⟩
  · rw [h.wr, hp.wr]; exact ⟨_, by simp, cF⟩
  · rw [r3]; exact ptr_succ _ 4 i
  · rw [r4]; exact ptr_succ _ 4 i
  · rw [r5]; exact count_sub hi
  · rw [m]
    exact h.frame.writeW (List.mem_singleton_self _) _ cF
  · intro j hj
    rw [m, show F s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (F s₀) i from rfl, coeffAt_writeW _ _ hj hi,
      h.coeff j hj]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right hij]
      by_cases hj' : j < i
      · rw [ite_eq_left hj', ite_eq_left (by omega)]
      · rw [ite_eq_right hj', ite_eq_right (by omega)]
  · rw [r5, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]; exact count_nz hi (by decide)

/-- The loop's initialization. -/
theorem init_ok {out : Nat → BitVec 32} {s₀ : State} :
    WP isa (.block polyInit) s₀ (Inv out s₀ 0) := by
  simp only [polyInit, loadImm_q]
  crun []
  refine ⟨by simp, by simp, by simp, by simp; decide, rfl, rfl, rfl, by simp, fun r hr => ?_, Frame.refl _ _,
    fun j _ => rfl⟩
  have : r ≠ .a2 ∧ r ≠ .a5 := by revert r hr; decide
  simp [this.1, this.2]

/-- The whole loop. -/
theorem loop_ok {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {body : List Instr}
    (hb : ∀ i < 256, ∀ s, Inv out s₀ i s → ∀ {x y c : BitVec 64}, s.gpr .a0 = x → s.gpr .a1 = y →
      s.gpr .a2 = c → InRegions (s.rd ++ s.wr) x 4 → InRegions (s.rd ++ s.wr) y 4 →
      InRegions s.wr x 4 → x.toNat % 4 = 0 → y.toNat % 4 = 0 → WP isa (.block body) s (Step s x y c (out i))) :
    WP isa (.seq (.block polyInit) (.loop (.block body) (.nonzero .a2))) s₀
      (Inv out s₀ 256) := by
  refine WP.seq (WP.mono (init_ok (out := out)) fun s h => ?_)
  exact wp_loop_nz (Inv out s₀) (N := 256) (by decide)
    (fun i hi s h => inv_step hp hi h (hb i hi s h)) (fun _ h => h) h

/-! ## Correctness -/

/-- The value stored in coefficient `j` by `vg_mldsa_add`. -/
def addOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((add (polyAt s₀.mem (F s₀)) (polyAt s₀.mem (G s₀)))[j]!).val

/-- The value stored in coefficient `j` by `vg_mldsa_sub`. -/
def subOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((sub (polyAt s₀.mem (F s₀)) (polyAt s₀.mem (G s₀)))[j]!).val

/-- What an iteration reads: coefficient `i` of each polynomial, as on entry. -/
theorem reads {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {s : State}
    (h : Inv out s₀ i s) {x y : BitVec 64} (h3 : s.gpr .a0 = x) (h4 : s.gpr .a1 = y) :
    s.mem.readW x 32 = coeffAt s₀.mem (F s₀) i ∧ s.mem.readW y 32 = coeffAt s₀.mem (G s₀) i := by
  rw [← h3, ← h4, h.a0, h.a1]
  refine ⟨?_, ?_⟩
  · show coeffAt s.mem (F s₀) i = _
    rw [h.coeff i hi, ite_eq_right (Nat.lt_irrefl i)]
  · show coeffAt s.mem (G s₀) i = _
    exact coeffAt_congr (bytes_frame h.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm) (by decide)) hi

/-- A word whose value is `x`. -/
theorem ofNat_val_eq {v : BitVec 32} {x : Zq} (h : v.toNat = x.val) : v = BitVec.ofNat 32 x.val := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega)]

theorem add_hb {s₀ : State} (hp : Pre s₀) : ∀ i < 256, ∀ s, Inv (addOut s₀) s₀ i s →
    ∀ {x y c : BitVec 64}, s.gpr .a0 = x → s.gpr .a1 = y → s.gpr .a2 = c →
      InRegions (s.rd ++ s.wr) x 4 → InRegions (s.rd ++ s.wr) y 4 → InRegions s.wr x 4 →
      x.toNat % 4 = 0 → y.toNat % 4 = 0 → WP isa (.block addBody) s (Step s x y c (addOut s₀ i)) := by
  intro i hi s h x y c h3 h4 h5 ia ib oa ax ay
  obtain ⟨ea, eb⟩ := reads hp hi h h3 h4
  refine WP.mono (addBody_ok h3 h4 h5 h.a5 ia ib oa ax ay) fun s' hs => ?_
  rw [ea, eb] at hs
  refine (?_ : _ = addOut s₀ i) ▸ hs
  refine ofNat_val_eq ?_
  have ha := hp.redF i hi
  have hb := hp.redG i hi
  rw [BitVec.toNat_setWidth, fixd_add (by rw [toNat_setWidth64]; exact ha)
      (by rw [toNat_setWidth64]; exact hb), toNat_setWidth64, toNat_setWidth64,
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide : 0 < q)) (by decide : q < 2 ^ 32)),
    add_get _ _ hi, val_add', polyAt_val hp.redF hi, polyAt_val hp.redG hi]

theorem sub_hb {s₀ : State} (hp : Pre s₀) : ∀ i < 256, ∀ s, Inv (subOut s₀) s₀ i s →
    ∀ {x y c : BitVec 64}, s.gpr .a0 = x → s.gpr .a1 = y → s.gpr .a2 = c →
      InRegions (s.rd ++ s.wr) x 4 → InRegions (s.rd ++ s.wr) y 4 → InRegions s.wr x 4 →
      x.toNat % 4 = 0 → y.toNat % 4 = 0 → WP isa (.block subBody) s (Step s x y c (subOut s₀ i)) := by
  intro i hi s h x y c h3 h4 h5 ia ib oa ax ay
  obtain ⟨ea, eb⟩ := reads hp hi h h3 h4
  refine WP.mono (subBody_ok h3 h4 h5 h.a5 ia ib oa ax ay) fun s' hs => ?_
  rw [ea, eb] at hs
  refine (?_ : _ = subOut s₀ i) ▸ hs
  refine ofNat_val_eq ?_
  have ha := hp.redF i hi
  have hb := hp.redG i hi
  rw [BitVec.toNat_setWidth, fixd_sub (by rw [toNat_setWidth64]; exact ha)
      (by rw [toNat_setWidth64]; exact hb), toNat_setWidth64, toNat_setWidth64,
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide : 0 < q)) (by decide : q < 2 ^ 32)),
    sub_get _ _ hi, val_sub', polyAt_val hp.redF hi, polyAt_val hp.redG hi,
    Nat.add_sub_assoc (by omega)]

/-- The loop's result: `f` is `out` of each coefficient. -/
theorem polyIs_of_inv {out : Nat → BitVec 32} {s₀ s : State} {g : Poly}
    (h : Inv out s₀ 256 s) (hg : ∀ j < 256, out j = BitVec.ofNat 32 (g[j]!).val) :
    PolyIs s.mem (F s₀) g :=
  polyIs_of_toNat fun j hj => by
    rw [h.coeff j hj, ite_eq_left hj, hg j hj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := val_lt g[j]!; omega)]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.addContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.addContract, Proof.MlDsa.accSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem pre_of_sub {s : State} (h : (Proof.MlDsa.subContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.subContract, Proof.MlDsa.accSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem reduced_zero (p : Addr) : Reduced (fun _ => 0) p := fun i _ => by
  rw [coeffAt_eq]
  have : Mem.readW (fun _ => (0 : Byte)) (coeffAddr p i) 32 = 0 := by
    simp [Mem.readW, Mem.read]
  rw [this]; decide

theorem add_verified : Verified RISCV64.target add (Proof.MlDsa.addContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.RISCV64.Add.ctRegs [.a0, .a1] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := loop_ok hp (add_hb hp)
    refine ⟨t, s', he, ⟨h.pres, h.sp, h.ra⟩, ?_⟩
    sig_post [Proof.MlDsa.addContract, Proof.MlDsa.accSig, RISCV64.abi, RISCV64.argRegs]
    exact polyIs_of_inv h fun j _ => rfl
  · sig_pub [Proof.MlDsa.addContract, Proof.MlDsa.accSig, RISCV64.abi, RISCV64.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · sig_pub [Proof.MlDsa.addContract, Proof.MlDsa.accSig, RISCV64.abi, RISCV64.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.addContract, Proof.MlDsa.accSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

theorem sub_verified : Verified RISCV64.target sub (Proof.MlDsa.subContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.RISCV64.Add.ctRegs [.a0, .a1] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of_sub hs
    obtain ⟨t, s', he, h⟩ := loop_ok hp (sub_hb hp)
    refine ⟨t, s', he, ⟨h.pres, h.sp, h.ra⟩, ?_⟩
    sig_post [Proof.MlDsa.subContract, Proof.MlDsa.accSig, RISCV64.abi, RISCV64.argRegs]
    exact polyIs_of_inv h fun j _ => rfl
  · sig_pub [Proof.MlDsa.subContract, Proof.MlDsa.accSig, RISCV64.abi, RISCV64.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · sig_pub [Proof.MlDsa.subContract, Proof.MlDsa.accSig, RISCV64.abi, RISCV64.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.subContract, Proof.MlDsa.accSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Arith.AddSub
