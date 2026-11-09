module

public import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsCT
public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFront
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFn
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsCT
meta import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFront
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFn
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
meta import VerifiedGarbage.Proof.Framework.Flat
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# DSA key derivation on RISC-V: constant time, the levels

`vg_dsa_derive_key` (`Derive.derive`) runs `Derive.entry`, then
`checkParams` with `Derive.body` or `zeroOut`, then `restore`. Its public data
(`vdD`) is the domain's octets, x's address and length, and `out`, which the
header keeps. Its levels are verification's (`CTBase.lean`) up to g's check,
each failing to `zeroOut` (`zero_rel`, cut after its loads of the header).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_taint)
open VG.Proof.Bignum.RISCV64 (At chain_cons chain_start at_zero_inv)

/-! ## The failing side: `zeroOut` -/

/-- `out`, which the header keeps. -/
abbrev oOf (v : VD) : Addr := v.out.getD 0

/-- `zeroOut`'s loads of the header. -/
abbrev ZH : List Instr :=
  [.load .d .t4 .s6 Sign.hOut] ++ getP .t5 ++ getQ .t2 ++ ([.add .t2 .t2 .t5, .add .t5 .t5 .t2, .add .t5 .t5 .t2,
    .li .s0 0] : List Instr)

abbrev FZ : List (Prog isa) := Code.flat Derive.zeroOut

theorem zhead_ok {v : VD} {s : State} (B : Base v s) (ho : v.out = some (oOf v)) :
    WP isa (.block ZH) s (Fix [(.s6, v.L.S), (.t4, oOf v), (.t5, BitVec.ofNat 64 (3 * v.L.pl + 2 * v.L.ql))]) := by
  have hL := B.ok
  obtain ⟨hin24, hal24⟩ := ScrL.hdr B.scr hL (d := 24) (by decide) (by decide)
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.t4] (Q := fun u => u.gpr .t4 = oOf v ∧ u.mem = s.mem)
    (by brun [Sign.hOut, B.regs.s6, hin24, hal24]; exact B.hout _ ho) (by decide) (by rfl))
    fun u ⟨⟨a4, mu⟩, ku⟩ => ?_
  have Bu := B.keepM ku mu
  refine WP.mono (getP_ok Bu.scr hL Bu.regs .t5) fun w ⟨⟨b5, mw⟩, kw⟩ => ?_
  have Bw := Bu.keepM kw mw
  refine WP.mono (getQ_ok Bw.scr hL Bw.regs .t2) fun x ⟨⟨b2, mx⟩, kx⟩ => ?_
  have Bx := Bw.keepM kx mx
  refine WP.mono (WP.keep [.t2, .t5, .s0] (Q := fun u => u.gpr .t5 = BitVec.ofNat 64 (3 * v.L.pl + 2 * v.L.ql))
    (by
      brun [kx.gpr (r := .t5) (by decide), b5, b2, exec_li_zero]
      simp only [BitVec.ofNat_add_ofNat]; congr 1; omega) (by decide) (by rfl)) fun t ⟨a5, kt⟩ => ?_
  exact ⟨(kt.gpr (r := .s6) (by decide)).trans Bx.regs.s6,
    (kt.gpr (r := .t4) (by decide)).trans ((kx.gpr (r := .t4) (by decide)).trans ((kw.gpr (r := .t4) (by decide)).trans a4)),
    a5, trivial⟩

/-- `zeroOut`, from a level whose states keep `out` in the header. -/
theorem zero_rel {Φ : VD → State → Prop} (hrun : ∀ v s, Φ v s → WP isa (Code.seqL FZ) s fun _ => True)
    (hB : ∀ v s, Φ v s → Base v s) (hO : ∀ v s, Φ v s → v.out = some (oOf v)) :
    RelCT isa (Two Φ) Derive.zeroOut fun _ _ => True :=
  chain_start (chain_cons hrun (m := 1) (by decide)
    (two_taint _ (pins_at_fix (rs := [.s6, .s11, .ra]) fixB (fun _ => rfl) fun _ _ h => ⟨[], _, .block rfl, (hB _ _ h).fixB⟩)
      (by taint_decide))
    (two_taint _ (pins_at_fix (rs := [.s6, .t4, .t5]) (fun v => [(.s6, v.L.S), (.t4, oOf v),
        (.t5, BitVec.ofNat 64 (3 * v.L.pl + 2 * v.L.ql))]) (fun _ => rfl) fun _ _ h =>
      WP.of_flat (c := .block ZH) rfl (zhead_ok (hB _ _ h) (hO _ _ h))) (by taint_decide)))

/-- The failing side's runs. -/
theorem run_else {α : Type} {Φ : α → State → Prop} {F : List (Prog isa)} {n : Nat} {r : Reg} {t e : Prog isa}
    (hrun : ∀ a s, Φ a s → WP isa (Code.seqL F) s fun _ => True)
    (hF : (F.drop n).take 1 = [.ite (.zero r) t e]) :
    ∀ a u, (At Φ F n a u ∧ u.gpr r ≠ 0) → WP isa (Code.seqL e.flat) u fun _ => True :=
  fun _ _ ⟨h, hz⟩ => WP.of_flat rfl (WP.ite_false (run_ite hrun hF h) (by
    rw [Steps.eval_zero]; simpa using hz))

/-! ## The entry -/

/-- A call's public data. -/
def vdD (s : State) : VD :=
  ⟨dlayOf s, s.gpr .a2, s.gpr .a5, 0, 0, Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat, (s.gpr .a3).toNat,
    (s.gpr .a6).toNat, false, some (s.gpr .a0)⟩

/-- The contract's buffers are apart from `scratch`. -/
theorem dsrc {s : State} {A : Addr} {n k : Nat} (hm : (⟨A, n⟩ : Region) ∈ s.rd)
    (hd : (⟨A, n⟩ : Region).Disjoint ⟨s.gpr .a7, (stackArg s 0).toNat * 8⟩) (hn : n < 2 ^ 64) (hk : k ≤ n)
    {t : State} (hr : t.rd = s.rd) (hw : t.wr = s.wr) : Src t (dlayOf s) A k :=
  ⟨fun i hi => ⟨_, by rw [hr, hw]; exact List.mem_append_left _ hm,
    Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun i hi => Pub.ne_of_disjoint hd (by omega_arith) i (by omega_arith)⟩

/-- On entry. -/
def C0d (v : VD) (s : State) : Prop := dContract.pre s ∧ vdD s = v

theorem frontD : ∀ v s, C0d v s → WP isa (.block Derive.entry) s (P0 v) := by
  rintro _ s ⟨h, rfl⟩
  have hL := dlayOf_ok h
  have hZ := hL.z256
  have hpre := h
  obtain ⟨hrd, -, -, -, -, -, dPS, dXS, -, -, -, -, -, -, -, hkl, -, -, -⟩ := h
  refine WP.mono (dfront_ok hpre) fun t ⟨F, k⟩ => ?_
  have hK : Src t (dlayOf s) (s.gpr .a2) (s.gpr .a3).toNat :=
    dsrc (by rw [hrd]; simp) dPS (s.gpr .a3).isLt (Nat.le_refl _) k.2.1 k.2.2
  exact ⟨⟨hL, F.regs, F.scr, hK, dsrc (by rw [hrd]; simp) dXS (s.gpr .a6).isLt (Nat.le_refl _) k.2.1 k.2.2,
    src_nil (Nat.zero_min _), hK.bytes F.out (by simp only [dlayOf] at hZ ⊢; omega),
    (by simp only [vdD, dlayOf]; omega), (fun h => nomatch h), fun o ho => by cases ho; exact F.outw⟩,
    F.lens.trans (congrArg _ (Nat.zero_min _).symm)⟩

theorem outD : ∀ v s, C0d v s → v.out = some (oOf v) := by
  rintro _ s ⟨-, rfl⟩
  rfl

/-- `scratch` is public. -/
theorem pins_a7 : Pins C0d [.a7] := by
  intro v s₁ s₂ h₁ h₂ r hr
  rw [List.mem_singleton] at hr
  subst hr
  exact congrArg (fun v : VD => v.L.S) (h₁.2.trans h₂.2.symm)

/-! ## The levels -/

abbrev R3d : Prog isa := .seq setupP (andThen (.seq (.block ptrG) checkElem) Derive.body Derive.zeroOut)
abbrev R2d : Prog isa := andThen pModQ R3d Derive.zeroOut
abbrev R1d : Prog isa := andThen (.block (ptrQ ++ odd)) R2d Derive.zeroOut
abbrev R0d : Prog isa := odds R2d Derive.zeroOut
abbrev X2d : Prog isa :=
  .seq (.block [.addi .a3 .a1 0, .shift .sll .d .t3 .a1 32, .load .d .t4 .s6 hLens, .add .t4 .t4 .t3,
    .store .d .t4 .s6 hLens]) (andThen pairs R0d Derive.zeroOut)
abbrev X1d : Prog isa :=
  .seq (.block [.addi .a2 .a1 0]) (andThen (.seq (.block ptrQ) bytesBits) X2d Derive.zeroOut)

abbrev FTd : List (Prog isa) := Code.flat Derive.derive
abbrev FX1d : List (Prog isa) := Code.flat X1d
abbrev FX2d : List (Prog isa) := Code.flat X2d
abbrev FR0d : List (Prog isa) := Code.flat R0d
abbrev FR1d : List (Prog isa) := Code.flat R1d
abbrev FR2d : List (Prog isa) := Code.flat R2d
abbrev FR3d : List (Prog isa) := Code.flat R3d
abbrev FBd : List (Prog isa) := Code.flat Derive.body

abbrev ΦX1d (v : VD) (u : State) : Prop := At C0d FTd 5 v u ∧ u.gpr .a0 = 0
abbrev ΦX2d (v : VD) (u : State) : Prop := At ΦX1d FX1d 5 v u ∧ u.gpr .a0 = 0
abbrev ΦR0d (v : VD) (u : State) : Prop := At ΦX2d FX2d 12 v u ∧ u.gpr .a0 = 0
abbrev ΦR1d (v : VD) (u : State) : Prop := At ΦR0d FR0d 1 v u ∧ u.gpr .a0 = 0
abbrev ΦR2d (v : VD) (u : State) : Prop := At ΦR1d FR1d 1 v u ∧ u.gpr .a0 = 0
abbrev ΦR3d (v : VD) (u : State) : Prop := At ΦR2d FR2d 23 v u ∧ u.gpr .a0 = 0
abbrev ΦEgd (v : VD) (u : State) : Prop := At ΦR3d FR3d 45 v u ∧ u.gpr .a0 = 0
abbrev ΦBd (v : VD) (u : State) : Prop := At ΦR3d FR3d 46 v u ∧ u.gpr .a0 = 0

theorem hFTd : (FTd.drop 5).take 1 = [.ite (.zero .a0) X1d Derive.zeroOut] := rfl
theorem hFX1d : (FX1d.drop 5).take 1 = [.ite (.zero .a0) X2d Derive.zeroOut] := rfl
theorem hFX2d : (FX2d.drop 12).take 1 = [.ite (.zero .a0) R0d Derive.zeroOut] := rfl
theorem hFR0d : (FR0d.drop 1).take 1 = [.ite (.zero .a0) R1d Derive.zeroOut] := rfl
theorem hFR1d : (FR1d.drop 1).take 1 = [.ite (.zero .a0) R2d Derive.zeroOut] := rfl
theorem hFR2d : (FR2d.drop 23).take 1 = [.ite (.zero .a0) R3d Derive.zeroOut] := rfl
theorem hFR3gd : (FR3d.drop 45).take 1 = [.ite (.zero .a0) elemOrder (.block [])] := rfl
theorem hFR3d : (FR3d.drop 46).take 1 = [.ite (.zero .a0) Derive.body Derive.zeroOut] := rfl

theorem runTd : ∀ v s, C0d v s → WP isa (Code.seqL FTd) s fun _ => True := fun _ s h =>
  let ⟨tr, t, e, _⟩ := deriveKey_correct s h.1
  ⟨tr, t, exec_flat.mp e, trivial⟩

theorem runX1d : ∀ v s, ΦX1d v s → WP isa (Code.seqL FX1d) s fun _ => True := run_then runTd hFTd
theorem runX2d : ∀ v s, ΦX2d v s → WP isa (Code.seqL FX2d) s fun _ => True := run_then runX1d hFX1d
theorem runR0d : ∀ v s, ΦR0d v s → WP isa (Code.seqL FR0d) s fun _ => True := run_then runX2d hFX2d
theorem runR1d : ∀ v s, ΦR1d v s → WP isa (Code.seqL FR1d) s fun _ => True := run_then runR0d hFR0d
theorem runR2d : ∀ v s, ΦR2d v s → WP isa (Code.seqL FR2d) s fun _ => True := run_then runR1d hFR1d
theorem runR3d : ∀ v s, ΦR3d v s → WP isa (Code.seqL FR3d) s fun _ => True := run_then runR2d hFR2d
theorem runEgd : ∀ v s, ΦEgd v s → WP isa (Code.seqL FE) s fun _ => True := run_then runR3d hFR3gd
theorem runBd : ∀ v s, ΦBd v s → WP isa (Code.seqL FBd) s fun _ => True := run_then runR3d hFR3d

theorem onX1d : ∀ v u, ΦX1d v u → SX1 v u := fun _ _ h => semX1 frontD ⟨atL rfl h.1, h.2⟩
theorem onX2d : ∀ v u, ΦX2d v u → SX2 v u := fun _ _ h => semX2 onX1d ⟨atL rfl h.1, h.2⟩
theorem onR0d : ∀ v u, ΦR0d v u → P1 v u := fun _ _ h => semR0 onX2d ⟨atL rfl h.1, h.2⟩
theorem onR1d : ∀ v u, ΦR1d v u → P1 v u ∧ v.p % 2 = 1 := fun _ _ h => semR1 onR0d ⟨atL rfl h.1, h.2⟩
theorem onR2d : ∀ v u, ΦR2d v u → SR2 v u := fun _ _ h => semR2 onR1d ⟨atL rfl h.1, h.2⟩
theorem onR3d : ∀ v u, ΦR3d v u → SR3 v u := fun _ _ h => semR3 onR2d ⟨atL rfl h.1, h.2⟩

/-- `body`'s phase: the domain passed the checks. -/
abbrev SD (v : VD) (u : State) : Prop := CK v u ∧ KM v ∧ EOk v (v.L.pl + v.L.ql)

theorem onBd : ∀ v u, ΦBd v u → SD v u := fun _ _ h =>
  let m := at_sem (Φ := ΦR3d) (F := FR3) (n := 46) (M := MR3) (fun _ _ h => midR3 onR3d h) (atL rfl h.1)
  ⟨m.1, m.2.1, m.2.2.mp h.2⟩

theorem oX1d : ∀ v u, ΦX1d v u → v.out = some (oOf v) := fun _ _ h => at_pure outD h.1
theorem oX2d : ∀ v u, ΦX2d v u → v.out = some (oOf v) := fun _ _ h => at_pure oX1d h.1
theorem oR0d : ∀ v u, ΦR0d v u → v.out = some (oOf v) := fun _ _ h => at_pure oX2d h.1
theorem oR1d : ∀ v u, ΦR1d v u → v.out = some (oOf v) := fun _ _ h => at_pure oR0d h.1
theorem oR2d : ∀ v u, ΦR2d v u → v.out = some (oOf v) := fun _ _ h => at_pure oR1d h.1
theorem oR3d : ∀ v u, ΦR3d v u → v.out = some (oOf v) := fun _ _ h => at_pure oR2d h.1
/-! ## The levels' relations -/

section Levels

variable (hbody : RelCT isa (Two ΦBd) Derive.body fun _ _ => True)
include hbody

theorem R3d_rel : RelCT isa (Two ΦR3d) R3d fun _ _ => True := by
  refine chain_start (chain_cons runR3d (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsR3_0 onR3d)) (by taint_decide)) ?_)
  refine chain_cons runR3d (m := 18) (by decide) (two_taint _ (pinsL rfl (pinsR3_2 onR3d)) (by taint_decide)) ?_
  refine chain_cons runR3d (m := 45) (by decide) (two_taint _ (pinsL rfl (pinsR3_18 onR3d)) (by taint_decide)) ?_
  refine chain_cons runR3d (m := 46) (by decide) (rel_ite_at hFR3gd (zeroL rfl (zeroEg onR3d))
    (eo_rel runEgd fun _ _ h => semEg onR3d ⟨atL rfl h.1, h.2⟩) nil_rel) ?_
  exact chain_cons runR3d (m := 47) (by decide) (rel_ite_at hFR3d (zeroL rfl (zeroR3 onR3d)) hbody
    (zero_rel (run_else runR3d hFR3d)
      (fun _ _ h => (at_sem (Φ := ΦR3d) (F := FR3) (n := 46) (M := MR3) (fun _ _ h => midR3 onR3d h) (atL rfl h.1)).1.base) fun _ _ h => at_pure oR3d h.1)) nil_rel

theorem R2d_rel : RelCT isa (Two ΦR2d) R2d fun _ _ => True := by
  refine chain_start (chain_cons runR2d (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsR2_0 onR2d)) (by taint_decide)) ?_)
  refine chain_cons runR2d (m := 10) (by decide) (two_taint _ (pinsL rfl (pinsR2_2 onR2d)) (by taint_decide)) ?_
  refine chain_cons runR2d (m := 23) (by decide) (two_taint _ (pinsL rfl (pinsR2_10 onR2d)) (by taint_decide)) ?_
  exact chain_cons runR2d (m := 24) (by decide) (rel_ite_at hFR2d (zeroL rfl (zeroR2 onR2d)) (R3d_rel hbody)
    (zero_rel (run_else runR2d hFR2d)
      (fun _ _ h => (at_sem (Φ := ΦR2d) (F := FR2) (n := 23) (M := MR2) (fun _ _ h => midR2 onR2d h) (atL rfl h.1)).1.1.1)
      fun _ _ h => at_pure oR2d h.1)) nil_rel

theorem R1d_rel : RelCT isa (Two ΦR1d) R1d fun _ _ => True :=
  chain_start (chain_cons runR1d (m := 1) (by decide) (relL rfl rfl (relR1 onR1d))
    (chain_cons runR1d (m := 2) (by decide) (rel_ite_at hFR1d (zeroL rfl (zeroR1 onR1d)) (R2d_rel hbody)
      (zero_rel (run_else runR1d hFR1d)
        (fun _ _ h => (at_sem (Φ := ΦR1d) (F := FR1) (n := 1) (M := MR1) (fun _ _ h => midR1 onR1d h) (atL rfl h.1)).1.1)
        fun _ _ h => at_pure oR1d h.1)) nil_rel))

theorem R0d_rel : RelCT isa (Two ΦR0d) R0d fun _ _ => True :=
  chain_start (chain_cons runR0d (m := 1) (by decide) (relL rfl rfl (relR0 onR0d))
    (chain_cons runR0d (m := 2) (by decide) (rel_ite_at hFR0d (zeroL rfl (zeroR0 onR0d)) (R1d_rel hbody)
      (zero_rel (run_else runR0d hFR0d)
        (fun _ _ h => (at_sem (Φ := ΦR0d) (F := FR0) (n := 1) (M := MR0) (fun _ _ h => midR0 onR0d h) (atL rfl h.1)).1.1)
        fun _ _ h => at_pure oR0d h.1)) nil_rel))

theorem X2d_rel : RelCT isa (Two ΦX2d) X2d fun _ _ => True :=
  chain_start (chain_cons runX2d (m := 12) (by decide)
    (two_taint _ (pinsL rfl (pinsX2_0 onX2d)) (by taint_decide))
    (chain_cons runX2d (m := 13) (by decide) (rel_ite_at hFX2d (zeroL rfl (zeroX2 onX2d)) (R0d_rel hbody)
      (zero_rel (run_else runX2d hFX2d)
        (fun _ _ h => (at_sem (Φ := ΦX2d) (F := FX2) (n := 12) (M := MX2) (fun _ _ h => midX2 onX2d h) (atL rfl h.1)).1)
        fun _ _ h => at_pure oX2d h.1)) nil_rel))

theorem X1d_rel : RelCT isa (Two ΦX1d) X1d fun _ _ => True := by
  refine chain_start (chain_cons runX1d (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsX1_0 onX1d)) (by taint_decide)) ?_)
  refine chain_cons runX1d (m := 4) (by decide) (two_taint _ (pinsL rfl (pinsX1_2 onX1d)) (by taint_decide)) ?_
  refine chain_cons runX1d (m := 5) (by decide) (two_taint _ (pinsL rfl (pinsX1_4 onX1d)) (by taint_decide)) ?_
  exact chain_cons runX1d (m := 6) (by decide) (rel_ite_at hFX1d (zeroL rfl (zeroX1 onX1d)) (X2d_rel hbody)
    (zero_rel (run_else runX1d hFX1d)
      (fun _ _ h => (at_sem (Φ := ΦX1d) (F := FX1) (n := 5) (M := MX1) (fun _ _ h => midX1 onX1d h) (atL rfl h.1)).1.1)
      fun _ _ h => at_pure oX1d h.1)) nil_rel

end Levels

end VG.Proof.Dsa.RISCV64.CT
