module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.VerifyEntry
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Sign.Inst
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.HighLow
import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.BitPack
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
public import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Sign.Leak
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintUnpackCT
public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.Prepare
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.HighLow
meta import VerifiedGarbage.Proof.MlDsa.Round.Ones
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.Proof.MlKem.RISCV64.Common
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.Arith
public import VerifiedGarbage.Proof.MlDsa.Round.Mem
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Output
import VerifiedGarbage.Proof.MlDsa.Sign.Setup
import VerifiedGarbage.Proof.MlDsa.Sign.Iter
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Output
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.MlDsa.Pack.Coeffs
import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintUnpackCT
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Proof.MlDsa.Pack.Coeffs
meta import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.Row
import VerifiedGarbage.Proof.MlDsa.Verify.Final
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Verify.Final
import VerifiedGarbage.Proof.MlKem.RISCV64.CmpSel
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.Compute
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.Compute
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Good
import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Samp
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Site
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Samp
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
meta import VerifiedGarbage.Proof.MlKem.KPke
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Site
meta import VerifiedGarbage.Proof.MlKem.RISCV64.CmpSel
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.Arith
meta import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Round
public import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `MlDsa.RISCV64.Round.NormLt`, which only this module used -/

section

/-!
# ML-DSA on RISCV64: `vg_mldsa_norm_lt`

As PPC64LE's (`Proof/MlDsa/PPC64LE/Pack/HintCT.lean`): one symbolic
execution of the loop body, for any pointer (`body_ok`), which ands into `a6`
the bit `ok a` (two `sltu`s, `ok_toNat`: 1 exactly when `a < bound` or
`q - a < bound`, `normZq_lt`); the invariant says `a6` is 1 exactly when
every coefficient so far is in bounds (`Inv`), and `normRq_lt` turns that
into the norm. `bound` is zero-extended first (`B`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Round.NormLt

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Round
open VG.Impl.MlDsa.RISCV64.Arith (loadImm)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (pR coeff_contains polyAt_val normZq_lt normRq_lt reduced_zero)
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_succ align4_add)
open VG.Proof.MlDsa.RISCV64.Arith (loadImm_q)

/-! ## Values -/

/-- The bit the body ands in, for the coefficient `a` and the bound `b`. -/
def ok (a b : BitVec 64) : BitVec 64 := (if a < b then 1 else 0) ||| (if 8380417 - a < b then 1 else 0)

theorem ok_toNat {a b : BitVec 64} (ha : a.toNat < q) (_hb : b.toNat < 2 ^ 32) :
    ok a b = if a.toNat < b.toNat ∨ q - a.toNat < b.toNat then 1 else 0 := by
  rw [VG.Proof.MlDsa.Round.q_eq] at ha ⊢
  have e : (8380417 - a).toNat = 8380417 - a.toNat := by
    rw [BitVec.toNat_sub, show (8380417 : BitVec 64).toNat = 8380417 from rfl]; omega_using [ha]
  unfold ok
  simp only [BitVec.lt_def, e]
  by_cases h1 : a.toNat < b.toNat <;> by_cases h2 : 8380417 - a.toNat < b.toNat <;> simp [h1, h2]

/-! ## The loop body -/

section
variable {s : State} {x c v : BitVec 64} (h3 : s.gpr .a0 = x) (h5 : s.gpr .a2 = 8380417) (h9 : s.gpr .a6 = v)
  (h10 : s.gpr .t1 = c) (ia : InRegions (s.rd ++ s.wr) x 4) (ax : x.toNat % 4 = 0)
include h3 h5 h9 h10 ia ax

theorem body_ok :
    WP isa (.block nlBody) s fun s' =>
      s'.gpr .a0 = x + 4 ∧ s'.gpr .t1 = c - 1 ∧ s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a2 = 8380417 ∧
      s'.gpr .a6 = v &&& ok ((s.mem.readW x 32).setWidth 64) (s.gpr .a1) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .ra = s.gpr .ra ∧
      ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  crun [nlBody, ok, h3, h5, h9, h10, ia, ax, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  simp [Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev Fp : Addr := s₀.gpr .a0
abbrev B : BitVec 64 := s₀.gpr .a1 <<< 32 >>> 32

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [pR (Fp s₀)]
  wr : s₀.wr = []
  fit : (Fp s₀).toNat + 1024 ≤ 2 ^ 64
  red : Reduced s₀.mem (Fp s₀)
  al : (Fp s₀).toNat % 4 = 0

/-- All of the first `i` coefficients are in bounds. -/
def AllOk (s₀ : State) (i : Nat) : Prop :=
  ∀ j < i, normZq (polyAt s₀.mem (Fp s₀))[j]! < (B s₀).toNat

instance (s₀ : State) (i : Nat) : Decidable (AllOk s₀ i) := by unfold AllOk; infer_instance

/-- After `i` iterations. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .a0 = Fp s₀ + BitVec.ofNat 64 (4 * i)
  r4 : s.gpr .a1 = B s₀
  r5 : s.gpr .a2 = 8380417
  r9 : s.gpr .a6 = if AllOk s₀ i then 1 else 0
  r10 : s.gpr .t1 = BitVec.ofNat 64 (256 - i)
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.gpr .ra = s₀.gpr .ra
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r

theorem ite_and_ite (a b : Prop) [Decidable a] [Decidable b] :
    ((if a then 1 else 0 : BitVec 64) &&& if b then 1 else 0) = if a ∧ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

theorem allOk_succ (s₀ : State) {i : Nat} (hi : i < 256) :
    AllOk s₀ (i + 1) ↔ AllOk s₀ i ∧ normZq (polyAt s₀.mem (Fp s₀))[i]! < (B s₀).toNat := by
  unfold AllOk
  constructor
  · intro h; exact ⟨fun j hj => h j (by omega_using [hj]), h i (by omega_using [])⟩
  · intro ⟨h, h'⟩ j hj
    by_cases e : j = i
    · subst e; exact h'
    · exact h j (by omega_using [hj, e])

theorem inv_step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {s : State} (h : Inv s₀ i s) :
    WP isa (.block nlBody) s fun s' => Inv s₀ (i + 1) s' ∧ (s'.gpr .t1 != 0) = decide (i + 1 ≠ 256) := by
  have cF := coeff_contains (Fp s₀) (i := i) hi
  refine WP.mono (body_ok h.r3 h.r5 h.r9 h.r10 (by rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cF⟩)
    (align4_add hp.al i))
    fun s' ⟨r3, r10, r4, r5, r9, m, rd, wr, sp, lr, pres⟩ => ⟨⟨?_, r4.trans h.r4, r5, ?_, ?_, m.trans h.mem,
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, lr.trans h.lr, fun r hr => (pres r hr).trans (h.pres r hr)⟩, ?_⟩
  · rw [r3]; exact ptr_succ _ 4 i
  · have hv := polyAt_val hp.red (i := i) hi
    have ha : ((s.mem.readW (Fp s₀ + BitVec.ofNat 64 (4 * i)) 32).setWidth 64).toNat =
        ((polyAt s₀.mem (Fp s₀))[i]!).val := by
      rw [h.mem, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (coeffAt s₀.mem (Fp s₀) i).isLt; omega_using [])]
      exact hv.symm
    have hb : (s.gpr .a1).toNat < 2 ^ 32 := by
      rw [h.r4, B, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
      omega_using []
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
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.gpr .ra = s₀.gpr .ra ∧
    s.gpr .a0 = if AllOk s₀ 256 then 1 else 0

theorem exit_ok {s₀ s : State} (h : Inv s₀ 256 s) : WP isa (.block [.addi .a0 .a6 0]) s (Post s₀) := by
  refine Steps.WP.cons (exec_addi (by decide)) (WP.block_nil ⟨?_, h.sp, ?_, ?_⟩)
  · intro r hr
    have : ¬r = .a0 := by revert r hr; decide
    rw [RegUpd.gpr_write_of_ne _ _ this]; exact h.pres r hr
  · rw [RegUpd.gpr_write_of_ne _ _ (by decide)]; exact h.lr
  · rw [RegUpd.gpr_write_self, show ∀ x : BitVec 64, x + BitVec.ofInt 64 0 = x from fun x => by simp]; exact h.r9

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa normLt s₀ (Post s₀) := by
  refine WP.seq ?_
  simp only [loadQ, loadImm_q, List.cons_append, List.nil_append]
  crun []
  refine WP.seq (wp_loop_nz (Inv s₀) (N := 256) (by decide) (fun i hi s h => inv_step hp hi h)
    (fun s h => exit_ok h) ?_)
  refine ⟨by simp, by simp [B], by simp; decide, ?_, by simp, rfl, rfl, rfl, rfl, by simp, fun r hr => ?_⟩
  · have : AllOk s₀ 0 := fun j hj => absurd hj (Nat.not_lt_zero j)
    simp [this]
  · have : r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a6 ∧ r ≠ .t1 := by revert r hr; decide
    simp [this.1, this.2.1, this.2.2.1, this.2.2.2]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.normLtContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := []

theorem verified : Verified RISCV64.target normLt (Proof.MlDsa.normLtContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.RISCV64.Add.ctRegs [.a0] (fun s₁ s₂ h => ?_)
    (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := correct hp
    refine ⟨t, s', he, ⟨h.1, h.2.1, h.2.2.1⟩, ?_⟩
    sig_post [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, RISCV64.abi, RISCV64.argRegs]
    rw [h.2.2.2]
    have e : AllOk s 256 ↔ normRq [polyAt s.mem (Fp s)] < (B s).toNat := by
      rw [normRq_lt]; rfl
    have eb : (B s).toNat = ((s.gpr .a1).setWidth 32).toNat := by
      rw [B, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_setWidth]
      omega_using []
    rw [eb] at e
    by_cases hc : AllOk s 256
    · rw [ite_eq_left hc, ite_eq_left (e.mp hc)]; rfl
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc (e.mpr h'))]; rfl
  · sig_pub [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, RISCV64.abi, RISCV64.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.2.1
  · sig_pub [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, RISCV64.abi, RISCV64.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.normLtContract, Proof.MlDsa.normLtSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Round.NormLt

end

end

/-! ### `MlDsa.RISCV64.Verify.Top`, which only this module used -/

section

/-! ### `MlDsa.RISCV64.Verify.Cmp`, which only this module used -/

section

/-! ### `MlDsa.RISCV64.Verify.Hash`, which only this module used -/

section

/-!
# ML-DSA verification on RISC-V: `c̃′`

As on PPC64LE (`Proof/MlDsa/PPC64LE/Verify/Cmp.lean`):
`c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)` to `3072` (`vhash_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv hashLay hashLay_ptr
  hashS hashS_tr pieceS ix_ne1 shake31)
open VG.Impl.MlDsa.RISCV64.Verify
open VG.Impl.MlKem.RISCV64 (hash)
open VG.Spec.MlDsa (Params toRq ntt simpleBitPack)
open VG.Proof.MlDsa (HintIs PolyIs polyAt Reduced)
open VG.Proof.MlDsa.Verify (vZ zHat w1Row)
open VG.Spec.Sha3 (bytesAt)

/-- The buffers of the sponge: `mu` and `scratch`. -/
abbrev Kmu : Nat → Bool := fun i => i == 3

theorem kmu : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → Kmu i = true → Kmu j = true → i ∈ vWb ∨ j ∈ vWb :=
  fun i _ j _ hij _ _ hi hj => by
    simp only [Kmu, beq_iff_eq] at hi hj; omega

/-- `w1Encode(w′₁)` of rows `A'`, `cc` and `h`. -/
abbrev w1Enc (p : Params) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly) (cc : Spec.MlDsa.Poly)
    (h : List (Vector Bool Spec.MlDsa.n)) : List Byte :=
  (List.range p.k).flatMap fun r => simpleBitPack (w1Row p (pkOf p σ) (sgOf p σ) A' (ntt cc) h r) (w1Max p)

theorem flatMap_congr_mem' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr_mem' fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- After the hash. -/
abbrev KF (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A' cc h R, KC5 p STK σ A' cc h R p.ℓ true p.k s ∧
    bytesAt s.mem ((vlay p STK σ).A 0 oCT) p.ctildeLen = Spec.MlDsa.H (muOf σ ++ w1Enc p σ A' cc h) p.ctildeLen

theorem vhPieces {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (hs : Site (vlay p STK σ) vWb STK s) :
    (∀ pc ∈ ([⟨.s9, 0, 64⟩, ⟨.s11, oB, p.k * w1Len p⟩] : List Impl.MlKem.RISCV64.Piece),
      PieceOk (hashLay (vlay p STK σ) s Kmu) ix s false pc) ∧
    PieceOk (hashLay (vlay p STK σ) s Kmu) ix s true (⟨.s11, oCT, p.ctildeLen⟩ : Impl.MlKem.RISCV64.Piece) := by
  have hk := hF.k
  obtain ⟨w1a, w1b⟩ := hF.w1
  refine ⟨fun pc hpc => ?_, pieceS hs rfl (show oCT < 32768 by decide)
    (show p.ctildeLen < 2048 by rcases hF.ct with e | e | e <;> omega_using [e])
    (show 0 < p.ctildeLen by rcases hF.ct with e | e | e <;> omega_using [e])
    (by rcases hF.ct with e | e | e <;> vsep hF [hashLay, Lay.size, e]) (.inl rfl)
    fun _ => show ix Reg.s11 ∈ vWb by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl
  · exact pieceS hs rfl (show (0 : Nat) < 32768 by decide) (show 64 < 2048 by decide) (by decide)
      (by vsep hF [hashLay, Lay.size]) (.inr rfl) fun h => absurd h (by decide)
  · exact pieceS hs rfl (show oB < 32768 by decide) (show p.k * w1Len p < 2048 by omega_using [w1a]) w1b
      (by rcases hF.w1l with e | ⟨e, _⟩ <;> vsep hF [hashLay, Lay.size, e]) (.inl rfl) fun h => absurd h (by decide)

theorem B_bytes {p : Params} {STK : Nat} {σ : State} {A' cc h R nz nc} {s : State}
    (hk5 : KC5 p STK σ A' cc h R nz nc p.k s) :
    bytesAt s.mem ((vlay p STK σ).A 0 oB) (p.k * w1Len p) = w1Enc p σ A' cc h := by
  rw [Nat.mul_comm, Lay.A, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ oB (w1Len p) p.k]
  exact flatMap_congr_mem' fun r hr => hk5.rows r (List.mem_range.mp hr)

theorem vhash_ok {p : Params} (hF : VFacts p) {STK : Nat} {σ : State} {A' cc h R} {s : State}
    (hk5 : KC5 p STK σ A' cc h R p.ℓ true p.k s) :
    WP isa (hash 136 0x1f [⟨.s9, 0, 64⟩, ⟨.s11, oB, p.k * w1Len p⟩] [⟨.s11, oCT, p.ctildeLen⟩]) s
      (KF p STK σ) := by
  have hk := hF.k
  have hs := hk5.vc.site
  obtain ⟨hin, hq⟩ := vhPieces hF hs
  refine WP.mono (hashS hs kmu (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by simp) hin hq)
    fun s' ⟨k', o'⟩ => ⟨A', cc, h, R, hk5.keep hF k' ?_, ?_⟩
  · have : p.ctildeLen ≤ 64 := by rcases hF.ct with e | e | e <;> omega_using [e]
    k5chks hF (Nat.le_refl _)
  · have o₃ : bytesAt s'.mem ((vlay p STK σ).A 0 oCT) p.ctildeLen = _ := o'
    rw [o₃]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
      hashLay_ptr _ _ _ (ix_ne1 _)]
    have e1 : bytesAt s.mem ((vlay p STK σ).ptr (ix Reg.s9) + BitVec.ofNat 64 0) 64 = muOf σ :=
      hk5.vc.mu
    have e2 : bytesAt s.mem ((vlay p STK σ).ptr (ix Reg.s11) + BitVec.ofNat 64 oB) (p.k * w1Len p) =
        w1Enc p σ A' cc h := B_bytes hk5
    rw [e1, e2, shake31]
    exact (Proof.MlKem.shake256_eq _ _).symm

theorem vhash_piece {p : Params} (hF : VFacts p) {STK : Nat} :
    VPiece p STK (KX p STK p.ℓ true p.k) (KF p STK)
      (hash 136 0x1f [⟨.s9, 0, 64⟩, ⟨.s11, oB, p.k * w1Len p⟩] [⟨.s11, oCT, p.ctildeLen⟩]) :=
  ⟨fun _ _ _ ⟨_, _, _, _, h⟩ => vhash_ok hF h,
    rel_of (RelCT.exists_ fun σ => hashS_tr kmu (rate := 136) (sfx := 0x1f) (by decide) (by decide)
      (by simp) (fun s hs => (vhPieces hF (σ := σ) hs).1) (fun s hs => (vhPieces hF hs).2) fun _ _ h => h)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ⟨σ₁, vc_twoL pub h₁.vc h₂.vc⟩⟩

end VG.Proof.MlDsa.RISCV64.Verify

end

end

/-! ### `MlDsa.RISCV64.Verify.SampC`, which the modules that import this one used -/

section

/-!
# ML-DSA verification on RISC-V: `c`, and the samplers

As on PPC64LE (`Proof/MlDsa/PPC64LE/Verify/Top.lean`): `c = SampleInBall(c̃)`
to polynomial 15, its result ANDed into `s4` and `c` masked with it
(`ball_piece`); and every sampler, after the checks of the signature
(`samples_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee BallOk
  ball_tr polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW keepD andMask_ok masked_poly taint31)
open VG.Impl.MlDsa.RISCV64.Verify
open VG.Impl.MlDsa.RISCV64.KeyGen (and24 mask setB seqR sampled)
open VG.Impl.MlKem.RISCV64 (copy)
open VG.Spec.MlDsa (Params toRq normRq rejNTTPoly minBounds Outcome sampleInBall)
open VG.Proof.MlDsa (HintIs PolyIs polyAt Reduced)
open VG.Proof.MlDsa.Verify (vZ vRho aSeed vCt)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers. -/
structure VS4 (p : Params) (STK : Nat) (σ s : State) : Prop where
  vb : VB p STK σ s
  red : ∀ r < p.k, ∀ s' < p.ℓ, Reduced s.mem (aA p STK σ r s')
  redC : Reduced s.mem ((vlay p STK σ).A 0 (oP 15))
  ok : ∃ q : Bool, s.gpr .s4 = flag q ∧
    (q = true → (∀ r < p.k, ∀ s' < p.ℓ,
      ∃ b : Nat, rejNTTPoly b (aSeed (pkOf p σ) r s') = some (polyAt s.mem (aA p STK σ r s'))) ∧
      ∃ b : Nat, (sampleInBall p.τ b (vCt p (sgOf p σ))).map toRq = some (polyAt s.mem ((vlay p STK σ).A 0 (oP 15)))) ∧
    (q = false → (∃ r < p.k, ∃ s' < p.ℓ, rejNTTPoly minBounds.rejNTT (aSeed (pkOf p σ) r s') = none) ∨
      sampleInBall p.τ minBounds.ball (vCt p (sgOf p σ)) = none)

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem ball_m {σ : State} :
    BallOk (vlay p STK σ) vWb (.s8, 0) p.ctildeLen p.τ pC (sc oSS) := by
  have hk := hF.k
  exact ⟨⟨vptr_ok rfl (by decide), by vsep hF⟩, ⟨vptr_ok rfl (by decide), by vsep hF⟩,
    ⟨vptr_ok rfl (by decide), by vsep hF⟩, show ix Reg.s11 ∈ vWb by decide,
    show ix Reg.s11 ∈ vWb by decide, by vsep hF, by vsep hF, by vsep hF, hF.ball.1,
    ⟨by rcases hF.ct with e | e | e <;> omega_using [e], by rcases hF.ct with e | e | e <;> omega_using [e], hF.ball.2⟩, by valsep, by valsep⟩

theorem vball_ok {σ s : State} (h : VS p STK p.k 0 σ s) :
    WP isa (sampled (ballAt P (.s8, 0) p.ctildeLen p.τ pC) pC) s (VS4 p STK σ) := by
  have hk := hF.k; have hl := hF.l
  have hs := h.vb.vc.site
  have hL := hs.ok
  unfold sampled ballAt
  refine WP.seq (KeyGen.ball_ok hP.ball hs hS (ball_m hF) fun s₃ k₃ hred hout => ?_)
  have eb : bytesAt s.mem (lpa (vlay p STK σ) (.s8, 0)) p.ctildeLen = vCt p (sgOf p σ) := by
    have := sig_slice h.vb.vc (o := 0) (l := p.ctildeLen) (by have := hF.sig; have := hF.hint; omega_arith)
    rw [List.drop_zero] at this
    exact this
  rw [eb] at hout
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  have kv₃ := h.vb.keep hF k₃ (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF)
  have kA3 : ∀ r < p.k, ∀ s' < p.ℓ, polyAt s₃.mem (aA p STK σ r s') = polyAt s.mem (aA p STK σ r s') ∧
      (Reduced s.mem (aA p STK σ r s') → Reduced s₃.mem (aA p STK σ r s')) := fun r hr s' hs' =>
    ⟨polyAt_keepW hL k₃.frame (by vsep hF) (by decide) rfl, reduced_keepW hL k₃.frame (by vsep hF) (by decide) rfl⟩
  have h24₃ : s₃.gpr .s4 = s.gpr .s4 := k₃.cs .s4 (by decide)
  refine WP.mono (andMask_ok kv₃.vc.site (a := pC) ⟨vptr_ok rfl (by decide), by vsep hF⟩
    (by valsep) (show ix Reg.s11 ∈ vWb by decide) hr01) fun s₄ ⟨s₅, r₅, k₄, r₄, co⟩ => ?_
  obtain ⟨pi, p1, _⟩ := masked_poly hred co
  have kv₄ := (kv₃.regs2 r₅).keep hF k₄ (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF)
  have kA4 : ∀ r < p.k, ∀ s' < p.ℓ, polyAt s₄.mem (aA p STK σ r s') = polyAt s₃.mem (aA p STK σ r s') ∧
      (Reduced s₃.mem (aA p STK σ r s') → Reduced s₄.mem (aA p STK σ r s')) := fun r hr s' hs' => by
    rw [← r₅.mem]
    exact ⟨polyAt_keepW hL k₄.frame (by vsep hF) (by decide) rfl, reduced_keepW hL k₄.frame (by vsep hF) (by decide) rfl⟩
  have dn : ∀ r s', s' < p.ℓ → (Dn p.k 0 r s' ↔ r < p.k) := fun r s' _ => by simp only [Dn]; omega_using []
  obtain ⟨q, hq, hok, hbad⟩ := h.ok
  refine ⟨kv₄, fun r hr s' hs' => (kA4 r hr s' hs').2 ((kA3 r hr s' hs').2 (h.red r s' hs' ((dn r s' hs').mpr hr))),
    pi.1, ⟨q && decide ((s₃.gpr .a0).setWidth 32 = 1), ?_, fun hq' => ⟨fun r hr s' hs' => ?_, ?_⟩, fun hq' => ?_⟩⟩
  · rw [r₄, h24₃, hq, flag_and01 q hr01]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
    obtain ⟨b, hb⟩ := hok hq'.1 r s' hs' ((dn r s' hs').mpr hr)
    exact ⟨b, by rw [(kA4 r hr s' hs').1, (kA3 r hr s' hs').1]; exact hb⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
    show ∃ b, _ = some (polyAt s₄.mem (lpa (vlay p STK σ) pC))
    rw [p1 hq'.2]
    rcases hout with ⟨_, b, hb⟩ | ⟨h0, _⟩
    · exact ⟨b.ball, hb⟩
    · rw [h0] at hq'; exact absurd hq'.2 (by decide)
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hq'
    rcases hq' with hq' | hq'
    · obtain ⟨r, s', hs', hd, hn⟩ := hbad hq'
      exact .inl ⟨r, (dn r s' hs').mp hd, s', hs', hn⟩
    · rcases hout with ⟨h1, _⟩ | ⟨_, hn⟩
      · exact absurd h1 hq'
      · exact .inr (Option.map_eq_none_iff.mp hn)

omit hP hF hS in
theorem ballTail_taint : (VG.RISCV64.taint.check (Taint.ofRegs [.s11]) (.seq (.block and24) (mask (pS 15)))
    (VG.Taint.hintOf VG.RISCV64.taint (Taint.ofRegs [.s11]) (.seq (.block and24) (mask (sc 0))))).isSome = true :=
  vAndMask_taint 15 (by decide)

theorem ball_piece :
    VPiece p STK (VS p STK p.k 0) (VS4 p STK) (sampled (ballAt P (.s8, 0) p.ctildeLen p.τ pC) pC) := by
  have hk := hF.k
  refine ⟨fun _ _ _ h => vball_ok hP hF hS h, ?_⟩
  unfold sampled ballAt
  refine RelCT.seq (R := VTwo p STK) ?_ (vtaint31 ballTail_taint)
  refine RelCT.mono (M := isa) (P := fun (x y : State) => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
    bytesAt x.mem (lpa (vlay p STK σ) (.s8, 0)) p.ctildeLen = bytesAt y.mem (lpa (vlay p STK σ) (.s8, 0)) p.ctildeLen)
    (RelCT.exists_ fun σ => ?_) (fun _ _ ⟨σ₁, _, _, _, pub, h₁, h₂⟩ => ?_) fun _ _ h => h
  · have ok := fun x (hs : Site (vlay p STK σ) vWb STK x) => KeyGen.ball_ok hP.ball hs hS
      (name := "vg_mldsa_sample_in_ball") (ball_m hF (σ := σ)) (Q := fun x' => ∃ rs, Kept rs x x') fun _ k _ _ => ⟨_, k⟩
    exact (VG.Proof.MlDsa.RISCV64.KeyGen.RelCT.two (fun _ _ h => h.1)
      (ball_tr hP.ball hS (ball_m hF) fun x y h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩)
      fun x hs => ok x hs).mono (fun _ _ h => h) fun x y h => ⟨σ, h⟩
  · refine ⟨σ₁, vc_twoL pub h₁.vb.vc h₂.vb.vc, ?_⟩
    show bytesAt _ ((vlay p STK σ₁).A 4 0) _ = bytesAt _ ((vlay p STK σ₁).A 4 0) _
    rw [sig_slice h₁.vb.vc (by have := hF.sig; have := hF.hint; omega_arith), pub.2.2.2.2.2.2.2.1, vlay_pub pub,
      sig_slice h₂.vb.vc (by have := hF.sig; have := hF.hint; omega_arith)]

/-! ## The samplers -/

omit hP hS in
theorem rho_piece :
    VPiece p STK (fun σ s => V2 p STK p.ℓ σ s ∧ flag (zOk p σ p.ℓ) ≠ 0) (VS p STK 0 0) (copy .s10 0 .s11 oSB 32) := by
  refine ⟨fun σ s _ ⟨h, hn⟩ => ?_, rel_of (vtaint4 (by taint_decide)) fun σ₁ _ _ _ _ _ pub h₁ h₂ =>
    ⟨σ₁, vc_twoL pub h₁.1.vc h₂.1.vc⟩⟩
  have hz : zOk p σ p.ℓ = true := flag_ne.mp hn
  exact rho_ok hF ⟨h.vc, h.hint, h.z, hz⟩ (by rw [h.s4, hz]; rfl)

theorem samples_piece :
    VPiece p STK (fun σ s => V2 p STK p.ℓ σ s ∧ flag (zOk p σ p.ℓ) ≠ 0) (VS4 p STK) (samples P p) :=
  (rho_piece hF).seq ((rows_piece hP hF hS).seq (ball_piece hP hF hS))

end

end VG.Proof.MlDsa.RISCV64.Verify

end

end

/-!
# ML-DSA verification on RISC-V: `c̃′ = c̃`

As on PPC64LE (`Proof/MlDsa/PPC64LE/Verify/Cmp.lean`): `r24 ← 0` unless
`c̃′ = c̃`, without a branch (`cmp_piece`), by ML-KEM's loop comparing two
buffers (`Proof/MlKem/RISCV64/CmpSel.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv argOk arg_ok
  argOk_ne baseReg_of base_pres)
open VG.Impl.MlDsa.RISCV64.Verify
open VG.Impl.MlDsa.RISCV64.KeyGen (Ptr Arg)
open VG.Impl.MlKem.RISCV64 (cmpBody)
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-! ## A state that differs but in registers other than the layout's -/

theorem siteCongr {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (h : Site L Wb STK s)
    (hr : ∀ r ∈ [Reg.s8, .s9, .s10, .s11], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Site L Wb STK s' :=
  ⟨h.ok, h.len, h.w0, h.w1, h.sz0, h.sz1, by rw [hsp]; exact h.p1, h.s1168, by rw [hsp]; exact h.spk,
    by rw [hsp]; exact h.al, h.al0,
    by rw [hr _ (by decide)]; exact h.s11, by rw [hr _ (by decide)]; exact h.s10,
    by rw [hr _ (by decide)]; exact h.s9, by rw [hr _ (by decide)]; exact h.s8,
    by rw [hwr]; exact h.cw, by rw [hrd, hwr]; exact h.cr⟩

theorem VC.congr {p : Params} {STK : Nat} {σ s s' : State} (h : VC p STK σ s)
    (hr : ∀ r ∈ preserved, r ≠ .s4 → r ≠ .s6 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VC p STK σ s' :=
  ⟨siteCongr h.site (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl <;> exact hr _ (by decide) (by decide) (by decide)) hsp hrd hwr,
    hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hp hs => by
      have : r ≠ .s4 ∧ r ≠ .s6 := ⟨fun e => by subst e; simp [savedTop] at hs,
        fun e => by subst e; simp [savedTop] at hs⟩
      rw [hr r hp this.1 this.2]; exact h.pres r hp hs,
    by rw [hm]; exact h.sav, by rw [hm]; exact h.pk, by rw [hm]; exact h.mu, by rw [hm]; exact h.sg, h.pre,
    by rw [hr .s3 (by decide) (by decide) (by decide)]; exact h.s3, by rw [hm]; exact h.cache⟩

/-! ## The comparison -/

theorem cmpPre_ok {a b : Ptr} (ha : argOk (.ptr a) = true) (hb : argOk (.ptr b) = true) {n : Nat} (hn : n < 2 ^ 31 - 2048)
    (s : State) :
    WP isa (.block (Arg.instrs .a0 (.ptr a) ++ Arg.instrs .a1 (.ptr b) ++ Arg.instrs .s6 (.imm n) ++
      ([.li .t2 0] : List Instr))) s fun s' =>
      s'.gpr .a0 = s.gpr a.1 + BitVec.ofNat 64 a.2 ∧ s'.gpr .a1 = s.gpr b.1 + BitVec.ofNat 64 b.2 ∧
      s'.gpr .s6 = BitVec.ofNat 64 n ∧ s'.gpr .t2 = 0 ∧ (∀ r ∈ preserved, r ≠ .s6 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have pa := base_pres (baseReg_of ha)
  have pb := base_pres (baseReg_of hb)
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (arg_ok .a0 ha (argOk_ne (by decide) ha) s) fun s1 e1 => ?_
  refine WP.mono (arg_ok .a1 hb (argOk_ne (by decide) hb) s1) fun s2 e2 => ?_
  refine WP.mono (arg_ok .s6 (a := .imm n) (by simp only [argOk, decide_eq_true_eq]; exact hn)
    (fun _ e => by cases e) s2) fun s3 e3 => ?_
  subst e1 e2 e3
  mrun []
  have nb3 : b.1 ≠ .a0 := fun e => by rw [e] at pb; simp [preserved] at pb
  and_intros
  all_goals first
    | rfl
    | trivial
    | (intro r hr hs
       have h1 : r ≠ .t2 := fun e => by subst e; simp [preserved] at hr
       have h2 : r ≠ .a1 := fun e => by subst e; simp [preserved] at hr
       have h3 : r ≠ .a0 := fun e => by subst e; simp [preserved] at hr
       simp only [h1, h2, h3, hs, ite_false])
    | simp only [KeyGen.argVal, nb3, ite_false]

theorem shr63_eq : ∀ n < 256, (BitVec.ofNat 64 n - 1) >>> 63 = if n = 0 then (1 : BitVec 64) else 0 := by
  decide +kernel

theorem shr63_of {v : BitVec 64} (h : v.toNat < 256) : (v - 1) >>> 63 = if v = 0 then (1 : BitVec 64) else 0 := by
  have hv := shr63_eq v.toNat h
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hv
  rw [hv]
  by_cases e : v = 0
  · subst e; rfl
  · have e' : ¬ v.toNat = 0 := fun h' => e (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
    simp only [e, e', ↓reduceIte]

theorem cmpPost_ok (s : State) :
    WP isa (.block [.addi .t2 .t2 (-1), .shift .srl .d .t2 .t2 63, .logic .and .s4 .s4 .t2]) s
      fun s' => s'.gpr .s4 = s.gpr .s4 &&& ((s.gpr .t2 - 1) >>> 63) ∧
        (∀ r ∈ preserved, r ≠ .s4 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  mrun []
  and_intros
  all_goals first
    | rfl
    | trivial
    | (intro r hr hs
       have h1 : r ≠ .t2 := fun e => by subst e; simp [preserved] at hr
       simp only [h1, hs, ite_false])

/-- `s4 ← s4 ∧ (the `n` bytes at `a` and `b` are equal)`. -/
theorem cmpAnd_okS {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) {a b : Ptr} {n : Nat}
    (pa : PtrIn L a n) (pb : PtrIn L b n) (hn : 0 < n) (hn' : n < 2 ^ 31 - 2048) :
    WP isa (cmpAnd a b n) s fun s' =>
      s'.gpr .s4 = s.gpr .s4 &&& flag (decide (bytesAt s.mem (lpa L a) n = bytesAt s.mem (lpa L b) n)) ∧
      (∀ r ∈ preserved, r ≠ .s4 → r ≠ .s6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  have cr : Covers [⟨lpa L a, n⟩, ⟨lpa L b, n⟩] (s.rd ++ s.wr) :=
    Covers.cons (hs.crE pa) (Covers.cons (hs.crE pb) Covers.nil)
  unfold cmpAnd
  refine WP.seq (WP.mono (cmpPre_ok pa.1 pb.1 hn' s) fun s₁ ⟨g3, g4, g26, g12, cs, m, rd, wr, sp⟩ => ?_)
  rw [hs.base (baseReg_of pa.1)] at g3
  rw [hs.base (baseReg_of pb.1)] at g4
  refine WP.seq (wp_loop_nz (CmpInv (lpa L a) (lpa L b) n s₁) (N := n) hn
      (fun k hk s h => cmp_step (by omega_using [hn']) (by rw [rd, wr]; exact cr) hk h) (fun s₂ h => ?_)
    ⟨by rw [g3]; simp [lpa, Lay.A], by rw [g4]; simp [lpa, Lay.A], by rw [g26, Nat.sub_zero], fun _ _ _ => rfl,
      rfl, rfl, rfl, rfl, by rw [g12]; decide,
      by rw [g12]; exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩⟩)
  refine WP.mono (cmpPost_ok s₂) fun s' ⟨r24, rs, m', rd', wr', sp'⟩ => ⟨?_, fun r hr h24 h26 => ?_,
    m'.trans (h.mem.trans m), rd'.trans (h.rd.trans rd), wr'.trans (h.wr.trans wr), sp'.trans (h.sp.trans sp)⟩
  · have e24 : s₂.gpr .s4 = s.gpr .s4 := (h.cs .s4 (by decide) (by decide)).trans (cs .s4 (by decide) (by decide))
    rw [r24, shr63_of h.lt, e24]
    congr 1
    have key : s₂.gpr .t2 = 0 ↔ bytesAt s.mem (lpa L a) n = bytesAt s.mem (lpa L b) n := by
      rw [h.eq, m]
      constructor
      · intro he
        exact Proof.MlKem.bytesAt_eq (Proof.MlKem.bytesAt_length _ _ _) fun t ht => by
          rw [he t ht, Proof.MlKem.bytesAt_getElem]
      · intro he t ht
        have := congrArg (fun L : List Byte => L[t]!) he
        simp only [Proof.MlKem.bytesAt_getElem! _ _ ht] at this
        exact this
    by_cases e : s₂.gpr .t2 = 0
    · simp only [e, decide_eq_true (key.mp e), ↓reduceIte, flag]
    · simp only [e, decide_eq_false (fun h' => e (key.mpr h')), ↓reduceIte, flag, Bool.false_eq_true]
  · rw [rs r hr h24]
    exact (h.cs r hr h26).trans (cs r hr h26)

/-! ## After the comparison -/

/-- At the end of `compute`: `s4` is the samplers' result `R` and whether
`c̃′ = c̃`. -/
abbrev KE (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A' cc h R, VC p STK σ s ∧ hintOf p σ = some h ∧ h.length = p.k ∧ Gd p σ A' cc R ∧
    s.gpr .s4 = R &&& flag (decide (Spec.MlDsa.H (muOf σ ++ w1Enc p σ A' cc h) p.ctildeLen =
      Proof.MlDsa.Verify.vCt p (sgOf p σ)))

theorem cmp_ok {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (h : KF p STK σ s) :
    WP isa (cmpAnd (sc oCT) (.s8, 0) p.ctildeLen) s (KE p STK σ) := by
  obtain ⟨A', cc, hh, R, hk5, hb⟩ := h
  have hk := hF.k
  have hct := hF.ct
  have pa : PtrIn (vlay p STK σ) (sc oCT) p.ctildeLen := by
    refine ⟨vptr_ok rfl (by decide), ?_⟩; rcases hct with e | e | e <;> vsep hF [e]
  have pb : PtrIn (vlay p STK σ) (.s8, 0) p.ctildeLen := by
    refine ⟨vptr_ok rfl (by decide), ?_⟩; have := hF.sig; have := hF.hint; vsep hF
  refine WP.mono (cmpAnd_okS hk5.vc.site pa pb (by omega_using [hct]) (by omega_using [hct]))
    fun s' ⟨r24, rs, m, rd, wr, sp⟩ => ⟨A', cc, hh, R, hk5.vc.congr rs m sp rd wr, hk5.hh, hk5.hint.1, hk5.gd, ?_⟩
  have e4 : bytesAt s.mem (lpa (vlay p STK σ) (.s8, 0)) p.ctildeLen = Proof.MlDsa.Verify.vCt p (sgOf p σ) := by
    have := sig_slice hk5.vc (o := 0) (l := p.ctildeLen) (by have := hF.sig; have := hF.hint; omega_arith)
    rw [List.drop_zero] at this
    exact this
  have e0 : bytesAt s.mem (lpa (vlay p STK σ) (sc oCT)) p.ctildeLen = _ := hb
  rw [r24, e0, e4, hk5.s4]

theorem cmp_taint {n : Nat} (hn : n = 32 ∨ n = 48 ∨ n = 64) : ∃ hc, (VG.RISCV64.taint.check
    (Taint.ofRegs [.s8, .s9, .s10, .s11]) (cmpAnd (sc oCT) (.s8, 0) n) hc).isSome = true := by
  rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem cmp_piece {p : Params} (hF : VFacts p) {STK : Nat} :
    VPiece p STK (KF p STK) (KE p STK) (cmpAnd (sc oCT) (.s8, 0) p.ctildeLen) :=
  ⟨fun _ _ _ h => cmp_ok hF h, rel_of (vtaint4 (cmp_taint hF.ct).choose_spec)
    fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ => ⟨σ₁, vc_twoL pub h₁.vc h₂.vc⟩⟩

end VG.Proof.MlDsa.RISCV64.Verify

end

end

/-!
# ML-DSA verification on RISC-V: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

As on PPC64LE (`Proof/MlDsa/PPC64LE/Verify/Top.lean`): the function, piece
by piece, for any parameter set of Table 1 and any verified implementations
of the primitives (`verify_piece`, `verify_verified`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv relStart)
open VG.Impl.MlKem.RISCV64 (topEnd)
open VG.Impl.MlDsa.RISCV64.Verify
open VG.Impl.MlDsa.RISCV64.KeyGen (seqR)
open VG.Spec.MlDsa (Params Bounds verifyMu minBounds toRq rejNTTPoly sampleInBall)
open VG.Proof.MlDsa (polyAt)
open VG.Proof.MlDsa.Verify (vZ vCt vHint aSeed common_bound verifyMu_rows verifyMu_norm verifyMu_hint_none
  verifyMu_rej_none verifyMu_ball_none verifyMu_mono bmax_left bmax_right normR_vZ_iff)
open VG.Proof.MlDsa.KeyGen (ifn)
open VG.Spec.Sha3 (bytesAt)

/-- A piece keeps a fact about the entry state. -/
theorem pieceFrame {Pre : State → Prop} {Pub : State → State → Prop} {I J : State → State → Prop} {c : Prog isa}
    (h : Piece Pre Pub I J c) (F : State → Prop) :
    Piece Pre Pub (fun σ s => I σ s ∧ F σ) (fun σ s => J σ s ∧ F σ) c :=
  ⟨fun σ s hp ⟨hs, hf⟩ => WP.mono (h.ok σ s hp hs) fun _ h' => ⟨h', hf⟩,
    RelCT.mono h.tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, i₁.1, i₂.1⟩) fun _ _ h => h⟩

/-! ## After the samplers -/

theorem vs4_kx {p : Params} {STK : Nat} {σ s : State} (h : VS4 p STK σ s) : KX p STK 0 false 0 σ s := by
  obtain ⟨hh, e, hi⟩ := h.vb.hint
  exact ⟨fun r c => polyAt s.mem (aA p STK σ r c), polyAt s.mem ((vlay p STK σ).A 0 (oP 15)), hh, s.gpr .s4,
    h.vb.vc, e, hi, fun r hr c hc => ⟨h.red r hr c hc, rfl⟩,
    fun i hi => by rw [ifn (Nat.not_lt_zero i)]; exact h.vb.z i hi, ⟨h.redC, rfl⟩,
    fun _ h => absurd h (Nat.not_lt_zero _), rfl, h.ok⟩

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

theorem compute_piece : VPiece p STK (KX p STK 0 false 0) (KE p STK) (compute P p) := by
  unfold compute
  refine Piece.seq (J := KX p STK p.ℓ false 0) ?_ ((nttC_piece hP hF hS).seq
    (Piece.seq (J := KX p STK p.ℓ true p.k) ?_ ((vhash_piece hF).seq (cmp_piece hF))))
  · refine Piece.mono (Piece.seqR (I := fun j => KX p STK j false 0) p.ℓ 0
      fun j _ hj => nttZ_piece hP hF hS (by omega_using [hj])) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun r => KX p STK p.ℓ true r) p.k 0
      fun r _ hr => row_piece hP hF hS (by omega_using [hr])) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

end

/-! ## The result -/

/-- `verifyMu` of the inputs of a run from `σ`, with the bounds `b`. -/
abbrev vv (p : Params) (σ : State) (b : Bounds) : Option Bool := verifyMu p b (pkOf p σ) (muOf σ) (sgOf p σ)

/-- What the result `r` says of `verifyMu`, as `verifyContract` does. -/
abbrev VOut (p : Params) (σ : State) (r : BitVec 64) : Prop :=
  (r = 1 ∧ ∃ b, vv p σ b = some true) ∨ (r = 0 ∧ vv p σ minBounds ≠ some true)

/-- At the end, before the epilogue: the result in `s4`. -/
abbrev VFin (p : Params) (STK : Nat) (σ s : State) : Prop := VC p STK σ s ∧ VOut p σ (s.gpr .s4)

theorem false_ne {p : Params} {σ : State} {b : Bounds} (h : vv p σ b = some false) : vv p σ minBounds ≠ some true :=
  fun hm => by
    have e₁ := verifyMu_mono (bmax_left b minBounds).rejNTT (bmax_left b minBounds).ball h
    have e₂ := verifyMu_mono (bmax_right b minBounds).rejNTT (bmax_right b minBounds).ball hm
    rw [e₁] at e₂
    cases e₂

theorem ke_out {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (h : KE p STK σ s)
    (hz : zOk p σ p.ℓ = true) : VFin p STK σ s := by
  obtain ⟨A', cc, hh, R, vc, e, hl, ⟨q, hR, hok, hbad⟩, r24⟩ := h
  refine ⟨vc, ?_⟩
  rw [r24, hR, flag_and]
  cases q with
  | false =>
    refine .inr ⟨rfl, ?_⟩
    rcases hbad rfl with ⟨r, hr, c, hc, hn'⟩ | hn'
    · show verifyMu p minBounds _ _ _ ≠ some true
      rw [verifyMu_rej_none minBounds _ _ e hr hc hn']; nofun
    · show verifyMu p minBounds _ _ _ ≠ some true
      rw [verifyMu_ball_none minBounds _ _ e hn']; nofun
  | true =>
    obtain ⟨hA, hB⟩ := hok rfl
    obtain ⟨nA, hnA⟩ := common_bound (P := fun r n => ∀ c < p.ℓ, rejNTTPoly n (aSeed (pkOf p σ) r c) = some (A' r c))
      (fun _ _ _ hle h c hc => Proof.MlDsa.Verify.rejNTTPoly_mono hle (h c hc)) p.k fun r hr =>
        common_bound (P := fun c n => rejNTTPoly n (aSeed (pkOf p σ) r c) = some (A' r c))
          (fun _ _ _ hle h => Proof.MlDsa.Verify.rejNTTPoly_mono hle h) p.ℓ fun c hc => hA r hr c hc
    obtain ⟨bB, hbB⟩ := hB
    obtain ⟨c, hc, hc'⟩ := Option.map_eq_some_iff.mp hbB
    have ev := verifyMu_rows p ⟨0, 0, nA, bB⟩ (pkOf p σ) (muOf σ) (sgOf p σ) e hl hnA hc
    have ew : ((List.range p.k).flatMap fun r => Spec.MlDsa.simpleBitPack
        (Proof.MlDsa.Verify.w1Row p (pkOf p σ) (sgOf p σ) A' (Spec.MlDsa.ntt cc) hh r)
        ((Spec.MlDsa.q - 1) / (2 * p.γ₂) - 1)) = w1Enc p σ A' cc hh := rfl
    rw [decide_eq_true ((normR_vZ_iff hF.nb.2 p hF.g1 _).mpr (of_decide_eq_true hz)), hc', Bool.true_and, ew] at ev
    by_cases hE : Spec.MlDsa.H (muOf σ ++ w1Enc p σ A' cc hh) p.ctildeLen = vCt p (sgOf p σ)
    · exact .inl ⟨by rw [decide_eq_true hE]; rfl, ⟨_, ev.trans (congrArg some (beq_iff_eq.mpr hE.symm))⟩⟩
    · exact .inr ⟨by rw [decide_eq_false hE]; rfl,
        false_ne (ev.trans (congrArg some (beq_eq_false_iff_ne.mpr (Ne.symm hE))))⟩

theorem flag_eq {b : Bool} (h : flag b = 0) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

/-! ## The body -/

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

/-- The samplers and the rest, once `z` is small enough. -/
theorem inner_piece :
    VPiece p STK (V2 p STK p.ℓ) (VFin p STK) (ifOk (.seq (samples P p) (compute P p))) := by
  refine ifOk_piece (v := fun σ => flag (zOk p σ p.ℓ)) (fun _ _ _ h => h.s4) (fun σ₁ σ₂ _ _ pub => ?_)
    ?_ fun σ s _ h hv => ⟨h.vc, .inr ⟨h.s4.trans hv, ?_⟩⟩
  · have e : sgOf p σ₁ = sgOf p σ₂ := pub.2.2.2.2.2.2.2.1
    dsimp only [zOk]
    rw [e]
  · refine Piece.mono (pieceFrame ((samples_piece hP hF hS).seq (Piece.mono (compute_piece hP hF hS)
      (fun _ _ _ h => vs4_kx h) fun _ _ _ h => h)) fun σ => zOk p σ p.ℓ = true)
      (fun _ _ _ h => ⟨h, flag_ne.mp h.2⟩) fun _ _ _ ⟨h, hz⟩ => ke_out hF h hz
  · obtain ⟨hh, e, -⟩ := h.hint
    refine verifyMu_norm minBounds _ _ e fun hn => ?_
    have := flag_eq hv
    rw [zOk, decide_eq_false_iff_not] at this
    exact this ((normR_vZ_iff hF.nb.2 p hF.g1 _).mp hn)

omit hP hF hS in
theorem v1_v2 {σ s : State} (h : V1 p STK σ s) (hv : flag (hintOf p σ).isSome ≠ 0) : V2 p STK 0 σ s := by
  cases e : hintOf p σ with
  | none => rw [e] at hv; exact absurd rfl hv
  | some hh =>
    refine ⟨h.vc, ⟨hh, e, h.hint hh e⟩, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
    rw [h.s4, e, show zOk p σ 0 = true from decide_eq_true fun _ h => absurd h (Nat.not_lt_zero _)]
    rfl

omit hP hF hS in
theorem v1_out {σ s : State} (h : V1 p STK σ s) (hv : flag (hintOf p σ).isSome = 0) : VFin p STK σ s := by
  refine ⟨h.vc, .inr ⟨h.s4.trans hv, ?_⟩⟩
  have e : hintOf p σ = none := Option.not_isSome_iff_eq_none.mp (by rw [flag_eq hv]; nofun)
  show verifyMu p minBounds _ _ _ ≠ some true
  rw [verifyMu_hint_none minBounds _ _ e]
  nofun

theorem body_piece : VPiece p STK (fun σ s => VC p STK σ s ∧ s.gpr .s4 = 1) (VFin p STK) (body P p) := by
  have hl := hF.l
  unfold body
  refine (hint_piece hP hF hS).seq (ifOk_piece (v := fun σ => flag (hintOf p σ).isSome) (fun _ _ _ h => h.s4)
    (fun σ₁ σ₂ _ _ pub => ?_) ?_ fun _ _ _ h hv => v1_out h hv)
  · have e : sgOf p σ₁ = sgOf p σ₂ := pub.2.2.2.2.2.2.2.1
    dsimp only [hintOf]
    rw [e]
  · refine Piece.seq (Piece.mono (Piece.seqR (I := fun j => V2 p STK j) p.ℓ 0
      fun j _ hj => zOne_piece hP hF hS (by omega_using [hj])) (fun _ _ _ h => v1_v2 h.1 h.2) fun _ _ _ h => ?_)
      (inner_piece hP hF hS)
    rwa [Nat.zero_add] at h

end

/-! ## The return -/

theorem vepi_ok {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (h : VFin p STK σ s) :
    WP isa (.block topEnd) s fun s' =>
      RISCV64.target.abiPreserved σ s' ∧ (Proof.MlDsa.verifyWithCacheContract p RISCV64.abi STK).post σ s' := by
  obtain ⟨vc, hr⟩ := h
  have hs := vc.site
  have hscr := hF.scr
  have hk := hF.k
  have hin : ∀ o, 1288 ≤ o → o + 8 ≤ 1368 → InRegions (s.rd ++ s.wr) (vScr σ + BitVec.ofNat 64 o) 8 :=
    fun o h₁ h₂ => mem_rd_wr' (Lay.covers (L := vlay p STK σ) (o := o) (l := 8) (hs.cw 0 (by decide) (by decide))
      (by rw [vlay_size0]; omega_using [hscr, h₂]) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
  refine WP.mono (topEnd_ok hs.s11 hs.al0 vc.sav hin vc.pres)
    fun s' ⟨pr, lr, r3, _, sp', _, _⟩ => ⟨⟨pr, sp'.trans vc.sp, lr⟩, ?_⟩
  sig_post [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, RISCV64.abi,
    RISCV64.argRegs]
  rw [r3]
  rcases hr with ⟨e, h⟩ | ⟨e, h⟩ <;> rw [e]
  · exact .inl ⟨rfl, h⟩
  · exact .inr ⟨rfl, h⟩

theorem vepi_piece {p : Params} (hF : VFacts p) {STK : Nat} :
    VPiece p STK (VFin p STK)
      (fun σ s => RISCV64.target.abiPreserved σ s ∧ (Proof.MlDsa.verifyWithCacheContract p RISCV64.abi STK).post σ s)
      (.block topEnd) :=
  ⟨fun _ _ _ h => vepi_ok hF h, vrel31 (fun _ _ h => h.1) (by taint_decide)⟩

/-! ## The function -/

theorem verify_piece {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat}
    (hS : S ≤ STK) (h48 : 1168 ≤ STK) :
    VPiece p STK (fun σ s => s = σ)
      (fun σ s => RISCV64.target.abiPreserved σ s ∧ (Proof.MlDsa.verifyWithCacheContract p RISCV64.abi STK).post σ s)
      (verify P p) :=
  (vpro_piece hF h48).seq ((body_piece hP hF hS).seq (vepi_piece hF))

/-- A state satisfying `verifyWithCacheContract`'s precondition, with an
empty cache. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x10000 | .a4 => 0x9000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x2000, 64⟩, ⟨0x3000, p.sigLen⟩, ⟨0x9000, 0⟩]
  wr := [⟨0x10000, scrLen p⟩]

/-- `vg_mldsa*_verify_with_cache` of the parameter set `p` meets its contract with `S`
bytes of stack, for any verified implementations `P` of the primitives it
calls with at most `S` bytes of stack, and `S` at least the 1168 bytes the
sponge needs. The contract's satisfiability (`hsat`, by `verifySat`) is
evaluated once `S` is known. -/
theorem verify_verified {P : Prims} {S : Nat} (hP : VPrimsOk P S) (h48 : 1168 ≤ S) (p : Spec.MlDsa.Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
    (hsat : (Proof.MlDsa.verifyWithCacheContract p RISCV64.abi S).pre (verifySat p)) :
    Verified RISCV64.target (verify P p) (Proof.MlDsa.verifyWithCacheContract p RISCV64.abi S) := by
  have hF := vfacts hp
  have hk := verify_piece hP hF (Nat.le_refl _) h48
  obtain ⟨n, rfl⟩ : ∃ n, S = n + 1 := ⟨S - 1, by omega_using [h48]⟩
  refine ⟨fun s hs => hk.ok s s (vpre_of hs) rfl, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_,
    ⟨verifySat p, hsat⟩⟩
  sig_pub [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, RISCV64.abi,
    RISCV64.argRegs] at hpub
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8⟩ := hpub
  obtain ⟨e12, e3⟩ := List.append_inj (Proof.MlDsa.KeyGen.leakBytes_inj hl)
    (by simp only [List.length_append, Proof.MlKem.bytesAt_length])
  obtain ⟨e1, e2⟩ := List.append_inj e12 (by simp only [Proof.MlKem.bytesAt_length])
  exact relStart hk.tr s₁ s₂ t₁ t₂ s₁' s₂' (vpre_of h₁) (vpre_of h₂) ⟨hsp, h3, h4, h5, h6, e1, e2, e3, h7, h8⟩ e₁ e₂

end VG.Proof.MlDsa.RISCV64.Verify

end

end

/-! ### `MlDsa.RISCV64.Pack.HintPackCT`, which only this module used -/

section

/-!
# ML-DSA on RISC-V: `vg_mldsa_hint_bit_pack`, constant time and `Verified`

Constant time but for the hint, as on AArch64: zeroing `y` leaks only the
pointers and `len` (the taint analysis), and leaves states that agree on
`k`, `ω` and the pointers, and on all the memory the loops may access (the
hint, which the contract lets them leak, and `y`, zeroed); `memTaint`
proves the rest. `omega` is a `u32`, whose register's upper bits the two
runs need not agree on: the code zero-extends it before using it.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack.Hint

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

theorem pre_of {s : State} (h : (hintBitPackContract RISCV64.abi).pre s) : PPre s := by
  sig_pre [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- The public registers of the loops: the pointers, `k`, `ω`. -/
abbrev hbpTaint : VG.RISCV64.Taint.T := VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3]

theorem ct : ConstantTime isa (hintBitPackContract RISCV64.abi).pre (hintBitPackContract RISCV64.abi).pub
    Impl.MlDsa.RISCV64.Pack.hintBitPack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.RISCV64.Pack.hintBitPack
  refine RelCT.seq (R := MAgree hbpTaint) ?_
    (RelCT.taint (A := memTaint) hbpTaint (fun _ _ h => h) (by taint_decide))
  refine RelCT.mono (RelCT.wpDep (F := fun (s₀ s : State) => ZPost s₀ s ∧ s.sp = s₀.sp)
    (RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs [.a3, .a4]) ?_ (by taint_decide))
    (fun x y ⟨hx, hy, _⟩ => ⟨wp_sp (zero_ok (pre_of hx)), wp_sp (zero_ok (pre_of hy))⟩)) (fun _ _ h => h) ?_
  · rintro a b ⟨_, _, hab⟩
    sig_pub [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs] at hab
    obtain ⟨hsp, -, -, -, -, h6, h7⟩ := hab
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h6
    · exact h7
  rintro x' y' ⟨_, x, y, ⟨hx, hy, hpb⟩, ⟨fx, spx⟩, ⟨fy, spy⟩⟩
  have px := pre_of hx
  have py := pre_of hy
  sig_pub [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs] at hpb
  obtain ⟨hsp, hleak, p3, p4, p5, p6, p7⟩ := hpb
  have hω : pω x = pω y := by simp only [pω, w32, p5]
  have hrd : x'.rd = y'.rd := by rw [fx.rd, fy.rd, px.rd, py.rd]; simp only [hR, pH, p3, p4]
  have hwr : x'.wr = y'.wr := by rw [fx.wr, fy.wr, px.wr, py.wr]; simp only [yR, pY, pLen, p6, p7]
  refine ⟨⟨by rw [spx, spy, hsp], fun r hr => ?_⟩, hrd, hwr, fun a ha => ?_⟩
  · simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [fx.a0, fy.a0]; simp only [pH, p3]
    · rw [fx.a1, fy.a1]; simp only [pk, pLen, p7, hω]
    · rw [fx.a2, fy.a2, hω]
    · rw [fx.a3, fy.a3]; simp only [pY, p6]
  · rw [fx.rd, fx.wr, px.rd, px.wr] at ha
    obtain ⟨r, hr, hc⟩ := ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · -- The hint: as on entry, where the runs agree.
      have hxy : ¬ (yR x).Contains a 1 := fun hc' => px.d_hy a hc hc'
      rw [fx.frame a (fun r hr hc' => by simp only [List.mem_singleton] at hr; subst hr; exact hxy hc'),
        fy.frame a (fun r hr hc' => by
          simp only [List.mem_singleton] at hr; subst hr
          simp only [yR, pY, pLen, ← p6, ← p7] at hc'
          exact hxy hc')]
      exact bytes_of_words (by simpa only [p3, p4] using hleak) (by simpa only [hR, pH, p3, p4] using hc)
    · -- `y`: zeros.
      have hlt : (a - pY x).toNat < pLen x := by simp only [Region.Contains] at hc; omega_using [hc]
      have ea : a = pY x + BitVec.ofNat 64 (a - pY x).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have h₁ := fx.zero _ hlt
      have h₂ := fy.zero _ (show _ < pLen y by simpa only [pLen, ← p7] using hlt)
      rw [← ea] at h₁
      rw [show pY y = pY x by simp only [pY, p6], ← ea] at h₂
      rw [h₁, h₂]

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 1024 | .a2 => 80 | .a3 => 0x3000 | .a4 => 84 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 4096⟩]
  wr := [⟨0x3000, 84⟩]

end VG.Proof.MlDsa.RISCV64.Pack.Hint

namespace VG.Proof.MlDsa.RISCV64.Pack

open VG VG.RISCV64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.RISCV64.Pack.Hint

theorem hintBitPack_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Pack.hintBitPack (hintBitPackContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, ct, ⟨satState, ?_⟩⟩
  · obtain ⟨t, s', he, hy, hk⟩ := correct (pre_of hs)
    refine ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), ?_⟩
    sig_post [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs]
    exact hy
  · sig_apply_check
    · decide +kernel
    · sig_reduce [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | (rw [hintOnes_zero]; exact Nat.zero_le _)
        | trivial
        | exact Region.disjoint_of_sep (by decide)
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Pack

end

end

/-! ### `MlDsa.RISCV64.Sign.Top`, which only this module used -/

section

/-!
# ML-DSA signing on RISC-V: the function

As on PPC64LE (`Proof/MlDsa/PPC64LE/Sign/Correct.lean`, `SignCT.lean`,
`Top.lean`). The function returns 1 with `Sign_internal`'s signature (within
`maxBounds`) in `sig`, or 0 when `Sign_internal` returns nothing within
`minBounds` (`sign_ok`): its `ExpandA` or its loop does not finish
(`signMu_min_A`, `signMu_min_L`), or an iteration passes (`signMu_max`). Two
runs whose entry states agree on what the contract makes public leak the same
(`sign_tr`): the prologue and the return only the pointers, `ExpandA` its seed
and results, the loop what `signLeakT` says, and the signature its hint.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relStart relInv)
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Impl.MlDsa.RISCV64.KeyGen (callAt seqR)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign (aSeed amat ParamsOk)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## `Sign_internal` -/

section
variable {p : Params} {σ : State}

theorem seedE_ij {i j : Nat} (hj : j < p.ℓ) : seedE p σ (p.ℓ * i + j) = aSeed (rhoOf p σ) i j := by
  have hl : 0 < p.ℓ := by omega_using [hj]
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [seedE, e1, e2]

theorem expandA_max (hok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (seedE p σ e)).isSome) :
    expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ)) :=
  Proof.MlDsa.Sign.expandA_some fun i hi j hj => by rw [← seedE_ij hj]; exact hok _ (ij_lt hi hj)

theorem signMu_min_A (h : ∃ e < p.k * p.ℓ, rejNTTPoly minBounds.rejNTT (seedE p σ e) = none) :
    signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none := by
  obtain ⟨e, he, hn⟩ := h
  have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega_using [he]
  exact Proof.MlDsa.Sign.signMu_none_A (Proof.MlDsa.Sign.expandA_none
    ⟨e / p.ℓ, (Nat.div_lt_iff_lt_mul hl).mpr he, e % p.ℓ, Nat.mod_lt _ hl, hn⟩)

theorem signMu_min_L (hA : expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ)))
    (hL : loopF p σ minBounds minBounds.sign 0 = none) :
    signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none := by
  cases e : expandA p minBounds (rhoOf p σ) with
  | none => exact Proof.MlDsa.Sign.signMu_none_A e
  | some A' =>
    have := Proof.MlDsa.Sign.expandA_mono (show minBounds.rejNTT ≤ maxBounds.rejNTT by decide) e
    rw [hA] at this
    obtain rfl := (Option.some.inj this).symm
    exact Proof.MlDsa.Sign.signMu_none_L e hL

theorem signMu_max (hp : ParamsOk p) (hA : expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ))) {t : Nat}
    (ht : t < 814) (hr : RejT p σ t) (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome)
    (hpass : PassV p σ (p.ℓ * t)) :
    signMu p maxBounds (skOf p σ) (muOf σ) (rndOf σ) = some (sigV p σ (p.ℓ * t)) :=
  Proof.MlDsa.Sign.signMu_some hA (Proof.MlDsa.Sign.signLoop_pass _ _ _ _ _ _ _ hr (show t < maxBounds.sign by
    show t < 1000; omega_using [ht]) (iter_pass hp hs hpass))

end

/-! ## Before the return -/

/-- What the return needs: the pointer to `scratch`, our caller's registers in it, and the registers
we preserve. -/
structure TF (p : Params) (STK : Nat) (σ s : State) : Prop where
  s11 : s.gpr .s11 = sScr σ
  sav : TopSaved s.mem (sScr σ) σ
  pres : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = σ.gpr r
  sp : s.sp = σ.sp
  inr : ∀ o, 1288 ≤ o → o + 8 ≤ 1368 → InRegions (s.rd ++ s.wr) (sScr σ + BitVec.ofNat 64 o) 8

theorem SC1.tf {p : Params} (hF : SFacts p) {STK : Nat} {σ s : State} (h : SC1 p STK σ s) : TF p STK σ s := by
  have hs := h.site
  have hscr := hF.scr
  exact ⟨hs.s11, h.sav, h.pres, h.sp, fun o h₁ h₂ => mem_rd_wr' (Lay.covers (L := slay1 p STK σ) (o := o)
    (l := 8) (hs.cw 0 (by decide) (by decide)) (by rw [slay1_size0]; omega_using [hscr, h₂]) _ _
    ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)⟩

theorem SC2.tf {p : Params} (hF : SFacts p) {STK : Nat} {σ s : State} (h : SC2 p STK σ s) : TF p STK σ s := by
  have hs := h.site
  have hscr := hF.scr
  exact ⟨hs.s11, h.sav, h.pres, h.sp, fun o h₁ h₂ => mem_rd_wr' (Lay.covers (L := slay2 p STK σ) (o := o)
    (l := 8) (hs.cw 0 (by decide) (by decide)) (by rw [slay2_size0]; omega_using [hscr, h₂]) _ _
    ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)⟩

/-- Before the return: `s4`, and the signature in `sig` if it is 1. -/
structure FS (p : Params) (STK : Nat) (σ s : State) : Prop where
  tf : TF p STK σ s
  r01 : s.gpr .s4 = 0 ∨ s.gpr .s4 = 1
  ok : s.gpr .s4 = 1 →
    signMu p maxBounds (skOf p σ) (muOf σ) (rndOf σ) = some (bytesAt s.mem (sSig σ) p.sigLen)
  bad : s.gpr .s4 = 0 → signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none

theorem r24_one {s : State} (h : s.gpr .s4 = 0 ∨ s.gpr .s4 = 1) (hne : s.gpr .s4 ≠ 0) : s.gpr .s4 = 1 := by
  rcases h with e | e
  · exact absurd e hne
  · exact e

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
  (hp : ParamsOk p)
include hP hF hS hp

theorem rest_ok {σ : State} (hpre : SPre p STK σ) {s : State} (h : IM p STK σ s) :
    WP isa (rest P p) s (FS p STK σ) := by
  have hA := expandA_max h.ok
  unfold rest
  refine WP.seq (WP.mono ((decode_piece hP hF hS).ok σ s hpre h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (signLoop_ok hP hF hS hp hpre h1.ik) fun s2 h2 => ?_)
  unfold ifOk ifOkElse
  refine WP.ite _ (Steps.eval_nonzero s2 .s4) (fun hb => ?_) fun hb => WP.block_nil ?_
  · have h1 := r24_one h2.r01 (by simpa using hb)
    obtain ⟨t, ht, hr, hs, hpass, hct, hz, hh⟩ := h2.pass h1
    refine WP.mono (output_ok hP hF hS ⟨h2.k, hz, hh, hpass, h1⟩ hct) fun s4 ⟨k4, hb4, h4⟩ =>
      ⟨k4.sc.tf hF, .inr h4, fun _ => ?_, fun h0 => absurd (h0.symm.trans h4) (by decide)⟩
    have e : (slay2 p STK σ).A 4 0 = sSig σ := by simp only [Lay.A, BitVec.add_zero]; rfl
    rw [← e, hb4]
    exact signMu_max hp hA ht hr hs hpass
  · have h0 : s2.gpr .s4 = 0 := by simpa using hb
    exact ⟨h2.k.sc.tf hF, .inl h0, fun h1 => absurd (h0.symm.trans h1) (by decide),
      fun _ => signMu_min_L hA (h2.fail h0)⟩


theorem sign_ok {σ : State} (hpre : SPre p STK σ) (h48 : 1168 ≤ STK) :
    WP isa (sign P p) σ fun s' =>
      RISCV64.target.abiPreserved σ s' ∧ (Proof.MlDsa.signWithCacheContract p RISCV64.abi STK).post σ s' := by
  unfold sign
  refine WP.seq (WP.mono (spro_ok hF h48 hpre) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (expandA_ok hP hF hS h₁.1 h₁.2) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (show WP isa (ifOk (rest P p)) s₂ (FS p STK σ) from ?_) fun s₄ h₄ => ?_)
  · unfold ifOk ifOkElse
    refine WP.ite _ (Steps.eval_nonzero s₂ .s4) (fun hb => ?_) fun hb => WP.block_nil ?_
    · exact rest_ok hP hF hS hp hpre (h₂.im (r24_one h₂.r01 (by simpa using hb)))
    · have h0 : s₂.gpr .s4 = 0 := by simpa using hb
      exact ⟨h₂.sc.tf hF, .inl h0, fun h1 => absurd (h0.symm.trans h1) (by decide),
        fun _ => signMu_min_A (h₂.bad h0)⟩
  · refine WP.mono (topEnd_ok h₄.tf.s11 hpre.al_c h₄.tf.sav h₄.tf.inr h₄.tf.pres)
      fun s' ⟨pr, lr, r3, m', sp', _, _⟩ => ⟨⟨pr, sp'.trans h₄.tf.sp, lr⟩, ?_⟩
    sig_post [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, Spec.MlDsa.signSig, RISCV64.abi,
      RISCV64.argRegs]
    rw [r3, m']
    rcases h₄.r01 with h0 | h1
    · exact .inr ⟨by rw [h0]; rfl, h₄.bad h0⟩
    · exact .inl ⟨by rw [h1]; rfl, maxBounds, h₄.ok h1⟩

/-! ## Two runs -/

omit hP hF hS hp in
/-- Two runs whose `ExpandA` finished agree on what their loops leak. -/
theorem pub_leq {σ₁ σ₂ : State} (hpub : sPub p σ₁ σ₂)
    (hA₁ : expandA p maxBounds (rhoOf p σ₁) = some (amat p (Am p σ₁)))
    (hA₂ : expandA p maxBounds (rhoOf p σ₂) = some (amat p (Am p σ₂))) : LeakEq p 0 σ₁ σ₂ := by
  have e := hpub.2.2.2.2.2.2.1
  rw [Proof.MlDsa.Sign.signLeak_eq hA₁, Proof.MlDsa.Sign.signLeak_eq hA₂, pub_rho hpub] at e
  exact List.append_cancel_left e

omit hP hF hS hp in
theorem relct_nil {Q : State → State → Prop} {P : State → State → Prop} (h : ∀ x y, P x y → Q x y) :
    RelCT isa P (.block []) Q := by
  intro _ _ _ _ _ _ hr e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  obtain ⟨rfl, rfl⟩ := e₁
  obtain ⟨rfl, rfl⟩ := e₂
  exact ⟨rfl, h _ _ hr⟩

omit hP hF hS hp in
theorem hintIs_unique {m : Mem} {a : Addr} {h h' : Vector Bool n} (H : HintIs m a 1 [h]) (H' : HintIs m a 1 [h']) :
    h = h' := by
  apply Vector.ext
  intro j hj
  have e := H.2 0 (by decide) j hj
  have e' := H'.2 0 (by decide) j hj
  simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero, getElem!_pos h j hj, getElem!_pos h' j hj] at e e'
  rw [e] at e'
  revert e'
  cases h[j] <;> cases h'[j] <;> decide

omit hp in
/-- The two runs of the signature, from the end of the loop. -/
theorem outIf_tr :
    RelCT isa (OX p STK) (ifOk (output P p)) fun x y => Rel2 (SPre p STK) (sPub p) (SC2 p STK) x y := by
  unfold ifOk ifOkElse
  refine RelCT.ite (fun x y ⟨_, _, _, _, _, _, _, e, _⟩ => by rw [Steps.eval_nonzero, Steps.eval_nonzero, e]) ?_ ?_
  · refine liftG (Q₀ := fun _ _ => True) (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂, e24, hh⟩, hb⟩ => ?_)
      (RelCT.mono (output_tr hP hF hS) (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂, e24, hh⟩, hb⟩ => ?_) fun _ _ h => h)
    · have hx := r24_one h₁.r01 (by rw [Steps.eval_nonzero] at hb; simpa using hb)
      have hy := r24_one h₂.r01 (by rw [← e24]; rw [Steps.eval_nonzero] at hb; simpa using hb)
      obtain ⟨t₁, -, -, -, ps₁, ct₁, z₁, hh₁⟩ := h₁.pass hx
      obtain ⟨t₂, -, -, -, ps₂, ct₂, z₂, hh₂⟩ := h₂.pass hy
      exact ⟨_, _, output_ok hP hF hS ⟨h₁.k, z₁, hh₁, ps₁, hx⟩ ct₁, output_ok hP hF hS ⟨h₂.k, z₂, hh₂, ps₂, hy⟩ ct₂,
        fun x' y' a b _ => ⟨σ₁, σ₂, p₁, p₂, pub, a.1.sc, b.1.sc⟩⟩
    · have hx := r24_one h₁.r01 (by rw [Steps.eval_nonzero] at hb; simpa using hb)
      have hy := r24_one h₂.r01 (by rw [← e24]; rw [Steps.eval_nonzero] at hb; simpa using hb)
      obtain ⟨t₁, -, -, -, ps₁, ct₁, z₁, hh₁⟩ := h₁.pass hx
      obtain ⟨t₂, -, -, -, ps₂, ct₂, z₂, hh₂⟩ := h₂.pass hy
      obtain ⟨f, f₁, f₂⟩ := hh hx
      refine ⟨σ₁, σ₂, p.ℓ * t₁, p.ℓ * t₂, p₁, p₂, pub, ⟨⟨h₁.k, z₁, hh₁, ps₁, hx⟩, ct₁⟩,
        ⟨⟨h₂.k, z₂, hh₂, ps₂, hy⟩, ct₂⟩, fun i hi => ?_⟩
      have a₂ := hh₂ i hi
      rw [← SL_pub pub] at a₂
      exact (hintIs_unique (hh₁ i hi) (f₁ i hi)).trans (hintIs_unique (f₂ i hi) a₂)
  · exact relct_nil fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂, _⟩, _⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.k.sc, h₂.k.sc⟩

/-- `rest`, from runs whose `ExpandA` finished. -/
theorem rest_tr :
    RelCT isa (Rel2 (SPre p STK) (sPub p) (IM p STK)) (rest P p)
      fun x y => Rel2 (SPre p STK) (sPub p) (SC2 p STK) x y := by
  unfold rest
  refine RelCT.mono (P := RS p STK (LeakEq p 0) (IM p STK)) ?_
    (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub,
      pub_leq pub (expandA_max h₁.ok) (expandA_max h₂.ok), h₁, h₂⟩) fun _ _ h => h
  refine RelCT.seq (pieceRS (decode_piece hP hF hS)) (RelCT.seq ?_ (outIf_tr hP hF hS))
  exact RelCT.mono (signLoop_tr hP hF hS hp) (fun x y h => h.mono fun _ _ h => h.ik) fun _ _ h => h

/-- Two runs whose entry states agree on the public data leak the same. -/
theorem sign_tr (h48 : 1168 ≤ STK) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) fun σ s => s = σ) (sign P p) fun _ _ => True := by
  unfold sign
  refine RelCT.seq (relInv (spro_piece hF h48).ok (spro_piece hF h48).tr) ?_
  refine RelCT.seq (RelCT.mono (expandA_tr hP hF hS) (fun x y h => ⟨h, trivial⟩) fun _ _ h => h) ?_
  refine RelCT.seq (Q := fun _ _ => True) (R := fun x y => Rel2 (SPre p STK) (sPub p) (SC1 p STK) x y ∨
      Rel2 (SPre p STK) (sPub p) (SC2 p STK) x y) ?_
    (relOr (srel1 (fun _ _ h => h) (by taint_decide)) (srel2 (fun _ _ h => h) (by taint_decide)))
  unfold ifOk ifOkElse
  refine RelCT.ite (fun x y ⟨_, e⟩ => by rw [Steps.eval_nonzero, Steps.eval_nonzero, e]) ?_ ?_
  · refine RelCT.mono (rest_tr hP hF hS hp) (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, e⟩, hb⟩ => ?_)
      fun _ _ h => .inr h
    have hx := r24_one h₁.r01 (by rw [Steps.eval_nonzero] at hb; simpa using hb)
    exact ⟨σ₁, σ₂, p₁, p₂, pub, h₁.im hx, h₂.im (r24_one h₂.r01 (by rw [← e, hx]; decide))⟩
  · exact relct_nil fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, _⟩, _⟩ => .inl ⟨σ₁, σ₂, p₁, p₂, pub, h₁.sc, h₂.sc⟩
end

/-! ## The contract -/

/-- A state that satisfies `signWithCacheContract`'s precondition, with an
empty cache, for the contract's satisfiability. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x8000 | .a2 => 0x9000 | .a3 => 0xA000 | .a4 => 0x10000 | .a5 => 0x9800 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x8000, 64⟩, ⟨0x9000, 32⟩, ⟨0x9800, 0⟩]
  wr := [⟨0xA000, p.sigLen⟩, ⟨0x10000, scrLen p⟩]

/-- `vg_mldsa*_sign_with_cache` of the parameter set `p` meets its contract with `S`
bytes of stack, for any verified implementations `P` of the primitives it
calls with at most `S` bytes of stack whose samplers' results are public
(`SPrimsOk`), and `S` at least the 48 bytes the sponge needs. The contract's
satisfiability (`hsat`, by `signSat`) is evaluated once `S` is known. -/
theorem sign_verified {P : Prims} {S : Nat} (hP : SPrimsOk P S) (h48 : 1168 ≤ S)
    (p : Spec.MlDsa.Params) (hp3 : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
    (hsat : (Proof.MlDsa.signWithCacheContract p RISCV64.abi S).pre (signSat p)) :
    Verified RISCV64.target (sign P p) (Proof.MlDsa.signWithCacheContract p RISCV64.abi S) := by
  have hF := sfacts hp3
  have hp : ParamsOk p := by rcases hp3 with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  obtain ⟨n, rfl⟩ : ∃ n, S = n + 1 := ⟨S - 1, by omega_using [h48]⟩
  refine ⟨fun s hs => sign_ok hP hF (Nat.le_refl _) hp (spre_of hs) h48,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨signSat p, hsat⟩⟩
  sig_pub [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, Spec.MlDsa.signSig, RISCV64.abi,
    RISCV64.argRegs] at hpub
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9⟩ := hpub
  exact relStart (sign_tr hP hF (Nat.le_refl _) hp h48) s₁ s₂ t₁ t₂ s₁' s₂' (spre_of h₁) (spre_of h₂)
    ⟨hsp, h3, h4, h5, h6, h7, hl, h8, h9⟩ e₁ e₂

end VG.Proof.MlDsa.RISCV64.Sign

end

end

/-! ### `MlDsa.RISCV64.Round.UseHint`, which only this module used -/

section

/-!
# ML-DSA on RISC-V: `vg_mldsa_use_hint`

As PPC64LE's (`Proof/MlDsa/PPC64LE/Round/UseHint.lean`).

The selection of `γ₂` (`sel_ok'`), then the loop for it: one symbolic
execution of its body for any pointers (`body_ok`), which stores `uhv` of
the coefficient of `r` and the hint word (`uh_val`: the value
`useHint_eq` gives); the invariant says which coefficients of `out` are
done.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Round.UseHint

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Round
open VG.Impl.MlKem.RISCV64 (fixup)
open VG.Impl.MlDsa.RISCV64.Arith (loadImm)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_writeW coeffAt_frame zipWith_get useHint_eq
  mem_gamma2s hbF hbM hbF_le hintAt_get natPolyIs_of_toNat reduced_zero)
open VG.Proof.MlDsa.RISCV64.Round
open VG.Proof.MlDsa.RISCV64.Round.Bits (dMul_lt kgpr selGpr sel_ok' sel_ct consts_ok)
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_succ align4_add)
open VG.Proof.MlDsa.RISCV64.Arith (loadImm_val loadImm_imm)

/-! ## Values -/

/-- What the body stores for the coefficient `a` and the hint word `w`. -/
def uhv (g : Nat) (a w : BitVec 64) : BitVec 64 :=
  fixk (BitVec.ofNat 64 (dMod g)) (fixk (BitVec.ofNat 64 (dMod g))
    (hbr g a + (hbr g a * BitVec.ofNat 64 (2 * g) - a) >>> 63 <<< 1 -
      (hbr g a * BitVec.ofNat 64 (2 * g) - a) >>> 63 <<< 1 * ((w - 1) >>> 63) + (w - 1) >>> 63 - 1) -
    BitVec.ofNat 64 (dMod g))

/-- The value `useHint_eq` gives. -/
def uhNat (g a : Nat) (b : Bool) : Nat :=
  (if b then (if hbF g a * (2 * g) < a then hbF g a + hbM g + 1 else hbF g a + hbM g - 1)
    else hbF g a + hbM g) % hbM g

/-- `fixup`, a subtraction of `m` and `fixup` again, of `u` in `[-1, m + 1]`:
`u mod m`. -/
theorem fixk2 {m : Nat} (hm : m < 64) (hm0 : 0 < m) {u : BitVec 64} (hu : u.toNat ≤ m + 1 ∨ u.toNat = 2 ^ 64 - 1) :
    (fixk (BitVec.ofNat 64 m) (fixk (BitVec.ofNat 64 m) u - BitVec.ofNat 64 m)).toNat =
      if u.toNat < m then u.toNat else if u.toNat ≤ m + 1 then u.toNat - m else m - 1 := by
  have hM : (BitVec.ofNat 64 m).toNat = m := by rw [BitVec.toNat_ofNat]; omega_using [hm]
  simp only [fixk_eq]
  generalize BitVec.ofNat 64 m = M at hM ⊢
  have h1 : u >>> 63 = 0 ∨ u >>> 63 = 1 := by bv_omega
  rcases h1 with h1 | h1 <;> rw [h1]
  · have h2 : (u + 0 * M - M) >>> 63 = 0 ∨ (u + 0 * M - M) >>> 63 = 1 := by bv_omega
    rcases h2 with h2 | h2 <;> rw [h2] <;> split <;> (try split) <;> bv_omega
  · have h2 : (u + 1 * M - M) >>> 63 = 0 ∨ (u + 1 * M - M) >>> 63 = 1 := by bv_omega
    rcases h2 with h2 | h2 <;> rw [h2] <;> split <;> (try split) <;> bv_omega

/-- `fixk2` of `u = x - m`, for `x` in `[m - 1, 2m + 1]`: `x mod m`. -/
theorem fixk2_mod {m : Nat} (hm : m < 64) (hm1 : 1 < m) {u : BitVec 64} {x : Nat} (hx : x ≤ 2 * m + 1)
    (hu : u.toNat + m = x ∨ (u.toNat = 2 ^ 64 - 1 ∧ x = m - 1)) :
    (fixk (BitVec.ofNat 64 m) (fixk (BitVec.ofNat 64 m) u - BitVec.ofNat 64 m)).toNat = x % m := by
  rw [fixk2 hm (by omega_using [hm1]) (by omega_using [hx, hu])]
  have m1 : ∀ y, m ≤ y → y < 2 * m → y % m = y - m := fun y h1 h2 => by
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega_using [h2])]
  have m2 : ∀ y, 2 * m ≤ y → y < 3 * m → y % m = y - 2 * m := fun y h1 h2 => by
    rw [Nat.mod_eq_sub_mod (by omega_using [h1]), m1 _ (by omega_using [h1]) (by omega_using [h2])]; omega_using []
  rcases hu with hu | ⟨hu, rfl⟩
  · split
    · rw [m1 _ (by omega_using [hu]) (by omega_arith)]; omega_using [hu]
    · split
      · rw [m2 _ (by omega_arith) (by omega_using [hm1, hx])]; omega_using [hu]
      · omega_arith
  · rw [Nat.mod_eq_of_lt (by omega_using [hm1])]
    split
    · omega_arith
    · split <;> omega_arith

theorem uh_val {g : Nat} (hg : g ∈ gamma2s) {a w : BitVec 64} (ha : a.toNat < q) (hw : w.toNat < 2 ^ 32) :
    (uhv g a w).toNat = uhNat g a.toNat (decide (w.toNat ≠ 0)) := by
  have hr := hbr_toNat hg ha
  have hf := hbF_le hg ha
  have hm := dMod_eq hg
  obtain ⟨-, m64⟩ := dMod_pos hg
  have m1 : 1 < dMod g := by unfold dMod; split <;> decide
  have hg2 : 2 * g ≤ 523776 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  have hF : (hbr g a).toNat ≤ dMod g := by rw [hr, hm]; exact hf
  unfold uhv uhNat
  rw [← hr, ← hm]
  generalize hbr g a = F at hF ⊢
  have hF44 : F.toNat ≤ 44 := Nat.le_trans hF (by unfold dMod; split <;> decide)
  rw [VG.Proof.MlDsa.Round.q_eq] at ha
  have hP : (F * BitVec.ofNat 64 (2 * g)).toNat = F.toNat * (2 * g) := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hg2] : 2 * g < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul hF44 hg2) (by decide))
  have hpf : F.toNat * (2 * g) ≤ 44 * 523776 := Nat.mul_le_mul hF44 hg2
  generalize F * BitVec.ofNat 64 (2 * g) = P at hP ⊢
  have z : (w - 1) >>> 63 = if w.toNat = 0 then 1 else 0 := by split <;> bv_omega
  have s : (P - a) >>> 63 = if P.toNat < a.toNat then 1 else 0 := by split <;> bv_omega
  rw [z, s, ← hP]
  by_cases hw0 : w.toNat = 0 <;> by_cases hs : P.toNat < a.toNat <;>
    simp only [hw0, hs, ite_true, ite_false, decide_true, decide_false, ne_eq, not_true_eq_false,
      not_false_eq_true, Bool.false_eq_true]
  · exact fixk2_mod m64 m1 (by omega_using [hF]) (Or.inl (by bv_omega_using [hF, hF44, m1, m64]))
  · exact fixk2_mod m64 m1 (by omega_using [hF]) (Or.inl (by bv_omega_using [hF, hF44, m1, m64]))
  · exact fixk2_mod m64 m1 (by omega_using [hF]) (Or.inl (by bv_omega_using [hF, hF44, m1, m64]))
  · exact fixk2_mod m64 m1 (by omega_using [hF]) (by bv_omega_using [hF, hF44, m1, m64])

/-! ## The loop body -/

/-- What an iteration does, for the value stored. -/
def Step (s : State) (x y w c : BitVec 64) (v : BitVec 32) (s' : State) : Prop :=
  s'.gpr .a0 = x + 4 ∧ s'.gpr .a1 = y + 4 ∧ s'.gpr .a3 = w + 4 ∧ s'.gpr .t3 = c - 1 ∧
    (∀ r ∈ [Reg.a2, .a7, .t1, .t2], s'.gpr r = s.gpr r) ∧
    s'.mem = s.mem.writeW w v ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .ra = s.gpr .ra ∧
    ∀ r ∈ preserved, s'.gpr r = s.gpr r

section
variable {g : Nat} {s : State} {x y w c : BitVec 64} (h3 : s.gpr .a0 = x) (h4 : s.gpr .a1 = y)
  (h6 : s.gpr .a3 = w) (h7 : s.gpr .t3 = c) (h5 : s.gpr .a2 = BitVec.ofNat 64 (2 * g))
  (h10 : s.gpr .a7 = BitVec.ofNat 64 (dMul g)) (h11 : s.gpr .t1 = BitVec.ofNat 64 (dAdd g))
  (h12 : s.gpr .t2 = BitVec.ofNat 64 (dMod g))
  (ix : InRegions (s.rd ++ s.wr) x 4) (iy : InRegions (s.rd ++ s.wr) y 4) (ow : InRegions s.wr w 4)
  (ax : x.toNat % 4 = 0) (ay : y.toNat % 4 = 0) (aw : w.toNat % 4 = 0)
include h3 h4 h6 h7 h5 h10 h11 h12 ix iy ow ax ay aw

theorem body_ok :
    WP isa (.block (uhBody g)) s
      (Step s x y w c ((uhv g ((s.mem.readW y 32).setWidth 64) ((s.mem.readW x 32).setWidth 64)).setWidth 32)) := by
  have hS := dShift_lt g
  crun [uhBody, hbRaw, fixup, Step, uhv, hbr, fixk, h3, h4, h5, h6, h7, h10, h11, h12, ix, iy, ow, ax, ay, aw, hS,
    preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev Hp : Addr := s₀.gpr .a0
abbrev Rp : Addr := s₀.gpr .a1
abbrev G : BitVec 32 := (s₀.gpr .a2).setWidth 32
abbrev O : Addr := s₀.gpr .a3

/-- The values stored. -/
def outs (g : Nat) : Vector Nat n :=
  Vector.zipWith (fun hj rj => (useHint g hj rj).toNat) ((hintAt s₀.mem (Hp s₀) 1).headD (Vector.replicate n false))
    (polyAt s₀.mem (Rp s₀))

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [pR (Hp s₀), pR (Rp s₀)]
  wr : s₀.wr = [pR (O s₀)]
  dh : (pR (Hp s₀)).Disjoint (pR (O s₀))
  dr : (pR (Rp s₀)).Disjoint (pR (O s₀))
  fitH : (Hp s₀).toNat + 1024 ≤ 2 ^ 64
  fitR : (Rp s₀).toNat + 1024 ≤ 2 ^ 64
  fitO : (O s₀).toNat + 1024 ≤ 2 ^ 64
  g : (G s₀).toNat ∈ gamma2s
  red : Reduced s₀.mem (Rp s₀)
  alH : (Hp s₀).toNat % 4 = 0
  alR : (Rp s₀).toNat % 4 = 0
  alO : (O s₀).toNat % 4 = 0

/-- After `i` iterations. -/
structure Inv (g : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .a0 = Hp s₀ + BitVec.ofNat 64 (4 * i)
  r4 : s.gpr .a1 = Rp s₀ + BitVec.ofNat 64 (4 * i)
  r6 : s.gpr .a3 = O s₀ + BitVec.ofNat 64 (4 * i)
  r7 : s.gpr .t3 = BitVec.ofNat 64 (256 - i)
  r5 : s.gpr .a2 = BitVec.ofNat 64 (2 * g)
  r10 : s.gpr .a7 = BitVec.ofNat 64 (dMul g)
  r11 : s.gpr .t1 = BitVec.ofNat 64 (dAdd g)
  r12 : s.gpr .t2 = BitVec.ofNat 64 (dMod g)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.gpr .ra = s₀.gpr .ra
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [pR (O s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, j < i → coeffAt s.mem (O s₀) j = BitVec.ofNat 32 (outs s₀ g)[j]!

theorem out_lt {g : Nat} (hg : g ∈ gamma2s) (s₀ : State) {i : Nat} (hi : i < 256) : (outs s₀ g)[i]! < 64 := by
  rw [outs, zipWith_get _ _ _ hi, useHint_eq hg, Int.toNat_natCast]
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by rcases mem_gamma2s hg with rfl | rfl <;> decide))
    (by rcases mem_gamma2s hg with rfl | rfl <;> decide)

theorem out_val {g : Nat} (hg : g ∈ gamma2s) {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) :
    (uhv g ((coeffAt s₀.mem (Rp s₀) i).setWidth 64) ((coeffAt s₀.mem (Hp s₀) i).setWidth 64)).setWidth 32 =
      BitVec.ofNat 32 (outs s₀ g)[i]! := by
  obtain ⟨ea, ha⟩ := HighLow.load_toNat hp.red hi
  have hw : ((coeffAt s₀.mem (Hp s₀) i).setWidth 64).toNat = (coeffAt s₀.mem (Hp s₀) i).toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (coeffAt s₀.mem (Hp s₀) i).isLt; omega_using [])
  have e := uh_val hg ha (by rw [hw]; exact (coeffAt s₀.mem (Hp s₀) i).isLt)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, e, BitVec.toNat_ofNat, outs, zipWith_get _ _ _ hi, useHint_eq hg,
    Int.toNat_natCast, hintAt_get _ _ hi, ea, hw, uhNat]
  have hb : decide ((coeffAt s₀.mem (Hp s₀) i).toNat ≠ 0) = decide (coeffAt s₀.mem (Hp s₀) i ≠ 0) :=
    decide_eq_decide.mpr ⟨fun h e => h (by rw [e]; rfl),
      fun h e => h (BitVec.eq_of_toNat_eq (by simpa using e))⟩
  rw [hb]

theorem inv_step {g : Nat} (hg : g ∈ gamma2s) {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {s : State}
    (h : Inv g s₀ i s) :
    WP isa (.block (uhBody g)) s fun s' => Inv g s₀ (i + 1) s' ∧ (s'.gpr .t3 != 0) = decide (i + 1 ≠ 256) := by
  have cH := coeff_contains (Hp s₀) (i := i) hi
  have cR := coeff_contains (Rp s₀) (i := i) hi
  have cO := coeff_contains (O s₀) (i := i) hi
  have hd : ∀ {p : Addr}, (pR p).Disjoint (pR (O s₀)) → ∀ r ∈ [pR (O s₀)], (pR p).Disjoint r :=
    fun hd r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd
  have eR : s.mem.readW (Rp s₀ + BitVec.ofNat 64 (4 * i)) 32 = coeffAt s₀.mem (Rp s₀) i :=
    coeffAt_frame h.frame (hd hp.dr) hi
  have eH : s.mem.readW (Hp s₀ + BitVec.ofNat 64 (4 * i)) 32 = coeffAt s₀.mem (Hp s₀) i :=
    coeffAt_frame h.frame (hd hp.dh) hi
  have hv := out_val hg hp hi
  rw [← eR, ← eH] at hv
  refine WP.mono (body_ok h.r3 h.r4 h.r6 h.r7 h.r5 h.r10 h.r11 h.r12 ?_ ?_ ?_ (align4_add hp.alH i)
      (align4_add hp.alR i) (align4_add hp.alO i))
    fun s' ⟨r3, r4, r6, r7, kp, m, rd, wr, sp, lr, pres⟩ => ⟨⟨?_, ?_, ?_, ?_,
      (kp .a2 (by simp)).trans h.r5, (kp .a7 (by simp)).trans h.r10, (kp .t1 (by simp)).trans h.r11,
      (kp .t2 (by simp)).trans h.r12, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, lr.trans h.lr,
      fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cH⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cR⟩
  · rw [h.wr, hp.wr]; exact ⟨_, by simp, cO⟩
  · rw [r3]; exact ptr_succ _ 4 i
  · rw [r4]; exact ptr_succ _ 4 i
  · rw [r6]; exact ptr_succ _ 4 i
  · rw [r7]; exact count_sub hi
  · rw [m]; exact h.frame.writeW (List.mem_singleton_self _) _ cO
  · intro j hj hji
    rw [m, hv, show O s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (O s₀) i from rfl, coeffAt_writeW _ _ hj hi]
    by_cases e : i = j
    · subst e; rw [ite_eq_left rfl]
    · rw [ite_eq_right e]; exact h.coeff j hj (by omega_using [hji, e])
  · rw [r7, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]; exact count_nz hi (by decide)

/-! ## The function -/

/-- What the function leaves. -/
def Post (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.gpr .ra = s₀.gpr .ra ∧
    ∀ j < 256, coeffAt s.mem (O s₀) j = BitVec.ofNat 32 (outs s₀ (G s₀).toNat)[j]!

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa useHint s₀ (Post s₀) := by
  refine sel_ok' (rg := .a2) (by decide) hp.g fun g hg hG s hgpr hm hrd hwr hsp => ?_
  have e : (if g = g32 then uhLoop g32 else uhLoop g88) = uhLoop g := by
    rcases mem_gamma2s hg with rfl | rfl <;> rfl
  rw [e]
  have b2 : 2 * g < 2 ^ 31 - 2048 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  unfold uhLoop
  rw [List.append_assoc]
  refine WP.seq (consts_ok ?_)
  simp only [loadImm, List.cons_append, List.nil_append]
  refine Steps.WP.cons exec_lui (Steps.WP.cons (exec_addi (loadImm_imm _))
    (Steps.WP.cons (exec_li (by decide)) (WP.block_nil ?_)))
  refine WP.mono (wp_loop_nz (Inv g s₀) (N := 256) (by decide) (fun i hi s h => inv_step hg hp hi h)
    (fun _ h => h) ?_) fun s' h' => ⟨h'.pres, h'.sp, h'.lr, fun j hj => hG ▸ h'.coeff j hj hj⟩
  have e5 := loadImm_val b2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrd, hwr, hsp, ?_, fun r hr => ?_,
    by rw [show _ = s.mem from rfl, hm]; exact Frame.refl _ _, fun j _ h => absurd h (by omega_using [])⟩
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write]
  · simp only [State.write, ite_true, ite_false, reduceCtorEq]; exact e5
  · simp [State.write, kgpr]
  · simp [State.write, kgpr]
  · simp [State.write, kgpr]
  · simp [State.write, kgpr, hgpr, selGpr]
  · have : r ≠ .t0 ∧ r ≠ .a2 ∧ r ≠ .a4 ∧ r ≠ .t3 ∧ r ≠ .a7 ∧ r ≠ .t1 ∧ r ≠ .t2 := by revert r hr; decide
    simp [State.write, kgpr, hgpr, selGpr, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1,
      this.2.2.2.2.2.1, this.2.2.2.2.2.2]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.useHintContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.useHintContract, Proof.MlDsa.useHintSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 95232 | .a3 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]
  wr := [⟨0x3000, 1024⟩]

theorem verified : Verified RISCV64.target useHint (Proof.MlDsa.useHintContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, sel_ct (rg := .a2) (by decide) [.a0, .a1, .a3] (by decide) (fun s₁ s₂ h => ?_)
    (by taint_decide) (by taint_decide) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := correct hp
    refine ⟨t, s', he, ⟨h.1, h.2.1, h.2.2.1⟩, ?_⟩
    sig_post [Proof.MlDsa.useHintContract, Proof.MlDsa.useHintSig, RISCV64.abi, RISCV64.argRegs]
    refine natPolyIs_of_toNat fun j hj => ?_
    rw [h.2.2.2 j hj, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (out_lt hp.g s hj) (by decide))
  · sig_pub [Proof.MlDsa.useHintContract, Proof.MlDsa.useHintSig, RISCV64.abi, RISCV64.argRegs] at h
    refine ⟨fun r hr => ?_, h.1, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.2.1
      · exact h.2.2.1
      · exact h.2.2.2.2
    · exact h.2.2.2.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.useHintContract, Proof.MlDsa.useHintSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Round.UseHint

end

end

/-! ### `MlDsa.RISCV64.Sign.Inst`, which only this module used -/

section

/-!
# ML-DSA signing on RISC-V, with this library's primitives

The RISC-V implementations of the primitives (`prims`) are verified with at
most 1168 bytes of stack (the samplers' Keccak frames; the others use none),
and their frames use no more; with the 1168 bytes they are verified with, the
two samplers whose results signing branches on return
what depends only on their public data, and succeed only if their algorithm
finishes within `maxBounds` (`rn_ret`, `sb_ret`, from what their own proofs
say they return). So signing with them is verified with 1168
(`sign44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Proof.MlDsa.Sign (ifn rejNTTPoly_mono sampleInBall_mono)
open VG.Proof.MlDsa.Sample (rnFold ballFold rejNTT_some sampleInBall_some)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The samplers' results -/

theorem rn_ret {s s' : State} {tr : List Leak} (h : (rejNTTContract RISCV64.abi 1168).pre s)
    (e : Exec isa Impl.MlDsa.RISCV64.Sample.rejNTT s tr s') :
    s'.gpr .a0 = if (rnFold [] (G (bytesAt s.mem (s.gpr .a0) 34) 1008)).length = 256 then 1 else 0 := by
  obtain ⟨_, _, e', h0, _⟩ := Sample.RejNtt.correct (Sample.RejNtt.spOk_of h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact h0

theorem rn_pub (s₁ s₂ : State) (h : (rejNTTContract RISCV64.abi 1168).pub s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .a0) 34 = bytesAt s₂.mem (s₂.gpr .a0) 34 := by
  sig_pub [rejNTTContract, rejNTTSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨_, hb, _⟩ := h
  exact Proof.MlDsa.Sign.leakBytes_inj hb

theorem sb_ret {s s' : State} {tr : List Leak} (h : (sampleInBallContract RISCV64.abi 1168).pre s)
    (e : Exec isa Impl.MlDsa.RISCV64.Sample.sampleInBall s tr s') :
    s'.gpr .a0 = if (ballFold ((s.gpr .a2).setWidth 32).toNat
      (H (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) 272)).2 = 256 then 1 else 0 := by
  obtain ⟨_, _, e', h0, _⟩ := Sample.Ball.correct (Sample.Ball.pre_of h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact h0

theorem sb_pub (s₁ s₂ : State) (h : (sampleInBallContract RISCV64.abi 1168).pub s₁ s₂) :
    (s₁.gpr .a2).setWidth 32 = (s₂.gpr .a2).setWidth 32 ∧
      bytesAt s₁.mem (s₁.gpr .a0) (s₁.gpr .a1).toNat = bytesAt s₂.mem (s₂.gpr .a0) (s₂.gpr .a1).toNat := by
  sig_pub [sampleInBallContract, sampleInBallSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨_, hb, _, _, h5, _⟩ := h
  exact ⟨h5, Proof.MlDsa.Sign.leakBytes_inj hb⟩

theorem zero_ne_one32 : (BitVec.setWidth 32 (0 : BitVec 64)) ≠ 1 := by decide

/-- The primitives satisfy what the proofs of signing need of them. -/
theorem prims_ok : SPrimsOk prims 1168 where
  ntt := ⟨⟨0, by decide, Arith.Ntt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨0, by decide, Arith.NttInv.verified⟩, by decide +kernel⟩
  mul := ⟨⟨0, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨0, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  add := ⟨⟨0, by decide, Arith.AddSub.add_verified⟩, by decide +kernel⟩
  sub := ⟨⟨0, by decide, Arith.AddSub.sub_verified⟩, by decide +kernel⟩
  rejNTT := ⟨⟨1168, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  expandMask := ⟨⟨1168, by decide, Sample.expandMask_verified⟩, by decide +kernel⟩
  ball := ⟨⟨1168, by decide, Sample.sampleInBall_verified⟩, by decide +kernel⟩
  highBits := ⟨⟨0, by decide, Round.HighLow.high_verified⟩, by decide +kernel⟩
  lowBits := ⟨⟨0, by decide, Round.HighLow.low_verified⟩, by decide +kernel⟩
  normLt := ⟨⟨0, by decide, Round.NormLt.verified⟩, by decide +kernel⟩
  makeHint := ⟨⟨0, by decide, Round.MakeHint.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitPack := ⟨⟨0, by decide, Pack.bitPack_verified⟩, by decide +kernel⟩
  bitUnpack := ⟨⟨0, by decide, Pack.bitUnpack_verified⟩, by decide +kernel⟩
  hintBitPack := ⟨⟨0, by decide, Pack.hintBitPack_verified⟩, by decide +kernel⟩
  rejX := ⟨1168, by decide, Sample.rejNTT_verified,
    fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
      ⟨Sample.rejNTT_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
        show _ = _ by rw [rn_ret h₁ e₁, rn_ret h₂ e₂, rn_pub s₁ s₂ hp]⟩,
    fun s t s' h e h1 => by
      rw [rn_ret h e] at h1
      by_cases hf : (rnFold [] (G (bytesAt s.mem (s.gpr .a0) 34) 1008)).length = 256
      · rw [rejNTTPoly_mono (show 1008 ≤ maxBounds.rejNTT by decide) (rejNTT_some hf)]; rfl
      · rw [ifn hf] at h1; exact absurd h1 zero_ne_one32⟩
  ballX := ⟨1168, by decide, Sample.sampleInBall_verified,
    fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
      ⟨Sample.sampleInBall_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
        show _ = _ by rw [sb_ret h₁ e₁, sb_ret h₂ e₂, (sb_pub s₁ s₂ hp).1, (sb_pub s₁ s₂ hp).2]⟩,
    fun s t s' h e h1 => by
      rw [sb_ret h e] at h1
      by_cases hf : (ballFold ((s.gpr .a2).setWidth 32).toNat
        (H (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) 272)).2 = 256
      · rw [sampleInBall_mono (show 272 ≤ maxBounds.ball by decide) (sampleInBall_some _ (by decide) hf)]; rfl
      · rw [ifn hf] at h1; exact absurd h1 zero_ne_one32⟩

theorem withCache44_sat : (Proof.MlDsa.signWithCacheContract mlDsa44 RISCV64.abi 1168).pre (signSat mlDsa44) := by
  sig_pre [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, signSig, RISCV64.abi,
    RISCV64.argRegs, signSat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache44_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.withCache44
      (Proof.MlDsa.signWithCacheContract mlDsa44 RISCV64.abi 1168) :=
  sign_verified prims_ok (by decide) _ (.inl rfl) withCache44_sat

theorem withCache65_sat : (Proof.MlDsa.signWithCacheContract mlDsa65 RISCV64.abi 1168).pre (signSat mlDsa65) := by
  sig_pre [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, signSig, RISCV64.abi,
    RISCV64.argRegs, signSat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache65_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.withCache65
      (Proof.MlDsa.signWithCacheContract mlDsa65 RISCV64.abi 1168) :=
  sign_verified prims_ok (by decide) _ (.inr (.inl rfl)) withCache65_sat

theorem withCache87_sat : (Proof.MlDsa.signWithCacheContract mlDsa87 RISCV64.abi 1168).pre (signSat mlDsa87) := by
  sig_pre [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, signSig, RISCV64.abi,
    RISCV64.argRegs, signSat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache87_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.withCache87
      (Proof.MlDsa.signWithCacheContract mlDsa87 RISCV64.abi 1168) :=
  sign_verified prims_ok (by decide) _ (.inr (.inr rfl)) withCache87_sat

end VG.Proof.MlDsa.RISCV64.Sign

end

end

/-! ### `MlDsa.RISCV64.Verify.Inst`, which only this module used -/

section

/-!
# ML-DSA verification on RISC-V, with this library's primitives

The RISC-V implementations of the primitives (`prims`) are verified with at
most 1168 bytes of stack (the samplers', for the sponge's frames; the others
use none), and their frames use no more (`prims_ok`), so verification with
them is verified with 1168 (`verify44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64
open VG.Impl.MlDsa.RISCV64.Verify

theorem prims_ok : VPrimsOk prims 1168 where
  ntt := ⟨⟨0, by decide, Arith.Ntt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨0, by decide, Arith.NttInv.verified⟩, by decide +kernel⟩
  mul := ⟨⟨0, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨0, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  sub := ⟨⟨0, by decide, Arith.AddSub.sub_verified⟩, by decide +kernel⟩
  rejNtt := ⟨⟨1168, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  ball := ⟨⟨1168, by decide, Sample.sampleInBall_verified⟩, by decide +kernel⟩
  useHint := ⟨⟨0, by decide, Round.UseHint.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitUnpack := ⟨⟨0, by decide, Pack.bitUnpack_verified⟩, by decide +kernel⟩
  unpackT1 := ⟨⟨0, by decide, Pack.unpackT1_verified⟩, by decide +kernel⟩
  hintUnpack := ⟨⟨0, by decide, Pack.hintBitUnpack_verified⟩, by decide +kernel⟩
  normLt := ⟨⟨0, by decide, Round.NormLt.verified⟩, by decide +kernel⟩

theorem withCache44_sat : (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa44 RISCV64.abi 1168).pre
    (verifySat Spec.MlDsa.mlDsa44) := by
  sig_pre [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, RISCV64.abi,
    RISCV64.argRegs, verifySat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache44_verified :
    Verified RISCV64.target withCache44 (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa44 RISCV64.abi 1168) :=
  verify_verified prims_ok (by decide) _ (.inl rfl) withCache44_sat

theorem withCache65_sat : (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa65 RISCV64.abi 1168).pre
    (verifySat Spec.MlDsa.mlDsa65) := by
  sig_pre [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, RISCV64.abi,
    RISCV64.argRegs, verifySat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache65_verified :
    Verified RISCV64.target withCache65 (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa65 RISCV64.abi 1168) :=
  verify_verified prims_ok (by decide) _ (.inr (.inl rfl)) withCache65_sat

theorem withCache87_sat : (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa87 RISCV64.abi 1168).pre
    (verifySat Spec.MlDsa.mlDsa87) := by
  sig_pre [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, RISCV64.abi,
    RISCV64.argRegs, verifySat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache87_verified :
    Verified RISCV64.target withCache87 (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa87 RISCV64.abi 1168) :=
  verify_verified prims_ok (by decide) _ (.inr (.inr rfl)) withCache87_sat

end VG.Proof.MlDsa.RISCV64.Verify

end

end


/-!
# ML-DSA on RISC-V: the entries of the kernels, with this library's kernels

`vg_mldsa*_sign` and `vg_mldsa*_verify` call `vg_mldsa*_sign_with_cache` and
`vg_mldsa*_verify_with_cache` (`Sign/Inst.lean`, `Verify/Inst.lean`), verified
with 1168 bytes of stack, in a frame of 16: so they are verified with 1184
(`sign44_verified`, `verify44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.PreparedKey

open VG VG.RISCV64
open VG.Spec.MlDsa

/-- A state that satisfies `signContract`'s precondition. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x8000 | .a2 => 0x9000 | .a3 => 0xA000 | .a4 => 0x10000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x8000, 64⟩, ⟨0x9000, 32⟩]
  wr := [⟨0xA000, p.sigLen⟩, ⟨0x10000, scratchWords p * 8⟩]

theorem sign44_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.sign44 (signContract mlDsa44 RISCV64.abi 1184) :=
  signEntry_verified (.inl rfl) Sign.withCache44_verified (by decide +kernel) _ false
    ⟨signSat mlDsa44, by simp only [signEK, Bool.false_eq_true, ↓reduceIte]; sig_sat_check [signContract, signSig, RISCV64.abi, RISCV64.argRegs, signSat]⟩

theorem sign65_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.sign65 (signContract mlDsa65 RISCV64.abi 1184) :=
  signEntry_verified (.inr (.inl rfl)) Sign.withCache65_verified (by decide +kernel) _ false
    ⟨signSat mlDsa65, by simp only [signEK, Bool.false_eq_true, ↓reduceIte]; sig_sat_check [signContract, signSig, RISCV64.abi, RISCV64.argRegs, signSat]⟩

theorem sign87_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.sign87 (signContract mlDsa87 RISCV64.abi 1184) :=
  signEntry_verified (.inr (.inr rfl)) Sign.withCache87_verified (by decide +kernel) _ false
    ⟨signSat mlDsa87, by simp only [signEK, Bool.false_eq_true, ↓reduceIte]; sig_sat_check [signContract, signSig, RISCV64.abi, RISCV64.argRegs, signSat]⟩

/-- A state that satisfies `verifyContract`'s precondition. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x10000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x2000, 64⟩, ⟨0x3000, p.sigLen⟩]
  wr := [⟨0x10000, scratchWords p * 8⟩]

theorem verify44_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Verify.verify44 (verifyContract mlDsa44 RISCV64.abi 1184) :=
  verifyEntry_verified (.inl rfl) Verify.withCache44_verified (by decide +kernel) _ false
    ⟨verifySat mlDsa44, by
      simp only [verifyEK, Bool.false_eq_true, ↓reduceIte]
      sig_sat_check [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs, verifySat]⟩

theorem verify65_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Verify.verify65 (verifyContract mlDsa65 RISCV64.abi 1184) :=
  verifyEntry_verified (.inr (.inl rfl)) Verify.withCache65_verified (by decide +kernel) _ false
    ⟨verifySat mlDsa65, by
      simp only [verifyEK, Bool.false_eq_true, ↓reduceIte]
      sig_sat_check [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs, verifySat]⟩

theorem verify87_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Verify.verify87 (verifyContract mlDsa87 RISCV64.abi 1184) :=
  verifyEntry_verified (.inr (.inr rfl)) Verify.withCache87_verified (by decide +kernel) _ false
    ⟨verifySat mlDsa87, by
      simp only [verifyEK, Bool.false_eq_true, ↓reduceIte]
      sig_sat_check [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs, verifySat]⟩

/-! ## Preparing keys -/

/-- A state that satisfies the precondition of preparing a key of `kl` bytes
into `ol`, with the buffer (`buf`) or without it. -/
def prepSat (kl ol : Nat) (buf : Bool) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x4000 | .a2 => 0x10000 | .a3 => 0x11000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, kl⟩]
  wr := [⟨0x4000, ol⟩, ⟨0x10000, 1024⟩] ++ if buf then [⟨0x11000, 1072⟩] else []

theorem preparePublic44_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.preparePublic mlDsa44)
      (preparePublicKeyContract mlDsa44 RISCV64.abi 1072) :=
  preparePublic_verified (.inl rfl)
    ⟨prepSat mlDsa44.pkLen (preparedPublicKeyBytes mlDsa44) true, by
      sig_sat_check [publicScratchContract, publicScratchSig, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa44.pkLen (preparedPublicKeyBytes mlDsa44) false, by
      sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

theorem prepareSecret44_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.prepareSecret mlDsa44)
      (prepareSecretKeyContract mlDsa44 RISCV64.abi 1072) :=
  prepareSecret_verified (.inl rfl)
    ⟨prepSat mlDsa44.skLen (preparedSecretKeyBytes mlDsa44) true, by
      sig_sat_check [secretScratchContract, secretScratchSig, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa44.skLen (preparedSecretKeyBytes mlDsa44) false, by
      sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

theorem preparePublic65_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.preparePublic mlDsa65)
      (preparePublicKeyContract mlDsa65 RISCV64.abi 1072) :=
  preparePublic_verified (.inr (.inl rfl))
    ⟨prepSat mlDsa65.pkLen (preparedPublicKeyBytes mlDsa65) true, by
      sig_sat_check [publicScratchContract, publicScratchSig, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa65.pkLen (preparedPublicKeyBytes mlDsa65) false, by
      sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

theorem prepareSecret65_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.prepareSecret mlDsa65)
      (prepareSecretKeyContract mlDsa65 RISCV64.abi 1072) :=
  prepareSecret_verified (.inr (.inl rfl))
    ⟨prepSat mlDsa65.skLen (preparedSecretKeyBytes mlDsa65) true, by
      sig_sat_check [secretScratchContract, secretScratchSig, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa65.skLen (preparedSecretKeyBytes mlDsa65) false, by
      sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

theorem preparePublic87_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.preparePublic mlDsa87)
      (preparePublicKeyContract mlDsa87 RISCV64.abi 1072) :=
  preparePublic_verified (.inr (.inr rfl))
    ⟨prepSat mlDsa87.pkLen (preparedPublicKeyBytes mlDsa87) true, by
      sig_sat_check [publicScratchContract, publicScratchSig, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa87.pkLen (preparedPublicKeyBytes mlDsa87) false, by
      sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

theorem prepareSecret87_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.prepareSecret mlDsa87)
      (prepareSecretKeyContract mlDsa87 RISCV64.abi 1072) :=
  prepareSecret_verified (.inr (.inr rfl))
    ⟨prepSat mlDsa87.skLen (preparedSecretKeyBytes mlDsa87) true, by
      sig_sat_check [secretScratchContract, secretScratchSig, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa87.skLen (preparedSecretKeyBytes mlDsa87) false, by
      sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

/-! ## Signing and verifying with a prepared key -/

/-- A prepared private key, at `0x4000` of some memory: the one `prepareSecret` writes from `prepSat`. -/
theorem secret_mem {p : Params}
    (hv : Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.prepareSecret p)
      (prepareSecretKeyContract p RISCV64.abi 1072))
    (hs : (prepareSecretKeyContract p RISCV64.abi 1072).pre (prepSat p.skLen (preparedSecretKeyBytes p) false)) :
    ∃ m, PreparedSecretKey p m 0x4000 := by
  obtain ⟨_, t, _, _, post⟩ := hv.1 _ hs
  sig_post [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs] at post
  exact ⟨t.mem, post.2⟩

/-- A prepared public key, at `0x4000` of some memory. -/
theorem public_mem {p : Params}
    (hv : Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.preparePublic p)
      (preparePublicKeyContract p RISCV64.abi 1072))
    (hs : (preparePublicKeyContract p RISCV64.abi 1072).pre (prepSat p.pkLen (preparedPublicKeyBytes p) false)) :
    ∃ m, PreparedPublicKey p m 0x4000 := by
  obtain ⟨_, t, _, _, post⟩ := hv.1 _ hs
  sig_post [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs] at post
  exact ⟨t.mem, post.2⟩

/-- A state that satisfies `preparedSignContract`'s precondition, with the prepared key in `m`. -/
def psSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .a0 => 0x4000 | .a1 => 0x10000 | .a2 => 0x10100 | .a3 => 0x11000 | .a4 => 0x20000 | _ => 0
  sp := 0x100000
  mem := m
  rd := [⟨0x4000, preparedSecretKeyBytes p⟩, ⟨0x10000, 64⟩, ⟨0x10100, 32⟩]
  wr := [⟨0x11000, p.sigLen⟩, ⟨0x20000, scratchWords p * 8⟩]

/-- A state that satisfies `preparedVerifyContract`'s precondition, with the prepared key in `m`. -/
def pvSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .a0 => 0x4000 | .a1 => 0x10000 | .a2 => 0x11000 | .a3 => 0x20000 | _ => 0
  sp := 0x100000
  mem := m
  rd := [⟨0x4000, preparedPublicKeyBytes p⟩, ⟨0x10000, 64⟩, ⟨0x11000, p.sigLen⟩]
  wr := [⟨0x20000, scratchWords p * 8⟩]

theorem psSat_pre {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {m : Mem}
    (hk : PreparedSecretKey p m 0x4000) : (signEK p true 1184).pre (psSat p m) := by
  simp only [signEK, ↓reduceIte]
  rcases hp3 with rfl | rfl | rfl
  all_goals
    sig_pre [preparedSignContract, preparedSignSig, RISCV64.abi, RISCV64.argRegs, psSat]
    sig_and_intros
    all_goals first
      | exact hk
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)

theorem pvSat_pre {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {m : Mem}
    (hk : PreparedPublicKey p m 0x4000) : (verifyEK p true 1184).pre (pvSat p m) := by
  simp only [verifyEK, ↓reduceIte]
  rcases hp3 with rfl | rfl | rfl
  all_goals
    sig_pre [preparedVerifyContract, preparedVerifySig, RISCV64.abi, RISCV64.argRegs, pvSat]
    sig_and_intros
    all_goals first
      | exact hk
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)

theorem secret44_mem : ∃ m, PreparedSecretKey mlDsa44 m 0x4000 :=
  secret_mem prepareSecret44_verified (by
    sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem public44_mem : ∃ m, PreparedPublicKey mlDsa44 m 0x4000 :=
  public_mem preparePublic44_verified (by
    sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem signPrepared44_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Sign.sign44E true) (signEK mlDsa44 true 1184) :=
  signEntry_verified (.inl rfl) Sign.withCache44_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := secret44_mem; exact ⟨psSat _ m, psSat_pre (.inl rfl) hm⟩)

theorem verifyPrepared44_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Verify.verify44E true) (verifyEK mlDsa44 true 1184) :=
  verifyEntry_verified (.inl rfl) Verify.withCache44_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := public44_mem; exact ⟨pvSat _ m, pvSat_pre (.inl rfl) hm⟩)

theorem secret65_mem : ∃ m, PreparedSecretKey mlDsa65 m 0x4000 :=
  secret_mem prepareSecret65_verified (by
    sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem public65_mem : ∃ m, PreparedPublicKey mlDsa65 m 0x4000 :=
  public_mem preparePublic65_verified (by
    sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem signPrepared65_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Sign.sign65E true) (signEK mlDsa65 true 1184) :=
  signEntry_verified (.inr (.inl rfl)) Sign.withCache65_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := secret65_mem; exact ⟨psSat _ m, psSat_pre (.inr (.inl rfl)) hm⟩)

theorem verifyPrepared65_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Verify.verify65E true) (verifyEK mlDsa65 true 1184) :=
  verifyEntry_verified (.inr (.inl rfl)) Verify.withCache65_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := public65_mem; exact ⟨pvSat _ m, pvSat_pre (.inr (.inl rfl)) hm⟩)

theorem secret87_mem : ∃ m, PreparedSecretKey mlDsa87 m 0x4000 :=
  secret_mem prepareSecret87_verified (by
    sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem public87_mem : ∃ m, PreparedPublicKey mlDsa87 m 0x4000 :=
  public_mem preparePublic87_verified (by
    sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem signPrepared87_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Sign.sign87E true) (signEK mlDsa87 true 1184) :=
  signEntry_verified (.inr (.inr rfl)) Sign.withCache87_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := secret87_mem; exact ⟨psSat _ m, psSat_pre (.inr (.inr rfl)) hm⟩)

theorem verifyPrepared87_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Verify.verify87E true) (verifyEK mlDsa87 true 1184) :=
  verifyEntry_verified (.inr (.inr rfl)) Verify.withCache87_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := public87_mem; exact ⟨pvSat _ m, pvSat_pre (.inr (.inr rfl)) hm⟩)

end VG.Proof.MlDsa.RISCV64.PreparedKey
