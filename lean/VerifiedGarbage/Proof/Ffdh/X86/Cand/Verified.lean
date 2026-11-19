module

public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Top
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.X86.EntryCT
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
meta import VerifiedGarbage.Impl.Ffdh.X86.Candidate
meta import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86.Cand.Main
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
public import VerifiedGarbage.Impl.Ffdh.X86.Candidate
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Proof.Ffdh.X86.Cand.Base
meta import VerifiedGarbage.Proof.Ffdh.X86.Stages
meta import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Phase
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Sieve
meta import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTBase
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoopTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Ffdh.X86.Stages
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTBase
public import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialLoopTiming
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
public import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Ffdh.X86.Cand.Sieve
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoopTiming
meta import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
meta import VerifiedGarbage.Proof.Framework.X86.SymFrame
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Framework.X86.Inline
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Mont.Words32
meta import VerifiedGarbage.Proof.Mont.X86.Words
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialLoopTiming
meta import VerifiedGarbage.Proof.Framework.X86.AllocFrame
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGen
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Stage
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.StageR
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Export

/-! ### `Ffdh.X86.Cand.CTTop`, which only this module used -/

section

/-! ### `Ffdh.X86.Cand.CTMain`, which only this module used -/

section

/-! ### `Ffdh.X86.Cand.CTTests`, which only this module used -/

section

/-! ### `Ffdh.X86.Cand.CTPhase`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86.Cand.CTDraw`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86.Cand.CTRound`, which only this module used -/

section

/-!
# The FFDH candidate on i686: a round's timing

Runs of `round` for the same prepared modulus leak the same trace
(`round_trace`): its power and multiplications are private CRT's, its
copies and words are checked by the taint analysis, and its one branch and
the count of its squarings come from `s` in `w − 1 = 2^s d`, which the
modulus fixes.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86.Candidate

/-! ## The taint checks -/

theorem copy135_check : ACheck (copy (.slot .wide 13) (.slot .wide 5) (one .wide)) := by
  dsimp only [ACheck]; taint_decide
theorem copy118_check : ACheck (copy (.slot .wide 11) (.slot .wide 8) (one .wide)) := by
  dsimp only [ACheck]; taint_decide
theorem eq63_check : ACheck (equal (.slot .wide 6) (.slot .wide 3) (one .wide)) := by
  dsimp only [ACheck]; taint_decide
theorem eq615_check : ACheck (equal (.slot .wide 6) (.slot .wide 15) (one .wide)) := by
  dsimp only [ACheck]; taint_decide
theorem storeHit_check : ACheck (.block [.store (sc hitOff) .ecx]) := by dsimp only [ACheck]; taint_decide
theorem tallyTwo_check : ACheck (.block [.alu .or .ecx (.mem (sc hitOff)), .store (sc hitOff) .ecx,
    .mov .eax (.mem (sc twoOff)), .alu .sub .eax (.imm 1), .store (sc jOff) .eax]) := by
  dsimp only [ACheck]; taint_decide
theorem tallyJ_check : ACheck (.block [.alu .or .ecx (.mem (sc hitOff)), .store (sc hitOff) .ecx,
    .mov .eax (.mem (sc jOff)), .alu .sub .eax (.imm 1), .store (sc jOff) .eax]) := by
  dsimp only [ACheck]; taint_decide
theorem nilR_check : ACheck (.block []) := by dsimp only [ACheck]; taint_decide
theorem mul666_check : MulCheck .wide 6 6 6 := by dsimp only [MulCheck]; taint_decide
theorem mul664_check : MulCheck .wide 6 6 4 := by dsimp only [MulCheck]; taint_decide

variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-! ## The runs' states -/

/-- A run with the modulus `w` prepared. -/
abbrev RP (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (w : Nat) (x : State) : Prop :=
  Run Ex base bytes len args sp x ∧ Prepped Ex base bytes len args w x

theorem RP.wst {w : Nat} {x : State} (R : RP Ex base bytes len args sp w x) :
    WSt Ex base bytes len args sp .wide [3, 4] 0 x := by
  have hM := R.2.ctx.gt
  refine ⟨w, R.2.ctx, fun j hj => ?_, fun j hj => absurd hj (Nat.not_lt_zero _), R.1.2.1, R.1.2.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · rw [R.2.one]; exact hM
  · rw [R.2.r2]; exact Nat.mod_lt _ (by omega_arith)

/-- A copy into slot 5 to 8 keeps the modulus prepared. -/
theorem copyRP_ok {w : Nat} {x : State} (R : RP Ex base bytes len args sp w x) {j d : Nat} (hj9 : 9 ≤ j)
    (hj : j ≤ 17) (hd5 : 5 ≤ d) (hd : d ≤ 8) :
    WP isa (copy (.slot .wide j) (.slot .wide d) (one .wide)) x (RP Ex base bytes len args sp w) := by
  have h := R.1.1
  have f := h.slot_fit .wide (j := d) (by omega_arith)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  refine WP.mono (copyDown_ok h hj9 hj (by omega_arith)) fun u ⟨O, _, K⟩ => ⟨R.1.keep K (O.mono (Nat.zero_le _) (by omega_arith)), ?_⟩
  exact R.2.keep (R.2.toReady.slot (a := d) hd5 (by omega_arith) K (by decide) (by decide) O) (kept_slot h O) (by decide)
    ⟨by simp; omega_arith, by simp; omega_arith, by simp; omega_arith⟩

/-- A power, with the modulus still prepared. -/
theorem powerRP_ok {w : Nat} {x : State} (R : RP Ex base bytes len args sp w x) :
    WP isa (windowPower .wide) x fun u => RP Ex base bytes len args sp w u ∧ sv u.mem base len .wide 6 < w := by
  have h := R.1.1
  have hM := R.2.ctx.gt
  refine WP.mono (windowPower_ok R.2.ctx R.2.one R.2.r2) fun u ⟨C, F, K, Y⟩ => ?_
  have G := stR_widen F (pwR_in h .wide 0)
  refine ⟨⟨⟨C.inp, R.1.2.1.keep K, (K.1 _ (by decide)).trans R.1.2.2⟩,
    R.2.keep ⟨C, by rw [pwR_sv3 h F h.room, R.2.one], by rw [pwR_sv4 h F h.room, R.2.r2]⟩
      (kept_ops h G h.room) (by decide)⟩, by rw [Y]; exact Nat.mod_lt _ (by omega_arith)⟩

/-- A multiplication into slot 6, with the modulus still prepared. -/
theorem mulRP_ok {w : Nat} {x : State} (R : RP Ex base bytes len args sp w x) {a b : Nat} (ha3 : 3 ≤ a) (ha : a ≤ 8)
    (hb3 : 3 ≤ b) (hb : b ≤ 8) (hbw : sv x.mem base len .wide b < w) :
    WP isa (CrtRt.mul .wide 6 a b) x fun u => RP Ex base bytes len args sp w u ∧ sv u.mem base len .wide 6 < w ∧
      Kept base len [] [] x.mem u.mem := by
  have h := R.1.1
  refine WP.mono (cmul_ok R.2.ctx (o := 6) (by decide) (by decide) ha3 ha hb3 hb hbw) fun u ⟨C, K, F, L, _⟩ => ?_
  have G := stR_widen F (mulR_in h .wide (by decide) 0)
  have kt := kept_ops h G h.room
  refine ⟨⟨⟨C.inp, R.1.2.1.keep K, (K.1 _ (by decide)).trans R.1.2.2⟩,
    R.2.keep ⟨C, by rw [mulR_sv h F h.room (by decide) (by decide) (by decide) (by decide) (by decide), R.2.one],
      by rw [mulR_sv h F h.room (by decide) (by decide) (by decide) (by decide) (by decide), R.2.r2]⟩ kt (by decide)⟩,
    L, kt⟩

theorem RP.regs {w : Nat} {x u : State} (R : RP Ex base bytes len args sp w x) {rs : List Reg} (K : Keeps rs x u)
    (m : u.mem = x.mem) (hrs : ∀ q ∈ rs, q ∈ [.eax, .ebx, .ecx, .edx, .ebp, .esi] := by decide) :
    RP Ex base bytes len args sp w u := by
  have S := Step.regs R.1.1 m K hrs
  exact ⟨run_step R.1 S, R.2.keep (R.2.toReady.regs K (by intro hm; have := hrs _ hm; simp at this)
    (by intro hm; have := hrs _ hm; simp at this) m) (js := []) (ds := []) (by rw [m]; exact Kept.refl _) (by decide)⟩

theorem RP.wst6 {w : Nat} {x : State} (R : RP Ex base bytes len args sp w x) (h6 : sv x.mem base len .wide 6 < w) :
    WSt Ex base bytes len args sp .wide [3, 4, 6] 0 x := by
  obtain ⟨M, C, Hk, He, A, e⟩ := R.wst
  refine ⟨M, C, fun j hj => ?_, He, A, e⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl
  · exact Hk 3 (by simp)
  · exact Hk 4 (by simp)
  · have : M = w := C.mod.symm.trans R.2.ctx.mod
    rw [this]; exact h6

/-- A wide slot after a header word's store. -/
theorem sv_hdr {s : State} (h : In Ex base bytes len args s) {d : Nat} (hd : Hdr d) {m : Mem}
    (O : Outside base d 4 s.mem m) {j : Nat} (hj : j ≤ 27) : sv m base len .wide j = sv s.mem base len .wide j := by
  have bl := h.bytes_lt
  have ej := lo_wide len j
  have nb : numBase = 3336 := rfl
  have f := slot_fit1 h hj
  rw [cb1] at f
  have bw := bc_eq_cwc len .wide
  exact O.val32 (.inr (by rcases hd.1 with e | e <;> omega_arith)) (by omega_arith)

/-- The squarings' state, `j` of them done: the hit mask a mask, and `s − 1 − j` to go. -/
abbrev SQ (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (w sn j : Nat) (x : State) : Prop :=
  RP Ex base bytes len args sp w x ∧ sv x.mem base len .wide 6 < w ∧
    (∃ old, w32 x.mem base hitOff = (cmask old).toNat) ∧ w32 x.mem base jOff = sn - 1 - j

theorem SQ.kept {w sn j : Nat} {x u : State} (Q : SQ Ex base bytes len args sp w sn j x)
    (R : RP Ex base bytes len args sp w u) (h6 : sv u.mem base len .wide 6 < w) (k : Kept base len [] [] x.mem u.mem) :
    SQ Ex base bytes len args sp w sn j u :=
  ⟨R, h6, let ⟨old, e⟩ := Q.2.2.1; ⟨old, by rw [k.word_eq, e]⟩, by rw [k.word_eq, Q.2.2.2]⟩

/-- One squaring's runs. -/
theorem squareStep_trace {w sn j : Nat} (hj : j < sn - 1) :
    RelCT isa (Both (SQ Ex base bytes len args sp w sn j)) squareStep
      (Both fun u => SQ Ex base bytes len args sp w sn (j + 1) u ∧ u.zf = some (decide (j + 1 = sn - 1))) := by
  unfold squareStep
  refine VG.RelCT.seq (mul_both sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    mul666_check (fun _ Q => (Q.1.wst6 Q.2.1).mulIn (by simp))
    fun x Q => WP.mono (mulRP_ok Q.1 (a := 6) (b := 6) (by decide) (by decide) (by decide) (by decide) Q.2.1)
      fun u ⟨R, h6, k⟩ => Q.kept R h6 k) ?_
  refine VG.RelCT.seq (mul_both sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    mul664_check (fun _ Q => (Q.1.wst6 Q.2.1).mulIn (by simp))
    fun x Q => WP.mono (mulRP_ok Q.1 (a := 6) (b := 4) (by decide) (by decide) (by decide) (by decide)
      (by rw [Q.1.2.r2]; exact Nat.mod_lt _ (by have := Q.1.2.ctx.gt; omega_arith)))
      fun u ⟨R, h6, k⟩ => Q.kept R h6 k) ?_
  refine VG.RelCT.seq (aRel (F := fun u => SQ Ex base bytes len args sp w sn j u ∧ ∃ c, u.gpr .ecx = cmask c)
    (fun _ Q => Q.1.1) eq615_check fun x Q =>
      WP.mono (eqW_ok Q.1.1.1 (a := 6) (b := 15) (by decide) (by decide)) fun u ⟨m, e, K⟩ =>
        ⟨Q.kept (Q.1.regs K m) (by rw [m]; exact Q.2.1) (by rw [m]; exact Kept.refl _), _, e⟩) ?_
  refine aRel (fun _ Q => Q.1.1.1) tallyJ_check fun x ⟨Q, c, e⟩ => ?_
  obtain ⟨old, ho⟩ := Q.2.2.1
  refine WP.mono (tally_ok Q.1.2 hdr_j (by decide) Q.2.2.2 (by omega_arith) ho e) fun u ⟨S, P, H, J, Z, k, s6⟩ => ?_
  refine ⟨⟨⟨run_step Q.1.1 S, P⟩, by rw [s6]; exact Q.2.1, ⟨_, H⟩, by rw [J]; omega_arith⟩, by rw [Z]; congr 1; exact decide_eq_decide.mpr ⟨fun _ => by omega_arith, fun _ => by omega_arith⟩⟩

/-- A round's runs for the same prepared modulus. -/
theorem round_trace {w : Nat} (hw3 : 3 ≤ w) (hodd : w % 2 = 1) :
    RelCT isa (Both (RP Ex base bytes len args sp w)) round fun _ _ => True := by
  have s1 := splitTwos_pos hw3 hodd
  generalize hsn : (Spec.Rsa.splitTwos (w - 1)).1 = sn at s1
  unfold round
  refine VG.RelCT.seq (aRel (fun _ R => R.1) copy135_check fun x R =>
    copyRP_ok R (j := 13) (d := 5) (by decide) (by decide) (by decide) (by decide)) ?_
  refine VG.RelCT.seq (aRel (fun _ R => R.1) copy118_check fun x R =>
    copyRP_ok R (j := 11) (d := 8) (by decide) (by decide) (by decide) (by decide)) ?_
  refine VG.RelCT.seq (relCT_both ((windowPower_relCT (winChecks .wide)).mono (fun _ _ h => ⟨h.1.wst, h.2.wst⟩)
    fun _ _ _ => trivial) fun x R => powerRP_ok R) ?_
  refine VG.RelCT.seq (aRel (F := fun u => (RP Ex base bytes len args sp w u ∧ sv u.mem base len .wide 6 < w) ∧
      ∃ c, u.gpr .ecx = cmask c) (fun _ R => R.1.1) eq63_check fun x R =>
    WP.mono (eqW_ok R.1.1.1 (a := 6) (b := 3) (by decide) (by decide)) fun u ⟨m, e, K⟩ =>
      ⟨⟨R.1.regs K m, by rw [m]; exact R.2⟩, _, e⟩) ?_
  refine VG.RelCT.seq (aRel (F := fun u => RP Ex base bytes len args sp w u ∧ sv u.mem base len .wide 6 < w ∧
      ∃ old, w32 u.mem base hitOff = (cmask old).toNat) (fun _ R => R.1.1.1) storeHit_check fun x ⟨R, c, e⟩ =>
    hdr_store R.1.1.1 hdr_hit fun u S W k O _ _ _ => WP.block_nil ⟨⟨run_step R.1.1 S,
      R.1.2.keep (R.1.2.toReady.hdr hdr_hit S.keeps (by decide) (by decide) O) k (by decide)⟩,
      by rw [sv_hdr R.1.1.1 hdr_hit O (by decide)]; exact R.2, c, by rw [W, e]⟩) ?_
  refine VG.RelCT.seq (aRel (F := fun u => (RP Ex base bytes len args sp w u ∧ sv u.mem base len .wide 6 < w ∧
      ∃ old, w32 u.mem base hitOff = (cmask old).toNat) ∧ ∃ c, u.gpr .ecx = cmask c) (fun _ R => R.1.1)
    eq615_check fun x R =>
    WP.mono (eqW_ok R.1.1.1 (a := 6) (b := 15) (by decide) (by decide)) fun u ⟨m, e, K⟩ =>
      ⟨⟨R.1.regs K m, by rw [m]; exact R.2.1, by rw [m]; exact R.2.2⟩, _, e⟩) ?_
  refine VG.RelCT.seq (aRel (F := fun u => SQ Ex base bytes len args sp w sn 0 u ∧ u.zf = some (decide (sn = 1)))
    (fun _ R => R.1.1.1) tallyTwo_check fun x ⟨⟨R, h6, old, ho⟩, c, e⟩ => ?_) ?_
  · refine WP.mono (tally_ok R.2 hdr_two (by decide) (by rw [R.2.two, hsn]) s1 ho e)
      fun u ⟨S, P, H, J, Z, k, s6⟩ => ⟨⟨⟨run_step R.1 S, P⟩, by rw [s6]; exact h6, ⟨_, H⟩, by rw [J, Nat.sub_zero]⟩, Z⟩
  refine ite_fixed (b := decide (sn = 1)) (fun _ h => h.2)
    (fun _ => (aRel (F := fun _ => True) (fun _ h => h.1.1.1) nilR_check fun _ _ => WP.block_nil trivial).mono
      (fun _ _ h => h) fun _ _ _ => trivial) fun e => ?_
  have hN : 0 < sn - 1 := by simp at e; omega_arith
  exact (relCT_countLoop hN (SQ Ex base bytes len args sp w sn) fun j hj => squareStep_trace hj).mono
    (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ _ => trivial

end VG.Proof.Ffdh.X86.Cand

end

end

/-!
# The FFDH candidate on i686: a draw's timing

`drawLoad` reads the witness's octets through pointers made from the cursor
and the count of octets, which the runs fix (`drawLoad_trace`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86.Candidate
open VG.Impl.Bignum.X86.PublicRt (argAt)

theorem drawSetup_check : ACheck (.seq (zero (.slot .wide 13) (one .wide)) (.block drawSetup)) := by
  dsimp only [ACheck]; taint_decide
theorem drawRev_check : PCheck [.ecx, .esi, .ebx] (.seq reverseBytes (.block [.mov .eax (.mem (sc octOff)),
    .alu .add .eax (.mem (sc curOff)), .store (sc curOff) .eax])) := by
  dsimp only [PCheck]; taint_decide
theorem cutHead_check : ACheck (.block [.mov .ecx (.mem (sc kOff)), .alu .sub .ecx (.imm 1), .mov .edx (.reg .ecx),
    .shift .shr .edx 5, .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx), .alu .and .ecx (.imm 31),
    .alu .add .ecx (.imm 1)]) := by
  dsimp only [ACheck]; taint_decide

/-- `cut`'s mask and store, which read its word's index and bits from `edx` and `ecx`. -/
abbrev cutRest (j : Nat) (top : Bool) : Prog isa :=
  .seq Impl.Ffdh.X86.Candidate.maskLoop <| .block (ptrTo (.slot .wide j) .ebx .ecx ++ [.alu .add .ebx (.reg .edx), .mov .ecx (.mem (at_ .ebx 0)),
    .alu .and .ecx (.reg .eax)] ++
    (if top then [.mov .ebp (.reg .eax), .shift .shr .ebp 1, .alu .xor .eax (.reg .ebp), .alu .or .ecx (.reg .eax)]
      else []) ++ [.store (at_ .ebx 0) .ecx])

theorem drawHead_check : ACheck (.block [.mov .eax (.mem (argAt 0 12)), .alu .sub .eax (.mem (sc curOff)),
    .alu .cmp .eax (.mem (sc octOff))]) := by dsimp only [ACheck]; taint_decide
theorem setSt3_check : ACheck (.block [.mov .eax (.imm 3), .store (sc stOff) .eax]) := by
  dsimp only [ACheck]; taint_decide
theorem setSt2_check : ACheck (.block [.mov .eax (.imm 2), .store (sc stOff) .eax]) := by
  dsimp only [ACheck]; taint_decide
theorem rangeMask13_check : ACheck (Impl.Ffdh.X86.rangeMask 13) := by dsimp only [ACheck]; taint_decide
theorem testMask_check : ACheck Impl.Ffdh.X86.testMask := by dsimp only [ACheck]; taint_decide
theorem hitTest_check : ACheck (.block [.mov .ecx (.mem (sc hitOff)), .alu .test .ecx (.reg .ecx)]) := by
  dsimp only [ACheck]; taint_decide
theorem passed_check : ACheck (.block passed) := by dsimp only [ACheck]; taint_decide
theorem drawFin_check : ACheck (.block [.mov .eax (.mem (sc stOff)), .alu .cmp .eax (.imm 0)]) := by
  dsimp only [ACheck]; taint_decide

theorem cutRest13_check : PCheck [.ecx, .edx] (cutRest 13 false) := by dsimp only [PCheck]; taint_decide
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- Runs with the same cursor `c` and count `o` load the witness alike. -/
theorem drawLoad_trace {c o : Nat} (ho1 : 1 ≤ o) {P : State → Prop}
    (hP : ∀ x, P x → Run Ex base bytes len args sp x ∧ w32 x.mem base curOff = c ∧ w32 x.mem base octOff = o) :
    RelCT isa (Both P) drawLoad fun _ _ => True := by
  unfold drawLoad
  refine RelCT.assoc (RelCT.seq (aRel (F := fun v => Run Ex base bytes len args sp v ∧
      v.gpr .ecx = BitVec.ofNat 32 o ∧ v.gpr .esi = (args 2 + BitVec.ofNat 32 c) + BitVec.ofNat 32 (o - 1) ∧
      PtrAt v base .ebx (lo len (.slot .wide 13))) (fun x h => (hP x h).1) drawSetup_check fun x h => ?_)
    (pinned_end (rs := [.ecx, .esi, .ebx]) (fun _ h => h.1) (fun x y hx hy r hr => ?_) drawRev_check))
  · obtain ⟨R, hc, ho⟩ := hP x h
    exact WP.mono (drawSetup_ok R.1 hc ho ho1) fun v ⟨hv, _, _, K, ecx, esi, pv⟩ =>
      ⟨⟨hv, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩, ecx, esi, pv⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hx.2.1, hy.2.1]
    · rw [hx.2.2.1, hy.2.2.1]
    · exact BitVec.eq_of_toNat_eq (hx.2.2.2.trans hy.2.2.2.symm)

/-- Runs with the same `k` cut alike. -/
theorem cut_trace {j : Nat} {top : Bool} (hc : PCheck [.ecx, .edx] (cutRest j top)) {k : Nat} (hk1 : 1 ≤ k)
    {P : State → Prop} (hP : ∀ x, P x → Run Ex base bytes len args sp x ∧ w32 x.mem base kOff = k) :
    RelCT isa (Both P) (cut (.slot .wide j) top) fun _ _ => True := by
  unfold cut
  refine RelCT.seq (aRel (F := fun v => Run Ex base bytes len args sp v ∧
      v.gpr .ecx = BitVec.ofNat 32 ((k - 1) % 32 + 1) ∧ v.gpr .edx = BitVec.ofNat 32 (4 * ((k - 1) / 32)))
    (fun x h => (hP x h).1) cutHead_check fun x h => ?_)
    (pinned_end (rs := [.ecx, .edx]) (fun _ h => h.1) (fun x y hx hy r hr => ?_) hc)
  · obtain ⟨R, hk⟩ := hP x h
    have := cutHead_ok (is := []) (Q := fun v => Run Ex base bytes len args sp v ∧
        v.gpr .ecx = BitVec.ofNat 32 ((k - 1) % 32 + 1) ∧ v.gpr .edx = BitVec.ofNat 32 (4 * ((k - 1) / 32)))
      R.1 hk hk1 fun t m K ec ed =>
      WP.block_nil ⟨⟨R.1.regs K m, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩, ec, ed⟩
    rwa [List.append_nil] at this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hx.2.1, hy.2.1]
    · rw [hx.2.2, hy.2.2]

/-- A draw's state, from a run's start `s₀`. -/
abbrev DrawRun (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (w : Nat) (T : List Byte) (n c : Nat) (x : State) : Prop :=
  ∃ s₀, Run Ex base bytes len args sp s₀ ∧ DrawAt Ex base bytes len args s₀ w T n c x

/-- A drawn witness's state, from a run's start `s₀`. -/
abbrev PickRun (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (w : Nat) (T : List Byte) (n c : Nat) (x : State) : Prop :=
  ∃ s₀, Run Ex base bytes len args sp s₀ ∧ Picked Ex base bytes len args s₀ w T n c x

theorem DrawRun.run {w n c : Nat} {T : List Byte} {x : State} (D : DrawRun Ex base bytes len args sp w T n c x) :
    Run Ex base bytes len args sp x := by
  obtain ⟨_, R, A⟩ := D; exact run_step R A.step

theorem PickRun.run {w n c : Nat} {T : List Byte} {x : State} (D : PickRun Ex base bytes len args sp w T n c x) :
    Run Ex base bytes len args sp x := by
  obtain ⟨_, R, A⟩ := D; exact run_step R A.step

/-- A drawn witness's round, for runs with the same witness. -/
theorem drawRound_trace {w n c : Nat} {T : List Byte} (G : TapeGeo Ex args base bytes sp T.length) (hw3 : 3 ≤ w)
    (hodd : w % 2 = 1) (hn : 1 ≤ n) :
    RelCT isa (Both (PickRun Ex base bytes len args sp w T n c))
      (.seq round <| .seq (.block [.mov .ecx (.mem (sc hitOff)), .alu .test .ecx (.reg .ecx)]) <|
        .ite .e (.block [.mov .eax (.imm 2), .store (sc stOff) .eax]) (.block passed))
      (Both (Run Ex base bytes len args sp)) := by
  have Gs : ∀ {s₀ : State}, Run Ex base bytes len args sp s₀ → TapeGeo Ex args base bytes (s₀.gpr .esp) T.length :=
    fun R => by rw [R.2.2]; exact G
  let Φ : State → Prop := fun v => PickRun Ex base bytes len args sp w T n c v ∧
    isa.eval .e v = some (!Spec.Ffdh.mrRound w (drawA w T c))
  refine RelCT.seq (relCT_both (F := fun v => Run Ex base bytes len args sp v ∧
      WP isa (.block [.mov .ecx (.mem (sc hitOff)), .alu .test .ecx (.reg .ecx)]) v Φ)
    ((round_trace (Ex := Ex) (base := base) (bytes := bytes) (len := len) (args := args) (sp := sp) hw3 hodd).mono
      (fun x y ⟨⟨_, R₁, P₁⟩, _, R₂, P₂⟩ => ⟨⟨run_step R₁ P₁.step, P₁.prep⟩, run_step R₂ P₂.step, P₂.prep⟩)
      fun _ _ h => h) fun x ⟨s₀, R, Pk⟩ => ?_) ?_
  · exact wp_and (WP.mono (round_ok Pk.prep Pk.wit hw3 hodd) fun u ⟨S, _⟩ => run_step (run_step R Pk.step) S)
      (WP.mono (WP.seq_iff.mp (drawRound_ok (Gs R) hw3 hodd Pk)) fun u h =>
        WP.mono h fun v ⟨P, e⟩ => ⟨⟨s₀, R, P⟩, e⟩)
  refine RelCT.seq (aRel (F := Φ) (fun _ h => h.1) hitTest_check fun _ h => h.2) ?_
  refine ite_fixed (b := !Spec.Ffdh.mrRound w (drawA w T c)) (fun _ h => h.2) (fun _ => ?_) fun _ => ?_
  · exact aRel (fun _ h => h.1.run) setSt2_check fun x ⟨⟨s₀, R, Pk⟩, _⟩ =>
      WP.mono (setSt_ok (Gs R) Pk.toMid (r := 2) (by decide)) fun u ⟨M, _⟩ => run_step R M.step
  · obtain ⟨n₁, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_arith⟩
    exact aRel (fun _ h => h.1.run) passed_check fun x ⟨⟨s₀, R, Pk⟩, _⟩ =>
      WP.mono (passed_ok (Gs R) Pk.toMid Pk.cnt) fun u ⟨M, _⟩ => run_step R M.step

/-- Runs at the same draw state leak the same trace. -/
theorem draw_trace {w n c : Nat} {T : List Byte} (G : TapeGeo Ex args base bytes sp T.length) (hw3 : 3 ≤ w)
    (hodd : w % 2 = 1) (hwl : w - 1 < 2 ^ (32 * cwc len .wide)) (hn : 1 ≤ n) (hc : c ≤ T.length) :
    RelCT isa (Both (DrawRun Ex base bytes len args sp w T n c)) draw fun _ _ => True := by
  have Gs : ∀ {s₀ : State}, Run Ex base bytes len args sp s₀ → TapeGeo Ex args base bytes (s₀.gpr .esp) T.length :=
    fun R => by rw [R.2.2]; exact G
  have bw := bc_eq_cwc len .wide
  obtain ⟨k2, kw, ho⟩ := witness_bits hw3 hwl
  generalize hk : Spec.RsaKeyGen.bitLength (w - 1) = k at k2 kw ho
  obtain ⟨o, hoo⟩ : ∃ o, Spec.Ffdh.witnessOctets w = o := ⟨_, rfl⟩
  rw [hoo] at ho
  unfold draw
  refine RelCT.seq (aRel (F := fun v => DrawRun Ex base bytes len args sp w T n c v ∧
      v.cf = some (decide (T.length - c < o))) (fun _ h => h.run) drawHead_check fun x ⟨s₀, R, A⟩ =>
    WP.mono (drawHead_ok (Gs R) (by have := bc_le A.step.inp.upper' .wide; omega_arith) A hc) fun v ⟨A', e⟩ => ⟨⟨s₀, R, A'⟩, by rw [e, hoo]⟩)
    (RelCT.seq (Q := fun _ _ => True) (R := Both (Run Ex base bytes len args sp)) ?_
      (aEnd (fun _ h => h) drawFin_check))
  refine ite_fixed (b := decide (T.length - c < o)) (fun _ h => h.2) (fun _ => ?_) fun e => ?_
  · exact aRel (fun _ h => h.1.run) setSt3_check fun x ⟨⟨s₀, R, A⟩, _⟩ =>
      WP.mono (setSt_ok (Gs R) A.toMid (r := 3) (by decide)) fun u ⟨M, _⟩ => run_step R M.step
  have co : c + o ≤ T.length := by simp at e; omega_arith
  let Φ : State → Prop := fun u => PickRun Ex base bytes len args sp w T n c u ∧
    isa.eval .e u = some (!drawRange w T c)
  -- The witness's octets.
  refine RelCT.seq (relCT_both (F := fun v => Run Ex base bytes len args sp v ∧ w32 v.mem base kOff = k ∧
      sv v.mem base len .wide 13 < 2 ^ (32 * ((k - 1) / 32 + 1)) ∧
      WP isa (.seq (cut (.slot .wide 13) false) (.seq (Impl.Ffdh.X86.rangeMask 13) Impl.Ffdh.X86.testMask)) v Φ)
    (drawLoad_trace (c := c) (o := o) (by omega_arith) fun x ⟨⟨_, R, A⟩, _⟩ =>
      ⟨run_step R A.step, A.cur, by rw [A.oct, hoo]⟩) fun x ⟨⟨s₀, R, A⟩, _⟩ => ?_) ?_
  · have Gx : TapeGeo Ex args base bytes (x.gpr .esp) T.length := by rw [A.step.esp]; exact Gs R
    have l := VG.Proof.Bignum.os2ip_lt ((T.drop c).take o)
    rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega_arith), VG.Proof.Bignum.pow256_eq] at l
    have W₁ : WP isa drawLoad x fun u => Run Ex base bytes len args sp u ∧ w32 u.mem base kOff = k ∧
        sv u.mem base len .wide 13 < 2 ^ (32 * ((k - 1) / 32 + 1)) :=
      WP.mono (drawLoad_ok A.prep Gx A.tape A.cur (by rw [A.oct, hoo]) (by omega_arith) co
        (by have := bc_le A.step.inp.upper' .wide; omega_arith)) fun u ⟨S, _, V, _, k₁⟩ =>
        ⟨run_step (run_step R A.step) S, by rw [k₁.word_eq, A.bits, hk],
          by rw [V]; exact Nat.lt_of_lt_of_le l (Nat.pow_le_pow_right (by decide) (by omega_arith))⟩
    have W₂ : WP isa drawLoad x fun u => WP isa (.seq (cut (.slot .wide 13) false)
        (.seq (Impl.Ffdh.X86.rangeMask 13) Impl.Ffdh.X86.testMask)) u Φ :=
      WP.mono (WP.seq_iff.mp (drawPick_ok (Gs R) hw3 hwl A (by rw [hoo]; exact co))) fun u h =>
        WP.mono h fun v ⟨P, e⟩ => ⟨⟨s₀, R, P⟩, e⟩
    exact WP.mono (wp_and W₁ W₂) fun u ⟨⟨a, b, c'⟩, d⟩ => ⟨a, b, c', d⟩
  -- Cut to the bits of `w − 1`.
  refine RelCT.seq (relCT_both (F := fun v => Run Ex base bytes len args sp v ∧
      WP isa (.seq (Impl.Ffdh.X86.rangeMask 13) Impl.Ffdh.X86.testMask) v Φ)
    (cut_trace cutRest13_check (k := k) (by omega_arith) fun _ h => ⟨h.1, h.2.1⟩) fun x ⟨R, hk', sm, hW⟩ =>
      wp_and (WP.mono (cut_ok R.1 (j := 13) (by decide) false hk' (by omega_arith) kw sm) fun u ⟨h, _, _, K⟩ =>
        ⟨h, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩) (WP.seq_iff.mp hW)) ?_
  -- Its range.
  refine RelCT.seq (aRel (F := fun v => Run Ex base bytes len args sp v ∧ WP isa Impl.Ffdh.X86.testMask v Φ)
    (fun _ h => h.1) rangeMask13_check fun x ⟨R, hW⟩ =>
      wp_and (WP.mono (rangeMask_ok R.1 (a := 13) (by decide)) fun u ⟨h, _, _, K⟩ =>
        ⟨h, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩) (WP.seq_iff.mp hW)) ?_
  refine RelCT.seq (aRel (F := Φ) (fun _ h => h.1) testMask_check fun _ h => h.2) ?_
  refine ite_fixed (b := !drawRange w T c) (fun _ h => h.2) (fun _ => ?_) fun _ => ?_
  · exact aRel (fun _ h => h.1.run) nilR_check fun x h => WP.block_nil h.1.run
  · exact (drawRound_trace G hw3 hodd hn).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h

end VG.Proof.Ffdh.X86.Cand

end

end

/-!
# The FFDH candidate on i686: a phase's timing

The halvings of `w − 1` and the draws each repeat as often in runs for the
same modulus and tape: the halving loop's count is `s` in `w − 1 = 2^s d`,
and each draw's next state (`drawN`, the cursor past the witness) and
whether the draws go on (`drawCont`) are functions of them
(`phase_trace`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86.Candidate

/-- What `prepHead` runs after the context's setup. -/
abbrev prepTail (j : Nat) : Prog isa :=
  .seq (setSmall (.slot .wide 14) (one .wide) 1) <| .seq (chain .sbb (.slot .wide 15) (.slot .wide j)
    (.slot .wide 14) (one .wide)) <| .seq (copy (.slot .wide 15) (.slot .wide 11) (one .wide))
    (.block [.mov .eax (.imm 0), .store (sc twoOff) .eax])
/-- The taint checks of `prepHead j`: the copy of the modulus before the context's setup, and what
follows it. -/
abbrev PrepHeadCk (j : Nat) : Prop :=
  ACheck (copy (.slot .wide j) (.slot .wide 0) (one .wide)) ∧ ACheck (prepTail j)
theorem prepHead9_check : PrepHeadCk 9 := by constructor <;> dsimp only [ACheck] <;> taint_decide
theorem prepHead10_check : PrepHeadCk 10 := by constructor <;> dsimp only [ACheck] <;> taint_decide
theorem halveBody_check : ACheck (.seq (halve (.slot .wide 11)) (.block (([.mov .eax (.mem (sc twoOff)),
    .alu .add .eax (.imm 1), .store (sc twoOff) .eax] : List Instr) ++ lowWord (.slot .wide 11) ++
    ([.alu .and .eax (.imm 1)] : List Instr)))) := by
  dsimp only [ACheck]; taint_decide
theorem setSt0_check : ACheck (.block [.mov .eax (.imm 0), .store (sc stOff) .eax]) := by
  dsimp only [ACheck]; taint_decide
theorem readSt_check : ACheck (.block [.mov .eax (.mem (sc stOff))]) := by dsimp only [ACheck]; taint_decide

variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- `k` halvings done, from a run's start. -/
abbrev HalvRun (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (w k : Nat) (x : State) : Prop :=
  ∃ s₀, Run Ex base bytes len args sp s₀ ∧ Halving Ex base bytes len args s₀ w k x

/-- Runs for the same modulus `w` prepare it alike. -/
theorem prepPhase_trace {j w : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 10) (hc : PrepHeadCk j) (hw3 : 3 ≤ w)
    (hodd : w % 2 = 1) {P : State → Prop}
    (hP : ∀ x, P x → Run Ex base bytes len args sp x ∧ sv x.mem base len .wide j = w) :
    RelCT isa (Both P) (prepPhase j) (Both (Run Ex base bytes len args sp)) := by
  unfold prepPhase
  have trace : RelCT isa (Both P) (prepHead j) fun _ _ => True :=
    RelCT.seq (aRel (F := Run Ex base bytes len args sp) (fun x h => (hP x h).1) hc.1 fun x h =>
      copyDown_run hj9 (by omega_using [hj]) (by decide) (hP x h).1)
      (RelCT.seq (prepare_relCT .wide) (RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2) hc.2))
  refine RelCT.seq (relCT_both (F := HalvRun Ex base bytes len args sp w 0) trace fun x h =>
    WP.mono (prepHead_ok (hP x h).1.1 hj9 hj (hP x h).2 hw3 hodd) fun v H => ⟨x, (hP x h).1, H⟩) ?_
  refine (RelCT.loop (I := fun m x y => ∃ k, m = (w - 1) / 2 ^ k ∧ m % 2 = 0 ∧ 0 < m ∧
      HalvRun Ex base bytes len args sp w k x ∧ HalvRun Ex base bytes len args sp w k y) (fun m => ?_) (w - 1)).mono
    (fun x y h => ⟨0, by simp, by omega_using [hodd], by omega_using [hw3], h.1, h.2⟩) fun _ _ h => h
  refine relCT_exists fun k => ?_
  refine (relCT_both (P := fun x => m = (w - 1) / 2 ^ k ∧ m % 2 = 0 ∧ 0 < m ∧
      HalvRun Ex base bytes len args sp w k x)
    (F := fun u => (m = (w - 1) / 2 ^ k ∧ m % 2 = 0 ∧ 0 < m) ∧ HalvRun Ex base bytes len args sp w (k + 1) u ∧
      isa.eval .e u = some (decide (((w - 1) / 2 ^ (k + 1)) % 2 = 0)))
    (RelCT.taint (A := taint) τA (fun x y h => ?_) halveBody_check) fun x ⟨hm, hx, hp, s₀, R, H⟩ => ?_).mono
    (fun x y ⟨a, b, c, d, e⟩ => ⟨⟨a, b, c, d⟩, a, b, c, e⟩)
    fun x y ⟨⟨⟨hm, hx, hp⟩, Hx, ex⟩, _, Hy, ey⟩ => ⟨by rw [ex, ey], ?_, ?_⟩
  · obtain ⟨⟨-, -, -, s₁, R₁, H₁⟩, -, -, -, s₂, R₂, H₂⟩ := h
    exact (run_step R₁ H₁.step).agree (run_step R₂ H₂.step)
  · have hwl : w < 2 ^ (32 * cwc len .wide) := by
      rw [← H.ready.ctx.mod]; exact val32_lt _ _ _ _
    rw [hm] at hx hp
    exact WP.mono (halveIter_ok H hx hp hwl) fun u ⟨Hu, z⟩ => ⟨⟨hm, by rw [hm]; exact hx, by rw [hm]; exact hp⟩,
      ⟨s₀, R, Hu⟩, z⟩
  · intro e
    obtain ⟨s₁, R₁, H₁⟩ := Hx
    obtain ⟨s₂, R₂, H₂⟩ := Hy
    exact ⟨run_step R₁ H₁.step, run_step R₂ H₂.step⟩
  · intro e
    rw [ex] at e
    have ev : ((w - 1) / 2 ^ (k + 1)) % 2 = 0 := by simpa using e
    have half : (w - 1) / 2 ^ (k + 1) = m / 2 := by rw [hm, Nat.pow_succ, Nat.div_div_eq_div_mul]
    exact ⟨m / 2, by omega_using [hp], k + 1, half.symm, by rw [← half]; exact ev, by omega_using [hx, hp], Hx, Hy⟩

/-- Runs at the same draw state draw alike until the phase ends. -/
theorem drawLoop_trace {w : Nat} {T : List Byte} (G : TapeGeo Ex args base bytes sp T.length) (hw3 : 3 ≤ w)
    (hodd : w % 2 = 1) (hwl : w - 1 < 2 ^ (32 * cwc len .wide)) {n c : Nat} (hn : 1 ≤ n) (hc : c ≤ T.length) :
    RelCT isa (Both (DrawRun Ex base bytes len args sp w T n c)) (.loop draw .e)
      (Both (Run Ex base bytes len args sp)) := by
  have Gs : ∀ {s₀ : State}, Run Ex base bytes len args sp s₀ → TapeGeo Ex args base bytes (s₀.gpr .esp) T.length :=
    fun R => by rw [R.2.2]; exact G
  refine (RelCT.loop (I := fun m x y => ∃ n c, m = T.length - c ∧ 1 ≤ n ∧ c ≤ T.length ∧
      DrawRun Ex base bytes len args sp w T n c x ∧ DrawRun Ex base bytes len args sp w T n c y) (fun m => ?_)
      (T.length - c)).mono (fun x y h => ⟨n, c, rfl, hn, hc, h.1, h.2⟩) fun _ _ h => h
  refine relCT_exists fun n => relCT_exists fun c => relCT_of_imp (A := 1 ≤ n ∧ c ≤ T.length) (fun ⟨hn, hc⟩ => ?_)
    fun _ _ h => ⟨h.2.1, h.2.2.1⟩
  let o := Spec.Ffdh.witnessOctets w
  refine (relCT_both (P := fun x => m = T.length - c ∧ 1 ≤ n ∧ c ≤ T.length ∧
      DrawRun Ex base bytes len args sp w T n c x)
    (F := fun u => (m = T.length - c) ∧
      ((isa.eval .e u = some true ∧ drawCont w n T c = true ∧
        DrawRun Ex base bytes len args sp w T (drawN w n T c) (c + o) u ∧ 1 ≤ drawN w n T c ∧ c < c + o ∧
        c + o ≤ T.length) ∨
      (isa.eval .e u = some false ∧ drawCont w n T c = false ∧ Run Ex base bytes len args sp u)))
    ((draw_trace G hw3 hodd hwl hn hc).mono (fun x y h => ⟨h.1.2.2.2, h.2.2.2.2⟩) fun _ _ h => h)
    fun x ⟨hm, _, _, s₀, R, A⟩ => ?_).mono (fun x y ⟨a, b, c, d, e⟩ => ⟨⟨a, b, c, d⟩, a, b, c, e⟩)
    fun x y ⟨⟨hm, Ox⟩, _, Oy⟩ => ?_
  · refine WP.mono (draw_ok (Gs R) hw3 hodd hwl A hn hc) fun u O => ⟨hm, ?_⟩
    rcases O with ⟨e, n', c', A', h1, h2, h3, -, h5, h6, h7⟩ | ⟨e, E, h7⟩
    · subst h5 h6
      exact .inl ⟨e, h7, ⟨s₀, R, A'⟩, h1, h2, h3⟩
    · exact .inr ⟨e, h7, run_step R E.step⟩
  · rcases Ox with ⟨ex, cx, Dx, h1, h2, h3⟩ | ⟨ex, cx, Rx⟩ <;>
      rcases Oy with ⟨ey, cy, Dy, -, -, -⟩ | ⟨ey, cy, Ry⟩
    · exact ⟨by rw [ex, ey], fun e => (by rw [ex] at e; cases e),
        fun _ => ⟨T.length - (c + o), by omega_using [hm, h2, h3], drawN w n T c, c + o, rfl, h1, h3, Dx, Dy⟩⟩
    · rw [cx] at cy; cases cy
    · rw [cx] at cy; cases cy
    · exact ⟨by rw [ex, ey], fun _ => ⟨Rx, Ry⟩, fun e => (by rw [ex] at e; cases e)⟩

/-- Runs of a phase for the same modulus, count of witnesses and tape cursor. -/
theorem phase_trace {j w n c : Nat} {T : List Byte} (hj9 : 9 ≤ j) (hj : j ≤ 10) (hck : PrepHeadCk j)
    (G : TapeGeo Ex args base bytes sp T.length) (hw3 : 3 ≤ w) (hodd : w % 2 = 1) (hn1 : 1 ≤ n)
    (hcT : c ≤ T.length) {P : State → Prop}
    (hP : ∀ x, P x → Run Ex base bytes len args sp x ∧
      Spec.Rsa.bytesAt x.mem (byteAddr (args 2)) T.length = T ∧ sv x.mem base len .wide j = w ∧
      w32 x.mem base octOff = Spec.Ffdh.witnessOctets w ∧ w32 x.mem base kOff = Spec.RsaKeyGen.bitLength (w - 1) ∧
      w32 x.mem base cntOff = n ∧ w32 x.mem base curOff = c) :
    RelCT isa (Both P) (phase j) fun _ _ => True := by
  refine relCT_of_imp (A := w - 1 < 2 ^ (32 * cwc len .wide)) (fun hwl => ?_) fun x _ h => by
    have := val32_lt x.mem base (lo len (.slot .wide j)) (cwc len .wide)
    change sv x.mem base len .wide j < _ at this
    have := (hP x h.1).2.2.1
    omega_arith
  unfold phase
  refine RelCT.assoc (RelCT.seq (relCT_both (F := DrawRun Ex base bytes len args sp w T n c)
    (RelCT.seq (prepPhase_trace hj9 hj hck hw3 hodd fun x h => ⟨(hP x h).1, (hP x h).2.2.1⟩)
      (aEnd (fun _ h => h) setSt0_check)) fun x h => ?_)
    (RelCT.seq (drawLoop_trace G hw3 hodd hwl hn1 hcT) (aEnd (fun _ h => h) readSt_check)))
  obtain ⟨R, hT, hw, ho, hk, hn, hc⟩ := hP x h
  exact WP.mono (phaseStart_ok R.1 (by rw [R.2.2]; exact G) hT hj9 hj hw hw3 hodd ho hk hn hc) fun u ⟨S, A, _⟩ =>
    ⟨u, run_step R S, A⟩

end VG.Proof.Ffdh.X86.Cand

end

end

/-!
# The FFDH candidate on i686: the tests' timing

Runs with the same moduli and tape run the same phases: each phase's status
is a function of them (`phase_ok`), so `onPass` takes the same side in both.
A result writes `used` through a pointer read from the header, which the
runs pin to the same argument (`usedTail_trace`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86 VG.Proof.Ffdh.X86.KeyGen
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86.Candidate

theorem zeroOut_check : ACheck zeroOut := by dsimp only [ACheck]; taint_decide
theorem acceptOut_check : ACheck acceptOut := by dsimp only [ACheck]; taint_decide
theorem readUsed0_check : ACheck (.block [.mov .eax (.imm 0), .mov .ecx (.mem (sc usedOff))]) := by
  dsimp only [ACheck]; taint_decide
theorem readUsedCur_check : ACheck (.block [.mov .eax (.mem (sc curOff)), .mov .ecx (.mem (sc usedOff))]) := by
  dsimp only [ACheck]; taint_decide
theorem writeUsed0_check : PCheck [.ecx] (.block [.store (at_ .ecx 0) .eax, .mov .eax (.imm 0),
    .store (at_ .ecx 4) .eax, .mov .eax (.imm 0)]) := by dsimp only [PCheck]; taint_decide
theorem writeUsed1_check : PCheck [.ecx] (.block [.store (at_ .ecx 0) .eax, .mov .eax (.imm 0),
    .store (at_ .ecx 4) .eax, .mov .eax (.imm 1)]) := by dsimp only [PCheck]; taint_decide
theorem writeUsed2_check : PCheck [.ecx] (.block [.store (at_ .ecx 0) .eax, .mov .eax (.imm 0),
    .store (at_ .ecx 4) .eax, .mov .eax (.imm 2)]) := by dsimp only [PCheck]; taint_decide
theorem words1_check : ACheck (.block (phaseWords 0 0 ++ ([.mov .eax (.imm 1), .store (sc cntOff) .eax] : List Instr))) := by
  dsimp only [ACheck]; taint_decide
theorem words2_check : ACheck (.block (phaseWords 1 0)) := by dsimp only [ACheck]; taint_decide
theorem words3_check : ACheck (.block (phaseWords 0 1)) := by dsimp only [ACheck]; taint_decide
theorem cmp1_check : ACheck (.block [.alu .cmp .eax (.imm 1)]) := by dsimp only [ACheck]; taint_decide
theorem cmp2_check : ACheck (.block [.alu .cmp .eax (.imm 2)]) := by dsimp only [ACheck]; taint_decide

variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- What a result needs of a run: `out`'s place, `used` in the header and the tape. -/
abbrev TCtx (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp up : BitVec 32) (T : List Byte) (x : State) : Prop :=
  Run Ex base bytes len args sp x ∧ OutAt args base bytes len 0 sp x.wr ∧ w32 x.mem base usedOff = up.toNat ∧
    Spec.Rsa.bytesAt x.mem (byteAddr (args 2)) T.length = T

theorem TCtx.step {up : BitVec 32} {T : List Byte} {x u : State} (C : TCtx Ex base bytes len args sp up T x)
    (G : TapeGeo Ex args base bytes sp T.length) (S : Step Ex base bytes len args x u)
    (hu : w32 u.mem base usedOff = w32 x.mem base usedOff) : TCtx Ex base bytes len args sp up T u :=
  ⟨run_step C.1 S, C.2.1.keep rfl S.keeps, by rw [hu, C.2.2.1],
    by rw [tape_keep (by rw [C.1.2.2]; exact G) S, C.2.2.2]⟩

theorem TCtx.regs {up : BitVec 32} {T : List Byte} {x v : State} (C : TCtx Ex base bytes len args sp up T x)
    (m : v.mem = x.mem) (K : Keeps [] x v) : TCtx Ex base bytes len args sp up T v :=
  ⟨⟨C.1.1.regs K m, C.1.2.1.keep K, (K.1 _ (by decide)).trans C.1.2.2⟩, C.2.1.keep rfl K, by rw [m]; exact C.2.2.1,
    by rw [m]; exact C.2.2.2⟩

/-- `used` written through the pointer in the header, after `i` sets `eax`. -/
theorem usedTail_trace {i : Instr} {r : BitVec 32} {up : BitVec 32}
    (hc₁ : ACheck (.block [i, .mov .ecx (.mem (sc usedOff))]))
    (hc₂ : PCheck [.ecx] (.block [.store (at_ .ecx 0) .eax, .mov .eax (.imm 0), .store (at_ .ecx 4) .eax,
      .mov .eax (.imm r)]))
    (hi : ∀ x, In Ex base bytes len args x → WP isa (.block [i]) x fun v => Keeps [.eax] x v ∧ v.mem = x.mem)
    {P : State → Prop} (hP : ∀ x, P x → Run Ex base bytes len args sp x ∧ w32 x.mem base usedOff = up.toNat) :
    RelCT isa (Both P) (.block (([i] : List Instr) ++ storeUsed ++ ([.mov .eax (.imm r)] : List Instr))) fun _ _ => True := by
  have e : [i] ++ storeUsed ++ [.mov .eax (.imm r)] = [i, .mov .ecx (.mem (sc usedOff))] ++
      [.store (at_ .ecx 0) .eax, .mov .eax (.imm 0), .store (at_ .ecx 4) .eax, .mov .eax (.imm r)] := rfl
  rw [e]
  refine RelCT.block_append (RelCT.seq (aRel (F := fun v => Run Ex base bytes len args sp v ∧ v.gpr .ecx = up)
    (fun x h => (hP x h).1) hc₁ fun x h => ?_)
    (pinned_end (rs := [.ecx]) (fun _ h => h.1) (fun x y hx hy r hr => ?_) hc₂))
  · obtain ⟨R, hu⟩ := hP x h
    refine (WP.block_append_iff (M := isa) (l₁ := [i]) (l₂ := [Instr.mov .ecx (.mem (sc usedOff))])).mpr
      (WP.mono (hi x R.1) fun s₁ ⟨K₁, m₁⟩ => ?_)
    have h₁ : In Ex base bytes len args s₁ := R.1.regs K₁ m₁
    refine wp_movS (hdr_read h₁ hdr_used) fun v U _ => WP.block_nil ⟨?_, ?_⟩
    · have K : Keeps [.eax, .ecx] x v := (K₁.mono (by decide)).trans (U.keeps.mono (by decide))
      exact ⟨h₁.regs U.keeps U.mem, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩
    · rw [U.gpr, m₁, hu, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    rw [hx.2, hy.2]

theorem movImm_keeps {x : State} {v : BitVec 32} :
    WP isa (.block [.mov .eax (.imm v)]) x fun u => Keeps [.eax] x u ∧ u.mem = x.mem :=
  wp_movS rfl fun _ U _ => WP.block_nil ⟨U.keeps, U.mem⟩

theorem movCur_keeps {x : State} (h : In Ex base bytes len args x) :
    WP isa (.block [.mov .eax (.mem (sc curOff))]) x fun u => Keeps [.eax] x u ∧ u.mem = x.mem :=
  wp_movS (hdr_read h hdr_cur) fun _ U _ => WP.block_nil ⟨U.keeps, U.mem⟩

/-- `out` zeroed: what follows has the run and `used`. -/
theorem zeroOut_both {up : BitVec 32} {T : List Byte} {P : State → Prop}
    (hP : ∀ x, P x → TCtx Ex base bytes len args sp up T x) :
    RelCT isa (Both P) zeroOut (Both fun v => Run Ex base bytes len args sp v ∧ w32 v.mem base usedOff = up.toNat) :=
  aRel (fun x h => (hP x h).1) zeroOut_check fun x h => by
    obtain ⟨R, Ox, hu, -⟩ := hP x h
    exact WP.mono (zeroOut_ok R.1 (by rw [R.2.2]; exact Ox)) fun v ⟨_, _, K, I, k⟩ =>
      ⟨⟨I, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩, by rw [k.word_eq, hu]⟩

theorem short_trace {up : BitVec 32} {T : List Byte} {P : State → Prop}
    (hP : ∀ x, P x → TCtx Ex base bytes len args sp up T x) :
    RelCT isa (Both P) short fun _ _ => True := by
  unfold short
  exact RelCT.seq (zeroOut_both hP) (usedTail_trace readUsed0_check writeUsed0_check (fun _ _ => movImm_keeps)
    fun _ h => h)

theorem reject_trace {up : BitVec 32} {T : List Byte} {P : State → Prop}
    (hP : ∀ x, P x → TCtx Ex base bytes len args sp up T x) :
    RelCT isa (Both P) reject fun _ _ => True := by
  unfold reject
  exact RelCT.seq (zeroOut_both hP) (usedTail_trace readUsedCur_check writeUsed2_check (fun _ h => movCur_keeps h)
    fun _ h => h)

theorem accept_trace {up : BitVec 32} {T : List Byte} {P : State → Prop}
    (hP : ∀ x, P x → TCtx Ex base bytes len args sp up T x ∧ sv x.mem base len .wide 9 < 2 ^ (8 * len)) :
    RelCT isa (Both P) Impl.Ffdh.X86.Candidate.accept fun _ _ => True := by
  unfold Impl.Ffdh.X86.Candidate.accept
  refine RelCT.seq (aRel (F := fun v => Run Ex base bytes len args sp v ∧ w32 v.mem base usedOff = up.toNat)
    (fun x h => (hP x h).1.1) acceptOut_check fun x h => ?_)
    (usedTail_trace readUsedCur_check writeUsed1_check (fun _ h => movCur_keeps h) fun _ h => h)
  obtain ⟨⟨R, Ox, hu, -⟩, hpl⟩ := hP x h
  exact WP.mono (acceptOut_ok R.1 (by rw [R.2.2]; exact Ox) rfl hpl) fun v ⟨_, _, K, I, k⟩ =>
    ⟨⟨I, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩, by rw [k.word_eq, hu]⟩

/-- The status compared with `k`. -/
theorem cmpStatus_ok {s : State} {D : Option (Bool × Spec.RsaKeyGen.Rand)}
    (he : s.gpr .eax = BitVec.ofNat 32 (drawStatus D)) {k : Nat} (hk : k < 4) :
    WP isa (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 k))]) s fun u =>
      isa.eval .e u = some (decide (drawStatus D = k)) ∧ u.mem = s.mem ∧ Keeps [] s u ∧ u.gpr .eax = s.gpr .eax := by
  have st : drawStatus D < 4 := by unfold drawStatus; split <;> decide
  refine wp_cmpi fun u F _ z => WP.block_nil ⟨?_, F.mem, F.keeps [], congrFun F.gpr _⟩
  show u.zf = _
  rw [z, he]
  exact congrArg some (sub_beq (by omega_arith) (by omega_arith))

/-- After a phase whose result `D` the runs share: on to `rest` if it passed, else a rejection or a
shortage. `P` holds through a comparison. -/
theorem onPass_trace {up : BitVec 32} {T : List Byte} {D : Option (Bool × Spec.RsaKeyGen.Rand)} {P : State → Prop}
    (hP : ∀ x, P x → TCtx Ex base bytes len args sp up T x ∧ x.gpr .eax = BitVec.ofNat 32 (drawStatus D))
    (hcl : ∀ x v, P x → v.mem = x.mem → Keeps [] x v → P v)
    {rest : Prog isa} (hrest : drawStatus D = 1 → RelCT isa (Both P) rest fun _ _ => True) :
    RelCT isa (Both P) (onPass rest) fun _ _ => True := by
  have cmp : ∀ k, k < 4 → ∀ x, P x → WP isa (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 k))]) x fun v =>
      P v ∧ isa.eval .e v = some (decide (drawStatus D = k)) := fun k hk x h =>
    WP.mono (cmpStatus_ok (hP x h).2 hk) fun v ⟨e, m, K, _⟩ => ⟨hcl x v h m K, e⟩
  unfold onPass
  refine RelCT.seq (aRel (fun x h => (hP x h).1.1) cmp1_check (cmp 1 (by decide))) ?_
  refine ite_fixed (b := decide (drawStatus D = 1)) (fun _ h => h.2) (fun e => ?_) fun _ => ?_
  · exact (hrest (by simpa using e)).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h
  refine RelCT.seq (aRel (fun x h => (hP x h.1).1.1) cmp2_check fun x h => cmp 2 (by decide) x h.1) ?_
  refine ite_fixed (b := decide (drawStatus D = 2)) (fun _ h => h.2) (fun _ => ?_) fun _ => ?_
  · exact reject_trace fun x h => (hP x h.1).1
  · exact short_trace fun x h => (hP x h.1).1

/-- After a phase from a state `Pre`: the words the phase keeps, the status of its result `D` in
`eax`, and where a pass leaves the tape. -/
abbrev Passed (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp up : BitVec 32) (T : List Byte) (Pre : State → Prop) (D : Option (Bool × Spec.RsaKeyGen.Rand)) (u : State) :
    Prop :=
  ((∃ x, Pre x ∧ Kept base len [11, 13, 14, 15] (twoOff :: drawDs) x.mem u.mem) ∧
    TCtx Ex base bytes len args sp up T u ∧ u.gpr .eax = BitVec.ofNat 32 (drawStatus D)) ∧
    ∀ b r, D = some (b, r) → ∃ c', w32 u.mem base curOff = c' ∧ c' ≤ T.length ∧ T.drop c' = r

/-- A phase and what follows it, for runs with the same modulus, count and cursor. -/
theorem phasePass_trace {up : BitVec 32} {T : List Byte} (G : TapeGeo Ex args base bytes sp T.length)
    {j w n c : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 10) (hck : PrepHeadCk j) (hw3 : 3 ≤ w) (hodd : w % 2 = 1)
    (hn1 : 1 ≤ n) (hcT : c ≤ T.length) {Pre : State → Prop}
    (hPre : ∀ x, Pre x → TCtx Ex base bytes len args sp up T x ∧ sv x.mem base len .wide j = w ∧
      w32 x.mem base octOff = Spec.Ffdh.witnessOctets w ∧ w32 x.mem base kOff = Spec.RsaKeyGen.bitLength (w - 1) ∧
      w32 x.mem base cntOff = n ∧ w32 x.mem base curOff = c)
    {rest : Prog isa}
    (hrest : drawStatus (ParameterCandidate.checkWitnesses w n (T.drop c)) = 1 →
      RelCT isa (Both (Passed Ex base bytes len args sp up T Pre (ParameterCandidate.checkWitnesses w n (T.drop c))))
        rest fun _ _ => True) :
    RelCT isa (Both Pre) (.seq (phase j) (onPass rest)) fun _ _ => True := by
  refine RelCT.seq (relCT_both (phase_trace (len := len) hj9 hj hck G hw3 hodd hn1 hcT fun x h => ?_) fun x h => ?_)
    (onPass_trace (fun x h => ⟨h.1.2.1, h.1.2.2⟩) (fun x v h m K => ⟨⟨?_, h.1.2.1.regs m K, ?_⟩, ?_⟩) hrest)
  · obtain ⟨⟨R, _, _, hT⟩, hw, ho, hk, hn, hc⟩ := hPre x h
    exact ⟨R, hT, hw, ho, hk, hn, hc⟩
  · obtain ⟨C, hw, ho, hk, hn, hc⟩ := hPre x h
    exact WP.mono (phase_ok C.1.1 (by rw [C.1.2.2]; exact G) C.2.2.2 hj9 hj hw hw3 hodd ho hk hn hn1 hc hcT)
      fun u ⟨S, E, Cu, k⟩ => ⟨⟨⟨x, h, k⟩, C.step G S (k.word_eq (d := usedOff) (by decide)), E⟩, Cu⟩
  · obtain ⟨x', hx', k⟩ := h.1.1
    exact ⟨x', hx', by rw [m]; exact k⟩
  · rw [K.1 _ (by decide)]; exact h.1.2.2
  · intro b r e
    obtain ⟨c', hc, hl, hr⟩ := h.2 b r e
    exact ⟨c', by rw [m]; exact hc, hl, hr⟩

/-- The tests' state: `bits`, p and q, and the cursor `c`. -/
abbrev TestsAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp up : BitVec 32) (T : List Byte) (bits p q c : Nat) (x : State) : Prop :=
  TCtx Ex base bytes len args sp up T x ∧ w32 x.mem base bitsOff = bits ∧ sv x.mem base len .wide 9 = p ∧
    sv x.mem base len .wide 10 = q ∧ w32 x.mem base curOff = c

/-- A phase's state: the tests' and the phase's words for the modulus `w`. -/
abbrev StageAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp up : BitVec 32) (T : List Byte) (bits p q w n c : Nat) (x : State) : Prop :=
  TestsAt Ex base bytes len args sp up T bits p q c x ∧ w32 x.mem base octOff = Spec.Ffdh.witnessOctets w ∧
    w32 x.mem base kOff = Spec.RsaKeyGen.bitLength (w - 1) ∧ w32 x.mem base cntOff = n

theorem drawStatus_one {D : Option (Bool × Spec.RsaKeyGen.Rand)} (h : drawStatus D = 1) :
    ∃ r, D = some (true, r) := by
  rcases D with _ | ⟨⟨⟩ | ⟨⟩, r⟩
  · simp [drawStatus] at h
  · simp [drawStatus] at h
  · exact ⟨r, rfl⟩

/-- After a phase that passed with the rest `r` of the tape: the tests' state from where it left the
tape. -/
theorem Passed.tests {up : BitVec 32} {T : List Byte} {bits p q w n c : Nat} {D : Option (Bool × Spec.RsaKeyGen.Rand)}
    {r : Spec.RsaKeyGen.Rand} (hD : D = some (true, r)) {u : State}
    (h : Passed Ex base bytes len args sp up T (StageAt Ex base bytes len args sp up T bits p q w n c) D u) :
    TestsAt Ex base bytes len args sp up T bits p q (T.length - r.length) u ∧ T.length - r.length ≤ T.length := by
  obtain ⟨⟨⟨x, ⟨⟨_, hb, hp, hq, _⟩, _⟩, k⟩, C, _⟩, hc⟩ := h
  obtain ⟨c', hc', hl, hr⟩ := hc true r hD
  have e : T.length - r.length = c' := by rw [← hr, List.length_drop]; omega_arith
  exact ⟨⟨C, by rw [k.word_eq, hb], by rw [k.slot_eq, hp], by rw [k.slot_eq, hq], by rw [e, hc']⟩, by omega_arith⟩

/-- A phase's words for the modulus `w` of `bits − δ` bits, with `n` witnesses. -/
theorem stageWords_ok {up : BitVec 32} {T : List Byte} (G : TapeGeo Ex args base bytes sp T.length)
    {bits p q c : Nat} {x : State} (A : TestsAt Ex base bytes len args sp up T bits p q c x) {δ ε w : Nat}
    (hδ : δ ≤ 1) (hε : ε ≤ 1) (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192)
    (hw : Spec.RsaKeyGen.bitLength (w - 1) = bits - δ) :
    WP isa (.block (phaseWords δ ε)) x
      (StageAt Ex base bytes len args sp up T bits p q w (Spec.Ffdh.primeChecks (bits - δ) - ε) c) := by
  obtain ⟨C, hb, hp, hq, hc⟩ := A
  have := phaseWords_ok (is := []) (Q := StageAt Ex base bytes len args sp up T bits p q w
      (Spec.Ffdh.primeChecks (bits - δ) - ε) c) C.1.1 hb hδ hε hb1 hb2 fun t S K O N k =>
    WP.block_nil ⟨⟨C.step G S (k.word_eq (d := usedOff)), by rw [k.word_eq, hb], by rw [k.slot_eq, hp],
      by rw [k.slot_eq, hq], by rw [k.word_eq, hc]⟩, by rw [O, Spec.Ffdh.witnessOctets, hw], by rw [K, hw], N⟩
  rwa [List.append_nil] at this

/-- Runs of the tests for the same p, q and cursor. -/
theorem tests_trace {up : BitVec 32} {T : List Byte} (G : TapeGeo Ex args base bytes sp T.length)
    {bits p q c₀ : Nat} (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hp3 : 3 ≤ p) (hpo : p % 2 = 1)
    (hq3 : 3 ≤ q) (hqo : q % 2 = 1) (hbp : Spec.RsaKeyGen.bitLength (p - 1) = bits)
    (hbq : Spec.RsaKeyGen.bitLength (q - 1) = bits - 1) (hpl : p < 2 ^ (8 * len)) (hcT : c₀ ≤ T.length) :
    RelCT isa (Both (TestsAt Ex base bytes len args sp up T bits p q c₀)) tests fun _ _ => True := by
  have pc : ∀ b, 1 ≤ Spec.Ffdh.primeChecks b - 1 := fun b => by unfold Spec.Ffdh.primeChecks; split <;> omega_arith
  unfold tests
  -- One witness for p.
  refine RelCT.seq (aRel (F := StageAt Ex base bytes len args sp up T bits p q p 1 c₀) (fun x h => h.1.1)
    words1_check fun x A => ?_) ?_
  · obtain ⟨C, hb, hp, hq, hc⟩ := A
    exact phaseWords_ok (δ := 0) (ε := 0) C.1.1 hb (by decide) (by decide) hb1 hb2 fun t₁ S₁ K₁ O₁ _ k₁ =>
      wp_movi fun t₂ U₂ => hdr_store (S₁.inp.regs U₂.keeps U₂.mem) hdr_cnt fun t₃ S₃ W₃ k₃ _ _ _ _ => by
        have S : Step Ex base bytes len args x t₃ := S₁.trans ((Step.regs S₁.inp U₂.mem U₂.keeps).trans S₃)
        have k : Kept base len [] [kOff, octOff, cntOff] x.mem t₃.mem :=
          k₁.trans ((by rw [U₂.mem]; exact (Kept.refl _).mono : Kept base len [] [kOff, octOff, cntOff] t₁.mem t₂.mem).trans
            k₃.mono)
        exact WP.block_nil ⟨⟨C.step G S (k.word_eq (d := usedOff)), by rw [k.word_eq, hb], by rw [k.slot_eq, hp],
          by rw [k.slot_eq, hq], by rw [k.word_eq, hc]⟩,
          by rw [k₃.word_eq, U₂.mem, O₁, Spec.Ffdh.witnessOctets, hbp, Nat.sub_zero],
          by rw [k₃.word_eq, U₂.mem, K₁, hbp, Nat.sub_zero], by rw [W₃, U₂.gpr]; rfl⟩
  refine phasePass_trace G (by decide) (by decide) prepHead9_check hp3 hpo (by decide) hcT
    (fun x h => ⟨h.1.1, h.1.2.2.1, h.2.1, h.2.2.1, h.2.2.2, h.1.2.2.2.2⟩) fun e₁ => ?_
  obtain ⟨r₁, hD₁⟩ := drawStatus_one e₁
  -- All of q's.
  refine RelCT.seq (aRel (F := StageAt Ex base bytes len args sp up T bits p q q
      (Spec.Ffdh.primeChecks (bits - 1) - 0) (T.length - r₁.length)) (fun x h => h.1.2.1.1)
    words2_check fun x h => stageWords_ok G (h.tests hD₁).1 (by decide) (by decide) hb1 hb2 hbq) ?_
  refine phasePass_trace G (by decide) (by decide) prepHead10_check hq3 hqo (by have := pc (bits - 1); omega_arith) (by omega_arith)
    (fun x h => ⟨h.1.1, h.1.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2, h.1.2.2.2.2⟩) fun e₂ => ?_
  obtain ⟨r₂, hD₂⟩ := drawStatus_one e₂
  -- The rest of p's.
  refine RelCT.seq (aRel (F := StageAt Ex base bytes len args sp up T bits p q p
      (Spec.Ffdh.primeChecks (bits - 0) - 1) (T.length - r₂.length)) (fun x h => h.1.2.1.1)
    words3_check fun x h => stageWords_ok G (h.tests hD₂).1 (by decide) (by decide) hb1 hb2 hbp) ?_
  refine phasePass_trace G (by decide) (by decide) prepHead9_check hp3 hpo (pc _) (by omega_arith)
    (fun x h => ⟨h.1.1, h.1.2.2.1, h.2.1, h.2.2.1, h.2.2.2, h.1.2.2.2.2⟩) fun e₃ => ?_
  obtain ⟨r₃, hD₃⟩ := drawStatus_one e₃
  exact accept_trace fun x h => by
    obtain ⟨A, -⟩ := h.tests hD₃
    exact ⟨A.1, by rw [A.2.2.1]; exact hpl⟩

end VG.Proof.Ffdh.X86.Cand

end

end

/-! ### `Ffdh.X86.Cand.CTSieve`, which only this module used -/

section

/-! ### `Ffdh.X86.Cand.CTSmall`, which this module and modules that import it used -/

section

/-!
# The FFDH candidate on i686: the timing of a division by a small prime

`divides` stores the number's end in its frame, which RSA's trial division
compares with its pointer: its loop runs for as many words as the number
has, the same in runs of the same length (`divides_trace`, through RSA's
`divisor_trace_bounded`). Everything else it does addresses the stack.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86.Candidate
open VG.Proof.RsaKeyGen.X86.Sieve (Geometry StackContext ReadControl)

variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- A frame of the stack ends where it began. -/
theorem frame_esp {bytes : Nat} {body : Prog isa} {s s' : State} {t : List Leak}
    (e : Exec isa (.frame (.alloc bytes) body (.free bytes)) s t s') : s'.gpr .esp = s.gpr .esp := by
  cases e with
  | frame p b q =>
    obtain rfl := alloc_some p
    simp only [isa, pop] at q
    split at q
    · rename_i hc
      cases q
      simp only [State.setReg, ↓reduceIte]
      rw [hc.2.2.2.1, allocFrame_esp, BitVec.sub_add_cancel]
    · cases q

/-- Runs of a frame whose bodies leak alike end with `esp` where it was. -/
theorem relCT_frame {bytes : Nat} {body : Prog isa} {P : State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, Both P s₁ s₂ ∧ a = allocFrame bytes s₁ ∧ b = allocFrame bytes s₂) body
      fun _ _ => True) :
    RelCT isa (Both P) (.frame (.alloc bytes) body (.free bytes)) fun a b => ∃ x y, Both P x y ∧
      a.gpr .esp = x.gpr .esp ∧ b.gpr .esp = y.gpr .esp :=
  fun x y _ _ _ _ hp e₁ e₂ => ⟨(RelCT.frameAlloc hb _ _ _ _ _ _ hp e₁ e₂).1, x, y, hp, frame_esp e₁, frame_esp e₂⟩

theorem restoreEdi_trace {Q : State → State → Prop} (hq : ∀ x y, Q x y → x.gpr .esp = y.gpr .esp) :
    RelCT isa Q (.block restoreEdi) fun _ _ => True :=
  (VG.Proof.Dsa.X86.checkedBlockInvariant (τ := τr [.esp]) rfl rfl).mono
    (fun x y h => agree_regs fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hq x y h) fun _ _ _ => trivial

/-- The frame's words for a division: the number's end at `esp + 4`, the prime and its inverse. -/
abbrev divSetup (prime inv : Nat) : List Instr :=
  [.mov .edi (.reg .eax), .store (VG.Impl.RsaKeyGen.X86.Sieve.slot 4) .ecx, .mov .ebx (.imm (BitVec.ofNat 32 prime)),
    .mov .esi (.imm (BitVec.ofNat 32 inv)), .mov .ebp (.imm 0)]

/-- The number's address. -/
abbrev slotPtr (base : Addr) (len j : Nat) : BitVec 32 := BitVec.ofNat 32 (base.toNat + lo len (.slot .wide j))

/-- The geometry RSA's trial division reads the number of wide slot `j` with, below `sp`. -/
abbrev divGeo (base : Addr) (len j : Nat) (sp : BitVec 32) : Geometry :=
  ⟨sp - BitVec.ofNat 32 20, slotPtr base len j, 0, mw len, 0⟩

/-- `bounds`: the address of wide slot `j` in `eax`, its end in `ecx`. -/
abbrev Bounded (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (j : Nat) (u : State) : Prop :=
  Run Ex base bytes len args sp u ∧ u.gpr .eax = slotPtr base len j ∧
    u.gpr .ecx = slotPtr base len j + BitVec.ofNat 32 (bc len .wide)

theorem bounds_run {j : Nat} (hj : j ≤ 27) {x : State} (R : Run Ex base bytes len args sp x) :
    WP isa (.block (bounds (.slot .wide j))) x (Bounded Ex base bytes len args sp j) := by
  have h := R.1
  have f := slot_fit1 h hj
  rw [cb1] at f
  have nw := h.scratch.nowrap
  have := bounds_ok (is := []) (Q := Bounded Ex base bytes len args sp j) h hj fun u mu Ku au cu => by
    have e : u.gpr .eax = slotPtr base len j := by
      apply BitVec.eq_of_toNat_eq; rw [au, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    exact WP.block_nil ⟨⟨h.regs Ku mu, R.2.1.keep Ku, (Ku.1 _ (by decide)).trans R.2.2⟩, e, by rw [cu, e]⟩
  rwa [List.append_nil] at this

theorem divSetup_ok {j : Nat} (hj : j ≤ 27) {prime inv : Nat} {u : State} (B : Bounded Ex base bytes len args sp j u) :
    WP isa (.block (divSetup prime inv)) (allocFrame 20 u) (ReadControl (divGeo base len j sp) 0) := by
  have h := B.1.1
  have f := slot_fit1 h hj
  rw [cb1] at f
  have nw := h.scratch.nowrap
  have low := h.room.low
  have bl := h.bytes_lt
  have c2 := cwc_two len
  have bw := bc_eq_cwc len .wide
  have spu : u.gpr .esp = sp := B.1.2.2
  have lw := h.lower'
  have mwp : 8 ≤ mw len := by simp only [mw, Spec.Rsa.modulusWords]; omega_arith
  have SC : StackContext (sp - BitVec.ofNat 32 20) (allocFrame 20 u) := by
    refine ⟨⟨?_, ?_⟩, by rw [allocFrame_esp, spu]⟩
    · rw [allocFrame_wr, spu]; exact List.mem_cons_self ..
    · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (sp - BitVec.ofNat 32 20).isLt; omega_arith),
        VG.X86.sub_toNat (by rw [← spu]; omega_arith)]
      rw [← spu]; omega_arith
  have PA : (slotPtr base len j).setWidth 64 = off base (lo len (.slot .wide j)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := base.isLt
    omega_arith
  refine wp_mov fun a₁ U₁ => ?_
  refine (WP.block_append_iff (M := isa) (l₁ := [Instr.store (VG.Impl.RsaKeyGen.X86.Sieve.slot 4) .ecx])
    (l₂ := [.mov .ebx (.imm (BitVec.ofNat 32 prime)), .mov .esi (.imm (BitVec.ofNat 32 inv)), .mov .ebp (.imm 0)])).mpr
    (WP.mono ((SC.keep U₁.keeps (by decide)).store 4 (by decide) .ecx) fun a₂ ⟨M₂, _, K₂, S₂⟩ => ?_)
  refine wp_movi fun a₃ U₃ => wp_movi fun a₄ U₄ => wp_movi fun a₅ U₅ => WP.block_nil ?_
  have K : Keeps [.ebx, .esi, .ebp] a₂ a₅ :=
    ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide))).trans (U₅.keeps.mono (by decide))
  have m : a₅.mem = a₂.mem := by rw [U₅.mem, U₄.mem, U₃.mem]
  refine ⟨S₂.keep K (by decide), fun k hk => ?_, ?_, ?_⟩
  · have Ws₅ : Ws a₅ base bytes := ⟨by
      rw [K.2.2, K₂.2.2, U₁.keeps.2.2, allocFrame_wr]; exact List.mem_cons_of_mem _ h.ws.wr, nw⟩
    show InRegions _ (off ((slotPtr base len j).setWidth 64) (4 * k)) 4
    rw [PA, off, VG.Offset.add_add, ← off]
    exact ws_read Ws₅ (by have : k < 2 * mw len := hk; omega_arith)
  · show a₅.mem.readW _ 32 = slotPtr base len j + BitVec.ofNat 32 (8 * mw len)
    rw [m, M₂, Mem.readW_writeW_self32, U₁.other _ (by decide), allocFrame_gpr _ _ (by decide), B.2.2]
    rfl
  · rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide), K₂.1 _ (by simp), U₁.gpr,
      allocFrame_gpr _ _ (by decide), B.2.1]
    simp

/-- The taint analysis passes `p` with only the registers `rs` public. -/
abbrev RCheck (rs : List Reg) (p : Prog isa) : Prop :=
  (VG.Taint.check taint (τr rs) p (VG.Taint.hintOf taint (τr rs) p)).isSome = true

/-- Runs of a division by a small prime of wide slot `j`. -/
theorem divides_trace {j : Nat} (hj : j ≤ 27) {prime inv : Nat} (hc₁ : ACheck (.block (bounds (.slot .wide j))))
    (hc₂ : RCheck [.esp, .eax] (.block (divSetup prime inv))) {P : State → Prop}
    (hP : ∀ x, P x → Run Ex base bytes len args sp x) :
    RelCT isa (Both P) (divides (.slot .wide j) prime inv) fun _ _ => True := by
  refine relCT_of_imp (A := 0 < mw len ∧ mw len ≤ 128 ∧ (slotPtr base len j).toNat + 8 * mw len ≤ 2 ^ 32)
    (fun ⟨pos, wb, fit⟩ => ?_) fun x _ h => by
      have h := (hP x h.1).1
      have f := slot_fit1 h hj
      rw [cb1] at f
      have nw := h.scratch.nowrap
      have lw := h.lower'
      have up := h.upper'
      have : 8 ≤ mw len ∧ mw len ≤ 128 := by simp only [mw, Spec.Rsa.modulusWords]; omega_arith
      refine ⟨by omega_arith, this.2, ?_⟩
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have : bc len .wide = 8 * mw len := rfl; omega_arith)]
      have : bc len .wide = 8 * mw len := rfl
      omega_arith
  unfold divides
  refine RelCT.seq (aRel (F := Bounded Ex base bytes len args sp j) (fun x h => hP x h) hc₁
    fun x h => bounds_run hj (hP x h)) ?_
  refine RelCT.seq (relCT_frame ?_) (restoreEdi_trace fun x y ⟨x₀, y₀, ⟨B₀, B₁⟩, ex, ey⟩ => by
    rw [ex, ey, B₀.1.2.2, B₁.1.2.2])
  refine RelCT.seq (((RelCT.taint (A := taint) (τr [.esp, .eax]) (fun a b h => ?_) hc₂).wp
    (F₁ := ReadControl (divGeo base len j sp) 0) (F₂ := ReadControl (divGeo base len j sp) 0)
    fun a b ⟨s₁, s₂, ⟨B₁, B₂⟩, ea, eb⟩ => ⟨ea ▸ divSetup_ok hj B₁, eb ▸ divSetup_ok hj B₂⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2)
    ((VG.Proof.RsaKeyGen.X86.Sieve.divisor_trace_bounded pos wb fit).mono (fun _ _ h => h) fun _ _ _ => trivial)
  obtain ⟨s₁, s₂, ⟨B₁, B₂⟩, rfl, rfl⟩ := h
  refine agree_regs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [allocFrame_esp, allocFrame_esp, B₁.1.2.2, B₂.1.2.2]
  · rw [allocFrame_gpr _ _ (by decide), allocFrame_gpr _ _ (by decide), B₁.2.1, B₂.2.1]

end VG.Proof.Ffdh.X86.Cand

end

end

/-!
# The FFDH candidate on i686: the sieve's timing

The sieve's frame is set up through the stack and the table's symbol, whose
addresses only `esp` fixes (`sieveSetup_trace`); RSA's sieve loop then
leaks which primes of the table divide the number (`loop_trace`), the same
for runs of the same number (`sieve_trace`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86.Candidate
open VG.Proof.RsaKeyGen.X86.Sieve (Geometry StackContext StateAt)

variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- The sieve's frame set up, from runs with `esp` at `p`. -/
theorem sieveSetup_trace {p : BitVec 32} (low : 4 ≤ p.toNat) :
    RelCT isa (fun a b => a.gpr .esp = p ∧ b.gpr .esp = p) sieveSetup fun _ _ => True := by
  have first : RelCT isa (fun a b => a.gpr .esp = p ∧ b.gpr .esp = p)
      (.block [.store (VG.Impl.RsaKeyGen.X86.Sieve.slot 0) .eax, .store (VG.Impl.RsaKeyGen.X86.Sieve.slot 4) .ecx,
        .store (VG.Impl.RsaKeyGen.X86.Sieve.slot 12) .edx])
      (fun a b => a.gpr .esp = p ∧ b.gpr .esp = p) := by
    intro s t tr ur u z ⟨S, T⟩ E G
    have A : VG.X86.Taint.Agree (τr [.esp]) s t :=
      agree_regs fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact S.trans T.symm
    refine ⟨((VG.Proof.Dsa.X86.checkedBlockInvariant (τ := τr [.esp]) rfl rfl) _ _ _ _ _ _ A E G).1, ?_, ?_⟩
    · rw [Exec.gpr (by decide) E, S]
    · rw [Exec.gpr (by decide) G, T]
  have middle : RelCT isa (fun a b => a.gpr .esp = p ∧ b.gpr .esp = p)
      VG.Impl.RsaKeyGen.X86.Sieve.tableAddress (VG.X86.Taint.Agree (τr [.esp])) := by
    intro s t tr ur u z ⟨S, T⟩ E G
    have Ls : 4 ≤ (s.gpr .esp).toNat := by rw [S]; exact low
    have Lt : 4 ≤ (t.gpr .esp).toNat := by rw [T]; exact low
    have U := VG.Proof.Dsa.X86.wp_result (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol s Ls) E
    have Z := VG.Proof.Dsa.X86.wp_result (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol t Lt) G
    refine ⟨?_, agree_regs (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact
      (U.gpr .esp (by decide)).trans (S.trans (T.symm.trans (Z.gpr .esp (by decide)).symm)))⟩
    rw [symFrame_trace Ls E, symFrame_trace Lt G, S, T]
  unfold sieveSetup
  exact RelCT.seq first (RelCT.seq middle ((VG.Proof.Dsa.X86.checkedBlockInvariant rfl rfl).mono
    (fun _ _ h => h) fun _ _ _ => trivial))

/-- The count block before the sieve's frame. -/
abbrev countBlock : List Instr := [.mov .edx (.mem (sc bitsOff)), .alu .cmp .edx (.imm 1025), .alu .sbb .edx (.reg .edx),
  .alu .and .edx (.imm 0xFFFFFE00), .alu .add .edx (.imm 1024)]

/-- Before the sieve's frame, from the state `s₀`: the number's address and end and the count. -/
abbrev SieveIn (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (P : State → Prop) (j bits : Nat) (u : State) : Prop :=
  ∃ s₀, P s₀ ∧ Run Ex base bytes len args sp u ∧ u.gpr .eax = slotPtr base len j ∧
    u.gpr .ecx = slotPtr base len j + BitVec.ofNat 32 (bc len .wide) ∧
    u.gpr .edx = BitVec.ofNat 32 (sieveCount bits) ∧ Keeps [.eax, .ecx, .edx] s₀ u ∧ u.mem = s₀.mem ∧
    u.syms = s₀.syms

/-- Runs of the sieve of the same number of wide slot `j`, for the same `bits`, with RSA's table at
`T`. -/
theorem sieve_trace {j : Nat} (hj : j ≤ 27) (hc : ACheck (.block (bounds (.slot .wide j) ++ countBlock)))
    {T : BitVec 32} {bits c : Nat} {P : State → Prop}
    (hP : ∀ x, P x → Run Ex base bytes len args sp x ∧ Table T sp x ∧ w32 x.mem base bitsOff = bits ∧
      sv x.mem base len .wide j = c) :
    RelCT isa (Both P) (sieve (.slot .wide j)) fun _ _ => True := by
  refine relCT_of_imp (A := (sieveGeo sp (slotPtr base len j) T len bits).Valid ∧ 20 + 4 ≤ sp.toNat ∧
      (slotPtr base len j).toNat = base.toNat + lo len (.slot .wide j))
    (fun ⟨v, low, au⟩ => ?_) fun x _ h => by
      obtain ⟨R, TT, -, -⟩ := hP x h.1
      have hh := R.1
      have f := slot_fit1 hh hj
      rw [cb1] at f
      have nw := hh.scratch.nowrap
      have lw := hh.lower'
      have : 8 ≤ mw len := by simp only [mw, Spec.Rsa.modulusWords]; omega_using [lw]
      have bc8 : bc len .wide = 8 * mw len := rfl
      have au : (slotPtr base len j).toNat = base.toNat + lo len (.slot .wide j) := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [f, nw, this, bc8])]
      have v := (sieveGeo_valid hh hj (by rw [R.2.2]; exact TT) au bits).1
      rw [R.2.2] at v
      exact ⟨v, by have := hh.room.low; rw [R.2.2] at this; omega_using [this], au⟩
  unfold sieve
  refine RelCT.seq (aRel (F := SieveIn Ex base bytes len args sp P j bits) (fun x h => (hP x h).1) hc
    fun x h => ?_) ?_
  · obtain ⟨R, TT, hb, -⟩ := hP x h
    have hh := R.1
    have pre : WP isa (.block (bounds (.slot .wide j) ++ (countBlock ++ []))) x fun u' =>
        Run Ex base bytes len args sp u' ∧ u'.gpr .eax = slotPtr base len j ∧
        u'.gpr .ecx = slotPtr base len j + BitVec.ofNat 32 (bc len .wide) ∧
        u'.gpr .edx = BitVec.ofNat 32 (sieveCount bits) ∧ Keeps [.eax, .ecx, .edx] x u' ∧ u'.mem = x.mem := by
      refine bounds_ok hh hj fun u mu Ku au' cu =>
        countBlock_ok (bits := bits) (hh.regs Ku mu) (by rw [mu]; exact hb) fun u' mu' Ku' du' => WP.block_nil ?_
      have K : Keeps [.eax, .ecx, .edx] x u' := Ku.trans (Ku'.mono (by decide))
      have m : u'.mem = x.mem := by rw [mu', mu]
      have e : u.gpr .eax = slotPtr base len j := by
        apply BitVec.eq_of_toNat_eq; rw [au', au]
      exact ⟨⟨hh.regs K m, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩, by rw [Ku'.1 _ (by decide), e],
        by rw [Ku'.1 _ (by decide), cu, e], du', K, m⟩
    rw [List.append_nil] at pre
    exact VG.X86.WP.mono_syms pre fun u ⟨a, b, c, d, e, f⟩ S => ⟨x, h, a, b, c, d, e, f, S⟩
  refine RelCT.seq (relCT_frame ?_) (restoreEdi_trace fun x y ⟨x₀, y₀, ⟨⟨_, _, R₀, _⟩, ⟨_, _, R₁, _⟩⟩, ex, ey⟩ => by
    rw [ex, ey, R₀.2.2, R₁.2.2])
  have setup : ∀ a, (∃ s₁, SieveIn Ex base bytes len args sp P j bits s₁ ∧ a = allocFrame 20 s₁) →
      WP isa sieveSetup a (StateAt (sieveGeo sp (slotPtr base len j) T len bits) c 0 (sieveCount bits)) := by
    rintro a ⟨s₁, ⟨s₀, h₀, R, ea, ec, ed, K, m, Sy⟩, rfl⟩
    obtain ⟨R₀, TT, -, hc⟩ := hP s₀ h₀
    have W := sieveSetup_ok R₀.1 hj (by rw [R₀.2.2]; exact TT) au ea ec ed K m Sy
    rw [R₀.2.2, hc] at W
    exact WP.mono W fun _ h => h.1
  refine RelCT.seq ((((sieveSetup_trace (p := sp - BitVec.ofNat 32 20) (by rw [VG.X86.sub_toNat (by omega_using [low])]; omega_using [low])).mono
      (fun a b ⟨s₁, s₂, ⟨⟨_, _, R₁, _⟩, ⟨_, _, R₂, _⟩⟩, ea, eb⟩ => ⟨by rw [ea, allocFrame_esp, R₁.2.2],
        by rw [eb, allocFrame_esp, R₂.2.2]⟩) fun _ _ h => h).wp
    (F₁ := StateAt (sieveGeo sp (slotPtr base len j) T len bits) c 0 (sieveCount bits))
    (F₂ := StateAt (sieveGeo sp (slotPtr base len j) T len bits) c 0 (sieveCount bits))
    fun a b ⟨s₁, s₂, ⟨B₁, B₂⟩, ea, eb⟩ => ⟨setup a ⟨s₁, B₁, ea⟩, setup b ⟨s₂, B₂, eb⟩⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2)
    ((VG.Proof.RsaKeyGen.X86.Sieve.loop_trace v (c := c) (d := c) fun _ _ => rfl).mono (fun _ _ h => h)
      fun _ _ _ => trivial)

end VG.Proof.Ffdh.X86.Cand

end

end

/-!
# The FFDH candidate on i686: the timing of p's checks

Runs with the same tape draw the same candidate p, so its congruences, the
divisions by small primes, its sieves and its tests run alike: each branch
is on a value the candidate fixes (`main_trace`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86.Candidate

theorem congHead_check : ACheck (.block [.mov .eax (.mem (sc genOff)), .alu .cmp .eax (.imm 2)]) := by
  dsimp only [ACheck]; taint_decide
theorem gen2Head_check : ACheck (.block (lowWord (.slot .wide 9) ++ ([.alu .and .eax (.imm 7), .alu .cmp .eax (.imm 3)] : List Instr))) := by
  dsimp only [ACheck]; taint_decide
theorem minus2_check : ACheck (minus 2) := by dsimp only [ACheck]; taint_decide
theorem minus3_check : ACheck (minus 3) := by dsimp only [ACheck]; taint_decide
theorem bounds12_check : ACheck (.block (bounds (.slot .wide 12))) := by dsimp only [ACheck]; taint_decide
theorem divSetup3_check : RCheck [.esp, .eax] (.block (divSetup 3 inv3)) := by dsimp only [RCheck]; taint_decide
theorem divSetup5_check : RCheck [.esp, .eax] (.block (divSetup 5 inv5)) := by dsimp only [RCheck]; taint_decide
theorem load9_check : ACheck (load (.slot .wide 9) (one .wide) 2 3) := by dsimp only [ACheck]; taint_decide
theorem shapeB_check : ACheck (.block [.mov .eax (.mem (VG.Impl.Bignum.X86.PublicRt.argAt 0 3)), .store (sc curOff) .eax,
    .mov .eax (.mem (sc bitsOff)), .store (sc kOff) .eax]) := by dsimp only [ACheck]; taint_decide
theorem cutSetLow9_check : PCheck [.ecx, .edx] (.seq (.seq Impl.Ffdh.X86.Candidate.maskLoop <|
    .block (ptrTo (.slot .wide 9) .ebx .ecx ++ ([.alu .add .ebx (.reg .edx), .mov .ecx (.mem (at_ .ebx 0)),
      .alu .and .ecx (.reg .eax)] : List Instr) ++
      ([.mov .ebp (.reg .eax), .shift .shr .ebp 1, .alu .xor .eax (.reg .ebp), .alu .or .ecx (.reg .eax)] : List Instr) ++
      ([.store (at_ .ebx 0) .ecx] : List Instr))) (.block (setLow (.slot .wide 9)))) := by
  dsimp only [PCheck]; taint_decide
theorem testEax_check : ACheck testEax := by dsimp only [ACheck]; taint_decide
theorem half_check : ACheck half := by dsimp only [ACheck]; taint_decide
theorem oddQ_check : ACheck (.block (lowWord (.slot .wide 10) ++ ([.alu .and .eax (.imm 1)] : List Instr))) := by
  dsimp only [ACheck]; taint_decide
theorem sieveHead9_check : ACheck (.block (bounds (.slot .wide 9) ++ countBlock)) := by
  dsimp only [ACheck]; taint_decide
theorem sieveHead10_check : ACheck (.block (bounds (.slot .wide 10) ++ countBlock)) := by
  dsimp only [ACheck]; taint_decide
theorem mov0_check : ACheck (.block [.mov .eax (.imm 0)]) := by dsimp only [ACheck]; taint_decide
theorem storeOk_check : ACheck (.block [.store (sc okOff) .eax]) := by dsimp only [ACheck]; taint_decide
theorem orOk_check : ACheck (.block [.alu .or .eax (.mem (sc okOff))]) := by dsimp only [ACheck]; taint_decide

variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

theorem relCT_assoc' {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc]
          exact ⟨ht, hq⟩

/-- A cut and what follows it, which the taint analysis checks with the cut's word and bits public. -/
theorem cutThen_trace {j : Nat} {top : Bool} {k : Prog isa} (hc : PCheck [.ecx, .edx] (.seq (cutRest j top) k))
    {n : Nat} (hn1 : 1 ≤ n) {P : State → Prop}
    (hP : ∀ x, P x → Run Ex base bytes len args sp x ∧ w32 x.mem base kOff = n) :
    RelCT isa (Both P) (.seq (cut (.slot .wide j) top) k) fun _ _ => True := by
  unfold cut
  refine relCT_assoc' (RelCT.seq (aRel (F := fun v => Run Ex base bytes len args sp v ∧
      v.gpr .ecx = BitVec.ofNat 32 ((n - 1) % 32 + 1) ∧ v.gpr .edx = BitVec.ofNat 32 (4 * ((n - 1) / 32)))
    (fun x h => (hP x h).1) cutHead_check fun x h => ?_)
    (pinned_end (rs := [.ecx, .edx]) (fun _ h => h.1) (fun x y hx hy r hr => ?_) hc))
  · obtain ⟨R, hk⟩ := hP x h
    have := cutHead_ok (is := []) (Q := fun v => Run Ex base bytes len args sp v ∧
        v.gpr .ecx = BitVec.ofNat 32 ((n - 1) % 32 + 1) ∧ v.gpr .edx = BitVec.ofNat 32 (4 * ((n - 1) / 32)))
      R.1 hk hn1 fun t m K ec ed =>
      WP.block_nil ⟨⟨R.1.regs K m, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩, ec, ed⟩
    rwa [List.append_nil] at this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hx.2.1, hy.2.1]
    · rw [hx.2.2, hy.2.2]

/-- A run, and p in wide slot 9. -/
abbrev PRun (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (p : Nat) (x : State) : Prop :=
  Run Ex base bytes len args sp x ∧ sv x.mem base len .wide 9 = p

theorem minus_run {p t : Nat} (ht : t ≤ p) (htl : t < 2 ^ 32) {x : State} (R : PRun Ex base bytes len args sp p x) :
    WP isa (minus t) x (PRun Ex base bytes len args sp p) :=
  WP.mono (minus_ok R.1.1 R.2 ht htl) fun _ ⟨S, _, k⟩ => ⟨run_step R.1 S, by rw [k.slot_eq, R.2]⟩

theorem divides_run {prime inv p : Nat} (p3 : 3 ≤ prime) (p65 : prime ≤ 65537) (podd : prime % 2 = 1)
    (pinv : (prime * inv + 1) % 2 ^ 32 = 0) (invl : inv < 2 ^ 32) {x : State} (R : PRun Ex base bytes len args sp p x) :
    WP isa (divides (.slot .wide 12) prime inv) x (PRun Ex base bytes len args sp p) :=
  WP.mono (dividesS_ok R.1.1 (j := 12) (by decide) p3 p65 podd pinv invl) fun _ ⟨S, _, k⟩ =>
    ⟨run_step R.1 S, by rw [k.slot_eq, R.2]⟩

/-- p's congruences, for runs with the same p and generator. -/
theorem congruences_trace {p g : Nat} (hp3 : 3 ≤ p) {P : State → Prop}
    (hP : ∀ x, P x → PRun Ex base bytes len args sp p x ∧ w32 x.mem base genOff = g) :
    RelCT isa (Both P) congruences fun _ _ => True := by
  unfold congruences
  refine RelCT.seq (aRel (F := fun u => PRun Ex base bytes len args sp p u ∧
      isa.eval .e u = some (decide (g = 2))) (fun x h => (hP x h).1.1) congHead_check fun x h => ?_) ?_
  · obtain ⟨R, hg⟩ := hP x h
    have gl : g < 2 ^ 32 := by rw [← hg]; exact (x.mem.readW _ 32).isLt
    refine wp_movS (hdr_read R.1.1 hdr_gen) fun u₁ U₁ _ => wp_cmpi fun u₂ F₂ _ z₂ => WP.block_nil ⟨?_, ?_⟩
    · have m₂ : u₂.mem = x.mem := by rw [F₂.mem, U₁.mem]
      exact ⟨run_step R.1 (Step.regs R.1.1 m₂ (U₁.keeps.trans (F₂.keeps _))), by rw [m₂, R.2]⟩
    · show u₂.zf = _
      rw [z₂, U₁.gpr, hg, show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl, sub_beq gl (by decide)]
  refine ite_fixed (b := decide (g = 2)) (fun _ h => h.2) (fun _ => ?_) fun _ => ?_
  · unfold gen2
    refine RelCT.seq (aRel (F := fun u => PRun Ex base bytes len args sp p u ∧
        isa.eval .e u = some (decide (p % 8 = 3))) (fun x h => h.1.1) gen2Head_check fun x ⟨R, _⟩ => ?_) ?_
    · refine lowWord_ok R.1.1 (j := 9) (by decide) fun u₃ m₃ K₃ e₃ => wp_andi fun u₄ U₄ =>
        wp_cmpi fun u₅ F₅ _ z₅ => WP.block_nil ⟨?_, ?_⟩
      · have m₅ : u₅.mem = x.mem := by rw [F₅.mem, U₄.mem, m₃]
        exact ⟨run_step R.1 (Step.regs R.1.1 m₅ ((K₃.trans (U₄.keeps.mono (by decide))).trans (F₅.keeps _))),
          by rw [m₅, R.2]⟩
      · have e₄ : u₄.gpr .eax = BitVec.ofNat 32 (p % 8) := by
          rw [U₄.gpr, e₃, R.2]
          apply BitVec.eq_of_toNat_eq
          have e8 : p % 2 ^ 32 % 8 = p % 8 := Nat.mod_mod_of_dvd p (by decide)
          rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)),
            show (7 : BitVec 32).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, e8,
            Nat.mod_eq_of_lt (by omega_arith : p % 8 < 2 ^ 32)]
        show u₅.zf = _
        rw [z₅, e₄, show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl, sub_beq (by omega_arith) (by decide)]
    refine ite_fixed (b := decide (p % 8 = 3)) (fun _ h => h.2) (fun _ => ?_) fun _ => ?_
    · exact RelCT.seq (aRel (fun x h => h.1.1) minus2_check fun x h => minus_run (by omega_arith) (by decide) h.1)
        (divides_trace (by decide) bounds12_check divSetup3_check fun _ h => h.1)
    · exact aEnd (fun x h => h.1.1) mov0_check
  · unfold gen5
    refine RelCT.seq (aRel (fun x h => h.1.1) minus2_check fun x h => minus_run (by omega_arith) (by decide) h.1) ?_
    refine RelCT.seq (relCT_both (divides_trace (by decide) bounds12_check divSetup5_check fun _ h => h.1)
      fun x h => divides_run (by decide) (by decide) (by decide) (by decide) (by decide) h) ?_
    refine RelCT.seq (aRel (F := PRun Ex base bytes len args sp p) (fun x h => h.1) storeOk_check fun x R =>
      hdr_store R.1.1 hdr_ok fun t S _ k _ _ _ _ => WP.block_nil ⟨run_step R.1 S, by rw [k.slot_eq, R.2]⟩) ?_
    refine RelCT.seq (aRel (fun x h => h.1) minus3_check fun x h => minus_run (by omega_arith) (by decide) h) ?_
    refine RelCT.seq (relCT_both (divides_trace (by decide) bounds12_check divSetup5_check fun _ h => h.1)
      fun x h => divides_run (by decide) (by decide) (by decide) (by decide) (by decide) h) ?_
    exact aEnd (fun x h => h.1) orOk_check

/-- p from the tape, for runs with the same `bits`. -/
theorem shape_trace {T : List Byte} (G : TapeGeo Ex args base bytes sp T.length) (h3 : args 3 = BitVec.ofNat 32 len)
    (hL : len ≤ T.length) {bits : Nat} (hb1 : 1 ≤ bits) {P : State → Prop}
    (hP : ∀ x, P x → Run Ex base bytes len args sp x ∧ w32 x.mem base bitsOff = bits) :
    RelCT isa (Both P) shape fun _ _ => True := by
  unfold shape
  refine RelCT.seq (aRel (F := fun u => Run Ex base bytes len args sp u ∧ w32 u.mem base bitsOff = bits)
    (fun x h => (hP x h).1) load9_check fun x h => ?_) ?_
  · obtain ⟨R, hb⟩ := hP x h
    have hh := R.1
    have bl := hh.bytes_lt
    have f9 := slot_fit1 hh (j := 9) (by decide)
    have c1 := cb1 len
    have lb := len_le_bc len
    have lo' := hh.lower'
    have Gx : TapeGeo Ex args base bytes (x.gpr .esp) T.length := by rw [R.2.2]; exact G
    have fit := Gx.fit
    have small := Gx.small
    refine WP.mono (load_ok hh (one_ok .wide) f9 (p := 2) (l := 3) (L := len) (by decide) (by decide) h3
      (by omega_arith) (by omega_arith) (by omega_arith)
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
        VG.CallLay.inRegions_sub (off := 0) (Gx.rd _ _ hh.extra) (by omega_arith : 0 + len ≤ T.length) (by omega_arith))
      (Gx.apart.sub_left (Region.sub_prefix hL))) fun u ⟨_, O, K⟩ => ?_
    rw [c1] at O
    exact ⟨run_step R (Step.slot hh (by decide) O K), by rw [(kept_slot hh O).word_eq, hb]⟩
  refine RelCT.seq (aRel (F := fun u => Run Ex base bytes len args sp u ∧ w32 u.mem base kOff = bits)
    (fun x h => h.1) shapeB_check fun x ⟨R, hb⟩ => ?_) ?_
  · have h₁ := R.1
    have bl : bits < 2 ^ 32 := by rw [← hb]; exact (x.mem.readW _ 32).isLt
    refine wp_movS (h₁.arg (i := 3) (by decide)) fun u₂ U₂ _ => ?_
    refine hdr_store (h₁.regs U₂.keeps U₂.mem) hdr_cur fun u₃ S₃ W₃ k₃ O₃ g₃ _ _ => ?_
    refine wp_movS (hdr_read S₃.inp hdr_bits) fun u₄ U₄ _ => ?_
    refine hdr_store (S₃.inp.regs U₄.keeps U₄.mem) hdr_k fun u₅ S₅ W₅ k₅ O₅ _ _ _ => WP.block_nil ⟨?_, ?_⟩
    · exact run_step R ((Step.regs h₁ U₂.mem U₂.keeps).trans (S₃.trans ((Step.regs S₃.inp U₄.mem U₄.keeps).trans S₅)))
    · rw [W₅, U₄.gpr, k₃.word_eq, U₂.mem, hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bl]
  exact cutThen_trace (j := 9) (top := true) (k := .block (setLow (.slot .wide 9))) cutSetLow9_check hb1
    fun _ h => h

/-- `main`'s state: what results need, `bits`, the generator and RSA's table. -/
abbrev MAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp up : BitVec 32) (T : List Byte) (bits g : Nat) (Tb : BitVec 32) (x : State) : Prop :=
  TCtx Ex base bytes len args sp up T x ∧ w32 x.mem base bitsOff = bits ∧ w32 x.mem base genOff = g ∧ Table Tb sp x

theorem MAt.step {up Tb : BitVec 32} {T : List Byte} {bits g : Nat} {x u : State}
    (A : MAt Ex base bytes len args sp up T bits g Tb x) (G : TapeGeo Ex args base bytes sp T.length)
    (TA : Region.Disjoint ⟨Tb.setWidth 64, 8192⟩ ⟨base, bytes⟩) (S : Step Ex base bytes len args x u)
    (sy : u.syms = x.syms) (hb : w32 u.mem base bitsOff = w32 x.mem base bitsOff)
    (hg : w32 u.mem base genOff = w32 x.mem base genOff) (hu : w32 u.mem base usedOff = w32 x.mem base usedOff) :
    MAt Ex base bytes len args sp up T bits g Tb u := by
  obtain ⟨C, b, gg, TT⟩ := A
  refine ⟨C.step G S hu, by rw [hb, b], by rw [hg, gg], ?_⟩
  have := Table.step (by rw [C.1.2.2]; exact TT) S sy TA
  rwa [S.esp, C.1.2.2] at this

theorem MAt.regs {up Tb : BitVec 32} {T : List Byte} {bits g : Nat} {x u : State}
    (A : MAt Ex base bytes len args sp up T bits g Tb x) (m : u.mem = x.mem) (K : Keeps [] x u)
    (sy : u.syms = x.syms) : MAt Ex base bytes len args sp up T bits g Tb u := by
  obtain ⟨C, b, gg, TT⟩ := A
  refine ⟨C.regs m K, by rw [m, b], by rw [m, gg], ?_⟩
  refine ⟨by rw [sy]; exact TT.sym, fun i hi d hd => by rw [K.2.1, K.2.2]; exact TT.read i hi d hd,
    fun i hi => by rw [m]; exact TT.words i hi, TT.fit, TT.far⟩

/-- p in wide slot 9 and the cursor past its octets. -/
abbrev PAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp up : BitVec 32) (T : List Byte) (bits g : Nat) (Tb : BitVec 32) (p : Nat) (x : State) : Prop :=
  MAt Ex base bytes len args sp up T bits g Tb x ∧ sv x.mem base len .wide 9 = p ∧ w32 x.mem base curOff = len

/-- And q in wide slot 10. -/
abbrev QAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp up : BitVec 32) (T : List Byte) (bits g : Nat) (Tb : BitVec 32) (p : Nat) (x : State) : Prop :=
  PAt Ex base bytes len args sp up T bits g Tb p x ∧ sv x.mem base len .wide 10 = (p - 1) / 2

theorem QAt.regs {up Tb : BitVec 32} {T : List Byte} {bits g p : Nat} {x u : State}
    (A : QAt Ex base bytes len args sp up T bits g Tb p x) (m : u.mem = x.mem) (K : Keeps [] x u)
    (sy : u.syms = x.syms) : QAt Ex base bytes len args sp up T bits g Tb p u :=
  ⟨⟨A.1.1.regs m K sy, by rw [m, A.1.2.1], by rw [m, A.1.2.2]⟩, by rw [m, A.2]⟩

/-- `test eax, eax` of a flag in `eax`, with what holds through a comparison kept. -/
theorem testEax_run {Q : State → Prop} {b : Bool} (hcl : ∀ x v, Q x → v.mem = x.mem → Keeps [] x v →
    v.syms = x.syms → Q v) {x : State} (hq : Q x) (he : x.gpr .eax = BitVec.ofNat 32 b.toNat) :
    WP isa testEax x fun v => Q v ∧ isa.eval .e v = some (!b) ∧ isa.eval .ne v = some b :=
  VG.X86.WP.mono_syms (testEax_ok he) fun v ⟨m, K, z⟩ sy => ⟨hcl x v hq m K sy, z, by
    show v.zf.map (!·) = _; rw [show v.zf = _ from z]; simp⟩

/-- Runs of `main` with the same tape, `bits` and generator. -/
theorem main_trace {T : List Byte} (G : TapeGeo Ex args base bytes sp T.length) (h3 : args 3 = BitVec.ofNat 32 len)
    (hL : len ≤ T.length) {bits g : Nat} (hbl : len = (bits + 7) / 8) (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192)
    (hg25 : g = 2 ∨ g = 5) {up Tb : BitVec 32} (TA : Region.Disjoint ⟨Tb.setWidth 64, 8192⟩ ⟨base, bytes⟩) :
    RelCT isa (Both (MAt Ex base bytes len args sp up T bits g Tb)) main fun _ _ => True := by
  generalize hx : Spec.Rsa.os2ip (T.take len) = x
  obtain ⟨hpo, hpl, hpu⟩ := ParameterCandidate.candidate_shape (bits := bits) (by omega_arith) x
  obtain ⟨hbp', hbp⟩ := ParameterCandidate.candidate_bitLength (bits := bits) (by omega_arith) x
  have hbq' := ParameterCandidate.half_bitLength (bits := bits) (by omega_arith) x
  have hbqp := fun qo => ParameterCandidate.half_pred_bitLength (bits := bits) (by omega_arith) x qo
  generalize hp : Spec.Ffdh.candidateOf bits x = p at hpo hpl hpu hbp' hbp hbq' hbqp
  have big : 2 ^ 20 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have p8 : p < 2 ^ (8 * len) := Nat.lt_of_lt_of_le hpu (Nat.pow_le_pow_right (by decide) (by omega_arith))
  have hp3 : 3 ≤ p := by omega_arith
  have pcl : ∀ x v, PAt Ex base bytes len args sp up T bits g Tb p x → v.mem = x.mem → Keeps [] x v →
      v.syms = x.syms → PAt Ex base bytes len args sp up T bits g Tb p v :=
    fun x v A m K sy => ⟨A.1.regs m K sy, by rw [m, A.2.1], by rw [m, A.2.2]⟩
  unfold main
  -- p.
  refine RelCT.seq (relCT_both (F := PAt Ex base bytes len args sp up T bits g Tb p)
    (shape_trace G h3 hL (by omega_arith) fun x h => ⟨h.1.1, h.2.1⟩) fun x A => ?_) ?_
  · have C := A.1
    exact VG.X86.WP.mono_syms (shape_ok C.1.1 (by rw [C.1.2.2]; exact G) C.2.2.2 h3 hL A.2.1 hbl hb1 hb2)
      fun u ⟨S, P₁, C₁, k₁⟩ sy => ⟨A.step G TA S sy k₁.word_eq k₁.word_eq k₁.word_eq, by rw [P₁, hx, hp], C₁⟩
  -- Its congruences.
  refine RelCT.seq (relCT_both (F := fun u => PAt Ex base bytes len args sp up T bits g Tb p u ∧
      u.gpr .eax = BitVec.ofNat 32 (Spec.Ffdh.generationShape bits g p).toNat)
    (congruences_trace hp3 fun x h => ⟨⟨h.1.1.1, h.2.1⟩, h.1.2.2.1⟩) fun x A => ?_) ?_
  · exact VG.X86.WP.mono_syms (congruences_ok A.1.1.1.1 A.2.1 hp3 hpo hbp' ⟨hb1, hb2⟩ A.1.2.2.1 hg25)
      fun u ⟨S, E, k⟩ sy => ⟨⟨A.1.step G TA S sy k.word_eq k.word_eq k.word_eq, by rw [k.slot_eq, A.2.1],
        by rw [k.word_eq, A.2.2]⟩, E⟩
  refine RelCT.seq (aRel (F := fun v => PAt Ex base bytes len args sp up T bits g Tb p v ∧
      isa.eval .e v = some (!Spec.Ffdh.generationShape bits g p) ∧
      isa.eval .ne v = some (Spec.Ffdh.generationShape bits g p))
    (fun x h => h.1.1.1.1) testEax_check fun x h => testEax_run pcl h.1 h.2) ?_
  refine ite_fixed (b := !Spec.Ffdh.generationShape bits g p) (fun _ h => h.2.1)
    (fun _ => reject_trace fun x h => h.1.1.1) fun _ => ?_
  -- q, odd.
  refine RelCT.seq (aRel (F := QAt Ex base bytes len args sp up T bits g Tb p) (fun x h => h.1.1.1.1) half_check
    fun x A => ?_) ?_
  · exact VG.X86.WP.mono_syms (half_ok A.1.1.1.1.1 A.1.2.1) fun u ⟨S, Q₄, k₄⟩ sy =>
      ⟨⟨A.1.1.step G TA S sy k₄.word_eq k₄.word_eq k₄.word_eq, by rw [k₄.slot_eq, A.1.2.1], by rw [k₄.word_eq, A.1.2.2]⟩,
        by rw [Q₄]; omega_arith⟩
  refine RelCT.seq (aRel (F := fun v => QAt Ex base bytes len args sp up T bits g Tb p v ∧
      isa.eval .e v = some (decide ((p - 1) / 2 % 2 = 0))) (fun x h => h.1.1.1.1) oddQ_check fun x A => ?_) ?_
  · exact VG.X86.WP.mono_syms (oddQ_ok A.1.1.1.1.1 A.2) fun u ⟨S, m, z⟩ sy =>
      ⟨⟨⟨A.1.1.step G TA S sy (by rw [m]) (by rw [m]) (by rw [m]), by rw [m, A.1.2.1], by rw [m, A.1.2.2]⟩,
        by rw [m, A.2]⟩, z⟩
  refine ite_fixed (b := decide ((p - 1) / 2 % 2 = 0)) (fun _ h => h.2)
    (fun _ => reject_trace fun x h => h.1.1.1.1) fun e => ?_
  have qo : (p - 1) / 2 % 2 = 1 := by simp at e; omega_arith
  -- RSA's sieve of p, then of q.
  refine RelCT.seq (relCT_both (F := fun u => QAt Ex base bytes len args sp up T bits g Tb p u ∧
      u.gpr .eax = BitVec.ofNat 32 (VG.Proof.RsaKeyGen.trialPrefix p (sieveCount bits)).toNat)
    (sieve_trace (j := 9) (by decide) sieveHead9_check (c := p) fun x h =>
      ⟨h.1.1.1.1.1, h.1.1.1.2.2.2, h.1.1.1.2.1, h.1.1.2.1⟩) fun x A => ?_) ?_
  · exact VG.X86.WP.mono_syms (sieveS_ok A.1.1.1.1.1.1 (j := 9) (by decide) (by rw [A.1.1.1.1.1.2.2]; exact A.1.1.1.2.2.2)
      A.1.1.1.2.1) fun u ⟨S, E, k⟩ sy => ⟨⟨⟨A.1.1.1.step G TA S sy k.word_eq k.word_eq k.word_eq,
        by rw [k.slot_eq, A.1.1.2.1], by rw [k.word_eq, A.1.1.2.2]⟩, by rw [k.slot_eq, A.1.2]⟩, by rw [E, A.1.1.2.1]⟩
  refine RelCT.seq (aRel (F := fun v => QAt Ex base bytes len args sp up T bits g Tb p v ∧
      isa.eval .e v = some (!VG.Proof.RsaKeyGen.trialPrefix p (sieveCount bits)) ∧
      isa.eval .ne v = some (VG.Proof.RsaKeyGen.trialPrefix p (sieveCount bits)))
    (fun x h => h.1.1.1.1.1) testEax_check fun x h => testEax_run (fun x v A m K sy => A.regs m K sy) h.1 h.2) ?_
  refine ite_fixed (b := VG.Proof.RsaKeyGen.trialPrefix p (sieveCount bits)) (fun _ h => h.2.2)
    (fun _ => reject_trace fun x h => h.1.1.1.1) fun _ => ?_
  refine RelCT.seq (relCT_both (F := fun u => QAt Ex base bytes len args sp up T bits g Tb p u ∧
      u.gpr .eax = BitVec.ofNat 32 (VG.Proof.RsaKeyGen.trialPrefix ((p - 1) / 2) (sieveCount bits)).toNat)
    (sieve_trace (j := 10) (by decide) sieveHead10_check (c := (p - 1) / 2) fun x h =>
      ⟨h.1.1.1.1.1, h.1.1.1.2.2.2, h.1.1.1.2.1, h.1.2⟩) fun x A => ?_) ?_
  · exact VG.X86.WP.mono_syms (sieveS_ok A.1.1.1.1.1.1 (j := 10) (by decide) (by rw [A.1.1.1.1.1.2.2]; exact A.1.1.1.2.2.2)
      A.1.1.1.2.1) fun u ⟨S, E, k⟩ sy => ⟨⟨⟨A.1.1.1.step G TA S sy k.word_eq k.word_eq k.word_eq,
        by rw [k.slot_eq, A.1.1.2.1], by rw [k.word_eq, A.1.1.2.2]⟩, by rw [k.slot_eq, A.1.2]⟩, by rw [E, A.1.2]⟩
  refine RelCT.seq (aRel (F := fun v => QAt Ex base bytes len args sp up T bits g Tb p v ∧
      isa.eval .e v = some (!VG.Proof.RsaKeyGen.trialPrefix ((p - 1) / 2) (sieveCount bits)) ∧
      isa.eval .ne v = some (VG.Proof.RsaKeyGen.trialPrefix ((p - 1) / 2) (sieveCount bits)))
    (fun x h => h.1.1.1.1.1) testEax_check fun x h => testEax_run (fun x v A m K sy => A.regs m K sy) h.1 h.2) ?_
  refine ite_fixed (b := VG.Proof.RsaKeyGen.trialPrefix ((p - 1) / 2) (sieveCount bits)) (fun _ h => h.2.2)
    (fun _ => reject_trace fun x h => h.1.1.1.1) fun _ => ?_
  -- The tests.
  have get : ∀ {x : State}, QAt Ex base bytes len args sp up T bits g Tb p x →
      TestsAt Ex base bytes len args sp up T bits p ((p - 1) / 2) len x :=
    fun h => ⟨h.1.1.1, h.1.1.2.1, h.1.2.1, h.2, h.1.2.2⟩
  exact (tests_trace G hb1 hb2 hp3 hpo (by omega_arith) qo hbp (hbqp qo) p8 hL).mono
    (fun x y h => ⟨get h.1.1, get h.2.1⟩)
    fun _ _ h => h

end VG.Proof.Ffdh.X86.Cand

end

end

/-!
# `vg_ffdh_parameter_candidate_sieved` on i686 in constant time

Runs with the same public arguments, table and tape take the same branch on
whether the tape is long enough, and then run `main` alike (`body_trace`);
the frame around the body is `wrap`'s (`constantTime`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86.Candidate
open VG.Impl.Bignum.X86.PublicRt (argAt)

theorem fill_check :
    (VG.Taint.check taint (τr [.esp]) (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.Candidate.args)) (.block [])).isSome =
      true := by
  taint_decide
theorem bodyHead_check : ACheck (.block (entryWords ++ ([.mov .eax (.mem (argAt 0 12)), .alu .cmp .eax (.mem (argAt 0 3))] : List Instr))) := by
  dsimp only [ACheck]; taint_decide

variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- Runs of the body with the same tape, `bits`, generator, `used` and table. -/
theorem body_trace {T : List Byte} {up Tb : BitVec 32} {bits g : Nat} (hbl : len = (bits + 7) / 8)
    (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hg25 : g = 2 ∨ g = 5) :
    RelCT isa (Both fun f => Run Ex base bytes len args sp f ∧ Facts Ex base bytes len args sp T up Tb bits g f)
      Impl.Ffdh.X86.Candidate.body fun _ _ => True := by
  refine relCT_of_imp (A := TapeGeo Ex args base bytes sp T.length ∧ args 3 = BitVec.ofNat 32 len ∧
      Region.Disjoint ⟨Tb.setWidth 64, 8192⟩ ⟨base, bytes⟩) (fun ⟨G, h3, TA⟩ => ?_)
    fun x _ h => ⟨h.1.2.G, h.1.2.h3, h.1.2.TA⟩
  unfold Impl.Ffdh.X86.Candidate.body
  refine RelCT.seq (aRel (F := fun u => MAt Ex base bytes len args sp up T bits g Tb u ∧
      u.cf = some (decide (T.length < len))) (fun x h => h.1) bodyHead_check fun x ⟨R, F⟩ => ?_) ?_
  · have Gx : TapeGeo Ex args base bytes (x.gpr .esp) T.length := by rw [R.2.2]; exact G
    exact VG.X86.WP.mono_syms (bodyHead_ok R.1 G.len G.small h3 F.rb F.rg F.ru F.dws (by rw [R.2.2]; exact F.d40)
      hb2 hg25) fun u ⟨S, B, Gn, Us, _, c⟩ sy => by
        refine ⟨⟨⟨run_step R S, F.Ox.keep rfl S.keeps, Us, by rw [tape_keep Gx S, F.hT]⟩, B, Gn, ?_⟩, c⟩
        have := Table.step (by rw [R.2.2]; exact F.TT) S sy TA
        rwa [S.esp, R.2.2] at this
  refine ite_fixed (b := decide (T.length < len)) (fun _ h => h.2)
    (fun _ => short_trace fun x h => h.1.1) fun e => ?_
  have hL : len ≤ T.length := by simp at e; omega_using [e]
  exact (main_trace G h3 hL hbl hb1 hb2 hg25 TA).mono (fun x y h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h

/-! ## Against the contract -/

open VG.Proof.Ffdh.X86.KeyGen
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)

theorem pub_facts {s t : State} (H : contract.pub s t) :
    s.gpr .esp = t.gpr .esp ∧ (∀ i < 9, arg s i = arg t i) ∧
      s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol ∧
      entryRand s = entryRand t := by
  sig_pub [contract, Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argSlots,
    argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at H
  obtain ⟨SP, sy, L, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := H
  have inj : ∀ {l l' : List Byte}, l.map (fun x => x.toNat) = l'.map (fun x => x.toNat) → l = l' :=
    fun h => (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp h
  refine ⟨SP, fun i hi => ?_, sy, inj L⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by omega_using [hi])
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a0
  · exact a1
  · exact a2
  · exact a3
  · exact a4
  · exact a5
  · exact a6
  · exact a7
  · exact a8

/-- What the body may read and write, once only the working space, `out` and `used` are writable. -/
theorem narrowRd {s : State} {rd wr : List Region} (h : Rd s rd wr) (w : Region) :
    Rd s (rd ++ wr) [w, outR s, usedR s] :=
  let ⟨⟨r₁, h₁, c₁⟩, _, _, ⟨r₄, h₄, c₄⟩, ⟨r₅, h₅, c₅⟩⟩ := h
  ⟨⟨r₁, List.mem_append_left _ h₁, c₁⟩, ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
    ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), Region.contains_self _ _⟩,
    ⟨r₄, List.mem_append_left _ h₄, c₄⟩, ⟨r₅, List.mem_append_left _ h₅, c₅⟩⟩

/-- The body's narrowed state, run from the frame's: a run with what the body needs. -/
theorem narrowed_facts {s f : State} (A : CandABI s) (Bf : BodyAt (Rd s) Impl.Ffdh.X86.Candidate.args s f)
    (sy : f.syms = s.syms) :
    Run (Rd s) (wsBase Impl.Ffdh.X86.Candidate.args s) (wsSize Impl.Ffdh.X86.Candidate.args s)
        (pLenOf Impl.Ffdh.X86.Candidate.args s) (synth Impl.Ffdh.X86.Candidate.args (arg s))
        (s.gpr .esp - BitVec.ofNat 32 argsFrame)
        (narrowed (wsBase Impl.Ffdh.X86.Candidate.args s) (wsSize Impl.Ffdh.X86.Candidate.args s) f
          [outR s, usedR s]) ∧
      Facts (Rd s) (wsBase Impl.Ffdh.X86.Candidate.args s) (wsSize Impl.Ffdh.X86.Candidate.args s)
        (pLenOf Impl.Ffdh.X86.Candidate.args s) (synth Impl.Ffdh.X86.Candidate.args (arg s))
        (s.gpr .esp - BitVec.ofNat 32 argsFrame) (entryRand s) (arg s 2)
        (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) (arg s 3).toNat (arg s 4).toNat
        (narrowed (wsBase Impl.Ffdh.X86.Candidate.args s) (wsSize Impl.Ffdh.X86.Candidate.args s) f
          [outR s, usedR s]) := by
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega_using [low, st'])
  have sub : Region.Sub ⟨frameAt s, argsFrame⟩ (belowR s) := by
    rw [FA]; exact Offset.sub_below _ (by decide) (by decide)
  have I := VG.Proof.Ffdh.X86.In.narrow Bf.1 (narrowRd Bf.1.extra
    ⟨wsBase Impl.Ffdh.X86.Candidate.args s, wsSize Impl.Ffdh.X86.Candidate.args s⟩)
  refine ⟨⟨I, Bf.argsOk (wrapABI A) (Out := [outR s, usedR s]) fun r hr => ?_, Bf.2.1⟩,
    frame_facts A _ I Bf.2.1 Bf.2.2.2.2 sy⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact A.belowOut.sub_left sub
  · exact A.belowUsed.sub_left sub

theorem constantTime : ConstantTime isa contract.pre contract.pub Impl.Ffdh.X86.Candidate.code := by
  intro s t tr ur sf tf S T H E F
  have A := candABI_of S
  have B := candABI_of T
  obtain ⟨SP, args, sy, tape⟩ := pub_facts H
  have hws : wsBase Impl.Ffdh.X86.Candidate.args s = wsBase Impl.Ffdh.X86.Candidate.args t := by
    show (arg s 7).setWidth 64 = (arg t 7).setWidth 64
    rw [args 7 (by decide)]
  have hwz : wsSize Impl.Ffdh.X86.Candidate.args s = wsSize Impl.Ffdh.X86.Candidate.args t := by
    show (arg s 8).toNat * 8 = (arg t 8).toNat * 8
    rw [args 8 (by decide)]
  have hpl : pLenOf Impl.Ffdh.X86.Candidate.args s = pLenOf Impl.Ffdh.X86.Candidate.args t := by
    show (arg s 1).toNat = (arg t 1).toNat
    rw [args 1 (by decide)]
  have hsy : synth Impl.Ffdh.X86.Candidate.args (arg t) = synth Impl.Ffdh.X86.Candidate.args (arg s) :=
    synth_congr (wrapABI A).below fun i hi => (args i hi).symm
  have hout : outR t = outR s := by
    show (⟨(arg t 0).setWidth 64, (arg t 1).toNat⟩ : Region) = ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    rw [args 0 (by decide), args 1 (by decide)]
  have hused : usedR t = usedR s := by
    show (⟨(arg t 2).setWidth 64, 8⟩ : Region) = ⟨(arg s 2).setWidth 64, 8⟩
    rw [args 2 (by decide)]
  have hRd : Rd t = Rd s := by
    show (fun rd wr => InRegions (rd ++ wr) ((arg t 5).setWidth 64) (arg t 6).toNat ∧
        InRegions wr ((arg t 0).setWidth 64) (arg t 1).toNat ∧ InRegions wr ((arg t 2).setWidth 64) 8 ∧
        InRegions (rd ++ wr) (argAddr t 0) 36 ∧
        InRegions (rd ++ wr) ((t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64) 8192) =
      fun rd wr => InRegions (rd ++ wr) ((arg s 5).setWidth 64) (arg s 6).toNat ∧
        InRegions wr ((arg s 0).setWidth 64) (arg s 1).toNat ∧ InRegions wr ((arg s 2).setWidth 64) 8 ∧
        InRegions (rd ++ wr) (argAddr s 0) 36 ∧
        InRegions (rd ++ wr) ((s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64) 8192
    rw [args 0 (by decide), args 1 (by decide), args 2 (by decide), args 5 (by decide), args 6 (by decide), sy,
      show argAddr t 0 = argAddr s 0 by simp only [argAddr, SP]]
  have ho : ∀ {x f : State}, CandABI x → BodyAt (Rd x) Impl.Ffdh.X86.Candidate.args x f →
      ∀ r ∈ [outR x, usedR x], r ∈ f.wr := fun X Bf r hr => by
    rw [Bf.2.2.2.1, X.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hw : ∀ {x f : State} (X : CandABI x) (Bf : BodyAt (Rd x) Impl.Ffdh.X86.Candidate.args x f),
      f.syms = x.syms → ∃ F, WP isa Impl.Ffdh.X86.Candidate.body
        (narrowed (wsBase Impl.Ffdh.X86.Candidate.args x) (wsSize Impl.Ffdh.X86.Candidate.args x) f
          [outR x, usedR x]) F := fun X Bf y => by
    obtain ⟨R, Fc⟩ := narrowed_facts X Bf y
    exact ⟨_, frame_ok X _ R.1 Bf.2.1 Bf.2.2.2.2 y⟩
  refine wrap_trace_syms (wrapABI A) (wrapABI B) args SP (rd_of A) (rd_of B) fill_check
    (fun f Bf y => WP.mono (frame_ok A f Bf.1 Bf.2.1 Bf.2.2.2.2 y) fun _ h => h.2.2)
    (fun f Bf y => WP.mono (frame_ok B f Bf.1 Bf.2.1 Bf.2.2.2.2 y) fun _ h => h.2.2) ?_ E F
  refine VG.Proof.Bignum.X86.PublicRt.relCT_narrow (fun f => f.rd ++ f.wr)
    (fun _ => ⟨wsBase Impl.Ffdh.X86.Candidate.args s, wsSize Impl.Ffdh.X86.Candidate.args s⟩ ::
      [outR s, usedR s]) (fun f g ⟨⟨B₁, y₁⟩, ⟨B₂, y₂⟩⟩ => ?_)
    (body_trace (Ex := Rd s) (base := wsBase Impl.Ffdh.X86.Candidate.args s)
      (bytes := wsSize Impl.Ffdh.X86.Candidate.args s) (args := synth Impl.Ffdh.X86.Candidate.args (arg s))
      (sp := s.gpr .esp - BitVec.ofNat 32 argsFrame) (T := entryRand s) (up := arg s 2)
      (Tb := s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) (hbl := A.outLen) A.bitsLow A.bitsHigh A.gen)
  have c₁ := B₁.covers (ho A B₁)
  have c₂ := B₂.covers (ho B B₂)
  have w₂ := hw B B₂ y₂
  have D₂ := narrowed_facts B B₂ y₂
  rw [← hws, ← hwz, hout, hused] at c₂ w₂ D₂
  rw [hRd, ← hpl, hsy, ← SP, ← tape, ← args 2 (by decide), ← args 3 (by decide), ← args 4 (by decide), ← sy] at D₂
  exact ⟨c₁.1, c₁.2, c₂.1, c₂.2, hw A B₁ y₁, w₂, narrowed_facts A B₁ y₁, D₂⟩

end VG.Proof.Ffdh.X86.Cand

end

end

/-! # `vg_ffdh_parameter_candidate_sieved` on i686, verified -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86

def satArgument : Nat → BitVec 32
  | 0 => 0x1000
  | 1 => 64
  | 2 => 0x2000
  | 3 => 512
  | 4 => 2
  | 5 => 0x3000
  | 6 => 0
  | 7 => 0x10000
  | _ => 1056

def satMemory : Mem := fun a =>
  if (a - 0x20004).toNat < 36 then
    (satArgument ((a - 0x20004).toNat / 4)).extractLsb' (8 * ((a - 0x20004).toNat % 4)) 8
  else constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed a

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemory
  rd := [⟨0x3000, 0⟩, ⟨0x30000, 8192⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 8⟩, ⟨0x10000, 8448⟩, ⟨0x20004, 36⟩]
  syms _ := 0x30000

theorem sat_arguments (i : Nat) (index : i < 9) : arg satState i = satArgument i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega_using [index]
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem single_held {m : Mem} {f : String → Addr} {name : String} {words : List (BitVec 64)}
    (H : ∀ i < words.length, m.readW (f name + BitVec.ofNat 64 (8 * i)) 64 = words.getD i 0) :
    Abi.constsHeld m f [(name, words)] := by
  intro c mem
  obtain rfl := List.mem_singleton.mp mem
  exact H

private theorem packed_regions (f : String → Addr) :
    Abi.constRegions f [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] =
      [⟨f VG.Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩] := by
  rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length]

theorem sat_table : Abi.constsHeld satState.mem (fun name => (satState.syms name).setWidth 64)
    VG.Impl.RsaKeyGen.TrialTable32.consts := by
  apply single_held
  intro i index
  have fit : 8 * VG.Impl.RsaKeyGen.TrialTable32.packed.length ≤ 2 ^ 64 := by
    rw [VG.Proof.RsaKeyGen.X86.Candidate.packed_length]; decide
  have small : i < 1024 := by simpa only [VG.Proof.RsaKeyGen.X86.Candidate.packed_length] using index
  have ix : i < VG.Impl.RsaKeyGen.TrialTable32.packed.length := by
    rw [VG.Proof.RsaKeyGen.X86.Candidate.packed_length]; exact small
  change satMemory.readW (0x30000#64 + BitVec.ofNat 64 (8 * i)) 64 = VG.Impl.RsaKeyGen.TrialTable32.packed.getD i 0
  have held := constMem_held 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed fit i ix
  refine Eq.trans (Mem.readW_congr (m := satMemory) (m' := constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed) ?_) held
  intro j bound
  have address : ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat =
      65532 + 8 * i + j := by
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [small, bound]
  change (if _ then _ else _) = _
  apply ite_eq_right
  intro inside
  exfalso
  apply (show ¬ ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat < 36 from by
    change ¬ ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat < 36
    rw [address]
    omega_using []) inside

theorem satisfiable : ∃ s, contract.pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [contract, Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow]
  simp only [sat_arguments 0 (by decide), sat_arguments 1 (by decide), sat_arguments 2 (by decide),
    sat_arguments 3 (by decide), sat_arguments 4 (by decide), sat_arguments 5 (by decide),
    sat_arguments 6 (by decide), sat_arguments 7 (by decide), sat_arguments 8 (by decide)]
  simp only [packed_regions, List.forall_mem_singleton]
  sig_and_intros
  all_goals first
    | exact sat_table
    | rfl
    | decide +kernel
    | exact Region.disjoint_of_sep (by decide +kernel)
    | (unfold Spec.Rsa.scratchWords; decide +kernel)

theorem verified : Verified target Impl.Ffdh.X86.Candidate.code contract :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Ffdh.X86.Cand
