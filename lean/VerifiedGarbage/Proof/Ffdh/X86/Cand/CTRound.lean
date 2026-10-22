module

public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Round
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTBase
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.WindowPower
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.StageR
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Coefficient
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeTable
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Impl.Ffdh.X86.Candidate
import VerifiedGarbage.Proof.Framework.Omega

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
  · rw [R.2.r2]; exact Nat.mod_lt _ (by omega)

/-- A copy into slot 5 to 8 keeps the modulus prepared. -/
theorem copyRP_ok {w : Nat} {x : State} (R : RP Ex base bytes len args sp w x) {j d : Nat} (hj9 : 9 ≤ j)
    (hj : j ≤ 17) (hd5 : 5 ≤ d) (hd : d ≤ 8) :
    WP isa (copy (.slot .wide j) (.slot .wide d) (one .wide)) x (RP Ex base bytes len args sp w) := by
  have h := R.1.1
  have f := h.slot_fit .wide (j := d) (by omega)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  refine WP.mono (copyDown_ok h hj9 hj (by omega)) fun u ⟨O, _, K⟩ => ⟨R.1.keep K (O.mono (Nat.zero_le _) (by omega)), ?_⟩
  exact R.2.keep (R.2.toReady.slot (a := d) hd5 (by omega) K (by decide) (by decide) O) (kept_slot h O) (by decide)
    ⟨by simp; omega, by simp; omega, by simp; omega⟩

/-- A power, with the modulus still prepared. -/
theorem powerRP_ok {w : Nat} {x : State} (R : RP Ex base bytes len args sp w x) :
    WP isa (windowPower .wide) x fun u => RP Ex base bytes len args sp w u ∧ sv u.mem base len .wide 6 < w := by
  have h := R.1.1
  have hM := R.2.ctx.gt
  refine WP.mono (windowPower_ok R.2.ctx R.2.one R.2.r2) fun u ⟨C, F, K, Y⟩ => ?_
  have G := stR_widen F (pwR_in h .wide 0)
  refine ⟨⟨⟨C.inp, R.1.2.1.keep K, (K.1 _ (by decide)).trans R.1.2.2⟩,
    R.2.keep ⟨C, by rw [pwR_sv3 h F h.room, R.2.one], by rw [pwR_sv4 h F h.room, R.2.r2]⟩
      (kept_ops h G h.room) (by decide)⟩, by rw [Y]; exact Nat.mod_lt _ (by omega)⟩

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
  exact O.val32 (.inr (by rcases hd.1 with e | e <;> omega)) (by omega)

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
      (by rw [Q.1.2.r2]; exact Nat.mod_lt _ (by have := Q.1.2.ctx.gt; omega)))
      fun u ⟨R, h6, k⟩ => Q.kept R h6 k) ?_
  refine VG.RelCT.seq (aRel (F := fun u => SQ Ex base bytes len args sp w sn j u ∧ ∃ c, u.gpr .ecx = cmask c)
    (fun _ Q => Q.1.1) eq615_check fun x Q =>
      WP.mono (eqW_ok Q.1.1.1 (a := 6) (b := 15) (by decide) (by decide)) fun u ⟨m, e, K⟩ =>
        ⟨Q.kept (Q.1.regs K m) (by rw [m]; exact Q.2.1) (by rw [m]; exact Kept.refl _), _, e⟩) ?_
  refine aRel (fun _ Q => Q.1.1.1) tallyJ_check fun x ⟨Q, c, e⟩ => ?_
  obtain ⟨old, ho⟩ := Q.2.2.1
  refine WP.mono (tally_ok Q.1.2 hdr_j (by decide) Q.2.2.2 (by omega) ho e) fun u ⟨S, P, H, J, Z, k, s6⟩ => ?_
  refine ⟨⟨⟨run_step Q.1.1 S, P⟩, by rw [s6]; exact Q.2.1, ⟨_, H⟩, by rw [J]; omega⟩, by rw [Z]; congr 1; exact decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩⟩

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
  have hN : 0 < sn - 1 := by simp at e; omega
  exact (relCT_countLoop hN (SQ Ex base bytes len args sp w sn) fun j hj => squareStep_trace hj).mono
    (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ _ => trivial

end VG.Proof.Ffdh.X86.Cand
