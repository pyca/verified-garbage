module

import VerifiedGarbage.Proof.Ffdh.X86.Cand.Phase
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTDraw
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
meta import VerifiedGarbage.Impl.Ffdh.X86.Candidate
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Draw

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
      copyDown_run hj9 (by omega) (by decide) (hP x h).1)
      (RelCT.seq (prepare_relCT .wide) (RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2) hc.2))
  refine RelCT.seq (relCT_both (F := HalvRun Ex base bytes len args sp w 0) trace fun x h =>
    WP.mono (prepHead_ok (hP x h).1.1 hj9 hj (hP x h).2 hw3 hodd) fun v H => ⟨x, (hP x h).1, H⟩) ?_
  refine (RelCT.loop (I := fun m x y => ∃ k, m = (w - 1) / 2 ^ k ∧ m % 2 = 0 ∧ 0 < m ∧
      HalvRun Ex base bytes len args sp w k x ∧ HalvRun Ex base bytes len args sp w k y) (fun m => ?_) (w - 1)).mono
    (fun x y h => ⟨0, by simp, by omega, by omega, h.1, h.2⟩) fun _ _ h => h
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
    exact ⟨m / 2, by omega, k + 1, half.symm, by rw [← half]; exact ev, by omega, Hx, Hy⟩

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
        fun _ => ⟨T.length - (c + o), by omega, drawN w n T c, c + o, rfl, h1, h3, Dx, Dy⟩⟩
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
    omega
  unfold phase
  refine RelCT.assoc (RelCT.seq (relCT_both (F := DrawRun Ex base bytes len args sp w T n c)
    (RelCT.seq (prepPhase_trace hj9 hj hck hw3 hodd fun x h => ⟨(hP x h).1, (hP x h).2.2.1⟩)
      (aEnd (fun _ h => h) setSt0_check)) fun x h => ?_)
    (RelCT.seq (drawLoop_trace G hw3 hodd hwl hn1 hcT) (aEnd (fun _ h => h) readSt_check)))
  obtain ⟨R, hT, hw, ho, hk, hn, hc⟩ := hP x h
  exact WP.mono (phaseStart_ok R.1 (by rw [R.2.2]; exact G) hT hj9 hj hw hw3 hodd ho hk hn hc) fun u ⟨S, A, _⟩ =>
    ⟨u, run_step R S, A⟩

end VG.Proof.Ffdh.X86.Cand
