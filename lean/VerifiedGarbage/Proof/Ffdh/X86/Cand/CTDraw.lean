module

public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Draw
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTBase
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTRound
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
meta import VerifiedGarbage.Impl.Ffdh.X86.Candidate
meta import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTBase
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega

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
theorem cutRest9_check : PCheck [.ecx, .edx] (cutRest 9 true) := by dsimp only [PCheck]; taint_decide

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
  · obtain ⟨n₁, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
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
    WP.mono (drawHead_ok (Gs R) (by have := bc_le A.step.inp.upper' .wide; omega) A hc) fun v ⟨A', e⟩ => ⟨⟨s₀, R, A'⟩, by rw [e, hoo]⟩)
    (RelCT.seq (Q := fun _ _ => True) (R := Both (Run Ex base bytes len args sp)) ?_
      (aEnd (fun _ h => h) drawFin_check))
  refine ite_fixed (b := decide (T.length - c < o)) (fun _ h => h.2) (fun _ => ?_) fun e => ?_
  · exact aRel (fun _ h => h.1.run) setSt3_check fun x ⟨⟨s₀, R, A⟩, _⟩ =>
      WP.mono (setSt_ok (Gs R) A.toMid (r := 3) (by decide)) fun u ⟨M, _⟩ => run_step R M.step
  have co : c + o ≤ T.length := by simp at e; omega
  let Φ : State → Prop := fun u => PickRun Ex base bytes len args sp w T n c u ∧
    isa.eval .e u = some (!drawRange w T c)
  -- The witness's octets.
  refine RelCT.seq (relCT_both (F := fun v => Run Ex base bytes len args sp v ∧ w32 v.mem base kOff = k ∧
      sv v.mem base len .wide 13 < 2 ^ (32 * ((k - 1) / 32 + 1)) ∧
      WP isa (.seq (cut (.slot .wide 13) false) (.seq (Impl.Ffdh.X86.rangeMask 13) Impl.Ffdh.X86.testMask)) v Φ)
    (drawLoad_trace (c := c) (o := o) (by omega) fun x ⟨⟨_, R, A⟩, _⟩ =>
      ⟨run_step R A.step, A.cur, by rw [A.oct, hoo]⟩) fun x ⟨⟨s₀, R, A⟩, _⟩ => ?_) ?_
  · have Gx : TapeGeo Ex args base bytes (x.gpr .esp) T.length := by rw [A.step.esp]; exact Gs R
    have l := VG.Proof.Bignum.os2ip_lt ((T.drop c).take o)
    rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega), VG.Proof.Bignum.pow256_eq] at l
    have W₁ : WP isa drawLoad x fun u => Run Ex base bytes len args sp u ∧ w32 u.mem base kOff = k ∧
        sv u.mem base len .wide 13 < 2 ^ (32 * ((k - 1) / 32 + 1)) :=
      WP.mono (drawLoad_ok A.prep Gx A.tape A.cur (by rw [A.oct, hoo]) (by omega) co
        (by have := bc_le A.step.inp.upper' .wide; omega)) fun u ⟨S, _, V, _, k₁⟩ =>
        ⟨run_step (run_step R A.step) S, by rw [k₁.word_eq, A.bits, hk],
          by rw [V]; exact Nat.lt_of_lt_of_le l (Nat.pow_le_pow_right (by decide) (by omega))⟩
    have W₂ : WP isa drawLoad x fun u => WP isa (.seq (cut (.slot .wide 13) false)
        (.seq (Impl.Ffdh.X86.rangeMask 13) Impl.Ffdh.X86.testMask)) u Φ :=
      WP.mono (WP.seq_iff.mp (drawPick_ok (Gs R) hw3 hwl A (by rw [hoo]; exact co))) fun u h =>
        WP.mono h fun v ⟨P, e⟩ => ⟨⟨s₀, R, P⟩, e⟩
    exact WP.mono (wp_and W₁ W₂) fun u ⟨⟨a, b, c'⟩, d⟩ => ⟨a, b, c', d⟩
  -- Cut to the bits of `w − 1`.
  refine RelCT.seq (relCT_both (F := fun v => Run Ex base bytes len args sp v ∧
      WP isa (.seq (Impl.Ffdh.X86.rangeMask 13) Impl.Ffdh.X86.testMask) v Φ)
    (cut_trace cutRest13_check (k := k) (by omega) fun _ h => ⟨h.1, h.2.1⟩) fun x ⟨R, hk', sm, hW⟩ =>
      wp_and (WP.mono (cut_ok R.1 (j := 13) (by decide) false hk' (by omega) kw sm) fun u ⟨h, _, _, K⟩ =>
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
