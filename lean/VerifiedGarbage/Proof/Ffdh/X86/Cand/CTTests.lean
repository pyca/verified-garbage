module

public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Tests
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTPhase
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
meta import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTBase
meta import VerifiedGarbage.Impl.Ffdh.X86.Candidate
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega

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
theorem words1_check : ACheck (.block (phaseWords 0 0 ++ [.mov .eax (.imm 1), .store (sc cntOff) .eax])) := by
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
    RelCT isa (Both P) (.block ([i] ++ storeUsed ++ [.mov .eax (.imm r)])) fun _ _ => True := by
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
  exact congrArg some (sub_beq (by omega) (by omega))

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
    {j w n c : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 10) (hck : ACheck (prepHead j)) (hw3 : 3 ≤ w) (hodd : w % 2 = 1)
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
  have e : T.length - r.length = c' := by rw [← hr, List.length_drop]; omega
  exact ⟨⟨C, by rw [k.word_eq, hb], by rw [k.slot_eq, hp], by rw [k.slot_eq, hq], by rw [e, hc']⟩, by omega⟩

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
  have pc : ∀ b, 1 ≤ Spec.Ffdh.primeChecks b - 1 := fun b => by unfold Spec.Ffdh.primeChecks; split <;> omega
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
  refine phasePass_trace G (by decide) (by decide) prepHead10_check hq3 hqo (by have := pc (bits - 1); omega) (by omega)
    (fun x h => ⟨h.1.1, h.1.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2, h.1.2.2.2.2⟩) fun e₂ => ?_
  obtain ⟨r₂, hD₂⟩ := drawStatus_one e₂
  -- The rest of p's.
  refine RelCT.seq (aRel (F := StageAt Ex base bytes len args sp up T bits p q p
      (Spec.Ffdh.primeChecks (bits - 0) - 1) (T.length - r₂.length)) (fun x h => h.1.2.1.1)
    words3_check fun x h => stageWords_ok G (h.tests hD₂).1 (by decide) (by decide) hb1 hb2 hbp) ?_
  refine phasePass_trace G (by decide) (by decide) prepHead9_check hp3 hpo (pc _) (by omega)
    (fun x h => ⟨h.1.1, h.1.2.2.1, h.2.1, h.2.2.1, h.2.2.2, h.1.2.2.2.2⟩) fun e₃ => ?_
  obtain ⟨r₃, hD₃⟩ := drawStatus_one e₃
  exact accept_trace fun x h => by
    obtain ⟨A, -⟩ := h.tests hD₃
    exact ⟨A.1, by rw [A.2.2.1]; exact hpl⟩

end VG.Proof.Ffdh.X86.Cand
