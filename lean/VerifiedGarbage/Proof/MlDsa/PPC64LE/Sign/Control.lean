module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Inv
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.StepsCT
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Samp
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.CallS
public import VerifiedGarbage.Proof.MlDsa.Sign.Leak
import VerifiedGarbage.Proof.MlDsa.Sign.Setup
import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.ContractsV
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-DSA signing on PPC64LE: the primitives, two runs, and the branches on the result

What the proofs need of the implementations of the primitives (`SPrimsOk`):
verified with at most `S` bytes of stack, and, as on 32-bit ARM
(`Proof/MlDsa/Arm/Sign/Prims.lean`), for the two samplers whose results the
function branches on, that the result is a function of their public data
(`RetPub`) and that they succeed only if the sampling finishes within
`maxBounds`. A call of such a sampler gives the same result in two runs
(`callVRet_tr`). Then: `ρ` is public (`pub_rho`); two runs with the same
layout (`STwo1`, `STwo2`) and the constant time of a piece without calls by
the taint analysis from the pointers; and `ifOkElse t e`, a branch on the
result in `r24` (`ifOkElse_piece`), which is a function of the public data.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv taint31 taint4
  Regs2 Callee CallRel glueOk glueSt glue_ok glueSt_rd glueSt_wr glue_noMem)
open VG.Impl.MlDsa.PPC64LE.KeyGen (callAt)
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The primitives -/

/-- The result of `c` (the low word of `r3`) is the same in two runs from
states that satisfy `k.pre` and agree on `k.pub`. -/
def RetPub (k : Contract isa) (c : Prog isa) : Prop :=
  RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c
    fun s₁ s₂ => (s₁.gpr .r3).setWidth 32 = (s₂.gpr .r3).setWidth 32

/-- What the proofs need of the implementations `P` of the primitives: each
verified against its contract with at most `S` bytes of stack, and the facts
about the two samplers the function branches on. -/
structure SPrimsOk (P : Prims) (S : Nat) : Prop where
  ntt : Callee P.ntt (fun stk => nttContract PPC64LE.abi stk) S
  invNtt : Callee P.invNtt (fun stk => nttInvContract PPC64LE.abi stk) S
  mul : Callee P.mul (fun stk => mulContract PPC64LE.abi stk) S
  mulAdd : Callee P.mulAdd (fun stk => mulAddContract PPC64LE.abi stk) S
  add : Callee P.add (fun stk => addContract PPC64LE.abi stk) S
  sub : Callee P.sub (fun stk => subContract PPC64LE.abi stk) S
  rejNTT : Callee P.rejNTT (fun stk => rejNTTContract PPC64LE.abi stk) S
  expandMask : Callee P.expandMask (fun stk => expandMaskContract PPC64LE.abi stk) S
  ball : Callee P.ball (fun stk => sampleInBallContract PPC64LE.abi stk) S
  highBits : Callee P.highBits (fun stk => highBitsContract PPC64LE.abi stk) S
  lowBits : Callee P.lowBits (fun stk => lowBitsContract PPC64LE.abi stk) S
  normLt : Callee P.normLt (fun stk => normLtContract PPC64LE.abi stk) S
  makeHint : Callee P.makeHint (fun stk => makeHintContract PPC64LE.abi stk) S
  simpleBitPack : Callee P.simpleBitPack (fun stk => simpleBitPackContract PPC64LE.abi stk) S
  bitPack : Callee P.bitPack (fun stk => bitPackContract PPC64LE.abi stk) S
  bitUnpack : Callee P.bitUnpack (fun stk => bitUnpackContract PPC64LE.abi stk) S
  hintBitPack : Callee P.hintBitPack (fun stk => hintBitPackContract PPC64LE.abi stk) S
  /-- `vg_mldsa_rej_ntt_poly`'s result depends only on its public data (its seed). -/
  rejRet : ∀ stk, RetPub (rejNTTContract PPC64LE.abi stk) P.rejNTT
  /-- `vg_mldsa_rej_ntt_poly` succeeds only if `RejNTTPoly` finishes within `maxBounds`. -/
  rejMax : ∀ stk s t s', (rejNTTContract PPC64LE.abi stk).pre s → Exec isa P.rejNTT s t s' →
    (s'.gpr .r3).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (s.gpr .r3) 34)).isSome
  /-- `vg_mldsa_sample_in_ball`'s result depends only on its public data (`c̃`). -/
  ballRet : ∀ stk, RetPub (sampleInBallContract PPC64LE.abi stk) P.ball
  /-- `vg_mldsa_sample_in_ball` succeeds only if `SampleInBall` finishes within `maxBounds`. -/
  ballMax : ∀ stk s t s', (sampleInBallContract PPC64LE.abi stk).pre s → Exec isa P.ball s t s' →
    (s'.gpr .r3).setWidth 32 = 1 →
    (sampleInBall ((s.gpr .r5).setWidth 32).toNat maxBounds.ball
      (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)).isSome

/-! ## Calls whose results are public -/

/-- The run of a call narrowed to the regions its contract gives it: the
same trace, and the same registers. -/
theorem narrow_run {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} {t : List Leak} {s' : State}
    (hpre : k.pre (s.withRegions rd wr)) (hc : PPC64LE.Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : PPC64LE.Covers wr s.wr)
    (he : Exec isa c s t s') : ∃ s'', Exec isa c (s.withRegions rd wr) t s'' ∧ s''.gpr = s'.gpr := by
  obtain ⟨t', s'', he', -⟩ := hv _ hpre
  have hw' := Exec.widen he' (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at hw'
  obtain ⟨rfl, rfl⟩ := Exec.det he hw'
  exact ⟨_, he', rfl⟩

/-- A call of verified code whose result is public in its own runs gives the
same result in two runs whose narrowed entry states satisfy its precondition
and agree on its public data. -/
theorem RelCT.callRet {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ →
      k.pre (s₁.callEntry.withRegions rd wr) ∧ k.pre (s₂.callEntry.withRegions rd wr) ∧
      k.pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) ∧
      PPC64LE.Covers (rd ++ wr) (s₁.rd ++ s₁.wr) ∧ PPC64LE.Covers wr s₁.wr ∧
      PPC64LE.Covers (rd ++ wr) (s₂.rd ++ s₂.wr) ∧ PPC64LE.Covers wr s₂.wr) :
    RelCT isa P (.call n c) fun s₁ s₂ => (s₁.gpr .r3).setWidth 32 = (s₂.gpr .r3).setWidth 32 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      obtain ⟨n₁, x₁, g₁⟩ := narrow_run hv p₁ (by simpa using c₁) (by simpa using w₁) b₁
      obtain ⟨n₂, x₂, g₂⟩ := narrow_run hv p₂ (by simpa using c₂) (by simpa using w₂) b₂
      obtain ⟨ht, hrax⟩ := hr _ _ _ _ _ _ ⟨p₁, p₂, hpub⟩ x₁ x₂
      rw [ret_eq r₁, ret_eq r₂]
      exact ⟨by simp only [ht], show _ = _ by rw [← g₁, ← g₂]; exact hrax⟩

/-- `callV_tr`, with the result of a callee that is public (`RetPub`). -/
theorem callVRet_tr {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {as : List (Reg × Impl.MlDsa.PPC64LE.KeyGen.Arg)} (hg : glueOk as = true)
    {P : State → State → Prop}
    (hP : ∀ x y, P x y → ∃ rd wr, CallRel k rd wr x y (glueSt x as) (glueSt y as)) :
    RelCT isa P (callAt name c as) fun x y => (x.gpr .r3).setWidth 32 = (y.gpr .r3).setWidth 32 := by
  unfold callAt
  refine RelCT.seq (RelCT.wpDep (F := fun x x1 => x1 = glueSt x as) (relct_noMem (glue_noMem as))
    fun x y _ => ⟨glue_ok hg x, glue_ok hg y⟩) ?_
  refine RelCT.mono (P := fun (a b : State) => ∃ rw : List Region × List Region, ∃ x y : State,
      CallRel k rw.1 rw.2 x y a b ∧ x.rd = a.rd ∧ x.wr = a.wr ∧ y.rd = b.rd ∧ y.wr = b.wr)
    (RelCT.exists_ fun (rw : List Region × List Region) => RelCT.callRet hv hr rw.1 rw.2
      fun a b ⟨x, y, h, e1, e2, e3, e4⟩ => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
        exact ⟨h1, h2, h3, by rwa [← e1, ← e2], by rwa [← e2], by rwa [← e3, ← e4], by rwa [← e4]⟩) ?_
    fun _ _ h => h
  rintro a b ⟨-, x, y, hp, rfl, rfl⟩
  obtain ⟨rd, wr, h⟩ := hP x y hp
  exact ⟨(rd, wr), x, y, h, (glueSt_rd x as).symm, (glueSt_wr x as).symm, (glueSt_rd y as).symm,
    (glueSt_wr y as).symm⟩

/-! ## The samplers' calls, with their bounds -/

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {L : Lay} {Wb : List Nat} {STK : Nat}
include hP

/-- `rn_ok`, and the success of `RejNTTPoly` within `maxBounds` if the call succeeded. -/
theorem rn_okX {s : State} (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} {sd a w : Impl.MlDsa.PPC64LE.KeyGen.Ptr}
    (m : KeyGen.RnOk L Wb sd a w) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri a 1024, tri w 2048, (1, 0, STK)]) s s' →
      ((s'.gpr .r3).setWidth 32 = 1 → Reduced s'.mem (lpa L a)) →
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (lpa L sd) 34)) ((s'.gpr .r3).setWidth 32)
        (polyAt s'.mem (lpa L a)) →
      ((s'.gpr .r3).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (lpa L sd) 34)).isSome) → Q s') :
    WP isa (callAt name P.rejNTT (KeyGen.rnArgs sd a w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hP.rejNTT.verified
  obtain ⟨c1, c2⟩ := KeyGen.rn_cov hs m
  have hv : ∀ s₀, (rejNTTContract PPC64LE.abi stk).pre s₀ → ∃ t s', Exec isa P.rejNTT s₀ t s' ∧
      abiPreserved s₀ s' ∧ ((rejNTTContract PPC64LE.abi stk).post s₀ s' ∧
        ((s'.gpr .r3).setWidth 32 = 1 →
          (rejNTTPoly maxBounds.rejNTT (bytesAt s₀.mem (s₀.gpr .r3) 34)).isSome)) := fun s₀ h₀ => by
    obtain ⟨t, s', e, ha, hp⟩ := hver.1 s₀ h₀
    exact ⟨t, s', e, ha, hp, hP.rejMax stk s₀ t s' h₀ e⟩
  refine KeyGen.callV (k := { rejNTTContract PPC64LE.abi stk with
      post := fun s₀ s' => (rejNTTContract PPC64LE.abi stk).post s₀ s' ∧
        ((s'.gpr .r3).setWidth 32 = 1 →
          (rejNTTPoly maxBounds.rejNTT (bytesAt s₀.mem (s₀.gpr .r3) 34)).isSome) }) hv
    (hs.depth hP.rejNTT.stack hS) m.hg (KeyGen.rn_preS hs (Nat.le_trans hstk hS) m) c1 c2
    fun s' hk ⟨hp, hx⟩ => hQ s' (hs.keptW [tri a 1024, tri w 2048] (Nat.le_trans hP.rejNTT.stack hS) hk) ?_ ?_ ?_
  all_goals
    obtain ⟨g3, g4, -⟩ := KeyGen.rn_vg hs m (KeyGen.rnRd L sd) (KeyGen.rnWr L a w)
    have := KeyGen.rejNtt_post hp
    rw [State.withRegions_mem, State.withRegions_gpr, g3, g4, KeyGen.view_glue_mem] at this
    rw [g3, KeyGen.view_glue_mem, State.withRegions_gpr] at hx
  exacts [this.1, this.2, hx]

/-- `ball_ok`, and the success of `SampleInBall` within `maxBounds` if the call succeeded. -/
theorem ball_okX {s : State} (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String}
    {ct c w : Impl.MlDsa.PPC64LE.KeyGen.Ptr} {len tau : Nat} (m : KeyGen.BallOk L Wb ct len tau c w)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri c 1024, tri w 2048, (1, 0, STK)]) s s' →
      ((s'.gpr .r3).setWidth 32 = 1 → Reduced s'.mem (lpa L c)) →
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (lpa L ct) len)).map toRq)
        ((s'.gpr .r3).setWidth 32) (polyAt s'.mem (lpa L c)) →
      ((s'.gpr .r3).setWidth 32 = 1 → (sampleInBall tau maxBounds.ball (bytesAt s.mem (lpa L ct) len)).isSome) →
      Q s') :
    WP isa (callAt name P.ball (KeyGen.ballArgs ct len tau c w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hP.ball.verified
  obtain ⟨c1, c2⟩ := KeyGen.ball_cov hs m
  obtain ⟨l0, ll, lt⟩ := m.lt
  have hv : ∀ s₀, (sampleInBallContract PPC64LE.abi stk).pre s₀ → ∃ t s', Exec isa P.ball s₀ t s' ∧
      abiPreserved s₀ s' ∧ ((sampleInBallContract PPC64LE.abi stk).post s₀ s' ∧
        ((s'.gpr .r3).setWidth 32 = 1 → (sampleInBall ((s₀.gpr .r5).setWidth 32).toNat maxBounds.ball
          (bytesAt s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat)).isSome)) := fun s₀ h₀ => by
    obtain ⟨t, s', e, ha, hp⟩ := hver.1 s₀ h₀
    exact ⟨t, s', e, ha, hp, hP.ballMax stk s₀ t s' h₀ e⟩
  refine KeyGen.callV (k := { sampleInBallContract PPC64LE.abi stk with
      post := fun s₀ s' => (sampleInBallContract PPC64LE.abi stk).post s₀ s' ∧
        ((s'.gpr .r3).setWidth 32 = 1 → (sampleInBall ((s₀.gpr .r5).setWidth 32).toNat maxBounds.ball
          (bytesAt s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat)).isSome) }) hv
    (hs.depth hP.ball.stack hS) m.hg (KeyGen.ball_preS hs (Nat.le_trans hstk hS) m) c1 c2
    fun s' hk ⟨hp, hx⟩ => hQ s' (hs.keptW [tri c 1024, tri w 2048] (Nat.le_trans hP.ball.stack hS) hk) ?_ ?_ ?_
  all_goals
    obtain ⟨g3, g4, g5, g6, -⟩ := KeyGen.ball_vg hs m (KeyGen.ballRd L ct len) (KeyGen.ballWr L c w)
    have := KeyGen.ball_post hp
    rw [State.withRegions_mem, State.withRegions_gpr, g3, g4, g5, g6, KeyGen.view_glue_mem,
      KeyGen.imm32 (by omega), KeyGen.imm32_toNat (by omega), KeyGen.imm_toNat (by omega)] at this
    rw [g3, g4, g5, KeyGen.view_glue_mem, State.withRegions_gpr, KeyGen.imm32 (by omega), KeyGen.imm32_toNat (by omega),
      KeyGen.imm_toNat (by omega)] at hx
  exacts [this.1, this.2, hx]

end

/-! ## `ρ` -/

theorem signLeak_head (p : Params) (sk μ rnd : List Byte) :
    ∃ X, signLeak p sk μ rnd = leakBytes (sk.take 32) ++ X := by
  rw [← Proof.MlDsa.Sign.signLeakT_eq_signLeak]
  unfold Proof.MlDsa.Sign.signLeakT
  rcases e : skDecode p sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  have hρ : ρ = sk.take 32 := by rw [← Proof.MlDsa.Sign.skRho_eq p sk, e]
  subst hρ
  exact ⟨_, rfl⟩

theorem leak_rho {p : Params} {sk₁ sk₂ μ₁ μ₂ r₁ r₂ : List Byte} (h1 : sk₁.length = p.skLen)
    (h2 : sk₂.length = p.skLen) (h : signLeak p sk₁ μ₁ r₁ = signLeak p sk₂ μ₂ r₂) :
    sk₁.take 32 = sk₂.take 32 := by
  obtain ⟨X₁, e₁⟩ := signLeak_head p sk₁ μ₁ r₁
  obtain ⟨X₂, e₂⟩ := signLeak_head p sk₂ μ₂ r₂
  rw [e₁, e₂] at h
  refine Proof.MlDsa.Sign.leakBytes_inj (List.append_inj h ?_).1
  rw [Proof.MlDsa.Sign.leakBytes_length, Proof.MlDsa.Sign.leakBytes_length, List.length_take, List.length_take, h1, h2]

theorem pub_rho {p : Params} {σ₁ σ₂ : State} (h : sPub p σ₁ σ₂) : (skOf p σ₁).take 32 = (skOf p σ₂).take 32 :=
  leak_rho (Proof.MlKem.bytesAt_length _ _ _) (Proof.MlKem.bytesAt_length _ _ _) h.2.2.2.2.2.2

/-! ## Two runs -/

section
variable {p : Params} {STK : Nat}

theorem sc1_twoL {σ₁ σ₂ x y : State} (pub : sPub p σ₁ σ₂) (h₁ : SC1 p STK σ₁ x) (h₂ : SC1 p STK σ₂ y) :
    Two (slay1 p STK σ₁) sWb1 STK x y :=
  ⟨h₁.site, slay1_pub pub ▸ h₂.site, by rw [h₁.sp, h₂.sp, pub.1]⟩

theorem sc2_twoL {σ₁ σ₂ x y : State} (pub : sPub p σ₁ σ₂) (h₁ : SC2 p STK σ₁ x) (h₂ : SC2 p STK σ₂ y) :
    Two (slay2 p STK σ₁) sWb2 STK x y :=
  ⟨h₁.site, slay2_pub pub ▸ h₂.site, by rw [h₁.sp, h₂.sp, pub.1]⟩

/-- A piece without calls before the hash of `ρ″`, checked by the taint
analysis from `scratch`. -/
theorem srel1 {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC1 p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r31]) c hc).isSome = true) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) I) c fun _ _ => True :=
  rel_of (RelCT.exists_ fun _ => taint31 (fun _ _ h => h) h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc1_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-- A piece without calls after the hash of `ρ″`, checked by the taint
analysis from `scratch`. -/
theorem srel2 {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC2 p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r31]) c hc).isSome = true) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) I) c fun _ _ => True :=
  rel_of (RelCT.exists_ fun _ => taint31 (fun _ _ h => h) h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-- `srel1`, from all the pointers. -/
theorem srel1p {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC1 p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r28, .r29, .r30, .r31]) c hc).isSome = true) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) I) c fun _ _ => True :=
  rel_of (RelCT.exists_ fun _ => taint4 (fun _ _ h => h) h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc1_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-- `srel2`, from all the pointers. -/
theorem srel2p {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC2 p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r28, .r29, .r30, .r31]) c hc).isSome = true) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) I) c fun _ _ => True :=
  rel_of (RelCT.exists_ fun _ => taint4 (fun _ _ h => h) h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-! ## A branch on `r24` -/

/-- `ifOkElse t e`: `t` if `r24 ≠ 0` and `e` otherwise, where `r24` is `v σ`,
a function of the public data. -/
theorem ifOkElse_piece {I J : State → State → Prop} {t e : Prog isa} {v : State → BitVec 64}
    (hv : ∀ σ s, SPre p STK σ → I σ s → s.gpr .r24 = v σ)
    (hpub : ∀ σ₁ σ₂, SPre p STK σ₁ → SPre p STK σ₂ → sPub p σ₁ σ₂ → v σ₁ = v σ₂)
    (ht : SPiece p STK (fun σ s => I σ s ∧ v σ ≠ 0) J t)
    (he : SPiece p STK (fun σ s => I σ s ∧ v σ = 0) J e) :
    SPiece p STK I J (ifOkElse t e) := by
  refine ⟨fun σ s hp hs => ?_, ?_⟩
  · have h24 := hv σ s hp hs
    refine WP.ite _ (eval_nonzero s .r24) (fun hb => ht.ok σ _ hp ⟨hs, ?_⟩) fun hb => he.ok σ _ hp ⟨hs, ?_⟩
    · rw [← h24]; simpa using hb
    · rw [← h24]; simpa using hb
  · refine RelCT.ite ?_ ?_ ?_
    · rintro _ _ ⟨σ₁, σ₂, p₁, p₂, pub, hx, hy⟩
      rw [eval_nonzero, eval_nonzero, hv _ _ p₁ hx, hv _ _ p₂ hy, hpub _ _ p₁ p₂ pub]
    · refine RelCT.mono ht.tr (fun _ _ ⟨⟨σ₁, σ₂, p₁, p₂, pub, hx, hy⟩, hb⟩ =>
        ⟨σ₁, σ₂, p₁, p₂, pub, ⟨hx, ?_⟩, ⟨hy, ?_⟩⟩) fun _ _ h => h
      · rw [eval_nonzero] at hb
        rw [← hv _ _ p₁ hx]; simpa using hb
      · rw [eval_nonzero] at hb
        rw [← hpub _ _ p₁ p₂ pub, ← hv _ _ p₁ hx]; simpa using hb
    · refine RelCT.mono he.tr (fun _ _ ⟨⟨σ₁, σ₂, p₁, p₂, pub, hx, hy⟩, hb⟩ =>
        ⟨σ₁, σ₂, p₁, p₂, pub, ⟨hx, ?_⟩, ⟨hy, ?_⟩⟩) fun _ _ h => h
      · rw [eval_nonzero] at hb
        rw [← hv _ _ p₁ hx]; simpa using hb
      · rw [eval_nonzero] at hb
        rw [← hpub _ _ p₁ p₂ pub, ← hv _ _ p₁ hx]; simpa using hb

/-- The empty block, from `I` to `J`. -/
theorem nil_piece {I J : State → State → Prop} (h : ∀ σ s, SPre p STK σ → I σ s → J σ s) :
    SPiece p STK I J (.block []) :=
  ⟨fun σ s hp hs => WP.block_nil (h σ s hp hs), RelCT.block_nil fun _ _ _ => trivial⟩

end

end VG.Proof.MlDsa.PPC64LE.Sign
