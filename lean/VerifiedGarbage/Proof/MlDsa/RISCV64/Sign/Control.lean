module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Inv
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.StepsCT
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Samp
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.CallS
public import VerifiedGarbage.Proof.MlDsa.Sign.Leak
import VerifiedGarbage.Proof.MlDsa.Sign.Setup
import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.ContractsV
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlKem.Mem

public import VerifiedGarbage.TCB.RISCV64.Target
/-!
# ML-DSA signing on RISC-V: the primitives, two runs, and the branches on the result

What the proofs need of the implementations of the primitives (`SPrimsOk`):
verified with at most `S` bytes of stack, and, as on 32-bit ARM
(`Proof/MlDsa/Arm/Sign/Prims.lean`), for the two samplers whose results the
function branches on, that the result is a function of their public data
(`RetPub`) and that they succeed only if the sampling finishes within
`maxBounds`. A call of such a sampler gives the same result in two runs
(`callVRet_tr`). Then: `ρ` is public (`pub_rho`); two runs with the same
layout (`STwo1`, `STwo2`) and the constant time of a piece without calls by
the taint analysis from the pointers.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv taint31 taint4
  Regs2 Callee CallRel glueOk glueSt glue_ok glueSt_rd glueSt_wr glue_noMem)
open VG.Impl.MlDsa.RISCV64.KeyGen (callAt)
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The primitives -/

/-- The result of `c` (the low word of `a0`) is the same in two runs from
states that satisfy `k.pre` and agree on `k.pub`. -/
def RetPub (k : Contract isa) (c : Prog isa) : Prop :=
  RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c
    fun s₁ s₂ => (s₁.gpr .a0).setWidth 32 = (s₂.gpr .a0).setWidth 32

/-- What the proofs need of the implementations `P` of the primitives: each
verified against its contract with at most `S` bytes of stack, and the facts
about the two samplers the function branches on. -/
structure SPrimsOk (P : Prims) (S : Nat) : Prop where
  ntt : Callee P.ntt (fun stk => nttContract RISCV64.abi stk) S
  invNtt : Callee P.invNtt (fun stk => nttInvContract RISCV64.abi stk) S
  mul : Callee P.mul (fun stk => mulContract RISCV64.abi stk) S
  mulAdd : Callee P.mulAdd (fun stk => mulAddContract RISCV64.abi stk) S
  add : Callee P.add (fun stk => addContract RISCV64.abi stk) S
  sub : Callee P.sub (fun stk => subContract RISCV64.abi stk) S
  rejNTT : Callee P.rejNTT (fun stk => rejNTTContract RISCV64.abi stk) S
  expandMask : Callee P.expandMask (fun stk => expandMaskContract RISCV64.abi stk) S
  ball : Callee P.ball (fun stk => sampleInBallContract RISCV64.abi stk) S
  highBits : Callee P.highBits (fun stk => highBitsContract RISCV64.abi stk) S
  lowBits : Callee P.lowBits (fun stk => lowBitsContract RISCV64.abi stk) S
  normLt : Callee P.normLt (fun stk => normLtContract RISCV64.abi stk) S
  makeHint : Callee P.makeHint (fun stk => makeHintContract RISCV64.abi stk) S
  simpleBitPack : Callee P.simpleBitPack (fun stk => simpleBitPackContract RISCV64.abi stk) S
  bitPack : Callee P.bitPack (fun stk => bitPackContract RISCV64.abi stk) S
  bitUnpack : Callee P.bitUnpack (fun stk => bitUnpackContract RISCV64.abi stk) S
  hintBitPack : Callee P.hintBitPack (fun stk => hintBitPackContract RISCV64.abi stk) S
  /-- With some stack (at most `S`) it is verified with, `vg_mldsa_rej_ntt_poly`'s result depends
  only on its public data (its seed), and it succeeds only if `RejNTTPoly` finishes within
  `maxBounds`. -/
  rejX : ∃ stk, stk ≤ S ∧ Verified RISCV64.target P.rejNTT (rejNTTContract RISCV64.abi stk) ∧
    RetPub (rejNTTContract RISCV64.abi stk) P.rejNTT ∧
    ∀ s t s', (rejNTTContract RISCV64.abi stk).pre s → Exec isa P.rejNTT s t s' →
      (s'.gpr .a0).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (s.gpr .a0) 34)).isSome
  /-- Likewise, `vg_mldsa_sample_in_ball`'s result depends only on its public data (`c̃`), and it
  succeeds only if `SampleInBall` finishes within `maxBounds`. -/
  ballX : ∃ stk, stk ≤ S ∧ Verified RISCV64.target P.ball (sampleInBallContract RISCV64.abi stk) ∧
    RetPub (sampleInBallContract RISCV64.abi stk) P.ball ∧
    ∀ s t s', (sampleInBallContract RISCV64.abi stk).pre s → Exec isa P.ball s t s' →
      (s'.gpr .a0).setWidth 32 = 1 →
      (sampleInBall ((s.gpr .a2).setWidth 32).toNat maxBounds.ball
        (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)).isSome

/-! ## Calls whose results are public -/

/-- The run of a call narrowed to the regions its contract gives it: the
same trace, and the same registers. -/
theorem narrow_run {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} {t : List Leak} {s' : State}
    (hpre : k.pre (s.withRegions rd wr)) (hc : RISCV64.Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : RISCV64.Covers wr s.wr)
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
      RISCV64.Covers (rd ++ wr) (s₁.rd ++ s₁.wr) ∧ RISCV64.Covers wr s₁.wr ∧
      RISCV64.Covers (rd ++ wr) (s₂.rd ++ s₂.wr) ∧ RISCV64.Covers wr s₂.wr) :
    RelCT isa P (.call n c) fun s₁ s₂ => (s₁.gpr .a0).setWidth 32 = (s₂.gpr .a0).setWidth 32 := by
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
    (hr : RetPub k c) {as : List (Reg × Impl.MlDsa.RISCV64.KeyGen.Arg)} (hg : glueOk as = true)
    {P : State → State → Prop}
    (hP : ∀ x y, P x y → ∃ rd wr, CallRel k rd wr x y (glueSt x as) (glueSt y as)) :
    RelCT isa P (callAt name c as) fun x y => (x.gpr .a0).setWidth 32 = (y.gpr .a0).setWidth 32 := by
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
theorem rn_okX {s : State} (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} {sd a w : Impl.MlDsa.RISCV64.KeyGen.Ptr}
    (m : KeyGen.RnOk L Wb sd a w) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri a 1024, tri w 2048, (1, 0, STK)]) s s' →
      ((s'.gpr .a0).setWidth 32 = 1 → Reduced s'.mem (lpa L a)) →
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (lpa L sd) 34)) ((s'.gpr .a0).setWidth 32)
        (polyAt s'.mem (lpa L a)) →
      ((s'.gpr .a0).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (lpa L sd) 34)).isSome) → Q s') :
    WP isa (callAt name P.rejNTT (KeyGen.rnArgs sd a w)) s Q := by
  obtain ⟨stk, hstk, hver, -, hmax⟩ := hP.rejX
  obtain ⟨c1, c2⟩ := KeyGen.rn_cov hs m
  have hv : ∀ s₀, (rejNTTContract RISCV64.abi stk).pre s₀ → ∃ t s', Exec isa P.rejNTT s₀ t s' ∧
      abiPreserved s₀ s' ∧ ((rejNTTContract RISCV64.abi stk).post s₀ s' ∧
        ((s'.gpr .a0).setWidth 32 = 1 →
          (rejNTTPoly maxBounds.rejNTT (bytesAt s₀.mem (s₀.gpr .a0) 34)).isSome)) := fun s₀ h₀ => by
    obtain ⟨t, s', e, ha, hp⟩ := hver.1 s₀ h₀
    exact ⟨t, s', e, ha, hp, hmax s₀ t s' h₀ e⟩
  refine KeyGen.callV (k := { rejNTTContract RISCV64.abi stk with
      post := fun s₀ s' => (rejNTTContract RISCV64.abi stk).post s₀ s' ∧
        ((s'.gpr .a0).setWidth 32 = 1 →
          (rejNTTPoly maxBounds.rejNTT (bytesAt s₀.mem (s₀.gpr .a0) 34)).isSome) }) hv
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
    {ct c w : Impl.MlDsa.RISCV64.KeyGen.Ptr} {len tau : Nat} (m : KeyGen.BallOk L Wb ct len tau c w)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri c 1024, tri w 2048, (1, 0, STK)]) s s' →
      ((s'.gpr .a0).setWidth 32 = 1 → Reduced s'.mem (lpa L c)) →
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (lpa L ct) len)).map toRq)
        ((s'.gpr .a0).setWidth 32) (polyAt s'.mem (lpa L c)) →
      ((s'.gpr .a0).setWidth 32 = 1 → (sampleInBall tau maxBounds.ball (bytesAt s.mem (lpa L ct) len)).isSome) →
      Q s') :
    WP isa (callAt name P.ball (KeyGen.ballArgs ct len tau c w)) s Q := by
  obtain ⟨stk, hstk, hver, -, hmax⟩ := hP.ballX
  obtain ⟨c1, c2⟩ := KeyGen.ball_cov hs m
  obtain ⟨l0, ll, lt⟩ := m.lt
  have hv : ∀ s₀, (sampleInBallContract RISCV64.abi stk).pre s₀ → ∃ t s', Exec isa P.ball s₀ t s' ∧
      abiPreserved s₀ s' ∧ ((sampleInBallContract RISCV64.abi stk).post s₀ s' ∧
        ((s'.gpr .a0).setWidth 32 = 1 → (sampleInBall ((s₀.gpr .a2).setWidth 32).toNat maxBounds.ball
          (bytesAt s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)).isSome)) := fun s₀ h₀ => by
    obtain ⟨t, s', e, ha, hp⟩ := hver.1 s₀ h₀
    exact ⟨t, s', e, ha, hp, hmax s₀ t s' h₀ e⟩
  refine KeyGen.callV (k := { sampleInBallContract RISCV64.abi stk with
      post := fun s₀ s' => (sampleInBallContract RISCV64.abi stk).post s₀ s' ∧
        ((s'.gpr .a0).setWidth 32 = 1 → (sampleInBall ((s₀.gpr .a2).setWidth 32).toNat maxBounds.ball
          (bytesAt s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)).isSome) }) hv
    (hs.depth hP.ball.stack hS) m.hg (KeyGen.ball_preS hs (Nat.le_trans hstk hS) m) c1 c2
    fun s' hk ⟨hp, hx⟩ => hQ s' (hs.keptW [tri c 1024, tri w 2048] (Nat.le_trans hP.ball.stack hS) hk) ?_ ?_ ?_
  all_goals
    obtain ⟨g3, g4, g5, g6, -⟩ := KeyGen.ball_vg hs m (KeyGen.ballRd L ct len) (KeyGen.ballWr L c w)
    have := KeyGen.ball_post hp
    rw [State.withRegions_mem, State.withRegions_gpr, g3, g4, g5, g6, KeyGen.view_glue_mem,
      KeyGen.imm32 (by omega_arith), KeyGen.imm32_toNat (by omega_arith), KeyGen.imm_toNat (by omega_arith)] at this
    rw [g3, g4, g5, KeyGen.view_glue_mem, State.withRegions_gpr, KeyGen.imm32 (by omega_arith), KeyGen.imm32_toNat (by omega_arith),
      KeyGen.imm_toNat (by omega_arith)] at hx
  exacts [this.1, this.2, hx]

theorem rn_trRet (hS : S ≤ STK) {name : String} {sd a w : Impl.MlDsa.RISCV64.KeyGen.Ptr}
    (m : KeyGen.RnOk L Wb sd a w) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      bytesAt x.mem (lpa L sd) 34 = bytesAt y.mem (lpa L sd) 34) :
    RelCT isa Q (callAt name P.rejNTT (KeyGen.rnArgs sd a w))
      fun x y => (x.gpr .a0).setWidth 32 = (y.gpr .a0).setWidth 32 := by
  obtain ⟨stk, hstk, hver, hret, -⟩ := hP.rejX
  refine callVRet_tr hver.1 hret m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, hl⟩ := hQ x y hxy
  obtain ⟨gx3, gx4, gx5⟩ := KeyGen.rn_vg hx m (KeyGen.rnRd L sd) (KeyGen.rnWr L a w)
  obtain ⟨gy3, gy4, gy5⟩ := KeyGen.rn_vg hy m (KeyGen.rnRd L sd) (KeyGen.rnWr L a w)
  refine ⟨KeyGen.rnRd L sd, KeyGen.rnWr L a w, KeyGen.rn_preS hx (Nat.le_trans hstk hS) m,
    KeyGen.rn_preS hy (Nat.le_trans hstk hS) m,
    KeyGen.rejNtt_pub (by rw [KeyGen.view_glue_sp, KeyGen.view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4])
      (by rw [gx5, gy5]) ?_, (KeyGen.rn_cov hx m).1, (KeyGen.rn_cov hx m).2, (KeyGen.rn_cov hy m).1,
    (KeyGen.rn_cov hy m).2⟩
  rw [gx3, gy3, KeyGen.view_glue_mem, KeyGen.view_glue_mem]
  exact hl

theorem ball_trRet (hS : S ≤ STK) {name : String} {ct c w : Impl.MlDsa.RISCV64.KeyGen.Ptr} {len tau : Nat}
    (m : KeyGen.BallOk L Wb ct len tau c w) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      bytesAt x.mem (lpa L ct) len = bytesAt y.mem (lpa L ct) len) :
    RelCT isa Q (callAt name P.ball (KeyGen.ballArgs ct len tau c w))
      fun x y => (x.gpr .a0).setWidth 32 = (y.gpr .a0).setWidth 32 := by
  obtain ⟨stk, hstk, hver, hret, -⟩ := hP.ballX
  obtain ⟨l0, ll, lt⟩ := m.lt
  refine callVRet_tr hver.1 hret m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, hl⟩ := hQ x y hxy
  obtain ⟨gx3, gx4, gx5, gx6, gx7⟩ := KeyGen.ball_vg hx m (KeyGen.ballRd L ct len) (KeyGen.ballWr L c w)
  obtain ⟨gy3, gy4, gy5, gy6, gy7⟩ := KeyGen.ball_vg hy m (KeyGen.ballRd L ct len) (KeyGen.ballWr L c w)
  refine ⟨KeyGen.ballRd L ct len, KeyGen.ballWr L c w, KeyGen.ball_preS hx (Nat.le_trans hstk hS) m,
    KeyGen.ball_preS hy (Nat.le_trans hstk hS) m,
    KeyGen.ball_pub (by rw [KeyGen.view_glue_sp, KeyGen.view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4])
      (by rw [gx5, gy5]) (by rw [gx6, gy6]) (by rw [gx7, gy7]) ?_, (KeyGen.ball_cov hx m).1, (KeyGen.ball_cov hx m).2,
    (KeyGen.ball_cov hy m).1, (KeyGen.ball_cov hy m).2⟩
  rw [gx3, gy3, gx4, gy4, KeyGen.view_glue_mem, KeyGen.view_glue_mem, KeyGen.imm_toNat (by omega_arith)]
  exact hl

end

/-! ## Two runs related by more than their entry states -/

/-- Two runs, each satisfying `I` from its entry state, related by `E`. -/
def RR (p : Params) (STK : Nat) (I E : State → State → Prop) (x y : State) : Prop :=
  Rel2 (SPre p STK) (sPub p) I x y ∧ E x y

theorem WP.conj {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁) (h₂ : WP isa c s Q₂) :
    WP isa c s fun s' => Q₁ s' ∧ Q₂ s' := by
  obtain ⟨t, s', e, q₁⟩ := h₁
  obtain ⟨_, _, e', q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact ⟨t, _, e, q₁, q₂⟩

/-- A piece that takes each run from `I` to `J` and from `s` to `s'` with
`F s s'`, and leaks the same from runs related by `RR I E`, with `Q₀` of the
final states. -/
theorem stepRR {p : Params} {STK : Nat} {I J E E' Q₀ F : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, SPre p STK σ → I σ s → WP isa c s fun s' => J σ s' ∧ F s s')
    (ht : RelCT isa (RR p STK I E) c Q₀)
    (hE : ∀ x y x' y', RR p STK I E x y → F x x' → F y y' → Q₀ x' y' → E' x' y') :
    RelCT isa (RR p STK I E) c (RR p STK J E') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, he⟩ := hr
  obtain ⟨_, u₁, f₁, g₁, k₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂, k₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', ⟨σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩, hE _ _ _ _ ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, he⟩ k₁ k₂ hq⟩

/-! ## `ρ` -/

theorem signLeak_head (p : Params) (sk μ rnd : List Byte) :
    ∃ X, signLeak p sk μ rnd = leakBytes (sk.take 32) ++ X := by
  unfold signLeak
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

/-! ## The state, but for `a0` and `s4` -/

theorem SC1.regs2 {p : Params} {STK : Nat} {σ s s' : State} (h : SC1 p STK σ s) (hr : Regs2 s s') :
    SC1 p STK σ s' :=
  ⟨h.site.regs2 hr, hr.rd.trans h.rd, hr.wr.trans h.wr, hr.sp.trans h.sp,
    fun r hp hs => by
      have : r ≠ .a0 ∧ r ≠ .s4 := ⟨fun e => by subst e; simp [preserved] at hp,
        fun e => by subst e; simp [savedTop] at hs⟩
      rw [hr.gpr r this.1 this.2]; exact h.pres r hp hs,
    by rw [hr.mem]; exact h.sav, by rw [hr.mem]; exact h.sig, by rw [hr.mem]; exact h.sk, by rw [hr.mem]; exact h.mu,
    by rw [hr.mem]; exact h.rnd⟩

theorem SC2.regs2 {p : Params} {STK : Nat} {σ s s' : State} (h : SC2 p STK σ s) (hr : Regs2 s s') :
    SC2 p STK σ s' :=
  ⟨h.site.regs2 hr, hr.rd.trans h.rd, hr.wr.trans h.wr, hr.sp.trans h.sp,
    fun r hp hs => by
      have : r ≠ .a0 ∧ r ≠ .s4 := ⟨fun e => by subst e; simp [preserved] at hp,
        fun e => by subst e; simp [savedTop] at hs⟩
      rw [hr.gpr r this.1 this.2]; exact h.pres r hp hs,
    by rw [hr.mem]; exact h.sav, by rw [hr.mem]; exact h.sk, by rw [hr.mem]; exact h.mu⟩

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
    {c : Prog isa} {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs [.s11]) c hc).isSome = true) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) I) c fun _ _ => True :=
  rel_of (RelCT.exists_ fun _ => taint31 (fun _ _ h => h) h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc1_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-- A piece without calls after the hash of `ρ″`, checked by the taint
analysis from `scratch`. -/
theorem srel2 {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC2 p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs [.s11]) c hc).isSome = true) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) I) c fun _ _ => True :=
  rel_of (RelCT.exists_ fun _ => taint31 (fun _ _ h => h) h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-- `srel1`, from all the pointers. -/
theorem srel1p {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC1 p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs [.s8, .s9, .s10, .s11]) c hc).isSome = true) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) I) c fun _ _ => True :=
  rel_of (RelCT.exists_ fun _ => taint4 (fun _ _ h => h) h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc1_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-- `srel2`, from all the pointers. -/
theorem srel2p {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC2 p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs [.s8, .s9, .s10, .s11]) c hc).isSome = true) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) I) c fun _ _ => True :=
  rel_of (RelCT.exists_ fun _ => taint4 (fun _ _ h => h) h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

end

end VG.Proof.MlDsa.RISCV64.Sign
