module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.LeafCT
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Classify
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.LeafCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Loop
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAdvance
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinish
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinishSquare
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFrameContext
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupLoop
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroups
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHead
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoopControl
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPending
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingMath
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawCore
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawSquares
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRun
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowSquares
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailBit
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Correct
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.GenerationBounds
import VerifiedGarbage.Proof.Ffdh.GenerationTape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Witness
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAdvance
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinishSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFrameContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroups
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHead
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoopControl
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPending
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawSquares
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRun
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowSquares
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailBit
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.Setup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.Store
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Classify
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Correct
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Loop
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.GenerationBounds
meta import VerifiedGarbage.Proof.Ffdh.GenerationTape
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Witness
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # The parameter search's timing depends on its public data alone (AArch64)

Every branch is on the attempts left, the candidate's status and the
tape's length, which the point (the public descriptor, the octets consumed
and the attempts left) fixes.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (writeController)
open VG.Impl.Ffdh.AArch64.Generation.Search

/-! ## The classification -/

theorem s_candidated_pins : Pins SCandidated [.x19] := by
  intro q s t ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.x19.trans h₂.x19.symm

/-- The candidate's status. -/
abbrev SPoint.status (q : SPoint) : Nat := candidateStatus (q.inputs.cand q.used)

/-- The status in `x9`, compared with `j` in `x12`. -/
def SGuard (j : Nat) (q : SPoint) (t : State) : Prop :=
  SCTL q t ∧ q.k ≠ 0 ∧ t.gpr .x9 = BitVec.ofNat 64 q.status ∧
    isa.eval (.zero .x .x12) t = some (decide (q.status = j))

/-- After the status and the pointer to `used` are loaded. -/
def SHead (q : SPoint) (t : State) : Prop :=
  SCandidated q t ∧ t.gpr .x11 = q.inputs.up ∧ t.gpr .x9 = BitVec.ofNat 64 q.status

private theorem head_first (q : SPoint) (s : State) (h : SCandidated q s) :
    WP isa (.block [.addImm .w .x9 .x0 0, ldf .x11 7]) s (SHead q) := by
  obtain ⟨original, h, hk, hp⟩ := h
  have a := h.access
  have hv7 := h.header (j := 7) (v := q.inputs.up) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv7
  have hst : q.status < 3 := status_lt (q.inputs.cand q.used)
  have h0 : (s.gpr .x0).setWidth 32 = BitVec.ofNat 32 q.status := by
    apply BitVec.eq_of_toNat_eq
    rw [hp.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (WP.keep [.x9, .x11] (Q := fun t =>
    (t.gpr .x11 = q.inputs.up ∧ t.gpr .x9 = BitVec.ofNat 64 q.status) ∧ t.mem = s.mem) ?_
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨⟨h11, h9⟩, hm⟩, k⟩ => ?_
  · brun [ldf, h.x19, hv7, a.ld 56 (by decide),
      VG.Proof.RsaKeyGen.AArch64.exec_addImm_w (show 0 < 4096 by decide), h0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · refine ⟨⟨original, h.keep k hm, hk, ?_⟩, h11, h9⟩
    unfold CandPost at hp ⊢
    rw [hm, k.gpr .x0 (by decide)]
    exact hp

theorem s_head_pins : Pins SHead [.x11] := by
  intro q s t h₁ h₂ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.2.1.trans h₂.2.1.symm

private theorem head_second (q : SPoint) (s : State) (h : SHead q s) :
    WP isa (.block [Impl.Bignum.AArch64.ld .x10 .x11, .subImm .x .x12 .x9 1]) s (SGuard 1 q) := by
  obtain ⟨⟨original, h, hk, _⟩, h11, h9⟩ := h
  have hu : InRegions (s.rd ++ s.wr) q.inputs.up 8 := by
    refine ⟨⟨q.inputs.up, 8⟩, List.mem_append_right _ ?_, ?_⟩
    · rw [h.wr, h.input.1.2.2.2.1, ← h.input.used_eq]; simp [inWrites]
    · simpa only [BitVec.add_zero] using Offset.contains_base q.inputs.up (d := 0) (n := 8) (k := 8)
        (by decide) (by decide)
  have hst : q.status < 3 := status_lt (q.inputs.cand q.used)
  refine WP.mono (WP.keep [.x10, .x12] (Q := fun t =>
    isa.eval (.zero .x .x12) t = some (decide (q.status = 1)) ∧ t.mem = s.mem) ?_
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨he, hm⟩, k⟩ =>
      ⟨⟨original, h.keep k hm⟩, hk, (k.gpr .x9 (by decide)).trans h9, he⟩
  brun [h11, h9, hu]
  have : ∀ st < 3, ((BitVec.ofNat 64 st - BitVec.ofNat 64 1) == 0) = decide (st = 1) := by decide
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq, this _ hst]

private theorem second_ready (q : SPoint) (s : State)
    (h : SGuard 1 q s ∧ isa.eval (.zero .x .x12) s = some false) :
    WP isa (.block [.subImm .x .x12 .x9 2]) s (SGuard 2 q) := by
  obtain ⟨⟨⟨o, hl⟩, hk, h9, _⟩, _⟩ := h
  refine WP.mono (test_two h9 (status_lt _)) fun t ⟨⟨he, hm⟩, kt⟩ => ?_
  exact ⟨⟨o, hl.keep kt hm⟩, hk, (kt.gpr .x9 (by decide)).trans h9, he⟩

private theorem guard_eq (j : Nat) (q : SPoint) (s₁ s₂ : State) (h₁ : SGuard j q s₁)
    (h₂ : SGuard j q s₂) : isa.eval (.zero .x .x12) s₁ = isa.eval (.zero .x .x12) s₂ :=
  h₁.2.2.2.trans h₂.2.2.2.symm

private theorem leafB {α : Type} {Φ : α → State → Prop} {c : Prog isa} (f : α → SPub)
    (hΦ : ∀ q s, Φ q s → SAny (f q) s) (hc : RelCT isa (Two SAny) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨f q, hΦ q _ h₁, hΦ q _ h₂, hsp⟩) fun _ _ h => h

/-- Whether the tape holds the entropy cap, after a short tape. -/
def SShort (q : SPoint) (t : State) : Prop :=
  SCTL q t ∧ isa.eval (.zero .x .x12) t =
    some (decide (q.inputs.randLen - q.used < parameterEntropy q.inputs.bits))

private theorem short_ready (q : SPoint) (s : State)
    (h : SGuard 2 q s ∧ isa.eval (.zero .x .x12) s = some false) :
    WP isa (.block [ldf .x10 11, ldf .x11 2, .subs .x .x12 .x10 .x11, Impl.Bignum.AArch64.movi .x13 0,
      Impl.Bignum.AArch64.movi .x14 1, .csel .x .x12 .x14 .x13]) s (SShort q) := by
  obtain ⟨⟨⟨o, hl⟩, _⟩, _⟩ := h
  exact WP.mono (short_guard hl) fun t ⟨⟨ht, _⟩, he⟩ => ⟨⟨o, ht⟩, he⟩

theorem s_short_ct : RelCT isa (Two fun q s => SGuard 2 q s ∧ isa.eval (.zero .x .x12) s = some false)
    short (fun _ _ => True) := by
  unfold short
  refine RelCT.seq (two_piece [.x19] (fun q _ _ h₁ h₂ => s_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide) short_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_request_ct
  · exact leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_exhausted_ct

theorem s_classify_ct : RelCT isa (Two SCandidated) classify (fun _ _ => True) := by
  unfold classify
  change RelCT isa (Two SCandidated) (.seq (.block ([.addImm .w .x9 .x0 0, ldf .x11 7] ++
    [Impl.Bignum.AArch64.ld .x10 .x11, .subImm .x .x12 .x9 1])) _) _
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (two_piece [.x19] s_candidated_pins (by taint_decide) head_first)
    (two_piece [.x11] s_head_pins (by taint_decide) head_second))) ?_
  refine two_ite (guard_eq 1) (leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_accept_ct) ?_
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide)) second_ready) ?_
  exact two_ite (guard_eq 2) (leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_reject_ct) s_short_ct

/-! ## An iteration -/

/-- Whether the search goes on after an iteration from `q`: a candidate is
rejected. -/
def sContinues (q : SPoint) : Prop := q.k ≠ 0 ∧ q.status = 2

instance (q : SPoint) : Decidable (sContinues q) :=
  inferInstanceAs (Decidable (q.k ≠ 0 ∧ q.status = 2))

/-- The point after a rejected candidate. -/
def nextPoint (q : SPoint) : SPoint := ⟨q.inputs, q.used + q.inputs.read q.used, q.k - 1⟩

/-- After the test of the attempts, the candidate and its classification. -/
def SBranchResult (q : SPoint) (t : State) : Prop :=
  if sContinues q then SCTL (nextPoint q) t ∧ word t.mem q.inputs.control 112 = 4
  else ∃ original r, SDone q.inputs original r t

theorem branch_x19 {q : SPoint} {t : State} (h : SBranchResult q t) :
    t.gpr .x19 = q.inputs.control := by
  by_cases hc : sContinues q
  · simp only [SBranchResult, hc, ite_true] at h
    obtain ⟨⟨_, hl⟩, _⟩ := h
    exact hl.x19
  · simp only [SBranchResult, hc, ite_false] at h
    obtain ⟨_, _, hd⟩ := h
    exact hd.x19

def KGuard (q : SPoint) (s : State) : Prop :=
  SCTL q s ∧ isa.eval (.zero .x .x9) s = some (decide (q.k = 0))

theorem k_ready (q : SPoint) (s : State) (h : SCTL q s) :
    WP isa (.block [ldf .x9 0]) s (KGuard q) := by
  obtain ⟨original, h⟩ := h
  exact WP.mono (attempts_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht⟩, he⟩

/-- The branch of an iteration. -/
abbrev sBranch (c : Cand) : Prog isa := .ite (.zero .x .x9) exhausted (.seq (candidateRun c.call) classify)

theorem s_branch_ready (c : Cand) (q : SPoint) (s : State) (h : KGuard q s) :
    WP isa (sBranch c) s (SBranchResult q) := by
  obtain ⟨⟨original, hl⟩, he⟩ := h
  refine WP.ite (decide (q.k = 0)) he ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    refine WP.mono (search_exhausted hl) fun t ht => ?_
    simp only [SBranchResult, sContinues, hz', ne_eq, not_true_eq_false, false_and, ite_false]
    exact ⟨original, _, ht⟩
  intro hnz
  have hk : q.k ≠ 0 := of_decide_eq_false hnz
  refine WP.seq (WP.mono (search_candidate_run c hl) fun t ⟨ht, hp⟩ => ?_)
  refine WP.mono (search_classify ht hk hp) fun r hr => ?_
  unfold SClassified at hr
  by_cases h2 : q.status = 2
  · simp only [SPoint.status] at h2
    simp only [h2, ite_true] at hr
    have hc : sContinues q := ⟨hk, h2⟩
    simp only [SBranchResult, hc, ite_true]
    exact ⟨⟨original, hr.1⟩, hr.2⟩
  · simp only [SPoint.status] at h2
    simp only [h2, ite_false] at hr
    have hc : ¬sContinues q := fun hc => h2 hc.2
    simp only [SBranchResult, hc, ite_false]
    exact ⟨original, _, hr⟩

theorem s_branch_ct (c : Cand) : RelCT isa (Two KGuard) (sBranch c) (fun _ _ => True) := by
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_exhausted_ct) ?_
  have hr : ∀ q s, KGuard q s ∧ isa.eval (.zero .x .x9) s = some false → SReady q s :=
    fun q s ⟨⟨hl, he⟩, hf⟩ => ⟨hl, of_decide_eq_false (Option.some.inj (he.symm.trans hf))⟩
  exact RelCT.seq (two_post ((s_candidate_run_ct c).mono
      (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, hr q _ h₁, hr q _ h₂, hsp⟩) fun _ _ h => h)
    fun q s h => s_candidate_ready c q s (hr q s h)) s_classify_ct

theorem s_iteration_ct (c : Cand) :
    RelCT isa (Two SCTL) (iteration c.call) (fun _ _ => True) := by
  unfold iteration
  refine RelCT.seq (two_piece [.x19] s_ctl_pins (by taint_decide) k_ready) ?_
  exact RelCT.seq (two_post (s_branch_ct c) (s_branch_ready c))
    (two_taint [.x19] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_x19 h₁).trans (branch_x19 h₂).symm) (by taint_decide))

def SCTStep (q : SPoint) (s : State) : Prop :=
  if sContinues q then isa.eval (.zero .x .x9) s = some true ∧ SCTL (nextPoint q) s
  else isa.eval (.zero .x .x9) s = some false

theorem s_ct_step (c : Cand) (q : SPoint) (s : State) (h : SCTL q s) :
    WP isa (iteration c.call) s (SCTStep q) := by
  unfold iteration
  refine WP.seq (WP.mono (k_ready q s h) fun u hu => ?_)
  refine WP.seq (WP.mono (s_branch_ready c q u hu) fun t ht => ?_)
  by_cases hc : sContinues q
  · simp only [SBranchResult, hc, ite_true] at ht
    obtain ⟨⟨original, hl⟩, hw⟩ := ht
    refine WP.mono (live_loop_guard hl hw) fun z ⟨hz, hzl⟩ => ?_
    simp only [SCTStep, hc, ite_true]
    exact ⟨hz, original, hzl⟩
  · simp only [SBranchResult, hc, ite_false] at ht
    obtain ⟨_, _, hd⟩ := ht
    refine WP.mono (done_loop_guard hd) fun z ⟨hz, _⟩ => ?_
    simp only [SCTStep, hc, ite_false]
    exact hz

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q, n = q.k + 1 ∧ SCTL q s ∧ SCTL q t ∧ s.sp = t.sp

private theorem iteration_pair (c : Cand) (n : Nat) :
    RelCT isa (LoopPair n) (iteration c.call) fun s t =>
      isa.eval (.zero .x .x9) s = isa.eval (.zero .x .x9) t ∧
      (isa.eval (.zero .x .x9) s = some false → True) ∧
      (isa.eval (.zero .x .x9) s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : SPoint) (s : State) (h : n = q.k + 1 ∧ SCTL q s) :
      WP isa (iteration c.call) s fun t => n = q.k + 1 ∧ SCTStep q t :=
    WP.mono (s_ct_step c q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((s_iteration_ct c).mono
    (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.2, h₂.2, hsp⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂, hsp⟩ => ⟨q, ⟨hn, h₁⟩, ⟨hn, h₂⟩, hsp⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, ⟨_, h₂⟩, hsp⟩
  by_cases hb : sContinues q
  · simp only [SCTStep, hb, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨(nextPoint q).k + 1, ?_, nextPoint q, rfl, h₁.2, h₂.2, hsp⟩
    have := hb.1
    simp only [nextPoint]
    omega
  · simp only [SCTStep, hb, ite_false] at h₁ h₂
    exact ⟨h₁.trans h₂.symm, fun _ => trivial, fun ht => absurd (ht.symm.trans h₁) (by decide)⟩

theorem s_loop_ct (c : Cand) :
    RelCT isa (Two SCTL) (.loop (iteration c.call) (.zero .x .x9)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht, hsp⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration c.call) (c := .zero .x .x9)
    (Q := fun _ _ => True) LoopPair (iteration_pair c) (q.k + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht, hsp⟩ he₁ he₂

end VG.Proof.Ffdh.AArch64.Generation
