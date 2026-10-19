module

public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPrivate.Correct
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPrivate.Correct
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.Octets
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
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAdvance
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedGroup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedGroupCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedStep
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinish
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinishSquare
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFrameContext
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupCore
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
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowStep
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailBit
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailByteCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
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
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Pieces
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Spec.Dsa.SignVerify
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAdvance
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedGroup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedGroupCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedStep
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinishSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFrameContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupCore
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowStep
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailBit
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailByteCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
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
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Pieces
meta import VerifiedGarbage.Proof.Ffdh.Domain
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
meta import VerifiedGarbage.Spec.Dsa.SignVerify

/-!
# `vg_ffdh_check_private` on AArch64: constant time

Runs with the same public data (`KpP`: all but x's octets, and whether x is
in range) leak the same (`kp_constantTime`): the exponentiation is RSA's,
constant time in the exponent, and the only branch on x is on its range,
which the status gives.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckPrivate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.AArch64.CheckDomain (pins_nil)
open VG.Spec.Ffdh

/-- A stage of some scalar. -/
def Ex (Φ : KpP → List Byte → State → Prop) (p : KpP) (t : State) : Prop := ∃ xb, Φ p xb t

theorem ex_post {Φ Ψ : KpP → List Byte → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (Ex Φ)) c fun _ _ => True)
    (hw : ∀ p xb s, Φ p xb s → WP isa c s fun u => Ψ p xb u ∧ KX s u) : RelCT isa (Two (Ex Φ)) c (Two (Ex Ψ)) :=
  two_post hct fun p s ⟨xb, h⟩ => WP.mono (hw p xb s h) fun _ h => ⟨xb, h.1⟩

theorem ex_post' {Φ Ψ : KpP → List Byte → State → Prop} {c : Prog isa} {P : KpP → State → Prop}
    (hct : RelCT isa (Two fun p s => Ex Φ p s ∧ P p s) c fun _ _ => True)
    (hw : ∀ p xb s, Φ p xb s → P p s → WP isa c s fun u => Ψ p xb u ∧ KX s u) :
    RelCT isa (Two fun p s => Ex Φ p s ∧ P p s) c (Two (Ex Ψ)) :=
  two_post hct fun p s ⟨⟨xb, h⟩, hp⟩ => WP.mono (hw p xb s h hp) fun _ h => ⟨xb, h.1⟩

/-- The working space, as the arithmetic sees it. -/
abbrev KpP.ws (p : KpP) : Ws := ⟨off p.B (inner ((p.k + 7) / 8)), slot ((p.k + 7) / 8) 8, (p.k + 7) / 8⟩

/-- The inner workspace's base. -/
abbrev KpP.g (p : KpP) : Addr := off p.B (inner ((p.k + 7) / 8))

/-- After the entry. -/
def E1' (p : KpP) (xb : List Byte) (t : State) : Prop := E1 (p.D xb) t ∧ Ok p xb

/-- After `domHead`. -/
def CE' (p : KpP) (xb : List Byte) (t : State) : Prop := CE (p.D xb) t ∧ Ok p xb

theorem k1_lpre' (p : KpP) (xb : List Byte) (t : State) (h : K1 p xb t) :
    LPre aXm sX sXl ((p.D xb).ld p.xp p.xl) t := by
  have := k1_lpre p xb t h
  rw [h.2.1] at this
  exact this

theorem In.x0 {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) : t.gpr .x0 = off D.B (inner D.w) := h.2.1.x0

/-- `g^x`'s public data. -/
abbrev KpP.pwG (p : KpP) : PowPub :=
  ⟨⟨p.B, p.Z, inner ((p.k + 7) / 8), (p.k + 7) / 8, (p.k + 7) / 8⟩, p.dp + BitVec.ofNat 64 p.k, p.k, p.xp, p.xl⟩

theorem k13_pre (p : KpP) (xb : List Byte) (t : State) (h : K13 p xb t) : PS0 sG sK sX sXl p.pwG t := by
  obtain ⟨⟨mi, hM, -⟩, ho, -⟩ := h
  have hb := hM.1
  have hs := hM.2.2.2.1
  have hx : Src t p.B p.Z p.xp xb := hb.srcs (p.xp, xb) (by simp [KpP.D])
  have hk1 : 64 ≤ p.k := hb.k1
  have hk2 : p.k ≤ 1024 := hb.k2
  have := hM.ps0 (bp := sG) (bl := sK) (ep := sX) (el := sXl) (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sG) (v := (p.D xb).dp + BitVec.ofNat 64 (p.D xb).k) (by simp))
    (by rw [hb.glen]; exact hs.get (i := sK) (by simp)) hb.gsrc (by rw [hb.glen]; simp; omega)
    (by rw [hb.glen]) (hs.get (i := sX) (v := p.xp) (by simp [KpP.D]))
    (by rw [ho.1]; exact hs.get (i := sXl) (by simp [KpP.D])) hx (by rw [ho.1]; exact ho.2.1)
    (by rw [ho.1]; have := ho.2.2.1; omega)
  rw [hb.glen, ho.1] at this
  exact this

/-- y's square-and-multiply's public data. -/
abbrev KpP.pwY (p : KpP) (lq : Nat) : PowPub :=
  ⟨⟨p.B, p.Z, inner ((p.k + 7) / 8), (p.k + 7) / 8, (p.k + 7) / 8⟩, p.yp, p.k,
    off (p.dp + BitVec.ofNat 64 (2 * p.k)) lq, p.k - lq⟩

/-- q's leading zero octets. -/
abbrev KpP.lq (p : KpP) : Nat := lead ((p.dom.drop (2 * p.k)).take p.k)

theorem k12_q {p : KpP} {xb : List Byte} {s : State} (h : K12 p xb s)
    (he : isa.eval (.zero .x .x3) s = some false) : p.dl = 3 * p.k :=
  h.1.choose_spec.1.1.q (by rw [k12_eval h] at he; simpa using he)

/-- The tail. -/
theorem tail_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => Ex K9 p s ∧ isa.eval (.zero .x .x9) s = some false)
      (seqs (CheckPrivate.tail W.code S.code M.mm)) fun _ _ => True := by
  rw [tail_eq]
  refine RelCT.seqs_append (by simp [r2Steps]) (by simp) (RelCT.seq (R := Two (Ex K10))
    (ex_post' ((r2_ct M).mono (fun _ _ h => two_bind (fun p s₁ s₂ ⟨⟨xb₁, ⟨mi₁, hI₁, _⟩, _⟩, _⟩
        ⟨⟨xb₂, ⟨mi₂, hI₂, _⟩, _⟩, _⟩ => by
      have hb := hI₁.1
      have ew := hb.ew
      have := hb.k1
      obtain ⟨hodd, -⟩ := valid_facts hI₁.2.2.2.2.2 hb.k1
      obtain rfl : mi₁ = mi₂ := xvals_minv (show 1 ≤ (p.D xb₁).w by omega) hodd hI₁.2.2.1 hI₂.2.2.1
      exact ⟨_, hI₁.r2pre, hI₂.r2pre⟩) h) fun _ _ h => h) fun p xb s h he => k9_k10 M p xb s h he) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex K11)) (ex_post (two_taint [.x0]
    (pins_x0B KpP.g fun (p : KpP) s (h : Ex K10 p s) => by
      obtain ⟨_, ⟨_, hM⟩, _⟩ := h; exact hM.2.1.sub.x0) (by taint_decide)) k10_k11) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex K12)) (ex_post (two_taint [.x0]
    (pins_x0B KpP.B fun (p : KpP) s (h : Ex K11 p s) => by
      obtain ⟨_, ⟨_, hP, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide)) k11_k12) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex K13)) (two_ite
    (fun p s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ => by rw [k12_eval h₁, k12_eval h₂])
    (ex_post' (two_taint [.x0] (pins_x0B KpP.B fun (p : KpP) s (h : Ex K12 p s ∧ _) => by
        obtain ⟨⟨_, ⟨_, hP, _⟩, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide))
      fun p xb s h he => k12_k13n p xb s h he) ?_) ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine RelCT.seqs_append (by simp [scan]) (by simp) (RelCT.seq (R := Two (Ex K12s))
      (ex_post' (two_map (fun p : KpP => (⟨p.B, p.Z, (p.k + 7) / 8, p.dp + BitVec.ofNat 64 (2 * p.k),
          (p.dom.drop (2 * p.k)).take p.k⟩ : ScanPub))
        (fun p s ⟨⟨xb, h⟩, he⟩ => h.1.choose_spec.1.scanPre (k12_q h he))
        (scan_ct (by taint_decide) (by taint_decide))) fun p xb s h he => k12_s p xb s h (k12_q h he)) ?_)
    refine seqs_cons_ct (by simp [pow]) (RelCT.seq (R := Two (Ex K12e)) (ex_post (two_taint [.x0]
      (pins_x0B KpP.B fun (p : KpP) s (h : Ex K12s p s) => by
        obtain ⟨_, ⟨_, hP, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide)) s_e) ?_)
    refine RelCT.seqs_append (by simp [pow]) (by simp [isOne, eqArr]) (RelCT.seq (R := Two (Ex K12p))
      (ex_post (two_map (fun p : KpP => p.pwY p.lq) (fun p s ⟨xb, h⟩ => e_pre p xb s h)
        (pow_ct W M S (loadArr_ct (by decide) (by taint_decide) (by taint_decide))
          (expLoop_ct W M S (by taint_decide)) (by taint_decide) (by taint_decide) (by taint_decide))) (e_p W M S)) ?_)
    exact ex_post (two_map KpP.ws (fun p s ⟨xb, ⟨mi, hM, _⟩, _⟩ => hM.inn.goodW1.1)
      (eqArr_ct (by decide) (by decide) (by taint_decide))) p_k13
  rw [seqs_one]
  refine two_ite (fun p s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ => by rw [k13_eval h₁, k13_eval h₂]; rfl)
    (two_taint [] (pins_nil _) (by taint_decide)) ?_
  simp only [fin, List.append_assoc]
  refine RelCT.seqs_append (by simp [pow]) (by simp [Crt.loadArr]) (RelCT.seq (R := Two (Ex K14))
    (ex_post' (two_map KpP.pwG (fun p s ⟨⟨xb, h⟩, _⟩ => k13_pre p xb s h)
      (pow_ct W M S (loadArr_ct (by decide) (by taint_decide) (by taint_decide))
        (expLoop_ct W M S (by taint_decide)) (by taint_decide) (by taint_decide) (by taint_decide)))
      fun p xb s h he => k13_k14 W M S p xb s h he) ?_)
  refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp [eqArr]) (RelCT.seq (R := Two (Ex K15))
    (ex_post (two_map (fun p : KpP => (⟨⟨p.B, p.Z, inner ((p.k + 7) / 8), (p.k + 7) / 8, (p.k + 7) / 8⟩, p.yp,
        p.yb.length⟩ : BPub)) (fun p s ⟨xb, ⟨mi, hM, _⟩, ho, _⟩ => hM.inn.lpreY ho)
      (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) k14_k15) ?_)
  refine RelCT.seqs_append (by simp [eqArr]) (by simp) (RelCT.seq (R := Two (Ex K16))
    (ex_post (two_map KpP.ws (fun p s ⟨xb, ⟨mi, hI, _⟩, _⟩ => hI.goodW1.1)
      (eqArr_ct (by decide) (by decide) (by taint_decide))) k15_k16) ?_)
  rw [seqs_one]
  exact two_taint [] (pins_nil _) (by taint_decide)

/-- x's range checks. -/
theorem scalar_ct :
    RelCT isa (Two (Ex K2)) (seqs (CheckPrivate.scalarRange)) (Two (Ex K7)) := by
  rw [scalarRange_eq]
  refine RelCT.seqs_append (by simp [isNonzero, geArr, cmpArr]) (by simp) (RelCT.seq (R := Two (Ex K3))
    (show RelCT isa (Two (Ex K2)) (seqs (isNonzero aXm)) (Two (Ex K3)) from
      ex_post (two_map KpP.ws (fun p s ⟨xb, ⟨mi, hI, _⟩, _⟩ => hI.goodW1.1)
        (geArr_ct (by decide) (by decide) (by taint_decide))) k2_k3) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex K4)) (ex_post (two_taint [.x0]
    (pins_x0B KpP.g fun (p : KpP) s (h : Ex K3 p s) => by
      obtain ⟨_, ⟨_, hI, _⟩, _⟩ := h; exact hI.2.1.x0) (by taint_decide)) k3_k4) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex K5)) (ex_post (two_taint [.x0]
    (pins_x0B KpP.B fun (p : KpP) s (h : Ex K4 p s) => by
      obtain ⟨_, ⟨_, hP, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide)) k4_k5) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex K6)) (two_ite
    (fun p s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ => by rw [k5_eval h₁, k5_eval h₂]) ?_ ?_) ?_)
  · simp only [List.cons_append, List.nil_append]
    refine seqs_cons_ct (by simp [ltP, Crt.copyArr]) (RelCT.seq
      (R := Two (Ex fun p xb t => K5e p xb t ∧ p.dl = 2 * p.k)) (ex_post' (two_taint [.x0]
        (pins_x0B KpP.B fun (p : KpP) s (h : Ex K5 p s ∧ _) => by
          obtain ⟨⟨_, ⟨_, hP, _⟩, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide))
        fun p xb s h he => WP.mono (k5_e p xb s h) fun u ⟨hu, k⟩ =>
          ⟨⟨hu, h.1.choose_spec.1.1.noq (Option.some.inj ((k5_eval h).symm.trans he))⟩, k⟩) ?_)
    exact ex_post (two_map KpP.ws (fun p s ⟨xb, ⟨⟨mi, hI, _⟩, _⟩, _⟩ => hI.goodW1)
      (ltP_ct (by decide) (by decide) (by taint_decide) (by taint_decide))) fun p xb s h => e_k6n p xb s h.1 h.2
  · simp only [List.cons_append, List.nil_append]
    refine seqs_cons_ct (by simp [Crt.loadArr]) (RelCT.seq
      (R := Two (Ex fun p xb t => K5e p xb t ∧ p.dl = 3 * p.k)) (ex_post' (two_taint [.x0]
        (pins_x0B KpP.B fun (p : KpP) s (h : Ex K5 p s ∧ _) => by
          obtain ⟨⟨_, ⟨_, hP, _⟩, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide))
        fun p xb s h he => WP.mono (k5_e p xb s h) fun u ⟨hu, k⟩ =>
          ⟨⟨hu, h.1.choose_spec.1.1.q (Option.some.inj ((k5_eval h).symm.trans he))⟩, k⟩) ?_)
    refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp [ltArr, cmpArr]) (RelCT.seq (R := Two (Ex K5q))
      (ex_post (two_map (fun p : KpP => (⟨⟨p.B, p.Z, inner ((p.k + 7) / 8), (p.k + 7) / 8, (p.k + 7) / 8⟩,
          p.dp + BitVec.ofNat 64 (2 * p.k), p.k⟩ : BPub)) (fun p s ⟨xb, h⟩ => e_lpreQ p xb s h.1 h.2)
        (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) fun p xb s h => e_q p xb s h.1 h.2) ?_)
    exact ex_post (two_map KpP.ws (fun p s ⟨xb, ⟨mi, hI, _⟩, _⟩ => hI.goodW1.1)
      (ltArr_ct (by decide) (by decide) (by taint_decide))) q_k6
  rw [seqs_one]
  exact ex_post (two_taint [.x0] (pins_x0B KpP.g fun (p : KpP) s (h : Ex K6 p s) => by
    obtain ⟨_, ⟨_, hI, _⟩, _⟩ := h; exact hI.2.1.x0) (by taint_decide)) k6_k7

/-- The main part, for a valid p. -/
theorem main_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => Ex CE' p s ∧ isa.eval (.zero .x .x9) s = some false)
      (CheckPrivate.main W.code S.code M.mm) fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [pSetup]) (by simp [Crt.loadArr]) (RelCT.seq (R := Two (Ex K1))
    (two_post (two_map (fun p : KpP => (⟨p.B, p.Z, p.k, p.dp⟩ : DPub)) (fun p s ⟨⟨xb, h⟩, he⟩ =>
      ce_setupP _ s h.1 he) setup_ct) fun p s ⟨⟨xb, h⟩, he⟩ => WP.mono (ce_in _ s h.1 he) fun u ⟨hu, _⟩ =>
        ⟨xb, hu, h.2⟩) ?_)
  refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp [CheckPrivate.scalarRange]) (RelCT.seq
    (R := Two (Ex K2)) (ex_post (two_map (fun p : KpP => (⟨⟨p.B, p.Z, inner ((p.k + 7) / 8), (p.k + 7) / 8,
      (p.k + 7) / 8⟩, p.xp, p.xl⟩ : BPub)) (fun p s ⟨xb, h⟩ => k1_lpre' p xb s h)
      (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) k1_k2) ?_)
  refine RelCT.seqs_append (by simp [CheckPrivate.scalarRange]) (by simp) (RelCT.seq (R := Two (Ex K7))
    scalar_ct ?_)
  rw [seqs_one]
  refine two_ite (fun p s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ => by rw [k7_eval h₁, k7_eval h₂])
    (two_taint [] (pins_nil _) (by taint_decide)) ?_
  refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp [range]) (RelCT.seq (R := Two (Ex K8))
    (ex_post' (two_map (fun p : KpP => (⟨⟨p.B, p.Z, inner ((p.k + 7) / 8), (p.k + 7) / 8, (p.k + 7) / 8⟩, p.yp,
        p.yb.length⟩ : BPub)) (fun p s ⟨⟨xb, ⟨mi, hI, _⟩, ho⟩, _⟩ => hI.lpreY ho)
      (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) fun p xb s h he => k7_k8 p xb s h he) ?_)
  refine RelCT.seqs_append (by simp [range]) (by simp) (RelCT.seq (R := Two (Ex K9))
    (ex_post (two_map KpP.ws (fun p s ⟨xb, ⟨mi, hI, _⟩, _⟩ => hI.goodW1) (range_ct (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide))) k8_k9) ?_)
  rw [seqs_one]
  exact two_ite (fun p s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ => by rw [k9_eval h₁, k9_eval h₂]; rfl)
    (two_taint [] (pins_nil _) (by taint_decide)) (tail_ct W M S)

/-- `CheckPrivate.code` leaks the same in runs with the same public data. -/
theorem kp_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two (Ex CR)) (CheckPrivate.code W.code S.code M.mm) fun _ _ => True := by
  unfold CheckPrivate.code
  refine RelCT.seq (R := Two (Ex CE')) (RelCT.block_append (RelCT.seq (two_piece (Ψ := Ex E1')
      [.x0, .x1, .x2, .x3, .x5, .x6, .x7] (pins_of entryRegs fun p s ⟨xb, h⟩ => cr_regs p xb s h) (by taint_decide)
      fun p s ⟨xb, h⟩ => WP.mono (cr_e1 p xb s h) fun _ h' => ⟨xb, h'.1, cr_ok h⟩)
    (ex_post (two_map (fun p : KpP => (⟨p.B, p.Z, p.k, p.dp⟩ : DPub)) (fun p s ⟨_, h, _⟩ => h.dhp) domHead_ct)
      fun p xb s h => WP.mono (e1_ce _ s h.1) fun u ⟨hu, k⟩ => ⟨⟨hu, h.2⟩, k⟩))) ?_
  exact two_ite (fun p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ => by rw [ce_eval h₁, ce_eval h₂]; rfl)
    (two_taint [] (pins_nil _) (by taint_decide)) (main_ct W M S)

/-- The public data of the second run. -/
theorem cr_pub {s₁ s₂ : State} (h₂ : kpPre s₂) (hp : kpPub s₁ s₂) : CR (kpOf s₁) (kpX s₂) s₂ := by
  obtain ⟨hr, hsp, ha, hl⟩ := hp
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hr
  rw [stackArgs_one, stackArgs_one] at ha
  simp only [List.cons.injEq, and_true] at ha
  unfold kpLeak at hl
  simp only [List.append_assoc] at hl
  obtain ⟨hd, hl'⟩ := List.append_inj hl (by simp [kpDom, Spec.Rsa.bytesAt, r1])
  obtain ⟨hy, hs⟩ := List.append_inj hl' (by simp [kpY, Spec.Rsa.bytesAt, r4])
  have hd' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd
  have hy' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hy
  simp only [List.cons.injEq, and_true] at hs
  refine ⟨h₂, hsp.symm, r7.symm, by rw [← ha]; rfl, by rw [← r2]; rfl, by rw [← r1]; rfl, r0.symm, hd'.symm,
    r3.symm, hy'.symm, r5.symm, by rw [← r6]; rfl, rfl, ?_⟩
  -- Whether x is in range, from the statuses.
  show privateValid (domainOf (s₁.gpr .x2).toNat (kpDom s₁)) (Spec.Rsa.os2ip (kpX s₁)) =
    privateValid (domainOf (s₁.gpr .x2).toNat (kpDom s₁)) (Spec.Rsa.os2ip (kpX s₂))
  rw [r2, hd'] at hs ⊢
  rw [hy'] at hs
  unfold privateStatus at hs
  generalize privateValid _ (Spec.Rsa.os2ip (kpX s₁)) = b₁ at hs ⊢
  generalize privateValid _ (Spec.Rsa.os2ip (kpX s₂)) = b₂ at hs ⊢
  cases b₁ <;> cases b₂ <;> simp at hs ⊢ <;> split at hs <;> simp at hs

/-- `vg_ffdh_check_private` is constant time. -/
theorem kp_constantTime (W : Window) (M : Mont) (S : Selector) :
    ConstantTime isa kpContract.pre kpContract.pub (CheckPrivate.code W.code S.code M.mm) :=
  RelCT.constantTime ((kp_ct W M S).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ =>
    ⟨kpOf s₁, ⟨kpX s₁, cr_of s₁ h₁⟩, ⟨kpX s₂, cr_pub h₂ hp⟩, hp.2.1⟩) fun _ _ h => h)

end VG.Proof.Ffdh.AArch64.CheckPrivate
