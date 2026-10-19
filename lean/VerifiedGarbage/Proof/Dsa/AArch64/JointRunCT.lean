module

public import VerifiedGarbage.Proof.Dsa.AArch64.JointByteCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ProductCallCT
public import VerifiedGarbage.Proof.Dsa.AArch64.JointBuildContext
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointByteCT
import VerifiedGarbage.Proof.Dsa.AArch64.JointRun
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointRun
import VerifiedGarbage.Proof.Dsa.AArch64.JointInit
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointInit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Math
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
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
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
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.JointBuild
import VerifiedGarbage.Proof.Dsa.AArch64.JointBuildCT
import VerifiedGarbage.Proof.Dsa.AArch64.JointByteHead
import VerifiedGarbage.Proof.Dsa.AArch64.JointEncode
import VerifiedGarbage.Proof.Dsa.AArch64.JointEncodeCT
import VerifiedGarbage.Proof.Dsa.AArch64.JointPrepareCT
import VerifiedGarbage.Proof.Dsa.AArch64.JointStore
import VerifiedGarbage.Proof.Dsa.AArch64.JointTableInit
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.AArch64.Power
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
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
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointBuild
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointBuildCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointByteHead
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointEncode
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointEncodeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointPrepareCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointStore
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointTableInit
meta import VerifiedGarbage.Proof.Dsa.AArch64.Load
meta import VerifiedGarbage.Proof.Dsa.AArch64.Power
meta import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # Constant time of the joint exponentiation loop and decoding -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure JointPublic extends ProductCallPublic where
  qLen : Nat
  qPositive : 0 < qLen
  qBound : qLen < 2 ^ 31
  parentSpace : 344 ≤ bytes.x.o

def JointPublic.scan (p : JointPublic) : JointBytesPublic :=
  ⟨p.x, off p.x.B u, off p.x.B v, p.qLen⟩

def JointScalars (p : JointPublic) (s : State) : Prop :=
  ∃ eb fb : List Byte, Src s p.x.B p.x.Z (off p.x.B u) eb ∧ Src s p.x.B p.x.Z (off p.x.B v) fb ∧
    eb.length = p.qLen ∧ fb.length = p.qLen ∧
    word s.mem p.x.B Field.qLen.offset = BitVec.ofNat 64 p.qLen

def JointRunPre (p : JointPublic) (s : State) : Prop :=
  SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx p.minv ∧
  JointCtx s (off p.x.B p.x.o) p.x.wx p.modulus p.minv ∧
  (∃ g y, JointTab s.mem (off p.x.B p.x.o) p.x.wx p.modulus g y) ∧
  wv s.mem (off p.x.B p.x.o) (slot p.x.wx aY) p.x.wx = 2 ^ (64 * p.x.wx) % p.modulus ∧
  wv s.mem (off p.x.B p.x.o) (slot p.x.wx aOne) p.x.wx = 1 ∧ JointScalars p s

/-- The link into `x5`: the parent workspace. -/
theorem jointLink_ok {p : JointPublic} {s : State} (h : JointRunPre p s) :
    WP isa (.block [ldh .x5 Crt.sLink]) s fun t => t.gpr .x0 = off p.x.B p.x.o ∧ t.gpr .x5 = p.x.B := by
  have hc := h.1
  exact WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = p.x.B)
    (by brun [hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hc.ld' (show Crt.sLink < 32 by decide), hc.link'])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨h1, k⟩ => ⟨(k.gpr .x0 (by decide)).trans hc.x0, h1⟩

theorem jointInit_ct : RelCT isa (Two JointRunPre) (.block Joint.expInit) (fun _ _ => True) := by
  change RelCT isa _ (.block ([ldh .x5 Crt.sLink] ++ Joint.expInit.tail)) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .x0 = off p.x.B p.x.o ∧ s.gpr .x5 = p.x.B) [.x0]
    (pins_x0B (fun p : JointPublic => off p.x.B p.x.o) (fun _ _ h => h.1.x0)) (by taint_decide)
    fun _ _ h => jointLink_ok h)
    (two_taint [.x0, .x5] (pins_of (fun (p : JointPublic) r => if r = .x0 then off p.x.B p.x.o else p.x.B)
      (by intro p s h r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.1
          · exact h.2)) (by simp only [Joint.expInit, List.tail_cons]; taint_decide))

theorem jointRun_ct (M : Mont) : RelCT isa (Two JointRunPre) (Joint.run M.mm) (fun _ _ => True) := by
  unfold Joint.run seqs
  refine RelCT.seq (two_post (Ψ := fun p : JointPublic => fun s => 0 < p.scan.len ∧ JointBytesInv p.scan 0 s)
    jointInit_ct ?_) ?_
  · rintro p s ⟨hc, hm, ⟨g, y, ht⟩, hy, ho, eb, fb, he, hf, hL, hF, hl⟩
    have hfield : 344 ≤ p.x.Z := by have := hc.hi; have : 344 ≤ p.x.o := p.parentSpace; omega
    refine WP.mono (jointInit_ok hc hm ht hfield hl)
      fun t ⟨hct, hmt, htt, ha, ep, fp, len, idx, hfrm, hk⟩ => ?_
    have het := work_source hc hfrm hk he
    have hft := work_source hc hfrm hk hf
    have hyt := (ha aY (by decide)).trans hy
    have hI : JointByteInv t (off p.x.B p.x.o) p.x.wx p.minv p.modulus
        (wv t.mem (off p.x.B p.x.o) (slot p.x.wx Crt.aXc) p.x.wx) g y
        (off p.x.B u) (off p.x.B v) p.qLen eb fb 0 t := by
      refine ⟨hmt.exp, htt, ?_, ?_, idx, ep, fp, len, Frm.refl _ _ _, Keep.refl _ _⟩
      · rw [hyt]; exact Nat.mod_lt _ (by have := p.greater; omega)
      · rw [hyt, Nat.mod_mod, pre_zero, pre_zero, Nat.pow_zero, Nat.pow_zero, Nat.one_mul]
    dsimp only [JointBytesInv, JointPublic.scan]
    exact ⟨p.qPositive, t, p.minv, p.modulus, _, g, y, eb, fb, hI, p.lower,
      by have : p.x.wx ≤ 48 := p.width48; omega, coprime_pow2 p.odd _, hL, hF, p.qBound, het, hft,
      by simpa only [hL] using joint_source_out hct het,
      by simpa only [hF] using joint_source_out hct hft⟩
  refine RelCT.seq (two_map JointPublic.scan (fun _ _ h => h) (jointBytes_ct M)) ?_
  exact two_map (fun p : JointBytesPublic => p.x.ws)
    (fun _ _ ⟨_, minv, _, _, _, _, _, _, hI, _⟩ => ⟨minv, hI.ctx.good, Nat.le_refl _⟩)
    (M.ct (by unfold MmUse; decide))

end VG.Proof.Dsa.AArch64
