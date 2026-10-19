module
public import VerifiedGarbage.Proof.Dsa.X86_64.ProductCallCT
public import VerifiedGarbage.Proof.Dsa.X86_64.JointHeadCT
public import VerifiedGarbage.Proof.Dsa.X86_64.JointBuildContext
public import VerifiedGarbage.Proof.Dsa.X86_64.JointWindow

import VerifiedGarbage.Proof.Dsa.X86_64.JointByteCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointByteCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointRun
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointRun
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointPrepareCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Dsa.X86_64.JointInit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
import VerifiedGarbage.Proof.Dsa.X86_64.JointBuild
import VerifiedGarbage.Proof.Dsa.X86_64.JointByteHead
import VerifiedGarbage.Proof.Dsa.X86_64.JointEncode
import VerifiedGarbage.Proof.Dsa.X86_64.JointEntries
import VerifiedGarbage.Proof.Dsa.X86_64.JointPrepare
import VerifiedGarbage.Proof.Dsa.X86_64.JointPrepareCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointStore
import VerifiedGarbage.Proof.Dsa.X86_64.JointWindowCT
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Power
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
meta import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointBuild
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointByteHead
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointEncode
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointEntries
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointPrepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointStore
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointWindowCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Power
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # Constant time of the joint exponentiation loop and decoding -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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

theorem jointInit_ct : RelCT isa (Two JointRunPre) (.block Joint.expInit) (fun _ _ => True) := by
  change RelCT isa _ (.block ([.mov .rax (.mem (hdr Crt.sLink))] ++ Joint.expInit.tail)) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .rdi = off p.x.B p.x.o ∧ s.gpr .rax = p.x.B) [.rdi]
    (pins_rdi (fun p : JointPublic => off p.x.B p.x.o) (fun _ _ h => h.1.rdi)) (by taint_decide) ?_)
    (two_taint [.rdi, .rax] (pins_of (fun (p : JointPublic) r => if r = .rdi then off p.x.B p.x.o else p.x.B)
      (by intro p s h r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.1
          · exact h.2)) (by simp only [Joint.expInit, List.tail_cons]; taint_decide))
  intro p s h
  have hc := h.1
  xrun [State.ea, hdr, hc.rdi, hdrOff, hc.link,
    hc.good.scr.ld (show 8 * Crt.sLink + 8 ≤ slot p.x.wx 8 by
      have := hdr_lt_slot p.x.wx 8 (show Crt.sLink < 32 by decide); omega)]

theorem jointRun_ct (M : Mont) (Sq : MontS) : RelCT isa (Two JointRunPre) (Joint.run Sq.mm M.mm) (fun _ _ => True) := by
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
  refine RelCT.seq (two_map JointPublic.scan (fun _ _ h => h) (jointBytes_ct M Sq)) ?_
  exact two_map (fun p : JointBytesPublic => p.x.ws)
    (fun _ _ ⟨_, minv, _, _, _, _, _, _, hI, _⟩ => ⟨minv, hI.ctx.good, Nat.le_refl _⟩)
    (M.ct (by unfold MmUse; decide))

end VG.Proof.Dsa.X86_64
