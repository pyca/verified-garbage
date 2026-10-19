module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.TailCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.ScalarCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.TailCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.StagesCT
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
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
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Correct
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Entry
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Main
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarBound
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarLess
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.TailCT
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Correct
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Entry
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Output
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.OutputCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.ArithmeticBridge
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Bridge
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Context
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CutFinish
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CutInputs
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Finish
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Mask
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskOutput
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskSetup
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.OutputBytes
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Outputs
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.PublicOutputCT
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Scalar
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Status
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Ffdh.X86_64.Scan
import VerifiedGarbage.Proof.Ffdh.X86_64.ScanRawCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
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
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
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
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Correct
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Entry
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Main
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Math
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarBound
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarLess
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
meta import VerifiedGarbage.Proof.Ffdh.X86_64.R2
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
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

/-! # FFDH on x86-64: set up the private-scalar core in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (loadArr)

abbrev GkP.d (p : GkP) : DPub := ⟨p.B, p.Z, p.k, p.dp⟩

private theorem sliced_setup (p : GkP) (s : State) (h : Sliced p s) : SetupP p.d s := by
  obtain ⟨_, hb, hd, _, _, hm, _⟩ := h
  have ho := (valid_facts hm hb.k1).1
  exact ⟨p.pb, hb.scr, hd, hb.k1, hb.k2, hb.hZ,
    hb.hdr (sDom, p.dp) (by simp [CheckPrivate.KpP.headers, GkP.kp]),
    hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CheckPrivate.KpP.headers, GkP.kp]),
    hb.dom.take p.k, hb.plen, ho⟩

private def Before (p : GkP) (s : State) : Prop := ∃ rb mi,
  CheckPrivate.Base p.kp (p.xb rb) s ∧ SubCtx s p.B p.Z (inner p.w) p.w p.w mi ∧
    WP isa (seqs (loadArr aXm sX sXl)) s (WorkIn p)

private theorem sliced_before (p : GkP) (s : State) (h : Sliced p s) :
    WP isa (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)) s (Before p) := by
  obtain ⟨rb, hb, hd, hG, hQ, hm, hbuf⟩ := h
  have hfull := WP.mono (CheckPrivate.setup_work hb hd hG hQ hm) fun t ⟨⟨mi, hw, hdi⟩, hi, _, k⟩ =>
    (show WorkIn p t from ⟨rb, mi, hw, hdi, hm, hbuf.keep hi k⟩)
  have htail : WP isa (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)) s
      fun t => WP isa (seqs (loadArr aXm sX sXl)) t (WorkIn p) := by
    obtain ⟨tr, t, he, hp⟩ := hfull
    exact WP.seq_iff.mp ⟨tr, t, exec_seqs_append (by simp [pSetup]) (by simp [loadArr]) he, hp⟩
  have hsetup : WP isa (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)) s
      fun t => ∃ mi, CheckPrivate.Base p.kp (p.xb rb) t ∧ SubCtx t p.B p.Z (inner p.w) p.w p.w mi :=
    WP.mono (setup_ok (B := p.B) (Z := p.Z) (k := p.k) (dp := p.dp) (pb := p.pb)
      hb.scr hd hb.k1 hb.k2 hb.hZ
      (hb.hdr (sDom, p.dp) (by simp [CheckPrivate.KpP.headers, GkP.kp]))
      (hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CheckPrivate.KpP.headers, GkP.kp]))
      (hb.dom.take p.k) hb.plen (valid_facts hm hb.k1).1)
      fun t ⟨mi, hc, _, _, hf, k⟩ => by
        obtain ⟨hi, hh, _, _⟩ := CheckPrivate.setup_frame (p := p.kp) hb.k1 hb.hZ hf
        exact ⟨mi, hb.keep hi k hh, hc⟩
  exact WP.mono (WP.and hsetup htail) fun _ ⟨⟨mi, hb, hc⟩, hw⟩ => ⟨rb, mi, hb, hc, hw⟩

private theorem before_load (p : GkP) (s : State) (h : Before p s) : LPre aXm sX sXl p.kp.xlPub s := by
  obtain ⟨rb, mi, hb, hc, hw⟩ := h
  refine CheckPrivate.beforeX_load p.kp s ⟨p.xb rb, mi, hb, hc, ?_⟩
  exact WP.mono hw fun _ ⟨rb, mi, hw, hd, hm, _⟩ => ⟨p.xb rb, mi, hw, hd, hm⟩

theorem setup_load_ct : RelCT isa (Two Sliced)
    (seqs ((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++ loadArr aXm sX sXl))
    (Two WorkIn) :=
  RelCT.seqs_append (by simp [pSetup]) (by simp [loadArr])
    (RelCT.seq (R := Two Before)
      (two_post (two_map GkP.d sliced_setup setup_ct) sliced_before)
      (two_post (two_map (fun p => p.kp.xlPub) before_load
        (loadArr_ct (by decide) (by taint_decide) (by taint_decide)))
        (fun _ _ h => h.choose_spec.choose_spec.2.2)))

end VG.Proof.Ffdh.X86_64.GenerateKey
