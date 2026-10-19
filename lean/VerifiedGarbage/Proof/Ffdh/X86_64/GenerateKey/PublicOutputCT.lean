module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.OutputCT
meta import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Outputs
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.ArithmeticBridge
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
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
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Context
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarBound
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarLess
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Correct
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Entry
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Output
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Bridge
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Context
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CutFinish
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CutInputs
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Finish
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Mask
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskOutput
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskSetup
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.OutputBytes
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Scalar
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.ScalarCT
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
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops

/-! # FFDH on x86-64: public-key encoding reuses exchange's timing proof -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (sLink ws)

private def BV (p : GkP) (s : State) : Prop := ∃ rb,
  CheckPrivate.Value p.kp (p.xb rb) s ∧ OutOk s p.B p.Z p.yp p.k

private def EV (p : GkP) (s : State) : Prop := ∃ rb, Exchange.Value (outputP p.kp) (p.xb rb) s
private def EC (p : GkP) (s : State) : Prop := ∃ rb, Exchange.Checked (outputP p.kp) (p.xb rb) s

private def bridgeRest : List Instr :=
  [.mov .rdx (.mem (ws .rax sY)), .store (ws .rax VG.Impl.Ffdh.X86_64.Domain.sOut) .rdx,
    .mov .rdx (.mem (ws .rax sG)), .store (ws .rax sY) .rdx]

private theorem bridge_ptr (p : GkP) (s : State) (h : BV p s) :
    WP isa (.block [.mov .rax (.mem (hdr sLink))]) s fun t => t.gpr .rax = p.B := by
  obtain ⟨_, ⟨⟨mi, _, hc, _⟩, _⟩, _⟩ := h
  have hld := hc.sub.good.scr.ld (hdr_lt_slot p.w 8 (show sLink < 32 by decide))
  xrun [State.ea, hdr, hc.sub.rdi, hdrOff, hld, hc.sub.link]
  rfl

private theorem bridge_ct : RelCT isa (Two BV) (.block bridge) (Two EV) := by
  change RelCT isa (Two BV) (.block ([.mov .rax (.mem (hdr sLink))] ++ bridgeRest)) (Two EV)
  refine RelCT.block_append (pin_ct [.rdi] [.rax] (fun p _ => p.B)
    (pins_rdiB (fun p => off p.B (inner p.w)) fun _ _ h => by
      obtain ⟨_, ⟨⟨_, _, hc, _⟩, _⟩, _⟩ := h; exact hc.sub.rdi)
    (by taint_decide) ?_ (by taint_decide) ?_)
  · intro p s h
    exact WP.mono (bridge_ptr p s h) fun _ hh r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hh
  · intro p s h
    obtain ⟨rb, hv, ho⟩ := h
    have hw : WP isa (.block bridge) s (EV p) :=
      WP.mono (value_bridge hv ho) fun _ ⟨he, _⟩ => ⟨rb, he⟩
    change WP isa (.block ([.mov .rax (.mem (hdr sLink))] ++ bridgeRest)) s (EV p) at hw
    exact WP.seq_iff.mpr (WP.block_append_iff.mp hw)

private theorem ev_good (p : GkP) (s : State) (h : EV p s) : GoodW1 (outputP p.kp).ws s := by
  obtain ⟨_, ⟨mi, _, hc⟩, _⟩ := h
  exact ⟨⟨mi, hc.sub.good, Nat.le_refl _⟩, Nat.le_trans (by decide) hc.w2,
    Nat.lt_trans hc.w28 (by decide)⟩

private theorem ev_checked (p : GkP) (s : State) (h : EV p s) :
    WP isa (seqs (range aY)) s (EC p) := by
  obtain ⟨rb, hv⟩ := h
  exact WP.mono (Exchange.value_checked hv) fun _ ⟨hc, _⟩ => ⟨rb, hc⟩

private theorem public_ct : RelCT isa (Two BV) (seqs publicOutput) fun _ _ => True := by
  unfold publicOutput
  refine seqs_cons_ct (by simp [range]) (RelCT.seq bridge_ct ?_)
  refine RelCT.seqs_append (a := range aY) (by simp [range]) (by simp)
    (RelCT.seq (R := Two EC)
      (two_post (two_map (fun p => (outputP p.kp).ws) ev_good
        (range_ct (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))) ev_checked) ?_)
  exact two_map (fun p => outputP p.kp) (fun _ _ h => by obtain ⟨rb, hc⟩ := h; exact ⟨_, hc⟩) Exchange.output_ct

/-- A computed generator power with its full scalar and output buffers. -/
def ValueIn (p : GkP) (s : State) : Prop := ∃ rb,
  CheckPrivate.Value p.kp (p.xb rb) s ∧ Buffers p rb s

private theorem value_mask (p : GkP) (s : State) (h : ValueIn p s) :
    WP isa (seqs publicOutput) s (MaskPre p) := by
  obtain ⟨rb, hv, hb⟩ := h
  have hZ : 128 * p.k + 256 ≤ p.Z := hv.1.choose_spec.1.hZ
  have hk : p.k ≤ 1024 := hv.1.choose_spec.1.k2
  refine WP.mono (publicOutput_ok hv hb.x hb.oy hb.xy hb.len) fun t ht => ?_
  obtain ⟨_, hax, hd, _, hs, hx, hn, hK, _, _, k⟩ := ht
  refine ⟨hs, hd, by omega, by omega, hb.ld, hx, hn, hK,
    ⟨fun i hi => by rw [k.2.2]; exact hb.ox.wr i hi, hb.ox.sep⟩, decide (p.fl rb), ?_⟩
  exact hax.trans (bit_eq_bool (p.fl rb))

theorem public_mask_ct : RelCT isa (Two ValueIn) (seqs publicOutput) (Two MaskPre) :=
  two_post (two_map id (fun _ _ h => by obtain ⟨rb, hv, hb⟩ := h; exact ⟨rb, hv, hb.oy⟩) public_ct) value_mask

end VG.Proof.Ffdh.X86_64.GenerateKey
