module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.OutputCT
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Outputs
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.ArithmeticBridge
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.OutputCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Outputs
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.ArithmeticBridge
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH on x86-64: public-key encoding reuses exchange's timing proof -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (sLink ws)

/-- A generator power and a writable output, as private-key validation
computes it: what the public output's timing depends on. -/
def KBV (p : CheckPrivate.KpP) (s : State) : Prop := ∃ xb,
  CheckPrivate.Value p xb s ∧ OutOk s p.B p.Z p.yp p.k

private def EV (p : CheckPrivate.KpP) (s : State) : Prop := ∃ xb, Exchange.Value (outputP p) xb s
private def EC (p : CheckPrivate.KpP) (s : State) : Prop := ∃ xb, Exchange.Checked (outputP p) xb s

private def bridgeRest : List Instr :=
  [.mov .rdx (.mem (ws .rax sY)), .store (ws .rax VG.Impl.Ffdh.X86_64.Domain.sOut) .rdx,
    .mov .rdx (.mem (ws .rax sG)), .store (ws .rax sY) .rdx]

private theorem bridge_ptr (p : CheckPrivate.KpP) (s : State) (h : KBV p s) :
    WP isa (.block [.mov .rax (.mem (hdr sLink))]) s fun t => t.gpr .rax = p.B := by
  obtain ⟨_, ⟨⟨mi, _, hc, _⟩, _⟩, _⟩ := h
  have hld := hc.sub.good.scr.ld (hdr_lt_slot p.w 8 (show sLink < 32 by decide))
  xrun [State.ea, hdr, hc.sub.rdi, hdrOff, hld, hc.sub.link]

private theorem bridge_ct : RelCT isa (Two KBV) (.block bridge) (Two EV) := by
  change RelCT isa (Two KBV) (.block ([.mov .rax (.mem (hdr sLink))] ++ bridgeRest)) (Two EV)
  refine RelCT.block_append (pin_ct [.rdi] [.rax] (fun p _ => p.B)
    (pins_rdiB (fun p => off p.B (inner p.w)) fun _ _ h => by
      obtain ⟨_, ⟨⟨_, _, hc, _⟩, _⟩, _⟩ := h; exact hc.sub.rdi)
    (by taint_decide) ?_ (by taint_decide) ?_)
  · intro p s h
    exact WP.mono (bridge_ptr p s h) fun _ hh r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hh
  · intro p s h
    obtain ⟨xb, hv, ho⟩ := h
    have hw : WP isa (.block bridge) s (EV p) :=
      WP.mono (value_bridge hv ho) fun _ ⟨he, _⟩ => ⟨xb, he⟩
    change WP isa (.block ([.mov .rax (.mem (hdr sLink))] ++ bridgeRest)) s (EV p) at hw
    exact WP.seq_iff.mpr (WP.block_append_iff.mp hw)

private theorem ev_good (p : CheckPrivate.KpP) (s : State) (h : EV p s) : GoodW1 (outputP p).ws s := by
  obtain ⟨_, ⟨mi, _, hc⟩, _⟩ := h
  exact ⟨⟨mi, hc.sub.good, Nat.le_refl _⟩, Nat.le_trans (by decide) hc.w2,
    Nat.lt_trans hc.w28 (by decide)⟩

private theorem ev_checked (p : CheckPrivate.KpP) (s : State) (h : EV p s) :
    WP isa (seqs (range aY)) s (EC p) := by
  obtain ⟨xb, hv⟩ := h
  exact WP.mono (Exchange.value_checked hv) fun _ ⟨hc, _⟩ => ⟨xb, hc⟩

/-- The public output's timing depends only on the public parameters. -/
theorem public_ct : RelCT isa (Two KBV) (seqs publicOutput) fun _ _ => True := by
  unfold publicOutput
  refine seqs_cons_ct (by simp [range]) (RelCT.seq bridge_ct ?_)
  refine RelCT.seqs_append (a := range aY) (by simp [range]) (by simp)
    (RelCT.seq (R := Two EC)
      (two_post (two_map (fun p => (outputP p).ws) ev_good
        (range_ct (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))) ev_checked) ?_)
  exact two_map outputP (fun _ _ h => by obtain ⟨xb, hc⟩ := h; exact ⟨_, hc⟩) Exchange.output_ct

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
  two_post (two_map GkP.kp (fun _ _ h => by obtain ⟨rb, hv, hb⟩ := h; exact ⟨_, hv, hb.oy⟩) public_ct) value_mask

end VG.Proof.Ffdh.X86_64.GenerateKey
