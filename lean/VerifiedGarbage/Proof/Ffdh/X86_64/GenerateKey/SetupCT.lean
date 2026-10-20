module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.TailCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.ScalarCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.StagesCT
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.TailCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.ScalarCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.Octets

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
