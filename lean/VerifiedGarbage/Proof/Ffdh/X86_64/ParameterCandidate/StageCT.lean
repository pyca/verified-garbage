module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCTData
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LinkCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeOriginal
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.HalveOutput
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseSetup
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LoadOutput
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: timing of candidate phase setup -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (sLink ws)
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen.X86_64

theorem shape_outer (d : CandidatePublic) (s : State) (h : OuterState d s) :
    WP isa shapeOriginal s (OuterValue false d) :=
  WP.mono (shapeOriginal_ok h.1.1 h.2 d.available)
    fun _ ⟨ht, hd, hv, _, _, k, _⟩ => ⟨⟨⟨ht, k.2.2.trans h.1.2.1, h.1.2.2⟩, hd⟩, hv⟩

theorem halve_outer (d : CandidatePublic) (s : State) (h : OuterValue false d s) :
    WP isa halveOutput s (OuterValue true d) :=
  WP.mono (halveOutput_ok h.1.1.1 h.1.2 h.2)
    fun _ ⟨ht, hd, hv, _, _, k⟩ => ⟨⟨⟨ht, k.2.2.trans h.1.1.2.1, h.1.1.2.2⟩, hd⟩, hv⟩

theorem setup_phase (q : Bool) (d : CandidatePublic) (s : State) (h : OuterValue q d s) :
    WP isa (phaseSetup q) s (PhaseSet q d) :=
  WP.mono (phaseSetup_state_ok h.1.1.1 h.1.2 q)
    fun _ ⟨mi, ht, hg, hp, _, _, k, hv⟩ =>
      ⟨⟨ht, k.2.2.trans h.1.1.2.1, h.1.1.2.2⟩, mi, hg, hp, by rw [hv]; exact h.2⟩

theorem load_phase (q : Bool) (d : CandidatePublic) (s : State) (h : PhaseSet q d s) :
    WP isa loadOutput s (PhaseLoaded q d) := by
  obtain ⟨mi, hg, hp, hv⟩ := h.2
  exact WP.mono (loadOutput_ok h.1.1 hg hp hv) fun _ ⟨ht, hgt, hpt, hnt, _, _, k, _⟩ =>
    ⟨⟨ht, k.2.2.trans h.1.2.1, h.1.2.2⟩, mi, hgt, hpt, hnt⟩

private theorem set_link {q : Bool} {d : CandidatePublic} {s : State} (h : PhaseSet q d s) :
    LinkHeader ⟨d.p.B, d.wr⟩ s := by
  obtain ⟨_, hg, hp, _⟩ := h.2
  exact ⟨h.1.2.2, hg.rdi, h.1.2.1, fun e he => by
    simp only [List.mem_singleton] at he; subst e; exact hp.link⟩

private theorem load_number (q : Bool) (d : CandidatePublic) (s : State) (h : PhaseSet q d s) :
    WP isa (.block [.mov .rax (.mem (hdr sLink)), .mov .rsi (.mem (ws .rax oOut)), .mov .rcx (.mem (ws .rax oLen))]) s
      (InnerNumber (d.inner q)) := by
  obtain ⟨mi, hg, hp, _⟩ := h.2
  have hb := h.1.1.base
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off d.p.B (8 * j)) 8 :=
    fun j hj => hb.scr.ld (by omega_using [hj, hb.header_room])
  have hlinkrd := hg.scr.ld (show 8 * sLink + 8 ≤ d.p.Z - 256 by
    have hz := (hb.phase_dims q).z
    change 136 ≤ d.p.Z - 256; unfold slot hdrBytes at hz; omega)
  have hout := hb.hdr (oOut, d.p.op) (by simp [CandidateP.headers])
  have hlen := hb.hdr (oLen, BitVec.ofNat 64 d.p.k) (by simp [CandidateP.headers])
  refine WP.mono (WP.keep [.rax, .rsi, .rcx] (Q := fun t => t.gpr .rsi = d.p.op ∧
    t.gpr .rcx = BitVec.ofNat 64 d.p.k ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, ws, hdrOff, hg.rdi, hp.link, hlinkrd, hout, hlen,
      hrd oOut (by decide), hrd oLen (by decide)]) rfl)
    fun t ⟨⟨hsi, hcx, hm⟩, k⟩ => ?_
  have hgt : Good t (off d.p.B 256) (d.p.Z - 256) (d.p.phaseWords q) mi :=
    ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩
  exact ⟨⟨h.1.2.2, good_hp hgt (k.2.2.trans h.1.2.1)⟩, hsi, hcx⟩

theorem loadOutput_ct (q : Bool) : RelCT isa (Two (PhaseSet q)) loadOutput fun _ _ => True := by
  unfold loadOutput
  exact RelCT.seq (two_post
    (two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic)) (fun _ _ h => set_link h) loadOutputHead_ct)
    (load_number q)) (two_map (fun d : CandidatePublic => d.inner q) (fun _ _ h => h) inner_loadCandidate_ct)

end VG.Proof.Ffdh.X86_64.ParameterCandidate
