module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Uniform
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega

/-! # The stored uniform mask agrees with the branch condition -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem saveUniform_ok {s : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64} {u : Bool}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w)
    (hax : s.gpr .rax = BitVec.ofNat 64 u.toNat) :
    WP isa (.block Impl.Dsa.X86_64.Generation.saveUniform) s fun t =>
      ModulusReady t B Z w mi N ∧ word t.mem B (8 * kU) = mask u ∧ t.zf = some (!u) ∧
      Frm B [(8 * kU, 8)] s.mem t.mem ∧ Keep [.rax, .rcx] s t := by
  have hst : InRegions s.wr (off B (8 * kU)) 8 :=
    h.good.scr.st (by have := hdr_lt_slot w 8 (show kU < 32 by decide); have := hd.z; omega)
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t =>
      t.mem = s.mem.writeW (off B (8 * kU)) (mask u) ∧ t.zf = some (!u)) (by
    xrun [Impl.Dsa.X86_64.Generation.saveUniform, State.ea, hdr, hdrOff, h.good.rdi, hst, hax,
      BitVec.and_self]
    cases u <;> exact ⟨rfl, by decide⟩) rfl) fun t ⟨⟨hm, hz⟩, hk⟩ => ?_
  have hf : Frm B [(8 * kU, 8)] s.mem t.mem := by
    rw [hm]
    exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kU) (by decide)) (by simp)
  refine ⟨h.of_frm hd hf hk ((hk.gpr (by decide)).trans h.good.rdi)
    (by simp; decide) (by rng_disj) (by rng_disj), ?_, hz, hf, hk⟩
  rw [hm, word_writeW_self]

end VG.Proof.Dsa.X86_64.Generation
