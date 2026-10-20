module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Load
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH parameter generation on x86-64: load a masked witness into Xm -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem loadWitness_ok {p : WitnessParams} {s : State}
    (h : ModulusReady s p.I p.IZ p.w p.mi p.N)
    (ho : OutOk s p.I p.IZ p.op p.len)
    (hsi : s.gpr .rsi = p.op) (hcx : s.gpr .rcx = BitVec.ofNat 64 p.len)
    (hv : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem p.op p.len) < 2 ^ (64 * p.w)) :
    WP isa (loadNumber aXm) s fun t =>
      ModulusReady t p.I p.IZ p.w p.mi p.N ∧
      wv t.mem p.I (slot p.w aXm) p.w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem p.op p.len) ∧
      Frm p.I [(slot p.w aXm, 8 * (p.w + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  let bs := Spec.Rsa.bytesAt s.mem p.op p.len
  have hlen : bs.length = p.len := bytesAt_length _ _ _
  have hw : p.w = (bs.length + 7) / 8 := by rw [hlen]; exact p.width
  have hb := p.width_bounds
  have hcx' : s.gpr .rcx = BitVec.ofNat 64 bs.length := by rw [hlen]; exact hcx
  refine WP.mono (loadNumber_ok (by decide : aXm < 8) h.good p.dims.z hsi hcx'
    (by omega_using [hlen, hb.2.2.1]) (by omega_using [hlen, hb.2.2.2.1])
    (by omega_using [hw]) (by omega_using [hw]) hv
    (fun i hi => by
      obtain ⟨r, hr, hc⟩ := ho.wr i (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (fun i hi => bytesAt_read _ _ (by omega : i < p.len))
    (fun i hi => Or.inr (by
      have hs := ho.sep i (by omega)
      change p.IZ ≤ ofs p.I (off p.op i) at hs
      have hf := slot_le (w := p.w) (show aXm < 8 by decide)
      omega_using [hs, hf, hw, p.dims.z]))) fun t ⟨hv', hg, hf, k⟩ => ?_
  have hf' : Frm p.I [(slot p.w aXm, 8 * (p.w + 2))] s.mem t.mem :=
    Frm.of_outside (hf.mono (o' := slot p.w aXm) (n' := 8 * (p.w + 2)) (Nat.le_refl _) (by omega_using [hw])) (by simp)
  refine ⟨h.of_frm p.dims hf' k hg.rdi (by rng_disj) (by rng_disj) (by rng_disj), hv', hf',
    k.mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
