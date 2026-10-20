module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WriteUsed
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # FFDH parameter generation on x86-64: the callable's final store and ABI return -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem finishTail_ok {p : CandidateP} {used status : Nat} {s₀ s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B)
    (hs : word s.mem p.B (8 * oStatus) = BitVec.ofNat 64 status) (hstatus : status < 2 ^ 64)
    (hsaved : ∀ i < 6, word s.mem p.B (8 * i) = s₀.gpr (saved.getD i .rax)) :
    WP isa (.block (([.mov .rax (.mem (hdr oStatus)), .mov .rdx (.mem (hdr oUsedP)), .mov .rcx (.mem (hdr oUsed)),
      .alu .test .rax (.reg .rax), .cmov .e .rcx (.reg .rax), .store (at0 .rdx) .rcx] : List Instr) ++ exit)) s
      fun t => t.gpr .rax = BitVec.ofNat 64 status ∧
        word t.mem p.up 0 = BitVec.ofNat 64 (if status = 0 then 0 else used) ∧
        Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.bytesAt s.mem p.op p.k ∧
        (∀ r ∈ saved, t.gpr r = s₀.gpr r) ∧
        Keep (saved ++ ([.rax, .rdx, .rcx] : List Reg)) s t := by
  rw [WP.block_append_iff]
  refine WP.mono (writeUsed_ok h hdi hs hstatus)
    fun u ⟨hax, hdu, hused, hout, hwords, ku⟩ => ?_
  refine WP.mono (VG.Proof.Ffdh.X86_64.exit_ok (h.base.scr.congr ku.2.2) hdu
    (by omega_using [h.base.header_room])
    (fun i hi => (hwords i (by omega)).trans (hsaved i hi)))
    fun t ⟨hregs, hm, kt⟩ => ?_
  exact ⟨(kt.gpr (by decide)).trans hax, by rw [hm]; exact hused,
    by rw [hm]; exact hout, hregs, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
