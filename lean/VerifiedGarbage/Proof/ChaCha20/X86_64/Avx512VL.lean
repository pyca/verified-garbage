module

public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512VL
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Verified
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512VL
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Verified
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.ChaCha20.Contract

/-!
# ChaCha20 on x86-64 with AVX-512, short data in `ymm` registers: verified

The comparison changes only the flags, which neither kernel's precondition
nor postcondition reads: each branch is its kernel's `correct` from the
state after it (`cmpLim_ok`). Constant time: the branch is on the length.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512VL

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512VL
open VG.Proof.ChaCha20.X86_64.Avx2 (APre eL xorAvx2X86_64)

set_option simprocs false in
theorem cmpLim_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 shortLim))]) s fun t =>
      (∃ cf of zf sf, t = s.setFlags cf of zf sf) ∧ t.cf = some (decide (eL s < shortLim)) := by
  have se : BitVec.signExtend 64 (BitVec.ofNat 32 shortLim) = BitVec.ofNat 64 shortLim := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left', se]
  exact ⟨⟨_, _, _, _, rfl⟩, rfl⟩

theorem apre_setFlags {s : State} (hp : APre s) (cf of zf sf : Option Bool) :
    APre (s.setFlags cf of zf sf) :=
  ⟨hp.1, hp.2, hp.3, hp.4, hp.5, hp.6, hp.7, hp.8, hp.9, hp.10, hp.11⟩

theorem correct {s₀ : State} (hp : APre s₀) :
    WP isa xorBy s₀ fun s' =>
      (gprPreserved s₀ s' ∧ xorAvx2X86_64.post s₀ s') ∧ s'.gpr .rsi = s₀.gpr .rcx := by
  refine WP.seq (WP.mono (cmpLim_ok s₀) fun t ⟨⟨cf, of, zf, sf, e⟩, hc⟩ => ?_)
  subst e
  refine WP.ite (decide (eL s₀ < shortLim)) (by simp [eval, hc]) (fun _ => ?_) (fun _ => ?_)
  · exact Avx2.correct true (apre_setFlags hp cf of zf sf)
  · exact Avx512.correct (apre_setFlags hp cf of zf sf)

theorem xor_rsi (s : State) (hs : xorAvx2X86_64.pre s) :
    ∃ t s', Exec isa xorBy s t s' ∧ abiPreserved s s' ∧
      (xorAvx2X86_64.post s s' ∧ s'.gpr .rsi = s.gpr .rcx) := by
  obtain ⟨t, s', he, ⟨h, hpost⟩, hr⟩ := correct (Avx2.APre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h, hpost, hr⟩

theorem xor_correct (s : State) (hs : xorAvx2X86_64.pre s) :
    ∃ t s', Exec isa xorBy s t s' ∧ abiPreserved s s' ∧ xorAvx2X86_64.post s s' :=
  (xor_rsi s hs).imp fun _ ⟨s', he, ha, h, _⟩ => ⟨s', he, ha, h⟩

theorem xor_ct : ConstantTime isa xorAvx2X86_64.pre xorAvx2X86_64.pub xorBy :=
  VG.Taint.constantTime (A := taint) Avx2.τ₀ (fun _ _ h₁ h₂ hp => Avx2.agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem xor_verified :
    Verified X86_64.target xorBy (Proof.ChaCha20.xorContract X86_64.abi 16) :=
  Verified.of_correct xor_correct xor_ct
    (by sig_implies [Proof.ChaCha20.xorContract, Proof.ChaCha20.xorSig, X86_64.abi, X86_64.argRegs,
      xorAvx2X86_64, Proof.ChaCha20.xorX86_64]
      [Avx2.sat] using Avx2.sat)

end VG.Proof.ChaCha20.X86_64.Avx512VL
