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
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.TCB.Artifact

/-!
# ChaCha20 on x86-64 with AVX-512, short data in `ymm` registers: verified

The comparison changes only the flags, which neither kernel's precondition
nor postcondition reads: each branch is its kernel's proof, from the source
to the destination (`xorTo 16`), from the state after it (`cmpLim_ok`).
Constant time: the branch is on the length.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512VL

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512VL
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2 (eL)

set_option simprocs false in
theorem cmpLim_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 shortLim))]) s fun t =>
      (∃ cf of zf sf, t = s.setFlags cf of zf sf) ∧ t.cf = some (decide (eL s < shortLim)) := by
  have se : BitVec.signExtend 64 (BitVec.ofNat 32 shortLim) = BitVec.ofNat 64 shortLim := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left', se]
  exact ⟨⟨_, _, _, _, rfl⟩, rfl⟩

theorem correct {s₀ : State} (hp : (xorTo 16).pre s₀) :
    WP isa xorBy s₀ fun s' => gprPreserved s₀ s' ∧ (xorTo 16).post s₀ s' := by
  refine WP.seq (WP.mono (cmpLim_ok s₀) fun t ⟨⟨cf, of, zf, sf, e⟩, hc⟩ => ?_)
  subst e
  have hp' : (xorTo 16).pre (s₀.setFlags cf of zf sf) := hp
  refine WP.ite (decide (eL s₀ < shortLim)) (by simp [eval, hc]) (fun _ => ?_) (fun _ => ?_)
  · obtain ⟨tr, s', he, ⟨h1, h2, -⟩, hpost⟩ := Avx2.xorWith_to true (by lit_decide) _ hp'
    exact ⟨tr, s', he, ⟨h1, h2⟩, hpost⟩
  · exact Avx512.correct (Avx2.TPre.of _ hp')

theorem xor_to (s : State) (hs : (xorTo 16).pre s) :
    ∃ t s', Exec isa xorBy s t s' ∧ abiPreserved s s' ∧ (xorTo 16).post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := correct hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h, hpost⟩

theorem xor_ctTo : ConstantTime isa (xorTo 16).pre (xorTo 16).pub xorBy :=
  VG.Taint.constantTime (A := taint) Xor.τ₀ (fun _ _ h₁ h₂ hp => Xor.agree₀ h₁ h₂ hp) (by taint_decide)

end VG.Proof.ChaCha20.X86_64.Avx512VL
