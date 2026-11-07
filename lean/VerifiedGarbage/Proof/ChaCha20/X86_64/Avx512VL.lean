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
nor postcondition reads: each branch is its kernel's proof from the state
after it (`cmpLim_ok`). The AVX2 kernel works from a source to a
destination (`Avx2.xorWith_to`) and the AVX-512 kernel in place
(`Avx512.correct`), so the whole is proven called in place (`xorIn`): the
AVX2 branch by `okIn_of_okTo`. Constant time: the branch is on the length,
and `r8` (the destination), which the AVX2 kernel reads, is `rsi` there.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512VL

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512VL
open VG.Proof.ChaCha20
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

theorem correct {s₀ : State} (hp : (xorIn 16).pre s₀) :
    WP isa xorBy s₀ fun s' => gprPreserved s₀ s' ∧ (xorIn 16).post s₀ s' := by
  refine WP.seq (WP.mono (cmpLim_ok s₀) fun t ⟨⟨cf, of, zf, sf, e⟩, hc⟩ => ?_)
  subst e
  refine WP.ite (decide (eL s₀ < shortLim)) (by simp [eval, hc]) (fun _ => ?_) (fun _ => ?_)
  · obtain ⟨tr, s', he, ⟨h1, h2, -⟩, hpost⟩ :=
      okIn_of_okTo (Avx2.xorWith_to true (by lit_decide)) (s₀.setFlags cf of zf sf) hp
    exact ⟨tr, s', he, ⟨h1, h2⟩, hpost⟩
  · exact WP.mono (Avx512.correct (apre_setFlags (Avx2.APre.of s₀ hp.1) cf of zf sf))
      fun s' ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩

theorem xor_in (s : State) (hs : (xorIn 16).pre s) :
    ∃ t s', Exec isa xorBy s t s' ∧ abiPreserved s s' ∧ (xorIn 16).post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := correct hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h, hpost⟩

/-- The public registers and what is known about memory on entry, called in
place: `Avx2.τ₀`'s, and `r8` (`rsi`). -/
def τIn : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false, lens := [64, 0, 320],
    bases := [(.rdi, 0, 0), (.rsi, 1, 0), (.rcx, 2, 0)] }

theorem agreeIn {s₁ s₂ : State} (h₁ : (xorIn 16).pre s₁) (h₂ : (xorIn 16).pre s₂)
    (hpub : (xorIn 16).pub s₁ s₂) : X86_64.Taint.Agree τIn s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpub
  have wf : ∀ s, (xorIn 16).pre s → X86_64.Taint.Wf τIn s := by
    intro s hs
    obtain ⟨⟨-, hw, d1, d2, d3, -⟩, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τIn], by simp [hw, d1, d2, d3], by simp [hw, Nat.le_of_lt (s.gpr .rdx).isLt]⟩,
      fun p hp => ?_⟩
    simp only [τIn, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [X86_64.Taint.region, hw]
  have p6 : s₁.gpr .r8 = s₂.gpr .r8 := by rw [h₁.2, h₂.2, p2]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [τIn, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.1.2.1, h₂.1.2.1, p1, p2, p3, p4]
  · intro sl h; simp [τIn] at h
  · intro sl h; simp [τIn] at h

theorem xor_ct : ConstantTime isa (xorIn 16).pre (xorIn 16).pub xorBy :=
  VG.Taint.constantTime (A := taint) τIn (fun _ _ h₁ h₂ hp => agreeIn h₁ h₂ hp) (by taint_decide)

end VG.Proof.ChaCha20.X86_64.Avx512VL
