module

import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit

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

/-- The existing stack allowance covers the shared kernel's return address.
Its inline proof transfers to a call because the kernel never touches `rsp`. -/
private theorem longCall_correct {s : State} (hp : (xorTo 16).pre s) :
    WP isa (.call "vg_chacha20_xor_avx512" VG.Impl.ChaCha20.X86_64.Avx512.xor) s
      fun t => gprPreserved s t ∧ (xorTo 16).post s t := by
  obtain ht := Avx2.TPre.of s hp
  have clear : Clear (hole (s.gpr .rsp)) s := by
    intro r hr
    rw [hp.1, hp.2.1] at hr
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (ht.stk_d.sub_left (Avx2.stk_ret s)).symm
    · exact (ht.stk_st.sub_left (Avx2.stk_ret s)).symm
    · exact (ht.stk_q.sub_left (Avx2.stk_ret s)).symm
    · exact (ht.stk_b.sub_left (Avx2.stk_ret s)).symm
  refine WP.mono (WP.of_inline (c := .call "vg_chacha20_xor_avx512" VG.Impl.ChaCha20.X86_64.Avx512.xor)
    (by lit_decide) clear (Avx512.correct ht)) ?_
  rintro t ⟨b, hv, u, heq, _, kb, hb⟩
  subst t
  have keep : gprPreserved s (b.patch (hole (s.gpr .rsp)) hv u) := by
    refine ⟨?_, ?_⟩
    · rw [State.patch_gpr]; exact kb.1
    · rw [State.patch_readW (by decide) (fun _ hx => not_hole_of_above hx)]
      exact kb.2
  refine ⟨keep, ?_, ?_⟩
  swap
  · rw [State.patch_gpr]; exact hb.2
  have same : Spec.ChaCha20.bytesAt (b.patch (hole (s.gpr .rsp)) hv u).mem (s.gpr .r8) (s.gpr .rdx).toNat =
      Spec.ChaCha20.bytesAt b.mem (s.gpr .r8) (s.gpr .rdx).toNat := by
    unfold Spec.ChaCha20.bytesAt
    apply List.map_congr_left
    intro i hi
    apply State.patch_mem
    intro hh
    exact (ht.stk_q.sub_left (Avx2.stk_ret s)) _ hh (Avx2.in_eqR (List.mem_range.mp hi))
  exact same.trans hb.1

theorem correct {s₀ : State} (hp : (xorTo 16).pre s₀) :
    WP isa xorBy s₀ fun s' => gprPreserved s₀ s' ∧ (xorTo 16).post s₀ s' := by
  refine WP.seq (WP.mono (cmpLim_ok s₀) fun t ⟨⟨cf, of, zf, sf, e⟩, hc⟩ => ?_)
  subst e
  have hp' : (xorTo 16).pre (s₀.setFlags cf of zf sf) := hp
  refine WP.ite (decide (eL s₀ < shortLim)) (by simp [eval, hc]) (fun _ => ?_) (fun _ => ?_)
  · obtain ⟨tr, s', he, ⟨h1, h2, -⟩, hpost⟩ := Avx2.xorWith_to true (by lit_decide) _ hp'
    exact ⟨tr, s', he, ⟨h1, h2⟩, hpost⟩
  · exact longCall_correct hp'

theorem xor_to (s : State) (hs : (xorTo 16).pre s) :
    ∃ t s', Exec isa xorBy s t s' ∧ abiPreserved s s' ∧ (xorTo 16).post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := correct hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h, hpost⟩

theorem xor_ctTo : ConstantTime isa (xorTo 16).pre (xorTo 16).pub xorBy :=
  VG.Taint.constantTime (A := taint) Xor.τ₀ (fun _ _ h₁ h₂ hp => Xor.agree₀ h₁ h₂ hp) (by taint_decide)

end VG.Proof.ChaCha20.X86_64.Avx512VL
