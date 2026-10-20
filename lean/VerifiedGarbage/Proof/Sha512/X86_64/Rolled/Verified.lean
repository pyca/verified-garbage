module

import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Compress
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Sha512.X86_64.Wide
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Impl.Sha512.X86_64.Rolled
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Compress
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Sha512.X86_64.Wide
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
meta import VerifiedGarbage.Impl.Sha512.X86_64.Rolled
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# SHA-512 on x86-64, rolled: verified

`compress_verified`: `Impl.Sha512.X86_64.Rolled.compress` against
`Proof.Sha512.compressWideX86_64`, under the plain calling convention: the
table of round constants is carried by the code (`aluTbl`). Constant time is
one run of the taint analysis: the schedule's stores are at fixed offsets of
`rcx`, and the table's reads at the public index `rdx`.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Rolled

open VG VG.X86_64

/-- The pointers and the count are public; `rdi` and `rcx` point at the
hash value and the scratch space. -/
def τW : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx], flags := false, lens := [64, 1328],
    bases := [(.rdi, 0, 0), (.rcx, 1, 0)] }

theorem agreeW {s₁ s₂ : State}
    (hr : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx], s₁.gpr r = s₂.gpr r)
    (hw₁ : s₁.wr = [⟨s₁.gpr .rdi, 64⟩, ⟨s₁.gpr .rcx, 1328⟩])
    (hw₂ : s₂.wr = [⟨s₂.gpr .rdi, 64⟩, ⟨s₂.gpr .rcx, 1328⟩])
    (hd₁ : Region.Disjoint ⟨s₁.gpr .rdi, 64⟩ ⟨s₁.gpr .rcx, 1328⟩)
    (hd₂ : Region.Disjoint ⟨s₂.gpr .rdi, 64⟩ ⟨s₂.gpr .rcx, 1328⟩) : taint.Agree τW s₁ s₂ := by
  have wf : ∀ s : State, s.wr = [⟨s.gpr .rdi, 64⟩, ⟨s.gpr .rcx, 1328⟩] →
      Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rcx, 1328⟩ → X86_64.Taint.Wf τW s := by
    intro s hw hd
    refine ⟨fun _ => ⟨by simp [hw, τW], by simp [hw, hd], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [τW, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr' => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ hw₁ hd₁, wf _ hw₂ hd₂, ?_, ?_,
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [τW, RegSet.mem_ofList] at hr'
    exact hr r hr'
  · rw [hw₁, hw₂, hr .rdi (by simp), hr .rcx (by simp)]
  · intro sl h; simp [τW] at h
  · intro sl h; simp [τW] at h

theorem compress_verified :
    Verified X86_64.target Impl.Sha512.X86_64.Rolled.compress Proof.Sha512.compressWideX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (Avx2.pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) τW ?_ (by taint_decide)
    intro s₁ s₂ hp₁ hp₂ ⟨h1, h2, h3, h4⟩
    have p₁ := Avx2.pre_of s₁ hp₁
    have p₂ := Avx2.pre_of s₂ hp₂
    refine agreeW (fun r hr => ?_) p₁.wr p₂.wr p₁.st_scr p₂.st_scr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine ⟨Avx2.satState, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha512.X86_64.Rolled
