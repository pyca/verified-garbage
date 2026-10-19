module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Advance
import VerifiedGarbage.Proof.Framework.Block

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

abbrev clob : List Reg := [.x0,.x1,.x2,.x3,.x9,.x10,.x11,.x12]

def evenResult (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat) (Γ : Nat → Nat) : Nat → Nat :=
  fun e => ((sumTerms terms F G zeroSums e).even + (sumTerms terms F G zeroSums e).odd * Γ e) % 3329

def oddResult (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat) : Nat → Nat :=
  fun e => (sumTerms terms F G zeroSums e).cross % 3329

structure StepPost (s : State) (p : Addr) (j : Nat) (O D : Nat → BitVec 32) (s' : State) : Prop where
  keep : Keep clob s s'
  constants : VConsts s'
  frame : Frame [polyRegion p] s.mem s'.mem
  out : CoeffsUpTo s'.mem p (j+8) O D
  x0 : s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 32
  x3 : s'.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 16
  x12 : s'.gpr .x12 = s.gpr .x12 + BitVec.ofNat 64 32
  x11 : s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1

theorem step_ok {s : State} (terms : List (Nat × Nat))
    {F G : (Nat × Nat) → Nat → Nat} {Γ : Nat → Nat} {p : Addr} {j : Nat}
    (hc : VConsts s) (hn : terms.length ≤ 4)
    (hin : ∀ fg ∈ terms, TermInput s fg (F fg) (G fg))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 0) 16)
    (hg : Lanes (s.mem.read (s.gpr .x3 + BitVec.ofNat 64 0) 16) Γ)
    (bg : ∀ e < 4, Γ e < 3329)
    (hx0 : s.gpr .x0 = coeffAddr p j) (hj : j+8 ≤ 256)
    (hw : ∀ i < 2, InRegions s.wr (coeffAddr p (j+4*i)) 16)
    {O D : Nat → BitVec 32} (ho : CoeffsUpTo s.mem p j O D)
    (hv : ∀ e < 8, O (j+e) = interleave (evenResult terms F G Γ) (oddResult terms F G) e) :
    WP isa (.block (body terms)) s (StepPost s p j O D) := by
  unfold body
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (compute_ok terms hc hn hin hr hg bg) fun s₁ ⟨k₁,c₁,l₁,l₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (store_ok (p := p) (j := j) (O := O) (D := D) (by rw [k₁.get .x0]; exact hx0) hj
    (fun i hi => by rw [k₁.wr]; exact hw i hi) c₁ l₁ l₂
    (by rw [k₁.mem]; exact ho) hv) fun s₂ ⟨k₂,c₂,f₂,o₂⟩ => ?_
  refine WP.mono (bump_ok s₂) fun s₃ ⟨k₃,v₃,e0,e3,e12,e11⟩ => ?_
  refine ⟨((k₁.keep.trans k₂).trans k₃.keep).mono, ⟨?_,?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₃]; exact c₂.q
  · rw [v₃]; exact c₂.m
  · rw [k₃.mem,←k₁.mem]; exact f₂
  · rw [k₃.mem]; exact o₂
  · rw [e0,k₂.get .x0,k₁.get .x0]
  · rw [e3,k₂.get .x3,k₁.get .x3]
  · rw [e12,k₂.get .x12,k₁.get .x12]
  · rw [e11,k₂.get .x11,k₁.get .x11]

end VG.Proof.MlKem.AArch64.Dot
