module

import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Pointer
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Bounds
public import VerifiedGarbage.Impl.MlKem.AArch64.Dot
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

def Accum (s : State) (a : Nat → Sums) : Prop :=
  Lanes (s.v .v21) (fun e => (a e).even) ∧
  Lanes (s.v .v22) (fun e => (a e).odd) ∧
  Lanes (s.v .v23) (fun e => (a e).cross)

def advance (a : Nat → Sums) (F G : Nat → Nat) : Nat → Sums :=
  fun e => (a e).next (F (2*e)) (F (2*e+1)) (G (2*e)) (G (2*e+1))

theorem fullTerm_ok {s : State} {fg : Nat × Nat} {a : Nat → Sums} {F G : Nat → Nat} {n : Nat}
    (hoF : fg.1 < 65536) (hoG : fg.2 < 65536)
    (hc : VConsts s) (ha : Accum s a) (hb : ∀ e < 4, (a e).Bounded n) (hn : n < 4)
    (bF : ∀ e < 8, F e < 3329) (bG : ∀ e < 8, G e < 3329)
    (hf : ∀ e < 8, (coeffAt s.mem (s.gpr .x28 + BitVec.ofNat 64 fg.1 + s.gpr .x12) e).toNat = F e)
    (hg : ∀ e < 8, (coeffAt s.mem (s.gpr .x28 + BitVec.ofNat 64 fg.2 + s.gpr .x12) e).toNat = G e)
    (rf : ∀ i < 2, InRegions (s.rd ++ s.wr)
      (s.gpr .x28 + BitVec.ofNat 64 fg.1 + s.gpr .x12 + BitVec.ofNat 64 (16*i)) 16)
    (rg : ∀ i < 2, InRegions (s.rd ++ s.wr)
      (s.gpr .x28 + BitVec.ofNat 64 fg.2 + s.gpr .x12 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (Impl.MlKem.AArch64.Dot.dotTerm fg)) s fun s' =>
      Only [.x1, .x2] s s' ∧ VConsts s' ∧ Accum s' (advance a F G) := by
  rw [term_partition, WP.block_append_iff]
  refine WP.mono (pointers_ok hoF hoG) fun s₁ ⟨h₁,v₁,e₁,e₂⟩ => ?_
  have hc₁ : VConsts s₁ := ⟨by rw [v₁]; exact hc.q, by rw [v₁]; exact hc.m⟩
  have ha₁ : Accum s₁ a := by simpa only [Accum, v₁] using ha
  have bnext : ∀ e < 4, ((advance a F G) e).Bounded (n+1) := fun e he =>
    (hb e he).next (bF _ (by omega)) (bF _ (by omega)) (bG _ (by omega)) (bG _ (by omega))
  rw [← List.append_nil termCore]
  refine termCore_ok (F := F) (G := G) (fun i hi => by rw [h₁.rd,h₁.wr,e₁]; exact rf i hi)
    (fun i hi => by rw [h₁.rd,h₁.wr,e₂]; exact rg i hi)
    (fun e he => by rw [h₁.mem,e₁]; exact hf e he)
    (fun e he => by rw [h₁.mem,e₂]; exact hg e he)
    ha₁.1 ha₁.2.1 ha₁.2.2
    (fun e he => by have := (bnext e he).noWrap (by omega); exact Nat.lt_trans this.1 (by decide))
    (fun e he => by have := (bnext e he).noWrap (by omega); exact Nat.lt_trans this.2.1 (by decide))
    (fun e he => by have := (bnext e he).noWrap (by omega); exact Nat.lt_trans this.2.2 (by decide))
    fun s₂ h₂ l₁ l₂ l₃ => wp_nil ?_
  refine ⟨?_, hc₁.chg h₂, l₁, l₂, l₃⟩
  exact ⟨fun r hr => by rw [h₂.gpr]; exact h₁.gpr r hr,
    h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    fun r hr => by rw [h₂.v r (by revert r hr; decide +kernel)]; exact h₁.vcs r hr⟩

end VG.Proof.MlKem.AArch64.Dot
