module

import VerifiedGarbage.Proof.Rsa.X86.RvOps
public import VerifiedGarbage.Proof.Rsa.RecoverSubtract
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Recovery subtraction, including its modular result and borrow -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (sub32 b2n)

theorem KS.subWrap {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {o a b : Nat}
    (h : KS g s0 A live AW liveW V ls s)
    (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live) (hoa : o ≠ a) (hob : o ≠ b)
    (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sub3 g.w o a b) s fun t =>
      KS g s0 (upd A o (sub32 g.w (A a) (A b))) (o :: live) AW liveW V ls t ∧
      (t.gpr .ebx).toNat = b2n (decide (A a < A b)) := by
  refine WP.mono (h.sub3_w ho ha hb hoa hob hlW) fun t ⟨X, ht, _, value, borrow⟩ => ?_
  have xb : X < 2 ^ (32 * g.w) := by
    have v := ht.arrs o (by simp)
    rw [upd_self] at v
    rw [← v]
    exact val32_lt _ _ _ _
  have bb : A b < 2 ^ (32 * g.w) := by
    rw [← h.arrs b hb]
    exact val32_lt _ _ _ _
  obtain ⟨result, flag⟩ := VG.Proof.Rsa.sub32_of xb bb value borrow
  exact ⟨result ▸ ht, flag⟩

theorem KS.subWrap_W {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {o a b : Nat}
    (h : KS g s0 A live AW liveW V ls s)
    (ho : o < 22) (ha : a ∈ liveW) (hb : b ∈ liveW) (hoa : o ≠ a) (hob : o ≠ b)
    (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (sub3 g.W o a b) s fun t =>
      KS g s0 A live (upd AW o (sub32 g.W (AW a) (AW b))) (o :: liveW) V ls t ∧
      (t.gpr .ebx).toNat = b2n (decide (AW a < AW b)) := by
  refine WP.mono (h.sub3_W ho ha hb hoa hob hl) fun t ⟨X, ht, _, value, borrow⟩ => ?_
  have xb : X < 2 ^ (32 * g.W) := by
    have v := ht.arrsW o (by simp)
    rw [upd_self] at v
    rw [← v]
    exact val32_lt _ _ _ _
  have bb : AW b < 2 ^ (32 * g.W) := by
    rw [← h.arrsW b hb]
    exact val32_lt _ _ _ _
  obtain ⟨result, flag⟩ := VG.Proof.Rsa.sub32_of xb bb value borrow
  exact ⟨result ▸ ht, flag⟩

end VG.Proof.Rsa.X86.Recover
