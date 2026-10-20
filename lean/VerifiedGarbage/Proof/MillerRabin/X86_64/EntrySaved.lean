module
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stack

import VerifiedGarbage.Proof.MillerRabin.X86_64.StackBookkeeping
import VerifiedGarbage.Proof.MillerRabin.X86_64.StackContext
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage

/-! # Saved words agree with the workspace after entering the round -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Impl.MillerRabin.X86_64

theorem entered_saved_headers {s t : State} {B : Addr} {Z : Nat}
    (h : Staged B s t) (hm : t.mem = s.mem)
    (hs : 120 ≤ (t.gpr .rsp).toNat) (hn : B.toNat + Z ≤ 2 ^ 64) (hz : 256 ≤ Z)
    (hd : Region.Disjoint ⟨t.gpr .rsp - 112#64, 112⟩ ⟨B, Z⟩) :
    ∀ p ∈ restoreSlots, (entered t).mem.readW
      ((entered t).gpr .rsp + BitVec.ofNat 64 p.2) 64 = word (entered t).mem B (8 * p.1) := by
  intro p hp
  have hj : p.1 < 32 := by
    simp only [restoreSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [entered_word hs hn hd (by omega_arith), hm]
  exact entered_bookkeeping h hs p hp

end VG.Proof.MillerRabin.X86_64
