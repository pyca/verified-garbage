module

import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import Mathlib.Tactic.ToAdditive
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant-time argument capture and packed-key pointer setup -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- Scratch and the stack pointer are public; pointed-to argument values
need not agree except for the scratch pointer loaded from its ABI slot. -/
def EntryStart (j : Nat) (p : Addr × Addr) (s : State) : Prop :=
  s.sp = p.2 ∧ word s.mem p.2 (8 * j) = p.1 ∧
    InRegions (s.rd ++ s.wr) (off p.2 (8 * j)) 8

def EntryPtrs (p : Addr × Addr) (s : State) : Prop := s.gpr .x11 = p.1 ∧ s.sp = p.2

theorem pins_entryPtrs : Pins EntryPtrs [.x11] :=
  pins_of (fun p _ => p.1) (by
    intro p s h r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h.1)

theorem entryScratch_ct (j : Nat) (hj : j < 4096) {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs []) (.block [.ldrSp .x11 (8 * j)]) hint).isSome = true) :
    RelCT isa (Two (EntryStart j)) (.block [.ldrSp .x11 (8 * j)]) (Two EntryPtrs) := by
  refine two_piece [] (by intro p s t hs ht r hr; cases hr) hT ?_
  intro p s h
  exact WP.mono (entryScratch_ok j hj h.1 h.2.2 h.2.1) fun t ⟨hb, _, hk⟩ =>
    ⟨hb, hk.sp.trans h.1⟩

theorem signEntry_ct : RelCT isa (Two (EntryStart 1)) (.block SignVerify.signEntry) (fun _ _ => True) := by
  unfold SignVerify.signEntry
  rw [List.append_assoc]
  apply RelCT.block_append
  exact RelCT.seq (entryScratch_ct 1 (by decide) (by taint_decide))
    (two_taint [.x11] pins_entryPtrs (by taint_decide))

theorem verifyEntry_ct : RelCT isa (Two (EntryStart 0)) (.block SignVerify.verifyEntry) (fun _ _ => True) := by
  unfold SignVerify.verifyEntry
  rw [List.append_assoc]
  apply RelCT.block_append
  exact RelCT.seq (entryScratch_ct 0 (by decide) (by taint_decide))
    (two_taint [.x11] pins_entryPtrs (by taint_decide))

end VG.Proof.Dsa.AArch64
