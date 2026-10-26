module
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Dsa.X86_64.EntryFields
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryFields
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToAdditive
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant-time argument capture and packed-key pointer setup -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Scratch and the stack pointer are public; pointed-to argument values
need not agree except for the scratch pointer loaded from its ABI slot. -/
def EntryStart (j : Nat) (p : Addr × Addr) (s : State) : Prop :=
  s.gpr .rsp = p.2 ∧ word s.mem p.2 (8 * j) = p.1 ∧
    InRegions (s.rd ++ s.wr) (off p.2 (8 * j)) 8

def EntryPtrs (p : Addr × Addr) (s : State) : Prop := s.gpr .r11 = p.1 ∧ s.gpr .rsp = p.2

theorem pins_entryPtrs : Pins EntryPtrs [.r11, .rsp] :=
  pins_of (fun p r => if r = .r11 then p.1 else p.2) (by
    intro p s h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2)

theorem entryScratch_ct (j : Nat) {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .r11 (.mem (Crt.stk j))]) hint).isSome = true) : RelCT isa (Two (EntryStart j))
    (.block [.mov .r11 (.mem (Crt.stk j))]) (Two EntryPtrs) := by
  refine two_piece [.rsp] (pins_of (fun p _ => p.2) (by
    intro p s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1)) hT ?_
  intro p s h
  exact WP.mono (entryScratch_ok j h.1 h.2.2 h.2.1) fun t ⟨hb, _, hk⟩ =>
    ⟨hb, (hk.gpr (by decide)).trans h.1⟩

theorem signEntry_ct : RelCT isa (Two (EntryStart 4)) (.block SignVerify.signEntry) (fun _ _ => True) := by
  change RelCT isa (Two (EntryStart 4)) (.block (([.mov .r11 (.mem (Crt.stk 4))] : List Instr) ++
    (SignVerify.save ++ signFields ++ SignVerify.keyPointers))) _
  apply RelCT.block_append
  exact RelCT.seq (entryScratch_ct 4 (by taint_decide)) (two_taint [.r11, .rsp] pins_entryPtrs (by taint_decide))

theorem verifyEntry_ct : RelCT isa (Two (EntryStart 3)) (.block SignVerify.verifyEntry) (fun _ _ => True) := by
  change RelCT isa (Two (EntryStart 3)) (.block (([.mov .r11 (.mem (Crt.stk 3))] : List Instr) ++
    (SignVerify.save ++ verifyFields ++ SignVerify.keyPointers))) _
  apply RelCT.block_append
  exact RelCT.seq (entryScratch_ct 3 (by taint_decide)) (two_taint [.r11, .rsp] pins_entryPtrs (by taint_decide))

end VG.Proof.Dsa.X86_64
