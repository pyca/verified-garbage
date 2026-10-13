module

public import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
meta import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

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

def EntryPtrs (p : Addr × Addr) (s : State) : Prop := s.gpr .x8 = p.1

theorem pins_entryPtrs : Pins EntryPtrs [.x8] :=
  pins_of (fun p _ => p.1) (by
    intro p s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h)

/-- Loading the scratch pointer reads only the stack, whose address is public. -/
theorem entryScratch_ct (j : Nat) (hj : (8 * j) % 8 = 0 ∧ 8 * j < 32768) {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs []) (.block [.ldrSp .x8 (8 * j)]) hint).isSome = true) :
    RelCT isa (Two (EntryStart j)) (.block [.ldrSp .x8 (8 * j)]) (Two EntryPtrs) := by
  refine two_piece [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) hT ?_
  intro p s ⟨hsp, hb, hr⟩
  exact WP.mono (entryScratch_ok hj hsp hr hb) fun t ⟨h8, _, _⟩ => h8

theorem signEntry_ct : RelCT isa (Two (EntryStart 1)) (.block SignVerify.signEntry) (fun _ _ => True) := by
  change RelCT isa (Two (EntryStart 1)) (.block (([.ldrSp .x8 (8 * 1)] : List Instr) ++
    (signFields ++ SignVerify.keyPointers))) _
  apply RelCT.block_append
  exact RelCT.seq (entryScratch_ct 1 (by decide) (by taint_decide)) (two_taint [.x8] pins_entryPtrs (by taint_decide))

theorem verifyEntry_ct : RelCT isa (Two (EntryStart 0)) (.block SignVerify.verifyEntry) (fun _ _ => True) := by
  change RelCT isa (Two (EntryStart 0)) (.block (([.ldrSp .x8 (8 * 0)] : List Instr) ++
    (verifyFields ++ SignVerify.keyPointers))) _
  apply RelCT.block_append
  exact RelCT.seq (entryScratch_ct 0 (by decide) (by taint_decide)) (two_taint [.x8] pins_entryPtrs (by taint_decide))

end VG.Proof.Dsa.AArch64
