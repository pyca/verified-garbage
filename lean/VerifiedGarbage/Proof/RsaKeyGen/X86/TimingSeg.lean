module

public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Traces of code whose public registers each run computes from the same header

The taint analysis takes what code reads from the workspace for secret. Code
that computes its pointers and counts from the workspace's header is checked
in segments: at each segment's start, every run holds the same values in the
registers the segment needs public, which correctness gives.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86

/-- Runs from states whose registers `rs` hold the same values `f r` leak
the same trace (`raw`), and each run ends in `Y` by correctness. -/
theorem seg {X Y : State → Prop} {c : Prog isa} (rs : List Reg) (f : Reg → BitVec 32)
    (vals : ∀ s, X s → ∀ r ∈ rs, s.gpr r = f r)
    (raw : RelCT isa (VG.X86.Taint.Agree (τr rs)) c (fun _ _ => True))
    (run : ∀ s, X s → WP isa c s Y) :
    RelCT isa (fun s t => X s ∧ X t) c (fun u z => Y u ∧ Y z) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have agree : VG.X86.Taint.Agree (τr rs) s t :=
    agree_regs fun r mem => (vals s S r mem).trans (vals t T r mem).symm
  exact ⟨(raw _ _ _ _ _ _ agree E G).1, wp_result (run s S) E, wp_result (run t T) G⟩

/-- A trace from a relation, and each run ending in `Y`. -/
theorem withRuns {X Y : State → Prop} {c : Prog isa} {R : State → State → Prop}
    (raw : RelCT isa (fun s t => X s ∧ X t) c R) (run : ∀ s, X s → WP isa c s Y) :
    RelCT isa (fun s t => X s ∧ X t) c (fun u z => Y u ∧ Y z) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  exact ⟨(raw _ _ _ _ _ _ ⟨S, T⟩ E G).1, wp_result (run s S) E, wp_result (run t T) G⟩

/-- A block with `rs` public leaks the same trace. -/
theorem rawBlock {rs : List Reg} {code : List Instr}
    (L : (VG.Taint.check taint (τr rs) (.block code) (.block [])).map (taint.le (τr [])) = some true) :
    RelCT isa (VG.X86.Taint.Agree (τr rs)) (.block code) (fun _ _ => True) :=
  (erased_relCT (σ := τr []) (.block code) (.block code) (.block []) rfl rfl rfl L).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem ptr_value {s : State} {W : Addr} {r : Reg} {x : Nat} (P : PtrAt s W r x) :
    s.gpr r = BitVec.ofNat 32 (W.toNat + x) := by
  apply BitVec.eq_of_toNat_eq
  rw [P, BitVec.toNat_ofNat]

end VG.Proof.RsaKeyGen.X86
