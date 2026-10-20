module
public import VerifiedGarbage.Proof.Rsa.X86.PrivContext

import VerifiedGarbage.Proof.Rsa.X86.PrivLocalArgument
import VerifiedGarbage.Proof.Rsa.X86.PrivStackWord
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-! # The private CRT call receives all eighteen cdecl arguments -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

def crtArgument (g : PrivGeometry) (j : Nat) : BitVec 32 :=
  if j = 0 then g.temporary else g.argument (if j < 4 then j else j + 2)

def CrtArgs (g : PrivGeometry) (s : State) : Prop :=
  ∀ j < 18, s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) 32 = crtArgument g j

theorem crtArgs_prefix_ok (n : Nat) (hn : n ≤ 17) (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s)
    (first : s.mem.readW (byteAddr g.stack) 32 = g.temporary) :
    WP isa (.block ((List.range n).flatMap (fun j => copyArgument (if j + 1 < 4 then j + 1 else j + 3) (j + 1)))) s
      fun t => PrivContext g bs t ∧
        (∀ j < n + 1, t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) 32 = crtArgument g j) ∧
        Frame [⟨byteAddr g.stack, 72⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  induction n generalizing s with
  | zero =>
    refine WP.block_nil ⟨h, ?_, Frame.refl _ _, Keeps.refl _ _⟩
    intro j hj
    have : j = 0 := by omega
    subst j
    simpa only [crtArgument, ite_true, Nat.mul_zero, BitVec.add_zero] using first
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h first) ?_
    rintro u ⟨hu, copied, F, K⟩
    refine WP.mono (copyArgument_ok u hu (i := if n + 1 < 4 then n + 1 else n + 3)
      (by split <;> omega) (by omega : n + 1 < 18)) ?_
    rintro t ⟨ht, M, F', K'⟩
    refine ⟨ht, ?_, F.trans (F'.sub ?_), K.trans K'⟩
    · intro j hj
      by_cases same : j = n + 1
      · subst j
        rw [M, Mem.readW_writeW_self32]
        simp only [crtArgument, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
      · rw [outgoing_word_preserved (by omega) (by omega) same F']
        exact copied j (by omega)
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩

theorem crtArgs_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) :
    WP isa (.block crtArgs) s fun t => PrivContext g bs t ∧ CrtArgs g t ∧
      Frame [⟨byteAddr g.stack, 72⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold crtArgs
  rw [WP.block_append_iff]
  refine WP.mono (localArgument_ok s h candidateOffset (by decide : 0 < 18)) ?_
  rintro u ⟨hu, M, F, K⟩
  have first : u.mem.readW (byteAddr g.stack) 32 = g.temporary := by
    rw [M]
    simpa only [Nat.mul_zero, BitVec.add_zero, PrivGeometry.temporary] using
      Mem.readW_writeW_self32 s.mem (byteAddr g.stack) (g.stack + BitVec.ofNat 32 candidateOffset)
  refine WP.mono (crtArgs_prefix_ok 17 (by decide) u hu first) ?_
  rintro t ⟨ht, A, F', K'⟩
  refine ⟨ht, A, (F.sub ?_).trans F', K.trans K'⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide : 4 * 0 + 4 ≤ 72)⟩

end VG.Proof.Rsa.X86.PrivChecked
