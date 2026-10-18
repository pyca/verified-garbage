module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptArguments

/-! # Prepare checked public RSA's ten outgoing arguments -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Encrypt

def publicArgument (g : Geometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.output | 1 => BitVec.ofNat 32 g.length
  | 2 => g.sources 4 | 3 => BitVec.ofNat 32 g.preLength
  | 4 => g.sources 1 | 5 => BitVec.ofNat 32 g.exponentLength
  | 6 => g.temporary | 7 => BitVec.ofNat 32 g.length
  | 8 => g.workspace | _ => BitVec.ofNat 32 g.scratchLength

def inputSlot (j : Nat) : Nat :=
  match j with
  | 0 => 0 | 1 => 3 | 2 => 12 | 3 => 13 | 4 => 4 | 5 => 5 | 7 => 3 | 8 => 10 | _ => 11

def prepare (j : Nat) : List Instr :=
  if j = 6 then localArgument emOffset j else copyArgument (inputSlot j) j

theorem publicArgs_ok {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) :
    WP isa (.block ((List.range 10).flatMap prepare)) s fun t =>
      Context g bs t ∧ Arguments g (publicArgument g) 10 t ∧
      Frame [⟨byteAddr g.stack, 40⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  have next {u : State} (hu : Context g bs u) {j : Nat} (hj : j < 10)
      (a : Arguments g (publicArgument g) j u) :
      WP isa (.block (prepare j)) u fun t =>
        Context g bs t ∧ Arguments g (publicArgument g) (j + 1) t ∧
        Frame [⟨byteAddr g.stack, 40⟩] u.mem t.mem ∧ Keeps [.eax] u t := by
    apply prepareArgument_ok (bs := bs) a hj
    by_cases isLocal : j = 6
    · subst j
      exact localArgument_ok u hu emOffset (by decide)
    · have inputBound : inputSlot j < 14 := by
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 7 ∨ j = 8 ∨ j = 9 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have value : g.argument (inputSlot j) = publicArgument g j := by
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 7 ∨ j = 8 ∨ j = 9 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      simp only [prepare, isLocal, ite_false]
      refine WP.mono (copyArgument_ok u hu inputBound hj) ?_
      rintro t ⟨ht, M, F, K⟩
      exact ⟨ht, by rw [value] at M; exact M, F, K⟩
  have copyMany (n : Nat) (hn : n ≤ 10) :
      WP isa (.block ((List.range n).flatMap prepare)) s fun t =>
        Context g bs t ∧ Arguments g (publicArgument g) n t ∧
        Frame [⟨byteAddr g.stack, 40⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
    induction n with
    | zero => exact WP.block_nil ⟨h, by intro j hj; omega, Frame.refl _ _, Keeps.refl _ _⟩
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
      refine WP.mono (ih (by omega)) ?_
      rintro v ⟨hv, av, F, K⟩
      refine WP.mono (next hv (by omega) av) ?_
      rintro t ⟨ht, args, Ft, Kt⟩
      exact ⟨ht, args, F.trans Ft, K.trans Kt⟩
  exact copyMany 10 (by decide)

end VG.Proof.RsaPkcs1Enc.X86.Enc
