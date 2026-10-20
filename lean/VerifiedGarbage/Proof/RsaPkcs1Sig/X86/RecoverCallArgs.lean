module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverArguments
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Recover
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverLocalArgument
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStackWord
import VerifiedGarbage.Proof.Framework.Contract

/-! # All ten arguments of precomputed public RSA verification -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (em1Offset copyArgument localArgument)
open VG.Impl.RsaPkcs1Sig.X86.Recover (pubArgs)

def publicArgument (g : Geometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.em1 | 1 => BitVec.ofNat 32 g.length
  | 2 => g.sources 3 | 3 => BitVec.ofNat 32 g.preLength
  | 4 => g.sources 1 | 5 => BitVec.ofNat 32 g.exponentLength
  | 6 => g.sources 2 | 7 => BitVec.ofNat 32 g.length
  | 8 => g.workspace | _ => BitVec.ofNat 32 g.scratchLength

private def inputSlot (j : Nat) : Nat :=
  match j with
  | 1 => 3 | 2 => 11 | 3 => 12 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 3 | 8 => 9 | _ => 10

theorem pubArgs_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) :
    WP isa (.block pubArgs) s fun t => Context g bs t ∧ Arguments g (publicArgument g) 10 t ∧
      Frame [⟨byteAddr g.stack, 40⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  have first : WP isa (.block (localArgument em1Offset 0)) s fun t =>
      Context g bs t ∧ Arguments g (publicArgument g) 1 t ∧
      Frame [⟨byteAddr g.stack, 40⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
    apply prepareArgument_ok (bs := bs) (n := 0) (by intro j hj; omega) (by decide)
    exact localArgument_ok s h em1Offset (by decide)
  have next {u : State} (hu : Context g bs u) {j : Nat} (hj : 1 ≤ j) (hj' : j < 10)
      (a : Arguments g (publicArgument g) j u) :
      WP isa (.block (copyArgument (inputSlot j) j)) u fun t =>
        Context g bs t ∧ Arguments g (publicArgument g) (j + 1) t ∧
        Frame [⟨byteAddr g.stack, 40⟩] u.mem t.mem ∧ Keeps [.eax] u t := by
    have inputBound : inputSlot j < 13 := by
      rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have value : g.argument (inputSlot j) = publicArgument g j := by
      rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    apply prepareArgument_ok (bs := bs) a hj'
    refine WP.mono (copyArgument_ok u hu inputBound hj') ?_
    rintro t ⟨ht, M, F, K⟩
    exact ⟨ht, by rw [value] at M; exact M, F, K⟩
  have copyMany (n : Nat) (hn : n ≤ 9) {u : State} (hu : Context g bs u)
      (a : Arguments g (publicArgument g) 1 u) :
      WP isa (.block ((List.range n).flatMap fun j => copyArgument (inputSlot (j + 1)) (j + 1))) u
        fun t => Context g bs t ∧ Arguments g (publicArgument g) (n + 1) t ∧
          Frame [⟨byteAddr g.stack, 40⟩] u.mem t.mem ∧ Keeps [.eax] u t := by
    induction n generalizing u with
    | zero => exact WP.block_nil ⟨hu, a, Frame.refl _ _, Keeps.refl _ _⟩
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
      refine WP.mono (ih (by omega) hu a) ?_
      rintro v ⟨hv, av, F, K⟩
      refine WP.mono (next hv (by omega) (by omega) av) ?_
      rintro t ⟨ht, args, Ft, Kt⟩
      exact ⟨ht, args, F.trans Ft, K.trans Kt⟩
  have code : pubArgs = localArgument em1Offset 0 ++
      (List.range 9).flatMap (fun j => copyArgument (inputSlot (j + 1)) (j + 1)) := rfl
  rw [code, WP.block_append_iff]
  refine WP.mono first ?_
  rintro u ⟨hu, args, F, K⟩
  refine WP.mono (copyMany 9 (by decide) hu args) ?_
  rintro t ⟨ht, argsT, Ft, Kt⟩
  exact ⟨ht, argsT, F.trans Ft, K.trans Kt⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv
