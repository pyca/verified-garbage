module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptArguments

/-! # The private RSA call's complete cdecl argument area -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.Bignum.X86 VG.Proof.Mont.X86

def privateArgument (g : Geometry) (j : Nat) : BitVec 32 := g.argument (privateInputSlot j)
def PrivateArgs (g : Geometry) (s : State) : Prop := Arguments g (privateArgument g) 20 s

theorem copyPrefix_ok {g : Geometry} (values : Nat → BitVec 32) (input : Nat → Nat) (start n : Nat)
    (bound : start + n ≤ 20) (inputs : ∀ j < n, input j < 23)
    (valuesEq : ∀ j < n, g.argument (input j) = values (start + j))
    {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) (a : Arguments g values start s) :
    WP isa (.block ((List.range n).flatMap fun j => copyArg (input j) (start + j))) s
      fun t => Context g bs t ∧ Arguments g values (start + n) t ∧
        Frame [⟨byteAddr g.stack, 80⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨h, a, Frame.refl _ _, Keeps.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) (fun j hj => inputs j (by omega))
      (fun j hj => valuesEq j (by omega)) h a) ?_
    rintro u ⟨hu, au, F, K⟩
    refine WP.mono (prepareArgument_ok (bs := bs) au (by omega)
      (WP.mono (copyArg_ok u hu (inputs n (by omega)) (by omega)) ?_)) ?_
    · rintro t ⟨ht, M, F', K'⟩
      exact ⟨ht, by rw [valuesEq n (by omega)] at M; exact M, F', K'⟩
    · rintro t ⟨ht, argsT, F', K'⟩
      exact ⟨ht, by simpa only [Nat.add_assoc] using argsT, F.trans F', K.trans K'⟩

theorem privArgs_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) :
    WP isa (.block privArgs) s fun t => Context g bs t ∧ PrivateArgs g t ∧
      Frame [⟨byteAddr g.stack, 80⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold privArgs
  apply copyPrefix_ok (privateArgument g) privateInputSlot 0 20 (by decide) ?_ (by intro j hj; simp only [Nat.zero_add]; rfl) h
    (by intro j hj; omega)
  intro j hj
  unfold privateInputSlot
  split <;> omega

end VG.Proof.RsaPkcs1Enc.X86.Dec
