module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignArguments

/-! # Install all twenty cdecl arguments for checked RSA signing -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Sign VG.Proof.Bignum.X86 VG.Proof.Mont.X86

def privateArgument (g : Geometry) (j : Nat) : BitVec 32 :=
  if j < 6 then g.argument j else if j = 6 then g.temporary else if j = 7 then g.argument 3 else g.argument (j + 1)

def PrivateArgs (g : Geometry) (s : State) : Prop := Arguments g (privateArgument g) 20 s

theorem copyPrefix_ok {g : Geometry} (values : Nat → BitVec 32) (input : Nat → Nat) (start n : Nat)
    (bound : start + n ≤ 20) (inputs : ∀ j < n, input j < 21)
    (valuesEq : ∀ j < n, g.argument (input j) = values (start + j))
    {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) (a : Arguments g values start s) :
    WP isa (.block ((List.range n).flatMap fun j => copyArgument (input j) (start + j))) s
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
      (WP.mono (copyArgument_ok u hu (inputs n (by omega)) (by omega)) ?_)) ?_
    · rintro t ⟨ht, M, F', K'⟩
      exact ⟨ht, by rw [valuesEq n (by omega)] at M; exact M, F', K'⟩
    · rintro t ⟨ht, argsT, F', K'⟩
      exact ⟨ht, by simpa only [Nat.add_assoc] using argsT, F.trans F', K.trans K'⟩

theorem callArgs_ok {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) :
    WP isa (.block callArgs) s fun t => Context g bs t ∧ PrivateArgs g t ∧
      Frame [⟨byteAddr g.stack, 80⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold callArgs
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyPrefix_ok (g := g) (privateArgument g) id 0 6 (by decide)
    (by intro j hj; exact Nat.lt_trans hj (by decide))
    (by intro j hj; simp only [id_eq, Nat.zero_add, privateArgument, hj, ite_true]) h
    (by intro j hj; omega)) ?_
  rintro a ⟨ha, aa, F, K⟩
  refine WP.mono (prepareArgument_ok (bs := bs) aa (by decide : 6 < 20)
    (WP.mono (localArgument_ok a ha emOffset (by decide : 6 < 20)) ?_)) ?_
  · rintro t ⟨ht, M, F', K'⟩
    exact ⟨ht, by simpa only [privateArgument, Geometry.temporary, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ite_false, ite_true] using M, F', K'⟩
  rintro b ⟨hb, ab, Fb, Kb⟩
  refine WP.mono (prepareArgument_ok (bs := bs) ab (by decide : 7 < 20)
    (WP.mono (copyArgument_ok b hb (by decide : 3 < 21) (by decide : 7 < 20)) ?_)) ?_
  · rintro t ⟨ht, M, F', K'⟩
    exact ⟨ht, by simpa only [privateArgument, Geometry.temporary, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ite_false, ite_true] using M, F', K'⟩
  rintro c ⟨hc, ac, Fc, Kc⟩
  simp only [show (fun j : Nat => copyArgument (j + 9) (j + 8)) = (fun j => copyArgument (j + 9) (8 + j)) by funext j; rw [Nat.add_comm j 8]]
  refine WP.mono (copyPrefix_ok (g := g) (privateArgument g) (fun j => j + 9) 8 12 (by decide)
    (by intro j hj; omega) (by intro j hj; simp only [privateArgument, show ¬8 + j < 6 by omega,
      show ¬8 + j = 6 by omega, show ¬8 + j = 7 by omega, ite_false]; congr 1; omega) hc ac) ?_
  rintro t ⟨ht, argsT, Ft, Kt⟩
  exact ⟨ht, argsT, F.trans (Fb.trans (Fc.trans Ft)), K.trans (Kb.trans (Kc.trans Kt))⟩

end VG.Proof.RsaPkcs1Sig.X86.Sgn
