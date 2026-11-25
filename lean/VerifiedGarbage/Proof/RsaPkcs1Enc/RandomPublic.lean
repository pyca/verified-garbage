module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Random
public import VerifiedGarbage.Proof.Framework.PublicOut
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: every target's proofs of the function share it

/-!
# The entropy RSAES-PKCS1-v1_5 encryption asks for is public

Every target's `vg_rsa_pkcs1_encrypt_random` is proven against
`encryptRandomAskedContract`: `Spec.RsaPkcs1Enc.encryptRandomContract`, but that
the length of the next tape it asks for is not any that the specification allows
but the one the code asks for (`PadAsked`), a function of the lengths and of
which octets of the tape are zero. It implies the contract of the specification
(`encryptRandom_imp`), and that the length is public (`encryptRandom_public`,
`Spec.RsaPkcs1Enc.encryptRandomOut`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc

open VG.Spec (Entropy.Result.Requests Entropy.RequestValid)
open VG.Spec.RsaPkcs1Enc
open VG.Spec.Rsa (bytesAt wordsAt lenValid publicScratchWords)

/-! ## The length the code asks for -/

/-- The length the code asks for after drawing a padding string of `n` octets from
`rand`: as many more octets as it lacks, up to the budget, or 0 if it asks for none. -/
def padRequested (n : Nat) (rand : List Byte) : Nat :=
  if (nz rand).length < n ∧ rand.length < n + 128 then min (n + 128) (rand.length + n - (nz rand).length)
  else 0

/-- The code asks for `q`, which the contract allows. -/
def PadAsked (n : Nat) (rand : List Byte) (q : Nat) : Prop :=
  (padSearch n rand).Requests (padEntropy n) q ∧ q = padRequested n rand

theorem padAsked_accepted {n : Nat} {rand ps : List Byte} {i : Nat} (h : nonzeroPrefix n rand = some (ps, i)) :
    PadAsked n rand 0 := by
  refine ⟨?_, ?_⟩
  · simp only [Spec.Entropy.Result.Requests, (padSearch_accepted h).1]
  · rw [padRequested, ite_eq_right fun hn => ?_]
    rw [nonzeroPrefix_none hn.1] at h
    cases h

theorem padAsked_exhausted {n : Nat} {rand : List Byte} (h : (nz rand).length < n)
    (hl : padEntropy n ≤ rand.length) : PadAsked n rand 0 := by
  refine ⟨?_, ?_⟩
  · simp only [Spec.Entropy.Result.Requests, (padSearch_exhausted h hl).1]
  · rw [padRequested, ite_eq_right fun hn => Nat.not_le.mpr hn.2 hl]

theorem padAsked_entropy {n q : Nat} {rand : List Byte} (h : (nz rand).length < n)
    (hl : rand.length < padEntropy n) (hq : q = min (n + 128) (rand.length + n - (nz rand).length)) :
    PadAsked n rand q := by
  refine ⟨?_, ?_⟩
  · simp only [Spec.Entropy.Result.Requests, (padSearch_entropy h hl).1]
    rw [hq]
    unfold padEntropy at *
    exact ⟨Nat.lt_min.mpr ⟨hl, by omega_using [h]⟩, Nat.min_le_left _ _⟩
  · rw [padRequested, ite_eq_left ⟨h, hl⟩, hq]

/-! ## It is a function of what is public -/

/-- How many octets are not zero, by which are. -/
theorem nz_mask : ∀ xs : List Byte, (nz xs).length = ((zeroMask xs).filter (· == 0)).length
  | [] => rfl
  | b :: xs => by
    have ih := nz_mask xs
    simp only [zeroMask, List.map_cons] at ih ⊢
    by_cases hb : b = 0
    · subst hb
      rw [nz_cons_zero, ih]; rfl
    · rw [nz_cons_ne hb, ite_eq_right hb, List.filter_cons_of_pos (by rfl), List.length_cons, List.length_cons, ih]

theorem nz_lt_of {n : Nat} {r₁ r₂ : List Byte} (hl : r₁.length = r₂.length)
    (h : (padSearch n r₁).trace = (padSearch n r₂).trace) (h₁ : (nz r₁).length < n) :
    (nz r₁).length = (nz r₂).length := by
  have hs := scanLen_eq h
  rw [scanLen_all h₁] at hs
  rw [trace_eq, trace_eq, scanLen_all h₁, ← hs, List.take_length, hl, List.take_length] at h
  rw [nz_mask, nz_mask, h]

theorem padRequested_congr {n : Nat} {r₁ r₂ : List Byte} (hl : r₁.length = r₂.length)
    (h : (padSearch n r₁).trace = (padSearch n r₂).trace) : padRequested n r₁ = padRequested n r₂ := by
  unfold padRequested
  by_cases h₁ : (nz r₁).length < n
  · rw [nz_lt_of hl h h₁, hl]
  · have h₂ : ¬ (nz r₂).length < n := fun h₂ => h₁ (nz_lt_of hl.symm h.symm h₂ ▸ h₂)
    rw [ite_eq_right fun hn => h₁ hn.1, ite_eq_right fun hn => h₂ hn.1]

/-! ## The contract -/

/-- `Spec.RsaPkcs1Enc.encryptRandomContract`, for code that asks for the next tape as
`PadAsked` says. -/
def encryptRandomAskedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptRandomSig.contract A
    (pre := fun _out outLen _tape _n nLen _e eLen _msg msgLen _rand randLen _scratch scratchLen
        _pre preLen _ =>
      lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ 1 ≤ eLen.toNat ∧
        eLen.toNat ≤ nLen.toNat ∧ msgLen.toNat + 11 ≤ nLen.toNat ∧
        randLen.toNat ≤ padEntropy (nLen.toNat - msgLen.toNat - 3) ∧
        publicScratchWords nLen.toNat ≤ scratchLen.toNat ∧
        preLen.toNat = Spec.Rsa.precomputedWords nLen.toNat)
    (post := fun out _outLen tape n nLen e eLen msg msgLen rand randLen _scratch _scratchLen pre
        preLen m m' r =>
      let psLen := nLen.toNat - msgLen.toNat - 3
      let res := padSearch psLen (bytesAt m rand randLen.toNat)
      (∃ requested, wordsAt m' tape 2 = [BitVec.ofNat 64 res.used, BitVec.ofNat 64 requested] ∧
        PadAsked psLen (bytesAt m rand randLen.toNat) requested) ∧
      match res.outcome with
      | .accepted ps =>
        Spec.Rsa.publicPrecompute (bytesAt m n nLen.toNat) = some (wordsAt m pre preLen.toNat) →
          writtenRandom m' out nLen.toNat r
            (encrypt (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat)
              (bytesAt m msg msgLen.toNat) ps)
      | .entropy .. => r = 0 ∧ bytesAt m' out nLen.toNat = List.replicate nLen.toNat 0
      | .exhausted => r = 3 ∧ bytesAt m' out nLen.toNat = List.replicate nLen.toNat 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _tape n nLen e eLen _msg msgLen rand randLen _scratch
        _scratchLen pre preLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat) ++
        (wordsAt m pre preLen.toNat).map (·.toNat) ++
        (padSearch (nLen.toNat - msgLen.toNat - 3) (bytesAt m rand randLen.toNat)).trace)

/-- `encryptRandomApi` with that contract: the forms that clean up a function's code take
an `Api`. -/
def encryptRandomAskedApi : Api :=
  { encryptRandomApi with contracts := some fun A stack => encryptRandomAskedContract A stack }

/-- `F` at the arguments `vs`. -/
theorem encryptRandom_apply {α : Type} (pb : Nat) (F : Curry (encryptRandomSig.words pb) α) :
    ∀ vs, Curry.apply (encryptRandomSig.words pb) F vs =
      @id (Addr → BitVec pb → Addr → Addr → BitVec pb → Addr → BitVec pb → Addr → BitVec pb → Addr → BitVec pb →
          Addr → BitVec pb → Addr → BitVec pb → α) F
        (vs.getD 0 0) ((vs.getD 1 0).setWidth pb) (vs.getD 2 0) (vs.getD 3 0) ((vs.getD 4 0).setWidth pb)
        (vs.getD 5 0) ((vs.getD 6 0).setWidth pb) (vs.getD 7 0) ((vs.getD 8 0).setWidth pb) (vs.getD 9 0)
        ((vs.getD 10 0).setWidth pb) (vs.getD 11 0) ((vs.getD 12 0).setWidth pb) (vs.getD 13 0)
        ((vs.getD 14 0).setWidth pb)
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
  | [_, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _]
  | [_, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _]
  | [_, _, _, _, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _, _, _, _]
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _]
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem encryptRandom_imp {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack rb : Nat}
    (h : VerifiedScrubbed T c (encryptRandomAskedContract A stack) rb)
    (hR : (T.noResidue.elim False fun R => R c (encryptRandomAskedContract A stack) rb) →
      T.noResidue.elim False fun R => R c (encryptRandomContract A stack) rb) :
    VerifiedScrubbed T c (encryptRandomContract A stack) rb :=
  h.post_mono hR fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨⟨q, h₁, h₂⟩, h₃⟩ => ⟨⟨q, h₁, h₂.1⟩, h₃⟩

/-- The length of the next tape is public. -/
theorem encryptRandom_public {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack rb : Nat}
    (h : VerifiedScrubbed T c (encryptRandomAskedContract A stack) rb) :
    encryptRandomOut.Of A c (encryptRandomContract A stack) := by
  refine PublicOut.of_post h.verified fun vals hv s₁ s₂ s₁' s₂' _ _ hpub _ h₁ h₂ => ?_
  simp only [Sig.contract] at hpub
  rw [hv] at hpub
  have hl := hpub.1.2
  have hw (i : Nat) (hi : i = 4 ∨ i = 6 ∨ i = 8 ∨ i = 10 ∨ i = 14) :
      ((vals s₁).getD i 0).setWidth A.ptrBits = ((vals s₂).getD i 0).setWidth A.ptrBits := by
    have := hpub.2.1 i (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> rfl)
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact this
  have h4 := hw 4 (by decide)
  have h6 := hw 6 (by decide)
  have h8 := hw 8 (by decide)
  have h10 := hw 10 (by decide)
  have h14 := hw 14 (by decide)
  replace hl := (congrFun (encryptRandom_apply A.ptrBits _ _) _).symm.trans
    (hl.trans (congrFun (encryptRandom_apply A.ptrBits _ _) _))
  replace h₁ := (congrFun (congrFun (congrFun (encryptRandom_apply A.ptrBits _ _) _) _) _).mp h₁
  replace h₂ := (congrFun (congrFun (congrFun (encryptRandom_apply A.ptrBits _ _) _) _) _).mp h₂
  dsimp only [id] at hl h₁ h₂
  have ho (s s' : T.isa.State) := congrFun (congrFun (congrFun
    (encryptRandom_apply A.ptrBits (encryptRandomOut.out A.ptrBits) (vals s)) (A.mem s)) (A.mem s')) ((A.ret s').setWidth _)
  refine (ho s₁ s₁').trans (Eq.trans ?_ (ho s₂ s₂').symm)
  dsimp only [id, encryptRandomOut]
  obtain ⟨⟨q₁, hw₁, -, hq₁⟩, -⟩ := h₁
  obtain ⟨⟨q₂, hw₂, -, hq₂⟩, -⟩ := h₂
  have e₁ := congrArg (·.getD 1 0) hw₁
  have e₂ := congrArg (·.getD 1 0) hw₂
  simp only [wordsAt, List.range, List.range.loop, List.map_cons, List.getD_cons_succ, List.getD_cons_zero,
    Nat.reduceMul] at e₁ e₂
  obtain ⟨-, htr⟩ := List.append_inj hl (by
    simp only [List.length_append, List.length_map, wordsAt, bytesAt, List.length_range, h4, h6, h14])
  refine List.cons_eq_cons.mpr ⟨?_, rfl⟩
  refine congrArg BitVec.toNat (e₁.trans (Eq.trans (congrArg (BitVec.ofNat 64) ?_) e₂.symm))
  rw [h4, h8] at hq₁ htr
  rw [hq₁, hq₂]
  exact padRequested_congr (by simp only [bytesAt, List.length_map, List.length_range, h10]) htr

end VG.Proof.RsaPkcs1Enc
