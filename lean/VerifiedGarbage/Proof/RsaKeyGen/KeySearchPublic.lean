module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.Framework.PublicOut
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract

-- separate module: every target's proofs of the key search share it

/-!
# The entropy the RSA key search asks for is public

Every target's `vg_rsa_generate` is proven against `keySearchAskedContract`:
`Spec.RsaKeyGen.keySearchContract`, but that the length of the next tape it asks
for is not any that the specification allows but the one the code asks for
(`Asked`), a function of what the contract declares it may leak. It implies the
contract of the specification (`keySearch_imp`), and that the length is public
(`keySearch_public`, `Spec.RsaKeyGen.keySearchOut`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG.Spec.Rsa (bytesAt wordsAt os2ip scratchWords)
open VG.Spec.RsaKeyGen

/-- `Spec.RsaKeyGen.keySearchContract`, for code that asks for the next tape as `Asked`
says. -/
def keySearchAskedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  keySearchSig.contract A
    (pre := fun _key keyLen _used _rand randLen _scratch scratchLen state m =>
      let pLen := (m.readW (state + 8) 64).toNat
      let eB := bytesAt m (state + 48) 8
      primeLenValid pLen ∧ keyLen.toNat = 9 * pLen ∧
      scratchWords (2 * pLen) ≤ scratchLen.toNat ∧
      (m.readW state 64).toNat ≤ primeLimit (8 * pLen) (os2ip eB) ∧
      m.readW (state + 16) 64 = BitVec.ofNat 64 (primeEntropy pLen) ∧
      (m.readW (state + 32) 64).toNat ≤ 1 ∧
      randLen.toNat ≤ primeEntropy pLen)
    (post := fun key _keyLen used rand randLen _scratch _scratchLen state m m' r =>
      let pLen := (m.readW (state + 8) 64).toNat
      let eB := bytesAt m (state + 48) 8
      let result := keySearch pLen eB (keyProgressAt m key state pLen)
        (bytesAt m rand randLen.toNat)
      let s := result.progress
      r.toNat = result.keyStatus ∧
      bytesAt m' key (9 * pLen) = keySearchBytes pLen result ∧
      wordsAt m' used 1 = [BitVec.ofNat 64 result.used] ∧
      ∃ requested, wordsAt m' state 6 = [BitVec.ofNat 64 s.remaining,
        BitVec.ofNat 64 pLen, BitVec.ofNat 64 (primeEntropy pLen), BitVec.ofNat 64 requested,
        BitVec.ofNat 64 (if s.phase = .p then 0 else 1), BitVec.ofNat 64 s.left] ∧
        bytesAt m' (state + 48) 8 = eB ∧
        Asked pLen result requested)
    (writeArgs := true) (stack := stack)
    (leak := some fun key _keyLen _used rand randLen _scratch _scratchLen state m =>
      let pLen := (m.readW (state + 8) 64).toNat
      let result := keySearch pLen (bytesAt m (state + 48) 8) (keyProgressAt m key state pLen)
        (bytesAt m rand randLen.toNat)
      (wordsAt m state 7).map (·.toNat) ++
        [result.keyStatus, result.used, result.available] ++ result.trace)

/-- `keySearchApi` with that contract: the forms that clean up a function's code take an
`Api`. -/
def keySearchAskedApi : Api :=
  { keySearchApi with contracts := some fun A stack => keySearchAskedContract A stack }

/-- `F` at the arguments `vs`. -/
theorem keySearch_apply {α : Type} (pb : Nat) (F : Curry (keySearchSig.words pb) α) :
    ∀ vs, Curry.apply (keySearchSig.words pb) F vs =
      @id (Addr → BitVec pb → Addr → Addr → BitVec pb → Addr → BitVec pb → Addr → α) F
        (vs.getD 0 0) ((vs.getD 1 0).setWidth pb) (vs.getD 2 0) (vs.getD 3 0) ((vs.getD 4 0).setWidth pb)
        (vs.getD 5 0) ((vs.getD 6 0).setWidth pb) (vs.getD 7 0)
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
  | [_, _, _, _, _, _, _] | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => rfl

/-- Two results of the key search with the same status and octets left have the same
request. -/
theorem requested_congr (L : Nat) {r t : KeySearchResult} (hs : r.keyStatus = t.keyStatus)
    (ha : r.available = t.available) :
    Entropy.requested (primeRequest L) r = Entropy.requested (primeRequest L) t := by
  obtain ⟨o, u, tr⟩ := r
  obtain ⟨o', u', tr'⟩ := t
  refine Entropy.requested_congr ?_ ha
  simp only [KeySearchResult.keyStatus] at hs
  rcases o with ⟨_, _⟩ | ⟨_ | _⟩ | _ <;> rcases o' with ⟨_, _⟩ | ⟨_ | _⟩ | _ <;> first
    | rfl
    | simp at hs

/-- What `keySearchAskedContract` requires of a run meets
`Spec.RsaKeyGen.keySearchContract`. -/
theorem keySearch_imp {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack rb : Nat}
    (h : VerifiedScrubbed T c (keySearchAskedContract A stack) rb)
    (hR : (T.noResidue.elim False fun R => R c (keySearchAskedContract A stack) rb) →
      T.noResidue.elim False fun R => R c (keySearchContract A stack) rb) :
    VerifiedScrubbed T c (keySearchContract A stack) rb :=
  h.post_mono hR fun _ _ _ _ _ _ _ _ _ _ _ ⟨h₁, h₂, h₃, q, h₄, h₅, h₆⟩ => ⟨h₁, h₂, h₃, q, h₄, h₅, h₆.1⟩

/-- The length of the next tape is public. -/
theorem keySearch_public {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack rb : Nat}
    (h : VerifiedScrubbed T c (keySearchAskedContract A stack) rb) :
    keySearchOut.Of A c (keySearchContract A stack) := by
  refine PublicOut.of_post h.verified fun vals hv s₁ s₂ s₁' s₂' _ _ hpub _ h₁ h₂ => ?_
  simp only [Sig.contract] at hpub
  rw [hv] at hpub
  have hl := hpub.1.2
  replace hl := (congrFun (keySearch_apply A.ptrBits _ _) _).symm.trans
    (hl.trans (congrFun (keySearch_apply A.ptrBits _ _) _))
  replace h₁ := (congrFun (congrFun (congrFun (keySearch_apply A.ptrBits _ _) _) _) _).mp h₁
  replace h₂ := (congrFun (congrFun (congrFun (keySearch_apply A.ptrBits _ _) _) _) _).mp h₂
  dsimp only [id] at hl h₁ h₂
  have ho (s s' : T.isa.State) := congrFun (congrFun (congrFun
    (keySearch_apply A.ptrBits (keySearchOut.out A.ptrBits) (vals s)) (A.mem s)) (A.mem s')) ((A.ret s').setWidth _)
  refine (ho s₁ s₁').trans (Eq.trans ?_ (ho s₂ s₂').symm)
  dsimp only [id, keySearchOut]
  obtain ⟨-, -, -, q₁, hw₁, -, -, hq₁⟩ := h₁
  obtain ⟨-, -, -, q₂, hw₂, -, -, hq₂⟩ := h₂
  have e₁ := congrArg (·.getD 3 0) hw₁
  have e₂ := congrArg (·.getD 3 0) hw₂
  simp only [wordsAt, List.range, List.range.loop, List.map_cons, List.getD_cons_succ, List.getD_cons_zero,
    Nat.reduceMul] at e₁ e₂
  obtain ⟨hab, -⟩ := List.append_inj hl (by simp [wordsAt])
  obtain ⟨hw, hc⟩ := List.append_inj hab (by simp [wordsAt])
  simp only [List.cons.injEq, and_true] at hc
  have hL := congrArg (·.getD 1 0) hw
  simp only [wordsAt, List.range, List.range.loop, List.map_cons, List.getD_cons_succ, List.getD_cons_zero,
    Nat.reduceMul] at hL
  refine List.cons_eq_cons.mpr ⟨?_, rfl⟩
  refine congrArg BitVec.toNat (e₁.trans (Eq.trans (congrArg (BitVec.ofNat 64) ?_) e₂.symm))
  rw [hq₁, hq₂, requested_congr _ hc.1 hc.2.2]
  refine congrArg (fun L => Entropy.requested (primeRequest L) _) ?_
  exact hL

end VG.Proof.RsaKeyGen
