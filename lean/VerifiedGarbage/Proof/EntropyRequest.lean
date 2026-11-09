module

public import VerifiedGarbage.Spec.RsaKeyGen.Generation
public import VerifiedGarbage.Spec.Ffdh.Generation

/-! # The entropy requests the searches' code makes

`Spec/Entropy.lean` lets a search ask for any next tape longer than the octets
it had left and at most its budget (`Spec.Entropy.RequestValid`). The code of
the RSA prime search and of the FFDH parameter search asks for twice the
larger of the octets left and a floor, capped at the budget (`request`), so
that the octets replayed by unfinished steps are at most about as many as
those consumed. This is that choice, what each target's proof shows its code
computes, and why it is one `RequestValid` allows.
-/

@[expose] public section

namespace VG.Proof.Entropy

/-- The next tape's length when `available` octets did not hold a whole step:
at least twice as many, at least `floor`, and at most the budget `cap`. -/
def request (floor cap available : Nat) : Nat := min (2 * max available floor) cap

theorem request_valid {floor cap available : Nat} (hfloor : 0 < floor) (hroom : available < cap) :
    Spec.Entropy.RequestValid cap available (request floor cap available) := by
  unfold request
  have h₁ := Nat.le_max_left available floor
  have h₂ := Nat.le_max_right available floor
  exact ⟨Nat.lt_min.mpr ⟨by omega, hroom⟩, Nat.min_le_right _ _⟩

/-- The length the code writes after the result `r`: `f` of the octets left
for more entropy, and 0 otherwise. -/
def requested {σ α : Type} (f : Nat → Nat) (r : Spec.Entropy.Result σ α) : Nat :=
  match r.outcome with
  | .entropy _ available => f available
  | _ => 0

theorem requested_requests {σ α : Type} {f : Nat → Nat} {cap : Nat} {r : Spec.Entropy.Result σ α}
    (h : ∀ s a, r.outcome = .entropy s a → Spec.Entropy.RequestValid cap a (f a)) :
    r.Requests cap (requested f r) := by
  obtain ⟨o, u, tr⟩ := r
  cases o with
  | entropy s a => exact h s a rfl
  | accepted => rfl
  | exhausted => rfl

/-- Two results with the same status and octets left have the same request. -/
theorem requested_congr {σ α : Type} {f : Nat → Nat} {r t : Spec.Entropy.Result σ α}
    (hs : r.status = t.status) (ha : r.available = t.available) :
    requested f r = requested f t := by
  obtain ⟨o, u, tr⟩ := r
  obtain ⟨o', u', tr'⟩ := t
  cases o <;> cases o' <;> first
    | rfl
    | (simp only [Spec.Entropy.Result.status, Spec.Entropy.Outcome.status] at hs; omega)
    | (simp only [requested]; simp only [Spec.Entropy.Result.available] at ha; rw [ha])

end VG.Proof.Entropy

namespace VG.Proof.RsaKeyGen

/-- The prime search's next tape (`Entropy.request`): at first `32 * pLen`, a
candidate and 31 witness draws. -/
def primeRequest (pLen available : Nat) : Nat :=
  Entropy.request (16 * pLen) (Spec.RsaKeyGen.primeEntropy pLen) available

/-- The length the prime search's code writes after the result `r`. -/
def requested (pLen : Nat) (r : Spec.RsaKeyGen.PrimeSearchResult) : Nat :=
  Entropy.requested (primeRequest pLen) r

end VG.Proof.RsaKeyGen

namespace VG.Proof.Ffdh

/-- The FFDH parameter search's next tape (`Entropy.request`): at first 512
octets per octet of p, enough for a candidate and the 2 · 128 witnesses of its
two Miller–Rabin tests even when about half of the witness draws are
rejected. -/
def parameterRequest (bits available : Nat) : Nat :=
  Entropy.request (256 * ((bits + 7) / 8)) (Spec.Ffdh.parameterEntropy bits) available

/-- The length the FFDH parameter search's code writes after the result `r`. -/
def requested (bits : Nat) : Spec.Ffdh.ParameterSearchResult → Nat
  | .entropy _ available _ => parameterRequest bits available
  | _ => 0

/-- The first tape's length the code asks for, 512 octets per octet of p, is
one the contract allows. -/
theorem first_valid {bits : Nat} (h : 512 ≤ bits) :
    Spec.Entropy.RequestValid (Spec.Ffdh.parameterEntropy bits) 0 (512 * ((bits + 7) / 8)) := by
  unfold Spec.Entropy.RequestValid Spec.Ffdh.parameterEntropy
  omega

theorem requested_requests {bits : Nat} {r : Spec.Ffdh.ParameterSearchResult}
    (h : ∀ k a u, r = .entropy k a u → Spec.Entropy.RequestValid (Spec.Ffdh.parameterEntropy bits) a
      (parameterRequest bits a)) :
    r.Requests (Spec.Ffdh.parameterEntropy bits) (requested bits r) := by
  cases r with
  | entropy k a u => exact h k a u rfl
  | accepted => rfl
  | exhausted => rfl

end VG.Proof.Ffdh
