module

public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.Sig

/-!
# Ed25519's whole functions: their contracts read only their buffers

A function that allocates a buffer of its own in a frame and wipes it
(`Verified.stackScratchWiped`) needs its pre- and postconditions to read the
memory on entry (`*_local`) and on return (`*Out_local`) only within the
function's buffers. Ed25519's verification reads the public key, the message
and the signature on entry, each with `bytesAt`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.WholeLocal

open VG VG.Spec.Ed25519

theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) : bytesAt m₂ p n = bytesAt m₁ p n := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => (h _ ?_).symm
  have hi := List.mem_range.mp hi
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

variable (pb : Nat)

/-- A prefix of the slice's region. -/
theorem slice_agree {m₁ m₂ : Mem} {p l : BitVec 64}
    (h : ∀ a, Region.Contains ⟨p, l.toNat⟩ a 1 → m₁ a = m₂ a) :
    ∀ a, Region.Contains ⟨p, (l.setWidth pb).toNat⟩ a 1 → m₁ a = m₂ a := fun a ha => h a (by
  simp only [Region.Contains, BitVec.toNat_setWidth] at ha ⊢
  have := Nat.mod_le l.toNat (2 ^ pb)
  omega)

/-! ## A seed and its public key

The seed of zeros, read at `0x2000`, and its public key, for the
satisfiability of the contracts that take a seed's digest. -/

def satSeed : List Byte := bytesAt (fun _ => 0) 0x2000 32
def satKey : List Byte := publicKey satSeed

theorem satKey_length : satKey.length = 32 := by
  simp only [satKey, publicKey, encodePoint, encodeLE, List.length_map, List.length_range]

/-- `verifyContract`'s postcondition and leak. -/
def verifyPost : verifySig.Post pb :=
  fun pk message len signature _scratch m _m' r =>
    r = if verify (bytesAt m pk 32) (bytesAt m message len.toNat) (bytesAt m signature 64) then 1 else 0

def verifyLeak : Curry (verifySig.words pb) (Mem → List Nat) :=
  fun pk message len signature _scratch m =>
    (bytesAt m pk 32 ++ bytesAt m message len.toNat ++ bytesAt m signature 64).map (·.toNat)

theorem verifyPost_local : ∀ vs m₁ m₂ m' r, vs.length = (verifySig.words pb).length →
    Curry.apply (verifySig.words pb) (Curry.const (fun _ => True) _) vs m₂ →
    (∀ b ∈ Sig.bufs verifySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (verifySig.words pb) (verifyPost pb) vs m₁ m' r →
    Curry.apply (verifySig.words pb) (verifyPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen _ hb h
  match vs, hlen with
  | [pk, msg, l, sg, sc], _ =>
    simp only [verifySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    change r = if verify (bytesAt m₁ pk 32) (bytesAt m₁ msg (l.setWidth pb).toNat) (bytesAt m₁ sg 64) then 1 else 0 at h
    change r = if verify (bytesAt m₂ pk 32) (bytesAt m₂ msg (l.setWidth pb).toNat) (bytesAt m₂ sg 64) then 1 else 0
    rw [bytesAt_congr hb.1, bytesAt_congr (slice_agree pb hb.2.1), bytesAt_congr hb.2.2.1]
    exact h

theorem verifyLeak_local : ∀ f, some (verifyLeak pb) = some f → ∀ vs m₁ m₂,
    vs.length = (verifySig.words pb).length →
    Curry.apply (verifySig.words pb) (Curry.const (fun _ => True) _) vs m₂ →
    (∀ b ∈ Sig.bufs verifySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply _ f vs m₁ = Curry.apply _ f vs m₂ := by
  intro f hf vs m₁ m₂ hlen _ hb
  cases hf
  match vs, hlen with
  | [pk, msg, l, sg, sc], _ =>
    simp only [verifySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    change (bytesAt m₁ pk 32 ++ bytesAt m₁ msg (l.setWidth pb).toNat ++ bytesAt m₁ sg 64).map (·.toNat) =
      (bytesAt m₂ pk 32 ++ bytesAt m₂ msg (l.setWidth pb).toNat ++ bytesAt m₂ sg 64).map (·.toNat)
    rw [bytesAt_congr hb.1, bytesAt_congr (slice_agree pb hb.2.1), bytesAt_congr hb.2.2.1]

end VG.Proof.Ed25519.WholeLocal
