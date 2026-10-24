module

public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.Sig

/-!
# Ed448's whole functions: their contracts read only their buffers

As Ed25519's (`Proof/Ed25519/WholeLocal.lean`): a function that allocates a
buffer of its own in a frame (`Verified.stackScratch`, `…Wiped`,
`…Args`) needs its precondition, postcondition and leak to read the memory
on entry (`*_local`), and for a wiped one its postcondition the memory on
return (`*Out_local`), only within the function's buffers. Ed448's read the
seed, the public key, the context, the message and the signature on entry,
and the output on return, each with `bytesAt`. `satMem` holds a seed and its
public key, for `signCachedContract`'s satisfiability.
-/

@[expose] public section

namespace VG.Proof.Ed448.WholeLocal

open VG VG.Spec.Ed448

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

/-! ## `vg_ed448_public_key` -/

/-- `publicKeyContract`'s postcondition. -/
def publicKeyPost : publicKeySig.Post pb :=
  fun out seed _scratch m m' _ => bytesAt m' out 57 = publicKey (bytesAt m seed 57)

theorem publicKeyPost_local : ∀ vs m₁ m₂ m' r, vs.length = (publicKeySig.words pb).length →
    (∀ b ∈ Sig.bufs publicKeySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (publicKeySig.words pb) (publicKeyPost pb) vs m₁ m' r →
    Curry.apply (publicKeySig.words pb) (publicKeyPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  match vs, hlen with
  | [o, sd, sc], _ =>
    simp only [publicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    change bytesAt m' o 57 = publicKey (bytesAt m₁ sd 57) at h
    change bytesAt m' o 57 = publicKey (bytesAt m₂ sd 57)
    rw [bytesAt_congr hb.2.1]
    exact h

theorem publicKeyPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (publicKeySig.words pb).length →
    (∀ b ∈ Sig.bufs publicKeySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (publicKeySig.words pb) (publicKeyPost pb) vs m m₁ r →
    Curry.apply (publicKeySig.words pb) (publicKeyPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [o, sd, sc], _ =>
    simp only [publicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    change bytesAt m₁ o 57 = publicKey (bytesAt m sd 57) at h
    change bytesAt m₂ o 57 = publicKey (bytesAt m sd 57)
    rw [bytesAt_congr hb.1]
    exact h

/-! ## `vg_ed448_sign_cached` -/

/-- `signCachedContract`'s precondition and postcondition. -/
def signCachedPre : Curry (signCachedSig.words pb) (Mem → Prop) :=
  fun _out seed pk _context ctxlen _message _len _scratch m =>
    bytesAt m pk 57 = publicKey (bytesAt m seed 57) ∧ ctxlen.toNat ≤ 255

def signCachedPost : signCachedSig.Post pb :=
  fun out seed _pk context ctxlen message len _scratch m m' _ =>
    bytesAt m' out 114 = sign (bytesAt m seed 57) (bytesAt m context ctxlen.toNat) (bytesAt m message len.toNat)

theorem signCachedPre_local : ∀ vs m₁ m₂, vs.length = (signCachedSig.words pb).length →
    (∀ b ∈ Sig.bufs signCachedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (signCachedSig.words pb) (signCachedPre pb) vs m₁ →
    Curry.apply (signCachedSig.words pb) (signCachedPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  match vs, hlen with
  | [o, sd, pk, ctx, cl, msg, l, sc], _ =>
    simp only [signCachedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    change bytesAt m₁ pk 57 = publicKey (bytesAt m₁ sd 57) ∧ (cl.setWidth pb).toNat ≤ 255 at h
    change bytesAt m₂ pk 57 = publicKey (bytesAt m₂ sd 57) ∧ (cl.setWidth pb).toNat ≤ 255
    rw [bytesAt_congr hb.2.2.1, bytesAt_congr hb.2.1]
    exact h

theorem signCachedPost_local : ∀ vs m₁ m₂ m' r, vs.length = (signCachedSig.words pb).length →
    (∀ b ∈ Sig.bufs signCachedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (signCachedSig.words pb) (signCachedPost pb) vs m₁ m' r →
    Curry.apply (signCachedSig.words pb) (signCachedPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  match vs, hlen with
  | [o, sd, pk, ctx, cl, msg, l, sc], _ =>
    simp only [signCachedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    change bytesAt m' o 114 = sign (bytesAt m₁ sd 57) (bytesAt m₁ ctx (cl.setWidth pb).toNat)
      (bytesAt m₁ msg (l.setWidth pb).toNat) at h
    change bytesAt m' o 114 = sign (bytesAt m₂ sd 57) (bytesAt m₂ ctx (cl.setWidth pb).toNat)
      (bytesAt m₂ msg (l.setWidth pb).toNat)
    rw [bytesAt_congr hb.2.1, bytesAt_congr (slice_agree pb hb.2.2.2.1),
      bytesAt_congr (slice_agree pb hb.2.2.2.2.1)]
    exact h

/-! ## `vg_ed448_verify` -/

/-- `verifyContract`'s postcondition and leak. -/
def verifyPost : verifySig.Post pb :=
  fun pk context ctxlen message len signature _scratch m _m' r =>
    r = if verify (bytesAt m pk 57) (bytesAt m context ctxlen.toNat) (bytesAt m message len.toNat)
      (bytesAt m signature 114) then 1 else 0

def verifyLeak : Curry (verifySig.words pb) (Mem → List Nat) :=
  fun pk context ctxlen message len signature _scratch m =>
    (bytesAt m pk 57 ++ bytesAt m context ctxlen.toNat ++ bytesAt m message len.toNat ++
      bytesAt m signature 114).map (·.toNat)

theorem verifyPost_local : ∀ vs m₁ m₂ m' r, vs.length = (verifySig.words pb).length →
    Curry.apply (verifySig.words pb) (Curry.const (fun _ => True) _) vs m₂ →
    (∀ b ∈ Sig.bufs verifySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (verifySig.words pb) (verifyPost pb) vs m₁ m' r →
    Curry.apply (verifySig.words pb) (verifyPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen _ hb h
  match vs, hlen with
  | [pk, ctx, cl, msg, l, sg, sc], _ =>
    simp only [verifySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    change r = if verify (bytesAt m₁ pk 57) (bytesAt m₁ ctx (cl.setWidth pb).toNat)
      (bytesAt m₁ msg (l.setWidth pb).toNat) (bytesAt m₁ sg 114) then 1 else 0 at h
    change r = if verify (bytesAt m₂ pk 57) (bytesAt m₂ ctx (cl.setWidth pb).toNat)
      (bytesAt m₂ msg (l.setWidth pb).toNat) (bytesAt m₂ sg 114) then 1 else 0
    rw [bytesAt_congr hb.1, bytesAt_congr (slice_agree pb hb.2.1), bytesAt_congr (slice_agree pb hb.2.2.1),
      bytesAt_congr hb.2.2.2.1]
    exact h

theorem verifyLeak_local : ∀ f, some (verifyLeak pb) = some f → ∀ vs m₁ m₂,
    vs.length = (verifySig.words pb).length →
    Curry.apply (verifySig.words pb) (Curry.const (fun _ => True) _) vs m₂ →
    (∀ b ∈ Sig.bufs verifySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply _ f vs m₁ = Curry.apply _ f vs m₂ := by
  intro f hf vs m₁ m₂ hlen _ hb
  cases hf
  match vs, hlen with
  | [pk, ctx, cl, msg, l, sg, sc], _ =>
    simp only [verifySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    change (bytesAt m₁ pk 57 ++ bytesAt m₁ ctx (cl.setWidth pb).toNat ++ bytesAt m₁ msg (l.setWidth pb).toNat ++
        bytesAt m₁ sg 114).map (·.toNat) =
      (bytesAt m₂ pk 57 ++ bytesAt m₂ ctx (cl.setWidth pb).toNat ++ bytesAt m₂ msg (l.setWidth pb).toNat ++
        bytesAt m₂ sg 114).map (·.toNat)
    rw [bytesAt_congr hb.1, bytesAt_congr (slice_agree pb hb.2.1), bytesAt_congr (slice_agree pb hb.2.2.1),
      bytesAt_congr hb.2.2.2.1]

/-! ## A memory with a seed and its public key

Zeros, the seed at `0x2000`, and its public key at `0x2100`, for
`signCachedContract`'s satisfiability. -/

def satSeed : List Byte := bytesAt (fun _ => 0) 0x2000 57
def satKey : List Byte := publicKey satSeed

theorem satKey_length : satKey.length = 57 := by
  simp only [satKey, publicKey, encodePoint, encodeLE, List.length_map, List.length_range]

def satMem (a : Addr) : Byte :=
  if a.toNat < 0x2100 then 0 else if a.toNat < 0x2139 then satKey[a.toNat - 0x2100]?.getD 0 else 0

theorem sat_seed : bytesAt satMem 0x2000 57 = satSeed := by
  unfold satSeed bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  unfold satMem
  rw [ha]
  simp only [show 0x2000 + i < 0x2100 from by omega, ite_true]

theorem sat_key : bytesAt satMem 0x2100 57 = satKey := by
  apply List.ext_getElem
  · simp only [bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    have hi' : i < 57 := by simpa only [bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x2100 : Addr) + BitVec.ofNat 64 i).toNat = 0x2100 + i := by
      change (0x2100 + i % 2 ^ 64) % 2 ^ 64 = 0x2100 + i
      omega
    simp only [bytesAt, List.getElem_map, List.getElem_range, satMem, ha,
      show ¬ 0x2100 + i < 0x2100 from by omega, ite_false, show 0x2100 + i < 0x2139 from by omega, ite_true,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

theorem sat_pk : bytesAt satMem 0x2100 57 = publicKey (bytesAt satMem 0x2000 57) := by
  rw [sat_seed, sat_key]; rfl

end VG.Proof.Ed448.WholeLocal
