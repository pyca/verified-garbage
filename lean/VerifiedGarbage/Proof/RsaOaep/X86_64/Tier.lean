module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Sel
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Tier
public import VerifiedGarbage.Spec.RsaOaep.AnyHash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSAES-OAEP on x86-64: the hash functions of a tier

The hash functions the selectors choose among (`oaepHs t`): those of
`Spec.RsaOaep.hashIds`, each with the streaming functions of its
implementation in the tier `t`. Their keys are `hashIds` (`oaepHs_keys`), and
they are what the proofs need (`oaepHs_ok`, `oaepHs_good`); the selector `i`
names the hash function `t.get i`, whose `MgfLink` is `HashId.mgf1 i`'s
(`tier_mgf_get`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG.Proof.Pbkdf2.Md.X86_64 (Tier MdHash)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

/-- The hash functions RSA-OAEP takes, by their numbers, in the tier `t`. -/
def oaepHs (t : Tier) : List (Nat × Stream) :=
  Spec.RsaOaep.hashIds.filterMap fun i => (t.get i).map fun h => (i, h.H.stream)

theorem tier_length (t : Tier) : t.hashes.length = 8 := by
  simpa using congrArg List.length t.mgf_ok

theorem tier_get_some (t : Tier) {i : Nat} (hi : i < 8) : ∃ h, t.get i = some h :=
  ⟨t.hashes[i]'(by rw [tier_length t]; exact hi), by simp [Tier.get]⟩

theorem tier_lt_of_get (t : Tier) {i : Nat} {h : MdHash} (hh : t.get i = some h) : i < 8 := by
  rw [← tier_length t]
  exact (List.getElem?_eq_some_iff.mp hh).1

/-- The hash function the selector `i` names in `t` is `HashId.mgf1 i`. -/
theorem tier_mgf_get (t : Tier) {i : Nat} {h : MdHash} (hh : t.get i = some h) :
    Spec.HashId.mgf1 i = some h.mgf.G := by
  have hi := tier_lt_of_get t hh
  have := congrArg (·[i]?) t.mgf_ok
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some] at this
  rw [show t.hashes[i]? = some h from hh] at this
  exact (Option.some.inj this).symm

theorem hashIds_lt {i : Nat} (hi : i ∈ Spec.RsaOaep.hashIds) : i < 8 := by
  simp only [Spec.RsaOaep.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hi; omega

theorem mem_oaepHs {t : Tier} {k : Nat} {H : Stream} :
    (k, H) ∈ oaepHs t ↔ k ∈ Spec.RsaOaep.hashIds ∧ ∃ h, t.get k = some h ∧ H = h.H.stream := by
  simp only [oaepHs, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, h, hh, rfl, rfl⟩; exact ⟨hi, h, hh, rfl⟩
  · rintro ⟨hk, h, hh, rfl⟩; exact ⟨k, hk, h, hh, rfl, rfl⟩

/-- The hash function the selector `k` names, of `oaepHs t`. -/
theorem tier_mem (t : Tier) {k : Nat} {h : MdHash} (hk : k ∈ Spec.RsaOaep.hashIds) (hh : t.get k = some h) :
    (k, h.H.stream) ∈ oaepHs t :=
  mem_oaepHs.mpr ⟨hk, h, hh, rfl⟩

theorem oaepHs_keys (t : Tier) : (oaepHs t).map (·.1) = Spec.RsaOaep.hashIds := by
  obtain ⟨h1, e1⟩ := tier_get_some t (i := 1) (by decide)
  obtain ⟨h2, e2⟩ := tier_get_some t (i := 2) (by decide)
  obtain ⟨h3, e3⟩ := tier_get_some t (i := 3) (by decide)
  obtain ⟨h4, e4⟩ := tier_get_some t (i := 4) (by decide)
  obtain ⟨h5, e5⟩ := tier_get_some t (i := 5) (by decide)
  obtain ⟨h6, e6⟩ := tier_get_some t (i := 6) (by decide)
  obtain ⟨h7, e7⟩ := tier_get_some t (i := 7) (by decide)
  simp [oaepHs, Spec.RsaOaep.hashIds, e1, e2, e3, e4, e5, e6, e7]

theorem oaepHs_ok (t : Tier) : HsOk (oaepHs t) where
  nodup := by rw [oaepHs_keys]; decide
  lt := by rw [oaepHs_keys]; decide
  len := fun ⟨k, H⟩ hp => by
    obtain ⟨-, h, hh, rfl⟩ := mem_oaepHs.mp hp
    show h.H.D = ((Spec.HashId.mgf1 k).map (·.len)).getD 0
    rw [tier_mgf_get t hh]; exact h.mgf.len.symm
  le := fun ⟨k, H⟩ hp => by
    obtain ⟨-, h, -, rfl⟩ := mem_oaepHs.mp hp
    exact Nat.le_trans h.ok.hDN h.ok.N_le

theorem oaepHs_good (t : Tier) : ∀ p ∈ oaepHs t, HGood p.2 := fun ⟨k, H⟩ hp => by
  obtain ⟨-, h, -, rfl⟩ := mem_oaepHs.mp hp
  exact HGood.of h.ok h.K

end VG.Proof.RsaOaep.X86_64
