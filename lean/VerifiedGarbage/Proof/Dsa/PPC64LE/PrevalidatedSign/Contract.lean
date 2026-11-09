module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Front
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.KeyPair
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# DSA prevalidated signing on PPC64LE: the contract on the registers

`spContract`: `vg_dsa_sign_prevalidated`, with `vg_dsa_sign`'s arguments,
result and public data (`sContract`), for a key whose exact octets pass the
specification's private-key validation. `validatePrivate_spec`: that
validation of the packed key at `key` is `KeyOk` (the checks of its public
part), `0 < x < q` and `g^x mod p = y`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE

/-- `vg_dsa_sign_prevalidated`, on the registers and the stack. -/
def spContract : Contract isa where
  pre s := sContract.pre s ∧ Spec.Dsa.validatePrivateKeyBytes (s.gpr .r7).toNat (s.gpr .r9).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) = true
  post := sContract.post
  pub := sContract.pub

/-- What private-key validation checks, on the packed key at `key`. -/
def PrivOk (m : Mem) (L : Lay) (key : Addr) : Prop :=
  KeyOk m L key ∧ (0 < xOf m L key ∧ xOf m L key < qOf m L key) ∧
    gOf m L key ^ xOf m L key % pOf m L key = yOf m L key

instance (m : Mem) (L : Lay) (key : Addr) : Decidable (PrivOk m L key) := by
  unfold PrivOk KeyOk
  infer_instance

theorem validatePrivate_spec {m : Mem} {L : Lay} {key : Addr} (hv : Spec.Dsa.lengthsValid L.pl L.ql) :
    Spec.Dsa.validatePrivateKeyBytes L.pl L.ql (Spec.Rsa.bytesAt m key (3 * L.pl + 2 * L.ql)) =
      decide (PrivOk m L key) := by
  have hkey : Spec.Dsa.privateKeyBytes L.pl L.ql (Spec.Rsa.bytesAt m key (3 * L.pl + 2 * L.ql)) =
      ⟨⟨pOf m L key, qOf m L key, gOf m L key⟩, yOf m L key, some (xOf m L key)⟩ := by
    rw [VG.Proof.Dsa.privateKeyBytes_at m key (Nat.le_refl _),
      VG.Proof.Dsa.publicKeyBytes_at m key (by omega)]
    rfl
  unfold Spec.Dsa.validatePrivateKeyBytes
  simp only [hv, decide_true, Bool.not_true, VG.Proof.Bignum.bytesAt_length, bne_self_eq_false,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte, hkey]
  by_cases hs : VG.Proof.Dsa.shapeValid (pOf m L key) (qOf m L key)
  · have e := VG.Proof.Dsa.privateChecks_spec (g := gOf m L key) (y := yOf m L key) (x := xOf m L key) hs
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, PrivOk, KeyOk, hs, true_and, ← e]
  · have hp : ¬ Spec.Dsa.parametersValid ⟨pOf m L key, qOf m L key, gOf m L key⟩ := fun P =>
      hs (VG.Proof.Dsa.parametersValid_shape P)
    simp only [hp, decide_false, Bool.false_and, PrivOk, KeyOk, hs, false_and]

/-- A key that passes private-key validation passes public-key validation's checks. -/
theorem PrivOk.keyOk {m : Mem} {L : Lay} {key : Addr} (h : PrivOk m L key) : KeyOk m L key := h.1

end VG.Proof.Dsa.PPC64LE
