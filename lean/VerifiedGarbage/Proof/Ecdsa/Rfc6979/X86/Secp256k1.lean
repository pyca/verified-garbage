module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Sat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Secp256k1Sha256
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Verified
public import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Lit
public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.X25519.X86.Column
meta import VerifiedGarbage.Proof.X25519.X86.Column
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find

/-!
# Deterministic ECDSA on x86 (32-bit): secp256k1

secp256k1 as the proof's curve (`secp256k1`): scalars of 4 64-bit words, the order
`n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_secp256k1_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at secp256k1's sizes, which is `Proof.Ecdsa.X86.Secp256k1.signX86`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem secp256k1_nBits : Spec.Ecdsa.nBits Spec.Secp256k1.curve = 256 := by
  show Spec.Secp256k1.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.Secp256k1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Secp256k1.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem secp256k1_core_pre {s : State} (h : (coreK Impl.Ecdsa.X86.secp256k1).pre s) :
    Proof.Ecdsa.X86.Secp256k1.signX86.pre s := by
  obtain ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss, _⟩ := h
  exact ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss⟩

/-- secp256k1, with the group law `hL`. -/
def secp256k1 (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Proof.Weierstrass.X86.Inv.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86.secp256k1
  inst := Spec.Ecdsa.Secp256k1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, secp256k1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.Secp256k1.curve = 0; rw [secp256k1_nBits]
  coreN := Spec.Ecdsa.Secp256k1.signApi.name
  coreC := Impl.Ecdsa.X86.signSecp256k1
  coreX := fun s h => Proof.Ecdsa.X86.Secp256k1.sign_x86 hL hI s (secp256k1_core_pre h)
  coreCT := by
    intro s t tr₁ tr₂ s' t' hs ht hp
    obtain ⟨he, a0, a1, a2, a3, a4, _⟩ := hp
    exact Proof.Ecdsa.X86.Secp256k1.sign_ct s t tr₁ tr₂ s' t' (secp256k1_core_pre hs) (secp256k1_core_pre ht)
      ⟨he, a0, a1, a2, a3, a4⟩
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)

/-- `vg_ecdsa_secp256k1_rfc6979_sign`, with the hash functions of the tier `t`,
meets the shared contract. -/
theorem secp256k1_any (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Proof.Weierstrass.X86.Inv.InvSounds) (t : Proof.Pbkdf2.Whole.X86.Tier) :
    Verified X86.target (cfgAny (secp256k1 hL hI) t.fns Spec.Ecdsa.Rfc6979.Secp256k1Sha256.inst).sign
      (Spec.Ecdsa.Rfc6979.Secp256k1Sha256.inst.signAnyContract (X86.abi.withConsts (secp256k1 hL hI).E.combConsts) 536) :=
  sign_verified _ _ rfl (by decide) (by decide) rfl t (sat_nil _ rfl (by decide))

/-- No instruction of `vg_ecdsa_secp256k1_rfc6979_sign` writes `esp` but the frames'. -/
theorem secp256k1_spSafe (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Proof.Weierstrass.X86.Inv.InvSounds) (t : Proof.Pbkdf2.Whole.X86.Tier) :
    (cfgAny (secp256k1 hL hI) t.fns Spec.Ecdsa.Rfc6979.Secp256k1Sha256.inst).sign.all (fun i => !isa.writesSp i) = true :=
  any_spSafe _ _ rfl (by decide) (by decide) t

end VG.Proof.Ecdsa.Rfc6979.X86
