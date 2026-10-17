module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Sat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Lit
public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.X25519.X86.Column
meta import VerifiedGarbage.Proof.X25519.X86.Column

/-!
# Deterministic ECDSA on x86 (32-bit): brainpoolP512r1

brainpoolP512r1 as the proof's curve (`brainpoolp512r1`): scalars of 8 64-bit words, the order
`n` of exactly 512 bits with `2^512 < 2 n`, and `vg_ecdsa_brainpoolp512r1_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at brainpoolP512r1's sizes, which is `Proof.Ecdsa.X86.BrainpoolP512r1.signX86`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem brainpoolp512r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP512r1.curve = 512 := by
  show Spec.BrainpoolP512r1.curve.n.log2 + 1 = 512
  have h₁ : 511 ≤ Spec.BrainpoolP512r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP512r1.curve.n.log2 < 512 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem core_pre_brainpoolp512r1 {s : State} (h : (coreK Impl.Ecdsa.X86.brainpoolp512r1).pre s) :
    Proof.Ecdsa.X86.BrainpoolP512r1.signX86.pre s := by
  obtain ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss, _⟩ := h
  exact ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss⟩

/-- brainpoolP512r1, with the group law `hL`. -/
def brainpoolp512r1 (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : RfcCurve where
  E := Impl.Ecdsa.X86.brainpoolp512r1
  inst := Spec.Ecdsa.BrainpoolP512r1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inr (.inr rfl)), .inl rfl, brainpoolp512r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86.BrainpoolP512r1.brainpoolp512r1_sh
  coreN := Spec.Ecdsa.BrainpoolP512r1.signApi.name
  coreC := Impl.Ecdsa.X86.signBrainpoolP512r1
  coreX := fun s h => Proof.Ecdsa.X86.BrainpoolP512r1.sign_x86 hL s (core_pre_brainpoolp512r1 h)
  coreCT := by
    intro s t tr₁ tr₂ s' t' hs ht hp
    obtain ⟨he, a0, a1, a2, a3, a4, _⟩ := hp
    exact Proof.Ecdsa.X86.BrainpoolP512r1.sign_ct s t tr₁ tr₂ s' t' (core_pre_brainpoolp512r1 hs) (core_pre_brainpoolp512r1 ht)
      ⟨he, a0, a1, a2, a3, a4⟩
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)

/-- `vg_ecdsa_brainpoolp512r1_rfc6979_sign`, with the hash functions of the tier `t`,
meets the shared contract. -/
theorem brainpoolp512r1_any (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (t : Proof.Pbkdf2.Whole.X86.Tier) :
    Verified X86.target (cfgAny (brainpoolp512r1 hL) t.fns Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst).sign
      (Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst.signAnyContract (X86.abi.withConsts (brainpoolp512r1 hL).E.combConsts) 536) :=
  sign_verified _ _ rfl (by decide) (by decide) rfl t (sat_nil _ rfl (by decide))

/-- No instruction of `vg_ecdsa_brainpoolp512r1_rfc6979_sign` writes `esp` but the frames'. -/
theorem brainpoolp512r1_spSafe (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (t : Proof.Pbkdf2.Whole.X86.Tier) :
    (cfgAny (brainpoolp512r1 hL) t.fns Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.inst).sign.all (fun i => !isa.writesSp i) = true :=
  any_spSafe _ _ rfl (by decide) (by decide) t

end VG.Proof.Ecdsa.Rfc6979.X86
