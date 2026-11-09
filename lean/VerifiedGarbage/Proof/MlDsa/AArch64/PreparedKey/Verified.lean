module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Frame
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.FrameTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Lay
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.AArch64.Depth

/-! # Verified preparation of canonical ML-DSA key transforms -/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.PreparedKey
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Spec.Sha3 (bytesAt)

theorem public_sizes {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    p.pkLen < 2 ^ 32 ∧ p.pkLen + 1024 * p.k < 2 ^ 32 := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem secret_sizes {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    p.skLen < 2 ^ 32 ∧ p.skLen + 1024 * (p.ℓ + 2 * p.k) < 2 ^ 32 := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem public_correct {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
    (σ : State) (hpre : (preparePublicKeyContract p AArch64.abi 80).pre σ) :
    ∃ tr t, Exec isa (preparePublic p) σ tr t ∧ abiPreserved σ t ∧
      (preparePublicKeyContract p AArch64.abi 80).post σ t := by
  have sizes := public_sizes hp
  have hd : 16 * (Code.seq (copy (.x26, 0) (.x25, 0) p.pkLen)
      (seqR (publicPoly p) 0 p.k)).aarch64Depth + 64 < 2 ^ 64 := by
    rcases hp with rfl | rfl | rfl <;> decide +kernel
  have hw := prepareFrame_correct (B := PreparedPublicKey p) hd (fun s L =>
    WP.mono (public_body hp s L) fun t ⟨ht, hc⟩ =>
      ⟨ht.post, ht.x24, by rw [← ht.post.pa (p := (.x26, 0)) (by decide)]; exact ht.encoded,
        by rw [← ht.post.pa (p := (.x26, 0)) (by decide)]; exact hc⟩)
    (public_pre hpre) sizes.1 sizes.2
  obtain ⟨tr, t, he, habi, hout, hc⟩ := hw
  refine ⟨tr, t, he, habi, ?_⟩
  sig_post [preparePublicKeyContract, preparePublicKeySig, AArch64.abi, VG.AArch64.argRegs]
  exact ⟨hout, hc⟩

theorem secret_correct {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
    (σ : State) (hpre : (prepareSecretKeyContract p AArch64.abi 80).pre σ) :
    ∃ tr t, Exec isa (prepareSecret p) σ tr t ∧ abiPreserved σ t ∧
      (prepareSecretKeyContract p AArch64.abi 80).post σ t := by
  have sizes := secret_sizes hp
  have hd : 16 * (Code.seq (copy (.x26, 0) (.x25, 0) p.skLen)
      (seqR (secretPoly p) 0 (p.ℓ + 2 * p.k))).aarch64Depth + 64 < 2 ^ 64 := by
    rcases hp with rfl | rfl | rfl <;> decide +kernel
  have hw := prepareFrame_correct (B := PreparedSecretKey p) hd (fun s L =>
    WP.mono (secret_body hp s L) fun t ⟨ht, hc⟩ =>
      ⟨ht.post, ht.x24, by rw [← ht.post.pa (p := (.x26, 0)) (by decide)]; exact ht.encoded,
        by rw [← ht.post.pa (p := (.x26, 0)) (by decide)]; exact hc⟩)
    (secret_pre hpre) sizes.1 sizes.2
  obtain ⟨tr, t, he, habi, hout, hc⟩ := hw
  refine ⟨tr, t, he, habi, ?_⟩
  sig_post [prepareSecretKeyContract, prepareSecretKeySig, AArch64.abi, VG.AArch64.argRegs]
  exact ⟨hout, hc⟩

theorem public_ct {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    ConstantTime isa (preparePublicKeyContract p AArch64.abi 80).pre
      (preparePublicKeyContract p AArch64.abi 80).pub (preparePublic p) := by
  intro x y tx ty x' y' hx hy hpub ex ey
  have sizes := public_sizes hp
  have hct := prepareFrame_tr sizes.1 sizes.2 (public_body_tr hp)
  sig_pub [preparePublicKeyContract, preparePublicKeySig, AArch64.abi, VG.AArch64.argRegs] at hpub
  exact (hct _ _ _ _ _ _ ⟨public_pre hx, public_pre hy,
    hpub.2.1, hpub.2.2.1, hpub.2.2.2, hpub.1⟩ ex ey).1

theorem secret_ct {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    ConstantTime isa (prepareSecretKeyContract p AArch64.abi 80).pre
      (prepareSecretKeyContract p AArch64.abi 80).pub (prepareSecret p) := by
  intro x y tx ty x' y' hx hy hpub ex ey
  have sizes := secret_sizes hp
  have hct := prepareFrame_tr sizes.1 sizes.2 (secret_body_tr hp)
  sig_pub [prepareSecretKeyContract, prepareSecretKeySig, AArch64.abi, VG.AArch64.argRegs] at hpub
  exact (hct _ _ _ _ _ _ ⟨secret_pre hx, secret_pre hy,
    hpub.2.1, hpub.2.2.1, hpub.2.2.2, hpub.1⟩ ex ey).1

def prepSat (bytes count : Nat) : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x10000 | .x2 => 0x100000 | _ => 0
  sp := 0x1000000
  mem _ := 0
  rd := [⟨0x1000, bytes⟩]
  wr := [⟨0x10000, bytes + 1024 * count⟩, ⟨0x100000, 1024⟩]

theorem public_sat {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    ∃ s, (preparePublicKeyContract p AArch64.abi 80).pre s := by
  rcases hp with rfl | rfl | rfl
  · refine ⟨prepSat mlDsa44.pkLen mlDsa44.k, ?_⟩
    sig_sat_check [preparePublicKeyContract, preparePublicKeySig, AArch64.abi, VG.AArch64.argRegs]
  · refine ⟨prepSat mlDsa65.pkLen mlDsa65.k, ?_⟩
    sig_sat_check [preparePublicKeyContract, preparePublicKeySig, AArch64.abi, VG.AArch64.argRegs]
  · refine ⟨prepSat mlDsa87.pkLen mlDsa87.k, ?_⟩
    sig_sat_check [preparePublicKeyContract, preparePublicKeySig, AArch64.abi, VG.AArch64.argRegs]

theorem secret_sat {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    ∃ s, (prepareSecretKeyContract p AArch64.abi 80).pre s := by
  rcases hp with rfl | rfl | rfl
  · refine ⟨prepSat mlDsa44.skLen (mlDsa44.ℓ + 2 * mlDsa44.k), ?_⟩
    sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, AArch64.abi, VG.AArch64.argRegs]
  · refine ⟨prepSat mlDsa65.skLen (mlDsa65.ℓ + 2 * mlDsa65.k), ?_⟩
    sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, AArch64.abi, VG.AArch64.argRegs]
  · refine ⟨prepSat mlDsa87.skLen (mlDsa87.ℓ + 2 * mlDsa87.k), ?_⟩
    sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, AArch64.abi, VG.AArch64.argRegs]

theorem preparePublic_verified (p : Params) (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    Verified AArch64.target (preparePublic p) (preparePublicKeyContract p AArch64.abi 80) :=
  ⟨public_correct hp, public_ct hp, public_sat hp⟩

theorem prepareSecret_verified (p : Params) (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    Verified AArch64.target (prepareSecret p) (prepareSecretKeyContract p AArch64.abi 80) :=
  ⟨secret_correct hp, secret_ct hp, secret_sat hp⟩

end VG.Proof.MlDsa.AArch64.PreparedKey
