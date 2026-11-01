module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Layout
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.SecretValues
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
import VerifiedGarbage.Proof.MlKem.Mem

/-! # Preparing a canonical secret-key polynomial -/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.PreparedKey
open VG.Spec.Sha3 (bytesAt)

theorem secretPoly_ok {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
    {s : State} (L : Lay 16 (input p.skLen) (output p.skLen (p.ℓ + 2 * p.k)) s)
    {key : List Byte} (hkey : bytesAt s.mem (pa s (.x25, 0)) p.skLen = key)
    {i : Nat} (hi : i < p.ℓ + 2 * p.k) :
    WP isa (secretPoly p i) s fun t =>
      PPostB 16 s t [((.x26, p.skLen + 1024 * i), 1024), ((.x28, 0), 1024)] ∧
      t.gpr .x24 = s.gpr .x24 ∧
      PolyIs t.mem (pa s (.x26, p.skLen + 1024 * i)) (preparedSecretPolys p key)[i]! := by
  obtain ⟨src, len, a, b, he⟩ : ∃ src len a b, secretPiece p i = (src, len, a, b) := by
    rcases secretPiece p i with ⟨src, len, a, b⟩
    exact ⟨src, len, a, b, rfl⟩
  have hchecks := secret_checks hp hi
  rw [he] at hchecks
  obtain ⟨hc, hi', hb⟩ := hchecks
  unfold secretPoly
  rw [he]
  refine WP.mono (unpackTransform_ok (by decide) KeyGen.prims_ok.bitUnpack
    KeyGen.prims_ok.ntt L hc hi' hb) fun t ⟨ht, h24, hpoly⟩ => ⟨ht, h24, ?_⟩
  have hbound : src + len ≤ p.skLen := by
    have hr := (rw_parts hc).2.1
    rwa [in25, decide_eq_true_eq] at hr
  have hslice : bytesAt s.mem (pa s (.x25, src)) len = (key.drop src).take len := by
    rw [← hkey, MlKem.bytesAt_slice _ _ hbound]
    simp only [pa, BitVec.add_zero]
  have hv := secret_value p key hi
  rw [he] at hv
  rwa [hslice, hv] at hpoly

end VG.Proof.MlDsa.AArch64.PreparedKey
