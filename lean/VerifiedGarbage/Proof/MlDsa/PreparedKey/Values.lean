module

public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.Sign.Setup
public import VerifiedGarbage.Proof.MlDsa.Verify.Spec
import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlKem.Mem

/-! # The prepared-key transforms are the existing sign/verify transforms

This bridge keeps the trusted cache format separate from implementation layout
facts. No validity assumption on the encoded key is added.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PreparedKey
open VG VG.Spec.MlDsa

theorem secretPolys_eq (p : Params) (sk : List Byte) :
    preparedSecretPolys p sk =
      (List.range p.ℓ).map (Sign.s1F p sk) ++
      (List.range p.k).map (Sign.s2F p sk) ++
      (List.range p.k).map (Sign.t0F p sk) := by
  rw [← Sign.skS1_eq, ← Sign.skS2_eq, ← Sign.skT0_eq]
  rcases e : skDecode p sk with ⟨rho, key, tr, s1, s2, t0⟩
  simp only [preparedSecretPolys, e, List.map_append]

theorem secretPolys_length (p : Params) (sk : List Byte) :
    (preparedSecretPolys p sk).length = p.ℓ + 2 * p.k := by
  rw [secretPolys_eq]
  simp only [List.length_append, List.length_map, List.length_range]
  omega

theorem secret_s1 (p : Params) (sk : List Byte) {i : Nat} (hi : i < p.ℓ) :
    (preparedSecretPolys p sk)[i]! = Sign.s1F p sk i := by
  rw [secretPolys_eq]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append, hi]

theorem secret_s2 (p : Params) (sk : List Byte) {i : Nat} (hi : i < p.k) :
    (preparedSecretPolys p sk)[p.ℓ + i]! = Sign.s2F p sk i := by
  rw [secretPolys_eq]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append, hi,
    show ¬ p.ℓ + i < p.ℓ by omega]

theorem secret_t0 (p : Params) (sk : List Byte) {i : Nat} (hi : i < p.k) :
    (preparedSecretPolys p sk)[p.ℓ + p.k + i]! = Sign.t0F p sk i := by
  rw [secretPolys_eq]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append,
    List.length_append, List.length_map, List.length_range]
  rw [ite_eq_right (by omega)]
  rw [show p.ℓ + p.k + i - (p.ℓ + p.k) = i by omega]
  simp [hi]

theorem publicPolys_eq (p : Params) (pk : List Byte) :
    preparedPublicPolys p pk = (List.range p.k).map (Verify.t1Hat pk) := by
  simp only [preparedPublicPolys, pkDecode, List.map_map]
  apply List.map_congr_left
  intro i _
  dsimp only [Function.comp_def, Verify.t1Hat, Verify.vT1]
  rw [show 32 * (bitlen (q - 1) - d) = 320 by decide]

theorem public_poly (p : Params) (pk : List Byte) {i : Nat} (hi : i < p.k) :
    (preparedPublicPolys p pk)[i]! = Verify.t1Hat pk i := by
  rw [publicPolys_eq]
  simp [hi]

/-- A byte-preserving copy also preserves canonical polynomial representation,
including when the source and destination have different base addresses. -/
theorem polyIs_of_copy {m m' : Mem} {src dst : Addr} {f : Poly}
    (hc : VG.Spec.Sha3.bytesAt m' dst 1024 = VG.Spec.Sha3.bytesAt m src 1024)
    (hf : PolyIs m src f) : PolyIs m' dst f := by
  apply Arith.polyIs_of_toNat
  intro i hi
  have hr : m'.read (dst + BitVec.ofNat 64 (4 * i)) 4 =
      m.read (src + BitVec.ofNat 64 (4 * i)) 4 := by
    apply Mem.read_eq_of_bytes
    intro j hj
    rw [Mem.extractLsb'_read _ _ hj]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      BitVec.add_assoc, ← BitVec.ofNat_add]
    have hij : 4 * i + j < 1024 := by change i < 256 at hi; omega
    have he := congrArg (fun xs : List Byte => xs.getD (4 * i + j) 0) hc
    rw [MlKem.bytesAt_getD _ _ hij, MlKem.bytesAt_getD _ _ hij] at he
    exact he
  have he : coeffAt m' dst i = coeffAt m src i := by
    change (m'.read (dst + BitVec.ofNat 64 (4 * i)) 4).setWidth 32 =
      (m.read (src + BitVec.ofNat 64 (4 * i)) 4).setWidth 32
    rw [hr]
  rw [he]
  exact Arith.polyIs_toNat hf hi

end VG.Proof.MlDsa.PreparedKey
