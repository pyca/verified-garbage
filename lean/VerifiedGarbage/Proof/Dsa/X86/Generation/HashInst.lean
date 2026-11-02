module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Hash
public import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Dsa

/-! # SHA-1 and SHA-256, with any backend, hash a seed -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

theorem ivBytes_getElem? (iv : List (BitVec 32)) {j i : Nat} (hj : j < iv.length) (hi : i < 4) :
    (ivBytes iv)[4 * j + i]? = some (iv[j].extractLsb' (8 * i) 8) := by
  induction iv generalizing j with
  | nil => simp at hj
  | cons w ws ih =>
    have chunk : ((List.range 4).map fun k => w.extractLsb' (8 * k) 8).length = 4 := by simp
    simp only [ivBytes, List.flatMap_cons] at ih ⊢
    rcases j with _ | j
    · rw [List.getElem?_append_left (by rw [chunk]; omega)]
      simp [hi]
    · rw [List.getElem?_append_right (by rw [chunk]; omega), chunk,
        show 4 * (j + 1) + i - 4 = 4 * j + i by omega]
      exact ih (by simp at hj; omega)

/-- The word `j` of an initial value whose bytes memory holds. -/
theorem iv_word {m : Mem} {p : Addr} {iv : List (BitVec 32)}
    (h : Spec.Sha256.bytesAt m p (4 * iv.length) = ivBytes iv) {j : Nat} (hj : j < iv.length) :
    m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = iv[j] := by
  show m.read _ 4 = _
  apply Mem.read_eq_of_bytes
  intro i hi
  have e := congrArg (·[4 * j + i]?) h
  simp only [Spec.Sha256.bytesAt, List.getElem?_map, List.getElem?_range (show 4 * j + i < 4 * iv.length by omega),
    Option.map_some, ivBytes_getElem? iv hj hi, Option.some.injEq] at e
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact e

def sha1_hashOk (v : Proof.Sha1.X86.Variants.Backend) :
    HashOk (Proof.Pbkdf2.Md.X86.sha1M v.stream v.cmpN v.cmpC) Spec.Sha1.H0.toList where
  ok := Proof.Pbkdf2.Md.X86.sha1Ok v.stream v.cmpN v.comp
  ivLen := rfl
  ivVal m p h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Pbkdf2.Md.X86.sha1Ok, Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact (iv_word (iv := Spec.Sha1.H0.toList) h (by simpa using hj)).trans (by simp)
  lenB := by
    show Proof.Sha1.md.lenBytes 20 = (List.range 8).map fun i => BitVec.ofNat 8 ((8 * 20) >>> (8 * (7 - i)))
    decide
  B := rfl
  L := rfl
  DN := rfl

def sha256_hashOk (v : Proof.Sha256.X86.Variants.Backend) :
    HashOk (Proof.Pbkdf2.Md.X86.sha256M v.stream v.cmpN v.cmpC) Spec.Sha256.H0.toList where
  ok := Proof.Pbkdf2.Md.X86.sha256Ok v.stream v.cmpN v.comp
  ivLen := rfl
  ivVal m p h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Pbkdf2.Md.X86.sha256Ok, Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact (iv_word (iv := Spec.Sha256.H0.toList) h (by simpa using hj)).trans (by simp)
  lenB := by
    show Proof.Sha256.md.lenBytes 32 = (List.range 8).map fun i => BitVec.ofNat 8 ((8 * 32) >>> (8 * (7 - i)))
    decide
  B := rfl
  L := rfl
  DN := rfl

example (v : Proof.Sha1.X86.Variants.Backend) (m : List Byte) :
    (sha1_hashOk v).ok.hH.SH.H.hash m = Spec.Dsa.seedHash 160 m := rfl

example (v : Proof.Sha256.X86.Variants.Backend) (m : List Byte) :
    (sha256_hashOk v).ok.hH.SH.H.hash m = Spec.Dsa.seedHash 256 m := rfl

end VG.Proof.Dsa.X86.Generation
