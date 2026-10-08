import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Spec.Gcm.OutOfPlace

/-!
# GCM: one-shot encryption out of place, from a list of slices

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather`
runs the streaming functions: it starts a message, absorbs the additional
data `a` and pads it with zeros to a whole block, encrypts the slices one
after the other from where they are to the output, and writes the tag.

* `streamRepr_padded`: once there is some text, the state of a message with
  the additional data padded with zeros represents the message with the
  additional data itself, as GHASH pads it so (`ghashInput_padded`).
* `gathered_succ`: the slices listed, one more at a time.
* `encryptWith_eq`: GCM-AE is the ciphertext and the full tag.
-/

namespace VG.Proof.Gcm

open VG VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)

/-- The additional data padded with zeros to a whole block. -/
abbrev padA (a : List Byte) : List Byte := a ++ zeros (padLen a.length)

theorem length_padA_mod (a : List Byte) : (padA a).length % 16 = 0 := by
  simp only [padA, List.length_append, length_zeros]; exact length_pad_mod _

theorem ghashInput_padded (a : List Byte) {c : List Byte} (hc : c ≠ []) :
    ghashInput (padA a) c = ghashInput a c := by
  rw [ghashInput_of_ne hc, ghashInput_of_ne hc, padLen_of_mod (length_padA_mod a)]
  simp [padA, zeros]

/-- A state of the message with the additional data padded, once it has some
text, represents the message with the additional data itself. -/
theorem streamRepr_padded {m : Mem} {p : Addr} {ciph : Block → Block} {h : Block} {iv a c : List Byte}
    (hc : c ≠ []) (hr : StreamRepr m p ciph h iv (padA a) c) : StreamRepr m p ciph h iv a c := by
  simp only [StreamRepr] at hr ⊢
  rw [ghashInput_padded a hc] at hr
  exact hr

/-- The slices `n + 1` descriptors list: those of the first `n`, then the
last. -/
theorem listed_succ (pb : Nat) (m : Mem) (e : Elem) (p : Addr) (n : Nat) :
    Sig.listed pb m e p (n + 1) = Sig.listed pb m e p n ++
      [⟨(m.readW (p + BitVec.ofNat 64 (n * (2 * (pb / 8)))) pb).setWidth 64,
        (m.readW (p + BitVec.ofNat 64 (n * (2 * (pb / 8))) + BitVec.ofNat 64 (pb / 8)) pb).toNat * e.size⟩] := by
  simp [Sig.listed, List.range_succ]

theorem gathered_succ (pb : Nat) (m : Mem) (p : Addr) (n : Nat) :
    gathered pb m p (n + 1) = gathered pb m p n ++
      bytesAt m ((m.readW (p + BitVec.ofNat 64 (n * (2 * (pb / 8)))) pb).setWidth 64)
        (m.readW (p + BitVec.ofNat 64 (n * (2 * (pb / 8))) + BitVec.ofNat 64 (pb / 8)) pb).toNat := by
  simp [gathered, listed_succ, Elem.size]

theorem gatheredLen_succ (pb : Nat) (m : Mem) (p : Addr) (n : Nat) :
    gatheredLen pb m p (n + 1) = gatheredLen pb m p n +
      (m.readW (p + BitVec.ofNat 64 (n * (2 * (pb / 8))) + BitVec.ofNat 64 (pb / 8)) pb).toNat := by
  simp [gatheredLen, listed_succ, Elem.size]

theorem length_gathered (pb : Nat) (m : Mem) (p : Addr) (n : Nat) :
    (gathered pb m p n).length = gatheredLen pb m p n := by
  induction n with
  | zero => simp [gathered, gatheredLen, Sig.listed]
  | succ n ih => rw [gathered_succ, gatheredLen_succ, List.length_append, ih, Cmac.bytesAt_length]

theorem length_fullTag (ciph : Block → Block) (h : Block) (iv a c : List Byte) :
    (fullTag ciph h iv a c).length = 16 := by
  simp [fullTag, length_gctr, toBytes]

/-- GCM-AE with a 16-byte tag: the ciphertext and the full tag. -/
theorem encryptWith_eq (ciph : Block → Block) (h : Block) (iv p a : List Byte) :
    encryptWith ciph h 16 iv p a =
      (gctr ciph (inc32 (j0 h iv)) p, fullTag ciph h iv a (gctr ciph (inc32 (j0 h iv)) p)) := by
  simp only [encryptWith, Prod.mk.injEq, true_and]
  exact List.take_of_length_le (by rw [length_fullTag])

end VG.Proof.Gcm
