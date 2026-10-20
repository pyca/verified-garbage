module
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH key generation on x86-64: byte outputs after masking -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- Read back a source buffer exactly. -/
theorem bytes_src {s : State} {B op : Addr} {Z : Nat} {bs : List Byte} (h : Src s B Z op bs) :
    Spec.Rsa.bytesAt s.mem op bs.length = bs := by
  apply List.ext_getElem (by rw [bytesAt_length])
  intro i _ hi
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  exact h.val i hi

/-- A masked buffer is the original octets or an equally sized zero string. -/
theorem bytes_masked {s t : State} {B op : Addr} {Z k : Nat} {bs : List Byte} {c : Bool}
    (h : Src s B Z op bs) (hl : bs.length = k)
    (hm : ∀ i < k, t.mem (off op i) = if c then s.mem (off op i) else 0) :
    Spec.Rsa.bytesAt t.mem op k = if c then bs else List.replicate k 0 := by
  cases c
  · apply List.ext_getElem (by simp only [Bool.false_eq_true, ↓reduceIte, bytesAt_length, List.length_replicate])
    intro i hi _
    simp only [Bool.false_eq_true, ↓reduceIte, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range,
      List.getElem_replicate]
    exact hm i (by rwa [bytesAt_length] at hi)
  · simp only [↓reduceIte]
    apply List.ext_getElem (by rw [bytesAt_length, hl])
    intro i _ hi
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact (hm i (by rwa [← hl])).trans (h.val i hi)

end VG.Proof.Ffdh.X86_64.GenerateKey
