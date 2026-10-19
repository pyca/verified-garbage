module

public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
public import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesXts.Alpha16
import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32

/-!
# One-pass XTS-AES on x86-64: blocks as words

The one-pass functions (`Impl/AesXts/X86_64Vaes.lean`) hold blocks and
tweaks as 128-bit words, in registers and in memory. Their bytes are `b16`
of the word (`bytesAt_b16`, `st_toList`); XOR of words is XOR of their bytes
(`b16_xor`); and the cipher of a register's state is the cipher of its bytes
(`ciphOf_b16`). `xtsWord`: the XTS of a block from its words, as the
functions compute it.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesXts (b16)
open VG.Proof.Aes.X86_64.AesNi (st)
open VG.Proof.AesCbc (ciphOf)

theorem bytesAt_b16 (m : Mem) (p : Addr) : bytesAt m p 16 = b16 (m.readW p 128) :=
  AesXts.bytesAt_readW (k := 16) m p

theorem b16_xor (a b : BitVec 128) : b16 (a ^^^ b) = Spec.Cbc.xor (b16 a) (b16 b) := by
  apply List.ext_getElem (by simp [b16, Spec.Cbc.xor])
  intro k h₁ h₂
  have hk : k < 16 := by simpa [b16] using h₁
  simp only [b16, Spec.Cbc.xor, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  ext j hj
  simp

theorem st_toList (v : BitVec 128) : (st v).toList = b16 v := by
  rw [Aes.X86_64.AesNi.st_toList]; rfl

/-- The function of states of a direction: the cipher or its inverse. -/
def stF (enc : Bool) (nr : Nat) (w : List Byte) : Spec.Aes.State → Spec.Aes.State :=
  if enc then Spec.Aes.cipher nr w else Spec.Aes.invCipher nr w

theorem ciphOf_b16 (enc : Bool) (nr : Nat) (w : List Byte) (v : BitVec 128) :
    ciphOf enc nr w (b16 v) = (stF enc nr w (st v)).toList := by
  have e : (Vector.ofFn fun i : Fin 16 => (b16 v).getD i.1 0) = st v := by
    apply Vector.ext
    intro i hi
    simp [b16, st, X86_64.byte]
  cases enc
  · simp only [ciphOf, stF, Bool.false_eq_true, ↓reduceIte, Spec.Cbc.aesInvWith, e]
  · simp only [ciphOf, stF, ↓reduceIte, Spec.Cbc.aesWith, e]

/-- A block `d` through XTS with the tweak `t`, as words, when `c` is the
word of the cipher of `d ⊕ t`'s state. -/
theorem xts_word (enc : Bool) (nr : Nat) (w : List Byte) (d t c : BitVec 128)
    (hc : st c = stF enc nr w (st (d ^^^ t))) :
    b16 (c ^^^ t) = Spec.Xts.block (ciphOf enc nr w) (b16 t) (b16 d) := by
  rw [Spec.Xts.block, b16_xor, ← st_toList c, hc, ← ciphOf_b16, b16_xor]

end VG.Proof.AesXts.X86_64.Vaes
