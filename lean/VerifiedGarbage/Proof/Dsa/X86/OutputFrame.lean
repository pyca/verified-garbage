module

public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Impl.Dsa.X86.Bytes
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.TCB.X86.State
import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Retaining scratch values while writing external signature bytes -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86

def OutputFrame (base out : Addr) (prefixSize len : Nat) (m m' : Mem) : Prop :=
  ∀ a, prefixSize ≤ ofs base a → len ≤ ofs out a → m' a = m a

/-- External writes also account for the helper's argument and return stack. -/
def StackOutputFrame (sp : BitVec 32) (base out : Addr) (prefixSize len : Nat) (m m' : Mem) : Prop :=
  ∀ a, prefixSize ≤ ofs base a → len ≤ ofs out a → ¬ (callStack sp).Contains a 1 → m' a = m a

def StackOutside (sp : BitVec 32) (base : Addr) (len : Nat) (m m' : Mem) : Prop :=
  ∀ a, len ≤ ofs base a → ¬ (callStack sp).Contains a 1 → m' a = m a

theorem OutputFrame.scratch_byte {base out : Addr} {prefixSize len size : Nat} {m m' : Mem}
    (F : OutputFrame base out prefixSize len m m') (apart : Region.Disjoint ⟨base, size⟩ ⟨out, len⟩)
    {a : Addr} (lo : prefixSize ≤ ofs base a) (hi : ofs base a < size) : m' a = m a := by
  apply F a lo
  have H := apart a (by change ofs base a + 1 ≤ size; omega)
  change ¬ (ofs out a + 1 ≤ len) at H
  omega

theorem OutputFrame.scratch_word {base out : Addr} {prefixSize len size d : Nat} {m m' : Mem}
    (F : OutputFrame base out prefixSize len m m') (apart : Region.Disjoint ⟨base, size⟩ ⟨out, len⟩)
    (lo : prefixSize ≤ d) (hi : d + 4 ≤ size) (bound : size ≤ 2 ^ 64) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 := by
  apply Mem.readW_congr
  intro i hi'
  have H : i < 4 := hi'
  apply F.scratch_byte apart
  · rw [ofs_off base (by omega)]; omega
  · rw [ofs_off base (by omega)]; omega

theorem OutputFrame.scratch_bytes {base out : Addr} {prefixSize len size d count : Nat} {m m' : Mem}
    (F : OutputFrame base out prefixSize len m m') (apart : Region.Disjoint ⟨base, size⟩ ⟨out, len⟩)
    (lo : prefixSize ≤ d) (hi : d + count ≤ size) (bound : size ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' (off base d) count = Spec.Rsa.bytesAt m (off base d) count := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi'
  have H := List.mem_range.mp hi'
  apply F.scratch_byte apart
  · rw [ofs_off base (by omega)]; omega
  · rw [ofs_off base (by omega)]; omega

theorem OutputFrame.other_bytes {base out ptr : Addr} {prefixSize len count : Nat} {m m' : Mem}
    (F : OutputFrame base out prefixSize len m m')
    (workApart : Region.Disjoint ⟨ptr, count⟩ ⟨base, prefixSize⟩)
    (outApart : Region.Disjoint ⟨ptr, count⟩ ⟨out, len⟩)
    (bound : count ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' ptr count = Spec.Rsa.bytesAt m ptr count := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  have H := List.mem_range.mp hi
  have inside : (⟨ptr, count⟩ : Region).Contains (ptr + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base ptr (by omega) (by omega)
  have W := workApart _ inside
  have O := outApart _ inside
  change ¬ (ofs base (ptr + BitVec.ofNat 64 i) + 1 ≤ prefixSize) at W
  change ¬ (ofs out (ptr + BitVec.ofNat 64 i) + 1 ≤ len) at O
  exact F _ (by omega) (by omega)

theorem OutputFrame.join {base out : Addr} {prefixSize n k : Nat} {m m' m'' : Mem}
    (F : OutputFrame base out prefixSize n m m')
    (G : OutputFrame base (out + BitVec.ofNat 64 n) prefixSize k m' m'')
    (bound : n + k ≤ 2 ^ 64) : OutputFrame base out prefixSize (n + k) m m'' := by
  intro a ha hb
  have H := Offset.lt_iff a out bound
  change ofs (out + BitVec.ofNat 64 n) a < k ↔ n ≤ ofs out a ∧ ofs out a < n + k at H
  exact (G a ha (by omega)).trans (F a ha (by omega))

end VG.Proof.Dsa.X86
