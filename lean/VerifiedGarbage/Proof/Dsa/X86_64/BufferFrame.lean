module

public import VerifiedGarbage.Proof.Dsa.X86_64.LocalCallFrame
import VerifiedGarbage.Proof.Dsa.Layout

/-! # Preserving operands and recovering result bytes between DSA calls -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem localCall_field {B : Addr} {o wx d k : Nat} {mem mem' : Mem}
    (hf : Frm B (localCallRanges o wx d k) mem mem') (ho : pWorkspace ≤ o) (hd : pWorkspace ≤ d)
    (f : Field) : word mem' B f.offset = word mem B f.offset := by
  have hb := VG.Proof.Dsa.field_bounds f
  apply hf.word_eq _ (Nat.le_trans hb.2 (by decide))
  intro r hr
  simp only [localCallRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · right; omega
  · left; omega
  · left; omega

theorem callFrame_source {s t : State} {B src out : Addr} {Z o wx k : Nat} {bs : List Byte} {rs : List Reg}
    (hf : CallFrame B o wx out k s.mem t.mem) (hk : Keep rs s t)
    (hZ : 176 ≤ Z) (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (hbound : Z ≤ 2 ^ 64)
    (hs : Src s B Z src bs)
    (hsep : ∀ i < bs.length, ∀ j < k, src + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j) : Src t B Z src bs := by
  have hslot : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  refine ⟨fun i hi => by rw [hk.2.1, hk.2.2]; exact hs.rd i hi, ?_, hs.out⟩
  intro i hi
  rw [hf _ (Or.inr (Nat.le_trans hZ (hs.out i hi))) ?_ (hsep i hi)]
  · exact hs.val i hi
  · intro r hr
    simp only [workRanges, List.mem_singleton] at hr
    subst r
    have hp := hs.out i hi
    rcases ofs_rebase B (src + BitVec.ofNat 64 i) (o := o) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only <;> right <;> omega

theorem source_bytesAt {s : State} {B p : Addr} {Z n : Nat} {bs : List Byte}
    (hb : Spec.Rsa.bytesAt s.mem p n = bs)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (ho : ∀ i < n, Z ≤ ofs B (p + BitVec.ofNat 64 i)) : Src s B Z p bs := by
  have hlen : bs.length = n := by rw [← hb]; simp [Spec.Rsa.bytesAt]
  refine ⟨fun i hi => hr i (by omega), ?_, fun i hi => ho i (by omega)⟩
  intro i hi
  subst bs
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]

/-- Read back a computed local scalar or element as an operand. -/
theorem output_operand {s : State} {B : Addr} {Z d k : Nat} {f : Field} {bs : List Byte}
    (hl : word s.mem B f.offset = BitVec.ofNat 64 k)
    (hb : Spec.Rsa.bytesAt s.mem (off B d) k = bs)
    (hr : ∀ i < k, InRegions (s.rd ++ s.wr) (off B d + BitVec.ofNat 64 i) 1)
    (ho : ∀ i < k, Z ≤ ofs B (off B d + BitVec.ofNat 64 i)) :
    OperandBytes s B Z ⟨.local d, f⟩ bs := by
  have hlen : bs.length = k := by rw [← hb]; simp [Spec.Rsa.bytesAt]
  exact ⟨by rw [hlen]; exact hl, source_bytesAt hb hr ho⟩

end VG.Proof.Dsa.X86_64
