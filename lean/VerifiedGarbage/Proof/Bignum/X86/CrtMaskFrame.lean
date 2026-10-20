module
public import VerifiedGarbage.Impl.Bignum.X86.CrtLayout
public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.Bignum.X86.CrtLayout
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Result masking preserves the call header and stays within scratch -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.Impl.Bignum.X86.Crt VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic VG.Proof.Mont

theorem mask_saved {n bytes : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base [(slot n 5, 8 * n), (slot n resultSlot, 8 * n)] m m') (hz : size n ≤ bytes) :
    Outside base 64 (bytes - 64) m m' := by
  have b5 := slot_bound (n := n) (i := 5) (by decide)
  have b7 := slot_bound (n := n) (i := resultSlot) (by decide)
  have d5 := slot_header n 5
  have d7 := slot_header n resultSlot
  simp only [stride] at b5 b7
  intro a ha
  apply O a
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only <;> omega

theorem mask_header {n d : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base [(slot n 5, 8 * n), (slot n resultSlot, 8 * n)] m m') (hd : d + 4 ≤ 64) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 := by
  have d5 := slot_header n 5
  have d7 := slot_header n resultSlot
  have V : val32 m' base d 1 = val32 m base d 1 := by
    apply O.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
    · omega
  apply BitVec.eq_of_toNat_eq
  simpa only [val32, w32, Nat.mul_zero, Nat.add_zero] using V

end VG.Proof.Bignum.X86.Crt
