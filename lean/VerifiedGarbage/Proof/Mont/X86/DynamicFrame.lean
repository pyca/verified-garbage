module
public import VerifiedGarbage.Proof.Mont.X86.DynamicOps
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp


/-! # Memory frames for composing runtime-modulus operations -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.X86

theorem OpKeep.keeps {M : Mod} {base : Addr} {acc o : Nat} {s t : State}
    (h : VG.Proof.Mont.X86.OpKeep M base acc o s t) : Keeps clob s t :=
  ⟨h.gpr, h.rd, h.wr⟩

/-- An integer disjoint from all three temporary/output ranges is preserved. -/
theorem OpKeep.val {M : Mod} {base : Addr} {acc o d n : Nat} {s t : State}
    (h : VG.Proof.Mont.X86.OpKeep M base acc o s t)
    (ho : d + 8 * n ≤ o ∨ o + 8 * M.n ≤ d)
    (ht : d + 8 * n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ d)
    (ha : d + 8 * n ≤ acc ∨ acc + accLen M ≤ d)
    (hd : d + 8 * n ≤ 2 ^ 64) : wordsVal t.mem base d n = wordsVal s.mem base d n := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply h.mem.val32
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> omega
  · omega

theorem OpKeep.read32 {M : Mod} {base : Addr} {acc o d : Nat} {s t : State}
    (h : VG.Proof.Mont.X86.OpKeep M base acc o s t)
    (ho : d + 4 ≤ o ∨ o + 8 * M.n ≤ d)
    (ht : d + 4 ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ d)
    (ha : d + 4 ≤ acc ∨ acc + accLen M ≤ d)
    (hd : d + 4 ≤ 2 ^ 64) : t.mem.readW (off base d) 32 = s.mem.readW (off base d) 32 := by
  apply BitVec.eq_of_toNat_eq
  have hv : val32 t.mem base d 1 = val32 s.mem base d 1 := by
    apply h.mem.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> omega
    · exact hd
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using hv

/-- The modulus remains available for the next arithmetic operation. -/
theorem Modulus.keep {M : Mod} {base : Addr} {size m acc o a b : Nat} {s t : State}
    (hm : Modulus M size m s.mem base) (hs : Scr s base size)
    (hl : OpLay M size acc o a b)
    (ho : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o)
    (hk : VG.Proof.Mont.X86.OpKeep M base acc o s t) : Modulus M size m t.mem base := by
  refine ⟨hm.n0, hm.mo, hm.tmp, hm.sep, ?_⟩
  rw [OpKeep.val hk (by omega) hm.sep (by have := hl.acc_mo; omega)
    (by have := hs.nowrap; have := hm.mo; omega), hm.val]

end VG.Proof.Mont.X86.Dynamic
