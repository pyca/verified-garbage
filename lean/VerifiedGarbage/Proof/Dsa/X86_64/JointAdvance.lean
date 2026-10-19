module

public import VerifiedGarbage.Proof.Dsa.X86_64.JointBuildContext
public import VerifiedGarbage.Impl.Dsa.X86_64.Joint
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # Advancing the row or column of the joint power table -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure JointBuildValues (m : Mem) (P : Addr) (w n g y j : Nat) : Prop where
  gen : wv m P (slot w aR2) w = g * 2 ^ (64 * w) % n
  base : wv m P (slot w aXm) w = y * 2 ^ (64 * w) % n
  one : wv m P (slot w aOne) w = 2 ^ (64 * w) % n
  row : wv m P (slot w aX) w = g ^ (j / 4) * 2 ^ (64 * w) % n
  entry : wv m P (slot w aY) w = (g ^ (j / 4) * y ^ (j % 4)) * 2 ^ (64 * w) % n

theorem JointBuildValues.congr {m m' : Mem} {P : Addr} {w n g y j : Nat}
    (h : JointBuildValues m P w n g y j)
    (he : ∀ a < 8, wv m' P (slot w a) w = wv m P (slot w a) w) :
    JointBuildValues m' P w n g y j :=
  ⟨(he _ (by decide)).trans h.gen, (he _ (by decide)).trans h.base,
    (he _ (by decide)).trans h.one, (he _ (by decide)).trans h.row, (he _ (by decide)).trans h.entry⟩

/-- Complete the next table value without changing either base or any table entry. -/
theorem jointAdvance_ok (M : Mont) {t : State} {P : Addr} {w n g y j : Nat} {minv : BitVec 64}
    (hc : JointCtx t P w n minv) (hw : 2 ≤ w) (hw' : w < 2 ^ 30)
    (hn : 0 < n) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (h : JointBuildValues t.mem P w n g y j) :
    WP isa (Joint.advance M.mm j) t fun u =>
      JointCtx u P w n minv ∧ JointBuildValues u.mem P w n g y (j + 1) ∧
      Arrays P w [aAcc, aTmp, aX, aY] t.mem u.mem ∧ Keep mmRegs t u := by
  have hnow := hc.mod.good.scr.nowrap
  unfold Joint.advance
  split
  · rename_i hcol
    have hd : (j + 1) / 4 = j / 4 + 1 := by omega
    have hm : (j + 1) % 4 = 0 := by omega
    refine WP.seq (WP.mono (jointProduct_ok M hc hw hw' (by unfold MmUse; decide)
      (by rw [h.gen]; exact Nat.mod_lt _ hn)) fun v ⟨hv, hlt, hmul, hf, hk⟩ => ?_)
    have hval : wv v.mem P (slot w aX) w = g ^ (j / 4 + 1) * 2 ^ (64 * w) % n := by
      have ha : wv t.mem P (slot w aX) w % n = g ^ (j / 4) * 2 ^ (64 * w) % n := by rw [h.row, Nat.mod_mod]
      have hb : wv t.mem P (slot w aR2) w % n = g * 2 ^ (64 * w) % n := by rw [h.gen, Nat.mod_mod]
      have v := VG.Proof.Dsa.mont_product hR ha hb hmul
      rw [Nat.mod_eq_of_lt hlt] at v
      simpa only [Nat.pow_succ] using v
    refine WP.mono (jointCopy_ok hv hw hw' (by decide) (by decide) (by decide) (by decide))
      fun u ⟨hu, hcopy, hf', hk'⟩ => ?_
    have f : Arrays P w [aAcc, aTmp, aX, aY] t.mem u.mem :=
      (hf.mono (by decide)).trans (hf'.mono (by decide))
    refine ⟨hu, ⟨?_, ?_, ?_, ?_, ?_⟩, f, (hk.trans hk').mono (by decide)⟩
    · exact (f.wv_of_not_mem (by decide) (by decide) hnow).trans h.gen
    · exact (f.wv_of_not_mem (by decide) (by decide) hnow).trans h.base
    · exact (f.wv_of_not_mem (by decide) (by decide) hnow).trans h.one
    · rw [hf'.wv_of_not_mem (by decide) (by decide) hv.mod.good.scr.nowrap, hval, hd]
    · rw [hcopy, hval, hd, hm, Nat.pow_zero, Nat.mul_one]
  · rename_i hcol
    have hd : (j + 1) / 4 = j / 4 := by omega
    have hm : (j + 1) % 4 = j % 4 + 1 := by omega
    refine WP.mono (jointProduct_ok M hc hw hw' (by unfold MmUse; decide)
      (by rw [h.base]; exact Nat.mod_lt _ hn)) fun u ⟨hu, hlt, hmul, hf, hk⟩ => ?_
    have hval : wv u.mem P (slot w aY) w = (g ^ (j / 4) * y ^ (j % 4 + 1)) * 2 ^ (64 * w) % n := by
      have ha : wv t.mem P (slot w aY) w % n = (g ^ (j / 4) * y ^ (j % 4)) * 2 ^ (64 * w) % n := by
        rw [h.entry, Nat.mod_mod]
      have hb : wv t.mem P (slot w aXm) w % n = y * 2 ^ (64 * w) % n := by rw [h.base, Nat.mod_mod]
      have v := VG.Proof.Dsa.mont_product hR ha hb hmul
      rw [Nat.mod_eq_of_lt hlt] at v
      simpa only [Nat.pow_succ, Nat.mul_assoc] using v
    refine ⟨hu, ⟨?_, ?_, ?_, ?_, ?_⟩, hf.mono (by decide), hk⟩
    · exact (hf.wv_of_not_mem (by decide) (by decide) hnow).trans h.gen
    · exact (hf.wv_of_not_mem (by decide) (by decide) hnow).trans h.base
    · exact (hf.wv_of_not_mem (by decide) (by decide) hnow).trans h.one
    · rw [hf.wv_of_not_mem (by decide) (by decide) hnow, h.row, hd]
    · rw [hval, hd, hm]

end VG.Proof.Dsa.X86_64
