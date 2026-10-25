module
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Memory

import VerifiedGarbage.Proof.Ed448.X86_64.Window.Loop
import VerifiedGarbage.Proof.Ed448.X86_64.Window.First
import VerifiedGarbage.Proof.X448.X86_64.Inv
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Table
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

/-! End-to-end joint multiplication, including runtime table construction. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window
set_option exponentiation.threshold 1024

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window
open VG.Proof.Ed448 VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr E Keep FieldOk Outside off clob)
open VG.Impl.X448.X86_64 (BITS)

private theorem first_rep {A : Spec.Ed448.Point} {a : EdwardsLaw.EPoint dZ} (hA : Rep A a)
    {S K : Nat} (hS : S < 2 ^ 456) (hK : K < 2 ^ 456) :
    Rep (Spec.Ed448.pointAdd (Proof.X448.basePt (SignedWindow.signedEntry S 455))
      (SignedWindow.signedPoint (SignedWindow.negative K 455)
        (Proof.Ed448.Window.multiples A (SignedWindow.magnitude K 455))))
      ((SignedWindow.high S 91 : Int) • baseAff + (SignedWindow.high K 91 : Int) • a) := by
  rw [SignedWindow.high_step S 91, SignedWindow.high_step K 91,
    SignedWindow.high_end hS, SignedWindow.high_end hK, Int.natCast_zero, mul_zero, zero_add]
  simp only [zero_add]
  exact pointAdd_rep (SignedWindow.signedEntry_rep S 455)
    (SignedWindow.signedPoint_rep
      (Proof.Ed448.Window.multiples_rep hA (SignedWindow.magnitude K 455)) (SignedWindow.negative K 455))

theorem joint_ok {F : Impl.X448.X86_64.Field} (hf : FieldOk F)
    {P : Point64.Ops} (hP : Point64.PointOk P) {s : State} {base : Addr} {S K o : Nat}
    (hs : Scr s base) (ho : 2048 ≤ o) (hbnd : o + 460 ≤ TAB)
    (bs : Bits base BITS S s) (bk : Bits base o K s)
    (hS : S < 2 ^ 456) (hK : K < 2 ^ 456)
    (hd : E s.mem base 11 = Spec.Ed448.d) (hz : E s.mem base 10 = 1)
    (hp : pt (E s.mem base) 0 1 2 = Spec.Ed448.identity) :
    WP isa (joint F P o) s fun u =>
      Scr u base ∧ (∀ r, r ∉ .rbx :: clob → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ Frame base s.mem u.mem ∧
      ∀ a, Rep (pt (E s.mem base) 6 7 10) a →
        Rep (pt (E u.mem base) 0 1 2) (S • baseAff + K • a) := by
  rw [joint]
  refine WP.seq (WP.mono (table_ok hP hs hd hz hp) fun s1 ⟨k1, d1, t1⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X448.X86_64.setRbx_ok s1 455 (by decide))
    fun s2 ⟨b2, g2, m2, r2, w2⟩ => ?_)
  have hs2 : Scr s2 base := ⟨(g2 _ (by decide)).trans (k1.scr hs).rdi, w2 ▸ (k1.scr hs).wr, hs.nowrap⟩
  have bits2 {o k : Nat} (ho : 2048 ≤ o) (hb : o + 460 ≤ TAB) (h : Bits base o k s) :
      Bits base o k s2 := by
    rw [Bits, m2]
    exact h.keepW ho hb k1
  have bs2 := bits2 (by decide) (by decide) bs
  have bk2 := bits2 ho hbnd bk
  have d2 : E s2.mem base 11 = Spec.Ed448.d := by rw [m2]; exact d1
  have hbnd' : o + 460 ≤ 8192 := by simp only [TAB] at hbnd; omega
  refine WP.seq (WP.mono (first_ok hf hP hs2 ho hbnd' b2 bs2 bk2 d2) fun s3 ⟨k3, d3, p3⟩ => ?_)
  have inv : Inv base S K (pt (E s.mem base) 6 7 10) s3 91 s3 := by
    refine ⟨k3.scr hs2, (k3.gpr _ (by decide)).trans b2, fun _ _ => rfl, rfl, rfl,
      Outside.refl _ _ _ _, d3, ?_, ?_⟩
    · intro i hi
      rw [tablePoint_keep k3 i hi, m2]; exact t1 i hi
    · intro a ha
      rw [p3, m2, t1 _ (SignedWindow.magnitude_lt K 455)]
      exact first_rep ha hS hK
  refine WP.mono (loop_ok hf hP ho hbnd'
    (bs2.keep (by decide) (by decide) k3) (bk2.keep ho hbnd' k3) 91 s3 (by decide) (by decide) inv)
    fun u hu => ?_
  have m3 : Outside base 64 1584 s1.mem s3.mem := by rw [← m2]; exact k3.mem
  refine ⟨hu.scr, ?_, hu.rd.trans (k3.rd.trans (r2.trans k1.rd)),
    hu.wr.trans (k3.wr.trans (w2.trans k1.wr)),
    (k1.mem.trans (m3.left _ _)).trans (hu.mem.left _ _), ?_⟩
  · intro r hr
    have hrc : r ∉ clob := fun h => hr (List.mem_cons_of_mem _ h)
    have hrb : r ≠ .rbx := fun h => hr (by simp [h])
    exact (((hu.gpr r hr).trans (k3.gpr r hrc)).trans (g2 r hrb)).trans (k1.gpr r hrc)
  · intro a ha
    simpa only [SignedWindow.high_zero, natCast_zsmul] using hu.rep a ha

end VG.Proof.Ed448.X86_64.Window
