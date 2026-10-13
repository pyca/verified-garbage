module

public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Loop
public import VerifiedGarbage.Proof.X448.X86_64.Inv
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! End-to-end joint multiplication, including runtime table construction. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window
set_option exponentiation.threshold 1024

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window
open VG.Proof.Ed448 VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr E Keep FieldOk Outside off clob)
open VG.Impl.X448.X86_64 (BITS)

private theorem init_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block Window.init) s fun u =>
      Scr u base ∧ u.gpr .rbx = BitVec.ofNat 64 456 ∧
      (∀ r, r ∉ .rbx :: clob → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      Outside base 64 1584 s.mem u.mem ∧
      pt (E u.mem base) 0 1 2 = Spec.Ed448.identity ∧ E u.mem base 11 = E s.mem base 11 := by
  rw [Window.init, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (constE_ok hs 0 0 c0) fun s1 ⟨k1, e1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constE_ok (k1.scr hs) 1 1 c1) fun s2 ⟨k2, e2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constE_ok (k2.scr (k1.scr hs)) 2 1 c1) fun s3 ⟨k3, e3⟩ => ?_
  refine WP.mono (VG.Proof.X448.X86_64.setRbx_ok s3 456 (by decide))
    fun u ⟨bu, gu, mu, ru, wu⟩ => ?_
  have k := (k1.trans k2).trans k3
  refine ⟨⟨(gu _ (by decide)).trans (k.scr hs).rdi, wu ▸ (k.scr hs).wr, hs.nowrap⟩,
    bu, ?_, ru.trans k.rd, wu.trans k.wr, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, not_or] at hr
    exact (gu r hr.1).trans (k.gpr r hr.2)
  · rw [mu]; exact k.mem
  · rw [mu, e3, e2, e1]; rfl
  · rw [mu, e3, e2, e1]; rfl

theorem joint_ok {F : Impl.X448.X86_64.Field} (hf : FieldOk F)
    {P : Point64.Ops} (hP : Point64.PointOk P) {s : State} {base : Addr} {S K o : Nat}
    (hs : Scr s base) (ho : 2048 ≤ o) (hbnd : o + 456 ≤ TAB)
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
  refine WP.seq (WP.mono (init_ok (k1.scr hs)) fun s2 ⟨hs2, b2, g2, r2, w2, m2, p2, d2⟩ => ?_)
  have bits2 {o k : Nat} (ho : 2048 ≤ o) (hb : o + 456 ≤ TAB) (h : Bits base o k s) :
      Bits base o k s2 := by
    intro j hj
    rw [m2 _ (Or.inr (by rw [VG.Proof.X448.X86_64.ofs_off' base (by simp only [TAB] at hb; omega)]; omega))]
    exact (h.keepW ho hb k1) j hj
  have inv : Inv base S K (pt (E s.mem base) 6 7 10) s2 114 s2 := by
    refine ⟨hs2, b2, fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _, d2.trans d1, ?_, ?_⟩
    · intro i hi
      rw [show tablePoint s2.mem base i = tablePoint s1.mem base i from
        pointAt_outside m2 (by simp only [tabOffset, TAB]; omega) (by simp only [tabOffset, TAB]; omega)]
      exact t1 i hi
    · intro a _
      change Rep (pt (E s2.mem base) 0 1 2) ((S / 2 ^ 456) • baseAff + (K / 2 ^ 456) • a)
      rw [p2, Nat.div_eq_of_lt hS, Nat.div_eq_of_lt hK, zero_smul, zero_smul, zero_add]
      exact identity_rep
  refine WP.mono (loop_ok hf hP ho (by simp only [TAB] at hbnd; omega)
    (bits2 (by decide) (by decide) bs) (bits2 ho hbnd bk) 114 s2 (by decide) (by decide) inv)
    fun u hu => ?_
  refine ⟨hu.scr, ?_, hu.rd.trans (r2.trans k1.rd), hu.wr.trans (w2.trans k1.wr),
    (k1.mem.trans (m2.left _ _)).trans (hu.mem.left _ _), ?_⟩
  · intro r hr
    exact ((hu.gpr r hr).trans (g2 r hr)).trans (k1.gpr r (fun h => hr (List.mem_cons_of_mem _ h)))
  · intro a ha
    simpa only [Nat.mul_zero, Nat.pow_zero, Nat.div_one] using hu.rep a ha

end VG.Proof.Ed448.X86_64.Window
