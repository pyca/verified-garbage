module

import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Init
public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Invariant
public import VerifiedGarbage.Impl.Ed448.X86_64.Wnaf.Joint
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Memory
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Table
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Recode
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Loop
import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLoop

/-! Sparse multiplication with full-width scalar semantics. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.Ed448 VG.Proof.X448.X86_64
open VG.Impl.Ed448.Wnaf (residual)
open VG.Impl.X448.X86_64 (BITS)
open VG.Proof.Ed448.X86_64.Window (table_ok tablePoint pointAt_outside)

def Frame (base : Addr) (m u : Mem) := Outside2 base 64 1584 SDIG 4288 m u

theorem Frame.wide {base : Addr} {m u : Mem} (h : Frame base m u) : Outside base 64 7296 m u :=
  h.outside (by decide) (by decide) (by decide) (by decide)

theorem RecInv.env {base : Addr} {dst k n : Nat} {s u : State} (h : RecInv base dst k s n u)
    (hd : 2048 ≤ dst) : E u.mem base = E s.mem base := by
  funext i
  apply E_outside h.mem i
  left
  have hi := slot_lt i
  simp only [VG.Impl.X448.X86_64.ACC] at hi
  omega

theorem RecInv.table {base : Addr} {dst k n : Nat} {s u : State} (h : RecInv base dst k s n u)
    (hd : dst + 461 ≤ Impl.Ed448.X86_64.Window.TAB) (i : Nat) (hi : i < 17) :
    tablePoint u.mem base i = tablePoint s.mem base i := by
  apply pointAt_outside h.mem
  · simp only [Impl.Ed448.X86_64.Window.tabOffset, Impl.Ed448.X86_64.Window.TAB]; omega
  · right; simp only [Impl.Ed448.X86_64.Window.tabOffset]; omega

theorem joint_ok {F : Impl.X448.X86_64.Field} (hf : FieldOk F) {P : Point64.Ops} (hP : Point64.PointOk P)
    {s : State} {base : Addr} {S K o : Nat} (hs : Scr s base) (ho : 2048 ≤ o) (hb : o + 460 ≤ SDIG)
    (bs : Window.Bits base BITS S s) (bk : Window.Bits base o K s)
    (hS : S < 2 ^ 456) (hK : K < 2 ^ 456) (hd : E s.mem base 11 = Spec.Ed448.d)
    (hz : E s.mem base 10 = 1) (hp : pt (E s.mem base) 0 1 2 = Spec.Ed448.identity) :
    WP isa (joint F P o) s fun u =>
      Scr u base ∧ (∀ r, r ∉ .rbx :: clob → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ Frame base s.mem u.mem ∧
      ∀ a, Rep (pt (E s.mem base) 6 7 10) a →
        Rep (pt (E u.mem base) 0 1 2) (S • baseAff + K • a) := by
  refine WP.seq (WP.mono (table_ok hP hs hd hz hp) fun a ⟨ka, da, ta⟩ => ?_)
  have bsA := bs.keepW (by decide) (by decide) ka
  have bkA := bk.keepW ho (by simp only [SDIG, Impl.Ed448.X86_64.Window.TAB] at *; omega) ka
  refine WP.seq (WP.mono (recode_ok (ka.scr hs) (by decide) (by decide) (by decide) bsA hS)
    fun b hB => ?_)
  have bkB : Window.Bits base o K b := by
    intro i hi
    rw [hB.mem _ (Or.inl (by rw [ofs_off' base (by simp only [SDIG] at hb; omega)]; omega))]
    exact bkA i hi
  refine WP.seq (WP.mono (recode_ok hB.scr (by omega) (by simp only [SDIG, KDIG] at *; omega)
    (by decide) bkB hK) fun c hC => ?_)
  have sb : Digits base SDIG S b := hB.digits
  have sc : Digits base SDIG S c := by
    intro i hi
    rw [hC.mem _ (Or.inl (by rw [ofs_off' base (by simp only [SDIG]; omega)]; simp only [SDIG, KDIG]; omega))]
    exact sb i hi
  have kc : Digits base KDIG K c := hC.digits
  refine WP.seq (WP.mono (initPoint_ok hC.scr) fun d hD => ?_)
  have inv : Inv base S K (pt (E s.mem base) 6 7 10) d 461 d := by
    refine ⟨hD.scr, hD.rbx, fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [hD.mem _ (Or.inr (by rw [ofs_off' base (by simp only [SDIG]; omega)]; simp only [SDIG]; omega))]
      exact sc i hi
    · intro i hi
      rw [hD.mem _ (Or.inr (by rw [ofs_off' base (by simp only [KDIG]; omega)]; simp only [KDIG]; omega))]
      exact kc i hi
    · rw [hD.d, hC.env (by decide), hB.env (by decide)]; exact da
    · intro i hi
      have ht : tablePoint d.mem base i = tablePoint c.mem base i := by
        apply pointAt_outside hD.mem <;>
          simp only [Impl.Ed448.X86_64.Window.tabOffset, Impl.Ed448.X86_64.Window.TAB] <;> omega
      rw [ht, hC.table (by decide) i hi, hB.table (by decide) i hi]
      exact ta i hi
    · intro aa _
      rw [hD.p, Proof.Ed448.Wnaf.residual_end hS, Proof.Ed448.Wnaf.residual_end hK]
      simpa only [Int.natCast_zero, zero_smul, zero_add] using identity_rep
  refine WP.mono (loop_ok hf hP 461 (by decide) (by decide) d inv) fun u hu => ?_
  refine ⟨hu.scr, ?_, hu.rd.trans (hD.rd.trans (hC.rd.trans (hB.rd.trans ka.rd))),
    hu.wr.trans (hD.wr.trans (hC.wr.trans (hB.wr.trans ka.wr))), ?_, ?_⟩
  · intro r hr
    exact (((hu.gpr r hr).trans (hD.gpr r hr)).trans (hC.gpr r hr)).trans
      ((hB.gpr r hr).trans (ka.gpr r (fun hh => hr (List.mem_cons_of_mem _ hh))))
  · intro p hx hy
    rw [hu.mem p hx, hD.mem p hx, hC.mem p (by rcases hy with hy | hy <;> simp only [SDIG, KDIG] at * <;> omega),
      hB.mem p (by rcases hy with hy | hy <;> simp only [SDIG] at * <;> omega)]
    exact ka.mem p hx (by rcases hy with hy | hy <;> simp only [SDIG, Impl.Ed448.X86_64.Window.TAB] at * <;> omega)
  · intro aa ha
    simpa only [residual, natCast_zsmul] using hu.rep aa ha

end VG.Proof.Ed448.X86_64.Wnaf
