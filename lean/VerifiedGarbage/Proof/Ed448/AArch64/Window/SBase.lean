import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Combine
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Table
import VerifiedGarbage.Proof.Ed448.AArch64.CombBase
import VerifiedGarbage.Proof.Ed448.AArch64.Window.CopyK

/-!
# Ed448 verification on AArch64: `[S]B`

Untrusted: everything here is checked by Lean. `sBase`, from the bits of `S` at
`BITS`, every slot's limbs below `Ib` and zero in slot 19: the comb of 57 tables by a call
of `vg_ed448_r56_comb_base` (`CombBase.call_ok`) and `16 A + C` (`sBase_ok`), as in
`vg_ed448_scalar_base`: `[S]B` in slots 0–2.
-/

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC BITS)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (Bits pt)
open VG.Proof.Ed448 (Rep baseAff)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem sBase_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hz : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0) {S : Nat} (hS : S < 256 ^ 57)
    (hbits : Bits 57 base S s.mem)
    (htb : VG.Proof.X448.AArch64.Base.TblAt s base (s.syms VG.Impl.X448.AArch64.Base.combSym)) :
    WP isa sBase s fun t =>
      Scr t base ∧ BEnv t.mem base ∧ (∀ w < 8, limbs t.mem base (slot (19 : Index).val) w = 0) ∧
      Rep (pt (EV t.mem base) 0 1 2) ((S : ℤ) • baseAff) ∧ Outside2 base 64 2816 ACC 1152 s.mem t.mem ∧
      t.gpr .x30 = s.gpr .x30 ∧ t.gpr .x20 = s.gpr .x20 ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold sBase
  have f0 : VG.Proof.X448.AArch64.Base.Frame s base s := ⟨hs, hb, hz, rfl, rfl, rfl, rfl, Outside2.refl _ _ _ _ _ _⟩
  refine WP.seq (WP.mono (CombBase.call_ok (Or.inr rfl) f0 ⟨hs, hb, hz, hbits, htb⟩) fun u ⟨fu, au, cu⟩ => ?_)
  refine WP.mono (Point56.combineCall_frame fu au cu) fun v ⟨fv, rv⟩ =>
    ⟨fv.scr, fv.env, fv.zero, by rw [← VG.Proof.X448.comb_total hS]; exact rv, fv.mem, fv.lr, fv.out, fv.rd, fv.wr⟩

end VG.Proof.Ed448.AArch64.Window
