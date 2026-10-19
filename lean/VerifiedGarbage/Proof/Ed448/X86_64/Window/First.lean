module
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Memory

import VerifiedGarbage.Proof.Ed448.X86_64.Window.SignedSelect
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Ops
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.X448.X86_64.AddSub

/-! Initialize from the first selected point, avoiding arithmetic on the identity. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window
open VG.Proof.Ed448 VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr E Keep FieldOk Index)
open VG.Impl.X448.X86_64 (BITS slot copyOut)
open VG.Proof.Ed448.SignedWindow (magnitude negative signedPoint signedEntry)

theorem takeBase_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (copyOut (slot 0) (slot 8) ++ copyOut (slot 1) (slot 9) ++ constSlot 2 1)) s fun u =>
      Keep base s u ∧ pt (E u.mem base) 0 1 2 = Proof.X448.basePt (E s.mem base 8, E s.mem base 9) ∧
      ∀ j : Index, 3 ≤ j.val → E u.mem base j = E s.mem base j := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (copySlot_ok hs 0 8) fun v ⟨kv, ev⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copySlot_ok (kv.scr hs) 1 9) fun w ⟨kw, ew⟩ => ?_
  refine WP.mono (constE_ok (kw.scr (kv.scr hs)) 2 1 c1) fun u ⟨ku, eu⟩ => ?_
  refine ⟨(kv.trans kw).trans ku, by rw [eu, ew, ev]; rfl, ?_⟩
  intro j hj
  have h0 : j ≠ 0 := by intro h; subst j; contradiction
  have h1 : j ≠ 1 := by intro h; subst j; contradiction
  have h2 : j ≠ 2 := by intro h; subst j; contradiction
  rw [eu, ew, ev, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h0]

theorem first_ok {F : Impl.X448.X86_64.Field} (hf : FieldOk F) {P : Point64.Ops} (hP : Point64.PointOk P)
    {s : State} {base : Addr} (hs : Scr s base) {o S K : Nat}
    (ho : 2048 ≤ o) (hbnd : o + 460 ≤ 8192)
    (hb : s.gpr .rbx = BitVec.ofNat 64 455) (bs : Bits base BITS S s) (bk : Bits base o K s)
    (hd : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (Window.first F P o) s fun u => Keep base s u ∧ E u.mem base 11 = Spec.Ed448.d ∧
      pt (E u.mem base) 0 1 2 = Spec.Ed448.pointAdd (Proof.X448.basePt (signedEntry S 455))
        (signedPoint (negative K 455) (tablePoint s.mem base (magnitude K 455))) := by
  rw [Window.first]
  refine WP.seq (WP.mono (selectSignedBase_ok hs (by decide) hb bs) fun s1 ⟨k1, p1, f1⟩ => ?_)
  refine WP.seq (WP.mono (takeBase_ok (k1.scr hs)) fun s2 ⟨k2, p2, f2⟩ => ?_)
  have k02 := k1.trans k2
  have q2 : pt (E s2.mem base) 0 1 2 = Proof.X448.basePt (signedEntry S 455) := by rw [p2, p1]
  have d2 : E s2.mem base 11 = Spec.Ed448.d := by
    rw [f2 11 (by decide), f1 11 (by decide) (by decide) (by decide) (by decide), hd]
  refine WP.seq (WP.mono (selectSignedKey_ok (k02.scr hs) ho hbnd (by decide)
    ((k02.gpr _ (by decide)).trans hb) (bk.keep ho hbnd k02)) fun s3 ⟨k3, p3, f3⟩ => ?_)
  have d3 : E s3.mem base 11 = Spec.Ed448.d := by
    rw [f3 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), d2]
  have q3 : pt (E s3.mem base) 0 1 2 = pt (E s2.mem base) 0 1 2 :=
    pt_congr (f3 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (f3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (f3 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  refine WP.seq (WP.mono (add_ok hf hP (k3.scr (k02.scr hs)) d3) fun s4 ⟨k4, e4⟩ => ?_)
  refine WP.mono (accept_ok (k4.scr (k3.scr (k02.scr hs)))) fun u ⟨ku, pu, fu⟩ => ?_
  refine ⟨((k02.trans k3).trans k4).trans ku, ?_, ?_⟩
  · rw [fu 11 (by decide), e4, addEnv_d, d3]
  · rw [pu, e4, addEnv_eval, d3, addWith_d, q3, q2, p3,
      tablePoint_keep k02 (magnitude K 455) (SignedWindow.magnitude_lt K 455)]

end VG.Proof.Ed448.X86_64.Window
