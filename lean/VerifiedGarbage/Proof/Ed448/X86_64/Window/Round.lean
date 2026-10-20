module
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Memory
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Ops

import VerifiedGarbage.Proof.Ed448.X86_64.Window.SignedSelect

import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86_64.BaseStep
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.X448.X86_64.AddSub
import VerifiedGarbage.Proof.MlKem.Arith

/-! One joint window: five doublings followed by two selected additions. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window
open VG.Proof.Ed448 VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr E Keep FieldOk Outside)
open VG.Impl.X448.X86_64 (BITS)
open VG.Proof.Ed448.SignedWindow (magnitude negative signedPoint signedEntry)

def roundPt (p q : Spec.Ed448.Point) (S t : Nat) :=
  Spec.Ed448.pointAdd (Spec.Ed448.pointAdd (dbl5Pt p)
    (Proof.X448.basePt (signedEntry S t))) q

theorem round_ok {F : Impl.X448.X86_64.Field} (hf : FieldOk F) {P : Point64.Ops} (hP : Point64.PointOk P)
    {s : State} {base : Addr} (hs : Scr s base) {o S K t : Nat}
    (ho : 2048 ≤ o) (hbnd : o + 460 ≤ 8192) (ht : t + 5 ≤ 460)
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base BITS S s) (bk : Bits base o K s)
    (hd : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (Window.round F P o) s fun u => Keep base s u ∧ u.zf = some (decide (t = 0)) ∧
      E u.mem base 11 = Spec.Ed448.d ∧ pt (E u.mem base) 0 1 2 =
        roundPt (pt (E s.mem base) 0 1 2) (signedPoint (negative K t) (tablePoint s.mem base (magnitude K t))) S t := by
  rw [Window.round]
  refine WP.seq (WP.mono (dbl5_ok hP hs) fun s1 ⟨k1, p1, f1⟩ => ?_)
  refine WP.seq (WP.mono (selectSignedBase_ok (k1.scr hs) ht (by rw [k1.gpr _ (by decide), hb])
    (bs.keep (by decide) (by decide) k1)) fun s2 ⟨k2, p2, f2⟩ => ?_)
  have d2 : E s2.mem base 11 = Spec.Ed448.d := by
    rw [f2 11 (by decide) (by decide) (by decide) (by decide), f1 11 (by decide) (by decide), hd]
  have q2 : pt (E s2.mem base) 0 1 2 = dbl5Pt (pt (E s.mem base) 0 1 2) := by
    rw [pt_congr (f2 0 (by decide) (by decide) (by decide) (by decide))
      (f2 1 (by decide) (by decide) (by decide) (by decide))
      (f2 2 (by decide) (by decide) (by decide) (by decide)), p1]
  refine WP.seq (WP.mono (hP.add (k2.scr (k1.scr hs)) d2) fun s3 ⟨k3, e3⟩ => ?_)
  refine WP.seq (WP.mono (accept_ok (k3.scr (k2.scr (k1.scr hs)))) fun s4 ⟨k4, p4, f4⟩ => ?_)
  have k04 := ((k1.trans k2).trans k3).trans k4
  have q4 : pt (E s4.mem base) 0 1 2 = Spec.Ed448.pointAdd (dbl5Pt (pt (E s.mem base) 0 1 2))
      (Proof.X448.basePt (signedEntry S t)) := by
    have hx := congrArg Prod.fst p2
    have hy := congrArg Prod.snd p2
    dsimp only at hx hy
    rw [p4, e3, Point64.addAffineOps_eval, d2, addWith_d, q2, hx, hy]
    rfl
  have d4 : E s4.mem base 11 = Spec.Ed448.d := by
    rw [f4 11 (by decide), e3, Point64.addAffineOps_keep _ _ (Or.inr (Or.inl (by decide))), d2]
  refine WP.seq (WP.mono (selectSignedKey_ok (k04.scr hs) ho hbnd ht (by rw [k04.gpr _ (by decide), hb])
    (bk.keep ho hbnd k04)) fun s5 ⟨k5, p5, f5⟩ => ?_)
  have d5 : E s5.mem base 11 = Spec.Ed448.d := by
    rw [f5 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), d4]
  have q5 : pt (E s5.mem base) 0 1 2 = pt (E s4.mem base) 0 1 2 :=
    pt_congr (f5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (f5 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (f5 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  refine WP.seq (WP.mono (add_ok hf hP (k5.scr (k04.scr hs)) d5) fun s6 ⟨k6, e6⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (accept_ok (k6.scr (k5.scr (k04.scr hs)))) fun s7 ⟨k7, p7, f7⟩ => ?_
  have k07 := ((k04.trans k5).trans k6).trans k7
  refine WP.mono (testRbx_ok s7 t (by omega) (by rw [k07.gpr _ (by decide), hb]))
    fun u ⟨zu, gu, mu, ru, wu⟩ => ?_
  refine ⟨⟨fun r hr => (gu r).trans (k07.gpr r hr), ru.trans k07.rd, wu.trans k07.wr, ?_⟩, zu, ?_, ?_⟩
  · rw [mu]; exact k07.mem
  · rw [mu, f7 11 (by decide), e6, addEnv_d, d5]
  · rw [mu, p7, e6, addEnv_eval, d5, addWith_d, q5, q4, p5,
      tablePoint_keep k04 (magnitude K t) (SignedWindow.magnitude_lt K t)]
    rfl

theorem dec5_ok (s : State) {t : Nat} (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 5)) :
    WP isa (.block ([.alu .sub .rbx (.imm 5)] : List Instr)) s fun u =>
      u.gpr .rbx = BitVec.ofNat 64 t ∧ (∀ r, r ≠ .rbx → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧
      u.rd = s.rd ∧ u.wr = s.wr := by
  have hb' : s.gpr .rbx - (5 : BitVec 32).signExtend 64 = BitVec.ofNat 64 t := by
    have e1 : (5 : BitVec 32).signExtend 64 = BitVec.ofNat 64 5 := by decide
    rw [hb, e1, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, hb',
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  exact ⟨trivial, fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags], rfl, rfl, rfl⟩

end VG.Proof.Ed448.X86_64.Window
