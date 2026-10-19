module

import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Joint
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Joint
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Timing
public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Loop
public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.ReadDigit
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Timing
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Recode
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Recode
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Init
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Init
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Add
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Add
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Table
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Table
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Coords
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Coords
import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
meta import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
import VerifiedGarbage.Proof.Ed448.X86_64.BaseField
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLoop
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Verified
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Digit
import VerifiedGarbage.Proof.Ed448.X86_64.Window.DirectKey
import VerifiedGarbage.Proof.Ed448.X86_64.Window.First
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Joint
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Register
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Round
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Digit
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Load
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Math
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Write
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.X448.X86_64.AddSub
import VerifiedGarbage.Proof.X448.X86_64.Pow223
import VerifiedGarbage.Proof.X448.X86_64.Pow223Verified
meta import VerifiedGarbage.Proof.Ed448.Scalar
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseField
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseLoop
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Verified
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Digit
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.DirectKey
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.First
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Joint
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Register
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Round
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Digit
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Load
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Loop
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Math
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Write
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Spill
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.X448.X86_64.AddSub
meta import VerifiedGarbage.Proof.X448.X86_64.Pow223
meta import VerifiedGarbage.Proof.X448.X86_64.Pow223Verified

/-! Sparse control flow depends only on the public verification scalars. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.X448.X86_64
open VG.Impl.Ed448.Wnaf (digitAt)
open VG.Impl.X448.X86_64 (BITS)
open VG.Proof.Ed448.X86_64.Window (seq_same JointTimingCtx)

structure Ctx (base : Addr) (S K n : Nat) (s : State) : Prop where
  scr : Scr s base
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  bs : Digits base SDIG S s
  bk : Digits base KDIG K s
  d : E s.mem base 11 = Spec.Ed448.d

theorem Ctx.keep {base : Addr} {S K n : Nat} {s u : State}
    (h : Ctx base S K n s) (hk : Keep base s u)
    (hd : E u.mem base 11 = Spec.Ed448.d) : Ctx base S K n u :=
  ⟨hk.scr h.scr, (hk.gpr _ (by decide)).trans h.rbx,
    h.bs.keep (by decide) (by decide) hk, h.bk.keep (by decide) (by decide) hk, hd⟩

private theorem ctx_agree {base : Addr} {S K n : Nat} {s u : State}
    (h : Ctx base S K n s ∧ Ctx base S K n u) :
    X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rbx]) s u := by
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.scr.rdi.trans h.2.scr.rdi.symm
  · exact h.1.rbx.trans h.2.rbx.symm

def Picked (base : Addr) (S K n : Nat) (d : Int) (s : State) : Prop :=
  Ctx base S K n s ∧ s.gpr .r15 = DigitWord d ∧ s.zf = some (decide (d = 0))

private theorem picked_agree {base : Addr} {S K n : Nat} {d : Int} {s u : State}
    (h : Picked base S K n d s ∧ Picked base S K n d u) :
    X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rbx, .r15]) s u := by
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1.1.scr.rdi.trans h.2.1.scr.rdi.symm
  · exact h.1.1.rbx.trans h.2.1.rbx.symm
  · exact h.1.2.1.trans h.2.2.1.symm

theorem conditional_ct (base : Addr) (S K n o : Nat) (d : Int) (p : Prog isa)
    (ho : o + n + 1 ≤ 8192) (hd : -15 ≤ d ∧ d ≤ 15)
    (hm : ∀ s, Ctx base S K n s → s.mem (off base (o + n)) = CodeByte d)
    (head : RelCT isa (fun s u => Ctx base S K n s ∧ Ctx base S K n u)
      (.block (getDigit o)) (fun _ _ => True))
    (hp : RelCT isa (fun s u => Picked base S K n d s ∧ Picked base S K n d u) p (fun _ _ => True)) :
    RelCT isa (fun s u => Ctx base S K n s ∧ Ctx base S K n u)
      (.seq (.block (getDigit o)) (.ite .ne p (.block []))) (fun _ _ => True) := by
  have hw (s : State) (h : Ctx base S K n s) : WP isa (.block (getDigit o)) s (Picked base S K n d) := by
    refine WP.mono (getDigit_ok h.scr ho hd h.rbx (hm s h)) fun u ⟨ur, uz, ku⟩ => ?_
    exact ⟨h.keep (keeps_keep (ku.mono (by decide))) (by rw [ku.2.1]; exact h.d), ur, uz⟩
  apply seq_same head hw
  apply RelCT.ite
  · intro s u h
    simp only [eval, h.1.2.2, h.2.2.2, Option.map_some]
  · exact hp.mono (fun _ _ h => h.1) (fun _ _ h => h)
  · exact RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

theorem addBase_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K n : Nat) (hn : n < 461) :
    RelCT isa (fun s u => Ctx base S K n s ∧ Ctx base S K n u) (addBase v.bodies) (fun _ _ => True) := by
  apply conditional_ct base S K n SDIG (digitAt S n) _ (by simp only [SDIG]; omega)
    (Proof.Ed448.Wnaf.digit_bounds _) (fun _ h => h.bs n hn)
  · exact RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbx]) (fun _ _ h => ctx_agree h) (by taint_decide)
  cases v <;> exact relCT_sum (Taint.ofRegs [.rdi, .rbx, .r15])
    (fun _ _ h => picked_agree h) (by taint_decide_sum [dblSum, addSum, dblAdxSum, addAdxSum])

theorem addKey_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K n : Nat) (hn : n < 461) :
    RelCT isa (fun s u => Ctx base S K n s ∧ Ctx base S K n u) (addKey v.field v.bodies) (fun _ _ => True) := by
  apply conditional_ct base S K n KDIG (digitAt K n) _ (by simp only [KDIG]; omega)
    (Proof.Ed448.Wnaf.digit_bounds _) (fun _ h => h.bk n hn)
  · exact RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbx]) (fun _ _ h => ctx_agree h) (by taint_decide)
  cases v <;> exact relCT_sum (Taint.ofRegs [.rdi, .rbx, .r15])
    (fun _ _ h => picked_agree h) (by taint_decide_sum [dblSum, addSum, dblAdxSum, addAdxSum])

theorem dbl_ctx (v : Impl.Ed448.X86_64.FieldVariant) {base : Addr} {S K n : Nat} {s : State}
    (h : Ctx base S K n s) : WP isa v.bodies.dbl s (Ctx base S K n) := by
  refine WP.mono ((FieldVariant.bodies_ok v).dbl h.scr) fun u ⟨ku, eu⟩ => ?_
  exact h.keep ku (by rw [eu, doubleOps_keep _ _ (Or.inl ⟨by decide, by decide⟩), h.d])

theorem base_ctx (v : Impl.Ed448.X86_64.FieldVariant) {base : Addr} {S K n : Nat} {s : State}
    (h : Ctx base S K n s) (hn : n < 461) : WP isa (addBase v.bodies) s (Ctx base S K n) := by
  refine WP.mono (addBase_ok (FieldVariant.bodies_ok v) h.scr hn (Proof.Ed448.Wnaf.digit_bounds _)
    h.rbx (h.bs n hn) h.d) fun u ⟨ku, du, _⟩ => h.keep ku du

theorem key_ctx (v : Impl.Ed448.X86_64.FieldVariant) {base : Addr} {S K n : Nat} {s : State}
    (h : Ctx base S K n s) (hn : n < 461) : WP isa (addKey v.field v.bodies) s (Ctx base S K n) := by
  refine WP.mono (addKey_ok (FieldVariant.field_ok v) (FieldVariant.bodies_ok v) h.scr hn
    (Proof.Ed448.Wnaf.digit_bounds _) h.rbx (h.bk n hn) h.d) fun u ⟨ku, du, _⟩ => h.keep ku du

theorem dec_ctx {base : Addr} {S K n : Nat} {s : State} (h : Ctx base S K (n + 1) s) :
    WP isa (.block [.alu .sub .rbx (.imm 1)]) s (Ctx base S K n) := by
  refine WP.mono (dec1_ok s h.rbx) fun u ⟨bu, gu, mu, ru, wu⟩ => ?_
  exact ⟨⟨(gu _ (by decide)).trans h.scr.rdi, wu ▸ h.scr.wr, h.scr.nowrap⟩,
    bu, (by rw [Digits, mu]; exact h.bs), (by rw [Digits, mu]; exact h.bk), (by rw [mu]; exact h.d)⟩

theorem step_ctx (v : Impl.Ed448.X86_64.FieldVariant) {base : Addr} {S K n : Nat} {s : State}
    (h : Ctx base S K (n + 1) s) (hn : n < 461) : WP isa (step v.field v.bodies) s fun u =>
      Ctx base S K n u ∧ u.zf = some (decide (n = 0)) := by
  refine WP.seq (WP.mono (dec_ctx h) fun a ha => ?_)
  refine WP.seq (WP.mono (dbl_ctx v ha) fun b hb => ?_)
  refine WP.seq (WP.mono (base_ctx v hb hn) fun c hc => ?_)
  refine WP.seq (WP.mono (key_ctx v hc hn) fun d hd => ?_)
  refine WP.mono (testCounter_ok d n hn hd.rbx) fun u ⟨zu, gu, mu, ru, wu⟩ => ?_
  exact ⟨⟨⟨(gu _).trans hd.scr.rdi, wu ▸ hd.scr.wr, hd.scr.nowrap⟩, (gu _).trans hd.rbx,
    (by rw [Digits, mu]; exact hd.bs), (by rw [Digits, mu]; exact hd.bk), (by rw [mu]; exact hd.d)⟩, zu⟩

theorem step_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K n : Nat) (hn : n < 461) :
    RelCT isa (fun s u => Ctx base S K (n + 1) s ∧ Ctx base S K (n + 1) u)
      (step v.field v.bodies) (fun _ _ => True) := by
  have dbl : RelCT isa (fun s u => Ctx base S K n s ∧ Ctx base S K n u) v.bodies.dbl (fun _ _ => True) := by
    cases v <;> exact relCT_sum (Taint.ofRegs [.rdi, .rbx])
      (fun _ _ h => ctx_agree h) (by taint_decide_sum [dblSum, addSum, dblAdxSum, addAdxSum])
  have test : RelCT isa (fun s u => Ctx base S K n s ∧ Ctx base S K n u)
      (.block [.alu .test .rbx (.reg .rbx)]) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbx]) (fun _ _ h => ctx_agree h) (by taint_decide)
  apply seq_same (p := .block [.alu .sub .rbx (.imm 1)]) _ (fun _ h => dec_ctx h)
    (seq_same dbl (fun _ h => dbl_ctx v h)
      (seq_same (addBase_ct v base S K n hn) (fun _ h => base_ctx v h hn)
        (seq_same (addKey_ct v base S K n hn) (fun _ h => key_ctx v h hn) test)))
  exact RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbx]) (fun _ _ h => ctx_agree h) (by taint_decide)

theorem loop_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K : Nat) :
    RelCT isa (fun s u => Ctx base S K 461 s ∧ Ctx base S K 461 u)
      (.loop (step v.field v.bodies) .ne) (fun _ _ => True) := by
  let I (n : Nat) (s u : State) := 1 ≤ n ∧ n ≤ 461 ∧ Ctx base S K n s ∧ Ctx base S K n u
  have hstep : ∀ n, RelCT isa (I n) (step v.field v.bodies) fun s u =>
      isa.eval .ne s = isa.eval .ne u ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m < n, I m s u) := by
    intro n s u tr1 tr2 s' u' hn ex1 ex2
    obtain ⟨hn0, hn1, hs, hu⟩ := hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨he, _⟩ := step_ct v base S K m (by omega) s u tr1 tr2 s' u' ⟨hs, hu⟩ ex1 ex2
    obtain ⟨_, a, ea, ha⟩ := step_ctx v hs (by omega)
    obtain ⟨_, b, eb, hb⟩ := step_ctx v hu (by omega)
    obtain ⟨_, rfl⟩ := Exec.det ex1 ea
    obtain ⟨_, rfl⟩ := Exec.det ex2 eb
    have za : isa.eval .ne s' = some (!decide (m = 0)) := by simp only [eval, ha.2, Option.map_some]
    have zb : isa.eval .ne u' = some (!decide (m = 0)) := by simp only [eval, hb.2, Option.map_some]
    refine ⟨he, za.trans zb.symm, fun _ => trivial, fun hz => ?_⟩
    have hp : 0 < m := by rw [za] at hz; simp only [Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at hz; omega
    exact ⟨m, by omega, hp, by omega, ha.1, hb.1⟩
  exact (RelCT.loop I hstep 461).mono (fun _ _ h => ⟨by decide, by decide, h⟩) (fun _ _ h => h)

def jointHead (v : Impl.Ed448.X86_64.FieldVariant) : Prog isa :=
  .seq (.seq (.seq (Window.table v.bodies) (recode BITS SDIG)) (recode KBITS KDIG))
    (.block (constSlot 0 0 ++ constSlot 1 1 ++ constSlot 2 1 ++ [.mov32 .rbx (.imm 461)]))

theorem jointHead_ok (v : Impl.Ed448.X86_64.FieldVariant) {base : Addr} {S K : Nat} {s : State}
    (h : JointTimingCtx base S K s) (hS : S < 2 ^ 456) (hK : K < 2 ^ 456) :
    WP isa (jointHead v) s (Ctx base S K 461) := by
  apply WP.assoc'
  apply WP.assoc'
  refine WP.seq (WP.mono (Window.table_ok (FieldVariant.bodies_ok v) h.scr h.d h.z h.p)
    fun a ⟨ka, da, _⟩ => ?_)
  have bsA := h.bs.keepW (by decide) (by decide) ka
  have bkA := h.bk.keepW (by decide) (by decide) ka
  refine WP.seq (WP.mono (recode_ok (ka.scr h.scr) (by decide) (by decide) (by decide) bsA hS)
    fun b hB => ?_)
  have bkB : Window.Bits base KBITS K b := by
    intro i hi
    rw [hB.mem _ (Or.inl (by rw [ofs_off' base (by simp only [KBITS]; omega)]; simp only [KBITS, SDIG]; omega))]
    exact bkA i hi
  refine WP.seq (WP.mono (recode_ok hB.scr (by decide) (by decide) (by decide) bkB hK) fun c hC => ?_)
  have sb : Digits base SDIG S b := hB.digits
  have sc : Digits base SDIG S c := by
    intro i hi
    rw [hC.mem _ (Or.inl (by rw [ofs_off' base (by simp only [SDIG]; omega)]; simp only [SDIG, KDIG]; omega))]
    exact sb i hi
  have kc : Digits base KDIG K c := hC.digits
  refine WP.mono (initPoint_ok hC.scr) fun d hD => ?_
  refine ⟨hD.scr, hD.rbx, ?_, ?_, ?_⟩
  · intro i hi
    rw [hD.mem _ (Or.inr (by rw [ofs_off' base (by simp only [SDIG]; omega)]; simp only [SDIG]; omega))]
    exact sc i hi
  · intro i hi
    rw [hD.mem _ (Or.inr (by rw [ofs_off' base (by simp only [KDIG]; omega)]; simp only [KDIG]; omega))]
    exact kc i hi
  · rw [hD.d, hC.env (by decide), hB.env (by decide)]; exact da

theorem joint_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K : Nat)
    (hS : S < 2 ^ 456) (hK : K < 2 ^ 456) :
    RelCT isa (fun s u => JointTimingCtx base S K s ∧ JointTimingCtx base S K u)
      (joint v.field v.bodies KBITS) (fun _ _ => True) := by
  have head : RelCT isa (fun s u => JointTimingCtx base S K s ∧ JointTimingCtx base S K u)
      (jointHead v) (fun _ _ => True) := by
    cases v <;> apply relCT_sum (Taint.ofRegs [.rdi]) _ (by taint_decide_sum [dblSum, addSum, dblAdxSum, addAdxSum])
    all_goals
      intro s u h
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h.1.scr.rdi.trans h.2.scr.rdi.symm
  exact (seq_same head (fun _ h => jointHead_ok v h hS hK) (loop_ct v base S K)).assoc.assoc.assoc

end VG.Proof.Ed448.X86_64.Wnaf
