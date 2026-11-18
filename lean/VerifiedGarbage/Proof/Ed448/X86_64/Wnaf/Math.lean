module

public import VerifiedGarbage.Impl.Ed448.Wnaf
import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
import Mathlib.Tactic.Abel
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Coords
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.SelectKey
public import VerifiedGarbage.Proof.X448.X86_64.Env
import VerifiedGarbage.Proof.X448.X86_64.Setup
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Register
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
import VerifiedGarbage.Proof.X448.X86_64.Chain
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Ops
public import VerifiedGarbage.Impl.Ed448.X86_64.Wnaf.Joint
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.X86_64.Basic
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import Mathlib.Tactic.NormNum.Prime
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-! ### `Ed448.X86_64.Wnaf.Add`, which this module and modules that import it used -/

section

/-! ### `Ed448.X86_64.Wnaf.ReadDigit`, which this module and modules that import it used -/

section

/-! Decoding the signed byte digits used by public table selection. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.X448.X86_64

abbrev CodeByte (d : Int) : Byte := (BitVec.ofInt 64 d).setWidth 8
abbrev DigitWord (d : Int) : BitVec 64 := (CodeByte d).setWidth 64

theorem bounded_index {d : Int} (h : -15 ≤ d ∧ d ≤ 15) : ∃ (i : Nat), i < 31 ∧ d = (i : Int) - 15 := by
  refine ⟨(d + 15).toNat, ?_, ?_⟩ <;> omega_using [h]

private theorem digit_zero : ∀ (i : Nat), i < 31 →
    (DigitWord ((i : Int) - 15) &&& DigitWord ((i : Int) - 15) == 0) = decide ((i : Int) - 15 = 0) := by
  decide +kernel

private theorem magnitude_calc : ∀ (i : Nat), i < 31 →
    (if (!decide ((DigitWord ((i : Int) - 15)).toNat < ((128 : BitVec 32).signExtend 64).toNat)) = true
      then (256 : BitVec 32).setWidth 64 - DigitWord ((i : Int) - 15) else DigitWord ((i : Int) - 15)) =
      BitVec.ofNat 64 ((i : Int) - 15).natAbs := by decide +kernel

theorem getDigit_ok {s : State} {base : Addr} (hs : Scr s base) {o t : Nat} {d : Int}
    (ho : o + t + 1 ≤ 8192) (hd : -15 ≤ d ∧ d ≤ 15) (hr : s.gpr .rbx = BitVec.ofNat 64 t)
    (hm : s.mem (off base (o + t)) = CodeByte d) :
    WP isa (.block (getDigit o)) s fun u =>
      u.gpr .r15 = DigitWord d ∧ u.zf = some (decide (d = 0)) ∧ Keeps [.r15] s u := by
  obtain ⟨i, hi, rfl⟩ := bounded_index hd
  have hread := hs.read ho
  apply WP.of_runBlock
  simp only [getDigit, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load8, ea_bitsAt hs.rdi hr, hread, hm, RegUpd.gpr_setReg_self, RegUpd.zf_arithFlags,
    RegUpd.gpr_arithFlags, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true]
  refine ⟨trivial, digit_zero i hi, fun r h => ?_, rfl, rfl, rfl⟩
  have hn : r ≠ .r15 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
  simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, hn, ite_false]

theorem magnitude_ok {s : State} {d : Int} (hd : -15 ≤ d ∧ d ≤ 15)
    (hr : s.gpr .r15 = DigitWord d) :
    WP isa (.block magnitude) s fun u =>
      u.gpr .r15 = BitVec.ofNat 64 d.natAbs ∧ Keeps [.rax, .r15] s u := by
  obtain ⟨i, hi, rfl⟩ := bounded_index hd
  xrun [magnitude, hr, execCmov, eval]
  simp only [apply_ite State.gpr, ite_apply, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    reduceCtorEq, ite_true, ite_false, hr]
  refine ⟨magnitude_calc i hi, fun r h => ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [apply_ite State.gpr, ite_apply, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
      h.1, h.2, ite_false, ite_self]
  · simp only [apply_ite State.mem, RegUpd.mem_setReg, RegUpd.mem_setFlags, ite_self]
  · simp only [apply_ite State.rd, RegUpd.rd_setReg, RegUpd.rd_setFlags, ite_self]
  · simp only [apply_ite State.wr, RegUpd.wr_setReg, RegUpd.wr_setFlags, ite_self]

end VG.Proof.Ed448.X86_64.Wnaf

end

end

/-! ### `Ed448.X86_64.Wnaf.Select`, which only this module used -/

section

/-! ### `Ed448.X86_64.Wnaf.Sign`, which only this module used -/

section

/-! Conditional point negation for balanced window digits. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Impl.Ed448.X86_64.Window (chooseMem)
open VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.Ed448.X86_64.Window (chooseMem_ok)
open VG.Proof.X448.X86_64
open VG.Impl.X448.X86_64 (W slot loads stores)

private theorem signFlag_ok {s : State} {base : Addr} (hs : Scr s base) {o t : Nat} {d : Int}
    (ho : o + t + 1 ≤ 8192) (hd : -15 ≤ d ∧ d ≤ 15) (hr : s.gpr .rbx = BitVec.ofNat 64 t)
    (hm : s.mem (off base (o + t)) = CodeByte d) :
    WP isa (.block (signFlag o)) s fun u =>
      u.zf = some (decide (d < 0)) ∧ Keeps [.rax] s u := by
  obtain ⟨i, hi, rfl⟩ := bounded_index hd
  have hread := hs.read ho
  have hc : ∀ (i : Nat), i < 31 →
      (((DigitWord ((i : Int) - 15) &&& (128 : BitVec 32).signExtend 64) -
        (128 : BitVec 32).signExtend 64) == 0) = decide ((i : Int) - 15 < 0) := by decide +kernel
  apply WP.of_runBlock
  simp only [signFlag, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load8, ea_bitsAt hs.rdi hr, hread, hm, RegUpd.gpr_setReg_self,
    RegUpd.zf_arithFlags, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨hc i hi, fun r hr => by
    have hn : r ≠ .rax := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr
    simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, hn, ite_false], rfl, rfl, rfl⟩

/-- The sign bit selects X or -X; all coordinates except the temporary and X survive. -/
theorem negateSelected_ok {s : State} {base : Addr} (hs : Scr s base) {o t : Nat} {d : Int}
    (ho : 2048 ≤ o) (hb : o + t + 1 ≤ 8192) (hd : -15 ≤ d ∧ d ≤ 15)
    (hr : s.gpr .rbx = BitVec.ofNat 64 t) (hm : s.mem (off base (o + t)) = CodeByte d) :
    WP isa (negateSelected o) s fun u => Keep base s u ∧
      E u.mem base 8 = (if d < 0 then -(E s.mem base 8) else E s.mem base 8) ∧
      ∀ j : Index, j ≠ 3 → j ≠ 8 → E u.mem base j = E s.mem base j := by
  rw [negateSelected]
  refine WP.seq (WP.mono (constE_ok hs 3 0 c0) fun v ⟨kv, ev⟩ => ?_)
  refine WP.seq (WP.mono (Point64.fop_frame baseline_ok (kv.scr hs) (.sub 3 3 8) (by decide))
    fun w ⟨kw, ew, _⟩ => ?_)
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  have ksw := kv.trans kw
  refine WP.mono (loads_ok (ksw.scr hs) (slot 8) W (by decide) (by decide) (by decide))
    fun x ⟨_, vx, kx⟩ => ?_
  rw [WP.block_append_iff]
  have hmx : x.mem (off base (o + t)) = CodeByte d := by
    rw [kx.2.1, ksw.mem _ (Or.inr (by rw [ofs_off' base (by omega_using [hb])]; omega_using [ho]))]
    exact hm
  refine WP.mono (signFlag_ok ((ksw.scr hs).of_keeps kx (by decide)) hb hd
    ((kx.1 _ (by decide)).trans ((ksw.gpr _ (by decide)).trans hr)) hmx) fun y ⟨zy, ky⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (chooseMem_ok (((ksw.scr hs).of_keeps kx (by decide)).of_keeps ky (by decide))
    (a := slot 3) (by decide) zy) fun z ⟨vz, kz⟩ => ?_
  have hsz := (((ksw.scr hs).of_keeps kx (by decide)).of_keeps ky (by decide)).of_keeps kz (by decide)
  refine WP.mono (stores_E hsz 8 W rfl) fun u ⟨eu, ou, gu, ru, wu⟩ => ?_
  have km : z.mem = w.mem := kz.2.1.trans (ky.2.1.trans kx.2.1)
  have kg : ∀ r, r ∉ clob → z.gpr r = w.gpr r := by
    intro r hr
    have hw : r ∉ W := fun h => hr ((show ∀ r ∈ W, r ∈ clob from by decide) r h)
    have ha : r ∉ [Reg.rax] := fun h => hr ((show ∀ r ∈ [Reg.rax], r ∈ clob from by decide) r h)
    exact (kz.1 r hw).trans ((ky.1 r ha).trans (kx.1 r hw))
  have ku : Keep base w u := ⟨fun r hr => (gu r).trans (kg r hr),
    ru.trans (kz.2.2.1.trans (ky.2.2.1.trans kx.2.2.1)),
    wu.trans (kz.2.2.2.trans (ky.2.2.2.trans kx.2.2.2)), by
      rw [km] at ou; exact ou.mono (by decide) (by decide)⟩
  refine ⟨ksw.trans ku, ?_, ?_⟩
  · have vy : rv y W = rv x W := rv_congr (fun r hr => ky.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; intro h; subst r; exact absurd hr (by decide)))
    rw [eu, Function.update_self, vz, vy, vx, ky.2.1, kx.2.1]
    change VG.Proof.X448.toFe (if decide (d < 0) then fe w.mem base (slot 3)
      else fe w.mem base (slot 8)) = _
    simp only [apply_ite VG.Proof.X448.toFe]
    change (if decide (d < 0) then E w.mem base 3 else E w.mem base 8) = _
    rw [ew, ev]
    simp only [VG.Proof.Ed448.evalOp, show VG.Proof.Ed448.idx 3 = (3 : Index) from rfl,
      show VG.Proof.Ed448.idx 8 = (8 : Index) from rfl, Function.update_self, Function.update_of_ne (by decide : (8 : Index) ≠ 3),
      zero_sub, decide_eq_true_eq]
  · intro j h3 h8
    rw [eu, Function.update_of_ne h8, km, ew, ev]
    simp only [VG.Proof.Ed448.evalOp, show VG.Proof.Ed448.idx 3 = (3 : Index) from rfl,
      show VG.Proof.Ed448.idx 8 = (8 : Index) from rfl, Function.update_of_ne h3]

end VG.Proof.Ed448.X86_64.Wnaf

end

end


/-! Sparse signed-digit selection preserves the accumulator and curve constant. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.Ed448.X86_64.Window (SelKeeps KeyKeeps tablePoint)
open VG.Proof.X448.X86_64
open VG.Proof.Ed448 (pt)

def baseEntry (d : Int) : Spec.X448.Fe × Spec.X448.Fe :=
  let p := Impl.Ed448.SignedWindow.entry d.natAbs
  (if d < 0 then -p.1 else p.1, p.2)

theorem abs_lt {d : Int} (hd : -15 ≤ d ∧ d ≤ 15) : d.natAbs < 17 := by omega_using [hd]

theorem code_keep {base : Addr} {o t : Nat} {d : Int} {s u : State} (h : Keep base s u)
    (ho : 2048 ≤ o) (hb : o + t + 1 ≤ 8192) (hm : s.mem (off base (o + t)) = CodeByte d) :
    u.mem (off base (o + t)) = CodeByte d := by
  rw [h.mem _ (Or.inr (by rw [ofs_off' base (by omega_using [hb])]; omega_using [ho]))]
  exact hm

theorem selectBase_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} {d : Int}
    (ht : t < 461) (hd : -15 ≤ d ∧ d ≤ 15) (hr : s.gpr .rbx = BitVec.ofNat 64 t)
    (hm : s.mem (off base (SDIG + t)) = CodeByte d) (hdigit : s.gpr .r15 = DigitWord d) :
    WP isa selectBase s fun u => Keep base s u ∧
      (E u.mem base 8, E u.mem base 9) = baseEntry d ∧ SelKeeps (E s.mem base) (E u.mem base) := by
  rw [selectBase]
  apply WP.seq
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (magnitude_ok hd hdigit) fun a ⟨da, ka⟩ => ?_
  have ka' : Keep base s a := keeps_keep (ka.mono (by decide))
  refine WP.mono (baseCoords_ok (ka'.scr hs) (abs_lt hd) da) fun b ⟨kb, pb, fb⟩ => ?_
  have kab := ka'.trans kb
  refine WP.mono (negateSelected_ok (kab.scr hs) (by decide : 2048 ≤ SDIG)
    (by simp only [SDIG]; omega_using [ht]) hd ((kab.gpr _ (by decide)).trans hr)
    (code_keep kab (by decide) (by simp only [SDIG]; omega_using [ht]) hm)) fun u ⟨ku, xu, fu⟩ => ?_
  refine ⟨kab.trans ku, ?_, ?_⟩
  · have px := congrArg Prod.fst pb
    have py := congrArg Prod.snd pb
    dsimp only at px py
    rw [xu, fu 9 (by decide) (by decide), px, py]
    rfl
  · intro j h3 h4 h8 h9
    rw [fu j h3 h8, fb j h3 h4 h8 h9, ka.2.1]

theorem selectKey_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} {d : Int}
    (ht : t < 461) (hd : -15 ≤ d ∧ d ≤ 15) (hr : s.gpr .rbx = BitVec.ofNat 64 t)
    (hm : s.mem (off base (KDIG + t)) = CodeByte d) (hdigit : s.gpr .r15 = DigitWord d) :
    WP isa selectKey s fun u => Keep base s u ∧
      pt (E u.mem base) 8 9 10 = Proof.Ed448.SignedWindow.signedPoint (decide (d < 0))
        (tablePoint s.mem base d.natAbs) ∧ KeyKeeps (E s.mem base) (E u.mem base) := by
  rw [selectKey]
  apply WP.seq
  rw [List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (magnitude_ok hd hdigit) fun a ⟨da, ka⟩ => ?_
  have ka' : Keep base s a := keeps_keep (ka.mono (by decide))
  refine WP.mono (keyCoords_ok (ka'.scr hs) (abs_lt hd) da) fun b ⟨kb, pb, fb⟩ => ?_
  have kab := ka'.trans kb
  refine WP.mono (negateSelected_ok (kab.scr hs) (by decide : 2048 ≤ KDIG)
    (by simp only [KDIG]; omega_using [ht]) hd ((kab.gpr _ (by decide)).trans hr)
    (code_keep kab (by decide) (by simp only [KDIG]; omega_using [ht]) hm)) fun u ⟨ku, xu, fu⟩ => ?_
  refine ⟨kab.trans ku, ?_, ?_⟩
  · have px := congrArg Spec.Ed448.Point.X pb
    have py := congrArg Spec.Ed448.Point.Y pb
    have pz := congrArg Spec.Ed448.Point.Z pb
    dsimp only [pt] at px py pz
    simp only [pt, xu, fu 9 (by decide) (by decide), fu 10 (by decide) (by decide), px, py, pz, ka.2.1]
    by_cases hn : d < 0 <;>
      simp only [hn, decide_true, decide_false, Proof.Ed448.SignedWindow.signedPoint,
        ite_true, Bool.false_eq_true, ite_false, Proof.Ed448.negPoint, zero_sub]
  · intro j h3 h4 h5 h8 h9 h10
    rw [fu j h3 h8, fb j h3 h4 h5 h8 h9 h10, ka.2.1]

end VG.Proof.Ed448.X86_64.Wnaf

end

end


/-! Optional additions for the nonzero signed digits. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.Ed448 VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64
open VG.Proof.Ed448.X86_64.Window (accept_ok tablePoint add_ok addEnv_d addEnv_eval)

private theorem baseBody_ok {P : Point64.Ops} (hP : Point64.PointOk P) {s : State} {base : Addr}
    (hs : Scr s base) {t : Nat} {d : Int} (ht : t < 461) (hd : -15 ≤ d ∧ d ≤ 15)
    (hr : s.gpr .rbx = BitVec.ofNat 64 t) (hm : s.mem (off base (SDIG + t)) = CodeByte d)
    (hi : s.gpr .r15 = DigitWord d) (hc : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (.seq selectBase (.seq P.add (.block Window.accept))) s fun u => Keep base s u ∧
      E u.mem base 11 = Spec.Ed448.d ∧ pt (E u.mem base) 0 1 2 =
        Spec.Ed448.pointAdd (pt (E s.mem base) 0 1 2) (Proof.X448.basePt (baseEntry d)) := by
  refine WP.seq (WP.mono (selectBase_ok hs ht hd hr hm hi) fun a ⟨ka, pa, fa⟩ => ?_)
  have ac : E a.mem base 11 = Spec.Ed448.d := by rw [fa 11 (by decide) (by decide) (by decide) (by decide), hc]
  have ap : pt (E a.mem base) 0 1 2 = pt (E s.mem base) 0 1 2 :=
    pt_congr (fa 0 (by decide) (by decide) (by decide) (by decide))
      (fa 1 (by decide) (by decide) (by decide) (by decide))
      (fa 2 (by decide) (by decide) (by decide) (by decide))
  refine WP.seq (WP.mono (hP.add (ka.scr hs) ac) fun b ⟨kb, eb⟩ => ?_)
  refine WP.mono (accept_ok (kb.scr (ka.scr hs))) fun u ⟨ku, pu, fu⟩ => ?_
  refine ⟨(ka.trans kb).trans ku, ?_, ?_⟩
  · rw [fu 11 (by decide), eb, Point64.addAffineOps_keep _ _ (Or.inr (Or.inl (by decide))), ac]
  · have px := congrArg Prod.fst pa
    have py := congrArg Prod.snd pa
    dsimp only at px py
    rw [pu, eb, Point64.addAffineOps_eval, ac, addWith_d, ap, px, py]
    rfl

private theorem keyBody_ok {F : Impl.X448.X86_64.Field} (hf : FieldOk F)
    {P : Point64.Ops} (hP : Point64.PointOk P) {s : State} {base : Addr}
    (hs : Scr s base) {t : Nat} {d : Int} (ht : t < 461) (hd : -15 ≤ d ∧ d ≤ 15)
    (hr : s.gpr .rbx = BitVec.ofNat 64 t) (hm : s.mem (off base (KDIG + t)) = CodeByte d)
    (hi : s.gpr .r15 = DigitWord d) (hc : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (.seq selectKey (.seq (Window.add F P) (.block Window.accept))) s fun u => Keep base s u ∧
      E u.mem base 11 = Spec.Ed448.d ∧ pt (E u.mem base) 0 1 2 =
        Spec.Ed448.pointAdd (pt (E s.mem base) 0 1 2)
          (SignedWindow.signedPoint (decide (d < 0)) (tablePoint s.mem base d.natAbs)) := by
  refine WP.seq (WP.mono (selectKey_ok hs ht hd hr hm hi) fun a ⟨ka, pa, fa⟩ => ?_)
  have ac : E a.mem base 11 = Spec.Ed448.d := by
    rw [fa 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hc]
  have ap : pt (E a.mem base) 0 1 2 = pt (E s.mem base) 0 1 2 :=
    pt_congr (fa 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fa 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fa 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  refine WP.seq (WP.mono (add_ok hf hP (ka.scr hs) ac) fun b ⟨kb, eb⟩ => ?_)
  refine WP.mono (accept_ok (kb.scr (ka.scr hs))) fun u ⟨ku, pu, fu⟩ => ?_
  refine ⟨(ka.trans kb).trans ku, ?_, ?_⟩
  · rw [fu 11 (by decide), eb, addEnv_d, ac]
  · rw [pu, eb, addEnv_eval, ac, addWith_d, ap, pa]

def maybeAdd (d : Int) (p q : Spec.Ed448.Point) : Spec.Ed448.Point :=
  if d = 0 then p else Spec.Ed448.pointAdd p q

theorem addBase_ok {P : Point64.Ops} (hP : Point64.PointOk P) {s : State} {base : Addr}
    (hs : Scr s base) {t : Nat} {d : Int} (ht : t < 461) (hd : -15 ≤ d ∧ d ≤ 15)
    (hr : s.gpr .rbx = BitVec.ofNat 64 t) (hm : s.mem (off base (SDIG + t)) = CodeByte d)
    (hc : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (addBase P) s fun u => Keep base s u ∧ E u.mem base 11 = Spec.Ed448.d ∧
      pt (E u.mem base) 0 1 2 = maybeAdd d (pt (E s.mem base) 0 1 2) (Proof.X448.basePt (baseEntry d)) := by
  refine WP.seq (WP.mono (getDigit_ok hs (by simp only [SDIG]; omega_using [ht]) hd hr hm) fun a ⟨ar, az, ak⟩ => ?_)
  have ka : Keep base s a := keeps_keep (ak.mono (by decide))
  refine WP.ite (!decide (d = 0)) (by simp only [eval, az, Option.map_some]) (fun hz => ?_) (fun hz => ?_)
  · have hn : d ≠ 0 := by simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using hz
    refine WP.mono (baseBody_ok hP (ka.scr hs) ht hd ((ka.gpr _ (by decide)).trans hr)
      (by rw [ak.2.1]; exact hm) ar (by rw [ak.2.1]; exact hc)) fun u ⟨ku, du, pu⟩ => ?_
    refine ⟨ka.trans ku, du, ?_⟩
    rw [pu, ak.2.1, maybeAdd, ite_eq_right hn]
  · have he : d = 0 := by simpa only [Bool.not_eq_false', decide_eq_true_eq] using hz
    refine WP.block_nil ⟨ka, ?_, ?_⟩
    · rw [ak.2.1]; exact hc
    · rw [maybeAdd, ite_eq_left he, ak.2.1]

theorem addKey_ok {F : Impl.X448.X86_64.Field} (hf : FieldOk F)
    {P : Point64.Ops} (hP : Point64.PointOk P) {s : State} {base : Addr}
    (hs : Scr s base) {t : Nat} {d : Int} (ht : t < 461) (hd : -15 ≤ d ∧ d ≤ 15)
    (hr : s.gpr .rbx = BitVec.ofNat 64 t) (hm : s.mem (off base (KDIG + t)) = CodeByte d)
    (hc : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (addKey F P) s fun u => Keep base s u ∧ E u.mem base 11 = Spec.Ed448.d ∧
      pt (E u.mem base) 0 1 2 = maybeAdd d (pt (E s.mem base) 0 1 2)
        (SignedWindow.signedPoint (decide (d < 0)) (tablePoint s.mem base d.natAbs)) := by
  refine WP.seq (WP.mono (getDigit_ok hs (by simp only [KDIG]; omega_using [ht]) hd hr hm) fun a ⟨ar, az, ak⟩ => ?_)
  have ka : Keep base s a := keeps_keep (ak.mono (by decide))
  refine WP.ite (!decide (d = 0)) (by simp only [eval, az, Option.map_some]) (fun hz => ?_) (fun hz => ?_)
  · have hn : d ≠ 0 := by simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using hz
    refine WP.mono (keyBody_ok hf hP (ka.scr hs) ht hd ((ka.gpr _ (by decide)).trans hr)
      (by rw [ak.2.1]; exact hm) ar (by rw [ak.2.1]; exact hc)) fun u ⟨ku, du, pu⟩ => ?_
    refine ⟨ka.trans ku, du, ?_⟩
    rw [pu, ak.2.1, maybeAdd, ite_eq_right hn]
  · have he : d = 0 := by simpa only [Bool.not_eq_false', decide_eq_true_eq] using hz
    refine WP.block_nil ⟨ka, ?_, ?_⟩
    · rw [ak.2.1]; exact hc
    · rw [maybeAdd, ite_eq_left he, ak.2.1]

end VG.Proof.Ed448.X86_64.Wnaf

end

end

/-! The sparse loop's group interpretation. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG.Proof.Ed448 VG.Proof.EdwardsLaw
open VG.Impl.Ed448.Wnaf (residual digitAt)

theorem signed_abs (d : Int) : (if decide (d < 0) then -(d.natAbs : Int) else (d.natAbs : Int)) = d := by
  by_cases hd : d < 0 <;> simp only [hd, decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false] <;> omega_using [hd]

theorem baseEntry_rep {d : Int} (hd : -15 ≤ d ∧ d ≤ 15) :
    Rep (Proof.X448.basePt (baseEntry d)) (d • baseAff) := by
  have h := SignedWindow.signedPoint_rep (SignedWindow.entry_rep d.natAbs (abs_lt hd)) (decide (d < 0))
  rw [signed_abs] at h
  have he : Proof.X448.basePt (baseEntry d) = SignedWindow.signedPoint (decide (d < 0))
      (Proof.X448.basePt (Impl.Ed448.SignedWindow.entry d.natAbs)) := by
    by_cases hn : d < 0 <;>
      simp only [baseEntry, Proof.X448.basePt, hn, decide_true, decide_false, SignedWindow.signedPoint,
        ite_true, Bool.false_eq_true, ite_false, negPoint, zero_sub]
  rw [he]; exact h

theorem maybeAdd_rep {p q : Spec.Ed448.Point} {a b : EPoint dZ} {d : Int}
    (hp : Rep p a) (hq : Rep q (d • b)) : Rep (maybeAdd d p q) (a + d • b) := by
  by_cases hd : d = 0
  · simpa only [maybeAdd, hd, ite_true, zero_smul, add_zero] using hp
  · rw [maybeAdd, ite_eq_right hd]
    exact pointAdd_rep hp hq

theorem round_rep {p q : Spec.Ed448.Point} {a : EPoint dZ} {S K n : Nat}
    (hp : Rep p ((residual S (n + 1) : Int) • baseAff + (residual K (n + 1) : Int) • a))
    (hq : Rep q ((digitAt K n) • a)) :
    Rep (maybeAdd (digitAt K n)
      (maybeAdd (digitAt S n) (double p) (Proof.X448.basePt (baseEntry (digitAt S n)))) q)
      ((residual S n : Int) • baseAff + (residual K n : Int) • a) := by
  have h := maybeAdd_rep (maybeAdd_rep (double_rep hp)
    (baseEntry_rep (Proof.Ed448.Wnaf.digit_bounds (residual S n)))) hq
  convert h using 1
  · rfl
  · rw [Proof.Ed448.Wnaf.residual_step S n, Proof.Ed448.Wnaf.residual_step K n, add_zsmul,
      add_zsmul, mul_smul, mul_smul, two_zsmul, two_zsmul]
    simp only [digitAt]
    abel

end VG.Proof.Ed448.X86_64.Wnaf
