module

public import VerifiedGarbage.Proof.Ffdh.X86.CheckPublicCT
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckPublicCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
meta import VerifiedGarbage.Proof.Ffdh.X86.Checks
meta import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivate
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.X86.Stages
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivate
meta import VerifiedGarbage.Proof.Ffdh.X86.Entry
meta import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ffdh.X86.Stages

/-! ### `Ffdh.X86.CheckPrivateTop`, which only this module used -/

section

/-! # `vg_ffdh_check_private` on i686 against its contract: the result -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.CheckPrivate

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In)
open VG.Proof.Ffdh.X86
open VG.Proof.Ffdh.X86.CheckDomain (domBytes)
open VG.Proof.Ffdh.X86.CheckPublic (YGeo yv)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)

theorem wrapABI {s : State} (A : CheckPrivateABI s) : WrapABI Impl.Ffdh.X86.CheckPrivate.args 9 s where
  below := ⟨(fun _ h => by cases h), by decide, by decide, by decide, (fun _ h => by cases h; decide),
    (fun _ h => by cases h; decide), by decide, (fun _ h => by cases h)⟩
  stackLow := A.stackLow
  stackBound := by have := A.stackBound; omega_using [this]
  argsIn := by rw [A.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  wsIn := by rw [A.wr]; exact List.mem_cons_self ..
  scratchArgs := A.scratchArgs
  retScratch := A.retScratch
  belowScratch := A.belowScratch
  scratchBound := A.scratchBound
  lower := A.pLen.1
  upper := A.pLen.2
  scratchLength := A.scratchLength

/-- The domain's and y's bytes at entry. -/
abbrev entryDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat
abbrev entryY (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 3) (arg s 4).toNat
abbrev entryX (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat

theorem frameBody_all :
    (Code.seq (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.CheckPrivate.args)) Impl.Ffdh.X86.CheckPrivate.body :
      Prog isa).allInstrs VG.Proof.Mont.X86.StaticSquare.noSp = true := by
  rsa_stack_shape

/-- What the body may read: the domain, y and x. -/
abbrev Rd (s : State) : List Region → List Region → Prop :=
  fun rd wr => InRegions (rd ++ wr) (argumentPointer s 0) (arg s 1).toNat ∧
    InRegions (rd ++ wr) (argumentPointer s 3) (arg s 4).toNat ∧
    InRegions (rd ++ wr) (argumentPointer s 5) (arg s 6).toNat

/-- The domain, y and x, as the synthetic arguments give them, for permissions that read them, apart from
the 96 bytes below the frame. -/
theorem frame_geo {s : State} (A : CheckPrivateABI s) {sp : BitVec 32}
    (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) {rd wr : List Region} (hrd : Rd s rd wr) :
    DomGeo (synth Impl.Ffdh.X86.CheckPrivate.args (arg s)) (wsBase Impl.Ffdh.X86.CheckPrivate.args s)
      (wsSize Impl.Ffdh.X86.CheckPrivate.args s) (pLenOf Impl.Ffdh.X86.CheckPrivate.args s) (arg s 1).toNat rd wr ∧
    YGeo (synth Impl.Ffdh.X86.CheckPrivate.args (arg s)) (wsBase Impl.Ffdh.X86.CheckPrivate.args s)
      (wsSize Impl.Ffdh.X86.CheckPrivate.args s) (pLenOf Impl.Ffdh.X86.CheckPrivate.args s) rd wr ∧
    XGeo (synth Impl.Ffdh.X86.CheckPrivate.args (arg s)) (wsBase Impl.Ffdh.X86.CheckPrivate.args s)
      (wsSize Impl.Ffdh.X86.CheckPrivate.args s) (pLenOf Impl.Ffdh.X86.CheckPrivate.args s) (arg s 6).toNat rd wr ∧
    Region.Disjoint ⟨byteAddr (synth Impl.Ffdh.X86.CheckPrivate.args (arg s) 2), (arg s 1).toNat⟩ (below sp 96) ∧
    Region.Disjoint ⟨byteAddr (synth Impl.Ffdh.X86.CheckPrivate.args (arg s) 8),
      pLenOf Impl.Ffdh.X86.CheckPrivate.args s⟩ (below sp 96) ∧
    Region.Disjoint ⟨byteAddr (synth Impl.Ffdh.X86.CheckPrivate.args (arg s) 10), (arg s 6).toNat⟩
      (below sp 96) := by
  have fb : argsFrame = 76 := rfl
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have yl := A.yLen
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega_using [fb, low, st'])
  have espN : sp.toNat = (s.gpr .esp).toNat - 76 := by rw [espf]; exact VG.X86.sub_toNat (by omega_using [fb, low, st'])
  have ofn : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have sub40 : Region.Sub (below sp 96) ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
    simp only [below]
    rw [VG.X86.Taint.sub_setWidth (by rw [espN]; omega_using [low, st']), espf,
      show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
      ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 96#64 = BitVec.ofNat 64 172 from rfl]
    exact Region.sub_prefix (by decide)
  have yR : (arg s 4).toNat = pLenOf Impl.Ffdh.X86.CheckPrivate.args s := yl
  refine ⟨⟨(ofn _).symm, (ofn _).symm, (ofn _).symm, rfl, rfl, (ofn _).symm, A.dLen, A.domBound, hrd.1,
    A.domScratch, A.pLen.1, A.pLen.2⟩, ⟨(ofn _).symm, ?_, ?_, ?_⟩,
    ⟨(ofn _).symm, A.xPos, A.xLen, A.xBound, hrd.2.2, A.xScratch⟩, (A.belowDom.sub_left sub40).symm, ?_,
    (A.belowX.sub_left sub40).symm⟩
  · show (arg s 3).toNat + _ ≤ _
    rw [← yR]; exact A.yBound
  · show InRegions _ (argumentPointer s 3) _
    rw [← yR]; exact hrd.2.1
  · show Region.Disjoint ⟨argumentPointer s 3, _⟩ _
    rw [← yR]; exact A.yScratch
  · show Region.Disjoint ⟨argumentPointer s 3, _⟩ _
    rw [← yR]; exact (A.belowY.sub_left sub40).symm

/-- The bytes apart from the frame and the working space, kept by the entry and the frame's filling. -/
theorem frame_keep {s : State} (A : CheckPrivateABI s) {m : Mem}
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.CheckPrivate.args s, wsSize Impl.Ffdh.X86.CheckPrivate.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem m) {p : Addr} {n : Nat}
    (hws : Region.Disjoint ⟨p, n⟩ ⟨wsBase Impl.Ffdh.X86.CheckPrivate.args s, wsSize Impl.Ffdh.X86.CheckPrivate.args s⟩)
    (hb : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p n = Spec.Rsa.bytesAt s.mem p n := by
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega_using [low, st'])
  exact frame_bytes Ft (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hws
    · exact (hb.sub_left (by rw [FA]; exact Offset.sub_below _ (by decide) (by decide))).symm) hn

/-- The status the contract asks for, for a valid domain. -/
abbrev spec (s : State) : Nat :=
  Spec.Ffdh.privateStatus (Spec.Ffdh.domainOf (arg s 2).toNat (entryDom s)) (Spec.Rsa.os2ip (entryY s))
    (Spec.Rsa.os2ip (entryX s))

/-- The body, from the frame's state. -/
theorem frame_ok {s : State} (A : CheckPrivateABI s) (f : State)
    (I : In (Rd s) (wsBase Impl.Ffdh.X86.CheckPrivate.args s) (wsSize Impl.Ffdh.X86.CheckPrivate.args s)
      (pLenOf Impl.Ffdh.X86.CheckPrivate.args s) (synth Impl.Ffdh.X86.CheckPrivate.args (arg s)) f)
    (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.CheckPrivate.args s, wsSize Impl.Ffdh.X86.CheckPrivate.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem f.mem) :
    WP isa Impl.Ffdh.X86.CheckPrivate.body f fun t =>
      (Spec.Ffdh.domainValid (arg s 2).toNat (entryDom s) = true → (t.gpr .eax).toNat = spec s) ∧
      Frame ([] ++ CrtRt.frameR (wsBase Impl.Ffdh.X86.CheckPrivate.args s) (f.gpr .esp)
        (fR (pLenOf Impl.Ffdh.X86.CheckPrivate.args s))) f.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t := by
  obtain ⟨G, Y, X, hb40, hy40, hx40⟩ := frame_geo A espf I.extra
  have D : domBytes f.mem (synth Impl.Ffdh.X86.CheckPrivate.args (arg s)) (arg s 1).toNat = entryDom s :=
    frame_keep A Ft A.domScratch A.belowDom (by have := A.domBound; omega_using [])
  have Yv : yv f.mem (synth Impl.Ffdh.X86.CheckPrivate.args (arg s)) (pLenOf Impl.Ffdh.X86.CheckPrivate.args s) =
      Spec.Rsa.os2ip (entryY s) := by
    have yR : (arg s 4).toNat = pLenOf Impl.Ffdh.X86.CheckPrivate.args s := A.yLen
    show Spec.Rsa.os2ip (Spec.Rsa.bytesAt f.mem (argumentPointer s 3) _) = _
    rw [← yR]
    exact congrArg _ (frame_keep A Ft A.yScratch A.belowY (by have := A.yBound; omega_using []))
  have Xv : xv f.mem (synth Impl.Ffdh.X86.CheckPrivate.args (arg s)) (arg s 6).toNat = Spec.Rsa.os2ip (entryX s) :=
    congrArg _ (frame_keep A Ft A.xScratch A.belowX (by have := A.xBound; omega_using []))
  refine WP.mono (body_ok I G Y X hb40 hy40 hx40)
    fun t ⟨r, ⟨E, F, K⟩, V⟩ => ⟨fun v => ?_, by rw [List.nil_append]; exact F, K⟩
  rw [show pLenOf Impl.Ffdh.X86.CheckPrivate.args s = (arg s 2).toNat from rfl] at V Yv
  rw [D] at V
  rw [E, V v, expected, params, D, Yv, Xv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  unfold Spec.Ffdh.privateStatus
  split
  · decide
  · split <;> decide

theorem operation_ok {s : State} (A : CheckPrivateABI s) :
    WP isa Impl.Ffdh.X86.CheckPrivate.code s fun u =>
      (Spec.Ffdh.domainValid (arg s 2).toNat (entryDom s) = true → (u.gpr .eax).toNat = spec s) ∧
        abiPreserved s u := by
  have hx : Rd s s.rd (⟨frameAt s, argsFrame⟩ :: s.wr) := by
    show InRegions (s.rd ++ _) _ _ ∧ InRegions (s.rd ++ _) _ _ ∧ InRegions (s.rd ++ _) _ _
    rw [A.rd]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.contains_self _ _⟩⟩
  exact wrap_ok (wrapABI A) (NoSp.of_all frameBody_all) hx (Out := []) (fun _ h => by cases h)
    (fun _ h => by cases h)
    (P := fun _ e => Spec.Ffdh.domainValid (arg s 2).toNat (entryDom s) = true → e.toNat = spec s)
    (hP := fun _ _ _ _ h => h)
    fun f I espf Ft => frame_ok A f I espf Ft

end VG.Proof.Ffdh.X86.CheckPrivate

end

end

/-!
# `vg_ffdh_check_private` on i686 in time that depends on the domain, y and the status only

The contract releases the domain, y and the status: runs with the same
ones leak the same traces. The one branch on x, whether it is an invalid
scalar, is whether the status is 2 (`privateValid`, which the code tests
for any domain); the rest, x's power and its comparison with y, is masked.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.CheckPrivate

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Proof.Ffdh.X86.CheckDomain (DomAt)
open VG.Proof.Ffdh.X86.CheckPublic (PubAt YGeo yv loadY_ok)
open VG.Impl.Ffdh.X86 (argsFrame ret testMask)

/-! ## The taint checks -/

theorem loads_check : ACheck (Prog.chain [Impl.Ffdh.X86.pSetup, load (.slot .wide 10) (one .wide) 4 5,
    load (.slot .wide 12) (one .wide) 8 9, load (.slot .wide 13) (one .wide) 10 11] (.block [])) := by
  dsimp only [ACheck]; taint_decide
theorem noQ_check : ACheck (.seq (copy (.slot .wide 15) (.slot .wide 16) (one .wide))
    (.seq (lessThan (.slot .wide 13) (.slot .wide 9) (one .wide)) (.block [.store (sc accOff) .ecx]))) := by
  dsimp only [ACheck]; taint_decide
theorem withQ_check : ACheck (.seq (load (.slot .wide 16) (one .wide) 6 7)
    (.block [.mov .ecx (.imm 0xFFFFFFFF), .store (sc accOff) .ecx])) := by
  dsimp only [ACheck]; taint_decide
theorem mask_check : ACheck (Prog.chain [Impl.Ffdh.X86.CheckPrivate.scalarMask, Impl.Ffdh.X86.testMask]
    (.block [])) := by
  dsimp only [ACheck]; taint_decide
theorem ret2_check : ACheck (ret 2) := by dsimp only [ACheck]; taint_decide
theorem range_check : ACheck (Impl.Ffdh.X86.rangeMask 12) := by dsimp only [ACheck]; taint_decide
theorem store_check : ACheck (.block [.store (sc accOff) .ecx]) := by dsimp only [ACheck]; taint_decide
theorem topLoads_check : ACheck (Prog.chain [copy (.slot .wide 10) (.slot .wide 5) (one .wide),
    loadTop (.slot .wide 8) (one .wide) 10 11] (.block [])) := by dsimp only [ACheck]; taint_decide
theorem count_check : ACheck (.block (lenCount 11)) := by dsimp only [ACheck]; taint_decide
theorem tail_check : ACheck (.seq (equal (.slot .wide 6) (.slot .wide 12) (one .wide))
    (.seq (.block [.alu .and .ecx (.mem (sc accOff))]) Impl.Ffdh.X86.retMask)) := by
  dsimp only [ACheck]; taint_decide
theorem fill_check :
    (VG.Taint.check taint (τr [.esp]) (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.CheckPrivate.args)) (.block [])).isSome =
      true := by
  taint_decide

/-! ## The runs of the body -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len dlen xl : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32} {D Yb : List Byte} {St : Nat}

/-- A run of the body, with the domain `D`, y's bytes `Yb`, and the status `St`. -/
structure PrivAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen xl : Nat)
    (args : Nat → BitVec 32) (sp : BitVec 32) (D Yb : List Byte) (St : Nat) (u : State) : Prop where
  pub : PubAt Ex base bytes len dlen args sp D Yb u
  geo : XGeo args base bytes len xl u.rd u.wr
  hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below sp 96)
  st : Spec.Ffdh.privateStatus (Spec.Ffdh.domainOf len D) (Spec.Rsa.os2ip Yb) (xv u.mem args xl) = St

theorem status_two {a : Spec.Ffdh.Parameters} {y x : Nat} :
    Spec.Ffdh.privateStatus a y x = 2 ↔ Spec.Ffdh.privateValid a x = false := by
  unfold Spec.Ffdh.privateStatus
  cases Spec.Ffdh.privateValid a x
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, iff_false]
    split <;> decide

/-- A run, with x's geometry. -/
abbrev RX (Ex : List Region → List Region → Prop) (base : Addr) (bytes len xl : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (u : State) : Prop :=
  Run Ex base bytes len args sp u ∧ XGeo args base bytes len xl u.rd u.wr

/-- x's power: p's context by `ctxP_relCT`, the copy and x's load by the taint analysis, and the power
over x's `xl` bytes by private CRT's windowed power. -/
theorem powTop_trace (hx : args 11 = BitVec.ofNat 32 xl ∧ 0 < xl ∧ xl ≤ 1024)
    (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below sp 96)) :
    RelCT isa (Both (RX Ex base bytes len xl args sp)) (Impl.Ffdh.X86.powTop 10)
      (Both (Run Ex base bytes len args sp)) := by
  rw [powTop_eq]
  apply VG.RelCT.chain
  refine VG.RelCT.seq (VG.Proof.Bignum.X86.PublicRt.relCT_both (F := WSt Ex base bytes len args sp .wide [3, 4] 0)
    ((VG.RelCT.seq (ctxP_relCT.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
      (RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2) topLoads_check))) fun x ⟨R, X⟩ => ?_) ?_
  · refine WP.mono (topFront_ok R.1 X (by rw [R.2.2]; exact hx40) (b := 10) (by decide) (by decide) rfl)
      fun u ⟨C, one, R4, _, _, _, _, K⟩ =>
      ⟨_, C, fun j hj => ?_, fun j hj => absurd hj (Nat.not_lt_zero _), R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩
    have hM := safeM_gt (sv x.mem base len .wide 9)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · rw [one]; exact hM
    · rw [R4]; exact Nat.mod_lt _ (by omega_using [hM])
  · exact (windowPowerWith_relCT (winChecks .wide) (N := 2 * xl) (by omega_using [hx]) (by omega_using [hx]) count_check
      fun _ W => lenCount_wst (by decide) hx.1 W).mono (fun _ _ h => h) fun _ _ h => ⟨WSt.run h.1, WSt.run h.2⟩

theorem pair_trace {P : State → Prop}
    (hP : ∀ x, P x → RX Ex base bytes len xl args sp x ∧ Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below sp 96)) :
    RelCT isa (Both P) Impl.Ffdh.X86.CheckPrivate.pair fun _ _ => True := by
  by_cases hx : (args 11 = BitVec.ofNat 32 xl ∧ 0 < xl ∧ xl ≤ 1024) ∧
    Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below sp 96)
  swap
  · refine VG.RelCT.of_false fun s₁ _ h => hx ?_
    obtain ⟨⟨R, X⟩, d⟩ := hP _ h.1
    exact ⟨⟨X.e11, X.pos, by have := X.le; have := R.1.upper'; omega_arith⟩, d⟩
  unfold Impl.Ffdh.X86.CheckPrivate.pair
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  refine VG.RelCT.seq (aRel (F := fun v => RX Ex base bytes len xl args sp v ∧ ∃ c, v.gpr .ecx = cmask c)
    (fun x h => (hP x h).1.1) range_check fun x R => ?_) ?_
  · obtain ⟨⟨R, X⟩, _⟩ := hP x R
    exact WP.mono (rangeMask_ok R.1 (a := 12) (by decide)) fun v ⟨_, e, O, K⟩ =>
      ⟨⟨run_step R (Step.word R.1 (by decide) O K), X.keep ⟨rfl, rfl⟩ K⟩, _, e⟩
  refine VG.RelCT.seq (aRel (F := RX Ex base bytes len xl args sp) (fun _ h => h.1.1) store_check
    fun x ⟨⟨R, X⟩, c, e⟩ => WP.mono (storeMask_ok R.1 (d := accOff) (by omega_using [ao, nb]) e) fun v ⟨_, O, _, _, K⟩ =>
      ⟨run_step R (Step.word R.1 (by omega_using [ao]) O K), X.keep ⟨rfl, rfl⟩ K⟩) ?_
  exact VG.RelCT.seq (powTop_trace hx.1 hx.2) (RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2) tail_check)

/-- A run, with the domain's geometry. -/
def RG (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (u : State) : Prop :=
  Run Ex base bytes len args sp u ∧ DomGeo args base bytes len dlen u.rd u.wr

theorem loads_rg {x : State} (A : PrivAt Ex base bytes len dlen xl args sp D Yb St x) :
    WP isa (Prog.chain [Impl.Ffdh.X86.pSetup, load (.slot .wide 10) (one .wide) 4 5,
      load (.slot .wide 12) (one .wide) 8 9, load (.slot .wide 13) (one .wide) 10 11] (.block [])) x
      (RG Ex base bytes len dlen args sp) := by
  have h := A.pub.dom.run.1
  have G := A.pub.dom.geo
  have dl := G.dl
  have fit := G.fit
  have lw := G.lower
  refine WP.seq (WP.mono (pSetup_ok h G.e3 (by omega_using [dl, fit])
    (by have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega_using [dl]) (by omega_using [fit])
        rwa [BitVec.add_zero] at this)
    (G.apart.sub_left (Region.sub_prefix (by omega_using [dl]))))
    fun u₁ ⟨I₁, F₁, _, _, _, _, K₁⟩ => ?_)
  have S₁ : Step Ex base bytes len args x u₁ := ⟨I₁, F₁, K₁⟩
  refine WP.seq (WP.mono (loadComp_ok I₁ (G.keep ⟨rfl, rfl⟩ K₁) (k := 1) (j := 10) (by decide) (by omega_using [dl])
    (by decide)) fun u₂ ⟨_, O₂, K₂⟩ => ?_)
  have S₂ := S₁.trans (Step.slot I₁ (by decide) O₂ K₂)
  refine WP.seq (WP.mono (loadY_ok S₂.inp (A.pub.geo.keep ⟨rfl, rfl⟩ S₂.keeps)) fun u₃ ⟨_, O₃, K₃⟩ => ?_)
  have S₃ := S₂.trans (Step.slot S₂.inp (by decide) O₃ K₃)
  refine WP.seq (WP.mono (loadX_ok S₃.inp (A.geo.keep ⟨rfl, rfl⟩ S₃.keeps)) fun u₄ ⟨_, O₄, K₄⟩ => WP.block_nil ?_)
  have S₄ := S₃.trans (Step.slot S₃.inp (by decide) O₄ K₄)
  exact ⟨run_step A.pub.dom.run S₄, G.keep ⟨rfl, rfl⟩ S₄.keeps⟩

theorem bound_relCT :
    RelCT isa (Both (RG Ex base bytes len dlen args sp)) Impl.Ffdh.X86.CheckPrivate.bound
      (Both (Run Ex base bytes len args sp)) := by
  refine VG.Proof.Bignum.X86.PublicRt.relCT_both ?_ fun x R =>
    WP.mono (bound_ok R.1.1 R.2 rfl rfl rfl (fun _ => rfl)) fun v ⟨S, _⟩ => run_step R.1 S
  unfold Impl.Ffdh.X86.CheckPrivate.bound
  refine VG.RelCT.seq (aRel (F := fun u => RG Ex base bytes len dlen args sp u ∧ Gate u (dlen = 2 * len))
    (fun _ R => R.1) VG.Proof.Ffdh.X86.CheckDomain.qTest_check fun x R =>
      WP.mono (qTest_ok R.1.1 R.2.e3 R.2.e12 R.2.dl) fun u ⟨z, m, K⟩ =>
        ⟨⟨run_step R.1 (Step.regs R.1.1 m K), R.2.keep ⟨rfl, rfl⟩ K⟩, Gate.of_eval z decide_eq_true_iff⟩) ?_
  exact gate_relCT (fun _ h => h.2) (aEnd (fun _ h => h.1.1.1) noQ_check) (aEnd (fun _ h => h.1.1.1) withQ_check)

theorem front_trace :
    RelCT isa (Both (PrivAt Ex base bytes len dlen xl args sp D Yb St)) (Prog.chain privFront (.block []))
      fun _ _ => True := by
  show RelCT isa _ (Prog.chain [Impl.Ffdh.X86.pSetup, load (.slot .wide 10) (one .wide) 4 5,
    load (.slot .wide 12) (one .wide) 8 9, load (.slot .wide 13) (one .wide) 10 11]
    (.seq Impl.Ffdh.X86.CheckPrivate.bound
      (Prog.chain [Impl.Ffdh.X86.CheckPrivate.scalarMask, Impl.Ffdh.X86.testMask] (.block [])))) _
  apply VG.RelCT.chain
  refine VG.RelCT.seq (aRel (fun _ A => A.pub.dom.run) loads_check fun _ A => loads_rg A) ?_
  exact VG.RelCT.seq bound_relCT (aEnd (fun _ h => h) mask_check)

theorem body_relCT :
    RelCT isa (Both (PrivAt Ex base bytes len dlen xl args sp D Yb St)) Impl.Ffdh.X86.CheckPrivate.body
      fun _ _ => True := by
  rw [body_eq]
  apply VG.RelCT.chain
  refine VG.RelCT.seq (VG.Proof.Bignum.X86.PublicRt.relCT_both
    (F := fun u => (RX Ex base bytes len xl args sp u ∧ Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below sp 96)) ∧
      Gate u (St = 2)) front_trace fun x A => ?_) ?_
  · refine WP.mono (front_ok A.pub.dom.run.1 A.pub.dom.geo A.pub.geo A.geo
      (by rw [A.pub.dom.run.2.2]; exact A.pub.dom.hb40) (by rw [A.pub.dom.run.2.2]; exact A.pub.hy40)
      (by rw [A.pub.dom.run.2.2]; exact A.hx40)) fun u ⟨S, G, _⟩ =>
      ⟨⟨⟨run_step A.pub.dom.run S, A.geo.keep ⟨rfl, rfl⟩ S.keeps⟩, A.hx40⟩, G.congr ?_⟩
    rw [← A.st, status_two, params, A.pub.dom.dom]
  · exact gate_relCT (fun _ h => h.2) (aEnd (fun _ h => h.1.1.1.1) ret2_check) (pair_trace fun _ h => h.1.1)

end

/-! ## Against the contract -/

theorem pub_facts {s t : State} (H : (Spec.Ffdh.checkPrivateContract abi stack).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ (∀ i < 9, arg s i = arg t i) ∧ entryDom s = entryDom t ∧ entryY s = entryY t ∧
      spec s = spec t := by
  sig_pub [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨SP, L, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := H
  have inj : ∀ {l l' : List Byte}, l.map (fun x => x.toNat) = l'.map (fun x => x.toNat) → l = l' :=
    fun h => (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp h
  obtain ⟨L₁, L₃⟩ := List.append_inj L (by simp [Spec.Rsa.bytesAt, a1, a4])
  obtain ⟨L₁, L₂⟩ := List.append_inj L₁ (by simp [Spec.Rsa.bytesAt, a1])
  refine ⟨SP, fun i hi => ?_, inj L₁, inj L₂, List.cons.inj L₃ |>.1⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by omega_using [hi])
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a0
  · exact a1
  · exact a2
  · exact a3
  · exact a4
  · exact a5
  · exact a6
  · exact a7
  · exact a8

theorem narrowRd {s : State} {rd wr : List Region} (h : Rd s rd wr) (x : Region) : Rd s (rd ++ wr) [x] :=
  let ⟨⟨r, hr, hc⟩, ⟨r', hr', hc'⟩, ⟨r'', hr'', hc''⟩⟩ := h
  ⟨⟨r, List.mem_append_left _ hr, hc⟩, ⟨r', List.mem_append_left _ hr', hc'⟩, ⟨r'', List.mem_append_left _ hr'', hc''⟩⟩

/-- The narrowed state the body runs from: a run with the domain, y and the status at entry. -/
theorem privAt_of {s f : State} (A : CheckPrivateABI s)
    (Bf : BodyAt (Rd s) Impl.Ffdh.X86.CheckPrivate.args s f) :
    PrivAt (Rd s) (wsBase Impl.Ffdh.X86.CheckPrivate.args s) (wsSize Impl.Ffdh.X86.CheckPrivate.args s)
      (pLenOf Impl.Ffdh.X86.CheckPrivate.args s) (arg s 1).toNat (arg s 6).toNat
      (synth Impl.Ffdh.X86.CheckPrivate.args (arg s)) (s.gpr .esp - BitVec.ofNat 32 argsFrame) (entryDom s)
      (entryY s) (spec s)
      (narrowed (wsBase Impl.Ffdh.X86.CheckPrivate.args s) (wsSize Impl.Ffdh.X86.CheckPrivate.args s) f) := by
  have hx := narrowRd Bf.1.extra ⟨wsBase Impl.Ffdh.X86.CheckPrivate.args s, wsSize Impl.Ffdh.X86.CheckPrivate.args s⟩
  obtain ⟨G, Y, X, hb, hy, hxx⟩ := frame_geo A (sp := s.gpr .esp - BitVec.ofNat 32 argsFrame) rfl hx
  have yR : (arg s 4).toNat = pLenOf Impl.Ffdh.X86.CheckPrivate.args s := A.yLen
  refine ⟨⟨⟨⟨VG.Proof.Ffdh.X86.In.narrow Bf.1 hx, Bf.argsOk (wrapABI A), Bf.2.1⟩, G, hb,
    frame_keep A Bf.2.2.2.2 A.domScratch A.belowDom (by have := A.domBound; omega_using [])⟩, Y, hy, ?_⟩, X, hxx, ?_⟩
  · show Spec.Rsa.bytesAt f.mem (argumentPointer s 3) _ = Spec.Rsa.bytesAt s.mem (argumentPointer s 3) (arg s 4).toNat
    rw [← yR]
    exact frame_keep A Bf.2.2.2.2 A.yScratch A.belowY (by have := A.yBound; omega_using [])
  · show Spec.Ffdh.privateStatus _ _ (Spec.Rsa.os2ip (Spec.Rsa.bytesAt f.mem (argumentPointer s 5) _)) = _
    rw [frame_keep A Bf.2.2.2.2 A.xScratch A.belowX (by have := A.xBound; omega_using [])]
    rfl

theorem constantTime : ConstantTime isa (Spec.Ffdh.checkPrivateContract abi stack).pre
    (Spec.Ffdh.checkPrivateContract abi stack).pub Impl.Ffdh.X86.CheckPrivate.code := by
  intro s t tr ur sf tf S T H E F
  have A := checkPrivateABI_of S
  have B := checkPrivateABI_of T
  obtain ⟨SP, args, dom, yb, st⟩ := pub_facts H
  have hws : wsBase Impl.Ffdh.X86.CheckPrivate.args s = wsBase Impl.Ffdh.X86.CheckPrivate.args t := by
    show (arg s 7).setWidth 64 = (arg t 7).setWidth 64
    rw [args 7 (by decide)]
  have hwz : wsSize Impl.Ffdh.X86.CheckPrivate.args s = wsSize Impl.Ffdh.X86.CheckPrivate.args t := by
    show (arg s 8).toNat * 8 = (arg t 8).toNat * 8
    rw [args 8 (by decide)]
  have hpl : pLenOf Impl.Ffdh.X86.CheckPrivate.args s = pLenOf Impl.Ffdh.X86.CheckPrivate.args t := by
    show (arg s 2).toNat = (arg t 2).toNat
    rw [args 2 (by decide)]
  have hsy : synth Impl.Ffdh.X86.CheckPrivate.args (arg t) = synth Impl.Ffdh.X86.CheckPrivate.args (arg s) :=
    synth_congr (wrapABI A).below fun i hi => (args i hi).symm
  have hRd : Rd t = Rd s := by
    show (fun rd wr => InRegions (rd ++ wr) ((arg t 0).setWidth 64) (arg t 1).toNat ∧
        InRegions (rd ++ wr) ((arg t 3).setWidth 64) (arg t 4).toNat ∧
        InRegions (rd ++ wr) ((arg t 5).setWidth 64) (arg t 6).toNat) =
      fun rd wr => InRegions (rd ++ wr) ((arg s 0).setWidth 64) (arg s 1).toNat ∧
        InRegions (rd ++ wr) ((arg s 3).setWidth 64) (arg s 4).toNat ∧
        InRegions (rd ++ wr) ((arg s 5).setWidth 64) (arg s 6).toNat
    rw [args 0 (by decide), args 1 (by decide), args 3 (by decide), args 4 (by decide), args 5 (by decide),
      args 6 (by decide)]
  have hl : (arg t 1).toNat = (arg s 1).toNat := by rw [args 1 (by decide)]
  have hl6 : (arg t 6).toNat = (arg s 6).toNat := by rw [args 6 (by decide)]
  have hx : ∀ {x : State}, CheckPrivateABI x → Rd x x.rd (⟨frameAt x, argsFrame⟩ :: x.wr) := fun {x} X => by
    show InRegions (x.rd ++ _) _ _ ∧ InRegions (x.rd ++ _) _ _ ∧ InRegions (x.rd ++ _) _ _
    rw [X.rd]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.contains_self _ _⟩⟩
  have hw : ∀ {x f : State} (X : CheckPrivateABI x) (Bf : BodyAt (Rd x) Impl.Ffdh.X86.CheckPrivate.args x f),
      ∃ F, WP isa Impl.Ffdh.X86.CheckPrivate.body
        (narrowed (wsBase Impl.Ffdh.X86.CheckPrivate.args x) (wsSize Impl.Ffdh.X86.CheckPrivate.args x) f) F :=
    fun X Bf => ⟨_, body_ok (privAt_of X Bf).pub.dom.run.1 (privAt_of X Bf).pub.dom.geo (privAt_of X Bf).pub.geo
      (privAt_of X Bf).geo
      (by rw [(privAt_of X Bf).pub.dom.run.2.2]; exact (privAt_of X Bf).pub.dom.hb40)
      (by rw [(privAt_of X Bf).pub.dom.run.2.2]; exact (privAt_of X Bf).pub.hy40)
      (by rw [(privAt_of X Bf).pub.dom.run.2.2]; exact (privAt_of X Bf).hx40)⟩
  refine wrap_trace (wrapABI A) (wrapABI B) args SP (hx A) (hx B) fill_check
    (fun f Bf => WP.mono (frame_ok A f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (fun f Bf => WP.mono (frame_ok B f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (narrow_body hws hwz (fun f Bf => hw A Bf) (fun g Bg => hw B Bg)
      (fun f g Bf Bg => ⟨privAt_of A Bf, ?_⟩) body_relCT) E F
  have D₂ := privAt_of B Bg
  rw [hRd, ← hws, ← hwz, ← hpl, hsy, hl, hl6, ← SP, ← dom, ← yb, ← st] at D₂
  rw [← hws, ← hwz]
  exact D₂

end VG.Proof.Ffdh.X86.CheckPrivate
