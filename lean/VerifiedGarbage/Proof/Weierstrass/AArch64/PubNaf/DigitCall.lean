module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.DigitCall
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointFinish
import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.PubNaf
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64 Spec.Weierstrass

/-- Rebase a loop invariant after changing registers and its ghost origin. -/
theorem NSt.rebaseGpr {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} {P : Point C}
    {o s o' t : State} (h : NSt K C base size P o s) {rs : List Reg}
    (kt : KeepRegs rs s t) (h0 : Reg.x0 ∉ rs) (hm : t.mem = s.mem) (ho : o'.mem = o.mem)
    (ko : KeepRegs (nafClob K.M.n) o' t) : NSt K C base size P o' t := by
  refine ⟨h.scr.of_keepRegs kt h0, ko, ?_, ?_, ?_⟩
  · simpa only [hm, ho] using h.unch
  · simpa only [hm] using h.mod
  · simpa only [OddTbl, tmv, hm] using h.tbl

/-- Calling a digit body preserves its loop contract, including the outer link. -/
theorem callDigits_wp {K : WinCfg} {C : Curve} {base : Addr} {size j : Nat} {P A B : Point C}
    {o s : State} {body : Prog isa} (name : String)
    (h30 : Reg.x30 ∉ nafClob K.M.n)
    (hlinks : ∀ r, r ∉ nafClob K.M.n → r ≠ .x30 → r ∉ linkRegs)
    (hv : ∀ i ∈ instrs body, vdstOf i ≠ some .v31)
    (raw : ∀ (g : Reg → BitVec 64) (a : State), a.syms = o.syms →
      JointDoublePost K C base size P {o with gpr := g} a j A →
      WP isa body a (fun t => JointDigitPost K C base size P {o with gpr := g} t j B))
    (sym : s.syms = o.syms) (h : JointDoublePost K C base size P o s j A) :
    WP isa (callDigits name body) s (fun t => JointDigitPost K C base size P o t j B) := by
  unfold callDigits
  refine WP.seq (WP.mono_syms (insOf_ok [(.x30, .v31, 1)] s (by simp) (by decide)) fun a ⟨ag, am, ard, awr, asp, alane, _⟩ asy => ?_)
  let g : Reg → BitVec 64 := fun r => if r = .x30 then a.callEntry.gpr .x30 else o.gpr r
  have ka : KeepRegs linkRegs s a.callEntry :=
    ⟨fun r hr => (State.callEntry_gpr a hr).trans (congrFun ag r), ard, awr, asp⟩
  have ko : KeepRegs (nafClob K.M.n) {o with gpr := g} a.callEntry := by
    refine ⟨fun r hr => ?_, ard.trans h.st.keep.rd, awr.trans h.st.keep.wr, asp.trans h.st.keep.sp⟩
    by_cases he : r = .x30
    · subst r; rfl
    · change a.callEntry.gpr r = g r
      rw [ka.gpr r (hlinks r hr he), h.st.keep.gpr r hr]
      simp only [g, ite_eq_right he]
  have pre : JointDoublePost K C base size P {o with gpr := g} a.callEntry j A := by
    refine ⟨h.st.rebaseGpr ka (by decide) am rfl ko, ?_, ?_, ?_, ?_⟩
    · rw [ka.gpr .x19 (by decide)]; exact h.x19
    · simpa only [State.callEntry_mem, am] using h.dlt
    · simpa only [tmv, State.callEntry_mem, am] using h.d
    · exact CacheUpTo.ofMem am h.cache
  have sy : a.callEntry.syms = o.syms := asy.trans sym
  obtain ⟨tr, t, et, post⟩ := raw g a.callEntry sy pre
  have keep31 := Exec.vec hv et
  have ret : isa.ret a.callEntry t = some t := by
    simp only [isa, VG.AArch64.ret, post.st.keep.gpr .x30 h30, g, ite_true]
  refine WP.seq (show WP isa (.call name body) a _ from ⟨_, t, Exec.call (call_callEntry a) et ret, ?_⟩)
  refine WP.mono (umovOf_ok [(.x30, .v31, 1)] t (by simp) (by decide)) fun z ⟨zm, zrd, zwr, zsp, zl, zg⟩ => ?_
  have kz : KeepRegs [.x30] t z := ⟨fun r hr => zg r hr, zrd, zwr, zsp⟩
  have koz : KeepRegs (nafClob K.M.n) o z := by
    refine ⟨fun r hr => ?_, zrd.trans post.st.keep.rd, zwr.trans post.st.keep.wr, zsp.trans post.st.keep.sp⟩
    by_cases he : r = .x30
    · subst r
      rw [zl (.x30, .v31, 1) (by simp)]
      change laneOf t .v31 1 = _
      rw [laneOf, keep31]
      exact (alane (.x30, .v31, 1) (by simp)).trans (h.st.keep.gpr .x30 h30)
    · rw [zg r (by simpa using he), post.st.keep.gpr r hr]
      simp only [g, ite_eq_right he]
  refine ⟨post.st.rebaseGpr kz (by decide) zm rfl koz, ?_, ?_, ?_, ?_⟩
  · rw [zg .x19 (by decide)]; exact post.x19
  · simpa only [zm] using post.rlt
  · simpa only [tmv, zm] using post.r
  · exact CacheUpTo.ofMem zm post.cache

/-- The concrete states of the link-save and restore instructions. -/
def savedDigitLink (s : State) : State := s.setV .v31 (setLane (s.v .v31) 64 1 (s.gpr .x30))
def restoredDigitLink (s : State) : State := s.write .x .x30 (laneOf s .v31 1)

theorem savedDigitLink_exec (s : State) :
    Exec isa (.block [.vop (.ins .d2 .v31 1 .x30)]) s [] (savedDigitLink s) := by
  apply Exec.block
  simp only [execBlock, isa, exec_ins (s := s) (r := .x30) (v := .v31) (l := 1) (by decide)]
  rfl

theorem restoredDigitLink_exec (s : State) :
    Exec isa (.block [.umov .x .x30 .v31 1]) s [] (restoredDigitLink s) := by
  apply Exec.block
  simp only [execBlock, isa, exec_umov (s := s) (r := .x30) (v := .v31) (l := 1) (by decide)]
  rfl

/-- The ghost origin records the called body's return token. -/
def digitOrigin (o s : State) : State :=
  {o with gpr := fun r => if r = .x30 then (savedDigitLink s).callEntry.gpr .x30 else o.gpr r}

theorem digitCall_pre {K : WinCfg} {C : Curve} {base : Addr} {size j : Nat} {P A : Point C}
    {o s : State} (hlinks : ∀ r, r ∉ nafClob K.M.n → r ≠ .x30 → r ∉ linkRegs)
    (h : JointDoublePost K C base size P o s j A) :
    JointDoublePost K C base size P (digitOrigin o s) (savedDigitLink s).callEntry j A := by
  have ka : KeepRegs linkRegs s (savedDigitLink s).callEntry :=
    ⟨fun r hr => State.callEntry_gpr _ hr, rfl, rfl, rfl⟩
  have ko : KeepRegs (nafClob K.M.n) (digitOrigin o s) (savedDigitLink s).callEntry := by
    refine ⟨fun r hr => ?_, h.st.keep.rd, h.st.keep.wr, h.st.keep.sp⟩
    by_cases he : r = .x30
    · subst r; rfl
    · rw [ka.gpr r (hlinks r hr he), h.st.keep.gpr r hr]
      simp only [digitOrigin, ite_eq_right he]
  exact ⟨h.st.rebaseGpr ka (by decide) rfl rfl ko,
    (ka.gpr .x19 (by decide)).trans h.x19, h.dlt, h.d, h.cache⟩

theorem _root_.VG.Proof.Weierstrass.AArch64.FieldPair.digitSaved {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {s t : State}
    (h : FieldPair M base size m Sl V E s t) :
    FieldPair M base size m Sl V E (savedDigitLink s).callEntry (savedDigitLink t).callEntry :=
  ⟨⟨⟨(State.callEntry_gpr _ (by decide)).trans h.left.scr.x0, h.left.scr.wr, h.left.scr.nowrap, h.left.scr.enc⟩,
      h.left.mod, h.left.sl, h.left.lt, h.left.val⟩,
    ⟨⟨(State.callEntry_gpr _ (by decide)).trans h.right.scr.x0, h.right.scr.wr, h.right.scr.nowrap, h.right.scr.enc⟩,
      h.right.mod, h.right.sl, h.right.lt, h.right.val⟩, h.sp⟩

theorem _root_.VG.Proof.Weierstrass.AArch64.FieldPair.digitRestored {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {s t : State}
    (h : FieldPair M base size m Sl V E s t) :
    FieldPair M base size m Sl V E (restoredDigitLink s) (restoredDigitLink t) :=
  ⟨⟨⟨h.left.scr.x0, h.left.scr.wr, h.left.scr.nowrap, h.left.scr.enc⟩,
      h.left.mod, h.left.sl, h.left.lt, h.left.val⟩,
    ⟨⟨h.right.scr.x0, h.right.scr.wr, h.right.scr.nowrap, h.right.scr.enc⟩,
      h.right.mod, h.right.sl, h.right.lt, h.right.val⟩, h.sp⟩

/-- The link-save, call and restore add no leakage to the digit body's trace. -/
theorem callDigits_relCT {body : Prog isa} {P Q : State → State → Prop} (name : String)
    (raw : RelCT isa P body Q) :
    RelCT isa (fun s t => P (savedDigitLink s).callEntry (savedDigitLink t).callEntry)
      (callDigits name body)
      (fun s t => ∃ a b, Q a b ∧ s = restoredDigitLink a ∧ t = restoredDigitLink b) := by
  intro s t ts tt s' t' pre es et
  cases es with
  | seq ss sc => cases et with
    | seq st tc =>
      obtain ⟨rfl, rfl⟩ := Exec.det ss (savedDigitLink_exec s)
      obtain ⟨rfl, rfl⟩ := Exec.det st (savedDigitLink_exec t)
      cases sc with
      | seq cs rs => cases tc with
        | seq ct rt =>
          cases cs with
          | call ce bs re => cases ct with
            | call cf bt rf =>
              rw [call_callEntry, Option.some.injEq] at ce cf
              subst ce cf
              change (if _ then some _ else none) = some _ at re rf
              obtain ⟨_, he⟩ := Option.ite_none_right_eq_some.mp re
              obtain ⟨_, hf⟩ := Option.ite_none_right_eq_some.mp rf
              cases Option.some.inj he
              cases Option.some.inj hf
              obtain ⟨rfl, rfl⟩ := Exec.det rs (restoredDigitLink_exec _)
              obtain ⟨rfl, rfl⟩ := Exec.det rt (restoredDigitLink_exec _)
              obtain ⟨ht, hq⟩ := raw _ _ _ _ _ _ pre bs bt
              exact ⟨by simpa only [isa, List.map_nil, List.nil_append, List.append_nil] using ht,
                _, _, hq, rfl, rfl⟩

end VG.Proof.Weierstrass.AArch64.PubNaf
