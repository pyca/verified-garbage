module

public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.P521.AArch64.Law
public import VerifiedGarbage.Spec.Ecdh.P521
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeExchange
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeFront
public meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeFront
public meta import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.Lit
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Fn
public meta import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Reduce
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.Lit

/-! ### `Weierstrass.AArch64.P521Native.NativeVerified`, which only this module used -/

section

/-! ### `Weierstrass.AArch64.P521Native.TimingFront`, which only this module used -/

section

/-! ### `Weierstrass.AArch64.P521Native.TimingChecks`, which only this module used -/

section

/-! ### `Weierstrass.AArch64.P521Native.TimingDomain`, which only this module used -/

section

/-! Public scalar lanes remain known when an instruction changes another vector.
This proof-only domain keeps memory secret and checks every instruction. -/
@[expose] public section
namespace VG.AArch64.P521NativeTiming
abbrev Part := RegSet VReg × RegSet VReg
abbrev T := AArch64.Taint.T × Part
def get (q : Part) (b : Bool) : RegSet VReg := if b then q.2 else q.1
def empty : Part := (RegSet.empty,RegSet.empty)
def ofRegs (rs : List Reg) : T := (AArch64.Taint.ofRegs rs,empty)
def AgreeV (q : Part) (s t : State) : Prop := ∀ b v, v∈get q b →
 (s.v v).extractLsb' (64*b.toNat) 64=(t.v v).extractLsb' (64*b.toNat) 64
def Agree (q : T) (s t : State) : Prop := AArch64.Taint.Agree q.1 s t ∧ AgreeV q.2 s t
abbrev setV := VectorTaint.setV
def put (q : Part) (b : Bool) (v : VReg) (p : Bool) : Part :=
 if b then (q.1,setV q.2 v p) else (setV q.1 v p,q.2)
def both (q : Part) (v : VReg) (p : Bool) : Part := (setV q.1 v p,setV q.2 v p)
abbrev scalar := VectorTaint.scalar
def afterV (q : Part) (i : Instr) : Part :=
 match vdstOf i with
 | none => q
 | some d => (q.1.erase d,q.2.erase d)
def step (q : T) : Instr → Option T
 | .vop (.dup _ d n) => some (q.1,both q.2 d (AArch64.Taint.pub q.1 n))
 | .vop (.ins .d2 d k n) => if k<2 then some (q.1,put q.2 (k==1) d (AArch64.Taint.pub q.1 n)) else none
 | .umov .x d n k => if k<2 then some (AArch64.Taint.set q.1 d ((get q.2 (k==1)).mem n),q.2) else none
 | .ldrqTbl t .. => some (q.1,both q.2 t true)
 | i => (AArch64.Taint.step q.1 i).map (fun g=>(g,afterV q.2 i))

theorem extract_setLane (x : BitVec 128) (v : BitVec 64) {i j : Nat} (hi : i < 2) (hj : j < 2) :
    (setLane x 64 i v).extractLsb' (64 * j) 64 = if i = j then v else x.extractLsb' (64 * j) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl <;>
    rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl <;>
    simp only [setLane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
      hk, decide_true, Bool.true_and, ite_true, ite_false, Nat.mul_zero, Nat.mul_one,
      Nat.sub_zero, reduceCtorEq] <;>
    (have h1 : k < 128 := by omega_using [hk]
     have h2 : 64 + k < 128 := by omega_using [hk]
     have h3 : ¬ 64 + k < 64 := by omega_using []
     simp [h1, h2, h3, hk])

private theorem both_set {q : Part} {s t : State} (h : AgreeV q s t) (d : VReg) {p : Bool}
 {x y : BitVec 128} (hp : p=true → x=y) : AgreeV (both q d p) (s.setV d x) (t.setV d y) := by
 intro b v hv
 have hv' : v∈setV (get q b) d p := by cases b <;> exact hv
 unfold setV VectorTaint.setV at hv'
 by_cases he : p=true
 · simp only [he,ite_true,RegSet.mem_insert] at hv'
   rcases hv' with rfl | hv'
   · simp only [RegUpd.v_setV,ite_true,hp he]
   · by_cases vd : v=d
     · simp only [RegUpd.v_setV,vd,ite_true,hp he]
     · simp only [RegUpd.v_setV,vd,ite_false]; exact h b v hv'
 · simp only [he,Bool.false_eq_true,ite_false,RegSet.mem_erase] at hv'
   simp only [RegUpd.v_setV,hv'.1,ite_false]
   exact h b v hv'.2

private theorem ins_set {q : Part} {s t : State} (h : AgreeV q s t) (d : VReg) {p : Bool}
 {x y : BitVec 64} {k : Nat} (hk : k<2) (hp : p=true → x=y) :
 AgreeV (put q (k==1) d p) (s.setV d (setLane (s.v d) 64 k x)) (t.setV d (setLane (t.v d) 64 k y)) := by
 intro b v hv
 have hb : b.toNat<2 := by cases b <;> decide
 by_cases vd : v=d
 · subst v
   simp only [RegUpd.v_setV,ite_true,extract_setLane _ _ hk hb]
   by_cases kb : k=b.toNat
   · simp only [kb,ite_true]
     apply hp
     cases b <;> subst k <;> cases p <;>
       simp_all [put, get, setV, VectorTaint.setV, RegSet.mem_erase]
   · simp only [kb,ite_false]
     apply h b d
     rcases (by omega_using [hk] : k=0 ∨ k=1) with rfl | rfl <;> cases b <;>
       first | contradiction | exact hv
 · simp only [RegUpd.v_setV,vd,ite_false]
   apply h b v
   rcases (by omega_using [hk] : k=0 ∨ k=1) with rfl | rfl <;> cases b
   all_goals
     first
     | exact hv
     | have hv' : v∈setV (get q false) d p := hv
       unfold setV VectorTaint.setV at hv'; split at hv'
       · exact (RegSet.mem_insert.mp hv').resolve_left vd
       · exact (RegSet.mem_erase.mp hv').2
     | have hv' : v∈setV (get q true) d p := hv
       unfold setV VectorTaint.setV at hv'; split at hv'
       · exact (RegSet.mem_insert.mp hv').resolve_left vd
       · exact (RegSet.mem_erase.mp hv').2

private theorem ordinary_sound {q q' : T} {i : Instr} {s t s' t' : State}
 (h : Agree q s t) (hs : (AArch64.Taint.step q.1 i).map (fun g=>(g,afterV q.2 i))=some q')
 (es : exec i s=some s') (et : exec i t=some t') : addrs i s=addrs i t ∧ Agree q' s' t' := by
 obtain ⟨g,hg,rfl⟩ := Option.map_eq_some_iff.mp hs
 obtain ⟨a,hg'⟩ := AArch64.Taint.step_sound h.1 hg es et
 refine ⟨a,hg',?_⟩
 intro b v hv
 have facts : v∈get q.2 b ∧ vdstOf i≠some v := by
   cases hd : vdstOf i with
   | none =>
     have old : v∈get q.2 b := by simpa only [afterV,hd] using hv
     exact ⟨old,by intro h; cases h⟩
   | some d =>
     have hv' : v≠d ∧ v∈get q.2 b := by
       cases b <;> simpa only [afterV,hd,get,reduceCtorEq,ite_true,ite_false,RegSet.mem_erase] using hv
     exact ⟨hv'.2,by intro h; exact hv'.1 (Option.some.inj h).symm⟩
 rw [exec_vec facts.2 es,exec_vec facts.2 et]
 exact h.2 b v facts.1

theorem step_sound {q q' : T} {i : Instr} {s t s' t' : State}
 (h : Agree q s t) (hs : step q i=some q') (es : exec i s=some s') (et : exec i t=some t') :
 addrs i s=addrs i t ∧ Agree q' s' t' := by
 cases i with
 | vop op =>
   cases op <;> try exact ordinary_sound h hs es et
   case dup a d n =>
     simp only [step,Option.some.injEq] at hs; subst hs
     cases a <;> simp only [reduceExec,VOp.eval,Option.map_some,Option.some.injEq] at es et
     all_goals
       subst es; subst et
       exact ⟨rfl,⟨h.1.1,h.1.2⟩,both_set h.2 d (fun hp=>by rw [h.1.reg hp])⟩
   case ins a d k n =>
     cases a <;> try exact ordinary_sound h hs es et
     simp only [step] at hs
     split at hs <;> [skip; cases hs]
     rename_i hk
     cases hs
     simp only [reduceExec,VOp.eval,hk,ite_true,Option.map_some,Option.some.injEq] at es et
     subst es; subst et
     exact ⟨rfl,⟨h.1.1,h.1.2⟩,ins_set h.2 d hk (fun hp=>h.1.reg hp)⟩
 | umov sz d n k =>
   cases sz
   · exact ordinary_sound h hs es et
   · simp only [step] at hs
     split at hs <;> [skip; cases hs]
     rename_i hk
     cases hs
     simp only [reduceExec,Size.bits,show k*64<128 by omega_using [hk],ite_true,Option.some.injEq] at es et
     subst es; subst et
     refine ⟨rfl,h.1.write .x d (fun hp=>?_),h.2⟩
     have hh := h.2 (k==1) n hp
     rcases (by omega_using [hk] : k=0 ∨ k=1) with rfl | rfl <;> exact hh
 | ldrqTbl d n off name ws =>
   simp only [step,Option.some.injEq] at hs; subst hs
   simp only [reduceExec] at es et
   split at es <;> [skip; cases es]
   split at et <;> [skip; cases et]
   cases es; cases et
   exact ⟨rfl,⟨h.1.1,h.1.2⟩,both_set h.2 d (fun _=>rfl)⟩
 | _ => exact ordinary_sound h hs es et

/-! The step the kernel evaluates. `step` gives a taint whose sets are terms in
the sets before, so no two taints of a check are the same term, and the kernel
analyses again a field function called again from the same taint. `stepK` is
`step` (`stepK_eq`), matching on the instruction once with its cases closed
(`inline_match%`) and giving a taint whose three sets are evaluated
(`RegSet.force`), as `AArch64.Taint.stepK` (`Proof/Framework/AArch64/Taint.lean`). -/

/-- `step`, as a function of the instruction first. -/
def stepFn : Instr → T → Option T
 | .vop (.dup _ d n) => fun q => some (q.1,both q.2 d (AArch64.Taint.pub q.1 n))
 | .vop (.ins .d2 d k n) => fun q =>
   if k<2 then some (q.1,put q.2 (k==1) d (AArch64.Taint.pub q.1 n)) else none
 | .umov .x d n k => fun q =>
   if k<2 then some (AArch64.Taint.set q.1 d ((get q.2 (k==1)).mem n),q.2) else none
 | .ldrqTbl t .. => fun q => some (q.1,both q.2 t true)
 | i => fun q => ((AArch64.Taint.stepFn i).run q.1).map (fun g=>(g,afterV q.2 i))

/-- `stepFn`, with its cases closed (`inline_match%`). -/
def stepFnK : Instr → T → Option T := inline_match% stepFn AArch64.Taint.stepFn afterV vdstOf VOp.dst

theorem stepFnK_eq (q : T) (i : Instr) : stepFnK i q = step q i := by
  cases i with
  | vop op =>
    cases op with
    | ins a d k n => cases a <;> rfl
    | _ => rfl
  | umov sz d n k => cases sz <;> rfl
  | _ => rfl

/-- A result of `step` with its three sets evaluated. -/
def forceT : Option T → Option T
 | some (g,a,b) => g.force fun g => a.force fun a => b.force fun b => some (g,a,b)
 | none => none

theorem forceT_eq (r : Option T) : forceT r = r := by
  rcases r with _ | ⟨g,a,b⟩ <;> rfl

/-- `step`, for the kernel. -/
def stepK (q : T) (i : Instr) : Option T := forceT (stepFnK i q)

theorem stepK_eq : stepK = step := by
  funext q i
  rw [stepK,forceT_eq,stepFnK_eq]

def taint : VG.Taint isa where
  T := T
  Agree := Agree
  step := stepK
  step_sound h hs := step_sound h ((congrFun (congrFun stepK_eq _) _).symm.trans hs)
  condPub τ := Taint.condPub τ.1
  cond_sound h hc := Taint.cond_sound h.1 hc
  meet τ σ := (τ.1.inter σ.1, τ.2.1.inter σ.2.1, τ.2.2.inter σ.2.2)
  meet_left h := by
    refine ⟨⟨h.1.1, fun r hr => h.1.2 r (RegSet.mem_inter.mp hr).1⟩, ?_⟩
    intro b v hv
    cases b <;> exact h.2 _ v (RegSet.mem_inter.mp hv).1
  meet_right h := by
    refine ⟨⟨h.1.1, fun r hr => h.1.2 r (RegSet.mem_inter.mp hr).2⟩, ?_⟩
    intro b v hv
    cases b <;> exact h.2 _ v (RegSet.mem_inter.mp hv).2
  le τ σ := τ.1.subset σ.1 && τ.2.1.subset σ.2.1 && τ.2.2.subset σ.2.2
  le_sound hl h := by
    simp only [Bool.and_eq_true] at hl
    obtain ⟨⟨hg, hlo⟩, hhi⟩ := hl
    refine ⟨⟨h.1.1, fun r hr => h.1.2 r (RegSet.mem_of_subset hg hr)⟩, ?_⟩
    intro b v hv
    cases b
    · exact h.2 false v (RegSet.mem_of_subset hlo hv)
    · exact h.2 true v (RegSet.mem_of_subset hhi hv)
  call τ := (VG.AArch64.taint.call τ.1).map (fun g => (g, τ.2))
  call_sound h hs e₁ e₂ := by
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    have ht := VG.AArch64.taint.call_sound h.1 hg e₁ e₂
    simp only [isa, call, Option.some.injEq] at e₁ e₂
    subst e₁; subst e₂
    exact ⟨ht.1, ht.2, h.2⟩
  ret τ := some τ
  ret_sound h hs e₁ e₂ := by
    cases hs
    simp only [isa, ret] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨rfl, h⟩
  push τ i := (Taint.push τ.1 i).map (fun g => (g, τ.2))
  push_sound {τ τ' i s₁ s₂ s₁' s₂'} h hs e₁ e₂ := by
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    have ht := Taint.push_sound h.1 hg e₁ e₂
    cases i <;> simp only [Taint.push, reduceCtorEq] at hg
    all_goals
      simp only [isa, push] at e₁ e₂
      split at e₁ <;> [skip; cases e₁]
      split at e₂ <;> [skip; cases e₂]
      cases e₁; cases e₂
      exact ⟨ht.1, ht.2, h.2⟩
  pop τ i := (Taint.pop τ.1 i).map (fun g => (g, τ.2))
  pop_sound {τ τ' i a₁ a₂ b₁ b₂ c₁ c₂} h hs e₁ e₂ := by
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hs
    have ht := Taint.pop_sound h.1 hg e₁ e₂
    cases i <;> simp only [Taint.pop, reduceCtorEq] at hg
    all_goals
      simp only [isa, pop] at e₁ e₂
      split at e₁ <;> [skip; cases e₁]
      split at e₂ <;> [skip; cases e₂]
      cases e₁; cases e₂
      exact ⟨ht.1, ht.2, h.2⟩

theorem agree_initial {τ : AArch64.Taint.T} {x y : State}
    (h : AArch64.Taint.Agree τ x y) : Agree (τ, empty) x y :=
  ⟨h,fun b r hr => by cases b <;> exact False.elim (RegSet.not_mem_empty r hr)⟩

theorem constantTime {Pre : State → Prop} {Pub : State → State → Prop} {c : Prog isa}
    (τ : AArch64.Taint.T)
    (hp : ∀x y,Pre x → Pre y → Pub x y → AArch64.Taint.Agree τ x y)
    {hc : VG.Taint.Hint T} (h : (taint.check (τ,empty) c hc).isSome=true) :
    ConstantTime isa Pre Pub c :=
  VG.Taint.constantTime (A:=taint) (τ,empty)
    (fun x y hx hy hxy => agree_initial (hp x y hx hy hxy)) h

end VG.AArch64.P521NativeTiming

end

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

deriving instance Lean.ToExpr for VReg
deriving instance Lean.ToExpr for Prod

-- The front is checked as a whole in TimingFront. Only the separately composed
-- window and finish phases need individual certificates here.
theorem window_constantTime :
    ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x19,.x26])) windowLoop :=
  P521NativeTiming.constantTime (AArch64.Taint.ofRegs [.x0,.x19,.x26])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem finish_constantTime :
    ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x19,.x26,.x20])) finishAndWrite :=
  P521NativeTiming.constantTime (AArch64.Taint.ofRegs [.x0,.x19,.x26,.x20])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64

theorem native_front_constantTime :
    ConstantTime isa (fun _ => True)
      (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x1,.x2,.x3])) nativeFront :=
  P521NativeTiming.constantTime (AArch64.Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass Spec.Weierstrass VG.Proof.Ecdsa.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (config windowLoop)

structure TimingWindowPre (origin s : State) : Prop where
  data : ∃k,WindowData (origin.gpr .x3) (origin.sp-3456#64) k s
  point : canonicalPoint s.mem (origin.gpr .x3) 1072
  counter : s.gpr .x19=105#64
  output : s.gpr .x20=origin.gpr .x0
  sp : s.sp=origin.sp-3456#64

structure TimingFinishPre (origin s : State) : Prop where
  workspace : s.gpr .x0=origin.gpr .x3
  table : s.gpr .x26=origin.sp-3456#64
  counter : s.gpr .x19=1#64
  output : s.gpr .x20=origin.gpr .x0
  sp : s.sp=origin.sp-3456#64

private theorem TimingExchange_TimingBody_TimingState_native_prime : config.C.p=fieldPrime := by
  dsimp only [config,VG.Impl.Ecdsa.AArch64.p521,Spec.P521.curve,Spec.P521.p,fieldPrime]

theorem timing_front_ready (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) (orderBound : 17≤config.C.n) {s : State} (pre : PrepareStackPre s) :
    WP isa nativeFront (allocated 3456 s) (TimingWindowPre s) := by
  refine WP.mono (native_front_api_ok hc law ha order orderBound pre) fun t post => ?_
  obtain ⟨_,_,_,_,_,_,_,_,_,_,result,out,sp,_⟩:=post
  have primeOne : 1<fieldPrime := by have h:=hc.p_ge; rw [TimingExchange_TimingBody_TimingState_native_prime] at h; omega_arith
  refine ⟨⟨_,result.data⟩,?_,result.counter,out,sp⟩
  change wordsVal t.mem (s.gpr .x3) 1072 9<fieldPrime ∧
    wordsVal t.mem (s.gpr .x3) 1144 9<fieldPrime ∧ wordsVal t.mem (s.gpr .x3) 1216 9<fieldPrime
  rw [result.accumulatorX,result.accumulatorY,result.accumulatorZ]
  exact ⟨by omega_arith,primeOne,by omega_arith⟩

theorem timing_window_ready {origin s : State} (pre : PrepareStackPre origin)
    (ready : TimingWindowPre origin s) : WP isa windowLoop s (TimingFinishPre origin) := by
  obtain ⟨k,data⟩:=ready.data
  refine WP.mono (native_window_ok data pre.table_scratch.symm ready.point ready.counter) fun t post => ?_
  exact ⟨post.workspace,post.tablePointer,post.counter,post.outputPointer.trans ready.output,post.sp.trans ready.sp⟩

def entryPublic (s t : State) : Prop :=
  AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x1,.x2,.x3]) s t

theorem TimingWindowPre.public {a b s t : State} (hs : TimingWindowPre a s) (ht : TimingWindowPre b t)
    (pub : entryPublic a b) :
    AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x19,.x26,.x20]) s t := by
  obtain ⟨_,ds⟩:=hs.data
  obtain ⟨_,dt⟩:=ht.data
  refine ⟨hs.sp.trans ((congrArg (fun v => v-3456#64) pub.1).trans ht.sp.symm),?_⟩
  intro r hr
  simp only [AArch64.Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact ds.scr.x0.trans ((pub.2 .x3 (by decide)).trans dt.scr.x0.symm)
  · exact hs.counter.trans ht.counter.symm
  · exact ds.readable.reg.trans ((congrArg (fun v => v-3456#64) pub.1).trans dt.readable.reg.symm)
  · exact hs.output.trans ((pub.2 .x0 (by decide)).trans ht.output.symm)

theorem TimingFinishPre.public {a b s t : State} (hs : TimingFinishPre a s) (ht : TimingFinishPre b t)
    (pub : entryPublic a b) :
    AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x19,.x26,.x20]) s t := by
  refine ⟨hs.sp.trans ((congrArg (fun v => v-3456#64) pub.1).trans ht.sp.symm),?_⟩
  intro r hr
  simp only [AArch64.Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact hs.workspace.trans ((pub.2 .x3 (by decide)).trans ht.workspace.symm)
  · exact hs.counter.trans ht.counter.symm
  · exact hs.table.trans ((congrArg (fun v => v-3456#64) pub.1).trans ht.table.symm)
  · exact hs.output.trans ((pub.2 .x0 (by decide)).trans ht.output.symm)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (config windowLoop finishAndWrite)

def nativeTimedBody : Prog isa := .seq nativeFront (.seq windowLoop finishAndWrite)

private theorem TimingExchange_TimingBody_wp_result {c : Prog isa} {s t : State} {trace : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (e : Exec isa c s trace t) : Q t := by
  obtain ⟨_,u,eu,qu⟩:=h
  obtain ⟨_,rfl⟩:=Exec.det e eu
  exact qu

private theorem TimingExchange_TimingBody_entry_allocated {a b : State} (h : entryPublic a b) :
    entryPublic (allocated 3456 a) (allocated 3456 b) :=
  ⟨congrArg (fun sp => sp-3456#64) h.1,h.2⟩

private theorem TimingExchange_TimingBody_window_public_narrow {a b : State}
    (h : AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x19,.x26,.x20]) a b) :
    AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x19,.x26]) a b := by
  refine ⟨h.1,?_⟩
  intro r hr
  apply h.2 r
  simp only [AArch64.Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
  rcases hr with rfl|rfl|rfl <;> simp

theorem native_timed_body_traces (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) (orderBound : 17≤config.C.n)
    {a b a' b' : State} {ta tb : List Leak} (pa : PrepareStackPre a) (pb : PrepareStackPre b)
    (pub : entryPublic a b)
    (ea : Exec isa nativeTimedBody (allocated 3456 a) ta a')
    (eb : Exec isa nativeTimedBody (allocated 3456 b) tb b') : ta=tb := by
  cases ea with
  | seq fa wa =>
    cases eb with
    | seq fb wb =>
      have frontTrace := native_front_constantTime _ _ _ _ _ _ trivial trivial (TimingExchange_TimingBody_entry_allocated pub) fa fb
      have readyA := TimingExchange_TimingBody_wp_result (timing_front_ready hc law ha order orderBound pa) fa
      have readyB := TimingExchange_TimingBody_wp_result (timing_front_ready hc law ha order orderBound pb) fb
      have windowPublic := TimingWindowPre.public readyA readyB pub
      cases wa with
      | seq wina fina =>
        cases wb with
        | seq winb finb =>
          have windowTrace := window_constantTime _ _ _ _ _ _ trivial trivial (TimingExchange_TimingBody_window_public_narrow windowPublic) wina winb
          have finishA := TimingExchange_TimingBody_wp_result (timing_window_ready pa readyA) wina
          have finishB := TimingExchange_TimingBody_wp_result (timing_window_ready pb readyB) winb
          have finishPublic := TimingFinishPre.public finishA finishB pub
          have finishTrace := finish_constantTime _ _ _ _ _ _ trivial trivial finishPublic fina finb
          rw [frontTrace,windowTrace,finishTrace]

private theorem TimingExchange_TimingBody_seq_parts {a b : Prog isa} {s t : State} {trace : List Leak}
    (e : Exec isa (.seq a b) s trace t) :
    ∃u ta tb,trace=ta++tb ∧ Exec isa a s ta u ∧ Exec isa b u tb t := by
  cases e with
  | seq ea eb => exact ⟨_,_,_,rfl,ea,eb⟩

private theorem TimingExchange_TimingBody_nil_parts {s t : State} {trace : List Leak}
    (e : Exec isa (.block []) s trace t) : trace=[] ∧ t=s := by
  cases e with
  | block hn =>
    simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at hn
    exact ⟨hn.2.symm,hn.1.symm⟩

private theorem TimingExchange_TimingBody_body_to_timed {s t : State} {trace : List Leak}
    (e : Exec isa VG.Impl.Weierstrass.AArch64.P521Native.body s trace t) :
    Exec isa nativeTimedBody s trace t := by
  obtain ⟨u,tp,tr,rfl,p,r⟩:=TimingExchange_TimingBody_seq_parts e
  obtain ⟨v,trc,tb,rfl,rc,b⟩:=TimingExchange_TimingBody_seq_parts r
  obtain ⟨w,tbl,tn,rfl,bl,n⟩:=TimingExchange_TimingBody_seq_parts b
  obtain ⟨x,tno,tw,rfl,no,ww⟩:=TimingExchange_TimingBody_seq_parts n
  obtain ⟨y,twi,tf,rfl,wi,f⟩:=TimingExchange_TimingBody_seq_parts ww
  obtain ⟨z,tfi,te,rfl,fi,empty⟩:=TimingExchange_TimingBody_seq_parts f
  obtain ⟨rfl,rfl⟩:=TimingExchange_TimingBody_nil_parts empty
  have assembled:=Exec.seq (Exec.seq p (Exec.seq rc (Exec.seq bl no))) (Exec.seq wi fi)
  simpa only [nativeTimedBody,nativeFront,nativeRecodeArithmetic,nativeFrontArithmetic,
    List.append_assoc,List.append_nil] using assembled

theorem native_body_traces (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) (orderBound : 17≤config.C.n)
    {a b a' b' : State} {ta tb : List Leak} (pa : PrepareStackPre a) (pb : PrepareStackPre b)
    (pub : entryPublic a b)
    (ea : Exec isa VG.Impl.Weierstrass.AArch64.P521Native.body (allocated 3456 a) ta a')
    (eb : Exec isa VG.Impl.Weierstrass.AArch64.P521Native.body (allocated 3456 b) tb b') : ta=tb :=
  native_timed_body_traces hc law ha order orderBound pa pb pub (TimingExchange_TimingBody_body_to_timed ea) (TimingExchange_TimingBody_body_to_timed eb)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (config outerBlock000 outerBlock172 exchange body sequence)

private theorem TimingExchange_seq_parts {a b : Prog isa} {s t : State} {trace : List Leak}
    (e : Exec isa (.seq a b) s trace t) :
    ∃u ta tb,trace=ta++tb ∧ Exec isa a s ta u ∧ Exec isa b u tb t := by
  cases e with
  | seq ea eb => exact ⟨_,_,_,rfl,ea,eb⟩

private theorem TimingExchange_nil_parts {s t : State} {trace : List Leak}
    (e : Exec isa (.block []) s trace t) : trace=[] ∧ t=s := by
  cases e with
  | block hn =>
    simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at hn
    exact ⟨hn.2.symm,hn.1.symm⟩

private theorem TimingExchange_alloc_parts {c : Prog isa} {s t : State} {trace : List Leak}
    (room : 3456≤s.sp.toNat) (e : Exec isa (.frame (.alloc 3456) c (.free 3456)) s trace t) :
    ∃u,Exec isa c (allocated 3456 s) trace u := by
  have pushKnown : isa.push (.alloc 3456) s=some (allocated 3456 s) := by
    simp only [isa,push,show 0<3456 from by decide,show 3456<4096 from by decide,
      show 3456%16=0 from by decide,room,and_self,ite_true]
    rfl
  cases e with
  | frame hp eb _ =>
    have eq := Option.some.inj (pushKnown.symm.trans hp)
    subst eq
    exact ⟨_,by simpa only [isa,addrs,List.map_nil,List.nil_append,List.append_nil] using eb⟩

private theorem TimingExchange_exchange_body_parts {s t : State} {trace : List Leak}
    (pre : PrepareStackPre s) (e : Exec isa exchange s trace t) :
    ∃u,Exec isa body (allocated 3456 (nativeSavedState s)) trace u := by
  obtain ⟨a,tp,tr,rfl,ep,rest⟩:=TimingExchange_seq_parts e
  obtain ⟨hp,ha⟩:=Exec.det ep (native_prologue_exec s)
  subst hp
  subst ha
  obtain ⟨b,tf,te,rfl,ef,tail⟩:=TimingExchange_seq_parts rest
  obtain ⟨c,ts,tn,rfl,es,en⟩:=TimingExchange_seq_parts tail
  obtain ⟨hn,he⟩:=TimingExchange_nil_parts en
  subst hn
  subst he
  obtain ⟨hs,_⟩:=Exec.det es (native_epilogue_exec b)
  subst hs
  have inner:=TimingExchange_alloc_parts (s:=nativeSavedState s) pre.room ef
  simpa only [List.nil_append,List.append_nil] using inner

private theorem TimingExchange_entry_public_of_contract {s t : State} (h : nativeContract.pub s t) : entryPublic s t := by
  sig_pub [nativeContract,Spec.EcKey.P521.inst,Spec.Ecdh.Instance.exchangeContract,
    Spec.Ecdh.Instance.exchangeSig,Spec.P521.curve,Spec.EcKey.scratchWords,abi,argRegs] at h
  obtain ⟨sp,_,g0,g1,g2,g3⟩:=h
  exact ⟨sp,fun r hr => by
    simp only [AArch64.Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact g0
    · exact g1
    · exact g2
    · exact g3⟩

theorem native_exchange_constantTime (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) (orderBound : 17≤config.C.n) :
    ConstantTime isa nativeContract.pre nativeContract.pub exchange := by
  intro a b ta tb a' b' pa pb pub ea eb
  have stackA:=prepare_stack_pre pa
  have stackB:=prepare_stack_pre pb
  obtain ⟨u,ua⟩:=TimingExchange_exchange_body_parts stackA ea
  obtain ⟨v,vb⟩:=TimingExchange_exchange_body_parts stackB eb
  have pubData:=TimingExchange_entry_public_of_contract pub
  have publicSaved : entryPublic (nativeSavedState a) (nativeSavedState b) := pubData
  have preA := prepare_stack_pre (native_pre_saved pa)
  have preB := prepare_stack_pre (native_pre_saved pb)
  exact native_body_traces hc law ha order orderBound preA preB publicSaved ua vb

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
attribute [local instance high] instPowNat
open VG VG.AArch64 VG.Proof.Weierstrass VG.Proof.Ecdsa.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (config exchange)

private theorem native_post_of {s t : State} (h : VG.Proof.Ecdh.AArch64.EPost config s t) :
    nativeContract.post s t := by
  sig_post [nativeContract,Spec.EcKey.P521.inst,Spec.Ecdh.Instance.exchangeContract,
    Spec.Ecdh.Instance.exchangeSig,Spec.P521.curve,Spec.EcKey.scratchWords,abi,argRegs]
  change VG.Proof.Ecdh.AArch64.EPost config s t
  exact h

 theorem native_verified (law : Law Spec.P521.curve) (inv : InvSounds) (order : PrimeOrder Spec.P521.curve) :
    Verified target exchange nativeContract := by
  have hc : BaseCfgOk config := (VG.Proof.Ecdsa.AArch64.P521.p521_ok inv).toBaseCfgOk
  have ha : AM3 config.C := (VG.Proof.Ecdsa.AArch64.P521.p521_ok inv).am3
  have hn : 17≤config.C.n := by decide +kernel
  refine ⟨?_,native_exchange_constantTime hc law ha order hn,native_contract_satisfiable⟩
  intro s pre
  obtain ⟨trace,t,exec,api,gp,rd,wr,sp⟩ := native_exchange_api_ok hc law ha order pre
  have vec : exchange.allInstrs keepsV=true := by lit_decide
  exact ⟨trace,t,exec,⟨gp,sp,Exec.preservedV exec vec⟩,native_post_of api⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

/-!
# P-521's ECDH on AArch64, without secret residue

`vg_ecdh_p521`, the native P-521 exchange, under the shared ECDH contract with
its stack of 3456 bytes (`nativeContract`), whose postcondition reads the
memory on return only within `out` (`EcKey.AArch64.Scrub.exchangeOkW`):
returns with every register it may leave secret cleared and its whole stack
zeroed (`Scrub.verifiedScrubbedAll`): `exchange_scrubbed`, the theorem the
registration file binds.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.P521Native.Scrub

open VG.Proof.P521.AArch64 (hasLaw)

/-- `vg_ecdh_p521` as emitted, cleanup included
(`Impl.Weierstrass.AArch64.P521Native.Fn.exchange`): it meets its contract in
constant time and returns without secret residue. What the cleanup needs of
the code (`Scrub.scrubSide`) is evaluated here, by the kernel. -/
theorem exchange_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Weierstrass.AArch64.P521Native.Fn.exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst AArch64.abi 3456) 32 :=
  AArch64.Scrub.verifiedScrubbedAll (api := Spec.Ecdh.P521.exchangeApi)
    { code := Impl.Weierstrass.AArch64.P521Native.exchange
      verified := native_verified hasLaw.law hasLaw.inv hasLaw.prime
      consts := []
      stack := 3456 } _
    (EcKey.AArch64.Scrub.exchangeOkW Spec.EcKey.P521.inst 3456)
    (by dsimp only; lit_decide)

end VG.Proof.Weierstrass.AArch64.P521Native.Scrub
