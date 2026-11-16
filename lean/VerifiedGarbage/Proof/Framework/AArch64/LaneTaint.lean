module
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
/-! A proof-only taint domain for public values saved in either 64-bit SIMD lane. -/
@[expose] public section
namespace VG.AArch64.LaneTaint
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
def afterV (q : Part) (i : Instr) : Part := if scalar i then q else empty
def step (q : T) : Instr → Option T
 | .vop (.dup _ d n) => some (q.1,both q.2 d (AArch64.Taint.pub q.1 n))
 | .vop (.ins .d2 d k n) => if k<2 then some (q.1,put q.2 (k==1) d (AArch64.Taint.pub q.1 n)) else none
 | .umov .x d n k => if k<2 then some (AArch64.Taint.set q.1 d ((get q.2 (k==1)).mem n),q.2) else none
 | .ldrqTbl t .. => some (q.1,both q.2 t true)
 | i => (AArch64.Taint.step q.1 i).map (fun g=>(g,afterV q.2 i))
private theorem scalar_vectors {i : Instr} {s s' : State}
    (hi : scalar i = true) (he : exec i s = some s') : s'.v = s.v := by
  cases i <;> simp only [scalar, VectorTaint.scalar, Bool.false_eq_true] at hi
  case ldp => obtain ⟨_, _, rfl⟩ := exec_ldp_eq he; rfl
  case stp => obtain ⟨_, rfl⟩ := exec_stp_eq he; rfl
  all_goals
    simp only [reduceExec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
  all_goals
    repeat' first
      | split at he
      | simp only [Option.map_eq_some_iff] at he
      | rcases he with ⟨_, _, he⟩
  all_goals
    simp_all only [State.store]
  all_goals
    repeat' first | split at he | cases he
  all_goals rfl

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
 by_cases hi : scalar i=true
 · simp only [afterV,hi,ite_true]
   intro b v hv
   rw [scalar_vectors hi es,scalar_vectors hi et]
   exact h.2 b v hv
 · simp only [afterV,hi]
   intro b v hv
   cases b <;> exact False.elim (RegSet.not_mem_empty v hv)

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

/-! ## The step the kernel evaluates

`stepK` is `step` (`stepK_eq`), as `Taint.stepK` is `Taint.step`
(`Proof/Framework/AArch64/Taint.lean`): a function of the instruction first,
with its cases closed (`inline_match%`), which gives a taint whose sets the
instruction writes are evaluated (`RegSet.force`) and whose others are the
terms they were, in pairs whose types are written the same in every case, so
that equal taints are the same term. The kernel then finds again every step
it has made of the same instruction from the same taint. -/

/-- What an instruction does to a taint, as a function of its general-purpose
registers and of its lanes. -/
structure Step where
  run : RegSet Reg → Part → Option T

/-- The taint of three sets, with the pairs' types written out. -/
local notation "⟪" g ", " lo ", " hi "⟫" =>
  @Prod.mk (RegSet Reg) (RegSet VReg × RegSet VReg) g (@Prod.mk (RegSet VReg) (RegSet VReg) lo hi)

/-- An instruction `step` leaves to `Taint.step`, `s` being its `Taint.stepFn`:
the general-purpose registers by `s`, evaluated, and the lanes kept (`true`:
the instruction is `scalar`) or none public. -/
def ordinary (s : AArch64.Taint.Step) : Bool → Step
  | true => ⟨fun g q => AArch64.Taint.forceO (s.run g) fun g' =>
      some (@Prod.mk (RegSet Reg) (RegSet VReg × RegSet VReg) g' q)⟩
  | false => ⟨fun g _ => AArch64.Taint.forceO (s.run g) fun g' => some ⟪g', ⟨nat_lit 0⟩, ⟨nat_lit 0⟩⟫⟩

/-- `step` of a vector instruction. -/
def vopFn : VOp → Step
  | .dup _ d n => ⟨fun g q => match q with
      | (lo, hi) => (setV lo d (AArch64.Taint.pub g n)).force fun lo' =>
        (setV hi d (AArch64.Taint.pub g n)).force fun hi' => some ⟪g, lo', hi'⟫⟩
  | .ins .d2 d k n => ⟨fun g q => if k < 2 then
      match q with
      | (lo, hi) =>
        bif k == 1 then (setV hi d (AArch64.Taint.pub g n)).force fun hi' => some ⟪g, lo, hi'⟫
        else (setV lo d (AArch64.Taint.pub g n)).force fun lo' => some ⟪g, lo', hi⟫
      else none⟩
  | _ => ⟨fun g _ => some ⟪g, ⟨nat_lit 0⟩, ⟨nat_lit 0⟩⟫⟩

/-- `vopFn`, with its cases closed (`inline_match%`). -/
def vopFnK : VOp → Step := inline_match% vopFn

theorem vopFnK_eq (op : VOp) : vopFnK op = vopFn op := by
  cases op <;> first | rfl | (rename_i a _ _ _; cases a <;> rfl)

/-- `step` of a move from a vector register. -/
def umovFn (d : Reg) (n : VReg) (k : Nat) : Size → Step
  | .x => ⟨fun g q => if k < 2 then
      (AArch64.Taint.set g d ((get q (k == 1)).mem n)).force fun g' =>
        some (@Prod.mk (RegSet Reg) (RegSet VReg × RegSet VReg) g' q)
      else none⟩
  | .w => ⟨fun g _ => (AArch64.Taint.set g d false).force fun g' => some ⟪g', ⟨nat_lit 0⟩, ⟨nat_lit 0⟩⟫⟩

/-- `step`, as a function of the instruction first. -/
def stepFn : Instr → Step
  | .vop op => vopFnK op
  | .umov sz d n k => umovFn d n k sz
  | .ldrqTbl t .. => ⟨fun g q => match q with
      | (lo, hi) => (setV lo t true).force fun lo' => (setV hi t true).force fun hi' => some ⟪g, lo', hi'⟫⟩
  | i => ordinary (AArch64.Taint.stepFn i) (VectorTaint.scalar i)

/-- `stepFn`, with its cases closed (`inline_match%`). -/
def stepFnK : Instr → Step := inline_match% stepFn AArch64.Taint.stepFn VectorTaint.scalar ordinary

theorem stepFnK_eq (i : Instr) : stepFnK i = stepFn i := by cases i <;> rfl

theorem ordinary_run (s : AArch64.Taint.Step) (b : Bool) (g : RegSet Reg) (q : Part) :
    (ordinary s b).run g q = (s.run g).map fun g' => (g', if b then q else empty) := by
  cases b <;> simp only [ordinary, AArch64.Taint.forceO_eq] <;> cases s.run g <;> rfl

theorem ordinary_step (i : Instr) (g : RegSet Reg) (q : Part)
    (h : stepFn i = ordinary (AArch64.Taint.stepFn i) (scalar i))
    (h' : step (g, q) i = (AArch64.Taint.step g i).map fun g' => (g', afterV q i)) :
    (stepFn i).run g q = step (g, q) i := by
  rw [h, h', ordinary_run]; rfl

/-- `step`, giving a taint that is evaluated. -/
def stepK (τ : T) (i : Instr) : Option T :=
  match τ with
  | (g, q) => (stepFnK i).run g q

theorem stepK_eq : stepK = step := by
  funext ⟨g, lo, hi⟩ i
  show (stepFnK i).run g (lo, hi) = step (g, lo, hi) i
  rw [stepFnK_eq]
  cases i with
  | vop op =>
    show (vopFnK op).run g (lo, hi) = _
    rw [vopFnK_eq]
    cases op <;> try rfl
    case ins a d k n =>
      cases a <;> try rfl
      show (if k < 2 then _ else none) = (if k < 2 then _ else none)
      split <;> [skip; rfl]
      cases k == 1 <;> rfl
  | umov sz d n k => cases sz <;> rfl
  | ldrqTbl => rfl
  | _ => exact ordinary_step _ g (lo, hi) rfl rfl

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

/-- The step of `taint` is `step`, for the proofs about it: the kernel
evaluates `stepK`. -/
theorem taint_step (τ : T) (i : Instr) : taint.step τ i = step τ i :=
  congrFun (congrFun stepK_eq τ) i

end VG.AArch64.LaneTaint
