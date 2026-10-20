module
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
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
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
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
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
    simp only [setLane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
      hk, decide_true, Bool.true_and, ite_true, ite_false, Nat.mul_zero, Nat.mul_one,
      Nat.sub_zero, reduceCtorEq] <;>
    (have h1 : k < 128 := by omega
     have h2 : 64 + k < 128 := by omega
     have h3 : ¬ 64 + k < 64 := by omega
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
     rcases (by omega : k=0 ∨ k=1) with rfl | rfl <;> cases b <;>
       first | contradiction | exact hv
 · simp only [RegUpd.v_setV,vd,ite_false]
   apply h b v
   rcases (by omega : k=0 ∨ k=1) with rfl | rfl <;> cases b
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
 obtain ⟨a,hg'⟩ := AArch64.taint.step_sound h.1 hg es et
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
     cases a <;> simp only [exec,VOp.eval,Option.map_some,Option.some.injEq] at es et
     all_goals
       subst es; subst et
       exact ⟨rfl,⟨h.1.1,h.1.2⟩,both_set h.2 d (fun hp=>by rw [h.1.reg hp])⟩
   case ins a d k n =>
     cases a <;> try exact ordinary_sound h hs es et
     simp only [step] at hs
     split at hs <;> [skip; cases hs]
     rename_i hk
     cases hs
     simp only [exec,VOp.eval,hk,ite_true,Option.map_some,Option.some.injEq] at es et
     subst es; subst et
     exact ⟨rfl,⟨h.1.1,h.1.2⟩,ins_set h.2 d hk (fun hp=>h.1.reg hp)⟩
 | umov sz d n k =>
   cases sz
   · exact ordinary_sound h hs es et
   · simp only [step] at hs
     split at hs <;> [skip; cases hs]
     rename_i hk
     cases hs
     simp only [exec,Size.bits,show k*64<128 by omega,ite_true,Option.some.injEq] at es et
     subst es; subst et
     refine ⟨rfl,h.1.write .x d (fun hp=>?_),h.2⟩
     have hh := h.2 (k==1) n hp
     rcases (by omega : k=0 ∨ k=1) with rfl | rfl <;> exact hh
 | ldrqTbl d n off name ws =>
   simp only [step,Option.some.injEq] at hs; subst hs
   simp only [exec] at es et
   split at es <;> [skip; cases es]
   split at et <;> [skip; cases et]
   cases es; cases et
   exact ⟨rfl,⟨h.1.1,h.1.2⟩,both_set h.2 d (fun _=>rfl)⟩
 | _ => exact ordinary_sound h hs es et

def taint : VG.Taint isa where
  T := T
  Agree := Agree
  step := step
  step_sound := step_sound
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

end VG.AArch64.LaneTaint
