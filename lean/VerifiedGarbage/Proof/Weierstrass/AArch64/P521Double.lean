module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Double
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.Cms
public import VerifiedGarbage.Proof.Weierstrass.Jac
import VerifiedGarbage.Proof.Mont.AArch64.P521Linear
import VerifiedGarbage.Proof.Framework.Block

/-! # P-521 fused field steps, with the ordinary field-program invariant -/

-- separate module: isolates the fused arithmetic composition from window callers
@[expose] public section

namespace VG.Impl.Weierstrass.AArch64.P521Double

open VG.Proof.Weierstrass.Cms (smulN)

def Step.out : Step → Nat
  | .op f => f.out
  | .cms o _ _ _ _ => o

def Step.ins : Step → List Nat
  | .op f => f.ins
  | .cms _ _ a _ b => [a,b]

def Step.small : Step → Bool
  | .op _ => true
  | .cms _ C _ D _ => C ≤ 16 && D ≤ 16

def Step.run {F : Type _} [Lean.Grind.CommRing F] : Step → (Nat → F) → Nat → F
  | .op f,e => f.run e
  | .cms o C a D b,e => Function.update e o (smulN C (e a)-smulN D (e b))

def runSteps {F : Type _} [Lean.Grind.CommRing F] (l : List Step) (E : Nat → F) : Nat → F :=
  l.foldl (fun e st => st.run e) E

def readOk : List Step → List Nat → Bool
  | [],_ => true
  | st::ss,V => st.ins.all (fun x => decide (x ∈ V)) && readOk ss (st.out::V)

def valid : List Step → List Nat → List Nat
  | [],V => V
  | st::ss,V => valid ss (st.out::V)

def Step.rename (σ : Nat → Nat) : Step → Step
  | .op f => .op (f.rename σ)
  | .cms o C a D b => .cms (σ o) C (σ a) D (σ b)

end VG.Impl.Weierstrass.AArch64.P521Double

namespace VG.Proof.Weierstrass.AArch64.P521Double

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Weierstrass.AArch64.P521Double
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Weierstrass.Cms

private theorem cmsKeep {M : Mod} {base : Addr} {o : Nat} {s t : State}
    (hn : M.n = 9) (k : KeepRegs (clob 9) s t) (O : Outside base o 72 s.mem t.mem) :
    OpKeep M base o s t :=
  ⟨fun r hr => k.gpr r (by simpa only [hn] using hr),k.rd,k.wr,k.sp,
    fun x hx _ => O x (by simpa only [hn] using hx)⟩

theorem step_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hsp : Impl.Mont.AArch64.P521Linear.supported M = true)
    (hL : Lay M size Sl) (hAl : Aligned M Sl) (hm : UnitMod m (2^(64*M.n)))
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s)
    {st : Step} (hsm : st.small = true) (hS : ∀ x ∈ st.out::st.ins, Sl x)
    (hLow : Low M (st.out::st.ins)) (hR : ∀ x ∈ st.ins, x ∈ V) :
    WP isa (st.code M) s fun t => OpKeep M base st.out s t ∧
      Inv M base size m Sl (st.out::V) (st.run E) t := by
  cases st with
  | op f => exact opProg_ok hL hAl hm hI hS hLow hR
  | cms o C a D b =>
    simp only [Step.small,Bool.and_eq_true,decide_eq_true_eq] at hsm
    simp only [Step.out,Step.ins,List.mem_cons,List.not_mem_nil,or_false,
      forall_eq_or_imp,forall_eq] at hS hR
    obtain ⟨hn,hp⟩ := Mont.AArch64.P521Linear.supported_mod hsp hI.mod.red
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    have ho := hL.le o hS.1
    have ha := hL.le a hS.2.1
    have hb := hL.le b hS.2.2
    simp only [hn] at hA hB ho ha hb
    refine WP.mono (Mont.AArch64.P521Linear.cms_ok hI.scr ho ha hb
      (hAl.sl o hS.1) (hAl.sl a hS.2.1) (hAl.sl b hS.2.2) hp hsm.1 hsm.2 hA hB)
      fun t ⟨he,hlt,hk,O⟩ => ?_
    have hOp := cmsKeep hn hk O
    refine ⟨hOp,hI.update hL hS.1 hOp (by simpa only [hn] using hlt) ?_⟩
    simp only [hn]
    rw [he,Nat.mul_comm (wordsVal s.mem base a 9) C,
      Nat.mul_comm (m-wordsVal s.mem base b 9) D,
      toM_cms _ _ _ _ _ (Nat.le_of_lt hB)]
    rw [← hn,hI.val a hR.1,hI.val b hR.2]

theorem program_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hsp : Impl.Mont.AArch64.P521Linear.supported M = true)
    (hL : Lay M size Sl) (hAl : Aligned M Sl) (hm : UnitMod m (2^(64*M.n))) :
    ∀ (l : List Step) {V : List Nat} {E : Nat → Fin m} {s : State},
      Inv M base size m Sl V E s → (∀ st ∈ l, st.small = true) →
      (∀ st ∈ l, ∀ x ∈ st.out::st.ins, Sl x) →
      (∀ st ∈ l, Low M (st.out::st.ins)) → readOk l V = true →
      WP isa (program M l) s fun t =>
        ProgKeep M base (l.map Step.out) s t ∧ Inv M base size m Sl (valid l V) (runSteps l E) t
  | [],_,_,s,hI,_,_,_,_ => WP.block_nil ⟨ProgKeep.refl _ _ _ s,hI⟩
  | st::ss,V,E,s,hI,hsm,hS,hLow,hR => by
    simp only [readOk,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at hR
    rw [program]
    refine WP.seq (WP.mono (step_ok hsp hL hAl hm hI (hsm st (List.mem_cons_self ..))
      (hS st (List.mem_cons_self ..)) (hLow st (List.mem_cons_self ..)) hR.1)
      fun u ⟨ku,Iu⟩ => ?_)
    refine WP.mono (program_ok hsp hL hAl hm ss Iu
      (fun st h => hsm st (List.mem_cons_of_mem _ h))
      (fun st h => hS st (List.mem_cons_of_mem _ h))
      (fun st h => hLow st (List.mem_cons_of_mem _ h)) hR.2)
      fun t ⟨kt,It⟩ => ?_
    refine ⟨⟨fun r hr => (kt.gpr r hr).trans (ku.gpr r hr),kt.rd.trans ku.rd,
      kt.wr.trans ku.wr,kt.sp.trans ku.sp,?_⟩,It⟩
    intro x hx ht
    rw [List.map_cons] at hx
    rw [kt.mem x (fun w hw => hx w (List.mem_cons_of_mem _ hw)) ht,
      ku.mem x (hx _ (List.mem_cons_self ..)) ht]

theorem mem_valid {x : Nat} : ∀ (l : List Step) (V : List Nat),
    x ∈ V ∨ x ∈ l.map Step.out → x ∈ valid l V
  | [],V,h => by simpa [valid] using h
  | st::ss,V,h => by
    refine mem_valid ss _ ?_
    simp only [List.map_cons,List.mem_cons] at h ⊢
    grind

theorem step_run_rename {F : Type _} [Lean.Grind.CommRing F] (σ : Nat → Nat)
    (st : Step) (E : Nat → F) (h : ∀ y, σ y = σ st.out → y = st.out) :
    (fun y => (st.rename σ).run E (σ y)) = st.run (fun y => E (σ y)) := by
  funext y
  have hy : σ y = σ st.out ↔ y = st.out := ⟨h y,fun h => h ▸ rfl⟩
  cases st with
  | op f => exact congrFun (FOp.run_rename σ f E h) y
  | cms o C a D b =>
    simp only [Step.out] at hy
    simp only [Step.rename,Step.run,Function.update_apply,hy]

theorem runSteps_rename {F : Type _} [Lean.Grind.CommRing F] (σ : Nat → Nat) :
    ∀ (l : List Step) (E : Nat → F), (∀ st ∈ l, ∀ y, σ y = σ st.out → y = st.out) →
      (fun y => runSteps (l.map (Step.rename σ)) E (σ y)) = runSteps l (fun y => E (σ y))
  | [],_,_ => rfl
  | st::ss,E,h => by
    change (fun y => runSteps (ss.map (Step.rename σ)) ((st.rename σ).run E) (σ y)) =
      runSteps ss (st.run (fun y => E (σ y)))
    rw [runSteps_rename σ ss _ (fun st hst => h st (List.mem_cons_of_mem _ hst)),
      step_run_rename σ st E (h st (List.mem_cons_self ..))]

def numbered : List Step := steps ⟨9,10,0,1,2,3,4,5⟩ ⟨11,12,13⟩ ⟨6,7,8⟩

theorem numbered_run {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F) :
    (runSteps numbered E 6,runSteps numbered E 7,runSteps numbered E 8) =
      dblJF (E 11) (E 12) (E 13) := by
  simp only [numbered,steps,runSteps,List.foldl,Step.run,FOp.run,Function.update_apply,
    dblJF,smulN,Prod.mk.injEq,Nat.reduceEqDiff,ite_true,ite_false]
  refine ⟨?_,?_,?_⟩ <;> grind

theorem steps_run {F : Type _} [Lean.Grind.CommRing F] {S : RcbSlots} {p o : Pt}
    (E : Nat → F) (hAp : RcbApart S p p o) :
    (runSteps (steps S p o) E o.x,runSteps (steps S p o) E o.y,
      runSteps (steps S p o) E o.z) = dblJF (E p.x) (E p.y) (E p.z) := by
  have he : steps S p o = numbered.map (Step.rename (rcbσ S p p o)) := rfl
  have hn : ∀ st ∈ numbered, st.out < 9 := by decide
  have hr := runSteps_rename (rcbσ S p p o) numbered E
    (fun st hst => hAp.inj (hn st hst))
  rw [← he] at hr
  have h6 := congrFun hr 6
  have h7 := congrFun hr 7
  have h8 := congrFun hr 8
  change runSteps (steps S p o) E o.x = _ at h6
  change runSteps (steps S p o) E o.y = _ at h7
  change runSteps (steps S p o) E o.z = _ at h8
  rw [h6,h7,h8,numbered_run]
  rfl

theorem steps_slots (S : RcbSlots) (p o : Pt) :
    ∀ st ∈ steps S p o, ∀ x ∈ st.out::st.ins, x ∈ rcbW S o++rcbR S p p := by
  intro st hst x hx
  simp only [steps,List.mem_cons,List.not_mem_nil,or_false] at hst
  rcases hst with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [Step.out,Step.ins,FOp.out,FOp.ins,rcbW,rcbR,
      List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hx ⊢ <;> grind

theorem steps_out (S : RcbSlots) (p o : Pt) :
    ∀ st ∈ steps S p o, st.out ∈ rcbW S o := by
  intro st hst
  simp only [steps,List.mem_cons,List.not_mem_nil,or_false] at hst
  rcases hst with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [Step.out,FOp.out,rcbW]

theorem steps_small (S : RcbSlots) (p o : Pt) :
    ∀ st ∈ steps S p o, st.small = true :=
  List.all_eq_true.mp (show (steps S p o).all Step.small = true from rfl)

theorem steps_read {S : RcbSlots} {p o : Pt} {V : List Nat}
    (hV : ∀ x ∈ rcbR S p p, x ∈ V) : readOk (steps S p o) V = true := by
  have hx := hV p.x (by simp [rcbR])
  have hy := hV p.y (by simp [rcbR])
  have hz := hV p.z (by simp [rcbR])
  simp [steps,readOk,Step.ins,Step.out,FOp.ins,FOp.out,hx,hy,hz]

end VG.Proof.Weierstrass.AArch64.P521Double
