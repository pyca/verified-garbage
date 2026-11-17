module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.LoopOps
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Math
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Inputs
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Math
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.AArch64.Joint
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.State
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.AArch64.Joint

/-! ### `Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Prep`, which only this module used -/

section

/-! Building the joint digit-pair table with the existing complete addition. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

theorem tablePrep_ok {base : Addr} {P Q : Point C} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C)
    {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) (hi : Inputs base P Q s)
    (ht : Table base P Q (d-1) s) :
    WP isa (tablePrep d) s fun t =>
      Changes base loopWork s t ∧ Inputs base P Q t ∧
      PointAt base t resultPt (pair P Q ((previous d)%4) ((previous d)/4)) ∧
      PointAt base t entry (if d%4=0 then Q else P) := by
  have hp : previous d < d := previous_lt h1
  have hp15 : previous d ≤ 15 := by omega_using [h15, hp]
  let A := pair P Q ((previous d)%4) ((previous d)/4)
  have prep : WP isa (.block (if previous d=0 then infinity else copyPt 6 resultPt (tablePt (previous d)))) s
      fun t => Changes base loopWork s t ∧ Inputs base P Q t ∧ PointAt base t resultPt A := by
    by_cases hz : previous d=0
    · rw [ite_eq_left hz]
      refine WP.mono (infinity_ok hi.scr hc hC) fun t ⟨k,p,_⟩ => ?_
      have W := k.mono resultWork_sub
      refine ⟨W,hi.unch (W.mono loopWork_sub),?_⟩
      have e : A=.infinity := by dsimp only [A]; rw [hz]; exact pair_zero P Q
      rw [e]; exact p
    · rw [ite_eq_right hz]
      refine WP.mono (copy_point hi.scr (load_layout (by omega_using [hz]) hp15)
        (ht (previous d) (by omega_using [hz]) (by omega_using [hp]))) fun t ⟨k,p,_⟩ => ?_
      have W := k.mono resultWork_sub
      exact ⟨W,hi.unch (W.mono loopWork_sub),p⟩
  have code : tablePrep d = .block ((if previous d=0 then infinity else copyPt 6 resultPt (tablePt (previous d))) ++
      affineEntry (if d%4=0 then PX else GX) (if d%4=0 then PY else GY)) := by
    by_cases hz : d%4=0
    · simp only [tablePrep,previous,ite_eq_left hz]
    · simp only [tablePrep,previous,ite_eq_right hz]
  rw [code,WP.block_append_iff]
  refine WP.mono prep fun s₁ ⟨k₁,I₁,R₁⟩ => ?_
  have aff : WP isa (.block (affineEntry (if d%4=0 then PX else GX) (if d%4=0 then PY else GY))) s₁
      fun t => Changes base entryWork s₁ t ∧ PointAt base t entry (if d%4=0 then Q else P) := by
    by_cases hz : d%4=0
    · simp only [ite_eq_left hz]
      change WP isa (.block (copyPt 6 entry qSource)) s₁ _
      exact WP.mono (copy_point I₁.scr entry_from_peer I₁.peer) fun t ⟨k,p,_⟩ => ⟨k,p⟩
    · simp only [ite_eq_right hz]
      change WP isa (.block (copyPt 6 entry gSource)) s₁ _
      exact WP.mono (copy_point I₁.scr entry_from_generator I₁.generator) fun t ⟨k,p,_⟩ => ⟨k,p⟩
  refine WP.mono aff fun s₂ ⟨k₂,E₂⟩ => ?_
  have W₂ := k₁.trans (k₂.mono entryWork_sub)
  have I₂ := hi.unch (W₂.mono loopWork_sub)
  have R₂ := k₂.point I₁.scr R₁ (by decide) (by decide)
  exact ⟨W₂,I₂,R₂,E₂⟩
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

end

end

/-! ### `Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Choose`, which only this module used -/

section

/-! Selecting a short copy path using only the public table counter. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans read_x)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

theorem choose_sub (s : State) {m : Nat} (hm : m < 4096) :
    WP isa (.block [.subImm .x .x2 .x19 m]) s fun t =>
      t.gpr .x2=s.gpr .x19-BitVec.ofNat 64 m ∧ Keeps [.x2] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,hm,ite_true,BitVec.setWidth_eq,
    RegUpd.gpr_write_self,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem choose_wp (f : Nat → Prog isa) {Q : State → Prop} :
    ∀ m,m ≤ 15 → ∀ {j : Nat} {s : State},1 ≤ j → j ≤ m →
      s.gpr .x19=BitVec.ofNat 64 j →
      (∀ t,Keeps [.x2] s t → WP isa (f j) t Q) → WP isa (choose f m) s Q
  | 0,_,_,_,hj,hjm,_,_ => False.elim (by omega_using [hj, hjm])
  | m+1,hm,j,s,hj,hjm,h19,h => by
    rw [choose]
    refine WP.seq (WP.mono (choose_sub s (m:=m+1) (by omega_using [hm])) fun t ⟨v,k⟩ => ?_)
    have z : (t.read .x .x2 == 0)=decide (j=m+1) := by
      rw [read_x,v,h19]
      by_cases e : j=m+1
      · rw [e,BitVec.sub_self]
        change true = decide (m+1=m+1)
        exact (decide_eq_true rfl).symm
      · rw [decide_eq_false e,beq_eq_false_iff_ne]
        intro hz
        have hh := congrArg BitVec.toNat hz
        rw [BitVec.toNat_sub,BitVec.toNat_ofNat,BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega_using [hm, hjm] : j < 2^64),
          Nat.mod_eq_of_lt (by omega_using [hm] : m+1 < 2^64)] at hh
        change (2^64-(m+1)+j)%(2^64)=0 at hh
        omega_using [hm, hjm, e, hh]
    apply WP.ite (decide (j=m+1)) (by change some (t.read .x .x2 == 0)=_; rw [z])
    · intro e
      rw [decide_eq_true_eq] at e
      subst j
      exact h t k
    · intro e
      rw [decide_eq_false_iff_not] at e
      exact choose_wp f m (by omega_using [hm]) hj (by omega_using [hjm, e]) ((k.gpr _ (by decide)).trans h19)
        fun u ku => h u (k.trans ku)
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

end

end


/-! One complete addition shared by the fifteen public table entries. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

materialize_code Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.prepChoice
materialize_code Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.storeChoice

theorem with_counter {c : Prog isa} {s : State} {Q : State → Prop}
    (h : ∀ i ∈ instrs c,clobbers i .x19=false) (w : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.gpr .x19=s.gpr .x19 := by
  obtain ⟨tr,t,e,q⟩ := w
  exact ⟨tr,t,e,q,Exec.gpr h e⟩

private theorem prep_counter : ∀ i ∈ instrs prepChoice,clobbers i .x19=false := by
  have h : prepChoice.allInstrs (fun i => decide (clobbers i .x19=false))=true := by lit_decide
  rw [Code.allInstrs_eq,List.all_eq_true] at h
  exact fun i hi => of_decide_eq_true (h i hi)

private theorem store_counter : ∀ i ∈ instrs storeChoice,clobbers i .x19=false := by
  have h : storeChoice.allInstrs (fun i => decide (clobbers i .x19=false))=true := by lit_decide
  rw [Code.allInstrs_eq,List.all_eq_true] at h
  exact fun i hi => of_decide_eq_true (h i hi)

theorem prepChoice_ok {base : Addr} {P Q : Point C} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15)
    (hi : Inputs base P Q s) (ht : Table base P Q (d-1) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 d) :
    WP isa prepChoice s fun t =>
      (Changes base loopWork s t ∧ Inputs base P Q t ∧
        PointAt base t resultPt (pair P Q ((previous d)%4) ((previous d)/4)) ∧
        PointAt base t entry (if d%4=0 then Q else P)) ∧ t.gpr .x19=s.gpr .x19 := by
  apply with_counter prep_counter
  apply choose_wp tablePrep 15 (by decide) h1 h15 h19
  intro u ku
  have W : Changes base loopWork s u := Changes.of_keeps ku (by decide)
  have I := hi.unch (W.mono loopWork_sub)
  have T : Table base P Q (d-1) u := fun j hj hjm =>
    W.table hi.scr hj (by omega_using [h15, hjm]) (ht j hj hjm)
  exact WP.mono (tablePrep_ok hc hC h1 h15 I T) fun t ⟨w,i,r,e⟩ => ⟨W.trans w,i,r,e⟩

theorem storeChoice_ok {base : Addr} {P Q : Point C} {s : State}
    {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) (hi : Inputs base P Q s)
    (ht : Table base P Q (d-1) s)
    (hp : PointAt base s resultPt (pair P Q (d%4) (d/4)))
    (h19 : s.gpr .x19=BitVec.ofNat 64 d) :
    WP isa storeChoice s fun t =>
      (Changes base arithmeticWork s t ∧ Inputs base P Q t ∧ Table base P Q d t) ∧
      t.gpr .x19=s.gpr .x19 := by
  apply with_counter store_counter
  apply choose_wp tableStore 15 (by decide) h1 h15 h19
  intro u ku
  have W : Changes base loopWork s u := Changes.of_keeps ku (by decide)
  have I := hi.unch (W.mono loopWork_sub)
  have T : Table base P Q (d-1) u := fun j hj hjm =>
    W.table hi.scr hj (by omega_using [h15, hjm]) (ht j hj hjm)
  have R := hp.of_mem ku.mem
  refine WP.mono (copy_point I.scr (store_layout h1 h15) R) fun t ⟨k,p,_⟩ => ?_
  have K := (W.mono loopWork_sub).trans (k.cover (tableWork_cover h1 h15))
  refine ⟨K,hi.unch K,fun j hj hjd => ?_⟩
  by_cases heq : j=d
  · subst j; exact p
  · have hj' : j < d := by omega_using [hjd, heq]
    exact k.point I.scr (T j hj (by omega_using [hjd, heq]))
      (fun x hx => Nat.le_trans (table_coord_bounds hj (by omega_using [h15, hjd]) x hx).2.1 (by decide))
      (earlier_table_apart hj hj')
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
