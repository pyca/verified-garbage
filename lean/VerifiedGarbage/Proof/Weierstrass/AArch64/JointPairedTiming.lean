import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
import VerifiedGarbage.Proof.Weierstrass.Joint
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoop
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.Weierstrass.AArch64.JointMixed
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Arithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Timing
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming

/-! ## `JointLoop` -/

section

/-! Shared doubling and two independent signed digits compose without an affine conversion. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)

structure JointLoopKeep (M : Mod) (base : Addr) (W : List Nat) (s t : State) : Prop where
  regs : KeepRegs (.x19::clob M.n) s t
  unch : Unch base (W.map (·,8*M.n)++[(M.tmp,8*M.n)]) s.mem t.mem

theorem JointLoopKeep.refl (M : Mod) (base : Addr) (W : List Nat) (s : State) :
    JointLoopKeep M base W s s := ⟨⟨fun _ _ => rfl,rfl,rfl,rfl⟩,fun _ _ => rfl⟩

theorem JointLoopKeep.trans {M : Mod} {base : Addr} {W : List Nat} {s t u : State}
    (h : JointLoopKeep M base W s t) (h' : JointLoopKeep M base W t u) :
    JointLoopKeep M base W s u := ⟨h.regs.trans h'.regs,fun x hx => (h'.unch x hx).trans (h.unch x hx)⟩

theorem JointLoopKeep.of_prog {M : Mod} {base : Addr} {W : List Nat} {s t : State}
    (h : ProgKeep M base W s t) : JointLoopKeep M base W s t :=
  ⟨(⟨h.gpr,h.rd,h.wr,h.sp⟩ : KeepRegs (clob M.n) s t).mono
    (fun _ hr => List.mem_cons_of_mem _ hr),h.unch⟩

/-- The loop invariant may include arbitrary stable tables and initialized cached fields. -/
structure JointOpsOk (c : Joint.Cfg) (o : Joint.Ops) (C : Curve) (base : Addr)
    (W : List Nat) (Core : Point C → State → Prop) (P Q : Point C) (u v : Nat) : Prop where
  keep : ∀ A s t, Keeps [.x19] s t → t.syms=s.syms → Core A s → Core A t
  double : ∀ A s, onCurve C A=true → Core A s →
    WP isa o.double s fun t => ProgKeep c.K.M base W s t ∧ Core (add A A) t
  peer : ∀ A j s, j<257 → onCurve C A=true → Core A s →
    s.gpr .x19=BitVec.ofNat 64 j → WP isa o.digitQ s fun t =>
      ProgKeep c.K.M base W s t ∧ Core (add A (FastNaf.point C Q 5 v j)) t
  generator : ∀ A j s, j<257 → onCurve C A=true → Core A s →
    s.gpr .x19=BitVec.ofNat 64 j → WP isa (Joint.fixedDigit c o.mixedAdd) s fun t =>
      ProgKeep c.K.M base W s t ∧ Core (add A (FastNaf.point C P 7 u j)) t

theorem jointDigits_ok {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {W : List Nat} {Core : Point C → State → Prop} {P Q : Point C} {u v j : Nat}
    (hC : Law C) (hQ : onCurve C Q=true) (hops : JointOpsOk c o C base W Core P Q u v)
    {A : Point C} (hA : onCurve C A=true) {s : State} (hs : Core A s)
    (hj : j<257) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (Joint.digits c o) s fun t => ProgKeep c.K.M base W s t ∧
      Core (add (add A (FastNaf.point C Q 5 v j)) (FastNaf.point C P 7 u j)) t := by
  rw [Joint.digits]
  apply WP.seq
  refine WP.mono (hops.peer A j s hj hA hs h19) fun a ⟨ka,ca⟩ => ?_
  refine WP.mono (hops.generator _ j a hj
    (hC.onCurve_add hA (FastNaf.onCurve_point hC hQ 5 v j)) ca
    ((ka.gpr _ (x19_not_clob _)).trans h19)) fun t ⟨kt,ct⟩ => ⟨ka.trans kt,ct⟩

theorem jointStep_ok {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {W : List Nat} {Core : Point C → State → Prop} {P Q : Point C} {u v j : Nat}
    (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hops : JointOpsOk c o C base W Core P Q u v) (hj : j<256)
    {s : State} (hs : Core (jointPoint P Q u v (j+1)) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 (j+1)) :
    WP isa (Joint.step c o) s fun t => JointLoopKeep c.K.M base W s t ∧
      Core (jointPoint P Q u v j) t ∧ t.gpr .x19=BitVec.ofNat 64 j := by
  rw [Joint.step]
  apply WP.seq
  refine WP.mono_syms (decCounter_ok s (by omega) (by omega) h19) fun a ⟨a19,ka⟩ hsym => ?_
  have ca := hops.keep _ s a ka hsym hs
  apply WP.seq
  refine WP.mono (hops.double _ a (jointPoint_curve hC hP hQ u v (j+1)) ca) fun b ⟨kb,cb⟩ => ?_
  have b19 : b.gpr .x19=BitVec.ofNat 64 j := by
    rw [kb.gpr _ (x19_not_clob _),a19,Nat.add_sub_cancel]
  refine WP.mono (jointDigits_ok hC hQ hops
    (hC.onCurve_add (jointPoint_curve hC hP hQ u v (j+1)) (jointPoint_curve hC hP hQ u v (j+1)))
    cb (by omega) b19) fun t ⟨kt,ct⟩ => ?_
  rw [jointPoint_step hC hP hQ] at ct
  have kp := kb.trans kt
  refine ⟨⟨(Keeps.regs ka).mono (by simp) |>.trans
    ((JointLoopKeep.of_prog kp).regs),?_⟩,ct,?_⟩
  · simpa only [ka.mem] using kp.unch
  · rw [kt.gpr _ (x19_not_clob _),b19]

theorem jointLoop_ok {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {W : List Nat} {Core : Point C → State → Prop} {P Q : Point C} {u v : Nat}
    (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hops : JointOpsOk c o C base W Core P Q u v)
    {s : State} (hs : Core (jointPoint P Q u v 256) s) (h19 : s.gpr .x19=256) :
    WP isa (.loop (Joint.step c o) (.nonzero .x .x19)) s fun t =>
      JointLoopKeep c.K.M base W s t ∧ Core (add (mul u P) (mul v Q)) t ∧ t.gpr .x19=0 := by
  let I := fun j t => JointLoopKeep c.K.M base W s t ∧
    Core (jointPoint P Q u v j) t ∧ t.gpr .x19=BitVec.ofNat 64 j
  apply countLoop_ok (Inv:=I) (n:=256) (by decide)
  · intro j a hj1 hj256 hi
    obtain ⟨ka,ca,a19⟩ := hi
    have he : j-1+1=j := by omega
    refine WP.mono (jointStep_ok hC hP hQ hops (by omega) (he.symm ▸ ca) (he.symm ▸ a19))
      fun t ⟨kt,ct,t19⟩ => ⟨⟨ka.trans kt,ct,t19⟩,t19⟩
  · intro t ht
    obtain ⟨kt,ct,t19⟩ := ht
    rw [jointPoint_zero] at ct
    exact ⟨kt,ct,t19⟩
  · decide
  · exact ⟨JointLoopKeep.refl _ _ _ _,hs,h19⟩

/-- Seed the possible carry digit, then consume all 256 remaining positions. -/
theorem jointRun_ok {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {W : List Nat} {Core : Point C → State → Prop} {P Q : Point C} {u v : Nat}
    (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hops : JointOpsOk c o C base W Core P Q u v) (hu : u<2^256) (hv : v<2^256)
    {s : State} (hs : Core .infinity s) (h19 : s.gpr .x19=256) :
    WP isa (Joint.run c o) s fun t => JointLoopKeep c.K.M base W s t ∧
      Core (add (mul u P) (mul v Q)) t ∧ t.gpr .x19=0 := by
  rw [Joint.run]
  apply WP.seq
  refine WP.mono (jointDigits_ok hC hQ hops (A:=.infinity) rfl hs (by decide) h19)
    fun a ⟨ka,ca⟩ => ?_
  have he := jointPoint_step hC hP hQ u v 256
  rw [jointPoint_top P Q hu hv] at he
  change add (add .infinity (FastNaf.point C Q 5 v 256))
    (FastNaf.point C P 7 u 256)=jointPoint P Q u v 256 at he
  rw [he] at ca
  refine WP.mono (jointLoop_ok hC hP hQ hops ca
    ((ka.gpr _ (x19_not_clob _)).trans h19)) fun t ⟨kt,ct,t19⟩ =>
      ⟨(JointLoopKeep.of_prog ka).trans kt,ct,t19⟩

end VG.Proof.Weierstrass.AArch64

end

/-! ## `JointLoopTiming` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (read_x)

/-- A paired invariant includes both public digit streams and a common field environment. -/
theorem jointLoop_relCT {c : Joint.Cfg} {o : Joint.Ops}
    (R : Nat → State → State → Prop)
    (counter : ∀ j s t, R j s t → s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
    (step : ∀ j, j<256 → RelCT isa (R (j+1)) (Joint.step c o) (R j)) :
    RelCT isa (R 256) (.loop (Joint.step c o) (.nonzero .x .x19)) (R 0) := by
  let I := fun j s t => 1≤j ∧ j≤256 ∧ R j s t
  have hs : ∀ j, RelCT isa (I j) (Joint.step c o) (fun s t =>
      eval (.nonzero .x .x19) s=eval (.nonzero .x .x19) t ∧
      (eval (.nonzero .x .x19) s=some false → R 0 s t) ∧
      (eval (.nonzero .x .x19) s=some true → ∃ n<j,I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hj256 : j≤256
      · refine (step (j-1) (by omega)).mono
          (P':=I j) (fun _ _ h => by simpa only [Nat.sub_add_cancel hj] using h.2.2) ?_
        intro s t hp
        obtain ⟨s19,t19⟩ := counter (j-1) s t hp
        refine ⟨by simp only [eval,State.read,s19,t19],fun he => ?_,fun he => ?_⟩
        · have hz : j-1=0 := by
            by_contra hn
            have hb : (BitVec.ofNat 64 (j-1) != 0)=true := by
              rw [bne_iff_ne]
              intro hh
              have hh' := congrArg BitVec.toNat hh
              simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : j-1<2^64)] at hh'
              exact hn hh'
            have htrue : eval (.nonzero .x .x19) s=some true := by
              change some (s.read .x .x19 != 0)=some true
              rw [read_x,s19,hb]
            rw [htrue] at he; cases he
          exact hz ▸ hp
        · have hz : j-1≠0 := by
            intro hz; simp only [eval,State.read,s19,hz] at he; cases he
          exact ⟨j-1,by omega,by omega,by omega,hp⟩
      · exact RelCT.of_false (fun _ _ h => hj256 h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  exact (RelCT.loop I hs 256).mono (fun _ _ h => ⟨by decide,by decide,h⟩) (fun _ _ h => h)

theorem jointRun_relCT {c : Joint.Cfg} {o : Joint.Ops}
    {Pre : State → State → Prop} (R : Nat → State → State → Prop)
    (counter : ∀ j s t, R j s t → s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
    (seed : RelCT isa Pre (Joint.digits c o) (R 256))
    (step : ∀ j, j<256 → RelCT isa (R (j+1)) (Joint.step c o) (R j)) :
    RelCT isa Pre (Joint.run c o) (R 0) :=
  RelCT.seq seed (jointLoop_relCT R counter step)

end VG.Proof.Weierstrass.AArch64

end

/-! ## `JointMixed` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

theorem jointMixedAdd_ok (certs : Forward.Arithmetic.Cases) {K : WinCfg} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hnc : Mont.callOf K.M = none)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hsize : 8192≤size) (hC : Law C) (ha : AM3 C)
    {p q o : Pt} (hA : RcbApart K.S p q o)
    (hSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hV : ∀ x ∈ rcbR K.S p q, x ∈ V)
    (hOne : K.one < C.p) {P Q : Point C} (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (hJP : InvJ C (E p.x) (E p.y) (E p.z) P) (hJQ : InvJ C (E q.x) (E q.y) (E q.z) Q) (hAff : E q.z=1) :
    WP isa (Joint.mixedAdd K p q o) s
      (JacPost K.M K.S base size C Sl V o (Spec.Weierstrass.add P Q) s) := by
  rw [Joint.mixedAdd]
  apply fieldBranch_ok hL hAl hm hI (hV p.z (by simp [rcbR]))
  · intro a ia ka hz
    have hp := (hJP.z_zero_iff hC).mp hz
    rw [hp]
    exact WP.mono (copyPointJ_ok hL hAl hA hSl ia hV hJQ)
      (fun t ht => ht.prefix (ka.mono (by simp)))
  · intro a ia ka hpz
    have hqz : E q.z ≠ 0 := by rw [hAff]; exact hC.one_ne_zero
    apply WP.seq
    refine WP.mono (jacMixedInit_ok hL hAl hSl ia hV) fun b ⟨kb,ib⟩ => ?_
    apply WP.seq
    refine WP.mono (Forward.Arithmetic.contract certs ib.scr hsize
      ((fprogB_wp _ _ hnc).mpr (jacMixedHead_ok hL hAl hm hA hSl ib hV))) fun c ⟨kc,ic,eh,er⟩ => ?_
    let EH := runOps (jacMixedHead K.S p q) (jacMixedInit K.S p E)
    have hkeep := (ka.mono (W' := rcbW K.S o) (by simp)).trans
      ((kb.mono (by simp)).trans kc)
    have hpkeep : ∀ x ∈ rcbR K.S p q, EH x = E x := fun x hx => jacMixedHead_readonly hA E hx
    have jp : InvJ C (EH p.x) (EH p.y) (EH p.z) P := by
      rw [hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR])]
      exact hJP
    have oldV : ∀ x ∈ V, x ∈ validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V) :=
      fun x hx => (mem_validAfter _ _).mpr (Or.inl (by simp [hx]))
    have hv : ∀ x ∈ rcbR K.S p p, x ∈ validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V) :=
      fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
    apply fieldBranch_ok hL hAl hm ic (a := K.S.t3) (by
      rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out])
    · intro d id kd hz
      have hx : E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)=0 := by simpa only [hAff,Lean.Grind.Semiring.mul_one] using eh.symm.trans hz
      apply fieldBranch_ok hL hAl hm id (a := K.S.t5) (by
        rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out])
      · intro e ie ke hrz
        have hy : E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z)=0 := by simpa only [hAff,Lean.Grind.Semiring.mul_one] using er.symm.trans hrz
        have hpq := hJP.same hC hJQ hpz hqz hx hy
        have hdA : RcbApart K.S p p o := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
        have hdSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p p, Sl x := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hSl x (List.mem_append_left _ hx)
          · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
        rw [←hpq]
        refine WP.mono (Forward.double_ok Forward.Production.cases hL hAl hnc hm hC ha hdA hdSl ie hv hP jp) fun t ⟨kt,it,jt⟩ => ?_
        exact (JacPost.sub ⟨_,kt,it,jt⟩ oldV).prefix
          (hkeep.trans ((kd.mono (by simp)).trans (ke.mono (by simp))))
      · intro e ie ke hrz
        have hy : E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z)≠0 := by
          intro he
          apply hrz
          rw [er]
          simpa only [hAff,Lean.Grind.Semiring.mul_one] using he
        have hadd := hJP.opposite hC hP hQ hJQ hpz hqz hx hy
        rw [hadd]
        refine WP.mono (infinityPoint_ok hL hAl
          (fun x hx => hSl x (by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
            rcases hx with rfl | rfl | rfl <;> simp [rcbW])) ie hOne) fun t ht => ?_
        exact (JacPost.sub ht oldV).prefix
          (hkeep.trans ((kd.mono (by simp)).trans (ke.mono (by simp))))
    · intro d id kd hz
      have hh : E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)≠0 := by
        intro he
        apply hz
        rw [eh]
        simpa only [hAff,Lean.Grind.Semiring.mul_one] using he
      refine WP.mono (Forward.Arithmetic.contract certs id.scr hsize
        ((fprogB_wp _ _ hnc).mpr (jacMixedTail_ok hL hAl hm hA hSl id hV))) fun t ⟨kt,it,ht⟩ => ?_
      have jt := hJP.add_ne hC ha hP hQ hJQ hpz hqz hh
      dsimp only at jt
      rw [hAff,←ht] at jt
      exact JacPost.prefix ⟨_,kt,it,jt⟩ (hkeep.trans (kd.mono (by simp)))

end VG.Proof.Weierstrass.AArch64

end

/-! ## `JointMixedTiming` -/

section

/-! Public-data mixed Jacobian addition retains a common field environment. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

structure JointMixedChecks (K : WinCfg) (p q o : Pt) : Prop where
  zero : ∀ a∈[p.z,K.S.t3,K.S.t5], FieldCT (.block (zeroMask K.M.n a))
  copyQ : FieldCT (.block (copyPt K.M.n o q))
  init : FieldCT (.block (copy K.M.n K.S.t2 p.x ++ copy K.M.n K.S.t4 p.y))
  head : FieldCT (VG.Impl.P256.VerifyArithmetic.program K.M (jacMixedHead K.S p q))
  tail : FieldCT (VG.Impl.P256.VerifyArithmetic.program K.M (jacMixedTail K.S p q o))
  double : FieldCT (VG.Impl.P256.VerifyDouble.double K.M K.S p o)
  infinity : FieldCT (.block (Jacobian.infinity K o))

theorem jointMixedAdd_relCT (certs : Forward.Arithmetic.Cases) {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hnc : Mont.callOf K.M = none)
    (hm : UnitMod m (2^(64*K.M.n))) (hsize : 8192≤size) {p q o : Pt} (hA : RcbApart K.S p q o)
    (hSl : ∀ x∈rcbW K.S o ++ rcbR K.S p q, Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR K.S p q, x∈V)
    (hOne : K.one<m) (hc : JointMixedChecks K p q o) :
    RelCT isa (FieldPair K.M base size m Sl V E) (Joint.mixedAdd K p q o)
      (fun s t => ∃ E', FieldPair K.M base size m Sl ([o.x,o.y,o.z]++V) E' s t) := by
  have os : ∀ x∈[o.x,o.y,o.z], Sl x := by
    intro x hx; apply hSl x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbW]
  have pv : ∀ x∈[p.x,p.y,p.z], x∈V := by
    intro x hx; apply hV x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbR]
  have qv : ∀ x∈[q.x,q.y,q.z], x∈V := by
    intro x hx; apply hV x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbR]
  rw [Joint.mixedAdd]
  apply fieldBranch_relCT hL hAl hm (pv _ (by simp)) (hc.zero _ (by simp))
  · intro _
    exact (copyPoint_relCT hL hAl os qv hc.copyQ).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
  · intro _
    have hi : RelCT isa (FieldPair K.M base size m Sl V E)
        (.block (copy K.M.n K.S.t2 p.x ++ copy K.M.n K.S.t4 p.y))
        (FieldPair K.M base size m Sl (K.S.t4::K.S.t2::V) (jacMixedInit K.S p E)) := by
      apply fieldWP_relCT hc.init
      intro s hs
      exact WP.mono (jacMixedInit_ok hL hAl hSl hs hV) fun _ ⟨hk,it⟩ => ⟨it,hk.sp⟩
    apply RelCT.seq hi
    have hh : RelCT isa (FieldPair K.M base size m Sl (K.S.t4::K.S.t2::V) (jacMixedInit K.S p E)) (VG.Impl.P256.VerifyArithmetic.program K.M (jacMixedHead K.S p q))
        (FieldPair K.M base size m Sl (validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V)) (runOps (jacMixedHead K.S p q) (jacMixedInit K.S p E))) := by
      apply fieldWP_relCT hc.head
      intro s hi
      exact WP.mono (Forward.Arithmetic.contract certs hi.scr hsize
        ((fprogB_wp _ _ hnc).mpr (jacMixedHead_ok hL hAl hm hA hSl hi hV))) fun _ ⟨hk,it,_,_⟩ => ⟨it,hk.sp⟩
    apply RelCT.seq hh
    have oldV : ∀ x∈V, x∈validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V) :=
      fun x hx => (mem_validAfter _ _).mpr (Or.inl (by simp [hx]))
    have subV : ∀ x∈[o.x,o.y,o.z]++V, x∈[o.x,o.y,o.z]++validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V) := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (oldV x hx)
    apply fieldBranch_relCT hL hAl hm (a:=K.S.t3) (by
      rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out]) (hc.zero _ (by simp))
    · intro _
      apply fieldBranch_relCT hL hAl hm (a:=K.S.t5) (by
        rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out]) (hc.zero _ (by simp))
      · intro _
        have hdA : RcbApart K.S p p o := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
        have hdSl : ∀ x∈rcbW K.S o ++ rcbR K.S p p, Sl x := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hSl x (List.mem_append_left _ hx)
          · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
        have hv : ∀ x∈rcbR K.S p p, x∈validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V) :=
          fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
        have hd := Forward.field_outputs_relCT Forward.Production.cases (base:=base) (E:=runOps (jacMixedHead K.S p q) (jacMixedInit K.S p E)) hL hAl hnc hm hdA hdSl hv hc.double
        exact hd.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
      · intro _
        exact (infinity_relCT hL hAl os hOne hc.infinity).mono
          (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
    · intro _
      have ht : RelCT isa
          (FieldPair K.M base size m Sl (validAfter (jacMixedHead K.S p q) (K.S.t4::K.S.t2::V)) (runOps (jacMixedHead K.S p q) (jacMixedInit K.S p E)))
          (VG.Impl.P256.VerifyArithmetic.program K.M (jacMixedTail K.S p q o))
          (FieldPair K.M base size m Sl ([o.x,o.y,o.z]++V)
            (runOps (jacMixedHead K.S p q ++ jacMixedTail K.S p q o) (jacMixedInit K.S p E))) := by
        apply fieldWP_relCT hc.tail
        intro s hi
        exact WP.mono (Forward.Arithmetic.contract certs hi.scr hsize
          ((fprogB_wp _ _ hnc).mpr (jacMixedTail_ok hL hAl hm hA hSl hi hV))) fun _ ⟨hk,it,_⟩ => ⟨it,hk.sp⟩
      exact ht.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)

end VG.Proof.Weierstrass.AArch64

end

/-! ## `JointPairedTiming` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 Spec.Weierstrass

def JointPair (c : Joint.Cfg) (C : Curve) (base : Addr) (size : Nat)
    (Core : Point C → State → Prop) (A : Point C) (j : Nat) (s t : State) : Prop :=
  (∃ E,FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t) ∧
    Core A s ∧ Core A t ∧ s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j

/-- Attach the point invariant and preserved counter to a field-level timing proof. -/
theorem jointPair_stage {c : Joint.Cfg} {C : Curve} {base : Addr} {size j : Nat}
    {Core : Point C → State → Prop} {A B : Point C} {code : Prog isa} {W : List Nat}
    (hw : ∀ s, Core A s → s.gpr .x19=BitVec.ofNat 64 j →
      WP isa code s fun t => ProgKeep c.K.M base W s t ∧ Core B t)
    (ht : ∀ E,RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      Core A s ∧ Core A t ∧ s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      code (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t)) :
    RelCT isa (JointPair c C base size Core A j) code (JointPair c C base size Core B j) := by
  intro s t ts tt s' t' ⟨⟨E,hp⟩,cs,ct,ps,pt⟩ es et
  obtain ⟨he,hp'⟩ := ht E _ _ _ _ _ _ ⟨hp,cs,ct,ps,pt⟩ es et
  obtain ⟨_,_,xs,ks,cs'⟩ := hw s cs ps
  obtain ⟨_,_,xt,kt,ct'⟩ := hw t ct pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨he,hp',cs',ct',(ks.gpr _ (x19_not_clob _)).trans ps,
    (kt.gpr _ (x19_not_clob _)).trans pt⟩

structure JointOpsTiming (c : Joint.Cfg) (o : Joint.Ops) (C : Curve) (base : Addr)
    (size : Nat) (Core : Point C → State → Prop) : Prop where
  double : ∀ A j E,RelCT isa (fun s t =>
    FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
    Core A s ∧ Core A t ∧ s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
    o.double (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t)
  peer : ∀ A j,j<257 → ∀ E,RelCT isa (fun s t =>
    FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
    Core A s ∧ Core A t ∧ s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
    o.digitQ (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t)
  generator : ∀ A j,j<257 → ∀ E,RelCT isa (fun s t =>
    FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
    Core A s ∧ Core A t ∧ s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
    (Joint.fixedDigit c o.mixedAdd)
    (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t)

theorem jointPair_digits {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {size u v j : Nat} {W : List Nat} {Core : Point C → State → Prop} {P Q A : Point C}
    (hC : Law C) (hQ : onCurve C Q=true) (hA : onCurve C A=true) (hj : j<257)
    (hw : JointOpsOk c o C base W Core P Q u v) (ht : JointOpsTiming c o C base size Core) :
    RelCT isa (JointPair c C base size Core A j) (Joint.digits c o)
      (JointPair c C base size Core (add (add A (FastNaf.point C Q 5 v j)) (FastNaf.point C P 7 u j)) j) := by
  apply RelCT.seq (jointPair_stage (fun s hs h19 => hw.peer A j s hj hA hs h19) (ht.peer A j hj))
  exact jointPair_stage (fun s hs h19 => hw.generator _ j s hj
    (hC.onCurve_add hA (FastNaf.onCurve_point hC hQ 5 v j)) hs h19) (ht.generator _ j hj)

theorem jointPair_counter {c : Joint.Cfg} {C : Curve} {base : Addr} {size j : Nat}
    {Core : Point C → State → Prop} {A : Point C}
    (hkeep : ∀ A s t,VG.Proof.Ed25519.AArch64.Keeps [.x19] s t → t.syms=s.syms → Core A s → Core A t)
    (hj : j<256)
    (hc : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x19])) (.block [decCounter])) :
    RelCT isa (JointPair c C base size Core A (j+1)) (.block [decCounter])
      (JointPair c C base size Core A j) := by
  intro s t ts tt s' t' ⟨⟨E,hp⟩,cs,ct,ps,pt⟩ es et
  obtain ⟨_,_,xs,s19,ks⟩ := decCounter_ok s (by omega) (by omega) ps
  obtain ⟨_,_,xt,t19,kt⟩ := decCounter_ok t (by omega) (by omega) pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  have he : ts=tt := hc _ _ _ _ _ _ trivial trivial ⟨hp.sp,fun r hr => by
    simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
    subst hr
    exact ps.trans pt.symm⟩ es et
  refine ⟨he,⟨E,hp.left.of_keeps ks (by decide),hp.right.of_keeps kt (by decide),
    ks.sp.trans (hp.sp.trans kt.sp.symm)⟩,hkeep A _ _ ks (Exec.syms es) cs,hkeep A _ _ kt (Exec.syms et) ct,?_,?_⟩
  · simpa only [Nat.add_sub_cancel] using s19
  · simpa only [Nat.add_sub_cancel] using t19

theorem jointPair_step {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {size u v j : Nat} {W : List Nat} {Core : Point C → State → Prop} {P Q : Point C}
    (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true) (hj : j<256)
    (hw : JointOpsOk c o C base W Core P Q u v) (ht : JointOpsTiming c o C base size Core)
    (hc : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x19])) (.block [decCounter])) :
    RelCT isa (JointPair c C base size Core (jointPoint P Q u v (j+1)) (j+1))
      (Joint.step c o) (JointPair c C base size Core (jointPoint P Q u v j) j) := by
  have hA := jointPoint_curve hC hP hQ u v (j+1)
  apply RelCT.seq (jointPair_counter hw.keep hj hc)
  apply RelCT.seq (jointPair_stage (fun s hs _ => hw.double _ s hA hs) (ht.double _ j))
  simpa only [jointPoint_step hC hP hQ] using
    jointPair_digits hC hQ (hC.onCurve_add hA hA) (by omega : j<257) hw ht

theorem jointPair_run {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {size u v : Nat} {W : List Nat} {Core : Point C → State → Prop} {P Q : Point C}
    (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hu : u<2^256) (hv : v<2^256)
    (hw : JointOpsOk c o C base W Core P Q u v) (ht : JointOpsTiming c o C base size Core)
    (hc : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x19])) (.block [decCounter])) :
    RelCT isa (JointPair c C base size Core .infinity 256) (Joint.run c o)
      (JointPair c C base size Core (add (mul u P) (mul v Q)) 0) := by
  have seed := jointPair_digits (j:=256) (A:=.infinity) hC hQ rfl (by decide) hw ht
  have he := jointPoint_step hC hP hQ u v 256
  rw [jointPoint_top P Q hu hv] at he
  change add (add .infinity (FastNaf.point C Q 5 v 256))
    (FastNaf.point C P 7 u 256)=jointPoint P Q u v 256 at he
  rw [he] at seed
  have out := jointRun_relCT (c:=c) (o:=o)
    (fun j => JointPair c C base size Core (jointPoint P Q u v j) j)
    (fun _ _ _ h => ⟨h.2.2.2.1,h.2.2.2.2⟩) seed
    (fun j hj => jointPair_step hC hP hQ hj hw ht hc)
  simpa only [jointPoint_zero] using out

end VG.Proof.Weierstrass.AArch64

end
