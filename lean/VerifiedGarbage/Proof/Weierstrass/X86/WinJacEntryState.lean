module

public import VerifiedGarbage.Proof.Weierstrass.X86.WinJacBuildState
public import VerifiedGarbage.Proof.Weierstrass.JacCoZ
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Weierstrass.X86.JacState
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Weierstrass.X86.WinJac
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Weierstrass.X86.NafAdjust
import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! ### `Weierstrass.X86.WinJacCoZField`, which only this module used -/

section

/-! Co-Z table arithmetic in the existing x86 scratch layout. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

/-- DBLU on numbered slots (`tblσ`). -/
def dbluN : List FOp :=
  [.mul 0 18 18, .mul 1 19 19, .mul 2 1 1, .mul 3 18 1, .add 3 3 3, .add 3 3 3, .sub 4 0 20,
   .add 5 4 4, .add 4 5 4, .mul 12 4 4, .sub 12 12 3, .sub 12 12 3, .sub 5 3 12, .mul 13 4 5,
   .add 2 2 2, .add 2 2 2, .add 2 2 2, .sub 13 13 2, .add 14 19 19, .mul 15 14 14, .mul 16 15 14]

/-- ZADDU on numbered slots (`tblσ`). -/
def zadduN : List FOp :=
  [.sub 0 9 12, .mul 1 0 0, .mul 14 14 0, .mul 9 9 1, .mul 3 12 1, .sub 4 10 13, .mul 5 4 4,
   .sub 2 9 3, .mul 10 10 2, .sub 12 5 9, .sub 12 12 3, .sub 13 9 12, .mul 13 4 13, .sub 13 13 10,
   .mul 15 15 1, .mul 16 15 14]

/-- DBLU from `P = (x, y, 1)`: `T = 2 P` with its powers, and `(t3, t2)` is
`P` scaled by `T`'s `Z`. -/
theorem dbluN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) (h20 : e 20 = 1) :
    (runOps dbluN e 12, runOps dbluN e 13, runOps dbluN e 14) = dblJF (e 18) (e 19) 1 ∧
      runOps dbluN e 15 = runOps dbluN e 14 * runOps dbluN e 14 ∧
      runOps dbluN e 16 = runOps dbluN e 15 * runOps dbluN e 14 ∧
      runOps dbluN e 3 * (1 * 1) = e 18 * (runOps dbluN e 14 * runOps dbluN e 14) ∧
      runOps dbluN e 2 * (1 * 1 * 1) =
        e 19 * (runOps dbluN e 14 * runOps dbluN e 14 * runOps dbluN e 14) := by
  simp only [dbluN, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, h20, dblJF, Prod.mk.injEq]
  refine ⟨⟨?_, ?_, ?_⟩, trivial, trivial, ?_, ?_⟩ <;> grind

/-- ZADDU of `D = (X1, Y1)` and `T = (X2, Y2)` sharing `Z`, with `T`'s powers. -/
theorem zadduN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    ((runOps zadduN e 12, runOps zadduN e 13, runOps zadduN e 14), (runOps zadduN e 9, runOps zadduN e 10)) =
        zadduF (e 9) (e 10) (e 12) (e 13) (e 14) ∧
      (e 15 = e 14 * e 14 → runOps zadduN e 15 = runOps zadduN e 14 * runOps zadduN e 14) ∧
      runOps zadduN e 16 = runOps zadduN e 15 * runOps zadduN e 14 := by
  simp only [zadduN, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, zadduF]
  refine ⟨?_, fun h => ?_, ?_⟩ <;> first | trivial | grind


/-- Co-Z numbered slots use the existing work-list order, then the affine input. -/
def coσ (K : JacWinCfg) (i : Nat) : Nat :=
  (work K ++ [K.P.x,K.P.y,K.P.z]).getD i K.P.x

theorem coP_readonly {K : JacWinCfg} {size wk : Nat} (hL : Layout K size wk) :
    ∀ x∈[K.P.x,K.P.y,K.P.z],x∉work K := by
  intro x hx
  exact hL.readonly x (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [ro])

/-- Run a numbered co-Z formula without making a second scratch layout. -/
theorem coProg_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) {N : List FOp}
    (hout : ∀ op∈N,op.out<18)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base size C.p (·∈slots K) V E s)
    (hr : readsOk (N.map (FOp.rename (coσ K))) V=true) :
    WP isa (fprog K.F (N.map (FOp.rename (coσ K)))) s fun t =>
      ProgKeep K.M base wk (work K) s t ∧
      Inv K.M base size C.p (·∈slots K)
        (validAfter (N.map (FOp.rename (coσ K))) V)
        (runOps (N.map (FOp.rename (coσ K))) E) t ∧
      (∀ i,runOps (N.map (FOp.rename (coσ K))) E (coσ K i)=
        runOps N (fun j => E (coσ K j)) i) := by
  obtain hp := coP_readonly hL
  obtain hinj : ∀ op∈N,∀ y,coσ K y=coσ K op.out → y=op.out := fun op ho y =>
    getD_append_inj hL.nd hp (hp _ (List.mem_cons_self ..)) (hout op ho) y
  obtain hmem : ∀ i,coσ K i∈slots K := by
    intro i
    obtain hx := getD_append_mem (W:=work K) (List.mem_cons_self (a:=K.P.x) (l:=[K.P.y,K.P.z])) i
    rcases List.mem_append.mp hx with h|h
    · exact List.mem_append_right _ h
    · apply List.mem_append_left
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with h|h|h <;> simp only [coσ,h] <;> simp [ro]
  obtain hS : ∀ op∈N.map (FOp.rename (coσ K)),∀ x∈op.out::op.ins,x∈slots K := by
    intro op ho
    obtain ⟨op',_,rfl⟩ := List.mem_map.mp ho
    cases op' <;> simp only [FOp.rename,FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] <;>
      rintro x (rfl|rfl|rfl) <;> exact hmem _
  refine WP.mono (fprog_ok hL.lay hW hm _ hi hS hr) fun t ⟨kt,it⟩ =>
    ⟨kt.mono ?_,it,?_⟩
  · intro x hx
    obtain ⟨op,ho,rfl⟩ := List.mem_map.mp hx
    obtain ⟨op',ho',rfl⟩ := List.mem_map.mp ho
    rw [FOp.out_rename]
    unfold coσ
    rw [getD_append_left (by simpa only [work,temps,List.length_append,List.length_cons,List.length_nil] using hout op' ho')]
    exact List.getElem_mem _
  · exact fun i => congrFun (runOps_rename (coσ K) N E hinj) i


theorem dblu_eq (K : JacWinCfg) : K.dbluOps=dbluN.map (FOp.rename (coσ K)) := rfl

theorem zaddu_eq (K : JacWinCfg) : K.zadduOps=zadduN.map (FOp.rename (coσ K)) := rfl

theorem dbluN_out : ∀ op∈dbluN,op.out<18 := by decide
theorem zadduN_out : ∀ op∈zadduN,op.out<18 := by decide
theorem dbluN_reads : readsOk dbluN [18,19,20]=true := by decide
theorem zadduN_reads : readsOk zadduN [9,10,12,13,14,15]=true := by decide

end VG.Proof.Weierstrass.X86.JWin

end

end

/-! ### `Weierstrass.X86.WinJacBuildInit`, which only this module used -/

section

/-! Initialize the cached table point from an affine input. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

private theorem coord_mem (K : JacWinCfg) {c : Nat} (hc : c<5) : K.T+32*c∈work K := by
  have : c=0 ∨ c=1 ∨ c=2 ∨ c=3 ∨ c=4 := by omega_arith
  rcases this with rfl|rfl|rfl|rfl|rfl <;> simp [work,JacWinCfg.E,JacWinCfg.z2,JacWinCfg.z3]

/-- Copy affine XYZ and use its unit Z for both cached powers. -/
theorem build_copy_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s : State} (hI : Inv K.M base size C.p (·∈slots K) (ro K) (tmv C K.M.n base s) s)
    {P : Point C} (hJ : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) (hz : tmv C K.M.n base s K.P.z=1) (hC : Law C) :
    WP isa (.block (copyPt 4 K.E K.P++copy 8 K.z2 K.P.z++copy 8 K.z3 K.P.z)) s fun t =>
      Cached C base t (fun c => K.T+32*c) P ∧ Frame K C base size wk s t := by
  have cs (c : Nat) (hc : c<5) : K.T+32*c∈slots K := List.mem_append_right _ (coord_mem K hc)
  obtain px : K.P.x∈ro K := by simp [ro]
  obtain py : K.P.y∈ro K := by simp [ro]
  obtain pz : K.P.z∈ro K := by simp [ro]
  have sep (x : Nat) (hx : x∈ro K) (c : Nat) (hc : c<5) : x≠K.T+32*c :=
    fun he => hL.readonly x hx (he ▸ coord_mem K hc)
  obtain spy : K.P.y≠K.T := by simpa using sep K.P.y py 0 (by decide)
  obtain spz := sep K.P.z pz
  obtain spz0 : K.P.z≠K.T := by simpa using spz 0 (by decide)
  simp only [copyPt,List.append_assoc]
  rw [WP.block_append_iff]
  obtain n8 : 2*K.M.n=8 := by rw [hL.n]
  obtain step := copyField_ok hL.lay hW hI (cs 0 (by decide)) px
  simp only [n8,Nat.reduceMul,Nat.add_zero] at step
  refine WP.mono step
    fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  obtain step := copyField_ok hL.lay hW ia (cs 1 (by decide)) (List.mem_cons_of_mem _ py)
  simp only [n8,Nat.reduceMul] at step
  refine WP.mono step fun b ⟨kb,ib⟩ => ?_
  rw [WP.block_append_iff]
  obtain step := copyField_ok hL.lay hW ib (cs 2 (by decide)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ pz))
  simp only [n8,Nat.reduceMul] at step
  refine WP.mono step fun c ⟨kc,ic⟩ => ?_
  rw [WP.block_append_iff]
  obtain step := copyField_ok hL.lay hW ic (cs 3 (by decide)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ pz)))
  simp only [n8,Nat.reduceMul] at step
  refine WP.mono step fun d ⟨kd,id⟩ => ?_
  obtain step := copyField_ok hL.lay hW id (cs 4 (by decide)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ pz))))
  simp only [n8,Nat.reduceMul] at step
  refine WP.mono step
    fun t ⟨kt,it⟩ => ?_
  obtain hs : ∀ x∈[K.E.x,K.E.y,K.E.z,K.z2,K.z3],x∈work K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl <;> simp [work]
  obtain kk : ProgKeep K.M base wk [K.E.x,K.E.y,K.E.z,K.z2,K.z3] s t :=
    (progKeep_of_op ka (by simp [JacWinCfg.E])).trans
      ((progKeep_of_op kb (by simp [JacWinCfg.E])).trans
        ((progKeep_of_op kc (by simp [JacWinCfg.E])).trans
          ((progKeep_of_op kd (by simp [JacWinCfg.z2])).trans (progKeep_of_op kt (by simp [JacWinCfg.z3])))))
  refine ⟨?_,(Frame.refl hI.scr hI.mod).field hL hW kk hs⟩
  apply Cached.of_inv hL.n it
  · intro c hc
    have : c=0 ∨ c=1 ∨ c=2 ∨ c=3 ∨ c=4 := by omega_arith
    rcases this with rfl|rfl|rfl|rfl|rfl <;> simp
  all_goals
    simp only [JacWinCfg.E,JacWinCfg.z2,JacWinCfg.z3,Function.update_apply]
    simp only [spy,spz0,spz 1 (by decide),spz 2 (by decide),spz 3 (by decide),ite_false]
    simp (disch := omega_arith) only [ite_eq_right,ite_true]
  · exact hJ
  · rw [hz]; exact hC.one_ne_zero
  · rw [hz]; grind
  · rw [hz]; grind

/-- The first packed entry is the input point, with no field multiplications. -/
theorem build_init_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s : State} (hI : Inv K.M base size C.p (·∈slots K) (ro K) (tmv C K.M.n base s) s)
    {P : Point C} (hJ : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) (hz : tmv C K.M.n base s K.P.z=1) (hC : Law C) :
    WP isa (.block (copyPt 4 K.E K.P++copy 8 K.z2 K.P.z++copy 8 K.z3 K.P.z++
      ([.mov .esi (.imm 1)] : List Instr)++K.storeEntry)) s (BuildInv K C base size wk P s 1) := by
  rw [WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (build_copy_ok hL hW hI hJ hz hC) fun a ⟨pa,fa⟩ => ?_
  refine WP.mono (mov_counter_ok a 1) fun b ⟨cb,kb⟩ => ?_
  apply build_store_ok hL hW (fa.keeps kb) (m:=0) (by decide) cb
  · intro m h1 hm; omega_arith
  · rw [show 0+1=1 from rfl,mul_one_pt]
    exact pa.congr fun _ _ => by rw [kb.2.1]

end VG.Proof.Weierstrass.X86.JWin

end

end

/-! ### `Weierstrass.X86.WinJacDouble`, which only this module used -/

section

/-! In-place doubling for the secret-scalar Jacobian window loop. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

def dblN : List FOp := dblJMul ⟨9,10,0,1,2,3,4,5⟩ ⟨6,7,8⟩ ⟨6,7,8⟩
def dblσ (S : RcbSlots) (p : Pt) (i : Nat) : Nat := (rcbW S p).getD i S.a

theorem dbl_eq (S : RcbSlots) (p : Pt) : dblJMul S p p = dblN.map (FOp.rename (dblσ S p)) := rfl

theorem dblN_out : ∀ op∈dblN,op.out<9 := by decide

theorem dblN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps dblN e 6,runOps dblN e 7,runOps dblN e 8)=dblJF (e 6) (e 7) (e 8) := by
  dsimp only [dblN,dblJMul,runOps,List.foldl,FOp.run,Function.update]
  simp only [dblJF,Prod.mk.injEq]
  constructor
  · grind
  constructor <;> grind

theorem dbl_run {F : Type _} [Lean.Grind.CommRing F] {S : RcbSlots} {p : Pt}
    (hN : (rcbW S p).Nodup) (ha : S.a∉rcbW S p) (e : Nat → F) :
    (runOps (dblJMul S p p) e p.x,runOps (dblJMul S p p) e p.y,
      runOps (dblJMul S p p) e p.z)=dblJF (e p.x) (e p.y) (e p.z) := by
  rw [dbl_eq]
  have inj {w : Nat} (hw : w<9) (y : Nat) (he : dblσ S p y=dblσ S p w) : y=w :=
    getD_append_inj (R:=[]) hN (by simp) ha hw y (by simpa only [List.append_nil,dblσ] using he)
  obtain he := runOps_rename (dblσ S p) dblN e (fun op hop => inj (dblN_out op hop))
  exact (congrArg₂ Prod.mk (congrFun he 6)
    (congrArg₂ Prod.mk (congrFun he 7) (congrFun he 8))).trans (dblN_run (fun i => e (dblσ S p i)))

theorem dbl_field_ok {K : JacWinCfg} {base : Addr} {size wk : Nat} {C : Curve} {Sl : Nat → Prop}
    (hL : Lay K.M size Sl) (hW : WkOk K.F K.M C.p size wk Sl)
    (hm : UnitMod C.p (2^(64*K.M.n)))
    {p : Pt} (hN : (rcbW K.S p).Nodup) (hA : K.S.a∉rcbW K.S p)
    (hSl : ∀ x∈rcbW K.S p,Sl x) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hV : ∀ x∈[p.x,p.y,p.z],x∈V) :
    WP isa (K.dbl p) s fun t => ProgKeep K.M base wk (rcbW K.S p) s t ∧
      Inv K.M base size C.p Sl ([p.x,p.y,p.z]++V) (runOps (dblJMul K.S p p) E) t ∧
      (runOps (dblJMul K.S p p) E p.x,runOps (dblJMul K.S p p) E p.y,
        runOps (dblJMul K.S p p) E p.z)=dblJF (E p.x) (E p.y) (E p.z) := by
  obtain hs : ∀ op∈dblJMul K.S p p,∀ x∈op.out::op.ins,Sl x := by
    intro op hop x hx
    simp only [dblJMul,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx <;>
      rcases hx with rfl|rfl|rfl <;> exact hSl _ (by simp [rcbW])
  obtain hr : readsOk (dblJMul K.S p p) V=true := by
    rw [dbl_eq]
    exact readsOk_mono (readsOk_rename (dblσ K.S p)
      (show readsOk dblN [6,7,8]=true by decide)) hV
  refine WP.mono (fprog_ok hL hW hm _ hI hs hr) fun t ⟨kt,it⟩ => ⟨kt.mono ?_,it.sub ?_,?_⟩
  · intro x hx
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
    simp only [dblJMul,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [FOp.out,rcbW]
  · intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx|hx
    · right
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> simp [dblJMul,FOp.out]
    · exact Or.inl hx
  · exact dbl_run hN hA E

end VG.Proof.Weierstrass.X86.JWin

end

end


/-! ## `WinJacCoZState` -/

@[expose] public section

section

/-! The shared-Z table invariant and its transfer to memory. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

/-- The affine base point in coordinates sharing the current table entry's Z. -/
structure SharedZ (K : JacWinCfg) (C : Curve) (base : Addr) (P : Point C) (s : State) : Prop where
  lt : ∀ x∈[K.D.x,K.D.y],wordsVal s.mem base x K.M.n<C.p
  point : InvJ C (tmv C K.M.n base s K.D.x) (tmv C K.M.n base s K.D.y)
    (tmv C K.M.n base s K.E.z) P

structure CoBuildInv (K : JacWinCfg) (C : Curve) (base : Addr) (size wk : Nat)
    (P : Point C) (s₀ : State) (m : Nat) (s : State) : Prop where
  inv : BuildInv K C base size wk P s₀ m s
  shared : SharedZ K C base P s

/-- Saving an entry changes neither the live entry nor its shared-Z base point. -/
theorem SharedZ.store {K : JacWinCfg} {C : Curve} {base : Addr} {size wk m : Nat}
    (hL : Layout K size wk) {s t : State} (hs : Scr s base size)
    (hu : Unch base (storeW K m) s.mem t.mem) {P : Point C} (h : SharedZ K C base P s) :
    SharedZ K C base P t := by
  obtain ex := store_slot hL hs (show K.D.x∈slots K by simp [slots,work]) hu
  obtain ey := store_slot hL hs (show K.D.y∈slots K by simp [slots,work]) hu
  obtain ez := store_slot hL hs (show K.E.z∈slots K by simp [slots,work]) hu
  refine ⟨?_,?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · rw [ex]; exact h.lt _ (by simp)
    · rw [ey]; exact h.lt _ (by simp)
  · simpa only [tmv,ex,ey,ez] using h.point

variable {C : Curve}

theorem zaddu_x (hC : Law C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n) {m : Nat} (h2 : 2 ≤ m) (h15 : m ≤ 15) {X1 Y1 X2 Y2 Z : Fe C}
    (h1 : InvJ C X1 Y1 Z P) (hm : InvJ C X2 Y2 Z (mul m P)) (hz : Z ≠ 0) : X1 - X2 ≠ 0 := by
  intro hx
  obtain ⟨ne1, ne2⟩ := Window5.tbl_noexc hC hO hP hP0 hn17 h2 h15
  obtain hx' : X1 * (Z * Z) - X2 * (Z * Z) = 0 := by
    obtain e : X1 * (Z * Z) - X2 * (Z * Z) = (X1 - X2) * (Z * Z) := by grind
    rw [e, hx]; grind
  by_cases hy : Y1 * Z * (Z * Z) - Y2 * Z * (Z * Z) = 0
  · exact ne1 (hm.same hC h1 hz hz hx' hy)
  · exact ne2 (hm.opposite hC (hC.onCurve_mul hP m) hP h1 hz hz hx' hy)


theorem co_valid {K : JacWinCfg} {N : List FOp} {V : List Nat} {i : Nat}
    (hi : i∈N.map FOp.out) : coσ K i∈validAfter (N.map (FOp.rename (coσ K))) V := by
  rw [mem_validAfter]
  right
  obtain ⟨op,ho,rfl⟩ := List.mem_map.mp hi
  exact List.mem_map.mpr ⟨FOp.rename (coσ K) op,List.mem_map.mpr ⟨op,ho,rfl⟩,FOp.out_rename _ _⟩

theorem co_cached {K : JacWinCfg} {C : Curve} {base : Addr} {size : Nat} {Sl : Nat → Prop}
    (hn : K.M.n=4) {N : List FOp} {V : List Nat} {E r : Nat → Fe C} {t : State}
    (hi : Inv K.M base size C.p Sl (validAfter (N.map (FOp.rename (coσ K))) V) E t)
    (hv : ∀ i,E (coσ K i)=r i) (hout : ∀ i,12≤i → i≤16 → i∈N.map FOp.out)
    {Q : Point C} (hj : InvJ C (r 12) (r 13) (r 14) Q)
    (hz : r 14≠0) (h2 : r 15=r 14*r 14) (h3 : r 16=r 15*r 14) :
    Cached C base t (fun c => K.T+32*c) Q := by
  obtain e12 : E K.E.x=r 12 := hv 12
  obtain e13 : E K.E.y=r 13 := hv 13
  obtain e14 : E K.E.z=r 14 := hv 14
  obtain e15 : E K.z2=r 15 := hv 15
  obtain e16 : E K.z3=r 16 := hv 16
  apply Cached.of_inv hn hi
  · intro c hc
    have : c=0 ∨ c=1 ∨ c=2 ∨ c=3 ∨ c=4 := by omega_arith
    rcases this with rfl|rfl|rfl|rfl|rfl
    · exact co_valid (hout 12 (by decide) (by decide))
    · exact co_valid (hout 13 (by decide) (by decide))
    · exact co_valid (hout 14 (by decide) (by decide))
    · exact co_valid (hout 15 (by decide) (by decide))
    · exact co_valid (hout 16 (by decide) (by decide))
  · rwa [e12,e13,e14]
  · rwa [e14]
  · rwa [e15,e14]
  · rwa [e16,e15,e14]

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacCoZAdd` -/

section

/-! ZADDU advances the table while retaining a base point with the sum's Z. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem zaddu_point_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk m : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    (hn : 17≤C.n) {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity)
    (h2 : 2≤m) (h15 : m≤15) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base size C.p (·∈slots K) V E s)
    (hV : ∀ x∈[K.D.x,K.D.y,K.E.x,K.E.y,K.E.z,K.z2],x∈V)
    (hD : InvJ C (E K.D.x) (E K.D.y) (E K.E.z) P)
    (hT : InvJ C (E K.E.x) (E K.E.y) (E K.E.z) (mul m P))
    (hz : E K.E.z≠0) (hpow : E K.z2=E K.E.z*E K.E.z) :
    WP isa (fprog K.F K.zadduOps) s fun t =>
      ProgKeep K.M base wk (work K) s t ∧
      Cached C base t (fun c => K.T+32*c) (mul (m+1) P) ∧ SharedZ K C base P t := by
  obtain hr : readsOk (zadduN.map (FOp.rename (coσ K))) V=true :=
    readsOk_mono (readsOk_rename (coσ K) zadduN_reads) fun x hx => hV x (by
      simpa only [List.map_cons,List.map_nil,coσ,work,temps,List.cons_append,List.nil_append,
        List.getD_cons_zero,List.getD_cons_succ] using hx)
  rw [zaddu_eq]
  refine WP.mono (coProg_ok hL hW hm zadduN_out hi hr) fun t ⟨kt,it,hv⟩ => ?_
  obtain ⟨jt,hz2,hz3⟩ := zadduN_run (fun i => E (coσ K i))
  generalize runOps zadduN (fun i => E (coσ K i))=r at hv jt hz2 hz3
  obtain hx := zaddu_x hC hO hP hP0 hn h2 h15 hD hT hz
  obtain js := InvJ.zaddu hC ha hP (hC.onCurve_mul hP m) hD hT hz hx
  have jt' : ((r 12,r 13,r 14),(r 9,r 10))=zadduF (E K.D.x) (E K.D.y)
      (E K.E.x) (E K.E.y) (E K.E.z) := jt
  rw [←jt'] at js
  obtain he : Spec.Weierstrass.add (mul m P) P=mul (m+1) P :=
    (congrArg (Spec.Weierstrass.add (mul m P)) (mul_one_pt P).symm).trans (hC.add_mul_mul hP m 1)
  rw [he] at js
  obtain z : r 14≠0 := fun h => Window5.mul_ne_infinity hO hP hP0 (m:=m+1)
    (by omega_arith) (by omega_arith) ((js.1.z_zero_iff hC).mp h)
  have value (i : Nat) (ho : i∈zadduN.map FOp.out) : tmv C K.M.n base t (coσ K i)=r i :=
    (it.val _ (co_valid ho)).trans (hv i)
  refine ⟨kt,co_cached hL.n it hv (by
    obtain hb : ∀ i<17,12≤i → i∈zadduN.map FOp.out := by decide
    exact fun i h12 h16 => hb i (by omega_arith) h12) js.1 z (hz2 hpow) hz3,?_,?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact it.lt _ (co_valid (i:=9) (by decide))
    · exact it.lt _ (co_valid (i:=10) (by decide))
  · have v9 : tmv C K.M.n base t K.D.x=r 9 := value 9 (by decide)
    obtain v10 : tmv C K.M.n base t K.D.y=r 10 := value 10 (by decide)
    obtain v14 : tmv C K.M.n base t K.E.z=r 14 := value 14 (by decide)
    rw [v9,v10,v14]
    exact js.2

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacCoZDouble` -/

section

/-! DBLU constructs the second entry and the rescaled base point. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem dblu_point_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    (hn : 17≤C.n) {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base size C.p (·∈slots K) V E s)
    (hV : ∀ x∈[K.P.x,K.P.y,K.P.z],x∈V)
    (hj : InvJ C (E K.P.x) (E K.P.y) 1 P) (hz : E K.P.z=1) :
    WP isa (fprog K.F K.dbluOps) s fun t =>
      ProgKeep K.M base wk (work K) s t ∧
      Cached C base t (fun c => K.T+32*c) (mul 2 P) ∧
      wordsVal t.mem base K.S.t2 K.M.n<C.p ∧ wordsVal t.mem base K.S.t3 K.M.n<C.p ∧
      InvJ C (tmv C K.M.n base t K.S.t3) (tmv C K.M.n base t K.S.t2)
        (tmv C K.M.n base t K.E.z) P := by
  obtain hr : readsOk (dbluN.map (FOp.rename (coσ K))) V=true :=
    readsOk_mono (readsOk_rename (coσ K) dbluN_reads) fun x hx => hV x (by
      simpa only [List.map_cons,List.map_nil,coσ,work,temps,List.cons_append,List.nil_append,
        List.getD_cons_zero,List.getD_cons_succ] using hx)
  rw [dblu_eq]
  refine WP.mono (coProg_ok hL hW hm dbluN_out hi hr) fun t ⟨kt,it,hv⟩ => ?_
  have hz' : E (coσ K 20)=1 := hz
  obtain ⟨jt,h2,h3,hx,hy⟩ := dbluN_run (fun i => E (coσ K i)) hz'
  generalize runOps dbluN (fun i => E (coσ K i))=r at hv jt h2 h3 hx hy
  have jp : InvJ C (E (coσ K 18)) (E (coσ K 19)) 1 P := hj
  obtain j2 := InvJ.dbl' hC ha hP jp jt
  obtain he : Spec.Weierstrass.add P P=mul 2 P := by
    simpa only [mul_one_pt] using hC.add_mul_mul hP 1 1
  rw [he] at j2
  obtain z : r 14≠0 := fun h => Window5.mul_ne_infinity hO hP hP0 (m:=2)
    (by decide) (by omega_arith) ((j2.z_zero_iff hC).mp h)
  obtain jd : InvJ C (r 3) (r 2) (r 14) P := jp.rescale hC z hC.one_ne_zero hx hy (by grind)
  have value (i : Nat) (ho : i∈dbluN.map FOp.out) : tmv C K.M.n base t (coσ K i)=r i :=
    (it.val _ (co_valid ho)).trans (hv i)
  refine ⟨kt,co_cached hL.n it hv (by
    obtain hb : ∀ i<17,12≤i → i∈dbluN.map FOp.out := by decide
    exact fun i h12 h16 => hb i (by omega_arith) h12) j2 z h2 h3,
    it.lt _ (co_valid (i:=2) (by decide)),it.lt _ (co_valid (i:=3) (by decide)),?_⟩
  obtain v3 : tmv C K.M.n base t K.S.t3=r 3 := value 3 (by decide)
  obtain v2 : tmv C K.M.n base t K.S.t2=r 2 := value 2 (by decide)
  obtain v14 : tmv C K.M.n base t K.E.z=r 14 := value 14 (by decide)
  rw [v3,v2,v14]
  exact jd

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacCoZCopy` -/

section

/-! Copy the base point produced by DBLU into the shared-Z slots. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem co_ne {K : JacWinCfg} {size wk i j : Nat} (hL : Layout K size wk)
    (hj : j<18) (hne : i≠j) : coσ K i≠coσ K j := by
  intro he
  obtain hp := coP_readonly hL
  exact hne (getD_append_inj hL.nd hp (hp _ (List.mem_cons_self ..)) hj i he)

theorem copy_shared_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base size C.p (·∈slots K) (K.S.t2::K.S.t3::live K) E s) :
    WP isa (.block (copy 8 K.D.x K.S.t3++copy 8 K.D.y K.S.t2)) s fun t => ∃ E',
      ProgKeep K.M base wk [K.D.x,K.D.y] s t ∧
      Inv K.M base size C.p (·∈slots K) (K.D.y::K.D.x::K.S.t2::K.S.t3::live K) E' t ∧
      E' K.D.x=E K.S.t3 ∧ E' K.D.y=E K.S.t2 ∧ ∀ x∈live K,E' x=E x := by
  obtain dxy : K.D.x≠K.D.y := co_ne hL (i:=9) (j:=10) (by decide) (by decide)
  obtain tdx : K.S.t2≠K.D.x := co_ne hL (i:=2) (j:=9) (by decide) (by decide)
  have sep (x : Nat) (hx : x∈live K) : x≠K.D.x ∧ x≠K.D.y := by
    rcases List.mem_append.mp hx with hx|hx
    · constructor <;> intro he <;> apply hL.readonly x hx <;> rw [he] <;> simp [work]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl
      all_goals constructor
      all_goals first
        | exact co_ne hL (i:=12) (j:=9) (by decide) (by decide)
        | exact co_ne hL (i:=12) (j:=10) (by decide) (by decide)
        | exact co_ne hL (i:=13) (j:=9) (by decide) (by decide)
        | exact co_ne hL (i:=13) (j:=10) (by decide) (by decide)
        | exact co_ne hL (i:=14) (j:=9) (by decide) (by decide)
        | exact co_ne hL (i:=14) (j:=10) (by decide) (by decide)
        | exact co_ne hL (i:=15) (j:=9) (by decide) (by decide)
        | exact co_ne hL (i:=15) (j:=10) (by decide) (by decide)
        | exact co_ne hL (i:=16) (j:=9) (by decide) (by decide)
        | exact co_ne hL (i:=16) (j:=10) (by decide) (by decide)
  rw [WP.block_append_iff]
  obtain n8 : 2*K.M.n=8 := by rw [hL.n]
  obtain first := copyField_ok hL.lay hW hi (o:=K.D.x) (by simp [slots,work])
    (a:=K.S.t3) (by simp)
  rw [n8] at first
  refine WP.mono first fun a ⟨ka,ia⟩ => ?_
  obtain second := copyField_ok hL.lay hW ia (o:=K.D.y) (by simp [slots,work])
    (a:=K.S.t2) (by simp)
  rw [n8] at second
  refine WP.mono second fun t ⟨kt,it⟩ => ⟨_,
    (progKeep_of_op ka (by simp)).trans (progKeep_of_op kt (by simp)),it,?_,?_,?_⟩
  · simp only [Function.update_apply,dxy,ite_false,ite_true]
  · simp only [Function.update_apply,tdx,ite_false,ite_true]
  · intro x hx
    simp only [Function.update_apply,(sep x hx).1,(sep x hx).2,ite_false]

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacCoZStore` -/

section

/-! Preserve the shared-Z invariant through public counters and table stores. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem SharedZ.keeps {K : JacWinCfg} {C : Curve} {base : Addr} {P : Point C} {s t : State}
    (h : SharedZ K C base P s) (hk : CKeeps [.esi] s t) : SharedZ K C base P t := by
  refine ⟨?_,?_⟩
  · intro x hx
    rw [hk.2.1]; exact h.lt x hx
  · simpa only [tmv,hk.2.1] using h.point

theorem co_store_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk m : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s₀ s : State} (h : Frame K C base size wk s₀ s) (hm : m<16)
    (hb : s.gpr .esi=BitVec.ofNat 32 (m+1)) {P : Point C}
    (ht : Table K C base P m s)
    (hp : Cached C base s (fun c => K.T+32*c) (mul (m+1) P))
    (hd : SharedZ K C base P s) :
    WP isa (.block K.storeEntry) s (CoBuildInv K C base size wk P s₀ (m+1)) := by
  obtain hT : K.T+160≤K.tbl := by
    have := hL.low K.z3 (by simp [slots,work])
    simp only [JacWinCfg.z3] at this
    omega_arith
  refine WP.mono (store_table_ok h.scr hm hb hL.table hT ht hp)
    fun t ⟨ht,hu,hk⟩ => ⟨⟨h.store hL hW hm hu hk,ht,hp.store hL h.scr hu,
      (hk.gpr _ (by decide)).trans hb⟩,hd.store hL h.scr hu⟩

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacCoZInit` -/

section

/-! Store the second multiple and seed the shared-Z table loop. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem co_init_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    (hn : 17≤C.n) {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity)
    {s₀ s : State} (h : BuildInv K C base size wk P s₀ 1 s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hJP : InvJ C (tmv C K.M.n base s₀ K.P.x) (tmv C K.M.n base s₀ K.P.y) 1 P)
    (hPz : tmv C K.M.n base s₀ K.P.z=1) :
    WP isa (.seq (fprog K.F K.dbluOps)
      (.seq (.block (copy 8 K.D.x K.S.t3++copy 8 K.D.y K.S.t2))
        (.block (([.mov .esi (.imm 2)] : List Instr)++K.storeEntry)))) s
      (CoBuildInv K C base size wk P s₀ 2) := by
  obtain hi := h.frame.inv_cached hL hW hro h.point
  have tv (x : Nat) (hx : x∈ro K) : tmv C K.M.n base s x=tmv C K.M.n base s₀ x := by
    unfold tmv
    rw [h.frame.ro hL hW hx]
  apply WP.seq
  refine WP.mono (dblu_point_ok hL hW hm hC ha hO hn hP hP0 hi
    (by intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl <;> simp [live,ro])
    (by rw [tv _ (by simp [ro]),tv _ (by simp [ro])]; exact hJP)
    (by rw [tv _ (by simp [ro])]; exact hPz)) fun a ⟨ka,pa,ta2,ta3,ja⟩ => ?_
  obtain fa := h.frame.field hL hW ka (fun _ hx => hx)
  obtain tableA := h.table.field_keep hL h.frame.scr ka (fun _ hx => hx) (by decide)
  obtain ia := fa.inv_cached hL hW hro pa
  obtain ia' : Inv K.M base size C.p (·∈slots K) (K.S.t2::K.S.t3::live K)
      (tmv C K.M.n base a) a := by
    refine ⟨ia.scr,ia.mod,?_,?_,fun _ _ => rfl⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|rfl|hx
      · simp [slots,work,temps]
      · simp [slots,work,temps]
      · exact ia.sl x hx
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|rfl|hx
      · exact ta2
      · exact ta3
      · exact ia.lt x hx
  apply WP.seq
  refine WP.mono (copy_shared_ok hL hW ia') fun b ⟨e,kb,ib,dx,dy,ev⟩ => ?_
  obtain wb : ∀ x∈[K.D.x,K.D.y],x∈work K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> simp [work]
  obtain fb := fa.field hL hW kb wb
  obtain tableB := tableA.field_keep hL fa.scr kb wb (by decide)
  have ev4 (x : Nat) (hx : x∈live K) : e x=tmv C 4 base a x := by
    rw [ev x hx,hL.n]
  obtain pb : Cached C base b (fun c => K.T+32*c) (mul 2 P) := by
    apply Cached.of_inv hL.n ib
    · intro c hc
      have : c=0 ∨ c=1 ∨ c=2 ∨ c=3 ∨ c=4 := by omega_arith
      rcases this with rfl|rfl|rfl|rfl|rfl <;> simp [live,JacWinCfg.E,JacWinCfg.z2,JacWinCfg.z3]
    · rw [ev4 _ (by simp [live]),ev4 _ (by simp [live]),ev4 _ (by simp [live])]
      exact pa.jac
    · rw [ev4 _ (by simp [live])]; exact pa.z
    · rw [ev4 _ (by simp [live]),ev4 _ (by simp [live])]; exact pa.z2
    · rw [ev4 _ (by simp [live]),ev4 _ (by simp [live]),ev4 _ (by simp [live])]; exact pa.z3
  obtain sb : SharedZ K C base P b := by
    refine ⟨?_,?_⟩
    · intro x hx
      apply ib.lt x
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl <;> simp
    · have vx : tmv C K.M.n base b K.D.x=e K.D.x := ib.val _ (by simp)
      obtain vy : tmv C K.M.n base b K.D.y=e K.D.y := ib.val _ (by simp)
      obtain vz : tmv C K.M.n base b K.E.z=e K.E.z := ib.val _ (by simp [live])
      rw [vx,vy,vz,dx,dy,ev _ (by simp [live])]
      exact ja
  rw [WP.block_append_iff]
  refine WP.mono (mov_counter_ok b 2) fun t ⟨ct,kt⟩ => ?_
  apply co_store_ok hL hW (fb.keeps kt) (m:=1) (by decide) ct
  · intro m h1 hm
    exact (tableB m h1 hm).congr fun _ _ => by rw [kt.2.1]
  · exact pb.congr fun _ _ => by rw [kt.2.1]
  · exact sb.keeps kt

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacCounter` -/

section

/-! Public counters used by the cached-point table loop. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem inc_counter_ok {s : State} {m : Nat} (hc : s.gpr .esi=BitVec.ofNat 32 m) :
    WP isa (.block [.alu .add .esi (.imm 1)]) s fun t =>
      t.gpr .esi=BitVec.ofNat 32 (m+1) ∧ CKeeps [.esi] s t := by
  obtain he : BitVec.ofNat 32 m+(1 : BitVec 32)=BitVec.ofNat 32 (m+1) := by
    change BitVec.ofNat 32 m+BitVec.ofNat 32 1=_
    rw [BitVec.ofNat_add]
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    ite_true,hc,he,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem cmp_counter_ok {s : State} {m : Nat} (hm : m≤16) (hc : s.gpr .esi=BitVec.ofNat 32 m) :
    WP isa (.block [.alu .cmp .esi (.imm 16)]) s fun t =>
      t.zf=some (decide (m=16)) ∧ CKeeps [.esi] s t ∧ t.gpr .esi=BitVec.ofNat 32 m := by
  obtain he : (BitVec.ofNat 32 m-(16 : BitVec 32)==0)=decide (m=16) := by
    by_cases h : m=16
    · subst m; rfl
    · rw [decide_eq_false h,beq_eq_false_iff_ne]
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub,BitVec.toNat_ofNat] at this
      have h16 : (16 : BitVec 32).toNat=16 := rfl
      have h0 : (0 : BitVec 32).toNat=0 := rfl
      omega_arith
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.gpr_arithFlags,RegUpd.zf_arithFlags,hc,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,trivial⟩
  exact he

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacCoZStep` -/

section

/-! One public shared-Z table-construction iteration. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem co_step_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk m : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    (hn : 17≤C.n) {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity)
    (h2 : 2≤m) (h15 : m≤15) {s₀ s : State} (h : CoBuildInv K C base size wk P s₀ m s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p) :
    WP isa K.buildStep s fun t => CoBuildInv K C base size wk P s₀ (m+1) t ∧
      t.zf=some (decide (m+1=16)) := by
  unfold JacWinCfg.buildStep
  apply WP.seq
  refine WP.mono (inc_counter_ok h.inv.counter) fun a ⟨ca,ka⟩ => ?_
  obtain fa := h.inv.frame.keeps ka
  obtain pa := h.inv.point.congr (p:=fun c => K.T+32*c) fun _ _ => by rw [ka.2.1]
  obtain da := h.shared.keeps ka
  obtain ia := fa.inv_cached hL hW hro pa
  obtain ia' : Inv K.M base size C.p (·∈slots K) (K.D.x::K.D.y::live K)
      (tmv C K.M.n base a) a := by
    refine ⟨ia.scr,ia.mod,?_,?_,fun _ _ => rfl⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|rfl|hx
      · simp [slots,work]
      · simp [slots,work]
      · exact ia.sl x hx
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|rfl|hx
      · exact da.lt _ (by simp)
      · exact da.lt _ (by simp)
      · exact ia.lt x hx
  obtain ja : InvJ C (tmv C K.M.n base a K.E.x) (tmv C K.M.n base a K.E.y)
      (tmv C K.M.n base a K.E.z) (mul m P) := by
    simpa only [hL.n,JacWinCfg.E,Nat.reduceMul,Nat.add_zero] using pa.jac
  obtain za : tmv C K.M.n base a K.E.z≠0 := by
    simpa only [hL.n,JacWinCfg.E,Nat.reduceMul] using pa.z
  obtain z2a : tmv C K.M.n base a K.z2=tmv C K.M.n base a K.E.z*tmv C K.M.n base a K.E.z := by
    simpa only [hL.n,JacWinCfg.E,JacWinCfg.z2,Nat.reduceMul] using pa.z2
  apply WP.seq
  refine WP.mono (zaddu_point_ok hL hW hm hC ha hO hn hP hP0 h2 h15 ia'
    (by intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [live]) da.point ja za z2a)
    fun b ⟨kb,pb,db⟩ => ?_
  obtain fb := fa.field hL hW kb (fun _ hx => hx)
  obtain ta : Table K C base P m a := fun i h1 hm => (h.inv.table i h1 hm).congr fun _ _ => by rw [ka.2.1]
  obtain tb := ta.field_keep hL fa.scr kb (fun _ hx => hx) (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (co_store_ok hL hW fb (by omega_arith) ((kb.gpr _ (by decide)).trans ca) tb pb db)
    fun c hc => ?_
  refine WP.mono (cmp_counter_ok (by omega_arith) hc.inv.counter) fun t ⟨zt,kt,ct⟩ => ?_
  refine ⟨⟨⟨hc.inv.frame.keeps kt,?_,?_,ct⟩,hc.shared.keeps kt⟩,zt⟩
  · intro i h1 hm
    exact (hc.inv.table i h1 hm).congr fun _ _ => by rw [kt.2.1]
  · exact hc.inv.point.congr fun _ _ => by rw [kt.2.1]

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacBuild` -/

section

/-! Construct all sixteen cached multiples for the secret-scalar window. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem build_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    (hn : 17≤C.n) {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity)
    {s : State} (hI : Inv K.M base size C.p (·∈slots K) (ro K) (tmv C K.M.n base s) s)
    (hJ : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) (hz : tmv C K.M.n base s K.P.z=1) :
    WP isa K.build s (BuildInv K C base size wk P s 16) := by
  unfold JacWinCfg.build
  apply WP.seq
  refine WP.mono (build_init_ok hL hW hI hJ hz hC) fun a ia => ?_
  obtain jp : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y) 1 P := by
    simpa only [hz] using hJ
  apply WP.assoc
  apply WP.assoc
  apply WP.seq
  refine WP.mono (WP.assoc' (co_init_ok hL hW hm hC ha hO hn hP hP0 ia hI.lt jp hz)) fun b ib => ?_
  refine WP.loop (M:=isa)
    (fun j t => 1≤j ∧ j≤14 ∧ CoBuildInv K C base size wk P s (16-j) t)
    (fun j u ⟨hj,hj14,hu⟩ => ?_) 14 b ⟨by decide,by decide,ib⟩
  refine WP.mono (co_step_ok hL hW hm hC ha hO hn hP hP0 (by omega_arith) (by omega_arith) hu hI.lt)
    fun t ⟨it,zt⟩ => ?_
  by_cases he : j=1
  · subst j
    refine Or.inl ⟨?_,it.inv⟩
    change Option.map Bool.not t.zf=some false
    rw [zt]; rfl
  · refine Or.inr ⟨?_,j-1,by omega_arith,by omega_arith,by omega_arith,?_⟩
    · change Option.map Bool.not t.zf=some true
      rw [zt,decide_eq_false (by omega_arith)]
      rfl
    · rw [show 16-(j-1)=16-j+1 from by omega_arith]
      exact it

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacAccum` -/

section

/-! The accumulator keeps canonical fields even for scalars later rejected by ECDH. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

structure Accum (K : JacWinCfg) (C : Curve) (base : Addr) (size wk : Nat)
    (P : Point C) (k : Nat) (s₀ : State) (e : Nat) (s : State) : Prop where
  frame : Frame K C base size wk s₀ s
  table : Table K C base P 16 s
  lt : ∀ x∈[K.R.x,K.R.y,K.R.z],wordsVal s.mem base x K.M.n<C.p
  point : k<C.n → InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y)
    (tmv C K.M.n base s K.R.z) (mul e P)

theorem Accum.keeps {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e : Nat}
    {P : Point C} {s₀ s t : State} (h : Accum K C base size wk P k s₀ e s) (hk : CKeeps [.esi] s t) :
    Accum K C base size wk P k s₀ e t := by
  refine ⟨h.frame.keeps hk,?_,?_,?_⟩
  · intro m h1 hm; exact (h.table m h1 hm).congr fun _ _ => by rw [hk.2.1]
  · rw [hk.2.1]; exact h.lt
  · simpa only [tmv,hk.2.1] using h.point

theorem rcb_R_work (K : JacWinCfg) : ∀ x∈rcbW K.S K.R,x∈work K := by
  intro x hx
  simp only [rcbW,work,temps,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem rcb_R_nd {K : JacWinCfg} {size wk : Nat} (hL : Layout K size wk) :
    (rcbW K.S K.R).Nodup := by
  apply List.Nodup.sublist (l₂:=work K) _ hL.nd
  simp only [rcbW,work,temps,List.cons_append,List.nil_append]
  repeat first | exact List.Sublist.refl _ | apply List.Sublist.cons_cons | apply List.Sublist.cons

theorem Accum.inv {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e : Nat}
    {P : Point C} {s₀ s : State} (h : Accum K C base size wk P k s₀ e s)
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p) :
    Inv K.M base size C.p (·∈slots K) (ro K++[K.R.x,K.R.y,K.R.z]) (tmv C K.M.n base s) s := by
  refine ⟨h.frame.scr,h.frame.mod,?_,?_,fun _ _ => rfl⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact List.mem_append_left _ hx
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> simp [slots,work]
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · rw [h.frame.ro hL hW hx]; exact hro x hx
    · exact h.lt x hx

theorem Accum.preserve {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e : Nat}
    {P : Point C} {s₀ s t : State} (h : Accum K C base size wk P k s₀ e s)
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {W : List Nat} (hk : ProgKeep K.M base wk W s t) (hw : ∀ x∈W,x∈work K)
    (hd : ∀ x∈[K.R.x,K.R.y,K.R.z],x∉W) : Accum K C base size wk P k s₀ e t := by
  obtain hs : ∀ x∈[K.R.x,K.R.y,K.R.z],x∈slots K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [slots,work]
  refine ⟨h.frame.field hL hW hk hw,h.table.field_keep hL h.frame.scr hk hw (by decide),?_,?_⟩
  · intro x hx
    rw [hk.slot hL.lay hW h.frame.scr (fun x hx => List.mem_append_right _ (hw x hx)) (hs x hx) (hd x hx)]
    exact h.lt x hx
  · intro hvalid
    exact hk.invJ hL.lay hW h.frame.scr (fun x hx => List.mem_append_right _ (hw x hx)) hs hd (h.point hvalid)

theorem double_accum_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {P : Point C} (hP : onCurve C P=true) {s₀ s : State} (h : Accum K C base size wk P k s₀ e s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p) :
    WP isa (K.dbl K.R) s fun t => Accum K C base size wk P k s₀ (2*e) t ∧
      ProgKeep K.M base wk (rcbW K.S K.R) s t := by
  obtain hi := h.inv hL hW hro
  refine WP.mono (dbl_field_ok hL.lay hW hm (rcb_R_nd hL)
    (fun hx => hL.readonly K.S.a (by simp [ro]) (rcb_R_work K _ hx))
    (fun x hx => List.mem_append_right _ (rcb_R_work K x hx)) hi
    (fun _ hx => List.mem_append_right _ hx)) fun t ⟨kt,it,et⟩ => ?_
  refine ⟨⟨h.frame.field hL hW kt (rcb_R_work K),h.table.field_keep hL h.frame.scr kt (rcb_R_work K)
    (by decide),fun x hx => it.lt x (List.mem_append_left _ hx),?_⟩,kt⟩
  intro hk
  obtain jt := InvJ.dbl' hC ha (hC.onCurve_mul hP e) (h.point hk) et
  rw [hC.add_mul_mul hP,show e+e=2*e by omega_arith] at jt
  exact it.point_tmv (fun _ hx => List.mem_append_left _ hx) jt

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacChoose` -/

section

/-! Branchless field selection in the arithmetic environment. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem choose_field_ok {F : Impl.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr}
    {size wk m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hW : WkOk F M m size wk Sl) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {o a b : Nat} (ho : Sl o) (ha : a∈V) (hb : b∈V)
    (c : Bool) (hc : s.gpr .ecx=bmask c) :
    WP isa (.block (sel (2*M.n) o a b)) s fun t =>
      ProgKeep M base wk [o] s t ∧
      Inv M base size m Sl (o::V) (Function.update E o (if c then E b else E a)) t := by
  have sep (x : Nat) (hx : x∈V) : o≤x ∨ x+8*M.n≤o := by
    by_cases he : o=x
    · exact Or.inl (Nat.le_of_eq he)
    · have := hL.apart o x ho (hI.sl x hx) he
      omega_arith
  refine WP.mono (selWords_ok hI.scr c hc (hL.le o ho) (hL.le a (hI.sl a ha))
    (hL.le b (hI.sl b hb)) (sep a ha) (sep b hb)) fun t ⟨et,kt,ot⟩ => ?_
  obtain hk : ProgKeep M base wk [o] s t := ⟨fun r hr => kt.gpr r (fun he => hr (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl <;> simp [clob])),kt.rd,kt.wr,Outs.of_outside ot (by simp [progW])⟩
  refine ⟨hk,hI.update hL hW ho hk ?_ ?_⟩
  · rw [et]; cases c <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact hI.lt a ha
    · exact hI.lt b hb
  · rw [et]; cases c <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact hI.val a ha
    · exact hI.val b hb

theorem keep_of_ckeeps {M : Mod} {base : Addr} {wk : Nat} {s t : State}
    (hk : CKeeps clob s t) : ProgKeep M base wk [] s t :=
  ⟨hk.1,hk.2.2.1,hk.2.2.2,fun _ _ => congrFun hk.2.1 _⟩

theorem value_after {F : Impl.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr}
    {size wk m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hW : WkOk F M m size wk Sl)
    {V V' W : List Nat} {E E' : Nat → Fin m} {s t : State}
    (hi : Inv M base size m Sl V E s) (ht : Inv M base size m Sl V' E' t)
    (hk : ProgKeep M base wk W s t) (hw : ∀ x∈W,Sl x)
    {x : Nat} (hx : x∈V) (hx' : x∈V') (hn : x∉W) : E' x=E x := by
  rw [←ht.val x hx',hk.slot hL hW hi.scr hw (hi.sl x hx) hn,hi.val x hx]

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacDoubleLoop` -/

section

/-! Five doublings, with their public counter in the high bits of ESI. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem double_counter_ok {s : State} {j n : Nat} (hj : j<52) (h1 : 1≤n) (h5 : n≤5)
    (hc : s.gpr .esi=BitVec.ofNat 32 (j+4096*n)) :
    WP isa (.block [.alu .sub .esi (.imm 4096),.alu .cmp .esi (.imm 4096)]) s fun t =>
      t.gpr .esi=BitVec.ofNat 32 (j+4096*(n-1)) ∧ t.cf=some (decide (n=1)) ∧ CKeeps [.esi] s t := by
  obtain he : BitVec.ofNat 32 (j+4096*n)-(4096 : BitVec 32)=BitVec.ofNat 32 (j+4096*(n-1)) := by
    change BitVec.ofNat 32 (j+4096*n)-BitVec.ofNat 32 4096=_
    rw [BitVec.ofNat_sub_ofNat_of_le (j+4096*n) 4096 (by decide) (by omega_arith)]
    exact congrArg (BitVec.ofNat 32) (show j+4096*n-4096=j+4096*(n-1) by omega_arith)
  crun [hc,he,RegUpd.cf_arithFlags]
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · congr 1
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show j+4096*(n-1)<2^32 by omega_arith)]
    obtain heq : j+4096*(n-1)<4096 ↔ n=1 := by omega_arith
    change (j+4096*(n-1)<4096)=(n=1)
    exact propext heq
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem double_step_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e j n : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {P : Point C} (hP : onCurve C P=true) {s₀ s : State} (h : Accum K C base size wk P k s₀ e s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hj : j<52) (h1 : 1≤n) (h5 : n≤5) (hc : s.gpr .esi=BitVec.ofNat 32 (j+4096*n)) :
    WP isa K.dblStep s fun t => Accum K C base size wk P k s₀ (2*e) t ∧
      t.gpr .esi=BitVec.ofNat 32 (j+4096*(n-1)) ∧ t.cf=some (decide (n=1)) := by
  unfold JacWinCfg.dblStep
  apply WP.seq
  refine WP.mono (double_accum_ok hL hW hm hC ha hP h hro) fun a ⟨ha,ka⟩ => ?_
  refine WP.mono (double_counter_ok hj h1 h5 ((ka.gpr _ (by decide)).trans hc))
    fun t ⟨ct,ft,kt⟩ => ⟨ha.keeps kt,ct,ft⟩

theorem double_init_counter_ok {s : State} {j : Nat} (hc : s.gpr .esi=BitVec.ofNat 32 j) :
    WP isa (.block [.alu .add .esi (.imm 20480)]) s fun t =>
      t.gpr .esi=BitVec.ofNat 32 (j+4096*5) ∧ CKeeps [.esi] s t := by
  obtain he : BitVec.ofNat 32 j+(20480 : BitVec 32)=BitVec.ofNat 32 (j+4096*5) := by
    rw [BitVec.ofNat_add]; rfl
  crun [hc,he]
  refine ⟨fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem doubles_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e j : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {P : Point C} (hP : onCurve C P=true) {s₀ s : State} (h : Accum K C base size wk P k s₀ e s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hj : j<52) (hc : s.gpr .esi=BitVec.ofNat 32 j) :
    WP isa K.dbls s fun t => Accum K C base size wk P k s₀ (32*e) t ∧ t.gpr .esi=BitVec.ofNat 32 j := by
  unfold JacWinCfg.dbls
  apply WP.seq
  refine WP.mono (double_init_counter_ok hc) fun a ⟨ca,ka⟩ => ?_
  refine WP.loop (M:=isa)
    (fun n t => 1≤n ∧ n≤5 ∧ Accum K C base size wk P k s₀ (2^(5-n)*e) t ∧
      t.gpr .esi=BitVec.ofNat 32 (j+4096*n)) (fun n u ⟨h1,h5,hu,cu⟩ => ?_) 5 a
    ⟨by decide,by decide,by simpa using h.keeps ka,ca⟩
  refine WP.mono (double_step_ok hL hW hm hC ha hP hu hro hj h1 h5 cu) fun t ⟨ht,ct,ft⟩ => ?_
  by_cases he : n=1
  · subst n
    refine Or.inl ⟨?_,?_,?_⟩
    · change Option.map Bool.not t.cf=some false
      rw [ft]; rfl
    · simpa only [Nat.reduceSub,Nat.reducePow,←Nat.mul_assoc,Nat.reduceMul] using ht
    · simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using ct
  · refine Or.inr ⟨?_,n-1,by omega_arith,by omega_arith,by omega_arith,?_,ct⟩
    · change Option.map Bool.not t.cf=some true
      rw [ft,decide_eq_false he]; rfl
    · have hp : 5-(n-1)=(5-n)+1 := by omega_arith
      simpa only [hp,Nat.pow_succ,Nat.mul_assoc,Nat.mul_left_comm] using ht

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacEntry` -/

section

/-! Cached entries include the all-zero triple selected for magnitude zero. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

def coords (K : JacWinCfg) : List Nat := [K.E.x,K.E.y,K.E.z,K.z2,K.z3]

structure Entry (K : JacWinCfg) (C : Curve) (base : Addr) (Q : Point C) (s : State) : Prop where
  lt : ∀ x∈coords K,wordsVal s.mem base x K.M.n<C.p
  jac : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) Q
  z2 : tmv C K.M.n base s K.z2=tmv C K.M.n base s K.E.z*tmv C K.M.n base s K.E.z
  z3 : tmv C K.M.n base s K.z3=tmv C K.M.n base s K.z2*tmv C K.M.n base s K.E.z

theorem Entry.of_inv {K : JacWinCfg} {C : Curve} {base : Addr} {size : Nat}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hv : ∀ x∈coords K,x∈V)
    {Q : Point C} (hj : InvJ C (E K.E.x) (E K.E.y) (E K.E.z) Q)
    (h2 : E K.z2=E K.E.z*E K.E.z) (h3 : E K.z3=E K.z2*E K.E.z) : Entry K C base Q s := by
  have ev (x : Nat) (hx : x∈coords K) : tmv C K.M.n base s x=E x := hI.val x (hv x hx)
  refine ⟨fun x hx => hI.lt x (hv x hx),?_,?_,?_⟩
  · rw [ev _ (by simp [coords]),ev _ (by simp [coords]),ev _ (by simp [coords])]; exact hj
  · rw [ev _ (by simp [coords]),ev _ (by simp [coords])]; exact h2
  · rw [ev _ (by simp [coords]),ev _ (by simp [coords]),ev _ (by simp [coords])]; exact h3

theorem coords_work (K : JacWinCfg) : ∀ x∈coords K,x∈work K := by
  intro x hx
  simp only [coords,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl <;> simp [work]

theorem Cached.entry {K : JacWinCfg} {C : Curve} {base : Addr} {s : State} {Q : Point C}
    (hn : K.M.n=4) (h : Cached C base s (fun c => K.T+32*c) Q) : Entry K C base Q s := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    rw [hn]
    simp only [coords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl
    · exact h.lt 0 (by decide)
    · exact h.lt 1 (by decide)
    · exact h.lt 2 (by decide)
    · exact h.lt 3 (by decide)
    · exact h.lt 4 (by decide)
  · rw [hn]; exact h.jac
  · rw [hn]; exact h.z2
  · rw [hn]; exact h.z3

theorem selected_keep {K : JacWinCfg} {base : Addr} {wk : Nat} {s t : State} (hn : K.M.n=4)
    (hu : Outside base K.T 160 s.mem t.mem) (hk : KeepRegs [.ecx,.edx] s t) :
    ProgKeep K.M base wk (coords K) s t := by
  refine ⟨fun r hr => hk.gpr r (fun he => hr (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl <;> simp [clob])),hk.rd,hk.wr,?_⟩
  intro x hx
  apply hu
  have hc (o : Nat) (ho : o∈coords K) := hx (o,8*K.M.n)
    (List.mem_append_left _ (List.mem_map.mpr ⟨o,ho,rfl⟩))
  obtain h0 := hc K.E.x (by simp [coords])
  obtain h1 := hc K.E.y (by simp [coords])
  obtain h2 := hc K.E.z (by simp [coords])
  obtain h3 := hc K.z2 (by simp [coords])
  obtain h4 := hc K.z3 (by simp [coords])
  simp only [hn,JacWinCfg.E,JacWinCfg.z2,JacWinCfg.z3] at h0 h1 h2 h3 h4
  omega_arith

theorem select_entry_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk a : Nat}
    (hL : Layout K size wk) {s : State} (hs : Scr s base size) (ha : a≤16)
    (hb : s.gpr .ebx=BitVec.ofNat 32 a) {P : Point C} (ht : Table K C base P 16 s) :
    WP isa (.block K.select) s fun t => Entry K C base (mul a P) t ∧
      ProgKeep K.M base wk (coords K) s t := by
  obtain hT : K.T+160≤K.tbl := by
    have := hL.low K.z3 (by simp [slots,work])
    simp only [JacWinCfg.z3] at this
    omega_arith
  refine WP.mono (select_ok hs ha hb hL.table (by have := hL.table; omega_arith) hT)
    fun t ⟨et,ot,kt⟩ => ⟨?_,selected_keep hL.n ot kt⟩
  by_cases h1 : 1≤a
  · exact ((ht a h1 ha).congr (fun c hc => by simpa only [h1,ite_true] using et c hc)).entry hL.n
  · have az : a=0 := by omega_arith
    subst a
    have ev (c : Nat) (hc : c<5) : wordsVal t.mem base (K.T+32*c) 4=0 := by
      simpa only [show ¬1≤0 by decide,ite_false] using et c hc
    have ez (c : Nat) (hc : c<5) : tmv C 4 base t (K.T+32*c)=0 := by
      unfold tmv; rw [ev c hc]; exact toM_zero _ _
    refine ⟨?_,?_,?_,?_⟩
    · intro x hx
      rw [hL.n]
      simp only [coords,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl
      · exact (ev 0 (by decide)).symm ▸ Nat.pos_of_ne_zero (NeZero.ne C.p)
      · exact (ev 1 (by decide)).symm ▸ Nat.pos_of_ne_zero (NeZero.ne C.p)
      · exact (ev 2 (by decide)).symm ▸ Nat.pos_of_ne_zero (NeZero.ne C.p)
      · exact (ev 3 (by decide)).symm ▸ Nat.pos_of_ne_zero (NeZero.ne C.p)
      · exact (ev 4 (by decide)).symm ▸ Nat.pos_of_ne_zero (NeZero.ne C.p)
    · rw [hL.n,Window5.mul_zero_pt]
      exact Or.inl ⟨rfl,ez 2 (by decide)⟩
    · rw [hL.n,show K.z2=K.T+32*3 from rfl,show K.E.z=K.T+32*2 from rfl,
        ez 3 (by decide),ez 2 (by decide)]
      grind
    · rw [hL.n,show K.z3=K.T+32*4 from rfl,show K.z2=K.T+32*3 from rfl,
        show K.E.z=K.T+32*2 from rfl,ez 4 (by decide),ez 3 (by decide),ez 2 (by decide)]
      grind

end VG.Proof.Weierstrass.X86.JWin

end

/-! ## `WinJacEntryState` -/

section

/-! Preserve the accumulator while selecting and signing a table entry. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem entry_nd {K : JacWinCfg} {size wk : Nat} (hL : Layout K size wk) :
    (coords K++[K.neg]).Nodup := by
  apply List.Nodup.sublist (l₂:=work K) _ hL.nd
  simp only [coords,work,temps,List.cons_append,List.nil_append]
  repeat first | exact List.Sublist.refl _ | apply List.Sublist.cons_cons | apply List.Sublist.cons

theorem entry_apart_R {K : JacWinCfg} {size wk : Nat} (hL : Layout K size wk) :
    ∀ x∈[K.R.x,K.R.y,K.R.z],x∉coords K++[K.neg] := by
  obtain hn : ([K.R.x,K.R.y,K.R.z]++coords K++[K.neg]).Nodup := by
    apply List.Nodup.sublist (l₂:=work K) _ hL.nd
    simp only [coords,work,temps,List.cons_append,List.nil_append]
    repeat first | exact List.Sublist.refl _ | apply List.Sublist.cons_cons | apply List.Sublist.cons
  rw [List.append_assoc,List.nodup_append] at hn
  exact fun x hx hy => hn.2.2 x hx x hy rfl

theorem Accum.inv_entry {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e : Nat}
    {P Q : Point C} {s₀ s : State} (h : Accum K C base size wk P k s₀ e s)
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p) (he : Entry K C base Q s) :
    Inv K.M base size C.p (·∈slots K) ((ro K++[K.R.x,K.R.y,K.R.z])++coords K) (tmv C K.M.n base s) s := by
  obtain hi := h.inv hL hW hro
  refine ⟨hi.scr,hi.mod,?_,?_,fun _ _ => rfl⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hi.sl x hx
    · exact List.mem_append_right _ (coords_work K x hx)
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hi.lt x hx
    · exact he.lt x hx

theorem Frame.inv_entry {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    {Q : Point C} {s₀ s : State} (h : Frame K C base size wk s₀ s)
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hro : ∀ x∈JWin.ro K,wordsVal s₀.mem base x K.M.n<C.p) (he : Entry K C base Q s) :
    Inv K.M base size C.p (·∈slots K) (JWin.ro K++coords K) (tmv C K.M.n base s) s := by
  refine ⟨h.scr,h.mod,?_,?_,fun _ _ => rfl⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (coords_work K x hx)
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · rw [h.ro hL hW hx]; exact hro x hx
    · exact he.lt x hx

end VG.Proof.Weierstrass.X86.JWin

end
