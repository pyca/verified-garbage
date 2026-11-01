module

import VerifiedGarbage.Proof.Secp256k1.X86_64.JointLayout
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitLayout
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointLoop
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsWrap
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacAdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacDouble
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableFields
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableInit
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.Comb
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsCT
public import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsAdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacAddTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointFieldTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableStoreTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.RegFieldTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableState
import VerifiedGarbage.Proof.Weierstrass.JacDbl0
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Secp256k1.X86_64.JointTiming
public import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint
public import VerifiedGarbage.Proof.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInvariant

/-!
# secp256k1 on x86-64: the table of `Q`'s odd multiples by calls

The joint verifier builds `Q, 3Q, …, 15Q` by calls of
`vg_secp256k1_jac_double` and `vg_secp256k1_jac_add_cached`
(`Joint.tableCall`): `R = 2Q`, copied to `E` with its `Z²` and `Z³` at the
selected pair, then seven steps `R = R + E`, each stored in the next entry.
Its proof (`table_call_ok`) runs over the joint loop's slots, which hold the
selected pair the cached addition reads: an invariant `TC` of the steps,
whose facts about the slots a step does not write follow from their
distinctness, which the kernel checks on the layout.
-/

@[expose] public section

namespace VG.Proof.Secp256k1.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Secp256k1.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

/-- The slots the table writes, but its entries: `Naf.table`'s and the selected pair. -/
def tcW : List Nat :=
  winOther publicJoint.K ++ nafTblSlots publicJoint.K ++ [publicJoint.selected, publicJoint.selected + 8*publicJoint.K.M.n]

/-- The slots whose values the table's steps keep, but its entries. -/
def tcFixed : List Nat :=
  winRo publicJoint.K ++ jacCoords publicJoint.K.R ++ jacCoords publicJoint.K.E ++
    [publicJoint.selected, publicJoint.selected + 8*publicJoint.K.M.n] ++ jacCoords (Naf.twice publicJoint.K)

/-- The slots valid after `m` entries. -/
def tcLive (m : Nat) : List Nat := tcFixed ++ nafTableSlots publicJoint.K m

/-- The table after `m` entries, `R` holding `[k]Q`, from `s`. -/
structure TC (C : Curve) (base : Addr) (Q : Point C) (s t : State) (m k : Nat) : Prop where
  field : Inv publicJoint.K.M base 8192 C.p (·∈jointSlots publicJoint) (tcLive m)
    (tmv C 4 base t) t
  keep : JointLoopKeep publicJoint.K.M base tcW s t
  point : InvJ C (tmv C 4 base t publicJoint.K.R.x) (tmv C 4 base t publicJoint.K.R.y)
    (tmv C 4 base t publicJoint.K.R.z) (mul k Q)
  e : InvJ C (tmv C 4 base t publicJoint.K.E.x) (tmv C 4 base t publicJoint.K.E.y)
    (tmv C 4 base t publicJoint.K.E.z) (mul 2 Q)
  c2 : tmv C 4 base t publicJoint.selected =
    tmv C 4 base t publicJoint.K.E.z * tmv C 4 base t publicJoint.K.E.z
  c3 : tmv C 4 base t (publicJoint.selected + 8*publicJoint.K.M.n) =
    tmv C 4 base t publicJoint.selected * tmv C 4 base t publicJoint.K.E.z
  twice : InvJ C (tmv C 4 base t (Naf.twice publicJoint.K).x) (tmv C 4 base t (Naf.twice publicJoint.K).y)
    (tmv C 4 base t (Naf.twice publicJoint.K).z) (mul 2 Q)
  table : ∀ a, 1≤a → a≤m → InvJ C (tmv C 4 base t (publicJoint.K.tblPt a).x)
    (tmv C 4 base t (publicJoint.K.tblPt a).y) (tmv C 4 base t (publicJoint.K.tblPt a).z) (mul (2*a-1) Q)
  counter : t.gpr .rbx = BitVec.ofNat 64 m
  ro : ∀ x∈winRo publicJoint.K, tmv C 4 base t x = tmv C 4 base s x

/-! ## The layout's facts -/

theorem k_n : publicJoint.K.M.n = 4 := rfl

theorem lay : Lay publicJoint.K.M 8192 (·∈jointSlots publicJoint) := joint_layout.lay

theorem fixed_sl : ∀ x∈tcFixed, x∈jointSlots publicJoint := by decide +kernel

theorem tcW_sl : ∀ x∈tcW, x∈jointSlots publicJoint := by decide +kernel

theorem tcW_init : ∀ x∈tcW, x∈jointInitWork publicJoint := by decide +kernel

theorem tbl_sl : ∀ a, 1≤a → a≤9 → ∀ x∈jacCoords (publicJoint.K.tblPt a), x∈jointSlots publicJoint := by
  have h : ∀ a<10, 1≤a → ∀ x∈jacCoords (publicJoint.K.tblPt a), x∈jointSlots publicJoint := by
    decide +kernel
  exact fun a h1 h9 => h a (by omega) h1

theorem tbl_w : ∀ a, 1≤a → a≤9 → ∀ x∈jacCoords (publicJoint.K.tblPt a), x∈tcW := by
  have h : ∀ a<10, 1≤a → ∀ x∈jacCoords (publicJoint.K.tblPt a), x∈tcW := by decide +kernel
  exact fun a h1 h9 => h a (by omega) h1

/-- The writes of a cached addition's body, apart from the fixed slots but `R`
and from the table's entries. -/
def addW : List Nat := rcbW publicJoint.K.S publicJoint.K.D ++ jacCoords publicJoint.K.R

theorem addW_sl : ∀ x∈addW, x∈jointSlots publicJoint := by decide +kernel

theorem addW_w : ∀ x∈addW, x∈tcW := by decide +kernel

theorem addW_fixed : ∀ x∈tcFixed, x∉jacCoords publicJoint.K.R → x∉addW := by decide +kernel

theorem addW_tbl : ∀ a, 1≤a → a≤9 → ∀ x∈jacCoords (publicJoint.K.tblPt a), x∉addW := by
  have h : ∀ a<10, 1≤a → ∀ x∈jacCoords (publicJoint.K.tblPt a), x∉addW := by decide +kernel
  exact fun a h1 h9 => h a (by omega) h1

/-- Distinct entries are apart. -/
theorem tbl_tbl : ∀ a b, 1≤a → a≤9 → 1≤b → b≤9 → a≠b →
    ∀ x∈jacCoords (publicJoint.K.tblPt a), x∉jacCoords (publicJoint.K.tblPt b) := by
  intro a b h1 h9 g1 g9 hne x hx hy
  simp only [jacCoords,WinCfg.tblPt,k_n,List.mem_cons,List.not_mem_nil,or_false] at hx hy
  omega

theorem fixed_tbl : ∀ a, 1≤a → a≤8 → ∀ x∈tcFixed, x∉jacCoords (publicJoint.K.tblPt a) := by
  have h : ∀ a<9, 1≤a → ∀ x∈tcFixed, x∉jacCoords (publicJoint.K.tblPt a) := by decide +kernel
  exact fun a h1 h8 => h a (by omega) h1

theorem mem_tcLive_fixed {m x : Nat} (h : x∈tcFixed) : x∈tcLive m := List.mem_append_left _ h

theorem tblPt_mem_tcLive {m a : Nat} (h1 : 1≤a) (ha : a≤m) :
    ∀ x∈jacCoords (publicJoint.K.tblPt a), x∈tcLive m := by
  intro x hx
  apply List.mem_append_right
  simp only [jacCoords,WinCfg.tblPt,List.mem_cons,List.not_mem_nil,or_false] at hx
  simp only [nafTableSlots,List.mem_map,List.mem_range]
  rcases hx with rfl|rfl|rfl
  · exact ⟨3*(a-1),by omega,by rw [k_n]; omega⟩
  · exact ⟨3*(a-1)+1,by omega,by rw [k_n]; omega⟩
  · exact ⟨3*(a-1)+2,by omega,by rw [k_n]; omega⟩

theorem tcLive_sl {m : Nat} (hm : m≤9) : ∀ x∈tcLive m, x∈jointSlots publicJoint := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact fixed_sl x hx
  · simp only [nafTableSlots,List.mem_map,List.mem_range] at hx
    obtain ⟨i,hi,rfl⟩ := hx
    have h : ∀ i<27, publicJoint.K.tbl+8*publicJoint.K.M.n*i∈jointSlots publicJoint := by decide +kernel
    exact h i (by omega)

/-! ## The invariant through the steps -/

section
variable {C : Curve} {base : Addr} {Q : Point C}

/-- A slot apart from what a program writes keeps its value. -/
theorem tmv_keep {W : List Nat} {x y : State} (hk : ProgKeep publicJoint.K.M base W x y)
    (hs : Scr x base 8192) (hW : ∀ w∈W, w∈jointSlots publicJoint) {z : Nat}
    (hz : z∈jointSlots publicJoint) (hn : z∉W) : tmv C 4 base y z = tmv C 4 base x z := by
  unfold tmv
  rw [show 4 = publicJoint.K.M.n from rfl, hk.slot lay hs hW hz hn]

theorem invJ_keep {W : List Nat} {x y : State} (hk : ProgKeep publicJoint.K.M base W x y)
    (hs : Scr x base 8192) (hW : ∀ w∈W, w∈jointSlots publicJoint) {p : Pt}
    (hp : ∀ z∈jacCoords p, z∈jointSlots publicJoint) (hn : ∀ z∈jacCoords p, z∉W) {P : Point C}
    (h : InvJ C (tmv C 4 base x p.x) (tmv C 4 base x p.y) (tmv C 4 base x p.z) P) :
    InvJ C (tmv C 4 base y p.x) (tmv C 4 base y p.y) (tmv C 4 base y p.z) P := by
  rw [tmv_keep hk hs hW (hp _ (by simp [jacCoords])) (hn _ (by simp [jacCoords])),
    tmv_keep hk hs hW (hp _ (by simp [jacCoords])) (hn _ (by simp [jacCoords])),
    tmv_keep hk hs hW (hp _ (by simp [jacCoords])) (hn _ (by simp [jacCoords]))]
  exact h

/-- What keeps memory keeps the invariant, if it keeps `rbx` and `rdi`. -/
theorem TC.of_keeps {s x y : State} {m k : Nat} {rs : List Reg} (h : TC C base Q s x m k)
    (hk : Keeps rs x y) (hr : Reg.rbx∉rs) (hd : Reg.rdi∉rs) (hc : ∀ r∈rs, r∈Reg.rbx::clob 4) :
    TC C base Q s y m k := by
  have hm : y.mem = x.mem := hk.2.1
  have ht : ∀ z, tmv C 4 base y z = tmv C 4 base x z := fun z => by unfold tmv; rw [hm]
  refine ⟨(h.field.of_keeps hk hd).to_tmv, h.keep.trans ⟨(VG.Proof.Mont.X86_64.Keeps.regs hk).mono hc, fun z _ => by rw [hm]⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [ht]
  · exact h.point
  · exact h.e
  · exact h.c2
  · exact h.c3
  · exact h.twice
  · exact h.table
  · rw [hk.1 _ hr]; exact h.counter
  · exact h.ro

theorem R_fixed : ∀ z∈jacCoords publicJoint.K.R, z∈tcFixed := by decide +kernel

theorem rcbR_fixed : ∀ z∈rcbR publicJoint.K.S publicJoint.K.R publicJoint.K.E, z∈tcFixed := by
  decide +kernel

theorem tcLive_next (m : Nat) :
    ∀ x∈tcLive (m+1), x∈jacCoords (publicJoint.K.tblPt (m+1)) ++ tcLive m := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact List.mem_append_right _ (List.mem_append_left _ hx)
  · simp only [nafTableSlots,List.mem_map,List.mem_range] at hx
    obtain ⟨i,hi,rfl⟩ := hx
    by_cases h : i<3*m
    · exact List.mem_append_right _ (List.mem_append_right _
        (List.mem_map.mpr ⟨i,List.mem_range.mpr h,rfl⟩))
    · apply List.mem_append_left
      simp only [jacCoords,WinCfg.tblPt,k_n,List.mem_cons,List.not_mem_nil,or_false]
      omega

theorem table_step_ok {s t : State} {m : Nat} (hm : UnitMod C.p (2^(64*publicJoint.K.M.n)))
    (hC : Law C) (hd : JDblOk C dblJ0) (hOne : publicJoint.K.one<C.p) (hQ : onCurve C Q=true)
    (hm1 : 1≤m) (hm7 : m≤7) (h : TC C base Q s t m (2*m-1)) :
    WP isa (Joint.tableCallStep publicJoint Impl.Weierstrass.PointOps.secp256k1).inline t
      (fun u => TC C base Q s u (m+1) (2*(m+1)-1) ∧ u.cf=some (decide (m+1<8))) := by
  have hnc : (PointOps.addCachedBody publicJoint.K publicJoint.selected dblJ0).noCalls=true := by
    decide +kernel
  have hclob : ∀ r∈Proof.Weierstrass.X86_64.PointOps.keptRegs, r∈clob publicJoint.K.M.n := by
    decide
  rw [Joint.tableCallStep]
  simp only [Code.inline]
  apply WP.seq
  have call : WP isa (PointOps.wrap (PointOps.addCachedBody publicJoint.K publicJoint.selected dblJ0)) t
      (fun u => ProgKeep publicJoint.K.M base addW t u ∧ TC C base Q s u m (2*m+1)) := by
    refine Proof.Weierstrass.X86_64.PointOps.wrap_keep_ok (P := fun x => TC C base Q s x m (2*m-1))
      (F := fun u => TC C base Q s u m (2*m+1)) hclob
      (fun x y _ k _ hx => hx.of_keeps k (by simp) (by simp) (by simp))
      (fun x y _ k _ hx => hx.of_keeps k (by decide) (by decide)
        (fun r hr => List.mem_cons_of_mem _ (hclob r hr))) h fun x hx => ?_
    rw [← Code.inline_of_noCalls hnc, PointOps.addCachedBody]
    simp only [Code.inline]
    apply WP.seq
    have Lfix : ∀ z∈tcFixed, z∈tcLive m := fun _ hz => mem_tcLive_fixed hz
    refine WP.mono (cachedJacAdd_ok lay hm hC hd joint_add_layout.addApart joint_add_layout.cache2Apart
      joint_add_layout.cache3Apart ⟨by decide +kernel,by decide +kernel⟩ (by decide +kernel) hx.field
      (fun z hz => Lfix z (rcbR_fixed z hz)) ⟨Lfix _ (by decide +kernel),Lfix _ (by decide +kernel)⟩
      hx.c2 hx.c3 hOne (hC.onCurve_mul hQ _) (hC.onCurve_mul hQ _) hx.point hx.e)
      fun d ⟨E',kd,id,jd⟩ => ?_
    refine WP.mono (copyPointFields_ok lay joint_add_layout.accumNodup joint_add_layout.copyApart
      (by decide +kernel) id (fun _ hz => List.mem_append_left _ hz)) fun u ⟨E'',ku,iu,vu⟩ => ?_
    have kw : ProgKeep publicJoint.K.M base addW x u :=
      (kd.mono (fun _ hz => List.mem_append_left _ hz)).trans (ku.mono (fun _ hz => List.mem_append_right _ hz))
    have hs := hx.field.scr
    refine ⟨kw,iu.to_tmv.sub (fun _ hz => List.mem_append_right _ (List.mem_append_right _ hz)),
      hx.keep.trans (JointLoopKeep.of_prog (kw.mono addW_w)),?_,
      invJ_keep kw hs addW_sl (by decide +kernel) (by decide +kernel) hx.e,?_,?_,
      invJ_keep kw hs addW_sl (by decide +kernel) (by decide +kernel) hx.twice,
      fun a h1 ha => invJ_keep kw hs addW_sl (tbl_sl a h1 (by omega)) (addW_tbl a h1 (by omega))
        (hx.table a h1 ha),?_,?_⟩
    · have jr : InvJ C (E'' publicJoint.K.R.x) (E'' publicJoint.K.R.y) (E'' publicJoint.K.R.z)
          (add (mul (2*m-1) Q) (mul 2 Q)) := by
        simp only [Prod.mk.injEq] at vu
        rw [vu.1,vu.2.1,vu.2.2]
        exact jd
      have jt := iu.point_tmv (fun _ hz => List.mem_append_left _ hz) jr
      rw [hC.add_mul_mul hQ,show 2*m-1+2=2*m+1 by omega] at jt
      exact jt
    · rw [tmv_keep kw hs addW_sl (by decide +kernel) (by decide +kernel),
        tmv_keep kw hs addW_sl (by decide +kernel) (by decide +kernel)]
      exact hx.c2
    · rw [tmv_keep kw hs addW_sl (by decide +kernel) (by decide +kernel),
        tmv_keep kw hs addW_sl (by decide +kernel) (by decide +kernel),
        tmv_keep kw hs addW_sl (by decide +kernel) (by decide +kernel)]
      exact hx.c3
    · rw [kw.gpr _ (rbx_not_clob _)]
      exact hx.counter
    · intro z hz
      have hzf : z∈tcFixed := by revert z hz; decide +kernel
      have hzr : z∉jacCoords publicJoint.K.R := by revert z hz; decide +kernel
      exact (tmv_keep kw hs addW_sl (fixed_sl z hzf) (addW_fixed z hzf hzr)).trans (hx.ro z hz)
  refine WP.mono call fun u ⟨_,hu⟩ => ?_
  rw [WP.block_append_iff]
  have hs := hu.field.scr
  refine WP.mono (nafTableFields_ok lay (Or.inl rfl) rfl rfl hu.field (j:=m) (by omega) hu.counter
    (by decide) (by decide) (tbl_sl (m+1) (by omega) (by omega))
    (fun z hz => mem_tcLive_fixed (R_fixed z hz)) (by decide)) fun v ⟨kv,iv⟩ => ?_
  have hsv : Scr v base 8192 := kv.scr hs
  refine WP.mono (nafTable_advance_ok (m:=m) (by omega)
    (by rw [kv.gpr _ (rbx_not_clob _)]; exact hu.counter)) fun w ⟨cw,cf,kk⟩ => ⟨?_,cf⟩
  have hmw : w.mem = v.mem := kk.2.1
  have tw : ∀ z, tmv C 4 base w z = tmv C 4 base v z := fun z => by unfold tmv; rw [hmw]
  have hW : ∀ z∈jacCoords (publicJoint.K.tblPt (m+1)), z∈jointSlots publicJoint :=
    tbl_sl (m+1) (by omega) (by omega)
  have keepF : ∀ z∈tcFixed, tmv C 4 base w z = tmv C 4 base u z := fun z hz =>
    (tw z).trans (tmv_keep kv hs hW (fixed_sl z hz) (fixed_tbl (m+1) (by omega) (by omega) z hz))
  have keepJ : ∀ {p : Pt}, (∀ z∈jacCoords p, z∈tcFixed) → ∀ {P : Point C},
      InvJ C (tmv C 4 base u p.x) (tmv C 4 base u p.y) (tmv C 4 base u p.z) P →
      InvJ C (tmv C 4 base w p.x) (tmv C 4 base w p.y) (tmv C 4 base w p.z) P := by
    intro p hp P hP
    rw [keepF _ (hp _ (by simp [jacCoords])),keepF _ (hp _ (by simp [jacCoords])),
      keepF _ (hp _ (by simp [jacCoords]))]
    exact hP
  refine ⟨((iv.of_keeps kk (by decide)).to_tmv).sub (tcLive_next m),
    hu.keep.trans ((JointLoopKeep.of_prog (kv.mono (tbl_w (m+1) (by omega) (by omega)))).trans
      (JointLoopKeep.of_keeps kk)),?_,keepJ (by decide +kernel) hu.e,?_,?_,
    keepJ (by decide +kernel) hu.twice,?_,cw,?_⟩
  · rw [show 2*(m+1)-1=2*m+1 by omega]
    exact keepJ (by decide +kernel) hu.point
  · rw [keepF _ (by decide +kernel),keepF _ (by decide +kernel)]
    exact hu.c2
  · rw [keepF _ (by decide +kernel),keepF _ (by decide +kernel),keepF _ (by decide +kernel)]
    exact hu.c3
  · intro a h1 ha
    by_cases he : a=m+1
    · subst he
      have nv : ∀ z∈jacCoords (publicJoint.K.tblPt (m+1)),
          tmv C 4 base w z = pointTransferEnv (tmv C 4 base u) (publicJoint.K.tblPt (m+1))
            publicJoint.K.R z := fun z hz => (tw z).trans (iv.val z (List.mem_append_left _ hz))
      have ne1 : (publicJoint.K.tblPt (m+1)).y≠(publicJoint.K.tblPt (m+1)).x := by
        simp only [WinCfg.tblPt,k_n]; omega
      have ne2 : (publicJoint.K.tblPt (m+1)).z≠(publicJoint.K.tblPt (m+1)).x := by
        simp only [WinCfg.tblPt,k_n]; omega
      have ne3 : (publicJoint.K.tblPt (m+1)).z≠(publicJoint.K.tblPt (m+1)).y := by
        simp only [WinCfg.tblPt,k_n]; omega
      rw [nv _ (by simp [jacCoords]),nv _ (by simp [jacCoords]),nv _ (by simp [jacCoords])]
      simp only [pointTransferEnv,ne1,ne2,ne3,↓reduceIte]
      rw [show 2*(m+1)-1=2*m+1 by omega]
      exact hu.point
    · have ham : a≤m := by omega
      have hn : ∀ z∈jacCoords (publicJoint.K.tblPt a), z∉jacCoords (publicJoint.K.tblPt (m+1)) :=
        tbl_tbl a (m+1) h1 (by omega) (by omega) (by omega) he
      have ht := hu.table a h1 ham
      have eqa : ∀ z∈jacCoords (publicJoint.K.tblPt a), tmv C 4 base w z = tmv C 4 base u z :=
        fun z hz => (tw z).trans (tmv_keep kv hs hW (tbl_sl a h1 (by omega) z hz) (hn z hz))
      rw [eqa _ (by simp [jacCoords]),eqa _ (by simp [jacCoords]),eqa _ (by simp [jacCoords])]
      exact ht
  · intro z hz
    exact (keepF z (by revert z hz; decide +kernel)).trans (hu.ro z hz)

/-- The live slots of the table, `R`'s and `P`'s among them. -/
theorem nafTableLive_tcLive : ∀ z∈nafTableLive publicJoint.K 8, z∈tcLive 8 := by
  intro z hz
  simp only [nafTableLive,List.mem_append] at hz
  rcases hz with ((hz|hz)|hz)|hz
  · exact List.mem_append_left _ (by revert z hz; decide +kernel)
  · exact List.mem_append_left _ (by revert z hz; decide +kernel)
  · exact List.mem_append_left _ (by revert z hz; decide +kernel)
  · exact List.mem_append_right _ hz

/-- The table's eight entries give what the joint loop needs. -/
theorem TC.post {s t : State} {k : Nat} (h : TC C base Q s t 8 k) :
    JointTablePost publicJoint C base 8192 Q s t where
  field := h.field.sub nafTableLive_tcLive
  keep := h.keep.regs
  unch := h.keep.unch.mono (by
    intro w hw
    simp only [jointInitRanges,List.mem_append,List.mem_map,List.mem_singleton] at hw ⊢
    rcases hw with ⟨x,hx,rfl⟩|rfl
    · exact Or.inl ⟨x,tcW_init x hx,rfl⟩
    · exact Or.inr rfl)
  ro := h.ro
  table := h.table

/-- The values of `cacheE`: `Z²` and `Z³` of `E`. -/
theorem cacheE_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps (Joint.cacheE publicJoint) e publicJoint.selected = e publicJoint.K.E.z * e publicJoint.K.E.z ∧
    runOps (Joint.cacheE publicJoint) e (publicJoint.selected + 8*publicJoint.K.M.n) =
      runOps (Joint.cacheE publicJoint) e publicJoint.selected * e publicJoint.K.E.z ∧
    ∀ z, z≠publicJoint.selected → z≠publicJoint.selected + 8*publicJoint.K.M.n →
      runOps (Joint.cacheE publicJoint) e z = e z := by
  have h1 : publicJoint.selected + 8*publicJoint.K.M.n ≠ publicJoint.selected := by decide
  have h2 : publicJoint.K.E.z ≠ publicJoint.selected := by decide +kernel
  have h1' : publicJoint.selected ≠ publicJoint.selected + 8*publicJoint.K.M.n := Ne.symm h1
  refine ⟨?_,?_,fun z hz1 hz2 => ?_⟩
  · simp only [Joint.cacheE, runOps, List.foldl, FOp.run, Function.update_apply, h1', h2, ite_true,
      ite_false]
  · simp only [Joint.cacheE, runOps, List.foldl, FOp.run, Function.update_apply, h1, h1', h2,
      ite_true, ite_false]
  · simp only [Joint.cacheE, runOps, List.foldl, FOp.run, Function.update_apply, hz1, hz2, ite_false]

/-- The table by calls builds the table. -/
theorem table_call_ok : JointTableCallOk publicJoint Impl.Weierstrass.PointOps.secp256k1 8192 := by
  intro C base Q s hm hC hd hOne hQ hi hp h1
  have hs := hi.scr
  have hi' : Inv publicJoint.K.M base 8192 C.p (·∈jointSlots publicJoint) (winRo publicJoint.K)
      (tmv C 4 base s) s :=
    ⟨hi.scr,hi.mod,fun x hx => List.mem_append_left _ (List.mem_append_left _ (hi.sl x hx)),hi.lt,hi.val⟩
  have roSl : ∀ z∈winRo publicJoint.K, z∈jointSlots publicJoint := by decide +kernel
  have roW : ∀ z∈winRo publicJoint.K, z∉tcW := by decide +kernel
  have tcW' : ∀ {W : List Nat}, (∀ z∈W, z∈tcW) → ∀ z∈W, z∈jointSlots publicJoint :=
    fun hW z hz => tcW_sl z (hW z hz)
  -- `ro` along any writes within `tcW`
  have roK : ∀ {W : List Nat} {x y : State}, (∀ z∈W, z∈tcW) → ProgKeep publicJoint.K.M base W x y →
      Scr x base 8192 → ∀ z∈winRo publicJoint.K, tmv C 4 base y z = tmv C 4 base x z :=
    fun hW hk hx z hz => tmv_keep hk hx (tcW' hW) (roSl z hz) (fun h => roW z hz (hW z h))
  rw [Joint.tableCall]
  simp only [Code.inline]
  -- `R = Q`
  apply WP.seq
  refine WP.mono (copyPointFields_ok lay (o:=publicJoint.K.R) (q:=publicJoint.K.P) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hi' (by decide +kernel)) fun a ⟨ea,ka,ia,va⟩ => ?_
  have hsa := ka.scr hs
  have jaR : InvJ C (tmv C 4 base a publicJoint.K.R.x) (tmv C 4 base a publicJoint.K.R.y)
      (tmv C 4 base a publicJoint.K.R.z) Q := by
    apply ia.point_tmv (fun _ hz => List.mem_append_left _ hz)
    simp only [Prod.mk.injEq] at va
    rw [va.1,va.2.1,va.2.2]
    exact hp
  have wa : ∀ z∈jacCoords publicJoint.K.R, z∈tcW := by decide +kernel
  have Ia : Inv publicJoint.K.M base 8192 C.p (·∈jointSlots publicJoint)
      (jacCoords publicJoint.K.R ++ winRo publicJoint.K) (tmv C 4 base a) a := ia.to_tmv
  -- `R = 2Q`, by a call of `vg_secp256k1_jac_double`
  apply WP.seq
  have hnc : (PointOps.doubleBody publicJoint.K dblJ0).noCalls=true := by decide +kernel
  have hclob : ∀ r∈Proof.Weierstrass.X86_64.PointOps.keptRegs, r∈clob publicJoint.K.M.n := by decide
  let V1 := jacCoords publicJoint.K.R ++ winRo publicJoint.K
  have dbl : WP isa (PointOps.wrap (PointOps.doubleBody publicJoint.K dblJ0)) a (fun b =>
      ProgKeep publicJoint.K.M base addW a b ∧
      (Inv publicJoint.K.M base 8192 C.p (·∈jointSlots publicJoint) V1 (tmv C 4 base b) b ∧
        InvJ C (tmv C 4 base b publicJoint.K.R.x) (tmv C 4 base b publicJoint.K.R.y)
          (tmv C 4 base b publicJoint.K.R.z) (mul 2 Q))) := by
    have keepP : ∀ (P : Point C) (rs : List Reg), Reg.rdi∉rs → ∀ x y, Keeps rs x y →
        (Inv publicJoint.K.M base 8192 C.p (·∈jointSlots publicJoint) V1 (tmv C 4 base x) x ∧
          InvJ C (tmv C 4 base x publicJoint.K.R.x) (tmv C 4 base x publicJoint.K.R.y)
            (tmv C 4 base x publicJoint.K.R.z) P) →
        (Inv publicJoint.K.M base 8192 C.p (·∈jointSlots publicJoint) V1 (tmv C 4 base y) y ∧
          InvJ C (tmv C 4 base y publicJoint.K.R.x) (tmv C 4 base y publicJoint.K.R.y)
            (tmv C 4 base y publicJoint.K.R.z) P) := by
      intro P rs hr x y k ⟨hI,hJ⟩
      have ht : ∀ z, tmv C 4 base y z = tmv C 4 base x z := fun z => by unfold tmv; rw [k.2.1]
      refine ⟨(hI.of_keeps k hr).to_tmv,?_⟩
      simp only [ht]
      exact hJ
    refine Proof.Weierstrass.X86_64.PointOps.wrap_keep_ok hclob
      (fun x y _ k _ hx => keepP Q [] (by simp) x y k hx)
      (fun x y _ k _ hx => keepP (mul 2 Q) _ (by decide) x y k hx) ⟨Ia,jaR⟩ fun x ⟨hI,hJ⟩ => ?_
    rw [← Code.inline_of_noCalls hnc, PointOps.doubleBody]
    simp only [Code.inline]
    apply WP.seq
    have apart : RcbApart publicJoint.K.S publicJoint.K.R publicJoint.K.R publicJoint.K.D :=
      ⟨joint_add_layout.addApart.nodup,fun x hx => joint_add_layout.addApart.apart x (by
        simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)⟩
    refine WP.mono (jacDouble_ok lay hm hd apart (by decide +kernel) hI (by decide +kernel) hQ hJ)
      fun d ⟨kd,id,jd⟩ => ?_
    refine WP.mono (copyPointFields_ok lay joint_add_layout.accumNodup joint_add_layout.copyApart
      (by decide +kernel) id (fun _ hz => List.mem_append_left _ hz)) fun u ⟨E'',ku,iu,vu⟩ => ?_
    refine ⟨(kd.mono (fun _ hz => List.mem_append_left _ hz)).trans
        (ku.mono (fun _ hz => List.mem_append_right _ hz)),
      iu.to_tmv.sub (fun _ hz => List.mem_append_right _ (List.mem_append_right _ hz)),?_⟩
    have jr : InvJ C (E'' publicJoint.K.R.x) (E'' publicJoint.K.R.y) (E'' publicJoint.K.R.z)
        (add Q Q) := by
      simp only [Prod.mk.injEq] at vu
      rw [vu.1,vu.2.1,vu.2.2]
      exact jd
    have jt := iu.point_tmv (fun _ hz => List.mem_append_left _ hz) jr
    rwa [← mul_one_pt Q,hC.add_mul_mul hQ] at jt
  refine WP.mono dbl fun b ⟨kb,Ib,jbR⟩ => ?_
  have hsb := kb.scr hsa
  -- `E = 2Q` and the ninth entry `2Q`
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (copyPointFields_ok lay (o:=publicJoint.K.E) (q:=publicJoint.K.R) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) Ib (fun _ hz => List.mem_append_left _ hz))
    fun c1 ⟨e1,k1,i1,v1⟩ => ?_
  refine WP.mono (copyPointFields_ok lay (o:=Naf.twice publicJoint.K) (q:=publicJoint.K.R)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) i1
    (fun _ hz => List.mem_append_right _ (List.mem_append_left _ hz))) fun c ⟨e2,k2,i2,v2⟩ => ?_
  have hsc := k2.scr (k1.scr hsb)
  have I2 := i2.to_tmv
  have jE : InvJ C (tmv C 4 base c publicJoint.K.E.x) (tmv C 4 base c publicJoint.K.E.y)
      (tmv C 4 base c publicJoint.K.E.z) (mul 2 Q) := by
    have j1 : InvJ C (tmv C 4 base c1 publicJoint.K.E.x) (tmv C 4 base c1 publicJoint.K.E.y)
        (tmv C 4 base c1 publicJoint.K.E.z) (mul 2 Q) := by
      apply i1.point_tmv (fun _ hz => List.mem_append_left _ hz)
      simp only [Prod.mk.injEq] at v1
      rw [v1.1,v1.2.1,v1.2.2]
      exact jbR
    exact invJ_keep k2 (k1.scr hsb) (by decide +kernel) (by decide +kernel) (by decide +kernel) j1
  have jT : InvJ C (tmv C 4 base c (Naf.twice publicJoint.K).x) (tmv C 4 base c (Naf.twice publicJoint.K).y)
      (tmv C 4 base c (Naf.twice publicJoint.K).z) (mul 2 Q) := by
    have jR1 := invJ_keep k1 hsb (by decide +kernel) (by decide +kernel) (by decide +kernel) jbR
    apply i2.point_tmv (fun _ hz => List.mem_append_left _ hz)
    simp only [Prod.mk.injEq] at v2
    rw [v2.1,v2.2.1,v2.2.2]
    have e1R : ∀ z∈jacCoords publicJoint.K.R, e1 z = tmv C 4 base c1 z := fun z hz =>
      (i1.val z (List.mem_append_right _ (List.mem_append_left _ hz))).symm
    rw [e1R _ (by simp [jacCoords]),e1R _ (by simp [jacCoords]),e1R _ (by simp [jacCoords])]
    exact jR1
  -- `E`'s `Z²` and `Z³`
  apply WP.seq
  refine WP.mono (fprogB_ok lay hm (Joint.cacheE publicJoint) I2 (by decide +kernel) (by decide +kernel))
    fun d ⟨kd,id⟩ => ?_
  have hsd := kd.scr hsc
  have cr := cacheE_run (tmv C 4 base c)
  have tvd : ∀ z∈[publicJoint.selected,publicJoint.selected + 8*publicJoint.K.M.n],
      tmv C 4 base d z = runOps (Joint.cacheE publicJoint) (tmv C 4 base c) z := fun z hz =>
    id.val z ((mem_validAfter _ _).mpr (Or.inr (by revert z hz; decide +kernel)))
  have cW : ∀ z∈(Joint.cacheE publicJoint).map FOp.out, z∈tcW := by decide +kernel
  have kEz : tmv C 4 base d publicJoint.K.E.z = tmv C 4 base c publicJoint.K.E.z :=
    tmv_keep kd hsc (tcW' cW) (by decide +kernel) (by decide +kernel)
  have c2d : tmv C 4 base d publicJoint.selected =
      tmv C 4 base d publicJoint.K.E.z * tmv C 4 base d publicJoint.K.E.z := by
    rw [tvd _ (by simp),cr.1,kEz]
  have c3d : tmv C 4 base d (publicJoint.selected + 8*publicJoint.K.M.n) =
      tmv C 4 base d publicJoint.selected * tmv C 4 base d publicJoint.K.E.z := by
    rw [tvd _ (by simp),tvd _ (by simp),cr.2.1,kEz]
  have Id : Inv publicJoint.K.M base 8192 C.p (·∈jointSlots publicJoint) tcFixed (tmv C 4 base d) d :=
    id.to_tmv.sub (by decide +kernel)
  -- `Q` in the first entry and `R`, and the counter
  apply WP.seq
  rw [List.append_assoc,WP.block_append_iff]
  have hP : ∀ z∈jacCoords publicJoint.K.P, z∈tcFixed := by decide +kernel
  refine WP.mono (copyPointFields_ok lay (o:=publicJoint.K.tblPt 1) (q:=publicJoint.K.P)
    (by decide +kernel) (by decide +kernel) (tbl_sl 1 (by decide) (by decide)) Id hP)
    fun f ⟨ef,kf,iff,vf⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyPointFields_ok lay (o:=publicJoint.K.R) (q:=publicJoint.K.P)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) iff
    (fun z hz => List.mem_append_right _ (hP z hz))) fun g ⟨eg,kg,ig,vg⟩ => ?_
  refine WP.mono (nafTable_initCounter_ok g) fun t₀ ⟨ct,kt⟩ => ?_
  have hsf := kf.scr hsd
  have hsg := kg.scr hsf
  -- `P` is `Q` until then: no write reaches it.
  have Wall : ∀ z∈addW ++ jacCoords publicJoint.K.E ++ jacCoords (Naf.twice publicJoint.K) ++
      (Joint.cacheE publicJoint).map FOp.out ++ jacCoords (publicJoint.K.tblPt 1), z∈tcW := by
    decide +kernel
  have kAll : ProgKeep publicJoint.K.M base (jacCoords publicJoint.K.R ++ (addW ++
      jacCoords publicJoint.K.E ++ jacCoords (Naf.twice publicJoint.K) ++
      (Joint.cacheE publicJoint).map FOp.out ++ jacCoords (publicJoint.K.tblPt 1))) s f :=
    (ka.mono (fun _ hz => List.mem_append_left _ hz)).trans
      ((kb.mono (by intro z hz; simp only [List.mem_append] at hz ⊢; grind)).trans
      ((k1.mono (by intro z hz; simp only [List.mem_append] at hz ⊢; grind)).trans
      ((k2.mono (by intro z hz; simp only [List.mem_append] at hz ⊢; grind)).trans
      ((kd.mono (by intro z hz; simp only [List.mem_append] at hz ⊢; grind)).trans
      (kf.mono (by intro z hz; simp only [List.mem_append] at hz ⊢; grind))))))
  have kAllW : ∀ z∈jacCoords publicJoint.K.R ++ (addW ++
      jacCoords publicJoint.K.E ++ jacCoords (Naf.twice publicJoint.K) ++
      (Joint.cacheE publicJoint).map FOp.out ++ jacCoords (publicJoint.K.tblPt 1)), z∈tcW := by
    decide +kernel
  have jPf : InvJ C (tmv C 4 base f publicJoint.K.P.x) (tmv C 4 base f publicJoint.K.P.y)
      (tmv C 4 base f publicJoint.K.P.z) Q :=
    invJ_keep kAll hs (tcW' kAllW) (by decide +kernel) (by decide +kernel) hp
  have jPd : InvJ C (tmv C 4 base d publicJoint.K.P.x) (tmv C 4 base d publicJoint.K.P.y)
      (tmv C 4 base d publicJoint.K.P.z) Q := by
    have := jPf
    rwa [tmv_keep kf hsd (tbl_sl 1 (by decide) (by decide)) (by decide +kernel) (by decide +kernel),
      tmv_keep kf hsd (tbl_sl 1 (by decide) (by decide)) (by decide +kernel) (by decide +kernel),
      tmv_keep kf hsd (tbl_sl 1 (by decide) (by decide)) (by decide +kernel) (by decide +kernel)] at this
  have j1f : InvJ C (tmv C 4 base f (publicJoint.K.tblPt 1).x) (tmv C 4 base f (publicJoint.K.tblPt 1).y)
      (tmv C 4 base f (publicJoint.K.tblPt 1).z) Q := by
    apply iff.point_tmv (fun _ hz => List.mem_append_left _ hz)
    simp only [Prod.mk.injEq] at vf
    rw [vf.1,vf.2.1,vf.2.2]
    exact jPd
  have jRg : InvJ C (tmv C 4 base g publicJoint.K.R.x) (tmv C 4 base g publicJoint.K.R.y)
      (tmv C 4 base g publicJoint.K.R.z) Q := by
    apply ig.point_tmv (fun _ hz => List.mem_append_left _ hz)
    simp only [Prod.mk.injEq] at vg
    have ef : ∀ z∈jacCoords publicJoint.K.P, ef z = tmv C 4 base f z := fun z hz =>
      (iff.val z (List.mem_append_right _ (hP z hz))).symm
    rw [vg.1,vg.2.1,vg.2.2,ef _ (by simp [jacCoords]),ef _ (by simp [jacCoords]),ef _ (by simp [jacCoords])]
    exact jPf
  have tt : ∀ z, tmv C 4 base t₀ z = tmv C 4 base g z := fun z => by unfold tmv; rw [kt.2.1]
  have kfg : ProgKeep publicJoint.K.M base (jacCoords (publicJoint.K.tblPt 1) ++ jacCoords publicJoint.K.R) d g :=
    (kf.mono (fun _ hz => List.mem_append_left _ hz)).trans (kg.mono (fun _ hz => List.mem_append_right _ hz))
  have kfgW : ∀ z∈jacCoords (publicJoint.K.tblPt 1) ++ jacCoords publicJoint.K.R, z∈jointSlots publicJoint := by
    decide +kernel
  have keepEd : ∀ z∈jacCoords publicJoint.K.E ++ jacCoords (Naf.twice publicJoint.K) ++
      [publicJoint.selected,publicJoint.selected + 8*publicJoint.K.M.n],
      tmv C 4 base t₀ z = tmv C 4 base d z := fun z hz =>
    (tt z).trans (tmv_keep kfg hsd kfgW (by revert z hz; decide +kernel) (by revert z hz; decide +kernel))
  have jEd := invJ_keep kd hsc (tcW' cW) (by decide +kernel) (by decide +kernel) jE
  have jTd := invJ_keep kd hsc (tcW' cW) (by decide +kernel) (by decide +kernel) jT
  have init : TC C base Q s t₀ 1 1 := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,ct,?_⟩
    · have it := (ig.of_keeps kt (by decide)).to_tmv
      refine it.sub fun z hz => ?_
      rcases List.mem_append.mp hz with hz|hz
      · by_cases hR : z∈jacCoords publicJoint.K.R
        · exact List.mem_append_left _ hR
        · exact List.mem_append_right _ (List.mem_append_right _ hz)
      · apply List.mem_append_right
        apply List.mem_append_left
        simp only [nafTableSlots,List.mem_map,List.mem_range] at hz
        obtain ⟨i,hi,rfl⟩ := hz
        simp only [jacCoords,WinCfg.tblPt,k_n,List.mem_cons,List.not_mem_nil,or_false]
        omega
    · exact (JointLoopKeep.of_prog (kAll.mono kAllW)).trans
        ((JointLoopKeep.of_prog (kg.mono (by decide +kernel))).trans (JointLoopKeep.of_keeps kt))
    · rw [mul_one_pt]
      simp only [tt]
      exact jRg
    · rw [keepEd _ (by decide +kernel),keepEd _ (by decide +kernel),keepEd _ (by decide +kernel)]
      exact jEd
    · rw [keepEd _ (by decide +kernel),keepEd _ (by decide +kernel)]
      exact c2d
    · rw [keepEd _ (by decide +kernel),keepEd _ (by decide +kernel),keepEd _ (by decide +kernel)]
      exact c3d
    · rw [keepEd _ (by decide +kernel),keepEd _ (by decide +kernel),keepEd _ (by decide +kernel)]
      exact jTd
    · intro a h1 ha
      obtain rfl : a=1 := by omega
      rw [show 2*1-1=1 from rfl,mul_one_pt]
      have kt1 : ∀ z∈jacCoords (publicJoint.K.tblPt 1), tmv C 4 base t₀ z = tmv C 4 base f z :=
        fun z hz => (tt z).trans (tmv_keep kg hsf (by decide +kernel)
          (tbl_sl 1 (by decide) (by decide) z hz) (by revert z hz; decide +kernel))
      rw [kt1 _ (by simp [jacCoords]),kt1 _ (by simp [jacCoords]),kt1 _ (by simp [jacCoords])]
      exact j1f
    · intro z hz
      exact (tt z).trans ((roK (by decide +kernel) kg hsf z hz).trans (roK kAllW kAll hs z hz))
  refine WP.loop (M:=isa) (fun j t => 1≤j ∧ j≤7 ∧ TC C base Q s t (8-j) (2*(8-j)-1))
    (fun j u ⟨hj,hj7,hu⟩ => ?_) 7 t₀ ⟨by decide,by decide,init⟩
  refine WP.mono (table_step_ok hm hC hd hOne hQ (by omega) (by omega) hu) fun t ⟨it,cf⟩ => ?_
  by_cases hj1 : j=1
  · subst j
    exact Or.inl ⟨cf,it.post⟩
  · refine Or.inr ⟨?_,j-1,by omega,by omega,by omega,?_⟩
    · change t.cf=some true
      rw [cf]; congr 1; exact decide_eq_true (by omega)
    · rw [show 8-(j-1)=8-j+1 from by omega]
      exact it

/-! ## Timing -/

/-- Two runs after `m` entries: the same values in the live slots, and `m` in `rbx`. -/
def TP (C : Curve) (base : Addr) (size m : Nat) (s t : State) : Prop :=
  ∃ E, FieldPair publicJoint.K.M base size C.p (·∈jointSlots publicJoint) (tcLive m) E s t ∧
    s.gpr .rbx=BitVec.ofNat 64 m ∧ t.gpr .rbx=BitVec.ofNat 64 m

theorem cV_fixed : ∀ x∈PointOps.cV publicJoint.K publicJoint.selected, x∈tcFixed := by decide +kernel

theorem cachedLay {size : Nat} (hL : JointInitLayout publicJoint size) :
    PointOps.CachedLay publicJoint.K publicJoint.selected size (·∈jointSlots publicJoint) dblJ0 :=
  ⟨hL.layout.lay,joint_add_layout.addApart,joint_add_layout.cache2Apart,joint_add_layout.cache3Apart,
    by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel⟩

theorem table_step_ct {C : Curve} {base : Addr} {size m : Nat} (hL : JointInitLayout publicJoint size)
    (hm : UnitMod C.p (2^(64*publicJoint.K.M.n))) (hOne : publicJoint.K.one<C.p) (hm8 : m<8)
    :
    RelCT isa (TP C base size m) (Joint.tableCallStep publicJoint Impl.Weierstrass.PointOps.secp256k1).inline
      (fun s t => TP C base size (m+1) s t ∧
        s.cf=some (decide (m+1<8)) ∧ t.cf=some (decide (m+1<8))) := by
  have hnc : (PointOps.addCachedBody publicJoint.K publicJoint.selected dblJ0).noCalls=true := by
    decide +kernel
  unfold TP
  apply RelCT.exists_
  intro E
  rw [Joint.tableCallStep]
  simp only [Code.inline]
  have hb := Proof.Weierstrass.X86_64.PointOps.addCachedBody_relCT (base:=base) (E:=E) (cachedLay hL) hm hOne
    joint_cached_checks.add joint_cached_checks.copy (V:=tcLive m) (fun x hx => mem_tcLive_fixed (cV_fixed x hx)) ⟨dblJ0N,dblJ0N_ok,dblJ0_eq⟩
  rw [Code.inline_of_noCalls hnc] at hb
  apply RelCT.seq ((relCT_keepGprS (v:=BitVec.ofNat 64 m) (Proof.Weierstrass.X86_64.PointOps.wrap_relCT hb) addCachedFn_keeps).mono
    (Q':=fun (s t : State) => ∃ e, FieldPair publicJoint.K.M base size C.p (·∈jointSlots publicJoint)
      (jacCoords publicJoint.K.R++tcLive m) e s t ∧
      s.gpr .rbx=BitVec.ofNat 64 m ∧ t.gpr .rbx=BitVec.ofNat 64 m)
    (fun _ _ h => h) (fun _ _ ⟨⟨e,p⟩,rest⟩ => ⟨e,p,rest⟩))
  apply RelCT.exists_
  intro e
  apply RelCT.block_append
  apply RelCT.seq (nafTableStore_relCT (base:=base) (j:=m) (E:=e) hL.layout.lay (Or.inl rfl) rfl rfl hm8
    hL.tableSmall (by have := hL.naf.table_le; omega) (tbl_sl (m+1) (by omega) (by omega))
    (fun _ hx => List.mem_append_left _ hx) (by decide) tableStore_ct)
  have adv := keepsField_relCT (M:=publicJoint.K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=(·∈jointSlots publicJoint))
    (V:=jacCoords (publicJoint.K.tblPt (m+1))++(jacCoords publicJoint.K.R++tcLive m))
    (E:=pointTransferEnv e (publicJoint.K.tblPt (m+1)) publicJoint.K.R)
    (Pre:=fun s => s.gpr .rbx=BitVec.ofNat 64 m)
    (Post:=fun s => s.gpr .rbx=BitVec.ofNat 64 (m+1) ∧ s.cf=some (decide (m+1<8)))
    (by decide : Reg.rdi∉[Reg.rbx]) tableAdvance_ct
    (fun _ _ _ ps pt => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ps.trans pt.symm))
    (fun _ _ hp => WP.mono (nafTable_advance_ok hm8 hp) (fun _ ⟨ct,cf,hk⟩ => ⟨⟨ct,cf⟩,hk⟩))
  exact adv.mono (fun _ _ h => h) (fun _ _ ⟨p,ps,pt⟩ =>
    ⟨⟨_,p.sub (fun x hx => by
      rcases List.mem_append.mp (tcLive_next m x hx) with hx|hx
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (List.mem_append_right _ hx)),ps.1,pt.1⟩,ps.2,pt.2⟩)

/-- The table by calls is constant time. -/
theorem table_call_ct : JointTableCallCT publicJoint Impl.Weierstrass.PointOps.secp256k1 := by
  intro C base size E hL hm hOne
  have lay := hL.layout.lay
  have hnc : (PointOps.doubleBody publicJoint.K dblJ0).noCalls=true := by decide +kernel
  let I := fun j s t => 1≤j ∧ j≤7 ∧ TP C base size (8-j) s t
  have step : ∀ j, RelCT isa (I j) (Joint.tableCallStep publicJoint Impl.Weierstrass.PointOps.secp256k1).inline
      (fun s t => eval .b s=eval .b t ∧
        (eval .b s=some false → TP C base size 8 s t) ∧
        (eval .b s=some true → ∃ n<j, I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hj7 : j≤7
      · refine (table_step_ct hL hm hOne (m:=8-j) (by omega)).mono
          (P':=I j) (fun _ _ h => h.2.2) ?_
        intro s t ⟨hp,cs,ct⟩
        refine ⟨cs.trans ct.symm,fun he => ?_,fun he => ?_⟩
        · change s.cf=some false at he
          have hn := of_decide_eq_false (Option.some.inj (cs.symm.trans he))
          have hj1 : j=1 := by omega
          subst j
          exact hp
        · change s.cf=some true at he
          have hy := of_decide_eq_true (Option.some.inj (cs.symm.trans he))
          refine ⟨j-1,by omega,by omega,by omega,?_⟩
          rw [show 8-(j-1)=8-j+1 from by omega]
          exact hp
      · exact RelCT.of_false (fun _ _ h => hj7 h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  have lift : ∀ {V : List Nat} {E : Nat → Fe C} {s : State},
      Inv publicJoint.K.M base size C.p (·∈nafSlots publicJoint.K) V E s →
      Inv publicJoint.K.M base size C.p (·∈jointSlots publicJoint) V E s :=
    fun hi => ⟨hi.scr,hi.mod,fun x hx => List.mem_append_left _ (List.mem_append_left _ (hi.sl x hx)),hi.lt,hi.val⟩
  rw [Joint.tableCall]
  simp only [Code.inline]
  refine RelCT.mono (P:=FieldPair publicJoint.K.M base size C.p (·∈jointSlots publicJoint)
    (winRo publicJoint.K) E) ?_ (fun _ _ h => ⟨lift h.1,lift h.2⟩) (fun _ _ h => h)
  -- `R = Q`
  apply RelCT.seq (copyPoint_relCT lay (o:=publicJoint.K.R) (q:=publicJoint.K.P) (E:=E)
    (V:=winRo publicJoint.K) (by decide +kernel) (by decide +kernel) tableCopyInit_ct)
  -- `R = 2R`, by a call of `vg_secp256k1_jac_double`
  have hdb : RelCT isa (FieldPair publicJoint.K.M base size C.p (·∈jointSlots publicJoint)
      (jacCoords publicJoint.K.R++winRo publicJoint.K)
      (copyPointEnv E publicJoint.K.R publicJoint.K.P)) (PointOps.doubleBody publicJoint.K dblJ0)
      (fun s t => ∃ E',FieldPair publicJoint.K.M base size C.p (·∈jointSlots publicJoint)
        (jacCoords publicJoint.K.R++winRo publicJoint.K) E' s t) := by
    rw [← Code.inline_of_noCalls hnc,PointOps.doubleBody]
    simp only [Code.inline]
    apply RelCT.seq (doubleFieldPlain_relCT lay hm (S:=publicJoint.K.S) (p:=publicJoint.K.R)
      (o:=publicJoint.K.D) (by decide +kernel) (by decide +kernel) ⟨dblJ0N,dblJ0N_ok,dblJ0_eq⟩ jointDouble_ct)
    exact (copyPoint_relCT lay (o:=publicJoint.K.R) (q:=publicJoint.K.D) (by decide +kernel)
      (fun _ hx => List.mem_append_left _ hx) joint_cached_checks.copy).mono (fun _ _ h => h)
      (fun _ _ h => ⟨_,h.sub (fun _ hx => List.mem_append_right _ (List.mem_append_right _ hx))⟩)
  apply RelCT.seq (Proof.Weierstrass.X86_64.PointOps.wrap_relCT hdb)
  apply RelCT.exists_
  intro E1
  -- `E = 2Q` and the ninth entry
  apply RelCT.seq (RelCT.block_append (RelCT.seq
    (copyPoint_relCT lay (o:=publicJoint.K.E) (q:=publicJoint.K.R) (E:=E1)
      (V:=jacCoords publicJoint.K.R++winRo publicJoint.K) (by decide +kernel)
      (fun _ hx => List.mem_append_left _ hx) tableE_ct)
    (copyPoint_relCT lay (o:=Naf.twice publicJoint.K) (q:=publicJoint.K.R)
      (by decide +kernel) (fun _ hx => List.mem_append_right _ (List.mem_append_left _ hx)) tableTwice_ct)))
  -- `E`'s `Z²` and `Z³`
  apply RelCT.seq (fieldProgram_relCT cacheE_ct (fun s hi =>
    WP.mono (fprogB_ok lay hm (Joint.cacheE publicJoint) hi (by decide +kernel) (by decide +kernel))
      (fun _ h => h.2)))
  -- `Q` in the first entry and `R`, and the counter
  rw [List.append_assoc]
  apply RelCT.seq (RelCT.block_append (RelCT.seq
    (copyPoint_relCT lay (o:=publicJoint.K.tblPt 1) (q:=publicJoint.K.P)
      (tbl_sl 1 (by decide) (by decide)) (by decide +kernel) tableCopyFirst_ct)
    (RelCT.block_append (RelCT.seq
      (copyPoint_relCT lay (o:=publicJoint.K.R) (q:=publicJoint.K.P)
        (by decide +kernel) (by decide +kernel) tableCopyInit_ct)
      ((keepsField_relCT (Pre:=fun _ => True) (Post:=fun s => s.gpr .rbx=1)
        (by decide : Reg.rdi∉[Reg.rbx]) tableCounter_ct (fun _ _ hp _ _ => fieldPair_public hp)
        (fun s _ _ => nafTable_initCounter_ok s)).mono (fun _ _ hp => ⟨hp,trivial,trivial⟩)
        (fun _ _ h => h))))))
  exact (RelCT.loop I step 7).mono (fun _ _ ⟨hp,hs,ht⟩ => ⟨by decide,by decide,_,
      hp.sub (by decide +kernel),hs,ht⟩)
    (fun _ _ ⟨E',hp,_,_⟩ => ⟨E',hp.sub nafTableLive_tcLive⟩)

end

theorem joint_init_layout : JointInitLayout publicJoint 8192 :=
  ⟨joint_layout,joint_naf_layout,by decide,by decide,by decide,by decide,by decide,by decide +kernel,
    by decide,by decide,fun _ C' h => by
      obtain rfl := Option.some.inj h
      exact table_call_ok⟩

end VG.Proof.Secp256k1.X86_64
