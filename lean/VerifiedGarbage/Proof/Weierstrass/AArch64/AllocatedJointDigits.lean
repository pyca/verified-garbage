module

public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
public import VerifiedGarbage.Impl.Weierstrass.AArch64.CachedJac
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Comb
public import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedAddField
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Jac
import VerifiedGarbage.Proof.Weierstrass.Comb
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafNeg
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigitRead
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoadTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch

/-! ### `Weierstrass.AArch64.CachedDigit`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.AArch64.CachedEntry`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.AArch64.CachedEntryLoad`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

theorem tmv_keep {M : Mod} {base : Addr} {size : Nat} {C : Curve} {Sl : Nat → Prop}
    (hL : Lay M size Sl) {s t : State} {W : List Nat}
    (hk : ProgKeep M base W s t) (hn : base.toNat+size≤2^64)
    (hW : ∀ w∈W,Sl w) {x : Nat} (hx : Sl x) (hne : x∉W) :
    tmv C M.n base t x=tmv C M.n base s x := by
  unfold tmv
  rw [hk.unch.wordsVal (fun q hq => ?_) (by have := hL.le x hx; omega_using [hn, this])]
  simp only [List.mem_append,List.mem_map,List.mem_singleton] at hq
  rcases hq with ⟨w,hw,rfl⟩ | rfl
  · exact hL.apart x w hx (hW w hw) (fun he => hne (he ▸ hw))
  · exact hL.tmp x hx

def entryWrites : List Nat := [K.E.x,K.E.y,K.E.z,5400,5432]
def entryLive (V : List Nat) : List Nat := [K.E.x,K.E.y,K.E.z]++([5400,5432]++V)

theorem entryLoad_ok {base : Addr} {size a : Nat} {C : Curve} {Sl : Nat → Prop}
    (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hsize : 6512≤size)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hi : Inv K.M base size C.p Sl V E s)
    (h2 : s.gpr .x2=BitVec.ofNat 64 a) (ha : 1≤a) (ha8 : a≤8)
    (hD : ∀ x∈entryWrites,Sl x)
    (hT : ∀ x∈[(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z,
      6000+64*(a-1),6032+64*(a-1)],x∈V)
    (hz2 : E (6000+64*(a-1))=E (Jacobian.tablePt K a).z*E (Jacobian.tablePt K a).z)
    (hz3 : E (6032+64*(a-1))=E (Jacobian.tablePt K a).z*(E (Jacobian.tablePt K a).z*E (Jacobian.tablePt K a).z))
    {P : Point C} (hJ : InvJ C (E (Jacobian.tablePt K a).x) (E (Jacobian.tablePt K a).y)
      (E (Jacobian.tablePt K a).z) P) :
    WP isa (.block (CachedJac.load++Jacobian.publicEntry K)) s fun t =>
      ProgKeep K.M base entryWrites s t ∧
      Inv K.M base size C.p Sl (entryLive V) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y) (tmv C K.M.n base t K.E.z) P ∧
      tmv C K.M.n base t 5400=tmv C K.M.n base t K.E.z*tmv C K.M.n base t K.E.z ∧
      tmv C K.M.n base t 5432=tmv C K.M.n base t K.E.z*(tmv C K.M.n base t K.E.z*tmv C K.M.n base t K.E.z) := by
  have dc : ∀ x∈[5400,5432],Sl x := fun x hx => hD x (by
    simp only [entryWrites,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)
  have de : ∀ x∈[K.E.x,K.E.y,K.E.z],Sl x := fun x hx => hD x (by
    simp only [entryWrites,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)
  have st : ∀ x∈[(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z],x∈V :=
    fun x hx => hT x (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)
  rw [WP.block_append_iff]
  refine WP.mono (cachedLoadField_ok hL (by rfl) hi h2 ha ha8 hsize dc
    (fun x hx => hT x (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)))
    fun b ⟨kb,ib,b2,b3,bidx0⟩ => ?_
  have bt : ∀ x∈[(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z],
      tmv C K.M.n base b x=E x := by
    intro x hx
    rw [tmv_keep hL kb hi.scr.nowrap dc (hi.sl x (st x hx)) ?_]
    exact hi.val x (st x hx)
    simp only [Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    rw [not_or]
    have ht : K.tbl=2848 := rfl
    rw [ht] at hx
    omega_using [hx]
  have bidx : b.gpr .x2=BitVec.ofNat 64 a := bidx0.trans h2
  refine WP.mono (jacPublicFields_ok hL hAl (by rfl) (by rfl) (by rfl) ib bidx ha (by decide)
    de (fun x hx => List.mem_append_right _ (st x hx)) (Or.inl (by change 704+96≤2848+96*(a-1); omega_using [])))
    fun t ⟨kt,it,vt⟩ => ?_
  have vals : (tmv C K.M.n base t K.E.x,tmv C K.M.n base t K.E.y,tmv C K.M.n base t K.E.z)=
      (E (Jacobian.tablePt K a).x,E (Jacobian.tablePt K a).y,E (Jacobian.tablePt K a).z) := by
    rw [vt,bt _ (by simp),bt _ (by simp),bt _ (by simp)]
  have kc : ∀ x∈[5400,5432],tmv C K.M.n base t x=tmv C K.M.n base b x := by
    intro x hx
    exact tmv_keep hL kt ib.scr.nowrap de (dc x hx) (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl <;> decide)
  have vz : tmv C K.M.n base t K.E.z=E (Jacobian.tablePt K a).z := congrArg (fun z => z.2.2) vals
  refine ⟨(kb.mono (by simp [entryWrites])).trans (kt.mono (by simp [entryWrites])),it,?_,?_,?_⟩
  · simp only [Prod.mk.injEq] at vals
    rw [vals.1,vals.2.1,vals.2.2]; exact hJ
  · rw [kc _ (by simp),b2,hz2,vz]
  · rw [kc _ (by simp),b3,hz3,vz]

theorem entryLoadFields_ok {base : Addr} {size a : Nat} {C : Curve} {Sl : Nat → Prop}
    (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hsize : 6512≤size)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hi : Inv K.M base size C.p Sl V E s)
    (h2 : s.gpr .x2=BitVec.ofNat 64 a) (ha : 1≤a) (ha8 : a≤8)
    (hD : ∀ x∈entryWrites,Sl x)
    (hT : ∀ x∈[(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z,
      6000+64*(a-1),6032+64*(a-1)],x∈V)
    :
    WP isa (.block (CachedJac.load++Jacobian.publicEntry K)) s fun t =>
      ProgKeep K.M base entryWrites s t ∧
      Inv K.M base size C.p Sl (entryLive V) (tmv C K.M.n base t) t ∧
      (tmv C K.M.n base t K.E.x,tmv C K.M.n base t K.E.y,tmv C K.M.n base t K.E.z)=
        (E (Jacobian.tablePt K a).x,E (Jacobian.tablePt K a).y,E (Jacobian.tablePt K a).z) ∧
      tmv C K.M.n base t 5400=E (6000+64*(a-1)) ∧
      tmv C K.M.n base t 5432=E (6032+64*(a-1)) := by
  have dc : ∀ x∈[5400,5432],Sl x := fun x hx => hD x (by
    simp only [entryWrites,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)
  have de : ∀ x∈[K.E.x,K.E.y,K.E.z],Sl x := fun x hx => hD x (by
    simp only [entryWrites,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)
  have st : ∀ x∈[(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z],x∈V :=
    fun x hx => hT x (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)
  rw [WP.block_append_iff]
  refine WP.mono (cachedLoadField_ok hL (by rfl) hi h2 ha ha8 hsize dc
    (fun x hx => hT x (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)))
    fun b ⟨kb,ib,b2,b3,bidx0⟩ => ?_
  have bt : ∀ x∈[(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z],
      tmv C K.M.n base b x=E x := by
    intro x hx
    rw [tmv_keep hL kb hi.scr.nowrap dc (hi.sl x (st x hx)) ?_]
    exact hi.val x (st x hx)
    simp only [Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    rw [not_or]
    have ht : K.tbl=2848 := rfl
    rw [ht] at hx
    omega_using [hx]
  have bidx : b.gpr .x2=BitVec.ofNat 64 a := bidx0.trans h2
  refine WP.mono (jacPublicFields_ok hL hAl (by rfl) (by rfl) (by rfl) ib bidx ha (by decide)
    de (fun x hx => List.mem_append_right _ (st x hx)) (Or.inl (by change 704+96≤2848+96*(a-1); omega_using [])))
    fun t ⟨kt,it,vt⟩ => ?_
  have vals : (tmv C K.M.n base t K.E.x,tmv C K.M.n base t K.E.y,tmv C K.M.n base t K.E.z)=
      (E (Jacobian.tablePt K a).x,E (Jacobian.tablePt K a).y,E (Jacobian.tablePt K a).z) := by
    rw [vt,bt _ (by simp),bt _ (by simp),bt _ (by simp)]
  have kc : ∀ x∈[5400,5432],tmv C K.M.n base t x=tmv C K.M.n base b x := by
    intro x hx
    exact tmv_keep hL kt ib.scr.nowrap de (dc x hx) (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl <;> decide)
  exact ⟨(kb.mono (by simp [entryWrites])).trans (kt.mono (by simp [entryWrites])),it,
    vals,(kc _ (by simp)).trans b2,(kc _ (by simp)).trans b3⟩

end VG.Proof.Weierstrass.AArch64.CachedField

end

end

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

abbrev cfg := VG.Impl.Ecdsa.Verify.AArch64.P256Joint.cfg

theorem cfg_K : cfg.K=K := rfl

theorem entry_work : ∀ x∈entryWrites,x∈jointWork cfg := by decide +kernel
theorem entry_slots : ∀ x∈entryWrites,x∈jointSlots cfg := by decide +kernel

theorem entrySources_live {a : Nat} (ha : 1≤a) (ha8 : a≤8) : ∀ x∈[(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z,
      6000+64*(a-1),6032+64*(a-1)],x∈jointLive cfg := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · apply List.mem_append_left; apply List.mem_append_right
      exact List.mem_map.mpr ⟨3*(a-1),List.mem_range.mpr (by omega),by simp only [Jacobian.tablePt,cfg_K]; omega_using []⟩
    · apply List.mem_append_left; apply List.mem_append_right
      exact List.mem_map.mpr ⟨3*(a-1)+1,List.mem_range.mpr (by omega_using [ha8]),by simp only [Jacobian.tablePt,cfg_K]; omega_using []⟩
    · apply List.mem_append_left; apply List.mem_append_right
      exact List.mem_map.mpr ⟨3*(a-1)+2,List.mem_range.mpr (by omega_using [ha8]),by simp only [Jacobian.tablePt,cfg_K]; omega_using []⟩
    · apply List.mem_append_right
      exact List.mem_map.mpr ⟨2*(a-1),List.mem_range.mpr (by omega_using [ha8]),by omega_using []⟩
    · apply List.mem_append_right
      exact List.mem_map.mpr ⟨2*(a-1)+1,List.mem_range.mpr (by omega_using [ha8]),by omega_using []⟩

def EntryPost (C : Curve) (base : Addr) (size : Nat) (P : Point C)
    (V : List Nat) (s t : State) : Prop :=
  ProgKeep K.M base entryWrites s t ∧
  Inv K.M base size C.p (·∈jointSlots cfg) (entryLive V) (tmv C K.M.n base t) t ∧
  InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y) (tmv C K.M.n base t K.E.z) P ∧
  tmv C K.M.n base t 5400=tmv C K.M.n base t K.E.z*tmv C K.M.n base t K.E.z ∧
  tmv C K.M.n base t 5432=tmv C K.M.n base t K.E.z*(tmv C K.M.n base t K.E.z*tmv C K.M.n base t K.E.z)

theorem entry_ok {C : Curve} {base : Addr} {size u v j : Nat}
    (hL : JointLayout cfg size) (hsize : 6512≤size)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hj : j<257)
    (hmag : 1≤nafMagnitude (FastNaf.byte 5 v j)) (hmag15 : nafMagnitude (FastNaf.byte 5 v j)≤15)
    (hodd : nafMagnitude (FastNaf.byte 5 v j)%2=1)
    {Q : Point C} {s : State}
    (hi : Inv K.M base size C.p (·∈jointSlots cfg) (jointLive cfg) (tmv C K.M.n base s) s)
    (hs : JointStable cfg C base Q u v s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) (h2 : s.gpr .x2=(FastNaf.byte 5 v j).setWidth 64) :
    WP isa (CachedJac.entry K) s
      (EntryPost C base size (if nafNegative (FastNaf.byte 5 v j) then
        negPt (mul (nafMagnitude (FastNaf.byte 5 v j)) Q) else mul (nafMagnitude (FastNaf.byte 5 v j)) Q)
        (jointLive cfg) s) := by
  let a := (nafMagnitude (FastNaf.byte 5 v j)+1)/2
  have ha : 1≤a := by dsimp [a]; omega_using [hmag]
  have ha8 : a≤8 := by dsimp [a]; omega_using [hmag15]
  have he : 2*a-1=nafMagnitude (FastNaf.byte 5 v j) := by dsimp [a]; omega_using [hodd]
  have ht := entrySources_live ha ha8
  rw [CachedJac.entry]
  apply WP.seq
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (nafIndex_ok h2) fun b ⟨b2,kb⟩ => ?_
  have eb : tmv C K.M.n base b=tmv C K.M.n base s := by funext x; unfold tmv; rw [kb.mem]
  have ib := hi.of_keeps kb (by decide)
  rw [←eb] at ib
  have sb := hs.of_mem kb.mem
  have kb' : ProgKeep K.M base entryWrites s b := keeps_prog kb (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [clob])
  have cb2 : tmv C K.M.n base b (6000+64*(a-1))=
      tmv C K.M.n base b (Jacobian.tablePt K a).z*tmv C K.M.n base b (Jacobian.tablePt K a).z := by
    simpa only [cfg_K,VG.Impl.Weierstrass.CachedJac.tableZ2,Nat.sub_add_cancel ha] using sb.cache2 (a-1) (by omega_using [ha8])
  have cb3 : tmv C K.M.n base b (6032+64*(a-1))=
      tmv C K.M.n base b (Jacobian.tablePt K a).z*(tmv C K.M.n base b (Jacobian.tablePt K a).z*tmv C K.M.n base b (Jacobian.tablePt K a).z) := by
    have h := sb.cache3 (a-1) (by omega_using [ha8])
    simp only [cfg_K,VG.Impl.Weierstrass.CachedJac.tableZ2,VG.Impl.Weierstrass.CachedJac.tableZ3,Nat.sub_add_cancel ha] at h
    rw [h,cb2]; grind
  refine WP.mono (entryLoad_ok hL.lay hL.aligned hsize ib b2 ha ha8 entry_slots ht cb2 cb3
    (sb.peer.table a ha ha8)) fun d ⟨kd,id,jd,d2,d3⟩ => ?_
  rw [he] at jd
  have kp := kb'.trans kd
  have sd := hs.keep (kp.mono entry_work) (fun r hr => by
    have := hL.stableBounds r hr; have := hi.scr.nowrap; omega_arith) hL.stableSep
  have d19 : d.gpr .x19=BitVec.ofNat 64 j := by
    rw [kp.gpr _ (by decide),h19]
  apply WP.seq
  refine WP.mono (nafSignRead_ok id.scr (by decide) (by change 1824+j<size; omega_using [hsize, hj]) d19
    (sd.peer.bits j hj)) fun e ⟨e3,ke⟩ => ?_
  have ee : tmv C K.M.n base e=tmv C K.M.n base d := by funext x; unfold tmv; rw [ke.mem]
  have ie := id.of_keeps ke (by decide)
  rw [←ee] at ie jd d2 d3
  have se := sd.of_mem ke.mem
  have kpe : ProgKeep K.M base entryWrites s e := kp.trans (keeps_prog ke (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp [clob]))
  refine WP.ite (nafNegative (FastNaf.byte 5 v j)) (by
    change some (e.read .x .x3 != 0)=some _
    rw [read_x,e3]; cases nafNegative (FastNaf.byte 5 v j) <;> decide) (fun hn => ?_) (fun hn => ?_)
  · have hz : tmv C K.M.n base e K.zero=0 := by
      have hz := se.peer.zero
      rw [cfg_K] at hz
      unfold tmv; rw [hz,toM_zero]
    have ev : ∀ x∈[K.E.x,K.E.y,K.E.z,K.zero],x∈entryLive (jointLive cfg) := by decide +kernel
    refine WP.mono (nafNeg_ok (K:=K) hL.lay hL.aligned hm ie ev (by decide) (by decide) hz jd)
      fun t ⟨kt,it,jt⟩ => ?_
    have vy := it.val
    have same (x : Nat) (hx : x∈entryLive (jointLive cfg)) (hn : x≠K.E.y) :
        tmv C K.M.n base t x=tmv C K.M.n base e x := by
      exact (vy x hx).trans (Function.update_of_ne hn _ _)
    refine ⟨kpe.trans (kt.mono (by simp [entryWrites])),it.to_tmv,?_,?_,?_⟩
    · rw [hn]; exact it.point_tmv (fun x hx => by
        simp only [entryLive,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind) jt
    · rw [same 5400 (by decide) (by decide),same K.E.z (by decide) (by decide)]; exact d2
    · rw [same 5432 (by decide) (by decide),same K.E.z (by decide) (by decide)]; exact d3
  · apply WP.block_nil
    refine ⟨kpe,ie,?_,d2,d3⟩
    rw [hn]; exact jd

end VG.Proof.Weierstrass.AArch64.CachedField

end

end

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem magnitude_byte (v j : Nat) : nafMagnitude (FastNaf.byte 5 v j)=FastNaf.magnitude 5 v j :=
  FastNaf.byte_magnitude 5 v j

theorem negative_byte (v j : Nat) : nafNegative (FastNaf.byte 5 v j)=FastNaf.negative 5 v j :=
  FastNaf.byte_negative 5 v j

/-- Stable external generator data is framed by work writes and unchanged symbols. -/
def ExternalFrame (base : Addr) (External : State → Prop) : Prop :=
  ∀ {s t},ProgKeep K.M base (jointWork cfg) s t → t.syms=s.syms → External s → External t

theorem entry_core_ok {C : Curve} {base : Addr} {size u v j : Nat}
    (hL : JointLayout cfg size) (hsize : 6512≤size)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hj : j<257)
    (hmag : 1≤nafMagnitude (FastNaf.byte 5 v j)) (hmag15 : nafMagnitude (FastNaf.byte 5 v j)≤15)
    (hodd : nafMagnitude (FastNaf.byte 5 v j)%2=1)
    {Q A : Point C} {External : State → Prop} (hExt : ExternalFrame base External) {s : State}
    (h : JointCore cfg C base size Q u v External A s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) (h2 : s.gpr .x2=(FastNaf.byte 5 v j).setWidth 64) :
    WP isa (CachedJac.entry K) s fun t =>
      EntryPost C base size (FastNaf.point C Q 5 v j) (jointLive cfg) s t ∧
      JointCore cfg C base size Q u v External A t := by
  refine WP.mono_syms (entry_ok hL hsize hm hj hmag hmag15 hodd h.field h.stable h19 h2)
    fun t hp sy => ?_
  have pointEq : (if nafNegative (FastNaf.byte 5 v j) then negPt (mul (nafMagnitude (FastNaf.byte 5 v j)) Q)
      else mul (nafMagnitude (FastNaf.byte 5 v j)) Q)=FastNaf.point C Q 5 v j := by
    rw [negative_byte v j,magnitude_byte v j]; rfl
  rw [pointEq] at hp
  refine ⟨hp,h.of_write (E:=tmv C K.M.n base t) hL hp.1 entry_work entry_slots (by decide +kernel) ?_
    (hExt (hp.1.mono entry_work) sy h.external)⟩
  exact hp.2.1.sub (fun _ hx => List.mem_append_right _ (List.mem_append_right _ hx))

end VG.Proof.Weierstrass.AArch64.CachedField

end

end

/-! Digit selection remains unchanged while point arithmetic uses a wider frame.
The callbacks include the final coordinate copy, so no intermediate scratch
or register agreement is imposed beyond what the next point operation reads.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

private theorem byteTest : ∀ b : BitVec 8,(b.setWidth 64 != 0)=decide (nafMagnitude b≠0) := by decide +kernel

theorem allocatedCachedDigit_ok {C : Curve} {base : Addr} {size u v j : Nat}
    (hL : JointLayout cfg size) (hsize : 8192≤size)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C)
    {rs : List Reg} {W : List (Nat × Nat)} {code : CachedJac.Ops}
    (hregs : ∀ r∈clob K.M.n,r∈rs)
    (hcover : ∀ w∈(jointWork cfg).map (·,8*K.M.n)++[(K.M.tmp,8*K.M.n)],
      ∃ w'∈W,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2)
    (hj : j<257) {Q A : Point C} (hQ : onCurve C Q=true) (hA : onCurve C A=true)
    {External : State → Prop} (hExt : ExternalFrame base External) {s : State}
    (hsum : ∀ {A B : Point C} {s : State},onCurve C A=true → onCurve C B=true →
      JointCore cfg C base size Q u v External A s →
      Inv K.M base size C.p (·∈jointSlots cfg) (entryLive (jointLive cfg)) (tmv C K.M.n base s) s →
      InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) B →
      tmv C K.M.n base s 5400=tmv C K.M.n base s K.E.z*tmv C K.M.n base s K.E.z →
      tmv C K.M.n base s 5432=tmv C K.M.n base s K.E.z*(tmv C K.M.n base s K.E.z*tmv C K.M.n base s K.E.z) →
      WP isa (.seq (CachedJac.add K code) (.block (copyPt 4 K.R K.D))) s fun t =>
        AllocatedFrame rs base W s t ∧ JointCore cfg C base size Q u v External (add A B) t)
    (h : JointCore cfg C base size Q u v External A s) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (CachedJac.digit K code) s fun t =>
      AllocatedFrame rs base W s t ∧
      JointCore cfg C base size Q u v External (add A (FastNaf.point C Q 5 v j)) t := by
  rw [CachedJac.digit]
  apply WP.seq
  refine WP.mono_syms (nafRead_ok h.field.scr (by decide) (by change 1824+j<size; omega_using [hsize, hj]) h19
    (h.stable.peer.bits j hj) .x2) fun b ⟨b2,kb⟩ sy => ?_
  have kp : ProgKeep K.M base (jointWork cfg) s b := keeps_prog kb (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp [clob])
  have cb := h.of_keeps kb (by decide) (hExt kp sy h.external)
  have b19 : b.gpr .x19=BitVec.ofNat 64 j := (kb.gpr _ (by decide)).trans h19
  refine WP.ite (decide (FastNaf.magnitude 5 v j≠0)) (by
    change some (b.read .x .x2 != 0)=_
    rw [read_x,b2,byteTest,magnitude_byte]) (fun hn => ?_) (fun hz => ?_)
  · have hm0 : FastNaf.magnitude 5 v j≠0 := of_decide_eq_true hn
    apply WP.seq
    refine WP.mono (entry_core_ok hL (by omega_using [hsize]) hm hj
      (by rw [magnitude_byte]; omega_using [hm0])
      (by rw [magnitude_byte]; exact FastNaf.magnitude_le (Or.inl rfl) v j)
      (by rw [magnitude_byte]; exact (FastNaf.magnitude_odd_or_zero 5 v j).resolve_left hm0)
      hExt cb b19 b2) fun d ⟨⟨kd,id,jd,d2,d3⟩,cd⟩ => ?_
    exact WP.mono (hsum hA (FastNaf.onCurve_point hC hQ 5 v j) cd id jd d2 d3)
      fun t ⟨kt,ct⟩ => ⟨(AllocatedFrame.of_prog (kp.trans (kd.mono entry_work)) hregs hcover).trans kt,ct⟩
  · have hm0 : FastNaf.magnitude 5 v j=0 := by simpa only [ne_eq,not_not] using of_decide_eq_false hz
    have hp : FastNaf.point C Q 5 v j=.infinity := by
      unfold FastNaf.point
      rw [hm0,Spec.Weierstrass.mul]
      cases FastNaf.negative 5 v j <;> rfl
    have he : add A (FastNaf.point C Q 5 v j)=A := by rw [hp]; cases A <;> rfl
    apply WP.block_nil
    exact ⟨AllocatedFrame.of_prog kp hregs hcover,he.symm ▸ cb⟩

end VG.Proof.Weierstrass.AArch64.CachedField

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

local macro "jslots" : tactic => `(tactic| plain_simp_names (simp only [jointSlots,jointLive,jointWork,
                   jacWinSlots,nafLive,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind))

theorem allocatedJointFixedDigit_ok
    {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v j : Nat}
    {G Q A : Point C} {s : State} (hL : JointFixedLayout c size)
    (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C)
    {rs : List Reg} {W : List (Nat × Nat)} {mixed : Prog isa}
    (hregs : ∀ r∈clob c.K.M.n,r∈rs)
    (hcover : ∀ w∈(jointWork c).map (·,8*c.K.M.n)++[(c.K.M.tmp,8*c.K.M.n)],
      ∃ w'∈W,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2)
    (hG : onCurve C G=true) (hA : onCurve C A=true)
    (hsum : ∀ {A B : Point C} {s : State},onCurve C A=true → onCurve C B=true →
      JointCore c C base size Q u v (JointGenerator c C base size G T) A s →
      Inv c.K.M base size C.p (·∈jointSlots c) ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c)
        (tmv C c.K.M.n base s) s →
      InvJ C (tmv C c.K.M.n base s c.K.E.x) (tmv C c.K.M.n base s c.K.E.y)
        (tmv C c.K.M.n base s c.K.E.z) B → tmv C c.K.M.n base s c.K.E.z=1 →
      WP isa (.seq mixed (.block (copyPt 4 c.K.R c.K.D))) s fun t =>
        AllocatedFrame rs base W s t ∧
        JointCore c C base size Q u v (JointGenerator c C base size G T) (add A B) t)
    (h : JointCore c C base size Q u v (JointGenerator c C base size G T) A s)
    (hj : j<257) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (Joint.fixedDigit c mixed) s fun t =>
      AllocatedFrame rs base W s t ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T)
        (add A (FastNaf.point C G c.gw u j)) t := by
  have hgl := hL.layout.stableBounds (c.gBits,jointGLen c) (by simp [jointStableRanges])
  have wsl : ∀ x∈jointWork c,x∈jointSlots c := by intro x hx; jslots
  have workBound : ∀ x∈jointWork c,x+8*c.K.M.n≤size := fun x hx => hL.layout.lay.le x (wsl x hx)
  rw [Joint.fixedDigit]
  apply WP.seq
  refine WP.mono_syms (jointFixedRead_ok h.field.scr hL.gBits hj hgl h19
    h.stable.generator) fun a ⟨a2,_,a3,ka⟩ sa => ?_
  have kp : ProgKeep c.K.M base (jointWork c) s a := keeps_prog ka (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [clob])
  have ea := h.external.keep kp sa workBound h.field.mod.tmp
  have ca := h.of_keeps ka (by decide) ea
  have a19 := (ka.gpr .x19 (by decide)).trans h19
  refine WP.ite (decide (FastNaf.magnitude c.gw u j≠0)) (by
    change some (a.read .x .x2 != 0)=_
    rw [read_x,a2]
    congr 1
    have hz := jointGCell_zero_iff hL.layout.gw u j
    by_cases h0 : FastNaf.magnitude c.gw u j=0
    · rw [hz.mpr h0,h0]; rfl
    · rw [bne_iff_ne.mpr (fun he => h0 (hz.mp he)),decide_eq_true h0])
    (fun hn => ?_) (fun hz => ?_)
  · apply WP.seq
    refine WP.mono (jointEntry_generator_ok hL hm ca hj a2 a3 a19 (of_decide_eq_true hn))
      fun b ⟨kb,cb,ib,jb,zb⟩ => ?_
    exact WP.mono (hsum hA (FastNaf.onCurve_point hC hG c.gw u j) cb ib jb zb)
      fun t ⟨kt,ct⟩ => ⟨(AllocatedFrame.of_prog (kp.trans kb) hregs hcover).trans kt,ct⟩
  · have hm0 : FastNaf.magnitude c.gw u j=0 := by simpa only [ne_eq,not_not] using of_decide_eq_false hz
    have hp : FastNaf.point C G c.gw u j=.infinity := by
      rw [FastNaf.point,hm0]
      have h0 : mul 0 G=.infinity := by rw [Spec.Weierstrass.mul]; rfl
      rw [h0]; split <;> rfl
    apply WP.block_nil
    rw [hp,add_infinity]
    exact ⟨AllocatedFrame.of_prog kp hregs hcover,ca⟩

end VG.Proof.Weierstrass.AArch64
