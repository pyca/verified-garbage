module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64.Joint
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDoubler
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepFields
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTail
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointMul
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointInput
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFinal
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitLayout
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGenerator
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombLay
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.JacAdd
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Scalars

/-! ### `Ecdsa.Verify.X86_64.JointGenerator`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.X86_64.JointGeneratorTable`, which only this module used -/

section

/-! A comb table's first row (`[m]G` for `m ≤ 2^(w-1)`) supplies the joint generator row directly. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

def combGeneratorRow (n : Nat) {C : Curve} {w J H : Nat} {tbl : List (List (Nat×Nat))}
    {start : Nat×Nat} (hm : UnitMod C.p (2^(64*n))) (hC : Law C) (hT : CombOkW C w J tbl start)
    (hJ : 0<J) (hH : H<2^(w-1)) : JointGeneratorRow n C (G C) H where
  x a := (combAt tbl 0 (a-1)).1*2^(64*n)%C.p
  y a := (combAt tbl 0 (a-1)).2*2^(64*n)%C.p
  canonical _ _ _ _ := ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p)),
    Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p))⟩
  point a ha hb _ := by
    rw [toM_mont hm,toM_mont hm]
    have hp := hT.entry 0 hJ (a-1) (by omega_using [hH, hb])
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.mul_one,Nat.sub_add_cancel ha] at hp
    rw [hp]
    exact InvJ.affine hC _ _

theorem wordsVal_addr (mem : Mem) (base : Addr) (d o n : Nat) :
    wordsVal mem (off base d) o n=wordsVal mem base (d+o) n := by
  apply wordsVal_congr₂
  intro i _
  simp only [Mont.word,off,Offset.add_add,Nat.add_assoc]

theorem combGenerator_coordinates {n : Nat} {C : Curve} {w J a : Nat} {tbl : List (List (Nat×Nat))}
    {start : Nat×Nat}
    (hp : C.p<2^(64*n)) (hT : CombOkW C w J tbl start) (hJ : 0<J)
    {s : State} {T : Addr} (ht : TblMem s T (tcombWords n (2^(64*n)) C.p tbl))
    (ha : 1≤a) (hb : a<2^(w-1)+1) :
    wordsVal s.mem (off T (16*n*(a-1))) 0 n=(combAt tbl 0 (a-1)).1*2^(64*n)%C.p ∧
    wordsVal s.mem (off T (16*n*(a-1))) (8*n) n=(combAt tbl 0 (a-1)).2*2^(64*n)%C.p := by
  have he := tbl_entry (n:=n) (R:=2^(64*n)) (p:=C.p) (H:=2^(w-1)) (J:=J)
    ht hT.len hT.lenH (j:=0) (m:=a-1) hJ (by omega_using [ha, hb])
    (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p))) hp)
    (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p))) hp)
  rw [wordsVal_addr,wordsVal_addr,Nat.add_zero]
  simpa only [Nat.zero_mul,BitVec.add_zero] using he

theorem jointGenerator_of_table {c : Joint.Cfg} {C : Curve} {J size : Nat}
    {tbl : List (List (Nat×Nat))} {start : Nat×Nat}
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hC : Law C) (hp : C.p<2^(64*c.K.M.n))
    {w H : Nat} (hT : CombOkW C w J tbl start) (hJ : 0<J) (hH : H<2^(w-1))
    {s : State} {T base : Addr} (ht : TblMem s T (tcombWords c.K.M.n (2^(64*c.K.M.n)) C.p tbl))
    (hout : ∀ i<(tcombWords c.K.M.n (2^(64*c.K.M.n)) C.p tbl).length,∀ b<8,
      size≤ofs base (T+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b))
    (hsym : s.syms c.tsym=T) :
    JointGenerator c C base T size (combGeneratorRow c.K.M.n hm hC hT hJ hH) s := by
  have hlen : (tcombWords c.K.M.n (2^(64*c.K.M.n)) C.p tbl).length=J*(2^(w-1)*(2*c.K.M.n)) :=
    tcombWords_length (n:=c.K.M.n) (R:=2^(64*c.K.M.n)) (p:=C.p) hT.len hT.lenH
  have hlen' : 2^(w-1)*(2*c.K.M.n)≤(tcombWords c.K.M.n (2^(64*c.K.M.n)) C.p tbl).length := by
    rw [hlen]
    exact Nat.le_mul_of_pos_left _ hJ
  intro a ha hb _
  have coords := combGenerator_coordinates hp hT hJ ht ha (by omega_using [hH, hb])
  have hk : 16*c.K.M.n*(a-1)=16*(c.K.M.n*(a-1)) := Nat.mul_assoc ..
  have hka : c.K.M.n*(a-1)+c.K.M.n≤c.K.M.n*2^(w-1) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega_using [hH, hb])
  have hl2 : 2^(w-1)*(2*c.K.M.n)=2*(c.K.M.n*2^(w-1)) := by
    rw [Nat.mul_comm (2^(w-1)),Nat.mul_assoc,Nat.mul_comm c.K.M.n]
  refine ⟨hsym,?_,?_,coords.1,coords.2⟩
  · intro i hi
    simp only [off,Offset.add_add]
    obtain ⟨r,hr,hreg⟩ := ht.rd
    exact ⟨r,hr,Region.contains_off hreg (by omega_using [hlen', hk, hka, hl2, hi])⟩
  · intro i hi b hb'
    have ho := hout (2*(c.K.M.n*(a-1))+2*i+b/8) (by omega_using [hlen', hka, hl2, hi, hb']) (b%8) (by omega_using [])
    simp only [off,Offset.add_add] at ho ⊢
    have he : 16*c.K.M.n*(a-1)+16*i+b=8*(2*(c.K.M.n*(a-1))+2*i+b/8)+b%8 := by omega_using [hk]
    rw [he]
    exact ho

end VG.Proof.Weierstrass.X86_64

end

end


/-! Reuse the verifier contract's existing width-seven comb table and certificate. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)

/-- The joint loop's table of `[m]G`: `d`, one of the curve's tables of
constants, of `J` rows, whose first row holds `[m]G` for `m = 1 … 2^(d.w-1)`,
past the largest magnitude of the generator's digits: the comb's, or the
verifier's own (`Cfg.gtab`). -/
structure JointGTable (c : Cfg) (j : Joint.Cfg) (d : CombData) (J : Nat) : Prop where
  mem : (d.tsym,c.combWords d)∈c.combConsts
  ok : CombOkW c.C d.w J d.tbl d.start
  pos : 0<J
  top : jointGTop j<2^(d.w-1)
  sym : j.tsym=d.tsym

theorem JointGTable.ofComb {c : Cfg} {j : Joint.Cfg} {d : CombData} {J : Nat}
    (hcd : c.comb=some d) (hT : CombOkW c.C d.w J d.tbl d.start) (hJ : 0<J)
    (ht : jointGTop j<2^(d.w-1)) (hs : j.tsym=d.tsym) : JointGTable c j d J :=
  ⟨comb_mem_consts hcd,hT,hJ,ht,hs⟩

theorem JointGTable.ofGTab {c : Cfg} {j : Joint.Cfg} {d : CombData} {J : Nat}
    (hcd : c.gtab=some d) (hT : CombOkW c.C d.w J d.tbl d.start) (hJ : 0<J)
    (ht : jointGTop j<2^(d.w-1)) (hs : j.tsym=d.tsym) : JointGTable c j d J :=
  ⟨gtab_mem_consts hcd,hT,hJ,ht,hs⟩

def jointCombRow {c : Cfg} {j : Joint.Cfg} {d : CombData} {J : Nat} (hc : BaseCfgOk c) (hC : Law c.C)
    (hG : JointGTable c j d J) : JointGeneratorRow j.K.M.n c.C (G c.C) (jointGTop j) :=
  combGeneratorRow j.K.M.n (unitMod_pow_two hc.p_odd (64*j.K.M.n)) hC hG.ok hG.pos hG.top

theorem jointMid_generator {c : Cfg} {j : Joint.Cfg} {d : CombData} {J : Nat}
    (hc : BaseCfgOk c) (hC : Law c.C) (hG : JointGTable c j d J)
    (hK : j.K=c.winCfg PX PY BP)
    {s₀ s : State} {g : Reg → BitVec 64} (hp : VPre c s₀) (h : Mid c s₀ (s₀.gpr .rcx) g s) :
    JointGenerator j c.C (s₀.gpr .rcx) (s₀.syms d.tsym) size
      (jointCombRow (j:=j) hc hC hG) s := by
  have hjn : j.K.M.n=c.n := by rw [hK]; rfl
  have table := tbl_of_held_mem hG.mem hp.tbls (by rw [hp.wr]; simp)
    (s:=s) (fun r hr => by rw [h.rd,hp.rd]; simp [hr]) h.unch
  have ws : c.combWords d=tcombWords j.K.M.n (2^(64*j.K.M.n)) c.C.p d.tbl := by
    simp only [Cfg.combWords,Cfg.R,hjn]
  have hpn : c.C.p<2^(64*j.K.M.n) := by rw [hjn]; exact hc.p_lt
  unfold jointCombRow
  apply jointGenerator_of_table (unitMod_pow_two hc.p_odd (64*j.K.M.n)) hC hpn
  · rw [←ws]
    exact table.1
  · rw [←ws]
    exact table.2
  · rw [hG.sym,h.syms]

end VG.Proof.Ecdsa.Verify.X86_64

end

end

/-! ### `Ecdsa.Verify.X86_64.JointFrame`, which this module and modules that import it used -/

section

/-! The joint multiplication preserves the fixed inputs of the final comparison. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)

def jointRanges (j : Joint.Cfg) : List (Nat×Nat) :=
  jointPrepRanges j++((jointInitWork j++jointWork j).map (·,8*j.K.M.n)++[(j.K.M.tmp,8*j.K.M.n)])

/-- The ranges `W` of the working space, which a joint multiplication writes, miss the fixed inputs of
the final comparison. -/
structure FrameLayout (c : Cfg) (W : List (Nat×Nat)) : Prop where
  fixed : FixedOk c W
  k : ∀ w∈W,c.sl K+8*c.n≤w.1 ∨ w.1+w.2≤c.sl K
  flag : ∀ w∈W,c.sl FLAG+8≤w.1 ∨ w.1+w.2≤c.sl FLAG

abbrev JointFrameLayout (c : Cfg) (j : Joint.Cfg) : Prop := FrameLayout c (jointRanges j)

theorem frame_input {c : Cfg} {j : Joint.Cfg} (hc : BaseCfgOk c)
    (hK : j.K=c.winCfg PX PY BP) {W : List (Nat×Nat)} (hF : FrameLayout c W)
    {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64} (h : Mid c s₀ base g s)
    {Q A : Point c.C} {u v : Nat} {External : State → Prop}
    (ht : JointCore j c.C base size Q u v External A t)
    (hu : Unch base W s.mem t.mem) : ProjectiveInput c s₀ base g t := by
  have rx := ht.field.lt j.K.R.x (jointLive_R j _ (by simp [jacCoords]))
  have rz := ht.field.lt j.K.R.z (jointLive_R j _ (by simp [jacCoords]))
  rw [hK] at rx rz
  refine ⟨ht.field.scr,h.fixed.unch hc.n10 h.scr.nowrap hF.fixed hu,
    (sv_unch hu hc.n10 h.scr.nowrap (by decide) hF.k).trans h.k,?_,rx,rz⟩
  refine (hu.word hF.flag ?_).trans h.flag
  have := sl_le c hc.n10 (i:=FLAG) (by decide)
  have := hc.n0
  have := h.scr.nowrap
  omega_arith

theorem jointFrame_input {c : Cfg} {j : Joint.Cfg} (hc : BaseCfgOk c)
    (hK : j.K=c.winCfg PX PY BP) (hF : JointFrameLayout c j)
    {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64} (h : Mid c s₀ base g s)
    {Q A : Point c.C} {u v : Nat} {External : State → Prop}
    (ht : JointCore j c.C base size Q u v External A t)
    (hu : Unch base (jointRanges j) s.mem t.mem) : ProjectiveInput c s₀ base g t :=
  frame_input hc hK hF h ht hu

end VG.Proof.Ecdsa.Verify.X86_64

end

end

/-! End-to-end correctness of public Jacobian joint verification. -/

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/X86_64/JointPoints.lean`, which only this module imported.
section

/-! The joint multiplication consumes the verifier's actual scalars and preserves its final inputs. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)
open VG.Impl.Ecdsa.Verify.X86_64 (U V)

structure JointPointsPost (c : Cfg) (s₀ sM : State) (g : Reg → BitVec 64) (Q : Point c.C) (t : State) : Prop where
  input : ProjectiveInput c s₀ (s₀.gpr .rcx) g t
  point : InvJ c.C (tmv c.C c.n (s₀.gpr .rcx) t (c.sl RX))
    (tmv c.C c.n (s₀.gpr .rcx) t (c.sl RY)) (tmv c.C c.n (s₀.gpr .rcx) t (c.sl RZ))
    (add (mul (sv c (s₀.gpr .rcx) sM U) (G c.C)) (mul (sv c (s₀.gpr .rcx) sM V) Q))

theorem jointPoints_ok {c : Cfg} {j : Joint.Cfg} {d : CombData} {double : Prog isa}
    (hc : BaseCfgOk c) (hC : Law c.C) {J : Nat} (hG : JointGTable c j d J)
    (hK : j.K=c.winCfg PX PY BP) (hd : JDblOk c.C j.dbl) (hnp : c.C.n≤c.C.p)
    (hL : JointAddLayout j size) (hInit : JointInitLayout j size)
    (hPrep : JointPrepLayout j size (c.sl U) (c.sl V)) (hFrame : JointFrameLayout c j)
    (hD : JointDoubler j c.C size double) (hZ : j.coZ=true → PrimeOrder c.C ∧ 17≤c.C.n ∧ AM3 c.C)
    {s₀ s : State} {g : Reg → BitVec 64} (hp : VPre c s₀) (h : Mid c s₀ (s₀.gpr .rcx) g s)
    {Q : Point c.C} (hQ : onCurve c.C Q=true)
    (hq : Rep c.C (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PX))
      (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PY)) (tmv c.C c.n (s₀.gpr .rcx) s (c.sl ONEP)) Q) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointPoints c j double).inline s (JointPointsPost c s₀ s g Q) := by
  have field := jointMid_field hc hK hnp h
  have point := jointMid_point hc hC hK h hq
  have zero := jointMid_zero hK h
  have generator := jointMid_generator hc hC hG hK hp h
  have hjn : j.K.M.n=c.n := by rw [hK]; rfl
  have hm : UnitMod c.C.p (2^(64*j.K.M.n)) := unitMod_pow_two hc.p_odd _
  have hone : j.K.one<c.C.p := by
    rw [hK]
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne c.C.p))
  have honeval : toM c.C.p (2^(64*j.K.M.n)) j.K.one=1 := by
    rw [hK]
    change toM c.C.p (2^(64*c.n)) (c.mont 1)=1
    simp only [Cfg.mont,Cfg.R,Nat.one_mul]
    exact toM_one (unitMod_pow_two hc.p_odd _)
  have nlt : c.C.n<2^(64*j.K.M.n) := by rw [hjn]; exact hc.n_lt
  have sv4 (i : Nat) : wordsVal s.mem (s₀.gpr .rcx) (c.sl i) j.K.M.n=sv c (s₀.gpr .rcx) s i := by
    unfold sv
    rw [hjn]
  refine WP.mono (jointMul_ok hL hInit hPrep hm hC hd hD hone honeval hc.onG hQ
    point (jointMid_affine hc hK h) zero hZ (Nat.lt_trans h.u_lt nlt) (Nat.lt_trans h.v_lt nlt) field generator (sv4 U) (sv4 V))
    fun t ⟨ct,_,_,_,ut⟩ => ?_
  refine ⟨jointFrame_input hc hK hFrame h ct ut,?_⟩
  have pt := ct.point
  rw [hK] at pt
  exact pt

end VG.Proof.Ecdsa.Verify.X86_64
end

end

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY)

/-- Joint verification inlined: only the points and the tail call functions. -/
theorem jointVerifyWith_inline (c : Cfg) (pts : Prog isa) :
    (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerifyWith c pts).inline =
    .seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.args c)) (.seq (Impl.Ecdh.X86_64.Cfg.prefix' c (some D))
      (.seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.loadS c)) (.seq (.block (Impl.Ecdh.X86_64.Cfg.peer c))
      (.seq (Impl.Ecdh.X86_64.Cfg.check c).inline (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.scalars c).inline
      (.seq c.nPow.inline (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.uv c).inline
      (.seq pts.inline (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail c).inline)))))))) := by
  show Code.seq _ (Code.seq _ (Code.seq _ (Code.seq _ (Code.seq (Impl.Ecdh.X86_64.Cfg.check c).inline
    (Code.seq (Impl.Ecdsa.Verify.X86_64.Cfg.scalars c).inline (Code.seq c.nPow.inline
    (Code.seq (Impl.Ecdsa.Verify.X86_64.Cfg.uv c).inline _))))))) = _
  rfl

theorem jointVerify_inline (c : Cfg) (j : Joint.Cfg) (double : Prog isa) :
    (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify c j double).inline =
    .seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.args c)) (.seq (Impl.Ecdh.X86_64.Cfg.prefix' c (some D))
      (.seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.loadS c)) (.seq (.block (Impl.Ecdh.X86_64.Cfg.peer c))
      (.seq (Impl.Ecdh.X86_64.Cfg.check c).inline (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.scalars c).inline
      (.seq c.nPow.inline (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.uv c).inline
      (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.jointPoints c j double).inline
        (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail c).inline)))))))) :=
  jointVerifyWith_inline c _

/-- Verification by the public joint method, from what the points' code `pts` leaves. -/
theorem jointVerifyWith_ok {c : Cfg} {pts : Prog isa}
    (hc : BaseCfgOk c) (hC : Law c.C)
    (hpub : c.pubVerify=true) (hnp : c.C.n<c.C.p) (hpn : c.C.p≤2*c.C.n)
    {s₀ : State} (hp : VPre c s₀)
    (hpoints : ∀ {s : State} {g : Reg → BitVec 64} (_h : Mid c s₀ (s₀.gpr .rcx) g s)
      {Q : Point c.C}, onCurve c.C Q=true →
      Rep c.C (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PX))
        (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PY)) (tmv c.C c.n (s₀.gpr .rcx) s (c.sl ONEP)) Q →
      WP isa pts.inline s (JointPointsPost c s₀ s g Q)) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerifyWith c pts).inline s₀ fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s₀.gpr r) ∧ VPost c s₀ t := by
  rw [jointVerifyWith_inline]
  refine front_ok hc hp fun g s₁ hg hF => mid_ok hc hF fun s₂ hM => ?_
  have one := (consts_tmv hc hM.fixed).2.2
  let Q := peerPt c (s₀.mem (s₀.gpr .rdi)=4) (keyX c s₀) (keyY c s₀)
  have hQ : onCurve c.C Q=true := peerPt_onCurve hc _ _ _
  have hRep : Rep c.C (tmv c.C c.n (s₀.gpr .rcx) s₂ (c.sl PX))
      (tmv c.C c.n (s₀.gpr .rcx) s₂ (c.sl PY)) (tmv c.C c.n (s₀.gpr .rcx) s₂ (c.sl ONEP)) Q := by
    rw [one]
    exact peerPt_rep hC _ _ _ hM.px hM.py
  apply WP.seq
  refine WP.mono (hpoints hM hQ hRep) fun s₃ hP => ?_
  refine WP.mono (jointTail_ok hc hC hpub hnp hpn hM hP.input hP.point) fun t ⟨saved,post⟩ => ?_
  exact ⟨fun r hr => (saved r hr).trans (hg r hr),post⟩

theorem jointVerify_ok {c : Cfg} {j : Joint.Cfg} {double : Prog isa}
    (hc : BaseCfgOk c) (hC : Law c.C)
    (hpub : c.pubVerify=true) (hnp : c.C.n<c.C.p) (hpn : c.C.p≤2*c.C.n)
    {s₀ : State} (hp : VPre c s₀)
    (hpoints : ∀ {s : State} {g : Reg → BitVec 64} (_h : Mid c s₀ (s₀.gpr .rcx) g s)
      {Q : Point c.C}, onCurve c.C Q=true →
      Rep c.C (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PX))
        (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PY)) (tmv c.C c.n (s₀.gpr .rcx) s (c.sl ONEP)) Q →
      WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointPoints c j double).inline s (JointPointsPost c s₀ s g Q)) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify c j double).inline s₀ fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s₀.gpr r) ∧ VPost c s₀ t :=
  jointVerifyWith_ok hc hC hpub hnp hpn hp hpoints

end VG.Proof.Ecdsa.Verify.X86_64
