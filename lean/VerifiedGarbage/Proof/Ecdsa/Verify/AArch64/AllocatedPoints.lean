module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFieldTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointInitTiming
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
public import VerifiedGarbage.Proof.P256.VerifyTable.Env
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedRaw
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
public import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
public import VerifiedGarbage.Proof.P256.Linear.WeakCertificate
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
public import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointGenerator
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointPrep
import VerifiedGarbage.Impl.Weierstrass.AArch64.ArithmeticTable
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Arithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
import VerifiedGarbage.Proof.Weierstrass.JacAdd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
meta import VerifiedGarbage.Proof.Framework.AArch64.Spill
meta import VerifiedGarbage.Proof.Mont.AArch64.Words
meta import VerifiedGarbage.Proof.Weierstrass.Unch
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
meta import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
meta import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
meta import VerifiedGarbage.Proof.Weierstrass.InverseContract
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut

/-! ### `Weierstrass.AArch64.JointFinish`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- A final canonical homogeneous representative, including infinity. -/
theorem jointFinish_ok {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v : Nat}
    {External : State → Prop}
    (hL : JacWinLay c.K size) (hJ : c.K.J=52) (hAl : Aligned c.K.M (· ∈ jacWinSlots c.K))
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hC : Law C) (hOne : c.K.one<C.p)
    (hone : toM C.p (2^(64*c.K.M.n)) c.K.one=1) (hBits : c.K.bits+5≤4096)
    {P A : Point C} {s : State} (h : JointCore c C base size P u v External A s) :
    WP isa (Jacobian.jacFinish c.K) s fun t =>
      KeepRegs (tcombClob c.K.M.n) s t ∧ Unch base (jacLoopWrites c.K) s.mem t.mem ∧
      ModOkA c.K.M size C.p t.mem base ∧
      (∀ x ∈ [c.K.R.x,c.K.R.y,c.K.R.z], wordsVal t.mem base x c.K.M.n<C.p) ∧
      Rep C (tmv C c.K.M.n base t c.K.R.x) (tmv C c.K.M.n base t c.K.R.y)
        (tmv C c.K.M.n base t c.K.R.z) A := by
  have lay := jacFinishLayout hL hJ hBits
  have al : CombA (jacFinishCfg c.K).toComb := ⟨fun x hx => hAl.sl x (by
    apply hL.old_slots x
    simp only [combSlots,jacFinishCfg,TCombCfg.toComb,winSlots,winRo,winOther,rcbW,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind),hAl.mod,fun _ _ h => nomatch (callOf_small (M := c.K.M) (Nat.le_of_eq hL.n)).symm.trans h⟩
  have pn := wordsVal_lt s.mem base c.K.M.mo c.K.M.n
  rw [h.field.mod.val] at pn
  have hl : ∀ x ∈ rcbR c.K.S c.K.R ⟨c.K.zero,c.K.zero,c.K.zero⟩, wordsVal s.mem base x c.K.M.n<C.p := by
    intro x hx
    apply h.field.lt x
    apply List.mem_append_left
    simp only [rcbR,nafLive,winRo,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  exact jacComb_finish_ok lay al hC hm hL.n hOne hone pn h.field.scr h.field.mod hl h.stable.peer.zero h.point

end VG.Proof.Weierstrass.AArch64

end

end

/-! ### `Weierstrass.AArch64.InvEarlyExtra`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64.P256Allocated (extra saveExtra restoreExtra)
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- The four additional callee-saved registers used by allocated arithmetic. -/
def allocatedExtraRegs : List Reg := extra.map Prod.fst

theorem allocatedSave_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hsize : 7832≤size) : WP isa (.block saveExtra) s fun t =>
      KeepRegs [] s t ∧ Outside base 7800 32 s.mem t.mem ∧ Spill.Saved base s.gpr extra t.mem := by
  refine WP.mono (Spill.save_wp (b:=.x0) (l:=extra) (by decide) (fun p hp => hs.st (by
    have h : ∀ p∈extra,p.2+8≤7832 := by decide
    exact Nat.le_trans (h p hp) hsize))) fun t h => ⟨⟨?_,h.rd,h.wr,h.sp⟩,?_,?_⟩
  · intro r _; exact congrFun h.gpr r
  · rw [h.mem,hs.x0]
    intro x hx
    change (((s.mem.writeW (off base 7800) (s.gpr .x26)).writeW (off base 7808) (s.gpr .x27)).writeW
      (off base 7816) (s.gpr .x28)).writeW (off base 7824) (s.gpr .x30) x=s.mem x
    rw [(writeW_outside _ base (d:=7824) _ (by decide)) x (by omega_using [hx]),
      (writeW_outside _ base (d:=7816) _ (by decide)) x (by omega_using [hx]),
      (writeW_outside _ base (d:=7808) _ (by decide)) x (by omega_using [hx]),
      (writeW_outside _ base (d:=7800) _ (by decide)) x (by omega_using [hx])]
  · rw [h.mem,hs.x0]; exact Spill.saveMem_saved (by decide) _ _ _

/-- A body's write frame preserves the saved extra registers. -/
theorem allocatedSaved_keep {base : Addr} {g : Reg → BitVec 64} {s t : State}
    {W : List (Nat × Nat)} (h : Spill.Saved base g extra s.mem)
    (hu : Unch base W s.mem t.mem)
    (hw : ∀ w∈W,w.1+w.2≤7800 ∨ 7832≤w.1) : Spill.Saved base g extra t.mem := by
  intro p hp
  have hb : ∀ p∈extra,7800≤p.2 ∧ p.2+8≤7832 := by decide
  change word t.mem base p.2=_
  rw [hu.word (fun w hm => by have := hw w hm; have := hb p hp; omega_arith) (by have := hb p hp; omega_using [this])]
  exact h p hp

 theorem allocatedRestore_ok {s : State} {base : Addr} {size : Nat} {g : Reg → BitVec 64}
    (hs : Scr s base size) (hsize : 7832≤size) (hsv : Spill.Saved base g extra s.mem) :
    WP isa (.block restoreExtra) s fun t =>
      VG.Proof.Ed25519.AArch64.Keeps allocatedExtraRegs s t ∧ ∀ r∈allocatedExtraRegs,t.gpr r=g r := by
  refine WP.mono (Spill.restore_wp hs.x0 (l:=extra) (by decide) (by decide)
    (fun p hp => by
      rw [←hs.x0]
      apply hs.ld
      have hh : ∀ p∈extra,p.2+8≤7832 := by decide
      exact Nat.le_trans (hh p hp) hsize) hsv) fun t h => ⟨⟨h.other,h.mem,h.rd,h.wr,h.sp⟩,?_⟩
  intro r hr
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
  exact h.gpr p hp

/-- Restoring the saved registers removes them from the enclosing register frame. -/
theorem allocatedRestore_frame {s a b t : State} {rs : List Reg}
    (hs : KeepRegs [] s a) (hb : KeepRegs rs a b)
    (ht : Keeps allocatedExtraRegs b t) (hv : ∀ r∈allocatedExtraRegs,t.gpr r=s.gpr r) :
    KeepRegs (rs.filter fun r => r∉allocatedExtraRegs) s t := by
  refine ⟨?_,ht.rd.trans (hb.rd.trans hs.rd),ht.wr.trans (hb.wr.trans hs.wr),ht.sp.trans (hb.sp.trans hs.sp)⟩
  intro r hr
  by_cases he : r∈allocatedExtraRegs
  · exact hv r he
  · have hnot : r∉rs := by simpa only [List.mem_filter,decide_eq_true_eq,he,not_false_eq_true,and_true] using hr
    rw [ht.gpr r he,hb.gpr r hnot,hs.gpr r (by simp)]

 theorem invAllocated_save_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (.block saveExtra) := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

 theorem invAllocated_restore_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (.block restoreExtra) := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)


end VG.Proof.Weierstrass.AArch64

end

end

/-! ### `Ecdsa.Verify.AArch64.JointPoints`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.Verify.AArch64.JointGenerator`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Proof.Weierstrass Spec.Weierstrass

namespace JointGenerator

theorem coordinates (hc : CfgOk p256)
    (hT : CombOkW p256.C 9 1 P256Joint.p256v.tbl P256Joint.p256v.start)
    {s : State} {T : Addr} (ht : TblMem s T P256Joint.p256v.combWords)
    (a : Nat) (ha : 1≤a) (ha32 : a≤128) :
    wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) 0 4=p256.mont (combAt P256Joint.p256v.tbl 0 (2*a-2)).1 ∧
    wordsVal s.mem (T+BitVec.ofNat 64 (128*(a-1))) 32 4=p256.mont (combAt P256Joint.p256v.tbl 0 (2*a-2)).2 := by
  have he := tbl_entry (n:=4) (R:=p256.R) (p:=p256.C.p) (H:=256) (J:=1)
    ht hT.len hT.lenH (j:=0) (m:=2*a-2) (by decide) (by omega)
    (Nat.lt_trans (mont_lt hc _) hc.p_lt) (Nat.lt_trans (mont_lt hc _) hc.p_lt)
  simp only [Nat.zero_mul,BitVec.add_zero,Nat.reduceMul] at he
  rw [wordsVal_addr,wordsVal_addr,Nat.add_zero]
  rw [show 128*(a-1)=64*(2*a-2) from by omega_using []]
  exact he

theorem of_table (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 9 1 P256Joint.p256v.tbl P256Joint.p256v.start)
    {s : State} {T base : Addr} (ht : TblMem s T P256Joint.p256v.combWords)
    (hout : ∀ i<P256Joint.p256v.combWords.length,∀ b<8,
      8192≤ofs base (T+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b))
    (hsym : s.syms P256Joint.cfg.tsym=T) :
    Weierstrass.AArch64.JointGenerator P256Joint.cfg p256.C base 8192 (G p256.C) T s := by
  have hlen : P256Joint.p256v.combWords.length=2048 :=
    tcombWords_length (n:=4) (R:=p256.R) (p:=p256.C.p) hT.len hT.lenH
  refine ⟨hsym,?_,?_,?_,?_⟩
  · intro a ha ha32 i hi
    change a≤128 at ha32
    rw [Offset.add_add]
    obtain ⟨r,hr,hreg⟩ := ht.rd
    exact ⟨r,hr,Region.contains_off hreg (by rw [hlen]; omega_using [hi, ha32])⟩
  · intro a ha ha32 i hi b hb
    change a≤128 at ha32
    rw [Offset.add_add T (128*(a-1)) (8*i)]
    have hd : 128*(a-1)+8*i=8*(16*(a-1)+i) := by omega_using []
    rw [hd]
    exact hout _ (by rw [hlen]; omega_using [hi, ha32]) b hb
  · intro a ha ha32
    change a≤128 at ha32
    rw [(coordinates hc hT ht a ha ha32).1,(coordinates hc hT ht a ha ha32).2]
    exact ⟨mont_lt hc _,mont_lt hc _⟩
  · intro a ha ha32
    change a≤128 at ha32
    rw [(coordinates hc hT ht a ha ha32).1,(coordinates hc hT ht a ha ha32).2]
    have hx := toM_cmont hc.toBaseCfgOk (combAt P256Joint.p256v.tbl 0 (2*a-2)).1
    have hy := toM_cmont hc.toBaseCfgOk (combAt P256Joint.p256v.tbl 0 (2*a-2)).2
    change toM p256.C.p (2^256) _=_ at hx hy
    rw [hx,hy]
    have hp := hT.entry 0 (by decide) (2*a-2) (by omega_using [ha32])
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.mul_one,show 2*a-2+1=2*a-1 from by omega_using [ha]] at hp
    rw [hp]
    exact InvJ.affine hC _ _

theorem of_pre (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 9 1 P256Joint.p256v.tbl P256Joint.p256v.start)
    {s : State} {T base : Addr} (ht : TblPre P256Joint.p256v s T base)
    (hsym : s.syms P256Joint.cfg.tsym=T) :
    Weierstrass.AArch64.JointGenerator P256Joint.cfg p256.C base 8192 (G p256.C) T s := by
  obtain ⟨hm,ho⟩ := tbl_of ht rfl (Unch.refl _ _ _)
  exact of_table hc hC hT hm ho hsym

end JointGenerator
end VG.Proof.Ecdsa.Verify.AArch64

end

end

/-! ## `JointPrep` -/

-- Formerly `VerifiedGarbage/Proof/Weierstrass/AArch64/ArithmeticTable.lean`, which only this module imported.

@[expose] public section

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V)

def jointPrepRanges : List (Nat×Nat) := [(P256Joint.cfg.gBits,520),(P256Joint.cfg.K.bits,264)]

def jointPrepProgram : Prog isa :=
  .seq (Joint.gPrep P256Joint.cfg (p256.sl U))
    (Impl.Weierstrass.AArch64.FastNaf.prep P256Joint.cfg.K (p256.sl V) 5)

structure JointPrepPost (base : Addr) (g : Reg → BitVec 64) (P : Point p256.C) (s t : State) : Prop where
  field : Inv P256Joint.cfg.K.M base size p256.C.p (·∈jacWinSlots P256Joint.cfg.K)
    (winRo P256Joint.cfg.K) (tmv p256.C 4 base t) t
  peer : NafWindowInput P256Joint.cfg.K p256.C base P (sv p256 base s V) t
  generator : ∀ i<jointGLen P256Joint.cfg,t.mem (off base (P256Joint.cfg.gBits+i))=
    jointGByte P256Joint.cfg (sv p256 base s U) i
  fixed : Fixed p256 base g t.mem
  one : tmv p256.C 4 base t P256Joint.cfg.onep=1
  same : ∀ i<45,sv p256 base t i=sv p256 base s i
  keep : KeepRegs nafPrepClob s t
  unch : Unch base jointPrepRanges s.mem t.mem
  syms : t.syms=s.syms

theorem apart_jointPrep {i : Nat} (hi : i<45) :
    ∀ w∈jointPrepRanges,p256.sl i+8*p256.n≤w.1 ∨ w.1+w.2≤p256.sl i := by
  intro w hw
  simp only [jointPrepRanges,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl
  · apply Or.inl; rw [sl_eq4 p256 (by decide)]; change 64+32*i+32≤2112; omega_using [hi]
  · apply Or.inl; rw [sl_eq4 p256 (by decide)]; change 64+32*i+32≤1824; omega_using [hi]

theorem jointPrepStage_ok (hc : CfgOk p256) (hC : Law p256.C) {base : Addr} {s : State}
    (hs : Scr s base size) {g : Reg → BitVec 64} (F : Fixed p256 base g s.mem) {P : Point p256.C}
    (hpx : sv p256 base s PX<p256.C.p) (hpy : sv p256 base s PY<p256.C.p)
    (hrep : Rep p256.C (tmv p256.C 4 base s (p256.sl PX)) (tmv p256.C 4 base s (p256.sl PY))
      (tmv p256.C 4 base s (p256.sl ONEP)) P) :
    WP isa jointPrepProgram s (JointPrepPost base g P s) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  have hmont : ∀ x,p256.mont x<p256.C.p := fun x => Nat.mod_lt _ (by omega_using [hpx])
  refine WP.mono_syms (Weierstrass.AArch64.jointPrep_ok P256Joint.cfg hs
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inr JointLayout.bits_disjoint) (by decide)) fun s₂ ⟨hs₂,bG,bQ,k₂,U₂⟩ sy₂ => ?_
  have F₂ := F.unch h7 hn (W:=jointPrepRanges) (by unfold FixedOk jointPrepRanges; decide) U₂
  have e₂ : ∀ {i},i<45 → sv p256 base s₂ i=sv p256 base s i := fun hi =>
    sv_unch U₂ h7 hn hi (apart_jointPrep hi)
  have hM₂ := modP_of hc F₂.mp
  have tv : ∀ {i}, i < 45 → tmv p256.C p256.n base s₂ (p256.sl i) = tmv p256.C p256.n base s (p256.sl i) := fun hi => by
    show toM _ _ (sv p256 base s₂ _) = toM _ _ (sv p256 base s _); rw [e₂ hi]
  have hlt : ∀ x∈winRo (P256Joint.cfg.K),wordsVal s₂.mem base x p256.n<p256.C.p := by
    intro x hx
    simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₂.ap (hmont _)
    · exact lt_of_eq_of_lt F₂.bm (hmont _)
    · exact lt_of_eq_of_lt F₂.zero (by omega_using [hpx])
    · exact lt_of_eq_of_lt (e₂ (i:=PX) (by decide)) hpx
    · exact lt_of_eq_of_lt (e₂ (i:=PY) (by decide)) hpy
    · exact lt_of_eq_of_lt F₂.onep (Nat.mod_lt _ (by omega_using [hpx]))
  have hI : Inv (P256Joint.cfg.K).M base size p256.C.p (·∈jacWinSlots (P256Joint.cfg.K))
      (winRo (P256Joint.cfg.K)) (tmv p256.C p256.n base s₂) s₂ :=
    ⟨hs₂,hM₂,fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx),hlt,fun _ _ => rfl⟩
  have one : tmv p256.C p256.n base s₂ (p256.sl ONEP)=1 := by
    change toM _ _ (wordsVal s₂.mem base (p256.sl ONEP) p256.n)=1
    rw [F₂.onep]
    have hm1 := toM_cmont hc.toBaseCfgOk 1
    have ho : Fin.ofNat p256.C.p 1 = (1:Fe p256.C) := by rfl
    simpa only [Cfg.mont,Cfg.R,Nat.one_mul,ho] using hm1
  have hp : Rep p256.C (tmv p256.C p256.n base s₂ (p256.sl PX)) (tmv p256.C p256.n base s₂ (p256.sl PY))
      (tmv p256.C p256.n base s₂ (p256.sl ONEP)) P := by
    rw [tv (by decide),tv (by decide),tv (by decide)]; exact hrep
  have hj : InvJ p256.C (tmv p256.C p256.n base s₂ (p256.sl PX)) (tmv p256.C p256.n base s₂ (p256.sl PY))
      (tmv p256.C p256.n base s₂ (p256.sl ONEP)) P := by
    have hh := InvJ.of_rep hC hp
    simpa only [one,Lean.Grind.Semiring.mul_one] using hh
  exact ⟨hI,⟨F₂.zero,fun i hi => bQ i hi,hj⟩,bG,F₂,one,fun _ hi => e₂ hi,k₂,U₂,sy₂⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointFrame` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 Spec.Weierstrass

/-- The points stage writes only arithmetic work, public digits, and precomputation. -/
def jointPointRanges : List (Nat×Nat) :=
  [(128,32),(512,544),(1824,808),(2848,1536),(5400,64),(6000,512)]

theorem jointPoint_prep : ∀ w∈jointPrepRanges,∃ r∈jointPointRanges,
    r.1≤w.1 ∧ w.1+w.2≤r.1+r.2 := by decide +kernel

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointTable` -/

/-! ## `JointSetup` -/

/-! ## `JointPoints` -/

end

end

/-! # Allocated P-256 verification points

The register-allocated verification builds `Q`'s odd multiples by co-Z
arithmetic (`Impl/P256/VerifyTable.lean`), which leaves their cached powers
of `Z` too, then runs the joint loop. -/

@[expose] public section

/-! ## `AllocatedSetup` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)

/-- What the co-Z table writes: what the joint table and cache write, and the
working space of ECDH's allocated blocks. -/
def allocatedSetupRanges : List (Nat×Nat) := jointPointRanges++[(7104,576)]

theorem buildW_cover : ∀ w∈Proof.P256.VerifyTable.buildW,∃ r∈allocatedSetupRanges,
    r.1≤w.1 ∧ w.1+w.2≤r.1+r.2 := by decide +kernel

theorem tablePt_dst (a : Nat) :
    (Jacobian.tablePt P256Joint.cfg.K a).x=Proof.P256.VerifyTable.dst a 0 ∧
    (Jacobian.tablePt P256Joint.cfg.K a).y=Proof.P256.VerifyTable.dst a 1 ∧
    (Jacobian.tablePt P256Joint.cfg.K a).z=Proof.P256.VerifyTable.dst a 2 :=
  ⟨rfl,rfl,rfl⟩

theorem tableZ_dst (i : Nat) :
    CachedJac.tableZ2 i=Proof.P256.VerifyTable.dst (i+1) 3 ∧
    CachedJac.tableZ3 i=Proof.P256.VerifyTable.dst (i+1) 4 := by
  simp only [CachedJac.tableZ2,CachedJac.tableZ3,Proof.P256.VerifyTable.dst,Nat.reduceLT,↓reduceIte,
    Nat.add_sub_cancel,Nat.reduceSub]
  omega_using []

theorem build_slots : ∀ x∈Proof.P256.VerifyTable.buildSlots,x∈jointSlots P256Joint.cfg := by
  decide +kernel

theorem build_live : ∀ x∈jointLive P256Joint.cfg,
    x∈Proof.P256.VerifyTable.copiesV Proof.P256.VerifyTable.l4 (Proof.P256.VerifyTable.Vl 7) := by
  decide +kernel

theorem build_entries : ∀ a<8,∀ j<5,Proof.P256.VerifyTable.dst (a+1) j∈
    Proof.P256.VerifyTable.copiesV Proof.P256.VerifyTable.l4 (Proof.P256.VerifyTable.Vl 7) := by
  decide +kernel

/-- The co-Z table from the prepared state: the odd multiples of `Q` with
their cached powers, everything else the joint loop reads unchanged. -/
theorem buildStage_ok (hc : CfgOk p256) (hC : Law p256.C) (hO : PrimeOrder p256.C)
    {base : Addr} {g : Reg → BitVec 64} {P : Point p256.C} (hP : onCurve p256.C P=true)
    {s₀ s : State} (h : JointPrepPost base g P s₀ s) :
    WP isa Impl.P256.VerifyTable.build s fun t =>
      AllocatedFrame Proof.P256.VerifyTable.regs base Proof.P256.VerifyTable.buildW s t ∧
      Inv P256Joint.cfg.K.M base size p256.C.p (·∈jointSlots P256Joint.cfg)
        (jointLive P256Joint.cfg) (tmv p256.C 4 base t) t ∧
      JointStable P256Joint.cfg p256.C base P (sv p256 base s₀ U) (sv p256 base s₀ V) t := by
  have hi : Inv Proof.P256.VerifyTable.M base 8192 Proof.P256.VerifyTable.C.p
      (·∈jointSlots P256Joint.cfg) Proof.P256.VerifyTable.V0 (tmv p256.C 4 base s) s :=
    h.field.mono_sl fun x hx => List.mem_append_left _ (List.mem_append_left _ hx)
  refine WP.mono (Proof.P256.VerifyTable.build_field JointLayout.layout.lay JointLayout.layout.aligned
    build_slots hi) fun t ⟨kt,it⟩ => ?_
  have un := kt.unch
  have val (x : Nat) (hx : x∈Proof.P256.VerifyTable.copiesV Proof.P256.VerifyTable.l4
      (Proof.P256.VerifyTable.Vl 7)) :
      tmv p256.C 4 base t x=Proof.P256.VerifyTable.buildEnv (tmv p256.C 4 base s) x := it.val x hx
  have h1 : tmv p256.C 4 base s 224=1 := h.one
  have jp : InvJ p256.C (tmv p256.C 4 base s 1280) (tmv p256.C 4 base s 1440) 1 P := by
    have := h.peer.2.2
    change InvJ p256.C (tmv p256.C 4 base s 1280) (tmv p256.C 4 base s 1440)
      (tmv p256.C 4 base s 224) P at this
    rw [h1] at this
    exact this
  have env := Proof.P256.VerifyTable.build_env hC hc.am3 hO hP jp h1
  have ev (a : Nat) (ha : 1≤a) (ha8 : a≤8) (j : Nat) (hj : j<5) :
      tmv p256.C 4 base t (Proof.P256.VerifyTable.dst a j)=
        Proof.P256.VerifyTable.buildEnv (tmv p256.C 4 base s) (Proof.P256.VerifyTable.dst a j) := by
    apply val
    have := build_entries (a-1) (by omega_using [ha8]) j hj
    rwa [show a-1+1=a by omega_using [ha]] at this
  have keep (x : Nat) (hx : ∀ w∈Proof.P256.VerifyTable.buildW,x+8*4≤w.1 ∨ w.1+w.2≤x)
      (hb : x+8*4≤2^64) : wordsVal t.mem base x 4=wordsVal s.mem base x 4 := un.wordsVal hx hb
  refine ⟨kt,(it.sub build_live).to_tmv,⟨⟨?_,fun a ha h8 => ?_,fun j hj => ?_⟩,fun j hj => ?_,?_,
    fun i hi => ?_,fun i hi => ?_⟩⟩
  · rw [show P256Joint.cfg.K.M.n=4 from rfl,keep _ (by decide) (by decide)]; exact h.peer.1
  · obtain ⟨ex,ey,ez⟩ := tablePt_dst a
    rw [show P256Joint.cfg.K.M.n=4 from rfl,ex,ey,ez,ev a ha h8 0 (by decide),ev a ha h8 1 (by decide),ev a ha h8 2 (by decide)]
    exact (env a ha h8).1
  · rw [un.byte (fun w hw => ?_) (by change 1824+j<2^64; omega_using [hj])]
    · exact h.peer.2.1 j hj
    · have : ∀ w∈Proof.P256.VerifyTable.buildW,2088≤w.1 ∨ w.1+w.2≤1824 := by decide
      have := this w hw
      change 1824+j+1≤w.1 ∨ w.1+w.2≤1824+j
      omega_using [hj, this]
  · change j<514 at hj
    rw [un.byte (fun w hw => ?_) (by change 2112+j<2^64; omega_using [hj])]
    · exact h.generator j hj
    · have : ∀ w∈Proof.P256.VerifyTable.buildW,2632≤w.1 ∨ w.1+w.2≤2112 := by decide
      have := this w hw
      change 2112+j+1≤w.1 ∨ w.1+w.2≤2112+j
      omega_using [hj, this]
  · change toM _ _ (wordsVal t.mem base P256Joint.cfg.onep 4)=1
    rw [keep _ (by decide) (by decide)]
    exact h.one
  · obtain ⟨e2,_⟩ := tableZ_dst i
    obtain ⟨_,_,ez⟩ := tablePt_dst (i+1)
    rw [show P256Joint.cfg.K.M.n=4 from rfl,e2,ez,ev (i+1) (by omega_using []) (by omega_using [hi]) 3 (by decide),ev (i+1) (by omega_using []) (by omega_using [hi]) 2 (by decide)]
    exact (env (i+1) (by omega_using []) (by omega_using [hi])).2.1
  · obtain ⟨e2,e3⟩ := tableZ_dst i
    obtain ⟨_,_,ez⟩ := tablePt_dst (i+1)
    rw [show P256Joint.cfg.K.M.n=4 from rfl,e3,e2,ez,ev (i+1) (by omega_using []) (by omega_using [hi]) 4 (by decide),ev (i+1) (by omega_using []) (by omega_using [hi]) 3 (by decide),
      ev (i+1) (by omega_using []) (by omega_using [hi]) 2 (by decide)]
    exact (env (i+1) (by omega_using []) (by omega_using [hi])).2.2

def allocatedSetup : Prog isa := .seq jointPrepProgram <|
  .seq Impl.P256.VerifyTable.build (.block [])

structure AllocatedSetupPost (base T : Addr) (P : Point p256.C) (u v : Nat) (s t : State) : Prop where
  field : Inv P256Joint.cfg.K.M base size p256.C.p (·∈jointSlots P256Joint.cfg)
    (jointLive P256Joint.cfg) (tmv p256.C 4 base t) t
  stable : JointStable P256Joint.cfg p256.C base P u v t
  generator : Weierstrass.AArch64.JointGenerator P256Joint.cfg p256.C base size (G p256.C) T t
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  unch : Unch base allocatedSetupRanges s.mem t.mem
  syms : t.syms=s.syms

theorem allocatedSetup_bounds : ∀ w∈allocatedSetupRanges,w.1+w.2≤size := by decide +kernel

theorem allocatedSetup_ok (hc : CfgOk p256) (hC : Law p256.C) (hO : PrimeOrder p256.C)
    (hT : CombOkW p256.C 9 1 P256Joint.p256v.tbl P256Joint.p256v.start)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (hM : Mid p256 s₀ base g s)
    (hTP : TblPre P256Joint.p256v s₀ (s₀.syms P256Joint.p256v.tsym) base)
    {P : Point p256.C} (hP : onCurve p256.C P=true)
    (hrep : Rep p256.C (tmv p256.C 4 base s (p256.sl PX)) (tmv p256.C 4 base s (p256.sl PY))
      (tmv p256.C 4 base s (p256.sl ONEP)) P) :
    WP isa allocatedSetup s
      (AllocatedSetupPost base (s₀.syms P256Joint.p256v.tsym) P (sv p256 base s U) (sv p256 base s V) s) := by
  unfold allocatedSetup
  refine WP.seq (WP.mono (jointPrepStage_ok hc hC hM.scr hM.fixed hM.px_lt hM.py_lt hrep)
    fun a ia => ?_)
  refine WP.seq (WP.mono_syms (buildStage_ok hc hC hO hP ia) fun b ⟨kb,ib,sb⟩ sy => ?_)
  apply WP.of_runBlock
  refine ⟨b,rfl,?_⟩
  have u1 : Unch base allocatedSetupRanges s.mem a.mem :=
    (ia.unch.cover jointPoint_prep).mono fun _ h => List.mem_append_left _ h
  have u2 : Unch base allocatedSetupRanges a.mem b.mem := kb.unch.cover buildW_cover
  have un : Unch base allocatedSetupRanges s.mem b.mem :=
    (u1.trans u2).mono fun _ hw => (List.mem_append.mp hw).elim id id
  have rd : b.rd=s.rd := kb.regs.rd.trans ia.keep.rd
  have wr : b.wr=s.wr := kb.regs.wr.trans ia.keep.wr
  have ss : b.syms=s.syms := sy.trans ia.syms
  have whole : Unch base [(0,size)] s₀.mem b.mem := unch_whole (hM.unch.trans un) (by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_singleton.mp hw]; exact Nat.zero_add size |>.le
    · exact allocatedSetup_bounds w hw)
  obtain ⟨table,outside⟩ := tbl_of hTP (rd.trans hM.rd) whole
  have gen := JointGenerator.of_table hc hC hT table outside (by rw [ss,hM.syms]; rfl)
  exact ⟨ib,sb,gen,rd,wr,kb.regs.sp.trans ia.keep.sp,un,ss⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `AllocatedPointsFrame` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)

def bodyRanges : List (Nat × Nat) := jointPointRanges++[(7104,576)]
def pointRanges : List (Nat × Nat) := bodyRanges++[(7800,32)]

theorem point_bounds : ∀ w∈pointRanges,w.1+w.2≤size := by decide +kernel
theorem point_fixed : FixedOk p256 pointRanges := by unfold FixedOk; decide +kernel

theorem save_same {s t : State} {base : Addr}
    (hu : Outside base 7800 32 s.mem t.mem) :
    ∀ i<45,sv p256 base t i=sv p256 base s i := by
  intro i hi
  apply hu.unch.wordsVal
  · have h : ∀ i<45,∀ w∈[(7800,32)],p256.sl i+32≤w.1 ∨ w.1+w.2≤p256.sl i := by decide +kernel
    exact h i hi
  · have h : ∀ i<45,p256.sl i+32≤2^64 := by decide +kernel
    exact h i hi

/-- Saving extra registers touches no scalar, flag, peer or fixed verifier data. -/
theorem mid_saved {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64}
    (h : Mid p256 s₀ base g s) (hk : KeepRegs [] s t)
    (hu : Outside base 7800 32 s.mem t.mem) (hsy : t.syms=s.syms) :
    Mid p256 s₀ base g t := by
  have same := save_same hu
  have whole : Unch base [(0,size)] s₀.mem t.mem := unch_whole (h.unch.trans hu.unch) (by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_singleton.mp hw]; exact Nat.zero_add size |>.le
    · rw [List.mem_singleton.mp hw]; decide)
  refine ⟨h.scr.of_keepRegs hk (by simp),hk.wr.trans h.wr,hk.rd.trans h.rd,
    h.fixed.unch (by decide) h.scr.nowrap (by unfold FixedOk; decide +kernel) hu.unch,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,whole,hsy.trans h.syms,?_⟩
  · rw [same RX (by decide)]; exact h.rx
  · rw [same RY (by decide)]; exact h.ry
  · rw [same RZ (by decide)]; exact h.rz
  · rw [hu.unch.word (by decide +kernel) (by decide)]; exact h.flag
  · rw [same PX (by decide)]; exact h.px_lt
  · rw [same PY (by decide)]; exact h.py_lt
  · rw [same PX (by decide)]; exact h.px
  · rw [same PY (by decide)]; exact h.py
  · rw [same RM' (by decide)]; exact h.rm_lt
  · rw [same RM' (by decide)]; exact h.rm
  · rw [same U (by decide)]; exact h.u_lt
  · rw [same U (by decide)]; exact h.u
  · rw [same V (by decide)]; exact h.v_lt
  · rw [same V (by decide)]; exact h.v
  · rw [same VG.Impl.Ecdsa.AArch64.K (by decide)]; exact h.k

/-- The allocated body preserves the numerical inputs to the final check. -/
theorem finalState_of_allocated {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64}
    (h : Mid p256 s₀ base g s) (hs : Scr t base size)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hu : Unch base pointRanges s.mem t.mem)
    (hx : sv p256 base t RX<p256.C.p) (hz : sv p256 base t RZ<p256.C.p) :
    FinalState p256 s₀ base g t := by
  have same (i : Nat) (hi : i∈[RM',VG.Impl.Ecdsa.AArch64.K]) : sv p256 base t i=sv p256 base s i := by
    apply hu.wordsVal
    · have he : ∀ i∈[RM',VG.Impl.Ecdsa.AArch64.K],∀ w∈pointRanges,p256.sl i+32≤w.1 ∨ w.1+w.2≤p256.sl i := by decide +kernel
      exact he i hi
    · have he : ∀ i∈[RM',VG.Impl.Ecdsa.AArch64.K],p256.sl i+32≤2^64 := by decide +kernel
      exact he i hi
  refine ⟨hs,hw.trans h.wr,hr.trans h.rd,h.fixed.unch (by decide) h.scr.nowrap point_fixed hu,
    ?_,?_,?_,hz,?_,?_,hx⟩
  · rw [hu.word (by decide +kernel) (by decide)]; exact h.flag
  · rw [same RM' (by simp)]; exact h.rm_lt
  · change toM _ _ (sv p256 base t RM')=_
    rw [same RM' (by simp)]; exact h.rm
  · exact unch_whole (h.unch.trans hu) (by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rw [List.mem_singleton.mp hw]; exact Nat.zero_add size |>.le
      · exact point_bounds w hw)
  · rw [same VG.Impl.Ecdsa.AArch64.K (by simp)]; exact h.k

end VG.Proof.Ecdsa.Verify.AArch64.Allocated

end

/-! ## `AllocatedPoints` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)

structure BodyPost (base : Addr) (P : Point C) (s t : State) : Prop where
  scr : Scr t base size
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  unch : Unch base bodyRanges s.mem t.mem
  bounds : ∀ i∈[RX,RY,RZ],sv p256 base t i<C.p
  point : Rep C (tmv C 4 base t (p256.sl RX)) (tmv C 4 base t (p256.sl RY))
    (tmv C 4 base t (p256.sl RZ)) P

theorem body_ok (raw : RawCorrect) (hc : CfgOk p256) (hC : Law p256.C) (hO : PrimeOrder p256.C)
    (hT : CombOkW p256.C 9 1 P256Joint.p256v.tbl P256Joint.p256v.start)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (hM : Mid p256 s₀ base g s)
    (hTP : TblPre P256Joint.p256v s₀ (s₀.syms P256Joint.p256v.tsym) base)
    {P : Point p256.C} (hP : onCurve p256.C P=true)
    (hrep : Rep p256.C (tmv p256.C 4 base s (p256.sl PX)) (tmv p256.C 4 base s (p256.sl PY))
      (tmv p256.C 4 base s (p256.sl ONEP)) P) :
    WP isa (Joint.points cfg P256Allocated.ops (p256.sl U) (p256.sl V)) s
      (BodyPost base (add (mul (sv p256 base s U) (G C)) (mul (sv p256 base s V) P)) s) := by
  have hm := unitMod_pow_two hc.p_odd (64*p256.n)
  have hOne : K.one<C.p := by
    change 2^256%C.p<C.p
    exact Nat.mod_lt _ (by decide)
  have hone : toM C.p (2^(64*K.M.n)) K.one=1 := toM_cmont hc.toBaseCfgOk 1
  rw [Joint.points,Joint.window]
  apply WP.assoc
  apply WP.assoc
  apply WP.assoc
  refine WP.seq (WP.mono (WP.assoc' (allocatedSetup_ok hc hC hO hT hM hTP hP hrep)) fun a ia => ?_)
  apply WP.assoc
  refine WP.seq (WP.mono (initializedRun_ok raw hC hc.am3 hm hOne hc.onG hP
    (show sv p256 base s U<2^256 from wordsVal_lt ..)
    (show sv p256 base s V<2^256 from wordsVal_lt ..) ia.field ia.stable ia.generator)
    fun b ⟨kb,ib,_⟩ => ?_)
  refine WP.mono (jointFinish_ok (jacLay hc rfl) rfl (jacAligned p256 rfl) hm hC hOne hone
    (by decide) ib) fun t ⟨kt,ut,_,lt,rep⟩ => ?_
  have u1 : Unch base bodyRanges s.mem a.mem := ia.unch
  have u2 : Unch base bodyRanges a.mem b.mem := kb.unch.cover (by decide +kernel)
  have u3 : Unch base bodyRanges b.mem t.mem := ut.cover (by decide +kernel)
  have un := ((u1.trans u2).mono (fun _ h => (List.mem_append.mp h).elim id id)).trans u3
  refine ⟨ib.field.scr.of_keepRegs kt (by decide),kt.rd.trans (kb.regs.rd.trans ia.rd),
    kt.wr.trans (kb.regs.wr.trans ia.wr),kt.sp.trans (kb.regs.sp.trans ia.sp),
    un.mono (fun _ h => (List.mem_append.mp h).elim id id),?_,rep⟩
  intro i hi
  rcases List.mem_cons.mp hi with rfl|hi
  · exact lt _ (by decide)
  rcases List.mem_cons.mp hi with rfl|hi
  · exact lt _ (by decide)
  rcases List.mem_singleton.mp hi with rfl
  exact lt _ (by decide)

/-- Allocated point arithmetic restores its additional callee-saved registers and
returns the same numerical and geometric verification postcondition. -/
theorem points_ok (hc : CfgOk p256) (hC : Law p256.C) (hO : PrimeOrder p256.C)
    (hT : CombOkW p256.C 9 1 P256Joint.p256v.tbl P256Joint.p256v.start)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (hM : Mid p256 s₀ base g s)
    (hTP : TblPre P256Joint.p256v s₀ (s₀.syms P256Joint.p256v.tsym) base)
    {P : Point p256.C} (hP : onCurve p256.C P=true)
    (hrep : Rep p256.C (tmv p256.C 4 base s (p256.sl PX)) (tmv p256.C 4 base s (p256.sl PY))
      (tmv p256.C 4 base s (p256.sl ONEP)) P) :
    WP isa P256Allocated.points s fun t => FinalState p256 s₀ base g t ∧
      Rep C (tmv C 4 base t (p256.sl RX)) (tmv C 4 base t (p256.sl RY))
        (tmv C 4 base t (p256.sl RZ))
        (add (mul (sv p256 base s U) (G C)) (mul (sv p256 base s V) P)) ∧
      ∀ r∈allocatedExtraRegs,t.gpr r=s.gpr r := by
  unfold P256Allocated.points
  apply WP.seq
  refine WP.mono_syms (allocatedSave_ok hM.scr (by decide)) fun a ⟨ka,ua,sa⟩ sya => ?_
  have ma := mid_saved hM ka ua sya
  have repa : Rep C (tmv C 4 base a (p256.sl PX)) (tmv C 4 base a (p256.sl PY))
      (tmv C 4 base a (p256.sl ONEP)) P := by
    change Rep C (toM _ _ (sv p256 base a PX)) (toM _ _ (sv p256 base a PY))
      (toM _ _ (sv p256 base a ONEP)) P
    rw [save_same ua PX (by decide),save_same ua PY (by decide),save_same ua ONEP (by decide)]
    exact hrep
  refine WP.seq (WP.mono (body_ok raw_correct hc hC hO hT ma hTP hP repa) fun b hb => ?_)
  have sb := allocatedSaved_keep sa hb.unch (by decide +kernel)
  refine WP.mono (allocatedRestore_ok hb.scr (by decide) sb) fun t ⟨kt,extra⟩ => ?_
  have whole : Unch base pointRanges s.mem t.mem := by
    rw [kt.mem]
    exact (ua.unch.trans hb.unch).mono (by
      intro w hw
      rcases List.mem_append.mp hw with hw|hw
      · exact List.mem_append_right _ hw
      · exact List.mem_append_left _ hw)
  have bounds : ∀ i∈[RX,RY,RZ],sv p256 base t i<C.p := by simpa only [sv,kt.mem] using hb.bounds
  refine ⟨finalState_of_allocated hM (hb.scr.of_keepRegs (show KeepRegs allocatedExtraRegs b t from ⟨kt.gpr,kt.rd,kt.wr,kt.sp⟩) (by decide))
    (kt.rd.trans (hb.rd.trans ka.rd)) (kt.wr.trans (hb.wr.trans ka.wr)) whole
    (bounds _ (by decide)) (bounds _ (by decide)),?_,extra⟩
  have rep := hb.point
  rw [save_same ua U (by decide),save_same ua V (by decide)] at rep
  simpa only [tmv,kt.mem] using rep

/-- The extra-register wrapper preserves precisely the verifier's untouched registers. -/
theorem points_untouched (hc : CfgOk p256) (hC : Law p256.C) (hO : PrimeOrder p256.C)
    (hT : CombOkW p256.C 9 1 P256Joint.p256v.tbl P256Joint.p256v.start)
    {s₀ s : State} {g : Reg → BitVec 64} (hp : VPreG s₀)
    (hm : Mid p256 s₀ (s₀.gpr .x3) g s) :
    WP isa P256Allocated.points s fun t => ∀ r∈untouched,t.gpr r=s.gpr r := by
  let P := peerPt p256 (s₀.mem (s₀.gpr .x0)=4) (keyX p256 s₀) (keyY p256 s₀)
  have hP : onCurve p256.C P=true := peerPt_onCurve hc _ _ _
  have hr : Rep p256.C (tmv p256.C 4 (s₀.gpr .x3) s (p256.sl PX))
      (tmv p256.C 4 (s₀.gpr .x3) s (p256.sl PY))
      (tmv p256.C 4 (s₀.gpr .x3) s (p256.sl ONEP)) P := by
    have hOne : tmv p256.C 4 (s₀.gpr .x3) s (p256.sl ONEP)=1 := onep_tmv hc hm.fixed
    rw [hOne]
    exact peerPt_rep hC _ _ _ hm.px hm.py
  exact WP.mono (points_ok hc hC hO hT hm hp.tbl hP hr) fun _ h r hr => h.2.2 r (by revert hr; revert r; decide)

end VG.Proof.Ecdsa.Verify.AArch64.Allocated

end
