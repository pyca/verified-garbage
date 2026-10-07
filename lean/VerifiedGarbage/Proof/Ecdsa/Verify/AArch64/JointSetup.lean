import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointTable
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointCache
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointFrame
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointGenerator
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)

def jointSetup : Prog isa := .seq jointPrepProgram <|
  .seq (ArithmeticTable.table P256Joint.cfg.K) (CachedJac.cache P256Joint.cfg.K)

structure JointSetupPost (base T : Addr) (P : Point p256.C) (u v : Nat) (s t : State) : Prop where
  field : Inv P256Joint.cfg.K.M base size p256.C.p (·∈jointSlots P256Joint.cfg)
    (jointLive P256Joint.cfg) (tmv p256.C 4 base t) t
  stable : JointStable P256Joint.cfg p256.C base P u v t
  generator : Weierstrass.AArch64.JointGenerator P256Joint.cfg p256.C base size (G p256.C) T t
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  unch : Unch base jointPointRanges s.mem t.mem
  syms : t.syms=s.syms

theorem jointSetup_ok (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (hM : Mid p256 s₀ base g s)
    (hTP : TblPre p256 s₀ (s₀.syms p256.tsym) base)
    {P : Point p256.C} (hP : onCurve p256.C P=true)
    (hrep : Rep p256.C (tmv p256.C 4 base s (p256.sl PX)) (tmv p256.C 4 base s (p256.sl PY))
      (tmv p256.C 4 base s (p256.sl ONEP)) P) :
    WP isa jointSetup s (JointSetupPost base (s₀.syms p256.tsym) P (sv p256 base s U) (sv p256 base s V) s) := by
  unfold jointSetup
  refine WP.seq (WP.mono (jointPrepStage_ok hc hC hM.scr hM.fixed hM.px_lt hM.py_lt hrep)
    fun a ia => ?_)
  refine WP.seq (WP.mono (jointTableStage_ok Forward.Arithmetic.cases hc hC hP ia) fun b ib => ?_)
  refine WP.mono_syms (jointCache_ok JointLayout.layout (unitMod_pow_two hc.p_odd _)
    ib.field ib.stable ib.generator ib.one) fun t ⟨kt,it,st⟩ sy => ?_
  have u1 := ia.unch.cover jointPoint_prep
  have u2 := ib.table.unch.cover jointPoint_table
  have u3 : Unch base jointPointRanges b.mem t.mem := kt.unch.cover jointPoint_cache
  have un := jointPoint_union (jointPoint_union u1 u2) u3
  have rd : t.rd=s.rd := kt.rd.trans (ib.table.keep.rd.trans ia.keep.rd)
  have wr : t.wr=s.wr := kt.wr.trans (ib.table.keep.wr.trans ia.keep.wr)
  have ss : t.syms=s.syms := sy.trans (ib.syms.trans ia.syms)
  have whole : Unch base [(0,size)] s₀.mem t.mem := unch_whole (hM.unch.trans un) (by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_singleton.mp hw]; exact Nat.zero_add size |>.le
    · exact jointPoint_bounds w hw)
  obtain ⟨table,outside⟩ := tbl_of hTP (rd.trans hM.rd) whole
  have gen := JointGenerator.of_table hc hC hT table outside (by rw [ss,hM.syms]; rfl)
  exact ⟨it,st,gen,rd,wr,kt.sp.trans (ib.table.keep.sp.trans ia.keep.sp),un,ss⟩

end VG.Proof.Ecdsa.Verify.AArch64
