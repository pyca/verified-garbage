module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.AddBase
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.AddKey
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Move
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode

/-! A shared doubling followed by the two signed public additions. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Keeps off)
open VG.Proof.X448.AArch64.Base (pt)
open VG.Proof.Ed448.WnafWide (maybeAdd baseEntry keyEntry)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

structure StepKeep (base:Addr) (s t:State) : Prop where
  regs : Keeps (.x19::pointClob) s t
  mem : JointFrame base s.mem t.mem

def roundPoint (P Q:Spec.Ed448.Point) (ds dk:Int) : Spec.Ed448.Point :=
  maybeAdd dk (maybeAdd ds (VG.Proof.Ed448.double Q) (baseEntry ds)) (keyEntry P dk)

theorem jointStep_ok (hA:AffineOk) {s:State} {base:Addr} {P:Spec.Ed448.Point} (h:Core base s)
    (ht:OddTabOk s.mem base P 8)
    (hxb:∀ e<8,∀ w<8,(Window.tw s.mem base e w).toNat<VG.Proof.Curve448.AArch64.Fast.Mb)
    (hbt:BaseTableAt s base (s.syms baseSym)) {i:Nat} (hi:i<464)
    (hc:s.gpr .x19=BitVec.ofNat 64 (i+1)) {ds dk:Int}
    (hds:-127≤ds ∧ ds≤127) (hdk:-15≤dk ∧ dk≤15)
    (hsd:s.mem (off base (SDIG+i))=BitVec.ofInt 8 ds)
    (hkd:s.mem (off base (BITS+i))=BitVec.ofInt 8 dk) :
    WP isa step s fun t => Core base t ∧ StepKeep base s t ∧
      t.gpr .x19=BitVec.ofNat 64 i ∧ t.gpr .x9=BitVec.ofNat 64 i ∧
      pt (EV t.mem base) 3 4 5=roundPoint P (pt (EV s.mem base) 3 4 5) ds dk := by
  unfold step
  refine WP.seq (WP.mono_syms (VG.Proof.X448.AArch64.Weak.decCounter_ok (by omega) hc)
    fun a ⟨a19,ag,am,ar,aw,_⟩ asy => ?_)
  have ak:Keeps [.x19] s a:=⟨fun r hr => ag r (by simpa only [List.mem_singleton] using hr),ar,aw⟩
  have ha:=h.regsOnly ak am (by decide)
  refine WP.seq (WP.mono_syms (Point56.doubleCall_ok ha.scr ha.env ha.zbound)
    fun b ⟨bk,bb,bsm,_,_,bz,be,_⟩ bsy => ?_)
  have kb:=PointKeep.of_call bk
  have hb:=ha.after kb bb bsm (by decide) (by decide) bz
  have b19:b.gpr .x19=BitVec.ofNat 64 i:=(kb.regs.1 _ (by decide)).trans a19
  have btab:BaseTableAt b base (b.syms baseSym):=by
    rw [bsy,asy]
    apply kb.baseTable
    refine ⟨?_,hbt.far,?_⟩
    · rw [ar,aw]
      exact hbt.read
    · rw [am]
      exact hbt.val
  refine WP.seq (WP.mono (addBase_ok hA hb btab hi b19 hds (by rw [kb.baseDigit hi,am];exact hsd))
    fun c ⟨hc',kc,cp⟩ => ?_)
  have kbc:=kb.trans kc
  have ctab:OddTabOk c.mem base P 8:=by
    apply kbc.oddTable
    rw [am]
    exact ht
  have cxb:∀ e<8,∀ w<8,(Window.tw c.mem base e w).toNat<VG.Proof.Curve448.AArch64.Fast.Mb:=by
    apply kbc.xbounds
    rw [am]
    exact hxb
  have c19:c.gpr .x19=BitVec.ofNat 64 i:=(kc.regs.1 _ (by decide)).trans b19
  refine WP.seq (WP.mono (addKey_ok hc' ctab cxb hi c19 hdk
    (by rw [kbc.keyDigit hi,am];exact hkd)) fun d ⟨hd,kd,dp⟩ => ?_)
  have d19:d.gpr .x19=BitVec.ofNat 64 i:=(kd.regs.1 _ (by decide)).trans c19
  refine WP.mono (Window.mov_ok .x9 .x19 d) fun t ⟨t9,tm,tk⟩ => ?_
  have kt:=PointKeep.of_keeps (base:=base) tk tm (by decide)
  have kap:=((kb.trans kc).trans kd).trans kt
  refine ⟨hd.of_keeps kt tm,⟨?_,?_⟩,(tk.1 _ (by decide)).trans d19,t9.trans d19,?_⟩
  · exact (ak.mono (by decide)).trans (kap.regs.mono (by decide))
  · rw [←am]
    exact kap.mem
  · rw [tm,dp,cp,be,Window.dblEnv_345,ha.one,Window.dblPt_eq,am]
    rfl

end VG.Proof.Ed448.AArch64.Sparse
