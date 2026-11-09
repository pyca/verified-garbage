module

-- separate module: the public five-double counter protocol is checked independently of the final complete addition

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishAssemble
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowFiveDoubles
import VerifiedGarbage.Proof.Framework.Block

/-! The final digit executes the same five proven doubles at public index zero. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Impl.Weierstrass.AArch64.P521Native

theorem finish_five_doubles_source : finishFiveDoubles=windowFiveDoubles := by
  rw [finishFiveDoubles,windowFiveDoubles,finish_doubling_loop_source,finish_counter_sources.2.2.2.2]

theorem finish_five_doubles_ok {s : State} {W : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4584≤W)
    (bound : canonicalPoint s.mem (s.gpr .x0) 1072)
    (counter : s.gpr .x19=1#64) :
    WP isa (.seq (.block outerBlock144) finishFiveDoubles) s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1288 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1288=
        windowDbl (windowDbl (windowDbl (windowDbl (windowDbl (ordinaryPoint s.mem (s.gpr .x0) 1072))))) ∧
      WindowWorkFrame (s.gpr .x0) s.mem t.mem ∧ WindowLoopStable s t ∧ t.gpr .x19=0#64 := by
  rw [WP.seq_iff]
  refine WP.mono (finish_counter_enter s) fun u ⟨cu,_,ku,vu⟩ => ?_
  have base : u.gpr .x0=s.gpr .x0 := ku.gpr .x0 (by decide)
  have hu : Scr u (u.gpr .x0) W := by rw [base]; exact hs.of_keeps ku (by decide)
  have bu : canonicalPoint u.mem (u.gpr .x0) 1072 := by rw [base,ku.mem]; exact bound
  have packed : u.gpr .x19=windowPacked 0 2 := by rw [cu,counter]; exact finish_counter_zero
  rw [finish_five_doubles_source]
  refine WP.mono (window_five_doubles_ok hu room bu (by decide : 0<4294967296) packed)
    fun t ⟨bt,pt,ft,kt,ct⟩ => ?_
  rw [base] at bt pt ft
  rw [ku.mem] at pt ft
  refine ⟨bt,pt,ft,?_,ct⟩
  constructor
  · exact kt.base.trans base
  · exact kt.rd.trans ku.rd
  · exact kt.wr.trans ku.wr
  · exact kt.sp.trans ku.sp
  · intro r hr h30 h19
    exact (kt.gp r hr h30 h19).trans (ku.gpr r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨h19,(by decide : ∀r∈preserved,r≠Reg.x2) r hr⟩))
  · rw [kt.v29,vu]
  · rw [kt.v31,vu]

end VG.Proof.Weierstrass.AArch64.P521Native
