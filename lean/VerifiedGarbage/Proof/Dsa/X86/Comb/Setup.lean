module

public import VerifiedGarbage.Impl.Dsa.X86.CombSetup
public import VerifiedGarbage.Proof.Mont.X86.ContextInit

import VerifiedGarbage.Proof.Mont.X86.PublicPower
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Impl.Mont.X86.ContextSquares
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.RepeatSquares
/-! Public full-width and padded setup paths establish the same Montgomery seed. -/

-- Formerly `VerifiedGarbage/Proof/Mont/X86/ContextSquares.lean`, which only this module imported.
section

/-! The common squaring-loop proof instantiated for the DSA Montgomery workspace. -/

section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

structure SetupState (n m size : Nat) (base : Addr) (s t : State) : Prop where
  context : Context n m base size t
  one : wordsVal t.mem base (slot n 3) n=wordsVal s.mem base (slot n 3) n
  mem : Outs base (setupRanges n) s.mem t.mem
  keeps : Keeps powerClob s t

theorem setupSquares_ok {n size m a : Nat} {base : Addr} {s : State}
    (C : Context n m base size s)
    (V : wordsVal s.mem base (slot n 4) n=2^(64*n+a)%m) :
    WP isa (setupSquares n) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 3) n=wordsVal s.mem base (slot n 3) n ∧
      wordsVal t.mem base (slot n 4) n=2^(64*n+64*a)%m ∧
      Outs base (setupRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  let square := mul (contextMod n) 0 (slot n 2) (slot n 4) (slot n 4) (slot n 4)
  let P := SetupState n m size base s
  let num := fun t : State => wordsVal t.mem base (slot n 4) n
  have stable (u v : State) (U : P u) (mem : v.mem=u.mem) (keep : Keeps [.esi] u v) : P v :=
    ⟨⟨U.context.scr.of_keeps keep (by decide),U.context.size_le,mem ▸ U.context.modulus,
      U.context.gt_one,mem ▸ U.context.inverse⟩,mem ▸ U.one,mem ▸ U.mem,
      U.keeps.trans (keep.mono (by decide))⟩
  have step (u : State) (U : P u) (lt : num u<m) :
      WP isa square u fun v =>
        P v ∧ Keeps clob u v ∧ num v<m ∧ num v*2^(64*n)%m=num u*num u%m := by
    refine WP.mono (context_mul_ok U.context (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) lt) fun v ⟨Cv,K,lv,Mv⟩ => ?_
    refine ⟨⟨Cv,?_,U.mem.trans (K.mem.mono ?_),
      U.keeps.trans ((OpKeep.keeps K).mono (by decide))⟩,OpKeep.keeps K,lv,Mv⟩
    · exact (context_slot_val U.context (i := 3) (by decide) (by decide) (by decide) (by decide) K).trans U.one
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl <;> simp [setupRanges,contextMod,accLen,words] <;> omega
  have initial : P s := ⟨C,rfl,Outs.refl _ _ _,Keeps.refl _ _⟩
  change WP isa (repeatSquaresWith square 6) s _
  refine WP.mono (repeatSquaresWith_ok square P num (E := a) C.coprime stable
    (fun u v h => by dsimp only [num];rw [h]) step (by decide) (by decide) initial
    (by dsimp only [num];rw [V];exact Nat.mod_lt _ (by have := C.gt_one;omega))
    (by dsimp only [num];rw [V,Nat.mod_mod,←Nat.pow_add];congr 2;omega))
    fun t ⟨T,lt,value⟩ => ?_
  refine ⟨T.context,T.one,?_,T.mem,T.keeps⟩
  rw [Nat.mod_eq_of_lt lt,show 2^(6 : Nat)*a=64*a from rfl,←Nat.pow_add] at value
  simpa only [Nat.add_comm] using value

end VG.Proof.Mont.X86.Dynamic
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Comb

theorem seed_ok {n size m : Nat} {base : Addr} {s : State}
    (hs : Scr s base size) (hn : 0 < n) (hn32 : 128*n < 2^32)
    (hz : contextBytes n ≤ size) (hv : wordsVal s.mem base (slot n 0) n = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (seed n) s fun t =>
      Context n m base size t ∧ wordsVal t.mem base (slot n 3) n = 1 ∧
      wordsVal t.mem base (slot n 4) n = 2^(65*n) % m ∧
      Outs base (setupRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold seed
  refine WP.seq (WP.mono (contextStart_ok hs hn hz hv hm1 hodd) fun v ⟨Cv, Vv, Ov, Kv⟩ => ?_)
  have s04 := slot_le (n := n) (i := 0) (j := 4) (by decide)
  refine WP.mono (publicPower_ok Cv.scr Cv.modulus
    (context_opLay hz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by change slot n 4+8*n≤slot n 0 ∨ slot n 0+8*n≤slot n 4;unfold stride at s04;omega)
    hn32 hm1 hodd) fun t ⟨Vt,Mt,Ot,Kt⟩ => ?_
  obtain ⟨Ct,one,frame⟩ := Cv.power_frame Mt Ot Kt
  exact ⟨Ct,one.trans Vv,Vt,Ov.trans frame,Kv.trans Kt⟩

theorem setup_ok {n size m : Nat} {base : Addr} {s : State}
    (hs : Scr s base size) (hn : 0 < n) (hn32 : 128*n < 2^32)
    (hz : contextBytes n ≤ size) (hv : wordsVal s.mem base (slot n 0) n = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (setup n) s fun t =>
      Context n m base size t ∧ wordsVal t.mem base (slot n 3) n = 1 ∧
      wordsVal t.mem base (slot n 4) n = 2^(128*n) % m ∧
      Outs base (setupRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold setup
  refine WP.seq (WP.mono (seed_ok hs hn hn32 hz hv hm1 hodd) fun u ⟨Cu, Ou, Vu, Fu, Ku⟩ => ?_)
  have value : wordsVal u.mem base (slot n 4) n = 2^(64*n+n) % m := by
    simpa only [show 64*n+n = 65*n by omega] using Vu
  refine WP.mono (setupSquares_ok Cu value) fun t ⟨Ct, Ot, Vt, Ft, Kt⟩ => ?_
  exact ⟨Ct, Ot.trans Ou, by simpa only [show 64*n+64*n = 128*n by omega] using Vt,
    Fu.trans Ft, Ku.trans Kt⟩

end VG.Proof.Dsa.X86.Comb
