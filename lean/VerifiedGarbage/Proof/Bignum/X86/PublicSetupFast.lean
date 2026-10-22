module

public import VerifiedGarbage.Proof.Bignum.X86.PublicSetup
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Mont.X86.PublicPower
import VerifiedGarbage.Proof.Mont.X86.RepeatSquares
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame

/-! Reuse public-modulus seeding and the shared six-square loop in RSA's compact workspace. -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext VG.Impl.Mont VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem power_ranges {n : Nat} {r : Nat × Nat}
    (hr : r∈[(slot n 5,8*n),((modulus n).tmp,8*n),(slot n 2,accLen (modulus n))]) :
    r∈setupRanges n := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl <;> simp [setupRanges,modulus,accLen,words] <;> omega

theorem Context.power_keep {n bytes m : Nat} {base : Addr} {s t : State}
    (C : Context n m base bytes s) (M : Modulus (modulus n) bytes m t.mem base)
    (O : Outs base [(slot n 5,8*n),((modulus n).tmp,8*n),(slot n 2,accLen (modulus n))] s.mem t.mem)
    (K : Keeps powerClob s t) :
    Context n m base bytes t ∧ wordsVal t.mem base (slot n 4) n=wordsVal s.mem base (slot n 4) n := by
  have hdr := slot_header n 1
  have h4 := slot_header n 4
  have s13 := slot_le (n := n) (i := 1) (j := 4) (by decide)
  have s34 := slot_le (n := n) (i := 4) (j := 5) (by decide)
  have s23 := acc_end n
  simp only [acc_length] at s23
  have b3 := slot_bound (n := n) (i := 4) (by decide)
  have inv : w32 t.mem base inverseOffset=w32 s.mem base inverseOffset := by
    have v := O.val32 (d := inverseOffset) (k := 1) (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      all_goals simp only [modulus,inverseOffset,VG.Impl.Bignum.sMinv]
      all_goals have := slot_header n 2
      all_goals have := slot_header n 5
      all_goals omega) (by decide)
    simpa only [val32,Nat.mul_zero,Nat.add_zero] using v
  refine ⟨⟨C.scr.of_keeps K (by decide),C.size_le,M,C.gt_one,by rw [inv];exact C.inverse⟩,?_⟩
  rw [wordsVal_eq_val32,wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl <;> simp only [modulus,accLen,words] <;>
      unfold stride at s13 s34 <;> omega
  · have := C.scr.nowrap
    have := C.size_le
    unfold stride at b3
    omega

structure SetupState (n m bytes : Nat) (base : Addr) (s t : State) : Prop where
  context : Context n m base bytes t
  one : wordsVal t.mem base (slot n 4) n=wordsVal s.mem base (slot n 4) n
  mem : Outs base (setupRanges n) s.mem t.mem
  keeps : Keeps powerClob s t

theorem squares_ok {n bytes m : Nat} {base : Addr} {s : State}
    (C : Context n m base bytes s) (odd : m%2=1)
    (value : wordsVal s.mem base (slot n 5) n=2^(65*n)%m) :
    WP isa (VG.Impl.Mont.X86.Dynamic.repeatSquaresWith (multiply n 5 5 5) 6) s fun t =>
      SetupState n m bytes base s t ∧ wordsVal t.mem base (slot n 5) n=2^(128*n)%m := by
  let P := SetupState n m bytes base s
  let num := fun t : State => wordsVal t.mem base (slot n 5) n
  have stable (a b : State) (A : P a) (mem : b.mem=a.mem) (keep : Keeps [.esi] a b) : P b :=
    ⟨⟨A.context.scr.of_keeps keep (by decide),A.context.size_le,mem ▸ A.context.mod,
      A.context.gt_one,mem ▸ A.context.inverse⟩,mem ▸ A.one,mem ▸ A.mem,
      A.keeps.trans (keep.mono (by decide))⟩
  have step (a : State) (A : P a) (lt : num a<m) :
      WP isa (multiply n 5 5 5) a fun b =>
        P b ∧ Keeps clob a b ∧ num b<m ∧ num b*2^(64*n)%m=num a*num a%m := by
    refine WP.mono (multiply_ok A.context (by unfold operand;decide) (by unfold operand;decide) (by unfold operand;decide)
      (by decide) (by decide) (by decide) (by decide) lt) fun b ⟨B,K,lb,V⟩ => ?_
    refine ⟨⟨B,?_,A.mem.trans (K.mem.mono (fun _ hr => power_ranges hr)),
      A.keeps.trans ((OpKeep.keeps K).mono (by decide))⟩,OpKeep.keeps K,lb,V⟩
    exact (slot_value A.context (i := 4) (by unfold operand;decide) (by decide) (by decide) K).trans A.one
  have initial : P s := ⟨C,rfl,Outs.refl _ _ _,Keeps.refl _ _⟩
  refine WP.mono (repeatSquaresWith_ok (multiply n 5 5 5) P num
    (E := n) (VG.Proof.Bignum.coprime_pow2 odd _) stable
    (fun a b h => by dsimp only [num];rw [h]) step (by decide) (by decide) initial
    (by dsimp only [num];rw [value];exact Nat.mod_lt _ (by have := C.gt_one;omega))
    (by dsimp only [num];rw [value,Nat.mod_mod,←Nat.pow_add];congr 2;omega))
    fun t ⟨T,lt,V⟩ => ?_
  refine ⟨T,?_⟩
  rw [Nat.mod_eq_of_lt lt,show 2^(6 : Nat)*n=64*n from rfl,←Nat.pow_add] at V
  simpa only [show 64*n+64*n=128*n by omega] using V

theorem setup_ok {n bytes m : Nat} {base : Addr} {s : State}
    (hs : Scr s base bytes) (hn : 0<n) (small : 128*n<2^32)
    (hz : size n≤bytes) (hv : wordsVal s.mem base (slot n 0) n=m)
    (hm1 : 1<m) (odd : m%2=1) :
    WP isa (setup n) s fun t =>
      Context n m base bytes t ∧ wordsVal t.mem base (slot n 4) n=1 ∧
      wordsVal t.mem base (slot n 5) n=2^(128*n)%m ∧
      Outs base (setupRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold setup
  refine WP.seq (WP.mono (start_ok hs hn hz hv hm1 odd) fun u ⟨Cu,one,Ou,Ku⟩ => ?_)
  refine WP.seq (WP.mono (publicPower_ok Cu.scr Cu.mod
    (operation_layout hz (by unfold operand;decide) (by unfold operand;decide)
      (by unfold operand;decide) (by decide))
    (by have h := slot_le (n := n) (i := 0) (j := 5) (by decide)
        change slot n 5+8*n≤slot n 0 ∨ slot n 0+8*n≤slot n 5
        unfold stride at h;omega) small hm1 odd) fun v ⟨value,Mv,Ov,Kv⟩ => ?_)
  obtain ⟨Cv,onev⟩ := Cu.power_keep Mv Ov Kv
  refine WP.mono (squares_ok Cv odd value) fun t ⟨T,Vt⟩ => ?_
  exact ⟨T.context,T.one.trans (onev.trans one),Vt,
    (Ou.trans (Ov.mono (fun _ hr => power_ranges hr))).trans T.mem,Ku.trans (Kv.trans T.keeps)⟩

end VG.Proof.Bignum.X86.PublicContext
