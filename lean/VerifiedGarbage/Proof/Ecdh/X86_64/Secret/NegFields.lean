import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Bits
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.LayoutOps
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldSelect
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero

/-! The signed five-bit digit conditionally negates Y without changing the other fields. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

abbrev digitCfg (K : WinCfg) : TCombCfg := {WinCfg.tc K with w:=5,kbytes:=5*K.J}

def negEnv {C : Curve} (K : WinCfg) (E : Nat → Fe C) (k j : Nat) : Nat → Fe C :=
  Function.update (Function.update E K.neg (-E K.E.y)) K.E.y
    (if combWin 5 k j<16 then -E K.E.y else E K.E.y)

theorem neg_fields_ok {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : SecretLay K size) (hm : UnitMod C.p (2^(64*K.M.n)))
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (·∈slots K) V E s)
    (hy : K.E.y∈V) (hz : K.zero∈V) (h0 : E K.zero=0)
    (hj : j<K.J) (hc : s.gpr .rbx=BitVec.ofNat 64 j) (hb : ScalarBits K base k s) :
    WP isa (.block (digitCfg K).negY) s fun t =>
      ProgKeep K.M base [K.E.y,K.neg] s t ∧
      Inv K.M base size C.p (·∈slots K) (K.E.y::K.neg::V) (negEnv K E k j) t := by
  have hn : K.neg∈localWrites K := by simp [localWrites,winOther]
  have hny : K.E.y≠K.neg := by
    have hh := hL.nodup
    simp only [localWrites,winOther,List.cons_append,List.nil_append,List.nodup_cons,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at hh
    grind
  have hsl : ∀ x∈(FOp.sub K.neg K.zero K.E.y).out::(FOp.sub K.neg K.zero K.E.y).ins,x∈slots K := by
    intro x hx
    simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact local_slots K _ hn
    · exact hI.sl _ hz
    · exact hI.sl _ hy
  have hread : ∀ x∈(FOp.sub K.neg K.zero K.E.y).ins,x∈V := by
    intro x hx
    simp only [FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact hz
    · exact hy
  rw [TCombCfg.negY,List.append_assoc,WP.block_append_iff]
  refine WP.mono (fop_ok hL.lay hm hI hsl hread) fun u ⟨ku,iu⟩ => ?_
  have ku' : ProgKeep K.M base [K.neg] s u := progKeep_of_op ku (by simp [FOp.out])
  have cu : u.gpr .rbx=BitVec.ofNat 64 j := (ku'.gpr _ (by rw [hL.n]; decide)).trans hc
  have bu := hb.keep hL hI.scr (CounterKeep.of_progKeep ku') (by
    intro x hx
    obtain rfl := List.mem_singleton.mp hx
    exact List.mem_append_left _ hn)
  have iu' : Inv K.M base size C.p (·∈slots K) (K.neg::V)
      (Function.update E K.neg (-E K.E.y)) u := by
    simpa only [FOp.out,FOp.run,h0,show (0 : Fe C)-E K.E.y = -E K.E.y from by grind] using iu
  rw [WP.block_append_iff]
  refine WP.mono (signMask_ok (digitCfg K) iu'.scr (k:=k) (j:=j) (N:=5*K.J)
    (by change 1≤5; decide) (by change 5<2^31; decide) (by change 5*j+5≤5*K.J; omega) hL.bits cu bu) fun v ⟨cv,kv⟩ => ?_
  have iv := iu'.of_keeps kv (by decide)
  have kv' : ProgKeep K.M base [] u v := by
    refine ⟨fun r hr => kv.1 r ?_,kv.2.2.1,kv.2.2.2,fun x _ _ => congrFun kv.2.1 x⟩
    intro hh
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl|rfl|rfl <;> exact hr (by simp [clob])
  refine WP.mono (selectField_ok hL.lay iv (hI.sl _ hy)
    (List.mem_cons_of_mem _ hy) (List.mem_cons_self ..)
    (decide (combWin 5 k j<16)) cv) fun t ⟨kt,it⟩ => ?_
  refine ⟨(ku'.mono (by simp)).trans ((kv'.mono (by simp)).trans (kt.mono (by simp))),?_⟩
  simpa only [negEnv,Function.update_self,Function.update_of_ne hny,decide_eq_true_eq] using it

end VG.Proof.Ecdh.X86_64.Secret
