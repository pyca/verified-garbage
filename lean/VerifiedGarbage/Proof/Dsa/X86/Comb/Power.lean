module

import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerInit
import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerLoop
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
import VerifiedGarbage.Proof.Mont.X86.CombTableState

/-! Shared-table exponentiation, including padding and Montgomery decoding. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt)

theorem power_ok {n e m g : Nat} {base : Addr} {s : State}
    (h : Supported n e) (pub : Bool) (C : Context n m base (layout n e).size s)
    (T : TableAt n (context n) m g (32*e) base (fun _ => True) s.mem)
    (one : wordsVal s.mem base (slot n 3) n=1) :
    WP isa (VG.Impl.Mont.X86.Comb.combPower n e (context n) pub) s fun t =>
      Context n m base (layout n e).size t ∧
      wordsVal t.mem base (slot n 6) n=g^val32 s.mem base (slot n 8) e%m ∧
      Outs base (powerRanges n e) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold VG.Impl.Mont.X86.Comb.combPower VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  refine WP.seq (WP.mono (powerInit_ok h C T) fun u ⟨Cu,Tu,Au,Xu,ESI,Ou,Ku⟩ => ?_)
  refine WP.seq (WP.mono (powerLoop_ok h pub Cu Tu Au Xu (val32_lt _ _ _ _) ESI)
    fun v ⟨Cv,Tv,Av,Ov,Kv⟩ => ?_)
  have O := Ou.trans Ov
  have Onev : wordsVal v.mem base (slot n 3) n=1 := (power_preserves_one h O).trans one
  refine WP.seq (WP.mono (context_mul_ok Cv (o := 6) (a := 6) (b := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [Onev]; exact C.gt_one)) fun t ⟨Ct,Kt,lt,Vt⟩ => WP.block_nil ?_)
  refine ⟨Ct,?_,?_,(Ku.trans Kv).trans ((OpKeep.keeps Kt).mono (by decide))⟩
  · have decoded := VG.Proof.Dsa.mont_decode (A := wordsVal v.mem base (slot n 6) n)
      (out := wordsVal t.mem base (slot n 6) n) (a := Spec.Rsa.powMod g (val32 s.mem base (slot n 8) e) m) C.coprime
      (by rw [Av,Nat.mod_mod]) (by rw [Vt,Onev])
    rw [Nat.mod_eq_of_lt lt,VG.Proof.Bignum.powMod_eq,Nat.mod_mod] at decoded
    exact decoded
  · have ot : Outs base (powerRanges n e) v.mem t.mem := Kt.mem.mono (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl <;> simp [powerRanges,contextMod,accLen,words] <;> omega)
    exact O.trans ot

end VG.Proof.Dsa.X86.Comb
