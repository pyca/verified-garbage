module

public import VerifiedGarbage.Impl.Ecdh.P521.AArch64.Window
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Mont.AArch64.Words

/-! # Bound the working scalar while retaining the original range-check input -/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P521.Window

attribute [local instance high] instPowNat

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64
open VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64.P521Window
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

theorem andLow_ok (s : State) :
    WP isa (.block [.movz .x .x4 511 0,.logic .and .x .x3 .x3 .x4]) s fun t =>
      (t.gpr .x3).toNat = (s.gpr .x3).toNat % 512 ∧ Keeps [.x3,.x4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,Size.bits,Nat.mul_zero,show (0:Nat)<64 from by decide,
    BitVec.shiftLeft_zero,read_x,RegUpd.gpr_write,
    BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  · rw [BitVec.toNat_and]
    change (s.gpr .x3).toNat &&& (2^9-1) = (s.gpr .x3).toNat % 2^9
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

theorem lowHigh_mod {L B T m : Nat} (hL : L < B) :
    (L+B*T) % (B*2^m) = L+B*(T%2^m) := by
  have hT := Nat.div_add_mod T (2^m)
  have hp : 0 < 2^m := Nat.pow_pos (by decide)
  have hlt : L+B*(T%2^m) < B*2^m := by
    have := Nat.mod_lt T hp
    have : B*(T%2^m)+B ≤ B*2^m := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this
    omega
  rw [show L+B*T = L+B*(T%2^m)+B*2^m*(T/2^m) by
    conv_lhs => rw [← hT]
    rw [Nat.mul_add,Nat.mul_assoc]; omega]
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hlt]

theorem lowHigh_pow {L T a b : Nat} (hL : L < 2^a) :
    (L+2^a*T)%2^(a+b) = L+2^a*(T%2^b) := by
  rw [Nat.pow_add]
  exact lowHigh_mod hL

theorem mask_ok {base : Addr} {s : State} (hs : Scr s base size) :
    WP isa (.block maskK) s fun t => Scr t base size ∧ KeepRegs [.x3,.x4] s t ∧
      sv c base t K = sv c base s K % 2^521 ∧ Unch base (slW c [K]) s.mem t.mem := by
  have hd : c.sl K+64+8 ≤ size := by decide +kernel
  have ha : (c.sl K+64)%8=0 := by decide +kernel
  rw [maskK,show ([ld .x3 (c.sl K+64),.movz .x .x4 511 0,
    .logic .and .x .x3 .x3 .x4,st .x3 (c.sl K+64)] : List Instr) =
    [ld .x3 (c.sl K+64)] ++ [.movz .x .x4 511 0,.logic .and .x .x3 .x3 .x4] ++
      [st .x3 (c.sl K+64)] from rfl,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (ld_ok hs hd ha .x3) fun s₁ ⟨e₁,k₁,_⟩ => ?_
  refine WP.mono (andLow_ok s₁) fun s₂ ⟨e₂,k₂⟩ => ?_
  have k : Keeps [.x3,.x4] s s₂ := (k₁.mono (by simp)).trans k₂
  have hs₂ := hs.of_keeps k (by decide)
  refine WP.mono (st_out hs₂ hd ha .x3) fun t ⟨hm,hg,_⟩ => ?_
  have hs' := hs₂.of_keepRegs hg (by decide)
  have ho : Outside base (c.sl K+64) 8 s.mem t.mem := by
    rw [hm,k.mem]; exact writeW_outside _ _ _ (by have := hs.nowrap; omega)
  refine ⟨hs', (Keeps.regs k).trans (hg.mono (by simp)), ?_, fun x hx => ?_⟩
  · unfold sv
    change wordsVal t.mem base (c.sl K) (8+1) = wordsVal s.mem base (c.sl K) (8+1) % 2^521
    rw [wordsVal_succ_top _ _ _ 8,wordsVal_succ_top _ _ _ 8,
      ho.wordsVal (by omega) (by have := hs.nowrap; omega),hm,word_writeW_self]
    change _ + _ * (s₂.gpr .x3).toNat = _
    rw [e₂,e₁]
    have he := @lowHigh_pow (wordsVal s.mem base (c.sl K) 8)
      (word s.mem base (c.sl K+64)).toNat (64*8) 9 (wordsVal_lt s.mem base (c.sl K) 8)
    simp only [show 64*8=512 from rfl,show 8*8=64 from rfl,show 512+9=521 from rfl] at he ⊢
    conv at he => rhs; arg 2; arg 2; arg 2; change 512
    exact he.symm
  · apply ho
    have h := hx _ (List.mem_singleton_self _)
    change ofs base x < c.sl K ∨ c.sl K+8*c.n ≤ ofs base x at h
    change ofs base x < c.sl K+64 ∨ c.sl K+64+8 ≤ ofs base x
    have hn : c.n = 9 := rfl
    omega

end VG.Proof.Ecdh.AArch64.P521.Window
