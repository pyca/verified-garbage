module

import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Read
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Digit
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Write
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
public import VerifiedGarbage.Proof.Ed448.WnafWide.Bits
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem

/-! A signed digit and the exact next biased carry, framed to one byte. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.WnafWide
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps off)

/-- All general-purpose registers the recoder may write. -/
def recClob : List Reg := [.x2,.x4,.x5,.x6,.x7,.x8,.x9,.x19]

def Enc (wide : Bool) (k i : Nat) : Byte := BitVec.ofInt 8 (digitAt wide k i)

structure StepOut (base : Addr) (wide : Bool) (k i : Nat) (s u : State) : Prop where
  scr : Scr u base
  x19 : u.gpr .x19=BitVec.ofNat 64 (i+1)
  carry : ∃ c≤radix wide, u.gpr .x6=BitVec.ofNat 64 c ∧
    residual wide k (i+1)+half wide=k/2^(i+1)+c
  keep : Keeps recClob s u
  mem : u.mem=s.mem.writeW (off base (BITS+i)) (Enc wide k i)

theorem signedStep_ok (wide : Bool) {s : State} {base : Addr} (hs : Scr s base)
    {k i c : Nat} (hi:i<464) (hc:c≤radix wide)
    (hr:s.gpr .x19=BitVec.ofNat 64 i) (h6:s.gpr .x6=BitVec.ofNat 64 c)
    (hrel:residual wide k i+half wide=k/2^i+c)
    {p : List Instr}
    (hp:WP isa (.block p) s fun u =>
      u.gpr .x4=BitVec.ofNat 64 (k/2^i%radix wide) ∧
      u.gpr .x5=BitVec.ofNat 64 (k/2^i%2) ∧ u.gpr .x2=off base i ∧
      Keeps [.x2,.x4,.x5] s u ∧ u.mem=s.mem) :
    WP isa (.block (p ++ digitStep wide ++ writeDigit)) s (StepOut base wide k i s) := by
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono hp fun a ⟨a4,a5,a2,ak,am⟩ => ?_
  rw [WP.block_append_iff]
  have hb:k/2^i%radix wide<radix wide := Nat.mod_lt _ (by cases wide <;> decide)
  have he:k/2^i%radix wide%2=k/2^i%2 := by
    cases wide <;> simp only [radix,half,Bool.false_eq_true,↓reduceIte] <;> omega
  have ac:a.gpr .x6=BitVec.ofNat 64 c := (ak.1 _ (by decide)).trans h6
  refine WP.mono (digitStep_ok wide hb hc a4 (by rw [he];exact a5) ac)
    fun b ⟨b7,b6,bk,bm⟩ => ?_
  have kAB:Keeps recClob s b := (ak.mono (by decide)).trans (bk.mono (by decide))
  have bs:Scr b base := hs.of_keeps kAB (by decide)
  have br:b.gpr .x19=BitVec.ofNat 64 i := (bk.1 _ (by decide)).trans ((ak.1 _ (by decide)).trans hr)
  have bp:b.gpr .x2=off base i := (bk.1 _ (by decide)).trans a2
  refine WP.mono (writeDigit_ok bs hi bp br) fun u ⟨ur,uk,um⟩ => ?_
  have kSU:Keeps recClob s u := kAB.trans (uk.mono (by decide))
  refine ⟨hs.of_keeps kSU (by decide),ur,?_,kSU,?_⟩
  · refine ⟨carryNext wide (k/2^i%radix wide) c,WnafWide.carry_bounds wide hc,
      (uk.1 _ (by decide)).trans b6,?_⟩
    have h:=WnafWide.carry_step wide hrel
    change next wide (residual wide k i)+half wide=k/2^(i+1)+_
    rw [Nat.pow_succ,←Nat.div_div_eq_div_mul]
    exact h
  · have hd:=WnafWide.digit_bounds wide (residual wide k i)
    have hd':-127≤digitAt wide k i ∧ digitAt wide k i≤127 := by
      cases wide <;> simp only [half,Bool.false_eq_true,↓reduceIte] at hd <;>
        change -127≤digit _ _ ∧ digit _ _≤127 <;> omega
    have h7:b.gpr .x7=BitVec.ofInt 64 (digitAt wide k i) := by
      rw [b7,WnafWide.local_digit wide hrel]
      rfl
    rw [um,h7,encode_digit hd',bm,am]
    rfl

theorem recodeBody_ok (wide : Bool) {s : State} {base : Addr} (hs : Scr s base)
    {k i c : Nat} (hi:i<456) (hc:c≤radix wide)
    (hr:s.gpr .x19=BitVec.ofNat 64 i) (h6:s.gpr .x6=BitVec.ofNat 64 c)
    (hrel:residual wide k i+half wide=k/2^i+c)
    (hb:∀ j<8,s.mem (off base (BITS+i+j))=BitVec.ofNat 8 (WnafWide.bit k (i+j))) :
    WP isa (.block (recodeBody wide)) s fun u => StepOut base wide k i s u ∧
      (u.gpr .x9==0)=decide (i+1=456) := by
  have hwidth:2^(width wide)=radix wide := by cases wide <;> rfl
  have hp:=loadBits_ok wide hs hi hr hb
  simp only [WnafWide.look,WnafWide.bit,hwidth] at hp
  have hg:=signedStep_ok wide hs (by omega) hc hr h6 hrel hp
  change WP isa (.block ((loadBits wide ++ digitStep wide ++ writeDigit) ++
    [.subImm .x .x9 .x19 456])) s _
  rw [WP.block_append_iff]
  refine WP.mono hg fun t ht => ?_
  refine WP.mono (counter_ok hi ht.x19) fun u ⟨uz,uk,um⟩ => ?_
  have ku:=uk.mono (show ∀ r∈[Reg.x9],r∈recClob by decide)
  refine ⟨⟨ht.scr.of_keeps uk (by decide),(uk.1 _ (by decide)).trans ht.x19,?_,ht.keep.trans ku,?mem⟩,uz⟩
  case mem => rw [um];exact ht.mem
  obtain ⟨c,hc,h6,hr⟩:=ht.carry
  exact ⟨c,hc,(uk.1 _ (by decide)).trans h6,hr⟩

theorem zeroHead_ok {s : State} {base : Addr} (hs:Scr s base) {i : Nat}
    (hr:s.gpr .x19=BitVec.ofNat 64 i) :
    WP isa (.block [.add .x .x2 .x3 .x19,.movz .x .x4 0 0,.movz .x .x5 0 0]) s fun u =>
      u.gpr .x4=0 ∧ u.gpr .x5=0 ∧ u.gpr .x2=off base i ∧
      Keeps [.x2,.x4,.x5] s u ∧ u.mem=s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,
    RegUpd.gpr_write,BitVec.setWidth_eq,hs.x3,hr,Nat.reduceMul,Nat.reduceLT,
    ite_true,BitVec.shiftLeft_zero,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨by trivial,by trivial,by trivial,⟨fun r hn => ?_,rfl,rfl⟩,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
  simp only [RegUpd.gpr_write,hn.1,hn.2.1,hn.2.2,ite_false]

theorem zeroStep_ok (wide : Bool) {s : State} {base : Addr} (hs:Scr s base)
    {k i c : Nat} (hk:k<VG.Impl.Ed448.WnafWide.scalarLimit) (hi:i<464) (h456:456≤i) (hc:c≤radix wide)
    (hr:s.gpr .x19=BitVec.ofNat 64 i) (h6:s.gpr .x6=BitVec.ofNat 64 c)
    (hrel:residual wide k i+half wide=k/2^i+c) :
    WP isa (.block (zeroStep wide)) s (StepOut base wide k i s) := by
  have hdiv:k/2^i=0 := WnafWide.tail_quotient hk h456
  have hz:=zeroHead_ok hs hr
  have hp:WP isa (.block [.add .x .x2 .x3 .x19,.movz .x .x4 0 0,.movz .x .x5 0 0]) s
      (fun u => u.gpr .x4=BitVec.ofNat 64 (k/2^i%radix wide) ∧
        u.gpr .x5=BitVec.ofNat 64 (k/2^i%2) ∧ u.gpr .x2=off base i ∧
        Keeps [.x2,.x4,.x5] s u ∧ u.mem=s.mem) := by
    simpa only [hdiv,Nat.zero_mod,show BitVec.ofNat 64 0=(0 : BitVec 64) from rfl] using hz
  exact signedStep_ok wide hs hi hc hr h6 hrel hp

end VG.Proof.Ed448.AArch64.Sparse
