module

public import VerifiedGarbage.Proof.Rsa.X86.InvDispatch
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob

/-! # Comparing public lengths without changing the inverse inputs -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
 VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.KeyRt VG.Impl.Rsa.X86.KeyRt

 theorem cmpBoth {s : State} {d : Reg} {src : Src} {v : BitVec 32} {is : List Instr} {Q : State → Prop}
    (h : readSrc s src=some v)
    (k : ∀ t,Fupd s t → t.zf=some (s.gpr d-v==0) →
      t.cf=some (decide ((s.gpr d).toNat<v.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .cmp d src::is)) s Q :=
  cons (s':=arithFlags s (s.gpr d-v) (decide ((s.gpr d).toNat<v.toNat)) (subOverflow (s.gpr d) v (s.gpr d-v)))
    (by simp only [exec,execAlu,h,Option.bind_some])
    (k _ ⟨rfl,rfl,rfl,rfl,rfl⟩ rfl rfl)

 theorem invCompare_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q i limit : Nat} {s : State} {v : BitVec 32}
    (h : InvInput args base size len P Q s) (arg : CallArgument s base size i v) (small : limit<2^32) :
    WP isa (.block [.mov .eax (.mem (argOp i)),.alu .cmp .eax (.imm (BitVec.ofNat 32 limit))]) s fun t =>
      InvInput args base size len P Q t ∧ Keeps [.eax] s t ∧ t.mem=s.mem ∧
      t.zf=some (decide (v=BitVec.ofNat 32 limit)) ∧ t.cf=some (decide (v.toNat<limit)) := by
  refine wp_movS arg.readSrc fun u U _ => cmpBoth rfl fun t T zf cf => WP.block_nil ?_
  have K := U.keeps.trans (T.keeps _)
  have mem : t.mem=s.mem := T.mem.trans U.mem
  refine ⟨h.rest K (by decide) (by decide) mem,K,mem,?_,?_⟩
  · rw [zf,U.gpr]
    congr 1
    rw [Bool.eq_iff_iff,beq_iff_eq,decide_eq_true_iff,BitVec.sub_eq_iff_eq_add]
    change v=0#32+BitVec.ofNat 32 limit ↔ _
    rw [BitVec.zero_add]
  · rw [cf,U.gpr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]

 theorem InvPost.pre_rest {base : Addr} {size len P Q : Nat} {s u t : State} {regs : List Reg}
    (h : InvPost base size len P Q u t) (K : Keeps regs s u)
    (incl : ∀ r∈regs,r∈VG.Proof.Weierstrass.X86.Inv.wordClob) (mem : u.mem=s.mem) :
    InvPost base size len P Q s t := by
  exact ⟨h.1,mem ▸ h.2.1,(K.mono incl).trans h.2.2.1,h.2.2.2⟩

end VG.Proof.Rsa.X86.CrtValuesRt
