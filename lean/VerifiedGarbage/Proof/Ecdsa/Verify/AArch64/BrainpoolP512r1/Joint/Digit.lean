module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Inputs
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.CombDigitW
import VerifiedGarbage.Proof.Weierstrass.CombW
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AddrArith

/-! Reading one public pair of unsigned two-bit digits. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint

abbrev Bits (base : Addr) (u v : Nat) (s : State) : Prop :=
  (∀ t < 512,s.mem (off base (bitsU+t)) = if u.testBit t then 1 else 0) ∧
  (∀ t < 512,s.mem (off base (bitsV+t)) = if v.testBit t then 1 else 0)

def digitPair (u v j : Nat) : Nat := (u >>> (2*j)) % 4 + 4*((v >>> (2*j)) % 4)

theorem digitPair_lt (u v j : Nat) : digitPair u v j < 16 := by
  unfold digitPair; omega

theorem Changes.bits {base : Addr} {u v : Nat} {s t : State}
    (h : Changes base arithmeticWork s t) (hb : Bits base u v s) : Bits base u v t := by
  have apart : ∀ b ∈ [bitsU,bitsV],∀ j < 512,∀ w ∈ arithmeticWork,
      b+j+1 ≤ w.1 ∨ w.1+w.2 ≤ b+j := by
    intro b h j hj w hw
    have hd : ∀ b ∈ [bitsU,bitsV],∀ w ∈ arithmeticWork,b+512 ≤ w.1 ∨ w.1+w.2 ≤ b := by decide
    have := hd b h w hw; omega
  constructor
  · intro j hj
    rw [h.mem.byte (apart bitsU (by simp) j hj) (by change 2944+j < 2^64; omega)]
    exact hb.1 j hj
  · intro j hj
    rw [h.mem.byte (apart bitsV (by simp) j hj) (by change 3456+j < 2^64; omega)]
    exact hb.2 j hj

theorem index2_ok {s : State} {base : Addr} (hs : Scr s base 8192) {j : Nat}
    (hx : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.lsl .x .x16 .x19 1,.add .x .x16 .x0 .x16]) s fun t =>
      t.gpr .x16 = off base (2*j) ∧ Keeps [.x16] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    show 1 < Size.x.bits by decide,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,hx,hs.x0,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [BitVec.shiftLeft_eq_mul_twoPow]
    change base + BitVec.ofNat 64 j * BitVec.ofNat 64 2 = base + BitVec.ofNat 64 (2*j)
    rw [←BitVec.ofNat_mul,Nat.mul_comm j 2]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

theorem read2_ok {base : Addr} {s : State} (hs : Scr s base 8192) {bits k j : Nat}
    (hbits : bits+512 ≤ 8192) (henc : bits+2 ≤ 4096) (hj : j < 256)
    (h16 : s.gpr .x16 = off base (2*j))
    (hb : ∀ t < 512,s.mem (off base (bits+t)) = if k.testBit t then 1 else 0) :
    WP isa (.block (hornerBits bits 2)) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 ((k >>> (2*j)) % 4) ∧ Keeps [.x2,.x4] s t := by
  have hv : ∀ i,(k.testBit (2*j+(i-bits))).toNat ≤ 1 := fun _ => Bool.toNat_le _
  refine WP.mono (hornerBits_ok hv 2 bits (s:=s) (by decide) henc fun i hi => ?_)
    fun t ⟨v,h⟩ => ⟨?_,h⟩
  · have e : s.gpr .x16+BitVec.ofNat 64 (bits+i) = off base (bits+(2*j+i)) := by
      rw [h16,off,off,BitVec.add_assoc,←BitVec.ofNat_add]
      exact congrArg (base+·) (congrArg _ (by omega))
    refine ⟨?_,?_⟩
    · rw [e]; exact ⟨_,List.mem_append_right _ hs.wr,hs.contains (by omega) (by decide)⟩
    · rw [e,hb _ (by omega),show bits+i-bits=i by omega]
      cases k.testBit (2*j+i) <;> rfl
  · have he : hornerVal (fun i => (k.testBit (2*j+(i-bits))).toNat) bits 2 = combWin 2 k j := by
      have hh := hornerVal_eq k 2 j 2 (Nat.le_refl _)
      rw [Nat.sub_self,Nat.add_zero] at hh
      rw [combWin,←hh]
      exact hornerVal_congr fun i _ => by simp only [show bits+i-bits=i by omega]
    rw [v,he,combWin,Nat.shiftRight_eq_div_pow]

theorem save_digit_ok (s : State) :
    WP isa (.block [.addImm .x .x6 .x2 0]) s fun t => t.gpr .x6=s.gpr .x2 ∧ Keeps [.x6] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    show (0 : Nat) < 4096 by decide,BitVec.setWidth_eq,BitVec.add_zero,ite_true,
    Option.some.injEq,exists_eq_left']
  refine ⟨True.intro,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write,hr,ite_false]

theorem combine_ok (s : State) {a b : Nat}
    (h6 : s.gpr .x6=BitVec.ofNat 64 a) (h2 : s.gpr .x2=BitVec.ofNat 64 b) :
    WP isa (.block [.lsl .x .x2 .x2 2,.add .x .x2 .x2 .x6]) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 (a+4*b) ∧ Keeps [.x2] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    show 2 < Size.x.bits by decide,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,h6,h2,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 b*BitVec.ofNat 64 4+BitVec.ofNat 64 a=BitVec.ofNat 64 (a+4*b)
    rw [←BitVec.ofNat_mul,←BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

theorem digit_ok {base : Addr} {s : State} (hs : Scr s base 8192) {u v j : Nat}
    (hb : Bits base u v s) (hj : j < 256) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block digit) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 (digitPair u v j) ∧ Keeps [.x2,.x4,.x6,.x16] s t := by
  rw [Impl.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.digit]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (index2_ok hs h19) fun s₁ ⟨p₁,k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (read2_ok (hs.of_keeps k₁ (by decide)) (bits:=bitsU) (k:=u) (by decide) (by decide) hj p₁
    (by rw [k₁.mem]; exact hb.1)) fun s₂ ⟨v₂,k₂⟩ => ?_
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono (save_digit_ok s₂) fun s₃ ⟨v₃,k₃⟩ => ?_
  rw [WP.block_append_iff]
  have hs₃ := ((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  have p₃ : s₃.gpr .x16=off base (2*j) := by rw [k₃.gpr _ (by decide),k₂.gpr _ (by decide),p₁]
  refine WP.mono (read2_ok hs₃ (bits:=bitsV) (k:=v) (by decide) (by decide) hj p₃
    (by rw [k₃.mem,k₂.mem,k₁.mem]; exact hb.2)) fun s₄ ⟨v₄,k₄⟩ => ?_
  have e₆ : s₄.gpr .x6=BitVec.ofNat 64 ((u >>> (2*j)) % 4) := by rw [k₄.gpr _ (by decide),v₃,v₂]
  refine WP.mono (combine_ok s₄ e₆ v₄) fun t ⟨v₅,k₅⟩ => ?_
  exact ⟨v₅,((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans
    (k₃.mono (by decide))).trans (k₄.mono (by decide))).trans (k₅.mono (by decide))⟩
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint
