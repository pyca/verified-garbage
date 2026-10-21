module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNaf16State
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafStep
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafShift
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafChoose
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafSubtract
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafChoose
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.Words

/-! The width-nine recoder of a scalar of `n` words: its digits as sixteen-bit words. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.X25519.X86_64

theorem fastEvenStep16_ok {s : State} {base : Addr} {size n bits k j : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hI : FastPrepState16 n base size bits k j s)
    (ho : FastNaf.residual 9 k j%2=0) :
    WP isa (.block (Impl.Weierstrass.X86_64.FastNaf.shiftN n 1++Impl.Weierstrass.X86_64.FastNaf.advance 1)) s fun t =>
      FastPrepState16 n base size bits k (j+1) t ∧ KeepRegs (nafPrepClobN n) s t ∧
      Outside base bits (128*n+8) s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (fastShiftN_ok s hn (Or.inl rfl)) fun a ⟨va,ka⟩ => ?_
  have ca : a.gpr .rbx=BitVec.ofNat 64 j := (ka.1 _ (fun h => by
    rcases List.mem_cons.mp h with h|h
    · cases h
    exact notin_sregs (by decide) h)).trans hI.count
  refine WP.mono (fastAdvance_ok a (Or.inl rfl) ca) fun t ⟨ct,kt⟩ => ?_
  have mt : t.mem=s.mem := kt.2.1.trans ka.2.1
  refine ⟨⟨(hI.scr.of_keeps ka (fun h => by
    rcases List.mem_cons.mp h with h|h
    · cases h
    exact notin_sregs (by decide) h)).of_keeps kt (by decide),?_,ct,?_⟩,?_,?_⟩
  · rw [nafValN_keep kt.1 (by decide),va,hI.value,
      FastNaf.residual_succ,FastNaf.next_even 9 _ ho]
  · intro i hi
    rw [mt,hI.digits i hi]
    by_cases he : i/2=j
    · simp only [he,Nat.lt_irrefl,ite_false,Nat.lt_add_one,ite_true]
      exact (FastNaf.wbyte_of_zero (by rw [he]; exact (FastNaf.magnitude_zero_iff 9 k j).mpr ho)).symm
    · have hh : (i/2<j)=(i/2<j+1) := propext (by omega)
      simp only [hh]
  · exact ((VG.Proof.Mont.X86_64.Keeps.regs ka).mono (fun r hr => mem_clobN (pre:=[.rax])
      (by decide) hr)).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kt).mono (fun r hr => mem_clobN (pre:=[.rbx])
        (by decide) (List.mem_append_left _ hr)))
  · rw [mt]
    exact Outside.refl _ _ _ _

theorem fastOddStep16_ok {s : State} {base : Addr} {size n bits k j : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hI : FastPrepState16 n base size bits k j s)
    (hb : bits+128*n+8≤size) (hj : j<64*n+1) (hv : FastNaf.residual 9 k j≤2^(64*n))
    (ho : FastNaf.residual 9 k j%2≠0) :
    WP isa (.seq (Impl.Weierstrass.X86_64.FastNaf.choose 9)
      (.block (Naf.subtractDigitN n++([.store16 (Impl.Weierstrass.X86_64.FastNaf.tbl16 bits) .rcx] : List Instr)++
        Impl.Weierstrass.X86_64.FastNaf.shiftN n 9++Impl.Weierstrass.X86_64.FastNaf.advance 9))) s fun t =>
      FastPrepState16 n base size bits k (j+9) t ∧ KeepRegs (nafPrepClobN n) s t ∧
      Outside base bits (128*n+8) s.mem t.mem := by
  have hw : FastNaf.Wide 9 := Or.inr (Or.inr rfl)
  have hsft : (9:Nat)=1 ∨ (9:Nat)=5 ∨ (9:Nat)=7 ∨ (9:Nat)=9 := Or.inr (Or.inr (Or.inr rfl))
  have hx : (s.gpr .r8).toNat%2^9=FastNaf.residual 9 k j%2^9 := by
    have h := hI.value
    rw [nafValN_r8] at h
    omega
  refine WP.seq (WP.mono (fastChoose_ok s hw) fun a ⟨da,ka⟩ => ?_)
  have sa := hI.scr.of_keeps ka (by decide)
  have va : nafValN n a=FastNaf.residual 9 k j :=
    (nafValN_keep ka.1 (by decide)).trans hI.value
  have da' := da.trans (fastOdd_eq hw hx ho)
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (fastSubtractN_ok a hn 9 k j da' va hv) fun b ⟨vb,kb⟩ => ?_
  have sb := sa.of_keeps kb (fun h => by
    rcases List.mem_cons.mp h with h|h
    · cases h
    rcases List.mem_cons.mp h with h|h
    · cases h
    exact notin_sregs (by decide) h)
  have cb : b.gpr .rbx=BitVec.ofNat 64 j := (kb.1 _ (fun h => by
    rcases List.mem_cons.mp h with h|h
    · cases h
    rcases List.mem_cons.mp h with h|h
    · cases h
    exact notin_sregs (by decide) h)).trans ((ka.1 _ (by decide)).trans hI.count)
  have db : b.gpr .rcx=BitVec.ofInt 64 (FastNaf.digit 9 k j) := (kb.1 _ (fun h => by
    rcases List.mem_cons.mp h with h|h
    · cases h
    rcases List.mem_cons.mp h with h|h
    · cases h
    exact notin_sregs (by decide) h)).trans da'
  rw [WP.block_append_iff]
  refine WP.mono (fastStore16_ok sb (by omega) cb db) fun c ⟨mc,kc⟩ => ?_
  have sc := sb.of_keepRegs kc (by simp)
  rw [WP.block_append_iff]
  refine WP.mono (fastShiftN_ok c hn hsft) fun d ⟨vd,kd⟩ => ?_
  have sd := sc.of_keeps kd (fun h => by
    rcases List.mem_cons.mp h with h|h
    · cases h
    exact notin_sregs (by decide) h)
  have cd : d.gpr .rbx=BitVec.ofNat 64 j := (kd.1 _ (fun h => by
    rcases List.mem_cons.mp h with h|h
    · cases h
    exact notin_sregs (by decide) h)).trans ((kc.gpr _ (by simp)).trans cb)
  refine WP.mono (fastAdvance_ok d hsft cd) fun t ⟨ct,kt⟩ => ?_
  have mt : t.mem=s.mem.writeW (off base (bits+2*j)) (FastNaf.word k j) := by
    rw [kt.2.1,kd.2.1,mc,kb.2.1,ka.2.1]
  have hnw := hI.scr.nowrap
  refine ⟨⟨sd.of_keeps kt (by decide),?_,ct,?_⟩,?_,?_⟩
  · rw [nafValN_keep kt.1 (by decide),vd,nafValN_keep kc.gpr (by simp),vb]
    rw [FastNaf.residual_succ,FastNaf.next_odd9 _ ho,FastNaf.residual_skip9 k j ho]
    omega
  · intro i hi
    rw [mt]
    by_cases hij : i/2=j
    · have he : bits+i=bits+2*j+i%2 := by omega
      rw [he,writeW16_at _ _ _ (Nat.mod_lt _ (by decide)),ite_eq_left (by omega),FastNaf.wbyte,hij]
    · rw [writeW16_outside _ _ _ (by omega) (by
        rw [ofs_off0 base (d:=bits+i) (by omega)]; omega),hI.digits i hi]
      by_cases hij' : i/2<j
      · simp only [hij',show i/2<j+9 from by omega,ite_true]
      · by_cases hil : i/2<j+9
        · simp only [hij',hil,ite_false,ite_true]
          exact (FastNaf.wbyte_of_zero (by
            have h := FastNaf.magnitude_skip_zero9 k j (i/2-j) ho (by omega) (by omega)
            rwa [Nat.add_sub_of_le (by omega)] at h)).symm
        · simp only [hij',hil,ite_false]
  · exact (((VG.Proof.Mont.X86_64.Keeps.regs ka).mono (fun r hr => mem_clobN (pre:=[.rcx])
      (by decide) (List.mem_append_left _ hr))).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kb).mono (fun r hr => mem_clobN (pre:=[.rax,.rdx])
        (by decide) hr))).trans
      ((kc.mono (by simp)).trans (((VG.Proof.Mont.X86_64.Keeps.regs kd).mono
        (fun r hr => mem_clobN (pre:=[.rax]) (by decide) hr)).trans
        ((VG.Proof.Mont.X86_64.Keeps.regs kt).mono (fun r hr => mem_clobN (pre:=[.rbx])
          (by decide) (List.mem_append_left _ hr)))))
  · intro x hx
    rw [mt]
    exact writeW16_outside _ _ _ (by omega) (by omega)

def fastDelta16 (k j : Nat) : Nat := if FastNaf.residual 9 k j%2=0 then 1 else 9

theorem fastPrepStep16_ok {s : State} {base : Addr} {size n bits k j : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hI : FastPrepState16 n base size bits k j s)
    (hb : bits+128*n+8≤size) (hj : j<64*n+1) (hv : FastNaf.residual 9 k j≤2^(64*n)) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.stepN16 n bits) s fun t =>
      FastPrepState16 n base size bits k (j+fastDelta16 k j) t ∧
      t.cf=some (decide (j+fastDelta16 k j<64*n+1)) ∧ KeepRegs (nafPrepClobN n) s t ∧
      Outside base bits (128*n+8) s.mem t.mem := by
  have hd : fastDelta16 k j=1 ∨ fastDelta16 k j=9 := by
    unfold fastDelta16
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  rw [Impl.Weierstrass.X86_64.FastNaf.stepN16]
  refine WP.seq (WP.mono (nafParity_ok s) fun a ⟨_,hz,ka⟩ => ?_)
  have ia := hI.of_keeps ka (by decide)
  have hp : s.gpr .r8 &&& 1=0 ↔ FastNaf.residual 9 k j%2=0 := by
    rw [nafParity]
    have h := hI.value
    rw [nafValN_r8] at h
    omega
  apply WP.seq
  have branches : WP isa
      (.ite .e (.block (Impl.Weierstrass.X86_64.FastNaf.shiftN n 1++Impl.Weierstrass.X86_64.FastNaf.advance 1))
        (.seq (Impl.Weierstrass.X86_64.FastNaf.choose 9)
          (.block (Naf.subtractDigitN n++[.store16 (Impl.Weierstrass.X86_64.FastNaf.tbl16 bits) .rcx]++
            Impl.Weierstrass.X86_64.FastNaf.shiftN n 9++Impl.Weierstrass.X86_64.FastNaf.advance 9)))) a
      (fun t => FastPrepState16 n base size bits k (j+fastDelta16 k j) t ∧
        KeepRegs (nafPrepClobN n) a t ∧ Outside base bits (128*n+8) a.mem t.mem) := by
    apply WP.ite (decide (s.gpr .r8 &&& 1=0)) hz
    · intro h
      have he := hp.mp (of_decide_eq_true h)
      simpa only [fastDelta16,he,ite_true] using fastEvenStep16_ok hn ia he
    · intro h
      have he : FastNaf.residual 9 k j%2≠0 := fun he => (of_decide_eq_false h) (hp.mpr he)
      simpa only [fastDelta16,he,ite_false] using fastOddStep16_ok hn ia hb hj hv he
  refine WP.mono branches fun b ⟨ib,kb,ob⟩ => ?_
  refine WP.mono (fastCompare_ok b (n:=n) (by omega) (by rcases hd with h|h <;> omega) ib.count)
    fun t ⟨cf,kt⟩ => ?_
  refine ⟨ib.of_keeps kt (by simp),cf,?_,?_⟩
  · exact (((VG.Proof.Mont.X86_64.Keeps.regs ka).mono (fun r hr => mem_clobN (pre:=[.rcx])
      (by decide) (List.mem_append_left _ hr))).trans kb).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kt).mono (by simp))
  · rw [kt.2.1,ka.2.1] at *
    exact ob

theorem fastClear16_ok {s : State} {base : Addr} {size n bits : Nat}
    (hs : Scr s base size) (hb : bits+128*n+8≤size) :
    WP isa (.block (setConst (16*n+1) bits 0)) s fun t =>
      (∀ i<128*n+8,t.mem (off base (bits+i))=0) ∧ KeepRegs [.rax] s t ∧
        Outside base bits (128*n+8) s.mem t.mem := by
  have hc : WP isa (.block (setConst (16*n+1) bits 0)) s fun t =>
      wordsVal t.mem base bits (16*n+1)=0 ∧ KeepRegs [.rax] s t ∧
        Outside base bits (8*(16*n+1)) s.mem t.mem :=
    setConst_ok hs (by omega) (Nat.two_pow_pos _)
  refine WP.mono hc fun t ⟨ht,kt,ot⟩ => ⟨?_,kt,?_⟩
  · intro i hi
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    rw [testBit_byte t.mem base (n:=16*n+1) (by omega) hb,ht]
    simp only [BitVec.ofNat_eq_ofNat,Nat.zero_testBit,BitVec.getLsbD_zero]
  · rwa [show 8*(16*n+1)=128*n+8 by omega] at ot

theorem fastPrepInit16_ok {s : State} {base : Addr} {size n src bits : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hs : Scr s base size) (hsrc : src+8*n≤size) (hb : bits+128*n+8≤size) :
    WP isa (.block (Naf.initN n src++setConst (16*n+1) bits 0)) s fun t =>
      FastPrepState16 n base size bits (wordsVal s.mem base src n) 0 t ∧
      KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (128*n+8) s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (nafPrepInitN_ok hn hs hsrc) fun a ⟨va,ca,ka,ma,sa⟩ => ?_
  refine WP.mono (fastClear16_ok sa hb) fun t ⟨zt,kt,ot⟩ => ?_
  have hv : nafValN n t=nafValN n a :=
    VG.Proof.Mont.X86_64.regsVal_congr fun r hr => kt.gpr r (by
      rcases hn with rfl|rfl|rfl <;> revert r <;> decide)
  refine ⟨⟨sa.of_keepRegs kt (by decide),?_,?_,?_⟩,ka.trans (kt.mono (by
    rcases hn with rfl|rfl|rfl <;> decide)),?_⟩
  · rw [hv,va,FastNaf.residual_zero]
  · exact (kt.gpr .rbx (by decide)).trans ca
  · intro i hi
    simpa only [Nat.not_lt_zero,ite_false] using zt i (by omega)
  · rw [ma] at ot
    exact ot

theorem fastPrep16_ok {s : State} {base : Addr} {size n src bits : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hs : Scr s base size) (hsrc : src+8*n≤size) (hb : bits+128*n+8≤size) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.prepN16 n src bits) s fun t =>
      (∃ j,64*n+1≤j ∧ j≤64*n+9 ∧ FastPrepState16 n base size bits (wordsVal s.mem base src n) j t) ∧
      KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (128*n+8) s.mem t.mem := by
  let k := wordsVal s.mem base src n
  have hk : k<2^(64*n) := wordsVal_lt ..
  let I (m : Nat) (t : State) := FastPrepState16 n base size bits k (64*n+1-m) t ∧
    KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (128*n+8) s.mem t.mem
  rw [Impl.Weierstrass.X86_64.FastNaf.prepN16]
  refine WP.seq (WP.mono (fastPrepInit16_ok hn hs hsrc hb) fun a ⟨ia,ka,oa⟩ => ?_)
  refine WP.loop (M:=isa) (fun m t => 1≤m ∧ m≤64*n+1 ∧ I m t) (fun m t ⟨hm,hm',hi⟩ => ?_)
    (64*n+1) a ⟨by omega,by omega,by simpa only [Nat.sub_self] using ia,ka,oa⟩
  have hj : 64*n+1-m<64*n+1 := by omega
  have hv : FastNaf.residual 9 k (64*n+1-m)≤2^(64*n) := by
    have h := FastNaf.residual_boundB 9 (Nat.le_of_lt hk) (j:=64*n+1-m) (by omega)
    exact Nat.le_trans h (Nat.pow_le_pow_right (by decide) (by omega))
  have hd : 1≤fastDelta16 k (64*n+1-m) ∧ fastDelta16 k (64*n+1-m)≤9 := by
    unfold fastDelta16; split <;> decide
  refine WP.mono (fastPrepStep16_ok hn hi.1 hb hj hv) fun u ⟨iu,cf,ku,ou⟩ => ?_
  have ki := hi.2.1.trans ku
  have oi := hi.2.2.trans ou
  by_cases he : 64*n+1≤64*n+1-m+fastDelta16 k (64*n+1-m)
  · refine Or.inl ⟨?_,⟨_,he,by omega,iu⟩,ki,oi⟩
    change u.cf=some false
    rw [cf]
    congr 1
    exact decide_eq_false (by omega)
  · refine Or.inr ⟨?_,m-fastDelta16 k (64*n+1-m),by omega,by omega,by omega,?_,ki,oi⟩
    · change u.cf=some true
      rw [cf]
      congr 1
      exact decide_eq_true (by omega)
    · rw [show 64*n+1-(m-fastDelta16 k (64*n+1-m))=64*n+1-m+fastDelta16 k (64*n+1-m) from by omega]
      exact iu

/-- The recoder leaves every digit's bytes. -/
theorem fastPrepDigits16_ok {s : State} {base : Addr} {size n src bits : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hs : Scr s base size) (hsrc : src+8*n≤size) (hb : bits+128*n+8≤size) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.prepN16 n src bits) s fun t =>
      (∀ i<2*(64*n+1),t.mem (off base (bits+i))=FastNaf.wbyte (wordsVal s.mem base src n) i) ∧
      KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (128*n+8) s.mem t.mem := by
  refine WP.mono (fastPrep16_ok hn hs hsrc hb) fun t ⟨⟨j,hj,_,hi⟩,kt,ot⟩ => ⟨?_,kt,ot⟩
  intro i hi'
  simpa only [show i/2<j from by omega,ite_true] using hi.digits i hi'

end VG.Proof.Weierstrass.X86_64
