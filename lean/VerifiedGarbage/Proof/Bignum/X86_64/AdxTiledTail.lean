module
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledProduct
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Row
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailSetup
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxCarry8
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Core
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Add
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Store
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.Rectangular
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8AddChain
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Digit
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `Bignum.X86_64.AdxCarry8Loop`, which only this module used -/

section

/-! ## AdxCarry8 -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxCarry8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8
open VG.Proof.MlKem.X86_64 (Keep)

theorem close_ok (s : State) {c : Bool} (hc : s.cf = some c) (hz : s.gpr .rax = 0) :
    WP isa (.block AdxCarry8.close) s fun t =>
      (t.gpr .rbp).toNat = c.toNat ∧ Keeps [.rbp] s t := by
  unfold AdxCarry8.close
  rw [show ([.mov32 .rbp (.imm 0),.adcx .rbp (.reg .rax)] : List Instr) =
    [.mov32 .rbp (.imm 0)] ++ [.adcx .rbp (.reg .rax)] from rfl,WP.block_append_iff]
  refine WP.mono (movZero_ok s .rbp) fun a ⟨za,ca,_,ka⟩ => ?_
  refine WP.mono (adcx_ok a (src := .reg .rax) rfl (fun _ h => nomatch h) (ca.trans hc))
    fun t ⟨ct,_,_,et,kt⟩ => ?_
  rw [za,(ka.gpr (by decide)).trans hz] at et
  simp only [show (0 : BitVec 64).toNat = 0 from rfl,Nat.zero_add] at et
  have bc := Bool.toNat_le c
  have carryZero : ct = false := Bool.toNat_eq_zero.mp (by omega_using [et,bc])
  rw [carryZero] at et
  simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at et
  exact ⟨et,(ka.trans kt).mono (by decide)⟩

theorem add_ok (s : State) (hz : s.gpr .rcx = 0) :
    WP isa AdxCarry8.add s fun t =>
      cols t + 2^512*(t.gpr .rbp).toNat = cols s+(s.gpr .rbp).toNat ∧
      (t.gpr .rbp).toNat ≤ 1 ∧ Keeps [.rax,.rbp,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15] s t := by
  unfold AdxCarry8.add
  refine WP.seq (WP.mono (xorRax_ok s) fun a ⟨za,ca,ka⟩ => ?_)
  have sources : ∀ k < 8, ∀ t, Keeps [.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15] a t →
      readSrc t (if k=0 then .reg .rbp else .reg .rcx) = some (if k=0 then s.gpr .rbp else 0) := by
    intro k _ t kt
    by_cases hk : k=0
    · simp only [hk,↓reduceIte,readSrc,kt.gpr (r := .rbp) (by decide),ka.gpr (r := .rbp) (by decide)]
    · simp only [hk,↓reduceIte,readSrc,kt.gpr (r := .rcx) (by decide),ka.gpr (r := .rcx) (by decide),hz]
  refine WP.seq (WP.mono (chain_ok a _ _ ca sources (by
    intro k _ x; split <;> intro h <;> nomatch h)) fun b ⟨cb,hcb,eb,kb⟩ => ?_)
  refine WP.mono (close_ok b hcb ((kb.gpr (by decide)).trans za)) fun t ⟨et,kt⟩ => ?_
  rw [cols_keep ka.keep (by decide)] at eb
  simp only [number,Nat.reduceEqDiff,↓reduceIte,show (0 : BitVec 64).toNat = 0 from rfl,
    Nat.mul_zero,Nat.add_zero,Bool.toNat_false] at eb
  refine ⟨?_,?_,(ka.trans (kb.trans kt)).mono (by decide)⟩
  · rw [cols_keep kt.keep (by decide),et]; exact eb
  · rw [et]; exact Bool.toNat_le _

theorem block8_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (hp : s.gpr .rsi = off B e) (he : e+64 ≤ Z) (hz : s.gpr .rcx = 0) :
    WP isa AdxCarry8.block8 s fun t =>
      wv t.mem B e 8 + 2^512*(t.gpr .rbp).toNat = wv s.mem B e 8+(s.gpr .rbp).toNat ∧
      (t.gpr .rbp).toNat ≤ 1 ∧ Outside B e 64 s.mem t.mem ∧
      Keep [.rax,.rbp,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15] s t := by
  unfold AdxCarry8.block8
  refine WP.seq (WP.mono (loadCols_ok hs hp he) fun a ⟨va,ka⟩ => ?_)
  refine WP.seq (WP.mono (add_ok a ((ka.gpr (by decide)).trans hz)) fun b ⟨eb,bb,kb⟩ => ?_)
  have kab := ka.trans kb
  refine WP.mono (storeCols_ok (hs.congr kab.2.2.2) ((kab.gpr (by decide)).trans hp) he)
    fun t ⟨vt,ot,kt⟩ => ?_
  rw [va,ka.gpr (r := .rbp) (by decide)] at eb
  refine ⟨?_,?_,?_,(kab.keep.trans kt).mono (by decide)⟩
  · rw [vt,kt.gpr (r := .rbp) (by simp)]; exact eb
  · rw [kt.gpr (r := .rbp) (by simp)]; exact bb
  · rw [kab.2.1] at ot; exact ot

end VG.Proof.Bignum.X86_64.AdxCarry8

end

/-! ## AdxCarry8Loop -/
section

/-! The carry loop visits each remaining eight-word block exactly once. -/
namespace VG.Proof.Bignum.X86_64.AdxCarry8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem advance_ok (s : State) {B : Addr} {e k n : Nat}
    (hp : s.gpr .rsi = off B (e+64*k)) (hend : s.gpr .rdx = off B (e+64*n))
    (hk : k < n) (hn : e+64*n < 2^64) :
    WP isa (.block AdxCarry8.advance) s fun t =>
      t.gpr .rsi = off B (e+64*(k+1)) ∧ t.zf = some (decide (k+1=n)) ∧
      t.mem = s.mem ∧ Keep [.rsi] s t := by
  have add : off B (e+64*k)+64=off B (e+64*(k+1)) := by
    change off (off B (e+64*k)) 64 = off B (e+64*(k+1))
    rw [off_off]; congr 1
  have cmp : ((off B (e+64*(k+1))-off B (e+64*n)) == 0) = decide (k+1=n) := by
    rw [off_sub_beq B (by omega_using [hk, hn]) hn]
    exact decide_eq_decide.mpr (by omega_using [])
  refine WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = off B (e+64*(k+1)) ∧
    t.zf = some (decide (k+1=n)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨a,b,c⟩,keep⟩ => ⟨a,b,c,keep⟩
  unfold AdxCarry8.advance
  xrun [hp,hend,show (64 : BitVec 32).signExtend 64 = 64 from rfl,add,cmp]

structure Inv (s₀ : State) (B : Addr) (Z e k n : Nat) (s : State) : Prop where
  scr : Scr s B Z
  rsi : s.gpr .rsi = off B (e+64*k)
  rdx : s.gpr .rdx = off B (e+64*n)
  rcx : s.gpr .rcx = 0
  keep : Keep [.rax,.rbp,.rsi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15] s₀ s
  frame : Outside B e (64*k) s₀.mem s.mem
  val : wv s.mem B e (8*k)+2^(512*k)*(s.gpr .rbp).toNat =
    wv s₀.mem B e (8*k)+(s₀.gpr .rbp).toNat

theorem step_ok {s₀ s : State} {B : Addr} {Z e k n : Nat}
    (hZ : e+64*n ≤ Z) (hend : e+64*n < 2^64) (hk : k < n)
    (h : Inv s₀ B Z e k n s) :
    WP isa AdxCarry8.step s fun t => t.zf = some (decide (k+1=n)) ∧
      (t.gpr .rbp).toNat ≤ 1 ∧ Inv s₀ B Z e (k+1) n t := by
  have nowrap := h.scr.nowrap
  unfold AdxCarry8.step
  refine WP.seq (WP.mono (block8_ok h.scr h.rsi (by omega_using [hZ, hk]) h.rcx)
    fun a ⟨ea,ba,oa,ka⟩ => ?_)
  refine WP.mono (advance_ok a ((ka.gpr (by decide)).trans h.rsi)
    ((ka.gpr (by decide)).trans h.rdx) hk hend) fun t ⟨pt,zt,mt,kt⟩ => ?_
  have pre : wv a.mem B e (8*k) = wv s.mem B e (8*k) := oa.wv (by omega_using []) (by omega_using [hend, hk])
  have input : wv s.mem B (e+64*k) 8 = wv s₀.mem B (e+64*k) 8 := h.frame.wv (by omega_using []) (by omega_using [hend, hk])
  rw [input] at ea
  have kap := ka.trans kt
  refine ⟨zt,?_,⟨h.scr.congr kap.2.2,pt,(kap.gpr (by decide)).trans h.rdx,
    (kap.gpr (by decide)).trans h.rcx,(h.keep.trans kap).mono (by decide),?_,?_⟩⟩
  · rw [kt.gpr (by decide)]; exact ba
  · rw [mt]
    exact (h.frame.mono (o' := e) (n' := 64*(k+1)) (by omega_using []) (by omega_using [])).trans
      (oa.mono (o' := e) (n' := 64*(k+1)) (by omega_using []) (by omega_using []))
  · rw [mt,kt.gpr (by decide),show 8*(k+1)=8*k+8 by omega_using [],wv_add,wv_add,pre,
      show e+8*(8*k)=e+64*k by omega_using [],show 64*(8*k)=512*k by omega_using [],
      show 512*(k+1)=512*k+512 by omega_using [],Nat.pow_add]
    exact VG.Proof.Bignum.Rectangular.extend_carry h.val ea

theorem propagate_ok {s : State} {B : Addr} {Z e n : Nat}
    (hs : Scr s B Z) (hp : s.gpr .rsi = off B e) (he : s.gpr .rdx = off B (e+64*n))
    (hz : s.gpr .rcx = 0) (hZ : e+64*n ≤ Z) (hend : e+64*n < 2^64) (hn : 0 < n) :
    WP isa AdxCarry8.propagate s fun t =>
      (t.gpr .rbp).toNat ≤ 1 ∧ Inv s B Z e n n t := by
  have h0 : Inv s B Z e 0 n s :=
    ⟨hs,by simpa only [Nat.mul_zero,Nat.add_zero] using hp,he,hz,Keep.refl _ _,Outside.refl _ _ _ _,by
      simp only [Nat.mul_zero,Nat.pow_zero,Nat.one_mul,wv,Nat.zero_add]⟩
  unfold AdxCarry8.propagate
  apply wp_upto (a := 0) (N := n) hn (fun k t => (k=0 ∨ (t.gpr .rbp).toNat ≤ 1) ∧ Inv s B Z e k n t)
  · intro k _ hk t ⟨_,h⟩
    exact WP.mono (step_ok hZ hend hk h) fun _ ⟨z,b,i⟩ => ⟨z,Or.inr b,i⟩
  · intro t ⟨h,i⟩
    exact ⟨h.resolve_left (by omega_using [hn]),i⟩
  · exact ⟨Or.inl rfl,h0⟩

end VG.Proof.Bignum.X86_64.AdxCarry8

end

end

end


/-! Complete a rectangular row by propagating its pending carry to the end. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum.X86_64.AdxHeader (highPad)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

private theorem suffix_arith {L P X Y Q C D : Nat} (h : X+Q*D=Y+C) :
    L+P*X+(P*Q)*D=L+P*Y+P*C := by grind

theorem suffix_value {m m' : Mem} {B : Addr} {e d n cin cout : Nat}
    (hZ : e+8*(d+n) ≤ (2 : Nat)^64) (hf : Outside B (e+8*d) (8*n) m m')
    (hv : wv m' B (e+8*d) n + (2 : Nat)^(64*n)*cout = wv m B (e+8*d) n+cin) :
    wv m' B e (d+n)+(2 : Nat)^(64*(d+n))*cout =
      wv m B e (d+n)+(2 : Nat)^(64*d)*cin := by
  have lo := hf.wv (show e+8*d ≤ e+8*d ∨ e+8*d+8*n ≤ e by omega_using []) (by omega_using [hZ])
  rw [wv_add,wv_add,lo,Nat.mul_add,Nat.pow_add]
  exact suffix_arith hv

theorem tail_ok {s : State} {B : Addr} {Z w i n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hn : w=i+8+8*n)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i)
    (hp : s.gpr .rsi = off B (rawBase w+8*(i+w))) :
    WP isa AdxTiledProduct.tail s fun t =>
      (∃ c, wv t.mem B (rawBase w) (2*w)+(2 : Nat)^(128*w)*c =
        wv s.mem B (rawBase w) (2*w)+(2 : Nat)^(64*(i+w+8))*(word s.mem B carryOffset).toNat) ∧
      Outside B (rawBase w) (16*w) s.mem t.mem ∧ Keep mmRegs s t := by
  have nowrap := hs.nowrap
  have rawEnd : rawBase w+16*w=highPad w := by unfold rawBase highPad; omega_using []
  have padBound : highPad w+16 ≤ slot w 8 := by unfold highPad slot aAcc; omega_using []
  unfold AdxTiledProduct.tail
  refine WP.seq (WP.mono (tailTest_ok hs hd hh hZ hw (by omega_using [hn]) hidx) fun a ⟨za,ma,ka⟩ => ?_)
  by_cases he : i+8=w
  · refine WP.ite true (by simp [eval,za,he]) (fun _ => WP.block_nil ?_) (by simp)
    refine ⟨⟨(word s.mem B carryOffset).toNat,?_⟩,?_,ka.mono (by decide)⟩
    · rw [ma,show 64*(i+w+8)=128*w by omega_using [he]]
    · rw [ma]; exact Outside.refl _ _ _ _
  · refine WP.ite false (by simp [eval,za,he]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (tailSetup_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hd)
      (ma ▸ hh) hZ ((ka.gpr (by decide)).trans hp)) fun b ⟨cb,pb,eb,zb,mb,kb⟩ => ?_)
    have hend : rawBase w+8*(i+w+8)+64*n=highPad w := by rw [← rawEnd]; omega_using [hn]
    refine WP.mono (AdxCarry8.propagate_ok (hs.congr (ka.trans kb).2.2) pb
      (by rw [hend]; exact eb) zb (by rw [hend]; omega_using [hZ, padBound]) (by rw [hend]; omega_using [hZ, nowrap, padBound]) (by omega_using [hn, he] : 0<n))
      fun t ⟨_,ht⟩ => ?_
    have val := ht.val
    rw [cb,ma,show 512*n=64*(8*n) by omega_using []] at val
    have lifted := suffix_value (e := rawBase w) (d := i+w+8) (n := 8*n)
      (by omega_using [hZ, hn, nowrap, rawEnd, padBound] : rawBase w+8*(i+w+8+8*n) ≤ (2 : Nat)^64)
      (by rw [show 8*(8*n)=64*n by omega_using []]; exact ht.frame) val
    rw [mb,ma,show i+w+8+8*n=2*w by omega_using [hn],show 64*(2*w)=128*w by omega_using []] at lifted
    refine ⟨⟨(t.gpr .rbp).toNat,lifted⟩,?_,((ka.trans kb).trans ht.keep).mono (by decide)⟩
    have frame := ht.frame.mono (o' := rawBase w) (n' := 16*w) (by omega_using []) (by omega_using [hn])
    rw [mb,ma] at frame
    exact frame

end VG.Proof.Bignum.X86_64.AdxTiledProduct
