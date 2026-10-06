import VerifiedGarbage.Proof.Bignum.X86_64.AdxCarry8
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.Rectangular

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
    rw [off_sub_beq B (by omega) hn]
    exact decide_eq_decide.mpr (by omega)
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
  refine WP.seq (WP.mono (block8_ok h.scr h.rsi (by omega) h.rcx)
    fun a ⟨ea,ba,oa,ka⟩ => ?_)
  refine WP.mono (advance_ok a ((ka.gpr (by decide)).trans h.rsi)
    ((ka.gpr (by decide)).trans h.rdx) hk hend) fun t ⟨pt,zt,mt,kt⟩ => ?_
  have pre : wv a.mem B e (8*k) = wv s.mem B e (8*k) := oa.wv (by omega) (by omega)
  have input : wv s.mem B (e+64*k) 8 = wv s₀.mem B (e+64*k) 8 := h.frame.wv (by omega) (by omega)
  rw [input] at ea
  have kap := ka.trans kt
  refine ⟨zt,?_,⟨h.scr.congr kap.2.2,pt,(kap.gpr (by decide)).trans h.rdx,
    (kap.gpr (by decide)).trans h.rcx,(h.keep.trans kap).mono (by decide),?_,?_⟩⟩
  · rw [kt.gpr (by decide)]; exact ba
  · rw [mt]
    exact (h.frame.mono (o' := e) (n' := 64*(k+1)) (by omega) (by omega)).trans
      (oa.mono (o' := e) (n' := 64*(k+1)) (by omega) (by omega))
  · rw [mt,kt.gpr (by decide),show 8*(k+1)=8*k+8 by omega,wv_add,wv_add,pre,
      show e+8*(8*k)=e+64*k by omega,show 64*(8*k)=512*k by omega,
      show 512*(k+1)=512*k+512 by omega,Nat.pow_add]
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
    exact ⟨h.resolve_left (by omega),i⟩
  · exact ⟨Or.inl rfl,h0⟩

end VG.Proof.Bignum.X86_64.AdxCarry8
