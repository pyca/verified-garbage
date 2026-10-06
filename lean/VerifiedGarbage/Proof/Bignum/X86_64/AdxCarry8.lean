import VerifiedGarbage.Impl.Bignum.X86_64.AdxCarry8
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Add
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Store

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
  exact ⟨et,(ka.trans kt).mono (by simp)⟩

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
  refine ⟨?_,?_,(ka.trans (kb.trans kt)).mono (by simp)⟩
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
  refine ⟨?_,?_,?_,(kab.keep.trans kt).mono (by simp)⟩
  · rw [vt,kt.gpr (r := .rbp) (by simp)]; exact eb
  · rw [kt.gpr (r := .rbp) (by simp)]; exact bb
  · rw [kab.2.1] at ot; exact ot

end VG.Proof.Bignum.X86_64.AdxCarry8
