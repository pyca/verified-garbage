import VerifiedGarbage.Impl.Bignum.X86_64.AdxRect8
import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddInput
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Product

/-! Exact rectangular products, with both inputs and all other memory preserved. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8
open VG.Proof.MlKem.X86_64 (Keep)

theorem finish_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (hp : s.gpr .rsi = off B e) (he : e + 64 ≤ Z) :
    WP isa AdxRect8.finish s fun t =>
      wv t.mem B e 8 + 2^512 * (t.gpr .rax).toNat =
        cols s + wv s.mem B e 8 + (s.gpr .rdx).toNat ∧
      (t.gpr .rax).toNat ≤ 2 ∧ Outside B e 64 s.mem t.mem ∧
      Keep [.rax,.rdx,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15] s t := by
  unfold AdxRect8.finish
  refine WP.seq (WP.mono (AdxDualAdd.addInput_ok hs hp he)
    fun a ⟨ea,ba,_,_,ka⟩ => ?_)
  refine WP.mono (storeCols_ok (hs.congr ka.2.2.2)
    ((ka.gpr (by decide)).trans hp) he) fun t ⟨vt,ot,kt⟩ => ?_
  refine ⟨?_,?_,?_,(ka.keep.trans kt).mono (by simp)⟩
  · rw [vt,kt.gpr (r := .rax) (by simp)]; exact ea
  · rw [kt.gpr (r := .rax) (by simp)]; exact ba
  · rw [ka.2.1] at ot; exact ot

theorem product_ok {s : State} {B : Addr} {Z eA eB eO : Nat}
    (hs : Scr s B Z) (ha : s.gpr .rcx = off B eA)
    (hb : s.gpr .rbp = off B eB) (ho : s.gpr .rsi = off B eO)
    (hA : eA + 64 ≤ Z) (hB : eB + 64 ≤ Z) (hO : eO + 64 ≤ Z)
    (sepA : eA + 64 ≤ eO ∨ eO + 64 ≤ eA)
    (sepB : eB + 64 ≤ eO ∨ eO + 64 ≤ eB) :
    WP isa AdxRect8.product s fun t =>
      wv t.mem B eO 8 + 2^512 * cols t =
        wv s.mem B eO 8 + wv s.mem B eA 8 * wv s.mem B eB 8 ∧
      Outside B eO 64 s.mem t.mem ∧
      Keep [.rdx,.rax,.rbx,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15] s t := by
  unfold AdxRect8.product
  refine WP.seq (WP.mono (loadCols_ok hs ho hO) fun a ⟨va,ka⟩ => ?_)
  refine WP.mono (productN_disjoint_ok (hs.congr ka.2.2.2)
    ((ka.gpr (by decide)).trans ha) ((ka.gpr (by decide)).trans hb)
    ((ka.gpr (by decide)).trans ho) hA hO hB sepA sepB)
    fun t ⟨vt,ot,kt⟩ => ?_
  rw [va,ka.2.1] at vt
  simp only [Nat.reduceMul] at vt
  rw [ka.2.1] at ot
  exact ⟨vt,ot,(ka.keep.trans kt).mono (by simp)⟩

end VG.Proof.Bignum.X86_64.AdxRect8
