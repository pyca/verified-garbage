import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Accumulate
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Product
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Frame

/-! One input block and eight multiplier rows, with the overflow retained. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem middleBody_ok {s : State} {B : Addr} {Z eU eO eN : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (hp : s.gpr .rbp = off B eN)
    (ho : s.gpr .rsi = off B eO) (he : 8 ≤ eU) (huZ : eU + 64 ≤ Z)
    (hoZ : eO + 64 ≤ Z) (hnZ : eN + 64 ≤ Z)
    (hsepU : eU + 64 ≤ eO) (hsepN : eN + 64 ≤ eU - 8) :
    WP isa AdxRotate8.middleBody s fun t =>
      wv t.mem B eO 8 + 2 ^ 512 * (cols t + (word t.mem B (eU - 8)).toNat) =
        cols s + (word s.mem B (eU - 8)).toNat + wv s.mem B eO 8 +
          wv s.mem B eU 8 * wv s.mem B eN 8 ∧
      (word t.mem B (eU - 8)).toNat ≤ 2 ∧ BlockOut B (eU - 8) eO 64 s.mem t.mem ∧
      Keep [.rdx, .rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hn := hs.nowrap
  unfold AdxRotate8.middleBody
  refine WP.seq (WP.mono (accumulate_ok hs hc ho he (by omega) hoZ) fun a ⟨va, ba, oa, ka⟩ => ?_)
  refine WP.mono (productN_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hc)
    ((ka.gpr (by decide)).trans hp) ((ka.gpr (by decide)).trans ho) huZ hoZ hnZ hsepU (by omega))
    fun t ⟨vt, ot, kt⟩ => ?_
  have wn : wv a.mem B eN 8 = wv s.mem B eN 8 := oa.wv (by omega) (by omega)
  have wu : wv a.mem B eU 8 = wv s.mem B eU 8 := oa.wv (by omega) (by omega)
  have wc : word t.mem B (eU - 8) = word a.mem B (eU - 8) := ot.word (by omega) (by omega)
  rw [wn, wu] at vt
  refine ⟨?_, by rw [wc]; exact ba, (BlockOut.first oa).trans (BlockOut.second ot), (ka.trans kt).mono (by simp)⟩
  rw [wc]
  omega_using [va, vt]
end VG.Proof.Bignum.X86_64.AdxRotate8
