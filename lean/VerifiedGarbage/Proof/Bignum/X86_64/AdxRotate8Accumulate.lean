import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Add
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep

/-! Add the input block and saved overflow before its register product. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem ea_carry {s : State} {B : Addr} {e : Nat} (hc : s.gpr .rcx = off B e) (he : 8 ≤ e) :
    s.ea AdxRotate8.blockCarry = off B (e - 8) := by
  change s.gpr .rcx + BitVec.ofInt 64 (-8) = off B (e - 8)
  rw [hc, show BitVec.ofInt 64 (-8) = 0 - BitVec.ofNat 64 8 from rfl]
  exact Offset.add_ofNat_add_neg B he

theorem accumulate_ok {s : State} {B : Addr} {Z eU eO : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (ho : s.gpr .rsi = off B eO)
    (he : 8 ≤ eU) (huZ : eU ≤ Z) (hoZ : eO + 64 ≤ Z) :
    WP isa AdxRotate8.accumulate s fun t =>
      cols t + 2 ^ 512 * (word t.mem B (eU - 8)).toNat =
        cols s + (word s.mem B (eU - 8)).toNat + wv s.mem B eO 8 ∧
      (word t.mem B (eU - 8)).toNat ≤ 2 ∧ Outside B (eU - 8) 8 s.mem t.mem ∧
      Keep [.rdx, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  unfold AdxRotate8.accumulate
  refine WP.seq (WP.mono (addMem_ok hs ho hoZ) fun a ⟨ea, ba, ca, ka⟩ => ?_)
  have sa := hs.congr ka.2.2.2
  have hca := (ka.gpr (by decide)).trans hc
  have hm := readSrc_word sa (ea_carry hca he) (show eU - 8 + 8 ≤ Z by omega)
  refine WP.seq (WP.mono (addWord_ok a (-8) hm ca (by omega)) fun b ⟨eb, _, _, kb⟩ => ?_)
  have kab := ka.trans kb
  have hcb := (kab.gpr (by decide)).trans hc
  refine WP.mono (storeMem_ok (hs.congr kab.2.2.2) (ea_carry hcb he) (show eU - 8 + 8 ≤ Z by omega))
    fun t ⟨wt, ot, kt⟩ => ?_
  rw [ka.2.1] at eb
  refine ⟨?_, ?_, ?_, (kab.keep.trans kt).mono (by simp)⟩
  · rw [wt, cols_keep kt (by simp)]
    omega_using [ea, eb]
  · rw [wt]
    have bc := cols_lt b
    have ac := cols_lt s
    have tw := wv_lt s.mem B eO 8
    have cw := (word s.mem B (eU - 8)).isLt
    omega_using [ea, eb, ac, tw, cw]
  · rw [kab.2.1] at ot; exact ot
end VG.Proof.Bignum.X86_64.AdxRotate8
