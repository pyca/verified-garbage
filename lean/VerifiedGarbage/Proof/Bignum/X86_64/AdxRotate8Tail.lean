import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Accumulate

/-! The final input block consumes both saved carries. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem ea_tileCarry {s : State} {B : Addr} {e : Nat} (hc : s.gpr .rcx = off B e) (he : 16 ≤ e) :
    s.ea AdxRotate8.tileCarry = off B (e - 16) := by
  change s.gpr .rcx + BitVec.ofInt 64 (-16) = off B (e - 16)
  rw [hc, show BitVec.ofInt 64 (-16) = 0 - BitVec.ofNat 64 16 from rfl]
  exact Offset.add_ofNat_add_neg B he

theorem tailCore_ok {s : State} {B : Addr} {Z eU eO : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (ho : s.gpr .rsi = off B eO)
    (he : 16 ≤ eU) (huZ : eU ≤ Z) (hoZ : eO + 64 ≤ Z) :
    WP isa AdxRotate8.tailCore s fun t =>
      wv t.mem B eO 8 + 2 ^ 512 * (t.gpr .rax).toNat =
        cols s + (word s.mem B (eU - 8)).toNat + wv s.mem B eO 8 +
          (word s.mem B (eU - 16)).toNat ∧
      (t.gpr .rax).toNat ≤ 3 ∧ Outside B eO 64 s.mem t.mem ∧
      Keep [.rdx, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  unfold AdxRotate8.tailCore
  refine WP.seq (WP.mono (addInputCarry_ok hs hc ho (by omega) huZ hoZ)
    fun b ⟨eb,bb,cb,kab⟩ => ?_)
  have sb := hs.congr kab.2.2.2
  have hm' := readSrc_word sb (ea_tileCarry ((kab.gpr (by decide)).trans hc) he) (show eU - 16 + 8 ≤ Z by omega)
  refine WP.seq (WP.mono (addWord_ok b (-16) hm' cb (by omega)) fun c ⟨ec, bc, _, kc⟩ => ?_)
  have kabc := kab.trans kc
  refine WP.mono (storeCols_ok (hs.congr kabc.2.2.2) ((kabc.gpr (by decide)).trans ho) hoZ)
    fun t ⟨vt, ot, kt⟩ => ?_
  rw [kab.2.1] at ec
  refine ⟨?_, ?_, ?_, (kabc.keep.trans kt).mono (by decide)⟩
  · rw [vt, kt.gpr (r := .rax) (by simp)]
    omega_using [eb, ec]
  · rw [kt.gpr (r := .rax) (by simp)]
    omega_using [bb, bc]
  · rw [kabc.2.1] at ot; exact ot
end VG.Proof.Bignum.X86_64.AdxRotate8
