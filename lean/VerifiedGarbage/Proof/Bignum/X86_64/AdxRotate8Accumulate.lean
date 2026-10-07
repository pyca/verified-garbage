import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddInput
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

theorem addInputCarry_ok {s : State} {B : Addr} {Z eU eO : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (ho : s.gpr .rsi = off B eO)
    (he : 8 ≤ eU) (huZ : eU ≤ Z) (hoZ : eO + 64 ≤ Z) :
    WP isa (.block AdxRotate8.addInputCarry) s fun t =>
      cols t + 2^512 * (t.gpr .rax).toNat =
        cols s + (word s.mem B (eU - 8)).toNat + wv s.mem B eO 8 ∧
      (t.gpr .rax).toNat ≤ 2 ∧ t.cf = some false ∧
      Keeps [.rdx,.rax,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15] s t := by
  unfold AdxRotate8.addInputCarry
  rw [WP.block_append_iff]
  have hm := readSrc_word hs (ea_carry hc he) (show eU - 8 + 8 ≤ Z by omega)
  refine WP.mono (movMem_ok s (dst := .rdx) hm) fun a ⟨da,_,_,ka⟩ => ?_
  refine WP.mono (AdxDualAdd.addInput_ok (hs.congr ka.2.2.2)
    ((ka.gpr (by decide)).trans ho) hoZ) fun t ⟨et,bt,ct,_,kt⟩ => ?_
  rw [cols_keep ka.keep (by decide), ka.2.1, da] at et
  exact ⟨by omega_using [et],bt,ct,(ka.trans kt).mono (by simp)⟩

theorem accumulate_ok {s : State} {B : Addr} {Z eU eO : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (ho : s.gpr .rsi = off B eO)
    (he : 8 ≤ eU) (huZ : eU ≤ Z) (hoZ : eO + 64 ≤ Z) :
    WP isa AdxRotate8.accumulate s fun t =>
      cols t + 2 ^ 512 * (word t.mem B (eU - 8)).toNat =
        cols s + (word s.mem B (eU - 8)).toNat + wv s.mem B eO 8 ∧
      (word t.mem B (eU - 8)).toNat ≤ 2 ∧ Outside B (eU - 8) 8 s.mem t.mem ∧
      Keep [.rdx, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  unfold AdxRotate8.accumulate
  refine WP.seq (WP.mono (addInputCarry_ok hs hc ho he huZ hoZ) fun b ⟨eb,bb,_,kb⟩ => ?_)
  refine WP.mono (storeMem_ok (hs.congr kb.2.2.2)
    (ea_carry ((kb.gpr (by decide)).trans hc) he) (show eU - 8 + 8 ≤ Z by omega))
    fun t ⟨wt,ot,kt⟩ => ?_
  refine ⟨?_,?_,?_,(kb.keep.trans kt).mono (by simp)⟩
  · rw [wt, cols_keep kt (by simp)]; exact eb
  · rw [wt]; exact bb
  · rw [kb.2.1] at ot; exact ot
end VG.Proof.Bignum.X86_64.AdxRotate8
