import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcRow

/-! Selecting and storing a cancellation digit without changing the columns. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

def digitValue (s : State) (mi : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((s.gpr .r8).toNat * mi.toNat)

theorem cols_keep {s t : State} {rs : List Reg} (hk : Keep rs s t)
    (h : ∀ r ∈ [Reg.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15], r ∉ rs) : cols t = cols s := by
  unfold cols
  rw [hk.gpr (h _ (by simp)), hk.gpr (h _ (by simp)), hk.gpr (h _ (by simp)),
    hk.gpr (h _ (by simp)), hk.gpr (h _ (by simp)), hk.gpr (h _ (by simp)),
    hk.gpr (h _ (by simp)), hk.gpr (h _ (by simp))]

theorem digit_ok {s : State} {B : Addr} {Z e k : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B e) (he : e + 8 * k + 8 ≤ Z)
    (hm : readSrc s (.mem (hdr sMinv)) = some mi) :
    WP isa (.block (AdxRotate8.digit k)) s fun t =>
      t.gpr .rdx = digitValue s mi ∧ cols t = cols s ∧
      t.mem = s.mem.writeW (off B (e + 8 * k)) (digitValue s mi) ∧
      Keep [.rdx, .rax] s t := by
  have hm' : s.load64 (s.ea (hdr sMinv)) = some mi := hm
  refine WP.mono (WP.keep [.rdx, .rax] (Q := fun t =>
    t.gpr .rdx = digitValue s mi ∧
      t.mem = s.mem.writeW (off B (e + 8 * k)) (digitValue s mi)) ?_ rfl)
    fun t ⟨⟨hd, ht⟩, hk⟩ => ⟨hd, cols_keep hk (by decide), ht, hk⟩
  unfold AdxRotate8.digit
  have hm'' : s.load64 (s.gpr .rdi + BitVec.ofInt 64 (8 * (sMinv : Int))) = some mi := hm'
  simp only [State.load64] at hm''
  xrun [execMulx, State.ea, hdr, at_, hc, BitVec.ofInt_natCast, off_off, hm'', hs.st he]
  exact ⟨rfl, rfl⟩

end VG.Proof.Bignum.X86_64.AdxRotate8
