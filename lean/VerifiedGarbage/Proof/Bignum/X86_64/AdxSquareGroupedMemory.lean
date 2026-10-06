import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareGroupedCarry
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep

/-! The grouped diagonal accesses the same disjoint input and output words. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareGrouped
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem head_ok {s : State} {B : Addr} {Z A eb i k : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 i) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2*i))
    (hA : A + 16*(i+k) + 16 ≤ Z) (hb : eb + 8*(i+k) + 8 ≤ Z) :
    WP isa (.block (AdxSquareGrouped.head k)) s fun t =>
      t.gpr .rdx = word s.mem B (eb + 8*(i+k)) ∧
      t.gpr .r11 = word s.mem B (A + 16*(i+k)) ∧
      t.gpr .r12 = word s.mem B (A + 16*(i+k) + 8) ∧
      t.cf = s.cf ∧ t.of = s.of ∧ Keeps [.rdx, .r11, .r12] s t := by
  have ea : off B A + BitVec.ofNat 64 (2*i) * BitVec.ofNat 64 8 +
      BitVec.ofInt 64 ((16*k : Nat) : Int) = off B (A + 16*(i+k)) := by
    rw [addrD]; congr 1; omega
  have ea' : off B A + BitVec.ofNat 64 (2*i) * BitVec.ofNat 64 8 +
      BitVec.ofInt 64 ((16*k+8 : Nat) : Int) = off B (A + 16*(i+k) + 8) := by
    rw [addrD]; congr 1; omega
  have eb' : off B eb + BitVec.ofNat 64 i * BitVec.ofNat 64 8 +
      BitVec.ofInt 64 ((8*k : Nat) : Int) = off B (eb + 8*(i+k)) := by
    rw [addrD]; congr 1; omega
  refine WP.mono (WP.keep [.rdx, .r11, .r12] (Q := fun t =>
      t.gpr .rdx = word s.mem B (eb + 8*(i+k)) ∧
      t.gpr .r11 = word s.mem B (A + 16*(i+k)) ∧
      t.gpr .r12 = word s.mem B (A + 16*(i+k) + 8) ∧
      t.cf = s.cf ∧ t.of = s.of ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h,q⟩ => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,
      q.1,h.2.2.2.2.2,q.2⟩
  unfold AdxSquareGrouped.head
  xrun [State.ea, ix, h8, h9, hbp, h14, ea, ea', eb',
    hs.ld hb, hs.ld (show A + 16*(i+k) + 8 ≤ Z by omega), hs.ld hA] <;> rfl

theorem store_ok {s : State} {B : Addr} {Z A i k : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B A) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2*i))
    (hA : A + 16*(i+k) + 16 ≤ Z) :
    WP isa (.block (AdxSquareGrouped.store k)) s fun t =>
      t.mem = (s.mem.writeW (off B (A + 16*(i+k))) (s.gpr .r11)).writeW
        (off B (A + 16*(i+k) + 8)) (s.gpr .r12) ∧
      t.cf = s.cf ∧ t.of = s.of ∧ Keep [] s t := by
  have ea : off B A + BitVec.ofNat 64 (2*i) * BitVec.ofNat 64 8 +
      BitVec.ofInt 64 ((16*k : Nat) : Int) = off B (A + 16*(i+k)) := by
    rw [addrD]; congr 1; omega
  have ea' : off B A + BitVec.ofNat 64 (2*i) * BitVec.ofNat 64 8 +
      BitVec.ofInt 64 ((16*k+8 : Nat) : Int) = off B (A + 16*(i+k) + 8) := by
    rw [addrD]; congr 1; omega
  refine WP.mono (WP.keep [] (Q := fun t =>
      t.mem = (s.mem.writeW (off B (A + 16*(i+k))) (s.gpr .r11)).writeW
        (off B (A + 16*(i+k) + 8)) (s.gpr .r12) ∧ t.cf = s.cf ∧ t.of = s.of)
    ?_ rfl) fun t ⟨h,q⟩ => ⟨h.1,h.2.1,h.2.2,q⟩
  unfold AdxSquareGrouped.store
  xrun [State.ea, ix, h8, h14, ea, ea', hs.st (show A + 16*(i+k) + 8 ≤ Z by omega), hs.st hA]

end VG.Proof.Bignum.X86_64.AdxSquareGrouped
