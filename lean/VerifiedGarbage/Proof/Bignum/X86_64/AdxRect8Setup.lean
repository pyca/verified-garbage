import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Tile
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused

/-! Tile addresses depend only on the public word indices and array layout. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem shift3 (n : Nat) : (BitVec.ofNat 64 n) <<< (3 : Nat) = BitVec.ofNat 64 (8*n) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 n * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8*n)
  rw [← BitVec.ofNat_mul,Nat.mul_comm]

theorem setup_ok {s : State} {B : Addr} {Z w i j : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) {a b : Nat} (ha : a < 8) (hb : b < 8)
    (hi : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i)
    (hj : word s.mem B (8*sFn 13) = BitVec.ofNat 64 j) :
    WP isa (.block (AdxRect8.setup a b)) s fun t =>
      t.gpr .rcx = off B (slot w a+8*i) ∧
      t.gpr .rbp = off B (slot w b+8*j) ∧
      t.gpr .rsi = off B (slot w aAcc+16+8*(i+j)) ∧
      t.mem = s.mem ∧ Keep [.rax,.rdx,.rcx,.rbp,.rsi] s t := by
  have hl : ∀ k < 32, InRegions (s.rd ++ s.wr) (off B (8*k)) 8 := fun k hk =>
    hs.ld (by have := hdr_lt_slot w 8 hk; omega)
  refine WP.mono (WP.keep [.rax,.rdx,.rcx,.rbp,.rsi] (Q := fun t =>
    t.gpr .rcx = off B (slot w a+8*i) ∧
    t.gpr .rbp = off B (slot w b+8*j) ∧
    t.gpr .rsi = off B (slot w aAcc+16+8*(i+j)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hc,hp,ho,hm⟩,k⟩ => ⟨hc,hp,ho,hm,k⟩
  unfold AdxRect8.setup
  xrun [State.ea,hdr,hd,hdrOff,hl (sFn 12) (by decide),hl (sFn 13) (by decide),
    hl (sArr a) (by unfold sArr; omega),hl (sArr b) (by unfold sArr; omega),
    hl (sArr aAcc) (by decide),hi,hj,hh.harr a ha,hh.harr b hb,hh.harr aAcc (by decide),
    shift3,show (16 : BitVec 32).signExtend 64 = 16 from rfl]
  simp only [off,BitVec.ofNat_add,Nat.mul_add,BitVec.add_assoc, true_and]
  have commute (x y z : BitVec 64) : x+(y+z)=z+(x+y) := by
    rw [← BitVec.add_assoc,BitVec.add_comm]
  exact congrArg (fun x : BitVec 64 => B+(BitVec.ofNat 64 (slot w aAcc)+x))
    (commute _ _ _)

end VG.Proof.Bignum.X86_64.AdxRect8
