import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledProduct
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderSave
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCarry8Loop
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Row

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Bignum.X86_64.AdxHeader (highPad)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

theorem tailTest_ok {s : State} {B : Addr} {Z w i : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hi : i+8 ≤ w)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i) :
    WP isa (.block AdxTiledProduct.tailTest) s fun t =>
      t.zf = some (decide (i+8=w)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have ld : ∀ k < 32, InRegions (s.rd ++ s.wr) (off B (8*k)) 8 := fun k hk =>
    hs.ld (by have := hdr_lt_slot w 8 hk; omega)
  have add : BitVec.ofNat 64 i + (8 : BitVec 64) = BitVec.ofNat 64 (i+8) := by
    rw [BitVec.ofNat_add]; rfl
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (i+8=w)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨z,m⟩,k⟩ => ⟨z,m,k⟩
  unfold AdxTiledProduct.tailTest
  xrun [State.ea,hdr,hd,hdrOff,ld (sFn 12) (by decide),ld sW (by decide),
    hidx,hh.hw,add,ofNat_sub_beq (by omega : i+8<2^64) (by omega : w<2^64)]

theorem tailSetup_ok {s : State} {B : Addr} {Z w i : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hp : s.gpr .rsi = off B (rawBase w+8*(i+w))) :
    WP isa (.block AdxTiledProduct.tailSetup) s fun t =>
      t.gpr .rbp = word s.mem B carryOffset ∧
      t.gpr .rsi = off B (rawBase w+8*(i+w+8)) ∧ t.gpr .rdx = off B (highPad w) ∧
      t.gpr .rcx = 0 ∧ t.mem = s.mem ∧ Keep [.rbp,.rsi,.rdx,.rcx] s t := by
  have ld : ∀ k < 32, InRegions (s.rd ++ s.wr) (off B (8*k)) 8 := fun k hk =>
    hs.ld (by have := hdr_lt_slot w 8 hk; omega)
  have sh : BitVec.ofNat 64 w <<< (4 : Nat) = BitVec.ofNat 64 (16*w) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 w * BitVec.ofNat 64 16 = BitVec.ofNat 64 (16*w)
    rw [← BitVec.ofNat_mul,Nat.mul_comm]
  have ep : (BitVec.ofNat 64 (16*w)+off B (slot w aAcc))+(16 : BitVec 64) =
      off B (highPad w) := by
    rw [BitVec.add_comm (BitVec.ofNat 64 (16*w))]
    change off (off (off B (slot w aAcc)) (16*w)) 16 = off B (highPad w)
    rw [off_off,off_off]; congr 1; unfold highPad; omega
  have advance : off B (rawBase w+8*(i+w))+(64 : BitVec 64) =
      off B (rawBase w+8*(i+w+8)) := by
    change off (off B (rawBase w+8*(i+w))) 64 = _
    rw [off_off]; apply congrArg (off B); omega
  refine WP.mono (WP.keep [.rbp,.rsi,.rdx,.rcx] (Q := fun t =>
    t.gpr .rbp = word s.mem B carryOffset ∧ t.gpr .rsi = off B (rawBase w+8*(i+w+8)) ∧
    t.gpr .rdx = off B (highPad w) ∧ t.gpr .rcx = 0 ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨a,b,c,d,e⟩,k⟩ => ⟨a,b,c,d,e,k⟩
  unfold AdxTiledProduct.tailSetup
  xrun [State.ea,hdr,hd,hdrOff,ld (sFn 14) (by decide),ld sW (by decide),
    ld (sArr aAcc) (by decide),hh.hw,hh.harr aAcc (by decide),hp,show (64 : BitVec 32).signExtend 64 = 64 from rfl,advance,sh,ep,carryOffset]

end VG.Proof.Bignum.X86_64.AdxTiledProduct
