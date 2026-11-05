module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillABI
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Refill
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The refillable-tape search's entry on x86-64

The entry stores the arguments in the attempts' frame and the controller's
words. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.Refill

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Impl.Bignum.X86_64 (at0)

/-- The entry's stores of registers and constants. -/
def headerA (pLen qLen : Nat) : List Instr :=
  [.store (sp 48) .rdi, .store (sp 56) .rsi, .store (Impl.Dsa.X86_64.Generation.Refill.ctl 0) .rdx,
   .store (sp 64) .rcx, .store (sp 72) .r8, .store (sp 104) .rcx, .store (sp 120) .r8,
   .store (sp 88) .rcx, .mov32 .rax (.imm 0), .store (sp 96) .rax, .store (sp 80) .rax,
   .store (sp 40) .r9,
   .mov32 .rax (.imm (BitVec.ofNat 32 pLen)), .store (sp 136) .rax,
   .mov32 .rax (.imm (BitVec.ofNat 32 qLen)), .store (sp 144) .rax, .store (sp 224) .rax]

/-- The entry's loads of `state` and `state[0]`. -/
def headerB : List Instr :=
  [.mov .rax (.mem (sp (Impl.Dsa.X86_64.Generation.Refill.frameBytes + 32 + 48 + 16))),
   .store (Impl.Dsa.X86_64.Generation.Refill.ctl 1) .rax,
   .mov .rax (.mem (at0 .rax)), .store (Impl.Dsa.X86_64.Generation.Refill.ctl 2) .rax]

theorem entryHeader_eq (pLen qLen : Nat) :
    Impl.Dsa.X86_64.Generation.Refill.entryHeader pLen qLen = headerA pLen qLen ++ headerB := rfl

/-- The memory after `headerA`. -/
def chainA (m : Mem) (F : Addr) (g : Reg → BitVec 64) (pLen qLen : Nat) : Mem :=
  ((((((((((((((m.writeW (off F 48) (g .rdi)).writeW (off F 56) (g .rsi)).writeW (off F 296) (g .rdx)).writeW
    (off F 64) (g .rcx)).writeW (off F 72) (g .r8)).writeW (off F 104) (g .rcx)).writeW (off F 120) (g .r8)).writeW
    (off F 88) (g .rcx)).writeW (off F 96) (0 : BitVec 64)).writeW (off F 80) (0 : BitVec 64)).writeW
    (off F 40) (g .r9)).writeW (off F 136) (BitVec.ofNat 64 pLen)).writeW (off F 144) (BitVec.ofNat 64 qLen)).writeW
    (off F 224) (BitVec.ofNat 64 qLen))

theorem zext_ofNat {n : Nat} (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem headerA_ok {s : State} {F : Addr} (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) (hctl : ctlRegion F ∈ s.wr)
    (hb : F.toNat + 328 ≤ 2 ^ 64) {pLen qLen : Nat} (hp : pLen < 2 ^ 31) (hq : qLen < 2 ^ 31) :
    WP isa (.block (headerA pLen qLen)) s fun t =>
      t.mem = chainA s.mem F s.gpr pLen qLen ∧ Keep [.rax] s t := by
  have fs : Scr s F frameBytes := Scr.of_mem hfr (by unfold frameBytes; omega)
  have cs : Scr s (off F 296) 32 := Scr.of_mem hctl (by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have c0 : InRegions s.wr (off F 296) 8 := by simpa [off_off] using cs.st (d := 0) (by decide)
  refine WP.keep [.rax] ?_ rfl
  xrun [headerA, chainA, Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes,
    ea_sp, hsp, c0, fs.st (d := 48) (by decide), fs.st (d := 56) (by decide), fs.st (d := 64) (by decide),
    fs.st (d := 72) (by decide), fs.st (d := 104) (by decide), fs.st (d := 120) (by decide),
    fs.st (d := 88) (by decide), fs.st (d := 96) (by decide), fs.st (d := 80) (by decide),
    fs.st (d := 40) (by decide), fs.st (d := 136) (by decide), fs.st (d := 144) (by decide),
    fs.st (d := 224) (by decide), Nat.mul_zero, Nat.add_zero, zext_ofNat (by omega : pLen < 2 ^ 32),
    zext_ofNat (by omega : qLen < 2 ^ 32), zext_ofNat (by decide : 0 < 2 ^ 32)]
  rfl

end VG.Proof.Dsa.X86_64.Generation.Refill
