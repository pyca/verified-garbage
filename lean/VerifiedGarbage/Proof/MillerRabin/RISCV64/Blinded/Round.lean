module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Ctx
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.Sieve
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# The blinded Miller–Rabin loop on RISC-V: after a passing round

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Blinded/Round.lean`): `passed_ok`,
one more witness (`hIdx := k + 1`), and `hStat := 1` if there are at least 16
and the uniform ones (`hUni`) reach `hChecks`, else 4.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Blinded

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.MillerRabin.RISCV64.Search VG.Impl.MillerRabin.RISCV64.Blinded
open VG.Proof.MillerRabin.RISCV64 (Env)
open VG.Proof.MillerRabin.RISCV64.Search (ge_val)
open VG.Proof.Bignum (slot Frm word off writeW_outside word_writeW_self)

/-- The registers `passed` writes. -/
def passedRegs : List Reg := [.t2, .t3, .t4, .t5]

/-- After a passing round, from `k` witnesses of which `u` uniform. -/
theorem passed_ok {s : State} {B : Addr} {Z w k u ch : Nat} (e : Env s B Z w)
    (hk : word s.mem B (8 * hIdx) = BitVec.ofNat 64 k) (hu : word s.mem B (8 * hUni) = BitVec.ofNat 64 u)
    (hch : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch) (hk' : k + 1 < 2 ^ 63) (hu' : u < 2 ^ 63)
    (hch' : ch < 2 ^ 63) :
    WP isa (.block passed) s fun s' =>
      (word s'.mem B (8 * hIdx) = BitVec.ofNat 64 (k + 1) ∧
        word s'.mem B (8 * hStat) = BitVec.ofNat 64 (if 16 ≤ k + 1 ∧ ch ≤ u then 1 else 4) ∧
        Frm B [(8 * hIdx, 8), (8 * hStat, 8)] s.mem s'.mem) ∧ Keep passedRegs s s' := by
  have hs := e.hs
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have r176 : s.mem.readW (B + 176#64) 64 = BitVec.ofNat 64 k := hk
  have o176 := writeW_outside s.mem B (BitVec.ofNat 64 (k + 1)) (d := 176) (by omega)
  have r32 : (s.mem.writeW (B + 176#64) (BitVec.ofNat 64 (k + 1))).readW (B + 32#64) 64 = BitVec.ofNat 64 u :=
    (o176.word (by omega) (by omega)).trans hu
  have r168 : (s.mem.writeW (B + 176#64) (BitVec.ofNat 64 (k + 1))).readW (B + 168#64) 64 = BitVec.ofNat 64 ch :=
    (o176.word (by omega) (by omega)).trans hch
  have ek : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by rw [← BitVec.ofNat_add]
  have g1 := ge_val (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 16)
  have g2 := ge_val (BitVec.ofNat 64 u) (BitVec.ofNat 64 ch)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at g1
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at g2
  simp only [passed, geFlag, ldh, sth, hIdx, hUni, hChecks, hStat]
  brun [e.s6, hs.ld (d := 176) (n := 8) (by omega), hs.al8 (d := 176) (by omega) (by decide),
    hs.st (d := 176) (n := 8) (by omega), hs.ld (d := 32) (n := 8) (by omega), hs.al8 (d := 32) (by omega) (by decide),
    hs.ld (d := 168) (n := 8) (by omega), hs.al8 (d := 168) (by omega) (by decide),
    hs.st (d := 160) (n := 8) (by omega), hs.al8 (d := 160) (by omega) (by decide),
    r176, exec_li (show imm12 16 by decide), exec_li (show imm12 3 by decide),
    exec_li (show imm12 4 by decide)]
  simp only [ek, r32, r168]
  rw [show (1#64 : BitVec 64) = BitVec.ofInt 64 1 from rfl, g1, g2]
  have hv : BitVec.ofNat 64 4 - (BitVec.ofNat 64 (if ch ≤ u then 1 else 0) &&&
      BitVec.ofNat 64 (if 16 ≤ k + 1 then 1 else 0)) * BitVec.ofNat 64 3 =
      BitVec.ofNat 64 (if 15 ≤ k ∧ ch ≤ u then 1 else 4) := by
    by_cases h1 : ch ≤ u <;> by_cases h2 : 15 ≤ k <;> simp [h1, h2] <;> decide
  rw [hv]
  refine ⟨?_, ?_, ?_⟩
  · rw [show (B + 160#64 : Addr) = off B 160 from rfl, (writeW_outside _ _ _ (by omega)).word (by omega) (by omega),
      show (B + 176#64 : Addr) = off B 176 from rfl, word_writeW_self]
  · rw [show (B + 160#64 : Addr) = off B 160 from rfl, word_writeW_self]
  · exact Frm.trans (Frm.of_outside (o := 176) (n := 8) (writeW_outside _ _ _ (by omega)) (by simp))
      (Frm.of_outside (o := 160) (n := 8) (writeW_outside _ _ _ (by omega)) (by simp))

end VG.Proof.MillerRabin.RISCV64.Blinded
