module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.Ctx
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.GeFlag
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# The blinded Miller–Rabin loop on PPC64LE: after a passing round

`passed_ok`: one more witness (`hIdx := k + 1`), and `hStat := 1` if there
are at least 16 and the uniform ones (`hUni`) reach `hChecks`, else 4.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Blinded

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.MillerRabin.PPC64LE.Search VG.Impl.MillerRabin.PPC64LE.Blinded
open VG.Proof.MillerRabin.PPC64LE (Env)
open VG.Proof.MillerRabin.PPC64LE.Search (ge_val)
open VG.Proof.Bignum (slot Frm word off writeW_outside word_writeW_self)

/-- `(f₁ & f₂) · 3` subtracted from 4, for flags `f₁`, `f₂`: 1 if both, else 4. -/
theorem stat_val (p q : Prop) [Decidable p] [Decidable q] :
    BitVec.ofNat 64 4 - (BitVec.ofNat 64 (if p then 1 else 0) &&& BitVec.ofNat 64 (if q then 1 else 0)) *
        BitVec.ofNat 64 3 = BitVec.ofNat 64 (if q ∧ p then 1 else 4) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] <;> decide

/-- The registers `passed` writes. -/
def passedRegs : List Reg := [.r0, .r3, .r4, .r5, .r7]

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
  refine WP.keep _ ?_ (by decide)
  have r176 : s.mem.readW (B + 176#64) 64 = BitVec.ofNat 64 k := hk
  have o176 := writeW_outside s.mem B (BitVec.ofNat 64 (k + 1)) (d := 176) (by omega)
  have r32 : (s.mem.writeW (B + 176#64) (BitVec.ofNat 64 (k + 1))).readW (B + 32#64) 64 = BitVec.ofNat 64 u :=
    (o176.word (by omega) (by omega)).trans hu
  have r168 : (s.mem.writeW (B + 176#64) (BitVec.ofNat 64 (k + 1))).readW (B + 168#64) 64 = BitVec.ofNat 64 ch :=
    (o176.word (by omega) (by omega)).trans hch
  have ek : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by rw [BitVec.ofNat_add]
  simp only [passed, geFlag, ldh, sth, hIdx, hUni, hChecks, hStat]
  prun [e.h31, hs.ld (d := 176) (n := 8) (by omega), hs.st (d := 176) (n := 8) (by omega),
    hs.ld (d := 32) (n := 8) (by omega), hs.ld (d := 168) (n := 8) (by omega), hs.st (d := 160) (n := 8) (by omega),
    r176, ek, r32, r168, ge_val (show k + 1 < 2 ^ 64 by omega) (show 16 < 2 ^ 63 by decide),
    ge_val (show u < 2 ^ 64 by omega) hch']
  have hv : ∀ x : BitVec 64, (x = BitVec.ofNat 64 (if ch ≤ u then 1 else 0) &&& BitVec.ofNat 64 (if 15 ≤ k then 1 else 0)
      + 0#64) → 4#64 - x * 3#64 = BitVec.ofNat 64 (if 15 ≤ k ∧ ch ≤ u then 1 else 4) := by
    rintro x rfl
    by_cases h1 : ch ≤ u <;> by_cases h2 : 15 ≤ k <;> simp [h1, h2] <;> decide
  rw [hv _ rfl]
  refine ⟨?_, ?_, ?_⟩
  · rw [show (B + 160#64 : Addr) = off B 160 from rfl, (writeW_outside _ _ _ (by omega)).word (by omega) (by omega),
      show (B + 176#64 : Addr) = off B 176 from rfl, word_writeW_self]
  · rw [show (B + 160#64 : Addr) = off B 160 from rfl, word_writeW_self]
  · exact Frm.trans (Frm.of_outside (o := 176) (n := 8) (writeW_outside _ _ _ (by omega)) (by simp))
      (Frm.of_outside (o := 160) (n := 8) (writeW_outside _ _ _ (by omega)) (by simp))

end VG.Proof.MillerRabin.PPC64LE.Blinded
