module

public import VerifiedGarbage.Impl.Dsa.AArch64.ProbablePrime
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # The probable-prime test's octets read and status, as the function returns them -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.ProbablePrime VG.Impl.RsaKeyGen.AArch64.Candidate

theorem exit_ok {u : State} {B F U used st : Addr} (hx0 : u.gpr .x0 = B) (hsp : u.sp = F)
    (hrU : InRegions (u.rd ++ u.wr) (off B (8 * kUsed)) 8) (hrS : InRegions (u.rd ++ u.wr) (off B (8 * kStat)) 8)
    (hrF : InRegions (u.rd ++ u.wr) (off F usedSlot) 8) (hwU : InRegions u.wr U 8)
    (hU : word u.mem F usedSlot = U) (hused : word u.mem B (8 * kUsed) = used)
    (hst : word u.mem B (8 * kStat) = st) (hsep : Mem.Sep (off B (8 * kStat)) 8 U 8) :
    WP isa (.block exit) u fun t =>
      t.mem = u.mem.writeW U used ∧ t.gpr .x0 = st - (st >>> 1) ∧ Keep [.x0, .x3, .x4] u t := by
  have hread : (u.mem.writeW U used).readW (off B (8 * kStat)) 64 = st := by
    rw [Mem.readW_writeW_sep hsep (by decide)]; exact hst
  have run : WP isa (.block exit) u fun t => t.mem = u.mem.writeW U used ∧ t.gpr .x0 = st - (st >>> 1) := by
    unfold exit usedSlot at *
    simp only [word, off, kUsed, kStat, VG.Impl.Bignum.sFn] at hrU hrS hrF hU hused hst hread
    rw [← hx0] at hrU hrS hused hst hread
    rw [← hsp] at hrF hU
    brun [State.write, exec_ldrSp (by decide : 136 % 8 = 0 ∧ 136 < 32768), hrU, hrS, hrF, hwU, hused, hread, hU, kUsed, kStat, BitVec.add_zero,
      VG.Impl.Bignum.sFn]
    done
  exact WP.mono (WP.keep [.x0, .x3, .x4] run (by decide)) fun t ⟨⟨hm, hx⟩, k⟩ => ⟨hm, hx, k⟩

/-- The test's 0, 1 and 3 are the function's 0, 1 and 2. -/
theorem status_halve (b : Option Bool) :
    let st : BitVec 64 := BitVec.ofNat 64 (match b with | none => 0 | some true => 1 | some false => 3)
    st - (st >>> 1) = BitVec.ofNat 64 (match b with | none => 0 | some true => 1 | some false => 2) := by
  rcases b with _ | _ | _ <;> decide

end VG.Proof.Dsa.AArch64.ProbablePrime
