module

public import VerifiedGarbage.Impl.Dsa.AArch64.Random
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Accesses to the randomized-signing frame. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_load {s : State} {B : Addr} {r : Reg} {d : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hd : d + 8 ≤ Random.frameBytes) (ha : d % 8 = 0) :
    exec (.ldrSp r d) s = some (s.write .x r (word s.mem B d)) := by
  have hp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 d) 8 := by
    rw [hsp]; exact hs.ld hd
  simpa only [hsp] using exec_ldrSp ⟨ha, by unfold Random.frameBytes at hd; omega⟩ hp

theorem random_rangeInit_ok {s : State} {B q : Addr} {l n : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 l)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 n)
    (hq : word s.mem B Random.oQ = q) :
    WP isa (.block Random.rangeInit) s fun t =>
      t.gpr .x2 = off B (Random.oNonce + l) ∧
      t.gpr .x12 = q + BitVec.ofNat 64 n ∧ t.gpr .x9 = BitVec.ofNat 64 n ∧
      t.gpr .x8 = 0 ∧ t.gpr .x10 = 0 ∧ t.mem = s.mem ∧
      Keep [.x2, .x4, .x8, .x9, .x10, .x12] s t := by
  refine WP.mono (WP.keep [.x2, .x4, .x8, .x9, .x10, .x12] (Q := fun t =>
      t.gpr .x2 = off B (Random.oNonce + l) ∧
      t.gpr .x12 = q + BitVec.ofNat 64 n ∧ t.gpr .x9 = BitVec.ofNat 64 n ∧
      t.gpr .x8 = 0 ∧ t.gpr .x10 = 0 ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun _ ⟨⟨hd, hq, hn, h8, h9, hm⟩, hk⟩ => ⟨hd, hq, hn, h8, h9, hm, hk⟩
  unfold Random.rangeInit
  brun [exec_addSp (show Random.oNonce < 4096 by decide), hsp,
    exec_ldrSp (show Random.oQLen % 8 = 0 ∧ Random.oQLen < 32768 by decide),
    exec_ldrSp (show Random.oWidth % 8 = 0 ∧ Random.oWidth < 32768 by decide),
    exec_ldrSp (show Random.oQ % 8 = 0 ∧ Random.oQ < 32768 by decide),
    hs.ld (d := Random.oQLen) (by decide), hs.ld (d := Random.oWidth) (by decide),
    hs.ld (d := Random.oQ) (by decide), hl, hn, hq]

end VG.Proof.Dsa.AArch64
