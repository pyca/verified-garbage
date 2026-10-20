module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomClear
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Wipe the nonce and publish the consumed-byte count and return status. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomPublishMem (m : Mem) (B : Addr) : Mem :=
  (randomClearMem m B).writeW (word m B Random.oUsedPtr) (word m B Random.oUsed)

theorem random_publish_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hw : InRegions s.wr (word s.mem B Random.oUsedPtr) 8)
    (hsep : Mem.Sep (off B Random.oStatus) 8 (word s.mem B Random.oUsedPtr) 8) :
    WP isa (.block (Random.clearNonce ++
      ([.ldrSp .x2 Random.oUsedPtr, .ldrSp .x0 Random.oUsed,
       .str .x .x0 .x2 0, .ldrSp .x0 Random.oStatus] : List Instr))) s fun t =>
      t.gpr .x0 = word s.mem B Random.oStatus ∧ t.mem = randomPublishMem s.mem B ∧
      Keep [.x0, .x2, .x15] s t := by
  have hstatus (m : Mem) : word (m.writeW (word s.mem B Random.oUsedPtr)
      (word s.mem B Random.oUsed)) B Random.oStatus = word m B Random.oStatus :=
    Mem.readW_writeW_sep hsep (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (random_clear_ok hs hsp) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.wr
  have husp := hku.sp.trans hsp
  have hp : word u.mem B Random.oUsedPtr = word s.mem B Random.oUsedPtr := by
    rw [hum]; exact (random_clear_outside _ _).word (by decide) (by decide)
  have hu : word u.mem B Random.oUsed = word s.mem B Random.oUsed := by
    rw [hum]; exact (random_clear_outside _ _).word (by decide) (by decide)
  have hz : word u.mem B Random.oStatus = word s.mem B Random.oStatus := by
    rw [hum]; exact (random_clear_outside _ _).word (by decide) (by decide)
  have huw : InRegions u.wr (word s.mem B Random.oUsedPtr) 8 := by rw [hku.wr]; exact hw
  refine WP.mono (WP.keep [.x0, .x2] (Q := fun t =>
      t.gpr .x0 = word s.mem B Random.oStatus ∧ t.mem = randomPublishMem s.mem B) ?_ rfl rfl rfl)
    fun t ⟨h, hkt⟩ => ⟨h.1, h.2, (hku.trans hkt).mono (by decide)⟩
  brun [exec_ldrSp (show Random.oUsedPtr % 8 = 0 ∧ Random.oUsedPtr < 32768 by decide),
    exec_ldrSp (show Random.oUsed % 8 = 0 ∧ Random.oUsed < 32768 by decide),
    exec_ldrSp (show Random.oStatus % 8 = 0 ∧ Random.oStatus < 32768 by decide), husp,
    hus.ld (d := Random.oUsedPtr) (by decide), hus.ld (d := Random.oUsed) (by decide),
    hus.ld (d := Random.oStatus) (by decide), hp, hu, huw, hstatus, hz]
  rw [hum]
  rfl

end VG.Proof.Dsa.AArch64
