module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomClear
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame

/-! Wipe the nonce and publish the consumed-byte count and return status. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomPublishMem (m : Mem) (B : Addr) : Mem :=
  (randomClearMem m B).writeW (word m B Random.oUsedPtr) (word m B Random.oUsed)

theorem random_publish_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hw : InRegions s.wr (word s.mem B Random.oUsedPtr) 8)
    (hsep : Mem.Sep (off B Random.oStatus) 8 (word s.mem B Random.oUsedPtr) 8) :
    WP isa (.block (Random.clearNonce ++
      ([.mov .rdx (.mem (Random.sp Random.oUsedPtr)), .mov .rax (.mem (Random.sp Random.oUsed)),
       .store { base := .rdx } .rax, .mov .rax (.mem (Random.sp Random.oStatus))] : List Instr))) s fun t =>
      t.gpr .rax = word s.mem B Random.oStatus ∧ t.mem = randomPublishMem s.mem B ∧
      Keep [.rax, .rdx] s t := by
  have hstatus (m : Mem) : word (m.writeW (word s.mem B Random.oUsedPtr)
      (word s.mem B Random.oUsed)) B Random.oStatus = word m B Random.oStatus :=
    Mem.readW_writeW_sep hsep (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (random_clear_ok hs hsp) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.2.2
  have husp := (hku.gpr (by decide)).trans hsp
  have hp : word u.mem B Random.oUsedPtr = word s.mem B Random.oUsedPtr := by
    rw [hum]; exact (random_clear_outside _ _).word (by decide) (by decide)
  have hu : word u.mem B Random.oUsed = word s.mem B Random.oUsed := by
    rw [hum]; exact (random_clear_outside _ _).word (by decide) (by decide)
  have hz : word u.mem B Random.oStatus = word s.mem B Random.oStatus := by
    rw [hum]; exact (random_clear_outside _ _).word (by decide) (by decide)
  have huw : InRegions u.wr (word s.mem B Random.oUsedPtr) 8 := by rw [hku.2.2]; exact hw
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
      t.gpr .rax = word s.mem B Random.oStatus ∧ t.mem = randomPublishMem s.mem B) ?_ rfl)
    fun t ⟨h, hkt⟩ => ⟨h.1, h.2, (hku.trans hkt).mono (by decide)⟩
  xrun [random_ea_sp, random_ea_base, husp,
    hus.ld (d := Random.oUsedPtr) (by decide), hus.ld (d := Random.oUsed) (by decide),
    hus.ld (d := Random.oStatus) (by decide), hp, hu, huw, hstatus, hz]
  rw [hum]
  rfl

end VG.Proof.Dsa.X86_64
