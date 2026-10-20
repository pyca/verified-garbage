module

public import VerifiedGarbage.Proof.Seed.X86.Ecb
public import VerifiedGarbage.Proof.Seed.ModeCipher
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Impl.Seed.X86.Modes
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Seed.X86.Prologue
import VerifiedGarbage.Proof.Seed.X86.Crypt8
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.AesCtr.Inc
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.Linear
public import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Proof.Modes.Steps
public import VerifiedGarbage.Proof.Modes.X86.Counter
public import VerifiedGarbage.Proof.Modes.X86.Ops
public import VerifiedGarbage.Proof.Seed.G16
public import VerifiedGarbage.Proof.Seed.Memory
public import VerifiedGarbage.Proof.Seed.X86.Crypt8
public import VerifiedGarbage.Spec.Seed.Contract
import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Linear
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Modes.Steps
import VerifiedGarbage.Proof.Modes.X86.Counter
import VerifiedGarbage.Proof.Modes.X86.Ops
import VerifiedGarbage.Proof.Seed.G16
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Spec.Seed.Contract

/-!
# SEED's core for the modes on x86 (32-bit)

`dirCoreSpec d`: SEED's core for the direction `d` (`Impl.Seed.X86.dirCore d`)
meets what the modes need of a core (`Proof.Modes.X86.CoreSpec`), with the
key a schedule, read through the first stack argument, its cipher
`Spec.Seed.cipher` for encryption and `Spec.Seed.invCipher` for decryption,
and the key ready when the table of round keys in `d`'s order is in the
scratch buffer (`ReadyAt`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Seed.X86
open VG.Impl.Aes.X86 (argOp sb)
open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout)
open VG.Proof.Seed (scheduleAt_congr_at bytesAt_eq dirKeys dirCipher dirCipher_bytes crypt_congr)
open VG.Spec.Seed (Direction)
open VG.Spec.Aes (bytesAt)

/-- The schedule, at the address in the first stack argument, outside the
regions `rs`, as is that argument. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Seed.Schedule) : Prop :=
  ∃ p : BitVec 32, InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4 ∧ s.mem.readW (s.ea (argOp 0)) 32 = p ∧
    k = Spec.Seed.scheduleAt s.mem (p.setWidth 64) ∧ (⟨p.setWidth 64, 128⟩ : Region) ∈ s.rd ++ s.wr ∧
    p.toNat + 128 ≤ 2 ^ 32 ∧ (∀ r ∈ rs, Region.Disjoint ⟨p.setWidth 64, 128⟩ r) ∧
    ∀ r ∈ rs, Region.Disjoint ⟨s.ea (argOp 0), 4⟩ r

/-- Entry `j` of the table of round keys in the scratch buffer at `B`: two
words. -/
def entryAt (m : Mem) (B : BitVec 32) (j : Nat) : Spec.Seed.Word × Spec.Seed.Word :=
  (m.readW (wordAddr B (tableSlot + 2 * j)) 32, m.readW (wordAddr B (tableSlot + 2 * j + 1)) 32)

/-- The table of round keys in the order of `d`. -/
def ReadyAt (d : Direction) (m : Mem) (B : BitVec 32) (k : Spec.Seed.Schedule) : Prop :=
  ∀ j < 16, entryAt m B j = dirKeys d k j

theorem dirCore_slots (d : Direction) : (dirCore d).slots = 206 := rfl
theorem dirCore_total (d : Direction) : (dirCore d).total = 216 := rfl

/-- A table word, outside the regions apart from the core or within its
buffer. -/
theorem table_keep {d : Direction} {B : BitVec 32} (hfit : B.toNat + 4 * (dirCore d).total ≤ 2 ^ 32)
    {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B))
    {i : Nat} (hi : i < 32) : m'.readW (wordAddr B (tableSlot + i)) 32 = m.readW (wordAddr B (tableSlot + i)) 32 := by
  rw [dirCore_total] at hfit
  rw [slot_addr (by rw [tableSlot_eq]; omega)]
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases hd r hr with h | h
  · exact h.symm.sub_right (VG.Offset.sub_base _ (by simp only [dirCore, slots_eq, tableSlot_eq]; omega)) |>.symm
  · refine Region.Disjoint.sub_right ?_ h
    exact VG.Offset.disjoint _ (.inr (by simp only [dirCore, tailSlot_eq, tableSlot_eq]; omega))
      (by rw [tableSlot_eq]; omega) (by simp only [dirCore, tailSlot_eq]; omega)

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Seed.Schedule} (h : KeyArgs s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨p, hin, hp, rfl, hsch, hfit, hdis, hadis⟩ := h
  have hea : s'.ea (argOp 0) = s.ea (argOp 0) := by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  refine ⟨p, by rw [hrd, hwr, hea]; exact hin, ?_, ?_, by rw [hrd, hwr]; exact hsch, hfit, hdis,
    by rw [hea]; exact hadis⟩
  · rw [hea, hf.readW (Region.contains_self _ _) hadis (by decide), hp]
  · exact (scheduleAt_congr_at fun i hi => hf.bytes (R := ⟨p.setWidth 64, 128⟩) hdis (by show 128 ≤ 2 ^ 64; omega) hi).symm

/-- The scratch buffer of the modes is one for the ECB code. -/
theorem scrIn_of {s : State} {B : BitVec 32} {d : Direction}
    (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total) : ScrIn s.wr B :=
  have hf := hs.fit
  ⟨⟨216, by rw [slots_eq]; decide, hf, hs.wr⟩, by rw [dirCore_total] at hf; rw [slots_eq]; omega⟩

theorem prepare_wp (d : Direction) {s : State} {B : BitVec 32} {rs : List Region} {k : Spec.Seed.Schedule}
    (hB : s.gpr VG.Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total)
    (hR : (⟨B.setWidth 64, 4 * (dirCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k)
    (_ : (dirCore d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (dirCore d).prepare s fun s' => ReadyAt d s'.mem B k ∧ s'.gpr VG.Impl.Modes.X86.sb = B ∧
      s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion (dirCore d) B, stkRegion (s.gpr .esp) (dirCore d).stack] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hin, hp, rfl, hsch, hfit, hdis, -⟩ := hk
  obtain ⟨s₁, e₁, c₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .ecx 0 hin
  have hpre : SchedPre s₁ B p :=
    ⟨by rw [o₁ _ (by decide)]; exact hB, by rw [wr₁]; exact scrIn_of hs, by rw [c₁, hp],
      by rw [rd₁, wr₁]; exact hsch, hfit,
      (hdis _ hR).sub_right (Region.sub_prefix (by rw [dirCore_total, slots_eq]; decide))⟩
  obtain ⟨s₂, e₂, t₂, -, g₂, rd₂, wr₂, f₂⟩ := table_ok d hpre
  have e : runBlock isa (keyTable d) s = some s₂ := by
    rw [keyTable_eq, show Instr.mov .ecx (.mem (argOp 0)) :: loadsCode (tableMoves d) =
        [.mov .ecx (.mem (argOp 0))] ++ loadsCode (tableMoves d) from rfl, runBlock_append, e₁,
      Option.bind_some, e₂]
  refine WP.of_runBlock ⟨s₂, e, fun j hj => ?_, ?_, ?_, ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · have hk := keyPairs_eq d s₁.mem hfit hj
    rw [m₁] at hk
    simp only [entryAt]
    rw [show tableSlot + 2 * j + 1 = tableSlot + (2 * j + 1) by omega, t₂ (2 * j) (by omega),
      t₂ (2 * j + 1) (by omega), m₁]
    cases d <;> exact hk
  · rw [g₂ _ (by decide), o₁ _ (by decide)]; exact hB
  · rw [g₂ _ (by decide), o₁ _ (by decide)]
  · rw [← m₁]
    exact f₂.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [dirCore]

theorem crypt_wp (d : Direction) {s : State} {B : BitVec 32} {k : Spec.Seed.Schedule}
    (hB : s.gpr VG.Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total)
    (hr : ReadyAt d s.mem B k) (_ : (dirCore d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr VG.Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      ReadyAt d s'.mem B k ∧ Frame [coreRegion (dirCore d) B, stkRegion (s.gpr .esp) (dirCore d).stack] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, bytesAt s'.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw) =
        dirCipher d k (bytesAt s.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hB' : s.gpr sb = B := hB
  have hfB := hs.fit
  rw [dirCore_total] at hfB
  have hroom : Room s := ⟨by rw [hB']; exact ⟨216, by rw [slots_eq]; decide, hfB, hs.wr⟩,
    by rw [hB', slots_eq]; omega⟩
  refine WP.mono (crypt8_wp hroom) fun s' ⟨hb', _, rd', wr', sb', esp', sl', f'⟩ => ?_
  have base'' : s'.gpr sb = B := by rw [sb', hB']
  have fr : Frame [⟨B.setWidth 64, 4 * tableSlot⟩] s.mem s'.mem := by rw [hB'] at f'; exact f'
  -- The table is unchanged.
  have hT : ∀ i < 32, s'.mem.readW (wordAddr B (tableSlot + i)) 32 = s.mem.readW (wordAddr B (tableSlot + i)) 32 :=
    fun i hi => by
      have := sl' (tableSlot + i) (by omega) (by rw [slots_eq, tableSlot_eq]; omega)
      simp only [slotW, sb', hB'] at this
      exact this
  have hent : ∀ j < 16, entryAt s'.mem B j = entryAt s.mem B j := fun j hj => by
    simp only [entryAt]
    rw [show tableSlot + 2 * j + 1 = tableSlot + (2 * j + 1) by omega, hT _ (by omega), hT _ (by omega)]
  -- The table's keys are the direction's.
  have hkeys : ∀ j < 16, tableKeys s j = dirKeys d k j := fun j hj => by
    rw [← hr j hj]
    simp only [tableKeys, entryAt, slotW, hB']
  refine ⟨base'', esp', fun j hj => by rw [hent j hj]; exact hr j hj,
    fr.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by simp only [dirCore, slots_eq, tableSlot_eq]; omega)⟩,
    fun j hj => ?_, rd', wr'⟩
  have e₁ := hb' j hj
  simp only [tailBlock, base'', hB'] at e₁
  have ha : blkAddr (dirCore d) B j = B.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * j) := by
    simp only [blkAddr, dirCore, VG.Offset.add_add]
  rw [show 4 * (dirCore d).bw = 16 from rfl, ha, dirCipher_bytes, bytesAt_eq, e₁,
    crypt_congr hkeys]

/-- SEED's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Direction) : CoreSpec (dirCore d) where
  Key := Spec.Seed.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready s B k := ReadyAt d s.mem B k ∧ B.toNat + 4 * (dirCore d).total ≤ 2 ^ 32
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, dirCore]
  layout := ⟨by simp only [dirCore]; decide, .inr rfl, by simp only [dirCore, slots_eq, tailSlot_eq]; omega,
    by simp only [dirCore]; omega⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame h _ _ _ _ hf _ hd := ⟨fun j hj => by
      rw [← h.1 j hj]
      simp only [entryAt]
      rw [show tableSlot + 2 * j + 1 = tableSlot + (2 * j + 1) by omega,
        table_keep h.2 hf hd (show 2 * j < 32 by omega), table_keep h.2 hf hd (show 2 * j + 1 < 32 by omega)],
    h.2⟩
  prepare_wp hB hs hR hk hst := WP.mono (prepare_wp d hB hs hR hk hst) fun _ ⟨r, h⟩ => ⟨⟨r, hs.fit⟩, h⟩
  crypt_wp hB hs hr hst := WP.mono (crypt_wp d hB hs hr.1 hst) fun _ ⟨b, e, r, h⟩ => ⟨b, e, ⟨r, hr.2⟩, h⟩

end VG.Proof.Seed.X86
