import VerifiedGarbage.Proof.Sm4.X86.Ecb
import VerifiedGarbage.Proof.Modes.X86.Core
import VerifiedGarbage.Impl.Sm4.X86.Modes
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Spec.Sm4.Cbc

/-!
# SM4's core for the modes on x86 (32-bit)

`dirCoreSpec d`: SM4's core for the direction `d` (`Impl.Sm4.X86.dirCore d`)
meets what the modes need of a core (`Proof.Modes.X86.CoreSpec`), with the
key a schedule, read through the first stack argument, its cipher
`Spec.Sm4.cipher` for encryption and `Spec.Sm4.invCipher` for decryption,
and the key ready when the table of round keys in `d`'s order is in the
scratch buffer.
-/

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Impl.Aes.X86 (argOp sb)
open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout)
open VG.Proof.Sm4 (scheduleAt_congr bytesAt_eq_blockAt ofFn_toList crypt_eq specDirX86)
open VG.Spec.Aes (bytesAt)

/-- The schedule, at the address in the first stack argument, outside the
regions `rs`, as is that argument. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Sm4.Schedule) : Prop :=
  ∃ p : BitVec 32, InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4 ∧ s.mem.readW (s.ea (argOp 0)) 32 = p ∧
    k = Spec.Sm4.scheduleAt s.mem (p.setWidth 64) ∧ (⟨p.setWidth 64, 128⟩ : Region) ∈ s.rd ++ s.wr ∧
    p.toNat + 128 ≤ 2 ^ 32 ∧ (∀ r ∈ rs, Region.Disjoint ⟨p.setWidth 64, 128⟩ r) ∧
    ∀ r ∈ rs, Region.Disjoint ⟨s.ea (argOp 0), 4⟩ r

/-- The table of round keys in the order of `d`. -/
def ReadyAt (d : Dir) (m : Mem) (B : BitVec 32) (k : Spec.Sm4.Schedule) : Prop :=
  ∀ e < 32, W32.WordRel (entryW m B e) fun _ => dirKeys d k e

/-- The cipher of the direction `d`. -/
def dirCipher : Dir → Spec.Sm4.Schedule → Spec.Cbc.Cipher
  | .encrypt => Spec.Sm4.cipher
  | .decrypt => Spec.Sm4.invCipher

/-- The cipher of `d` on the 16 bytes at `p`: the 32 rounds with the round
keys in `d`'s order. -/
theorem dirCipher_bytes (d : Dir) (k : Spec.Sm4.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (bytesAt m p 16) =
      (outBlock (quads .enc (dirKeys d k) 8 (ofBlock (Spec.Sm4.blockAt m p)))).toList := by
  cases d
  · rw [dirCipher, Spec.Sm4.cipher, bytesAt_eq_blockAt, ofFn_toList, Spec.Sm4.encryptBlock, crypt_eq]; rfl
  · rw [dirCipher, Spec.Sm4.invCipher, bytesAt_eq_blockAt, ofFn_toList, Spec.Sm4.decryptBlock, crypt_eq]; rfl

theorem dirCore_slots (d : Dir) : (dirCore d).slots = 352 := rfl
theorem dirCore_total (d : Dir) : (dirCore d).total = 362 := rfl

/-- An entry's word, outside the regions apart from the core or within its
buffer. -/
theorem entry_keep {d : Dir} {B : BitVec 32} (hfit : B.toNat + 4 * (dirCore d).total ≤ 2 ^ 32) {m m' : Mem}
    {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B))
    {e j : Nat} (he : e < 32) (hj : j < 8) : entryW m' B e j = entryW m B e j := by
  rw [dirCore_total] at hfit
  simp only [entryW]
  rw [slot_addr (by rw [tableSlot_eq]; omega)]
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases hd r hr with h | h
  · exact h.symm.sub_right (VG.Offset.sub_base _ (by simp only [dirCore, tableEnd_eq, tableSlot_eq]; omega)) |>.symm
  · refine Region.Disjoint.sub_right ?_ h
    exact VG.Offset.disjoint _ (.inr (by simp only [dirCore, tailSlot_eq, tableSlot_eq]; omega))
      (by rw [tableSlot_eq]; omega) (by simp only [dirCore, tailSlot_eq]; omega)

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Sm4.Schedule} (h : KeyArgs s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨p, hin, hp, rfl, hsch, hfit, hdis, hadis⟩ := h
  have hea : s'.ea (argOp 0) = s.ea (argOp 0) := by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  refine ⟨p, by rw [hrd, hwr, hea]; exact hin, ?_, ?_, by rw [hrd, hwr]; exact hsch, hfit, hdis,
    by rw [hea]; exact hadis⟩
  · rw [hea, hf.readW (Region.contains_self _ _) hadis (by decide), hp]
  · exact (scheduleAt_congr fun i hi => hf.bytes (R := ⟨p.setWidth 64, 128⟩) hdis (by show 128 ≤ 2 ^ 64; omega) hi).symm

theorem prepare_wp (d : Dir) {s : State} {B : BitVec 32} {rs : List Region} {k : Spec.Sm4.Schedule}
    (hB : s.gpr VG.Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total)
    (hR : (⟨B.setWidth 64, 4 * (dirCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) (_ : (dirCore d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (dirCore d).prepare s fun s' => ReadyAt d s'.mem B k ∧ s'.gpr VG.Impl.Modes.X86.sb = B ∧
      s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion (dirCore d) B, stkRegion (s.gpr .esp) (dirCore d).stack] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hin, hp, rfl, hsch, hfit, hdis, -⟩ := hk
  have hfB := hs.fit
  rw [dirCore_total] at hfB
  have hpre : SchedPre s B p :=
    ⟨hB, ⟨⟨362, by rw [slots_eq]; decide, hfB, hs.wr⟩, by rw [slots_eq]; omega⟩, hsch, hfit,
      (hdis _ hR).sub_right (Region.sub_prefix (by rw [dirCore_total, slots_eq]; decide))⟩
  refine WP.mono (keys_wp d hpre hin hp) fun s' k' => ?_
  refine ⟨fun e he => ?_, k'.pre.base, k'.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide), (k'.frame.mono fun r hr => by simp at hr; subst hr; simp [dirCore]), k'.rd, k'.wr⟩
  have := k'.key.keys e he
  rw [k'.pre.base] at this
  exact this

theorem crypt_wp (d : Dir) {s : State} {B : BitVec 32} {k : Spec.Sm4.Schedule} (hB : s.gpr VG.Impl.Modes.X86.sb = B)
    (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total) (hr : ReadyAt d s.mem B k) (_ : (dirCore d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr VG.Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      ReadyAt d s'.mem B k ∧ Frame [coreRegion (dirCore d) B, stkRegion (s.gpr .esp) (dirCore d).stack] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, bytesAt s'.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw) =
        dirCipher d k (bytesAt s.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfB := hs.fit
  rw [dirCore_total] at hfB
  have hkey : KeyCtx s (dirKeys d k) :=
    { scr := by rw [show s.gpr sb = B from hB]; exact ⟨⟨362, by rw [slots_eq]; decide, hfB, hs.wr⟩, by rw [slots_eq]; omega⟩
      keys := fun e he => by rw [show s.gpr sb = B from hB]; exact hr e he }
  refine WP.mono (crypt8_wp hkey) fun s' ⟨c', hb'⟩ => ?_
  have hB' : s.gpr sb = B := hB
  have base'' : s'.gpr sb = B := by rw [c'.base, hB']
  have base' : s'.gpr VG.Impl.Modes.X86.sb = B := base''
  have fr : Frame [⟨B.setWidth 64, 4 * tableSlot⟩] s.mem s'.mem := by
    have := c'.frame; rw [hB'] at this; exact this
  refine ⟨base', c'.keep _ (by decide) (by decide), fun e he => (hr e he).congr fun j hj => ?_,
    fr.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by simp only [dirCore, tableEnd_eq, tableSlot_eq]; omega)⟩,
    fun j hj => ?_, c'.rd, c'.wr⟩
  · simp only [entryW]
    rw [slot_addr (by rw [tableSlot_eq]; omega)]
    refine fr.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base _ (by omega) (by rw [tableSlot_eq]; omega)
  · have e₁ := hb' j hj
    simp only [tailBlock, base'', hB'] at e₁
    have ha : blkAddr (dirCore d) B j = B.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * j) := by
      simp only [blkAddr, slotA, dirCore, VG.Offset.add_add]
    rw [show 4 * (dirCore d).bw = 16 from rfl, ha, dirCipher_bytes, bytesAt_eq_blockAt, e₁]

/-- The core's blocks are four words. -/
@[simp] theorem dirCore_bw (d : Dir) : (dirCore d).bw = 4 := rfl

/-- SM4's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) where
  Key := Spec.Sm4.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready s B k := ReadyAt d s.mem B k ∧ B.toNat + 4 * (dirCore d).total ≤ 2 ^ 32
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Sm4.cipher, Spec.Sm4.invCipher]
  layout := ⟨by simp only [dirCore]; decide, .inr rfl, by simp only [dirCore, tableEnd_eq, tailSlot_eq]; omega,
    by simp only [dirCore]; omega⟩
  keyArgs_congr := keyArgs_congr
  ready_frame h _ _ _ hf _ hd := ⟨fun e he => (h.1 e he).congr fun _ hj => entry_keep h.2 hf hd he hj, h.2⟩
  prepare_wp hB hs hR hk hst := WP.mono (prepare_wp d hB hs hR hk hst) fun _ ⟨r, h⟩ => ⟨⟨r, hs.fit⟩, h⟩
  crypt_wp hB hs hr hst := WP.mono (crypt_wp d hB hs hr.1 hst) fun _ ⟨b, e, r, h⟩ => ⟨b, e, ⟨r, hr.2⟩, h⟩

end VG.Proof.Sm4.X86
