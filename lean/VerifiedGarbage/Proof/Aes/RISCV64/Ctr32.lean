module

public import VerifiedGarbage.Proof.Aes.RISCV64.Group
import VerifiedGarbage.Proof.Aes.RISCV64.Ecb
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Aes.RISCV64.Prologue
import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Impl.Aes.RISCV64.Ctr32
public import VerifiedGarbage.Proof.Aes.RISCV64.Keys

/-!
# AES counter mode on RISC-V: the whole function

As on PPC64LE (`Proof/Aes/PPC64LE/Ctr32.lean`): the prologue rounds the
scratch buffer up, saves the callee-saved registers and builds the masks
(`Prologue.lean`), copies the counter block to its slots and writes back the
final counter (`ctrSetup_wp`); the key loop (`Keys.lean`) and the group
loop (`Group.lean`) do the rest; the epilogue restores the registers.
-/

@[expose] public section

namespace VG.Proof.Aes

open Spec.Gcm

open VG.RISCV64 in
/-- RISC-V contract for `vg_aes_ctr32(schedule: *const [u8; 240], rounds: usize,
counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64;
256])`: XORs the AES counter-mode keystream from the counter block at `counter`
into the `n` blocks at `data`, and advances the counter block by `n`.

The code may read `schedule` (240 bytes) and read and write `counter` (16
bytes), `data` (`16 n` bytes) and `scratch` (2048 bytes, whose contents on
exit are unspecified). These may not overlap each other, and `data` may not
wrap around the end of the address space. `rounds` is 10, 12 or 14. The
pointers, `rounds` and `n` are public; the key schedule, the counter block and
the data are secret. -/
def ctr32RISCV64 : Contract RISCV64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 240⟩
    let counter : Region := ⟨s.gpr .a2, 16⟩
    let data : Region := ⟨s.gpr .a3, 16 * (s.gpr .a4).toNat⟩
    let scratch : Region := ⟨s.gpr .a5, 2048⟩
    s.rd = [sched] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .a3).toNat + 16 * (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    let ciph := aesWith (s.gpr .a1).toNat
      (Spec.Aes.bytesAt s.mem (s.gpr .a0) (16 * ((s.gpr .a1).toNat + 1)))
    blocksAt s'.mem (s.gpr .a3) (s.gpr .a4).toNat =
        ctr32 ciph (blockAt s.mem (s.gpr .a2)) (blocksAt s.mem (s.gpr .a3) (s.gpr .a4).toNat) ∧
      blockAt s'.mem (s.gpr .a2) = Nat.repeat inc32 (s.gpr .a4).toNat (blockAt s.mem (s.gpr .a2))
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes

/-! ## The counter block -/

/-- The big-endian word of four bytes is the byte-reversed little-endian one. -/
theorem beWord_eq (m : Mem) (p : Addr) (off : Nat) :
    ByteLoad.beWord m p off = byteRev32 (m.readW (p + BitVec.ofNat 64 off) 32) := by
  unfold ByteLoad.beWord byteRev32
  have e : ∀ i < 4, m (p + BitVec.ofNat 64 (off + i)) =
      (m.readW (p + BitVec.ofNat 64 off) 32).extractLsb' (8 * i) 8 := fun i hi => by
    rw [← Mem.readW_byte _ _ hi, Offset.add_add]
  have e0 : m (p + BitVec.ofNat 64 off) = (m.readW (p + BitVec.ofNat 64 off) 32).extractLsb' 0 8 := by
    simpa using e 0 (by decide)
  rw [e0, e 1 (by decide), e 2 (by decide), e 3 (by decide)]

/-- The memory after `ctrSetup`: the counter block's slots, and the final
counter written back. -/
def setupMem (m : Mem) (b ctr : Addr) (N : BitVec 64) : Mem :=
  let m₁ := m.writeW (b + BitVec.ofNat 64 (8 * 59)) (m.readW ctr 64)
  let m₂ := m₁.writeW (b + BitVec.ofNat 64 (8 * 60))
    ((m₁.readW (ctr + BitVec.ofNat 64 8) 32).setWidth 64)
  let c := (byteRev32 (m₂.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64
  let m₃ := m₂.writeW (b + BitVec.ofNat 64 (8 * 61)) c
  m₃.writeW (ctr + BitVec.ofNat 64 12) (byteRev32 ((c + N).setWidth 32))

theorem ctrSetup_wp {s : State} {X b ctr : Addr} (hs : Scr s X 2048) (hb : s.gpr sb = b)
    (hc : s.gpr .a2 = ctr) (hcw : (⟨ctr, 16⟩ : Region) ∈ s.wr) {P : State → Prop}
    (h : ∀ s', s'.mem = setupMem s.mem b ctr (s.gpr .a4) →
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ t2 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → P s') :
    WP isa (.block ctrSetup) s P := by
  have hcw' := List.mem_append_right s.rd hcw
  have l : ∀ d, d + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .a2 + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [hc]; exact in_off hcw' (by omega) (by omega)
  have al : ∀ k, 8 * k < 2048 → (b + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 := fun k hk => by
    rw [← hb]; exact wordAddr_al hs.al k hk
  have cn : ∀ k, 8 * k + 8 + 7 ≤ 2048 → InRegions s.wr (b + BitVec.ofNat 64 (8 * k)) 8 := fun k hk =>
    ⟨_, hs.wr, by rw [← hb]; exact hs.contains hk (by decide)⟩
  unfold ctrSetup stS cLo cHi cNum
  repeat rw [List.append_assoc]
  rw [WP.block_append_iff (M := isa)]
  refine WP.mono (Bytes.loadLE64_ok (d := t0) (tmp := t1) (hi := t2) (n := .a2) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (l 0 (by omega)) (l 4 (by omega))) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  rw [List.singleton_append]
  refine wp_sd (by decide) (by rw [g₁ _ (by decide) (by decide) (by decide), hb]) (al 59 (by decide))
    (by rw [wr₁]; exact cn 59 (by decide)) fun s₂ u₂ => ?_
  have c₂ : s₂.gpr .a2 = ctr := by rw [u₂.gpr, g₁ _ (by decide) (by decide) (by decide), hc]
  rw [WP.block_append_iff (M := isa)]
  refine WP.mono (ByteLoad.loadLE32_ok (d := t0) (tmp := t1) (n := .a2) (off := 8)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [u₂.rd, u₂.wr, rd₁, wr₁, c₂, ← hc]; exact l 8 (by omega))) fun s₃ e₃ => ?_
  subst e₃
  rw [List.singleton_append]
  refine wp_sd (by decide) (by
      rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), u₂.gpr,
        g₁ _ (by decide) (by decide) (by decide), hb]) (al 60 (by decide))
    (by simp only [RegUpd.wr_write]; rw [u₂.wr, wr₁]; exact cn 60 (by decide)) fun s₄ u₄ => ?_
  rw [WP.block_append_iff (M := isa)]
  have c₄ : s₄.gpr .a2 = ctr := by
    rw [u₄.gpr, RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), c₂]
  refine WP.mono (ByteLoad.loadBE32_ok (d := t0) (tmp := t1) (n := .a2) (off := 12)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [u₄.rd, u₄.wr]; simp only [RegUpd.rd_write, RegUpd.wr_write]
        rw [u₂.rd, u₂.wr, rd₁, wr₁, c₄, ← hc]; exact l 12 (by omega))) fun s₅ e₅ => ?_
  subst e₅
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine wp_sd (by decide) (by
      rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), u₄.gpr,
        RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), u₂.gpr,
        g₁ _ (by decide) (by decide) (by decide), hb]) (al 61 (by decide))
    (by simp only [RegUpd.wr_write]; rw [u₄.wr]; simp only [RegUpd.wr_write]; rw [u₂.wr, wr₁]
        exact cn 61 (by decide)) fun s₆ u₆ => ?_
  refine wp_add fun s₇ u₇ => ?_
  have c₇ : s₇.gpr .a2 = ctr := by
    rw [u₇.other _ (by decide), u₆.gpr, RegUpd.gpr_write_of_ne _ _ (by decide),
      RegUpd.gpr_write_of_ne _ _ (by decide), c₄]
  have hin : ∀ j < 4, InRegions s₇.wr (s₇.gpr .a2 + BitVec.ofNat 64 (12 + j)) 1 := fun j hj => by
    rw [c₇, u₇.wr, u₆.wr]; simp only [RegUpd.wr_write]; rw [u₄.wr]; simp only [RegUpd.wr_write]
    rw [u₂.wr, wr₁]
    exact in_off hcw (by omega) (by omega)
  refine WP.mono (ByteLoad.storeBE_ok (v := t0) (tmp := t1) (n := .a2) (off := 12) (w := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) hin) fun s₈ e₈ => ?_
  -- What the registers and memory hold.
  have a4₄ : s₄.gpr .a4 = s.gpr .a4 := by
    rw [u₄.gpr, RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide),
      u₂.gpr, g₁ _ (by decide) (by decide) (by decide)]
  have t0₇ : s₇.gpr t0 = (byteRev32 (s₄.mem.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64 +
      s.gpr .a4 := by
    rw [u₇.gpr, u₆.gpr, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ (by decide),
      RegUpd.gpr_write_of_ne _ _ (by decide), a4₄, c₄, beWord_eq]
  have m₄ : s₄.mem = (s.mem.writeW (b + BitVec.ofNat 64 (8 * 59)) (s.mem.readW ctr 64)).writeW
      (b + BitVec.ofNat 64 (8 * 60)) (((s.mem.writeW (b + BitVec.ofNat 64 (8 * 59))
        (s.mem.readW ctr 64)).readW (ctr + BitVec.ofNat 64 8) 32).setWidth 64) := by
    rw [u₄.mem]
    simp only [RegUpd.mem_write, RegUpd.gpr_write_self]
    rw [c₂, u₂.mem, m₁, e₁, hc, BitVec.add_zero]
  have m₇ : s₇.mem = s₄.mem.writeW (b + BitVec.ofNat 64 (8 * 61))
      ((byteRev32 (s₄.mem.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64) := by
    rw [u₇.mem, u₆.mem]
    simp only [RegUpd.mem_write, RegUpd.gpr_write_self]
    rw [c₄, beWord_eq]
  have g₇ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ t2 → s₇.gpr r = s.gpr r := fun r h0 h1 h2 => by
    rw [u₇.other _ h0, u₆.gpr, RegUpd.gpr_write_of_ne _ _ h0, RegUpd.gpr_write_of_ne _ _ h1, u₄.gpr,
      RegUpd.gpr_write_of_ne _ _ h0, RegUpd.gpr_write_of_ne _ _ h1, u₂.gpr, g₁ _ h0 h1 h2]
  have rd₇ : s₇.rd = s.rd := by
    rw [u₇.rd, u₆.rd]; simp only [RegUpd.rd_write]; rw [u₄.rd]; simp only [RegUpd.rd_write]
    rw [u₂.rd, rd₁]
  have wr₇ : s₇.wr = s.wr := by
    rw [u₇.wr, u₆.wr]; simp only [RegUpd.wr_write]; rw [u₄.wr]; simp only [RegUpd.wr_write]
    rw [u₂.wr, wr₁]
  have sp₇ : s₇.sp = s.sp := by
    rw [u₇.sp, u₆.sp]; simp only [RegUpd.sp_write]; rw [u₄.sp]; simp only [RegUpd.sp_write]
    rw [u₂.sp, sp₁]
  subst e₈
  refine h _ ?_ (fun r h0 h1 h2 => ?_) (by rw [RegUpd.rd_write]; exact rd₇)
    (by rw [RegUpd.wr_write]; exact wr₇) (by rw [RegUpd.sp_write]; exact sp₇)
  · rw [RegUpd.mem_write]
    show WriteBytes.writeBytes s₇.mem _ _ = _
    rw [writeBytes_be4, c₇, t0₇, m₇, m₄]
    rfl
  · rw [RegUpd.gpr_write_of_ne _ _ h1]; exact g₇ r h0 h1 h2

theorem c_off (base : Addr) {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n :=
  Offset.contains_base base h ho

theorem out_of_disj {r₁ r₂ : Region} (hd : r₁.Disjoint r₂) {x a : Addr} {n : Nat} (hx : r₁.Contains x 1)
    (ha : r₂.Contains a n) : ¬ (x - a).toNat < n := fun h => hd x hx (ha.byte h)

section Setup

variable {m : Mem} {b ctr : Addr} {N : BitVec 64}

theorem setupMem_eq (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2040⟩) :
    setupMem m b ctr N =
      (((m.writeW (b + BitVec.ofNat 64 (8 * 59)) (m.readW ctr 64)).writeW
        (b + BitVec.ofNat 64 (8 * 60)) ((m.readW (ctr + BitVec.ofNat 64 8) 32).setWidth 64)).writeW
        (b + BitVec.ofNat 64 (8 * 61)) ((byteRev32 (m.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64)).writeW
        (ctr + BitVec.ofNat 64 12)
          (byteRev32 (((byteRev32 (m.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64 + N).setWidth 32)) := by
  have s8 : Mem.Sep (ctr + BitVec.ofNat 64 8) (32 / 8) (b + BitVec.ofNat 64 (8 * 59)) (64 / 8) :=
    hd.sep (c_off ctr (by omega_arith) (by omega_arith)) (c_off b (by omega_arith) (by omega_arith))
  have s12a : Mem.Sep (ctr + BitVec.ofNat 64 12) (32 / 8) (b + BitVec.ofNat 64 (8 * 59)) (64 / 8) :=
    hd.sep (c_off ctr (by omega_arith) (by omega_arith)) (c_off b (by omega_arith) (by omega_arith))
  have s12b : Mem.Sep (ctr + BitVec.ofNat 64 12) (32 / 8) (b + BitVec.ofNat 64 (8 * 60)) (64 / 8) :=
    hd.sep (c_off ctr (by omega_arith) (by omega_arith)) (c_off b (by omega_arith) (by omega_arith))
  simp only [setupMem]
  rw [Mem.readW_writeW_sep s8 (by decide), Mem.readW_writeW_sep s12b (by decide),
    Mem.readW_writeW_sep s12a (by decide)]

theorem setup_frame (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2040⟩) :
    Frame [⟨b + BitVec.ofNat 64 (8 * 59), 24⟩, ⟨ctr, 16⟩] m (setupMem m b ctr N) := by
  rw [setupMem_eq hd]
  have h₀ : (⟨b + BitVec.ofNat 64 (8 * 59), 24⟩ : Region) ∈
      [(⟨b + BitVec.ofNat 64 (8 * 59), 24⟩ : Region), ⟨ctr, 16⟩] := by simp
  have h₁ : (⟨ctr, 16⟩ : Region) ∈ [(⟨b + BitVec.ofNat 64 (8 * 59), 24⟩ : Region), ⟨ctr, 16⟩] := by
    simp
  exact ((((Frame.refl _ _).writeW h₀ _ (Offset.contains b (by omega_arith) (by omega_arith) (by omega_arith))).writeW h₀ _
    (Offset.contains b (by omega_arith) (by omega_arith) (by omega_arith))).writeW h₀ _
    (Offset.contains b (by omega_arith) (by omega_arith) (by omega_arith))).writeW h₁ _ (c_off ctr (by omega_arith) (by omega_arith))

theorem setup_slots (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2040⟩) :
    cloW (setupMem m b ctr N) b = m.readW ctr 64 ∧
    chiLo (setupMem m b ctr N) b = m.readW (ctr + BitVec.ofNat 64 8) 32 ∧
    numW (setupMem m b ctr N) b = (byteRev32 (m.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64 := by
  rw [setupMem_eq hd]
  have t : ∀ {k w}, 8 * k + w / 8 ≤ 2040 → Mem.Sep (b + BitVec.ofNat 64 (8 * k)) (w / 8)
      (ctr + BitVec.ofNat 64 12) (32 / 8) := fun h =>
    hd.symm.sep (c_off b h (by omega_arith)) (c_off ctr (by omega_arith) (by omega_arith))
  refine ⟨?_, ?_, ?_⟩
  · rw [cloW, Mem.readW_writeW_sep (t (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep b (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep b (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [chiLo, Mem.readW_writeW_sep (t (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep b (d := 8 * 60) (n := 4) (e := 8 * 61) (k := 8) (by omega_arith)
        (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_lo32 (Mem.readW_writeW_self64 _ _ _)]
    simp
  · rw [numW, Mem.readW_writeW_sep (t (by omega_arith)) (by decide), Mem.readW_writeW_self64]

theorem setup_ctr (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2040⟩) {k : Nat} (hk : k < 16) :
    setupMem m b ctr N (ctr + BitVec.ofNat 64 k) =
      if k < 12 then m (ctr + BitVec.ofNat 64 k)
      else (byteRev32 (((byteRev32 (m.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64 + N).setWidth 32)).extractLsb'
        (8 * (k - 12)) 8 := by
  rw [setupMem_eq hd, writeW_apply, off_toNat ctr (by omega_arith) (by omega_arith)]
  have hx : (⟨ctr, 16⟩ : Region).Contains (ctr + BitVec.ofNat 64 k) 1 := c_off ctr (by omega_arith) (by omega_arith)
  by_cases h : k < 12
  · rw [ite_eq_right (show ¬ 12 ≤ k by omega_arith), ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega_arith),
      ite_eq_left h, writeW_apply, ite_eq_right (out_of_disj hd hx (c_off b (by omega_arith) (by omega_arith))),
      writeW_apply, ite_eq_right (out_of_disj hd hx (c_off b (by omega_arith) (by omega_arith))),
      writeW_apply, ite_eq_right (out_of_disj hd hx (c_off b (by omega_arith) (by omega_arith)))]
  · rw [ite_eq_left (show 12 ≤ k by omega_arith), ite_eq_left (show k - 12 < 32 / 8 by omega_arith),
      ite_eq_right h, BitVec.setWidth_eq]

end Setup

/-! ## The counter block and the data, as blocks -/

theorem byteRev32_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (byteRev32 v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  rw [byteRev32_getLsbD _ (by omega_arith),
    show (8 * k + j) / 8 = k by omega_arith, show (8 * k + j) % 8 = j by omega_arith]

/-- The counter, as the slot holds it. -/
theorem icb_lo (m : Mem) (ctr : Addr) :
    byteRev32 (m.readW (ctr + BitVec.ofNat 64 12) 32) = (Spec.Gcm.blockAt m ctr).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have e : t = 8 * (t / 8) + t % 8 := by omega_arith
  rw [e, byteRev32_bit _ (by omega_arith) (by omega_arith), BitVec.getLsbD_extractLsb', Nat.zero_add,
    decide_eq_true (by omega_arith : 8 * (t / 8) + t % 8 < 32), Bool.true_and,
    show 8 * (t / 8) + t % 8 = 8 * (15 - (15 - t / 8)) + t % 8 by omega_arith,
    blockAt_bit _ _ (by omega_arith) (by omega_arith)]
  have hb := Mem.readW_byte m (ctr + BitVec.ofNat 64 12) (i := 3 - t / 8) (by omega_arith)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 12 + (3 - t / 8) = 15 - t / 8 by omega_arith] at hb
  rw [hb, BitVec.getLsbD_extractLsb']
  simp [show t % 8 < 8 by omega_arith]

theorem ctr_after {m m' : Mem} {ctr : Addr} {n : Nat}
    (h : ∀ k < 16, m' (ctr + BitVec.ofNat 64 k) = if k < 12 then m (ctr + BitVec.ofNat 64 k)
      else (byteRev32 (((byteRev32 (m.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64 +
        BitVec.ofNat 64 n).setWidth 32)).extractLsb' (8 * (k - 12)) 8) :
    Spec.Gcm.blockAt m' ctr = Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt m ctr) := by
  refine block_ext fun k hk => ?_
  rw [toBytes_blockAt _ _ hk, h k hk, ctrBlock_byte _ _ hk]
  split
  · rw [toBytes_blockAt _ _ hk]
  · rw [lo32_add, lo32_ext, setWidth_ofNat32, icb_lo]
    refine byte_ext fun j hj => ?_
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', byteRev32_bit _ (by omega_arith) hj]
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega_arith

theorem ctr32_of_dataInv {m₀ m : Mem} {D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (h : DataInv m₀ m D n n (keyStream R w icb)) :
    Spec.Gcm.blocksAt m D n =
      Spec.Gcm.ctr32 (Spec.Gcm.aesWith R w) icb (Spec.Gcm.blocksAt m₀ D n) := by
  unfold Spec.Gcm.ctr32 Spec.Gcm.keystream Spec.Gcm.blocksAt
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, List.length_map,
    List.length_range]
  simp only [List.length_map, List.length_range] at h1
  refine block_ext fun k hk => ?_
  rw [toBytes_xor _ _ hk, toBytes_blockAt _ _ hk, toBytes_blockAt _ _ hk, BitVec.add_assoc,
    ← BitVec.ofNat_add, h _ (by omega_arith), ite_eq_left (by omega_arith)]
  refine congrArg (_ ^^^ ·) ?_
  unfold Spec.Gcm.aesWith
  rw [toBytes_ofBytes (by simp) hk, keyStream, show (16 * i + k) / 16 = i by omega_arith,
    show (16 * i + k) % 16 = k by omega_arith, getD_eq _ hk, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hk, Option.getD_some]
  rfl


/-! ## The whole function -/

theorem not_ctr_writes : ∀ r ∈ [Reg.ra, .a3, .a4, .a5], r ∉ keyWrites := by decide

theorem correct {s₀ : State} (hp : Proof.Aes.ctr32RISCV64.pre s₀) :
    WP isa Impl.Aes.RISCV64.ctr32 s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        Proof.Aes.ctr32RISCV64.post s₀ s' := by
  obtain ⟨hrd, hwr, dSC, dSD, dSS, dCD, dCS, dDS, hwrap, hR⟩ := hp
  have hwC : (⟨s₀.gpr .a2, 16⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwD : (⟨s₀.gpr .a3, 16 * (s₀.gpr .a4).toNat⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwS : (⟨s₀.gpr .a5, 2048⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hrS : (⟨s₀.gpr .a0, 240⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  have n16 : 16 * (s₀.gpr .a4).toNat < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hc => dCD (s₀.gpr .a2) (by simp [Region.Contains]) ?_
    simp only [Region.Contains]
    have := (s₀.gpr .a2 - s₀.gpr .a3).isLt
    omega_arith
  have hR14 : (s₀.gpr .a1).toNat ≤ 14 := by omega_arith
  let X := s₀.gpr .a5
  let b := X + BitVec.ofNat 64 (pad X)
  let R := (s₀.gpr .a1).toNat
  let n := (s₀.gpr .a4).toNat
  let ctr := s₀.gpr .a2
  let D := s₀.gpr .a3
  have dCb : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2040⟩ := dCS.sub_right (scr_base X (by omega))
  -- The prologue.
  unfold Impl.Aes.RISCV64.ctr32
  refine WP.seq ?_
  repeat rw [WP.block_append_iff (M := isa)]
  refine roundSb_wp fun s₁ b₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_
  have hb₁ : s₁.gpr sb = b := b₁
  have hscr₁ : Scr s₁ X 2048 := ⟨by rw [wr₁]; exact hwS, hb₁⟩
  rw [saveRegs_eq]
  refine Spill.save_ok (rest := []) hscr₁.al savedOffs_ho (fun p hp => ⟨_, hscr₁.wr,
    hscr₁.contains (by have := savedOffs_range p hp; omega) (by decide)⟩) (WP.block_nil ?_)
  generalize hS : ({ s₁ with mem := Spill.saveMem s₁.mem (s₁.gpr sb) s₁.gpr savedOffs } : State) = s₁'
  have g₁' : s₁'.gpr = s₁.gpr := by rw [← hS]
  have mm₁ : s₁'.mem = Spill.saveMem s₁.mem (s₁.gpr sb) s₁.gpr savedOffs := by rw [← hS]
  have rd₁' : s₁'.rd = s₁.rd := by rw [← hS]
  have wr₁' : s₁'.wr = s₁.wr := by rw [← hS]
  have sp₁' : s₁'.sp = s₁.sp := by rw [← hS]
  have sv₁ : Spill.Saved b s₁.gpr savedOffs s₁'.mem := by
    rw [mm₁, ← hb₁]; exact Spill.saveMem_saved savedOffs_fits _ _ _
  have f₁ : Frame [⟨b + BitVec.ofNat 64 320, 96⟩] s₁.mem s₁'.mem := by
    rw [mm₁, ← hb₁]; exact Spill.saveMem_frame savedOffs_range (by decide) _ _ _
  have hscr₁' : Scr s₁' X 2048 := ⟨by rw [wr₁']; exact hscr₁.wr, by rw [g₁']; exact hscr₁.base⟩
  refine WP.mono (maskInit_ok hscr₁') fun s₂ ⟨mk₂, fm₂, g₂, rd₂, wr₂, sp₂⟩ => ?_
  have b₁' : s₁'.gpr sb = b := by rw [g₁']; exact hb₁
  rw [b₁'] at mk₂ fm₂
  have hb₂ : s₂.gpr sb = b := by rw [g₂ _ (by decide) (by decide)]; exact b₁'
  have hscr₂ : Scr s₂ X 2048 := ⟨by rw [wr₂]; exact hscr₁'.wr, hb₂⟩
  have k₂ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ sb → s₂.gpr r = s₀.gpr r := fun r h0 h1 h2 => by
    rw [g₂ r h0 h1, g₁', o₁ r h2]
  refine ctrSetup_wp (ctr := ctr) hscr₂ hb₂ (k₂ _ (by decide) (by decide) (by decide))
    (by rw [wr₂, wr₁', wr₁]; exact hwC) fun s₃ m₃ o₃ rd₃ wr₃ sp₃ => ?_
  have k₃ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ sb → s₃.gpr r = s₀.gpr r :=
    fun r h0 h1 h2 h3 => by rw [o₃ r h0 h1 h2, k₂ r h0 h1 h3]
  refine keySetup_wp (s := s₃) (R := R) (by
      rw [k₃ _ (by decide) (by decide) (by decide) (by decide)]; simp [R])
    hR14 fun s₄ a0₄ a2₄ a1₄ o₄ m₄ rd₄ wr₄ sp₄ => ?_
  have hb₄ : s₄.gpr sb = b := by
    rw [o₄ sb (by decide) (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide)]
    exact hb₂
  have hscr₄ : Scr s₄ X 2048 := ⟨by rw [wr₄, wr₃]; exact hscr₂.wr, hb₄⟩
  have fS : Frame [⟨b + BitVec.ofNat 64 (8 * 59), 24⟩, ⟨ctr, 16⟩] s₂.mem s₄.mem := by
    rw [m₄, m₃]; exact setup_frame dCb
  -- The memory so far changed only in the scratch buffer and the counter.
  have f₀₄ : Frame [⟨X, 2048⟩, ⟨ctr, 16⟩] s₀.mem s₄.mem := by
    have f01 : Frame [⟨X, 2048⟩, ⟨ctr, 16⟩] s₀.mem s₁'.mem := fun x hx =>
      ((f₁.sub fun r hr => ⟨⟨X, 2048⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact scr_part X (by omega)⟩) x hx).trans
        (congrFun m₁ x)
    refine (f01.trans (fm₂.sub fun r hr => ⟨⟨X, 2048⟩, by simp, ?_⟩)).trans (fS.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact scr_part X (by omega)
      · exact scr_part X (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨X, 2048⟩, by simp, scr_part X (by omega)⟩
      · exact ⟨⟨ctr, 16⟩, by simp, fun _ h => h⟩
  have dSc : ∀ r ∈ [(⟨b + BitVec.ofNat 64 416, 48⟩ : Region), ⟨b + BitVec.ofNat 64 512, 96⟩],
      True := fun _ _ => trivial
  have mk₄ : MasksAt s₄.mem b allKs := by
    refine masks_frame fS (fun r hr => ?_) mk₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Offset.disjoint b (by omega) (by omega) (by omega),
        Offset.disjoint b (by omega) (by omega) (by omega)⟩
    · exact ⟨(dCb.sub_right (Offset.sub_base b (by omega))).symm,
        (dCb.sub_right (Offset.sub_base b (by omega))).symm⟩
  let w := Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * (R + 1))
  have hk : KSetup s₄ X b (s₀.gpr .a0) R w :=
    { scr := hscr₄
      base := hb₄
      masks := mk₄
      sch := List.mem_append_left _ (by rw [rd₄, rd₃, rd₂, rd₁', rd₁]; exact hrS)
      sep := dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        refine (f₀₄.bytes (R := ⟨s₀.gpr .a0, 240⟩) (fun r hr => ?_) (by simp) (by simp only; omega_arith)).symm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dSS
        · exact dSC }
  have hi₄ : KInv s₄ b (s₀.gpr .a0) R w R s₄ :=
    { hj := Nat.le_refl _
      a1 := a1₄
      a0 := by rw [a0₄, k₃ _ (by decide) (by decide) (by decide) (by decide)]
      a2 := by rw [a2₄, o₃ _ (by decide) (by decide) (by decide), hb₂]; simp [keyAddr, lastKey]
      rd := rfl
      wr := rfl
      sp := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega_arith) }
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₄) fun s₅ d₅ => ?_)
  refine WP.seq ?_
  unfold keyDone
  refine wp_addi (imm := 64) (by decide) fun s₆ u₆ => WP.block_nil ?_
  have g₆ : ∀ r ∈ [Reg.ra, .a3, .a4, .a5], s₆.gpr r = s₄.gpr r := fun r hr => by
    rw [u₆.other r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
      d₅.keep r (not_ctr_writes r hr)]
  have k₄ : ∀ r ∈ [Reg.ra, .a3, .a4], s₄.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [o₄ _ (by decide) (by decide) (by decide) (by decide),
        k₃ _ (by decide) (by decide) (by decide) (by decide)]
  have a4₆ : s₆.gpr .a4 = s₀.gpr .a4 := by rw [g₆ _ (by simp), k₄ _ (by simp)]
  have a3₆ : s₆.gpr .a3 = D := by rw [g₆ _ (by simp), k₄ _ (by simp)]
  have ra₆ : s₆.gpr .ra = s₀.gpr .ra := by rw [g₆ _ (by simp), k₄ _ (by simp)]
  have hb₆ : s₆.gpr sb = b := by rw [show sb = .a5 from rfl, g₆ _ (by simp)]; exact hb₄
  have hK0 : s₆.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * R) := by
    rw [u₆.gpr, d₅.a2]; exact BitVec.sub_add_cancel _ _
  have fK : Frame (kRegions b) s₄.mem s₆.mem := u₆.mem ▸ d₅.frame
  have kd : ∀ {x lx}, 320 ≤ x → x + lx ≤ 1024 → ∀ r ∈ kRegions b,
      Region.Disjoint ⟨b + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h1 h2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ h1 (by omega_arith)
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  obtain ⟨sl₁, sl₂, sl₃⟩ := setup_slots (m := s₂.mem) (N := s₂.gpr .a4) dCb
  rw [← m₃] at sl₁ sl₂ sl₃
  -- The counter's bytes in `s₂`, as on entry.
  have dc : ∀ {x lx}, x + lx ≤ 16 → ∀ r ∈ [(⟨b + BitVec.ofNat 64 320, 96⟩ : Region)],
      Region.Disjoint ⟨ctr + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (dCb.sub_right (Offset.sub_base b (by omega))).sub_left (Offset.sub_base _ h)
  have dcm : ∀ {x lx}, x + lx ≤ 16 → ∀ r ∈ [(⟨b + BitVec.ofNat 64 416, 48⟩ : Region),
      ⟨b + BitVec.ofNat 64 512, 96⟩], Region.Disjoint ⟨ctr + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dCb.sub_right (Offset.sub_base b (by omega))).sub_left (Offset.sub_base _ h)
    · exact (dCb.sub_right (Offset.sub_base b (by omega))).sub_left (Offset.sub_base _ h)
  have m02 : ∀ {x lx}, x + lx ≤ 16 → lx ≤ 8 →
      s₂.mem.readW (ctr + BitVec.ofNat 64 x) (8 * lx) = s₀.mem.readW (ctr + BitVec.ofNat 64 x) (8 * lx) := by
    intro x lx h hl
    rw [fm₂.readW (Region.contains_self _ _) (by simpa using dcm h) (by omega),
      f₁.readW (Region.contains_self _ _) (by simpa using dc h) (by omega), m₁]
  have clo₆ : cloW s₆.mem b = s₀.mem.readW ctr 64 := by
    have e : cloW s₆.mem b = cloW s₄.mem b :=
      fK.readW (r := ⟨b + BitVec.ofNat 64 (8 * 59), 8⟩) (Region.contains_self _ _)
        (kd (by omega_arith) (by omega_arith)) (by decide)
    rw [e, m₄, sl₁]
    simpa using m02 (x := 0) (lx := 8) (by omega) (by omega)
  have chi₆ : chiLo s₆.mem b = s₀.mem.readW (ctr + BitVec.ofNat 64 8) 32 := by
    have e : chiLo s₆.mem b = chiLo s₄.mem b :=
      fK.readW (r := ⟨b + BitVec.ofNat 64 (8 * 60), 4⟩) (Region.contains_self _ _)
        (kd (by omega_arith) (by omega_arith)) (by decide)
    rw [e, m₄, sl₂]
    exact m02 (x := 8) (lx := 4) (by omega) (by omega)
  have num₆ : numW s₆.mem b = (byteRev32 (s₀.mem.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64 := by
    have e : numW s₆.mem b = numW s₄.mem b :=
      fK.readW (r := ⟨b + BitVec.ofNat 64 (8 * 61), 8⟩) (Region.contains_self _ _)
        (kd (by omega_arith) (by omega_arith)) (by decide)
    rw [e, m₄, sl₃, m02 (x := 12) (lx := 4) (by omega) (by omega)]
  let icb := Spec.Gcm.blockAt s₀.mem ctr
  have hs : GSetup s₆ X b D n R w icb :=
    { scr := ⟨by rw [u₆.wr, d₅.wr]; exact hscr₄.wr, hb₆⟩
      base := hb₆
      masks := by rw [u₆.mem]; exact masks_kept d₅.frame hk.masks
      dat := by rw [u₆.wr, d₅.wr, wr₄, wr₃, wr₂, wr₁', wr₁]; exact hwD
      hn := n16
      sep := dDS
      rounds := hR
      keys := fun j hj => keyRel_congr (d₅.keys j hj) fun k hk => by
        rw [u₆.mem, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add, show 1920 - 64 * R + 64 * j =
          1920 - 64 * (R - j) by omega_arith]
      lo := fun i hi j hj => by
        rw [clo₆, readW_bit _ _ hi hj, ← BitVec.add_zero ctr,
          blockAt_bit _ _ (by omega_arith) hj]
        simp
      hi := fun i hi j hj => by
        rw [chi₆, readW32_bit _ _ hi hj, show 8 * (7 - i) + j = 8 * (15 - (8 + i)) + j by omega_arith,
          blockAt_bit _ _ (by omega_arith) hj, BitVec.ofNat_add, ← BitVec.add_assoc] }
  -- The data is as on entry.
  have dd : ∀ r ∈ [(⟨X, 2048⟩ : Region), ⟨ctr, 16⟩], Region.Disjoint ⟨D, 16 * n⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dDS
    · exact dCD.symm
  have dK : ∀ r ∈ kRegions b, Region.Disjoint ⟨D, 16 * n⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dDS.sub_right (scr_base X (by omega))
    · exact dDS.sub_right (scr_part X (by omega))
  have data₆ : DataInv s₀.mem s₆.mem D n 0 (keyStream R w icb) :=
    dataInv_frame fK dK n16 (dataInv_frame f₀₄ dd n16 fun i hi => by simp)
  refine WP.seq (WP.mono (Q := GDone s₀.mem s₆ b D n R w icb) ?_ fun s₇ gd => ?_)
  · refine WP.ite (decide (n = 0)) (eval_zero_ofNat _ _ (by omega_arith)
      (by rw [a4₆]; simp [n])) (fun h0 => ?_) (fun h0 => ?_)
    · have hn0 : n = 0 := by simpa using h0
      exact WP.block_nil ⟨hb₆, rfl, rfl, rfl, rfl, Frame.refl _ _, fun i hi => by omega_arith⟩
    · have hn0 : n ≠ 0 := by simpa using h0
      refine groups_ok hs ⟨by omega_arith, ?_, ?_, hb₆, hK0, rfl, rfl, rfl, rfl, Frame.refl _ _, ?_,
        data₆⟩
      · rw [a3₆]; simp
      · rw [a4₆]; simp [n]
      · rw [num₆, icb_lo]; simp [icb]
  -- The epilogue.
  have sv : Spill.Saved b s₁.gpr savedOffs s₇.mem := by
    have dS : ∀ r ∈ [(⟨b + BitVec.ofNat 64 416, 48⟩ : Region), ⟨b + BitVec.ofNat 64 512, 96⟩],
        Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint b (by omega) (by omega) (by omega)
      · exact Offset.disjoint b (by omega) (by omega) (by omega)
    have dS2 : ∀ r ∈ [(⟨b + BitVec.ofNat 64 (8 * 59), 24⟩ : Region), ⟨ctr, 16⟩],
        Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint b (by omega) (by omega) (by omega)
      · exact (dCb.sub_right (Offset.sub_base b (by omega))).symm
    have dK' : ∀ r ∈ kRegions b, Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r :=
      kd (by omega) (by omega)
    have dG : ∀ r ∈ gRegions b D n, Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r :=
      hs.slot_disj (by omega) (by omega) (by omega)
    exact (((sv₁.frame_in savedOffs_range fm₂ dS).frame_in savedOffs_range fS dS2).frame_in
      savedOffs_range fK dK').frame_in savedOffs_range gd.frame dG
  have hscr₇ : Scr s₇ X 2048 := ⟨by rw [gd.wr, u₆.wr, d₅.wr]; exact hscr₄.wr, by rw [gd.base]⟩
  rw [restoreRegs_eq]
  refine WP.mono (Spill.restore_wp (B := b) (by rw [← hb₁]; exact hscr₁.al) gd.base savedOffs_ho
    savedOffs_restorable (fun p hp => ⟨_, List.mem_append_right _ hscr₇.wr, by
      rw [← gd.base]
      exact hscr₇.contains (by have := savedOffs_range p hp; omega) (by decide)⟩) sv)
    fun s₈ rs₈ => ?_
  have fsub : ∀ {x lx}, x + lx + 7 ≤ 2048 → Region.Sub ⟨b + BitVec.ofNat 64 x, lx⟩ ⟨X, 2048⟩ :=
    fun h => scr_part X h
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have hr' : r ∈ savedOffs.map Prod.fst := by rw [savedOffs_regs]; exact hr
    rw [rs₈.gpr_of (.inl hr')]
    have : r ∉ [sb] := by revert hr; revert r; decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rw [o₁ r this]
  · rw [rs₈.other _ not_saved_ra, gd.ra, ra₆]
  · show Spec.Gcm.blocksAt s₈.mem D n = _
    rw [rs₈.mem]
    exact ctr32_of_dataInv gd.data
  · show Spec.Gcm.blockAt s₈.mem ctr = _
    rw [rs₈.mem]
    refine ctr_after fun k hk => ?_
    have hC : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, Region.Disjoint ⟨ctr, 16⟩ r) →
        m' (ctr + BitVec.ofNat 64 k) = m (ctr + BitVec.ofNat 64 k) :=
      fun hf hd => hf.bytes hd (by simp) hk
    rw [hC gd.frame (fun r hr => by
        simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dCb.sub_right (Region.sub_prefix (by omega))
        · exact dCb.sub_right (Offset.sub_base b (by omega))
        · exact dCD),
      hC fK (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dCb.sub_right (Region.sub_prefix (by omega))
        · exact dCb.sub_right (Offset.sub_base b (by omega))),
      m₄, m₃, setup_ctr dCb hk, m02 (x := 12) (lx := 4) (by omega) (by omega)]
    have e7 : BitVec.ofNat 64 (s₀.gpr .a4).toNat = s₂.gpr .a4 := by
      rw [k₂ _ (by decide) (by decide) (by decide)]; simp
    split
    · have dcS : ∀ r ∈ [(⟨b + BitVec.ofNat 64 320, 96⟩ : Region)], Region.Disjoint ⟨ctr, 16⟩ r :=
        fun r hr => by simpa using dc (x := 0) (lx := 16) (by omega) r hr
      have dcM : ∀ r ∈ [(⟨b + BitVec.ofNat 64 416, 48⟩ : Region), ⟨b + BitVec.ofNat 64 512, 96⟩],
          Region.Disjoint ⟨ctr, 16⟩ r :=
        fun r hr => by simpa using dcm (x := 0) (lx := 16) (by omega) r hr
      rw [fm₂.bytes (R := ⟨ctr, 16⟩) dcM (by simp) hk, f₁.bytes (R := ⟨ctr, 16⟩) dcS (by simp) hk, m₁]
    · rw [e7]

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a3 => 0x3000 | .a4 => 1 | .a5 => 0x4000
    | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 2048⟩]

theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32RISCV64.pre s) :
    ∃ t s', Exec isa Impl.Aes.RISCV64.ctr32 s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32RISCV64.post s s' := by
  obtain ⟨t, s', he, h₁, hra, h₂⟩ := correct hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩

end VG.Proof.Aes.RISCV64
