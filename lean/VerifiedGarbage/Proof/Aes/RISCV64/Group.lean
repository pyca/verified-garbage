module

import VerifiedGarbage.Proof.Aes.RISCV64.Prologue
public import VerifiedGarbage.Proof.Aes.Blocks
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Aes.RISCV64.Keys
import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Impl.Aes.RISCV64.Ctr32
public import VerifiedGarbage.Proof.Aes.RISCV64.Encrypt
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill

/-!
# One group of counter-mode blocks on RISC-V

As on x86-64 (`Proof/Aes/X86_64/Group.lean`): `ctrBlocks` builds the
counter blocks `c + b` (`b < 4`) from the slots of the counter block
(`ctrBlocks_wp`, then `ctr_inRel` for `InRel`), `encrypt4` encrypts them
(`Encrypt.lean`), and `xorFull` or `xorTail` XOR the keystream into the
data, a byte at a time (`Bytes.loadLE64_ok`, `Bytes.storeLE64_ok`). The last
four bytes of each counter block are stored big-endian, a byte at a time
(`ByteLoad.storeBE_ok`), into the high half of the slot that holds bytes
8–11, and the slot is loaded whole.
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes

theorem q_ctr : ∀ c < 4, q c ≠ sb ∧ q (c + 4) ≠ sb ∧ q c ≠ t0 ∧ q (c + 4) ≠ t0 ∧ q c ≠ q (c + 4) ∧
    q c ≠ t1 ∧ q (c + 4) ≠ t1 ∧ q c ≠ t2 ∧ q (c + 4) ≠ t2 := by
  decide

/-! ## Words in memory -/

/-- Bit `8 i + t` of a 32-bit read is bit `t` of byte `i`. -/
theorem readW32_bit (m : Mem) (a : Addr) {i t : Nat} (hi : i < 4) (ht : t < 8) :
    (m.readW a 32).getLsbD (8 * i + t) = (m (a + BitVec.ofNat 64 i)).getLsbD t := by
  rw [Mem.readW_byte m a hi, BitVec.getLsbD_extractLsb']
  simp [ht]

/-- A 32-bit store into the high half of a 64-bit word. -/
theorem readW_writeW_hi (m : Mem) (a : Addr) (x : BitVec 32) :
    (m.writeW (a + BitVec.ofNat 64 4) x).readW a 64 = x ++ m.readW a 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨k, t, ht, rfl⟩ : ∃ k t, t < 8 ∧ i = 8 * k + t :=
    ⟨i / 8, i % 8, Nat.mod_lt _ (by decide), (Nat.div_add_mod i 8).symm⟩
  have hk : k < 8 := by omega
  rw [readW_bit _ _ hk ht, writeW_apply, off_toNat a (by omega) (by omega), BitVec.getLsbD_append]
  by_cases h4 : k < 4
  · rw [ite_eq_right (show ¬ 4 ≤ k by omega), ite_eq_right (show ¬ 2 ^ 64 + k - 4 < 32 / 8 by omega),
      ite_eq_left (show 8 * k + t < 32 by omega), readW32_bit _ _ h4 ht]
  · rw [ite_eq_left (show 4 ≤ k by omega), ite_eq_left (show k - 4 < 32 / 8 by omega),
      ite_eq_right (show ¬ 8 * k + t < 32 by omega), BitVec.getLsbD_extractLsb',
      BitVec.setWidth_eq]
    simp only [ht, decide_true, Bool.true_and]
    congr 1; omega

/-! ## The counter blocks -/

/-- The words of the counter block: bytes 0–7, bytes 8–11, and the counter. -/
abbrev cloW (m : Mem) (b : Addr) : BitVec 64 := m.readW (b + BitVec.ofNat 64 (8 * 59)) 64
abbrev chiLo (m : Mem) (b : Addr) : BitVec 32 := m.readW (b + BitVec.ofNat 64 (8 * 60)) 32
abbrev numW (m : Mem) (b : Addr) : BitVec 64 := m.readW (b + BitVec.ofNat 64 (8 * 61)) 64

/-- The last four bytes of counter block `c + i`, as `storeBE` stores them. -/
def ctrW (C : BitVec 64) (i : Nat) : BitVec 32 := byteRev32 ((C + BitVec.ofNat 64 i).setWidth 32)

/-- The high word of counter block `c + i`. -/
def hiWord (lo : BitVec 32) (C : BitVec 64) (i : Nat) : BitVec 64 := ctrW C i ++ lo

/-- The address `storeBE` stores to. -/
abbrev ctrAddr (b : Addr) : Addr := b + BitVec.ofNat 64 (8 * 60 + 4)

theorem ctrAddr_eq (b : Addr) : ctrAddr b = b + BitVec.ofNat 64 (8 * 60) + BitVec.ofNat 64 4 := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Four bytes stored big-endian are the byte-reversed word. -/
theorem writeBytes_be4 (m : Mem) (a : Addr) (v : BitVec 64) :
    WriteBytes.writeBytes m a (ByteLoad.beBytes 4 v) = m.writeW a (byteRev32 (v.setWidth 32)) := by
  funext x
  simp only [WriteBytes.writeBytes, ByteLoad.beBytes_length, Mem.writeW, Mem.write]
  by_cases h : (x - a).toNat < 4
  · rw [ite_eq_left h, ite_eq_left (show (x - a).toNat < 32 / 8 from h)]
    simp only [ByteLoad.beBytes, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range h, Option.map_some, Option.getD_some]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', hj,
      decide_true, Bool.true_and]
    rw [byteRev32_getLsbD _ (by omega), BitVec.getLsbD_setWidth,
      show (8 * (x - a).toNat + j) / 8 = (x - a).toNat by omega,
      show (8 * (x - a).toNat + j) % 8 = j by omega]
    rw [decide_eq_true (show 8 * (x - a).toNat + j < 8 * (32 / 8) by omega), Bool.true_and,
      show 4 - 1 - (x - a).toNat = 3 - (x - a).toNat from rfl,
      decide_eq_true (show 8 * (3 - (x - a).toNat) + j < 32 by omega), Bool.true_and]
  · rw [ite_eq_right h, ite_eq_right (show ¬ (x - a).toNat < 32 / 8 from h)]

theorem ctrBlock_wp {s : State} {X b : Addr} {c : Nat} (hc : c < 4) (hs : Scr s X 2048)
    (hb : s.gpr sb = b) {P : State → Prop}
    (h : ∀ s', s'.gpr (q c) = cloW s.mem b →
      s'.gpr (q (c + 4)) = hiWord (chiLo s.mem b) (numW s.mem b) c →
      (∀ r, r ≠ q c → r ≠ q (c + 4) → r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW (ctrAddr b) (ctrW (numW s.mem b) c) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → P s') :
    WP isa (.block (ctrBlock c)) s P := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := q_ctr c hc
  have hw' : (⟨X, 2048⟩ : Region) ∈ s.rd ++ s.wr := List.mem_append_right _ hs.wr
  have al : ∀ k, 8 * k < 2048 → (b + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 := fun k hk => by
    rw [← hb]; exact wordAddr_al hs.al k hk
  have cn : ∀ d n, d + n + 7 ≤ 2048 → (⟨X, 2048⟩ : Region).Contains (b + BitVec.ofNat 64 d) n :=
    fun d n h => by rw [← hb]; exact hs.contains h (by decide)
  simp only [ctrBlock, ldS, cLo, cNum, cHi]
  rw [List.append_assoc, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_ld (by decide) (by rw [hb]) (al 59 (by decide)) ⟨_, hw', cn _ _ (by decide)⟩
    fun s₁ u₁ => ?_
  have hb₁ : s₁.gpr sb = b := by rw [u₁.other _ (Ne.symm h1), hb]
  refine wp_ld (by decide) (by rw [hb₁]) (al 61 (by decide))
    ⟨_, by rw [u₁.rd, u₁.wr]; exact hw', cn _ _ (by decide)⟩ fun s₂ u₂ => ?_
  refine wp_addi (imm := c) (by omega) fun s₃ u₃ => ?_
  have hb₃ : s₃.gpr sb = b := by rw [u₃.other _ (by decide), u₂.other _ (by decide), hb₁]
  have ht₃ : s₃.gpr t0 = numW s.mem b + BitVec.ofNat 64 c := by
    rw [u₃.gpr, u₂.gpr, u₁.mem]
  rw [WP.block_append_iff (M := isa)]
  have hin4 : ∀ j < 4, InRegions s₃.wr (s₃.gpr sb + BitVec.ofNat 64 (8 * 60 + 4 + j)) 1 :=
    fun j hj => ⟨_, (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hs.wr), (by
      rw [hb₃]; exact cn _ _ (by omega))⟩
  refine WP.mono (ByteLoad.storeBE_ok (v := t0) (tmp := t1) (n := sb) (off := 8 * 60 + 4) (w := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) hin4) fun s₄ e₄ => ?_
  have hm₄ : s₄.mem = s.mem.writeW (ctrAddr b) (ctrW (numW s.mem b) c) := by
    rw [e₄, RegUpd.mem_write]
    show WriteBytes.writeBytes s₃.mem _ _ = _
    rw [writeBytes_be4, ht₃, hb₃, u₃.mem, u₂.mem, u₁.mem]; rfl
  have hb₄ : s₄.gpr sb = b := by
    rw [e₄, RegUpd.gpr_write_of_ne _ _ (by decide)]; exact hb₃
  have o₄ : ∀ r, r ≠ t1 → s₄.gpr r = s₃.gpr r := fun r hr => by
    rw [e₄, RegUpd.gpr_write_of_ne _ _ hr]
  have rd₄ : s₄.rd = s₃.rd := by rw [e₄]; rfl
  have wr₄ : s₄.wr = s₃.wr := by rw [e₄]; rfl
  have sp₄ : s₄.sp = s₃.sp := by rw [e₄]; rfl
  refine wp_ld (by decide) (by rw [hb₄]) (al 60 (by decide))
    ⟨_, by rw [rd₄, wr₄, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hw', cn _ _ (by decide)⟩
    fun s₅ u₅ => WP.block_nil ?_
  refine h s₅ ?_ ?_ (fun r r1 r2 r3 r4 => ?_) (by rw [u₅.mem, hm₄])
    (by rw [u₅.rd, rd₄, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₅.sp, sp₄, u₃.sp, u₂.sp, u₁.sp])
  · rw [u₅.other _ h5, o₄ _ h6, u₃.other _ h3, u₂.other _ h3, u₁.gpr]
  · rw [u₅.gpr, hm₄, ctrAddr_eq, readW_writeW_hi]; rfl
  · rw [u₅.other _ r2, o₄ _ r4, u₃.other _ r3, u₂.other _ r3, u₁.other _ r1]

theorem numW_ctr (m : Mem) (b : Addr) (x : BitVec 32) :
    numW (m.writeW (ctrAddr b) x) b = numW m b :=
  Mem.readW_writeW_sep (Offset.sep b (d := 8 * 61) (n := 8) (e := 8 * 60 + 4) (k := 4) (by omega)
    (by omega) (by omega)) (by decide)

theorem cloW_ctr (m : Mem) (b : Addr) (x : BitVec 32) :
    cloW (m.writeW (ctrAddr b) x) b = cloW m b :=
  Mem.readW_writeW_sep (Offset.sep b (d := 8 * 59) (n := 8) (e := 8 * 60 + 4) (k := 4) (by omega)
    (by omega) (by omega)) (by decide)

theorem chiLo_ctr (m : Mem) (b : Addr) (x : BitVec 32) :
    chiLo (m.writeW (ctrAddr b) x) b = chiLo m b :=
  Mem.readW_writeW_sep (Offset.sep b (d := 8 * 60) (n := 4) (e := 8 * 60 + 4) (k := 4) (by omega)
    (by omega) (by omega)) (by decide)

theorem q_distinct : ∀ c < 4, ∀ d < 4, c ≠ d →
    q c ≠ q d ∧ q c ≠ q (d + 4) ∧ q (c + 4) ≠ q d ∧ q (c + 4) ≠ q (d + 4) := by
  decide

theorem q_ne_t0' : ∀ c < 8, q c ≠ t0 ∧ q c ≠ t1 ∧ q c ≠ t2 := by decide

/-- The region the counter blocks write: the counter's bytes 12–15 and the
counter, in slots 60 and 61. -/
abbrev ctrRegion (b : Addr) : Region := ⟨ctrAddr b, 12⟩

theorem ctrRegion_contains4 (b : Addr) : (ctrRegion b).Contains (ctrAddr b) (32 / 8) :=
  Offset.contains b (by omega) (by omega) (by omega)

theorem ctrRegion_contains8 (b : Addr) :
    (ctrRegion b).Contains (b + BitVec.ofNat 64 (8 * 61)) (64 / 8) :=
  Offset.contains b (by omega) (by omega) (by omega)

/-- The four counter blocks. -/
theorem ctrBlocks_wp {s : State} {X b : Addr} (hs : Scr s X 2048) (hb : s.gpr sb = b) :
    WP isa (.block ctrBlocks) s fun s' =>
      (∀ c < 4, s'.gpr (q c) = cloW s.mem b ∧
        s'.gpr (q (c + 4)) = hiWord (chiLo s.mem b) (numW s.mem b) c) ∧
      (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [ctrRegion b] s.mem s'.mem ∧ numW s'.mem b = numW s.mem b + 4 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold ctrBlocks
  repeat rw [WP.block_append_iff (M := isa)]
  have keep : ∀ {s s' : State} {c : Nat}, c < 4 →
      (∀ r, r ≠ q c → r ≠ q (c + 4) → r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) →
      ∀ r, (r ∉ sboxWrites ∨ r = sb) → s'.gpr r = s.gpr r := by
    intro s s' c hc h r hr
    have : r ≠ q c ∧ r ≠ q (c + 4) ∧ r ≠ t0 ∧ r ≠ t1 := by
      have := q_ctr c hc
      rcases hr with hr | rfl
      · refine ⟨fun h => hr ?_, fun h => hr ?_, fun h => hr (h ▸ by decide),
          fun h => hr (h ▸ by decide)⟩ <;> (subst h; unfold q; split <;> decide)
      · exact ⟨this.1.symm, this.2.1.symm, by decide, by decide⟩
    exact h r this.1 this.2.1 this.2.2.1 this.2.2.2
  refine ctrBlock_wp (c := 0) (by omega_arith) hs hb fun s₁ a₁ b₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_
  have hb₁ : s₁.gpr sb = b := (keep (by omega_arith) o₁ sb (.inr rfl)).trans hb
  have hs₁ : Scr s₁ X 2048 := hs.congr wr₁ (by rw [hb₁, hb])
  refine ctrBlock_wp (c := 1) (by omega_arith) hs₁ hb₁ fun s₂ a₂ b₂ o₂ m₂ rd₂ wr₂ sp₂ => ?_
  have hb₂ : s₂.gpr sb = b := (keep (by omega_arith) o₂ sb (.inr rfl)).trans hb₁
  have hs₂ : Scr s₂ X 2048 := hs₁.congr wr₂ (by rw [hb₂, hb₁])
  refine ctrBlock_wp (c := 2) (by omega_arith) hs₂ hb₂ fun s₃ a₃ b₃ o₃ m₃ rd₃ wr₃ sp₃ => ?_
  have hb₃ : s₃.gpr sb = b := (keep (by omega_arith) o₃ sb (.inr rfl)).trans hb₂
  have hs₃ : Scr s₃ X 2048 := hs₂.congr wr₃ (by rw [hb₃, hb₂])
  refine ctrBlock_wp (c := 3) (by omega_arith) hs₃ hb₃ fun s₄ a₄ b₄ o₄ m₄ rd₄ wr₄ sp₄ => ?_
  have hb₄ : s₄.gpr sb = b := (keep (by omega_arith) o₄ sb (.inr rfl)).trans hb₃
  have hs₄ : Scr s₄ X 2048 := hs₃.congr wr₄ (by rw [hb₄, hb₃])
  -- The slots read by each block are those of `s`.
  have n₁ : numW s₁.mem b = numW s.mem b := by rw [m₁, numW_ctr]
  have n₂ : numW s₂.mem b = numW s.mem b := by rw [m₂, numW_ctr, n₁]
  have n₃ : numW s₃.mem b = numW s.mem b := by rw [m₃, numW_ctr, n₂]
  have n₄ : numW s₄.mem b = numW s.mem b := by rw [m₄, numW_ctr, n₃]
  have l₁ : cloW s₁.mem b = cloW s.mem b := by rw [m₁, cloW_ctr]
  have l₂ : cloW s₂.mem b = cloW s.mem b := by rw [m₂, cloW_ctr, l₁]
  have l₃ : cloW s₃.mem b = cloW s.mem b := by rw [m₃, cloW_ctr, l₂]
  have c₁ : chiLo s₁.mem b = chiLo s.mem b := by rw [m₁, chiLo_ctr]
  have c₂ : chiLo s₂.mem b = chiLo s.mem b := by rw [m₂, chiLo_ctr, c₁]
  have c₃ : chiLo s₃.mem b = chiLo s.mem b := by rw [m₃, chiLo_ctr, c₂]
  rw [l₁] at a₂; rw [c₁, n₁] at b₂
  rw [l₂] at a₃; rw [c₂, n₂] at b₃
  rw [l₃] at a₄; rw [c₃, n₃] at b₄
  have hfr₄ : Frame [ctrRegion b] s.mem s₄.mem := by
    rw [m₄, m₃, m₂, m₁]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ctrRegion_contains4 b)).writeW
      (List.mem_singleton_self _) _ (ctrRegion_contains4 b)).writeW (List.mem_singleton_self _) _
      (ctrRegion_contains4 b)).writeW (List.mem_singleton_self _) _ (ctrRegion_contains4 b)
  simp only [ldS, stS, cNum]
  have al : (b + BitVec.ofNat 64 (8 * 61)).toNat % 8 = 0 := by
    rw [← hb]; exact wordAddr_al hs.al 61 (by decide)
  have cn : (⟨X, 2048⟩ : Region).Contains (b + BitVec.ofNat 64 (8 * 61)) 8 := by
    rw [← hb]; exact hs.contains (by decide) (by decide)
  refine wp_ld (by decide) (by rw [hb₄]) al ⟨_, List.mem_append_right _ hs₄.wr, cn⟩ fun s₅ u₅ => ?_
  refine wp_addi (imm := 4) (by decide) fun s₆ u₆ => ?_
  have hb₆ : s₆.gpr sb = b := by rw [u₆.other _ (by decide), u₅.other _ (by decide), hb₄]
  refine wp_sd (by decide) (by rw [hb₆]) al ⟨_, by rw [u₆.wr, u₅.wr]; exact hs₄.wr, cn⟩
    fun s₇ u₇ => WP.block_nil ?_
  have ht₆ : s₆.gpr t0 = numW s.mem b + 4 := by rw [u₆.gpr, u₅.gpr, ← n₄]; rfl
  have hm₇ : s₇.mem = s₄.mem.writeW (b + BitVec.ofNat 64 (8 * 61)) (numW s.mem b + 4) := by
    rw [u₇.mem, u₆.mem, u₅.mem, ht₆]
  have o₇ : ∀ r, r ≠ t0 → s₇.gpr r = s₄.gpr r := fun r hr => by
    rw [u₇.gpr, u₆.other _ hr, u₅.other _ hr]
  refine ⟨fun c hc => ?_, fun r hr => ?_, ?_, ?_, by rw [u₇.rd, u₆.rd, u₅.rd, rd₄, rd₃, rd₂, rd₁],
    by rw [u₇.wr, u₆.wr, u₅.wr, wr₄, wr₃, wr₂, wr₁], by rw [u₇.sp, u₆.sp, u₅.sp, sp₄, sp₃, sp₂, sp₁]⟩
  · rw [o₇ _ (q_ne_t0' c (by omega_arith)).1, o₇ _ (q_ne_t0' (c + 4) (by omega_arith)).1]
    have pres : ∀ {s s' : State} (c d : Nat), c < 4 → d < 4 → c ≠ d →
        (∀ r, r ≠ q d → r ≠ q (d + 4) → r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) →
        s'.gpr (q c) = s.gpr (q c) ∧ s'.gpr (q (c + 4)) = s.gpr (q (c + 4)) := by
      intro s s' c d hc hd hcd o
      have := q_distinct c hc d hd hcd
      exact ⟨o _ this.1 this.2.1 (q_ne_t0' c (by omega_arith)).1 (q_ne_t0' c (by omega_arith)).2.1,
        o _ this.2.2.1 this.2.2.2 (q_ne_t0' (c + 4) (by omega_arith)).1
          (q_ne_t0' (c + 4) (by omega_arith)).2.1⟩
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · rw [(pres 0 3 (by omega_arith) (by omega_arith) (by omega_arith) o₄).1,
        (pres 0 2 (by omega_arith) (by omega_arith) (by omega_arith) o₃).1,
        (pres 0 1 (by omega_arith) (by omega_arith) (by omega_arith) o₂).1,
        (pres 0 3 (by omega_arith) (by omega_arith) (by omega_arith) o₄).2,
        (pres 0 2 (by omega_arith) (by omega_arith) (by omega_arith) o₃).2,
        (pres 0 1 (by omega_arith) (by omega_arith) (by omega_arith) o₂).2, a₁, b₁]
      exact ⟨rfl, rfl⟩
    · rw [(pres 1 3 (by omega_arith) (by omega_arith) (by omega_arith) o₄).1,
        (pres 1 2 (by omega_arith) (by omega_arith) (by omega_arith) o₃).1,
        (pres 1 3 (by omega_arith) (by omega_arith) (by omega_arith) o₄).2,
        (pres 1 2 (by omega_arith) (by omega_arith) (by omega_arith) o₃).2, a₂, b₂]
      exact ⟨rfl, rfl⟩
    · rw [(pres 2 3 (by omega_arith) (by omega_arith) (by omega_arith) o₄).1,
        (pres 2 3 (by omega_arith) (by omega_arith) (by omega_arith) o₄).2, a₃, b₃]
      exact ⟨rfl, rfl⟩
    · rw [a₄, b₄]
      exact ⟨rfl, rfl⟩
  · rw [o₇ r (fun h => hr (h ▸ by decide)), keep (by omega_arith) o₄ r (.inl hr),
      keep (by omega_arith) o₃ r (.inl hr), keep (by omega_arith) o₂ r (.inl hr),
      keep (by omega_arith) o₁ r (.inl hr)]
  · rw [hm₇]; exact hfr₄.writeW (List.mem_singleton_self _) _ (ctrRegion_contains8 b)
  · rw [hm₇, numW, Mem.readW_writeW_self64]

/-! ## The counter blocks as states -/

theorem setWidth_ofNat32 (k : Nat) : (BitVec.ofNat 64 k).setWidth 32 = BitVec.ofNat 32 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

/-- The counter blocks `4g … 4g + 3` in the words, as `InRel` has them. -/
theorem ctr_inRel {Q : Nat → BitVec 64} {icb : Spec.Gcm.Block} {lo : BitVec 64} {hi : BitVec 32}
    {C : BitVec 64} {g : Nat}
    (hlo : ∀ i < 8, ∀ j < 8, lo.getLsbD (8 * i + j) = icb.getLsbD (8 * (15 - i) + j))
    (hhi : ∀ i < 4, ∀ j < 8, hi.getLsbD (8 * i + j) = icb.getLsbD (8 * (7 - i) + j))
    (hC : C.setWidth 32 = icb.extractLsb' 0 32 + BitVec.ofNat 32 (4 * g))
    (hQ : ∀ c < 4, Q c = lo ∧ Q (c + 4) = hiWord hi C c) :
    InRel Q (fun c => ctrState icb (4 * g + c)) := by
  intro c hc i hi16 j hj
  obtain ⟨h0, h1⟩ := hQ c hc
  simp only [ctrState, getD_eq _ hi16, Vector.getElem_ofFn]
  rw [ctrBlock_byte _ _ hi16]
  by_cases h8 : i < 8
  · rw [show i / 8 = 0 by omega, Nat.mul_zero, Nat.add_zero, h0, show i % 8 = i by omega,
      ite_eq_left (show i < 12 by omega), toBytes_getD _ hi16, BitVec.getLsbD_extractLsb',
      hlo i h8 j hj, decide_eq_true hj, Bool.true_and]
  · rw [show i / 8 = 1 by omega, Nat.mul_one, h1, hiWord, BitVec.getLsbD_append]
    by_cases h12 : i < 12
    · rw [ite_eq_left (show 8 * (i % 8) + j < 32 by omega), hhi (i % 8) (by omega) j hj,
        ite_eq_left h12, toBytes_getD _ hi16, BitVec.getLsbD_extractLsb', decide_eq_true hj,
        Bool.true_and, show 8 * (7 - i % 8) + j = 8 * (15 - i) + j by omega]
    · rw [ite_eq_right (show ¬ 8 * (i % 8) + j < 32 by omega), ite_eq_right h12, ctrW,
        byteRev32_getLsbD _ (by omega), lo32_add, hC,
        setWidth_ofNat32, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.getLsbD_extractLsb',
        decide_eq_true hj, Bool.true_and,
        show 8 * (3 - (8 * (i % 8) + j - 32) / 8) + (8 * (i % 8) + j - 32) % 8 = 8 * (15 - i) + j by
          omega]

/-! ## XOR into the data -/

/-- The 8 bytes at `src` XORed with `v`, written to `a`. -/
def xorTo (m : Mem) (a src : Addr) (v : BitVec 64) : Mem := m.writeW a (m.readW src 64 ^^^ v)

theorem xorTo_apply (m : Mem) (a src x : Addr) (v : BitVec 64) :
    xorTo m a src v x = if (x - a).toNat < 8 then
      m (src + BitVec.ofNat 64 (x - a).toNat) ^^^ v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  unfold xorTo Mem.writeW Mem.write
  split
  · rename_i h
    rw [← Mem.extractLsb'_read m src (n := 8) h]
    ext t ht
    simp only [BitVec.getElem_extractLsb', BitVec.getElem_xor, Mem.readW]
    simp
  · rfl

theorem xorTo_miss {m : Mem} {a src x : Addr} {v : BitVec 64} (h : ¬ (x - a).toNat < 8) :
    xorTo m a src v x = m x := by
  rw [xorTo_apply, ite_eq_right h]

theorem xorTo_hit {m : Mem} {a src x : Addr} {v : BitVec 64} {t : Nat} (ht : (x - a).toNat = t)
    (h8 : t < 8) : xorTo m a src v x = m (src + BitVec.ofNat 64 t) ^^^ v.extractLsb' (8 * t) 8 := by
  rw [xorTo_apply, ite_eq_left (by rw [ht]; exact h8), ht]

theorem out_of_disj {r₁ r₂ : Region} (hd : r₁.Disjoint r₂) {x a : Addr} {n : Nat} (hx : r₁.Contains x 1)
    (ha : r₂.Contains a n) : ¬ (x - a).toNat < n := fun h => hd x hx (ha.byte h)

/-- The source and the destination of `n` blocks: the same (in place), or
apart. -/
def Alias (S D : Addr) (n : Nat) : Prop := S = D ∨ Region.Disjoint ⟨S, 16 * n⟩ ⟨D, 16 * n⟩

/-- Byte `i` of the source is none of the `w` bytes of the destination from
offset `e`, if `i` is outside `[e, e + w)`. -/
theorem miss {S D : Addr} {n i e w : Nat} (hA : Alias S D n) (hn : 16 * n < 2 ^ 64) (hi : i < 16 * n)
    (he : e + w ≤ 16 * n) (hie : i < e ∨ e + w ≤ i) :
    ¬ (S + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 e)).toNat < w := by
  rcases hA with rfl | hd
  · rw [off_toNat S (by omega_arith) (by omega_arith)]
    split <;> omega_arith
  · exact out_of_disj hd (Offset.contains_base S (by omega_arith) (by omega_arith))
      (Offset.contains_base D he (by omega_arith))

theorem hit (D : Addr) {i e : Nat} (hi : i < 2 ^ 64) (he : e ≤ i) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 e)).toNat = i - e := by
  rw [off_toNat D hi (by omega_arith), ite_eq_left he]

/-- The data after `k` blocks: the first `16 k` of the `16 n` bytes at `D`
are the keystream `ks` XORed into those at `S` in `m₀`, and the bytes at `S`
from `16 k` on are still those of `m₀`. -/
def DataInv (m₀ m : Mem) (S D : Addr) (n k : Nat) (ks : Nat → Byte) : Prop :=
  ∀ i < 16 * n, (i < 16 * k → m (D + BitVec.ofNat 64 i) = m₀ (S + BitVec.ofNat 64 i) ^^^ ks i) ∧
    (16 * k ≤ i → m (S + BitVec.ofNat 64 i) = m₀ (S + BitVec.ofNat 64 i))

theorem dataInv_zero (m₀ : Mem) (S D : Addr) (n : Nat) (ks : Nat → Byte) : DataInv m₀ m₀ S D n 0 ks :=
  fun _ _ => ⟨fun h => absurd h (by omega_arith), fun _ => rfl⟩

/-- One block of keystream XORed in: the two doublewords of block `k` of
the source, XORed with `v₁` and `v₂`, written to block `k` of `D`. -/
theorem dataInv_step {m₀ m : Mem} {S D : Addr} {n k : Nat} {ks : Nat → Byte} {v₁ v₂ : BitVec 64}
    (hA : Alias S D n) (hn : 16 * n < 2 ^ 64) (hk : k < n) (h : DataInv m₀ m S D n k ks)
    (hks : ∀ t < 16, (if t < 8 then v₁.extractLsb' (8 * t) 8 else v₂.extractLsb' (8 * (t - 8)) 8) =
      ks (16 * k + t)) :
    DataInv m₀ (xorTo (xorTo m (D + BitVec.ofNat 64 (16 * k)) (S + BitVec.ofNat 64 (16 * k)) v₁)
        (D + BitVec.ofNat 64 (16 * k + 8)) (S + BitVec.ofNat 64 (16 * k + 8)) v₂) S D n (k + 1) ks ∧
      Frame [⟨D, 16 * n⟩] m
        (xorTo (xorTo m (D + BitVec.ofNat 64 (16 * k)) (S + BitVec.ofNat 64 (16 * k)) v₁)
          (D + BitVec.ofNat 64 (16 * k + 8)) (S + BitVec.ofNat 64 (16 * k + 8)) v₂) := by
  have hD : Alias D D n := .inl rfl
  refine ⟨fun i hi => ⟨fun h1 => ?_, fun h2 => ?_⟩, fun x hx => ?_⟩
  · by_cases hlo : i < 16 * k
    · rw [xorTo_miss (miss hD hn hi (e := 16 * k + 8) (w := 8) (by omega_arith) (.inl (by omega_arith))),
        xorTo_miss (miss hD hn hi (e := 16 * k) (w := 8) (by omega_arith) (.inl hlo))]
      exact (h i hi).1 hlo
    · have hsrc := (h i hi).2 (by omega_arith)
      have hk' := hks (i - 16 * k) (by omega_arith)
      by_cases h8 : i < 16 * k + 8
      · rw [ite_eq_left (show i - 16 * k < 8 by omega_arith), show 16 * k + (i - 16 * k) = i by omega_arith]
          at hk'
        rw [xorTo_miss (miss hD hn hi (e := 16 * k + 8) (w := 8) (by omega_arith) (.inl h8)),
          xorTo_hit (hit D (i := i) (e := 16 * k) (by omega_arith) (by omega_arith)) (by omega_arith),
          Offset.add_add, show 16 * k + (i - 16 * k) = i by omega_arith, hsrc, hk']
      · rw [ite_eq_right (show ¬ i - 16 * k < 8 by omega_arith), show 16 * k + (i - 16 * k) = i by omega_arith,
          show i - 16 * k - 8 = i - (16 * k + 8) by omega_arith] at hk'
        rw [xorTo_hit (hit D (i := i) (e := 16 * k + 8) (by omega_arith) (by omega_arith)) (by omega_arith),
          Offset.add_add, show 16 * k + 8 + (i - (16 * k + 8)) = i by omega_arith,
          xorTo_miss (miss hA hn hi (e := 16 * k) (w := 8) (by omega_arith) (.inr (by omega_arith))), hsrc, hk']
  · rw [xorTo_miss (miss hA hn hi (e := 16 * k + 8) (w := 8) (by omega_arith) (.inr (by omega_arith))),
      xorTo_miss (miss hA hn hi (e := 16 * k) (w := 8) (by omega_arith) (.inr (by omega_arith)))]
    exact (h i hi).2 (by omega_arith)
  · have hx' : ¬ (⟨D, 16 * n⟩ : Region).Contains x 1 := hx _ (List.mem_singleton_self _)
    rw [xorTo_miss fun h => hx' (Offset.sub_base D (d := 16 * k + 8) (n := 8)
        (show 16 * k + 8 + 8 ≤ 16 * n by omega_arith) x h),
      xorTo_miss fun h => hx' (Offset.sub_base D (d := 16 * k) (n := 8)
        (show 16 * k + 8 ≤ 16 * n by omega_arith) x h)]

theorem dataInv_mono {m₀ m : Mem} {S D : Addr} {n k k' : Nat} {ks : Nat → Byte}
    (h : DataInv m₀ m S D n k ks) (hk : n ≤ k) (hk' : n ≤ k') : DataInv m₀ m S D n k' ks :=
  fun i hi => ⟨fun _ => (h i hi).1 (by omega_arith), fun h2 => absurd h2 (by omega_arith)⟩

/-- The keystream, byte by byte: byte `i` is byte `i mod 16` of the
encrypted counter block `i / 16`. -/
def keyStream (R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) (i : Nat) : Byte :=
  (Spec.Aes.cipher R w (ctrState icb (i / 16))).getD (i % 16) 0

theorem ks_of_inRel {Q : Nat → BitVec 64} {R g : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (h : InRel Q (fun c => Spec.Aes.cipher R w (ctrState icb (4 * g + c)))) {c t : Nat} (hc : c < 4)
    (ht : t < 16) :
    (Q (c + 4 * (t / 8))).extractLsb' (8 * (t % 8)) 8 = keyStream R w icb (16 * (4 * g + c) + t) := by
  apply byte_ext
  intro j hj
  rw [BitVec.getLsbD_extractLsb', h c hc t ht j hj, keyStream,
    show (16 * (4 * g + c) + t) / 16 = 4 * g + c by omega_arith, show (16 * (4 * g + c) + t) % 16 = t by omega_arith]
  simp [hj]

theorem xorTo_eq (m : Mem) (a src : Addr) (v : BitVec 64) :
    (m.writeW a ((m.readW src 64 ^^^ v).setWidth 32)).writeW (a + BitVec.ofNat 64 4)
      (((m.readW src 64 ^^^ v) >>> 32).setWidth 32) = xorTo m a src v :=
  Words64.writeW64_split _ _ _

theorem srcReg_t (o : Bool) : srcReg o ≠ t0 ∧ srcReg o ≠ t1 ∧ srcReg o ≠ t2 := by
  cases o <;> decide

theorem xorBlock_wp {o wd : Bool} {s : State} {m₀ : Mem} {S D : Addr} {n g c : Nat} {ks : Nat → Byte}
    (hc : c < 4) (hk : 4 * g + c < n) (hn : 16 * n < 2 ^ 64) (hD : (⟨D, 16 * n⟩ : Region) ∈ s.wr)
    (hS : (⟨S, 16 * n⟩ : Region) ∈ s.rd ++ s.wr) (hA : Alias S D n)
    (hal : wd = true → D.toNat % 8 = 0 ∧ S.toNat % 8 = 0)
    (hd : s.gpr .a3 = D + BitVec.ofNat 64 (64 * g)) (hs : s.gpr (srcReg o) = S + BitVec.ofNat 64 (64 * g))
    (hinv : DataInv m₀ s.mem S D n (4 * g + c) ks)
    (hks : ∀ t < 16, (s.gpr (q (c + 4 * (t / 8)))).extractLsb' (8 * (t % 8)) 8 =
      ks (16 * (4 * g + c) + t))
    {P : State → Prop}
    (h : ∀ s', DataInv m₀ s'.mem S D n (4 * g + c + 1) ks → Frame [⟨D, 16 * n⟩] s.mem s'.mem →
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ t2 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → P s') :
    WP isa (.block (xorBlock o wd c)) s P := by
  obtain ⟨rs0, rs1, rs2⟩ := srcReg_t o
  have hB : ∀ (B : Addr) (r : Reg), s.gpr r = B + BitVec.ofNat 64 (64 * g) → ∀ e,
      s.gpr r + BitVec.ofNat 64 (16 * c + e) = B + BitVec.ofNat 64 (16 * (4 * g + c) + e) :=
    fun B r hr e => by rw [hr, Offset.add_add]; congr 2; omega_arith
  have D0 : s.gpr .a3 + BitVec.ofNat 64 (16 * c) = D + BitVec.ofNat 64 (16 * (4 * g + c)) := by
    simpa using hB D _ hd 0
  have D8 := hB D _ hd 8
  have S0 : s.gpr (srcReg o) + BitVec.ofNat 64 (16 * c) = S + BitVec.ofNat 64 (16 * (4 * g + c)) := by
    simpa using hB S _ hs 0
  have S8 := hB S _ hs 8
  have inS : ∀ e, e + 8 ≤ 16 →
      InRegions (s.rd ++ s.wr) (s.gpr (srcReg o) + BitVec.ofNat 64 (16 * c + e)) 8 :=
    fun e he => by rw [hB S _ hs]; exact in_off hS (by omega_arith) hn
  have inW : ∀ e, e + 8 ≤ 16 → InRegions s.wr (s.gpr .a3 + BitVec.ofNat 64 (16 * c + e)) 8 :=
    fun e he => by rw [hB D _ hd]; exact in_off hD (by omega_arith) hn
  have alS : ∀ e, e % 8 = 0 → wd = true →
      (s.gpr (srcReg o) + BitVec.ofNat 64 (16 * c + e)).toNat % 8 = 0 := fun e he hw => by
    rw [hB S _ hs]; exact VG.RISCV64.Align.al_add (hal hw).2 (k := 8) (by decide) (by omega_arith)
  have alD : ∀ e, e % 8 = 0 → wd = true → (s.gpr .a3 + BitVec.ofNat 64 (16 * c + e)).toNat % 8 = 0 :=
    fun e he hw => by
      rw [hB D _ hd]; exact VG.RISCV64.Align.al_add (hal hw).1 (k := 8) (by decide) (by omega_arith)
  obtain ⟨nq0, nq1, nq2⟩ := q_ne_t0' c (by omega_arith)
  obtain ⟨nr0, nr1, nr2⟩ := q_ne_t0' (c + 4) (by omega_arith)
  have e4 : ∀ e, s.gpr .a3 + BitVec.ofNat 64 (16 * c + e + 4) =
      s.gpr .a3 + BitVec.ofNat 64 (16 * c + e) + BitVec.ofNat 64 4 := fun e => (Offset.add_add _ _ _).symm
  unfold xorBlock
  repeat rw [List.append_assoc]
  rw [WP.block_append_iff (M := isa)]
  refine WP.mono (loadLE64W_ok (d := t0) (tmp := t1) (hi := t2) (n := srcReg o) (off := 16 * c)
    rs0.symm rs1.symm rs2.symm (by decide) (by decide) (by decide) (by omega_arith)
    (by simpa using inS 0 (by omega)) (fun hw => by simpa using alS 0 (by omega) hw))
    fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  rw [List.singleton_append]
  refine wp_xor fun s₂ u₂ => ?_
  have a₂ : s₂.gpr .a3 = s.gpr .a3 := by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide) (by decide)]
  have r₂ : s₂.gpr (srcReg o) = s.gpr (srcReg o) := by rw [u₂.other _ rs0, g₁ _ rs0 rs1 rs2]
  rw [WP.block_append_iff (M := isa)]
  refine WP.mono (storeLE64W_ok (v := t0) (tmp := t1) (hi := t2) (n := .a3) (off := 16 * c)
    (by decide) (by decide) (by decide) (by decide) (by omega_arith)
    (by rw [a₂, u₂.wr, wr₁]; simpa using inW 0 (by omega))
    (fun hw => by rw [a₂]; simpa using alD 0 (by omega) hw))
    fun s₃ ⟨m₃, g₃, rd₃, wr₃, sp₃⟩ => ?_
  have a₃ : s₃.gpr .a3 = s.gpr .a3 := by rw [g₃ _ (by decide) (by decide), a₂]
  have r₃ : s₃.gpr (srcReg o) = s.gpr (srcReg o) := by rw [g₃ _ rs1 rs2, r₂]
  have v₂ : s₂.gpr t0 = s.mem.readW (S + BitVec.ofNat 64 (16 * (4 * g + c))) 64 ^^^ s.gpr (q c) := by
    rw [u₂.gpr, e₁, g₁ _ nq0 nq1 nq2, S0]
  have hm₃ : s₃.mem = xorTo s.mem (D + BitVec.ofNat 64 (16 * (4 * g + c)))
      (S + BitVec.ofNat 64 (16 * (4 * g + c))) (s.gpr (q c)) := by
    have e40 : s.gpr .a3 + BitVec.ofNat 64 (16 * c + 4) =
        s.gpr .a3 + BitVec.ofNat 64 (16 * c) + BitVec.ofNat 64 4 := (Offset.add_add _ _ _).symm
    rw [m₃, a₂, u₂.mem, m₁, e40, v₂, D0, xorTo_eq]
  rw [WP.block_append_iff (M := isa)]
  refine WP.mono (loadLE64W_ok (d := t0) (tmp := t1) (hi := t2) (n := srcReg o) (off := 16 * c + 8)
    rs0.symm rs1.symm rs2.symm (by decide) (by decide) (by decide) (by omega_arith)
    (by rw [r₃, rd₃, wr₃, u₂.rd, u₂.wr, rd₁, wr₁]; exact inS 8 (by omega))
    (fun hw => by rw [r₃]; exact alS 8 (by omega) hw)) fun s₄ ⟨e₄, g₄, m₄, rd₄, wr₄, sp₄⟩ => ?_
  rw [List.singleton_append]
  refine wp_xor fun s₅ u₅ => ?_
  have a₅ : s₅.gpr .a3 = s.gpr .a3 := by
    rw [u₅.other _ (by decide), g₄ _ (by decide) (by decide) (by decide), a₃]
  refine WP.mono (storeLE64W_ok (v := t0) (tmp := t1) (hi := t2) (n := .a3) (off := 16 * c + 8)
    (by decide) (by decide) (by decide) (by decide) (by omega_arith)
    (by rw [a₅, u₅.wr, wr₄, wr₃, u₂.wr, wr₁]; exact inW 8 (by omega))
    (fun hw => by rw [a₅]; exact alD 8 (by omega) hw)) fun s₆ ⟨m₆, g₆, rd₆, wr₆, sp₆⟩ => ?_
  have qk : s₄.gpr (q (c + 4)) = s.gpr (q (c + 4)) := by
    rw [g₄ _ nr0 nr1 nr2, g₃ _ nr1 nr2, u₂.other _ nr0, g₁ _ nr0 nr1 nr2]
  have v₅ : s₅.gpr t0 = s₃.mem.readW (S + BitVec.ofNat 64 (16 * (4 * g + c) + 8)) 64 ^^^
      s.gpr (q (c + 4)) := by
    rw [u₅.gpr, e₄, r₃, S8, qk]
  have hm : s₆.mem = xorTo (xorTo s.mem (D + BitVec.ofNat 64 (16 * (4 * g + c)))
      (S + BitVec.ofNat 64 (16 * (4 * g + c))) (s.gpr (q c)))
      (D + BitVec.ofNat 64 (16 * (4 * g + c) + 8)) (S + BitVec.ofNat 64 (16 * (4 * g + c) + 8))
      (s.gpr (q (c + 4))) := by
    rw [m₆, a₅, u₅.mem, m₄, e4 8, v₅, D8, xorTo_eq, hm₃]
  have hst := dataInv_step (v₁ := s.gpr (q c)) (v₂ := s.gpr (q (c + 4))) hA hn hk hinv
    (fun t ht => by
      rw [← hks t ht]
      by_cases h8 : t < 8
      · rw [ite_eq_left h8, show t / 8 = 0 by omega_arith, show t % 8 = t by omega_arith, Nat.mul_zero,
          Nat.add_zero]
      · rw [ite_eq_right h8, show t / 8 = 1 by omega_arith, show t % 8 = t - 8 by omega_arith, Nat.mul_one])
  rw [← hm] at hst
  refine h s₆ hst.1 hst.2 (fun r hr0 hr1 hr2 => ?_) (by rw [rd₆, u₅.rd, rd₄, rd₃, u₂.rd, rd₁])
    (by rw [wr₆, u₅.wr, wr₄, wr₃, u₂.wr, wr₁]) (by rw [sp₆, u₅.sp, sp₄, sp₃, u₂.sp, sp₁])
  rw [g₆ r hr1 hr2, u₅.other _ hr0, g₄ r hr0 hr1 hr2, g₃ r hr1 hr2, u₂.other _ hr0, g₁ r hr0 hr1 hr2]

/-! ## The XOR phase of a group -/

/-- After `k` blocks of the group have been XORed in, from `s₃`. -/
structure XS (m₀ : Mem) (S D : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ : State) (k : Nat) (s : State) :
    Prop where
  data : DataInv m₀ s.mem S D n (4 * g + k) ks
  frame : Frame [⟨D, 16 * n⟩] s₃.mem s.mem
  keep : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ t2 → s.gpr r = s₃.gpr r
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr
  sp : s.sp = s₃.sp

/-- Before the XOR phase of group `g`: the keystream is in the words. -/
structure XPre (o wd : Bool) (m₀ : Mem) (S D : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ : State) :
    Prop where
  hg : 4 * g < n
  hn : 16 * n < 2 ^ 64
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₃.wr
  src : (⟨S, 16 * n⟩ : Region) ∈ s₃.rd ++ s₃.wr
  alias : Alias S D n
  a3 : s₃.gpr .a3 = D + BitVec.ofNat 64 (64 * g)
  sr : s₃.gpr (srcReg o) = S + BitVec.ofNat 64 (64 * g)
  a4 : s₃.gpr .a4 = BitVec.ofNat 64 (n - 4 * g)
  data : DataInv m₀ s₃.mem S D n (4 * g) ks
  ks : ∀ c < 4, ∀ t < 16, (s₃.gpr (q (c + 4 * (t / 8)))).extractLsb' (8 * (t % 8)) 8 =
    ks (16 * (4 * g + c) + t)
  /-- The data's addresses multiples of 8, for accesses by doublewords. -/
  al : wd = true → D.toNat % 8 = 0 ∧ S.toNat % 8 = 0

/-- After the XOR phase: no blocks are left, or group `g + 1` is next. -/
def XDone (o : Bool) (m₀ : Mem) (S D : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ s : State) : Prop :=
  Frame [⟨D, 16 * n⟩] s₃.mem s.mem ∧
    (∀ r, r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ .a3 → r ≠ .a4 → r ≠ .a2 → s.gpr r = s₃.gpr r) ∧
    s.rd = s₃.rd ∧ s.wr = s₃.wr ∧ s.sp = s₃.sp ∧
    ((s.gpr .a4 = 0 ∧ DataInv m₀ s.mem S D n n ks) ∨
     (4 * g + 4 < n ∧ DataInv m₀ s.mem S D n (4 * (g + 1)) ks ∧
      s.gpr .a3 = D + BitVec.ofNat 64 (64 * (g + 1)) ∧ s.gpr .a4 = BitVec.ofNat 64 (n - 4 * (g + 1)) ∧
      s.gpr (srcReg o) = S + BitVec.ofNat 64 (64 * (g + 1))))

/-- Out of place, `a2` on past four blocks. -/
theorem srcStep_wp {o : Bool} {s : State} {P : State → Prop}
    (h : ∀ s', s'.gpr (srcReg o) = (if o then s.gpr .a2 + BitVec.ofNat 64 64 else s.gpr .a3) →
      (∀ r, r ≠ .a2 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → P s') :
    WP isa (.block (srcStep o)) s P := by
  cases o
  · exact WP.block_nil (h s rfl (fun _ _ => rfl) rfl rfl rfl rfl)
  · exact wp_addi (imm := 64) (by decide) fun s' u =>
      WP.block_nil (h s' u.gpr (fun r hr => u.other r hr) u.mem u.rd u.wr u.sp)

section Xor

variable {o wd : Bool} {m₀ : Mem} {S D : Addr} {n g : Nat} {ks : Nat → Byte} {s₃ : State}

theorem xs_step (hp : XPre o wd m₀ S D n g ks s₃) {k : Nat} (hk : k < 4) (hkn : 4 * g + k < n) {s : State}
    (hs : XS m₀ S D n g ks s₃ k s) {P : State → Prop} (h : ∀ s', XS m₀ S D n g ks s₃ (k + 1) s' → P s') :
    WP isa (.block (xorBlock o wd k)) s P := by
  obtain ⟨rs0, rs1, rs2⟩ := srcReg_t o
  refine xorBlock_wp hk hkn hp.hn (hs.wr ▸ hp.dat) (by rw [hs.rd, hs.wr]; exact hp.src) hp.alias hp.al
    (by rw [hs.keep _ (by decide) (by decide) (by decide)]; exact hp.a3)
    (by rw [hs.keep _ rs0 rs1 rs2]; exact hp.sr) hs.data
    (fun t ht => by
      have := q_ne_t0' (k + 4 * (t / 8)) (by omega_arith)
      rw [hs.keep _ this.1 this.2.1 this.2.2]; exact hp.ks k hk t ht)
    fun s' d f ok rd wr sp => h s' ⟨d, hs.frame.trans f,
      fun r h0 h1 h2 => (ok r h0 h1 h2).trans (hs.keep r h0 h1 h2), rd.trans hs.rd, wr.trans hs.wr,
      sp.trans hs.sp⟩

theorem xs_zero (hp : XPre o wd m₀ S D n g ks s₃) {s : State} (hg : ∀ r, r ≠ t0 → s.gpr r = s₃.gpr r)
    (hm : s.mem = s₃.mem) (hrd : s.rd = s₃.rd) (hwr : s.wr = s₃.wr) (hsp : s.sp = s₃.sp) :
    XS m₀ S D n g ks s₃ 0 s :=
  ⟨by rw [hm, Nat.add_zero]; exact hp.data, by rw [hm]; exact Frame.refl _ _,
    fun r h _ _ => hg r h, hrd, hwr, hsp⟩

theorem xs_t0 {k : Nat} {s s' : State} {v : BitVec 64} (hs : XS m₀ S D n g ks s₃ k s) (u : Upd s s' t0 v) :
    XS m₀ S D n g ks s₃ k s' :=
  ⟨u.mem ▸ hs.data, u.mem ▸ hs.frame, fun r h h1 h2 => (u.other r h).trans (hs.keep r h h1 h2),
    u.rd.trans hs.rd, u.wr.trans hs.wr, u.sp.trans hs.sp⟩

theorem xorFull_eq : xorFull o wd = xorBlock o wd 0 ++ xorBlock o wd 1 ++ xorBlock o wd 2 ++
    xorBlock o wd 3 ++ (.addi .a3 .a3 64 :: .addi .a4 .a4 (-4) :: srcStep o) := by
  simp only [xorFull, List.range_succ, List.range_zero, List.nil_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append]

theorem xorPhase_wp (hp : XPre o wd m₀ S D n g ks s₃) :
    WP isa (.seq (.block [shrI t0 .a4 2]) (.ite (.nonzero t0) (.block (xorFull o wd)) (xorTail o wd)))
      s₃ (XDone o m₀ S D n g ks s₃) := by
  have hg := hp.hg
  have hn := hp.hn
  refine shr2_wp (k := n - 4 * g) (by omega_arith) hp.a4 fun s₄ u₄ ev₄ => ?_
  have x₀ := xs_zero hp (fun r h => u₄.other r h) u₄.mem u₄.rd u₄.wr u₄.sp
  refine WP.ite (decide (4 ≤ n - 4 * g)) ev₄ (fun hb => ?_) (fun hb => ?_)
  · -- Four blocks.
    have h4 : 4 ≤ n - 4 * g := by simpa using hb
    rw [xorFull_eq]
    repeat rw [WP.block_append_iff (M := isa)]
    refine xs_step hp (k := 0) (by omega_arith) (by omega_arith) x₀ fun s₅ x₅ => ?_
    refine xs_step hp (k := 1) (by omega_arith) (by omega_arith) x₅ fun s₆ x₆ => ?_
    refine xs_step hp (k := 2) (by omega_arith) (by omega_arith) x₆ fun s₇ x₇ => ?_
    refine xs_step hp (k := 3) (by omega_arith) (by omega_arith) x₇ fun s₈ x₈ => ?_
    refine wp_addi (imm := 64) (by decide) fun s₉ u₉ => wp_subi (imm := 4) (by decide)
      fun s₁₀ u₁₀ => srcStep_wp fun s₁₁ sr₁₁ o₁₁ m₁₁ rd₁₁ wr₁₁ sp₁₁ => ?_
    obtain ⟨rs0, rs1, rs2⟩ := srcReg_t o
    have e₁ : s₈.gpr .a3 = D + BitVec.ofNat 64 (64 * g) :=
      (x₈.keep _ (by decide) (by decide) (by decide)).trans hp.a3
    have e₂ : s₈.gpr .a4 = BitVec.ofNat 64 (n - 4 * g) :=
      (x₈.keep _ (by decide) (by decide) (by decide)).trans hp.a4
    have es : s₈.gpr (srcReg o) = S + BitVec.ofNat 64 (64 * g) :=
      (x₈.keep _ rs0 rs1 rs2).trans hp.sr
    have r7' : s₁₁.gpr .a4 = BitVec.ofNat 64 (n - 4 * (g + 1)) := by
      rw [o₁₁ _ (by decide), u₁₀.gpr, u₉.other _ (by decide), e₂, ofNat_sub_ofNat' h4,
        show n - 4 * g - 4 = n - 4 * (g + 1) by omega_arith]
    have a3' : s₁₁.gpr .a3 = D + BitVec.ofNat 64 (64 * (g + 1)) := by
      rw [o₁₁ _ (by decide), u₁₀.other _ (by decide), u₉.gpr, e₁]; exact off_add64 D g
    have sr' : s₁₁.gpr (srcReg o) = S + BitVec.ofNat 64 (64 * (g + 1)) := by
      rw [sr₁₁]
      cases o with
      | false =>
        rw [ite_eq_right (by decide), u₁₀.other _ (by decide), u₉.gpr]
        exact (congrArg (· + BitVec.ofNat 64 64) es).trans (off_add64 S g)
      | true =>
        rw [ite_eq_left rfl, u₁₀.other _ (by decide), u₉.other _ (by decide)]
        exact (congrArg (· + BitVec.ofNat 64 64) es).trans (off_add64 S g)
    refine ⟨by rw [m₁₁, u₁₀.mem, u₉.mem]; exact x₈.frame, fun r h1 h1' h1'' h2 h3 h4 => ?_,
      by rw [rd₁₁, u₁₀.rd, u₉.rd]; exact x₈.rd, by rw [wr₁₁, u₁₀.wr, u₉.wr]; exact x₈.wr,
      by rw [sp₁₁, u₁₀.sp, u₉.sp]; exact x₈.sp, ?_⟩
    · rw [o₁₁ _ h4, u₁₀.other _ h3, u₉.other _ h2]; exact x₈.keep r h1 h1' h1''
    have hd : DataInv m₀ s₁₁.mem S D n (4 * (g + 1)) ks := by
      rw [m₁₁, u₁₀.mem, u₉.mem]; simpa [Nat.mul_add] using x₈.data
    by_cases hl : n - 4 * g = 4
    · refine .inl ⟨by rw [r7', show n - 4 * (g + 1) = 0 by omega_arith]; rfl,
        dataInv_mono hd (by omega_arith) (by omega_arith)⟩
    · exact .inr ⟨by omega_arith, hd, a3', r7', sr'⟩
  · -- The last one to three blocks.
    have h4 : n - 4 * g < 4 := by simpa using hb
    unfold xorTail
    refine WP.seq ?_
    rw [WP.block_append_iff (M := isa)]
    refine xs_step hp (k := 0) (by omega_arith) (by omega_arith) x₀ fun s₅ x₅ => ?_
    refine wp_subi (imm := 1) (by decide) fun s₆ u₆ => WP.block_nil ?_
    have x₆ := xs_t0 x₅ u₆
    have r7₅ : s₅.gpr .a4 = BitVec.ofNat 64 (n - 4 * g) :=
      (x₅.keep _ (by decide) (by decide) (by decide)).trans hp.a4
    have t₆ : s₆.gpr t0 = BitVec.ofNat 64 (n - 4 * g - 1) := by
      rw [u₆.gpr, r7₅, ofNat_sub_ofNat' (by omega_arith)]
    refine WP.seq (WP.mono (Q := XS m₀ S D n g ks s₃ (n - 4 * g)) ?_ fun s hs => ?_)
    · refine WP.ite (decide (n - 4 * g - 1 ≠ 0)) (Steps.eval_nonzero_ofNat s₆ t0 (by omega_arith) t₆)
        (fun hb => ?_) (fun hb => ?_)
      · have h2 : 2 ≤ n - 4 * g := by simp at hb; omega_arith
        refine WP.seq ?_
        rw [WP.block_append_iff (M := isa)]
        refine xs_step hp (k := 1) (by omega_arith) (by omega_arith) x₆ fun s₇ x₇ => ?_
        refine wp_subi (imm := 3) (by decide) fun s₈ u₈ => WP.block_nil ?_
        have x₈ := xs_t0 x₇ u₈
        have r7₇ : s₇.gpr .a4 = BitVec.ofNat 64 (n - 4 * g) :=
          (x₇.keep _ (by decide) (by decide) (by decide)).trans hp.a4
        have z₈ : isa.eval (.zero t0) s₈ = some (decide (n - 4 * g = 3)) := by
          rw [eval_zero, u₈.gpr, r7₇]
          congr 1
          have : n - 4 * g = 2 ∨ n - 4 * g = 3 := by omega_arith
          rcases this with h | h <;> rw [h] <;> decide
        refine WP.ite (decide (n - 4 * g = 3)) z₈ (fun hb => ?_) (fun hb => ?_)
        · have h3 : n - 4 * g = 2 + 1 := by simp at hb; omega_arith
          refine xs_step hp (k := 2) (by omega_arith) (by omega_arith) x₈ fun s₉ x₉ => ?_
          rw [h3]; exact x₉
        · have h3 : n - 4 * g = 2 := by simp at hb; omega_arith
          exact WP.block_nil (by rw [h3]; exact x₈)
      · have h1 : n - 4 * g = 1 := by simp at hb; omega_arith
        exact WP.block_nil (by rw [h1]; exact x₆)
    · refine wp_li (imm := 0) (by decide) fun s' u' => WP.block_nil ?_
      refine ⟨by rw [u'.mem]; exact hs.frame,
        fun r h1 h1' h1'' _ h3 _ => (u'.other r h3).trans (hs.keep r h1 h1' h1''),
        by rw [u'.rd]; exact hs.rd, by rw [u'.wr]; exact hs.wr, by rw [u'.sp]; exact hs.sp,
        .inl ⟨u'.gpr, ?_⟩⟩
      have := hs.data
      rw [show 4 * g + (n - 4 * g) = n by omega_arith, ← u'.mem] at this
      exact this

end Xor

/-! ## A group -/

/-- What the group loop runs with: `s₂` is the state after the round keys
are bitsliced, `X` the scratch buffer (rounded to `b`), `S` the source and
`D` the destination (`n` blocks), `icb` the first counter block. -/
structure GSetup (s₂ : State) (X b S D : Addr) (n R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) :
    Prop where
  scr : Scr s₂ X 2048
  base : s₂.gpr sb = b
  masks : MasksAt s₂.mem b allKs
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₂.wr
  src : (⟨S, 16 * n⟩ : Region) ∈ s₂.rd ++ s₂.wr
  alias : Alias S D n
  hn : 16 * n < 2 ^ 64
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨X, 2048⟩
  ssep : Region.Disjoint ⟨S, 16 * n⟩ ⟨X, 2048⟩
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  keys : KeysAt s₂.mem (b + BitVec.ofNat 64 (1920 - 64 * R)) R w
  lo : ∀ i < 8, ∀ j < 8, (cloW s₂.mem b).getLsbD (8 * i + j) = icb.getLsbD (8 * (15 - i) + j)
  hi : ∀ i < 4, ∀ j < 8, (chiLo s₂.mem b).getLsbD (8 * i + j) = icb.getLsbD (8 * (7 - i) + j)

/-- The memory a group writes: slots 0–39, the counter and the data. -/
abbrev gRegions (b D : Addr) (n : Nat) : List Region :=
  [⟨b, 320⟩, ctrRegion b, ⟨D, 16 * n⟩]

/-- Before group `g`. -/
structure GInv (o : Bool) (m₀ : Mem) (s₂ : State) (b S D : Addr) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (g : Nat) (s : State) : Prop where
  hg : 4 * g < n
  a3 : s.gpr .a3 = D + BitVec.ofNat 64 (64 * g)
  sr : s.gpr (srcReg o) = S + BitVec.ofNat 64 (64 * g)
  a4 : s.gpr .a4 = BitVec.ofNat 64 (n - 4 * g)
  base : s.gpr sb = b
  a0 : s.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * R)
  ra : s.gpr .ra = s₂.gpr .ra
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (gRegions b D n) s₂.mem s.mem
  num : numW s.mem b = (icb.extractLsb' 0 32).setWidth 64 + BitVec.ofNat 64 (4 * g)
  data : DataInv m₀ s.mem S D n (4 * g) (keyStream R w icb)

/-- After the last group. -/
structure GDone (m₀ : Mem) (s₂ : State) (b S D : Addr) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (s : State) : Prop where
  base : s.gpr sb = b
  ra : s.gpr .ra = s₂.gpr .ra
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (gRegions b D n) s₂.mem s.mem
  data : DataInv m₀ s.mem S D n n (keyStream R w icb)

theorem dataInv_frame {m₀ m m' : Mem} {S D : Addr} {n k : Nat} {ks : Nat → Byte} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r)
    (hs : ∀ r ∈ rs, Region.Disjoint ⟨S, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : DataInv m₀ m S D n k ks) : DataInv m₀ m' S D n k ks := fun i hi =>
  ⟨fun h1 => (hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega_arith) hi).trans ((h i hi).1 h1),
    fun h2 => (hf.bytes (R := ⟨S, 16 * n⟩) hs (by simp only; omega_arith) hi).trans ((h i hi).2 h2)⟩

section
variable {s₂ : State} {X b S D : Addr} {n R : Nat} {w : List Byte} {icb : Spec.Gcm.Block}

theorem GSetup.dat_disj (hs : GSetup s₂ X b S D n R w icb) {x lx : Nat} (h : x + lx + 7 ≤ 2048) :
    Region.Disjoint ⟨D, 16 * n⟩ ⟨b + BitVec.ofNat 64 x, lx⟩ := by
  refine hs.sep.sub_right ?_
  rw [← hs.base]; exact hs.scr.sub h

theorem GSetup.src_disj (hs : GSetup s₂ X b S D n R w icb) {x lx : Nat} (h : x + lx + 7 ≤ 2048) :
    Region.Disjoint ⟨S, 16 * n⟩ ⟨b + BitVec.ofNat 64 x, lx⟩ := by
  refine hs.ssep.sub_right ?_
  rw [← hs.base]; exact hs.scr.sub h

theorem GSetup.b320 (hs : GSetup s₂ X b S D n R w icb) : Region.Sub ⟨b, 320⟩ ⟨X, 2048⟩ := by
  rw [← hs.base, hs.scr.base]
  exact Offset.sub_base X (by have := Align.pad_lt X; omega)

theorem GSetup.d320 (hs : GSetup s₂ X b S D n R w icb) : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 320⟩ :=
  hs.sep.sub_right hs.b320

theorem GSetup.s320 (hs : GSetup s₂ X b S D n R w icb) : Region.Disjoint ⟨S, 16 * n⟩ ⟨b, 320⟩ :=
  hs.ssep.sub_right hs.b320

theorem GSetup.keys_disj (hs : GSetup s₂ X b S D n R w icb) :
    ∀ r ∈ gRegions b D n, Region.Disjoint ⟨b + 1024, 960⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact keys_disjoint b
  · exact Offset.disjoint b (d := 1024) (e := 8 * 60 + 4) (by omega) (by omega) (by omega)
  · exact (hs.dat_disj (x := 1024) (lx := 960) (by omega)).symm

theorem GSetup.slot_disj (hs : GSetup s₂ X b S D n R w icb) {x lx : Nat} (h1 : 320 ≤ x)
    (h2 : x + lx ≤ 484 ∨ 496 ≤ x) (h3 : x + lx + 7 ≤ 2048) :
    ∀ r ∈ gRegions b D n, Region.Disjoint ⟨b + BitVec.ofNat 64 x, lx⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint_base b h1 (by omega)
  · exact Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
  · exact (hs.dat_disj h3).symm

theorem GSetup.masks_disj (hs : GSetup s₂ X b S D n R w icb) : ∀ r ∈ gRegions b D n,
      Region.Disjoint ⟨b + BitVec.ofNat 64 416, 48⟩ r ∧
      Region.Disjoint ⟨b + BitVec.ofNat 64 512, 96⟩ r := fun r hr =>
  ⟨hs.slot_disj (by omega) (by omega) (by omega) r hr, hs.slot_disj (by omega) (by omega) (by omega) r hr⟩

end

theorem num_succ (icb : Spec.Gcm.Block) (g : Nat) :
    (icb.extractLsb' 0 32).setWidth 64 + BitVec.ofNat 64 (4 * g) + 4 =
      (icb.extractLsb' 0 32).setWidth 64 + BitVec.ofNat 64 (4 * (g + 1)) := by
  rw [BitVec.add_assoc]
  congr 1
  rw [show 4 * (g + 1) = 4 * g + 4 by omega, BitVec.ofNat_add]; rfl

theorem num_lo (icb : Spec.Gcm.Block) (g : Nat) :
    ((icb.extractLsb' 0 32).setWidth 64 + BitVec.ofNat 64 (4 * g)).setWidth 32 =
      icb.extractLsb' 0 32 + BitVec.ofNat 32 (4 * g) := by
  rw [lo32_add, lo32_ext, setWidth_ofNat32]

/-- The source register is none of those a group's code uses otherwise. -/
theorem srcReg_keep (o : Bool) : srcReg o ≠ t0 ∧ srcReg o ∉ sboxWrites ∧ srcReg o ≠ kp := by
  cases o <;> decide

theorem GInv.of_t0 {o : Bool} {m₀ : Mem} {s₂ : State} {b S D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} {g : Nat} {s s' : State} {v : BitVec 64}
    (h : GInv o m₀ s₂ b S D n R w icb g s) (u : Upd s s' t0 v) :
    GInv o m₀ s₂ b S D n R w icb g s' :=
  ⟨h.hg, by rw [u.other _ (by decide)]; exact h.a3, by rw [u.other _ (srcReg_keep o).1]; exact h.sr,
    by rw [u.other _ (by decide)]; exact h.a4,
    by rw [u.other _ (by decide)]; exact h.base, by rw [u.other _ (by decide)]; exact h.a0,
    by rw [u.other _ (by decide)]; exact h.ra, u.rd.trans h.rd, u.wr.trans h.wr, u.sp.trans h.sp,
    u.mem ▸ h.frame, by rw [u.mem]; exact h.num, u.mem ▸ h.data⟩

/-- One group: from before group `g`, to after the last group (`a4 = 0`) or
before group `g + 1`. -/
theorem group_ok {o : Bool} {m₀ : Mem} {s₂ : State} {X b S D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (hs : GSetup s₂ X b S D n R w icb) {wd : Bool}
    (hal : wd = true → D.toNat % 8 = 0 ∧ S.toNat % 8 = 0)
    {g : Nat} {s : State} (hi : GInv o m₀ s₂ b S D n R w icb g s) :
    WP isa (group o wd) s fun s' =>
      (isa.eval (.nonzero .a4) s' = some false ∧ GDone m₀ s₂ b S D n R w icb s') ∨
      (isa.eval (.nonzero .a4) s' = some true ∧ GInv o m₀ s₂ b S D n R w icb (g + 1) s') := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega_arith
  have hn := hs.hn
  have hscr : Scr s X 2048 := hs.scr.congr hi.wr (by rw [hi.base, hs.base])
  obtain ⟨-, sk1, sk2⟩ := srcReg_keep o
  unfold group
  refine WP.seq (WP.mono (ctrBlocks_wp hscr hi.base) fun s₁ ⟨hq₁, o₁, f₁, num₁, rd₁, wr₁, sp₁⟩ => ?_)
  have hb₁ : s₁.gpr sb = b := (o₁ sb (by decide)).trans hi.base
  have hf₁ : Frame (gRegions b D n) s₂.mem s₁.mem :=
    hi.frame.trans (f₁.mono fun r hr => by simp at hr; simp [hr])
  have clo : cloW s.mem b = cloW s₂.mem b :=
    hi.frame.readW (Region.contains_self _ _)
      (hs.slot_disj (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)
  have chi : chiLo s.mem b = chiLo s₂.mem b :=
    hi.frame.readW (Region.contains_self _ _)
      (hs.slot_disj (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)
  have hp : EncPre s₁ X R w :=
    ⟨hscr.congr wr₁ (by rw [hb₁, hi.base]),
      by rw [hb₁]; exact masks_frame hf₁ hs.masks_disj hs.masks, hs.rounds,
      by rw [o₁ .a0 (by decide), hi.a0, hb₁],
      by rw [o₁ .a0 (by decide), hi.a0]; exact keysAt_frame hR hf₁ hs.keys_disj hs.keys⟩
  have hin : InRel (Q s₁) (fun c => ctrState icb (4 * g + c)) :=
    ctr_inRel (by rw [clo]; exact hs.lo) (by rw [chi]; exact hs.hi) (by rw [hi.num]; exact num_lo icb g)
      hq₁
  refine WP.seq (WP.mono (encrypt4_ok hp hin) fun s₃ ⟨hc₃, hin₃⟩ => ?_)
  have fr₃ := hc₃.frame
  rw [hb₁] at fr₃
  have hx : XPre o wd m₀ S D n g (keyStream R w icb) s₃ :=
    { hg := hi.hg, hn := hn, al := hal, alias := hs.alias
      dat := by rw [hc₃.wr, wr₁, hi.wr]; exact hs.dat
      src := by rw [hc₃.rd, hc₃.wr, rd₁, wr₁, hi.rd, hi.wr]; exact hs.src
      a3 := by rw [hc₃.keep .a3 (by decide) (by decide), o₁ .a3 (by decide), hi.a3]
      sr := by rw [hc₃.keep _ sk1 sk2, o₁ _ sk1, hi.sr]
      a4 := by rw [hc₃.keep .a4 (by decide) (by decide), o₁ .a4 (by decide), hi.a4]
      data := dataInv_frame fr₃ (by simpa using hs.d320) (by simpa using hs.s320) hn
        (dataInv_frame f₁ (by simpa using hs.dat_disj (by omega_arith))
          (by simpa using hs.src_disj (by omega_arith)) hn hi.data)
      ks := fun c hc t ht => ks_of_inRel hin₃ hc ht }
  refine WP.mono (xorPhase_wp hx) fun s' ⟨f', o', rd', wr', sp', hz⟩ => ?_
  have keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → r ≠ .a2 → s'.gpr r = s.gpr r :=
    fun r h1 h2 h4 h5 h6 => (o' r (fun h => h1 (h ▸ by decide)) (fun h => h1 (h ▸ by decide))
      (fun h => h1 (h ▸ by decide)) h4 h5 h6).trans ((hc₃.keep r h1 h2).trans (o₁ r h1))
  have base' : s'.gpr sb = b :=
    (keep sb (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi.base
  have ra' : s'.gpr .ra = s₂.gpr .ra :=
    (keep .ra (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi.ra
  have rd'' : s'.rd = s₂.rd := by rw [rd', hc₃.rd, rd₁, hi.rd]
  have wr'' : s'.wr = s₂.wr := by rw [wr', hc₃.wr, wr₁, hi.wr]
  have sp'' : s'.sp = s₂.sp := by rw [sp', hc₃.sp, sp₁, hi.sp]
  have frame' : Frame (gRegions b D n) s₂.mem s'.mem :=
    hf₁.trans ((fr₃.mono fun r hr => by simp at hr; simp [hr]).trans
      (f'.mono fun r hr => by simp at hr; simp [hr]))
  rcases hz with ⟨z, d⟩ | ⟨h4, d, r6', r7', sr'⟩
  · refine .inl ⟨by rw [eval_nonzero, z]; rfl, base', ra', rd'', wr'', sp'', frame', d⟩
  · refine .inr ⟨by rw [Steps.eval_nonzero_ofNat s' .a4 (by omega_arith) r7']; simp; omega_arith,
      ⟨by omega_arith, r6', sr', r7', base', ?_, ra', rd'', wr'', sp'', frame', ?_, d⟩⟩
    · rw [keep .a0 (by decide) (by decide) (by decide) (by decide) (by decide), hi.a0]
    · have e₁ : numW s'.mem b = numW s₃.mem b :=
        f'.readW (Region.contains_self _ _) (by simpa using (hs.dat_disj (by omega_arith)).symm)
          (by decide)
      have e₂ : numW s₃.mem b = numW s₁.mem b :=
        fr₃.readW (Region.contains_self _ _)
          (by simpa using Offset.disjoint_base b (d := 8 * 61) (n := 8) (k := 320) (by omega) (by omega))
          (by decide)
      rw [e₁, e₂, num₁, hi.num, num_succ]

/-- The loop over the groups. -/
theorem groups_ok {o : Bool} {m₀ : Mem} {s₂ : State} {X b S D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (hs : GSetup s₂ X b S D n R w icb) {wd : Bool}
    (hal : wd = true → D.toNat % 8 = 0 ∧ S.toNat % 8 = 0)
    {s : State} (hi : GInv o m₀ s₂ b S D n R w icb 0 s) :
    WP isa (.loop (group o wd) (.nonzero .a4)) s (GDone m₀ s₂ b S D n R w icb) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 4 * g ∧ GInv o m₀ s₂ b S D n R w icb g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (group_ok hs hal hg) fun s' h => ?_) n s ⟨0, by omega_arith, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, n - 4 * (g + 1), by have := hg.hg; omega_arith, g + 1, rfl, d⟩

end VG.Proof.Aes.RISCV64
