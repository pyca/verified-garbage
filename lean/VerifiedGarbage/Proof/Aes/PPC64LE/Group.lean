module

import VerifiedGarbage.Proof.Aes.PPC64LE.Keys
public import VerifiedGarbage.Proof.Aes.Blocks
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Aes.PPC64LE.Encrypt
import Mathlib.Data.List.Induction

/-!
# One group of counter-mode blocks on PPC64LE

`ctrBlocks` builds the counter blocks `c + b` (`b < 4`) from the slots of
the counter block (`ctrBlocks_wp`, then `ctr_inRel` for `InRel`),
`encrypt4` encrypts them (`Encrypt.lean`), and `xorFull` or `xorTail` XOR
the keystream into the data, byte by byte, as on x86-64
(`Proof/Aes/X86_64/Group.lean`). The last four bytes of each counter block
are stored big-endian into the high half of the slot that holds bytes 8–11
(`stwbrx`), and the slot is loaded whole.
-/

@[expose] public section

namespace VG.Proof.Aes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.Aes.PPC64LE VG.Proof.Aes

theorem q_ctr : ∀ c < 4, q c ≠ sb ∧ q (c + 4) ≠ sb ∧ q c ≠ t0 ∧ q (c + 4) ≠ t0 ∧ q c ≠ q (c + 4) ∧
    q c ≠ .r10 ∧ q (c + 4) ≠ .r10 ∧ q c ≠ .r0 ∧ q (c + 4) ≠ .r0 := by
  decide

/-! ## Words in memory -/

theorem off_toNat (D : Addr) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 j)).toNat =
      if j ≤ i then i - j else 2 ^ 64 + i - j := Offset.sub_toNat' D hj hi

theorem writeW_apply {m : Mem} {a x : Addr} {w : Nat} (v : BitVec w) :
    m.writeW a v x = if (x - a).toNat < w / 8 then
      (v.setWidth (8 * (w / 8))).extractLsb' (8 * (x - a).toNat) 8 else m x := rfl

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
abbrev cloW (m : Mem) (b : Addr) : BitVec 64 := m.readW (b + BitVec.ofNat 64 (8 * 58)) 64
abbrev chiLo (m : Mem) (b : Addr) : BitVec 32 := m.readW (b + BitVec.ofNat 64 (8 * 59)) 32
abbrev numW (m : Mem) (b : Addr) : BitVec 64 := m.readW (b + BitVec.ofNat 64 (8 * 60)) 64

/-- The last four bytes of counter block `c + i`, as `stwbrx` stores them. -/
def ctrW (C : BitVec 64) (i : Nat) : BitVec 32 := rev32 ((C + BitVec.ofNat 64 i).setWidth 32)

/-- The high word of counter block `c + i`. -/
def hiWord (lo : BitVec 32) (C : BitVec 64) (i : Nat) : BitVec 64 := ctrW C i ++ lo

/-- The address `stwbrx` stores to. -/
abbrev ctrAddr (b : Addr) : Addr := b + BitVec.ofNat 64 (8 * 59 + 4)

theorem ctrAddr_eq (b : Addr) : ctrAddr b = b + BitVec.ofNat 64 (8 * 59) + BitVec.ofNat 64 4 := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ctrBlock_wp {s : State} {b : Addr} {c : Nat} (hc : c < 4) (hb : s.gpr sb = b)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 (8 * 59 + 4)) (hw : (⟨b, 2048⟩ : Region) ∈ s.wr)
    {P : State → Prop}
    (h : ∀ s', s'.gpr (q c) = cloW s.mem b →
      s'.gpr (q (c + 4)) = hiWord (chiLo s.mem b) (numW s.mem b) c →
      (∀ r, r ≠ q c → r ≠ q (c + 4) → r ≠ t0 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW (ctrAddr b) (ctrW (numW s.mem b) c) → s'.rd = s.rd → s'.wr = s.wr →
      P s') :
    WP isa (.block (ctrBlock c)) s P := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := q_ctr c hc
  have hw' : (⟨b, 2048⟩ : Region) ∈ s.rd ++ s.wr := List.mem_append_right _ hw
  simp only [ctrBlock, ldS, cLo, cNum, cHi]
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [hb])
    (in_off hw' (off := 8 * 58) (n := 8) (by omega_arith) (by omega_arith)) fun s₁ u₁ => ?_
  have hb₁ : s₁.gpr sb = b := by rw [u₁.other _ (Ne.symm h1), hb]
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [hb₁])
    (by rw [u₁.rd, u₁.wr]; exact in_off hw' (off := 8 * 60) (n := 8) (by omega_arith) (by omega_arith))
    fun s₂ u₂ => ?_
  refine wp_addi (by decide) (by omega_arith) fun s₃ u₃ => ?_
  have hb₃ : s₃.gpr sb = b := by rw [u₃.other _ (by decide), u₂.other _ (by decide), hb₁]
  have h10₃ : s₃.gpr .r10 = BitVec.ofNat 64 (8 * 59 + 4) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (Ne.symm h6), h10]
  refine wp_stwbrx (by decide) (by rw [hb₃, h10₃]) (by
      rw [u₃.wr, u₂.wr, u₁.wr]; exact in_off hw (off := 8 * 59 + 4) (n := 4) (by omega_arith) (by omega_arith))
    fun s₄ u₄ => ?_
  have hb₄ : s₄.gpr sb = b := by rw [u₄.gpr, hb₃]
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [hb₄])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact in_off hw' (off := 8 * 59) (n := 8) (by omega_arith) (by omega_arith))
    fun s₅ u₅ => wp_nil ?_
  have ht₃ : s₃.gpr t0 = numW s.mem b + BitVec.ofNat 64 c := by
    rw [u₃.gpr, u₂.gpr, u₁.mem]
  have hm₄ : s₄.mem = s.mem.writeW (ctrAddr b) (ctrW (numW s.mem b) c) := by
    rw [u₄.mem, ht₃, u₃.mem, u₂.mem, u₁.mem]; rfl
  refine h s₅ ?_ ?_ (fun r r1 r2 r3 => ?_) (by rw [u₅.mem, hm₄]) (by
    rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₅.other _ h5, u₄.gpr, u₃.other _ h3, u₂.other _ h3, u₁.gpr]
  · rw [u₅.gpr, hm₄, ctrAddr_eq, readW_writeW_hi]; rfl
  · rw [u₅.other _ r2, u₄.gpr, u₃.other _ r3, u₂.other _ r3, u₁.other _ r1]

theorem numW_ctr (m : Mem) (b : Addr) (x : BitVec 32) :
    numW (m.writeW (ctrAddr b) x) b = numW m b :=
  Mem.readW_writeW_sep (Offset.sep b (d := 8 * 60) (n := 8) (e := 8 * 59 + 4) (k := 4) (by omega)
    (by omega) (by omega)) (by decide)

theorem cloW_ctr (m : Mem) (b : Addr) (x : BitVec 32) :
    cloW (m.writeW (ctrAddr b) x) b = cloW m b :=
  Mem.readW_writeW_sep (Offset.sep b (d := 8 * 58) (n := 8) (e := 8 * 59 + 4) (k := 4) (by omega)
    (by omega) (by omega)) (by decide)

theorem chiLo_ctr (m : Mem) (b : Addr) (x : BitVec 32) :
    chiLo (m.writeW (ctrAddr b) x) b = chiLo m b :=
  Mem.readW_writeW_sep (Offset.sep b (d := 8 * 59) (n := 4) (e := 8 * 59 + 4) (k := 4) (by omega)
    (by omega) (by omega)) (by decide)

theorem q_distinct : ∀ c < 4, ∀ d < 4, c ≠ d →
    q c ≠ q d ∧ q c ≠ q (d + 4) ∧ q (c + 4) ≠ q d ∧ q (c + 4) ≠ q (d + 4) := by
  decide

theorem q_ne_t0' : ∀ c < 8, q c ≠ t0 := by decide

/-- The region the counter blocks write: the counter's bytes 12–15 and the
counter, in slots 59 and 60. -/
abbrev ctrRegion (b : Addr) : Region := ⟨ctrAddr b, 12⟩

theorem ctrRegion_contains4 (b : Addr) : (ctrRegion b).Contains (ctrAddr b) (32 / 8) :=
  Offset.contains b (by omega) (by omega) (by omega)

theorem ctrRegion_contains8 (b : Addr) :
    (ctrRegion b).Contains (b + BitVec.ofNat 64 (8 * 60)) (64 / 8) :=
  Offset.contains b (by omega) (by omega) (by omega)

/-- The four counter blocks. -/
theorem ctrBlocks_wp {s : State} {b : Addr} (hb : s.gpr sb = b) (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) :
    WP isa (.block ctrBlocks) s fun s' =>
      (∀ c < 4, s'.gpr (q c) = cloW s.mem b ∧
        s'.gpr (q (c + 4)) = hiWord (chiLo s.mem b) (numW s.mem b) c) ∧
      (∀ r, r ∉ sboxWrites → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      Frame [ctrRegion b] s.mem s'.mem ∧ numW s'.mem b = numW s.mem b + 4 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold ctrBlocks
  repeat rw [WP.block_append_iff (M := isa)]
  refine wp_li (by decide) fun s₀ u₀ => wp_nil ?_
  have keep : ∀ {s s' : State} {c : Nat}, c < 4 →
      (∀ r, r ≠ q c → r ≠ q (c + 4) → r ≠ t0 → s'.gpr r = s.gpr r) →
      ∀ r, (r ∉ sboxWrites ∨ r = sb ∨ r = .r10) → s'.gpr r = s.gpr r := by
    intro s s' c hc h r hr
    have : r ≠ q c ∧ r ≠ q (c + 4) ∧ r ≠ t0 := by
      have := q_ctr c hc
      rcases hr with hr | rfl | rfl
      · refine ⟨fun h => hr ?_, fun h => hr ?_, fun h => hr (h ▸ by decide)⟩ <;>
          (subst h; unfold q; split <;> decide)
      · exact ⟨this.1.symm, this.2.1.symm, by decide⟩
      · exact ⟨this.2.2.2.2.2.1.symm, this.2.2.2.2.2.2.1.symm, by decide⟩
    exact h r this.1 this.2.1 this.2.2
  have hb₀ : s₀.gpr sb = b := by rw [u₀.other _ (by decide), hb]
  have h10 : s₀.gpr .r10 = BitVec.ofNat 64 (8 * 59 + 4) := u₀.gpr
  have hw₀ : (⟨b, 2048⟩ : Region) ∈ s₀.wr := u₀.wr ▸ hw
  refine ctrBlock_wp (c := 0) (by omega_arith) hb₀ h10 hw₀ fun s₁ a₁ b₁ o₁ m₁ rd₁ wr₁ => ?_
  have hb₁ : s₁.gpr sb = b := (keep (by omega_arith) o₁ sb (.inr (.inl rfl))).trans hb₀
  have h10₁ := (keep (by omega_arith) o₁ .r10 (.inr (.inr rfl))).trans h10
  refine ctrBlock_wp (c := 1) (by omega_arith) hb₁ h10₁ (wr₁ ▸ hw₀) fun s₂ a₂ b₂ o₂ m₂ rd₂ wr₂ => ?_
  have hb₂ : s₂.gpr sb = b := (keep (by omega_arith) o₂ sb (.inr (.inl rfl))).trans hb₁
  have h10₂ := (keep (by omega_arith) o₂ .r10 (.inr (.inr rfl))).trans h10₁
  refine ctrBlock_wp (c := 2) (by omega_arith) hb₂ h10₂ (wr₂ ▸ wr₁ ▸ hw₀) fun s₃ a₃ b₃ o₃ m₃ rd₃ wr₃ => ?_
  have hb₃ : s₃.gpr sb = b := (keep (by omega_arith) o₃ sb (.inr (.inl rfl))).trans hb₂
  have h10₃ := (keep (by omega_arith) o₃ .r10 (.inr (.inr rfl))).trans h10₂
  refine ctrBlock_wp (c := 3) (by omega_arith) hb₃ h10₃ (wr₃ ▸ wr₂ ▸ wr₁ ▸ hw₀)
    fun s₄ a₄ b₄ o₄ m₄ rd₄ wr₄ => ?_
  have hb₄ : s₄.gpr sb = b := (keep (by omega_arith) o₄ sb (.inr (.inl rfl))).trans hb₃
  have hw₄ : (⟨b, 2048⟩ : Region) ∈ s₄.wr := wr₄ ▸ wr₃ ▸ wr₂ ▸ wr₁ ▸ hw₀
  -- The slots read by each block are those of `s`.
  have n₁ : numW s₁.mem b = numW s.mem b := by rw [m₁, numW_ctr, u₀.mem]
  have n₂ : numW s₂.mem b = numW s.mem b := by rw [m₂, numW_ctr, n₁]
  have n₃ : numW s₃.mem b = numW s.mem b := by rw [m₃, numW_ctr, n₂]
  have n₄ : numW s₄.mem b = numW s.mem b := by rw [m₄, numW_ctr, n₃]
  have l₁ : cloW s₁.mem b = cloW s.mem b := by rw [m₁, cloW_ctr, u₀.mem]
  have l₂ : cloW s₂.mem b = cloW s.mem b := by rw [m₂, cloW_ctr, l₁]
  have l₃ : cloW s₃.mem b = cloW s.mem b := by rw [m₃, cloW_ctr, l₂]
  have c₁ : chiLo s₁.mem b = chiLo s.mem b := by rw [m₁, chiLo_ctr, u₀.mem]
  have c₂ : chiLo s₂.mem b = chiLo s.mem b := by rw [m₂, chiLo_ctr, c₁]
  have c₃ : chiLo s₃.mem b = chiLo s.mem b := by rw [m₃, chiLo_ctr, c₂]
  rw [u₀.mem] at a₁ b₁
  rw [l₁] at a₂; rw [c₁, n₁] at b₂
  rw [l₂] at a₃; rw [c₂, n₂] at b₃
  rw [l₃] at a₄; rw [c₃, n₃] at b₄
  have hfr₄ : Frame [ctrRegion b] s.mem s₄.mem := by
    rw [m₄, m₃, m₂, m₁, u₀.mem]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ctrRegion_contains4 b)).writeW
      (List.mem_singleton_self _) _ (ctrRegion_contains4 b)).writeW (List.mem_singleton_self _) _
      (ctrRegion_contains4 b)).writeW (List.mem_singleton_self _) _ (ctrRegion_contains4 b)
  simp only [ldS, stS, cNum]
  have hw₄' : (⟨b, 2048⟩ : Region) ∈ s₄.rd ++ s₄.wr := List.mem_append_right _ hw₄
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [hb₄])
    (in_off hw₄' (off := 8 * 60) (n := 8) (by omega_arith) (by omega_arith)) fun s₅ u₅ => ?_
  refine wp_addi (by decide) (by decide) fun s₆ u₆ => ?_
  have hb₆ : s₆.gpr sb = b := by rw [u₆.other _ (by decide), u₅.other _ (by decide), hb₄]
  refine wp_std (by decide) ⟨by decide, by decide⟩ (by rw [hb₆])
    (by rw [u₆.wr, u₅.wr]; exact in_off hw₄ (off := 8 * 60) (n := 8) (by omega_arith) (by omega_arith))
    fun s₇ u₇ => wp_nil ?_
  have ht₆ : s₆.gpr t0 = numW s.mem b + 4 := by rw [u₆.gpr, u₅.gpr, ← n₄]; rfl
  have hm₇ : s₇.mem = s₄.mem.writeW (b + BitVec.ofNat 64 (8 * 60)) (numW s.mem b + 4) := by
    rw [u₇.mem, u₆.mem, u₅.mem, ht₆]
  have o₇ : ∀ r, r ≠ t0 → s₇.gpr r = s₄.gpr r := fun r hr => by
    rw [u₇.gpr, u₆.other _ hr, u₅.other _ hr]
  refine ⟨fun c hc => ?_, fun r hr h10r => ?_, ?_, ?_, by rw [u₇.rd, u₆.rd, u₅.rd, rd₄, rd₃, rd₂, rd₁,
    u₀.rd], by rw [u₇.wr, u₆.wr, u₅.wr, wr₄, wr₃, wr₂, wr₁, u₀.wr]⟩
  · rw [o₇ _ (q_ne_t0' c (by omega_arith)), o₇ _ (q_ne_t0' (c + 4) (by omega_arith))]
    have pres : ∀ {s s' : State} (c d : Nat), c < 4 → d < 4 → c ≠ d →
        (∀ r, r ≠ q d → r ≠ q (d + 4) → r ≠ t0 → s'.gpr r = s.gpr r) →
        s'.gpr (q c) = s.gpr (q c) ∧ s'.gpr (q (c + 4)) = s.gpr (q (c + 4)) := by
      intro s s' c d hc hd hcd o
      have := q_distinct c hc d hd hcd
      exact ⟨o _ this.1 this.2.1 (q_ne_t0' c (by omega_arith)),
        o _ this.2.2.1 this.2.2.2 (q_ne_t0' (c + 4) (by omega_arith))⟩
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
      keep (by omega_arith) o₁ r (.inl hr), u₀.other _ h10r]
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
        show rev32 = byteRev32 from rfl, byteRev32_getLsbD _ (by omega), lo32_add, hC,
        setWidth_ofNat32, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.getLsbD_extractLsb',
        decide_eq_true hj, Bool.true_and,
        show 8 * (3 - (8 * (i % 8) + j - 32) / 8) + (8 * (i % 8) + j - 32) % 8 = 8 * (15 - i) + j by
          omega]

/-! ## XOR into the data -/

/-- XOR `v` into the 8 bytes at `a`. -/
def xorW (m : Mem) (a : Addr) (v : BitVec 64) : Mem := m.writeW a (m.readW a 64 ^^^ v)

theorem xorW_apply (m : Mem) (a x : Addr) (v : BitVec 64) :
    xorW m a v x = if (x - a).toNat < 8 then m x ^^^ v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  unfold xorW Mem.writeW Mem.write
  split
  · rename_i h
    have hx : a + BitVec.ofNat 64 (x - a).toNat = x := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have := Mem.extractLsb'_read m a (n := 8) h
    rw [hx] at this
    rw [← this]
    ext t ht
    simp only [BitVec.getElem_extractLsb', BitVec.getElem_xor, Mem.readW]
    simp
  · rfl

/-- XOR two words into the 16 bytes at `a`. -/
theorem xorW2_apply (m : Mem) (a x : Addr) (v₁ v₂ : BitVec 64) :
    xorW (xorW m a v₁) (a + 8) v₂ x =
      if (x - a).toNat < 16 then
        m x ^^^ (if (x - a).toNat < 8 then v₁.extractLsb' (8 * (x - a).toNat) 8
          else v₂.extractLsb' (8 * ((x - a).toNat - 8)) 8)
      else m x := by
  rw [xorW_apply, xorW_apply]
  have hxa := (x - a).isLt
  have e : (x - (a + 8)).toNat = (2 ^ 64 - 8 + (x - a).toNat) % 2 ^ 64 := by
    rw [VG.Offset.sub_add_eq, BitVec.toNat_sub]; rfl
  by_cases h : (x - a).toNat < 8
  · have : ¬ (x - (a + 8)).toNat < 8 := by rw [e]; omega_using [h, hxa]
    rw [ite_eq_right this, ite_eq_left h, ite_eq_left (show (x - a).toNat < 16 by omega_using [h]), ite_eq_left h]
  · by_cases h' : (x - a).toNat < 16
    · have : (x - (a + 8)).toNat = (x - a).toNat - 8 := by rw [e]; omega_using [h, hxa]
      rw [this, ite_eq_left (show (x - a).toNat - 8 < 8 by omega_using [h']), ite_eq_right h, ite_eq_left h',
        ite_eq_right h]
    · have : ¬ (x - (a + 8)).toNat < 8 := by rw [e]; omega_using [h', hxa]
      rw [ite_eq_right this, ite_eq_right h, ite_eq_right h']

/-- The data after `k` blocks: the keystream `ks` XORed into the first
`16 k` of the `16 n` bytes at `D`. -/
def DataInv (m₀ m : Mem) (D : Addr) (n k : Nat) (ks : Nat → Byte) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    m₀ (D + BitVec.ofNat 64 i) ^^^ (if i < 16 * k then ks i else 0)

/-- One block of keystream XORed in. -/
theorem dataInv_step {m₀ m : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} {v₁ v₂ : BitVec 64}
    (hn : 16 * n ≤ 2 ^ 64) (hk : k < n) (h : DataInv m₀ m D n k ks)
    (hks : ∀ t < 16, (if t < 8 then v₁.extractLsb' (8 * t) 8 else v₂.extractLsb' (8 * (t - 8)) 8) =
      ks (16 * k + t)) :
    DataInv m₀ (xorW (xorW m (D + BitVec.ofNat 64 (16 * k)) v₁) (D + BitVec.ofNat 64 (16 * k) + 8) v₂)
        D n (k + 1) ks ∧
      Frame [⟨D, 16 * n⟩] m
        (xorW (xorW m (D + BitVec.ofNat 64 (16 * k)) v₁) (D + BitVec.ofNat 64 (16 * k) + 8) v₂) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · rw [xorW2_apply, off_toNat D (by omega_arith) (by omega_arith), h i hi]
    by_cases h1 : 16 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 16 * k < 16
      · rw [ite_eq_left h2, hks _ h2, ite_eq_right (show ¬ i < 16 * k by omega_arith),
          ite_eq_left (show i < 16 * (k + 1) by omega_arith), show 16 * k + (i - 16 * k) = i by omega_arith]
        simp
      · rw [ite_eq_right h2, ite_eq_right (show ¬ i < 16 * k by omega_arith),
          ite_eq_right (show ¬ i < 16 * (k + 1) by omega_arith)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 16 * k < 16 by omega_arith),
        ite_eq_left (show i < 16 * k by omega_arith), ite_eq_left (show i < 16 * (k + 1) by omega_arith)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx ⟨D, 16 * n⟩ (List.mem_singleton_self _)
    rw [xorW2_apply, ite_eq_right]
    have : 16 * k < 2 ^ 64 := by omega_arith
    have : (BitVec.ofNat 64 (16 * k)).toNat = 16 * k := by simp; omega_arith
    bv_omega

theorem dataInv_mono {m₀ m : Mem} {D : Addr} {n k k' : Nat} {ks : Nat → Byte} (h : DataInv m₀ m D n k ks)
    (hk : n ≤ k) (hk' : n ≤ k') : DataInv m₀ m D n k' ks := by
  intro i hi
  rw [h i hi, ite_eq_left (show i < 16 * k by omega_arith), ite_eq_left (show i < 16 * k' by omega_arith)]

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

theorem add_off8 (A : Addr) (x : Nat) :
    A + BitVec.ofNat 64 (x + 8) = A + BitVec.ofNat 64 x + 8 := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl

theorem xorBlock_wp {s : State} {m₀ : Mem} {D : Addr} {n g c : Nat} {ks : Nat → Byte} (hc : c < 4)
    (hk : 4 * g + c < n) (hn : 16 * n < 2 ^ 64) (hD : (⟨D, 16 * n⟩ : Region) ∈ s.wr)
    (hd : s.gpr .r6 = D + BitVec.ofNat 64 (64 * g)) (hinv : DataInv m₀ s.mem D n (4 * g + c) ks)
    (hks : ∀ t < 16, (s.gpr (q (c + 4 * (t / 8)))).extractLsb' (8 * (t % 8)) 8 =
      ks (16 * (4 * g + c) + t))
    {P : State → Prop}
    (h : ∀ s', DataInv m₀ s'.mem D n (4 * g + c + 1) ks → Frame [⟨D, 16 * n⟩] s.mem s'.mem →
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (xorBlock c)) s P := by
  have ha : s.gpr .r6 + BitVec.ofNat 64 (16 * c) = D + BitVec.ofNat 64 (16 * (4 * g + c)) := by
    rw [hd, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
  have ha8 : s.gpr .r6 + BitVec.ofNat 64 (16 * c + 8) = D + BitVec.ofNat 64 (16 * (4 * g + c)) + 8 := by
    rw [add_off8, ha]
  have hD' : (⟨D, 16 * n⟩ : Region) ∈ s.rd ++ s.wr := List.mem_append_right _ hD
  have i1 := in_off hD (off := 16 * (4 * g + c)) (n := 8) (by omega_arith) hn
  have i2 := in_off hD (off := 16 * (4 * g + c) + 8) (n := 8) (by omega_arith) hn
  have i1' := in_off hD' (off := 16 * (4 * g + c)) (n := 8) (by omega_arith) hn
  have i2' := in_off hD' (off := 16 * (4 * g + c) + 8) (n := 8) (by omega_arith) hn
  rw [add_off8] at i2 i2'
  have hqc := q_ne_t0' c (by omega_arith)
  have hqc4 := q_ne_t0' (c + 4) (by omega_arith)
  unfold xorBlock
  refine wp_ld (by decide) ⟨by omega_arith, by omega_arith⟩ ha i1' fun s₁ u₁ => ?_
  refine wp_xor fun s₂ u₂ => ?_
  have hd₂ : s₂.gpr .r6 = s.gpr .r6 := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  refine wp_std (by decide) ⟨by omega_arith, by omega_arith⟩ (by rw [hd₂, ha])
    (by rw [u₂.wr, u₁.wr]; exact i1) fun s₃ u₃ => ?_
  have hd₃ : s₃.gpr .r6 = s.gpr .r6 := by rw [u₃.gpr, hd₂]
  refine wp_ld (by decide) ⟨by omega_arith, by omega_arith⟩ (by rw [hd₃, ha8])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i2') fun s₄ u₄ => ?_
  refine wp_xor fun s₅ u₅ => ?_
  have hd₅ : s₅.gpr .r6 = s.gpr .r6 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), hd₃]
  refine wp_std (by decide) ⟨by omega_arith, by omega_arith⟩ (by rw [hd₅, ha8])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact i2) fun s₆ u₆ => wp_nil ?_
  have m₃ : s₃.mem = xorW s.mem (D + BitVec.ofNat 64 (16 * (4 * g + c))) (s.gpr (q c)) := by
    rw [u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.other _ hqc, u₁.mem]; rfl
  have hm : s₆.mem = xorW (xorW s.mem (D + BitVec.ofNat 64 (16 * (4 * g + c))) (s.gpr (q c)))
      (D + BitVec.ofNat 64 (16 * (4 * g + c)) + 8) (s.gpr (q (c + 4))) := by
    rw [← m₃, u₆.mem, u₅.gpr, u₅.mem, u₄.gpr, u₄.other _ hqc4, u₄.mem, u₃.gpr, u₂.other _ hqc4,
      u₁.other _ hqc4]
    rfl
  have hst := dataInv_step (v₁ := s.gpr (q c)) (v₂ := s.gpr (q (c + 4))) (by omega_arith) hk hinv
    (fun t ht => by
      rw [← hks t ht]
      by_cases h8 : t < 8
      · rw [ite_eq_left h8, show t / 8 = 0 by omega_arith, show t % 8 = t by omega_arith, Nat.mul_zero,
          Nat.add_zero]
      · rw [ite_eq_right h8, show t / 8 = 1 by omega_arith, show t % 8 = t - 8 by omega_arith, Nat.mul_one])
  rw [← hm] at hst
  refine h s₆ hst.1 hst.2 (fun r hr => ?_) (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  rw [u₆.gpr, u₅.other _ hr, u₄.other _ hr, u₃.gpr, u₂.other _ hr, u₁.other _ hr]

/-! ## The XOR phase of a group -/

/-- After `k` blocks of the group have been XORed in, from `s₃`. -/
structure XS (m₀ : Mem) (D : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ : State) (k : Nat) (s : State) :
    Prop where
  data : DataInv m₀ s.mem D n (4 * g + k) ks
  frame : Frame [⟨D, 16 * n⟩] s₃.mem s.mem
  keep : ∀ r, r ≠ t0 → s.gpr r = s₃.gpr r
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr

/-- Before the XOR phase of group `g`: the keystream is in the words. -/
structure XPre (m₀ : Mem) (D : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ : State) : Prop where
  hg : 4 * g < n
  hn : 16 * n < 2 ^ 64
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₃.wr
  r6 : s₃.gpr .r6 = D + BitVec.ofNat 64 (64 * g)
  r7 : s₃.gpr .r7 = BitVec.ofNat 64 (n - 4 * g)
  data : DataInv m₀ s₃.mem D n (4 * g) ks
  ks : ∀ c < 4, ∀ t < 16, (s₃.gpr (q (c + 4 * (t / 8)))).extractLsb' (8 * (t % 8)) 8 =
    ks (16 * (4 * g + c) + t)

/-- After the XOR phase: no blocks are left, or group `g + 1` is next. -/
def XDone (m₀ : Mem) (D : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ s : State) : Prop :=
  Frame [⟨D, 16 * n⟩] s₃.mem s.mem ∧ (∀ r, r ≠ t0 → r ≠ .r6 → r ≠ .r7 → s.gpr r = s₃.gpr r) ∧
    s.rd = s₃.rd ∧ s.wr = s₃.wr ∧
    ((s.gpr .r7 = 0 ∧ DataInv m₀ s.mem D n n ks) ∨
     (4 * g + 4 < n ∧ DataInv m₀ s.mem D n (4 * (g + 1)) ks ∧
      s.gpr .r6 = D + BitVec.ofNat 64 (64 * (g + 1)) ∧ s.gpr .r7 = BitVec.ofNat 64 (n - 4 * (g + 1))))

section Xor

variable {m₀ : Mem} {D : Addr} {n g : Nat} {ks : Nat → Byte} {s₃ : State}

theorem xs_step (hp : XPre m₀ D n g ks s₃) {k : Nat} (hk : k < 4) (hkn : 4 * g + k < n) {s : State}
    (hs : XS m₀ D n g ks s₃ k s) {P : State → Prop} (h : ∀ s', XS m₀ D n g ks s₃ (k + 1) s' → P s') :
    WP isa (.block (xorBlock k)) s P := by
  refine xorBlock_wp hk hkn hp.hn (hs.wr ▸ hp.dat) (by rw [hs.keep _ (by decide)]; exact hp.r6)
    hs.data (fun t ht => by rw [hs.keep _ (q_ne_t0' _ (by omega_arith))]; exact hp.ks k hk t ht)
    fun s' d f o rd wr => h s' ⟨d, hs.frame.trans f, fun r hr => (o r hr).trans (hs.keep r hr),
      rd.trans hs.rd, wr.trans hs.wr⟩

theorem xs_zero (hp : XPre m₀ D n g ks s₃) {s : State} (hg : ∀ r, r ≠ t0 → s.gpr r = s₃.gpr r)
    (hm : s.mem = s₃.mem) (hrd : s.rd = s₃.rd) (hwr : s.wr = s₃.wr) : XS m₀ D n g ks s₃ 0 s :=
  ⟨by rw [hm, Nat.add_zero]; exact hp.data, by rw [hm]; exact Frame.refl _ _, hg, hrd, hwr⟩

theorem xs_t0 {k : Nat} {s s' : State} {v : BitVec 64} (hs : XS m₀ D n g ks s₃ k s) (u : Upd s s' t0 v) :
    XS m₀ D n g ks s₃ k s' :=
  ⟨u.mem ▸ hs.data, u.mem ▸ hs.frame, fun r h => (u.other r h).trans (hs.keep r h),
    u.rd.trans hs.rd, u.wr.trans hs.wr⟩

theorem xorFull_eq : xorFull = xorBlock 0 ++ xorBlock 1 ++ xorBlock 2 ++ xorBlock 3 ++
    ([.addi .r6 .r6 64, .subi .r7 .r7 4] : List Instr) := rfl

theorem ofNat_sub_ofNat' {x y : Nat} (h : y ≤ x) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 y = BitVec.ofNat 64 (x - y) := Offset.ofNat_sub_ofNat h

theorem off_add64 (D : Addr) (g : Nat) :
    D + BitVec.ofNat 64 (64 * g) + BitVec.ofNat 64 64 = D + BitVec.ofNat 64 (64 * (g + 1)) :=
  (Offset.add_add D _ 64).trans (by rw [show 64 * g + 64 = 64 * (g + 1) by omega_arith])

theorem ofNat_shr2 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 2 = BitVec.ofNat 64 (a / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- The branch on `t0 := r7 >>> 2`: four blocks or more left. -/
theorem shr2_wp {s : State} {k : Nat} (hk : k < 2 ^ 64) (h7 : s.gpr .r7 = BitVec.ofNat 64 k)
    {c : Prog isa} {P : State → Prop}
    (h : ∀ s', Upd s s' t0 (BitVec.ofNat 64 (k / 4)) →
      isa.eval (.nonzero .d t0) s' = some (decide (4 ≤ k)) → WP isa c s' P) :
    WP isa (.seq (.block [shrI t0 .r7 2]) c) s P := by
  refine WP.seq (wp_lsr (by decide) fun s' u => wp_nil ?_)
  rw [h7, ofNat_shr2 hk] at u
  refine h s' u ?_
  rw [eval_nonzero_ofNat' s' t0 (by omega) u.gpr]
  congr 1; exact decide_eq_decide.mpr (by omega)

theorem xorPhase_wp (hp : XPre m₀ D n g ks s₃) :
    WP isa (.seq (.block [shrI t0 .r7 2]) (.ite (.nonzero .d t0) (.block xorFull) xorTail)) s₃
      (XDone m₀ D n g ks s₃) := by
  have hg := hp.hg
  have hn := hp.hn
  refine shr2_wp (k := n - 4 * g) (by omega_arith) hp.r7 fun s₄ u₄ ev₄ => ?_
  have x₀ := xs_zero hp (fun r h => u₄.other r h) u₄.mem u₄.rd u₄.wr
  refine WP.ite (decide (4 ≤ n - 4 * g)) ev₄ (fun hb => ?_) (fun hb => ?_)
  · -- Four blocks.
    have h4 : 4 ≤ n - 4 * g := by simpa using hb
    rw [xorFull_eq]
    repeat rw [WP.block_append_iff (M := isa)]
    refine xs_step hp (k := 0) (by omega_arith) (by omega_arith) x₀ fun s₅ x₅ => ?_
    refine xs_step hp (k := 1) (by omega_arith) (by omega_arith) x₅ fun s₆ x₆ => ?_
    refine xs_step hp (k := 2) (by omega_arith) (by omega_arith) x₆ fun s₇ x₇ => ?_
    refine xs_step hp (k := 3) (by omega_arith) (by omega_arith) x₇ fun s₈ x₈ => ?_
    refine wp_addi (by decide) (by decide) fun s₉ u₉ => wp_subi (by decide) (by decide)
      fun s₁₀ u₁₀ => wp_nil ?_
    have e₁ : s₈.gpr .r6 = D + BitVec.ofNat 64 (64 * g) := (x₈.keep _ (by decide)).trans hp.r6
    have e₂ : s₈.gpr .r7 = BitVec.ofNat 64 (n - 4 * g) := (x₈.keep _ (by decide)).trans hp.r7
    have r7' : s₁₀.gpr .r7 = BitVec.ofNat 64 (n - 4 * (g + 1)) := by
      rw [u₁₀.gpr, u₉.other _ (by decide), e₂, ofNat_sub_ofNat' h4,
        show n - 4 * g - 4 = n - 4 * (g + 1) by omega_arith]
    refine ⟨by rw [u₁₀.mem, u₉.mem]; exact x₈.frame, fun r h1 h2 h3 => ?_,
      by rw [u₁₀.rd, u₉.rd]; exact x₈.rd, by rw [u₁₀.wr, u₉.wr]; exact x₈.wr, ?_⟩
    · rw [u₁₀.other _ h3, u₉.other _ h2]; exact x₈.keep r h1
    have hd : DataInv m₀ s₁₀.mem D n (4 * (g + 1)) ks := by
      rw [u₁₀.mem, u₉.mem]; simpa [Nat.mul_add] using x₈.data
    by_cases hl : n - 4 * g = 4
    · refine .inl ⟨by rw [r7', show n - 4 * (g + 1) = 0 by omega_arith]; rfl,
        dataInv_mono hd (by omega_arith) (by omega_arith)⟩
    · refine .inr ⟨by omega_arith, hd, ?_, r7'⟩
      rw [u₁₀.other _ (by decide), u₉.gpr, e₁]; exact off_add64 D g
  · -- The last one to three blocks.
    have h4 : n - 4 * g < 4 := by simpa using hb
    unfold xorTail
    refine WP.seq ?_
    rw [WP.block_append_iff (M := isa)]
    refine xs_step hp (k := 0) (by omega_arith) (by omega_arith) x₀ fun s₅ x₅ => ?_
    refine wp_subi (by decide) (by decide) fun s₆ u₆ => wp_nil ?_
    have x₆ := xs_t0 x₅ u₆
    have r7₅ : s₅.gpr .r7 = BitVec.ofNat 64 (n - 4 * g) := (x₅.keep _ (by decide)).trans hp.r7
    have t₆ : s₆.gpr t0 = BitVec.ofNat 64 (n - 4 * g - 1) := by
      rw [u₆.gpr, r7₅, ofNat_sub_ofNat' (by omega_arith)]
    refine WP.seq (WP.mono (Q := XS m₀ D n g ks s₃ (n - 4 * g)) ?_ fun s hs => ?_)
    · refine WP.ite (decide (n - 4 * g - 1 ≠ 0)) (eval_nonzero_ofNat' s₆ t0 (by omega_arith) t₆)
        (fun hb => ?_) (fun hb => ?_)
      · have h2 : 2 ≤ n - 4 * g := by simp at hb; omega_arith
        refine WP.seq ?_
        rw [WP.block_append_iff (M := isa)]
        refine xs_step hp (k := 1) (by omega_arith) (by omega_arith) x₆ fun s₇ x₇ => ?_
        refine wp_subi (by decide) (by decide) fun s₈ u₈ => wp_nil ?_
        have x₈ := xs_t0 x₇ u₈
        have r7₇ : s₇.gpr .r7 = BitVec.ofNat 64 (n - 4 * g) := (x₇.keep _ (by decide)).trans hp.r7
        have z₈ : isa.eval (.zero .d t0) s₈ = some (decide (n - 4 * g = 3)) := by
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
    · refine wp_li (by decide) fun s' u' => wp_nil ?_
      refine ⟨by rw [u'.mem]; exact hs.frame, fun r h1 _ h3 => (u'.other r h3).trans (hs.keep r h1),
        by rw [u'.rd]; exact hs.rd, by rw [u'.wr]; exact hs.wr, .inl ⟨u'.gpr, ?_⟩⟩
      have := hs.data
      rw [show 4 * g + (n - 4 * g) = n by omega_arith, ← u'.mem] at this
      exact this

end Xor

/-! ## A group -/

/-- What the group loop runs with: `s₂` is the state after the round keys
are bitsliced, `b` the scratch buffer, `D` the data (`n` blocks), `icb` the
first counter block. -/
structure GSetup (s₂ : State) (b D : Addr) (n R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) :
    Prop where
  scr : (⟨b, 2048⟩ : Region) ∈ s₂.wr
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₂.wr
  hn : 16 * n < 2 ^ 64
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 2048⟩
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  keys : KeysAt s₂.mem (b + BitVec.ofNat 64 (1920 - 64 * R)) R w
  lo : ∀ i < 8, ∀ j < 8, (cloW s₂.mem b).getLsbD (8 * i + j) = icb.getLsbD (8 * (15 - i) + j)
  hi : ∀ i < 4, ∀ j < 8, (chiLo s₂.mem b).getLsbD (8 * i + j) = icb.getLsbD (8 * (7 - i) + j)

/-- The memory a group writes: slots 0–39, the counter and the data. -/
abbrev gRegions (b D : Addr) (n : Nat) : List Region :=
  [⟨b, 320⟩, ctrRegion b, ⟨D, 16 * n⟩]

/-- Before group `g`. -/
structure GInv (m₀ : Mem) (s₂ : State) (b D : Addr) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (g : Nat) (s : State) : Prop where
  hg : 4 * g < n
  r6 : s.gpr .r6 = D + BitVec.ofNat 64 (64 * g)
  r7 : s.gpr .r7 = BitVec.ofNat 64 (n - 4 * g)
  base : s.gpr sb = b
  r3 : s.gpr .r3 = b + BitVec.ofNat 64 (1920 - 64 * R)
  r2 : s.gpr .r2 = s₂.gpr .r2
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (gRegions b D n) s₂.mem s.mem
  num : numW s.mem b = (icb.extractLsb' 0 32).setWidth 64 + BitVec.ofNat 64 (4 * g)
  data : DataInv m₀ s.mem D n (4 * g) (keyStream R w icb)

/-- After the last group. -/
structure GDone (m₀ : Mem) (s₂ : State) (b D : Addr) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (s : State) : Prop where
  base : s.gpr sb = b
  r2 : s.gpr .r2 = s₂.gpr .r2
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (gRegions b D n) s₂.mem s.mem
  data : DataInv m₀ s.mem D n n (keyStream R w icb)

theorem scr_disj (b : Addr) {lx y ly : Nat} (h : lx ≤ y) (hy : y + ly ≤ 2048) :
    Region.Disjoint ⟨b, lx⟩ ⟨b + BitVec.ofNat 64 y, ly⟩ := Offset.base_disjoint b h (by omega_arith)

theorem scr_sub (b : Addr) {x lx : Nat} (h : x + lx ≤ 2048) :
    Region.Sub ⟨b + BitVec.ofNat 64 x, lx⟩ ⟨b, 2048⟩ := Offset.sub_base b h

theorem keysAt_frame {m m' : Mem} {b : Addr} {R : Nat} {w : List Byte} {rs : List Region}
    (hR : R ≤ 14) (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + 1024, 1024⟩ r)
    (h : KeysAt m (b + BitVec.ofNat 64 (1920 - 64 * R)) R w) :
    KeysAt m' (b + BitVec.ofNat 64 (1920 - 64 * R)) R w :=
  fun j hj => keyRel_congr (h j hj) fun k hk => hf.readW (key_contains _ hR hj hk) hd (by decide)

theorem dataInv_frame {m₀ m m' : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : DataInv m₀ m D n k ks) : DataInv m₀ m' D n k ks := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega_arith) hi

theorem GSetup.dat_disj {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (hs : GSetup s₂ b D n R w icb) {x lx : Nat} (h : x + lx ≤ 2048) :
    Region.Disjoint ⟨D, 16 * n⟩ ⟨b + BitVec.ofNat 64 x, lx⟩ :=
  hs.sep.sub_right (scr_sub b h)

theorem GSetup.keys_disj {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (hs : GSetup s₂ b D n R w icb) : ∀ r ∈ gRegions b D n, Region.Disjoint ⟨b + 1024, 1024⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact keys_disjoint b
  · exact Offset.disjoint b (d := 1024) (e := 8 * 59 + 4) (by omega) (by omega) (by omega)
  · exact (hs.sep.sub_right (Offset.sub_base b (d := 1024) (n := 1024) (by omega))).symm

theorem GSetup.slot_disj {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (hs : GSetup s₂ b D n R w icb) {x lx : Nat} (h1 : 320 ≤ x) (h2 : x + lx ≤ 476 ∨ 488 ≤ x)
    (h3 : x + lx ≤ 2048) : ∀ r ∈ gRegions b D n, Region.Disjoint ⟨b + BitVec.ofNat 64 x, lx⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (scr_disj b h1 h3).symm
  · exact Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
  · exact (hs.dat_disj h3).symm

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

/-- One group: from before group `g`, to after the last group (`r7 = 0`) or
before group `g + 1`. -/
theorem group_ok {m₀ : Mem} {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (hs : GSetup s₂ b D n R w icb) {g : Nat} {s : State}
    (hi : GInv m₀ s₂ b D n R w icb g s) :
    WP isa group s fun s' =>
      (isa.eval (.nonzero .d .r7) s' = some false ∧ GDone m₀ s₂ b D n R w icb s') ∨
      (isa.eval (.nonzero .d .r7) s' = some true ∧ GInv m₀ s₂ b D n R w icb (g + 1) s') := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega_arith
  have hn := hs.hn
  have hscr : (⟨b, 2048⟩ : Region) ∈ s.wr := hi.wr ▸ hs.scr
  unfold group
  refine WP.seq (WP.mono (ctrBlocks_wp hi.base hscr) fun s₁ ⟨hq₁, o₁, f₁, num₁, rd₁, wr₁⟩ => ?_)
  have hb₁ : s₁.gpr sb = b := (o₁ sb (by decide) (by decide)).trans hi.base
  have hf₁ : Frame (gRegions b D n) s₂.mem s₁.mem :=
    hi.frame.trans (f₁.mono fun r hr => by simp at hr; simp [hr])
  have clo : cloW s.mem b = cloW s₂.mem b :=
    hi.frame.readW (Region.contains_self _ _) (hs.slot_disj (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)
  have chi : chiLo s.mem b = chiLo s₂.mem b :=
    hi.frame.readW (Region.contains_self _ _) (hs.slot_disj (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)
  have hp : EncPre s₁ R w :=
    ⟨by rw [hb₁, wr₁, hi.wr]; exact hs.scr, hs.rounds,
      by rw [o₁ .r3 (by decide) (by decide), hi.r3, hb₁],
      by rw [o₁ .r3 (by decide) (by decide), hi.r3]; exact keysAt_frame hR hf₁ hs.keys_disj hs.keys⟩
  have hin : InRel (Q s₁) (fun c => ctrState icb (4 * g + c)) :=
    ctr_inRel (by rw [clo]; exact hs.lo) (by rw [chi]; exact hs.hi) (by rw [hi.num]; exact num_lo icb g)
      hq₁
  refine WP.seq (WP.mono (encrypt4_ok hp hin) fun s₃ ⟨hc₃, hin₃⟩ => ?_)
  have fr₃ := hc₃.frame
  rw [hb₁] at fr₃
  have d320 : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 320⟩ := hs.sep.sub_right (Region.sub_prefix (by omega_arith))
  have hx : XPre m₀ D n g (keyStream R w icb) s₃ :=
    { hg := hi.hg, hn := hn, dat := by rw [hc₃.wr, wr₁, hi.wr]; exact hs.dat
      r6 := by rw [hc₃.keep .r6 (by decide) (by decide), o₁ .r6 (by decide) (by decide), hi.r6]
      r7 := by rw [hc₃.keep .r7 (by decide) (by decide), o₁ .r7 (by decide) (by decide), hi.r7]
      data := dataInv_frame fr₃ (by simpa using d320) hn
        (dataInv_frame f₁ (by simpa using hs.dat_disj (by omega_arith)) hn hi.data)
      ks := fun c hc t ht => ks_of_inRel hin₃ hc ht }
  refine WP.mono (xorPhase_wp hx) fun s' ⟨f', o', rd', wr', hz⟩ => ?_
  have keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .r10 → r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => (o' r (fun h => h1 (h ▸ by decide)) h4 h5).trans
      ((hc₃.keep r h1 h2).trans (o₁ r h1 h3))
  have base' : s'.gpr sb = b :=
    (keep sb (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi.base
  have r2' : s'.gpr .r2 = s₂.gpr .r2 :=
    (keep .r2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi.r2
  have rd'' : s'.rd = s₂.rd := by rw [rd', hc₃.rd, rd₁, hi.rd]
  have wr'' : s'.wr = s₂.wr := by rw [wr', hc₃.wr, wr₁, hi.wr]
  have frame' : Frame (gRegions b D n) s₂.mem s'.mem :=
    hf₁.trans ((fr₃.mono fun r hr => by simp at hr; simp [hr]).trans (f'.mono fun r hr => by simp at hr; simp [hr]))
  rcases hz with ⟨z, d⟩ | ⟨h4, d, r6', r7'⟩
  · refine .inl ⟨by rw [eval_nonzero, z]; rfl, base', r2', rd'', wr'', frame', d⟩
  · refine .inr ⟨by rw [eval_nonzero_ofNat' s' .r7 (by omega_arith) r7']; simp; omega_arith,
      ⟨by omega_arith, r6', r7', base', ?_, r2', rd'', wr'', frame', ?_, d⟩⟩
    · rw [keep .r3 (by decide) (by decide) (by decide) (by decide) (by decide), hi.r3]
    · have e₁ : numW s'.mem b = numW s₃.mem b :=
        f'.readW (Region.contains_self _ _) (by simpa using (hs.dat_disj (by omega_arith)).symm) (by decide)
      have e₂ : numW s₃.mem b = numW s₁.mem b :=
        fr₃.readW (Region.contains_self _ _) (by simpa using (scr_disj b (by omega_arith) (by omega_arith)).symm)
          (by decide)
      rw [e₁, e₂, num₁, hi.num, num_succ]

/-- The loop over the groups. -/
theorem groups_ok {m₀ : Mem} {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (hs : GSetup s₂ b D n R w icb) {s : State}
    (hi : GInv m₀ s₂ b D n R w icb 0 s) :
    WP isa (.loop group (.nonzero .d .r7)) s (GDone m₀ s₂ b D n R w icb) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 4 * g ∧ GInv m₀ s₂ b D n R w icb g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (group_ok hs hg) fun s' h => ?_) n s ⟨0, by omega_arith, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, n - 4 * (g + 1), by have := hg.hg; omega_arith, g + 1, rfl, d⟩

end VG.Proof.Aes.PPC64LE
