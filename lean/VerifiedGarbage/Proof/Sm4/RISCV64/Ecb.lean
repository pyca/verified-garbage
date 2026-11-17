module

public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.Proof.Sm4.RISCV64.Prologue
import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit
public import VerifiedGarbage.Proof.Sm4.Common
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.CopyFast
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Spill

/-! ### `Sm4.RISCV64.Group`, which this module and modules that import it used -/

section

/-! ### `Sm4.RISCV64.Crypt16`, which this module and modules that import it used -/

section

/-!
# The transposes, and sixteen blocks of bitsliced SM4 on RISCV64

`toBs_step` turns the sixteen blocks of the tail buffer into the state's
planes, and `fromBs_step` turns the state's planes back into the output
blocks (the words in reverse order); `crypt16_wp` composes them with the
32 rounds (`rounds_wp`): each block of the tail buffer becomes the output
of SM4's rounds with the table's round keys.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 movR)
open VG.Proof.Aes.RISCV64 (sboxWrites restRegs not_sboxWrites)
open VG.Proof.Sm4 (WordRel quads ofBlock outBlock readW64_bit getLsbD_wordAt getLsbD_outBlock' blockAt_getD)
open VG.Impl.Sm4 (Lin)

/-- Block `b` of the tail buffer. -/
abbrev tailBlock (s : State) (b : Nat) : Spec.Sm4.Block :=
  Spec.Sm4.blockAt s.mem (s.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * b))

theorem KeyCtx.of_ctx {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) :
    KeyCtx s E where
  scr := by rw [hc.wr, hc.base]; exact hp.scr
  fit := by rw [hc.base]; exact hp.fit
  al := by rw [hc.base]; exact hp.al
  keys e he := by rw [hc.base]; exact (hp.keys e he).congr fun j hj => hc.entry hp he hj

theorem Ctx.trans {s₀ s₁ s₂ : State} (h₁ : Ctx s₀ s₁) (h₂ : Ctx s₁ s₂) : Ctx s₀ s₂ :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r a b => (h₂.keep r a b).trans (h₁.keep r a b),
    h₁.frame.trans (by rw [← h₁.base]; exact h₂.frame), h₂.masks⟩

theorem ok_bs {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) : Ok bsCfg s where
  slotIn k hk := ⟨_, by rw [hc.wr]; exact hp.scr, by
    have hfit := hp.fit
    simp only [bsCfg, tableSlot_eq] at hk
    simp only [wordAddr, bsCfg, hc.base]
    rw [slots_eq] at hfit ⊢
    exact VG.Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩
  extIn k hk := by simp [bsCfg] at hk
  baseAl _ := by simp only [bsCfg]; rw [hc.base]; exact hp.al
  extAl h := by simp [bsCfg] at h
  slots := by simp only [bsCfg, tableSlot_eq]; omega_using []
  sep k _ j hj := by simp [bsCfg] at hj

/-- What a block of slots below the table that keeps the masks keeps of `Ctx`. -/
theorem Ctx.bs {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) (hf : Frame [slotRegion bsCfg s] s.mem s'.mem)
    (hm : MasksOk s') : Ctx s₀ s' :=
  hc.step hrd hwr (fun r h _ => hk r h) (hf.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, bsCfg, hc.base]) hm

theorem byte_addr (b : Addr) {k i : Nat} {n : Nat} (hn : 8 * k + i = n) :
    wordAddr b k + BitVec.ofNat 64 i = b + BitVec.ofNat 64 n := by
  rw [wordAddr, addr_add, hn]

/-- The tail buffer's blocks to the state's planes. -/
theorem toBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) :
    ∃ s', runBlock isa toBs s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kr = s.gpr kr ∧
      StRel s' (fun b w => ofBlock (tailBlock s b) w) := by
  have hchk := toBs_check
  unfold toBsEnv at hchk
  obtain ⟨s', h', -, hso, hkr, rd', wr', -, o', f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (tailSlot + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      simp only [tailIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk, rfl, rfl⟩ := hji
      exact ⟨by simp only [bsCfg, tableSlot_eq, tailSlot_eq]; omega_using [hk], by omega_using [hk], rfl⟩)
    (fun kv hkv => ⟨by have := mask_lt hkv; simp only [bsCfg, tableSlot_eq]; omega_using [this], hc.masks kv hkv⟩)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso hkr
  have hall : (restRegs.all fun r => toBs.all fun i => dst i != some r) = true := by
    lit_decide
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  refine ⟨s', h', hc.bs rd' wr' hkeep f' (fun kv hkv => ?_), hkeep _ (by decide), fun w hw b hb i hi j hj => ?_⟩
  · rw [slotW, hb', hkr kv.1 (List.mem_map_of_mem hkv) (by have := mask_lt hkv; rw [tableSlot_eq]; omega_using [this])]
    exact hc.masks kv hkv
  · have hp16 : 16 * i + b < 64 := by omega_using [hb, hi]
    have hmem := hso (64 + (8 * w + j)) (toBsG ((8 * w + j) / 8) ((8 * w + j) % 8)) (by
        simp only [toBsOuts, List.mem_map, List.mem_range]; exact ⟨8 * w + j, by omega_using [hw, hj], rfl⟩)
        (by rw [tableSlot_eq]; omega_using [hw, hj]) _ hp16
    rw [show (8 * w + j) / 8 = w by omega_using [hj], show (8 * w + j) % 8 = j by omega_using [hj]] at hmem
    have ht : 8 * (4 * (w % 2) + i) + j < 64 := by omega_using [hi, hj]
    show (slotW s' (stateSlot w j)).getLsbD (16 * i + b) = _
    rw [slotW, hb', show stateSlot w j = 64 + (8 * w + j) by simp only [stateSlot]; omega_using [], hmem, toBsG,
      show (16 * i + b) % 16 = b by omega_using [hb], show (16 * i + b) / 16 = i by omega_using [hb], xorBits_cons, xorBits_nil,
      Bool.xor_false, Nat.add_assoc, bitOf_word _ _ _ ht, slotW, readW64_bit _ _ (by omega_using [hi]) hj]
    simp only [ofBlock]
    rw [getLsbD_wordAt _ _ hi hj, blockAt_getD _ _ (by omega_using [hw, hi]), byte_addr _ rfl, addr_add]
    rw [show 8 * (tailSlot + (2 * b + w / 2)) + (4 * (w % 2) + i) = 8 * tailSlot + 16 * b + (4 * w + i) by omega_using []]

/-- The state's planes back to the tail buffer's blocks. -/
theorem fromBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s X) :
    ∃ s', runBlock isa fromBs s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kr = s.gpr kr ∧ StRel s' X ∧
      ∀ b < 16, tailBlock s' b = outBlock (X b) := by
  have hchk := fromBs_check
  unfold fromBsEnv at hchk
  obtain ⟨s', h', -, hso, hkr, rd', wr', -, o', f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (64 + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by simp only [bsCfg, tableSlot_eq]; omega_arith, by omega_arith, by simp only [Nat.zero_add]; rfl⟩)
    (fun kv hkv => ⟨by have := mask_lt hkv; simp only [bsCfg, tableSlot_eq]; omega_arith, hc.masks kv hkv⟩)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso hkr
  have hall : (restRegs.all fun r => fromBs.all fun i => dst i != some r) = true := by
    lit_decide
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  have keep : ∀ k ∈ keyMaskSlots ++ stateSlots, slotW s' k = slotW s k := fun k hk => by
    have hk' : k < 128 := (keep_range k hk).2
    rw [slotW, hb', hkr k hk (by rw [tableSlot_eq]; exact hk')]
  refine ⟨s', h', hc.bs rd' wr' hkeep f' (fun kv hkv => ?_), hkeep _ (by decide), ?_, fun b hb => ?_⟩
  · rw [keep kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv))]; exact hc.masks kv hkv
  · exact fun w hw => (hX w hw).congr fun j hj => by
      show slotW s' (stateSlot w j) = slotW s (stateSlot w j)
      exact keep _ (List.mem_append_right _ (by
        simp only [stateSlots, List.mem_map, List.mem_range]
        exact ⟨8 * w + j, by omega_arith, by simp only [stateSlot]; omega_arith⟩))
  · apply Vector.ext
    intro k hk
    refine BitVec.eq_of_getLsbD_eq fun j hj => ?_
    rw [getLsbD_outBlock' (X b) hk hj]
    have ht : 8 * (k % 8) + j < 64 := by omega_arith
    have hmem := hso (tailSlot + (2 * b + k / 8)) (fromBsG (2 * b + k / 8)) (by
        simp only [fromBsOuts, List.mem_map, List.mem_range]; exact ⟨2 * b + k / 8, by omega_arith, rfl⟩)
        (by rw [tableSlot_eq, tailSlot_eq]; omega_arith) _ ht
    rw [readW64_bit _ _ (by omega_arith) hj, byte_addr _ rfl] at hmem
    have e1 : 8 * (3 - (2 * ((2 * b + k / 8) % 2) + (8 * (k % 8) + j) / 32)) + (8 * (k % 8) + j) % 8 =
        8 * (3 - k / 4) + j := by omega_arith
    have e2 : 16 * ((8 * (k % 8) + j) / 8 % 4) + (2 * b + k / 8) / 2 = 16 * (k % 4) + b := by omega_arith
    have hw : 3 - k / 4 < 4 := by omega_arith
    have hbit := hX (3 - k / 4) hw b hb (k % 4) (by omega_arith) j hj
    rw [fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false, e1, Nat.add_assoc, e2, bitOf_word _ _ _ (by omega_arith)] at hmem
    simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
    rw [addr_add, show 8 * tailSlot + 16 * b + k = 8 * (tailSlot + (2 * b + k / 8)) + k % 8 by omega_arith,
      hb', hmem, ← hbit, planes_eq]

/-- The state's planes of block 0 back to the tail buffer's first block (`fromBs0`). -/
theorem fromBs0_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s X) :
    ∃ s', runBlock isa fromBs0 s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kr = s.gpr kr ∧ StRel s' X ∧
      tailBlock s' 0 = outBlock (X 0) := by
  have hchk := fromBs0_check
  unfold fromBsEnv at hchk
  obtain ⟨s', h', -, hso, hkr, rd', wr', -, o', f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (64 + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by simp only [bsCfg, tableSlot_eq]; omega_arith, by omega_arith, by simp only [Nat.zero_add]; rfl⟩)
    (fun kv hkv => ⟨by have := mask_lt hkv; simp only [bsCfg, tableSlot_eq]; omega_arith, hc.masks kv hkv⟩)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso hkr
  have hall : (restRegs.all fun r => fromBs0.all fun i => dst i != some r) = true := by
    lit_decide
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  have keep : ∀ k ∈ keyMaskSlots ++ stateSlots, slotW s' k = slotW s k := fun k hk => by
    have hk' : k < 128 := (keep_range k hk).2
    rw [slotW, hb', hkr k hk (by rw [tableSlot_eq]; exact hk')]
  refine ⟨s', h', hc.bs rd' wr' hkeep f' (fun kv hkv => ?_), hkeep _ (by decide), ?_, ?_⟩
  · rw [keep kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv))]; exact hc.masks kv hkv
  · exact fun w hw => (hX w hw).congr fun j hj => by
      show slotW s' (stateSlot w j) = slotW s (stateSlot w j)
      exact keep _ (List.mem_append_right _ (by
        simp only [stateSlots, List.mem_map, List.mem_range]
        exact ⟨8 * w + j, by omega_arith, by simp only [stateSlot]; omega_arith⟩))
  · apply Vector.ext
    intro k hk
    refine BitVec.eq_of_getLsbD_eq fun j hj => ?_
    rw [getLsbD_outBlock' (X 0) hk hj]
    have ht : 8 * (k % 8) + j < 64 := by omega_arith
    have hmem := hso (tailSlot + (2 * 0 + k / 8)) (fromBsG (2 * 0 + k / 8)) (by
        simp only [fromBs0Outs, List.mem_map, List.mem_range]; exact ⟨2 * 0 + k / 8, by omega_arith, rfl⟩)
        (by rw [tableSlot_eq, tailSlot_eq]; omega_arith) _ ht
    rw [readW64_bit _ _ (by omega_arith) hj, byte_addr _ rfl] at hmem
    have e1 : 8 * (3 - (2 * ((2 * 0 + k / 8) % 2) + (8 * (k % 8) + j) / 32)) + (8 * (k % 8) + j) % 8 =
        8 * (3 - k / 4) + j := by omega_arith
    have e2 : 16 * ((8 * (k % 8) + j) / 8 % 4) + (2 * 0 + k / 8) / 2 = 16 * (k % 4) + 0 := by omega_arith
    have hw : 3 - k / 4 < 4 := by omega_arith
    have hbit := hX (3 - k / 4) hw 0 (by decide) (k % 4) (by omega_arith) j hj
    rw [fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false, e1, Nat.add_assoc, e2, bitOf_word _ _ _ (by omega_arith)] at hmem
    simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
    rw [addr_add, show 8 * tailSlot + 16 * 0 + k = 8 * (tailSlot + (2 * 0 + k / 8)) + k % 8 by omega_arith,
      hb', hmem, ← hbit, planes_eq]

/-- `crypt16`: each block of the tail buffer becomes the output of SM4's 32
rounds with the table's round keys. -/
theorem crypt16_wp {s₀ : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hm : MasksOk s₀)
    (ha0 : s₀.gpr .a0 = s₀.gpr sb + BitVec.ofNat 64 (8 * tableEnd)) :
    WP isa crypt16 s₀ fun s' => Ctx s₀ s' ∧
      ∀ b < 16, tailBlock s' b = outBlock (quads .enc E 8 (ofBlock (tailBlock s₀ b))) := by
  obtain ⟨s₁, e₁, c₁, -, X₁⟩ := toBs_step hp (Ctx.refl hm)
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have ha0₁ : s₁.gpr .a0 = s₁.gpr sb + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [c₁.keep _ (by decide) (by decide), c₁.base, ha0]
  refine WP.seq (WP.mono (rounds_wp .enc (hp.of_ctx c₁) c₁.masks ha0₁ X₁) fun s₂ ⟨c₂, X₂⟩ => ?_)
  have c₀₂ := c₁.trans c₂
  obtain ⟨s₃, e₃, c₃, -, -, hout⟩ := fromBs_step hp c₀₂ X₂
  exact WP.of_runBlock ⟨s₃, e₃, c₃, hout⟩

end VG.Proof.Sm4.RISCV64

end

end

/-! ### `Sm4.RISCV64.Keys`, which this module and modules that import it used -/

section

/-!
# The table of bitsliced round keys on RISCV64

`keyOne_step`: `keyOne h` bitslices round key `2 m + h`, half `h` of the
64-bit word at `a0`, into the table's entry at `kr`, every block's copy of
it alike. `keys_wp` copies the schedule to the tail buffer, which is
aligned, and builds the table from the copy in the order the rounds use the
round keys: `rk₀ … rk₃₁` for encryption, `rk₃₁ … rk₀` for decryption. As on
PPC64LE (`Proof/Sm4/PPC64LE/Ecb.lean`), which reads the schedule itself.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 movR)
open VG.Proof.Aes.RISCV64 (sboxWrites restRegs not_sboxWrites)
open VG.Proof.Sm4 (WordRel readW64_bit getLsbD_scheduleAt)

/-! ## The fill of a round key's planes

A plane has its bits at `16 i` (`keyBit`), and `keyFill` fills each
16-bit group with its bit: `(x ⋘ 16) - x` is `x · 0xFFFF`, which, with no
carries between the groups, copies bit `16 i` to bits `16 i … 16 i + 15`.
`getLsbD_fill` proves it for the sixteen such words, by evaluation, and
`keyFill_ok` runs the code. -/

/-- What `keyFill` makes of a plane. -/
def fill (x : BitVec 64) : BitVec 64 := (x <<< 16) - x

/-- The word with bits `b₀ … b₃` at `0`, `16`, `32` and `48`. -/
def sparse (b₀ b₁ b₂ b₃ : Bool) : BitVec 64 :=
  (if b₀ then 1 else 0) ||| (if b₁ then 0x10000 else 0) ||| (if b₂ then 0x100000000 else 0) |||
    (if b₃ then 0x1000000000000 else 0)

theorem getLsbD_sparse : ∀ b₀ b₁ b₂ b₃ : Bool, ∀ p < 64, (sparse b₀ b₁ b₂ b₃).getLsbD p =
    (decide (p = 0) && b₀ || decide (p = 16) && b₁ || decide (p = 32) && b₂ || decide (p = 48) && b₃) := by
  decide +kernel

theorem getLsbD_fill_sparse : ∀ b₀ b₁ b₂ b₃ : Bool, ∀ p < 64,
    (fill (sparse b₀ b₁ b₂ b₃)).getLsbD p = (sparse b₀ b₁ b₂ b₃).getLsbD (16 * (p / 16)) := by
  decide +kernel

/-- A word with its bits at `16 i` only, filled: bit `p` is bit `16 ⌊p / 16⌋`. -/
theorem getLsbD_fill {x : BitVec 64} (hx : ∀ p < 64, p % 16 ≠ 0 → x.getLsbD p = false) {p : Nat}
    (hp : p < 64) : (fill x).getLsbD p = x.getLsbD (16 * (p / 16)) := by
  obtain hs : x = sparse (x.getLsbD 0) (x.getLsbD 16) (x.getLsbD 32) (x.getLsbD 48) := by
    refine BitVec.eq_of_getLsbD_eq fun k hk => ?_
    rw [getLsbD_sparse _ _ _ _ k hk]
    by_cases h : k % 16 = 0
    · have : k = 0 ∨ k = 16 ∨ k = 32 ∨ k = 48 := by omega_using [hk, h]
      rcases this with rfl | rfl | rfl | rfl <;> simp
    · have : k ≠ 0 ∧ k ≠ 16 ∧ k ≠ 32 ∧ k ≠ 48 := by omega_using [h]
      simp [hx k hk h, this.1, this.2.1, this.2.2.1, this.2.2.2]
  rw [hs]
  exact getLsbD_fill_sparse _ _ _ _ p hp

/-- `r := ` its fill, through `t0`. -/
theorem fillOne_ok (s : State) {r : Reg} (hr : r ≠ t0) :
    ∃ s', runBlock isa [VG.Impl.Aes.RISCV64.shlI t0 r 16, .sub r t0 r] s = some s' ∧ s'.gpr r = fill (s.gpr r) ∧
      (∀ r', r' ≠ r → r' ≠ t0 → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write t0 (s.gpr r <<< 16)
  refine ⟨s₁.write r (s₁.gpr t0 - s₁.gpr r),
    by simp only [VG.Impl.Aes.RISCV64.shlI, runBlock_cons, exec_shift_d (show 16 < 64 by decide), runStep_some]; rfl,
    ?_, fun r' h1 h2 => ?_, rfl, rfl, rfl⟩
  · simp only [s₁]
    rw [RegUpd.gpr_write_self, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ hr]; rfl
  · simp only [s₁]
    rw [RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]

/-- The registers `rs`, each to its fill. -/
theorem fillList_ok : ∀ (rs : List Reg), rs.Nodup → t0 ∉ rs → ∀ s : State,
    ∃ s', runBlock isa (rs.flatMap fun r => [VG.Impl.Aes.RISCV64.shlI t0 r 16, .sub r t0 r]) s = some s' ∧
      (∀ r ∈ rs, s'.gpr r = fill (s.gpr r)) ∧ (∀ r, r ∉ rs → r ≠ t0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], _, _, s => ⟨s, rfl, by simp, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  | r :: rs, hn, ht, s => by
    obtain hr : r ≠ t0 := fun h => ht (h ▸ List.mem_cons_self)
    obtain hn' := List.nodup_cons.mp hn
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := fillOne_ok s hr
    obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := fillList_ok rs hn'.2 (fun h => ht (List.mem_cons_of_mem _ h)) s₁
    refine ⟨s₂, by rw [List.flatMap_cons, Interleave.runBlock_append, e₁, Option.bind_some, e₂], fun r' hr' => ?_,
      fun r' h1 h2 => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rcases List.mem_cons.mp hr' with rfl | h
      · rw [o₂ _ hn'.1 hr, v₁]
      · rw [v₂ r' h, o₁ r' (fun e => hn'.1 (e ▸ h)) (fun e => ht (e ▸ List.mem_cons_of_mem _ h))]
    · rw [o₂ r' (fun h => h1 (List.mem_cons_of_mem _ h)) h2, o₁ r' (fun h => h1 (h ▸ List.mem_cons_self)) h2]

/-- `keyFill`: each plane to its fill. -/
theorem keyFill_ok (s : State) :
    ∃ s', runBlock isa VG.Impl.Sm4.RISCV64.keyFill s = some s' ∧
      (∀ j < 8, s'.gpr (q j) = fill (s.gpr (q j))) ∧
      (∀ r, (∀ j < 8, r ≠ q j) → r ≠ t0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hq : (List.range 8).map q = [q 0, q 1, q 2, q 3, q 4, q 5, q 6, q 7] := rfl
  obtain ⟨s', e', v', o', m', rd', wr'⟩ := fillList_ok ((List.range 8).map q) (by rw [hq]; decide)
    (by rw [hq]; decide) s
  refine ⟨s', by rw [VG.Impl.Sm4.RISCV64.keyFill]; rw [List.flatMap_map] at e'; exact e', fun j hj =>
    v' _ (List.mem_map_of_mem (List.mem_range.mpr hj)), fun r hr h0 => o' r (fun h => ?_) h0, m', rd', wr'⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
  exact hr j (List.mem_range.mp hj) rfl

/-- Round key `2 m + h`, half `h` of the 64-bit word `x`. -/
def rkWord (x : BitVec 64) (h : Nat) : Spec.Sm4.Word := (x >>> (32 * h)).setWidth 32

theorem keyStore_eq (h : Nat) : keyOne h = keyLoad h ++ keyStore := rfl

/-- Round key `2 m + h` from the word at `r3` to the entry at `kr`. -/
theorem keyOne_step {s : State} {b : Addr} {e h : Nat} (hh : h = 0 ∨ h = 1)
    (hb : s.gpr sb = b) (hal : b.toNat % 8 = 0) (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hkr : s.gpr kr = b + BitVec.ofNat 64 (8 * tableSlot + 64 * e)) (he : e < 32)
    (hx0 : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .a0) 0) 8) (hxal : (s.gpr .a0).toNat % 8 = 0)
    (hsep : ∀ k < 64, Mem.Sep (wordAddr b k) 8 (wordAddr (s.gpr .a0) 0) 8)
    (hm : MasksOk s) :
    ∃ s', runBlock isa (keyOne h) s = some s' ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ MasksOk s' ∧
      Frame [⟨b, 8 * 64⟩, ⟨b + BitVec.ofNat 64 (8 * tableSlot + 64 * e), 64⟩] s.mem s'.mem ∧
      WordRel (entryW s'.mem b e) (fun _ => rkWord (s.mem.readW (wordAddr (s.gpr .a0) 0) 64) h) := by
  rw [slots_eq] at hscr
  obtain hok : Ok keyCfg s :=
    { slotIn := fun k hk => ⟨_, hscr, by
        simp only [keyCfg] at hk ⊢
        rw [hb]; exact VG.Offset.contains_base b (by omega_arith) (by omega_arith)⟩
      extIn := fun k hk => by simp only [keyCfg] at hk ⊢; obtain rfl : k = 0 := by omega_arith
                              exact hx0
      baseAl := fun _ => by simp only [keyCfg]; rw [hb]; exact hal
      extAl := fun _ => by simp only [keyCfg]; exact hxal
      slots := by simp [keyCfg]
      sep := fun k hk j hj => by
        simp only [keyCfg] at hk hj ⊢; obtain rfl : j = 0 := by omega_arith
        rw [hb]; exact hsep k hk }
  obtain hchk : check (lanes 64 7) keyCfg (linExt 0) (keyPre h) keyEnv
      (linPostG 7 (qOuts (keyBsG0 h)) [] keyMaskSlots keyEnv) = true := by
    rcases hh with rfl | rfl
    · exact keyPre0_check
    · exact keyPre1_check
  unfold keyEnv at hchk
  obtain ⟨s₀, e₀, ho₀, -, hkr₀, rd₀, wr₀, -, o₀, f₀, hb₀, -⟩ := linG_ok hchk hok
    (fun k => s.mem.readW (wordAddr (s.gpr .a0) k) 64)
    (fun r i hri => by simp at hri) (fun j i hji => by simp at hji)
    (fun kv hkv => ⟨by simp only [keyCfg]; exact mask_lt hkv, by simp only [keyCfg]; exact hm kv hkv⟩)
    (fun j hj => ⟨by simp only [keyCfg] at hj; omega_arith, by simp only [keyCfg, Nat.zero_add]⟩)
  simp only [keyCfg] at hb₀ hkr₀ f₀
  obtain hall₁ : ∀ r, r ∉ sboxWrites → ((keyPre h).all fun i => dst i != some r) = true := fun r hr => by
    have : (restRegs.all fun r => (keyPre h).all fun i => dst i != some r) =
        true := by rcases hh with rfl | rfl <;> decide +kernel
    exact List.all_eq_true.mp this r (not_sboxWrites r hr)
  -- The fill.
  obtain ⟨s₁, e₁', v₁, o₁', m₁, rd₁', wr₁'⟩ := keyFill_ok s₀
  obtain hqW : ∀ j < 8, q j ∈ sboxWrites := by decide
  obtain k₁' : ∀ r, r ∉ sboxWrites → s₁.gpr r = s₀.gpr r := fun r hr =>
    o₁' r (fun j hj h => hr (h ▸ hqW j hj)) (fun h => hr (h ▸ by decide))
  obtain k₁ : ∀ r, r ∉ sboxWrites → s₁.gpr r = s.gpr r := fun r hr => (k₁' r hr).trans (o₀ r (hall₁ r hr))
  obtain e₁ : runBlock isa (keyLoad h) s = some s₁ := by
    rw [keyLoad, Interleave.runBlock_append, e₀, Option.bind_some, e₁']
  obtain rd₁ : s₁.rd = s.rd := by rw [rd₁', rd₀]
  obtain wr₁ : s₁.wr = s.wr := by rw [wr₁', wr₀]
  obtain hb₁ : s₁.gpr sb = s.gpr sb := (k₁' sb (by decide)).trans hb₀
  obtain hkr₁ : ∀ k ∈ keyMaskSlots, k < 64 → s₁.mem.readW (wordAddr (s.gpr sb) k) 64 =
      s.mem.readW (wordAddr (s.gpr sb) k) 64 := fun k hk hk' => by
    rw [m₁]; exact hkr₀ k hk hk'
  obtain f₁ : Frame [slotRegion keyCfg s] s.mem s₁.mem := by rw [m₁]; exact f₀
  -- The planes of the round key.
  obtain hQ : WordRel (Qs s₁) (fun _ => rkWord (s.mem.readW (wordAddr (s.gpr .a0) 0) 64) h) := by
    intro b' hb' i hi j hj
    obtain hp : 16 * i + b' < 64 := by omega_arith
    obtain hmem : (q j, keyBsG0 h j) ∈ qOuts (keyBsG0 h) := by
      simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
    obtain hz : ∀ p < 64, p % 16 ≠ 0 → (s₀.gpr (q j)).getLsbD p = false := fun p hp' h0 => by
      rw [ho₀ (q j) (keyBsG0 h j) hmem _ hp']; simp only [keyBsG0, h0, ↓reduceIte, xorBits_nil]
    obtain hb16 : keyBsG0 h j (16 * i) = keyBsG h j (16 * i) := by simp [keyBsG0]
    rw [Qs, v₁ j hj, getLsbD_fill hz hp, show (16 * i + b') / 16 = i by omega_arith,
      ho₀ (q j) (keyBsG0 h j) hmem _ (by omega_arith), hb16, keyBsG,
      xorBits_cons, xorBits_nil, Bool.xor_false,
      show 32 * h + 8 * (3 - 16 * i / 16) + j = 64 * 0 + (32 * h + 8 * (3 - i) + j) by omega_arith,
      bitOf_word _ _ _ (by rcases hh with rfl | rfl <;> omega_arith), rkWord, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight]
    simp only [show 8 * (3 - i) + j < 32 by omega_arith, decide_true, Bool.true_and]
    exact congrArg (BitVec.getLsbD _) (by omega_arith)
  -- The stores.
  obtain hkr₁' : s₁.gpr kr = s.gpr kr := k₁ kr (by decide)
  obtain hok₂ : Ok entryCfg s₁ :=
    { slotIn := fun k hk => ⟨_, by rw [wr₁]; exact hscr, by
        simp only [entryCfg] at hk ⊢
        rw [hkr₁', hkr, wordAddr, addr_add, tableSlot_eq]
        exact VG.Offset.contains_base b (by omega_arith) (by omega_arith)⟩
      extIn := fun k hk => by simp [entryCfg] at hk
      baseAl := fun _ => by simp only [entryCfg]; rw [hkr₁', hkr]; exact Spill.al8 hal (by omega_arith)
      extAl := fun h0 => by simp [entryCfg] at h0
      slots := by simp [entryCfg]
      sep := fun k _ j hj => by simp [entryCfg] at hj }
  have hchk₂ := keyStore_check
  unfold entryEnv at hchk₂
  obtain ⟨s₂, e₂, -, hso₂, -, rd₂, wr₂, -, o₂, f₂, hb₂, -⟩ := linG_ok hchk₂ hok₂ (Qs s₁)
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega_arith, rfl⟩)
    (fun j i hji => by simp at hji) (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [entryCfg] at hj)
  simp only [entryCfg] at hb₂ hso₂ f₂
  obtain k₂ : ∀ r, s₂.gpr r = s₁.gpr r := fun r => o₂ r (by simp [keyStore, dst])
  obtain he₂ : ∀ j < 8, entryW s₂.mem b e j = Qs s₁ j := fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => by
    obtain h := hso₂ j (fun p => [64 * j + p]) (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      hj p hp
    rw [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp] at h
    rw [← h, entryW, wordAddr, hkr₁', hkr, addr_add]
  refine ⟨s₂, ?_, fun r hr => by rw [k₂, k₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun kv hkv => ?_,
    ?_, hQ.congr fun j hj => he₂ j hj⟩
  · rw [keyStore_eq, runBlock_app, e₁, Option.bind_some, e₂]
  · have hk : kv.1 < 64 := mask_lt hkv
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    obtain h2 : s₂.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = s₁.mem.readW (wordAddr (s.gpr sb) kv.1) 64 := by
      refine f₂.readW (r := ⟨wordAddr (s.gpr sb) kv.1, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
        (by decide)
      simp only [slotRegion, List.mem_singleton] at hr; subst hr
      rw [hkr₁', hkr, hb, wordAddr]
      rw [tableSlot_eq]
      exact VG.Offset.disjoint b (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    rw [k₂, hb₁, h2, hkr₁ kv.1 (List.mem_map_of_mem hkv) hk]
    exact hm kv hkv
  · refine (f₁.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr; simp [hb, keyCfg]
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr
      simp [hkr₁', hkr]


/-! ## Steps of the pointers -/

theorem addI_ok (s : State) (d n : Reg) {imm : Int} (h : imm12 imm) :
    ∃ s', runBlock isa [.addi d n imm] s = some s' ∧ s'.gpr d = s.gpr n + BitVec.ofInt 64 imm ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by simp only [runBlock_cons, exec_addi h, runStep_some, runBlock_nil], RegUpd.gpr_write_self _ _ _,
    fun _ hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

/-! ## The loop -/

/-- The entry of round key `i`: `i` for encryption, `31 - i` for decryption. -/
def entOf : Dir → Nat → Nat
  | .encrypt, i => i
  | .decrypt, i => 31 - i

/-- `kr` before iteration `m`, as an offset in the scratch buffer. -/
def rsiAt : Dir → Nat → Nat
  | .encrypt, m => 8 * tableSlot + 128 * m
  | .decrypt, m => 8 * tableSlot - 64 + 64 * (32 - 2 * m)

/-- The instruction stepping `kr`. -/
def krStep : Dir → Instr
  | .encrypt => .addi kr kr 64
  | .decrypt => .addi kr kr (-64)

/-- `kr` moves from `x` to `y`. -/
def RsiStep : Dir → Nat → Nat → Prop
  | .encrypt, x, y => y = x + 64
  | .decrypt, x, y => x = y + 64

/-- `kr ± 64`. -/
theorem rsiStep_ok (dir : Dir) (s : State) {b : Addr} {x y : Nat} (hxy : RsiStep dir x y)
    (hkr : s.gpr kr = b + BitVec.ofNat 64 x) :
    ∃ s', runBlock isa [krStep dir] s = some s' ∧
      s'.gpr kr = b + BitVec.ofNat 64 y ∧
      (∀ r, r ≠ kr → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases dir
  · obtain ⟨s', e', r', o', m', rd', wr'⟩ := addI_ok s kr kr (imm := 64) (by decide)
    refine ⟨s', e', ?_, o', m', rd', wr'⟩
    rw [r', hkr, show BitVec.ofInt 64 64 = BitVec.ofNat 64 64 from rfl, addr_add, show y = x + 64 from hxy]
  · obtain ⟨s', e', r', o', m', rd', wr'⟩ := addI_ok s kr kr (imm := -64) (by decide)
    refine ⟨s', e', ?_, o', m', rd', wr'⟩
    have hxy : x = y + 64 := hxy
    rw [r', hkr, show BitVec.ofInt 64 (-64) = -BitVec.ofNat 64 64 from by decide, ← BitVec.sub_eq_add_neg,
      VG.Offset.add_ofNat_sub _ (by omega_arith), show x - 64 = y by omega_arith]

/-- The scratch buffer at `b`: writable, aligned, not wrapping around. -/
structure KPre (s : State) (b : Addr) : Prop where
  base : s.gpr sb = b
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  al : b.toNat % 8 = 0

theorem KPre.congr {s s' : State} {b : Addr} (h : KPre s b) (hb : s'.gpr sb = s.gpr sb)
    (hwr : s'.wr = s.wr) : KPre s' b :=
  ⟨hb.trans h.base, hwr ▸ h.scr, h.fit, h.al⟩

/-- The schedule's copy, in the tail buffer. -/
abbrev srcOf (b : Addr) : Addr := b + BitVec.ofNat 64 (8 * tailSlot)

/-- The regions the table's construction writes: the slots below 64 and the
table. -/
def keyRegions (b : Addr) : List Region := [⟨b, 8 * 64⟩, ⟨b + BitVec.ofNat 64 (8 * tableSlot), 8 * 256⟩]

theorem KPre.srcIn {s : State} {b : Addr} (h : KPre s b) {m : Nat} (hm : m < 16) :
    InRegions (s.rd ++ s.wr) (wordAddr (srcOf b + BitVec.ofNat 64 (8 * m)) 0) 8 := by
  have hf := h.fit
  rw [slots_eq] at hf
  refine ⟨_, List.mem_append_right _ h.scr, ?_⟩
  rw [wordAddr, addr_add, addr_add, slots_eq, tailSlot_eq]
  exact VG.Offset.contains_base b (by omega_arith) (by omega_arith)

theorem KPre.srcAl {s : State} {b : Addr} (h : KPre s b) (m : Nat) :
    (srcOf b + BitVec.ofNat 64 (8 * m)).toNat % 8 = 0 := by
  rw [addr_add]; exact Spill.al8 h.al (by omega_arith)

theorem KPre.srcSep {s : State} {b : Addr} (h : KPre s b) {m : Nat} (hm : m < 16)
    {k : Nat} (hk : k < 64) : Mem.Sep (wordAddr b k) 8 (wordAddr (srcOf b + BitVec.ofNat 64 (8 * m)) 0) 8 := by
  have hf := h.fit
  rw [slots_eq] at hf
  rw [wordAddr, wordAddr, addr_add, addr_add, tailSlot_eq]
  exact VG.Offset.sep b (by omega_arith) (by omega_arith) (by omega_arith)

/-- The schedule's round keys `2 m` and `2 m + 1`, as halves of its word `m`. -/
theorem rkWord_eq (mem : Mem) (sched : Addr) {m h : Nat} (hm : m < 16) (hh : h < 2) :
    rkWord (mem.readW (wordAddr (sched + BitVec.ofNat 64 (8 * m)) 0) 64) h =
      (Spec.Sm4.scheduleAt mem sched).getD (2 * m + h) 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  obtain hi : 2 * m + h < 32 := by omega_arith
  rw [VG.Proof.Aes.getD_eq _ hi, show k = 8 * (k / 8) + k % 8 by omega_arith, VG.Proof.Sm4.getLsbD_scheduleAt _ _ hi (by omega_arith) (by omega_arith),
    rkWord, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  simp only [show 8 * (k / 8) + k % 8 < 32 by omega_arith, decide_true, Bool.true_and]
  rw [show 32 * h + (8 * (k / 8) + k % 8) = 8 * (4 * h + k / 8) + k % 8 by omega_arith,
    readW64_bit _ _ (by omega_arith) (by omega_arith), wordAddr, addr_add, addr_add]
  rw [show 8 * m + (8 * 0 + (4 * h + k / 8)) = 4 * (2 * m + h) + k / 8 by omega_arith]

/-- An entry outside a frame keeps its planes. -/
theorem entryW_frame {m m' : Mem} {b : Addr} {e i : Nat}
    (hf : Frame [⟨b, 8 * 64⟩, ⟨b + BitVec.ofNat 64 (8 * tableSlot + 64 * e), 64⟩] m m')
    (hi : i < 32) (he : e < 32) (hie : i ≠ e) {j : Nat} (hj : j < 8) : entryW m' b i j = entryW m b i j := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [tableSlot_eq] at *
  rcases hr with rfl | rfl
  · exact VG.Offset.disjoint_base b (by omega_arith) (by omega_arith)
  · exact VG.Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)

/-- The copy is outside the regions the table's construction writes. -/
theorem src_eq {b : Addr} {m m' : Mem} (hf : Frame (keyRegions b) m m') :
    Spec.Sm4.scheduleAt m' (srcOf b) = Spec.Sm4.scheduleAt m (srcOf b) := by
  obtain hb : ∀ k < 128, m' (srcOf b + BitVec.ofNat 64 k) = m (srcOf b + BitVec.ofNat 64 k) := fun k hk => by
    refine hf.bytes (R := ⟨srcOf b, 128⟩) (fun r hr => ?_) (by show 128 ≤ 2 ^ 64; omega_arith) hk
    simp only [keyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    show Region.Disjoint ⟨b + BitVec.ofNat 64 768, 128⟩ r
    rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base b (by decide) (by decide)
    · exact VG.Offset.disjoint b (d := 768) (e := 1024) (by decide) (by decide) (by decide)
  apply Vector.ext
  intro i hi
  simp only [Spec.Sm4.scheduleAt, Vector.getElem_ofFn, List.range, List.range.loop, List.foldl]
  rw [hb (4 * i + 0) (by omega_arith), hb (4 * i + 1) (by omega_arith), hb (4 * i + 2) (by omega_arith),
    hb (4 * i + 3) (by omega_arith)]

/-- A step's frame within the table's construction's. -/
theorem keyFrame_sub {b : Addr} {e : Nat} (he : e < 32) :
    ∀ r ∈ [(⟨b, 8 * 64⟩ : Region), ⟨b + BitVec.ofNat 64 (8 * tableSlot + 64 * e), 64⟩],
      ∃ r' ∈ keyRegions b, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨b, 8 * 64⟩, by simp [keyRegions], fun _ h => h⟩
  · refine ⟨⟨b + BitVec.ofNat 64 (8 * tableSlot), 8 * 256⟩, by simp [keyRegions], ?_⟩
    rw [← addr_add]
    exact VG.Offset.sub_base _ (by omega_arith)

/-- What the loop keeps, after `m` of its 16 iterations. -/
structure KInv (s₀ : State) (b : Addr) (dir : Dir) (m : Nat) (s : State) : Prop where
  pre : KPre s b
  rsi : s.gpr kr = b + BitVec.ofNat 64 (rsiAt dir m)
  rdi : s.gpr .a0 = srcOf b + BitVec.ofNat 64 (8 * m)
  ent : ∀ i < 2 * m, WordRel (entryW s.mem b (entOf dir i))
    (fun _ => (Spec.Sm4.scheduleAt s₀.mem (srcOf b)).getD i 0)
  masks : MasksOk s
  frame : Frame (keyRegions b) s₀.mem s.mem
  regs : ∀ r, r ∉ sboxWrites → r ≠ kr → r ≠ .a0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem entOf_lt (dir : Dir) {i : Nat} (hi : i < 32) : entOf dir i < 32 := by cases dir <;> simp [entOf] <;> omega_arith

theorem entOf_inj (dir : Dir) {i i' : Nat} (hi : i < 32) (hi' : i' < 32) (h : entOf dir i = entOf dir i') :
    i = i' := by cases dir <;> simp [entOf] at h <;> omega_arith

theorem rsiAt_ent (dir : Dir) {m : Nat} (hm : m < 16) :
    rsiAt dir m = 8 * tableSlot + 64 * entOf dir (2 * m) := by
  cases dir <;> simp only [rsiAt, entOf, tableSlot_eq] <;> omega_arith

theorem rsiAt_succ (dir : Dir) {m : Nat} (hm : m < 16) :
    RsiStep dir (rsiAt dir m) (8 * tableSlot + 64 * entOf dir (2 * m + 1)) ∧
    RsiStep dir (8 * tableSlot + 64 * entOf dir (2 * m + 1)) (rsiAt dir (m + 1)) := by
  cases dir <;> simp only [RsiStep, rsiAt, entOf, tableSlot_eq] <;> omega_arith

/-- One iteration: round keys `2 m` and `2 m + 1`. -/
theorem keyIter_ok (dir : Dir) {s₀ s : State} {b : Addr} {m : Nat} (hm : m < 16)
    (hi : KInv s₀ b dir m s) :
    ∃ s', runBlock isa (keyOne 0 ++ ([krStep dir] : List Instr) ++ keyOne 1 ++
        ([krStep dir, .addi .a0 .a0 8] : List Instr)) s = some s' ∧
      KInv s₀ b dir (m + 1) s' := by
  have hpre := hi.pre
  have hfit := hpre.fit
  obtain he0 := entOf_lt dir (show 2 * m < 32 by omega_arith)
  obtain he1 := entOf_lt dir (show 2 * m + 1 < 32 by omega_arith)
  obtain hsched : Spec.Sm4.scheduleAt s.mem (srcOf b) = Spec.Sm4.scheduleAt s₀.mem (srcOf b) :=
    src_eq hi.frame
  -- Round key `2 m`.
  obtain ⟨s₁, e₁, o₁, rd₁, wr₁, m₁, f₁, E₁⟩ := keyOne_step (h := 0) (e := entOf dir (2 * m)) (Or.inl rfl)
    hpre.base hpre.al hpre.scr (by rw [hi.rsi, rsiAt_ent dir hm]) he0 (by rw [hi.rdi]; exact hpre.srcIn hm)
    (by rw [hi.rdi]; exact hpre.srcAl m) (fun k hk => by rw [hi.rdi]; exact hpre.srcSep hm hk) hi.masks
  rw [hi.rdi, rkWord_eq _ _ hm (by decide), hsched] at E₁
  obtain ⟨st1, st2⟩ := rsiAt_succ dir hm
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := rsiStep_ok dir s₁ (b := b) (x := rsiAt dir m)
    (y := 8 * tableSlot + 64 * entOf dir (2 * m + 1)) st1
    (by rw [o₁ _ (by decide), hi.rsi])
  obtain hpre₂ : KPre s₂ b :=
    hpre.congr (by rw [o₂ _ (by decide), o₁ _ (by decide)]) (by rw [wr₂, wr₁])
  obtain hrdi₂ : s₂.gpr .a0 = srcOf b + BitVec.ofNat 64 (8 * m) := by
    rw [o₂ _ (by decide), o₁ _ (by decide), hi.rdi]
  obtain hm₂ : MasksOk s₂ := fun kv hkv => by
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    rw [m₂, o₂ _ (by decide)]; exact m₁ kv hkv
  -- Round key `2 m + 1`.
  obtain ⟨s₃, e₃, o₃, rd₃, wr₃, m₃, f₃, E₃⟩ := keyOne_step (h := 1) (e := entOf dir (2 * m + 1)) (Or.inr rfl)
    hpre₂.base hpre₂.al hpre₂.scr r₂ he1 (by rw [hrdi₂]; exact hpre₂.srcIn hm) (by rw [hrdi₂]; exact hpre₂.srcAl m)
    (fun k hk => by rw [hrdi₂]; exact hpre₂.srcSep hm hk) hm₂
  obtain hfr₂ : Frame (keyRegions b) s₀.mem s₂.mem := by
    rw [m₂]; exact hi.frame.trans (f₁.sub (keyFrame_sub he0))
  rw [hrdi₂, rkWord_eq _ _ hm (by decide), src_eq hfr₂] at E₃
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := rsiStep_ok dir s₃ (b := b)
    (x := 8 * tableSlot + 64 * entOf dir (2 * m + 1)) (y := rsiAt dir (m + 1))
    st2 (by rw [o₃ _ (by decide), r₂])
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addI_ok s₄ .a0 .a0 (imm := 8) (by decide)
  obtain hmem : s₅.mem = s₃.mem := by rw [m₅, m₄]
  obtain hb₆ : s₅.gpr sb = s₃.gpr sb := by rw [o₅ _ (by decide), o₄ _ (by decide)]
  obtain hf₃ : Frame (keyRegions b) s₀.mem s₃.mem := hfr₂.trans (f₃.sub (keyFrame_sub he1))
  refine ⟨s₅, ?_, ⟨hpre₂.congr (by rw [hb₆, o₃ _ (by decide)]) (by rw [wr₅, wr₄, wr₃]),
      by rw [o₅ _ (by decide), r₄], ?_, fun i hi' => ?_,
      fun kv hkv => ?_, by rw [hmem]; exact hf₃, fun r h1 h2 h3 => ?_,
      by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩⟩
  · rw [runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃,
      Option.bind_some,
      show ([krStep dir, .addi .a0 .a0 8] : List Instr) = [krStep dir] ++ [.addi .a0 .a0 8] from rfl,
      runBlock_app, e₄, Option.bind_some, e₅]
  · rw [r₅, o₄ _ (by decide), o₃ _ (by decide), hrdi₂, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl,
      addr_add, show 8 * m + 8 = 8 * (m + 1) by omega_arith]
  · have hent : ∀ i' < 32, i' ≠ entOf dir (2 * m) → i' ≠ entOf dir (2 * m + 1) → ∀ j < 8,
        entryW s₅.mem b i' j = entryW s.mem b i' j := fun i' hi'' h0 h1 j hj => by
      rw [hmem, entryW_frame f₃ hi'' he1 h1 hj, m₂, entryW_frame f₁ hi'' he0 h0 hj]
    rcases (show i < 2 * m ∨ i = 2 * m ∨ i = 2 * m + 1 by omega_arith) with hlt | rfl | rfl
    · exact (hi.ent i hlt).congr fun j hj => hent _ (entOf_lt dir (by omega_arith))
        (fun h => by have := entOf_inj dir (by omega_arith) (by omega_arith) h; omega_arith)
        (fun h => by have := entOf_inj dir (by omega_arith) (by omega_arith) h; omega_arith) j hj
    · refine E₁.congr fun j hj => ?_
      rw [hmem, entryW_frame f₃ he0 he1 (fun h => by have := entOf_inj dir (by omega_arith) (by omega_arith) h; omega_arith) hj, m₂]
    · exact E₃.congr fun j hj => by rw [hmem]
  · show s₅.mem.readW (wordAddr (s₅.gpr sb) kv.1) 64 = kv.2
    rw [hmem, hb₆]; exact m₃ kv hkv
  · rw [o₅ r h3, o₄ r h2, o₃ r h1, o₂ r h2, o₁ r h1, hi.regs r h1 h2 h3]

theorem entOf_entOf (dir : Dir) {e : Nat} (he : e < 32) : entOf dir (entOf dir e) = e := by
  cases dir <;> simp [entOf] <;> omega_arith

/-- The round keys in the order the rounds use them. -/
def dirKeys (dir : Dir) (sch : Spec.Sm4.Schedule) (e : Nat) : Spec.Sm4.Word := sch.getD (entOf dir e) 0

theorem keyPairs_wp (dir : Dir) {s₀ : State} {b : Addr} :
    ∀ n m, m + n = 16 → ∀ s, KInv s₀ b dir m s →
      WP isa (keyPairs (krStep dir) n) s (KInv s₀ b dir 16)
  | 0, m, h, s, hi => WP.block_nil (by rw [show m = 16 by omega_arith] at hi; exact hi)
  | n + 1, m, h, s, hi => by
    obtain ⟨s', e', hi'⟩ := keyIter_ok dir (by omega_arith) hi
    exact WP.seq (WP.of_runBlock ⟨s', e', keyPairs_wp dir n (m + 1) (by omega_arith) s' hi'⟩)

/-! ## The schedule's copy and the whole table -/

/-- The scratch buffer at `b` and the schedule at `sched`, apart. -/
structure SchedPre (s : State) (b sched : Addr) : Prop extends KPre s b where
  sch : (⟨sched, 128⟩ : Region) ∈ s.rd ++ s.wr
  schFit : sched.toNat + 128 ≤ 2 ^ 64
  sep : Region.Disjoint ⟨sched, 128⟩ ⟨b, 8 * slots⟩

theorem SchedPre.congr {s s' : State} {b sched : Addr} (h : SchedPre s b sched) (hb : s'.gpr sb = s.gpr sb)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : SchedPre s' b sched :=
  ⟨h.toKPre.congr hb hwr, hrd ▸ hwr ▸ h.sch, h.schFit, h.sep⟩

/-- `t1 := a0`, `t2 :=` the tail buffer, `t3 := 128`. -/
theorem copySetup_ok (s : State) :
    ∃ s', runBlock isa ([movR .t1 .a0] ++ slotAddr .t2 tailSlot ++ ([.li .t3 128] : List Instr)) s = some s' ∧
      s'.gpr .t1 = s.gpr .a0 ∧ s'.gpr .t2 = s.gpr sb + BitVec.ofNat 64 (8 * tailSlot) ∧
      s'.gpr .t3 = BitVec.ofNat 64 128 ∧ (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [show slotAddr .t2 tailSlot = [.addi .t2 sb ((768 : Nat) : Int)] from rfl]
  refine ⟨((s.write .t1 (s.gpr .a0 + BitVec.ofInt 64 0)).write .t2
      ((s.write .t1 (s.gpr .a0 + BitVec.ofInt 64 0)).gpr sb + BitVec.ofNat 64 768)).write .t3
      (BitVec.ofInt 64 128),
    by simp only [movR, List.cons_append, List.nil_append, runBlock_cons,
      exec_addi (show imm12 0 by decide), exec_addi_nat (show 768 < 2048 by decide),
      exec_li (show imm12 128 by decide), runStep_some, runBlock_nil], ?_, ?_, rfl, fun r h1 h2 h3 => ?_,
    rfl, rfl, rfl⟩
  · simp [RegUpd.gpr_write]
  · simp [RegUpd.gpr_write, sb, tailSlot]
  · simp [RegUpd.gpr_write, h1, h2, h3]

/-- The schedule's copy in the tail buffer, then `a0 :=` the copy. -/
theorem copySchedule_wp {s₀ : State} {b sched : Addr} (hp : SchedPre s₀ b sched)
    (ha0 : s₀.gpr .a0 = sched) {Q : State → Prop}
    (hQ : ∀ s, SchedPre s b sched → s.gpr .a0 = srcOf b →
      Spec.Sm4.scheduleAt s.mem (srcOf b) = Spec.Sm4.scheduleAt s₀.mem sched →
      Frame [⟨srcOf b, 128⟩] s₀.mem s.mem → (∀ r, r ∉ sboxWrites → r ≠ .a0 → s.gpr r = s₀.gpr r) →
      s.rd = s₀.rd → s.wr = s₀.wr → Q s) :
    WP isa copySchedule s₀ Q := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  have hb := hp.base
  obtain ⟨s₁, e₁, t1₁, t2₁, t3₁, o₁, m₁, rd₁, wr₁⟩ := copySetup_ok s₀
  rw [hb] at t2₁
  obtain hsrc : ∀ i n, i + n ≤ 128 → (⟨b, 8 * slots⟩ : Region).Contains (srcOf b + BitVec.ofNat 64 i) n :=
    fun i n hi => by
      rw [addr_add, slots_eq, tailSlot_eq]
      exact VG.Offset.contains_base b (by omega_arith) (by omega_arith)
  unfold copySchedule
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.seq (WP.mono (copyAny_ok (tmp := .t4) (src := .t1) (dst := .t2) (cnt := .t3) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) s₁ (N := 128) (by decide) (by decide) (by decide)
    t3₁
    (fun i hi => by
      rw [rd₁, wr₁, t1₁, ha0]
      exact ⟨_, hp.sch, VG.Offset.contains_base _ (by omega_arith) (by have := hp.schFit; omega_arith)⟩)
    (fun i hi => by rw [wr₁, t2₁]; exact ⟨_, hp.scr, hsrc i 1 (by omega_arith)⟩)
    (fun i hi _ => by
      rw [rd₁, wr₁, t1₁, ha0]
      exact ⟨_, hp.sch, VG.Offset.contains_base _ (by omega_arith) (by have := hp.schFit; omega_arith)⟩)
    (fun i hi _ => by rw [wr₁, t2₁]; exact ⟨_, hp.scr, hsrc (8 * i) 8 (by omega_arith)⟩)
    (by
      rw [t1₁, t2₁, ha0]
      exact hp.sep.symm.sep (by simpa using hsrc 0 128 (by decide)) (Region.contains_self _ _))) fun t ⟨tc, tf, tk⟩ => ?_)
  obtain hcopy : ∀ r ∈ ([.t4, .t1, .t2, .t3] : List Reg), r ∈ sboxWrites := by decide
  obtain tsb : t.gpr sb = b := by rw [tk.gpr (by decide), o₁ _ (by decide) (by decide) (by decide), hb]
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := slotAddr_ok t .a0 tailSlot
  refine WP.of_runBlock ⟨s₂, e₂, hQ s₂ (hp.congr ?_ ?_ ?_) (by rw [r₂, tsb]) ?_ ?_ (fun r h1 h2 => ?_) ?_ ?_⟩
  · rw [o₂ _ (by decide), tsb, hb]
  · rw [rd₂, tk.2.1, rd₁]
  · rw [wr₂, tk.2.2, wr₁]
  · have hbyte : ∀ k < 128, s₂.mem (srcOf b + BitVec.ofNat 64 k) = s₀.mem (sched + BitVec.ofNat 64 k) :=
      fun k hk => by
        have := tc k hk
        rw [t2₁, t1₁, ha0, m₁] at this
        rw [m₂]; exact this
    apply Vector.ext
    intro i hi
    simp only [Spec.Sm4.scheduleAt, Vector.getElem_ofFn, List.range, List.range.loop, List.foldl]
    rw [hbyte (4 * i + 0) (by omega_arith), hbyte (4 * i + 1) (by omega_arith),
      hbyte (4 * i + 2) (by omega_arith), hbyte (4 * i + 3) (by omega_arith)]
  · rw [m₂, ← m₁]; rw [t2₁] at tf; exact tf
  · rw [o₂ r h2, tk.gpr fun h => h1 (hcopy r h)]
    have : r ∉ ([.t4, .t1, .t2, .t3] : List Reg) := fun h => h1 (hcopy r h)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    exact o₁ r this.2.1 this.2.2.1 this.2.2.2
  · rw [rd₂, tk.2.1, rd₁]
  · rw [wr₂, tk.2.2, wr₁]

/-- The masks, outside the schedule's copy. -/
theorem MasksOk.copy {s s' : State} {b : Addr} (hm : MasksOk s) (hb : s.gpr sb = b) (hb' : s'.gpr sb = b)
    (hf : Frame [⟨srcOf b, 128⟩] s.mem s'.mem) : MasksOk s' := by
  intro kv hkv
  obtain hk := masks_lt kv hkv
  show s'.mem.readW (wordAddr (s'.gpr sb) kv.1) 64 = kv.2
  rw [hb', hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), ← hb]
  · exact hm kv hkv
  · simp only [List.mem_singleton] at hr
    subst hr
    show Region.Disjoint ⟨b + BitVec.ofNat 64 (8 * kv.1), 8⟩ ⟨b + BitVec.ofNat 64 768, 128⟩
    exact VG.Offset.disjoint b (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)

/-- After the table: its entries, the scratch buffer, `a0 :=` the table's end. -/
structure KeysPost (s₀ : State) (b sched : Addr) (dir : Dir) (s : State) : Prop where
  pre : SchedPre s b sched
  key : KeyCtx s (dirKeys dir (Spec.Sm4.scheduleAt s₀.mem sched))
  masks : MasksOk s
  rdi : s.gpr .a0 = b + BitVec.ofNat 64 (8 * tableEnd)
  frame : Frame [⟨b, 8 * tableEnd⟩] s₀.mem s.mem
  regs : ∀ r, r ∉ sboxWrites → r ≠ kr → r ≠ .a0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem keysGen_wp (dir : Dir) (k : Nat) (hk : 8 * k = rsiAt dir 0) (hse : 8 * k < 4088)
    {s₀ u : State} {b sched : Addr} (hp : SchedPre u b sched) (hrdi : u.gpr .a0 = srcOf b) (hm : MasksOk u)
    (hsch : Spec.Sm4.scheduleAt u.mem (srcOf b) = Spec.Sm4.scheduleAt s₀.mem sched)
    (hf : Frame [⟨srcOf b, 128⟩] s₀.mem u.mem)
    (hregs : ∀ r, r ∉ sboxWrites → r ≠ .a0 → u.gpr r = s₀.gpr r) (hrd : u.rd = s₀.rd) (hwr : u.wr = s₀.wr) :
    WP isa (.seq (.seq (.block (slotAddr kr k)) (keyPairs (krStep dir) 16))
      (.block (slotAddr .a0 tableEnd))) u (KeysPost s₀ b sched dir) := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := slotAddr_ok u kr k hse
  obtain hinv : KInv u b dir 0 s₁ := by
    refine ⟨hp.toKPre.congr (by rw [o₁ _ (by decide)]) wr₁,
      by rw [r₁, hp.base, hk], by rw [o₁ _ (by decide), hrdi]; simp,
      fun i hi => by omega_arith, fun kv hkv => ?_, by rw [m₁]; exact Frame.refl _ _,
      fun r _ h2 _ => by rw [o₁ r h2], rd₁, wr₁⟩
    show s₁.mem.readW (wordAddr (s₁.gpr sb) kv.1) 64 = kv.2
    rw [m₁, o₁ _ (by decide)]; exact hm kv hkv
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.mono (keyPairs_wp dir 16 0 rfl s₁ hinv) fun s h => ?_⟩))
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := slotAddr_ok s .a0 tableEnd
  obtain hb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), h.pre.base]
  refine WP.of_runBlock ⟨s₃, e₃, hp.congr (by rw [hb₃, hp.base]) (by rw [rd₃, h.rd])
    (by rw [wr₃, h.wr]), ⟨?_, ?_, ?_, fun e he => ?_⟩, fun kv hkv => ?_,
    by rw [r₃, h.pre.base], ?_, fun r h1 h2 h3 => ?_, by rw [rd₃, h.rd, hrd], by rw [wr₃, h.wr, hwr]⟩
  · rw [wr₃, hb₃, h.wr]; exact hp.scr
  · rw [hb₃]; exact hp.fit
  · rw [hb₃]; exact hp.al
  · rw [hb₃, m₃]
    have := h.ent (entOf dir e) (by have := entOf_lt dir he; omega_arith)
    rw [entOf_entOf dir he, hsch] at this
    exact this
  · show s₃.mem.readW (wordAddr (s₃.gpr sb) kv.1) 64 = kv.2
    rw [m₃, o₃ _ (by decide)]; exact h.masks kv hkv
  · rw [m₃]
    refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [tableEnd_eq]
      exact VG.Offset.sub_base b (by decide)
    · simp only [keyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [tableEnd_eq]
      rcases hr with rfl | rfl
      · exact fun x hx => by simp only [Region.Contains] at hx ⊢; omega_arith
      · rw [tableSlot_eq]; exact VG.Offset.sub_base b (by decide)
  · rw [o₃ r h3, h.regs r h1 h2 h3, hregs r h1 h3]

theorem keys_wp (dir : Dir) {s₀ : State} {b sched : Addr} (hp : SchedPre s₀ b sched)
    (hrdi : s₀.gpr .a0 = sched) (hm : MasksOk s₀) :
    WP isa (keys dir) s₀ (KeysPost s₀ b sched dir) := by
  unfold keys
  refine WP.seq (copySchedule_wp hp hrdi fun u hu ha hs hf hr hrd hwr => ?_)
  obtain hm' := hm.copy hp.base hu.base hf
  cases dir
  · exact keysGen_wp .encrypt tableSlot (by simp [rsiAt]) (by decide) hu ha hm' hs hf hr hrd hwr
  · exact keysGen_wp .decrypt (tableSlot + 8 * 31) (by simp [rsiAt, tableSlot_eq]) (by decide) hu ha hm' hs hf
      hr hrd hwr

end VG.Proof.Sm4.RISCV64

end

end

/-!
# A group of blocks of SM4 ECB on RISCV64

`dataGroup_wp`: one iteration of the data loop copies the group's blocks
(sixteen, or the last one to fifteen) to the tail buffer, a byte at a time
(`copyAny_ok`), transforms it (`crypt16_wp`, which keeps the data pointer,
the blocks left and the table's end in `a1`, `a2` and `a0`), copies the
blocks back and steps to the next group. As on PPC64LE
(`Proof/Sm4/PPC64LE/Ecb.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Sm4.RISCV64
open VG.Proof.Sm4 (DInv quads ofBlock outBlock not_contains_off blockAt_getD)
open VG.Impl.Aes.RISCV64 (q sb t0 t1 movR ldS stS shrI shlI)
open VG.Impl.Words.RISCV64 (copyAny)
open VG.Proof.Aes.RISCV64 (sboxWrites)

/-! ## Small blocks -/

theorem lsr4_beq {v : Nat} (hv : v < 2 ^ 64) : (BitVec.ofNat 64 v >>> 4 == 0) = decide (v < 16) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow] at this
    simp at this
    omega_using [this]
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow]
    simp
    omega_using [h]

theorem movR_ok (s : State) (d n : Reg) :
    ∃ s', runBlock isa [movR d n] s = some s' ∧ s'.gpr d = s.gpr n ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write d (s.gpr n + BitVec.ofInt 64 0), by
    simp only [movR, runBlock_cons, exec_addi (show imm12 0 by decide), runStep_some, runBlock_nil],
    (RegUpd.gpr_write_self _ _ _).trans (by simp), fun _ h => RegUpd.gpr_write_of_ne _ _ h, rfl, rfl, rfl⟩

theorem shl4_ok (s : State) (d n : Reg) :
    ∃ s', runBlock isa [shlI d n 4] s = some s' ∧ s'.gpr d = s.gpr n <<< 4 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by simp only [shlI, runBlock_cons, exec_shift_d (show 4 < 64 by decide), runStep_some, runBlock_nil],
    RegUpd.gpr_write_self _ _ _, fun _ h => RegUpd.gpr_write_of_ne _ _ h, rfl, rfl, rfl⟩

theorem ofNat_shl4 {c : Nat} (h : c < 2 ^ 60) : BitVec.ofNat 64 c <<< 4 = BitVec.ofNat 64 (16 * c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (a := c) (by omega_using [h])]
  congr 1; omega_using []

/-- `a4 := min(a2, 16)`. -/
theorem groupCount_wp {s : State} {v : Nat} (hr : s.gpr .a2 = BitVec.ofNat 64 v) (hv : v < 2 ^ 64) :
    WP isa groupCount s fun s' => s'.gpr .a4 = BitVec.ofNat 64 (min v 16) ∧
      (∀ r, r ≠ .a4 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write t0 (s.gpr .a2 >>> 4)
  obtain e₁ : runBlock isa [shrI t0 .a2 4] s = some s₁ := by
    simp only [shrI, runBlock_cons, exec_shift_d (show 4 < 64 by decide), runStep_some, runBlock_nil, s₁]
  obtain t₁ : s₁.gpr t0 = BitVec.ofNat 64 v >>> 4 := by rw [RegUpd.gpr_write_self, hr]
  obtain o₁ : ∀ r, r ≠ t0 → s₁.gpr r = s.gpr r := fun _ h => RegUpd.gpr_write_of_ne _ _ h
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.ite (decide (16 ≤ v)) ((eval_nonzero s₁ t0).trans (by rw [t₁, lsr4_beq hv]; by_cases h : v < 16 <;> simp [h] <;> omega_using [h]))
    (fun h => ?_) (fun h => ?_)
  · refine WP.of_runBlock ⟨s₁.write .a4 (BitVec.ofInt 64 16), by
      simp only [runBlock_cons, exec_li (show imm12 16 by decide), runStep_some, runBlock_nil], ?_, fun r h1 h2 => by rw [RegUpd.gpr_write_of_ne _ _ h1, o₁ r h2], rfl, rfl, rfl⟩
    rw [RegUpd.gpr_write_self, Nat.min_eq_right (by simp at h; omega_using [h])]; rfl
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .a4 .a2
    refine WP.of_runBlock ⟨s₂, e₂, ?_, fun r h1 h2 => by rw [o₂ r h1, o₁ r h2], m₂, rd₂, wr₂⟩
    rw [r₂, o₁ _ (by decide), hr, Nat.min_eq_left (by simp at h; omega_using [h])]

theorem readW_slot_write {m : Mem} {b : Addr} {j k : Nat} (v : BitVec 64) (hj : j < slots) (hk : k < slots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 64 = if j = k then v else m.readW (wordAddr b j) 64 := by
  rw [slots_eq] at hj hk
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self64 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega_using [hj]) (by omega_using [hk]) h) (by decide)

/-! ## The scratch buffer's contents -/

/-- The masks, in the memory at `b`. -/
def MasksAt (m : Mem) (b : Addr) : Prop := ∀ kv ∈ maskCs, m.readW (wordAddr b kv.1) 64 = kv.2

theorem MasksOk.at {s : State} {b : Addr} (h : MasksOk s) (hb : s.gpr sb = b) : MasksAt s.mem b :=
  fun kv hkv => by rw [← hb]; exact h kv hkv

theorem MasksAt.ok {s : State} {b : Addr} (h : MasksAt s.mem b) (hb : s.gpr sb = b) : MasksOk s :=
  fun kv hkv => by show s.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = kv.2; rw [hb]; exact h kv hkv

/-- What the data loop keeps in the scratch buffer: the masks, the table and
the saved registers. -/
structure ScrOk (s₀ : State) (b : Addr) (E : Nat → Spec.Sm4.Word) (m : Mem) : Prop where
  masks : MasksAt m b
  keys : ∀ e < 32, VG.Proof.Sm4.WordRel (entryW m b e) fun _ => E e
  saved : Saved s₀ b m

/-- The slots `ScrOk` reads: 40–50, the table (128–383) and 384–395. -/
abbrev scrRegions (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 (8 * 40), 88⟩, ⟨b + BitVec.ofNat 64 (8 * tableSlot), 8 * 256⟩,
    ⟨b + BitVec.ofNat 64 (8 * savedSlot), 96⟩]

theorem masks_range : ∀ kv ∈ maskCs, 40 ≤ kv.1 ∧ kv.1 < 51 := by decide

theorem mask_range {kv : Nat × BitVec 64} (hkv : kv ∈ maskCs) : 40 ≤ kv.1 ∧ kv.1 < 51 := masks_range kv hkv

theorem ScrOk.frame {s₀ : State} {b : Addr} {E : Nat → Spec.Sm4.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ t ∈ scrRegions b, ∀ r ∈ rs, Region.Disjoint t r) :
    ScrOk s₀ b E m' := by
  obtain hR : ∀ t ∈ scrRegions b, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨fun kv hkv => ?_, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · have hk := mask_range hkv
    rw [← h.masks kv hkv]
    exact hR _ List.mem_cons_self (8 * kv.1) (VG.Offset.sub b (by omega_using [hk]) (by omega_using [hk]))
  · exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * tableSlot + 64 * i + 8 * j)
      (VG.Offset.sub b (by omega_using []) (by rw [tableSlot_eq]; omega_using [hi, hj]))
  · rw [← h.saved i hi]
    exact hR _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (8 * (savedSlot + i))
      (VG.Offset.sub b (by omega_using []) (by omega_using [hi]))

theorem ScrOk.frame2 {s₀ : State} {b : Addr} {E : Nat → Spec.Sm4.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) {rs : List Region} (hf : Frame rs m m') (hm : MasksAt m' b)
    (hd : ∀ t ∈ (scrRegions b).tail, ∀ r ∈ rs, Region.Disjoint t r) : ScrOk s₀ b E m' := by
  obtain hR : ∀ t ∈ (scrRegions b).tail, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨hm, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact hR _ List.mem_cons_self (8 * tableSlot + 64 * i + 8 * j)
      (VG.Offset.sub b (by omega_using []) (by rw [tableSlot_eq]; omega_using [hi, hj]))
  · rw [← h.saved i hi]
    exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * (savedSlot + i))
      (VG.Offset.sub b (by omega_using []) (by omega_using [hi]))

/-! ## The data loop -/

/-- Each block, transformed: the output of the 32 rounds with the round keys `E`. -/
def outF (m₀ : Mem) (D : Addr) (E : Nat → Spec.Sm4.Word) (j : Nat) : Spec.Sm4.Block :=
  outBlock (quads .enc E 8 (ofBlock (Spec.Sm4.blockAt m₀ (D + BitVec.ofNat 64 (16 * j)))))

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : Addr) (n : Nat) : Prop where
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 8 * slots⟩
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  fitD : D.toNat + 16 * n ≤ 2 ^ 64
  al : b.toNat % 8 = 0

/-- `copyAny` of `c` blocks from `t1` to `t2`, `t3 = 16 c` bytes, set up. -/
theorem copy_wp {s : State} {X Y : Addr} {c : Nat} (hc : 0 < c) (hc16 : c ≤ 16)
    (hx : s.gpr .t1 = X) (hy : s.gpr .t2 = Y) (hcx : s.gpr .t3 = BitVec.ofNat 64 (16 * c))
    (hX : ∀ i n, i + n ≤ 16 * c → i < 16 * c → InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 i) n)
    (hY : ∀ i n, i + n ≤ 16 * c → i < 16 * c → InRegions s.wr (Y + BitVec.ofNat 64 i) n)
    (hsep : Region.Disjoint ⟨X, 16 * c⟩ ⟨Y, 16 * c⟩) :
    WP isa (copyAny .t4 .t1 .t2 .t3) s fun s' =>
      (∀ t < 16 * c, s'.mem (Y + BitVec.ofNat 64 t) = s.mem (X + BitVec.ofNat 64 t)) ∧
      Frame [⟨Y, 16 * c⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (copyAny_ok (tmp := .t4) (src := .t1) (dst := .t2) (cnt := .t3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s (N := 16 * c) (by omega_using [hc]) (by omega_using [hc16]) (by omega_using []) hcx
    (by rw [hx]; exact fun i hi => hX i 1 (by omega_using [hi]) hi) (by rw [hy]; exact fun i hi => hY i 1 (by omega_using [hi]) hi)
    (by rw [hx]; exact fun i hi _ => hX (8 * i) 8 (by omega_using [hi]) (by omega_using [hi]))
    (by rw [hy]; exact fun i hi _ => hY (8 * i) 8 (by omega_using [hi]) (by omega_using [hi]))
    (by rw [hx, hy]; exact hsep.symm.sep (Region.contains_self _ _) (Region.contains_self _ _)))
    fun t ⟨tc, tf, tk⟩ => ⟨by rw [← hx, ← hy]; exact tc, by rw [← hy]; exact tf,
      fun r h1 h2 h3 h4 => tk.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h4, h1, h2, h3⟩),
      tk.2.1, tk.2.2⟩

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : Addr) (n : Nat) (E : Nat → Spec.Sm4.Word) (k : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  a1 : s.gpr .a1 = D + BitVec.ofNat 64 (256 * k)
  a2 : s.gpr .a2 = BitVec.ofNat 64 (n - 16 * k)
  lt : 16 * k < n
  a0 : s.gpr .a0 = b + BitVec.ofNat 64 (8 * tableEnd)
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem D n (16 * k) (outF s₀.mem D E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : Addr) (n : Nat) (E : Nat → Spec.Sm4.Word) (s : State) : Prop where
  base : s.gpr sb = b
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem D n n (outF s₀.mem D E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem dataGroup_wp {s₀ : State} {b D : Addr} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {k : Nat} {s : State} (hi : GInv s₀ b D n E k s) :
    WP isa Impl.Sm4.RISCV64.group s fun s' => (s'.gpr .a2 = 0 ∧ GDone s₀ b D n E s') ∨
      (s'.gpr .a2 ≠ 0 ∧ GInv s₀ b D n E (k + 1) s') := by
  have hfit := hp.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  rw [slots_eq] at hfit
  let v := n - 16 * k
  let c := min v 16
  obtain hv : v < 2 ^ 64 := by omega_arith
  obtain hc0 : 0 < c := by omega_arith
  obtain hc16 : c ≤ 16 := by omega_arith
  obtain hkc : 256 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 64 (256 * k)
  let T := b + BitVec.ofNat 64 (8 * tailSlot)
  obtain hwS : (⟨b, 8 * slots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr
  obtain hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain inT : ∀ t n, t + n ≤ 256 → t < 256 → InRegions s.wr (T + BitVec.ofNat 64 t) n := by
    intro t n ht ht'
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base b (by rw [slots_eq, tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain inA : ∀ t n, t + n ≤ 16 * c → t < 16 * c → InRegions s.wr (A + BitVec.ofNat 64 t) n := by
    intro t n ht ht'
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)
  obtain sepAT : Region.Disjoint ⟨A, 16 * c⟩ ⟨T, 16 * c⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq, tailSlot_eq]; omega_arith))
  unfold Impl.Sm4.RISCV64.group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.a2 hv) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a⟩ := movR_ok s₁ .t1 .a1
  obtain ⟨s₂b, e₂b, r₂b, o₂b, m₂b, rd₂b, wr₂b⟩ := slotAddr_ok s₂a .t2 tailSlot
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := shl4_ok s₂b .t3 .a4
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂b, rd₂a, rd₁]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂b, wr₂a, wr₁]
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₂b, m₂a, m₁]
  obtain g₂ : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .a4 → r ≠ t0 → s₂.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₂ r h3, o₂b r h2, o₂a r h1, o₁ r h4 h5]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [Interleave.runBlock_append, Interleave.runBlock_append, e₂a, Option.bind_some, e₂b, Option.bind_some,
      e₂], ?_⟩)
  refine WP.mono (copy_wp (X := A) (Y := T) hc0 hc16
    (by rw [o₂ _ (by decide), o₂b _ (by decide), r₂a, o₁ _ (by decide) (by decide), hi.a1])
    (by rw [o₂ _ (by decide), r₂b, o₂a _ (by decide), o₁ _ (by decide) (by decide), hi.base])
    (by rw [r₂, o₂b _ (by decide), o₂a _ (by decide), c₁, ofNat_shl4 (by omega_arith)])
    (fun t n ht ht' => by rw [rd₂', wr₂']; exact inRd (inA t n ht ht'))
    (fun t n ht ht' => by rw [wr₂']; exact inT t n (by omega_arith) (by omega_arith)) sepAT) fun s₃ ⟨cp₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  obtain f₃' : Frame [⟨T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact f₃
  obtain wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂']
  obtain rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂']
  obtain g₃' : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .a4 → r ≠ t0 → s₃.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by rw [g₃ r h1 h2 h3 h4, g₂ r h1 h2 h3 h5 h6]
  obtain base₃ : s₃.gpr sb = b := by
    rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hi.base]
  obtain sc₃ : ScrOk s₀ b E s₃.mem := by
    refine hi.scr.frame (mem₂ ▸ f₃) fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> refine VG.Offset.disjoint b ?_ ?_ ?_ <;>
      (try simp only [tailSlot_eq, tableSlot_eq, savedSlot_eq]) <;> omega_arith
  -- The sixteen blocks.
  obtain hkey : KeyCtx s₃ E :=
    { scr := by rw [base₃, wr₃']; exact hwS
      fit := by rw [base₃, slots_eq]; exact hfit
      al := by rw [base₃]; exact hp.al
      keys := fun e he => by rw [base₃]; exact sc₃.keys e he }
  obtain ha0₃ : s₃.gpr .a0 = s₃.gpr sb + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hi.a0, base₃]
  refine WP.seq (WP.mono (crypt16_wp hkey (sc₃.masks.ok base₃) ha0₃) fun s₅ ⟨c₅, b₅⟩ => ?_)
  obtain base₅ : s₅.gpr sb = b := by rw [c₅.base, base₃]
  obtain f₅ : Frame [⟨b, 8 * tableSlot⟩] s₃.mem s₅.mem := by have := c₅.frame; rw [base₃] at this; exact this
  obtain sc₅ : ScrOk s₀ b E s₅.mem := by
    refine sc₃.frame2 f₅ (c₅.masks.at base₅) fun t ht r hr => ?_
    simp only [scrRegions, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at ht hr
    subst hr
    rcases ht with rfl | rfl
    · exact VG.Offset.disjoint_base b (by rw [tableSlot_eq]) (by rw [tableSlot_eq]; omega_arith)
    · exact VG.Offset.disjoint_base b (by rw [tableSlot_eq, savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith)
  obtain k₅ : ∀ r, r ∉ sboxWrites → r ≠ kr → s₅.gpr r = s₃.gpr r := fun r h1 h2 => c₅.keep r h1 h2
  obtain g₅ : ∀ r, r ∉ sboxWrites → r ≠ kr → r ≠ .a4 → s₅.gpr r = s.gpr r := fun r h1 h2 h3 => by
    obtain hsub : ∀ x ∈ ([.t1, .t2, .t3, .t4, t0] : List Reg), x ∈ sboxWrites := by decide
    obtain h' : r ∉ ([.t1, .t2, .t3, .t4, t0] : List Reg) := fun h => h1 (hsub r h)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h'
    rw [k₅ r h1 h2, g₃' r h'.1 h'.2.1 h'.2.2.1 h'.2.2.2.1 h3 h'.2.2.2.2]
  obtain a1₅ : s₅.gpr .a1 = A := by rw [g₅ _ (by decide) (by decide) (by decide), hi.a1]
  obtain a2₅ : s₅.gpr .a2 = BitVec.ofNat 64 v := by rw [g₅ _ (by decide) (by decide) (by decide), hi.a2]
  obtain a0₅ : s₅.gpr .a0 = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₅ _ (by decide) (by decide) (by decide), hi.a0]
  obtain wr₅' : s₅.wr = s.wr := by rw [c₅.wr, wr₃']
  obtain rd₅' : s₅.rd = s.rd := by rw [c₅.rd, rd₃']
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp a2₅ hv) fun s₇ ⟨c₇, o₇, m₇, rd₇, wr₇⟩ => ?_))
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a⟩ := slotAddr_ok s₇ .t1 tailSlot
  obtain ⟨s₈b, e₈b, r₈b, o₈b, m₈b, rd₈b, wr₈b⟩ := movR_ok s₈a .t2 .a1
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := shl4_ok s₈b .t3 .a4
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [Interleave.runBlock_append, e₈a, Option.bind_some,
      show ([movR .t2 .a1, shlI .t3 .a4 4] : List Instr) = [movR .t2 .a1] ++ [shlI .t3 .a4 4] from rfl,
      Interleave.runBlock_append, e₈b, Option.bind_some, e₈], ?_⟩)
  obtain mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈b, m₈a, m₇]
  obtain wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈b, wr₈a, wr₇, wr₅']
  obtain rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₈b, rd₈a, rd₇, rd₅']
  obtain g₈ : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .a4 → r ≠ t0 → s₈.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₈ r h3, o₈b r h2, o₈a r h1, o₇ r h4 h5]
  refine WP.mono (copy_wp (X := T) (Y := A) hc0 hc16
    (by rw [o₈ _ (by decide), o₈b _ (by decide), r₈a, o₇ _ (by decide) (by decide), base₅])
    (by rw [o₈ _ (by decide), r₈b, o₈a _ (by decide), o₇ _ (by decide) (by decide), a1₅])
    (by rw [r₈, o₈b _ (by decide), o₈a _ (by decide), c₇, ofNat_shl4 (by omega_arith)])
    (fun t n ht ht' => by rw [rd₈', wr₈']; exact inRd (inT t n (by omega_arith) (by omega_arith)))
    (fun t n ht ht' => by rw [wr₈']; exact inA t n ht ht') sepAT.symm) fun s₉ ⟨cp₉, f₉, g₉, rd₉, wr₉⟩ => ?_
  obtain g₉' : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .a4 → r ≠ t0 → s₉.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by rw [g₉ r h1 h2 h3 h4, g₈ r h1 h2 h3 h5 h6]
  obtain a4₉ : s₉.gpr .a4 = BitVec.ofNat 64 c := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide), o₈ _ (by decide), o₈b _ (by decide),
      o₈a _ (by decide), c₇]
  obtain base₉ : s₉.gpr sb = b := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), base₅]
  obtain a1₉ : s₉.gpr .a1 = A := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a1₅]
  obtain a2₉ : s₉.gpr .a2 = BitVec.ofNat 64 v := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a2₅]
  obtain a0₉ : s₉.gpr .a0 = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a0₅]
  obtain wr₉' : s₉.wr = s₀.wr := by rw [wr₉, wr₈', hi.wr]
  obtain rd₉' : s₉.rd = s₀.rd := by rw [rd₉, rd₈', hi.rd]
  -- The scratch buffer and the frame.
  obtain subS : ∀ {d l : Nat}, d + l ≤ 8 * slots → Region.Sub ⟨b + BitVec.ofNat 64 d, l⟩ ⟨b, 8 * slots⟩ :=
    fun h => VG.Offset.sub_base b h
  obtain sc₉ : ScrOk s₀ b E s₉.mem := by
    refine (mem₈ ▸ sc₅).frame f₉ fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    obtain hsub : Region.Sub t ⟨b, 8 * slots⟩ := by
      simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> refine subS ?_ <;> (try simp only [tableSlot_eq, savedSlot_eq]) <;>
        rw [slots_eq] <;> omega_arith
    exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right hsub).symm
  obtain fr₉ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s.mem s₉.mem := by
    refine (((mem₂ ▸ f₃).sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₅.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((mem₈ ▸ f₉).sub fun r hr => ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)))
    · simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base D (by omega_arith)
  -- The blocks the sixteen-block code read are the group's, as on entry.
  obtain hblk : ∀ j < c, tailBlock s₃ j = Spec.Sm4.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * (16 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn]
    rw [base₃, addr_add, addr_add]
    obtain ht : 16 * j + u < 16 * c := by omega_arith
    have := cp₃ (16 * j + u) ht
    rw [addr_add] at this
    rw [show 8 * tailSlot + 16 * j + u = 8 * tailSlot + (16 * j + u) by omega_arith, this, mem₂, addr_add,
      hi.data _ (by omega_arith), ite_eq_right (by omega_arith),
      show 256 * k + (16 * j + u) = 16 * (16 * k + j) + u by omega_arith]
  obtain hdata : DInv s₀.mem s₉.mem D n (16 * k + c) (outF s₀.mem D E) := by
    intro i hin
    by_cases hin1 : 256 * k ≤ i ∧ i < 256 * k + 16 * c
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 256 * k) := by
        rw [addr_add, show 256 * k + (i - 256 * k) = i by omega_arith]
      rw [e1, cp₉ _ (by omega_arith), mem₈, ite_eq_left (show i < 16 * (16 * k + c) by omega_arith),
        show i / 16 = 16 * k + (i - 256 * k) / 16 by omega_arith, show i % 16 = (i - 256 * k) % 16 by omega_arith]
      obtain hj : (i - 256 * k) / 16 < c := by omega_arith
      obtain eT : T + BitVec.ofNat 64 (i - 256 * k) = s₅.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * ((i - 256 * k) / 16)) +
          BitVec.ofNat 64 ((i - 256 * k) % 16) := by
        rw [base₅, addr_add, addr_add, show 8 * tailSlot + 16 * ((i - 256 * k) / 16) + (i - 256 * k) % 16 =
          8 * tailSlot + (i - 256 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (tailBlock s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨A, 16 * c⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      obtain hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b, 8 * slots⟩) →
          ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
      rw [f₉ _ hout, mem₈,
        f₅.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)) (by simp only; omega_arith) hin,
        f₃'.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith))
          (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 256 * k
      · rw [ite_eq_left (show i < 16 * (16 * k) by omega_arith), ite_eq_left (show i < 16 * (16 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (16 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (16 * k + c) by omega_arith)]
  obtain fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₉.mem := hi.frame.trans fr₉
  -- On to the next group.
  obtain ⟨s₁₀, e₁₀, r₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := subR_ok s₉ .a2 .a2 .a4
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := addI_ok s₁₀ .a1 .a1 (imm := 256) (by decide)
  refine WP.of_runBlock ⟨s₁₁, by
    rw [show ([Instr.sub .a2 .a2 .a4, .addi .a1 .a1 256] : List Instr) =
      [.sub .a2 .a2 .a4] ++ [.addi .a1 .a1 256] from rfl, Interleave.runBlock_append, e₁₀,
      Option.bind_some, e₁₁], ?_⟩
  obtain hm : s₁₁.mem = s₉.mem := by rw [m₁₁, m₁₀]
  obtain a2₁₁ : s₁₁.gpr .a2 = BitVec.ofNat 64 (v - c) := by
    rw [o₁₁ _ (by decide), r₁₀, a2₉, a4₉, VG.Offset.ofNat_sub_ofNat (by omega_arith)]
  obtain base₁₁ : s₁₁.gpr sb = b := by rw [o₁₁ _ (by decide), o₁₀ _ (by decide), base₉]
  obtain rd₁₁' : s₁₁.rd = s₀.rd := by rw [rd₁₁, rd₁₀, rd₉']
  obtain wr₁₁' : s₁₁.wr = s₀.wr := by rw [wr₁₁, wr₁₀, wr₉']
  by_cases hlt : v ≤ 16
  · have hn : 16 * k + c = n := by omega_arith
    refine .inl ⟨by rw [a2₁₁, show v - c = 0 by omega_arith]; rfl, base₁₁, hm ▸ sc₉,
      fun i hi' => by rw [hm, hdata i hi', hn], hm ▸ fr, rd₁₁', wr₁₁'⟩
  · have hc : c = 16 := by omega_arith
    refine .inr ⟨fun h => ?_, base₁₁, ?_, ?_, by omega_arith, ?_, hm ▸ sc₉, ?_, hm ▸ fr, rd₁₁', wr₁₁'⟩
    · have hne : v - c ≠ 0 := by omega_arith
      rw [a2₁₁] at h
      apply hne
      have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
    · rw [r₁₁, o₁₀ _ (by decide), a1₉, show BitVec.ofInt 64 256 = BitVec.ofNat 64 256 from rfl, addr_add,
        show 256 * k + 256 = 256 * (k + 1) by omega_arith]
    · rw [a2₁₁, show v - c = n - 16 * (k + 1) by omega_arith]
    · rw [o₁₁ _ (by decide), o₁₀ _ (by decide), a0₉]
    · rw [hm, show 16 * (k + 1) = 16 * k + c by omega_arith]; exact hdata

end VG.Proof.Sm4.RISCV64

end

end

/-!
# SM4 ECB on RISCV64: the whole function

`ecb_wp`: with the working space as an argument (`ecbRISCV64`), `ecb dir`
saves the callee-saved registers, sets the masks, builds the table of round
keys in the order `dir` uses them, transforms the blocks a group at a time
(`dataGroup_wp`) and restores the registers. As on PPC64LE
(`Proof/Sm4/PPC64LE/Ecb.lean`), with the working space aligned to 8 bytes.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.RISCV64 VG.Impl.Sm4.RISCV64

/-- The specification's direction. -/
def specDirRISCV64 : Dir → Spec.Sm4.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- ECB on RISCV64 with its working space at `a3`. -/
def ecbRISCV64 (dir : Dir) : Contract RISCV64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 128⟩
    let data : Region := ⟨s.gpr .a1, 16 * (s.gpr .a2).toNat⟩
    let scratch : Region := ⟨s.gpr .a3, 8 * slots⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      data.Disjoint scratch ∧
      (s.gpr .a0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 16 * (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + 8 * slots ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat % 8 = 0
  post s s' :=
    Spec.Sm4.blocksAt s'.mem (s.gpr .a1) (s.gpr .a2).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem (s.gpr .a0)) (specDirRISCV64 dir)
        (Spec.Sm4.blocksAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 movR ldS stS)
open VG.Proof.Aes.RISCV64 (sboxWrites)
open VG.Proof.Sm4 (DInv blocksAt_of_dinv ecb_eq blockFn specDirRISCV64 ecbRISCV64 crypt_eq quads ofBlock outBlock)

theorem dataLoop_wp {s₀ : State} {b D : Addr} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {s : State} (hi : GInv s₀ b D n E 0 s) :
    WP isa (.loop Impl.Sm4.RISCV64.group (.nonzero .a2)) s (GDone s₀ b D n E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 16 * k ∧ GInv s₀ b D n E k s) (fun m s hs => ?_) n s
    ⟨0, by omega_using [], hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨(eval_nonzero s' .a2).trans (by rw [z]; rfl), d⟩
  · exact .inr ⟨(eval_nonzero s' .a2).trans (by rw [beq_false_of_ne z]; rfl), n - 16 * (k + 1),
      by have := d.lt; have := hk.lt; omega_arith, k + 1, rfl, d⟩

/-- The schedule, outside the scratch buffer's frame. -/
theorem sched_frame {m m' : Mem} {b sched : Addr} (hf : Frame [⟨b, 8 * slots⟩] m m')
    (hd : Region.Disjoint ⟨sched, 128⟩ ⟨b, 8 * slots⟩) :
    Spec.Sm4.scheduleAt m' sched = Spec.Sm4.scheduleAt m sched := by
  have hb : ∀ k < 128, m' (sched + BitVec.ofNat 64 k) = m (sched + BitVec.ofNat 64 k) := fun k hk =>
    hf.bytes (R := ⟨sched, 128⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd)
      (by show 128 ≤ 2 ^ 64; omega_arith) hk
  apply Vector.ext
  intro i hi
  simp only [Spec.Sm4.scheduleAt, Vector.getElem_ofFn, List.range, List.range.loop, List.foldl]
  rw [hb (4 * i + 0) (by omega_arith), hb (4 * i + 1) (by omega_arith), hb (4 * i + 2) (by omega_arith),
    hb (4 * i + 3) (by omega_arith)]

theorem prologue_ok (ms : List (Nat × BitVec 64)) (hms : ∀ kv ∈ ms, kv.1 < tableSlot)
    (hnd : (ms.map (·.1)).Nodup) {sr : Reg} {s₀ : State} {b : Addr} (hb : s₀.gpr sr = b)
    (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr) (hal : b.toNat % 8 = 0) :
    ∃ s, runBlock isa (([movR sb sr] : List Instr) ++ saveRegs ++ setSlots ms) s₀ = some s ∧
      s.gpr sb = b ∧ (∀ r, r ≠ sb → r ≠ t0 → r ≠ t1 → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ (∀ kv ∈ ms, slotW s kv.1 = kv.2) ∧ Frame [⟨b, 8 * slots⟩] s₀.mem s.mem ∧
      s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ sb sr
  have hb₁ : s₁.gpr sb = b := by rw [r₁, hb]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂, -, -⟩ := save_ok (b := b) (by rw [wr₁]; exact hw) hb₁ hal
  obtain ⟨s₃, e₃, v₃, -, g₃, rd₃, wr₃, f₃⟩ := setSlots_ok (b := b) ms (by rw [g₂ _ sb_ne_t0, hb₁])
    (by rw [wr₂, wr₁]; exact hw) hal hms hnd
  refine ⟨s₃, by
    rw [Interleave.runBlock_append, Interleave.runBlock_append, e₁, Option.bind_some, e₂, Option.bind_some, e₃],
    by rw [g₃ _ sb_ne_t0 sb_ne_t1, g₂ _ sb_ne_t0, hb₁],
    fun r h1 h2 h3 => by rw [g₃ r h2 h3, g₂ r h2, o₁ r h1], fun i hi => ?_, v₃, ?_,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  · rw [← o₁ _ (sreg_ne_sb i hi), ← sv₂ i hi]
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [tableSlot_eq, savedSlot_eq]; omega_using [])
      (by rw [savedSlot_eq]; omega_using [hi])
  · rw [← m₁]
    refine f₂.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega_using [])

theorem outF_spec (dir : Dir) (m : Mem) (sch : Spec.Sm4.Schedule) (D : Addr) (j : Nat) :
    outF m D (dirKeys dir sch) j = blockFn sch (specDirRISCV64 dir) (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  cases dir
  · simp only [outF, blockFn, specDirRISCV64, Spec.Sm4.encryptBlock, crypt_eq]; rfl
  · simp only [outF, blockFn, specDirRISCV64, Spec.Sm4.decryptBlock, crypt_eq]; rfl

/-- `ecbWith sr k`, from the arguments' regions with the working space at
`sr`, for code `k` that builds the table of `dir` from the prologue's state. -/
theorem ecbWith_wp (sr : Reg) (k : Prog isa) (dir : Dir) {s₀ : State}
    (hrd : s₀.rd = [⟨s₀.gpr .a0, 128⟩]) (hwr : s₀.wr = [⟨s₀.gpr .a1, 16 * (s₀.gpr .a2).toNat⟩, ⟨s₀.gpr sr, 8 * slots⟩])
    (dSS : Region.Disjoint ⟨s₀.gpr .a0, 128⟩ ⟨s₀.gpr sr, 8 * slots⟩)
    (dDS : Region.Disjoint ⟨s₀.gpr .a1, 16 * (s₀.gpr .a2).toNat⟩ ⟨s₀.gpr sr, 8 * slots⟩)
    (fitK : (s₀.gpr .a0).toNat + 128 ≤ 2 ^ 64) (fitD : (s₀.gpr .a1).toNat + 16 * (s₀.gpr .a2).toNat ≤ 2 ^ 64)
    (fitB : (s₀.gpr sr).toNat + 8 * slots ≤ 2 ^ 64) (hal : (s₀.gpr sr).toNat % 8 = 0)
    (hk : ∀ s₁, SchedPre s₁ (s₀.gpr sr) (s₀.gpr .a0) → s₁.gpr .a0 = s₀.gpr .a0 → MasksOk s₁ →
      (∀ r, r ≠ sb → r ≠ t0 → r ≠ t1 → s₁.gpr r = s₀.gpr r) →
      WP isa k s₁ (KeysPost s₁ (s₀.gpr sr) (s₀.gpr .a0) dir)) :
    WP isa (ecbWith sr k) s₀ fun s' => (∀ i < 12, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      Spec.Sm4.blocksAt s'.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat =
        Spec.Sm4.ecb (Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .a0)) (specDirRISCV64 dir)
          (Spec.Sm4.blocksAt s₀.mem (s₀.gpr .a1) (s₀.gpr .a2).toNat) := by
  let b := s₀.gpr sr
  let D := s₀.gpr .a1
  let n := (s₀.gpr .a2).toNat
  let sched := s₀.gpr .a0
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  have hrK : (⟨sched, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  unfold ecbWith
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, v₁, f₁, rd₁, wr₁⟩ := prologue_ok (keyMasks ++ bsKs)
    (fun kv hkv => by have := masks_lt kv hkv; rw [tableSlot_eq]; omega_using [this]) (by decide) (b := b) rfl hwS hal
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hk₁ : SchedPre s₁ b sched :=
    ⟨⟨b₁, by rw [wr₁]; exact hwS, fitB, hal⟩, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  have a0₁ : s₁.gpr .a0 = sched := g₁ _ (by decide) (by decide) (by decide)
  -- The table.
  refine WP.seq (WP.mono (hk s₁ hk₁ a0₁ v₁ g₁) fun s₂ k₂ => ?_)
  let E : Nat → Spec.Sm4.Word := dirKeys dir (Spec.Sm4.scheduleAt s₀.mem sched)
  have hsch : Spec.Sm4.scheduleAt s₁.mem sched = Spec.Sm4.scheduleAt s₀.mem sched := sched_frame f₁ dSS
  have hfitB := fitB
  rw [slots_eq] at hfitB
  have f₀₂ : Frame [⟨b, 8 * slots⟩] s₀.mem s₂.mem :=
    f₁.trans (k₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [tableEnd_eq, slots_eq]; omega_using [])⟩)
  have base₂ : s₂.gpr sb = b := k₂.pre.base
  have sc₂ : ScrOk s₀ b E s₂.mem := by
    refine ⟨k₂.masks.at base₂, fun e he => ?_, fun i hi => ?_⟩
    · have := k₂.key.keys e he
      rw [base₂, hsch] at this
      exact this
    · rw [← sv₁ i hi]
      refine k₂.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [tableEnd_eq, savedSlot_eq]; omega_using [])
        (by rw [savedSlot_eq]; omega_using [hi])
  have data₂ : ∀ i < 16 * n, s₂.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi =>
    f₀₂.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS)
      (by simp only; omega) hi
  have fr₂ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₂.mem :=
    f₀₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have a2₂ : s₂.gpr .a2 = s₀.gpr .a2 := by
    rw [k₂.regs _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide)]
  have a1₂ : s₂.gpr .a1 = D := by
    rw [k₂.regs _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide)]
  have rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, rd₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, wr₁]
  -- Any blocks?
  have hz₃ : (s₂.gpr .a2 == 0) = decide (n = 0) := by
    rw [a2₂, show s₀.gpr .a2 = BitVec.ofNat 64 n by simp only [n, BitVec.ofNat_toNat, BitVec.setWidth_eq]]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h; have := congrArg BitVec.toNat h; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [])] at this
    · intro h; rw [h]; rfl
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n E)
    (WP.ite (decide (n = 0)) ((eval_zero s₂ .a2).trans (by rw [hz₃])) (fun h0 => ?_) (fun h0 => ?_))
    fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₂, sc₂, fun i hi => by omega, fr₂, rd₂, wr₂⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitB, fitD, hal⟩ ⟨base₂, by rw [a1₂]; simp,
      by rw [a2₂, Nat.mul_zero, Nat.sub_zero]; simp [n], by omega_using [hn0], k₂.rdi, sc₂, fun i hi => ?_, fr₂, rd₂, wr₂⟩
    rw [data₂ i hi, ite_eq_right (by omega_using [])]
  -- The epilogue.
  obtain ⟨s₅, e₅, rg₅, -, m₅, -, -⟩ := restore_ok (by rw [d₄.wr]; exact hwS) d₄.base hal d₄.scr.saved
  refine WP.of_runBlock ⟨s₅, e₅, rg₅, ?_⟩
  have hd₅ : DInv s₀.mem s₅.mem D n n (outF s₀.mem D E) := fun i hi => by
    rw [m₅]; exact d₄.data i hi
  show Spec.Sm4.blocksAt s₅.mem D n = _
  rw [blocksAt_of_dinv hd₅, ecb_eq]
  simp only [Spec.Sm4.blocksAt, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  exact outF_spec dir s₀.mem _ D j

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbRISCV64 dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => (∀ i < 12, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (ecbRISCV64 dir).post s₀ s' := by
  obtain ⟨hrd, hwr, -, dSS, dDS, fitK, fitD, fitB, hal⟩ := hp
  exact ecbWith_wp .a3 (keys dir) dir hrd hwr dSS dDS fitK fitD fitB hal
    fun _ hk₁ a0₁ m₁ _ => keys_wp dir hk₁ a0₁ m₁

end VG.Proof.Sm4.RISCV64
