module
public import VerifiedGarbage.Proof.Sm4.RISCV64.Core

import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.CopyFast
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit
import VerifiedGarbage.Proof.Framework.Interleave

/-!
# The table of bitsliced round keys on RISCV64

`keyOne_step`: `keyOne h` bitslices round key `2 m + h`, half `h` of the
64-bit word at `a0`, into the table's entry at `kr`, every block's copy of
it alike. `keys_wp` copies the schedule to the tail buffer, which is
aligned, and builds the table from the copy in the order the rounds use the
round keys: `rk₀ … rk₃₁` for encryption, `rk₃₁ … rk₀` for decryption. As on
PPC64LE (`Proof/Sm4/PPC64LE/Keys.lean`), which reads the schedule itself.
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
  have hs : x = sparse (x.getLsbD 0) (x.getLsbD 16) (x.getLsbD 32) (x.getLsbD 48) := by
    refine BitVec.eq_of_getLsbD_eq fun k hk => ?_
    rw [getLsbD_sparse _ _ _ _ k hk]
    by_cases h : k % 16 = 0
    · have : k = 0 ∨ k = 16 ∨ k = 32 ∨ k = 48 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> simp
    · have : k ≠ 0 ∧ k ≠ 16 ∧ k ≠ 32 ∧ k ≠ 48 := by omega
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
    have hr : r ≠ t0 := fun h => ht (h ▸ List.mem_cons_self)
    have hn' := List.nodup_cons.mp hn
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
  have hok : Ok keyCfg s :=
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
  have hchk : check (lanes 64 7) keyCfg (linExt 0) (keyPre h) keyEnv
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
  have hall₁ : ∀ r, r ∉ sboxWrites → ((keyPre h).all fun i => dst i != some r) = true := fun r hr => by
    have : (restRegs.all fun r => (keyPre h).all fun i => dst i != some r) =
        true := by rcases hh with rfl | rfl <;> decide +kernel
    exact List.all_eq_true.mp this r (not_sboxWrites r hr)
  -- The fill.
  obtain ⟨s₁, e₁', v₁, o₁', m₁, rd₁', wr₁'⟩ := keyFill_ok s₀
  have hqW : ∀ j < 8, q j ∈ sboxWrites := by decide
  have k₁' : ∀ r, r ∉ sboxWrites → s₁.gpr r = s₀.gpr r := fun r hr =>
    o₁' r (fun j hj h => hr (h ▸ hqW j hj)) (fun h => hr (h ▸ by decide))
  have k₁ : ∀ r, r ∉ sboxWrites → s₁.gpr r = s.gpr r := fun r hr => (k₁' r hr).trans (o₀ r (hall₁ r hr))
  have e₁ : runBlock isa (keyLoad h) s = some s₁ := by
    rw [keyLoad, Interleave.runBlock_append, e₀, Option.bind_some, e₁']
  have rd₁ : s₁.rd = s.rd := by rw [rd₁', rd₀]
  have wr₁ : s₁.wr = s.wr := by rw [wr₁', wr₀]
  have hb₁ : s₁.gpr sb = s.gpr sb := (k₁' sb (by decide)).trans hb₀
  have hkr₁ : ∀ k ∈ keyMaskSlots, k < 64 → s₁.mem.readW (wordAddr (s.gpr sb) k) 64 =
      s.mem.readW (wordAddr (s.gpr sb) k) 64 := fun k hk hk' => by
    rw [m₁]; exact hkr₀ k hk hk'
  have f₁ : Frame [slotRegion keyCfg s] s.mem s₁.mem := by rw [m₁]; exact f₀
  -- The planes of the round key.
  have hQ : WordRel (Qs s₁) (fun _ => rkWord (s.mem.readW (wordAddr (s.gpr .a0) 0) 64) h) := by
    intro b' hb' i hi j hj
    have hp : 16 * i + b' < 64 := by omega_arith
    have hmem : (q j, keyBsG0 h j) ∈ qOuts (keyBsG0 h) := by
      simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
    have hz : ∀ p < 64, p % 16 ≠ 0 → (s₀.gpr (q j)).getLsbD p = false := fun p hp' h0 => by
      rw [ho₀ (q j) (keyBsG0 h j) hmem _ hp']; simp only [keyBsG0, h0, ↓reduceIte, xorBits_nil]
    have hb16 : keyBsG0 h j (16 * i) = keyBsG h j (16 * i) := by simp [keyBsG0]
    rw [Qs, v₁ j hj, getLsbD_fill hz hp, show (16 * i + b') / 16 = i by omega_arith,
      ho₀ (q j) (keyBsG0 h j) hmem _ (by omega_arith), hb16, keyBsG,
      xorBits_cons, xorBits_nil, Bool.xor_false,
      show 32 * h + 8 * (3 - 16 * i / 16) + j = 64 * 0 + (32 * h + 8 * (3 - i) + j) by omega_arith,
      bitOf_word _ _ _ (by rcases hh with rfl | rfl <;> omega_arith), rkWord, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight]
    simp only [show 8 * (3 - i) + j < 32 by omega_arith, decide_true, Bool.true_and]
    exact congrArg (BitVec.getLsbD _) (by omega_arith)
  -- The stores.
  have hkr₁' : s₁.gpr kr = s.gpr kr := k₁ kr (by decide)
  have hok₂ : Ok entryCfg s₁ :=
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
  have k₂ : ∀ r, s₂.gpr r = s₁.gpr r := fun r => o₂ r (by simp [keyStore, dst])
  have he₂ : ∀ j < 8, entryW s₂.mem b e j = Qs s₁ j := fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => by
    have h := hso₂ j (fun p => [64 * j + p]) (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      hj p hp
    rw [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp] at h
    rw [← h, entryW, wordAddr, hkr₁', hkr, addr_add]
  refine ⟨s₂, ?_, fun r hr => by rw [k₂, k₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun kv hkv => ?_,
    ?_, hQ.congr fun j hj => he₂ j hj⟩
  · rw [keyStore_eq, runBlock_app, e₁, Option.bind_some, e₂]
  · have hk : kv.1 < 64 := mask_lt hkv
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    have h2 : s₂.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = s₁.mem.readW (wordAddr (s.gpr sb) kv.1) 64 := by
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
  have hi : 2 * m + h < 32 := by omega_arith
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
  have hb : ∀ k < 128, m' (srcOf b + BitVec.ofNat 64 k) = m (srcOf b + BitVec.ofNat 64 k) := fun k hk => by
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
  have he0 := entOf_lt dir (show 2 * m < 32 by omega_arith)
  have he1 := entOf_lt dir (show 2 * m + 1 < 32 by omega_arith)
  have hsched : Spec.Sm4.scheduleAt s.mem (srcOf b) = Spec.Sm4.scheduleAt s₀.mem (srcOf b) :=
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
  have hpre₂ : KPre s₂ b :=
    hpre.congr (by rw [o₂ _ (by decide), o₁ _ (by decide)]) (by rw [wr₂, wr₁])
  have hrdi₂ : s₂.gpr .a0 = srcOf b + BitVec.ofNat 64 (8 * m) := by
    rw [o₂ _ (by decide), o₁ _ (by decide), hi.rdi]
  have hm₂ : MasksOk s₂ := fun kv hkv => by
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    rw [m₂, o₂ _ (by decide)]; exact m₁ kv hkv
  -- Round key `2 m + 1`.
  obtain ⟨s₃, e₃, o₃, rd₃, wr₃, m₃, f₃, E₃⟩ := keyOne_step (h := 1) (e := entOf dir (2 * m + 1)) (Or.inr rfl)
    hpre₂.base hpre₂.al hpre₂.scr r₂ he1 (by rw [hrdi₂]; exact hpre₂.srcIn hm) (by rw [hrdi₂]; exact hpre₂.srcAl m)
    (fun k hk => by rw [hrdi₂]; exact hpre₂.srcSep hm hk) hm₂
  have hfr₂ : Frame (keyRegions b) s₀.mem s₂.mem := by
    rw [m₂]; exact hi.frame.trans (f₁.sub (keyFrame_sub he0))
  rw [hrdi₂, rkWord_eq _ _ hm (by decide), src_eq hfr₂] at E₃
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := rsiStep_ok dir s₃ (b := b)
    (x := 8 * tableSlot + 64 * entOf dir (2 * m + 1)) (y := rsiAt dir (m + 1))
    st2 (by rw [o₃ _ (by decide), r₂])
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addI_ok s₄ .a0 .a0 (imm := 8) (by decide)
  have hmem : s₅.mem = s₃.mem := by rw [m₅, m₄]
  have hb₆ : s₅.gpr sb = s₃.gpr sb := by rw [o₅ _ (by decide), o₄ _ (by decide)]
  have hf₃ : Frame (keyRegions b) s₀.mem s₃.mem := hfr₂.trans (f₃.sub (keyFrame_sub he1))
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
  have hsrc : ∀ i n, i + n ≤ 128 → (⟨b, 8 * slots⟩ : Region).Contains (srcOf b + BitVec.ofNat 64 i) n :=
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
  have hcopy : ∀ r ∈ ([.t4, .t1, .t2, .t3] : List Reg), r ∈ sboxWrites := by decide
  have tsb : t.gpr sb = b := by rw [tk.gpr (by decide), o₁ _ (by decide) (by decide) (by decide), hb]
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
  have hk := masks_lt kv hkv
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
  have hinv : KInv u b dir 0 s₁ := by
    refine ⟨hp.toKPre.congr (by rw [o₁ _ (by decide)]) wr₁,
      by rw [r₁, hp.base, hk], by rw [o₁ _ (by decide), hrdi]; simp,
      fun i hi => by omega_arith, fun kv hkv => ?_, by rw [m₁]; exact Frame.refl _ _,
      fun r _ h2 _ => by rw [o₁ r h2], rd₁, wr₁⟩
    show s₁.mem.readW (wordAddr (s₁.gpr sb) kv.1) 64 = kv.2
    rw [m₁, o₁ _ (by decide)]; exact hm kv hkv
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.mono (keyPairs_wp dir 16 0 rfl s₁ hinv) fun s h => ?_⟩))
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := slotAddr_ok s .a0 tableEnd
  have hb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), h.pre.base]
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
  have hm' := hm.copy hp.base hu.base hf
  cases dir
  · exact keysGen_wp .encrypt tableSlot (by simp [rsiAt]) (by decide) hu ha hm' hs hf hr hrd hwr
  · exact keysGen_wp .decrypt (tableSlot + 8 * 31) (by simp [rsiAt, tableSlot_eq]) (by decide) hu ha hm' hs hf
      hr hrd hwr

end VG.Proof.Sm4.RISCV64
