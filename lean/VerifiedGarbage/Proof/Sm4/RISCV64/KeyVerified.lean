module

public import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
public import VerifiedGarbage.Proof.Sm4.RISCV64.Ecb
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Impl.StackScratch.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Ecb
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Impl.Sm4.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Sm4.Common
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit
import VerifiedGarbage.Proof.Sm4.Planes
public import VerifiedGarbage.Proof.Sm4.RISCV64.Round
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
meta import VerifiedGarbage.Impl.Sm4.RISCV64.ExpandKey
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.Interleave
meta import VerifiedGarbage.Proof.Sm4.Common
meta import VerifiedGarbage.Proof.Sm4.Layout
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit
meta import VerifiedGarbage.Proof.Sm4.Planes
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Round
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64

/-! ### `Sm4.RISCV64.KeyEk`, which only this module used -/

section

/-! ### `Sm4.RISCV64.KeyInit`, which only this module used -/

section

/-!
# The start of the SM4 key schedule on RISCV64

As on PPC64LE (`Proof/Sm4/PPC64LE/KeyVerified.lean`): the planes of `CK`
stored as constants (`ckTable_ok`, through a pointer to the table, beyond
an offset's reach from `a5`), and `MK ⊕ FK` stored to the sixteen blocks of
the tail buffer (`loadHalf_ok`, the key read a byte at a time), whose
words, bitsliced, are the key schedule's initial state `keyInit`.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (q m sb t0 t1 t2 movR ldS stS xorR)
open VG.Impl.Words.RISCV64 (li64 loadLE64)
open VG.Impl.Sm4 (planeOf fkWord)

/-! ## Stores of a register -/

/-- `sd r, 8 k(sb)` for each `k` of `ks`. -/
theorem storeAll_ok (r : Reg) : ∀ (ks : List Nat) {s : State} {b : Addr}, s.gpr sb = b →
    (⟨b, 8 * slots⟩ : Region) ∈ s.wr → b.toNat % 8 = 0 → (∀ k ∈ ks, k < tableSlot) →
    ∃ s', runBlock isa (ks.map fun k => stS k r) s = some s' ∧ (∀ k ∈ ks, slotW s' k = s.gpr r) ∧
      (∀ k < slots, k ∉ ks → slotW s' k = slotW s k) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * slots⟩] s.mem s'.mem
  | [], s, _, _, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k :: ks, s, b, hb, hw, hal, hk => by
    have hk0 : k < tableSlot := hk k List.mem_cons_self
    rw [tableSlot_eq] at hk0
    have e₁ := stS_ok s r (k := k) (by omega_using [hk0]) (by rw [hb]; exact hal) ⟨_, hw, by
      rw [hb]; exact VG.Offset.contains_base b (by rw [slots_eq]; omega_using [hk0]) (by omega_using [hk0])⟩
    let s₁ : State := { s with mem := s.mem.writeW (wordAddr (s.gpr sb) k) (s.gpr r) }
    obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := storeAll_ok r ks (s := s₁) hb hw hal
      fun k h => hk k (List.mem_cons_of_mem _ h)
    have hslot : ∀ j < slots, slotW s₁ j = if j = k then s.gpr r else slotW s j := fun j hj => by
      simp only [slotW, s₁]
      exact readW_slot_write _ hj (by rw [slots_eq]; omega_using [hk0])
    refine ⟨s', by rw [List.map_cons, show (stS k r :: ks.map fun k => stS k r) = [stS k r] ++ ks.map fun k => stS k r
        from rfl, Interleave.runBlock_append, e₁, Option.bind_some]; exact e', fun j hj => ?_, fun j hj hn => ?_,
      by rw [g'], by rw [rd'], by rw [wr'], ?_⟩
    · rcases List.mem_cons.mp hj with rfl | hj'
      · by_cases hin : j ∈ ks
        · rw [v' j hin]
        · rw [o' j (by rw [slots_eq]; omega_using [hk0]) hin, hslot j (by rw [slots_eq]; omega_using [hk0]), ite_eq_left rfl]
      · rw [v' j hj']
    · simp only [List.mem_cons, not_or] at hn
      rw [o' j hj hn.2, hslot j hj, ite_eq_right hn.1]
    · refine Frame.trans (fun x hx => ?_) f'
      simp only [s₁, Mem.writeW, Mem.write, wordAddr, hb]
      exact ite_eq_right fun h => hx _ (List.mem_singleton_self _) (VG.Offset.sub_base b
        (show 8 * k + 8 ≤ 8 * slots by rw [slots_eq]; omega_using [hk0]) _ (by simp only [Region.Contains]; omega_using [h]))

/-! ## `MK ⊕ FK` -/

/-- `t0 := ` the key's 64-bit word `h` (little-endian, through `t2` and
`t3`) `⊕ FK`, through `t1`. -/
theorem keyWord_ok (s : State) (h : Nat) (hh : h < 2)
    (hr : ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 (8 * h + 4 * i)) 4) :
    ∃ s', runBlock isa (loadLE64 t0 t2 (m 1) .a0 (8 * h) ++ li64 t1 t2 (fkWord h) ++
        ([xorR t0 t0 t1] : List Instr)) s = some s' ∧
      s'.gpr t0 = s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 (8 * h)) 64 ^^^ fkWord h ∧
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ m 1 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -⟩ := Interleave.runBlock_of_WP (Bytes.loadLE64_ok (s := s)
    (d := t0) (tmp := t2) (hi := m 1) (n := .a0) (off := 8 * h) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by omega_using [hh])
    (by have := hr 0 (by decide); simpa using this) (by have := hr 1 (by decide); simpa using this))
  obtain ⟨s₂, e₂, h₂⟩ := Interleave.runBlock_of_WP (ByteLoad.li64_ok (s := s₁) (d := t1) (tmp := t2)
    (by decide) (fkWord h))
  subst h₂
  let s₂ := (s₁.write t2 (sext32 ((fkWord h).setWidth 32))).write t1 (fkWord h)
  let s₃ := s₂.write t0 (s₂.gpr t0 ^^^ s₂.gpr t1)
  have e₃ : runBlock isa [xorR t0 t0 t1] s₂ = some s₃ := by
    simp only [xorR, runBlock_cons, exec_logic, runStep_some, runBlock_nil, s₃]
  have g₂ : ∀ r, r ≠ t1 → r ≠ t2 → s₂.gpr r = s₁.gpr r := fun r h1 h2 => by
    rw [RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]
  refine ⟨s₃, ?_, ?_, fun r h0 h1 h2 h3 => ?_, m₁, rd₁, wr₁⟩
  · rw [Interleave.runBlock_append, Interleave.runBlock_append, e₁, Option.bind_some, e₂, Option.bind_some, e₃]
  · rw [RegUpd.gpr_write_self, g₂ _ (by decide) (by decide), v₁, RegUpd.gpr_write_self]
  · rw [RegUpd.gpr_write_of_ne _ _ h0, g₂ r h1 h2, o₁ r h0 h2 h3]

theorem tailAt_lt {b h : Nat} (hb : b < 16) (hh : h < 2) : tailAt b h < tableSlot := by
  simp only [tailAt, tailSlot_eq, tableSlot_eq]; omega_using [hb, hh]

/-- Half `h` of the key, XOR `FK`, to the sixteen blocks. -/
theorem loadHalf_ok {s : State} {b : Addr} (h : Nat) (hh : h < 2) (hb : s.gpr sb = b)
    (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hal : b.toNat % 8 = 0)
    (hr : ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 (8 * h + 4 * i)) 4) :
    ∃ s', runBlock isa (loadHalf h) s = some s' ∧
      (∀ c < 16, slotW s' (tailAt c h) = s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 (8 * h)) 64 ^^^ fkWord h) ∧
      (∀ k < slots, (∀ c < 16, k ≠ tailAt c h) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ m 1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * slots⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := keyWord_ok s h hh hr
  obtain ⟨s', e', v', k', g', rd', wr', f'⟩ := storeAll_ok t0 ((List.range 16).map fun c => tailAt c h)
    (s := s₁) (by rw [o₁ _ (by decide) (by decide) (by decide) (by decide), hb]) (by rw [wr₁]; exact hw) hal
    (fun k hk => by simp only [List.mem_map, List.mem_range] at hk; obtain ⟨c, hc, rfl⟩ := hk
                    exact tailAt_lt hc hh)
  refine ⟨s', ?_, fun c hc => ?_, fun k hk hne => ?_, fun r h0 h1 h2 h3 => by rw [g', o₁ r h0 h1 h2 h3],
    by rw [rd', rd₁], by rw [wr', wr₁], by rw [← m₁]; exact f'⟩
  · rw [loadHalf, Interleave.runBlock_append, e₁, Option.bind_some]
    simpa only [List.map_map, Function.comp_def] using e'
  · rw [v' _ (by simp only [List.mem_map, List.mem_range]; exact ⟨c, hc, rfl⟩), v₁]
  · rw [k' k hk (by simp only [List.mem_map, List.mem_range, not_exists, not_and]; exact fun c hc h' => hne c hc h'.symm)]
    simp only [slotW, m₁, o₁ sb (by decide) (by decide) (by decide) (by decide)]

/-! ## The table of `CK` -/

/-- `li64 t0, v` (through `t1`); `sd t0, d(a4)`. -/
theorem ckOne_ok {s : State} {A : Addr} {d : Nat} (v : BitVec 64) (ha : s.gpr .a4 = A) (hd : d < 2048)
    (hal : (A + BitVec.ofNat 64 d).toNat % 8 = 0) (hw : InRegions s.wr (A + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (li64 t0 t1 v ++ ([.store .d t0 .a4 d] : List Instr)) s = some s' ∧
      s'.mem = s.mem.writeW (A + BitVec.ofNat 64 d) v ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, h₁⟩ := Interleave.runBlock_of_WP (ByteLoad.li64_ok (s := s) (d := t0) (tmp := t1) (by decide) v)
  subst h₁
  let s₁ := (s.write t1 (sext32 (v.setWidth 32))).write t0 v
  have ha₁ : s₁.gpr .a4 = A := by
    rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), ha]
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s₁.gpr .a4 + BitVec.ofNat 64 d) (s₁.gpr t0) }, ?_, ?_,
    fun r h0 h1 => ?_, rfl, rfl⟩
  · rw [Interleave.runBlock_append, e₁, Option.bind_some]
    show runBlock isa [.store .d t0 .a4 d] s₁ = _
    simp only [runBlock_cons, exec_store_d (s := s₁) hd (by rw [ha₁]; exact hal) (by rw [ha₁]; exact hw),
      runStep_some, runBlock_nil]
  · show s₁.mem.writeW (s₁.gpr .a4 + BitVec.ofNat 64 d) (s₁.gpr t0) = _
    rw [ha₁, RegUpd.gpr_write_self]; rfl
  · show s₁.gpr r = _
    rw [RegUpd.gpr_write_of_ne _ _ h0, RegUpd.gpr_write_of_ne _ _ h1]

/-- Constants to the words at offsets `8 k` of `A`, through `a4`. -/
theorem ckStores_ok {A : Addr} (hal : A.toNat % 8 = 0) :
    ∀ (ms : List (Nat × BitVec 64)) {s : State}, s.gpr .a4 = A →
      (∀ k < 256, InRegions s.wr (wordAddr A k) 8) →
      (∀ kv ∈ ms, kv.1 < 256) → (ms.map (·.1)).Nodup →
      ∃ s', runBlock isa (ms.flatMap fun (k, v) => li64 t0 t1 v ++ ([.store .d t0 .a4 (8 * k)] : List Instr)) s = some s' ∧
        (∀ kv ∈ ms, s'.mem.readW (wordAddr A kv.1) 64 = kv.2) ∧
        (∀ k < 256, k ∉ ms.map (·.1) → s'.mem.readW (wordAddr A k) 64 = s.mem.readW (wordAddr A k) 64) ∧
        (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        Frame [⟨A, 2048⟩] s.mem s'.mem
  | [], s, _, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | (k, v) :: ms, s, ha, hw, hk, hnd => by
    have hk0 : k < 256 := hk _ List.mem_cons_self
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := ckOne_ok (d := 8 * k) v ha (by omega_using [hk0]) (Spill.al8 hal (by omega_using []))
      (hw k hk0)
    have ha₁ : s₁.gpr .a4 = A := by rw [g₁ _ (by decide) (by decide), ha]
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := ckStores_ok hal ms (s := s₁) ha₁ (fun k hk => by rw [wr₁]; exact hw k hk)
      (fun kv h => hk kv (List.mem_cons_of_mem _ h)) hnd.2
    have hslot : ∀ j < 256, s₁.mem.readW (wordAddr A j) 64 = if j = k then v else s.mem.readW (wordAddr A j) 64 :=
      fun j hj => by
        rw [m₁, show A + BitVec.ofNat 64 (8 * k) = wordAddr A k from rfl]
        split
        · rename_i h; subst h; exact Mem.readW_writeW_self64 _ _ _
        · rename_i h; exact Mem.readW_writeW_sep (slot_sep A (by omega_using [hj]) (by omega_using [hk0]) h) (by decide)
    refine ⟨s', by
      rw [List.flatMap_cons, Interleave.runBlock_append, e₁, Option.bind_some]; exact e', fun kv hkv => ?_,
      fun j hj hn => ?_, fun r h0 h1 => by rw [g' r h0 h1, g₁ r h0 h1], by rw [rd', rd₁], by rw [wr', wr₁], ?_⟩
    · rcases List.mem_cons.mp hkv with rfl | hkv'
      · rw [o' _ hk0 hnd.1, hslot _ hk0, ite_eq_left rfl]
      · exact v' kv hkv'
    · simp only [List.map_cons, List.mem_cons, not_or] at hn
      rw [o' j hj hn.2, hslot j hj, ite_eq_right hn.1]
    · refine Frame.trans ?_ f'
      rw [m₁]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Offset.contains_base A (by omega_using [hk0]) (by omega_using [hk0]))

end VG.Proof.Sm4.RISCV64

end

end

/-! ### `Sm4.RISCV64.KeyLoop`, which only this module used -/

section

/-!
# The loop of the SM4 key schedule on RISCV64

Each iteration runs four rounds of the key schedule (`rounds4_ok .key`),
puts the state's words of the first copy in the tail buffer as a block
(`fromBs0_step`), and
stores them to the schedule as little-endian words (`extract_ok`): the
first block's 64-bit words, byte-reversed (stored big-endian a byte at a
time, `storeBE`). As on PPC64LE (`Proof/Sm4/PPC64LE/KeyLoop.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 movR ldS stS)
open VG.Impl.Words.RISCV64 (storeBE)
open VG.RISCV64.ByteLoad (beBytes)
open VG.WriteBytes (writeBytes writeBytes_frame)
open VG.Proof.Aes.RISCV64 (sboxWrites)
open VG.Impl.Sm4 (planeOf fkWord)
open VG.Proof.Sm4 (WordRel quads ofBlock outBlock keyInit rkOf readW64_bit getLsbD_outBlock' ofInt_nat)

/-! ## Bytes -/

/-- A byte of a big-endian word written. -/
theorem beBytes_byte (m : Mem) (q : Addr) (x : BitVec 64) {t j : Nat} (ht : t < 8) (hj : j < 8) :
    ((writeBytes m q (beBytes 8 x)) (q + BitVec.ofNat 64 t)).getLsbD j = x.getLsbD (8 * (7 - t) + j) := by
  simp only [writeBytes, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, ByteLoad.beBytes_length]
  rw [Nat.mod_eq_of_lt (by omega_arith)]
  simp only [ht, ↓reduceIte, beBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht,
    Option.map_some, Option.getD_some, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  simp only [hj, decide_true, Bool.true_and]

/-- A byte outside the bytes written. -/
theorem writeBytes_other (m : Mem) (q x : Addr) (xs : List Byte) (h : ¬ (x - q).toNat < xs.length) :
    writeBytes m q xs x = m x := by
  simp only [writeBytes, h, ite_false]

/-- `storeBE 8 t0 t1 a1 off`. -/
theorem storeBE8_ok (s : State) {off : Nat} (ho : off + 8 ≤ 2048)
    (hw : ∀ j < 8, InRegions s.wr (s.gpr .a1 + BitVec.ofNat 64 (off + j)) 1) :
    ∃ s', runBlock isa (storeBE 8 t0 t1 .a1 off) s = some s' ∧
      s'.mem = writeBytes s.mem (s.gpr .a1 + BitVec.ofNat 64 off) (beBytes 8 (s.gpr t0)) ∧
      (∀ r, r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e', h'⟩ := Interleave.runBlock_of_WP (ByteLoad.storeBE_ok (s := s) (v := t0) (tmp := t1) (n := .a1)
    (off := off) (w := 8) (by decide) (by decide) (by decide) (by decide) ho hw)
  subst h'
  exact ⟨_, e', rfl, fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl⟩

/-- A byte of the tail buffer's block `0`. -/
theorem tail_byte (s : State) {h t j : Nat} (hh : h < 2) (ht : t < 8) (hj : j < 8) :
    (slotW s (tailAt 0 h)).getLsbD (8 * t + j) = ((tailBlock s 0)[8 * h + t]'(by omega_arith)).getLsbD j := by
  rw [slotW, readW64_bit _ _ ht hj]
  simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn, wordAddr, addr_add, tailAt]
  rw [show 8 * (tailSlot + 2 * 0 + h) + t = 8 * tailSlot + 16 * 0 + (8 * h + t) by omega_arith]

/-! ## The extraction -/

/-- The schedule's bytes `16 m … 16 m + 15`: the words of the tail buffer's
first block, the last first, each little-endian. -/
theorem extract_ok {s : State} {b S : Addr} {m : Nat} (hm : m < 8) (hb : s.gpr sb = b) (hal : b.toNat % 8 = 0)
    (ha1 : s.gpr .a1 = S + BitVec.ofNat 64 (16 * m))
    (hS : ∀ t < 16, InRegions s.wr (S + BitVec.ofNat 64 (16 * m + t)) 1)
    (hT : ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr b (tailAt 0 t)) 8)
    (hsep : ∀ t < 2, Region.Disjoint ⟨wordAddr b (tailAt 0 t), 8⟩ ⟨S + BitVec.ofNat 64 (16 * m), 16⟩) :
    ∃ s', runBlock isa extract s = some s' ∧
      (∀ t < 16, ∀ j < 8, (s'.mem (S + BitVec.ofNat 64 (16 * m + t))).getLsbD j =
        ((tailBlock s 0)[15 - t]'(by omega_arith)).getLsbD j) ∧
      Frame [⟨S + BitVec.ofNat 64 (16 * m), 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hal' : (s.gpr sb).toNat % 8 = 0 := by rw [hb]; exact hal
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldMask_ok (r := t0) (k := tailAt 0 1)
    (by simp only [tailAt, tailSlot_eq]; omega_arith) hal' (by rw [hb]; exact hT 1 (by decide)) rfl
  obtain ha1₁ : s₁.gpr .a1 = S + BitVec.ofNat 64 (16 * m) := by rw [o₁ _ (by decide), ha1]
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := storeBE8_ok s₁ (off := 0) (by decide) fun j hj => by
    rw [wr₁, ha1₁, addr_add, Nat.zero_add]; exact hS j (by omega_arith)
  obtain hb₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide), o₁ _ (by decide), hb]
  obtain ⟨s₄, e₄, v₄, o₄, m₄, rd₄, wr₄⟩ := ldMask_ok (s := s₃) (r := t0) (k := tailAt 0 0)
    (by simp only [tailAt, tailSlot_eq]; omega_arith) (by rw [hb₃]; exact hal)
    (by rw [rd₃, wr₃, rd₁, wr₁, hb₃]; exact hT 0 (by decide)) rfl
  obtain ha1₄ : s₄.gpr .a1 = S + BitVec.ofNat 64 (16 * m) := by
    rw [o₄ _ (by decide), g₃ _ (by decide), ha1₁]
  obtain ⟨s₆, e₆, m₆, g₆, rd₆, wr₆⟩ := storeBE8_ok s₄ (off := 8) (by decide) fun j hj => by
    rw [wr₄, wr₃, wr₁, ha1₄, addr_add]; exact hS (8 + j) (by omega_arith)
  obtain hW₃ : s₃.mem = writeBytes s.mem (S + BitVec.ofNat 64 (16 * m)) (beBytes 8 (slotW s (tailAt 0 1))) := by
    rw [m₃, ha1₁, v₁, m₁, addr_add, Nat.add_zero]
  obtain q0 : s₄.gpr t0 = slotW s (tailAt 0 0) := by
    rw [v₄]
    simp only [slotW, hb₃, hb, hW₃]
    exact (writeBytes_frame _ _ _ (Region.contains_self _ _)).readW (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hsep 0 (by decide)).sub_right (Region.sub_prefix (by simp [ByteLoad.beBytes_length])))
      (by decide)
  obtain hm6 : s₆.mem = writeBytes (writeBytes s.mem (S + BitVec.ofNat 64 (16 * m)) (beBytes 8 (slotW s (tailAt 0 1))))
      (S + BitVec.ofNat 64 (16 * m + 8)) (beBytes 8 (slotW s (tailAt 0 0))) := by
    rw [m₆, m₄, hW₃, ha1₄, q0, addr_add]
  refine ⟨s₆, ?_, fun t ht j hj => ?_, ?_, fun r hr h1 => ?_, by rw [rd₆, rd₄, rd₃, rd₁],
    by rw [wr₆, wr₄, wr₃, wr₁]⟩
  · rw [extract, Interleave.runBlock_append, Interleave.runBlock_append, Interleave.runBlock_append,
      e₁, Option.bind_some, e₃, Option.bind_some, e₄, Option.bind_some, e₆]
  · rw [hm6]
    by_cases h8 : t < 8
    · rw [writeBytes_other _ _ _ _ (by
          rw [ByteLoad.beBytes_length]
          exact VG.Proof.Sm4.off_sub_not S (n := 8) (Or.inl (by omega_arith)) (by omega_arith) (by decide) (by omega_arith)),
        ← addr_add, beBytes_byte _ _ _ h8 hj, show 8 * (7 - t) + j = 8 * (7 - t) + j from rfl,
        tail_byte s (by decide) (by omega_arith) hj]
      simp only [show 8 * 1 + (7 - t) = 15 - t by omega_arith]
    · rw [show S + BitVec.ofNat 64 (16 * m + t) = S + BitVec.ofNat 64 (16 * m + 8) + BitVec.ofNat 64 (t - 8) by
          rw [addr_add, show 16 * m + 8 + (t - 8) = 16 * m + t by omega_arith], beBytes_byte _ _ _ (by omega_arith) hj,
        tail_byte s (by decide) (by omega_arith) hj]
      simp only [show 8 * 0 + (7 - (t - 8)) = 15 - t by omega_arith]
  · rw [hm6]
    exact (writeBytes_frame _ _ _ (by
        rw [ByteLoad.beBytes_length]; exact VG.Offset.contains S (by omega_arith) (by omega_arith) (by omega_arith))).trans
      (writeBytes_frame _ _ _ (by
        rw [ByteLoad.beBytes_length]; exact VG.Offset.contains S (by omega_arith) (by omega_arith) (by omega_arith)))
  · rw [g₆ r h1, o₄ r hr, g₃ r h1, o₁ r hr]

/-! ## The loop -/

/-- What the loop keeps, after `m` of its eight iterations: the state holds
the key schedule's words after `4 m` rounds, and the schedule its first
`4 m` round keys. -/
structure EkInv (s₀ : State) (b S : Addr) (key : Spec.Sm4.Block) (m : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  a1 : s.gpr .a1 = S + BitVec.ofNat 64 (16 * m)
  a4 : s.gpr .a4 = b + BitVec.ofNat 64 (8 * tableEnd)
  kr : AtEntry s b (4 * m)
  keys : KeyCtx s Spec.Sm4.ck
  masks : MasksOk s
  st : StRel s (fun _ => quads .key Spec.Sm4.ck m (keyInit key))
  sched : ∀ i < 4 * m, ∀ c < 4, ∀ j < 8,
    (s.mem (S + BitVec.ofNat 64 (4 * i + c))).getLsbD j = (rkOf key i).getLsbD (8 * c + j)
  saved : Saved s₀ b s.mem
  frame : Frame [⟨b, 8 * slots⟩, ⟨S, 128⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The scratch buffer and the schedule, writable and apart. -/
structure EkPre (s₀ : State) (b S : Addr) : Prop where
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr
  sch : (⟨S, 128⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨S, 128⟩ ⟨b, 8 * slots⟩
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  fitS : S.toNat + 128 ≤ 2 ^ 64
  al : b.toNat % 8 = 0

theorem ekIter_ok {s₀ : State} {b S : Addr} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S) {m : Nat} (hm : m < 8)
    {s : State} (hi : EkInv s₀ b S key m s) :
    ∃ s', runBlock isa keyBody s = some s' ∧ EkInv s₀ b S key (m + 1) s' ∧
      (s'.gpr t0 == 0) = decide (m + 1 = 8) := by
  have hfit := hp.fit
  have hfitS := hp.fitS
  rw [slots_eq] at hfit
  obtain hc0 : Ctx s s := Ctx.refl hi.masks
  -- Four rounds.
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := rounds4_ok .key hi.keys hc0 (by rw [hi.base]; exact hi.kr) hm hi.st
  obtain ⟨s₂, e₂, kr₂, o₂, m₂, rd₂, wr₂⟩ := addKp_ok s₁ 256 (by decide)
  obtain c₂ : Ctx s s₂ := c₁.kr o₂ m₂ rd₂ wr₂
  rw [show BitVec.ofInt 64 256 = BitVec.ofNat 64 256 from rfl] at kr₂
  obtain X₂ : StRel s₂ (fun _ => quads .key Spec.Sm4.ck (m + 1) (keyInit key)) :=
    X₁.congr fun k => by simp only [slotW, m₂, o₂ sb (by decide)]
  -- The words to the tail buffer.
  obtain ⟨s₃, e₃, c₃, kr₃, X₃, T₃⟩ := fromBs0_step hi.keys c₂ X₂
  obtain base₃ : s₃.gpr sb = b := by rw [c₃.base, hi.base]
  obtain a1₃ : s₃.gpr .a1 = S + BitVec.ofNat 64 (16 * m) := by rw [c₃.keep _ (by decide) (by decide), hi.a1]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [c₃.wr, hi.wr]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [c₃.rd, hi.rd]
  obtain inS : ∀ t < 16, InRegions s₃.wr (S + BitVec.ofNat 64 (16 * m + t)) 1 := fun t ht =>
    ⟨_, by rw [wr₃]; exact hp.sch, VG.Offset.contains_base S (by omega_arith) (by omega_arith)⟩
  obtain inT : ∀ t < 2, InRegions (s₃.rd ++ s₃.wr) (wordAddr b (tailAt 0 t)) 8 := fun t ht =>
    ⟨_, List.mem_append_right _ (by rw [wr₃]; exact hp.scr), by
      rw [wordAddr]; exact VG.Offset.contains_base b (by rw [tailAt, tailSlot_eq, slots_eq]; omega_arith)
        (by rw [tailAt, tailSlot_eq]; omega_arith)⟩
  obtain sepTS : ∀ k < slots, Region.Disjoint ⟨wordAddr b k, 8⟩ ⟨S + BitVec.ofNat 64 (16 * m), 16⟩ := fun k hk =>
    (hp.sep.sub_left (VG.Offset.sub_base S (by omega_arith))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq] at hk ⊢; omega_arith)) |>.symm
  -- To the schedule.
  obtain ⟨s₄, e₄, B₄, f₄, o₄, rd₄, wr₄⟩ := extract_ok hm base₃ hp.al a1₃ inS inT
    (fun t ht => sepTS _ (by have := tailAt_lt (b := 0) (by decide) ht; rw [tableSlot_eq] at this; rw [slots_eq]; omega_arith))
  obtain keep₄ : ∀ k < slots, slotW s₄ k = slotW s₃ k := fun k hk => by
    simp only [slotW, o₄ sb (by decide) (by decide), base₃]
    exact f₄.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sepTS k hk) (by decide)
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addI_ok s₄ .a1 .a1 (imm := 16) (by decide)
  rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl] at r₅
  obtain ⟨s₆, e₆, z₆, g₆, m₆, rd₆, wr₆⟩ := subR_ok s₅ t0 kr .a4
  obtain mem₆ : s₆.mem = s₄.mem := by rw [m₆, m₅]
  obtain g₆' : ∀ r, r ≠ .a1 → r ≠ t0 → r ≠ t1 → s₆.gpr r = s₃.gpr r := fun r h1 h2 h3 => by rw [g₆ r h2, o₅ r h1, o₄ r h2 h3]
  obtain base₆ : s₆.gpr sb = b := by rw [g₆' _ (by decide) (by decide) (by decide), base₃]
  obtain keep₆ : ∀ k < slots, slotW s₆ k = slotW s₃ k := fun k hk => by
    rw [← keep₄ k hk]; simp only [slotW, mem₆, g₆' sb (by decide) (by decide) (by decide), o₄ sb (by decide) (by decide)]
  obtain kr₆ : AtEntry s₆ b (4 * (m + 1)) := by
    rw [AtEntry, g₆' _ (by decide) (by decide) (by decide), kr₃, kr₂, k₁, show s.gpr kr = _ from hi.kr, addr_add,
      show 8 * tableSlot + 64 * (4 * m) + 256 = 8 * tableSlot + 64 * (4 * (m + 1)) by omega_arith]
  obtain rdi₆ : s₆.gpr .a4 = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₆' _ (by decide) (by decide) (by decide), c₃.keep _ (by decide) (by decide), hi.a4]
  obtain hent : ∀ (st : State) e j, entryW st.mem (st.gpr sb) e j = slotW st (tableSlot + 8 * e + j) := fun st e j => by
    simp only [entryW, slotW, wordAddr]; rw [show 8 * (tableSlot + 8 * e + j) = 8 * tableSlot + 64 * e + 8 * j by omega_arith]
  obtain key₃ := hi.keys.of_ctx c₃
  -- The schedule's bytes outside this iteration's.
  obtain old₆ : ∀ x, (∀ r ∈ [(⟨b, 8 * tableSlot⟩ : Region), ⟨S + BitVec.ofNat 64 (16 * m), 16⟩], ¬ r.Contains x 1) →
      s₆.mem x = s.mem x := fun x hx => by
    rw [mem₆, f₄ x (fun r hr => hx r (by simp at hr; simp [hr])),
      c₃.frame x (fun r hr => by simp at hr; subst hr; rw [hi.base]; exact hx _ (by simp))]
  refine ⟨s₆, ?_, ⟨base₆, ?_,
    rdi₆, kr₆, ⟨by rw [base₆, wr₆, wr₅, wr₄, wr₃]; exact hp.scr, by rw [base₆]; rw [slots_eq]; exact hfit,
      by rw [base₆]; exact hp.al,
      fun e he => (key₃.keys e he).congr fun j hj => by
        rw [hent s₆, hent s₃, keep₆ _ (by rw [tableSlot_eq, slots_eq]; omega_arith)]⟩,
    fun kv hkv => by rw [keep₆ _ (by have := mask_lt hkv; rw [slots_eq]; omega_arith)]; exact c₃.masks kv hkv,
    fun w hw => (X₃ w hw).congr fun j hj => keep₆ _ (by simp only [stateSlot, slots_eq]; omega_arith),
    fun i hi' c hc j hj => ?_, fun i hi' => ?_, ?_, by rw [rd₆, rd₅, rd₄, rd₃], by rw [wr₆, wr₅, wr₄, wr₃]⟩, ?_⟩
  · rw [keyBody, Interleave.runBlock_append, Interleave.runBlock_append, Interleave.runBlock_append, Interleave.runBlock_append, e₁, Option.bind_some,
      e₂, Option.bind_some,
      e₃, Option.bind_some, e₄, Option.bind_some,
      show ([.addi .a1 .a1 16, .sub t0 kr .a4] : List Instr) =
        [.addi .a1 .a1 16] ++ [.sub t0 kr .a4] from rfl, Interleave.runBlock_append, e₅, Option.bind_some, e₆]
  · rw [g₆ _ (by decide), r₅, o₄ _ (by decide) (by decide), a1₃, addr_add, show 16 * m + 16 = 16 * (m + 1) by omega_arith]
  · by_cases hnew : 4 * m ≤ i
    · have ht : 4 * (i - 4 * m) + c < 16 := by omega_arith
      obtain hB := B₄ _ ht j hj
      rw [show 16 * m + (4 * (i - 4 * m) + c) = 4 * i + c by omega_arith] at hB
      rw [mem₆, hB, T₃, getLsbD_outBlock' _ _ hj]
      simp only [rkOf]
      rw [show i / 4 + 1 = m + 1 by omega_arith, show 3 - (15 - (4 * (i - 4 * m) + c)) / 4 = i % 4 by omega_arith,
        show 8 * (3 - (15 - (4 * (i - 4 * m) + c)) % 4) + j = 8 * c + j by omega_arith]
    · rw [old₆ _ (fun r hr => ?_)]
      · exact hi.sched i (by omega_arith) c hc j hj
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · intro hc'
          exact hp.sep (S + BitVec.ofNat 64 (4 * i + c)) (VG.Offset.contains_base S (by omega_arith) (by omega_arith))
            (Region.sub_prefix (show 8 * tableSlot ≤ 8 * slots by rw [tableSlot_eq, slots_eq]; omega_arith) _ hc')
        · exact VG.Proof.Sm4.not_contains_off S (Or.inl (by omega_arith)) (by omega_arith) (by decide) (by omega_arith)
  · have hk : savedSlot + i < slots := by rw [savedSlot_eq, slots_eq]; omega_arith
    obtain h1 : s₆.mem.readW (wordAddr b (savedSlot + i)) 64 = s₃.mem.readW (wordAddr b (savedSlot + i)) 64 := by
      have := keep₆ _ hk; simp only [slotW, base₆, base₃] at this; exact this
    obtain h2 : s₃.mem.readW (wordAddr b (savedSlot + i)) 64 = s.mem.readW (wordAddr b (savedSlot + i)) 64 :=
      c₃.frame.readW (r := ⟨wordAddr b (savedSlot + i), 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [hi.base, wordAddr]
        exact VG.Offset.disjoint_base _ (by rw [tableSlot_eq, savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith))
        (by decide)
    rw [h1, h2]; exact hi.saved i hi'
  · rw [mem₆]
    refine hi.frame.trans ((c₃.frame.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      (f₄.sub fun r hr => ⟨⟨S, 128⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩))
    · simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
      exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base S (by omega_arith)
  · rw [z₆, o₅ _ (by decide), o₅ _ (by decide), o₄ _ (by decide) (by decide), o₄ _ (by decide) (by decide), kr₃, kr₂, k₁,
      show s.gpr kr = _ from hi.kr, c₃.keep _ (by decide) (by decide), hi.a4, addr_add,
      show 8 * tableSlot + 64 * (4 * m) + 256 = 8 * tableSlot + 64 * (4 * (m + 1)) by omega_arith,
      show 8 * tableEnd = 8 * tableSlot + 64 * 32 by rw [tableSlot_eq, tableEnd_eq],
      entry_beq _ (by rw [tableSlot_eq]; omega_arith) (by rw [tableSlot_eq]; omega_arith)]
    simp only [decide_eq_decide]; omega_arith

end VG.Proof.Sm4.RISCV64

end

end


/-!
# The SM4 key schedule on RISCV64: the whole function

`expandKey_wp`: with the working space as an argument (`expandKeyRISCV64`),
`expandKey` saves the callee-saved registers, sets the masks, stores the
table of `CK`'s planes, bitslices sixteen copies of `MK ⊕ FK`, runs the
loop (`ekIter_ok`) and restores the registers; the schedule is the
specification's `expandKey`. As on PPC64LE (`Proof/Sm4/PPC64LE/KeyVerified.lean`),
with the working space aligned to 8 bytes.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.RISCV64 VG.Impl.Sm4.RISCV64

/-- The key schedule on RISCV64 with its working space at `a2`. -/
def expandKeyRISCV64 : Contract RISCV64.isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 16⟩
    let sched : Region := ⟨s.gpr .a1, 128⟩
    let scratch : Region := ⟨s.gpr .a2, 8 * slots⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧ key.Disjoint sched ∧ key.Disjoint scratch ∧
      sched.Disjoint scratch ∧
      (s.gpr .a0).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 128 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + 8 * slots ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat % 8 = 0
  post s s' :=
    Spec.Sm4.scheduleAt s'.mem (s.gpr .a1) = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem (s.gpr .a0))
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (q m sb t0 t1 t2 movR ldS stS)
open VG.Impl.Words.RISCV64 (li64)
open VG.Proof.Aes.RISCV64 (sboxWrites)
open VG.Impl.Sm4 (planeOf fkWord)
open VG.Proof.Sm4 (planeOf_rel fkWord_bit WordRel quads ofBlock outBlock keyInit rkOf readW64_bit getLsbD_wordAt ofInt_nat
  expandKeyRISCV64)

/-! ## `MK ⊕ FK` in the tail buffer -/

theorem keyInit_bit (key : Spec.Sm4.Block) {w i j : Nat} (hi : i < 4) (hj : j < 8) :
    (keyInit key w).getLsbD (8 * (3 - i) + j) =
      ((key.getD (4 * w + i) 0).getLsbD j ^^ (Spec.Sm4.fk.getD w 0).getLsbD (8 * (3 - i) + j)) := by
  rw [keyInit, BitVec.getLsbD_xor, getLsbD_wordAt _ _ hi hj]

/-- Byte `i` of block `c` of the tail buffer, from its words. -/
theorem tailBlock_bit (s : State) {c i j : Nat} (hi : i < 16) (hj : j < 8) :
    ((tailBlock s c).getD i 0).getLsbD j = (slotW s (tailAt c (i / 8))).getLsbD (8 * (i % 8) + j) := by
  rw [slotW, readW64_bit _ _ (by omega_arith) hj, VG.Proof.Sm4.blockAt_getD _ _ hi, wordAddr, addr_add, addr_add, tailAt]
  rw [show 8 * tailSlot + 16 * c + i = 8 * (tailSlot + 2 * c + i / 8) + i % 8 by omega_arith]

/-- The tail buffer's blocks are `MK ⊕ FK`, from the key's 64-bit words `K h`. -/
theorem keyInit_rel {s : State} {key : Spec.Sm4.Block} {K : Nat → BitVec 64}
    (hK : ∀ h < 2, ∀ t < 8, ∀ j < 8, (K h).getLsbD (8 * t + j) = (key.getD (8 * h + t) 0).getLsbD j)
    (hT : ∀ c < 16, ∀ h < 2, slotW s (tailAt c h) = K h ^^^ fkWord h) :
    ∀ c < 16, ∀ w < 4, ofBlock (tailBlock s c) w = keyInit key w := by
  intro c hc w hw
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  obtain hi : 3 - k / 8 < 4 := by omega_arith
  rw [show k = 8 * (3 - (3 - k / 8)) + k % 8 by omega_arith, keyInit_bit key (w := w) hi (by omega_arith)]
  simp only [ofBlock]
  rw [getLsbD_wordAt _ _ hi (by omega_arith), tailBlock_bit s (c := c) (by omega_arith) (by omega_arith), hT c hc _ (by omega_arith),
    BitVec.getLsbD_xor, fkWord_bit (by omega_arith)]
  obtain e1 : 8 * ((4 * w + (3 - k / 8)) % 8) + k % 8 = 8 * (4 * (w % 2) + (3 - k / 8)) + k % 8 := by omega_arith
  rw [e1, hK _ (by omega_arith) _ (by omega_arith) _ (by omega_arith)]
  obtain h1 : 2 * ((4 * w + (3 - k / 8)) / 8) + (8 * (4 * (w % 2) + (3 - k / 8)) + k % 8) / 32 = w := by omega_arith
  obtain h2 : 8 * (3 - (8 * (4 * (w % 2) + (3 - k / 8)) + k % 8) % 32 / 8) +
      (8 * (4 * (w % 2) + (3 - k / 8)) + k % 8) % 8 = 8 * (3 - (3 - k / 8)) + k % 8 := by omega_arith
  obtain h3 : 8 * ((4 * w + (3 - k / 8)) / 8) + (4 * (w % 2) + (3 - k / 8)) = 4 * w + (3 - k / 8) := by omega_arith
  rw [h1, h2, h3]

theorem ckEntries_mem {e j : Nat} (he : e < 32) (hj : j < 8) :
    (8 * e + j, planeOf (Spec.Sm4.ck e) j) ∈ ckEntries := by
  simp only [ckEntries, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨e, he, j, hj, rfl⟩

theorem ckEntries_lt : ∀ kv ∈ ckEntries, kv.1 < 256 := by decide +kernel

theorem ckEntries_nodup : (ckEntries.map (·.1)).Nodup := by
  -- The offsets are consecutive: a linear check, not the quadratic `Nodup` search.
  rw [show ckEntries.map (·.1) = List.range' 0 256 by decide +kernel]
  exact List.nodup_range'

theorem entryW_slot (s : State) (e j : Nat) : entryW s.mem (s.gpr sb) e j = slotW s (tableSlot + 8 * e + j) := by
  simp only [entryW, slotW, wordAddr]; rw [show 8 * (tableSlot + 8 * e + j) = 8 * tableSlot + 64 * e + 8 * j by omega_arith]

/-- The table of `CK`'s planes, through `a4`. -/
theorem ckTable_ok {s : State} {b : Addr} (hb : s.gpr sb = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hal : b.toNat % 8 = 0) :
    ∃ s', runBlock isa ckTable s = some s' ∧
      (∀ e < 32, ∀ j < 8, entryW s'.mem b e j = planeOf (Spec.Sm4.ck e) j) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ .a4 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b + BitVec.ofNat 64 (8 * tableSlot), 2048⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := slotAddr_ok s .a4 tableSlot
  rw [hb] at r₁
  obtain ⟨s', e', v', -, g', rd', wr', f'⟩ := ckStores_ok (A := b + BitVec.ofNat 64 (8 * tableSlot))
    (Spill.al8 hal (by decide)) ckEntries (s := s₁) r₁
    (fun k hk => ⟨_, by rw [wr₁]; exact hw, by
      rw [wordAddr, addr_add, tableSlot_eq]
      exact VG.Offset.contains_base b (by rw [slots_eq]; omega_arith) (by omega_arith)⟩)
    ckEntries_lt ckEntries_nodup
  refine ⟨s', by rw [ckTable, Interleave.runBlock_append, e₁, Option.bind_some]; exact e',
    fun e he j hj => ?_, fun r h0 h1 h4 => by rw [g' r h0 h1, o₁ r h4], by rw [rd', rd₁], by rw [wr', wr₁],
    by rw [← m₁]; exact f'⟩
  have := v' _ (ckEntries_mem he hj)
  rw [wordAddr, addr_add] at this
  rw [entryW, show 8 * tableSlot + 64 * e + 8 * j = 8 * tableSlot + 8 * (8 * e + j) by omega_arith]
  exact this

/-- The code before the loop. -/
def ekHead : List Instr :=
  [movR sb .a2] ++ saveRegs ++ setSlots (keyMasks ++ bsKs) ++ ckTable ++ loadHalf 0 ++
    loadHalf 1 ++ toBs ++ slotAddr .a4 tableEnd ++ slotAddr kr tableSlot

theorem ekHead_ok {s₀ : State} (hp : expandKeyRISCV64.pre s₀) :
    ∃ s, runBlock isa ekHead s₀ = some s ∧
      EkInv s₀ (s₀.gpr .a2) (s₀.gpr .a1) (Spec.Sm4.blockAt s₀.mem (s₀.gpr .a0)) 0 s := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB, hal⟩ := hp
  let b := s₀.gpr .a2
  let Kp := s₀.gpr .a0
  obtain hwB : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hfitB := fitB
  rw [slots_eq] at hfitB
  -- Saving and the masks.
  obtain ⟨s₃, e₃, hb₃, g₃, sv₃, v₃, f₃, rd₃, wr₃⟩ := prologue_ok (keyMasks ++ bsKs)
    (fun kv hkv => by have := masks_lt kv hkv; rw [tableSlot_eq]; omega_arith) (by decide) (b := b) rfl hwB hal
  -- The table of `CK`.
  obtain ⟨s₄, e₄, v₄, g₄, rd₄, wr₄, f₄⟩ := ckTable_ok hb₃ (by rw [wr₃]; exact hwB) hal
  obtain hb₄ : s₄.gpr sb = b := by rw [g₄ _ (by decide) (by decide) (by decide), hb₃]
  obtain notCk : ∀ k, k < tableSlot ∨ tableEnd ≤ k → k < slots → slotW s₄ k = slotW s₃ k := fun k hk hk' => by
    simp only [slotW, hb₄, hb₃]
    refine f₄.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [wordAddr]
    rw [tableSlot_eq, tableEnd_eq, slots_eq] at *
    exact VG.Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
  obtain f₀₄ : Frame [⟨b, 8 * slots⟩] s₀.mem s₄.mem :=
    f₃.trans (f₄.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base b (by rw [tableSlot_eq, slots_eq]; omega_arith)⟩)
  -- The key.
  obtain inK : ∀ h < 2, ∀ i < 2, InRegions (s₄.rd ++ s₄.wr) (Kp + BitVec.ofNat 64 (8 * h + 4 * i)) 4 :=
    fun h hh i hi => ⟨_, List.mem_append_left _ (by rw [rd₄, rd₃, hrd]; exact List.mem_singleton_self _),
      VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain hKw : ∀ (m : Mem), Frame [⟨b, 8 * slots⟩] s₀.mem m → ∀ h < 2,
      m.readW (Kp + BitVec.ofNat 64 (8 * h)) 64 = s₀.mem.readW (Kp + BitVec.ofNat 64 (8 * h)) 64 :=
    fun m hf h hh => hf.readW (r := ⟨Kp, 16⟩) (VG.Offset.contains_base _ (by omega_arith) (by omega_arith))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKB) (by decide)
  obtain ha0₄ : s₄.gpr .a0 = Kp := by
    rw [g₄ _ (by decide) (by decide) (by decide), g₃ _ (by decide) (by decide) (by decide)]
  obtain ⟨s₅, e₅, v₅, k₅, g₅, rd₅, wr₅, f₅⟩ := loadHalf_ok 0 (by decide) hb₄ (by rw [wr₄, wr₃]; exact hwB) hal
    (by rw [ha0₄]; exact inK 0 (by decide))
  obtain hb₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide), hb₄]
  obtain ha0₅ : s₅.gpr .a0 = Kp := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide), ha0₄]
  obtain ⟨s₆, e₆, v₆, k₆, g₆, rd₆, wr₆, f₆⟩ := loadHalf_ok 1 (by decide) hb₅
    (by rw [wr₅, wr₄, wr₃]; exact hwB) hal
    (by rw [rd₅, wr₅, ha0₅]; exact inK 1 (by decide))
  obtain hb₆ : s₆.gpr sb = b := by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), hb₅]
  obtain f₀₆ : Frame [⟨b, 8 * slots⟩] s₀.mem s₆.mem := (f₀₄.trans f₅).trans f₆
  obtain hk₆ : ∀ k < slots, (∀ c < 16, ∀ h < 2, k ≠ tailAt c h) → slotW s₆ k = slotW s₄ k := fun k hk hn => by
    rw [k₆ k hk (fun c hc => hn c hc 1 (by decide)), k₅ k hk (fun c hc => hn c hc 0 (by decide))]
  obtain notTail : ∀ k, tableSlot ≤ k ∨ k < tailSlot → ∀ c < 16, ∀ h < 2, k ≠ tailAt c h := fun k hk c hc h hh => by
    simp only [tailAt, tailSlot_eq, tableSlot_eq] at hk ⊢; omega_arith
  -- The table and the masks.
  obtain hkey₆ : KeyCtx s₆ Spec.Sm4.ck :=
    { scr := by rw [hb₆, wr₆, wr₅, wr₄, wr₃]; exact hwB
      fit := by rw [hb₆]; exact fitB
      al := by rw [hb₆]; exact hal
      keys := fun e he => (planeOf_rel (Spec.Sm4.ck e)).congr fun j hj => by
        rw [entryW_slot, hk₆ _ (by rw [tableSlot_eq, slots_eq]; omega_arith) (notTail _ (Or.inl (by omega_arith))),
          ← entryW_slot, hb₄, v₄ e he j hj] }
  obtain hm₆ : MasksOk s₆ := fun kv hkv => by
    have := mask_range hkv
    rw [hk₆ _ (by rw [slots_eq]; omega_arith) (notTail _ (Or.inr (by rw [tailSlot_eq]; omega_arith))),
      notCk _ (Or.inl (by rw [tableSlot_eq]; omega_arith)) (by rw [slots_eq]; omega_arith), v₃ kv hkv]
  -- The key, bitsliced.
  obtain ⟨s₇, e₇, c₇, kr₇, X₇⟩ := toBs_step hkey₆ (Ctx.refl hm₆)
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := slotAddr_ok s₇ .a4 tableEnd
  obtain ⟨s₉, e₉, r₉, o₉, m₉, rd₉, wr₉⟩ := slotAddr_ok s₈ kr tableSlot
  obtain hb₇ : s₇.gpr sb = b := by rw [c₇.base, hb₆]
  obtain hb₉ : s₉.gpr sb = b := by rw [o₉ _ (by decide), o₈ _ (by decide), hb₇]
  obtain mem₉ : s₉.mem = s₇.mem := by rw [m₉, m₈]
  obtain g₉ : ∀ r, r ∉ sboxWrites → r ≠ kr → r ≠ .a4 → s₉.gpr r = s₆.gpr r := fun r h1 h2 h3 => by
    rw [o₉ r h2, o₈ r h3, c₇.keep r h1 h2]
  obtain g₆' : ∀ r, r ∉ sboxWrites → r ≠ sb → r ≠ .a4 → s₆.gpr r = s₀.gpr r := fun r h1 h2 h3 => by
    obtain hsub : ∀ x ∈ ([t0, t1, t2, m 1] : List Reg), x ∈ sboxWrites := by decide
    obtain h' : r ∉ ([t0, t1, t2, m 1] : List Reg) := fun h => h1 (hsub r h)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h'
    rw [g₆ r h'.1 h'.2.1 h'.2.2.1 h'.2.2.2, g₅ r h'.1 h'.2.1 h'.2.2.1 h'.2.2.2, g₄ r h'.1 h'.2.1 h3,
      g₃ r h2 h'.1 h'.2.1]
  obtain hK : ∀ h < 2, ∀ t < 8, ∀ j < 8, (s₀.mem.readW (Kp + BitVec.ofNat 64 (8 * h)) 64).getLsbD (8 * t + j) =
      ((Spec.Sm4.blockAt s₀.mem Kp).getD (8 * h + t) 0).getLsbD j := fun h hh t ht j hj => by
    rw [readW64_bit _ _ ht hj, VG.Proof.Sm4.blockAt_getD _ _ (by omega_arith), addr_add]
  obtain hT : ∀ c < 16, ∀ h < 2, slotW s₆ (tailAt c h) = s₀.mem.readW (Kp + BitVec.ofNat 64 (8 * h)) 64 ^^^ fkWord h := by
    intro c hc h hh
    rcases (show h = 0 ∨ h = 1 by omega_arith) with rfl | rfl
    · rw [k₆ _ (by have := tailAt_lt hc (show 0 < 2 by decide); rw [tableSlot_eq] at this; rw [slots_eq]; omega_arith)
        (fun c' _ h' => by simp only [tailAt] at h'; omega_arith), v₅ c hc, ha0₄, hKw _ f₀₄ 0 (by decide)]
    · rw [v₆ c hc, ha0₅, hKw _ (f₀₄.trans f₅) 1 (by decide)]
  obtain hst : StRel s₉ (fun _ => quads .key Spec.Sm4.ck 0 (keyInit (Spec.Sm4.blockAt s₀.mem Kp))) := fun w hw =>
    ((X₇ w hw).congr fun j _ => by simp only [planes, slotW, mem₉, hb₉, hb₇]).congr_right fun c hc =>
      (keyInit_rel hK hT c hc w hw).symm
  refine ⟨s₉, ?_, ⟨hb₉, ?_, ?_, ?_, ?_, ?_, hst, fun i hi => by omega_arith, fun i hi => ?_, ?_,
    by rw [rd₉, rd₈, c₇.rd, rd₆, rd₅, rd₄, rd₃], by rw [wr₉, wr₈, c₇.wr, wr₆, wr₅, wr₄, wr₃]⟩⟩
  · rw [ekHead, Interleave.runBlock_append, Interleave.runBlock_append, Interleave.runBlock_append,
      Interleave.runBlock_append, Interleave.runBlock_append, Interleave.runBlock_append, e₃, Option.bind_some, e₄, Option.bind_some, e₅, Option.bind_some, e₆,
      Option.bind_some, e₇, Option.bind_some, e₈, Option.bind_some, e₉]
  · rw [g₉ _ (by decide) (by decide) (by decide), g₆' _ (by decide) (by decide) (by decide)]
    exact (BitVec.add_zero _).symm
  · rw [o₉ _ (by decide), r₈, hb₇]
  · rw [AtEntry, r₉, o₈ _ (by decide), hb₇]; simp; rfl
  · exact (hkey₆.of_ctx c₇) |> fun h => ⟨by rw [wr₉, wr₈, hb₉, ← hb₇]; exact h.scr, by rw [hb₉, ← hb₇]; exact h.fit,
      by rw [hb₉, ← hb₇]; exact h.al, fun e he => by rw [hb₉, ← hb₇, mem₉]; exact h.keys e he⟩
  · exact fun kv hkv => by simp only [slotW, mem₉, hb₉, ← hb₇]; exact c₇.masks kv hkv
  · have hk : savedSlot + i < slots := by rw [savedSlot_eq, slots_eq]; omega_arith
    obtain h7 : slotW s₇ (savedSlot + i) = slotW s₆ (savedSlot + i) := by
      simp only [slotW, hb₇, hb₆]
      refine c₇.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      rw [hb₆, wordAddr]
      exact VG.Offset.disjoint_base _ (by rw [tableSlot_eq, savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith)
    obtain h6 : slotW s₆ (savedSlot + i) = slotW s₃ (savedSlot + i) := by
      rw [hk₆ _ hk (notTail _ (Or.inl (by rw [tableSlot_eq, savedSlot_eq]; omega_arith))),
        notCk _ (Or.inr (by rw [tableEnd_eq, savedSlot_eq]; omega_arith)) hk]
    obtain h3 := sv₃ i hi
    show s₉.mem.readW (wordAddr b (savedSlot + i)) 64 = _
    rw [mem₉, ← h3]
    have := h7.trans h6
    simp only [slotW, hb₇, hb₃] at this
    exact this
  · rw [mem₉]
    refine (f₀₆.trans (c₇.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).sub
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self, fun _ h => h⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [hb₆]; exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega_arith)

/-! ## The loop and the whole function -/

theorem ekLoop_wp {s₀ s : State} {b S : Addr} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S)
    (hi : EkInv s₀ b S key 0 s) :
    WP isa (.loop (.block keyBody) (.nonzero t0)) s (EkInv s₀ b S key 8) := by
  refine WP.loop (M := isa) (fun n s => ∃ m, n = 8 - m ∧ m < 8 ∧ EkInv s₀ b S key m s)
    (fun n s hs => ?_) 8 s ⟨0, rfl, by omega_arith, hi⟩
  obtain ⟨m, rfl, hm, hi⟩ := hs
  obtain ⟨s', e', hi', z'⟩ := ekIter_ok hp hm hi
  refine WP.of_runBlock ⟨s', e', ?_⟩
  by_cases h8 : m + 1 = 8
  · exact .inl ⟨by rw [eval_nonzero, z', h8]; rfl, by rw [h8] at hi'; exact hi'⟩
  · exact .inr ⟨by rw [eval_nonzero, z']; simp [h8], 8 - (m + 1), by omega_arith, m + 1, rfl, by omega_arith, hi'⟩

theorem expandKey_wp {s₀ : State} (hp : expandKeyRISCV64.pre s₀) :
    WP isa expandKey s₀ fun s' => (∀ i < 12, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      expandKeyRISCV64.post s₀ s' := by
  obtain ⟨s₁, e₁, h₁⟩ := ekHead_ok hp
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB, hal⟩ := hp
  let b := s₀.gpr .a2
  let S := s₀.gpr .a1
  obtain hwB : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  obtain hwS : (⟨S, 128⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [S]
  obtain pre : EkPre s₀ b S := ⟨hwB, hwS, dSB, fitB, fitS, hal⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.seq (WP.mono (ekLoop_wp pre h₁) fun s₂ h₂ => ?_)⟩)
  obtain ⟨s₃, e₃, rg₃, -, m₃, -, -⟩ := restore_ok (by rw [h₂.wr]; exact hwB) h₂.base hal h₂.saved
  refine WP.of_runBlock ⟨s₃, e₃, rg₃, ?_⟩
  show Spec.Sm4.scheduleAt s₃.mem S = _
  rw [expandKey_eq]
  apply Vector.ext
  intro i hi
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [show k = 8 * (k / 8) + k % 8 by omega_arith, VG.Proof.Sm4.getLsbD_scheduleAt _ _ hi (by omega_arith) (by omega_arith),
    Vector.getElem_ofFn, m₃]
  exact h₂.sched i (by omega_arith) _ (by omega_arith) _ (by omega_arith)

end VG.Proof.Sm4.RISCV64

end

end

/-!
# SM4 key expansion on RISCV64 meets its contracts

`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time, by the taint analysis with the pointers and the stack pointer public.
`expandKey_framed` runs it with its working space on the stack, zeroed on
return, as `ecb_framed` does. As on PPC64LE
(`Proof/Sm4/PPC64LE/KeyVerified.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4.RISCV64
open VG.Proof.Sm4 (expandKeyRISCV64)

theorem expandKeyTaint_agree (s₁ s₂ : State) (_ : expandKeyRISCV64.pre s₁) (_ : expandKeyRISCV64.pre s₂)
    (hp : expandKeyRISCV64.pub s₁ s₂) : taint.Agree (Taint.ofRegs [.a0, .a1, .a2]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h1, h2, h3]

theorem expandKey_ct : ConstantTime isa expandKeyRISCV64.pre expandKeyRISCV64.pub expandKey :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) expandKeyTaint_agree (by taint_decide)

/-- The registers key expansion writes: all but `ra`. -/
def expandKeyWrites : List Reg :=
  [.t0, .t1, .t2, .s0, .s1, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9,
   .s10, .s11, .t3, .t4, .t5, .t6]

theorem expandKey_correct (s : State) (hs : expandKeyRISCV64.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyRISCV64.post s s' := by
  have hn : callFree expandKey = true := by lit_decide
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, hk⟩ := WP.keep expandKeyWrites (expandKey_wp hs) (by lit_decide) hn
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, hk.gpr (by decide)⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega_using [])
  · exact h₁ 1 (by omega_using [])
  · exact h₁ 2 (by omega_using [])
  · exact h₁ 3 (by omega_using [])
  · exact h₁ 4 (by omega_using [])
  · exact h₁ 5 (by omega_using [])
  · exact h₁ 6 (by omega_using [])
  · exact h₁ 7 (by omega_using [])
  · exact h₁ 8 (by omega_using [])
  · exact h₁ 9 (by omega_using [])
  · exact h₁ 10 (by omega_using [])
  · exact h₁ 11 (by omega_using [])

/-- A state satisfying the precondition. -/
def expandKeySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 8 * 396⟩]

theorem expandKey_verified :
    Verified target expandKey (Proof.Sm4.expandKeyScratchContract abi slots) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Sm4.expandKeyScratchContract, Proof.Sm4.expandKeyScratchSig, Proof.Sm4.expandKeyPost,
      expandKeyRISCV64, abi, argRegs, slots, savedSlot, tableEnd, tableSlot]
      [expandKeySat] using expandKeySat)

/-- A state satisfying the key schedule's precondition: the key at
`0x1000`, the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Sm4.expandKeyContract abi 3168).pre s := by
  implies_sat [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, abi, argRegs]
    [expandKeyFrameSat] using expandKeyFrameSat

/-- Key expansion, with its working space on the stack. -/
theorem expandKey_framed :
    Verified target (Impl.StackScratch.RISCV64.withStackScratchWiped 3168 .a2 396 expandKey)
      (Spec.Sm4.expandKeyContract abi 3168) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Sm4.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 396) (post := Proof.Sm4.expandKeyPost abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 3168) (words := 396) expandKey_verified (by decide) (by decide) (by decide)
    (Proof.Sm4.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Sm4.RISCV64
