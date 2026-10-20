module
public import VerifiedGarbage.Proof.Camellia.Arm.KeyPair
public import VerifiedGarbage.Proof.Camellia.Arm.Prologue

import VerifiedGarbage.Proof.Framework.Arm.Bytes
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Camellia.Arm.Fl
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Camellia's key schedule on ARMv7: the subkeys' stores

`revs_ok`: the values' words byte-swapped in place, which makes them the
32-bit words of the 128-bit values, the most significant first (`NumOf`,
`num_of_rev`). `rotWord_ok`: a word of a value rotated left, from two of its
words. `storeSubkeys_ok`: each subkey, the high or low half of a rotated
value, byte-swapped and stored, so that its bytes are those of
`rotHalf` (as `schedule_of_stores` takes them).
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS eorR lsrOp)
open VG.Proof.Camellia (byteOf getLsbD_byteOf hiW loW rotHalf hi_split lo_split hiW_append loW_append)

/-! ## Words of 128-bit values -/

/-- Word `j` (0–3, the most significant first) of `x`. -/
def numWord (x : BitVec 128) (j : Nat) : BitVec 32 := (x >>> (96 - 32 * j)).setWidth 32

theorem numWord_bit (x : BitVec 128) {j p : Nat} (_hj : j < 4) (hp : p < 32) :
    (numWord x j).getLsbD p = x.getLsbD (96 - 32 * j + p) := by
  simp only [numWord, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hp, decide_true, Bool.true_and]

theorem rotl_bit (x : BitVec 128) {r k : Nat} (hr : r < 128) (hk : k < 128) :
    (x.rotateLeft r).getLsbD k = x.getLsbD ((k + 128 - r) % 128) := by
  rw [BitVec.getLsbD_rotateLeft]
  simp only [show r % 128 = r by omega]
  split
  · congr 1; omega
  · rw [decide_eq_true hk, Bool.true_and]; congr 1; omega

/-- The four words at slot `a` are those of `x`. -/
def NumOf (s : State) (a : Nat) (x : BitVec 128) : Prop := ∀ j < 4, slotW s (a + j) = numWord x j

theorem NumOf.congr {s s' : State} {a : Nat} {x : BitVec 128} (h : NumOf s a x)
    (hs : ∀ j < 4, slotW s' (a + j) = slotW s (a + j)) : NumOf s' a x := fun j hj => by
  rw [hs j hj]; exact h j hj

/-- Byte-swapping the words of a value gives the words of its number. -/
theorem num_of_rev {s s' : State} {a : Nat} {v : BitVec 64 × BitVec 64} (hv : VW s a v)
    (h : ∀ j < 4, slotW s' (a + j) = rev (slotW s (a + j))) : NumOf s' a (v.1 ++ v.2) := by
  intro j hj
  rw [h j hj]
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  obtain ⟨k, t, hk, ht, rfl⟩ : ∃ k t, k < 4 ∧ t < 8 ∧ p = 8 * k + t := ⟨p / 8, p % 8, by omega, by omega, by omega⟩
  rw [rev_bit _ hk ht, numWord_bit _ hj hp]
  have := hv (4 * j + (3 - k)) (by omega) t ht
  rw [show (4 * j + (3 - k)) / 4 = j by omega, show (4 * j + (3 - k)) % 4 = 3 - k by omega] at this
  rw [this, BitVec.getLsbD_append]
  by_cases h8 : 4 * j + (3 - k) < 8
  · rw [itePos h8, getLsbD_byteOf _ (by omega) ht, iteNeg (show ¬ 96 - 32 * j + (8 * k + t) < 64 by omega)]
    congr 1; omega
  · rw [iteNeg h8, getLsbD_byteOf _ (by omega) ht, itePos (show 96 - 32 * j + (8 * k + t) < 64 by omega)]
    congr 1; omega

/-! ## Byte swaps in place -/

/-- `ldr t0, [sb, #4 k]; rev t0, t0; str t0, [sb, #4 k]` for each `k` of `L`. -/
theorem revs_ok {b : BitVec 32} : ∀ (L : List Nat) {s : State}, s.gpr sb = b → ScrIn s.wr b → L.Nodup →
    (∀ k ∈ L, k < slots) →
    ∃ s', runBlock isa (L.flatMap fun k => [ldS t0 k, .rev t0 t0, stS k t0]) s = some s' ∧
      (∀ k ∈ L, s'.mem.readW (wordAddr b k) 32 = rev (s.mem.readW (wordAddr b k) 32)) ∧
      (∀ k < slots, k ∉ L → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem
  | [], s, _, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | x :: L, s, hb, hw, hnd, hin => by
    have hx := hin x List.mem_cons_self
    have hfit := hw.fit
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s t0 sb (k := x) hb hx hw
    let s₂ := s₁.setReg t0 (rev (s₁.gpr t0))
    obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, sp₃, -, f₃⟩ := stSlot_ok s₂ t0 sb (k := x)
      (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), o₁ _ (by decide), hb]) hx
      (by rw [RegUpd.wr_setReg, wr₁]; exact hw)
    rw [List.nodup_cons] at hnd
    obtain ⟨s', e', v', k', g', rd', wr', sp', f'⟩ := revs_ok L (s := s₃)
      (by rw [g₃, RegUpd.gpr_setReg_of_ne _ _ (by decide), o₁ _ (by decide), hb])
      (by rw [wr₃, RegUpd.wr_setReg, wr₁]; exact hw) hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    have hslot : ∀ j < slots, s₃.mem.readW (wordAddr b j) 32 = if j = x then
        rev (s.mem.readW (wordAddr b x) 32) else s.mem.readW (wordAddr b j) 32 := fun j hj => by
      rw [m₃, readW_slot_write hfit _ hj hx, RegUpd.gpr_setReg_self, v₁, RegUpd.mem_setReg, m₁]
    refine ⟨s', ?_, fun y hy => ?_, fun j hj hn => ?_, fun r hr => by
        rw [g' r hr, g₃, RegUpd.gpr_setReg_of_ne _ _ hr, o₁ r hr],
      by rw [rd', rd₃, RegUpd.rd_setReg, rd₁], by rw [wr', wr₃, RegUpd.wr_setReg, wr₁],
      by rw [sp', sp₃, RegUpd.sp_setReg, sp₁], ?_⟩
    · rw [List.flatMap_cons, runBlock_app, show ([ldS t0 x, .rev t0 t0, stS x t0] : List Instr) =
        [.ldr t0 sb (4 * x)] ++ ([.rev t0 t0] ++ [.str t0 sb (4 * x)]) from rfl, runBlock_app, e₁,
        Option.bind_some, runBlock_app, runBlock_cons, show exec (.rev t0 t0) s₁ = some s₂ from rfl, runStep_some,
        runBlock_nil, Option.bind_some, e₃, Option.bind_some]
      exact e'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rw [k' _ hx hnd.1, hslot _ hx, ite_eq_left rfl]
      · rw [v' y hy', hslot _ (hin y (List.mem_cons_of_mem _ hy')), ite_eq_right (fun h => hnd.1 (by rw [← h]; exact hy'))]
    · simp only [List.mem_cons, not_or] at hn
      rw [k' j hj hn.2, hslot j hj, ite_eq_right hn.1]
    · rw [RegUpd.mem_setReg, m₁] at f₃
      exact (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit hx⟩).trans f'

theorem valSlot_lt (v : Nat) (hv : v < 4) : valSlot v + 4 ≤ slots := by
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

/-- The values' slots. -/
def revSlots : List Nat := [0, 1, 2, 3].flatMap fun v => (List.range 4).map (valSlot v + ·)

theorem revValues_eq : revValues = revSlots.flatMap fun k => [ldS t0 k, .rev t0 t0, stS k t0] := rfl

theorem revSlots_facts : revSlots.Nodup ∧ (∀ k ∈ revSlots, k < slots) := by
  constructor <;> decide

theorem mem_revSlots {v k : Nat} (hv : v < 4) (hk : k < 4) : valSlot v + k ∈ revSlots := by
  simp only [revSlots, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨v, by omega, k, hk, rfl⟩

/-! ## Rotations -/

/-- Word `o` of value `v` rotated left by `r`, in `t0`. -/
theorem rotWord_ok {s : State} {b : BitVec 32} (hb : s.gpr sb = b) (hw : ScrIn s.wr b) {v r o : Nat}
    (hv : v < 4) (hr : r < 128) (ho : o < 4) {x : BitVec 128} (hx : NumOf s (valSlot v) x) :
    ∃ s', runBlock isa (rotWord v r o) s = some s' ∧ s'.gpr t0 = numWord (x.rotateLeft r) o ∧
      (∀ r', r' ≠ t0 → r' ≠ t1 → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  have hvs : valSlot v + 4 ≤ slots := valSlot_lt v hv
  have hW : ∀ j < 4, s.mem.readW (wordAddr b (valSlot v + j)) 32 = numWord x j := fun j hj => by
    rw [← hb]; exact hx j hj
  unfold rotWord
  dsimp only
  split
  · rename_i h0
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s t0 sb (k := valSlot v + (o + r / 32) % 4) hb
      (by omega) hw
    refine ⟨s₁, e₁, ?_, fun r' h1 _ => o₁ r' h1, m₁, rd₁, wr₁, sp₁⟩
    rw [v₁, hW _ (by omega)]
    apply BitVec.eq_of_getLsbD_eq; intro p hp
    rw [numWord_bit _ (by omega) hp, numWord_bit _ ho hp, rotl_bit _ hr (by omega)]
    congr 1; omega
  · rename_i h0
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s t0 sb (k := valSlot v + (o + r / 32) % 4) hb
      (by omega) hw
    obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := ldSlot_ok s₁ t1 sb (k := valSlot v + (o + r / 32 + 1) % 4)
      (by rw [o₁ _ (by decide), hb]) (by omega) (by rw [wr₁]; exact hw)
    let s₃ := s₂.setReg t0 (s₂.gpr t0 <<< (r % 32))
    let s₄ := s₃.setReg t0 (s₃.gpr t0 ||| s₃.gpr t1 >>> (32 - r % 32))
    have hs1 : 1 ≤ r % 32 ∧ r % 32 ≤ 31 := by omega
    have hs2 : 1 ≤ 32 - r % 32 ∧ 32 - r % 32 ≤ 31 := by omega
    refine ⟨s₄, ?_, ?_, fun r' h1 h2 => by
        rw [RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_setReg_of_ne _ _ h1, o₂ r' h2, o₁ r' h1],
      by rw [show s₄.mem = s₂.mem from rfl, m₂, m₁], by rw [show s₄.rd = s₂.rd from rfl, rd₂, rd₁],
      by rw [show s₄.wr = s₂.wr from rfl, wr₂, wr₁], by rw [show s₄.sp = s₂.sp from rfl, sp₂, sp₁]⟩
    · rw [show ([ldS t0 (valSlot v + (o + r / 32) % 4), ldS t1 (valSlot v + (o + r / 32 + 1) % 4),
          .mov t0 (.shifted t0 .lsl (r % 32)), .dp .orr t0 t0 (lsrOp t1 (32 - r % 32))] : List Instr) =
          [.ldr t0 sb (4 * (valSlot v + (o + r / 32) % 4))] ++ ([.ldr t1 sb (4 * (valSlot v + (o + r / 32 + 1) % 4))] ++
            [.mov t0 (.shifted t0 .lsl (r % 32)), .dp .orr t0 t0 (lsrOp t1 (32 - r % 32))]) from rfl,
        runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_cons,
        show exec (.mov t0 (.shifted t0 .lsl (r % 32))) s₂ = some s₃ by simp [exec, Op2.eval, hs1, s₃],
        runStep_some, runBlock_cons, show exec (.dp .orr t0 t0 (lsrOp t1 (32 - r % 32))) s₃ = some s₄ by
          simp [exec, Op2.eval, lsrOp, hs2, s₄], runStep_some, runBlock_nil]
    · rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (by decide),
        o₂ _ (by decide), v₁, v₂, m₁, hW _ (by omega), hW _ (by omega)]
      apply BitVec.eq_of_getLsbD_eq; intro p hp
      rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, numWord_bit _ ho hp,
        rotl_bit _ hr (by omega)]
      by_cases hps : p < r % 32
      · have hlt : 32 - r % 32 + p < 32 := by omega
        simp only [hp, decide_true, Bool.true_and, hps, Bool.not_true, Bool.false_and, Bool.false_or]
        rw [numWord_bit _ (by omega) hlt]
        congr 1; omega
      · rw [BitVec.getLsbD_of_ge (numWord x ((o + r / 32 + 1) % 4)) (32 - r % 32 + p) (by omega)]
        simp only [hp, decide_true, Bool.true_and, hps, decide_false, Bool.not_false, Bool.or_false]
        rw [numWord_bit _ (by omega) (by omega)]
        congr 1; omega

/-! ## Stores -/

/-- The schedule at `S`, writable, apart from the scratch buffer at `b`. -/
structure SchedOut (s : State) (b S : BitVec 32) : Prop where
  r2 : s.gpr .r2 = S
  wr : (⟨State.addr S, 272⟩ : Region) ∈ s.wr
  fit : S.toNat + 272 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr S, 272⟩ ⟨State.addr b, 4 * slots⟩

theorem SchedOut.congr {s s' : State} {b S : BitVec 32} (h : SchedOut s b S) (h2 : s'.gpr .r2 = s.gpr .r2)
    (hwr : s'.wr = s.wr) : SchedOut s' b S := ⟨h2.trans h.r2, hwr ▸ h.wr, h.fit, h.sep⟩

/-- A slot, kept by a frame of the schedule. -/
theorem SchedOut.slot {s : State} {b S : BitVec 32} (h : SchedOut s b S) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {m m' : Mem} {R : Region} (hf : Frame [R] m m') (hR : Region.Sub R ⟨State.addr S, 272⟩) {k : Nat}
    (hk : k < slots) : m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((h.sep.sub_left hR).symm.sub_left (slot_sub hfit hk)) ) (by decide)

/-- Word `o` of value `v` rotated left by `r`, byte-swapped and stored at `S + off`. -/
theorem wordStore_ok {s : State} {b S : BitVec 32} (hb : s.gpr sb = b) (hw : ScrIn s.wr b) (hS : SchedOut s b S)
    {v r o off : Nat} (hv : v < 4) (hr : r < 128) (ho : o < 4) (hoff : off + 4 ≤ 272) {x : BitVec 128}
    (hx : NumOf s (valSlot v) x) :
    ∃ s', runBlock isa (rotWord v r o ++ ([.rev t0 t0, .str t0 .r2 off] : List Instr)) s = some s' ∧
      s'.mem = s.mem.writeW (State.addr S + BitVec.ofNat 64 off) (rev (numWord (x.rotateLeft r) o)) ∧
      (∀ r', r' ≠ t0 → r' ≠ t1 → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := rotWord_ok hb hw hv hr ho hx
  let s₂ := s₁.setReg t0 (rev (s₁.gpr t0))
  have ea : State.addr (s₂.gpr .r2 + BitVec.ofNat 32 off) = State.addr S + BitVec.ofNat 64 off := by
    rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), o₁ _ (by decide) (by decide), hS.r2,
      VG.Arm.addr_add (by have := hS.fit; omega)]
  have hin : InRegions s₂.wr (State.addr (s₂.gpr .r2 + BitVec.ofNat 32 off)) 4 := by
    rw [ea]
    exact ⟨_, by rw [RegUpd.wr_setReg, wr₁]; exact hS.wr,
      VG.Offset.contains_base _ (by omega) (by have := hS.fit; omega)⟩
  refine ⟨{ s₂ with mem := s₂.mem.writeW (State.addr (s₂.gpr .r2 + BitVec.ofNat 32 off)) (s₂.gpr t0) }, ?_, ?_,
    fun r' h1 h2 => by
      show (s₁.setReg t0 _).gpr r' = _
      rw [RegUpd.gpr_setReg_of_ne _ _ h1, o₁ r' h1 h2], by rw [← rd₁]; rfl, by rw [← wr₁]; rfl, by rw [← sp₁]; rfl⟩
  · rw [runBlock_app, e₁, Option.bind_some, runBlock_cons, show exec (.rev t0 t0) s₁ = some s₂ from rfl,
      runStep_some, runBlock_cons, exec_str (by omega) hin, runStep_some, runBlock_nil]
  · show s₂.mem.writeW _ _ = _
    rw [ea, RegUpd.gpr_setReg_self, v₁, RegUpd.mem_setReg, m₁]

/-- The bytes of a stored word: the half's bytes `4 k … 4 k + 3`. -/
theorem stored_byte (x : BitVec 128) (r : Nat) (hi : Bool) {k q : Nat} (hk : k < 2) (hq : q < 4) :
    (rev (numWord (x.rotateLeft r) ((if hi then 0 else 2) + k))).extractLsb' (8 * q) 8 =
      byteOf (if hi then Spec.Camellia.hi x r else Spec.Camellia.lo x r) (4 * k + q) := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [BitVec.getLsbD_extractLsb', getLsbD_byteOf _ (by omega) ht, rev_bit _ hq ht,
    numWord_bit _ (by split <;> omega) (by omega)]
  simp only [ht, decide_true, Bool.true_and]
  cases hi
  · simp only [Bool.false_eq_true, ↓reduceIte, Spec.Camellia.lo, BitVec.getLsbD_setWidth,
      show 56 - 8 * (4 * k + q) + t < 64 by omega, decide_true, Bool.true_and]
    congr 1; omega
  · simp only [↓reduceIte, Spec.Camellia.hi, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      show 56 - 8 * (4 * k + q) + t < 64 by omega, decide_true, Bool.true_and]
    congr 1; omega

/-- A subkey: the high or low half of value `v` rotated left by `r`, stored at `S + 8 i`. -/
theorem subkey_ok {s : State} {b S : BitVec 32} (hb : s.gpr sb = b) (hw : ScrIn s.wr b) (hS : SchedOut s b S)
    {i v r : Nat} {hi : Bool} (hv : v < 4) (hr : r < 128) (hi8 : 8 * i + 8 ≤ 272) {x : BitVec 128}
    (hx : NumOf s (valSlot v) x) :
    ∃ s', runBlock isa (subkey i v r hi) s = some s' ∧
      (∀ j < 8, s'.mem (State.addr S + BitVec.ofNat 64 (8 * i + j)) =
        byteOf (if hi then Spec.Camellia.hi x r else Spec.Camellia.lo x r) j) ∧
      Frame [⟨State.addr S + BitVec.ofNat 64 (8 * i), 8⟩] s.mem s'.mem ∧
      (∀ r', r' ≠ t0 → r' ≠ t1 → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hfit := hw.fit
  have hSf := hS.fit
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, sp₁⟩ := wordStore_ok hb hw hS hv hr (o := (if hi then 0 else 2) + 0)
    (off := 8 * i + 4 * 0) (by split <;> omega) (by omega) hx
  have sub0 : Region.Sub ⟨State.addr S + BitVec.ofNat 64 (8 * i + 4 * 0), 4⟩ ⟨State.addr S, 272⟩ :=
    VG.Offset.sub_base _ (by omega)
  have hx₁ : NumOf s₁ (valSlot v) x := hx.congr fun j hj => by
    simp only [slotW]
    rw [g₁ _ (by decide) (by decide), hb, m₁]
    have hj' : valSlot v + j < slots := by have := valSlot_lt v hv; omega
    exact hS.slot hfit ((Frame.refl _ s.mem).writeW (r := ⟨State.addr S + BitVec.ofNat 64 (8 * i + 4 * 0), 4⟩)
      (List.mem_singleton_self _) (rev (numWord (x.rotateLeft r) ((if hi then 0 else 2) + 0)))
      (Region.contains_self _ _)) sub0 hj'
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, sp₂⟩ := wordStore_ok (by rw [g₁ _ (by decide) (by decide), hb])
    ⟨by rw [wr₁]; exact hw.mem, hfit⟩ (hS.congr (g₁ _ (by decide) (by decide)) wr₁) hv hr
    (o := (if hi then 0 else 2) + 1) (off := 8 * i + 4 * 1) (by split <;> omega) (by omega) hx₁
  refine ⟨s₂, ?_, fun j hj => ?_, ?_, fun r' h1 h2 => by rw [g₂ r' h1 h2, g₁ r' h1 h2],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁]⟩
  · rw [subkey, show ([0, 1] : List Nat).flatMap (fun k => rotWord v r ((if hi then 0 else 2) + k) ++
        [.rev t0 t0, .str t0 .r2 (8 * i + 4 * k)]) =
        (rotWord v r ((if hi then 0 else 2) + 0) ++ [.rev t0 t0, .str t0 .r2 (8 * i + 4 * 0)]) ++
        (rotWord v r ((if hi then 0 else 2) + 1) ++ [.rev t0 t0, .str t0 .r2 (8 * i + 4 * 1)]) by simp,
      runBlock_app, e₁, Option.bind_some, e₂]
  · rw [m₂]
    by_cases h4 : j < 4
    · rw [writeW32_other _ (VG.Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)), m₁]
      have h0 := st_byte s.mem (State.addr S + BitVec.ofNat 64 (8 * i + 4 * 0))
        (rev (numWord (x.rotateLeft r) ((if hi then 0 else 2) + 0))) h4
      rw [VG.Offset.add_add, show 8 * i + 4 * 0 + j = 8 * i + j by omega] at h0
      rw [h0, stored_byte x r hi (k := 0) (q := j) (by decide) h4, show 4 * 0 + j = j by omega]
    · have h1 := st_byte s₁.mem (State.addr S + BitVec.ofNat 64 (8 * i + 4 * 1))
        (rev (numWord (x.rotateLeft r) ((if hi then 0 else 2) + 1))) (t := j - 4) (by omega)
      rw [VG.Offset.add_add, show 8 * i + 4 * 1 + (j - 4) = 8 * i + j by omega] at h1
      rw [h1, stored_byte x r hi (k := 1) (q := j - 4) (by decide) (by omega), show 4 * 1 + (j - 4) = j by omega]
  · rw [m₂, m₁]
    refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)).sub
      fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)).sub
      fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩) <;>
      (simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub _ (by omega) (by omega))

/-- The half a subkey stores. -/
def subHalf (X : Nat → BitVec 128) (k : Nat × Nat × Bool) : BitVec 64 :=
  if k.2.2 then Spec.Camellia.hi (X k.1) k.2.1 else Spec.Camellia.lo (X k.1) k.2.1

/-- The subkeys `ks`, from entry `n` of the schedule. -/
theorem stores_ok {b S : BitVec 32} {X : Nat → BitVec 128} : ∀ (ks : List (Nat × Nat × Bool)) (n : Nat) (s : State),
    s.gpr sb = b → ScrIn s.wr b → SchedOut s b S → (∀ k ∈ ks, k.1 < 4 ∧ k.2.1 < 128) →
    8 * (n + ks.length) ≤ 272 → (∀ v < 4, NumOf s (valSlot v) (X v)) →
    ∃ s', runBlock isa ((ks.zipIdx n).flatMap fun ((v, r, hi), i) => subkey i v r hi) s = some s' ∧
      (∀ i < ks.length, ∀ j < 8, s'.mem (State.addr S + BitVec.ofNat 64 (8 * (n + i) + j)) =
        byteOf (subHalf X (ks.getD i (0, 0, true))) j) ∧
      Frame [⟨State.addr S + BitVec.ofNat 64 (8 * n), 8 * ks.length⟩] s.mem s'.mem ∧
      (∀ r', r' ≠ t0 → r' ≠ t1 → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp
  | [], _, s, _, _, _, _, _, _ => ⟨s, rfl, fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _,
      fun _ _ _ => rfl, rfl, rfl, rfl⟩
  | (v, r, hi) :: ks, n, s, hb, hw, hS, hks, hlen, hX => by
    have hfit := hw.fit
    have hSf := hS.fit
    simp only [List.length_cons] at hlen
    obtain ⟨hv, hr⟩ := hks _ List.mem_cons_self
    obtain ⟨s₁, e₁, b₁, f₁, g₁, rd₁, wr₁, sp₁⟩ := subkey_ok (i := n) (hi := hi) hb hw hS hv hr (by omega) (hX v hv)
    have hsub : Region.Sub ⟨State.addr S + BitVec.ofNat 64 (8 * n), 8⟩ ⟨State.addr S, 272⟩ :=
      VG.Offset.sub_base _ (by omega)
    have hX₁ : ∀ u < 4, NumOf s₁ (valSlot u) (X u) := fun u hu => (hX u hu).congr fun j hj => by
      simp only [slotW]
      rw [g₁ _ (by decide) (by decide), hb]
      exact hS.slot hfit f₁ hsub (by have := valSlot_lt u hu; omega)
    have hb₁ : s₁.gpr sb = b := by rw [g₁ _ (by decide) (by decide), hb]
    obtain ⟨s', e', b', f', g', rd', wr', sp'⟩ := stores_ok ks (n + 1) s₁ hb₁ ⟨by rw [wr₁]; exact hw.mem, hfit⟩
      (hS.congr (g₁ _ (by decide) (by decide)) wr₁) (fun k hk => hks k (List.mem_cons_of_mem _ hk))
      (by omega) hX₁
    refine ⟨s', ?_, fun i hi j hj => ?_, ?_, fun r' h1 h2 => by rw [g' r' h1 h2, g₁ r' h1 h2],
      by rw [rd', rd₁], by rw [wr', wr₁], by rw [sp', sp₁]⟩
    · rw [List.zipIdx_cons, List.flatMap_cons, runBlock_app, e₁, Option.bind_some]
      exact e'
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [f' _ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          intro hc
          rcases Nat.eq_zero_or_pos ks.length with h0 | hpos
          · simp only [Region.Contains, h0, Nat.mul_zero] at hc; omega
          · exact VG.Proof.Camellia.not_contains_off _ (.inl (by omega)) (by omega) (by omega) (by omega) hc),
          Nat.add_zero, b₁ j hj]
        simp only [subHalf, List.getD_cons_zero]
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        have := b' i' (by simp only [List.length_cons] at hi; omega) j hj
        rw [show n + 1 + i' = n + (i' + 1) by omega] at this
        rw [this, List.getD_cons_succ]
    · refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (f'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩) <;>
        (simp only [List.mem_singleton] at hr; subst hr; simp only [List.length_cons]
         exact VG.Offset.sub _ (by omega) (by omega))

end VG.Proof.Camellia.Arm
