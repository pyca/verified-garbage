module

public import VerifiedGarbage.Proof.Camellia.Arm.KeyPair
public import VerifiedGarbage.Proof.Camellia.Arm.Prologue
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Camellia.Arm.Fl
public import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Camellia.Arm.Copy
import VerifiedGarbage.Proof.Camellia.Layout32
public import VerifiedGarbage.Impl.Camellia.Arm.ExpandKey
public import VerifiedGarbage.Proof.Camellia.Arm.Core
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Camellia.Planes32
import VerifiedGarbage.Proof.Camellia.Arm.Crypt8

/-! ### `Camellia.Arm.KeyStore`, which only this module used -/

section

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
  simp only [show r % 128 = r by omega_arith]
  split
  · congr 1; omega_arith
  · rw [decide_eq_true hk, Bool.true_and]; congr 1; omega_arith

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
  obtain ⟨k, t, hk, ht, rfl⟩ : ∃ k t, k < 4 ∧ t < 8 ∧ p = 8 * k + t := ⟨p / 8, p % 8, by omega_arith, by omega_arith, by omega_arith⟩
  rw [rev_bit _ hk ht, numWord_bit _ hj hp]
  have := hv (4 * j + (3 - k)) (by omega_arith) t ht
  rw [show (4 * j + (3 - k)) / 4 = j by omega_arith, show (4 * j + (3 - k)) % 4 = 3 - k by omega_arith] at this
  rw [this, BitVec.getLsbD_append]
  by_cases h8 : 4 * j + (3 - k) < 8
  · rw [itePos h8, getLsbD_byteOf _ (by omega_arith) ht, iteNeg (show ¬ 96 - 32 * j + (8 * k + t) < 64 by omega_arith)]
    congr 1; omega_arith
  · rw [iteNeg h8, getLsbD_byteOf _ (by omega_arith) ht, itePos (show 96 - 32 * j + (8 * k + t) < 64 by omega_arith)]
    congr 1; omega_arith

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
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> decide

/-- The values' slots. -/
def revSlots : List Nat := [0, 1, 2, 3].flatMap fun v => (List.range 4).map (valSlot v + ·)

theorem revValues_eq : revValues = revSlots.flatMap fun k => [ldS t0 k, .rev t0 t0, stS k t0] := rfl

theorem revSlots_facts : revSlots.Nodup ∧ (∀ k ∈ revSlots, k < slots) := by
  constructor <;> decide

theorem mem_revSlots {v k : Nat} (hv : v < 4) (hk : k < 4) : valSlot v + k ∈ revSlots := by
  simp only [revSlots, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨v, by omega_arith, k, hk, rfl⟩

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
      (by omega_arith) hw
    refine ⟨s₁, e₁, ?_, fun r' h1 _ => o₁ r' h1, m₁, rd₁, wr₁, sp₁⟩
    rw [v₁, hW _ (by omega_arith)]
    apply BitVec.eq_of_getLsbD_eq; intro p hp
    rw [numWord_bit _ (by omega_arith) hp, numWord_bit _ ho hp, rotl_bit _ hr (by omega_arith)]
    congr 1; omega_arith
  · rename_i h0
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s t0 sb (k := valSlot v + (o + r / 32) % 4) hb
      (by omega_arith) hw
    obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := ldSlot_ok s₁ t1 sb (k := valSlot v + (o + r / 32 + 1) % 4)
      (by rw [o₁ _ (by decide), hb]) (by omega_arith) (by rw [wr₁]; exact hw)
    let s₃ := s₂.setReg t0 (s₂.gpr t0 <<< (r % 32))
    let s₄ := s₃.setReg t0 (s₃.gpr t0 ||| s₃.gpr t1 >>> (32 - r % 32))
    have hs1 : 1 ≤ r % 32 ∧ r % 32 ≤ 31 := by omega_arith
    have hs2 : 1 ≤ 32 - r % 32 ∧ 32 - r % 32 ≤ 31 := by omega_arith
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
        o₂ _ (by decide), v₁, v₂, m₁, hW _ (by omega_arith), hW _ (by omega_arith)]
      apply BitVec.eq_of_getLsbD_eq; intro p hp
      rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, numWord_bit _ ho hp,
        rotl_bit _ hr (by omega_arith)]
      by_cases hps : p < r % 32
      · have hlt : 32 - r % 32 + p < 32 := by omega_arith
        simp only [hp, decide_true, Bool.true_and, hps, Bool.not_true, Bool.false_and, Bool.false_or]
        rw [numWord_bit _ (by omega_arith) hlt]
        congr 1; omega_arith
      · rw [BitVec.getLsbD_of_ge (numWord x ((o + r / 32 + 1) % 4)) (32 - r % 32 + p) (by omega_arith)]
        simp only [hp, decide_true, Bool.true_and, hps, decide_false, Bool.not_false, Bool.or_false]
        rw [numWord_bit _ (by omega_arith) (by omega_arith)]
        congr 1; omega_arith

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
      VG.Arm.addr_add (by have := hS.fit; omega_arith)]
  have hin : InRegions s₂.wr (State.addr (s₂.gpr .r2 + BitVec.ofNat 32 off)) 4 := by
    rw [ea]
    exact ⟨_, by rw [RegUpd.wr_setReg, wr₁]; exact hS.wr,
      VG.Offset.contains_base _ (by omega_arith) (by have := hS.fit; omega_arith)⟩
  refine ⟨{ s₂ with mem := s₂.mem.writeW (State.addr (s₂.gpr .r2 + BitVec.ofNat 32 off)) (s₂.gpr t0) }, ?_, ?_,
    fun r' h1 h2 => by
      show (s₁.setReg t0 _).gpr r' = _
      rw [RegUpd.gpr_setReg_of_ne _ _ h1, o₁ r' h1 h2], by rw [← rd₁]; rfl, by rw [← wr₁]; rfl, by rw [← sp₁]; rfl⟩
  · rw [runBlock_app, e₁, Option.bind_some, runBlock_cons, show exec (.rev t0 t0) s₁ = some s₂ from rfl,
      runStep_some, runBlock_cons, exec_str (by omega_arith) hin, runStep_some, runBlock_nil]
  · show s₂.mem.writeW _ _ = _
    rw [ea, RegUpd.gpr_setReg_self, v₁, RegUpd.mem_setReg, m₁]

/-- The bytes of a stored word: the half's bytes `4 k … 4 k + 3`. -/
theorem stored_byte (x : BitVec 128) (r : Nat) (hi : Bool) {k q : Nat} (hk : k < 2) (hq : q < 4) :
    (rev (numWord (x.rotateLeft r) ((if hi then 0 else 2) + k))).extractLsb' (8 * q) 8 =
      byteOf (if hi then Spec.Camellia.hi x r else Spec.Camellia.lo x r) (4 * k + q) := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [BitVec.getLsbD_extractLsb', getLsbD_byteOf _ (by omega_arith) ht, rev_bit _ hq ht,
    numWord_bit _ (by split <;> omega_arith) (by omega_arith)]
  simp only [ht, decide_true, Bool.true_and]
  cases hi
  · simp only [Bool.false_eq_true, ↓reduceIte, Spec.Camellia.lo, BitVec.getLsbD_setWidth,
      show 56 - 8 * (4 * k + q) + t < 64 by omega_arith, decide_true, Bool.true_and]
    congr 1; omega_arith
  · simp only [↓reduceIte, Spec.Camellia.hi, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      show 56 - 8 * (4 * k + q) + t < 64 by omega_arith, decide_true, Bool.true_and]
    congr 1; omega_arith

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
    (off := 8 * i + 4 * 0) (by split <;> omega_arith) (by omega_arith) hx
  have sub0 : Region.Sub ⟨State.addr S + BitVec.ofNat 64 (8 * i + 4 * 0), 4⟩ ⟨State.addr S, 272⟩ :=
    VG.Offset.sub_base _ (by omega_arith)
  have hx₁ : NumOf s₁ (valSlot v) x := hx.congr fun j hj => by
    simp only [slotW]
    rw [g₁ _ (by decide) (by decide), hb, m₁]
    have hj' : valSlot v + j < slots := by have := valSlot_lt v hv; omega_arith
    exact hS.slot hfit ((Frame.refl _ s.mem).writeW (r := ⟨State.addr S + BitVec.ofNat 64 (8 * i + 4 * 0), 4⟩)
      (List.mem_singleton_self _) (rev (numWord (x.rotateLeft r) ((if hi then 0 else 2) + 0)))
      (Region.contains_self _ _)) sub0 hj'
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, sp₂⟩ := wordStore_ok (by rw [g₁ _ (by decide) (by decide), hb])
    ⟨by rw [wr₁]; exact hw.mem, hfit⟩ (hS.congr (g₁ _ (by decide) (by decide)) wr₁) hv hr
    (o := (if hi then 0 else 2) + 1) (off := 8 * i + 4 * 1) (by split <;> omega_arith) (by omega_arith) hx₁
  refine ⟨s₂, ?_, fun j hj => ?_, ?_, fun r' h1 h2 => by rw [g₂ r' h1 h2, g₁ r' h1 h2],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁]⟩
  · rw [subkey, show ([0, 1] : List Nat).flatMap (fun k => rotWord v r ((if hi then 0 else 2) + k) ++
        [.rev t0 t0, .str t0 .r2 (8 * i + 4 * k)]) =
        (rotWord v r ((if hi then 0 else 2) + 0) ++ [.rev t0 t0, .str t0 .r2 (8 * i + 4 * 0)]) ++
        (rotWord v r ((if hi then 0 else 2) + 1) ++ [.rev t0 t0, .str t0 .r2 (8 * i + 4 * 1)]) by simp,
      runBlock_app, e₁, Option.bind_some, e₂]
  · rw [m₂]
    by_cases h4 : j < 4
    · rw [writeW32_other _ (VG.Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)), m₁]
      have h0 := st_byte s.mem (State.addr S + BitVec.ofNat 64 (8 * i + 4 * 0))
        (rev (numWord (x.rotateLeft r) ((if hi then 0 else 2) + 0))) h4
      rw [VG.Offset.add_add, show 8 * i + 4 * 0 + j = 8 * i + j by omega_arith] at h0
      rw [h0, stored_byte x r hi (k := 0) (q := j) (by decide) h4, show 4 * 0 + j = j by omega_arith]
    · have h1 := st_byte s₁.mem (State.addr S + BitVec.ofNat 64 (8 * i + 4 * 1))
        (rev (numWord (x.rotateLeft r) ((if hi then 0 else 2) + 1))) (t := j - 4) (by omega_arith)
      rw [VG.Offset.add_add, show 8 * i + 4 * 1 + (j - 4) = 8 * i + j by omega_arith] at h1
      rw [h1, stored_byte x r hi (k := 1) (q := j - 4) (by decide) (by omega_arith), show 4 * 1 + (j - 4) = j by omega_arith]
  · rw [m₂, m₁]
    refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)).sub
      fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)).sub
      fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩) <;>
      (simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub _ (by omega_arith) (by omega_arith))

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
    obtain ⟨s₁, e₁, b₁, f₁, g₁, rd₁, wr₁, sp₁⟩ := subkey_ok (i := n) (hi := hi) hb hw hS hv hr (by omega_arith) (hX v hv)
    have hsub : Region.Sub ⟨State.addr S + BitVec.ofNat 64 (8 * n), 8⟩ ⟨State.addr S, 272⟩ :=
      VG.Offset.sub_base _ (by omega_arith)
    have hX₁ : ∀ u < 4, NumOf s₁ (valSlot u) (X u) := fun u hu => (hX u hu).congr fun j hj => by
      simp only [slotW]
      rw [g₁ _ (by decide) (by decide), hb]
      exact hS.slot hfit f₁ hsub (by have := valSlot_lt u hu; omega_arith)
    have hb₁ : s₁.gpr sb = b := by rw [g₁ _ (by decide) (by decide), hb]
    obtain ⟨s', e', b', f', g', rd', wr', sp'⟩ := stores_ok ks (n + 1) s₁ hb₁ ⟨by rw [wr₁]; exact hw.mem, hfit⟩
      (hS.congr (g₁ _ (by decide) (by decide)) wr₁) (fun k hk => hks k (List.mem_cons_of_mem _ hk))
      (by omega_arith) hX₁
    refine ⟨s', ?_, fun i hi j hj => ?_, ?_, fun r' h1 h2 => by rw [g' r' h1 h2, g₁ r' h1 h2],
      by rw [rd', rd₁], by rw [wr', wr₁], by rw [sp', sp₁]⟩
    · rw [List.zipIdx_cons, List.flatMap_cons, runBlock_app, e₁, Option.bind_some]
      exact e'
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [f' _ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          intro hc
          rcases Nat.eq_zero_or_pos ks.length with h0 | hpos
          · simp only [Region.Contains, h0, Nat.mul_zero] at hc; omega_arith
          · exact VG.Proof.Camellia.not_contains_off _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith) hc),
          Nat.add_zero, b₁ j hj]
        simp only [subHalf, List.getD_cons_zero]
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega_arith⟩
        have := b' i' (by simp only [List.length_cons] at hi; omega_arith) j hj
        rw [show n + 1 + i' = n + (i' + 1) by omega_arith] at this
        rw [this, List.getD_cons_succ]
    · refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (f'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩) <;>
        (simp only [List.mem_singleton] at hr; subst hr; simp only [List.length_cons]
         exact VG.Offset.sub _ (by omega_arith) (by omega_arith))

end VG.Proof.Camellia.Arm

end

end

/-! ### `Camellia.Arm.KaKb`, which only this module used -/

section

/-!
# Camellia's key schedule on ARMv7: `KA` and `KB`

`kaKb_wp`: from `KL` and `KR` in their slots and the constants' table, the
loop of three pairs of rounds on the running value (`pairPlain_step`), with
the XORs and copies between them (`wordsOp_ok`), leaves `KA` and `KB`
(`kaD2`, `kaD3`) in their slots.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS eorR lsrOp)
open VG.Proof.Camellia (byteOf byteOf_xor pair sigE kaD1 kaD2 kaD3 kaW)

/-! ## Operations on four words -/

/-- An operation on word `k` of the values at `w` and `x`: slot `w + k`
becomes `F` of slots `x + k` and `w + k`. -/
def OpOk (op : Nat → List Instr) (F : BitVec 32 → BitVec 32 → BitVec 32) (w x : Nat) : Prop :=
  ∀ k < 4, ∀ (s : State) (b : BitVec 32), s.gpr sb = b → ScrIn s.wr b →
    ∃ s', runBlock isa (op k) s = some s' ∧
      s'.mem = s.mem.writeW (wordAddr b (w + k))
        (F (s.mem.readW (wordAddr b (x + k)) 32) (s.mem.readW (wordAddr b (w + k)) 32)) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem copy_op (w x : Nat) (hw : w + 4 ≤ slots) (hx : x + 4 ≤ slots) :
    OpOk (fun k => [ldS t0 (x + k), stS (w + k) t0]) (fun a _ => a) w x := by
  intro k hk s b hb hs
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s t0 sb (k := x + k) hb (by omega_arith) hs
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, sp₂, -, -⟩ := stSlot_ok s₁ t0 sb (k := w + k) (by rw [o₁ _ (by decide), hb])
    (by omega_arith) (by rw [wr₁]; exact hs)
  refine ⟨s₂, ?_, by rw [m₂, v₁, m₁], fun r h0 _ => by rw [g₂, o₁ r h0], by rw [rd₂, rd₁], by rw [wr₂, wr₁],
    by rw [sp₂, sp₁]⟩
  show runBlock isa [ldS t0 (x + k), stS (w + k) t0] s = _
  rw [show ([ldS t0 (x + k), stS (w + k) t0] : List Instr) = [.ldr t0 sb (4 * (x + k))] ++
    [.str t0 sb (4 * (w + k))] from rfl, runBlock_app, e₁, Option.bind_some, e₂]

theorem xor_op (w x : Nat) (hw : w + 4 ≤ slots) (hx : x + 4 ≤ slots) :
    OpOk (fun k => [ldS t0 (x + k), ldS t1 (w + k), eorR t0 t0 t1, stS (w + k) t0]) (fun a c => a ^^^ c) w x := by
  intro k hk s b hb hs
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s t0 sb (k := x + k) hb (by omega_arith) hs
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := ldSlot_ok s₁ t1 sb (k := w + k) (by rw [o₁ _ (by decide), hb])
    (by omega_arith) (by rw [wr₁]; exact hs)
  let s₃ := s₂.setReg t0 (s₂.gpr t0 ^^^ s₂.gpr t1)
  have e₃ : runBlock isa [eorR t0 t0 t1] s₂ = some s₃ := by
    rw [runBlock_cons, show exec (eorR t0 t0 t1) s₂ = some s₃ by simp only [eorR, exec, Op2.eval, Option.map_some]; rfl,
      runStep_some, runBlock_nil]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, sp₄, -, -⟩ := stSlot_ok s₃ t0 sb (k := w + k)
    (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), o₂ _ (by decide), o₁ _ (by decide), hb])
    (by omega_arith) (by rw [RegUpd.wr_setReg, wr₂, wr₁]; exact hs)
  refine ⟨s₄, ?_, ?_, fun r h0 h1 => by rw [g₄, RegUpd.gpr_setReg_of_ne _ _ h0, o₂ r h1, o₁ r h0],
    by rw [rd₄, RegUpd.rd_setReg, rd₂, rd₁], by rw [wr₄, RegUpd.wr_setReg, wr₂, wr₁],
    by rw [sp₄, RegUpd.sp_setReg, sp₂, sp₁]⟩
  · show runBlock isa [ldS t0 (x + k), ldS t1 (w + k), eorR t0 t0 t1, stS (w + k) t0] s = _
    rw [show ([ldS t0 (x + k), ldS t1 (w + k), eorR t0 t0 t1, stS (w + k) t0] : List Instr) =
      [.ldr t0 sb (4 * (x + k))] ++ ([.ldr t1 sb (4 * (w + k))] ++ ([eorR t0 t0 t1] ++
        [.str t0 sb (4 * (w + k))])) from rfl, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂,
      Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · rw [m₄, RegUpd.gpr_setReg_self, RegUpd.mem_setReg, m₂, m₁, o₂ _ (by decide), v₁, v₂, m₁]

/-- Four words of an operation. -/
theorem wordsOp_ok {op : Nat → List Instr} {F : BitVec 32 → BitVec 32 → BitVec 32} {w x : Nat}
    (hop : OpOk op F w x) (hsep : x + 4 ≤ w ∨ w + 4 ≤ x) (hw : w + 4 ≤ slots) (hx : x + 4 ≤ slots)
    {b : BitVec 32} :
    ∀ n ≤ 4, ∀ s : State, s.gpr sb = b → ScrIn s.wr b →
      ∃ s', runBlock isa ((List.range n).flatMap op) s = some s' ∧
        (∀ k < n, s'.mem.readW (wordAddr b (w + k)) 32 =
          F (s.mem.readW (wordAddr b (x + k)) 32) (s.mem.readW (wordAddr b (w + k)) 32)) ∧
        (∀ j < slots, j < w ∨ w + n ≤ j → s'.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32) ∧
        (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        Frame [⟨wordAddr b w, 4 * n⟩] s.mem s'.mem
  | 0, _, s, _, _ => ⟨s, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl,
      rfl, Frame.refl _ _⟩
  | n + 1, hn, s, hb, hs => by
    have hfit := hs.fit
    obtain ⟨s₁, e₁, v₁, o₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := wordsOp_ok hop hsep hw hx n (by omega_arith) s hb hs
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, sp₂⟩ := hop n (by omega_arith) s₁ b (by rw [g₁ _ (by decide) (by decide), hb])
      (by rw [wr₁]; exact hs)
    have hfw : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32 := by rw [hb]; exact hfit
    refine ⟨s₂, by rw [List.range_succ, List.flatMap_append, runBlock_app, e₁, Option.bind_some,
        List.flatMap_singleton]; exact e₂, fun k hk => ?_, fun j hj h => ?_,
      fun r h0 h1 => by rw [g₂ r h0 h1, g₁ r h0 h1], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁], ?_⟩
    · rw [m₂, readW_slot_write hfit _ (by omega_arith) (by omega_arith)]
      by_cases hkn : k = n
      · subst hkn
        rw [ite_eq_left rfl, o₁ _ (by omega_arith) (by omega_arith), o₁ _ (by omega_arith) (by omega_arith)]
      · rw [ite_eq_right (by omega_arith), v₁ k (by omega_arith)]
    · rw [m₂, readW_slot_write hfit _ hj (by omega_arith), ite_eq_right (by omega_arith), o₁ j hj (by omega_arith)]
    · have hf2 := hfit
      rw [slots_eq] at hf2 hw
      have hsub1 : Region.Sub ⟨wordAddr b w, 4 * n⟩ ⟨wordAddr b w, 4 * (n + 1)⟩ := Region.sub_prefix (by omega_arith)
      have hsub2 : Region.Sub ⟨wordAddr b (w + n), 4⟩ ⟨wordAddr b w, 4 * (n + 1)⟩ := by
        simp only [wordAddr]
        rw [VG.Arm.addr_add (by omega_arith), VG.Arm.addr_add (by omega_arith)]
        exact VG.Offset.sub _ (by omega_arith) (by omega_arith)
      rw [m₂]
      exact (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
          simp only [List.mem_singleton] at hr; subst hr; exact hsub1⟩).trans
        (((Frame.refl _ _).writeW (r := ⟨wordAddr b (w + n), 4⟩) (List.mem_singleton_self _) _
          (Region.contains_self _ _)).sub fun r hr => ⟨_, List.mem_singleton_self _, by
            simp only [List.mem_singleton] at hr; subst hr; exact hsub2⟩)

/-! ## On the values -/

theorem VW_copy {s s' : State} {w x : Nat} {v : BitVec 64 × BitVec 64} (hv : VW s x v)
    (h : ∀ k < 4, slotW s' (w + k) = slotW s (x + k)) : VW s' w v := fun c hc j hj => by
  rw [h _ (by omega_arith)]; exact hv c hc j hj

theorem VW_xor {s s' : State} {w x : Nat} {v u : BitVec 64 × BitVec 64} (hv : VW s x v) (hu : VW s w u)
    (h : ∀ k < 4, slotW s' (w + k) = slotW s (x + k) ^^^ slotW s (w + k)) :
    VW s' w (v.1 ^^^ u.1, v.2 ^^^ u.2) := fun c hc j hj => by
  rw [h _ (by omega_arith), BitVec.getLsbD_xor, hv c hc j hj, hu c hc j hj]
  by_cases h8 : c < 8
  · simp only [itePos h8, byteOf_xor, BitVec.getLsbD_xor]
  · simp only [iteNeg h8, byteOf_xor, BitVec.getLsbD_xor]

/-! ## Under the rounds' context -/

/-- Four words of an operation in the tail buffer, under `Ctx`. -/
theorem words_ctx {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {op : Nat → List Instr} {F : BitVec 32 → BitVec 32 → BitVec 32} {w x : Nat} (hop : OpOk op F w x)
    (hsep : x + 4 ≤ w ∨ w + 4 ≤ x) (hw1 : tailSlot ≤ w) (hw2 : w + 4 ≤ tailSlot + 32) (hx : x + 4 ≤ slots) :
    ∃ s', runBlock isa ((List.range 4).flatMap op) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      (∀ k < 4, slotW s' (w + k) = F (slotW s (x + k)) (slotW s (w + k))) ∧
      (∀ j < slots, j < w ∨ w + 4 ≤ j → slotW s' j = slotW s j) := by
  have hs := hc.scr hp
  have hfit := hs.fit
  rw [tailSlot_eq] at hw1 hw2
  have hw : w + 4 ≤ slots := by rw [slots_eq]; omega_arith
  obtain ⟨s', e', v', o', g', rd', wr', -, f'⟩ := wordsOp_ok hop hsep hw hx 4 (Nat.le_refl _) s rfl ⟨hs.wr, hfit⟩
  have hb : s'.gpr sb = s.gpr sb := g' _ (by decide) (by decide)
  refine ⟨s', e', hc.step rd' wr' (fun r h1 _ => g' r (fun h => h1 (h ▸ by decide)) (fun h => h1 (h ▸ by decide)))
    ?_, g' _ (by decide) (by decide), fun k hk => by simp only [slotW, hb]; exact v' k hk,
    fun j hj h => by simp only [slotW, hb]; exact o' j hj h⟩
  refine f'.sub fun r hr => ⟨_, by simp only [ctxRegions, List.mem_cons]; exact .inr (.inr (.inl rfl)), ?_⟩
  simp only [List.mem_singleton] at hr; subst hr
  rw [slots_eq] at hfit
  simp only [wordAddr, hc.base]
  rw [← hc.base, VG.Arm.addr_add (by omega_arith), VG.Arm.addr_add (by rw [tailSlot_eq]; omega_arith)]
  exact VG.Offset.sub _ (by rw [tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)

/-- `KA` and `KB`, from `KL` and `KR`. -/
structure KaPost (s₀ : State) (KL KR : BitVec 64 × BitVec 64) (s : State) : Prop where
  ctx : Ctx s₀ s
  kl : VW s klSlot KL
  kr : VW s krSlot KR
  ka : VW s kaSlot (kaD2 KL KR)
  kb : VW s kbSlot (kaD3 KL KR)

/-- Before pair `i`. -/
structure KaInv (s₀ : State) (KL KR : BitVec 64 × BitVec 64) (i : Nat) (s : State) : Prop where
  lt : i < 3
  ctx : Ctx s₀ s
  kp : AtEntry s (s₀.gpr sb) (2 * i)
  w : VW s wSlot (kaW KL KR i)
  kl : VW s klSlot KL
  kr : VW s krSlot KR
  ka : 2 ≤ i → VW s kaSlot (kaD2 KL KR)
  cnt : slotW s cntSlot = BitVec.ofNat 32 (3 - i)

/-- The pair's result. -/
theorem pair_kaW (KL KR : BitVec 64 × BitVec 64) {i : Nat} (hi : i < 3) :
    pair (sigE (2 * i)) (sigE (2 * i + 1)) (kaW KL KR i) =
      (if i = 0 then kaD1 KL KR else if i = 1 then kaD2 KL KR else kaD3 KL KR) := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_arith) with rfl | rfl | rfl <;> rfl

/-- After pair `i` and the operations, before the count's step. -/
structure KaMid (s₀ : State) (KL KR : BitVec 64 × BitVec 64) (i : Nat) (s : State) : Prop where
  ctx : Ctx s₀ s
  kp : AtEntry s (s₀.gpr sb) (2 * i + 2)
  w : VW s wSlot (kaW KL KR (i + 1))
  kl : VW s klSlot KL
  kr : VW s krSlot KR
  ka : 1 ≤ i → VW s kaSlot (kaD2 KL KR)
  kb : i = 2 → VW s kbSlot (kaD3 KL KR)
  cnt : slotW s cntSlot = BitVec.ofNat 32 (3 - i)

/-- `cmp r, #v`. -/
theorem cmpImm_ok (s : State) (r : Reg) {v : BitVec 32} (hv : encodable v = true) :
    runBlock isa [.cmp r (.imm v)] s = some (subFlags s (s.gpr r) v) := by
  rw [runBlock_cons, show exec (.cmp r (.imm v)) s = some (subFlags s (s.gpr r) v) by
    simp only [exec, Op2.eval, hv, ↓reduceIte, Option.map_some], runStep_some, runBlock_nil]

/-- `mov t1, t0, lsr #1; cmp t1, #0`. -/
theorem cntTest_ok (s : State) :
    ∃ s', runBlock isa [.mov t1 (lsrOp t0 1), .cmp t1 (.imm 0)] s = some s' ∧
      s'.z = (s.gpr t0 >>> 1 - 0 == 0) ∧ (∀ r, r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₁ := s.setReg t1 (s.gpr t0 >>> 1)
  refine ⟨subFlags s₁ (s₁.gpr t1) 0, ?_, by rw [subFlags_z, RegUpd.gpr_setReg_self],
    fun r h => by rw [subFlags_gpr, RegUpd.gpr_setReg_of_ne _ _ h], rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.mov t1 (lsrOp t0 1)) s = some s₁ by simp [exec, lsrOp, Op2.eval, s₁],
    runStep_some, cmpImm_ok s₁ t1 (by decide)]

theorem kaStep_wp {s₀ : State} {KL KR : BitVec 64 × BitVec 64} (hp : KeyCtx s₀ 6 sigE) {i : Nat} {s : State}
    (h : KaInv s₀ KL KR i s) {c : Prog isa} {Q : State → Prop} (hcont : ∀ s', KaMid s₀ KL KR i s' → WP isa c s' Q) :
    WP isa (.seq (.block (pairPlain ++ [ldS t0 cntSlot, .mov t1 (lsrOp t0 1), .cmp t1 (.imm 0)]))
      (.seq (.ite .ne
          (.seq (.block [.cmp t0 (.imm 3)])
            (.ite .eq (.block (xorWords wSlot klSlot))
              (.block (copyWords kaSlot wSlot ++ xorWords wSlot krSlot))))
          (.block (copyWords kbSlot wSlot))) c)) s Q := by
  have hi := h.lt
  obtain ⟨s₁, e₁, c₁, k₁, w₁, o₁⟩ := pairPlain_step hp h.ctx h.kp (by omega_arith) (by omega_arith) h.w
  rw [pair_kaW KL KR hi] at w₁
  have hs₁ := c₁.scr hp
  have hb₁ := c₁.base
  have keep₁ : ∀ a, keySlot ≤ a → a + 4 ≤ wSlot ∨ wSlot + 4 ≤ a → a + 4 ≤ slots →
      ∀ v, VW s a v → VW s₁ a v := fun a h1 ha has v hv =>
    hv.congr fun j hj => o₁ _ (by omega_arith) (by omega_arith) (by omega_arith)
  have kl₁ := keep₁ klSlot (by decide) (by decide) (by decide) _ h.kl
  have kr₁ := keep₁ krSlot (by decide) (by decide) (by decide) _ h.kr
  have cnt₁ : slotW s₁ cntSlot = BitVec.ofNat 32 (3 - i) := by
    rw [o₁ _ (by decide) (by decide) (by decide), h.cnt]
  -- The count's tests.
  obtain ⟨s₂, e₂, v₂, g₂, m₂, rd₂, wr₂, sp₂⟩ := ldSlot_ok s₁ t0 sb (k := cntSlot) rfl (by decide)
    ⟨hs₁.wr, hs₁.fit⟩
  obtain ⟨s₄, e₃, z₄, g₄, m₄, rd₄, wr₄, sp₄⟩ := cntTest_ok s₂
  have ht0 : s₄.gpr t0 = BitVec.ofNat 32 (3 - i) := by
    rw [g₄ _ (by decide), v₂]; exact cnt₁
  have hz₄ : s₄.z = decide (i = 2) := by
    rw [z₄, v₂]
    change (slotW s₁ cntSlot >>> 1 - 0 == 0) = _
    rw [cnt₁]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_arith) with rfl | rfl | rfl <;> decide
  have c₄ : Ctx s₀ s₄ := c₁.step (by rw [rd₄, rd₂]) (by rw [wr₄, wr₂])
    (fun r h1 _ => by rw [g₄ r (fun e => h1 (by rw [e]; decide)), g₂ r (fun e => h1 (by rw [e]; decide))])
    (by rw [m₄, m₂]; exact Frame.refl _ _)
  have hs₄ : ∀ j, slotW s₄ j = slotW s₁ j := fun j => by
    simp only [slotW, m₄, m₂, g₄ sb (by decide), g₂ sb (by decide)]
  have k₄ : s₄.gpr kp = s₁.gpr kp := by rw [g₄ _ (by decide), g₂ _ (by decide)]
  have hk₄ : AtEntry s₄ (s₀.gpr sb) (2 * i + 2) := by rw [AtEntry, k₄]; exact k₁
  have w₄ := w₁.congr fun j _ => hs₄ _
  have kl₄ := kl₁.congr fun j _ => hs₄ _
  have kr₄ := kr₁.congr fun j _ => hs₄ _
  have cnt₄ : slotW s₄ cntSlot = BitVec.ofNat 32 (3 - i) := by rw [hs₄, cnt₁]
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [runBlock_app, e₁, Option.bind_some, show ([ldS t0 cntSlot, .mov t1 (lsrOp t0 1), .cmp t1 (.imm 0)] :
      List Instr) = [.ldr t0 sb (4 * cntSlot)] ++ [.mov t1 (lsrOp t0 1), .cmp t1 (.imm 0)] from rfl,
      runBlock_app, e₂, Option.bind_some, e₃], ?_⟩)
  refine WP.seq (WP.mono (Q := KaMid s₀ KL KR i) ?_ hcont)
  have hka : 2 ≤ i → VW s₄ kaSlot (kaD2 KL KR) := fun h2 =>
    ((keep₁ kaSlot (by decide) (by decide) (by decide) _ (h.ka h2)).congr fun j _ => hs₄ _)
  refine WP.ite (!(decide (i = 2))) ((eval_ne s₄).trans (by rw [hz₄])) (fun hne => ?_) (fun heq => ?_)
  · have hi2 : i ≠ 2 := by simpa using hne
    let s₅ := subFlags s₄ (s₄.gpr t0) 3
    have e₅ : runBlock isa [.cmp t0 (.imm 3)] s₄ = some s₅ := cmpImm_ok s₄ t0 (by decide)
    have hz₅ : s₅.z = decide (i = 0) := by
      rw [subFlags_z, ht0]
      rcases (show i = 0 ∨ i = 1 by omega_arith) with rfl | rfl <;> decide
    have c₅ : Ctx s₀ s₅ := c₄.step rfl rfl (fun _ _ _ => rfl) (Frame.refl _ _)
    have hs₅ : ∀ j, slotW s₅ j = slotW s₄ j := fun _ => rfl
    have w₅ := w₄.congr fun j _ => hs₅ _
    have kl₅ := kl₄.congr fun j _ => hs₅ _
    have kr₅ := kr₄.congr fun j _ => hs₅ _
    refine WP.seq (WP.of_runBlock ⟨s₅, e₅, ?_⟩)
    refine WP.ite (decide (i = 0)) ((eval_eq s₅).trans (by rw [hz₅])) (fun h0 => ?_) (fun h0 => ?_)
    · -- After the first pair: `KL` is XORed in.
      have hi0 : i = 0 := by simpa using h0
      subst hi0
      obtain ⟨s₆, e₆, c₆, k₆, v₆, o₆⟩ := words_ctx hp c₅ (xor_op wSlot klSlot (by decide) (by decide))
        (by decide) (by decide) (by decide) (by decide)
      refine WP.of_runBlock ⟨s₆, e₆, ⟨c₆, by rw [AtEntry, k₆]; exact hk₄, ?_, ?_, ?_, fun h => by omega_arith,
        fun h => by omega_arith, by rw [o₆ _ (by decide) (by decide), hs₅, cnt₄]⟩⟩
      · have := VW_xor (s := s₅) (s' := s₆) (x := klSlot) (w := wSlot) kl₅ w₅ fun k hk => by
          rw [v₆ k hk]
        simpa [kaW, BitVec.xor_comm] using this
      · exact kl₅.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)
      · exact kr₅.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)
    · -- After the second: it is `KA`, and `KR` is XORed in.
      have hi1 : i = 1 := by simp at h0; omega_arith
      subst hi1
      obtain ⟨s₆, e₆, c₆, k₆, v₆, o₆⟩ := words_ctx hp c₅ (copy_op kaSlot wSlot (by decide) (by decide))
        (by decide) (by decide) (by decide) (by decide)
      obtain ⟨s₇, e₇, c₇, k₇, v₇, o₇⟩ := words_ctx hp c₆ (xor_op wSlot krSlot (by decide) (by decide))
        (by decide) (by decide) (by decide) (by decide)
      have w₆ : VW s₆ wSlot (kaD2 KL KR) := w₅.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)
      have kr₆ : VW s₆ krSlot KR := kr₅.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)
      have ka₆ : VW s₆ kaSlot (kaD2 KL KR) := VW_copy w₅ fun k hk => by rw [v₆ k hk]
      refine WP.of_runBlock ⟨s₇, by
        rw [runBlock_app, show runBlock isa (copyWords kaSlot wSlot) s₅ = some s₆ from e₆, Option.bind_some]
        exact e₇,
        ⟨c₇, by rw [AtEntry, k₇, k₆]; exact hk₄, ?_, ?_, ?_, fun _ => ?_, fun h => by omega_arith, ?_⟩⟩
      · have := VW_xor (s := s₆) (s' := s₇) (x := krSlot) (w := wSlot) kr₆ w₆ fun k hk => by rw [v₇ k hk]
        simpa [kaW, BitVec.xor_comm] using this
      · exact (kl₅.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)).congr fun j hj =>
          o₇ _ (by decide +revert) (by decide +revert)
      · exact kr₆.congr fun j hj => o₇ _ (by decide +revert) (by decide +revert)
      · exact ka₆.congr fun j hj => o₇ _ (by decide +revert) (by decide +revert)
      · rw [o₇ _ (by decide) (by decide), o₆ _ (by decide) (by decide), hs₅, cnt₄]
  · -- After the third: it is `KB`.
    have hi2 : i = 2 := by simpa using heq
    subst hi2
    obtain ⟨s₆, e₆, c₆, k₆, v₆, o₆⟩ := words_ctx hp c₄ (copy_op kbSlot wSlot (by decide) (by decide))
      (by decide) (by decide) (by decide) (by decide)
    refine WP.of_runBlock ⟨s₆, e₆, ⟨c₆, by rw [AtEntry, k₆]; exact hk₄, ?_, ?_, ?_, fun _ => ?_, fun _ => ?_, ?_⟩⟩
    · exact w₄.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)
    · exact kl₄.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)
    · exact kr₄.congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)
    · exact (hka (by decide)).congr fun j hj => o₆ _ (by decide +revert) (by decide +revert)
    · exact VW_copy w₄ fun k hk => by rw [v₆ k hk]
    · rw [o₆ _ (by decide) (by decide), cnt₄]

/-- The count's step: `ldr t0, [sb, #4 cntSlot]; subs t0, t0, #1; str t0, [sb, #4 cntSlot]`. -/
theorem cntStep_ok {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {c : Nat} (hc3 : 1 ≤ c ∧ c ≤ 3) (hcnt : slotW s cntSlot = BitVec.ofNat 32 c) :
    ∃ s', runBlock isa [ldS t0 cntSlot, .subs t0 t0 (.imm 1), stS cntSlot t0] s = some s' ∧ Ctx s₀ s' ∧
      s'.z = decide (c = 1) ∧ s'.gpr kp = s.gpr kp ∧ slotW s' cntSlot = BitVec.ofNat 32 (c - 1) ∧
      (∀ j < slots, j ≠ cntSlot → slotW s' j = slotW s j) := by
  have hs := hc.scr hp
  have hfit := hs.fit
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s t0 sb (k := cntSlot) rfl (by decide) ⟨hs.wr, hfit⟩
  let s₂ := (subFlags s₁ (s₁.gpr t0) 1).setReg t0 (s₁.gpr t0 - 1)
  have e₂ : runBlock isa [.subs t0 t0 (.imm 1)] s₁ = some s₂ := by
    simp only [runBlock_cons, exec, Op2.eval, show encodable 1 = true by decide, ↓reduceIte, Option.map_some,
      runStep_some, runBlock_nil]
    rfl
  have hb₂ : s₂.gpr sb = s.gpr sb := by
    rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), subFlags_gpr, o₁ _ (by decide)]
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, sp₃, z₃, f₃⟩ := stSlot_ok s₂ t0 sb (k := cntSlot) hb₂ (by decide)
    ⟨by rw [RegUpd.wr_setReg, subFlags_wr, wr₁]; exact hs.wr, hfit⟩
  have ht : s₂.gpr t0 = BitVec.ofNat 32 (c - 1) := by
    rw [RegUpd.gpr_setReg_self, v₁]
    change slotW s cntSlot - 1 = _
    rw [hcnt, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_arith)]
  have hb₃ : s₃.gpr sb = s.gpr sb := by rw [g₃, hb₂]
  have hfit' := hfit
  rw [slots_eq] at hfit'
  refine ⟨s₃, ?_, hc.step (by rw [rd₃, RegUpd.rd_setReg, subFlags_rd, rd₁]) (by rw [wr₃, RegUpd.wr_setReg,
      subFlags_wr, wr₁]) (fun r h1 _ => by
        rw [g₃, RegUpd.gpr_setReg_of_ne _ _ (fun e => h1 (by rw [e]; decide)), subFlags_gpr,
          o₁ r (fun e => h1 (by rw [e]; decide))]) ?_, ?_, by rw [g₃, RegUpd.gpr_setReg_of_ne _ _ (by decide),
      subFlags_gpr, o₁ _ (by decide)], ?_, fun j hj hne => ?_⟩
  · rw [show ([ldS t0 cntSlot, .subs t0 t0 (.imm 1), stS cntSlot t0] : List Instr) =
      [.ldr t0 sb (4 * cntSlot)] ++ ([.subs t0 t0 (.imm 1)] ++ [.str t0 sb (4 * cntSlot)]) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  · have f₃' : Frame [⟨wordAddr (s.gpr sb) cntSlot, 4⟩] s.mem s₃.mem := by rw [← m₁]; exact f₃
    refine f₃'.sub fun r hr => ⟨_, by simp only [ctxRegions, List.mem_cons]; exact .inr (.inl rfl), ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [hc.base]
    exact fun _ h => h
  · rw [z₃, RegUpd.z_setReg, subFlags_z, v₁]
    change (slotW s cntSlot - 1 == 0) = _
    rw [hcnt, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat32_sub_beq (by omega_arith) (by omega_arith)]
  · rw [slotW, hb₃, m₃, ← hb₂, Mem.readW_writeW_self32, ht]
  · rw [slotW, hb₃, m₃, readW_slot_write hfit _ hj (by decide), ite_eq_right hne,
      RegUpd.mem_setReg, subFlags_mem, m₁]

/-- The loop's start: the running value `KL ⊕ KR`, the count 3. -/
theorem kaStart_ok {s₀ : State} {KL KR : BitVec 64 × BitVec 64} (hp : KeyCtx s₀ 6 sigE)
    (hk : AtEntry s₀ (s₀.gpr sb) 0) (hl : VW s₀ klSlot KL) (hr : VW s₀ krSlot KR) :
    ∃ s, runBlock isa (copyWords wSlot klSlot ++ xorWords wSlot krSlot ++
        ([.mov t0 (.imm 3), stS cntSlot t0] : List Instr)) s₀ =
      some s ∧ KaInv s₀ KL KR 0 s := by
  obtain ⟨s₁, e₁, c₁, k₁, v₁, o₁⟩ := words_ctx hp (Ctx.refl s₀) (copy_op wSlot klSlot (by decide) (by decide))
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₂, e₂, c₂, k₂, v₂, o₂⟩ := words_ctx hp c₁ (xor_op wSlot krSlot (by decide) (by decide))
    (by decide) (by decide) (by decide) (by decide)
  have hs₂ := c₂.scr hp
  let s₃ := s₂.setReg t0 (BitVec.ofNat 32 3)
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, sp₄, -, f₄⟩ := stSlot_ok s₃ t0 sb (b := s₂.gpr sb) (k := cntSlot)
    (RegUpd.gpr_setReg_of_ne _ _ (by decide)) (by decide)
    ⟨by rw [RegUpd.wr_setReg]; exact hs₂.wr, hs₂.fit⟩
  have hfit := hs₂.fit
  have hb₄ : s₄.gpr sb = s₂.gpr sb := by rw [g₄, RegUpd.gpr_setReg_of_ne _ _ (by decide)]
  have hs₄ : ∀ j < slots, j ≠ cntSlot → slotW s₄ j = slotW s₂ j := fun j hj hne => by
    rw [slotW, hb₄, m₄, readW_slot_write hfit _ hj (by decide), ite_eq_right hne]
    rfl
  have kl₁ := hl.congr fun j hj => o₁ _ (by decide +revert) (by decide +revert)
  have kr₁ := hr.congr fun j hj => o₁ _ (by decide +revert) (by decide +revert)
  have w₂ : VW s₂ wSlot (kaW KL KR 0) := by
    have := VW_xor (s := s₁) (s' := s₂) (x := krSlot) (w := wSlot) kr₁ (VW_copy hl fun k hk => by rw [v₁ k hk])
      fun k hk => by rw [v₂ k hk]
    simpa [kaW, BitVec.xor_comm] using this
  refine ⟨s₄, ?_, ⟨by decide, ?_, by rw [AtEntry, g₄, RegUpd.gpr_setReg_of_ne _ _ (by decide), k₂, k₁]; exact hk,
    w₂.congr fun j hj => hs₄ _ (by decide +revert) (by decide +revert),
    (kl₁.congr fun j hj => o₂ _ (by decide +revert) (by decide +revert)).congr fun j hj =>
      hs₄ _ (by decide +revert) (by decide +revert),
    (kr₁.congr fun j hj => o₂ _ (by decide +revert) (by decide +revert)).congr fun j hj =>
      hs₄ _ (by decide +revert) (by decide +revert),
    fun h => by omega_arith, ?_⟩⟩
  · rw [runBlock_app, runBlock_app, show runBlock isa (copyWords wSlot klSlot) s₀ = some s₁ from e₁,
      Option.bind_some, show runBlock isa (xorWords wSlot krSlot) s₁ = some s₂ from e₂, Option.bind_some,
      runBlock_cons, show exec (.mov t0 (.imm 3)) s₂ = some s₃ by
        simp only [exec, Op2.eval, show encodable (3 : BitVec 32) = true by decide, ↓reduceIte, Option.map_some]
        rfl, runStep_some, show ([stS cntSlot t0] : List Instr) = [.str t0 sb (4 * cntSlot)] from rfl, e₄]
  · refine c₂.step (by rw [rd₄]; rfl) (by rw [wr₄]; rfl) (fun r h1 _ => by
      rw [g₄, RegUpd.gpr_setReg_of_ne _ _ (fun e => h1 (by rw [e]; decide))]) ?_
    refine f₄.sub fun r hr => ⟨_, by simp only [ctxRegions, List.mem_cons]; exact .inr (.inl rfl), ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [c₂.base]
    exact fun _ h => h
  · rw [slotW, hb₄, m₄, Mem.readW_writeW_self32, RegUpd.gpr_setReg_self]

theorem kaKb_wp {s₀ : State} {KL KR : BitVec 64 × BitVec 64} (hp : KeyCtx s₀ 6 sigE)
    (hk : AtEntry s₀ (s₀.gpr sb) 0) (hl : VW s₀ klSlot KL) (hr : VW s₀ krSlot KR) :
    WP isa kaKb s₀ (KaPost s₀ KL KR) := by
  obtain ⟨s₁, e₁, h₁⟩ := kaStart_ok hp hk hl hr
  unfold kaKb
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.loop (M := isa) (fun n s => ∃ i, n = 3 - i ∧ KaInv s₀ KL KR i s) (fun n s hs => ?_) 3 s₁
    ⟨0, rfl, h₁⟩
  obtain ⟨i, rfl, hi⟩ := hs
  refine kaStep_wp hp hi fun s₂ h₂ => ?_
  obtain ⟨s₃, e₃, c₃, z₃, k₃, n₃, o₃⟩ := cntStep_ok hp h₂.ctx (c := 3 - i) (by have := hi.lt; omega_arith) h₂.cnt
  refine WP.of_runBlock ⟨s₃, e₃, ?_⟩
  have keep : ∀ a, a + 4 ≤ cntSlot ∨ cntSlot + 1 ≤ a → a + 4 ≤ slots → ∀ v, VW s₂ a v → VW s₃ a v :=
    fun a ha has v h => h.congr fun j hj => o₃ _ (by omega_arith) (by omega_arith)
  by_cases h2 : i = 2
  · subst h2
    refine .inl ⟨(eval_ne s₃).trans (by rw [z₃]; rfl), ⟨c₃, keep _ (by decide) (by decide) _ h₂.kl,
      keep _ (by decide) (by decide) _ h₂.kr, keep _ (by decide) (by decide) _ (h₂.ka (by decide)),
      keep _ (by decide) (by decide) _ (h₂.kb rfl)⟩⟩
  · have hi3 := hi.lt
    refine .inr ⟨(eval_ne s₃).trans (by rw [z₃]; simp; omega_arith), 3 - (i + 1), by omega_arith, i + 1, rfl,
      ⟨by omega_arith, c₃, by rw [AtEntry, k₃]; exact h₂.kp, keep _ (by decide) (by decide) _ h₂.w,
        keep _ (by decide) (by decide) _ h₂.kl, keep _ (by decide) (by decide) _ h₂.kr,
        fun h => keep _ (by decide) (by decide) _ (h₂.ka (by omega_arith)), by rw [n₃]; congr 1⟩⟩

end VG.Proof.Camellia.Arm

end

end

/-! ### `Camellia.Arm.KeyLoad`, which only this module used -/

section

/-!
# Camellia's key schedule on ARMv7: `KL` and `KR`

`loadKey_wp`: the key's words to the slots of `KL` and `KR` (`KR` zero for
a key of 16 bytes, its right half the complement of its left for one of
24), as `klkr_halves` gives their halves (`VW`, by `HW` for each half).
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS eorR)
open VG.Proof.Camellia (byteOf getLsbD_byteOf byteOf_wordAt)
open VG.Spec.Camellia (wordAt)

/-! ## Halves in words -/

/-- The two words at slot `a` hold `x`: its byte `c` (the most significant
first) is byte `c % 4` of word `c / 4`. -/
def HW (s : State) (a : Nat) (x : BitVec 64) : Prop :=
  ∀ c < 8, ∀ j < 8, (slotW s (a + c / 4)).getLsbD (8 * (c % 4) + j) = (byteOf x c).getLsbD j

theorem VW_of_HW {s : State} {a : Nat} {v : BitVec 64 × BitVec 64} (h1 : HW s a v.1) (h2 : HW s (a + 2) v.2) :
    VW s a v := fun c hc j hj => by
  by_cases h8 : c < 8
  · rw [itePos h8, Nat.mod_eq_of_lt h8]; exact h1 c h8 j hj
  · rw [iteNeg h8, show a + c / 4 = a + 2 + (c - 8) / 4 by omega_arith, show c % 4 = (c - 8) % 4 by omega_arith,
      show c % 8 = c - 8 by omega_arith]
    exact h2 (c - 8) (by omega_arith) j hj

/-- Two words loaded from `A` and `A + 4`. -/
theorem HW_words {s : State} {a : Nat} {m : Mem} {A : Addr} (h0 : slotW s a = m.readW A 32)
    (h1 : slotW s (a + 1) = m.readW (A + BitVec.ofNat 64 4) 32) : HW s a (wordAt m A) := by
  intro c hc j hj
  have hw : slotW s (a + c / 4) = m.readW (A + BitVec.ofNat 64 (4 * (c / 4))) 32 := by
    rcases (show c / 4 = 0 ∨ c / 4 = 1 by omega_arith) with h | h <;> rw [h]
    · rw [Nat.add_zero, h0]; simp
    · exact h1
  rw [hw, W32.readW32_bit _ _ (by omega_arith) hj, byteOf_wordAt _ _ hc, VG.Offset.add_add,
    show 4 * (c / 4) + c % 4 = c by omega_arith]

/-- The complements of two words loaded from `A` and `A + 4`. -/
theorem HW_not {s : State} {a : Nat} {m : Mem} {A : Addr} (h0 : slotW s a = m.readW A 32 ^^^ BitVec.allOnes 32)
    (h1 : slotW s (a + 1) = m.readW (A + BitVec.ofNat 64 4) 32 ^^^ BitVec.allOnes 32) :
    HW s a (~~~ wordAt m A) := by
  intro c hc j hj
  have hw : slotW s (a + c / 4) = m.readW (A + BitVec.ofNat 64 (4 * (c / 4))) 32 ^^^ BitVec.allOnes 32 := by
    rcases (show c / 4 = 0 ∨ c / 4 = 1 by omega_arith) with h | h <;> rw [h]
    · rw [Nat.add_zero, h0]; simp
    · exact h1
  rw [hw, BitVec.getLsbD_xor, BitVec.getLsbD_allOnes, getLsbD_byteOf _ hc hj, BitVec.getLsbD_not,
    W32.readW32_bit _ _ (by omega_arith) hj, ← getLsbD_byteOf _ hc hj, byteOf_wordAt _ _ hc, VG.Offset.add_add,
    show 4 * (c / 4) + c % 4 = c by omega_arith]
  simp [show 8 * (c % 4) + j < 32 by omega_arith, show 56 - 8 * c + j < 64 by omega_arith]

theorem HW_zero {s : State} {a : Nat} (h0 : slotW s a = 0) (h1 : slotW s (a + 1) = 0) : HW s a 0 := by
  intro c hc j hj
  have hw : slotW s (a + c / 4) = 0 := by
    rcases (show c / 4 = 0 ∨ c / 4 = 1 by omega_arith) with h | h <;> rw [h]
    · rw [Nat.add_zero, h0]
    · exact h1
  rw [hw, getLsbD_byteOf _ hc hj]; simp

/-! ## Loads -/

/-- The key at `K`, apart from the scratch buffer at `b`. -/
structure KeyIn (s : State) (b K : BitVec 32) (len : Nat) : Prop where
  base : s.gpr sb = b
  scr : ScrIn s.wr b
  r0 : s.gpr .r0 = K
  rd : (⟨State.addr K, len⟩ : Region) ∈ s.rd
  fit : K.toNat + len ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr K, len⟩ ⟨State.addr b, 4 * slots⟩
  le : len ≤ 32

theorem KeyIn.congr {s s' : State} {b K : BitVec 32} {len : Nat} (h : KeyIn s b K len)
    (hb : s'.gpr sb = s.gpr sb) (h0 : s'.gpr .r0 = s.gpr .r0) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    KeyIn s' b K len :=
  ⟨hb.trans h.base, ⟨hwr ▸ h.scr.mem, h.scr.fit⟩, h0.trans h.r0, hrd ▸ h.rd, h.fit, h.sep, h.le⟩

/-- The key's word at offset `o`. -/
theorem KeyIn.word {s : State} {b K : BitVec 32} {len : Nat} (h : KeyIn s b K len) {o : Nat} (ho : o + 4 ≤ len) :
    State.addr (s.gpr .r0 + BitVec.ofNat 32 o) = State.addr K + BitVec.ofNat 64 o ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 o)) 4 := by
  have e : State.addr (s.gpr .r0 + BitVec.ofNat 32 o) = State.addr K + BitVec.ofNat 64 o := by
    rw [h.r0, VG.Arm.addr_add (by have := h.fit; omega_arith)]
  refine ⟨e, ⟨_, List.mem_append_left _ h.rd, ?_⟩⟩
  rw [e]; exact VG.Offset.contains_base _ (by omega_arith) (by have := h.fit; omega_arith)

/-- A word of the key, kept by a frame of the scratch buffer. -/
theorem KeyIn.keep {s : State} {b K : BitVec 32} {len : Nat} (h : KeyIn s b K len) {m m' : Mem}
    (hf : Frame [⟨State.addr b, 4 * slots⟩] m m') {o : Nat} (ho : o + 4 ≤ len) :
    m'.readW (State.addr K + BitVec.ofNat 64 o) 32 = m.readW (State.addr K + BitVec.ofNat 64 o) 32 :=
  hf.readW (VG.Offset.contains_base _ (by omega_arith) (by have := h.fit; omega_arith)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.sep) (by decide)

/-- `ldr t0, [r0, #o]; str t0, [sb, #4 k]` for each `(o, k)` of `L`. -/
theorem loads_ok {b K : BitVec 32} {len : Nat} : ∀ (L : List (Nat × Nat)) {s : State}, KeyIn s b K len →
    (L.map (·.2)).Nodup → (∀ x ∈ L, x.1 + 4 ≤ len ∧ x.2 < slots) →
    ∃ s', runBlock isa (L.flatMap fun (o, k) => [.ldr t0 .r0 o, stS k t0]) s = some s' ∧
      (∀ x ∈ L, s'.mem.readW (wordAddr b x.2) 32 = s.mem.readW (State.addr K + BitVec.ofNat 64 x.1) 32) ∧
      (∀ k < slots, k ∉ L.map (·.2) → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem
  | [], s, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | x :: L, s, hk, hnd, hin => by
    obtain ⟨hx1, hx2⟩ := hin x List.mem_cons_self
    obtain ⟨ea, ei⟩ := hk.word hx1
    let s₁ := s.setReg t0 (s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 x.1)) 32)
    have e₁ : exec (.ldr t0 .r0 x.1) s = some s₁ := exec_ldr (by have := hk.le; omega_arith) ei
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, sp₂, -, f₂⟩ := stSlot_ok s₁ t0 sb (k := x.2)
      (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), hk.base]) hx2 hk.scr
    rw [List.map_cons, List.nodup_cons] at hnd
    have hk₂ : KeyIn s₂ b K len := hk.congr (by rw [g₂, RegUpd.gpr_setReg_of_ne _ _ (by decide)])
      (by rw [g₂, RegUpd.gpr_setReg_of_ne _ _ (by decide)]) rd₂ wr₂
    obtain ⟨s', e', v', k', g', rd', wr', sp', f'⟩ := loads_ok L hk₂ hnd.2
      fun y hy => hin y (List.mem_cons_of_mem _ hy)
    have hfit := hk.scr.fit
    have f₂' : Frame [⟨State.addr b, 4 * slots⟩] s.mem s₂.mem := f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit hx2⟩
    have hslot : ∀ j < slots, s₂.mem.readW (wordAddr b j) 32 = if j = x.2 then
        s.mem.readW (State.addr K + BitVec.ofNat 64 x.1) 32 else s.mem.readW (wordAddr b j) 32 := fun j hj => by
      rw [m₂, readW_slot_write hfit _ hj hx2, RegUpd.gpr_setReg_self, ea]; rfl
    refine ⟨s', ?_, fun y hy => ?_, fun j hj hn => ?_, fun r hr => by
        rw [g' r hr, g₂, RegUpd.gpr_setReg_of_ne _ _ hr],
      by rw [rd', rd₂]; rfl, by rw [wr', wr₂]; rfl, by rw [sp', sp₂]; rfl, f₂'.trans f'⟩
    · rw [List.flatMap_cons, runBlock_app, runBlock_cons, e₁, runStep_some,
        show ([stS x.2 t0] : List Instr) = [.str t0 sb (4 * x.2)] from rfl, e₂, Option.bind_some]
      exact e'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · by_cases hin' : y.2 ∈ L.map (·.2)
        · exact absurd hin' hnd.1
        · rw [k' _ hx2 hin', hslot _ hx2, ite_eq_left rfl]
      · rw [v' y hy', hk.keep f₂' (hin y (List.mem_cons_of_mem _ hy')).1]
    · simp only [List.map_cons, List.mem_cons, not_or] at hn
      rw [k' j hj hn.2, hslot j hj, ite_eq_right hn.1]

/-- `str r, [sb, #4 k]` for each `k` of `ks`. -/
theorem storeAll_ok (r : Reg) {b : BitVec 32} : ∀ (ks : List Nat) {s : State}, s.gpr sb = b →
    ScrIn s.wr b → (∀ k ∈ ks, k < slots) →
    ∃ s', runBlock isa (ks.map fun k => stS k r) s = some s' ∧
      (∀ k ∈ ks, s'.mem.readW (wordAddr b k) 32 = s.gpr r) ∧
      (∀ k < slots, k ∉ ks → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem
  | [], s, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k :: ks, s, hb, hw, hk => by
    have hk0 : k < slots := hk k List.mem_cons_self
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, sp₁, -, f₁⟩ := stSlot_ok s r sb (k := k) hb hk0 hw
    obtain ⟨s', e', v', o', g', rd', wr', sp', f'⟩ := storeAll_ok r ks (s := s₁) (by rw [g₁, hb])
      (by rw [wr₁]; exact hw) fun k h => hk k (List.mem_cons_of_mem _ h)
    have hfit := hw.fit
    have hslot : ∀ j < slots, s₁.mem.readW (wordAddr b j) 32 = if j = k then s.gpr r else
        s.mem.readW (wordAddr b j) 32 := fun j hj => by rw [m₁, readW_slot_write hfit _ hj hk0]
    refine ⟨s', by rw [List.map_cons, ← List.singleton_append, runBlock_app,
        show ([stS k r] : List Instr) = [.str r sb (4 * k)] from rfl, e₁, Option.bind_some]; exact e',
      fun j hj => ?_, fun j hj hn => ?_, by rw [g', g₁], by rw [rd', rd₁], by rw [wr', wr₁], by rw [sp', sp₁], ?_⟩
    · rcases List.mem_cons.mp hj with rfl | hj'
      · by_cases hin : j ∈ ks
        · rw [v' j hin, g₁]
        · rw [o' j hk0 hin, hslot j hk0, ite_eq_left rfl]
      · rw [v' j hj', g₁]
    · simp only [List.mem_cons, not_or] at hn
      rw [o' j hj hn.2, hslot j hj, ite_eq_right hn.1]
    · exact (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit hk0⟩).trans f'

/-! ## The key -/

/-- `KR` as `klkr_halves` gives its halves. -/
def krOf (m : Mem) (A : Addr) (len : Nat) : BitVec 64 × BitVec 64 :=
  (if len = 16 then 0 else wordAt m (A + BitVec.ofNat 64 16),
   if len = 16 then 0 else if len = 24 then ~~~ wordAt m (A + BitVec.ofNat 64 16) else wordAt m (A + BitVec.ofNat 64 24))

/-- What a branch of `loadKey` leaves, from `s`: `KR` in its slots. -/
structure KrPost (s : State) (b : BitVec 32) (m₀ : Mem) (A : Addr) (len : Nat) (s' : State) : Prop where
  kr : VW s' krSlot (krOf m₀ A len)
  keep : ∀ k < slots, k < krSlot ∨ krSlot + 4 ≤ k →
    s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32
  regs : ∀ r, r ≠ t0 → r ≠ u7 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem

theorem klSlot_eq : klSlot = 632 := rfl
theorem krSlot_eq : krSlot = 636 := rfl

theorem slotW_of {s : State} {b : BitVec 32} (hb : s.gpr sb = b) (k : Nat) :
    slotW s k = s.mem.readW (wordAddr b k) 32 := by rw [slotW, hb]

/-- The key's words in `s` are those of `m₀`. -/
def KeySame (s : State) (m₀ : Mem) (A : Addr) (len : Nat) : Prop :=
  ∀ o, o + 4 ≤ len → s.mem.readW (A + BitVec.ofNat 64 o) 32 = m₀.readW (A + BitVec.ofNat 64 o) 32

theorem KeySame.frame {s s' : State} {b K : BitVec 32} {len : Nat} {m₀ : Mem} (hk : KeyIn s b K len)
    (h : KeySame s m₀ (State.addr K) len) (hf : Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem) :
    KeySame s' m₀ (State.addr K) len := fun o ho => by rw [hk.keep hf ho]; exact h o ho

/-- A key of 16 bytes: `KR` is zero. -/
theorem kr16_ok {s : State} {b K : BitVec 32} {len : Nat} {m₀ : Mem} (hk : KeyIn s b K len) (h16 : len = 16) :
    ∃ s', runBlock isa (([.mov t0 (.imm 0)] : List Instr) ++ (List.range 4).map fun k => stS (krSlot + k) t0) s =
      some s' ∧
      KrPost s b m₀ (State.addr K) len s' := by
  have hfit := hk.scr.fit
  let s₃ := s.setReg t0 0
  obtain ⟨s₄, e₄, v₄, k₄, g₄, rd₄, wr₄, sp₄, f₄⟩ := storeAll_ok t0 (b := b) ((List.range 4).map fun k => krSlot + k)
    (s := s₃) (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hk.base)
    (by rw [RegUpd.wr_setReg]; exact hk.scr)
    (fun k hk' => by simp only [List.mem_map, List.mem_range] at hk'; obtain ⟨k, hk', rfl⟩ := hk'
                     rw [krSlot_eq, slots_eq]; omega_arith)
  have hb₄ : s₄.gpr sb = b := by rw [g₄, RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hk.base
  have hz : ∀ k < 4, slotW s₄ (krSlot + k) = 0 := fun k hk' => by
    rw [slotW_of hb₄, v₄ (krSlot + k) (by simp only [List.mem_map, List.mem_range]; exact ⟨k, hk', rfl⟩),
      RegUpd.gpr_setReg_self]
  have e : krOf m₀ (State.addr K) len = (0, 0) := by simp [krOf, h16]
  refine ⟨s₄, ?_, ⟨?_, fun k hk' h => ?_, fun r h1 _ => by rw [g₄, RegUpd.gpr_setReg_of_ne _ _ h1],
    rd₄, wr₄, sp₄, f₄⟩⟩
  · rw [runBlock_app, runBlock_cons, show exec (.mov t0 (.imm 0)) s = some s₃ by
      simp only [exec, Op2.eval, show encodable (0 : BitVec 32) = true by decide, ↓reduceIte, Option.map_some]; rfl,
      runStep_some, runBlock_nil, Option.bind_some]
    simpa only [List.map_map, Function.comp_def] using e₄
  · rw [e]
    exact VW_of_HW (HW_zero (hz 0 (by decide)) (hz 1 (by decide))) (HW_zero (hz 2 (by decide)) (hz 3 (by decide)))
  · rw [k₄ k hk' (by simp only [List.mem_map, List.mem_range, not_exists, not_and]; intro j hj h'; omega_arith)]; rfl

/-- `ldr t0, [r0, #o]; eor t0, t0, u7; str t0, [sb, #4 k]`, with `u7` all ones. -/
theorem ldNotSt_ok {s : State} {b K : BitVec 32} {len : Nat} (hk : KeyIn s b K len)
    (hu : s.gpr u7 = BitVec.allOnes 32) {o k : Nat} (ho : o + 4 ≤ len) (hks : k < slots) :
    ∃ s', runBlock isa [.ldr t0 .r0 o, eorR t0 t0 u7, stS k t0] s = some s' ∧
      s'.mem = s.mem.writeW (wordAddr b k) (s.mem.readW (State.addr K + BitVec.ofNat 64 o) 32 ^^^ BitVec.allOnes 32) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem := by
  obtain ⟨ea, ei⟩ := hk.word ho
  let s₁ := s.setReg t0 (s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 o)) 32)
  let s₂ := s₁.setReg t0 (s₁.gpr t0 ^^^ s₁.gpr u7)
  have hb₂ : s₂.gpr sb = b := by
    rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hk.base
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, sp₃, -, f₃⟩ := stSlot_ok s₂ t0 sb (k := k) hb₂ hks hk.scr
  refine ⟨s₃, ?_, ?_, fun r hr => ?_, rd₃, wr₃, sp₃, f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hk.scr.fit hks⟩⟩
  · rw [runBlock_cons, exec_ldr (by have := hk.le; omega_arith) ei, runStep_some, runBlock_cons,
      show exec (eorR t0 t0 u7) s₁ = some s₂ by simp only [eorR, exec, Op2.eval, Option.map_some]; rfl,
      runStep_some, show ([stS k t0] : List Instr) = [.str t0 sb (4 * k)] from rfl]
    exact e₃
  · rw [m₃, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (by decide), hu, ea]; rfl
  · rw [g₃, RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setReg_of_ne _ _ hr]

/-- A key of 24 bytes: `KR`'s right half is the complement of its left. -/
theorem kr24_ok {s : State} {b K : BitVec 32} {len : Nat} (hk : KeyIn s b K len) (h24 : len = 24) :
    ∃ s', runBlock isa [.mov u7 (.imm 0), .dp .sub u7 u7 (.imm 1), .ldr t0 .r0 16, eorR t0 t0 u7,
        stS (krSlot + 2) t0, .ldr t0 .r0 20, eorR t0 t0 u7, stS (krSlot + 3) t0] s = some s' ∧
      s'.mem.readW (wordAddr b (krSlot + 2)) 32 =
        s.mem.readW (State.addr K + BitVec.ofNat 64 16) 32 ^^^ BitVec.allOnes 32 ∧
      s'.mem.readW (wordAddr b (krSlot + 3)) 32 =
        s.mem.readW (State.addr K + BitVec.ofNat 64 20) 32 ^^^ BitVec.allOnes 32 ∧
      (∀ j < slots, j ≠ krSlot + 2 → j ≠ krSlot + 3 →
        s'.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32) ∧
      (∀ r, r ≠ t0 → r ≠ u7 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem := by
  have hfit := hk.scr.fit
  let s₁ := s.setReg u7 0
  let s₂ := s₁.setReg u7 (s₁.gpr u7 - 1)
  have hu : s₂.gpr u7 = BitVec.allOnes 32 := by rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_self]; decide
  have g₂ : ∀ r, r ≠ u7 → s₂.gpr r = s.gpr r := fun r h => by
    rw [RegUpd.gpr_setReg_of_ne _ _ h, RegUpd.gpr_setReg_of_ne _ _ h]
  have hk₂ : KeyIn s₂ b K len := hk.congr (g₂ _ (by decide)) (g₂ _ (by decide)) rfl rfl
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, sp₃, f₃⟩ := ldNotSt_ok hk₂ hu (o := 16) (k := krSlot + 2) (by omega_arith) (by decide)
  have hk₃ : KeyIn s₃ b K len := hk₂.congr (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, sp₄, f₄⟩ := ldNotSt_ok hk₃ (by rw [g₃ _ (by decide), hu]) (o := 20)
    (k := krSlot + 3) (by omega_arith) (by decide)
  refine ⟨s₄, ?_, ?_, ?_, fun j hj h1 h2 => ?_, fun r h1 h2 => by rw [g₄ r h1, g₃ r h1, g₂ r h2],
    by rw [rd₄, rd₃]; rfl, by rw [wr₄, wr₃]; rfl, by rw [sp₄, sp₃]; rfl, f₃.trans f₄⟩
  · rw [runBlock_cons, show exec (.mov u7 (.imm 0)) s = some s₁ by
        simp only [exec, Op2.eval, show encodable (0 : BitVec 32) = true by decide, ↓reduceIte, Option.map_some]; rfl,
      runStep_some, runBlock_cons, show exec (.dp .sub u7 u7 (.imm 1)) s₁ = some s₂ by
        simp only [exec, Op2.eval, show encodable (1 : BitVec 32) = true by decide, ↓reduceIte, Option.map_some]; rfl,
      runStep_some, show ([.ldr t0 .r0 16, eorR t0 t0 u7, stS (krSlot + 2) t0, .ldr t0 .r0 20, eorR t0 t0 u7,
        stS (krSlot + 3) t0] : List Instr) = [.ldr t0 .r0 16, eorR t0 t0 u7, stS (krSlot + 2) t0] ++
          [.ldr t0 .r0 20, eorR t0 t0 u7, stS (krSlot + 3) t0] from rfl, runBlock_app, e₃, Option.bind_some, e₄]
  · rw [m₄, readW_slot_write hfit _ (by decide) (by decide), ite_eq_right (by decide), m₃, Mem.readW_writeW_self32]
    rfl
  · rw [m₄, Mem.readW_writeW_self32, hk₂.keep f₃ (by omega_arith)]
    rfl
  · rw [m₄, readW_slot_write hfit _ hj (by decide), ite_eq_right h2, m₃, readW_slot_write hfit _ hj (by decide),
      ite_eq_right h1]
    rfl

/-- Keys of 24 or 32 bytes. -/
theorem krNot16_wp {s : State} {b K : BitVec 32} {len : Nat} {m₀ : Mem} (hk : KeyIn s b K len)
    (hm : KeySame s m₀ (State.addr K) len) (hlen : len = 24 ∨ len = 32)
    (hr1 : s.gpr .r1 = BitVec.ofNat 32 len) :
    WP isa (.seq (.block [.ldr t0 .r0 16, stS krSlot t0, .ldr t0 .r0 20, stS (krSlot + 1) t0, .cmp .r1 (.imm 24)])
        (.ite .eq
          (.block [.mov u7 (.imm 0), .dp .sub u7 u7 (.imm 1), .ldr t0 .r0 16, eorR t0 t0 u7,
            stS (krSlot + 2) t0, .ldr t0 .r0 20, eorR t0 t0 u7, stS (krSlot + 3) t0])
          (.block [.ldr t0 .r0 24, stS (krSlot + 2) t0, .ldr t0 .r0 28, stS (krSlot + 3) t0]))) s
      (KrPost s b m₀ (State.addr K) len) := by
  have hfit := hk.scr.fit
  have h16 : len ≠ 16 := by omega_arith
  obtain ⟨s₃, e₃, v₃, k₃, g₃, rd₃, wr₃, sp₃, f₃⟩ := loads_ok [(16, krSlot), (20, krSlot + 1)] hk (by decide)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact ⟨by omega_arith, by decide⟩)
  let s₄ := subFlags s₃ (s₃.gpr .r1) 24
  have e₄ : exec (.cmp .r1 (.imm 24)) s₃ = some s₄ := by
    simp only [exec, Op2.eval, show encodable (24 : BitVec 32) = true by decide, ↓reduceIte, Option.map_some]
    rfl
  have hz₄ : s₄.z = decide (len = 24) := by
    rw [subFlags_z, g₃ _ (by decide), hr1, show (24 : BitVec 32) = BitVec.ofNat 32 24 from rfl,
      ofNat32_sub_beq (by omega_arith) (by decide)]
  have hk₄ : KeyIn s₄ b K len := hk.congr (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃
  have hm₄ : KeySame s₄ m₀ (State.addr K) len := hm.frame hk f₃
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [show ([.ldr t0 .r0 16, stS krSlot t0, .ldr t0 .r0 20, stS (krSlot + 1) t0, .cmp .r1 (.imm 24)] :
        List Instr) = ([(16, krSlot), (20, krSlot + 1)].flatMap fun (o, k) => [.ldr t0 .r0 o, stS k t0]) ++
          [.cmp .r1 (.imm 24)] from rfl, runBlock_app, e₃, Option.bind_some, runBlock_cons, e₄, runStep_some,
      runBlock_nil], ?_⟩)
  have hl0 : s₄.mem.readW (wordAddr b krSlot) 32 = m₀.readW (State.addr K + BitVec.ofNat 64 16) 32 := by
    rw [show s₄.mem = s₃.mem from rfl, v₃ (16, krSlot) (by simp), hm 16 (by omega_arith)]
  have hl1 : s₄.mem.readW (wordAddr b (krSlot + 1)) 32 = m₀.readW (State.addr K + BitVec.ofNat 64 20) 32 := by
    rw [show s₄.mem = s₃.mem from rfl, v₃ (20, krSlot + 1) (by simp), hm 20 (by omega_arith)]
  have ho₄ : ∀ j < slots, j ≠ krSlot → j ≠ krSlot + 1 →
      s₄.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32 := fun j hj h1 h2 =>
    k₃ j hj (by simp [h1, h2])
  -- The right half, from `s₄` to `s'`.
  have tail : ∀ s' : State, s'.gpr sb = b → (∀ r, r ≠ t0 → r ≠ u7 → s'.gpr r = s₄.gpr r) →
      s'.rd = s₄.rd → s'.wr = s₄.wr → s'.sp = s₄.sp → Frame [⟨State.addr b, 4 * slots⟩] s₄.mem s'.mem →
      (∀ j < slots, j ≠ krSlot + 2 → j ≠ krSlot + 3 →
        s'.mem.readW (wordAddr b j) 32 = s₄.mem.readW (wordAddr b j) 32) →
      HW s' (krSlot + 2) (krOf m₀ (State.addr K) len).2 → KrPost s b m₀ (State.addr K) len s' := by
    intro s' hb hg hrd hwr hsp hf ho hR
    have e : (krOf m₀ (State.addr K) len).1 = wordAt m₀ (State.addr K + BitVec.ofNat 64 16) := by
      simp [krOf, h16]
    refine ⟨VW_of_HW (e ▸ HW_words ?_ ?_) hR, fun k hk' h => ?_, fun r h1 h2 => by rw [hg r h1 h2]; exact g₃ r h1,
      hrd.trans rd₃, hwr.trans wr₃, hsp.trans sp₃, f₃.trans hf⟩
    · rw [slotW_of hb, ho _ (by decide) (by decide) (by decide), hl0]
    · rw [slotW_of hb, ho _ (by decide) (by decide) (by decide), hl1, VG.Offset.add_add]
    · rw [ho k hk' (by omega_arith) (by omega_arith), ho₄ k hk' (by omega_arith) (by omega_arith)]
  refine WP.ite (decide (len = 24)) ((eval_eq s₄).trans (by rw [hz₄])) (fun h24 => ?_) (fun h24 => ?_)
  · have h24 : len = 24 := by simpa using h24
    obtain ⟨s', e', v2, v3, o', g', rd', wr', sp', f'⟩ := kr24_ok hk₄ h24
    have hb' : s'.gpr sb = b := by rw [g' _ (by decide) (by decide)]; exact hk₄.base
    refine WP.of_runBlock ⟨s', e', tail s' hb' g' rd' wr' sp' f' o' ?_⟩
    have e : (krOf m₀ (State.addr K) len).2 = ~~~ wordAt m₀ (State.addr K + BitVec.ofNat 64 16) := by
      simp [krOf, h24]
    rw [e]
    refine HW_not ?_ ?_
    · rw [slotW_of hb', v2, hm₄ 16 (by omega_arith)]
    · rw [slotW_of hb', v3, hm₄ 20 (by omega_arith), VG.Offset.add_add]
  · have h24 : len ≠ 24 := by simpa using h24
    obtain ⟨s₅, e₅, v₅, k₅, g₅, rd₅, wr₅, sp₅, f₅⟩ := loads_ok [(24, krSlot + 2), (28, krSlot + 3)] hk₄
      (by decide) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> exact ⟨by omega_arith, by decide⟩)
    have hb₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide)]; exact hk₄.base
    refine WP.of_runBlock ⟨s₅, by
      rw [show ([.ldr t0 .r0 24, stS (krSlot + 2) t0, .ldr t0 .r0 28, stS (krSlot + 3) t0] : List Instr) =
        [(24, krSlot + 2), (28, krSlot + 3)].flatMap fun (o, k) => [.ldr t0 .r0 o, stS k t0] from rfl]
      exact e₅, tail s₅ hb₅ (fun r h1 _ => g₅ r h1) rd₅ wr₅ sp₅ f₅
        (fun j hj h1 h2 => k₅ j hj (by simp [h1, h2])) ?_⟩
    have e : (krOf m₀ (State.addr K) len).2 = wordAt m₀ (State.addr K + BitVec.ofNat 64 24) := by
      simp [krOf, h16, h24]
    rw [e]
    refine HW_words ?_ ?_
    · rw [slotW_of hb₅, v₅ (24, krSlot + 2) (by simp), hm₄ 24 (by omega_arith)]
    · rw [slotW_of hb₅, v₅ (28, krSlot + 3) (by simp), hm₄ 28 (by omega_arith), VG.Offset.add_add]

/-- What `loadKey` leaves. -/
structure LoadPost (s₀ : State) (b K : BitVec 32) (len : Nat) (s : State) : Prop where
  kl : VW s klSlot (wordAt s₀.mem (State.addr K), wordAt s₀.mem (State.addr K + BitVec.ofNat 64 8))
  kr : VW s krSlot (krOf s₀.mem (State.addr K) len)
  keep : ∀ k < slots, k < klSlot ∨ klSlot + 8 ≤ k →
    s.mem.readW (wordAddr b k) 32 = s₀.mem.readW (wordAddr b k) 32
  regs : ∀ r, r ≠ t0 → r ≠ u7 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s.mem

theorem loadKey_wp {s₀ : State} {b K : BitVec 32} {len : Nat} (hk : KeyIn s₀ b K len)
    (hlen : len = 16 ∨ len = 24 ∨ len = 32) (hr1 : s₀.gpr .r1 = BitVec.ofNat 32 len) :
    WP isa loadKey s₀ (LoadPost s₀ b K len) := by
  have hfit := hk.scr.fit
  unfold loadKey
  -- `KL`.
  obtain ⟨s₁, e₁, v₁, k₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := loads_ok ((List.range 4).map fun k => (4 * k, klSlot + k)) hk
    (by decide) (fun x hx => by
      simp only [List.mem_map, List.mem_range] at hx; obtain ⟨k, hk', rfl⟩ := hx
      exact ⟨by rcases hlen with rfl | rfl | rfl <;> omega_arith, by rw [klSlot_eq, slots_eq]; omega_arith⟩)
  let s₂ := subFlags s₁ (s₁.gpr .r1) 16
  have e₂ : exec (.cmp .r1 (.imm 16)) s₁ = some s₂ := by
    simp only [exec, Op2.eval, show encodable (16 : BitVec 32) = true by decide, ↓reduceIte, Option.map_some]
    rfl
  have hz₂ : s₂.z = decide (len = 16) := by
    rw [subFlags_z, g₁ _ (by decide), hr1, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      ofNat32_sub_beq (by omega_arith) (by decide)]
  have hk₂ : KeyIn s₂ b K len := hk.congr (g₁ _ (by decide)) (g₁ _ (by decide)) rd₁ wr₁
  have hm₂ : KeySame s₂ s₀.mem (State.addr K) len := KeySame.frame hk (fun _ _ => rfl) f₁
  have hkl : ∀ k < 4, s₂.mem.readW (wordAddr b (klSlot + k)) 32 =
      s₀.mem.readW (State.addr K + BitVec.ofNat 64 (4 * k)) 32 := fun k hk' =>
    v₁ (4 * k, klSlot + k) (by simp only [List.mem_map, List.mem_range]; exact ⟨k, hk', rfl⟩)
  have hklo : ∀ j < slots, j < klSlot ∨ klSlot + 4 ≤ j →
      s₂.mem.readW (wordAddr b j) 32 = s₀.mem.readW (wordAddr b j) 32 := fun j hj h =>
    k₁ j hj (by
      simp only [List.map_map, Function.comp_def, List.mem_map, List.mem_range, not_exists, not_and]
      intro k hk' h'; omega_arith)
  have hcode : (List.range 4).flatMap (fun k => [Instr.ldr t0 .r0 (4 * k), stS (klSlot + k) t0]) =
      ((List.range 4).map fun k => (4 * k, klSlot + k)).flatMap fun (o, k) => [.ldr t0 .r0 o, stS k t0] := rfl
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [runBlock_app, hcode, e₁, Option.bind_some, runBlock_cons, e₂, runStep_some, runBlock_nil], ?_⟩)
  have post : ∀ s : State, KrPost s₂ b s₀.mem (State.addr K) len s → LoadPost s₀ b K len s := by
    intro s h
    have hb : s.gpr sb = b := by rw [h.regs _ (by decide) (by decide)]; exact hk₂.base
    have ho : ∀ k < 4, s.mem.readW (wordAddr b (klSlot + k)) 32 =
        s₀.mem.readW (State.addr K + BitVec.ofNat 64 (4 * k)) 32 := fun k hk' => by
      rw [h.keep _ (by rw [klSlot_eq, slots_eq]; omega_arith) (.inl (by rw [klSlot_eq, krSlot_eq]; omega_arith)), hkl k hk']
    refine ⟨VW_of_HW (HW_words ?_ ?_) (HW_words ?_ ?_), h.kr, fun k hk' hk2 => ?_,
      fun r h1 h2 => by rw [h.regs r h1 h2]; exact g₁ r h1, h.rd.trans rd₁, h.wr.trans wr₁, h.sp.trans sp₁,
      f₁.trans h.frame⟩
    · rw [slotW_of hb, show klSlot = klSlot + 0 from rfl, ho 0 (by decide)]; simp
    · rw [slotW_of hb, ho 1 (by decide)]
    · rw [slotW_of hb, ho 2 (by decide)]
    · rw [slotW_of hb, show klSlot + 2 + 1 = klSlot + 3 from rfl, ho 3 (by decide), VG.Offset.add_add]
      (try rfl)
    · rw [h.keep k hk' (by rw [klSlot_eq] at hk2; rw [krSlot_eq]; omega_arith), hklo k hk' (by omega_arith)]
  refine WP.ite (decide (len = 16)) ((eval_eq s₂).trans (by rw [hz₂])) (fun h16 => ?_) (fun h16 => ?_)
  · have h16 : len = 16 := by simpa using h16
    obtain ⟨s', e', h'⟩ := kr16_ok (m₀ := s₀.mem) hk₂ h16
    exact WP.of_runBlock ⟨s', e', post s' h'⟩
  · have h16 : len ≠ 16 := by simpa using h16
    exact WP.mono (krNot16_wp hk₂ hm₂ (by omega_arith) (by show s₁.gpr .r1 = _; rw [g₁ _ (by decide)]; exact hr1)) post

end VG.Proof.Camellia.Arm

end

end

/-! ### `Camellia.Arm.KeyInit`, which only this module used -/

section

/-!
# Camellia's key schedule on ARMv7: the prologue and the key

`ekPrologue_ok`: the callee-saved registers saved, the schedule's pointer
and the key's length in their slots, and the planes of `Sigma1 … Sigma6`
stored as the table's first six entries (`constStores_ok`), which hold the
constants in every lane (`sigma_rel`). `loadKey_wp`: `KL` and `KR`, from
the key's words, in their slots (`VW`).
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS eorR imm32)
open VG.Impl.Camellia (sigmas keyPlane32)
open VG.Proof.Camellia (sigma_rel)
open VG.Proof.Camellia (byteOf getLsbD_byteOf sigE byteOf_wordAt)

/-! ## Constants -/

/-- `movw d, #lo; movt d, #hi`. -/
theorem imm32_ok (s : State) (d : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa (imm32 d v) s = some s' ∧ s'.gpr d = v ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₁ := s.setReg d ((v.extractLsb' 0 16).setWidth 32)
  refine ⟨s₁.setReg d (v.extractLsb' 16 16 ++ (s₁.gpr d).extractLsb' 0 16), ?_, ?_,
    fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setReg_of_ne _ _ hr], rfl, rfl, rfl, rfl⟩
  · rw [imm32, runBlock_cons, show exec (.movw d (v.extractLsb' 0 16)) s = some s₁ from rfl, runStep_some,
      runBlock_cons, show exec (.movt d (v.extractLsb' 16 16)) s₁ =
        some (s₁.setReg d (v.extractLsb' 16 16 ++ (s₁.gpr d).extractLsb' 0 16)) from rfl,
      runStep_some, runBlock_nil]
  · rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_self]; exact movw_movt v

/-- `imm32 t0, v; str t0, [sb, #4 k]` for each `(k, v)` of `L`. -/
theorem constStores_ok {b : BitVec 32} : ∀ (L : List (Nat × BitVec 32)) {s : State}, s.gpr sb = b →
    ScrIn s.wr b → (L.map (·.1)).Nodup → (∀ x ∈ L, x.1 < slots) →
    ∃ s', runBlock isa (L.flatMap fun (k, v) => imm32 t0 v ++ [stS k t0]) s = some s' ∧
      (∀ x ∈ L, s'.mem.readW (wordAddr b x.1) 32 = x.2) ∧
      (∀ k < slots, k ∉ L.map (·.1) → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem
  | [], s, _, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | x :: L, s, hb, hw, hnd, hin => by
    have hx := hin x List.mem_cons_self
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := imm32_ok s t0 x.2
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, sp₂, -, f₂⟩ := stSlot_ok s₁ t0 sb (k := x.1)
      (by rw [o₁ _ (by decide), hb]) hx (by rw [wr₁]; exact hw)
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', k', g', rd', wr', sp', f'⟩ := constStores_ok L (s := s₂)
      (by rw [g₂, o₁ _ (by decide), hb]) (by rw [wr₂, wr₁]; exact hw) hnd.2
      fun y hy => hin y (List.mem_cons_of_mem _ hy)
    have hfit := hw.fit
    have hslot : ∀ j < slots, s₂.mem.readW (wordAddr b j) 32 = if j = x.1 then x.2 else
        s.mem.readW (wordAddr b j) 32 := fun j hj => by
      rw [m₂, readW_slot_write hfit _ hj hx, v₁, m₁]
    refine ⟨s', ?_, fun y hy => ?_, fun j hj hn => ?_, fun r hr => by rw [g' r hr, g₂, o₁ r hr],
      by rw [rd', rd₂, rd₁], by rw [wr', wr₂, wr₁], by rw [sp', sp₂, sp₁], ?_⟩
    · rw [List.flatMap_cons, runBlock_app, runBlock_app, e₁, Option.bind_some,
        show ([stS x.1 t0] : List Instr) = [.str t0 sb (4 * x.1)] from rfl, e₂, Option.bind_some]
      exact e'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · by_cases hin' : y.1 ∈ L.map (·.1)
        · exact absurd hin' hnd.1
        · rw [k' _ hx hin', hslot _ hx, ite_eq_left rfl]
      · exact v' y hy'
    · simp only [List.map_cons, List.mem_cons, not_or] at hn
      rw [k' j hj hn.2, hslot j hj, ite_eq_right hn.1]
    · rw [← m₁]
      exact (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit hx⟩).trans f'

/-- The table's first six entries' words. -/
def sigmaTable : List (Nat × BitVec 32) :=
  (List.range 6).flatMap fun e => (List.range 16).map fun k => (keySlot + 16 * e + k, keyPlane32 (sigE e) (k / 8) (k % 8))

theorem sigmas_zipIdx : sigmas.zipIdx = (List.range 6).map fun e => (sigE e, e) := rfl

theorem sigmas_eq : (sigmas.zipIdx.flatMap fun (x, e) => sigmaOne e x) =
    sigmaTable.flatMap fun (k, v) => imm32 t0 v ++ [stS k t0] := by
  rw [sigmas_zipIdx]
  simp only [sigmaTable, List.flatMap_map, List.flatMap_assoc, sigmaOne]

theorem sigmaTable_nodup : (sigmaTable.map (·.1)).Nodup ∧ ∀ x ∈ sigmaTable, x.1 < slots := by
  constructor <;> decide

theorem mem_sigmaTable {e k : Nat} (he : e < 6) (hk : k < 16) :
    (keySlot + 16 * e + k, keyPlane32 (sigE e) (k / 8) (k % 8)) ∈ sigmaTable := by
  simp only [sigmaTable, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨e, he, k, hk, rfl⟩

theorem sigmaTable_slot {x : Nat × BitVec 32} (hx : x ∈ sigmaTable) : keySlot ≤ x.1 ∧ x.1 < keySlot + 96 := by
  simp only [sigmaTable, List.mem_flatMap, List.mem_range, List.mem_map] at hx
  obtain ⟨e, he, k, hk, rfl⟩ := hx
  simp only; omega_using [he, hk]

/-! ## The prologue -/

theorem ekPrologue_ok {s₀ : State} {b : BitVec 32} (hb : s₀.gpr .r3 = b) (hw : ScrIn s₀.wr b) :
    ∃ s, runBlock isa (saveRegs .r3 ++ [movR sb .r3, stS dSlot .r2, stS nSlot .r1] ++
        (sigmas.zipIdx.flatMap fun (x, e) => sigmaOne e x)) s₀ = some s ∧
      s.gpr sb = b ∧ (∀ r, r ≠ sb → r ≠ t0 → s.gpr r = s₀.gpr r) ∧ Saved s₀ b s.mem ∧
      s.mem.readW (wordAddr b dSlot) 32 = s₀.gpr .r2 ∧ s.mem.readW (wordAddr b nSlot) 32 = s₀.gpr .r1 ∧
      (∀ e < 6, ∀ j < 16, entryW s.mem b e j = keyPlane32 (sigE e) (j / 8) (j % 8)) ∧
      Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp := by
  have hfit := hw.fit
  obtain ⟨s₁, e₁, sv₁, g₁, rd₁, wr₁, sp₁, f₁, -⟩ := save_ok hw hb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := movR_ok s₁ sb .r3
  have b₂ : s₂.gpr sb = b := by rw [r₂, g₁, hb]
  have hw₂ : ScrIn s₂.wr b := by rw [wr₂, wr₁]; exact hw
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, sp₃, -, f₃⟩ := stSlot_ok s₂ .r2 sb (k := dSlot) b₂ (by decide) hw₂
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, sp₄, -, f₄⟩ := stSlot_ok s₃ .r1 sb (k := nSlot) (by rw [g₃, b₂]) (by decide)
    (by rw [wr₃]; exact hw₂)
  obtain ⟨hnd, hlt⟩ := sigmaTable_nodup
  obtain ⟨s₅, e₅, v₅, k₅, g₅, rd₅, wr₅, sp₅, f₅⟩ := constStores_ok sigmaTable (s := s₄) (by rw [g₄, g₃, b₂])
    (by rw [wr₄, wr₃]; exact hw₂) hnd hlt
  have hout : ∀ k, k < keySlot ∨ keySlot + 96 ≤ k → k ∉ sigmaTable.map (·.1) := fun k hk h => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    have := sigmaTable_slot hx; omega_using [hk, this]
  have hg : ∀ r, r ≠ sb → r ≠ t0 → s₅.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [g₅ r h2, g₄, g₃, o₂ r h1, g₁]
  have hrun : runBlock isa (saveRegs .r3 ++ [movR sb .r3, stS dSlot .r2, stS nSlot .r1] ++
      (sigmas.zipIdx.flatMap fun (x, e) => sigmaOne e x)) s₀ = some s₅ := by
    rw [sigmas_eq, runBlock_app, runBlock_app, e₁, Option.bind_some,
      show ([movR sb .r3, stS dSlot .r2, stS nSlot .r1] : List Instr) =
        [movR sb .r3] ++ ([.str .r2 sb (4 * dSlot)] ++ [.str .r1 sb (4 * nSlot)]) from rfl,
      runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄, Option.bind_some]
    exact e₅
  refine ⟨s₅, hrun, by rw [g₅ _ (by decide), g₄, g₃, b₂], hg, fun i hi => ?_, ?_, ?_, fun e he j hj => ?_, ?_,
    by rw [rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₅, wr₄, wr₃, wr₂, wr₁], by rw [sp₅, sp₄, sp₃, sp₂, sp₁]⟩
  · rw [k₅ _ (by rw [savedSlot_eq, slots_eq]; omega_using [hi]) (hout _ (.inr (by rw [savedSlot_eq, keySlot_eq]; omega_using []))),
      m₄, readW_slot_write hfit _ (by rw [savedSlot_eq, slots_eq]; omega_using [hi]) (by decide),
      ite_eq_right (by rw [savedSlot_eq, nSlot_eq]; omega_using [hi]), m₃,
      readW_slot_write hfit _ (by rw [savedSlot_eq, slots_eq]; omega_using [hi]) (by decide),
      ite_eq_right (by rw [savedSlot_eq, dSlot_eq]; omega_using [hi]), m₂]
    exact sv₁ i hi
  · rw [k₅ _ (by decide) (hout _ (.inr (by decide))), m₄, readW_slot_write hfit _ (by decide) (by decide),
      ite_eq_right (by decide), m₃, readW_slot_write hfit _ (by decide) (by decide), ite_eq_left rfl, o₂ _ (by decide),
      g₁]
  · rw [k₅ _ (by decide) (hout _ (.inr (by decide))), m₄, readW_slot_write hfit _ (by decide) (by decide),
      ite_eq_left rfl, g₃, o₂ _ (by decide), g₁]
  · have := v₅ _ (mem_sigmaTable he hj)
    simp only at this
    rw [entryW]; exact this
  · refine f₁.trans ?_
    rw [← m₂]
    refine (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      ((f₄.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans f₅) <;>
      (simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit (by decide))

end VG.Proof.Camellia.Arm

end

end


/-!
# Camellia's key schedule on ARMv7: the whole function

`expandKey_wp`: `expandKey` meets `expandKeyArm`. After the prologue
(`ekPrologue_ok`), `loadKey_wp` and `kaKb_wp` leave `KL`, `KR`, `KA` and
`KB` in their slots; `revs_ok` byte-swaps them into numbers (`NumOf`), and
`stores_ok` stores the subkeys, which are the specification's
(`scheduleWords_expandKey`, `schedule_of_stores`).
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS)
open VG.Proof.Camellia (byteOf hiW loW rotHalf hi_eq lo_eq sigE kaD2 kaD3 kaD_eq klkr_halves
  schedule_of_stores subkeys_lt4 subkeys_length keyVals valNum)
open VG.Spec.Camellia (wordAt)

/-- The key schedule on ARMv7 with its working space at `r3`. -/
def expandKeyArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let sched : Region := ⟨State.addr (s.gpr .r2), 272⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 4 * slots⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧ key.Disjoint sched ∧ key.Disjoint scratch ∧
      sched.Disjoint scratch ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 272 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 4 * slots ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 16 ∨ (s.gpr .r1).toNat = 24 ∨ (s.gpr .r1).toNat = 32)
  post s s' :=
    Spec.Camellia.bytesAt s'.mem (State.addr (s.gpr .r2))
        (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds (s.gpr .r1).toNat)) =
      Spec.Camellia.scheduleBytes
        (Spec.Camellia.expandKey (Spec.Camellia.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat))
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp

theorem entryW_slot (s : State) (i j : Nat) : entryW s.mem (s.gpr sb) i j = slotW s (keySlot + 16 * i + j) := rfl

/-- What the subkeys' stores leave: the schedule's bytes. -/
structure StoresPost (s₈ : State) (b S : BitVec 32) (len : Nat) (key : List Byte) (s : State) : Prop where
  bytes : Spec.Camellia.bytesAt s.mem (State.addr S) (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len)) =
    Spec.Camellia.scheduleBytes (Spec.Camellia.expandKey key)
  frame : Frame [⟨State.addr S, 272⟩] s₈.mem s.mem
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s.gpr r = s₈.gpr r
  rd : s.rd = s₈.rd
  wr : s.wr = s₈.wr
  sp : s.sp = s₈.sp

/-- The stores of one key length's subkeys. -/
theorem stores_wp {s₈ : State} {b S : BitVec 32} {len : Nat} {key : List Byte} {ks : List (Nat × Nat × Bool)}
    (hb : s₈.gpr sb = b) (hw : ScrIn s₈.wr b) (hS : SchedOut s₈ b S) (hks : ∀ k ∈ ks, k.1 < 4 ∧ k.2.1 < 128)
    (hkl : ks.length ≤ 34) (hX : ∀ v < 4, NumOf s₈ (valSlot v) (valNum key v))
    (hlen : 8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len) = 8 * ks.length)
    (hks' : ks = if key.length = 16 then Impl.Camellia.subkeys128 else Impl.Camellia.subkeys256) :
    WP isa (.block (storeSubkeys ks)) s₈ (StoresPost s₈ b S len key) := by
  obtain ⟨s₉, e₉, b₉, f₉, g₉, rd₉, wr₉, sp₉⟩ := stores_ok (X := valNum key) ks 0 s₈ hb hw hS hks (by omega_using [hkl]) hX
  refine WP.of_runBlock ⟨s₉, e₉, ⟨?_, ?_, g₉, rd₉, wr₉, sp₉⟩⟩
  · rw [hlen, schedule_of_stores (vs := keyVals key) (H := fun v => hiW ((keyVals key).getD v 0))
      (L := fun v => loW ((keyVals key).getD v 0)) (fun k hk => (hks k hk).1) (fun v _ => ⟨rfl, rfl⟩)
      (fun i hi j hj => by
        rw [b₉ i hi j hj]
        have hmem : ks.getD i (0, 0, true) ∈ ks := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
          exact List.getElem_mem hi
        have hk := hks _ hmem
        simp only [subHalf, valNum]
        split
        · rename_i h; rw [hi_eq _ _ hk.2, h]
        · rename_i h; rw [lo_eq _ _ hk.2]; simp only [Bool.not_eq_true] at h; rw [h]),
      Spec.Camellia.scheduleBytes, Proof.Camellia.scheduleWords_expandKey, ← hks']
    rfl
  · exact f₉.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Nat.mul_zero]
      exact VG.Offset.sub_base _ (by omega_using [hkl])⟩

/-- After `KA` and `KB`: the four values in their slots, the schedule's
pointer and the key's length in theirs. -/
structure KeyMid (s₀ : State) (b : BitVec 32) (key : List Byte) (s : State) : Prop where
  base : s.gpr sb = b
  scr : ScrIn s.wr b
  vals : ∀ v < 4, VW s (valSlot v) (hiW ((keyVals key).getD v 0), loW ((keyVals key).getD v 0))
  d : s.mem.readW (wordAddr b dSlot) 32 = s₀.gpr .r2
  n : s.mem.readW (wordAddr b nSlot) 32 = s₀.gpr .r1
  saved : Saved s₀ b s.mem
  frame : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The prologue, the key, and `KA` and `KB`. -/
theorem ekHead_wp {s₀ : State} (hp : expandKeyArm.pre s₀) {c : Prog isa} {Q : State → Prop}
    (hcont : ∀ s, KeyMid s₀ (s₀.gpr .r3)
      (Spec.Camellia.bytesAt s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) s → WP isa c s Q) :
    WP isa (.seq (.block (saveRegs .r3 ++ [movR sb .r3, stS dSlot .r2, stS nSlot .r1] ++
        (Impl.Camellia.sigmas.zipIdx.flatMap fun (x, e) => sigmaOne e x)))
      (.seq loadKey (.seq (.block [slotAddr kp keySlot]) (.seq kaKb c)))) s₀ Q := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB, hlen⟩ := hp
  generalize hb : s₀.gpr .r3 = b at fitB dKB dSB hwr hcont
  generalize hK : s₀.gpr .r0 = K at fitK dKB dKS hrd hcont
  generalize hL : (s₀.gpr .r1).toNat = len at fitK dKB dKS hrd hlen hcont
  have hw : ScrIn s₀.wr b := ⟨by rw [hwr]; simp, fitB⟩
  have hfitB := fitB
  rw [slots_eq] at hfitB
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, d₁, n₁, ent₁, f₁, rd₁, wr₁, sp₁⟩ := ekPrologue_ok hb hw
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hk₁ : KeyIn s₁ b K len := ⟨b₁, ⟨by rw [wr₁]; exact hw.mem, fitB⟩, by rw [g₁ _ (by decide) (by decide), hK],
    by rw [rd₁, hrd]; simp, fitK, dKB, by omega_using [hlen]⟩
  have hkey : Spec.Camellia.bytesAt s₁.mem (State.addr K) len = Spec.Camellia.bytesAt s₀.mem (State.addr K) len :=
    Proof.Camellia.bytesAt_congr fun i hi => f₁.bytes (R := ⟨State.addr K, len⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKB) (by simp only; omega_using [hL]) hi
  -- `KL` and `KR`.
  refine WP.seq (WP.mono (loadKey_wp hk₁ hlen (by rw [g₁ _ (by decide) (by decide), ← hL]; simp)) fun s₂ h₂ => ?_)
  have hb₂ : s₂.gpr sb = b := by rw [h₂.regs _ (by decide) (by decide), b₁]
  let s₃ := s₂.setReg kp (s₂.gpr sb + BitVec.ofNat 32 (4 * keySlot))
  have e₃ : runBlock isa [slotAddr kp keySlot] s₂ = some s₃ := by
    rw [runBlock_cons, slotAddr, exec_addImm (by decide), runStep_some, runBlock_nil]
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have hb₃ : s₃.gpr sb = b := by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), hb₂]
  have hs₃ : ∀ k, slotW s₃ k = s₂.mem.readW (wordAddr b k) 32 := fun k => by
    rw [slotW, hb₃]; rfl
  -- The constants' table.
  have hkc : KeyCtx s₃ 6 sigE := by
    refine ⟨⟨by rw [hb₃, RegUpd.wr_setReg, h₂.wr, wr₁]; exact hw.mem, by rw [hb₃]; exact fitB⟩, by decide,
      fun i hi => (sigma_rel (sigE i)).congr fun j hj => ?_⟩
    rw [entryW_slot, hs₃, h₂.keep _ (by rw [keySlot_eq, slots_eq]; omega_using [hi, hj])
      (.inl (by rw [keySlot_eq, klSlot_eq]; omega_using [hi, hj])), ← ent₁ i hi j hj]
    rfl
  -- `KA` and `KB`.
  let key := Spec.Camellia.bytesAt s₁.mem (State.addr K) len
  obtain ⟨hKL1, hKL2, hKR1, hKR2⟩ := klkr_halves s₁.mem (State.addr K) hlen
  have vl : VW s₃ klSlot (hiW (Spec.Camellia.klkr key).1, loW (Spec.Camellia.klkr key).1) := by
    rw [hKL1, hKL2]; exact h₂.kl.congr fun j hj => slotW_setReg _ _ (by decide) _
  have vr : VW s₃ krSlot (hiW (Spec.Camellia.klkr key).2, loW (Spec.Camellia.klkr key).2) := by
    rw [hKR1, hKR2]; exact h₂.kr.congr fun j hj => slotW_setReg _ _ (by decide) _
  refine WP.seq (WP.mono (WP.sp (kaKb_wp hkc (by rw [AtEntry, RegUpd.gpr_setReg_self, hb₃, hb₂]; simp) vl vr))
    fun s₄ ⟨h₄, sp₄⟩ => hcont s₄ ?_)
  have hc := h₄.ctx
  have hb₄ : s₄.gpr sb = b := by rw [hc.base, hb₃]
  have keep₄ : ∀ k < slots, keySlot ≤ k → k ≠ grpSlot → k < tailSlot →
      s₄.mem.readW (wordAddr b k) 32 = s₁.mem.readW (wordAddr b k) 32 := fun k hk h1 h2 h3 => by
    have := hc.slot (by rw [hb₃]; exact fitB) hk h1 h2 (.inl h3)
    rw [slotW, hb₄, hs₃] at this
    rw [this, h₂.keep k hk (.inl (by rw [klSlot_eq]; rw [tailSlot_eq] at h3; omega_using [h3]))]
  have hka := kaD_eq (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2
  have hkey' : key = Spec.Camellia.bytesAt s₀.mem (State.addr K) len := hkey
  rw [← hkey']
  refine ⟨hb₄, ⟨by rw [hc.wr, RegUpd.wr_setReg, h₂.wr, wr₁]; exact hw.mem, fitB⟩, fun v hv => ?_,
    by rw [keep₄ _ (by decide) (by decide) (by decide) (by decide), d₁],
    by rw [keep₄ _ (by decide) (by decide) (by decide) (by decide), n₁],
    fun i hi => ?_, ?_, by rw [hc.rd, RegUpd.rd_setReg, h₂.rd, rd₁], by rw [hc.wr, RegUpd.wr_setReg, h₂.wr, wr₁],
    by rw [sp₄, RegUpd.sp_setReg, h₂.sp, sp₁]⟩
  · rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_using [hv]) with rfl | rfl | rfl | rfl
    · exact h₄.kl
    · exact h₄.kr
    · have := h₄.ka; rw [hka.1] at this; exact this
    · have := h₄.kb; rw [hka.2] at this; exact this
  · rw [keep₄ _ (by rw [savedSlot_eq, slots_eq]; omega_using [hi]) (by rw [savedSlot_eq, keySlot_eq]; omega_using [])
      (by rw [savedSlot_eq, grpSlot_eq]; omega_using []) (by rw [savedSlot_eq, tailSlot_eq]; omega_using [hi])]
    exact sv₁ i hi
  · have f₃ : Frame [⟨State.addr b, 4 * slots⟩] s₃.mem s₄.mem := by
      have := hc.frame; rw [hb₃] at this
      exact this.sub fun r hr => ⟨_, List.mem_singleton_self _, ctx_sub_scr fitB r hr⟩
    exact f₁.trans (h₂.frame.trans f₃)


theorem saved_not_rev : ∀ i < 9, savedSlot + i ∉ revSlots := by decide +kernel

/-- The values byte-swapped, the subkeys stored, the registers restored. -/
theorem ekTail_wp {s₀ s : State} {b S : BitVec 32} {key : List Byte} {len : Nat} (h : KeyMid s₀ b key s)
    (hS2 : s₀.gpr .r2 = S) (hSw : (⟨State.addr S, 272⟩ : Region) ∈ s₀.wr) (hSf : S.toNat + 272 ≤ 2 ^ 32)
    (hSd : Region.Disjoint ⟨State.addr S, 272⟩ ⟨State.addr b, 4 * slots⟩) (hr1 : s₀.gpr .r1 = BitVec.ofNat 32 len)
    (hlen : len = 16 ∨ len = 24 ∨ len = 32) (hkl : key.length = len) :
    WP isa (.seq (.block (revValues ++ [ldS .r2 dSlot, ldS t0 nSlot, .cmp t0 (.imm 16)]))
      (.seq (.ite .eq (.block (storeSubkeys Impl.Camellia.subkeys128)) (.block (storeSubkeys Impl.Camellia.subkeys256)))
        (.block ([movR .r12 sb] ++ restoreRegs .r12)))) s fun s' =>
      (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      Spec.Camellia.bytesAt s'.mem (State.addr S) (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len)) =
        Spec.Camellia.scheduleBytes (Spec.Camellia.expandKey key) := by
  have hfit := h.scr.fit
  obtain ⟨hnd, hlt⟩ := revSlots_facts
  -- The values, byte-swapped.
  obtain ⟨s₁, e₁, v₁, k₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := revs_ok revSlots (s := s) h.base h.scr hnd hlt
  have hb₁ : s₁.gpr sb = b := by rw [g₁ _ (by decide), h.base]
  have hX₁ : ∀ v < 4, NumOf s₁ (valSlot v) (valNum key v) := fun v hv => by
    have := num_of_rev (s' := s₁) (h.vals v hv) fun j hj => by
      simp only [slotW]
      rw [hb₁, h.base, v₁ (valSlot v + j) (mem_revSlots hv hj)]
    dsimp only at this
    exact this
  -- The schedule's pointer and the key's length.
  have hw₁ : ScrIn s₁.wr b := ⟨by rw [wr₁]; exact h.scr.mem, hfit⟩
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := ldSlot_ok s₁ .r2 sb (k := dSlot) hb₁ (by decide) hw₁
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := ldSlot_ok s₂ t0 sb (k := nSlot) (by rw [o₂ _ (by decide), hb₁])
    (by decide) (by rw [wr₂]; exact hw₁)
  let s₄ := subFlags s₃ (s₃.gpr t0) 16
  have e₄ := cmpImm_ok s₃ t0 (v := 16) (by decide)
  have hz₄ : s₄.z = decide (len = 16) := by
    rw [subFlags_z, v₃, m₂, k₁ nSlot (by decide) (by decide), h.n, hr1, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      ofNat32_sub_beq (by omega_using [hlen]) (by decide)]
  have hb₄ : s₄.gpr sb = b := by rw [subFlags_gpr, o₃ _ (by decide), o₂ _ (by decide), hb₁]
  have hm₄ : s₄.mem = s₁.mem := by rw [subFlags_mem, m₃, m₂]
  have hr2₄ : s₄.gpr .r2 = S := by
    rw [subFlags_gpr, o₃ _ (by decide), v₂, k₁ dSlot (by decide) (by decide), h.d, hS2]
  have wr₄ : s₄.wr = s.wr := by rw [subFlags_wr, wr₃, wr₂, wr₁]
  have hw₄ : ScrIn s₄.wr b := ⟨by rw [wr₄]; exact h.scr.mem, hfit⟩
  have hS₄ : SchedOut s₄ b S := ⟨hr2₄, by rw [wr₄, h.wr]; exact hSw, hSf, hSd⟩
  have hX₄ : ∀ v < 4, NumOf s₄ (valSlot v) (valNum key v) := fun v hv => (hX₁ v hv).congr fun j hj => by
    simp only [slotW, hb₄, hb₁, hm₄]
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [runBlock_app, revValues_eq, e₁, Option.bind_some, show ([ldS .r2 dSlot, ldS t0 nSlot, .cmp t0 (.imm 16)] :
      List Instr) = [.ldr .r2 sb (4 * dSlot)] ++ ([.ldr t0 sb (4 * nSlot)] ++ [.cmp t0 (.imm 16)]) from rfl,
      runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄], ?_⟩)
  -- The subkeys.
  have hk128 : ∀ k ∈ Impl.Camellia.subkeys128, k.1 < 4 ∧ k.2.1 < 128 := by decide
  have hk256 : ∀ k ∈ Impl.Camellia.subkeys256, k.1 < 4 ∧ k.2.1 < 128 := by decide
  refine WP.seq (WP.mono (Q := StoresPost s₄ b S len key)
    (WP.ite (decide (len = 16)) ((eval_eq s₄).trans (by rw [hz₄])) (fun h16 => ?_) (fun h16 => ?_))
    fun s₅ h₅ => ?_)
  · have h16 : len = 16 := by simpa using h16
    exact stores_wp hb₄ hw₄ hS₄ hk128 (by rw [subkeys_length.1]; omega_using []) hX₄
      (by rw [h16, subkeys_length.1]; rfl) (by rw [hkl, ite_eq_left h16])
  · have h16 : len ≠ 16 := by simpa using h16
    exact stores_wp hb₄ hw₄ hS₄ hk256 (by rw [subkeys_length.2]) hX₄
      (by rw [subkeys_length.2]; simp only [Spec.Camellia.rounds, h16, ↓reduceIte]; rfl)
      (by rw [hkl, ite_eq_right h16])
  -- The epilogue.
  have hb₅ : s₅.gpr sb = b := by rw [h₅.regs _ (by decide) (by decide), hb₄]
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := movR_ok s₅ .r12 sb
  have hsv : Saved s₀ b s₆.mem := fun i hi => by
    rw [m₆, hS₄.slot hfit h₅.frame (fun _ h => h) (by rw [savedSlot_eq, slots_eq]; omega_using [hi]), hm₄,
      k₁ (savedSlot + i) (by rw [savedSlot_eq, slots_eq]; omega_using [hi]) (saved_not_rev i hi)]
    exact h.saved i hi
  obtain ⟨s₇, e₇, rg₇, -, m₇, -, -, -⟩ := restore_ok (s₀ := s₀) (b := b)
    ⟨by rw [wr₆, h₅.wr, wr₄]; exact h.scr.mem, hfit⟩ (by rw [r₆, hb₅]) hsv
  refine WP.of_runBlock ⟨s₇, by rw [runBlock_app, e₆, Option.bind_some, e₇], rg₇, ?_⟩
  rw [m₇, m₆]
  exact h₅.bytes

theorem expandKey_wp {s₀ : State} (hp : expandKeyArm.pre s₀) :
    WP isa expandKey s₀ fun s' => (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ expandKeyArm.post s₀ s' := by
  have hp' := hp
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB, hlen⟩ := hp'
  unfold expandKey
  refine ekHead_wp hp fun s h => ?_
  exact ekTail_wp h rfl (by rw [hwr]; simp) fitS dSB (by simp) hlen (by simp [Spec.Camellia.bytesAt])

end VG.Proof.Camellia.Arm
