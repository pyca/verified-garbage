module
public import VerifiedGarbage.Proof.Camellia.X86.KeyPair

import VerifiedGarbage.Proof.Camellia.X86.Prologue
import VerifiedGarbage.Proof.Camellia.X86.Fl
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Camellia's key schedule on x86 (32-bit): the subkeys' stores

As on ARMv7 (`Proof/Camellia/Arm/KeyStore.lean`): `revs_ok`, the values'
words byte-swapped in place, which makes them the 32-bit words of the
128-bit values, the most significant first (`NumOf`, `num_of_rev`).
`rotWord_ok`: a word of a value rotated left, from two of its words.
`stores_ok`: each subkey, the high or low half of a rotated value,
byte-swapped and stored at `edx`, so that its bytes are those of `rotHalf`
(as `schedule_of_stores` takes them).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb tmpRegs slotAt st movS at_ rorI shrI andI)
open VG.Proof.Camellia (byteOf getLsbD_byteOf hiW loW rotHalf hi_split lo_split hiW_append loW_append)

/-! ## Bytes -/

theorem bswap_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (bswap v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  unfold bswap
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals first | omega_arith | (rw [decide_eq_true (by omega_arith), Bool.true_and]; congr 1; omega_arith)

theorem st_byte (m : Mem) (a : Addr) (v : BitVec 32) {t : Nat} (ht : t < 4) :
    m.writeW a v (a + BitVec.ofNat 64 t) = v.extractLsb' (8 * t) 8 := by
  rw [Mem.readW_byte (m.writeW a v) a ht, Mem.readW_writeW_self32]

theorem writeW32_other {m : Mem} {a x : Addr} (v : BitVec 32) (h : Region.Disjoint ⟨x, 1⟩ ⟨a, 4⟩) :
    m.writeW a v x = m x :=
  Mem.write_apply fun hx => h x (Region.contains_self _ _) (by simp only [Region.Contains]; omega_arith)

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
    (h : ∀ j < 4, slotW s' (a + j) = bswap (slotW s (a + j))) : NumOf s' a (v.1 ++ v.2) := by
  intro j hj
  rw [h j hj]
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  obtain ⟨k, t, hk, ht, rfl⟩ : ∃ k t, k < 4 ∧ t < 8 ∧ p = 8 * k + t := ⟨p / 8, p % 8, by omega_arith, by omega_arith, by omega_arith⟩
  rw [bswap_bit _ hk ht, numWord_bit _ hj hp]
  have := hv (4 * j + (3 - k)) (by omega_arith) t ht
  rw [show (4 * j + (3 - k)) / 4 = j by omega_arith, show (4 * j + (3 - k)) % 4 = 3 - k by omega_arith] at this
  rw [this, BitVec.getLsbD_append]
  by_cases h8 : 4 * j + (3 - k) < 8
  · rw [itePos h8, getLsbD_byteOf _ (by omega_arith) ht, iteNeg (show ¬ 96 - 32 * j + (8 * k + t) < 64 by omega_arith)]
    congr 1; omega_arith
  · rw [iteNeg h8, getLsbD_byteOf _ (by omega_arith) ht, itePos (show 96 - 32 * j + (8 * k + t) < 64 by omega_arith)]
    congr 1; omega_arith

/-! ## Byte swaps in place -/

/-- `mov eax, [edi + 4 k]; bswap eax; mov [edi + 4 k], eax` for each `k` of `L`. -/
theorem revs_ok {b : BitVec 32} : ∀ (L : List Nat) {s : State}, s.gpr sb = b → ScrIn s.wr b → L.Nodup →
    (∀ k ∈ L, k < slots) →
    ∃ s', runBlock isa (L.flatMap fun k => [movS .eax k, .bswap .eax, st k .eax]) s = some s' ∧
      (∀ k ∈ L, s'.mem.readW (wordAddr b k) 32 = bswap (s.mem.readW (wordAddr b k) 32)) ∧
      (∀ k < slots, k ∉ L → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem
  | [], s, _, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | x :: L, s, hb, hw, hnd, hin => by
    have hx := hin x List.mem_cons_self
    have hfit := hw.fit
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s .eax .edi (k := x) hb hx hw
    let s₂ := s₁.setReg .eax (bswap (s₁.gpr .eax))
    obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, -, -, f₃⟩ := stSlot_ok s₂ .eax .edi (b := b) (k := x)
      (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), o₁ _ (by decide)]; exact hb) hx
      (by rw [RegUpd.wr_setReg, wr₁]; exact hw)
    rw [List.nodup_cons] at hnd
    obtain ⟨s', e', v', k', g', rd', wr', f'⟩ := revs_ok (b := b) L (s := s₃)
      (by rw [show s₃.gpr sb = s₂.gpr sb from congrFun g₃ sb, RegUpd.gpr_setReg_of_ne _ _ (by decide),
        o₁ _ (by decide)]; exact hb)
      (by rw [wr₃, RegUpd.wr_setReg, wr₁]; exact hw) hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    have hslot : ∀ j < slots, s₃.mem.readW (wordAddr b j) 32 = if j = x then
        bswap (s.mem.readW (wordAddr b x) 32) else s.mem.readW (wordAddr b j) 32 := fun j hj => by
      rw [m₃, readW_slot_write hfit _ hj hx, RegUpd.gpr_setReg_self, v₁, RegUpd.mem_setReg, m₁]
    refine ⟨s', ?_, fun y hy => ?_, fun j hj hn => ?_, fun r hr => by
        rw [g' r hr, g₃, RegUpd.gpr_setReg_of_ne _ _ hr, o₁ r hr],
      by rw [rd', rd₃, RegUpd.rd_setReg, rd₁], by rw [wr', wr₃, RegUpd.wr_setReg, wr₁], ?_⟩
    · rw [List.flatMap_cons, runBlock_app, show ([movS .eax x, .bswap .eax, st x .eax] : List Instr) =
        [.mov .eax (.mem (slotAt .edi x))] ++ ([.bswap .eax] ++ [.store (slotAt .edi x) .eax]) from rfl,
        runBlock_app, e₁, Option.bind_some, runBlock_app, runBlock_cons, show exec (.bswap .eax) s₁ = some s₂ from rfl,
        runStep_some, runBlock_nil, Option.bind_some, e₃, Option.bind_some]
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

theorem revValues_eq : revValues = revSlots.flatMap fun k => [movS .eax k, .bswap .eax, st k .eax] := rfl

theorem revSlots_facts : revSlots.Nodup ∧ (∀ k ∈ revSlots, k < slots) := by
  constructor <;> decide

theorem mem_revSlots {v k : Nat} (hv : v < 4) (hk : k < 4) : valSlot v + k ∈ revSlots := by
  simp only [revSlots, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨v, by omega_arith, k, hk, rfl⟩

/-! ## Rotations -/

theorem rotr_mask (x : BitVec 32) {s : Nat} (h1 : 1 ≤ s) (h2 : s ≤ 31) :
    x.rotateRight (32 - s) &&& (BitVec.allOnes 32 <<< s) = x <<< s := by
  apply BitVec.eq_of_getLsbD_eq; intro p hp
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_rotateRight]
  simp only [hp, decide_true, Bool.true_and, show (32 - s) % 32 = 32 - s by omega_arith]
  by_cases hps : p < s
  · simp [hps]
  · simp only [hps, decide_false, Bool.not_false, Bool.true_and, show ¬ p < 32 - (32 - s) by omega_arith, ↓reduceIte,
      decide_eq_true (show p - s < 32 by omega_arith), Bool.and_true]
    congr 1; omega_arith

/-- Word `o` of value `v` rotated left by `r`, in `eax`. -/
theorem rotWord_ok {s : State} {b : BitVec 32} (hb : s.gpr sb = b) (hw : ScrIn s.wr b) {v r o : Nat}
    (hv : v < 4) (hr : r < 128) (ho : o < 4) {x : BitVec 128} (hx : NumOf s (valSlot v) x) :
    ∃ s', runBlock isa (rotWord v r o) s = some s' ∧ s'.gpr .eax = numWord (x.rotateLeft r) o ∧
      (∀ r', r' ≠ .eax → r' ≠ .ebx → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hvs : valSlot v + 4 ≤ slots := valSlot_lt v hv
  have hW : ∀ j < 4, s.mem.readW (wordAddr b (valSlot v + j)) 32 = numWord x j := fun j hj => by
    rw [← hb]; exact hx j hj
  unfold rotWord
  dsimp only
  split
  · rename_i h0
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s .eax .edi (k := valSlot v + (o + r / 32) % 4) hb
      (by omega_arith) hw
    refine ⟨s₁, e₁, ?_, fun r' h1 _ => o₁ r' h1, m₁, rd₁, wr₁⟩
    rw [v₁, hW _ (by omega_arith)]
    apply BitVec.eq_of_getLsbD_eq; intro p hp
    rw [numWord_bit _ (by omega_arith) hp, numWord_bit _ ho hp, rotl_bit _ hr (by omega_arith)]
    congr 1; omega_arith
  · rename_i h0
    have hs1 : 1 ≤ r % 32 ∧ r % 32 ≤ 31 := by omega_arith
    have hs2 : 1 ≤ 32 - r % 32 ∧ 32 - r % 32 ≤ 31 := by omega_arith
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s .eax .edi (k := valSlot v + (o + r / 32) % 4) hb
      (by omega_arith) hw
    obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, -, -⟩ := ldSlot_ok s₁ .ebx .edi (b := b)
      (k := valSlot v + (o + r / 32 + 1) % 4) (by rw [o₁ _ (by decide)]; exact hb) (by omega_arith) (by rw [wr₁]; exact hw)
    let W1 := s₂.gpr .eax
    let W2 := s₂.gpr .ebx
    let a₃ := W1.rotateRight (32 - r % 32)
    let s₃ := (s₂.setFlags (some a₃.msb) (if 32 - r % 32 = 1 then some (a₃.msb ^^ a₃.getMsbD 1) else none)
      s₂.zf s₂.sf).setReg .eax a₃
    have e₃ : runBlock isa [rorI .eax (32 - r % 32)] s₂ = some s₃ := by
      simp only [rorI, runBlock_cons, exec, execShift, hs2, and_self, ↓reduceIte, runStep_some, runBlock_nil]
      rfl
    let a₄ := s₃.gpr .eax &&& (BitVec.allOnes 32 <<< (r % 32))
    let s₄ := (arithFlags s₃ a₄ false false).setReg .eax a₄
    have e₄ : runBlock isa [andI .eax (BitVec.allOnes 32 <<< (r % 32))] s₃ = some s₄ := rfl
    let a₅ := s₄.gpr .ebx >>> (32 - r % 32)
    let s₅ := (s₄.setFlags (some ((s₄.gpr .ebx).getLsbD (32 - r % 32 - 1)))
      (if 32 - r % 32 = 1 then some (s₄.gpr .ebx).msb else none) (some (a₅ == 0)) (some a₅.msb)).setReg .ebx a₅
    have e₅ : runBlock isa [shrI .ebx (32 - r % 32)] s₄ = some s₅ := by
      simp only [shrI, runBlock_cons, exec, execShift, hs2, and_self, ↓reduceIte, runStep_some, runBlock_nil]
      rfl
    let a₆ := s₅.gpr .eax ||| s₅.gpr .ebx
    let s₆ := (arithFlags s₅ a₆ false false).setReg .eax a₆
    have e₆ : runBlock isa [.alu .or .eax (.reg .ebx)] s₅ = some s₆ := rfl
    have hg : ∀ r', r' ≠ .eax → r' ≠ .ebx → s₆.gpr r' = s₂.gpr r' := fun r' h1 h2 => by
      simp only [s₆, s₅, s₄, s₃, RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_setReg_of_ne _ _ h2,
        RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags]
    refine ⟨s₆, ?_, ?_, fun r' h1 h2 => by rw [hg r' h1 h2, o₂ r' h2, o₁ r' h1],
      by show s₂.mem = _; rw [m₂, m₁], by show s₂.rd = _; rw [rd₂, rd₁], by show s₂.wr = _; rw [wr₂, wr₁]⟩
    · rw [show ([movS .eax (valSlot v + (o + r / 32) % 4), movS .ebx (valSlot v + (o + r / 32 + 1) % 4),
          rorI .eax (32 - r % 32), andI .eax (BitVec.allOnes 32 <<< (r % 32)), shrI .ebx (32 - r % 32),
          .alu .or .eax (.reg .ebx)] : List Instr) =
          [.mov .eax (.mem (slotAt .edi (valSlot v + (o + r / 32) % 4)))] ++
            ([.mov .ebx (.mem (slotAt .edi (valSlot v + (o + r / 32 + 1) % 4)))] ++ ([rorI .eax (32 - r % 32)] ++
            ([andI .eax (BitVec.allOnes 32 <<< (r % 32))] ++ ([shrI .ebx (32 - r % 32)] ++
              [.alu .or .eax (.reg .ebx)])))) from rfl,
        runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
        runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, e₆]
    · have h6 : s₆.gpr .eax = (W1 <<< (r % 32)) ||| (W2 >>> (32 - r % 32)) := by
        show s₅.gpr .eax ||| s₅.gpr .ebx = _
        rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setFlags, RegUpd.gpr_setReg_self]
        show (s₄.gpr .eax ||| s₄.gpr .ebx >>> (32 - r % 32)) = _
        rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_arithFlags]
        show (s₃.gpr .eax &&& _) ||| s₃.gpr .ebx >>> _ = _
        rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setFlags,
          rotr_mask _ hs1.1 hs1.2]
      rw [h6]
      show (s₂.gpr .eax <<< (r % 32)) ||| (s₂.gpr .ebx >>> (32 - r % 32)) = _
      rw [o₂ _ (by decide), v₁, v₂, m₁, hW _ (by omega_arith), hW _ (by omega_arith)]
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

/-- The schedule at `S` (in `edx`), writable, apart from the scratch buffer at `b`. -/
structure SchedOut (s : State) (b S : BitVec 32) : Prop where
  edx : s.gpr .edx = S
  wr : (⟨S.setWidth 64, 272⟩ : Region) ∈ s.wr
  fit : S.toNat + 272 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨S.setWidth 64, 272⟩ ⟨b.setWidth 64, 4 * slots⟩

theorem SchedOut.congr {s s' : State} {b S : BitVec 32} (h : SchedOut s b S) (h2 : s'.gpr .edx = s.gpr .edx)
    (hwr : s'.wr = s.wr) : SchedOut s' b S := ⟨h2.trans h.edx, hwr ▸ h.wr, h.fit, h.sep⟩

/-- A slot, kept by a frame of the schedule. -/
theorem SchedOut.slot {s : State} {b S : BitVec 32} (h : SchedOut s b S) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {m m' : Mem} {R : Region} (hf : Frame [R] m m') (hR : Region.Sub R ⟨S.setWidth 64, 272⟩) {k : Nat}
    (hk : k < slots) : m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((h.sep.sub_left hR).symm.sub_left (slot_sub hfit hk))) (by decide)

/-- Word `o` of value `v` rotated left by `r`, byte-swapped and stored at `S + off`. -/
theorem wordStore_ok {s : State} {b S : BitVec 32} (hb : s.gpr sb = b) (hw : ScrIn s.wr b) (hS : SchedOut s b S)
    {v r o off : Nat} (hv : v < 4) (hr : r < 128) (ho : o < 4) (hoff : off + 4 ≤ 272) {x : BitVec 128}
    (hx : NumOf s (valSlot v) x) :
    ∃ s', runBlock isa (rotWord v r o ++ ([.bswap .eax, .store (at_ .edx off) .eax] : List Instr)) s = some s' ∧
      s'.mem = s.mem.writeW (S.setWidth 64 + BitVec.ofNat 64 off) (bswap (numWord (x.rotateLeft r) o)) ∧
      (∀ r', r' ≠ .eax → r' ≠ .ebx → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := rotWord_ok hb hw hv hr ho hx
  let s₂ := s₁.setReg .eax (bswap (s₁.gpr .eax))
  have ea : s₂.ea (at_ .edx off) = S.setWidth 64 + BitVec.ofNat 64 off := by
    rw [at_, ea_mk, RegUpd.gpr_setReg_of_ne _ _ (by decide), o₁ _ (by decide) (by decide), hS.edx,
      addr_eq (by have := hS.fit; omega_arith)]
  have hin : InRegions s₂.wr (s₂.ea (at_ .edx off)) 4 := by
    rw [ea]
    exact ⟨_, by rw [RegUpd.wr_setReg, wr₁]; exact hS.wr,
      VG.Offset.contains_base _ (by omega_arith) (by have := hS.fit; have := setWidth_toNat S; omega_arith)⟩
  refine ⟨{ s₂ with mem := s₂.mem.writeW (s₂.ea (at_ .edx off)) (s₂.gpr .eax) }, ?_, ?_,
    fun r' h1 h2 => by
      show (s₁.setReg .eax _).gpr r' = _
      rw [RegUpd.gpr_setReg_of_ne _ _ h1, o₁ r' h1 h2], by rw [← rd₁]; rfl, by rw [← wr₁]; rfl⟩
  · rw [runBlock_app, e₁, Option.bind_some, runBlock_cons, show exec (.bswap .eax) s₁ = some s₂ from rfl,
      runStep_some, runBlock_cons, show exec (.store (at_ .edx off) .eax) s₂ =
        some { s₂ with mem := s₂.mem.writeW (s₂.ea (at_ .edx off)) (s₂.gpr .eax) } by
        show s₂.store32 _ _ = _; simp only [State.store32, hin, ↓reduceIte], runStep_some, runBlock_nil]
  · show s₂.mem.writeW _ _ = _
    rw [ea, RegUpd.gpr_setReg_self, v₁, RegUpd.mem_setReg, m₁]

/-- The bytes of a stored word: the half's bytes `4 k … 4 k + 3`. -/
theorem stored_byte (x : BitVec 128) (r : Nat) (hi : Bool) {k q : Nat} (hk : k < 2) (hq : q < 4) :
    (bswap (numWord (x.rotateLeft r) ((if hi then 0 else 2) + k))).extractLsb' (8 * q) 8 =
      byteOf (if hi then Spec.Camellia.hi x r else Spec.Camellia.lo x r) (4 * k + q) := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [BitVec.getLsbD_extractLsb', getLsbD_byteOf _ (by omega_arith) ht, bswap_bit _ hq ht,
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
      (∀ j < 8, s'.mem (S.setWidth 64 + BitVec.ofNat 64 (8 * i + j)) =
        byteOf (if hi then Spec.Camellia.hi x r else Spec.Camellia.lo x r) j) ∧
      Frame [⟨S.setWidth 64 + BitVec.ofNat 64 (8 * i), 8⟩] s.mem s'.mem ∧
      (∀ r', r' ≠ .eax → r' ≠ .ebx → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit := hw.fit
  have hSf := hS.fit
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := wordStore_ok hb hw hS hv hr (o := (if hi then 0 else 2) + 0)
    (off := 8 * i + 4 * 0) (by split <;> omega_arith) (by omega_arith) hx
  have sub0 : Region.Sub ⟨S.setWidth 64 + BitVec.ofNat 64 (8 * i + 4 * 0), 4⟩ ⟨S.setWidth 64, 272⟩ :=
    VG.Offset.sub_base _ (by omega_arith)
  have hx₁ : NumOf s₁ (valSlot v) x := hx.congr fun j hj => by
    simp only [slotW]
    rw [g₁ _ (by decide) (by decide), hb, m₁]
    have hj' : valSlot v + j < slots := by have := valSlot_lt v hv; omega_arith
    exact hS.slot hfit ((Frame.refl _ s.mem).writeW (r := ⟨S.setWidth 64 + BitVec.ofNat 64 (8 * i + 4 * 0), 4⟩)
      (List.mem_singleton_self _) (bswap (numWord (x.rotateLeft r) ((if hi then 0 else 2) + 0)))
      (Region.contains_self _ _)) sub0 hj'
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := wordStore_ok (by rw [g₁ _ (by decide) (by decide), hb])
    (by rw [wr₁]; exact hw) (hS.congr (g₁ _ (by decide) (by decide)) wr₁) hv hr
    (o := (if hi then 0 else 2) + 1) (off := 8 * i + 4 * 1) (by split <;> omega_arith) (by omega_arith) hx₁
  refine ⟨s₂, ?_, fun j hj => ?_, ?_, fun r' h1 h2 => by rw [g₂ r' h1 h2, g₁ r' h1 h2],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [subkey, show ([0, 1] : List Nat).flatMap (fun k => rotWord v r ((if hi then 0 else 2) + k) ++
        [.bswap .eax, .store (at_ .edx (8 * i + 4 * k)) .eax]) =
        (rotWord v r ((if hi then 0 else 2) + 0) ++ [.bswap .eax, .store (at_ .edx (8 * i + 4 * 0)) .eax]) ++
        (rotWord v r ((if hi then 0 else 2) + 1) ++ [.bswap .eax, .store (at_ .edx (8 * i + 4 * 1)) .eax]) by simp,
      runBlock_app, e₁, Option.bind_some, e₂]
  · rw [m₂]
    by_cases h4 : j < 4
    · rw [writeW32_other _ (VG.Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)), m₁]
      have h0 := st_byte s.mem (S.setWidth 64 + BitVec.ofNat 64 (8 * i + 4 * 0))
        (bswap (numWord (x.rotateLeft r) ((if hi then 0 else 2) + 0))) h4
      rw [VG.Offset.add_add, show 8 * i + 4 * 0 + j = 8 * i + j by omega_arith] at h0
      rw [h0, stored_byte x r hi (k := 0) (q := j) (by decide) h4, show 4 * 0 + j = j by omega_arith]
    · have h1 := st_byte s₁.mem (S.setWidth 64 + BitVec.ofNat 64 (8 * i + 4 * 1))
        (bswap (numWord (x.rotateLeft r) ((if hi then 0 else 2) + 1))) (t := j - 4) (by omega_arith)
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
      (∀ i < ks.length, ∀ j < 8, s'.mem (S.setWidth 64 + BitVec.ofNat 64 (8 * (n + i) + j)) =
        byteOf (subHalf X (ks.getD i (0, 0, true))) j) ∧
      Frame [⟨S.setWidth 64 + BitVec.ofNat 64 (8 * n), 8 * ks.length⟩] s.mem s'.mem ∧
      (∀ r', r' ≠ .eax → r' ≠ .ebx → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], _, s, _, _, _, _, _, _ => ⟨s, rfl, fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _,
      fun _ _ _ => rfl, rfl, rfl⟩
  | (v, r, hi) :: ks, n, s, hb, hw, hS, hks, hlen, hX => by
    have hfit := hw.fit
    have hSf := hS.fit
    simp only [List.length_cons] at hlen
    obtain ⟨hv, hr⟩ := hks _ List.mem_cons_self
    obtain ⟨s₁, e₁, b₁, f₁, g₁, rd₁, wr₁⟩ := subkey_ok (i := n) (hi := hi) hb hw hS hv hr (by omega_arith) (hX v hv)
    have hsub : Region.Sub ⟨S.setWidth 64 + BitVec.ofNat 64 (8 * n), 8⟩ ⟨S.setWidth 64, 272⟩ :=
      VG.Offset.sub_base _ (by omega_arith)
    have hX₁ : ∀ u < 4, NumOf s₁ (valSlot u) (X u) := fun u hu => (hX u hu).congr fun j hj => by
      simp only [slotW]
      rw [g₁ _ (by decide) (by decide), hb]
      exact hS.slot hfit f₁ hsub (by have := valSlot_lt u hu; omega_arith)
    have hb₁ : s₁.gpr sb = b := by rw [g₁ _ (by decide) (by decide), hb]
    obtain ⟨s', e', b', f', g', rd', wr'⟩ := stores_ok (b := b) ks (n + 1) s₁ hb₁ (by rw [wr₁]; exact hw)
      (hS.congr (g₁ _ (by decide) (by decide)) wr₁) (fun k hk => hks k (List.mem_cons_of_mem _ hk))
      (by omega_arith) hX₁
    refine ⟨s', ?_, fun i hi j hj => ?_, ?_, fun r' h1 h2 => by rw [g' r' h1 h2, g₁ r' h1 h2],
      by rw [rd', rd₁], by rw [wr', wr₁]⟩
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

end VG.Proof.Camellia.X86
