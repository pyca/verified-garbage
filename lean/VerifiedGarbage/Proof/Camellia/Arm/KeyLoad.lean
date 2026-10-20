module
public import VerifiedGarbage.Proof.Camellia.Arm.KeyPair
public import VerifiedGarbage.Proof.Camellia.Arm.Prologue

import VerifiedGarbage.Proof.Camellia.Arm.Copy
import VerifiedGarbage.Proof.Camellia.Layout32
import VerifiedGarbage.Proof.Camellia.Arm.Fl
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
  · rw [iteNeg h8, show a + c / 4 = a + 2 + (c - 8) / 4 by omega, show c % 4 = (c - 8) % 4 by omega,
      show c % 8 = c - 8 by omega]
    exact h2 (c - 8) (by omega) j hj

/-- Two words loaded from `A` and `A + 4`. -/
theorem HW_words {s : State} {a : Nat} {m : Mem} {A : Addr} (h0 : slotW s a = m.readW A 32)
    (h1 : slotW s (a + 1) = m.readW (A + BitVec.ofNat 64 4) 32) : HW s a (wordAt m A) := by
  intro c hc j hj
  have hw : slotW s (a + c / 4) = m.readW (A + BitVec.ofNat 64 (4 * (c / 4))) 32 := by
    rcases (show c / 4 = 0 ∨ c / 4 = 1 by omega) with h | h <;> rw [h]
    · rw [Nat.add_zero, h0]; simp
    · exact h1
  rw [hw, W32.readW32_bit _ _ (by omega) hj, byteOf_wordAt _ _ hc, VG.Offset.add_add,
    show 4 * (c / 4) + c % 4 = c by omega]

/-- The complements of two words loaded from `A` and `A + 4`. -/
theorem HW_not {s : State} {a : Nat} {m : Mem} {A : Addr} (h0 : slotW s a = m.readW A 32 ^^^ BitVec.allOnes 32)
    (h1 : slotW s (a + 1) = m.readW (A + BitVec.ofNat 64 4) 32 ^^^ BitVec.allOnes 32) :
    HW s a (~~~ wordAt m A) := by
  intro c hc j hj
  have hw : slotW s (a + c / 4) = m.readW (A + BitVec.ofNat 64 (4 * (c / 4))) 32 ^^^ BitVec.allOnes 32 := by
    rcases (show c / 4 = 0 ∨ c / 4 = 1 by omega) with h | h <;> rw [h]
    · rw [Nat.add_zero, h0]; simp
    · exact h1
  rw [hw, BitVec.getLsbD_xor, BitVec.getLsbD_allOnes, getLsbD_byteOf _ hc hj, BitVec.getLsbD_not,
    W32.readW32_bit _ _ (by omega) hj, ← getLsbD_byteOf _ hc hj, byteOf_wordAt _ _ hc, VG.Offset.add_add,
    show 4 * (c / 4) + c % 4 = c by omega]
  simp [show 8 * (c % 4) + j < 32 by omega, show 56 - 8 * c + j < 64 by omega]

theorem HW_zero {s : State} {a : Nat} (h0 : slotW s a = 0) (h1 : slotW s (a + 1) = 0) : HW s a 0 := by
  intro c hc j hj
  have hw : slotW s (a + c / 4) = 0 := by
    rcases (show c / 4 = 0 ∨ c / 4 = 1 by omega) with h | h <;> rw [h]
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
    rw [h.r0, VG.Arm.addr_add (by have := h.fit; omega)]
  refine ⟨e, ⟨_, List.mem_append_left _ h.rd, ?_⟩⟩
  rw [e]; exact VG.Offset.contains_base _ (by omega) (by have := h.fit; omega)

/-- A word of the key, kept by a frame of the scratch buffer. -/
theorem KeyIn.keep {s : State} {b K : BitVec 32} {len : Nat} (h : KeyIn s b K len) {m m' : Mem}
    (hf : Frame [⟨State.addr b, 4 * slots⟩] m m') {o : Nat} (ho : o + 4 ≤ len) :
    m'.readW (State.addr K + BitVec.ofNat 64 o) 32 = m.readW (State.addr K + BitVec.ofNat 64 o) 32 :=
  hf.readW (VG.Offset.contains_base _ (by omega) (by have := h.fit; omega)) (fun r hr => by
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
    have e₁ : exec (.ldr t0 .r0 x.1) s = some s₁ := exec_ldr (by have := hk.le; omega) ei
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
                     rw [krSlot_eq, slots_eq]; omega)
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
  · rw [k₄ k hk' (by simp only [List.mem_map, List.mem_range, not_exists, not_and]; intro j hj h'; omega)]; rfl

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
  · rw [runBlock_cons, exec_ldr (by have := hk.le; omega) ei, runStep_some, runBlock_cons,
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
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, sp₃, f₃⟩ := ldNotSt_ok hk₂ hu (o := 16) (k := krSlot + 2) (by omega) (by decide)
  have hk₃ : KeyIn s₃ b K len := hk₂.congr (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, sp₄, f₄⟩ := ldNotSt_ok hk₃ (by rw [g₃ _ (by decide), hu]) (o := 20)
    (k := krSlot + 3) (by omega) (by decide)
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
  · rw [m₄, Mem.readW_writeW_self32, hk₂.keep f₃ (by omega)]
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
  have h16 : len ≠ 16 := by omega
  obtain ⟨s₃, e₃, v₃, k₃, g₃, rd₃, wr₃, sp₃, f₃⟩ := loads_ok [(16, krSlot), (20, krSlot + 1)] hk (by decide)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact ⟨by omega, by decide⟩)
  let s₄ := subFlags s₃ (s₃.gpr .r1) 24
  have e₄ : exec (.cmp .r1 (.imm 24)) s₃ = some s₄ := by
    simp only [exec, Op2.eval, show encodable (24 : BitVec 32) = true by decide, ↓reduceIte, Option.map_some]
    rfl
  have hz₄ : s₄.z = decide (len = 24) := by
    rw [subFlags_z, g₃ _ (by decide), hr1, show (24 : BitVec 32) = BitVec.ofNat 32 24 from rfl,
      ofNat32_sub_beq (by omega) (by decide)]
  have hk₄ : KeyIn s₄ b K len := hk.congr (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃
  have hm₄ : KeySame s₄ m₀ (State.addr K) len := hm.frame hk f₃
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [show ([.ldr t0 .r0 16, stS krSlot t0, .ldr t0 .r0 20, stS (krSlot + 1) t0, .cmp .r1 (.imm 24)] :
        List Instr) = ([(16, krSlot), (20, krSlot + 1)].flatMap fun (o, k) => [.ldr t0 .r0 o, stS k t0]) ++
          [.cmp .r1 (.imm 24)] from rfl, runBlock_app, e₃, Option.bind_some, runBlock_cons, e₄, runStep_some,
      runBlock_nil], ?_⟩)
  have hl0 : s₄.mem.readW (wordAddr b krSlot) 32 = m₀.readW (State.addr K + BitVec.ofNat 64 16) 32 := by
    rw [show s₄.mem = s₃.mem from rfl, v₃ (16, krSlot) (by simp), hm 16 (by omega)]
  have hl1 : s₄.mem.readW (wordAddr b (krSlot + 1)) 32 = m₀.readW (State.addr K + BitVec.ofNat 64 20) 32 := by
    rw [show s₄.mem = s₃.mem from rfl, v₃ (20, krSlot + 1) (by simp), hm 20 (by omega)]
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
    · rw [ho k hk' (by omega) (by omega), ho₄ k hk' (by omega) (by omega)]
  refine WP.ite (decide (len = 24)) ((eval_eq s₄).trans (by rw [hz₄])) (fun h24 => ?_) (fun h24 => ?_)
  · have h24 : len = 24 := by simpa using h24
    obtain ⟨s', e', v2, v3, o', g', rd', wr', sp', f'⟩ := kr24_ok hk₄ h24
    have hb' : s'.gpr sb = b := by rw [g' _ (by decide) (by decide)]; exact hk₄.base
    refine WP.of_runBlock ⟨s', e', tail s' hb' g' rd' wr' sp' f' o' ?_⟩
    have e : (krOf m₀ (State.addr K) len).2 = ~~~ wordAt m₀ (State.addr K + BitVec.ofNat 64 16) := by
      simp [krOf, h24]
    rw [e]
    refine HW_not ?_ ?_
    · rw [slotW_of hb', v2, hm₄ 16 (by omega)]
    · rw [slotW_of hb', v3, hm₄ 20 (by omega), VG.Offset.add_add]
  · have h24 : len ≠ 24 := by simpa using h24
    obtain ⟨s₅, e₅, v₅, k₅, g₅, rd₅, wr₅, sp₅, f₅⟩ := loads_ok [(24, krSlot + 2), (28, krSlot + 3)] hk₄
      (by decide) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> exact ⟨by omega, by decide⟩)
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
    · rw [slotW_of hb₅, v₅ (24, krSlot + 2) (by simp), hm₄ 24 (by omega)]
    · rw [slotW_of hb₅, v₅ (28, krSlot + 3) (by simp), hm₄ 28 (by omega), VG.Offset.add_add]

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
      exact ⟨by rcases hlen with rfl | rfl | rfl <;> omega, by rw [klSlot_eq, slots_eq]; omega⟩)
  let s₂ := subFlags s₁ (s₁.gpr .r1) 16
  have e₂ : exec (.cmp .r1 (.imm 16)) s₁ = some s₂ := by
    simp only [exec, Op2.eval, show encodable (16 : BitVec 32) = true by decide, ↓reduceIte, Option.map_some]
    rfl
  have hz₂ : s₂.z = decide (len = 16) := by
    rw [subFlags_z, g₁ _ (by decide), hr1, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      ofNat32_sub_beq (by omega) (by decide)]
  have hk₂ : KeyIn s₂ b K len := hk.congr (g₁ _ (by decide)) (g₁ _ (by decide)) rd₁ wr₁
  have hm₂ : KeySame s₂ s₀.mem (State.addr K) len := KeySame.frame hk (fun _ _ => rfl) f₁
  have hkl : ∀ k < 4, s₂.mem.readW (wordAddr b (klSlot + k)) 32 =
      s₀.mem.readW (State.addr K + BitVec.ofNat 64 (4 * k)) 32 := fun k hk' =>
    v₁ (4 * k, klSlot + k) (by simp only [List.mem_map, List.mem_range]; exact ⟨k, hk', rfl⟩)
  have hklo : ∀ j < slots, j < klSlot ∨ klSlot + 4 ≤ j →
      s₂.mem.readW (wordAddr b j) 32 = s₀.mem.readW (wordAddr b j) 32 := fun j hj h =>
    k₁ j hj (by
      simp only [List.map_map, Function.comp_def, List.mem_map, List.mem_range, not_exists, not_and]
      intro k hk' h'; omega)
  have hcode : (List.range 4).flatMap (fun k => [Instr.ldr t0 .r0 (4 * k), stS (klSlot + k) t0]) =
      ((List.range 4).map fun k => (4 * k, klSlot + k)).flatMap fun (o, k) => [.ldr t0 .r0 o, stS k t0] := rfl
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [runBlock_app, hcode, e₁, Option.bind_some, runBlock_cons, e₂, runStep_some, runBlock_nil], ?_⟩)
  have post : ∀ s : State, KrPost s₂ b s₀.mem (State.addr K) len s → LoadPost s₀ b K len s := by
    intro s h
    have hb : s.gpr sb = b := by rw [h.regs _ (by decide) (by decide)]; exact hk₂.base
    have ho : ∀ k < 4, s.mem.readW (wordAddr b (klSlot + k)) 32 =
        s₀.mem.readW (State.addr K + BitVec.ofNat 64 (4 * k)) 32 := fun k hk' => by
      rw [h.keep _ (by rw [klSlot_eq, slots_eq]; omega) (.inl (by rw [klSlot_eq, krSlot_eq]; omega)), hkl k hk']
    refine ⟨VW_of_HW (HW_words ?_ ?_) (HW_words ?_ ?_), h.kr, fun k hk' hk2 => ?_,
      fun r h1 h2 => by rw [h.regs r h1 h2]; exact g₁ r h1, h.rd.trans rd₁, h.wr.trans wr₁, h.sp.trans sp₁,
      f₁.trans h.frame⟩
    · rw [slotW_of hb, show klSlot = klSlot + 0 from rfl, ho 0 (by decide)]; simp
    · rw [slotW_of hb, ho 1 (by decide)]
    · rw [slotW_of hb, ho 2 (by decide)]
    · rw [slotW_of hb, show klSlot + 2 + 1 = klSlot + 3 from rfl, ho 3 (by decide), VG.Offset.add_add]
      (try rfl)
    · rw [h.keep k hk' (by rw [klSlot_eq] at hk2; rw [krSlot_eq]; omega), hklo k hk' (by omega)]
  refine WP.ite (decide (len = 16)) ((eval_eq s₂).trans (by rw [hz₂])) (fun h16 => ?_) (fun h16 => ?_)
  · have h16 : len = 16 := by simpa using h16
    obtain ⟨s', e', h'⟩ := kr16_ok (m₀ := s₀.mem) hk₂ h16
    exact WP.of_runBlock ⟨s', e', post s' h'⟩
  · have h16 : len ≠ 16 := by simpa using h16
    exact WP.mono (krNot16_wp hk₂ hm₂ (by omega) (by show s₁.gpr .r1 = _; rw [g₁ _ (by decide)]; exact hr1)) post

end VG.Proof.Camellia.Arm
