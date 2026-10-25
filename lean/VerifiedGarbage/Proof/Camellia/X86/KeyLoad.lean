module
public import VerifiedGarbage.Proof.Camellia.X86.KeyPair

import VerifiedGarbage.Proof.Camellia.X86.Prologue
import VerifiedGarbage.Proof.Camellia.X86.Fl
import VerifiedGarbage.Proof.Camellia.Layout32
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Camellia's key schedule on x86 (32-bit): `KL` and `KR`

As on ARMv7 (`Proof/Camellia/Arm/KeyLoad.lean`): `loadKey_wp`, the key's
words (at `ecx`, loaded from the first argument) to the slots of `KL` and
`KR` (`KR` zero for a key of 16 bytes, its right half the complement of
its left for one of 24), as `klkr_halves` gives their halves (`VW`, by
`HW` for each half). The key's length is read from the second argument.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb tmpRegs slotAt st movI argOp at_ notR)
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

/-- The key at `K` (in `ecx`), apart from the scratch buffer at `b`, and its
length `len` in the second argument's word at `A`. -/
structure KeyIn (s : State) (b K : BitVec 32) (A : Addr) (len : Nat) : Prop where
  base : s.gpr sb = b
  scr : ScrIn s.wr b
  ecx : s.gpr .ecx = K
  rd : (⟨K.setWidth 64, len⟩ : Region) ∈ s.rd
  fit : K.toNat + len ≤ 2 ^ 32
  sep : Region.Disjoint ⟨K.setWidth 64, len⟩ ⟨b.setWidth 64, 4 * slots⟩
  le : len ≤ 32
  argEa : s.ea (argOp 1) = A
  argIn : InRegions (s.rd ++ s.wr) A 4
  argV : s.mem.readW A 32 = BitVec.ofNat 32 len
  argSep : Region.Disjoint ⟨A, 4⟩ ⟨b.setWidth 64, 4 * slots⟩

theorem KeyIn.congr {s s' : State} {b K : BitVec 32} {A : Addr} {len : Nat} (h : KeyIn s b K A len)
    (hb : s'.gpr sb = s.gpr sb) (hc : s'.gpr .ecx = s.gpr .ecx) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem) :
    KeyIn s' b K A len :=
  ⟨hb.trans h.base, ⟨hwr ▸ h.scr.mem, h.scr.fit⟩, hc.trans h.ecx, hrd ▸ h.rd, h.fit, h.sep, h.le,
    by rw [← h.argEa]; show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hsp],
    hrd ▸ hwr ▸ h.argIn,
    by rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.argSep) (by decide)]; exact h.argV, h.argSep⟩

/-- The key's word at offset `o`. -/
theorem KeyIn.word {s : State} {b K : BitVec 32} {A : Addr} {len : Nat} (h : KeyIn s b K A len) {o : Nat}
    (ho : o + 4 ≤ len) :
    s.ea (at_ .ecx o) = K.setWidth 64 + BitVec.ofNat 64 o ∧
      InRegions (s.rd ++ s.wr) (s.ea (at_ .ecx o)) 4 := by
  have e : s.ea (at_ .ecx o) = K.setWidth 64 + BitVec.ofNat 64 o := by
    rw [at_, ea_mk, h.ecx, addr_eq (by have := h.fit; omega_arith)]
  refine ⟨e, ⟨_, List.mem_append_left _ h.rd, ?_⟩⟩
  have := setWidth_toNat K
  rw [e]; exact VG.Offset.contains_base _ (by omega_arith) (by have := h.fit; omega_arith)

/-- A word of the key, kept by a frame of the scratch buffer. -/
theorem KeyIn.keep {s : State} {b K : BitVec 32} {A : Addr} {len : Nat} (h : KeyIn s b K A len) {m m' : Mem}
    (hf : Frame [⟨b.setWidth 64, 4 * slots⟩] m m') {o : Nat} (ho : o + 4 ≤ len) :
    m'.readW (K.setWidth 64 + BitVec.ofNat 64 o) 32 = m.readW (K.setWidth 64 + BitVec.ofNat 64 o) 32 :=
  hf.readW (VG.Offset.contains_base _ (by omega_arith) (by have := h.fit; have := setWidth_toNat K; omega_arith))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.sep) (by decide)

/-- `mov eax, [ecx + o]`. -/
theorem ldKey_ok {s : State} {b K : BitVec 32} {A : Addr} {len : Nat} (h : KeyIn s b K A len) {o : Nat}
    (ho : o + 4 ≤ len) :
    ∃ s', runBlock isa [.mov .eax (.mem (at_ .ecx o))] s = some s' ∧
      s'.gpr .eax = s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 o) 32 ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨ea, ei⟩ := h.word ho
  refine ⟨s.setReg .eax (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 o) 32), ?_, RegUpd.gpr_setReg_self _ _ _,
    fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.mov .eax (.mem (at_ .ecx o))) s =
      some (s.setReg .eax (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 o) 32)) by
    show (s.load32 (s.ea (at_ .ecx o))).map (s.setReg .eax) = _
    rw [ea] at ei ⊢
    simp only [State.load32, ei, ↓reduceIte, Option.map_some], runStep_some, runBlock_nil]

/-- `mov eax, [ecx + o]; mov [edi + 4 k], eax` for each `(o, k)` of `L`. -/
theorem loads_ok {b K : BitVec 32} {A : Addr} {len : Nat} : ∀ (L : List (Nat × Nat)) {s : State},
    KeyIn s b K A len → (L.map (·.2)).Nodup → (∀ x ∈ L, x.1 + 4 ≤ len ∧ x.2 < slots) →
    ∃ s', runBlock isa (L.flatMap fun x => [.mov .eax (.mem (at_ .ecx x.1)), st x.2 .eax]) s = some s' ∧
      (∀ x ∈ L, s'.mem.readW (wordAddr b x.2) 32 = s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 x.1) 32) ∧
      (∀ k < slots, k ∉ L.map (·.2) → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem
  | [], s, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | x :: L, s, hk, hnd, hin => by
    obtain ⟨hx1, hx2⟩ := hin x List.mem_cons_self
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldKey_ok hk hx1
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, -, -, f₂⟩ := stSlot_ok s₁ .eax .edi (b := b) (k := x.2)
      (by rw [o₁ _ (by decide)]; exact hk.base) hx2 (by rw [wr₁]; exact hk.scr)
    rw [List.map_cons, List.nodup_cons] at hnd
    have hfit := hk.scr.fit
    have f₂' : Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s₂.mem := by
      rw [← m₁]
      exact f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit hx2⟩
    have hk₂ : KeyIn s₂ b K A len := hk.congr (by rw [show s₂.gpr sb = s₁.gpr sb from congrFun g₂ sb,
      o₁ _ (by decide)]) (by rw [g₂, o₁ _ (by decide)]) (by rw [g₂, o₁ _ (by decide)])
      (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) f₂'
    obtain ⟨s', e', v', k', g', rd', wr', f'⟩ := loads_ok L hk₂ hnd.2
      fun y hy => hin y (List.mem_cons_of_mem _ hy)
    have hslot : ∀ j < slots, s₂.mem.readW (wordAddr b j) 32 = if j = x.2 then
        s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 x.1) 32 else s.mem.readW (wordAddr b j) 32 := fun j hj => by
      rw [m₂, readW_slot_write hfit _ hj hx2, v₁, m₁]
    refine ⟨s', ?_, fun y hy => ?_, fun j hj hn => ?_, fun r hr => by
        rw [g' r hr, g₂, o₁ r hr],
      by rw [rd', rd₂, rd₁], by rw [wr', wr₂, wr₁], f₂'.trans f'⟩
    · rw [List.flatMap_cons, show ([.mov .eax (.mem (at_ .ecx x.1)), st x.2 .eax] : List Instr) =
        [.mov .eax (.mem (at_ .ecx x.1))] ++ [.store (slotAt .edi x.2) .eax] from rfl, runBlock_app,
        runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some]
      exact e'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · by_cases hin' : y.2 ∈ L.map (·.2)
        · exact absurd hin' hnd.1
        · rw [k' _ hx2 hin', hslot _ hx2, ite_eq_left rfl]
      · rw [v' y hy', hk.keep f₂' (hin y (List.mem_cons_of_mem _ hy')).1]
    · simp only [List.map_cons, List.mem_cons, not_or] at hn
      rw [k' j hj hn.2, hslot j hj, ite_eq_right hn.1]

/-- `mov eax, [esp + 8]; cmp eax, v`: the key's length against `v`. -/
theorem cmpLen_ok {s : State} {b K : BitVec 32} {A : Addr} {len : Nat} (h : KeyIn s b K A len) (v : Nat)
    (hv : v < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm (BitVec.ofNat 32 v))] s = some s' ∧
      s'.zf = some (decide (len = v)) ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax 1 (by rw [h.argEa]; exact h.argIn)
  let a := s₁.gpr .eax
  let c : BitVec 32 := BitVec.ofNat 32 v
  refine ⟨arithFlags s₁ (a - c) (a.toNat < c.toNat) (subOverflow a c (a - c)), ?_, ?_,
    fun r hr => by rw [RegUpd.gpr_arithFlags, o₁ r hr], by rw [RegUpd.mem_arithFlags, m₁],
    by rw [RegUpd.rd_arithFlags, rd₁], by rw [RegUpd.wr_arithFlags, wr₁]⟩
  · rw [show ([.mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm (BitVec.ofNat 32 v))] : List Instr) =
      [.mov .eax (.mem (argOp 1))] ++ [.alu .cmp .eax (.imm (BitVec.ofNat 32 v))] from rfl, runBlock_app, e₁,
      Option.bind_some]
    rfl
  · rw [RegUpd.zf_arithFlags, show a = _ from v₁, h.argEa, h.argV, ofNat32_sub_beq (by have := h.le; omega_arith) hv]

/-- `mov [edi + 4 k], eax` for each `k` of `ks`. -/
theorem storeAll_ok {b : BitVec 32} : ∀ (ks : List Nat) {s : State}, s.gpr sb = b →
    ScrIn s.wr b → (∀ k ∈ ks, k < slots) →
    ∃ s', runBlock isa (ks.map fun k => st k .eax) s = some s' ∧
      (∀ k ∈ ks, s'.mem.readW (wordAddr b k) 32 = s.gpr .eax) ∧
      (∀ k < slots, k ∉ ks → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem
  | [], s, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k :: ks, s, hb, hw, hk => by
    have hk0 : k < slots := hk k List.mem_cons_self
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, -, -, f₁⟩ := stSlot_ok s .eax .edi (b := b) (k := k) hb hk0 hw
    obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := storeAll_ok ks (s := s₁)
      (by rw [show s₁.gpr sb = s.gpr sb from congrFun g₁ sb, hb]) (by rw [wr₁]; exact hw)
      fun k h => hk k (List.mem_cons_of_mem _ h)
    have hfit := hw.fit
    have hslot : ∀ j < slots, s₁.mem.readW (wordAddr b j) 32 = if j = k then s.gpr .eax else
        s.mem.readW (wordAddr b j) 32 := fun j hj => by rw [m₁, readW_slot_write hfit _ hj hk0]
    refine ⟨s', by rw [List.map_cons, ← List.singleton_append, runBlock_app,
        show ([st k .eax] : List Instr) = [.store (slotAt .edi k) .eax] from rfl, e₁, Option.bind_some]; exact e',
      fun j hj => ?_, fun j hj hn => ?_, by rw [g', g₁], by rw [rd', rd₁], by rw [wr', wr₁], ?_⟩
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
structure KrPost (s : State) (b : BitVec 32) (m₀ : Mem) (K : Addr) (len : Nat) (s' : State) : Prop where
  kr : VW s' krSlot (krOf m₀ K len)
  keep : ∀ k < slots, k < krSlot ∨ krSlot + 4 ≤ k →
    s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32
  regs : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem

theorem klSlot_eq : klSlot = 72 := rfl
theorem krSlot_eq : krSlot = 76 := rfl

theorem slotW_of {s : State} {b : BitVec 32} (hb : s.gpr sb = b) (k : Nat) :
    slotW s k = s.mem.readW (wordAddr b k) 32 := by rw [slotW, hb]

/-- The key's words in `s` are those of `m₀`. -/
def KeySame (s : State) (m₀ : Mem) (K : Addr) (len : Nat) : Prop :=
  ∀ o, o + 4 ≤ len → s.mem.readW (K + BitVec.ofNat 64 o) 32 = m₀.readW (K + BitVec.ofNat 64 o) 32

theorem KeySame.frame {s s' : State} {b K : BitVec 32} {A : Addr} {len : Nat} {m₀ : Mem} (hk : KeyIn s b K A len)
    (h : KeySame s m₀ (K.setWidth 64) len) (hf : Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem) :
    KeySame s' m₀ (K.setWidth 64) len := fun o ho => by rw [hk.keep hf ho]; exact h o ho

/-- A key of 16 bytes: `KR` is zero. -/
theorem kr16_ok {s : State} {b K : BitVec 32} {A : Addr} {len : Nat} {m₀ : Mem} (hk : KeyIn s b K A len)
    (h16 : len = 16) :
    ∃ s', runBlock isa (([movI .eax 0] : List Instr) ++ (List.range 4).map fun k => st (krSlot + k) .eax) s =
      some s' ∧ KrPost s b m₀ (K.setWidth 64) len s' := by
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := movI_ok s .eax 0
  obtain ⟨s₄, e₄, v₄, k₄, g₄, rd₄, wr₄, f₄⟩ := storeAll_ok (b := b) ((List.range 4).map fun k => krSlot + k)
    (s := s₃) (by rw [o₃ _ (by decide)]; exact hk.base) (by rw [wr₃]; exact hk.scr)
    (fun k hk' => by simp only [List.mem_map, List.mem_range] at hk'; obtain ⟨k, hk', rfl⟩ := hk'
                     rw [krSlot_eq, slots_eq]; omega_arith)
  have hb₄ : s₄.gpr sb = b := by rw [g₄, o₃ _ (by decide)]; exact hk.base
  have hz : ∀ k < 4, slotW s₄ (krSlot + k) = 0 := fun k hk' => by
    rw [slotW_of hb₄, v₄ (krSlot + k) (by simp only [List.mem_map, List.mem_range]; exact ⟨k, hk', rfl⟩), v₃]
  have e : krOf m₀ (K.setWidth 64) len = (0, 0) := by simp [krOf, h16]
  refine ⟨s₄, ?_, ⟨?_, fun k hk' h => ?_, fun r h1 => by rw [g₄, o₃ r h1],
    by rw [rd₄, rd₃], by rw [wr₄, wr₃], by rw [← m₃]; exact f₄⟩⟩
  · rw [runBlock_app, e₃, Option.bind_some]
    simpa only [List.map_map, Function.comp_def] using e₄
  · rw [e]
    exact VW_of_HW (HW_zero (hz 0 (by decide)) (hz 1 (by decide))) (HW_zero (hz 2 (by decide)) (hz 3 (by decide)))
  · rw [k₄ k hk' (by simp only [List.mem_map, List.mem_range, not_exists, not_and]; intro j hj h'; omega_arith), m₃]

/-- `mov eax, [ecx + o]; not eax; mov [edi + 4 k], eax`. -/
theorem ldNotSt_ok {s : State} {b K : BitVec 32} {A : Addr} {len : Nat} (hk : KeyIn s b K A len) {o k : Nat}
    (ho : o + 4 ≤ len) (hks : k < slots) :
    ∃ s', runBlock isa [.mov .eax (.mem (at_ .ecx o)), notR .eax, st k .eax] s = some s' ∧
      s'.mem = s.mem.writeW (wordAddr b k) (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 o) 32 ^^^
        BitVec.allOnes 32) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldKey_ok hk ho
  let x := s₁.gpr .eax ^^^ BitVec.allOnes 32
  let s₂ := (arithFlags s₁ x false false).setReg .eax x
  have e₂ : runBlock isa [notR .eax] s₁ = some s₂ := rfl
  have hb₂ : s₂.gpr sb = b := by
    rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_arithFlags, o₁ _ (by decide)]; exact hk.base
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, -, -, f₃⟩ := stSlot_ok s₂ .eax .edi (b := b) (k := k) hb₂ hks
    (by show ScrIn s₁.wr b; rw [wr₁]; exact hk.scr)
  refine ⟨s₃, ?_, ?_, fun r hr => ?_, by rw [rd₃]; exact rd₁, by rw [wr₃]; exact wr₁, ?_⟩
  · rw [show ([.mov .eax (.mem (at_ .ecx o)), notR .eax, st k .eax] : List Instr) =
      [.mov .eax (.mem (at_ .ecx o))] ++ ([notR .eax] ++ [.store (slotAt .edi k) .eax]) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  · rw [m₃, RegUpd.gpr_setReg_self]; show s₁.mem.writeW _ (s₁.gpr .eax ^^^ _) = _; rw [v₁, m₁]
  · rw [g₃, RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, o₁ r hr]
  · rw [← m₁]
    exact f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hk.scr.fit hks⟩

/-- Keys of 24 or 32 bytes. -/
theorem krNot16_wp {s : State} {b K : BitVec 32} {A : Addr} {len : Nat} {m₀ : Mem} (hk : KeyIn s b K A len)
    (hm : KeySame s m₀ (K.setWidth 64) len) (hlen : len = 24 ∨ len = 32) :
    WP isa (.seq (.block [.mov .eax (.mem (at_ .ecx 16)), st krSlot .eax, .mov .eax (.mem (at_ .ecx 20)),
          st (krSlot + 1) .eax, .mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 24)])
        (.ite .e
          (.block [.mov .eax (.mem (at_ .ecx 16)), notR .eax, st (krSlot + 2) .eax,
            .mov .eax (.mem (at_ .ecx 20)), notR .eax, st (krSlot + 3) .eax])
          (.block [.mov .eax (.mem (at_ .ecx 24)), st (krSlot + 2) .eax, .mov .eax (.mem (at_ .ecx 28)),
            st (krSlot + 3) .eax]))) s
      (KrPost s b m₀ (K.setWidth 64) len) := by
  have hfit := hk.scr.fit
  have h16 : len ≠ 16 := by omega_arith
  obtain ⟨s₃, e₃, v₃, k₃, g₃, rd₃, wr₃, f₃⟩ := loads_ok [(16, krSlot), (20, krSlot + 1)] hk (by decide)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact ⟨by omega_arith, by decide⟩)
  have hk₃ : KeyIn s₃ b K A len := hk.congr (g₃ _ (by decide)) (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃ f₃
  obtain ⟨s₄, e₄, z₄, g₄, m₄, rd₄, wr₄⟩ := cmpLen_ok hk₃ 24 (by decide)
  have hk₄ : KeyIn s₄ b K A len := hk₃.congr (g₄ _ (by decide)) (g₄ _ (by decide)) (g₄ _ (by decide)) rd₄ wr₄
    (by rw [m₄]; exact Frame.refl _ _)
  have hm₄ : KeySame s₄ m₀ (K.setWidth 64) len := by
    have := hm.frame hk f₃; intro o ho; rw [m₄]; exact this o ho
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [show ([.mov .eax (.mem (at_ .ecx 16)), st krSlot .eax, .mov .eax (.mem (at_ .ecx 20)),
        st (krSlot + 1) .eax, .mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 24)] : List Instr) =
        ([(16, krSlot), (20, krSlot + 1)].flatMap fun x => [.mov .eax (.mem (at_ .ecx x.1)), st x.2 .eax]) ++
          [.mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm (BitVec.ofNat 32 24))] from rfl, runBlock_app, e₃,
      Option.bind_some, e₄], ?_⟩)
  have hl0 : s₄.mem.readW (wordAddr b krSlot) 32 = m₀.readW (K.setWidth 64 + BitVec.ofNat 64 16) 32 := by
    rw [m₄, v₃ (16, krSlot) (by simp), hm 16 (by omega_arith)]
  have hl1 : s₄.mem.readW (wordAddr b (krSlot + 1)) 32 = m₀.readW (K.setWidth 64 + BitVec.ofNat 64 20) 32 := by
    rw [m₄, v₃ (20, krSlot + 1) (by simp), hm 20 (by omega_arith)]
  have ho₄ : ∀ j < slots, j ≠ krSlot → j ≠ krSlot + 1 →
      s₄.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32 := fun j hj h1 h2 => by
    rw [m₄]; exact k₃ j hj (by simp [h1, h2])
  have f₃₄ : Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s₄.mem := by rw [m₄]; exact f₃
  -- The right half, from `s₄` to `s'`.
  have tail : ∀ s' : State, s'.gpr sb = b → (∀ r, r ≠ .eax → s'.gpr r = s₄.gpr r) →
      s'.rd = s₄.rd → s'.wr = s₄.wr → Frame [⟨b.setWidth 64, 4 * slots⟩] s₄.mem s'.mem →
      (∀ j < slots, j ≠ krSlot + 2 → j ≠ krSlot + 3 →
        s'.mem.readW (wordAddr b j) 32 = s₄.mem.readW (wordAddr b j) 32) →
      HW s' (krSlot + 2) (krOf m₀ (K.setWidth 64) len).2 → KrPost s b m₀ (K.setWidth 64) len s' := by
    intro s' hb hg hrd hwr hf ho hR
    have e : (krOf m₀ (K.setWidth 64) len).1 = wordAt m₀ (K.setWidth 64 + BitVec.ofNat 64 16) := by
      simp [krOf, h16]
    refine ⟨VW_of_HW (e ▸ HW_words ?_ ?_) hR, fun k hk' h => ?_, fun r h1 => by
        rw [hg r h1, g₄ r h1, g₃ r h1],
      by rw [hrd, rd₄, rd₃], by rw [hwr, wr₄, wr₃], f₃₄.trans hf⟩
    · rw [slotW_of hb, ho _ (by decide) (by decide) (by decide), hl0]
    · rw [slotW_of hb, ho _ (by decide) (by decide) (by decide), hl1, VG.Offset.add_add]
    · rw [ho k hk' (by omega_arith) (by omega_arith), ho₄ k hk' (by omega_arith) (by omega_arith)]
  refine WP.ite (decide (len = 24)) ((eval_e s₄).trans z₄) (fun h24 => ?_) (fun h24 => ?_)
  · have h24 : len = 24 := by simpa using h24
    obtain ⟨s₅, e₅, m₅, o₅, rd₅, wr₅, f₅⟩ := ldNotSt_ok hk₄ (o := 16) (k := krSlot + 2) (by omega_arith) (by decide)
    have hk₅ : KeyIn s₅ b K A len := hk₄.congr (o₅ _ (by decide)) (o₅ _ (by decide)) (o₅ _ (by decide)) rd₅ wr₅ f₅
    obtain ⟨s₆, e₆, m₆, o₆, rd₆, wr₆, f₆⟩ := ldNotSt_ok hk₅ (o := 20) (k := krSlot + 3) (by omega_arith) (by decide)
    have hb₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), o₅ _ (by decide)]; exact hk₄.base
    refine WP.of_runBlock ⟨s₆, by
      rw [show ([.mov .eax (.mem (at_ .ecx 16)), notR .eax, st (krSlot + 2) .eax,
          .mov .eax (.mem (at_ .ecx 20)), notR .eax, st (krSlot + 3) .eax] : List Instr) =
        [.mov .eax (.mem (at_ .ecx 16)), notR .eax, st (krSlot + 2) .eax] ++
          [.mov .eax (.mem (at_ .ecx 20)), notR .eax, st (krSlot + 3) .eax] from rfl, runBlock_app, e₅,
        Option.bind_some, e₆],
      tail s₆ hb₆ (fun r h => by rw [o₆ r h, o₅ r h]) (by rw [rd₆, rd₅]) (by rw [wr₆, wr₅]) (f₅.trans f₆)
        (fun j hj h1 h2 => by
          rw [m₆, readW_slot_write hfit _ hj (by decide), ite_eq_right h2, m₅,
            readW_slot_write hfit _ hj (by decide), ite_eq_right h1]) ?_⟩
    have e : (krOf m₀ (K.setWidth 64) len).2 = ~~~ wordAt m₀ (K.setWidth 64 + BitVec.ofNat 64 16) := by
      simp [krOf, h24]
    rw [e]
    refine HW_not ?_ ?_
    · rw [slotW_of hb₆, m₆, readW_slot_write hfit _ (by decide) (by decide), ite_eq_right (by decide), m₅,
        Mem.readW_writeW_self32, hm₄ 16 (by omega_arith)]
    · rw [slotW_of hb₆, m₆, show krSlot + 2 + 1 = krSlot + 3 from rfl, Mem.readW_writeW_self32,
        hk₄.keep f₅ (by omega_arith), hm₄ 20 (by omega_arith), VG.Offset.add_add]
  · have h24 : len ≠ 24 := by simpa using h24
    obtain ⟨s₅, e₅, v₅, k₅, g₅, rd₅, wr₅, f₅⟩ := loads_ok [(24, krSlot + 2), (28, krSlot + 3)] hk₄
      (by decide) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> exact ⟨by omega_arith, by decide⟩)
    have hb₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide)]; exact hk₄.base
    refine WP.of_runBlock ⟨s₅, by
      rw [show ([.mov .eax (.mem (at_ .ecx 24)), st (krSlot + 2) .eax, .mov .eax (.mem (at_ .ecx 28)),
          st (krSlot + 3) .eax] : List Instr) =
        [(24, krSlot + 2), (28, krSlot + 3)].flatMap fun x => [.mov .eax (.mem (at_ .ecx x.1)), st x.2 .eax]
        from rfl]
      exact e₅, tail s₅ hb₅ (fun r h1 => g₅ r h1) rd₅ wr₅ f₅
        (fun j hj h1 h2 => k₅ j hj (by simp [h1, h2])) ?_⟩
    have e : (krOf m₀ (K.setWidth 64) len).2 = wordAt m₀ (K.setWidth 64 + BitVec.ofNat 64 24) := by
      simp [krOf, h16, h24]
    rw [e]
    refine HW_words ?_ ?_
    · rw [slotW_of hb₅, v₅ (24, krSlot + 2) (by simp), hm₄ 24 (by omega_arith)]
    · rw [slotW_of hb₅, v₅ (28, krSlot + 3) (by simp), hm₄ 28 (by omega_arith), VG.Offset.add_add]

/-- What `loadKey` leaves. -/
structure LoadPost (s₀ : State) (b K : BitVec 32) (len : Nat) (s : State) : Prop where
  kl : VW s klSlot (wordAt s₀.mem (K.setWidth 64), wordAt s₀.mem (K.setWidth 64 + BitVec.ofNat 64 8))
  kr : VW s krSlot (krOf s₀.mem (K.setWidth 64) len)
  keep : ∀ k < slots, k < klSlot ∨ klSlot + 8 ≤ k →
    s.mem.readW (wordAddr b k) 32 = s₀.mem.readW (wordAddr b k) 32
  regs : ∀ r, r ≠ .eax → r ≠ .ecx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s.mem

/-- What `loadKey` needs: the key's address in the first argument, its
length in the second. -/
structure LoadPre (s : State) (b K : BitVec 32) (len : Nat) : Prop where
  base : s.gpr sb = b
  scr : ScrIn s.wr b
  rd : (⟨K.setWidth 64, len⟩ : Region) ∈ s.rd
  fit : K.toNat + len ≤ 2 ^ 32
  sep : Region.Disjoint ⟨K.setWidth 64, len⟩ ⟨b.setWidth 64, 4 * slots⟩
  hlen : len = 16 ∨ len = 24 ∨ len = 32
  arg0 : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4
  arg0V : s.mem.readW (s.ea (argOp 0)) 32 = K
  arg1 : InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4
  arg1V : s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 len
  arg1Sep : Region.Disjoint ⟨s.ea (argOp 1), 4⟩ ⟨b.setWidth 64, 4 * slots⟩

theorem loadKey_wp {s₀ : State} {b K : BitVec 32} {len : Nat} (hp : LoadPre s₀ b K len) :
    WP isa loadKey s₀ (LoadPost s₀ b K len) := by
  have hfit := hp.scr.fit
  have hlen := hp.hlen
  unfold loadKey
  obtain ⟨s₀', e₀, c₀, o₀, m₀, rd₀, wr₀⟩ := ldArg_ok s₀ .ecx 0 hp.arg0
  have hk : KeyIn s₀' b K (s₀.ea (argOp 1)) len :=
    ⟨by rw [o₀ _ (by decide)]; exact hp.base, by rw [wr₀]; exact hp.scr, by rw [c₀, hp.arg0V],
      by rw [rd₀]; exact hp.rd, hp.fit, hp.sep, by omega_arith,
      by show (s₀'.gpr .esp + _).setWidth 64 = (s₀.gpr .esp + _).setWidth 64; rw [o₀ _ (by decide)],
      by rw [rd₀, wr₀]; exact hp.arg1, by rw [m₀]; exact hp.arg1V, hp.arg1Sep⟩
  -- `KL`.
  obtain ⟨s₁, e₁, v₁, k₁, g₁, rd₁, wr₁, f₁⟩ := loads_ok ((List.range 4).map fun k => (4 * k, klSlot + k)) hk
    (by decide) (fun x hx => by
      simp only [List.mem_map, List.mem_range] at hx; obtain ⟨k, hk', rfl⟩ := hx
      exact ⟨by rcases hlen with rfl | rfl | rfl <;> omega_arith, by rw [klSlot_eq, slots_eq]; omega_arith⟩)
  have hk₁ : KeyIn s₁ b K (s₀.ea (argOp 1)) len :=
    hk.congr (g₁ _ (by decide)) (g₁ _ (by decide)) (g₁ _ (by decide)) rd₁ wr₁ f₁
  obtain ⟨s₂, e₂, z₂, g₂, m₂, rd₂, wr₂⟩ := cmpLen_ok hk₁ 16 (by decide)
  have hk₂ : KeyIn s₂ b K (s₀.ea (argOp 1)) len :=
    hk₁.congr (g₂ _ (by decide)) (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂ (by rw [m₂]; exact Frame.refl _ _)
  have f₀₂ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀'.mem s₂.mem := by rw [m₂]; exact f₁
  have hm₂ : KeySame s₂ s₀.mem (K.setWidth 64) len := by
    have := KeySame.frame hk (fun _ _ => by rw [m₀]) f₁; intro o ho; rw [m₂]; exact this o ho
  have hkl : ∀ k < 4, s₂.mem.readW (wordAddr b (klSlot + k)) 32 =
      s₀.mem.readW (K.setWidth 64 + BitVec.ofNat 64 (4 * k)) 32 := fun k hk' => by
    rw [m₂, v₁ (4 * k, klSlot + k) (by simp only [List.mem_map, List.mem_range]; exact ⟨k, hk', rfl⟩), m₀]
  have hklo : ∀ j < slots, j < klSlot ∨ klSlot + 4 ≤ j →
      s₂.mem.readW (wordAddr b j) 32 = s₀.mem.readW (wordAddr b j) 32 := fun j hj h => by
    rw [m₂, k₁ j hj (by
      simp only [List.map_map, Function.comp_def, List.mem_map, List.mem_range, not_exists, not_and]
      intro k hk' h'; omega_arith), m₀]
  have hcode : (List.range 4).flatMap (fun k => [Instr.mov .eax (.mem (at_ .ecx (4 * k))), st (klSlot + k) .eax]) =
      ((List.range 4).map fun k => (4 * k, klSlot + k)).flatMap fun x =>
        [.mov .eax (.mem (at_ .ecx x.1)), st x.2 .eax] := by
    simp only [List.flatMap_map]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [runBlock_app, runBlock_app, e₀, Option.bind_some, hcode, e₁, Option.bind_some]; exact e₂, ?_⟩)
  have post : ∀ s : State, KrPost s₂ b s₀.mem (K.setWidth 64) len s → LoadPost s₀ b K len s := by
    intro s h
    have hb : s.gpr sb = b := by rw [h.regs _ (by decide)]; exact hk₂.base
    have ho : ∀ k < 4, s.mem.readW (wordAddr b (klSlot + k)) 32 =
        s₀.mem.readW (K.setWidth 64 + BitVec.ofNat 64 (4 * k)) 32 := fun k hk' => by
      rw [h.keep _ (by rw [klSlot_eq, slots_eq]; omega_arith) (.inl (by rw [klSlot_eq, krSlot_eq]; omega_arith)), hkl k hk']
    refine ⟨VW_of_HW (HW_words ?_ ?_) (HW_words ?_ ?_), h.kr, fun k hk' hk2 => ?_,
      fun r h1 h2 => by rw [h.regs r h1, g₂ r h1, g₁ r h1, o₀ r h2], by rw [h.rd, rd₂, rd₁, rd₀],
      by rw [h.wr, wr₂, wr₁, wr₀], ?_⟩
    · rw [slotW_of hb, show klSlot = klSlot + 0 from rfl, ho 0 (by decide)]; simp
    · rw [slotW_of hb, ho 1 (by decide)]
    · rw [slotW_of hb, ho 2 (by decide)]
    · rw [slotW_of hb, show klSlot + 2 + 1 = klSlot + 3 from rfl, ho 3 (by decide), VG.Offset.add_add]
    · rw [h.keep k hk' (by rw [klSlot_eq] at hk2; rw [krSlot_eq]; omega_arith), hklo k hk' (by omega_arith)]
    · rw [← m₀]; exact f₀₂.trans h.frame
  refine WP.ite (decide (len = 16)) ((eval_e s₂).trans z₂) (fun h16 => ?_) (fun h16 => ?_)
  · have h16 : len = 16 := by simpa using h16
    obtain ⟨s', e', h'⟩ := kr16_ok (m₀ := s₀.mem) hk₂ h16
    exact WP.of_runBlock ⟨s', e', post s' h'⟩
  · have h16 : len ≠ 16 := by simpa using h16
    exact WP.mono (krNot16_wp hk₂ hm₂ (by omega_arith)) post

end VG.Proof.Camellia.X86
