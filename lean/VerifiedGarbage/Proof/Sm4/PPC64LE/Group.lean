module


public import VerifiedGarbage.Proof.Sm4.PPC64LE.Prologue
public import VerifiedGarbage.Proof.Sm4.Common
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Core
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Ecb
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Sm4.PPC64LE.Keys
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.PPC64LE.LayersLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Crypt16
import VerifiedGarbage.Proof.Sm4.Layout

/-! ### `Sm4.PPC64LE.Copy`, which only this module used -/

section

/-!
# Copying blocks on PPC64LE

`copyBlocks_wp`: the loop `copyBlocks` copies `c ≥ 1` blocks
of 16 bytes from `r6` to `r7` (areas that do not overlap), through `t0`,
counting down `r3`, and changes nothing else in memory.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4.PPC64LE
open VG.Impl.Aes.PPC64LE (t0)

/-- `ld t0, d(r6); std t0, d(r7)`. -/
theorem copyWord_ok (s : State) {d : Nat} (hd : d % 8 = 0 ∧ d < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r6 + BitVec.ofNat 64 d) 8)
    (hw : InRegions s.wr (s.gpr .r7 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [.load .d t0 .r6 d, .store .d t0 .r7 d] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r7 + BitVec.ofNat 64 d) (s.mem.readW (s.gpr .r6 + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have u := Upd.write s t0 (s.mem.readW (s.gpr .r6 + BitVec.ofNat 64 d) 64)
  have h7 : (s.write t0 (s.mem.readW (s.gpr .r6 + BitVec.ofNat 64 d) 64)).gpr .r7 = s.gpr .r7 :=
    u.other _ (by decide)
  let s₁ := s.write t0 (s.mem.readW (s.gpr .r6 + BitVec.ofNat 64 d) 64)
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s₁.gpr .r7 + BitVec.ofNat 64 d) (s₁.gpr t0) }, ?_, ?_, u.other,
    u.rd, u.wr⟩
  · simp only [runBlock_cons, exec_load_d (show Reg.r6 ≠ .r0 by decide) ⟨hd.2, by omega_using [hd]⟩ hr, runStep_some,
      exec_store_d (show Reg.r7 ≠ .r0 by decide) ⟨hd.2, by omega_using [hd]⟩ (by rw [h7]; exact hw), runBlock_nil, s₁]
  · show Mem.writeW _ _ _ = _
    rw [h7, u.gpr, u.mem]

/-- Copying, after `j` of `c` blocks. -/
structure CopyInv (A B : Addr) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  src : s.gpr .r6 = A + BitVec.ofNat 64 (16 * j)
  dst : s.gpr .r7 = B + BitVec.ofNat 64 (16 * j)
  cnt : s.gpr .r3 = BitVec.ofNat 64 (c - j)
  copied : ∀ t < 16 * j, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r3 → r ≠ t0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyBlocks_wp {A B : Addr} {c : Nat} {s₀ : State} (hc : 0 < c) (hc16 : c ≤ 16)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyBlocks s₀ (CopyInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega_arith, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  have hA0 := hA (2 * j) (by omega_arith)
  have hA1 := hA (2 * j + 1) (by omega_arith)
  have hB0 := hB (2 * j) (by omega_arith)
  have hB1 := hB (2 * j + 1) (by omega_arith)
  have hfA : Frame [⟨B, 16 * c⟩] s₀.mem s.mem := hi.frame
  have hAs : ∀ t < 16 * c, s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t) := fun t ht =>
    hfA.bytes (R := ⟨A, 16 * c⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega_arith) ht
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := copyWord_ok s (d := 0) (by decide)
    (by rw [hi.rd, hi.wr, hi.src, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_arith]; exact hA0)
    (by rw [hi.wr, hi.dst, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_arith]; exact hB0)
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := copyWord_ok s₁ (d := 8) (by decide)
    (by rw [rd₁, wr₁, hi.rd, hi.wr, g₁ _ (by decide), hi.src, addr_add,
      show 16 * j + 8 = 8 * (2 * j + 1) by omega_arith]; exact hA1)
    (by rw [wr₁, hi.wr, g₁ _ (by decide), hi.dst, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega_arith]; exact hB1)
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addI_ok s₂ .r6 .r6 (imm := 16) (by decide)
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addI_ok s₃ .r7 .r7 (imm := 16) (by decide)
  obtain ⟨s₅, e₅, c₅, o₅, m₅, rd₅, wr₅⟩ := subI_ok s₄ .r3 .r3 (imm := 1) (by decide)
  refine WP.of_runBlock ⟨s₅, by
    rw [show ([Instr.load .d t0 .r6 0, .store .d t0 .r7 0, .load .d t0 .r6 8, .store .d t0 .r7 8,
      .addi .r6 .r6 16, .addi .r7 .r7 16, .subi .r3 .r3 1] : List Instr) =
      [.load .d t0 .r6 0, .store .d t0 .r7 0] ++ ([.load .d t0 .r6 8, .store .d t0 .r7 8] ++
      ([.addi .r6 .r6 16] ++ ([.addi .r7 .r7 16] ++ [.subi .r3 .r3 1]))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, e₅], ?_⟩
  have hn : 16 * c < 2 ^ 64 := by omega_arith
  have r1 : s₁.gpr .r7 = B + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.dst]
  have a1 : s₁.gpr .r6 = A + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.src]
  have hm : s₅.mem = (s₁.mem.writeW (B + BitVec.ofNat 64 (16 * j + 8))
      (s₁.mem.readW (A + BitVec.ofNat 64 (16 * j + 8)) 64)) := by
    rw [m₅, m₄, m₃, m₂, r1, a1, addr_add, addr_add]
  have hm₁ : s₁.mem = s.mem.writeW (B + BitVec.ofNat 64 (16 * j))
      (s.mem.readW (A + BitVec.ofNat 64 (16 * j)) 64) := by
    rw [m₁, hi.dst, hi.src, addr_add, addr_add, Nat.add_zero]
  -- `s₁` and `s` agree on `A`'s area.
  have hA₁ : ∀ t < 16 * c, s₁.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [hm₁, writeW_readW_apply, ite_eq_right (not_in_of_disjoint hsep ht (by omega_arith) hn)]
  have hc₅ : s₅.gpr .r3 = BitVec.ofNat 64 (c - (j + 1)) := by
    rw [c₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.cnt,
      VG.Offset.ofNat_sub_ofNat (by omega_arith), show c - j - 1 = c - (j + 1) by omega_arith]
  have hinv : CopyInv A B c s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, hc₅, fun t ht => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), a₃, g₂ _ (by decide), a1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [o₅ _ (by decide), a₄, o₃ _ (by decide), g₂ _ (by decide), r1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [hm, writeW_readW_apply]
      by_cases h8 : 16 * j + 8 ≤ t
      · rw [ite_eq_left (by rw [off_sub_toNat B h8 (by omega_arith)]; omega_arith), off_sub_toNat B h8 (by omega_arith), addr_add,
          show 16 * j + 8 + (t - (16 * j + 8)) = t by omega_arith, hA₁ t (by omega_arith), hAs t (by omega_arith)]
      · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith)), hm₁,
          writeW_readW_apply]
        by_cases h0 : 16 * j ≤ t
        · rw [ite_eq_left (by rw [off_sub_toNat B h0 (by omega_arith)]; omega_arith), off_sub_toNat B h0 (by omega_arith), addr_add,
            show 16 * j + (t - 16 * j) = t by omega_arith, hAs t (by omega_arith)]
        · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith))]
          exact hi.copied t (by omega_arith)
    · have hout : ∀ e, e + 8 ≤ 16 * c → ¬ (x - (B + BitVec.ofNat 64 e)).toNat < 8 := fun e he h =>
        hx _ (List.mem_singleton_self _) (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega_arith))
      rw [hm, writeW_readW_apply, ite_eq_right (hout _ (by omega_arith)), hm₁, writeW_readW_apply,
        ite_eq_right (hout _ (by omega_arith))]
    · rw [o₅ r h3, o₄ r h2, o₃ r h1, g₂ r h4, g₁ r h4, hi.regs r h1 h2 h3 h4]
  have hz : (s₅.gpr .r3 == 0) = decide (c - (j + 1) = 0) := by
    rw [hc₅, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, Bool.eq_iff_iff, beq_iff_eq,
      decide_eq_true_iff]
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega_arith
    · intro h; rw [h]
  by_cases hl : j + 1 = c
  · refine .inl ⟨(eval_nonzero s₅ .r3).trans (by rw [hz]; simp; omega_arith),
      by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_nonzero s₅ .r3).trans (by rw [hz]; simp; omega_arith), c - (j + 1), by omega_arith, j + 1, rfl,
      by omega_arith, hinv⟩

end VG.Proof.Sm4.PPC64LE

end

end


/-!
# A group of blocks of SM4 ECB on PPC64LE

`dataGroup_wp`: one iteration of the data loop copies the group's blocks
(sixteen, or the last one to fifteen) to the tail buffer, transforms it
(`crypt16_wp`, which keeps the data pointer, the blocks left and the
table's end in `r4`–`r11`), copies the blocks back and steps to the next
group.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Sm4.PPC64LE
open VG.Proof.Sm4 (DInv quads ofBlock outBlock not_contains_off blockAt_getD)
open VG.Impl.Aes.PPC64LE (q sb t0 t1 movR ldS stS shrI)

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
  have u := Upd.write s d (s.gpr n ||| s.gpr n)
  ⟨_, by simp only [movR, runBlock_cons, exec_logic, runStep_some, runBlock_nil], u.gpr.trans BitVec.or_self,
    u.other, u.mem, u.rd, u.wr⟩

/-- `r12 := min(r5, 16)`. -/
theorem groupCount_wp {s : State} {v : Nat} (hr : s.gpr .r5 = BitVec.ofNat 64 v) (hv : v < 2 ^ 64) :
    WP isa groupCount s fun s' => s'.gpr .r12 = BitVec.ofNat 64 (min v 16) ∧
      (∀ r, r ≠ .r12 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write t0 (s.gpr .r5 >>> 4)
  have u₁ := Upd.write s t0 (s.gpr .r5 >>> 4)
  have e₁ : runBlock isa [shrI t0 .r5 4] s = some s₁ := by
    simp only [shrI, runBlock_cons, exec_lsr_d (show 4 < 64 by decide), runStep_some, runBlock_nil, s₁]
  have t₁ : s₁.gpr t0 = BitVec.ofNat 64 v >>> 4 := by rw [u₁.gpr, hr]
  have o₁ : ∀ r, r ≠ t0 → s₁.gpr r = s.gpr r := u₁.other
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.ite (decide (16 ≤ v)) ((eval_nonzero s₁ t0).trans (by rw [t₁, lsr4_beq hv]; by_cases h : v < 16 <;> simp [h] <;> omega_using [h]))
    (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := li_ok s₁ .r12 (v := 16)
    refine WP.of_runBlock ⟨s₂, e₂, ?_, fun r h1 h2 => by rw [o₂ r h1, o₁ r h2], m₂, rd₂, wr₂⟩
    rw [r₂, Nat.min_eq_right (by simp at h; omega_using [h])]
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .r12 .r5
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
def MasksAt (m : Mem) (b : Addr) : Prop := ∀ kv ∈ keyMasks, m.readW (wordAddr b kv.1) 64 = kv.2

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

/-- The slots `ScrOk` reads: 48–50, the table (128–383) and 384–401. -/
abbrev scrRegions (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 (8 * 48), 24⟩, ⟨b + BitVec.ofNat 64 (8 * tableSlot), 8 * 256⟩,
    ⟨b + BitVec.ofNat 64 (8 * savedSlot), 144⟩]

theorem mask_range {kv : Nat × BitVec 64} (hkv : kv ∈ keyMasks) : 48 ≤ kv.1 ∧ kv.1 < 51 := by
  simp [keyMasks] at hkv; rcases hkv with h | h | h <;> subst h <;> simp [evenSlot, oddSlot, grpSlot]

theorem ScrOk.frame {s₀ : State} {b : Addr} {E : Nat → Spec.Sm4.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ t ∈ scrRegions b, ∀ r ∈ rs, Region.Disjoint t r) :
    ScrOk s₀ b E m' := by
  have hR : ∀ t ∈ scrRegions b, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
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
  have hR : ∀ t ∈ (scrRegions b).tail, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
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

/-- `copyBlocks` from `r6` to `r7`, `r3` blocks, set up. -/
theorem copy_wp {s : State} {X Y : Addr} {c : Nat} (hc : 0 < c) (hc16 : c ≤ 16)
    (hx : s.gpr .r6 = X) (hy : s.gpr .r7 = Y) (hcx : s.gpr .r3 = BitVec.ofNat 64 c)
    (hX : ∀ t < 2 * c, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (8 * t)) 8)
    (hY : ∀ t < 2 * c, InRegions s.wr (Y + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨X, 16 * c⟩ ⟨Y, 16 * c⟩) :
    WP isa copyBlocks s fun s' => (∀ t < 16 * c, s'.mem (Y + BitVec.ofNat 64 t) = s.mem (X + BitVec.ofNat 64 t)) ∧
      Frame [⟨Y, 16 * c⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r3 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (copyBlocks_wp hc hc16 hX hY hsep ⟨by rw [hx]; simp, by rw [hy]; simp, by rw [hcx, Nat.sub_zero],
    fun t ht => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩)
    fun s' h => ⟨h.copied, h.frame, h.regs, h.rd, h.wr⟩

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : Addr) (n : Nat) (E : Nat → Spec.Sm4.Word) (k : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  r4 : s.gpr .r4 = D + BitVec.ofNat 64 (256 * k)
  r5 : s.gpr .r5 = BitVec.ofNat 64 (n - 16 * k)
  lt : 16 * k < n
  r11 : s.gpr .r11 = b + BitVec.ofNat 64 (8 * tableEnd)
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
    WP isa Impl.Sm4.PPC64LE.group s fun s' => (s'.gpr .r5 = 0 ∧ GDone s₀ b D n E s') ∨
      (s'.gpr .r5 ≠ 0 ∧ GInv s₀ b D n E (k + 1) s') := by
  have hfit := hp.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  rw [slots_eq] at hfit
  let v := n - 16 * k
  let c := min v 16
  have hv : v < 2 ^ 64 := by omega_arith
  have hc0 : 0 < c := by omega_arith
  have hc16 : c ≤ 16 := by omega_arith
  have hkc : 256 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 64 (256 * k)
  let T := b + BitVec.ofNat 64 (8 * tailSlot)
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have inT : ∀ t, t < 32 → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base b (by rw [slots_eq, tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  have inA : ∀ t, t < 2 * c → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)
  have sepAT : Region.Disjoint ⟨A, 16 * c⟩ ⟨T, 16 * c⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq, tailSlot_eq]; omega_arith))
  unfold Impl.Sm4.PPC64LE.group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.r5 hv) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a⟩ := movR_ok s₁ .r6 .r4
  obtain ⟨s₂b, e₂b, r₂b, o₂b, m₂b, rd₂b, wr₂b⟩ := slotAddr_ok s₂a .r7 tailSlot (by decide)
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₂b .r3 .r12
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂b, rd₂a, rd₁]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂b, wr₂a, wr₁]
  have mem₂ : s₂.mem = s.mem := by rw [m₂, m₂b, m₂a, m₁]
  have g₂ : ∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r3 → r ≠ .r12 → r ≠ t0 → s₂.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₂ r h3, o₂b r h2, o₂a r h1, o₁ r h4 h5]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [runBlock_app, runBlock_app, e₂a, Option.bind_some, e₂b, Option.bind_some, e₂], ?_⟩)
  refine WP.mono (copy_wp (X := A) (Y := T) hc0 hc16
    (by rw [o₂ _ (by decide), o₂b _ (by decide), r₂a, o₁ _ (by decide) (by decide), hi.r4])
    (by rw [o₂ _ (by decide), r₂b, o₂a _ (by decide), o₁ _ (by decide) (by decide), hi.base])
    (by rw [r₂, o₂b _ (by decide), o₂a _ (by decide), c₁])
    (fun t ht => by rw [rd₂', wr₂']; exact inRd (inA t ht))
    (fun t ht => by rw [wr₂']; exact inT t (by omega_arith)) sepAT) fun s₃ ⟨cp₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  have f₃' : Frame [⟨T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact f₃
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂']
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂']
  have g₃' : ∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r3 → r ≠ .r12 → r ≠ t0 → s₃.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [g₃ r h1 h2 h3 h5, g₂ r h1 h2 h3 h4 h5]
  have base₃ : s₃.gpr sb = b := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.base]
  have sc₃ : ScrOk s₀ b E s₃.mem := by
    refine hi.scr.frame (mem₂ ▸ f₃) fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> refine VG.Offset.disjoint b ?_ ?_ ?_ <;>
      (try simp only [tailSlot_eq, tableSlot_eq, savedSlot_eq]) <;> omega_arith
  -- The sixteen blocks.
  have hkey : KeyCtx s₃ E :=
    { scr := by rw [base₃, wr₃']; exact hwS
      fit := by rw [base₃, slots_eq]; exact hfit
      keys := fun e he => by rw [base₃]; exact sc₃.keys e he }
  have hr11₃ : s₃.gpr .r11 = s₃.gpr sb + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.r11, base₃]
  refine WP.seq (WP.mono (crypt16_wp hkey (sc₃.masks.ok base₃) hr11₃) fun s₅ ⟨c₅, b₅⟩ => ?_)
  have base₅ : s₅.gpr sb = b := by rw [c₅.base, base₃]
  have f₅ : Frame [⟨b, 8 * tableSlot⟩] s₃.mem s₅.mem := by have := c₅.frame; rw [base₃] at this; exact this
  have sc₅ : ScrOk s₀ b E s₅.mem := by
    refine sc₃.frame2 f₅ (c₅.masks.at base₅) fun t ht r hr => ?_
    simp only [scrRegions, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at ht hr
    subst hr
    rcases ht with rfl | rfl
    · exact VG.Offset.disjoint_base b (by rw [tableSlot_eq]) (by rw [tableSlot_eq]; omega_arith)
    · exact VG.Offset.disjoint_base b (by rw [tableSlot_eq, savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith)
  have k₅ : ∀ r, r ∉ sboxWrites → r ≠ kr → s₅.gpr r = s₃.gpr r := fun r h1 h2 => c₅.keep r h1 h2
  have r4₅ : s₅.gpr .r4 = A := by
    rw [k₅ _ (by decide) (by decide), g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.r4]
  have r5₅ : s₅.gpr .r5 = BitVec.ofNat 64 v := by
    rw [k₅ _ (by decide) (by decide), g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.r5]
  have r11₅ : s₅.gpr .r11 = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [k₅ _ (by decide) (by decide), g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.r11]
  have wr₅' : s₅.wr = s.wr := by rw [c₅.wr, wr₃']
  have rd₅' : s₅.rd = s.rd := by rw [c₅.rd, rd₃']
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r5₅ hv) fun s₇ ⟨c₇, o₇, m₇, rd₇, wr₇⟩ => ?_))
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a⟩ := slotAddr_ok s₇ .r6 tailSlot (by decide)
  obtain ⟨s₈b, e₈b, r₈b, o₈b, m₈b, rd₈b, wr₈b⟩ := movR_ok s₈a .r7 .r4
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := movR_ok s₈b .r3 .r12
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [runBlock_app, e₈a, Option.bind_some,
      show ([movR .r7 .r4, movR .r3 .r12] : List Instr) = [movR .r7 .r4] ++ [movR .r3 .r12] from rfl,
      runBlock_app, e₈b, Option.bind_some, e₈], ?_⟩)
  have mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈b, m₈a, m₇]
  have wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈b, wr₈a, wr₇, wr₅']
  have rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₈b, rd₈a, rd₇, rd₅']
  have g₈ : ∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r3 → r ≠ .r12 → r ≠ t0 → s₈.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₈ r h3, o₈b r h2, o₈a r h1, o₇ r h4 h5]
  refine WP.mono (copy_wp (X := T) (Y := A) hc0 hc16
    (by rw [o₈ _ (by decide), o₈b _ (by decide), r₈a, o₇ _ (by decide) (by decide), base₅])
    (by rw [o₈ _ (by decide), r₈b, o₈a _ (by decide), o₇ _ (by decide) (by decide), r4₅])
    (by rw [r₈, o₈b _ (by decide), o₈a _ (by decide), c₇])
    (fun t ht => by rw [rd₈', wr₈']; exact inRd (inT t (by omega_arith)))
    (fun t ht => by rw [wr₈']; exact inA t ht) sepAT.symm) fun s₉ ⟨cp₉, f₉, g₉, rd₉, wr₉⟩ => ?_
  have g₉' : ∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r3 → r ≠ .r12 → r ≠ t0 → s₉.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [g₉ r h1 h2 h3 h5, g₈ r h1 h2 h3 h4 h5]
  have r12₉ : s₉.gpr .r12 = BitVec.ofNat 64 c := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide), o₈ _ (by decide), o₈b _ (by decide),
      o₈a _ (by decide), c₇]
  have base₉ : s₉.gpr sb = b := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), base₅]
  have r4₉ : s₉.gpr .r4 = A := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), r4₅]
  have r5₉ : s₉.gpr .r5 = BitVec.ofNat 64 v := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), r5₅]
  have r11₉ : s₉.gpr .r11 = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), r11₅]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, wr₈', hi.wr]
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, rd₈', hi.rd]
  -- The scratch buffer and the frame.
  have subS : ∀ {d l : Nat}, d + l ≤ 8 * slots → Region.Sub ⟨b + BitVec.ofNat 64 d, l⟩ ⟨b, 8 * slots⟩ :=
    fun h => VG.Offset.sub_base b h
  have sc₉ : ScrOk s₀ b E s₉.mem := by
    refine (mem₈ ▸ sc₅).frame f₉ fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hsub : Region.Sub t ⟨b, 8 * slots⟩ := by
      simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> refine subS ?_ <;> (try simp only [tableSlot_eq, savedSlot_eq]) <;>
        rw [slots_eq] <;> omega_arith
    exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right hsub).symm
  have fr₉ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s.mem s₉.mem := by
    refine (((mem₂ ▸ f₃).sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₅.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((mem₈ ▸ f₉).sub fun r hr => ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)))
    · simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base D (by omega_arith)
  -- The blocks the sixteen-block code read are the group's, as on entry.
  have hblk : ∀ j < c, tailBlock s₃ j = Spec.Sm4.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * (16 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn]
    rw [base₃, addr_add, addr_add]
    have ht : 16 * j + u < 16 * c := by omega_arith
    have := cp₃ (16 * j + u) ht
    rw [addr_add] at this
    rw [show 8 * tailSlot + 16 * j + u = 8 * tailSlot + (16 * j + u) by omega_arith, this, mem₂, addr_add,
      hi.data _ (by omega_arith), ite_eq_right (by omega_arith),
      show 256 * k + (16 * j + u) = 16 * (16 * k + j) + u by omega_arith]
  have hdata : DInv s₀.mem s₉.mem D n (16 * k + c) (outF s₀.mem D E) := by
    intro i hin
    by_cases hin1 : 256 * k ≤ i ∧ i < 256 * k + 16 * c
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 256 * k) := by
        rw [addr_add, show 256 * k + (i - 256 * k) = i by omega_arith]
      rw [e1, cp₉ _ (by omega_arith), mem₈, ite_eq_left (show i < 16 * (16 * k + c) by omega_arith),
        show i / 16 = 16 * k + (i - 256 * k) / 16 by omega_arith, show i % 16 = (i - 256 * k) % 16 by omega_arith]
      have hj : (i - 256 * k) / 16 < c := by omega_arith
      have eT : T + BitVec.ofNat 64 (i - 256 * k) = s₅.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * ((i - 256 * k) / 16)) +
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
      have hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b, 8 * slots⟩) →
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
  have fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₉.mem := hi.frame.trans fr₉
  -- On to the next group.
  obtain ⟨s₁₀, e₁₀, r₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := subR_ok s₉ .r5 .r5 .r12
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := addI_ok s₁₀ .r4 .r4 (imm := 256) (by decide)
  refine WP.of_runBlock ⟨s₁₁, by
    rw [show ([Instr.sub .r5 .r5 .r12, .addi .r4 .r4 256] : List Instr) =
      [.sub .r5 .r5 .r12] ++ [.addi .r4 .r4 256] from rfl, runBlock_app, e₁₀,
      Option.bind_some, e₁₁], ?_⟩
  have hm : s₁₁.mem = s₉.mem := by rw [m₁₁, m₁₀]
  have r5₁₁ : s₁₁.gpr .r5 = BitVec.ofNat 64 (v - c) := by
    rw [o₁₁ _ (by decide), r₁₀, r5₉, r12₉, VG.Offset.ofNat_sub_ofNat (by omega_arith)]
  have base₁₁ : s₁₁.gpr sb = b := by rw [o₁₁ _ (by decide), o₁₀ _ (by decide), base₉]
  have rd₁₁' : s₁₁.rd = s₀.rd := by rw [rd₁₁, rd₁₀, rd₉']
  have wr₁₁' : s₁₁.wr = s₀.wr := by rw [wr₁₁, wr₁₀, wr₉']
  by_cases hlt : v ≤ 16
  · have hn : 16 * k + c = n := by omega_arith
    refine .inl ⟨by rw [r5₁₁, show v - c = 0 by omega_arith]; rfl, base₁₁, hm ▸ sc₉,
      fun i hi' => by rw [hm, hdata i hi', hn], hm ▸ fr, rd₁₁', wr₁₁'⟩
  · have hc : c = 16 := by omega_arith
    refine .inr ⟨fun h => ?_, base₁₁, ?_, ?_, by omega_arith, ?_, hm ▸ sc₉, ?_, hm ▸ fr, rd₁₁', wr₁₁'⟩
    · have hne : v - c ≠ 0 := by omega_arith
      rw [r5₁₁] at h
      apply hne
      have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
    · rw [r₁₁, o₁₀ _ (by decide), r4₉, addr_add, show 256 * k + 256 = 256 * (k + 1) by omega_arith]
    · rw [r5₁₁, show v - c = n - 16 * (k + 1) by omega_arith]
    · rw [o₁₁ _ (by decide), o₁₀ _ (by decide), r11₉]
    · rw [hm, show 16 * (k + 1) = 16 * k + c by omega_arith]; exact hdata

end VG.Proof.Sm4.PPC64LE
