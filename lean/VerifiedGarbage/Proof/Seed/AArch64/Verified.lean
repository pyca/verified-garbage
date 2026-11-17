module

public import VerifiedGarbage.Proof.Seed.AArch64.ConstantTime
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Spec.Seed.Contract
public import VerifiedGarbage.Proof.Seed.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Seed.AArch64.Lit
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Seed.AArch64.Steps
public import VerifiedGarbage.Proof.Seed.AArch64.Round
public import VerifiedGarbage.Proof.Seed.Rounds
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Seed.AArch64.Ecb`, which this module and modules that import it used -/

section

/-! ### `Seed.AArch64.Setup`, which this module and modules that import it used -/

section

/-!
# Storing to and loading from scratch slots

`stores_ok`: stores of registers to distinct slots, writing only the
scratch buffer; `loads_ok`: loads of distinct registers, other than `x5`,
from slots.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Impl.Aes.AArch64

theorem slot_in_scratch (s : State) {j : Nat} (hj : j < scratchSlots) :
    (scratchR s).Contains (wordAddr (s.gpr .x5) j) (64 / 8) :=
  slot_contains (s.gpr .x5) (n := scratchSlots) hj (by unfold scratchSlots; decide)

theorem slot_off {j : Nat} (hj : j < scratchSlots) : 8 * j % 8 = 0 ∧ 8 * j < 32768 := by
  unfold scratchSlots at hj; omega_using [hj]

/-- The memory after storing `v` in slot `k`. -/
def stMem (s : State) (k : Nat) (v : BitVec 64) : Mem := s.mem.writeW (wordAddr (s.gpr .x5) k) v

theorem exec_st {s : State} (h : Room s) {k : Nat} (hk : k < scratchSlots) (r : Reg) :
    exec (stS k r) s = some (setMem s (stMem s k (s.gpr r))) :=
  exec_str_x (slot_off hk) (h.wr (slot_in_scratch s hk))

theorem exec_ld {s : State} (h : Room s) {k : Nat} (hk : k < scratchSlots) (r : Reg) :
    exec (ldS r k) s = some (s.write .x r (slotW s k)) :=
  exec_ldr_x (slot_off hk) (h.rw (slot_in_scratch s hk))

theorem slotW_stMem (s : State) {k : Nat} (hk : k < scratchSlots) (v : BitVec 64) {j : Nat}
    (hj : j < scratchSlots) : slotW (setMem s (stMem s k v)) j = if j = k then v else slotW s j := by
  unfold scratchSlots at hk hj
  show (stMem s k v).readW (wordAddr (s.gpr .x5) j) 64 = _
  simp only [stMem]
  split
  · subst j; exact Mem.readW_writeW_self64 _ _ _
  · rename_i hne
    rw [Mem.readW_writeW_sep (slot_sep _ (by omega_using [hj]) (by omega_using [hk]) hne) (by decide)]
    rfl

theorem stMem_frame {s : State} {k : Nat} (hk : k < scratchSlots) (v : BitVec 64) :
    Frame [scratchR s] s.mem (stMem s k v) :=
  (Frame.refl _ _).writeW List.mem_cons_self _ (slot_in_scratch s hk)

theorem slotW_write (s : State) {r : Reg} (hr : r ≠ .x5) (v : BitVec 64) (j : Nat) :
    slotW (s.write .x r v) j = slotW s j := by
  show s.mem.readW (wordAddr ((s.write .x r v).gpr .x5) j) 64 = s.mem.readW (wordAddr (s.gpr .x5) j) 64
  rw [gpr_write_of_ne _ _ _ (Ne.symm hr)]

/-- A block of stores of registers to distinct scratch slots. -/
theorem stores_ok {s : State} (h : Room s) (l : List (Nat × Reg)) (hl : ∀ p ∈ l, p.1 < scratchSlots)
    (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (l.map fun p => stS p.1 p.2) s = some s' ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [scratchR s] s.mem s'.mem ∧
      (∀ p ∈ l, slotW s' p.1 = s.gpr p.2) ∧
      (∀ x < scratchSlots, (∀ p ∈ l, p.1 ≠ x) → slotW s' x = slotW s x) := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, rfl, rfl, rfl, Frame.refl _ _, (fun _ h => by cases h),
      fun _ _ _ => rfl⟩
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    have e := exec_st (r := p.2) h hp
    let s₁ : State := setMem s (stMem s p.1 (s.gpr p.2))
    have h₁ : Room s₁ := h
    have hd' : (l.map (·.1)).Nodup := (List.nodup_cons.mp hd).2
    have hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', g', rd', wr', sp', f', set', keep'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hd'
    refine ⟨s', ?_, g', rd', wr', sp', (stMem_frame hp _).trans f', fun q hq => ?_,
      fun x hx hne => ?_⟩
    · rw [List.map_cons, runBlock_cons, e, runStep_some]; exact run'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ hp (fun r hr he => hn (he ▸ List.mem_map_of_mem hr)), slotW_stMem s hp _ hp]
        simp
      · exact set' q hq
    · rw [keep' x hx (fun q hq => hne q (List.mem_cons_of_mem _ hq)), slotW_stMem s hp _ hx]
      simp [Ne.symm (hne p List.mem_cons_self)]

/-- A block of loads of distinct registers, other than `x5`, from scratch slots. -/
theorem loads_ok {s : State} (h : Room s) (l : List (Reg × Nat))
    (hl : ∀ p ∈ l, p.2 < scratchSlots ∧ p.1 ≠ .x5) (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (l.map fun p => ldS p.1 p.2) s = some s' ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ p ∈ l, s'.gpr p.1 = slotW s p.2) ∧ (∀ r, (∀ p ∈ l, p.1 ≠ r) → s'.gpr r = s.gpr r) := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, rfl, (fun _ h => by cases h), fun _ _ => rfl⟩
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    have e := exec_ld h hp.1 p.1
    let s₁ := s.write .x p.1 (slotW s p.2)
    have c₁ : s₁.gpr .x5 = s.gpr .x5 := gpr_write_of_ne _ _ _ (Ne.symm hp.2)
    have h₁ : Room s₁ := room_congr h c₁ rfl
    have hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', m', sp', set', keep'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (List.nodup_cons.mp hd).2
    have sl₁ : ∀ j, slotW s₁ j = slotW s j := slotW_write s hp.2 _
    refine ⟨s', ?_, by rw [m']; rfl, by rw [sp']; rfl, fun q hq => ?_, fun r hr => ?_⟩
    · rw [List.map_cons, runBlock_cons, e, runStep_some]; exact run'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ (fun r hr he => hn (by rw [← he]; exact List.mem_map_of_mem hr))]
        simp [s₁, gpr_write]
      · rw [set' q hq, sl₁]
    · rw [keep' r (fun q hq => hr q (List.mem_cons_of_mem _ hq))]
      simp only [s₁]
      rw [gpr_write_of_ne _ _ _ (Ne.symm (hr p List.mem_cons_self))]

end VG.Proof.Seed.AArch64

end

end

/-! ### `Seed.AArch64.Batch`, which this module and modules that import it used -/

section

/-! ### `Seed.AArch64.Rounds`, which only this module used -/

section

/-!
# Sixteen rounds on AArch64

`rounds_ok`: `rounds d` does sixteen rounds on every lane, with round
`j + 1`'s key at `x0 + j * step` (`kp`), and moves `x0` back.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Proof.Seed

/-- Where round `j + 1`'s key is, from `p`. -/
def kp (d : Spec.Seed.Direction) (p : Addr) (j : Nat) : Addr := p + BitVec.ofNat 64 j * stepW d

theorem kp_succ (d : Spec.Seed.Direction) (p : Addr) (j : Nat) : kp d p j + stepW d = kp d p (j + 1) := by
  simp only [kp, BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]

theorem exec_keyBack (d : Spec.Seed.Direction) (s : State) :
    exec (keyBack d) s = some (s.write .x .x0 (s.gpr .x0 - BitVec.ofNat 64 16 * stepW d)) := by
  cases d
  · rw [keyBack, exec_subImm_x (by decide), read_x]; rfl
  · rw [keyBack, exec_addImm_x (by decide), read_x, show BitVec.ofNat 64 16 * stepW .decrypt =
      -BitVec.ofNat 64 128 by decide, BitVec.sub_neg]

theorem kp_back (d : Spec.Seed.Direction) (p : Addr) : kp d p 16 - BitVec.ofNat 64 16 * stepW d = p := by
  rw [kp, BitVec.add_sub_cancel]

/-- The round keys, read from memory `m`. -/
def keysAt (d : Spec.Seed.Direction) (m : Mem) (p : Addr) (j : Nat) : Spec.Seed.Word × Spec.Seed.Word :=
  (m.readW (kp d p j) 32, m.readW (kp d p j + 4) 32)

/-- The keys can be read and are outside the scratch buffer. -/
def KeysOk (d : Spec.Seed.Direction) (s : State) (p : Addr) : Prop :=
  ∀ j < 16, InRegions (s.rd ++ s.wr) (kp d p j) 4 ∧ InRegions (s.rd ++ s.wr) (kp d p j + 4) 4 ∧
    Region.Disjoint ⟨kp d p j, 8⟩ (scratchR s)

/-- After `16 - m` rounds, with `m` left. -/
structure RoundsInv (d : Spec.Seed.Direction) (s₀ : State) (m : Nat) (s : State) : Prop where
  le : 1 ≤ m ∧ m ≤ 16
  quads : ∀ b < 16, quad s b = roundsN (keysAt d s₀.mem (s₀.gpr .x0)) (16 - m) (quad s₀ b)
  room : Room s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = kp d (s₀.gpr .x0) (16 - m)
  x4 : s.gpr .x4 = BitVec.ofNat 64 m
  regs : ∀ r ∈ [Reg.x1, .x2, .x5], s.gpr r = s₀.gpr r
  frame : Frame [workR s₀] s₀.mem s.mem

theorem contains_prefix {a : Addr} {k n : Nat} (h : k ≤ n) : (⟨a, n⟩ : Region).Contains a k := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

theorem x4_sub (m : Nat) (h : 1 ≤ m) (h' : m ≤ 16) :
    BitVec.ofNat 64 m - 1 = BitVec.ofNat 64 (m - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem rounds_ok (d : Spec.Seed.Direction) {s : State} (h : Room s) (hk : KeysOk d s (s.gpr .x0)) :
    WP isa (rounds d) s (fun s' =>
      (∀ b < 16, quad s' b = roundsN (keysAt d s.mem (s.gpr .x0)) 16 (quad s b)) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ [Reg.x0, .x1, .x2, .x5], s'.gpr r = s.gpr r) ∧
      Frame [workR s] s.mem s'.mem) := by
  let s1 := s.write .x .x4 ((16 : BitVec 16).setWidth 64 <<< (16 * 0))
  have e1 : runBlock isa [.movz .x .x4 16 0] s = some s1 := rfl
  have q1 : ∀ b, quad s1 b = quad s b := fun b => by
    simp only [quad, s1, lv_write _ _ _ (show ¬ Reg.x5 = .x4 by decide)]
  refine WP.seq (WP.of_runBlock ⟨s1, e1, ?_⟩)
  refine WP.seq (WP.loop (M := isa) (fun m t => RoundsInv d s m t) ?_ 16 s1 ?_)
  · intro m t inv
    have hi : 16 - m < 16 := by have := inv.le; omega_using [this]
    obtain ⟨hk0, hk1, hdis⟩ := hk (16 - m) hi
    have hk0' : InRegions (t.rd ++ t.wr) (t.gpr .x0) 4 := by rw [inv.rd, inv.wr, inv.x0]; exact hk0
    have hk1' : InRegions (t.rd ++ t.wr) (t.gpr .x0 + 4) 4 := by rw [inv.rd, inv.wr, inv.x0]; exact hk1
    obtain ⟨t', ht', hq, hroom, hrd, hwr, hsp, hx0, hx4, hx1, hx2, hx5, hfr⟩ :=
      round_ok d inv.room hk0' hk1'
    -- The key, from the original memory.
    have hkey : (t.mem.readW (t.gpr .x0) 32, t.mem.readW (t.gpr .x0 + 4) 32) =
        keysAt d s.mem (s.gpr .x0) (16 - m) := by
      simp only [keysAt, inv.x0]
      have hd : ∀ r ∈ [workR s], Region.Disjoint ⟨kp d (s.gpr .x0) (16 - m), 8⟩ r := by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact hdis.sub_right (Region.sub_prefix (by unfold scratchSlots; omega_using []))
      refine Eq.mpr (Prod.mk.injEq _ _ _ _) ⟨?_, ?_⟩
      · exact inv.frame.readW (contains_prefix (by decide)) hd (by decide)
      · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
        exact inv.frame.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega_using []) (by omega_using []))
          hd (by decide)
    refine WP.of_runBlock ⟨t', ht', ?_⟩
    have hquads : ∀ b < 16, quad t' b = roundsN (keysAt d s.mem (s.gpr .x0)) (16 - (m - 1)) (quad s b) := by
      intro b hb
      rw [hq b hb, hkey, inv.quads b hb, show 16 - (m - 1) = 16 - m + 1 by have := inv.le; omega_using [this],
        roundsN_succ]
    have hx4' : t'.gpr .x4 = BitVec.ofNat 64 (m - 1) := by
      rw [hx4, inv.x4, x4_sub m inv.le.1 inv.le.2]
    have hregs : ∀ r ∈ [Reg.x1, .x2, .x5], t'.gpr r = s.gpr r := by
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hx1]; exact inv.regs _ (by simp)
      · rw [hx2]; exact inv.regs _ (by simp)
      · rw [hx5]; exact inv.regs _ (by simp)
    have hframe : Frame [workR s] s.mem t'.mem := by
      refine inv.frame.trans ?_
      simpa [workR, inv.regs .x5 (by simp)] using hfr
    have hc : isa.eval (.nonzero .x .x4) t' = some (BitVec.ofNat 64 (m - 1) != 0) := by
      show some (t'.read .x .x4 != 0) = _
      rw [read_x, hx4']
    by_cases hm1 : m = 1
    · subst hm1
      left
      refine ⟨by rw [hc]; rfl, ?_⟩
      let u := t'.write .x .x0 (t'.gpr .x0 - BitVec.ofNat 64 16 * stepW d)
      refine WP.of_runBlock ⟨u, by rw [runBlock_cons, exec_keyBack, runStep_some, runBlock_nil], ?_⟩
      have hu5 : u.gpr .x5 = t'.gpr .x5 := gpr_write_of_ne _ _ _ (by decide)
      refine ⟨fun b hb => ?_, room_congr hroom hu5 rfl, by rw [rd_write, hrd, inv.rd],
        by rw [wr_write, hwr, inv.wr], by rw [sp_write, hsp, inv.sp], fun r hr => ?_, by rw [mem_write]; exact hframe⟩
      · have : quad u b = quad t' b := by simp only [quad, u, lv_write _ _ _ (show ¬ Reg.x5 = .x0 by decide)]
        rw [this, hquads b hb]
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | hr
        · rw [gpr_write_self, BitVec.setWidth_eq, hx0, inv.x0, kp_succ, kp_back]
        · rw [gpr_write_of_ne _ _ _ (by rcases hr with rfl | rfl | rfl <;> decide)]
          exact hregs _ (by simpa using hr)
    · right
      refine ⟨?_, m - 1, by omega_using [hi], ⟨by have := inv.le; omega_using [hm1, this], hquads, hroom, by rw [hrd, inv.rd],
        by rw [hwr, inv.wr], by rw [hsp, inv.sp], ?_, hx4', hregs, hframe⟩⟩
      · rw [hc]
        have : (BitVec.ofNat 64 (m - 1) != 0) = true := by
          simp only [bne_iff_ne, ne_eq]
          intro h0
          have hm2 : 2 ≤ m := by have := inv.le; omega_using [hi, hm1]
          have hm16 := inv.le.2
          have := congrArg BitVec.toNat h0
          rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mod_eq_of_lt (by omega_using [hm16])] at this
          omega_using [hi, hsp, hx0, hx4, hx1, hx2, hx5, hx4', hm1, h0, hm2, hm16, this]
        rw [this]
      · rw [hx0, inv.x0, kp_succ, show 16 - m + 1 = 16 - (m - 1) by have := inv.le; omega_using [this]]
  · refine ⟨by omega_using [], fun b _ => by rw [q1]; rfl, room_congr h rfl rfl, rfl, rfl, rfl,
      by simp [s1, kp, gpr_write], rfl, fun r hr => ?_, Frame.refl _ _⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rfl

end VG.Proof.Seed.AArch64

end

end

/-! ### `Seed.AArch64.Copy`, which only this module used -/

section

/-!
# Copying blocks into the arrays and back

As on x86-64: `copyIn_loop`: the loop of `copyInBody` copies `m` blocks from
`p` into lanes `0 … m - 1` of the arrays, each word byte-reversed (`bw`, a
block's big-endian word). `copyOut_loop`: the loop of `copyOutBody` copies
them back, `R` first.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64

-- The copies share one set of rewrites, not all of which each uses.
set_option linter.unusedSimpArgs false

/-- Word `w` of block `b` from `p`, big-endian. -/
def bw (m : Mem) (p : Addr) (b w : Nat) : BitVec 32 :=
  rev32 (m.readW (p + BitVec.ofNat 64 (16 * b + 4 * w)) 32)

theorem mem_arrA_of {w : Nat} (hw : w < 4) : arrSlot w ∈ arrays := by
  rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> decide

/-- What the copy into the arrays needs. -/
structure CopyPre (s : State) (p : Addr) (m : Nat) : Prop where
  room : Room s
  le : 1 ≤ m ∧ m ≤ 16
  read : ∀ b < m, ∀ w < 4, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (16 * b + 4 * w)) 4
  sep : Region.Disjoint ⟨p, 16 * m⟩ (arraysR s)

/-- After `j` blocks of the copy in. -/
structure CopyInInv (s₀ : State) (p : Addr) (m j : Nat) (s : State) : Prop where
  le : j ≤ m
  x3 : s.gpr .x3 = p + BitVec.ofNat 64 (16 * j)
  x4 : s.gpr .x4 = s₀.gpr .x5 + BitVec.ofNat 64 (4 * j)
  x15 : s.gpr .x15 = BitVec.ofNat 64 (m - j)
  lanes : ∀ w < 4, ∀ b < j, lv s (arrSlot w) b = bw s₀.mem p b w
  frame : Frame [arraysR s₀] s₀.mem s.mem
  regs : ∀ r, r ≠ .x14 → r ≠ .x4 → r ≠ .x15 → r ≠ .x3 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The copy of word `w` of a block. -/
def inWord (w : Nat) : List Instr :=
  [.ldr .w .x14 .x3 (4 * w), .rev32 .x14 .x14, .str .w .x14 .x4 (8 * arrSlot w)]

theorem copyInBody_eq : copyInBody = inWord 0 ++ (inWord 1 ++ (inWord 2 ++ (inWord 3 ++
    ([.addImm .x .x3 .x3 16, .addImm .x .x4 .x4 4, .subImm .x .x15 .x15 1] : List Instr)))) := rfl

theorem arr_off (w j : Nat) (b : Addr) :
    b + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 (8 * arrSlot w) = b + BitVec.ofNat 64 (8 * arrSlot w + 4 * j) := by
  rw [Offset.add_add, Nat.add_comm]

theorem arr_ok {w : Nat} (hw : w < 4) : 8 * arrSlot w % 4 = 0 ∧ 8 * arrSlot w < 16384 := by
  unfold arrSlot; omega_arith

/-- One word of a block into its lane. -/
theorem copyInWord_ok {w j : Nat} (hw : w < 4) (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .x4 = s.gpr .x5 + BitVec.ofNat 64 (4 * j))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (4 * w)) 4) :
    ∃ s', runBlock isa (inWord w) s = some s' ∧
      s'.mem = s.mem.writeW (laneA s (arrSlot w) j)
        (rev32 (s.mem.readW (s.gpr .x3 + BitVec.ofNat 64 (4 * w)) 32)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ≠ .x14 → s'.gpr r = s.gpr r) := by
  obtain hL : arrSlot w ∈ arrays := mem_arrA_of hw
  obtain hla : s.gpr .x4 + BitVec.ofNat 64 (8 * arrSlot w) = laneA s (arrSlot w) j := by
    rw [hrb, arr_off _ _]; rfl
  unfold inWord
  let v := s.mem.readW (s.gpr .x3 + BitVec.ofNat 64 (4 * w)) 32
  let s1 := s.write .w .x14 v
  let s2 := s1.write .w .x14 (rev32 (s1.read .w .x14))
  obtain e1 : exec (.ldr .w .x14 .x3 (4 * w)) s = some s1 := exec_ldr_w (by omega_arith) hr
  have e2 : exec (.rev32 .x14 .x14) s1 = some s2 := rfl
  obtain h4 : s2.gpr .x4 = s.gpr .x4 := by simp [s2, s1, gpr_write]
  obtain e3 := exec_str_w (s := s2) (t := .x14) (n := .x4) (arr_ok hw)
    (by rw [h4, hla]; simp only [s2, s1, wr_write]; exact lane_wr h hL hj)
  rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3, runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r hr => ?_⟩
  · show s2.mem.writeW _ _ = _
    rw [h4, hla]
    simp [s2, s1, gpr_write, mem_write, State.read, setWidth_setWidth_32, v]
  · simp [s2, s1, gpr_write, hr]

/-- The copy of one block into lane `j`, as writes of the block's words. -/
def inSpec (m : Mem) (q : Addr) : LaneSpec :=
  (List.range 4).map fun w => (arrSlot w, fun _ => rev32 (m.readW (q + BitVec.ofNat 64 (4 * w)) 32))

theorem inSpec_dests (m : Mem) (q : Addr) : ∀ kv ∈ inSpec m q, kv.1 ∈ arrays := by
  intro kv hkv
  simp only [inSpec, List.mem_map, List.mem_range] at hkv
  obtain ⟨w, hw, rfl⟩ := hkv
  exact mem_arrA_of hw

theorem copyInBody_ok {j : Nat} (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .x4 = s.gpr .x5 + BitVec.ofNat 64 (4 * j))
    (hr : ∀ w < 4, InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (4 * w)) 4)
    (hsep : ∀ w < 4, Region.Disjoint ⟨s.gpr .x3 + BitVec.ofNat 64 (4 * w), 4⟩ (arraysR s)) :
    ∃ s', runBlock isa copyInBody s = some s' ∧
      s'.mem = laneWrites s (inSpec s.mem (s.gpr .x3)) j ∧
      s'.gpr .x3 = s.gpr .x3 + 16 ∧ s'.gpr .x4 = s.gpr .x4 + 4 ∧
      s'.gpr .x15 = s.gpr .x15 - 1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x14 → r ≠ .x4 → r ≠ .x15 → r ≠ .x3 → s'.gpr r = s.gpr r) := by
  -- The block's words keep their values while the lanes are written.
  obtain hkeep : ∀ (t : State), Frame [arraysR s] s.mem t.mem → ∀ w < 4,
      t.mem.readW (s.gpr .x3 + BitVec.ofNat 64 (4 * w)) 32 =
        s.mem.readW (s.gpr .x3 + BitVec.ofNat 64 (4 * w)) 32 := by
    intro t ht w hw
    refine ht.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'; exact hsep w hw
  obtain ⟨s1, e1, m1, rd1, wr1, sp1, g1⟩ := copyInWord_ok (w := 0) (by decide) hj s h hrb (hr 0 (by decide))
  obtain h1 : Room s1 := room_congr h (g1 _ (by decide)) wr1
  obtain ⟨s2, e2, m2, rd2, wr2, sp2, g2⟩ := copyInWord_ok (w := 1) (by decide) hj s1 h1
    (by rw [g1 _ (by decide), g1 _ (by decide), hrb]) (by rw [rd1, wr1, g1 _ (by decide)]; exact hr 1 (by decide))
  obtain h2 : Room s2 := room_congr h1 (g2 _ (by decide)) wr2
  obtain ⟨s3, e3, m3, rd3, wr3, sp3, g3⟩ := copyInWord_ok (w := 2) (by decide) hj s2 h2
    (by rw [g2 _ (by decide), g2 _ (by decide), g1 _ (by decide), g1 _ (by decide), hrb])
    (by rw [rd2, wr2, rd1, wr1, g2 _ (by decide), g1 _ (by decide)]; exact hr 2 (by decide))
  obtain h3 : Room s3 := room_congr h2 (g3 _ (by decide)) wr3
  obtain ⟨s4, e4, m4, rd4, wr4, sp4, g4⟩ := copyInWord_ok (w := 3) (by decide) hj s3 h3
    (by rw [g3 _ (by decide), g3 _ (by decide), g2 _ (by decide), g2 _ (by decide), g1 _ (by decide),
      g1 _ (by decide), hrb])
    (by rw [rd3, wr3, rd2, wr2, rd1, wr1, g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)];
        exact hr 3 (by decide))
  let s5 := s4.write .x .x3 (s4.read .x .x3 + BitVec.ofNat _ 16)
  let s6 := s5.write .x .x4 (s5.read .x .x4 + BitVec.ofNat _ 4)
  let s7 := s6.write .x .x15 (s6.read .x .x15 - BitVec.ofNat _ 1)
  obtain hrun : runBlock isa copyInBody s = some s7 := by
    rw [copyInBody_eq]
    rw [runBlock_append, e1, Option.bind_some, runBlock_append, e2, Option.bind_some, runBlock_append, e3,
      Option.bind_some, runBlock_append, e4, Option.bind_some, runBlock_cons, exec_addImm_x (by decide),
      runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil]
  -- Registers through the words.
  obtain r9s : ∀ t ∈ [s1, s2, s3, s4], t.gpr .x5 = s.gpr .x5 := by
    intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact g1 _ (by decide)
    · rw [g2 _ (by decide), g1 _ (by decide)]
    · rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
    · rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  obtain r10s : ∀ t ∈ [s1, s2, s3, s4], t.gpr .x3 = s.gpr .x3 := by
    intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact g1 _ (by decide)
    · rw [g2 _ (by decide), g1 _ (by decide)]
    · rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
    · rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  obtain lA : ∀ t ∈ [s1, s2, s3, s4], ∀ k, laneA t k j = laneA s k j := by
    intro t ht k; simp only [laneA, r9s t ht]
  -- Memory.
  let v (w : Nat) := rev32 (s.mem.readW (s.gpr .x3 + BitVec.ofNat 64 (4 * w)) 32)
  obtain f1 : Frame [arraysR s] s.mem s1.mem := by
    rw [m1]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (lane_inArrays (mem_arrA_of (by decide)) hj s)
  obtain f2 : Frame [arraysR s] s.mem s2.mem := by
    rw [m2, lA s1 (by simp)]; exact f1.writeW List.mem_cons_self _ (lane_inArrays (mem_arrA_of (by decide)) hj s)
  obtain f3 : Frame [arraysR s] s.mem s3.mem := by
    rw [m3, lA s2 (by simp)]; exact f2.writeW List.mem_cons_self _ (lane_inArrays (mem_arrA_of (by decide)) hj s)
  obtain mm : s4.mem = (((s.mem.writeW (laneA s (arrSlot 0) j) (v 0)).writeW (laneA s (arrSlot 1) j) (v 1)).writeW
      (laneA s (arrSlot 2) j) (v 2)).writeW (laneA s (arrSlot 3) j) (v 3) := by
    rw [m4, lA s3 (by simp), r10s s3 (by simp), hkeep s3 f3 3 (by decide), m3, lA s2 (by simp),
      r10s s2 (by simp), hkeep s2 f2 2 (by decide), m2, lA s1 (by simp), r10s s1 (by simp),
      hkeep s1 f1 1 (by decide), m1]
  obtain r10_4 := r10s s4 (by simp)
  obtain rbx_4 : s4.gpr .x4 = s.gpr .x4 := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  obtain rcx_4 : s4.gpr .x15 = s.gpr .x15 := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  refine ⟨s7, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_⟩
  · simp only [s7, s6, s5, mem_write]
    rw [mm]
    simp only [laneWrites, inSpec, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.foldl_cons, List.foldl_nil, List.singleton_append, List.cons_append,
      List.map_cons]
    rfl
  · simp [s7, s6, s5, gpr_write, read_x, r10_4]
  · simp [s7, s6, s5, gpr_write, read_x, rbx_4]
  · simp [s7, s6, s5, gpr_write, read_x, rcx_4]
  · simp only [s7, s6, s5, rd_write, rd4, rd3, rd2, rd1]
  · simp only [s7, s6, s5, wr_write, wr4, wr3, wr2, wr1]
  · simp only [s7, s6, s5, sp_write, sp4, sp3, sp2, sp1]
  · simp only [s7, s6, s5, gpr_write, h3, h2, h4, ↓reduceIte]
    rw [g4 _ h1, g3 _ h1, g2 _ h1, g1 _ h1]

theorem cnt_ne_zero {k : Nat} (h1 : 2 ≤ k) (h2 : k ≤ 16) :
    (BitVec.ofNat 64 k - 1 != 0) = true := by
  simp only [bne_iff_ne, ne_eq]
  intro h0
  have := congrArg BitVec.toNat h0
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_arith)] at this
  omega_arith

theorem cnt_sub1 {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 16) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) :=
  x4_sub k h1 h2

theorem copyIn_loop {s₀ : State} {p : Addr} {m : Nat} (hpre : CopyPre s₀ p m) :
    ∀ k s, CopyInInv s₀ p m (m - k) s → 1 ≤ k → k ≤ m →
      WP isa (.loop (.block copyInBody) (.nonzero .x .x15)) s (fun s' => CopyInInv s₀ p m m s') := by
  intro k s hs hk1 hkm
  refine WP.loop (M := isa) (fun k t => CopyInInv s₀ p m (m - k) t ∧ 1 ≤ k ∧ k ≤ m) ?_ k s ⟨hs, hk1, hkm⟩
  intro k t ⟨inv, hk1, hkm⟩
  have hm16 := hpre.le.2
  let j := m - k
  obtain hj : j < 16 := by omega_arith
  obtain hr9 : t.gpr .x5 = s₀.gpr .x5 := inv.regs _ (by decide) (by decide) (by decide) (by decide)
  obtain hroom : Room t := room_congr hpre.room hr9 inv.wr
  obtain hrb : t.gpr .x4 = t.gpr .x5 + BitVec.ofNat 64 (4 * j) := by rw [inv.x4, hr9]
  obtain hdata : ∀ w < 4, t.gpr .x3 + BitVec.ofNat 64 (4 * w) = p + BitVec.ofNat 64 (16 * j + 4 * w) := by
    intro w _; rw [inv.x3, Offset.add_add]
  obtain hr : ∀ w < 4, InRegions (t.rd ++ t.wr) (t.gpr .x3 + BitVec.ofNat 64 (4 * w)) 4 := by
    intro w hw; rw [hdata w hw, inv.rd, inv.wr]; exact hpre.read j (by omega_arith) w hw
  obtain harr : arraysR t = arraysR s₀ := by simp [arraysR, hr9]
  obtain hsep : ∀ w < 4, Region.Disjoint ⟨t.gpr .x3 + BitVec.ofNat 64 (4 * w), 4⟩ (arraysR t) := by
    intro w hw
    rw [hdata w hw, harr]
    exact hpre.sep.sub_left (Offset.sub_base p (by omega_arith))
  obtain ⟨t', ht', hmem, hr10, hrbx, hrcx, hrd, hwr, hsp, hregs⟩ := copyInBody_ok hj t hroom hrb hr hsep
  refine WP.of_runBlock ⟨t', ht', ?_⟩
  obtain hr9' : t'.gpr .x5 = t.gpr .x5 := hregs _ (by decide) (by decide) (by decide) (by decide)
  obtain inv' : CopyInInv s₀ p m (j + 1) t' := by
    refine ⟨by omega_arith, ?_, ?_, ?_, fun w hw b hb => ?_, ?_, fun r h1 h2 h3 h4 => ?_, by rw [hsp, inv.sp],
      by rw [hrd, inv.rd], by rw [hwr, inv.wr]⟩
    · rw [hr10, inv.x3, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add]; congr 2
    · rw [hrbx, inv.x4, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    · rw [hrcx, inv.x15, show m - j = k by omega_arith, cnt_sub1 hk1 (by omega_arith)]; congr 1; omega_arith
    · have hl : lv t' (arrSlot w) b = (laneWrites t (inSpec t.mem (t.gpr .x3)) j).readW (laneA t (arrSlot w) b) 32 := by
        rw [← hmem]; simp only [lv, laneA, hr9']
      rw [hl, lv_laneWrites (inSpec_dests _ _) t (mem_arrA_of hw) (by omega_arith) hj]
      by_cases hbj : b = j
      · subst hbj
        simp only [ite_true, newVal, inSpec, List.range_succ, List.range_zero, List.nil_append,
          List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.singleton_append,
          List.cons_append]
        rw [bw, ← hdata w hw]
        obtain hkeep : t.mem.readW (t.gpr .x3 + BitVec.ofNat 64 (4 * w)) 32 =
            s₀.mem.readW (t.gpr .x3 + BitVec.ofNat 64 (4 * w)) 32 := by
          refine inv.frame.readW (Region.contains_self _ _) ?_ (by decide)
          intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'; rw [← harr]; exact hsep w hw
        rw [← hkeep]
        rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> simp [arrSlot]
      · rw [ite_eq_right hbj]; exact inv.lanes w hw b (by omega_arith)
    · refine inv.frame.trans ?_
      have := laneWrites_frame (inSpec_dests t.mem (t.gpr .x3)) t (b := j) hj
      rw [← hmem, harr] at this; exact this
    · rw [hregs r h1 h2 h3 h4]; exact inv.regs r h1 h2 h3 h4
  by_cases hk : k = 1
  · subst hk
    left
    obtain hjm : j + 1 = m := by omega_arith
    refine ⟨?_, hjm ▸ inv'⟩
    show some (t'.read .x .x15 != 0) = some false
    rw [read_x, hrcx, inv.x15, show m - (m - 1) = 1 by omega_arith]; rfl
  · right
    refine ⟨?_, k - 1, by omega_arith, ⟨by simpa [show j + 1 = m - (k - 1) by omega_arith] using inv', by omega_arith, by omega_arith⟩⟩
    show some (t'.read .x .x15 != 0) = some true
    rw [read_x, hrcx, inv.x15, show m - (m - k) = k by omega_arith, cnt_ne_zero (by omega_arith) (by omega_arith)]

/-! ## Copying out -/

/-- Byte `j` (in memory order) of a byte-swapped word is byte `3 - j` of the word. -/
theorem rev32_byte (x : BitVec 32) {j : Nat} (hj : j < 4) :
    (rev32 x).extractLsb' (8 * j) 8 = (x >>> (8 * (3 - j))).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain h4 := Proof.Seed.getLsbD_append4 (x.extractLsb' 0 8) (x.extractLsb' 8 8) (x.extractLsb' 16 8)
    (x.extractLsb' 24 8) hi
  obtain e : ((rev32 x).extractLsb' (8 * j) 8).getLsbD i = (rev32 x).getLsbD (8 * j + i) := by
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [e]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  unfold rev32
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega_arith) with rfl | rfl | rfl | rfl
  · rw [h4.1]; simp [BitVec.getLsbD_extractLsb', hi]
  · rw [h4.2.1]; simp [BitVec.getLsbD_extractLsb', hi]
  · rw [h4.2.2.1]; simp [BitVec.getLsbD_extractLsb', hi]
  · rw [h4.2.2.2]; simp [BitVec.getLsbD_extractLsb', hi]

/-- A byte of the 4 bytes a 32-bit write writes. -/
theorem writeW32_at (m : Mem) (a : Addr) (v : BitVec 32) {d i : Nat} (h1 : d ≤ i) (h2 : i < d + 4)
    (hi : i < 2 ^ 64) :
    (m.writeW (a + BitVec.ofNat 64 d) v) (a + BitVec.ofNat 64 i) = v.extractLsb' (8 * (i - d)) 8 := by
  simp only [Mem.writeW, Mem.write, Offset.sub_toNat a h1 hi, show i - d < 32 / 8 by omega_arith, ite_true,
    BitVec.setWidth_eq]

/-- A byte outside the 4 bytes a 32-bit write writes. -/
theorem writeW32_off (m : Mem) (a : Addr) (v : BitVec 32) {d i : Nat} (h : i < d ∨ d + 4 ≤ i)
    (hd : d + 4 ≤ 2 ^ 64) (hi : i < 2 ^ 64) :
    (m.writeW (a + BitVec.ofNat 64 d) v) (a + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i) := by
  apply Mem.write_apply
  have := Offset.sep a (d := i) (n := 1) (e := d) (k := 4) (by omega_arith) (by omega_arith) hd
  exact this _ (by simp)

/-- The four byte-swapped words `y` written from `a` are the block of their big-endian bytes. -/
theorem block_writes (m : Mem) (a : Addr) (y : Nat → BitVec 32) {i : Nat} (hi : i < 16) :
    ((((m.writeW (a + BitVec.ofNat 64 0) (rev32 (y 0))).writeW (a + BitVec.ofNat 64 4) (rev32 (y 1))).writeW
      (a + BitVec.ofNat 64 8) (rev32 (y 2))).writeW (a + BitVec.ofNat 64 12) (rev32 (y 3)))
      (a + BitVec.ofNat 64 i) = (y (i / 4) >>> (8 * (3 - i % 4))).setWidth 8 := by
  rcases (show i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3 by omega_arith) with h | h | h | h
  · rw [writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW32_at _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      rev32_byte _ (by omega_arith), h]
    congr 3; omega_arith
  · rw [writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      writeW32_at _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rev32_byte _ (by omega_arith), h]
    congr 3; omega_arith
  · rw [writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW32_at _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      rev32_byte _ (by omega_arith), h]
    congr 3; omega_arith
  · rw [writeW32_at _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rev32_byte _ (by omega_arith), h]
    congr 3; omega_arith

/-- The copy of word `w` of a block out. -/
def outWord (w : Nat) : List Instr :=
  [.ldr .w .x14 .x4 (8 * arrSlot ((w + 2) % 4)), .rev32 .x14 .x14, .str .w .x14 .x3 (4 * w)]

theorem copyOutBody_eq : copyOutBody = outWord 0 ++ (outWord 1 ++ (outWord 2 ++ (outWord 3 ++
    ([.addImm .x .x3 .x3 16, .addImm .x .x4 .x4 4, .subImm .x .x15 .x15 1] : List Instr)))) := rfl

theorem copyOutWord_ok {w j : Nat} (hw : w < 4) (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .x4 = s.gpr .x5 + BitVec.ofNat 64 (4 * j))
    (hwr : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (4 * w)) 4) :
    ∃ s', runBlock isa (outWord w) s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .x3 + BitVec.ofNat 64 (4 * w))
        (rev32 (lv s (arrSlot ((w + 2) % 4)) j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ≠ .x14 → s'.gpr r = s.gpr r) := by
  obtain hw' : (w + 2) % 4 < 4 := Nat.mod_lt _ (by decide)
  obtain hL : arrSlot ((w + 2) % 4) ∈ arrays := mem_arrA_of hw'
  obtain hla : s.gpr .x4 + BitVec.ofNat 64 (8 * arrSlot ((w + 2) % 4)) = laneA s (arrSlot ((w + 2) % 4)) j := by
    rw [hrb, arr_off _ _]; rfl
  unfold outWord
  let s1 := s.write .w .x14 (lv s (arrSlot ((w + 2) % 4)) j)
  let s2 := s1.write .w .x14 (rev32 (s1.read .w .x14))
  obtain e1 : exec (.ldr .w .x14 .x4 (8 * arrSlot ((w + 2) % 4))) s = some s1 := by
    rw [exec_ldr_w (arr_ok hw') (by rw [hla]; exact lane_rw h hL hj), hla]; rfl
  have e2 : exec (.rev32 .x14 .x14) s1 = some s2 := rfl
  obtain h3 : s2.gpr .x3 = s.gpr .x3 := by simp [s2, s1, gpr_write]
  obtain e3 := exec_str_w (s := s2) (t := .x14) (n := .x3) (off := 4 * w) (by omega_arith)
    (by rw [h3]; simp only [s2, s1, wr_write]; exact hwr)
  rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3, runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r hr => ?_⟩
  · show s2.mem.writeW _ _ = _
    rw [h3]
    simp [s2, s1, gpr_write, mem_write, State.read, setWidth_setWidth_32]
  · simp [s2, s1, gpr_write, hr]

/-- The four words `y` of a block, byte-swapped, from `q`. -/
def outWrites (m : Mem) (q : Addr) (y : Nat → BitVec 32) : Mem :=
  (((m.writeW (q + BitVec.ofNat 64 0) (rev32 (y 0))).writeW (q + BitVec.ofNat 64 4) (rev32 (y 1))).writeW
    (q + BitVec.ofNat 64 8) (rev32 (y 2))).writeW (q + BitVec.ofNat 64 12) (rev32 (y 3))

theorem copyOutBody_ok {j : Nat} (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .x4 = s.gpr .x5 + BitVec.ofNat 64 (4 * j))
    (hwr : ∀ w < 4, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (4 * w)) 4)
    (hsep : Region.Disjoint ⟨s.gpr .x3, 16⟩ (arraysR s)) :
    ∃ s', runBlock isa copyOutBody s = some s' ∧
      s'.mem = outWrites s.mem (s.gpr .x3) (fun w => lv s (arrSlot ((w + 2) % 4)) j) ∧
      s'.gpr .x3 = s.gpr .x3 + 16 ∧ s'.gpr .x4 = s.gpr .x4 + 4 ∧
      s'.gpr .x15 = s.gpr .x15 - 1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x14 → r ≠ .x4 → r ≠ .x15 → r ≠ .x3 → s'.gpr r = s.gpr r) := by
  -- The lanes keep their values while the block is written.
  obtain hkeep : ∀ (t : State), t.gpr .x5 = s.gpr .x5 → Frame [⟨s.gpr .x3, 16⟩] s.mem t.mem → ∀ w < 4,
      lv t (arrSlot ((w + 2) % 4)) j = lv s (arrSlot ((w + 2) % 4)) j := by
    intro t ht hf w hw
    simp only [lv, laneA, ht]
    refine hf.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'
    exact fun x h1 h2 => hsep x h2 (lane_inArrays (mem_arrA_of (Nat.mod_lt _ (by decide))) hj s
      |>.byte h1)
  obtain ⟨s1, e1, m1, rd1, wr1, sp1, g1⟩ := copyOutWord_ok (w := 0) (by decide) hj s h hrb (hwr 0 (by decide))
  obtain r9_1 : s1.gpr .x5 = s.gpr .x5 := g1 _ (by decide)
  obtain h1 : Room s1 := room_congr h r9_1 wr1
  obtain hin : ∀ w < 4, (⟨s.gpr .x3, 16⟩ : Region).Contains (s.gpr .x3 + BitVec.ofNat 64 (4 * w)) (32 / 8) :=
    fun w hw => Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain f1 : Frame [⟨s.gpr .x3, 16⟩] s.mem s1.mem := by
    rw [m1]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (hin 0 (by decide))
  obtain ⟨s2, e2, m2, rd2, wr2, sp2, g2⟩ := copyOutWord_ok (w := 1) (by decide) hj s1 h1
    (by rw [g1 _ (by decide), r9_1, hrb]) (by rw [wr1, g1 _ (by decide)]; exact hwr 1 (by decide))
  obtain r9_2 : s2.gpr .x5 = s.gpr .x5 := by rw [g2 _ (by decide), r9_1]
  obtain h2 : Room s2 := room_congr h r9_2 (by rw [wr2, wr1])
  obtain r10_1 : s1.gpr .x3 = s.gpr .x3 := g1 _ (by decide)
  obtain f2 : Frame [⟨s.gpr .x3, 16⟩] s.mem s2.mem := by
    rw [m2, r10_1]; exact f1.writeW List.mem_cons_self _ (hin 1 (by decide))
  obtain ⟨s3, e3, m3, rd3, wr3, sp3, g3⟩ := copyOutWord_ok (w := 2) (by decide) hj s2 h2
    (by rw [g2 _ (by decide), g1 _ (by decide), r9_2, hrb])
    (by rw [wr2, wr1, g2 _ (by decide), r10_1]; exact hwr 2 (by decide))
  obtain r9_3 : s3.gpr .x5 = s.gpr .x5 := by rw [g3 _ (by decide), r9_2]
  obtain h3 : Room s3 := room_congr h r9_3 (by rw [wr3, wr2, wr1])
  obtain r10_2 : s2.gpr .x3 = s.gpr .x3 := by rw [g2 _ (by decide), r10_1]
  obtain f3 : Frame [⟨s.gpr .x3, 16⟩] s.mem s3.mem := by
    rw [m3, r10_2]; exact f2.writeW List.mem_cons_self _ (hin 2 (by decide))
  obtain ⟨s4, e4, m4, rd4, wr4, sp4, g4⟩ := copyOutWord_ok (w := 3) (by decide) hj s3 h3
    (by rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), r9_3, hrb])
    (by rw [wr3, wr2, wr1, g3 _ (by decide), r10_2]; exact hwr 3 (by decide))
  obtain r10_3 : s3.gpr .x3 = s.gpr .x3 := by rw [g3 _ (by decide), r10_2]
  let s5 := s4.write .x .x3 (s4.read .x .x3 + BitVec.ofNat _ 16)
  let s6 := s5.write .x .x4 (s5.read .x .x4 + BitVec.ofNat _ 4)
  let s7 := s6.write .x .x15 (s6.read .x .x15 - BitVec.ofNat _ 1)
  obtain hrun : runBlock isa copyOutBody s = some s7 := by
    rw [copyOutBody_eq, runBlock_append, e1, Option.bind_some, runBlock_append, e2, Option.bind_some,
      runBlock_append, e3, Option.bind_some, runBlock_append, e4, Option.bind_some, runBlock_cons,
      exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some,
      runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil]
  obtain rbx_4 : s4.gpr .x4 = s.gpr .x4 := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  obtain rcx_4 : s4.gpr .x15 = s.gpr .x15 := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  obtain r10_4 : s4.gpr .x3 = s.gpr .x3 := by rw [g4 _ (by decide), r10_3]
  refine ⟨s7, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_⟩
  · simp only [s7, s6, s5, mem_write]
    rw [m4, r10_3, hkeep s3 r9_3 f3 3 (by decide), m3, r10_2,
      hkeep s2 r9_2 f2 2 (by decide), m2, r10_1, hkeep s1 r9_1 f1 1 (by decide), m1, outWrites]
  · simp [s7, s6, s5, gpr_write, read_x, r10_4]
  · simp [s7, s6, s5, gpr_write, read_x, rbx_4]
  · simp [s7, s6, s5, gpr_write, read_x, rcx_4]
  · simp only [s7, s6, s5, rd_write, rd4, rd3, rd2, rd1]
  · simp only [s7, s6, s5, wr_write, wr4, wr3, wr2, wr1]
  · simp only [s7, s6, s5, sp_write, sp4, sp3, sp2, sp1]
  · simp only [s7, s6, s5, gpr_write, h3, h2, h4, ↓reduceIte]
    rw [g4 _ h1, g3 _ h1, g2 _ h1, g1 _ h1]

theorem outWrites_off (m : Mem) (q : Addr) (y : Nat → BitVec 32) {x : Addr}
    (h : ¬ (x - q).toNat < 16) : outWrites m q y x = m x := by
  obtain hx : x = q + BitVec.ofNat 64 (x - q).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  obtain hlt := (x - q).isLt
  obtain hoff : ∀ c : Nat, c ≤ 12 → ¬ (x - (q + BitVec.ofNat 64 c)).toNat < 32 / 8 := by
    intro c hc
    have := Offset.sep q (d := (x - q).toNat) (n := 1) (e := c) (k := 4) (by omega_arith) (by omega_arith) (by omega_arith)
    refine this x ?_
    rw [← hx, BitVec.sub_self]; decide
  simp only [outWrites, Mem.writeW]
  rw [Mem.write_apply (hoff 12 (by decide)), Mem.write_apply (hoff 8 (by decide)),
    Mem.write_apply (hoff 4 (by decide)), Mem.write_apply (hoff 0 (by decide))]

theorem outWrites_frame {m₀ m : Mem} {p : Addr} {n j : Nat} (h : Frame [⟨p, n⟩] m₀ m) (hj : 16 * j + 16 ≤ n)
    (hn : n < 2 ^ 64) (y : Nat → BitVec 32) :
    Frame [⟨p, n⟩] m₀ (outWrites m (p + BitVec.ofNat 64 (16 * j)) y) := by
  obtain hc : ∀ c, c ≤ 12 → (⟨p, n⟩ : Region).Contains (p + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 c) (32 / 8) := by
    intro c hc; rw [Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  exact (((h.writeW List.mem_cons_self _ (hc 0 (by decide))).writeW List.mem_cons_self _ (hc 4 (by decide))).writeW
    List.mem_cons_self _ (hc 8 (by decide))).writeW List.mem_cons_self _ (hc 12 (by decide))

/-- Byte `i` of block `b` copied out: byte `3 - i % 4` of word `(i / 4 + 2) % 4` of lane `b`. -/
def outByte (s : State) (b i : Nat) : Byte := (lv s (arrSlot ((i / 4 + 2) % 4)) b >>> (8 * (3 - i % 4))).setWidth 8

/-- What the copy out of the arrays needs. -/
structure CopyOutPre (s : State) (p : Addr) (m : Nat) : Prop where
  room : Room s
  le : 1 ≤ m ∧ m ≤ 16
  write : ∀ b < m, ∀ w < 4, InRegions s.wr (p + BitVec.ofNat 64 (16 * b + 4 * w)) 4
  sep : Region.Disjoint ⟨p, 16 * m⟩ (arraysR s)

/-- After `j` blocks of the copy out. -/
structure CopyOutInv (s₀ : State) (p : Addr) (m j : Nat) (s : State) : Prop where
  le : j ≤ m
  x3 : s.gpr .x3 = p + BitVec.ofNat 64 (16 * j)
  x4 : s.gpr .x4 = s₀.gpr .x5 + BitVec.ofNat 64 (4 * j)
  x15 : s.gpr .x15 = BitVec.ofNat 64 (m - j)
  done : ∀ b < j, ∀ i < 16, s.mem (p + BitVec.ofNat 64 (16 * b + i)) = outByte s₀ b i
  frame : Frame [⟨p, 16 * m⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .x14 → r ≠ .x4 → r ≠ .x15 → r ≠ .x3 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyOut_loop {s₀ : State} {p : Addr} {m : Nat} (hpre : CopyOutPre s₀ p m) :
    ∀ k s, CopyOutInv s₀ p m (m - k) s → 1 ≤ k → k ≤ m →
      WP isa (.loop (.block copyOutBody) (.nonzero .x .x15)) s (fun s' => CopyOutInv s₀ p m m s') := by
  intro k s hs hk1 hkm
  refine WP.loop (M := isa) (fun k t => CopyOutInv s₀ p m (m - k) t ∧ 1 ≤ k ∧ k ≤ m) ?_ k s ⟨hs, hk1, hkm⟩
  intro k t ⟨inv, hk1, hkm⟩
  have hm16 := hpre.le.2
  let j := m - k
  obtain hj : j < 16 := by omega_arith
  obtain hr9 : t.gpr .x5 = s₀.gpr .x5 := inv.regs _ (by decide) (by decide) (by decide) (by decide)
  obtain hroom : Room t := room_congr hpre.room hr9 inv.wr
  obtain hrb : t.gpr .x4 = t.gpr .x5 + BitVec.ofNat 64 (4 * j) := by rw [inv.x4, hr9]
  obtain hwr : ∀ w < 4, InRegions t.wr (t.gpr .x3 + BitVec.ofNat 64 (4 * w)) 4 := by
    intro w hw; rw [inv.x3, Offset.add_add, inv.wr]; exact hpre.write j (by omega_arith) w hw
  obtain harr : arraysR t = arraysR s₀ := by simp [arraysR, hr9]
  obtain hsep : Region.Disjoint ⟨t.gpr .x3, 16⟩ (arraysR t) := by
    rw [inv.x3, harr]; exact hpre.sep.sub_left (Offset.sub_base p (by omega_arith))
  obtain ⟨t', ht', hmem, hr10, hrbx, hrcx, hrd, hwr', hsp, hregs⟩ := copyOutBody_ok hj t hroom hrb hwr hsep
  refine WP.of_runBlock ⟨t', ht', ?_⟩
  -- The lanes, as they were.
  obtain hlanes : ∀ w < 4, lv t (arrSlot ((w + 2) % 4)) j = lv s₀ (arrSlot ((w + 2) % 4)) j := by
    intro w hw
    simp only [lv, laneA, hr9]
    refine inv.frame.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'
    exact fun x h1 h2 => hpre.sep x h2 (lane_inArrays (mem_arrA_of (Nat.mod_lt _ (by decide))) hj s₀ |>.byte h1)
  obtain inv' : CopyOutInv s₀ p m (j + 1) t' := by
    refine ⟨by omega_arith, ?_, ?_, ?_, fun b hb i hi => ?_, ?_, fun r h1 h2 h3 h4 => ?_, by rw [hsp, inv.sp],
      by rw [hrd, inv.rd], by rw [hwr', inv.wr]⟩
    · rw [hr10, inv.x3, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add]; congr 2
    · rw [hrbx, inv.x4, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    · rw [hrcx, inv.x15, show m - j = k by omega_arith, cnt_sub1 hk1 (by omega_arith)]; congr 1; omega_arith
    · rw [hmem]
      by_cases hbj : b = j
      · subst hbj
        rw [show p + BitVec.ofNat 64 (16 * (m - k) + i) = t.gpr .x3 + BitVec.ofNat 64 i by
          rw [inv.x3, Offset.add_add]]
        unfold outWrites
        rw [block_writes _ _ (fun w => lv t (arrSlot ((w + 2) % 4)) j) hi, outByte, hlanes _ (by omega_arith)]
      · rw [outWrites_off _ _ _ ?_]
        · exact inv.done b (by omega_arith) i hi
        · rw [inv.x3, Offset.sub_toNat' p (by omega_arith) (by omega_arith)]
          split <;> omega_arith
    · rw [hmem, inv.x3]
      exact outWrites_frame inv.frame (by omega_arith) (by omega_arith) _
    · rw [hregs r h1 h2 h3 h4]; exact inv.regs r h1 h2 h3 h4
  by_cases hk : k = 1
  · subst hk
    left
    obtain hjm : j + 1 = m := by omega_arith
    refine ⟨?_, hjm ▸ inv'⟩
    show some (t'.read .x .x15 != 0) = some false
    rw [read_x, hrcx, inv.x15, show m - (m - 1) = 1 by omega_arith]; rfl
  · right
    refine ⟨?_, k - 1, by omega_arith, ⟨by simpa [show j + 1 = m - (k - 1) by omega_arith] using inv', by omega_arith, by omega_arith⟩⟩
    show some (t'.read .x .x15 != 0) = some true
    rw [read_x, hrcx, inv.x15, show m - (m - k) = k by omega_arith, cnt_ne_zero (by omega_arith) (by omega_arith)]

end VG.Proof.Seed.AArch64

end

end


/-!
# A batch on AArch64

`batch_ok`: a batch encrypts or decrypts the first `min n 16` blocks at
`x1` in place (`n = x2`), with the keys at `x0` (`keysAt`), and moves `x1`
and `x2` past them.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Impl.Aes.AArch64
  VG.Proof.Seed

/-! ## The batch size -/

theorem exec_movR (s : State) (d n : Reg) : exec (movR d n) s = some (s.write .x d (s.gpr n)) := by
  rw [movR, exec_addImm_x (by decide), read_x]
  exact congrArg (fun v => some (s.write .x d v)) (BitVec.add_zero _)

theorem exec_sub (s : State) (sz : Size) (d n m : Reg) :
    exec (.sub sz d n m) s = some (s.write sz d (s.read sz n - s.read sz m)) := rfl

theorem batchSize_ok (s : State) :
    WP isa batchSize s (fun s' => s'.gpr .x15 = BitVec.ofNat 64 (min (s.gpr .x2).toNat 16) ∧
      (∀ r, r ≠ .x15 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp) := by
  let s₁ := s.write .x .x15 (s.gpr .x2 >>> 4)
  obtain e₁ : runBlock isa [lsrI .x15 .x2 4] s = some s₁ := by
    rw [runBlock_cons, lsrI, exec_lsr_x (by decide), runStep_some, runBlock_nil, read_x]
  obtain g₁ : ∀ r, r ≠ .x15 → s₁.gpr r = s.gpr r := fun r hr => gpr_write_of_ne _ _ _ hr
  obtain hc : isa.eval (.nonzero .x .x15) s₁ = some (decide (16 ≤ (s.gpr .x2).toNat)) := by
    show some (s₁.read .x .x15 != 0) = _
    rw [read_x, gpr_write_self, BitVec.setWidth_eq]
    congr 1
    by_cases h : 16 ≤ (s.gpr .x2).toNat
    · simp only [h, decide_true, bne_iff_ne, ne_eq]
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ushiftRight] at this
      simp at this; omega_using [h, this]
    · simp only [h, decide_false, bne_eq_false_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight]; simp; omega
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.ite _ hc (fun hb => ?_) (fun hb => ?_)
  · have hge := of_decide_eq_true hb
    let s₂ := s₁.write .x .x15 ((16 : BitVec 16).setWidth 64 <<< (16 * 0))
    refine WP.of_runBlock ⟨s₂, rfl, ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [gpr_write_self, Nat.min_eq_right (by omega_using [hge])]; rfl
    · rw [gpr_write_of_ne _ _ _ hr, g₁ r hr]
  · have hlt := of_decide_eq_false hb
    refine WP.of_runBlock ⟨s₁.write .x .x15 (s₁.gpr .x2), by rw [runBlock_cons, exec_movR, runStep_some,
      runBlock_nil], ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [gpr_write_self, BitVec.setWidth_eq, g₁ _ (by decide), Nat.min_eq_left (by omega_using [hlt]),
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [gpr_write_of_ne _ _ _ hr, g₁ r hr]

/-! ## Small steps -/

theorem copyStart_ok (s : State) :
    ∃ t, runBlock isa copyStart s = some t ∧ t.gpr .x3 = s.gpr .x1 ∧ t.gpr .x4 = s.gpr .x5 ∧
      (∀ r, r ≠ .x3 → r ≠ .x4 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp :=
  ⟨(s.write .x .x3 (s.gpr .x1)).write .x .x4 ((s.write .x .x3 (s.gpr .x1)).gpr .x5),
    by rw [copyStart, runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_movR, runStep_some,
      runBlock_nil]; rfl,
    by simp [gpr_write], by simp [gpr_write], fun r h1 h2 => by simp [gpr_write, h1, h2],
    rfl, rfl, rfl, rfl⟩

theorem ofNat_zero_add (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-! ## Blocks and lanes -/

theorem quad_of_lanes {t : State} {m : Mem} {p : Addr} {b : Nat}
    (h : ∀ w < 4, lv t (arrSlot w) b = bw m p b w) :
    quad t b = decodeQ (Spec.Seed.blockAt m (p + BitVec.ofNat 64 (16 * b))) := by
  rw [decodeQ_blockAt]
  simp only [quad, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), bw,
    Offset.add_ofNat_add_ofNat, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul]
  rfl

theorem encodeSwapped_get (t : State) (b : Nat) {i : Nat} (hi : i < 16) :
    (encodeSwapped (quad t b))[i] = outByte t b i := by
  obtain hk : ∀ w < 4, (#v[(quad t b).2.2.1, (quad t b).2.2.2, (quad t b).1, (quad t b).2.1] :
      Vector Spec.Seed.Word 4).getD w 0 = lv t (arrSlot ((w + 2) % 4)) b := by
    intro w hw
    rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_using [hw]) with rfl | rfl | rfl | rfl <;> rfl
  simp only [encodeSwapped, Vector.getElem_ofFn, outByte]
  rw [hk _ (by omega_using [hi])]

theorem blockAt_of_bytes {m : Mem} {q : Addr} {v : Spec.Seed.Block}
    (h : ∀ i (hi : i < 16), m (q + BitVec.ofNat 64 i) = v[i]) : Spec.Seed.blockAt m q = v := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Seed.blockAt, Vector.getElem_ofFn]
  exact h i hi

/-! ## The batch -/

/-- What a batch needs: the scratch buffer; the batch's blocks writable, and
they and the keys apart from the scratch buffer and each other. -/
structure BatchPre (d : Spec.Seed.Direction) (s : State) : Prop where
  room : Room s
  pos : 1 ≤ (s.gpr .x2).toNat
  data : ∀ b < min (s.gpr .x2).toNat 16, ∀ w < 4,
    InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * b + 4 * w)) 4
  dataSep : Region.Disjoint ⟨s.gpr .x1, 16 * min (s.gpr .x2).toNat 16⟩ (scratchR s)
  keys : KeysOk d s (s.gpr .x0)
  keyData : ∀ j < 16, Region.Disjoint ⟨kp d (s.gpr .x0) j, 8⟩ ⟨s.gpr .x1, 16 * min (s.gpr .x2).toNat 16⟩

structure BatchPost (d : Spec.Seed.Direction) (s s' : State) : Prop where
  done : ∀ b < min (s.gpr .x2).toNat 16,
    Spec.Seed.blockAt s'.mem (s.gpr .x1 + BitVec.ofNat 64 (16 * b)) =
      Spec.Seed.crypt (keysAt d s.mem (s.gpr .x0))
        (Spec.Seed.blockAt s.mem (s.gpr .x1 + BitVec.ofNat 64 (16 * b)))
  rsi : s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (16 * min (s.gpr .x2).toNat 16)
  rdx : s'.gpr .x2 = s.gpr .x2 - BitVec.ofNat 64 (min (s.gpr .x2).toNat 16)
  regs : ∀ r ∈ [Reg.x0, .x5], s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [workR s, ⟨s.gpr .x1, 16 * min (s.gpr .x2).toNat 16⟩] s.mem s'.mem

theorem arraysR_sub_scratch (s : State) : Region.Sub (arraysR s) (scratchR s) := by
  show Region.Sub ⟨s.gpr .x5 + BitVec.ofNat 64 (8 * 48), 8 * 64⟩ ⟨s.gpr .x5, 8 * scratchSlots⟩
  exact Offset.sub_base _ (by unfold scratchSlots; omega_using [])

theorem arraysR_sub_work (s : State) : Region.Sub (arraysR s) (workR s) := by
  show Region.Sub ⟨s.gpr .x5 + BitVec.ofNat 64 (8 * 48), 8 * 64⟩ ⟨s.gpr .x5, 8 * 112⟩
  exact Offset.sub_base _ (by omega_using [])

theorem batch_ok (d : Spec.Seed.Direction) {s : State} (h : BatchPre d s) :
    WP isa (batch d) s (BatchPost d s) := by
  let n := (s.gpr .x2).toNat
  let k := min n 16
  let p := s.gpr .x1
  obtain hk1 : 1 ≤ k := by have := h.pos; omega
  obtain hk16 : k ≤ 16 := by omega_using []
  have hpos := h.pos
  -- the copy in
  apply WP.seq
  apply WP.seq
  refine WP.mono (batchSize_ok s) fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  apply WP.seq
  obtain ⟨s₂, e₂, x3₂, x4₂, g₂, m₂, rd₂, wr₂, sp₂⟩ := copyStart_ok s₁
  refine WP.of_runBlock ⟨s₂, e₂, ?_⟩
  obtain G₂ : ∀ r, r ≠ .x15 → r ≠ .x3 → r ≠ .x4 → s₂.gpr r = s.gpr r := fun r a b c =>
    (g₂ r b c).trans (g₁ r a)
  obtain x5₂ : s₂.gpr .x5 = s.gpr .x5 := G₂ _ (by decide) (by decide) (by decide)
  obtain scr₂ : scratchR s₂ = scratchR s := by simp only [scratchR, x5₂]
  obtain arr₂ : arraysR s₂ = arraysR s := by simp only [arraysR, x5₂]
  obtain room₂ : Room s₂ := room_congr h.room x5₂ (by rw [wr₂, wr₁])
  obtain pre₂ : CopyPre s₂ p k := by
    refine ⟨room₂, ⟨hk1, hk16⟩, fun b hb w hw => ?_, ?_⟩
    · obtain ⟨r, hr, hc⟩ := h.data b hb w hw
      exact ⟨r, by rw [rd₂, wr₂, rd₁, wr₁]; exact List.mem_append_right _ hr, hc⟩
    · rw [arr₂]; exact h.dataSep.sub_right (arraysR_sub_scratch s)
  obtain inv₂ : CopyInInv s₂ p k (k - k) s₂ := by
    refine ⟨by omega_using [], ?_, ?_, ?_, fun w _ b hb => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl,
      rfl⟩
    · rw [x3₂, Nat.sub_self, Nat.mul_zero, ofNat_zero_add, g₁ _ (by decide)]
    · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add, x4₂, g₂ _ (by decide) (by decide)]
    · rw [Nat.sub_self, Nat.sub_zero, g₂ _ (by decide) (by decide), c₁]
  refine WP.mono (copyIn_loop pre₂ k s₂ inv₂ hk1 (Nat.le_refl _)) fun s₃ i₃ => ?_
  obtain x5₃ : s₃.gpr .x5 = s.gpr .x5 := (i₃.regs _ (by decide) (by decide) (by decide) (by decide)).trans x5₂
  obtain G₃ : ∀ r ∈ [Reg.x0, .x1, .x2], s₃.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .x14 ∧ r ≠ .x4 ∧ r ≠ .x15 ∧ r ≠ .x3 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    rw [i₃.regs _ this.1 this.2.1 this.2.2.1 this.2.2.2]
    exact G₂ _ this.2.2.1 this.2.2.2 this.2.1
  obtain rd₃ : s₃.rd = s.rd := by rw [i₃.rd, rd₂, rd₁]
  obtain wr₃ : s₃.wr = s.wr := by rw [i₃.wr, wr₂, wr₁]
  obtain sp₃ : s₃.sp = s.sp := by rw [i₃.sp, sp₂, sp₁]
  obtain room₃ : Room s₃ := room_congr h.room x5₃ wr₃
  obtain f₃ : Frame [arraysR s] s.mem s₃.mem := by
    have := i₃.frame; rw [arr₂, m₂, m₁] at this; exact this
  obtain scr₃ : scratchR s₃ = scratchR s := by simp only [scratchR, x5₃]
  obtain keys₃ : KeysOk d s₃ (s₃.gpr .x0) := by
    rw [G₃ .x0 (by simp)]
    intro j hj
    obtain ⟨a, b, c⟩ := h.keys j hj
    exact ⟨by rw [rd₃, wr₃]; exact a, by rw [rd₃, wr₃]; exact b, by rw [scr₃]; exact c⟩
  -- the keys are as on entry
  obtain hkeys : ∀ j < 16, keysAt d s₃.mem (s₃.gpr .x0) j = keysAt d s.mem (s.gpr .x0) j := by
    intro j hj
    rw [G₃ .x0 (by simp)]
    obtain ⟨-, -, hdis⟩ := h.keys j hj
    obtain hd : ∀ r ∈ [arraysR s], Region.Disjoint ⟨kp d (s.gpr .x0) j, 8⟩ r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact hdis.sub_right (arraysR_sub_scratch s)
    simp only [keysAt]
    refine Eq.mpr (Prod.mk.injEq _ _ _ _) ⟨?_, ?_⟩
    · exact f₃.readW (contains_prefix (by decide)) hd (by decide)
    · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
      exact f₃.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega_using []) (by omega_using [])) hd (by decide)
  -- the blocks, in the lanes
  obtain hq₃ : ∀ b < k, quad s₃ b = decodeQ (Spec.Seed.blockAt s.mem (p + BitVec.ofNat 64 (16 * b))) := by
    intro b hb
    refine quad_of_lanes fun w hw => ?_
    rw [i₃.lanes w hw b hb, m₂, m₁]
  -- the rounds
  apply WP.seq
  refine WP.mono (rounds_ok d room₃ keys₃) fun s₄ ⟨q₄, room₄, rd₄, wr₄, sp₄, g₄, f₄⟩ => ?_
  obtain G₄ : ∀ r ∈ [Reg.x0, .x1, .x2, .x5], s₄.gpr r = s.gpr r := by
    intro r hr
    rw [g₄ r hr]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact G₃ _ (by simp)
    · exact G₃ _ (by simp)
    · exact G₃ _ (by simp)
    · exact x5₃
  obtain hq₄ : ∀ b < k, quad s₄ b = roundsN (keysAt d s.mem (s.gpr .x0)) 16
      (decodeQ (Spec.Seed.blockAt s.mem (p + BitVec.ofNat 64 (16 * b)))) := by
    intro b hb
    rw [q₄ b (by omega_using [hb]), hq₃ b hb]
    exact roundsN_congr 16 _ hkeys
  -- the copy out
  apply WP.seq
  refine WP.mono (batchSize_ok s₄) fun s₅ ⟨c₅, g₅, m₅, rd₅, wr₅, sp₅⟩ => ?_
  apply WP.seq
  obtain ⟨s₆, e₆, x3₆, x4₆, g₆, m₆, rd₆, wr₆, sp₆⟩ := copyStart_ok s₅
  refine WP.of_runBlock ⟨s₆, e₆, ?_⟩
  obtain G₆ : ∀ r, r ≠ .x15 → r ≠ .x3 → r ≠ .x4 → s₆.gpr r = s₄.gpr r := fun r a b c =>
    (g₆ r b c).trans (g₅ r a)
  obtain x5₆ : s₆.gpr .x5 = s.gpr .x5 := (G₆ _ (by decide) (by decide) (by decide)).trans (G₄ _ (by simp))
  obtain x2₄ : s₄.gpr .x2 = s.gpr .x2 := G₄ _ (by simp)
  obtain x1₄ : s₄.gpr .x1 = p := G₄ _ (by simp)
  obtain rd₆ : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  obtain wr₆ : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  obtain sp₆ : s₆.sp = s.sp := by rw [sp₆, sp₅, sp₄, sp₃]
  obtain arr₆ : arraysR s₆ = arraysR s := by simp only [arraysR, x5₆]
  obtain pre₆ : CopyOutPre s₆ p k := by
    refine ⟨room_congr h.room x5₆ wr₆, ⟨hk1, hk16⟩, fun b hb w hw => ?_, ?_⟩
    · rw [wr₆]; exact h.data b hb w hw
    · rw [arr₆]; exact h.dataSep.sub_right (arraysR_sub_scratch s)
  obtain inv₆ : CopyOutInv s₆ p k (k - k) s₆ := by
    refine ⟨by omega_using [], ?_, ?_, ?_, fun b hb => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl,
      rfl⟩
    · rw [x3₆, Nat.sub_self, Nat.mul_zero, ofNat_zero_add, g₅ _ (by decide), x1₄]
    · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add, x4₆, g₆ _ (by decide) (by decide)]
    · rw [Nat.sub_self, Nat.sub_zero, g₆ _ (by decide) (by decide), c₅, x2₄]
  obtain quad₆ : ∀ b, quad s₆ b = quad s₄ b := fun b => by
    simp only [quad, lv, laneA, m₆, m₅, x5₆, G₄ .x5 (by simp)]
  apply WP.seq
  refine WP.mono (copyOut_loop pre₆ k s₆ inv₆ hk1 (Nat.le_refl _)) fun s₇ i₇ => ?_
  apply WP.seq
  refine WP.mono (batchSize_ok s₇) fun s₈ ⟨c₈, g₈, m₈, rd₈, wr₈, sp₈⟩ => ?_
  obtain G₇ : ∀ r, r ≠ .x14 → r ≠ .x4 → r ≠ .x15 → r ≠ .x3 → s₇.gpr r = s₄.gpr r :=
    fun r a b c e => (i₇.regs r a b c e).trans (G₆ r c e b)
  obtain x2₇ : s₇.gpr .x2 = s.gpr .x2 := (G₇ _ (by decide) (by decide) (by decide) (by decide)).trans x2₄
  obtain c₈' : s₈.gpr .x15 = BitVec.ofNat 64 k := by rw [c₈, x2₇]
  obtain x3₈ : s₈.gpr .x3 = p + BitVec.ofNat 64 (16 * k) := by rw [g₈ _ (by decide), i₇.x3]
  let s₉ := s₈.write .x .x1 (s₈.gpr .x3)
  let s' := s₉.write .x .x2 (s₉.read .x .x2 - s₉.read .x .x15)
  refine WP.of_runBlock ⟨s', by rw [runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_sub,
    runStep_some, runBlock_nil], ?_⟩
  obtain g' : ∀ r, r ≠ .x1 → r ≠ .x2 → s'.gpr r = s₈.gpr r := fun r a b => by
    simp [s', s₉, gpr_write, a, b]
  obtain x2₉ : s₉.gpr .x2 = s.gpr .x2 := by rw [gpr_write_of_ne _ _ _ (by decide), g₈ _ (by decide), x2₇]
  obtain x15₉ : s₉.gpr .x15 = BitVec.ofNat 64 k := by rw [gpr_write_of_ne _ _ _ (by decide), c₈']
  obtain mem' : s'.mem = s₇.mem := by simp only [s', s₉, mem_write, m₈]
  obtain G' : ∀ r ∈ [Reg.x0, .x5], s'.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .x2 ∧ r ≠ .x1 ∧ r ≠ .x15 ∧ r ≠ .x14 ∧ r ≠ .x4 ∧ r ≠ .x3 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    rw [g' _ this.2.1 this.1, g₈ _ this.2.2.1, G₇ _ this.2.2.2.1 this.2.2.2.2.1 this.2.2.1 this.2.2.2.2.2]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    exact G₄ _ (by rcases hr with rfl | rfl <;> simp)
  obtain x5' : s'.gpr .x5 = s.gpr .x5 := G' _ (by simp)
  -- the memory
  obtain f₇ : Frame [⟨p, 16 * k⟩] s₄.mem s₇.mem := by
    have := i₇.frame; rw [m₆, m₅] at this; exact this
  obtain frame : Frame [workR s, ⟨p, 16 * k⟩] s.mem s'.mem := by
    rw [mem']
    obtain a : Frame [workR s, ⟨p, 16 * k⟩] s.mem s₃.mem :=
      (f₃.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨workR s, List.mem_cons_self, arraysR_sub_work s⟩)
    obtain b : Frame [workR s, ⟨p, 16 * k⟩] s₃.mem s₄.mem :=
      f₄.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [workR, x5₃]; exact List.mem_cons_self
    obtain c : Frame [workR s, ⟨p, 16 * k⟩] s₄.mem s₇.mem :=
      f₇.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact List.mem_cons_of_mem _ List.mem_cons_self
    exact (a.trans b).trans c
  refine ⟨fun b hb => ?_, ?_, ?_, G', ?_, by simp only [s', s₉, rd_write, rd₈, i₇.rd, rd₆],
    by simp only [s', s₉, wr_write, wr₈, i₇.wr, wr₆], frame⟩
  · rw [crypt_eq, ← hq₄ b hb, ← quad₆ b, mem']
    refine blockAt_of_bytes fun i hi => ?_
    rw [Offset.add_ofNat_add_ofNat, i₇.done b hb i hi, encodeSwapped_get _ _ hi]
  · simp [s', s₉, gpr_write, x3₈]; rfl
  · simp only [s', gpr_write_self, BitVec.setWidth_eq, read_x, x2₉, x15₉]; rfl
  · simp only [s', s₉, sp_write, sp₈, i₇.sp, sp₆]

end VG.Proof.Seed.AArch64

end

end

/-!
# The function on AArch64

After moving the scratch buffer to `x5` and saving the callee-saved
registers in it, the function runs batches of up to 16 blocks until none are
left (`loop_ok`), then restores the registers (`ecb_ok`).
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Impl.Aes.AArch64
  VG.Proof.Seed

theorem toNat_ofNat_le {m n : Nat} (hm : m ≤ n) (hn : 16 * n ≤ 2 ^ 64) : (BitVec.ofNat 64 m).toNat = m := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : Spec.Seed.blockAt m' p = Spec.Seed.blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Seed.blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 16⟩) hd (by show 16 ≤ 2 ^ 64; decide) hi

/-- The keys are as in `m` wherever the frame's regions leave them. -/
theorem keysAt_frame {d : Spec.Seed.Direction} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    {j : Nat} (hd : ∀ r ∈ rs, (⟨kp d p j, 8⟩ : Region).Disjoint r) : keysAt d m' p j = keysAt d m p j := by
  simp only [keysAt]
  refine Eq.mpr (Prod.mk.injEq _ _ _ _) ⟨?_, ?_⟩
  · exact hf.readW (contains_prefix (by decide)) hd (by decide)
  · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
    exact hf.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega_arith) (by omega_arith)) hd (by decide)

/-! ## The loop of batches -/

/-- What the loop may assume throughout, of the state it starts in. -/
structure BatchesEnv (d : Spec.Seed.Direction) (s₀ : State) (n : Nat) : Prop where
  room : Room s₀
  dataIn : (⟨s₀.gpr .x1, 16 * n⟩ : Region) ∈ s₀.wr
  dataSep : Region.Disjoint ⟨s₀.gpr .x1, 16 * n⟩ (scratchR s₀)
  fit : 16 * n ≤ 2 ^ 64
  keys : KeysOk d s₀ (s₀.gpr .x0)
  keyData : ∀ j < 16, Region.Disjoint ⟨kp d (s₀.gpr .x0) j, 8⟩ ⟨s₀.gpr .x1, 16 * n⟩

/-- `m` blocks left, the first `n - m` done. -/
structure BatchesInv (d : Spec.Seed.Direction) (s₀ : State) (n m : Nat) (s : State) : Prop where
  pos : 1 ≤ m
  le : m ≤ n
  x2 : s.gpr .x2 = BitVec.ofNat 64 m
  x1 : s.gpr .x1 = s₀.gpr .x1 + BitVec.ofNat 64 (16 * (n - m))
  regs : ∀ r ∈ [Reg.x0, .x5], s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n - m, Spec.Seed.blockAt s.mem (s₀.gpr .x1 + BitVec.ofNat 64 (16 * b)) =
    Spec.Seed.crypt (keysAt d s₀.mem (s₀.gpr .x0))
      (Spec.Seed.blockAt s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 (16 * b)))
  frame : Frame [workR s₀, ⟨s₀.gpr .x1, 16 * (n - m)⟩] s₀.mem s.mem

structure BatchesPost (d : Spec.Seed.Direction) (s₀ : State) (n : Nat) (s : State) : Prop where
  regs : ∀ r ∈ [Reg.x0, .x5], s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n, Spec.Seed.blockAt s.mem (s₀.gpr .x1 + BitVec.ofNat 64 (16 * b)) =
    Spec.Seed.crypt (keysAt d s₀.mem (s₀.gpr .x0))
      (Spec.Seed.blockAt s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 (16 * b)))
  frame : Frame [workR s₀, ⟨s₀.gpr .x1, 16 * n⟩] s₀.mem s.mem

theorem BatchesInv.batchPre {d : Spec.Seed.Direction} {s₀ : State} {n m : Nat} (E : BatchesEnv d s₀ n)
    {s : State} (h : BatchesInv d s₀ n m s) : BatchPre d s := by
  have hp := h.pos
  have hl := h.le
  have hfit := E.fit
  obtain hm : (s.gpr .x2).toNat = m := by rw [h.x2]; exact toNat_ofNat_le h.le E.fit
  obtain r9 : s.gpr .x5 = s₀.gpr .x5 := h.regs _ (by simp)
  obtain rdi : s.gpr .x0 = s₀.gpr .x0 := h.regs _ (by simp)
  obtain scr : scratchR s = scratchR s₀ := by simp only [scratchR, r9]
  let D := s₀.gpr .x1
  obtain hsub : Region.Sub ⟨s.gpr .x1, 16 * min (s.gpr .x2).toNat 16⟩ ⟨D, 16 * n⟩ := by
    rw [h.x1, hm]; exact Offset.sub_base _ (by omega_arith)
  refine ⟨room_congr E.room r9 h.wr, by omega_arith, fun b hb w hw => ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [h.wr, h.x1, Offset.add_ofNat_add_ofNat]
    rw [hm] at hb
    exact ⟨_, E.dataIn, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [scr]; exact E.dataSep.sub_left hsub
  · rw [rdi]
    intro j hj
    obtain ⟨a, b, c⟩ := E.keys j hj
    exact ⟨by rw [h.rd, h.wr]; exact a, by rw [h.rd, h.wr]; exact b, by rw [scr]; exact c⟩
  · rw [rdi]; exact (E.keyData j hj).sub_right hsub

theorem loop_ok (d : Spec.Seed.Direction) {s₀ : State} {n : Nat} (E : BatchesEnv d s₀ n) (m : Nat) (s : State)
    (hs : BatchesInv d s₀ n m s) : WP isa (.loop (batch d) (.nonzero .x .x2)) s (BatchesPost d s₀ n) := by
  refine WP.loop (M := isa) (BatchesInv d s₀ n) ?_ m s hs
  intro m s h
  have hp := h.pos
  have hl := h.le
  have hfit := E.fit
  apply WP.mono (batch_ok d (h.batchPre E))
  intro s' q
  obtain hm : (s.gpr .x2).toNat = m := by rw [h.x2]; exact toNat_ofNat_le h.le E.fit
  obtain ⟨qdone, qrsi, qrdx, qregs, qsp, qrd, qwr, qframe⟩ := q
  rw [hm] at qdone qrsi qrdx qframe
  generalize hk : min m 16 = k at qdone qrsi qrdx qframe
  obtain hk1 : 1 ≤ k := by omega_arith
  obtain hkm : k ≤ m := by omega_arith
  let D := s₀.gpr .x1
  let S := s₀.gpr .x0
  obtain r9 : s.gpr .x5 = s₀.gpr .x5 := h.regs _ (by simp)
  obtain rdi : s.gpr .x0 = S := h.regs _ (by simp)
  obtain workR_eq : workR s = workR s₀ := by simp only [workR, r9]
  rw [h.x1, workR_eq] at qframe
  rw [h.x1] at qrsi qdone
  rw [rdi] at qdone
  -- the memory written so far
  obtain frame' : Frame [workR s₀, ⟨D, 16 * (n - (m - k))⟩] s₀.mem s'.mem := by
    obtain f₁ : Frame [workR s₀, ⟨D, 16 * (n - (m - k))⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 16 * (n - (m - k))⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          Region.sub_prefix (by omega_arith)⟩
    obtain f₂ : Frame [workR s₀, ⟨D, 16 * (n - (m - k))⟩] s.mem s'.mem := qframe.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 16 * (n - (m - k))⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          Offset.sub_base _ (by omega_arith)⟩
    exact f₁.trans f₂
  obtain workSep : ∀ b, b < n → (⟨D + BitVec.ofNat 64 (16 * b), 16⟩ : Region).Disjoint (workR s₀) := fun b hb =>
    (E.dataSep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right
      (Region.sub_prefix (by unfold scratchSlots; omega_arith))
  obtain done' : ∀ b < n - (m - k), Spec.Seed.blockAt s'.mem (D + BitVec.ofNat 64 (16 * b)) =
      Spec.Seed.crypt (keysAt d s₀.mem S) (Spec.Seed.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * b))) := by
    intro b hb
    by_cases hb' : b < n - m
    · rw [← h.done b hb']
      refine blockAt_frame qframe fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact workSep b (by omega_arith)
      · exact Offset.disjoint D (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega_arith⟩
      obtain e := qdone j (by omega_arith)
      rw [Offset.add_ofNat_add_ofNat, show 16 * (n - m) + 16 * j = 16 * (n - m + j) by omega_arith] at e
      rw [e]
      obtain hK : ∀ i < 16, keysAt d s.mem S i = keysAt d s₀.mem S i := fun i hi =>
        keysAt_frame h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          obtain ⟨-, -, hdis⟩ := E.keys i hi
          rcases hr with rfl | rfl
          · exact hdis.sub_right (Region.sub_prefix (by unfold scratchSlots; omega_arith))
          · exact (E.keyData i hi).sub_right (Region.sub_prefix (by omega_arith))
      obtain hB : Spec.Seed.blockAt s.mem (D + BitVec.ofNat 64 (16 * (n - m + j))) =
          Spec.Seed.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * (n - m + j))) :=
        blockAt_frame h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact workSep _ (by omega_arith)
          · exact Offset.disjoint_base D (by omega_arith) (by omega_arith)
      rw [hB]
      exact crypt_congr hK _
  obtain rdx' : s'.gpr .x2 = BitVec.ofNat 64 (m - k) := by
    rw [qrdx, h.x2, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith) hkm]
  obtain zf' : isa.eval (.nonzero .x .x2) s' = some (BitVec.ofNat 64 (m - k) != 0) := by
    show some (s'.read .x .x2 != 0) = _
    rw [read_x, rdx']
  obtain regs' : ∀ r ∈ [Reg.x0, .x5], s'.gpr r = s₀.gpr r := fun r hr =>
    (qregs r hr).trans (h.regs r hr)
  obtain sp' : s'.sp = s₀.sp := qsp.trans h.sp
  obtain rd' := qrd.trans h.rd
  obtain wr' := qwr.trans h.wr
  by_cases hend : m ≤ 16
  · have hkm' : k = m := by omega_arith
    left
    refine ⟨?_, regs', sp', rd', wr', ?_, ?_⟩
    · rw [zf', hkm', Nat.sub_self]; rfl
    · rw [hkm', Nat.sub_self, Nat.sub_zero] at done'; exact done'
    · rw [hkm', Nat.sub_self, Nat.sub_zero] at frame'; exact frame'
  · have hk16 : k = 16 := by omega_arith
    right
    refine ⟨?_, m - k, by omega_arith, ⟨by omega_arith, by omega_arith, rdx', ?_, regs', sp', rd', wr', done', frame'⟩⟩
    · rw [zf']
      have : (BitVec.ofNat 64 (m - k) != 0) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        rw [toNat_ofNat_le (show m - k ≤ n by omega_arith) E.fit] at this
        have z : (0 : BitVec 64).toNat = 0 := rfl
        omega_arith
      rw [this]
    · rw [qrsi, Offset.add_ofNat_add_ofNat]; congr 2; omega_arith

/-! ## The keys -/

/-- Where round `j + 1`'s key is in the schedule. -/
def keyOff : Spec.Seed.Direction → Nat → Nat
  | .encrypt, j => 8 * j
  | .decrypt, j => 8 * (15 - j)

theorem keyOff_le (d : Spec.Seed.Direction) {j : Nat} (hj : j < 16) : keyOff d j + 8 ≤ 128 := by
  cases d <;> simp only [keyOff] <;> omega_arith

theorem kp_start_const (d : Spec.Seed.Direction) :
    ∀ j < 16, BitVec.ofNat 64 (keyStart d) + BitVec.ofNat 64 j * stepW d = BitVec.ofNat 64 (keyOff d j) := by
  cases d <;> decide

theorem kp_start (d : Spec.Seed.Direction) (S : Addr) {j : Nat} (hj : j < 16) :
    kp d (S + BitVec.ofNat 64 (keyStart d)) j = S + BitVec.ofNat 64 (keyOff d j) := by
  rw [kp, BitVec.add_assoc, kp_start_const d j hj]

/-- The block function in the direction `d`. -/
def cipher (d : Spec.Seed.Direction) (K : Spec.Seed.Schedule) (b : Spec.Seed.Block) : Spec.Seed.Block :=
  match d with
  | .encrypt => Spec.Seed.encryptBlock K b
  | .decrypt => Spec.Seed.decryptBlock K b

theorem crypt_keysAt (d : Spec.Seed.Direction) (m : Mem) (S : Addr) (b : Spec.Seed.Block) :
    Spec.Seed.crypt (keysAt d m (S + BitVec.ofNat 64 (keyStart d))) b = cipher d (Spec.Seed.scheduleAt m S) b := by
  cases d
  · show _ = Spec.Seed.crypt (Spec.Seed.roundKey (Spec.Seed.scheduleAt m S)) b
    refine crypt_congr (fun j hj => ?_) b
    rw [keysAt, kp_start _ _ hj, roundKey_readW _ _ hj]
    simp only [keyOff]
  · show _ = Spec.Seed.crypt (fun j => Spec.Seed.roundKey (Spec.Seed.scheduleAt m S) (15 - j)) b
    refine crypt_congr (fun j hj => ?_) b
    rw [keysAt, kp_start _ _ hj, roundKey_readW _ _ (by omega_arith)]
    simp only [keyOff]

theorem ecb_blocks (K : Spec.Seed.Schedule) (d : Spec.Seed.Direction) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, Spec.Seed.blockAt m' (D + BitVec.ofNat 64 (16 * b)) =
      cipher d K (Spec.Seed.blockAt m (D + BitVec.ofNat 64 (16 * b)))) :
    Spec.Seed.blocksAt m' D n = Spec.Seed.ecb K d (Spec.Seed.blocksAt m D n) := by
  cases d <;>
  · simp only [Spec.Seed.blocksAt, Spec.Seed.ecb, List.map_map]
    apply List.map_congr_left
    intro b hb
    rw [Function.comp_apply]
    exact h b (List.mem_range.mp hb)

/-! ## The function -/

/-- What the function needs: the scratch buffer and the data writable, the
schedule readable, apart from each other. -/
structure EcbPre (s : State) : Prop where
  scratch : ∃ n, 8 * scratchSlots ≤ n ∧ (⟨s.gpr .x3, n⟩ : Region) ∈ s.wr
  dataIn : (⟨s.gpr .x1, 16 * (s.gpr .x2).toNat⟩ : Region) ∈ s.wr
  keyIn : (⟨s.gpr .x0, 128⟩ : Region) ∈ s.rd
  keyData : (⟨s.gpr .x0, 128⟩ : Region).Disjoint ⟨s.gpr .x1, 16 * (s.gpr .x2).toNat⟩
  keyBuf : (⟨s.gpr .x0, 128⟩ : Region).Disjoint ⟨s.gpr .x3, 8 * scratchSlots⟩
  dataBuf : (⟨s.gpr .x1, 16 * (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x3, 8 * scratchSlots⟩
  fit : 16 * (s.gpr .x2).toNat ≤ 2 ^ 64

/-- What the function does: every block of the data becomes its encryption or
decryption, the callee-saved registers it uses are restored, and only the
scratch buffer and the data change. -/
structure EcbPost (d : Spec.Seed.Direction) (s s' : State) : Prop where
  saved : ∀ p ∈ Impl.Seed.AArch64.savedRegs, s'.gpr p.1 = s.gpr p.1
  done : ∀ b < (s.gpr .x2).toNat, Spec.Seed.blockAt s'.mem (s.gpr .x1 + BitVec.ofNat 64 (16 * b)) =
    cipher d (Spec.Seed.scheduleAt s.mem (s.gpr .x0))
      (Spec.Seed.blockAt s.mem (s.gpr .x1 + BitVec.ofNat 64 (16 * b)))
  frame : Frame [⟨s.gpr .x3, 8 * scratchSlots⟩, ⟨s.gpr .x1, 16 * (s.gpr .x2).toNat⟩] s.mem s'.mem

theorem savedRegs_ok : ∀ p ∈ Impl.Seed.AArch64.savedRegs, p.2 < scratchSlots ∧ p.1 ≠ .x5 ∧ 112 ≤ p.2 := by
  decide

theorem setup_eq (d : Spec.Seed.Direction) : setup d =
    [movR .x5 .x3] ++ (Impl.Seed.AArch64.savedRegs.map fun p => (p.2, p.1)).map (fun p => stS p.1 p.2) ++
      ([.addImm .x .x0 .x0 (keyStart d)] : List Instr) := rfl

theorem restore_eq : restore = Impl.Seed.AArch64.savedRegs.map (fun p => ldS p.1 p.2) := rfl

theorem keyStart_lt (d : Spec.Seed.Direction) : keyStart d < 4096 := by cases d <;> decide

theorem ecb_ok (d : Spec.Seed.Direction) {s : State} (h : EcbPre s) : WP isa (ecb d) s (EcbPost d s) := by
  let n := (s.gpr .x2).toNat
  let D := s.gpr .x1
  let S := s.gpr .x0
  have hn := h.fit
  rw [ecb]
  apply WP.seq
  -- `x5 := x3`
  let s₁ := s.write .x .x5 (s.gpr .x3)
  obtain e₁ : runBlock isa [movR .x5 .x3] s = some s₁ := by
    rw [runBlock_cons, exec_movR, runStep_some, runBlock_nil]
  obtain r9₁ : s₁.gpr .x5 = s.gpr .x3 := by simp [s₁, gpr_write]
  obtain g₁ : ∀ r, r ≠ .x5 → s₁.gpr r = s.gpr r := fun r hr => gpr_write_of_ne _ _ _ hr
  obtain scr₁ : scratchR s₁ = ⟨s.gpr .x3, 8 * scratchSlots⟩ := by simp only [scratchR, r9₁]
  obtain room₁ : Room s₁ := by
    obtain ⟨n, hn, hm⟩ := h.scratch; exact ⟨n, hn, by rw [r9₁]; exact hm⟩
  -- the saved registers
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, sp₂, f₂, set₂, keep₂⟩ := stores_ok room₁
    (Impl.Seed.AArch64.savedRegs.map fun p => (p.2, p.1)) (by decide) (by decide)
  -- the key pointer
  let s₅ := s₂.write .x .x0 (s₂.read .x .x0 + BitVec.ofNat _ (keyStart d))
  refine WP.of_runBlock ⟨s₅, by
    rw [setup_eq]
    exact runBlock_trans (runBlock_trans e₁ e₂)
      (by rw [runBlock_cons, exec_addImm_x (keyStart_lt d), runStep_some, runBlock_nil]), ?_⟩
  -- the state after the setup
  obtain G₅ : ∀ r, r ≠ .x5 → r ≠ .x0 → s₅.gpr r = s.gpr r := fun r a b => by
    rw [gpr_write_of_ne _ _ _ b, g₂, g₁ r a]
  obtain r9₅ : s₅.gpr .x5 = s.gpr .x3 := by rw [gpr_write_of_ne _ _ _ (by decide), g₂, r9₁]
  obtain rdi₅ : s₅.gpr .x0 = S + BitVec.ofNat 64 (keyStart d) := by
    simp only [s₅, gpr_write_self, BitVec.setWidth_eq, read_x, g₂, g₁ _ (show Reg.x0 ≠ .x5 by decide)]; rfl
  obtain rd₅ : s₅.rd = s.rd := by simp only [s₅, rd_write, rd₂]; rfl
  obtain wr₅ : s₅.wr = s.wr := by simp only [s₅, wr_write, wr₂]; rfl
  obtain sp₅ : s₅.sp = s.sp := by simp only [s₅, sp_write, sp₂]; rfl
  obtain mem₅ : s₅.mem = s₂.mem := by simp only [s₅, mem_write]
  obtain slot₅ : ∀ k, slotW s₅ k = slotW s₂ k := fun k => by
    show s₅.mem.readW (Straight.wordAddr (s₅.gpr .x5) k) 64 = s₂.mem.readW (Straight.wordAddr (s₂.gpr .x5) k) 64
    rw [mem₅, r9₅, g₂, r9₁]
  obtain scr₅ : scratchR s₅ = ⟨s.gpr .x3, 8 * scratchSlots⟩ := by simp only [scratchR, r9₅]
  obtain room₅ : Room s₅ := by
    obtain ⟨n, hn, hm⟩ := h.scratch; exact ⟨n, hn, by rw [r9₅, wr₅]; exact hm⟩
  obtain f₅ : Frame [⟨s.gpr .x3, 8 * scratchSlots⟩] s.mem s₅.mem := by
    rw [mem₅, ← scr₁]; exact f₂
  obtain zf₅ : isa.eval (.zero .x .x2) s₅ = some (s.gpr .x2 == 0) := by
    show some (s₅.read .x .x2 == 0) = _
    rw [read_x, G₅ _ (by decide) (by decide)]
  obtain rsi₅ : s₅.gpr .x1 = D := G₅ _ (by decide) (by decide)
  obtain rdx₅ : s₅.gpr .x2 = s.gpr .x2 := G₅ _ (by decide) (by decide)
  obtain saved₅ : ∀ p ∈ Impl.Seed.AArch64.savedRegs, slotW s₅ p.2 = s.gpr p.1 := by
    intro p hp
    obtain hp' := savedRegs_ok p hp
    rw [slot₅, set₂ (p.2, p.1) (List.mem_map_of_mem hp), g₁ _ hp'.2.1]
  -- the keys, in the schedule
  obtain K₅ : ∀ j < 16, keysAt d s₅.mem (s₅.gpr .x0) j = keysAt d s.mem (S + BitVec.ofNat 64 (keyStart d)) j := by
    intro j hj
    rw [rdi₅]
    refine keysAt_frame f₅ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    rw [kp_start _ _ hj]
    exact h.keyBuf.sub_left (Offset.sub_base _ (keyOff_le d hj))
  obtain B₅ : ∀ b < n, Spec.Seed.blockAt s₅.mem (D + BitVec.ofNat 64 (16 * b)) =
      Spec.Seed.blockAt s.mem (D + BitVec.ofNat 64 (16 * b)) := fun b hb =>
    blockAt_frame f₅ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.dataBuf.sub_left (Offset.sub_base _ (by omega_arith))
  -- after the loop (or none), the registers restored
  obtain finish : ∀ s₆ : State, BatchesPost d s₅ n s₆ → WP isa (.block restore) s₆ (EcbPost d s) := by
    intro s₆ p
    obtain r9₆ : s₆.gpr .x5 = s₅.gpr .x5 := p.regs _ (by simp)
    obtain room₆ : Room s₆ := room_congr room₅ r9₆ p.wr
    obtain ⟨s', run', m', sp', set', keep'⟩ := loads_ok room₆ Impl.Seed.AArch64.savedRegs
      (fun q hq => ⟨(savedRegs_ok q hq).1, (savedRegs_ok q hq).2.1⟩) (by decide)
    refine WP.of_runBlock ⟨s', by rw [restore_eq]; exact run', ?_⟩
    have pf := p.frame
    rw [rsi₅] at pf
    obtain frame : Frame [⟨s.gpr .x3, 8 * scratchSlots⟩, ⟨D, 16 * n⟩] s.mem s'.mem := by
      rw [m']
      refine (f₅.mono (by simp)).trans (pf.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨_, List.mem_cons_self, ?_⟩
        simp only [workR, r9₅]
        exact Region.sub_prefix (by unfold scratchSlots; omega_arith)
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    refine ⟨fun q hq => ?_, fun b hb => ?_, frame⟩
    · have hq' := savedRegs_ok q hq
      rw [set' q hq, ← saved₅ q hq]
      show s₆.mem.readW (Straight.wordAddr (s₆.gpr .x5) q.2) 64 =
        s₅.mem.readW (Straight.wordAddr (s₅.gpr .x5) q.2) 64
      rw [r9₆]
      refine pf.readW (r := ⟨Straight.wordAddr (s₅.gpr .x5) q.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [workR]
        exact Offset.disjoint_base _ (by omega) (by unfold scratchSlots at hq'; omega)
      · rw [r9₅]
        exact (h.dataBuf.sub_right (Offset.sub_base _ (by unfold scratchSlots at hq' ⊢; omega))).symm
    · have e := p.done b hb
      rw [rsi₅] at e
      rw [m', e, B₅ b hb, crypt_congr K₅, crypt_keysAt]
  apply WP.seq
  apply WP.ite (s.gpr .x2 == 0) zf₅
  · intro hz
    apply WP.block_nil
    obtain hn0 : n = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz)
      simpa [n] using this
    refine finish s₅ ⟨fun _ _ => rfl, rfl, rfl, rfl, fun b hb => by omega_arith, ?_⟩
    rw [hn0]; exact Frame.refl _ _
  · intro hz
    obtain hn1 : 1 ≤ n := by
      have : s.gpr .x2 ≠ 0 := by simpa using hz
      have : (s.gpr .x2).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
      omega_arith
    obtain E : BatchesEnv d s₅ n := by
      refine ⟨room₅, by rw [rsi₅, wr₅]; exact h.dataIn, by rw [rsi₅, scr₅]; exact h.dataBuf, hn,
        fun j hj => ?_, fun j hj => ?_⟩
      · rw [rdi₅, kp_start _ _ hj, rd₅, wr₅, scr₅]
        obtain hle := keyOff_le d hj
        refine ⟨⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩, ?_,
          h.keyBuf.sub_left (Offset.sub_base _ hle)⟩
        rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_ofNat_add_ofNat]
        exact ⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
      · rw [rdi₅, kp_start _ _ hj, rsi₅]
        exact h.keyData.sub_left (Offset.sub_base _ (keyOff_le d hj))
    obtain I : BatchesInv d s₅ n n s₅ := by
      refine ⟨hn1, Nat.le_refl _, ?_, ?_, fun _ _ => rfl, rfl, rfl, rfl, fun b hb => by omega_arith,
        by rw [Nat.sub_self]; exact Frame.refl _ _⟩
      · rw [rdx₅]; exact BitVec.eq_of_toNat_eq (by simp [n])
      · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add]
    exact WP.mono (loop_ok d E n s₅ I) finish

end VG.Proof.Seed.AArch64

end

end

/-! # The ECB functions meet their contracts, with the scratch buffer as an argument -/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64

/-- With `n` bytes of working space at `x3` (976 for ECB, 1088 for the blocks functions). -/
def contract (d : Spec.Seed.Direction) (n : Nat := 976) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x1, 16 * (s.gpr .x2).toNat⟩
    let buf : Region := ⟨s.gpr .x3, n⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ (s.gpr .x1).toNat + 16 * (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' :=
    Spec.Seed.blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.Seed.ecb (Spec.Seed.scheduleAt s.mem (s.gpr .x0)) d
        (Spec.Seed.blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub := PublicRegs [.x0, .x1, .x2, .x3]

theorem ecbPre_of {s : State} {d : Spec.Seed.Direction} {n : Nat} (hn : 976 ≤ n)
    (hs : (contract d n).pre s) : EcbPre s := by
  obtain ⟨rd, wr, kd, kb, db, fit⟩ := hs
  have sub : Region.Sub ⟨s.gpr .x3, 8 * Impl.Seed.AArch64.scratchSlots⟩ ⟨s.gpr .x3, n⟩ := by
    have h := Offset.sub_base (s.gpr .x3) (d := 0) (n := 8 * Impl.Seed.AArch64.scratchSlots) (k := n)
      (by unfold Impl.Seed.AArch64.scratchSlots; omega_using [hn])
    simpa using h
  exact { scratch := ⟨n, by unfold Impl.Seed.AArch64.scratchSlots; omega_using [hn], by
            rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
          dataIn := by rw [wr]; exact List.mem_cons_self
          keyIn := by rw [rd]; exact List.mem_cons_self
          keyData := kd
          keyBuf := kb.sub_right sub
          dataBuf := db.sub_right sub
          fit := by omega_using [fit] }

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 976⟩]

/-- `satState` with the 1088 bytes of `vg_seed_*_blocks`'s working space. -/
def satStateBlocks : State := { satState with wr := [⟨0x2000, 0⟩, ⟨0x3000, 1088⟩] }

/-- The callee-saved registers, from those the code saves and `x30`, which it never writes. -/
theorem abi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hs : ∀ p ∈ Impl.Seed.AArch64.savedRegs, s'.gpr p.1 = s.gpr p.1) (h30 : s'.gpr .x30 = s.gpr .x30)
    (hv : c.allInstrs keepsV = true) : abiPreserved s s' := by
  refine ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he hv⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hs (.x19, 112) (by decide)
  · exact hs (.x20, 113) (by decide)
  · exact hs (.x21, 114) (by decide)
  · exact hs (.x22, 115) (by decide)
  · exact hs (.x23, 116) (by decide)
  · exact hs (.x24, 117) (by decide)
  · exact hs (.x25, 118) (by decide)
  · exact hs (.x26, 119) (by decide)
  · exact hs (.x27, 120) (by decide)
  · exact hs (.x28, 121) (by decide)
  · exact h30

theorem ecb_wp (d : Spec.Seed.Direction) {n : Nat} (hn : 976 ≤ n) (s : State) (hs : (contract d n).pre s) :
    WP isa (Impl.Seed.AArch64.ecb d) s fun s' =>
      (∀ p ∈ Impl.Seed.AArch64.savedRegs, s'.gpr p.1 = s.gpr p.1) ∧ (contract d n).post s s' :=
  WP.mono (ecb_ok d (ecbPre_of hn hs)) fun _ hp => ⟨hp.saved, ecb_blocks _ _ _ _ _ _ hp.done⟩

theorem encrypt_correct {n : Nat} (hn : 976 ≤ n) (s : State) (hs : (contract .encrypt n).pre s) :
    ∃ t s', Exec isa Impl.Seed.AArch64.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt n).post s s' := by
  obtain ⟨t, s', he, ⟨hsv, hp⟩, h30⟩ := WP.gprs (c := Impl.Seed.AArch64.encrypt) (ecb_wp .encrypt hn s hs)
    (rs := [.x30]) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, abi_of he hsv (h30 _ (by simp)) (by lit_decide), hp⟩

theorem decrypt_correct {n : Nat} (hn : 976 ≤ n) (s : State) (hs : (contract .decrypt n).pre s) :
    ∃ t s', Exec isa Impl.Seed.AArch64.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt n).post s s' := by
  obtain ⟨t, s', he, ⟨hsv, hp⟩, h30⟩ := WP.gprs (c := Impl.Seed.AArch64.decrypt) (ecb_wp .decrypt hn s hs)
    (rs := [.x30]) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, abi_of he hsv (h30 _ (by simp)) (by lit_decide), hp⟩

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2, .x3] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
      s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 := by
  simp [PublicRegs]

/-- ECB against `vg_seed_encrypt_blocks`'s contract: its working space is 136 words, of which
the code uses the first 122. -/
theorem encrypt_blocks_verified : Verified target Impl.Seed.AArch64.encrypt
    (Proof.Seed.blocksContract abi .encrypt) := by
  refine Verified.of_correct (encrypt_correct (n := 1088) (by decide)) (encrypt_constantTime _) ?_
  sig_implies [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, abi, argRegs,
    contract, publicRegs_four] [satStateBlocks] using satStateBlocks

theorem decrypt_blocks_verified : Verified target Impl.Seed.AArch64.decrypt
    (Proof.Seed.blocksContract abi .decrypt) := by
  refine Verified.of_correct (decrypt_correct (n := 1088) (by decide)) (decrypt_constantTime _) ?_
  sig_implies [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, abi, argRegs,
    contract, publicRegs_four] [satStateBlocks] using satStateBlocks

end VG.Proof.Seed.AArch64
