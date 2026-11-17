module

import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Seed.RISCV64.Round
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
public import VerifiedGarbage.Proof.Seed.RISCV64.Lanes
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Seed.G
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Seed.Rounds

/-! ### `Seed.RISCV64.Batch`, which this module and modules that import it used -/

section

/-! ### `Seed.RISCV64.Rounds`, which only this module used -/

section

/-!
# Sixteen rounds on RISC-V

As on PPC64LE (`Proof/Seed/PPC64LE/Ecb.lean`): `rounds_ok`: `rounds d`
does sixteen rounds on every lane, with round `j + 1`'s key at
`a0 + j * step` (`kp`), and moves `a0` back.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64 VG.Proof.Seed
open VG.Impl.Aes.RISCV64 (sb)

/-- Where round `j + 1`'s key is, from `p`. -/
def kp (d : Spec.Seed.Direction) (p : Addr) (j : Nat) : Addr := p + BitVec.ofNat 64 j * stepW d

theorem kp_succ (d : Spec.Seed.Direction) (p : Addr) (j : Nat) : kp d p j + stepW d = kp d p (j + 1) := by
  simp only [kp, BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]

theorem exec_keyBack (d : Spec.Seed.Direction) (s : State) :
    exec (keyBack d) s = some (s.write .a0 (s.gpr .a0 - BitVec.ofNat 64 16 * stepW d)) := by
  cases d
  · rw [keyBack, exec_addi (by decide), show (-128 : Int) = -((128 : Nat) : Int) from rfl,
      RISCV64.Steps.add_ofInt_neg]; rfl
  · rw [keyBack, exec_addi (by decide), show BitVec.ofNat 64 16 * stepW .decrypt =
      -BitVec.ofNat 64 128 by decide, BitVec.sub_neg]; rfl

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
  quads : ∀ b < 16, quad s b = roundsN (keysAt d s₀.mem (s₀.gpr .a0)) (16 - m) (quad s₀ b)
  room : Room s
  masks : Masks s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  a0 : s.gpr .a0 = kp d (s₀.gpr .a0) (16 - m)
  a4 : s.gpr .a4 = BitVec.ofNat 64 m
  regs : ∀ r ∈ [Reg.ra, .a1, .a2, .a3, .a5], s.gpr r = s₀.gpr r
  frame : Frame [workR s₀] s₀.mem s.mem

theorem contains_prefix {a : Addr} {k n : Nat} (h : k ≤ n) : (⟨a, n⟩ : Region).Contains a k := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

theorem a4_sub (m : Nat) (h : 1 ≤ m) (h' : m ≤ 16) :
    BitVec.ofNat 64 m - 1 = BitVec.ofNat 64 (m - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega_arith

theorem rounds_ok (d : Spec.Seed.Direction) {s : State} (h : Room s) (hm : Masks s)
    (hk : KeysOk d s (s.gpr .a0)) :
    WP isa (rounds d) s (fun s' =>
      (∀ b < 16, quad s' b = roundsN (keysAt d s.mem (s.gpr .a0)) 16 (quad s b)) ∧
      Room s' ∧ Masks s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ [Reg.ra, .a0, .a1, .a2, .a3, .a5], s'.gpr r = s.gpr r) ∧
      Frame [workR s] s.mem s'.mem) := by
  let s1 := s.write .a4 (BitVec.ofNat 64 16)
  have e1 : runBlock isa [.li .a4 16] s = some s1 := by
    simp only [runBlock_cons, exec_li (show imm12 16 by decide), runStep_some, runBlock_nil, s1]
    rfl
  have q1 : ∀ b, quad s1 b = quad s b := fun b => by
    simp only [quad, s1, lv_write _ _ (show ¬ sb = .a4 by decide)]
  refine WP.seq (WP.of_runBlock ⟨s1, e1, ?_⟩)
  refine WP.seq (WP.loop (M := isa) (fun m t => RoundsInv d s m t) ?_ 16 s1 ?_)
  · intro m t inv
    have hi : 16 - m < 16 := by have := inv.le; omega_arith
    obtain ⟨hk0, hk1, hdis⟩ := hk (16 - m) hi
    have hk0' : InRegions (t.rd ++ t.wr) (t.gpr .a0) 4 := by rw [inv.rd, inv.wr, inv.a0]; exact hk0
    have hk1' : InRegions (t.rd ++ t.wr) (t.gpr .a0 + 4) 4 := by rw [inv.rd, inv.wr, inv.a0]; exact hk1
    obtain ⟨t', ht', hq, hroom, hmasks, hrd, hwr, hsp, hr3, hr7, hx1, hx2, hx3, hx5, hxra, hfr⟩ :=
      round_ok d inv.room inv.masks hk0' hk1'
    -- The key, from the original memory.
    have hkey : (t.mem.readW (t.gpr .a0) 32, t.mem.readW (t.gpr .a0 + 4) 32) =
        keysAt d s.mem (s.gpr .a0) (16 - m) := by
      simp only [keysAt, inv.a0]
      have hd : ∀ r ∈ [workR s], Region.Disjoint ⟨kp d (s.gpr .a0) (16 - m), 8⟩ r := by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact hdis.sub_right (Region.sub_prefix (by unfold scratchSlots; omega_arith))
      refine congr (congrArg Prod.mk ?_) ?_
      · exact inv.frame.readW (contains_prefix (by decide)) hd (by decide)
      · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
        exact inv.frame.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega_arith) (by omega_arith))
          hd (by decide)
    refine WP.of_runBlock ⟨t', ht', ?_⟩
    have hquads : ∀ b < 16, quad t' b = roundsN (keysAt d s.mem (s.gpr .a0)) (16 - (m - 1)) (quad s b) := by
      intro b hb
      rw [hq b hb, hkey, inv.quads b hb, show 16 - (m - 1) = 16 - m + 1 by have := inv.le; omega_arith,
        roundsN_succ]
    have hr7' : t'.gpr .a4 = BitVec.ofNat 64 (m - 1) := by
      rw [hr7, inv.a4, a4_sub m inv.le.1 inv.le.2]
    have hregs : ∀ r ∈ [Reg.ra, .a1, .a2, .a3, .a5], t'.gpr r = s.gpr r := by
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hxra]; exact inv.regs _ (by simp)
      · rw [hx1]; exact inv.regs _ (by simp)
      · rw [hx2]; exact inv.regs _ (by simp)
      · rw [hx3]; exact inv.regs _ (by simp)
      · rw [hx5]; exact inv.regs _ (by simp)
    have hframe : Frame [workR s] s.mem t'.mem := by
      refine inv.frame.trans ?_
      simpa [workR, show t.gpr sb = s.gpr sb from inv.regs .a5 (by simp)] using hfr
    have hc : isa.eval (.nonzero .a4) t' = some (BitVec.ofNat 64 (m - 1) != 0) := by
      rw [RISCV64.Steps.eval_nonzero, hr7']
    by_cases hm1 : m = 1
    · subst hm1
      left
      refine ⟨by rw [hc]; rfl, ?_⟩
      let u := t'.write .a0 (t'.gpr .a0 - BitVec.ofNat 64 16 * stepW d)
      refine WP.of_runBlock ⟨u, by rw [runBlock_cons, exec_keyBack, runStep_some, runBlock_nil], ?_⟩
      have hu5 : u.gpr sb = t'.gpr sb := gpr_write_of_ne _ _ (by decide)
      refine ⟨fun b hb => ?_, room_congr hroom hu5 rfl,
        hmasks.frame hu5 (gpr_write_of_ne _ _ (by decide)) (by rw [mem_write]; exact Frame.refl _ _),
        by rw [rd_write, hrd, inv.rd],
        by rw [wr_write, hwr, inv.wr], by rw [sp_write, hsp, inv.sp], fun r hr => ?_, by rw [mem_write]; exact hframe⟩
      · have : quad u b = quad t' b := by simp only [quad, u, lv_write _ _ (show ¬ sb = .a0 by decide)]
        rw [this, hquads b hb]
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | hr
        · rw [gpr_write_of_ne _ _ (by decide)]; exact hregs _ (by simp)
        · rw [gpr_write_self, hr3, inv.a0, kp_succ, kp_back]
        · rw [gpr_write_of_ne _ _ (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
          exact hregs _ (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; exact .inr hr)
    · right
      refine ⟨?_, m - 1, by omega_arith, ⟨by have := inv.le; omega_arith, hquads, hroom, hmasks,
        by rw [hrd, inv.rd],
        by rw [hwr, inv.wr], by rw [hsp, inv.sp], ?_, hr7', hregs, hframe⟩⟩
      · rw [hc]
        have : (BitVec.ofNat 64 (m - 1) != 0) = true := by
          simp only [bne_iff_ne, ne_eq]
          intro h0
          have hm2 : 2 ≤ m := by have := inv.le; omega_arith
          have hm16 := inv.le.2
          have := congrArg BitVec.toNat h0
          rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mod_eq_of_lt (by omega_arith)] at this
          omega_arith
        rw [this]
      · rw [hr3, inv.a0, kp_succ, show 16 - m + 1 = 16 - (m - 1) by have := inv.le; omega_arith]
  · refine ⟨by omega_arith, fun b _ => by rw [q1]; rfl, room_congr h rfl rfl,
      hm.frame (gpr_write_of_ne _ _ (by decide)) (gpr_write_of_ne _ _ (by decide))
        (by simp only [s1, mem_write]; exact Frame.refl _ _), rfl, rfl, rfl,
      by simp [s1, kp, gpr_write], rfl, fun r hr => ?_, Frame.refl _ _⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Seed.RISCV64

end

end

/-! ### `Seed.RISCV64.Copy`, which only this module used -/

section

/-!
# Copying blocks into the arrays and back

As on PPC64LE (`Proof/Seed/PPC64LE/Copy.lean`): `copyIn_loop`: the loop of
`copyInBody` copies `m` blocks from `p` into lanes `0 … m - 1` of the
arrays, each word big-endian (`bw`, the byte reversal of the little-endian
word, which is what `loadBE32` assembles from the bytes: `beWord_eq`).
`copyOut_loop`: the loop of `copyOutBody` copies them back, `R` first, each
word stored big-endian a byte at a time (`storeBE`, which is the
little-endian write of its byte reversal: `writeBytes_beBytes`).
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64 VG.WriteBytes
open VG.Impl.Aes.RISCV64 (sb)

-- The copies share one set of rewrites, not all of which each uses.
set_option linter.unusedSimpArgs false

/-- Word `w` of block `b` from `p`, big-endian. -/
def bw (m : Mem) (p : Addr) (b w : Nat) : BitVec 32 :=
  byteRev32 (m.readW (p + BitVec.ofNat 64 (16 * b + 4 * w)) 32)

/-- Byte `j` (in memory order) of a byte-swapped word is byte `3 - j` of the word. -/
theorem byteRev32_byte (x : BitVec 32) {j : Nat} (hj : j < 4) :
    (byteRev32 x).extractLsb' (8 * j) 8 = (x >>> (8 * (3 - j))).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain h4 := Proof.Seed.getLsbD_append4 (x.extractLsb' 0 8) (x.extractLsb' 8 8) (x.extractLsb' 16 8)
    (x.extractLsb' 24 8) hi
  obtain e : ((byteRev32 x).extractLsb' (8 * j) 8).getLsbD i = (byteRev32 x).getLsbD (8 * j + i) := by
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [e]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  unfold byteRev32
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega_arith) with rfl | rfl | rfl | rfl
  · rw [h4.1]; simp [BitVec.getLsbD_extractLsb', hi]
  · rw [h4.2.1]; simp [BitVec.getLsbD_extractLsb', hi]
  · rw [h4.2.2.1]; simp [BitVec.getLsbD_extractLsb', hi]
  · rw [h4.2.2.2]; simp [BitVec.getLsbD_extractLsb', hi]

/-- The big-endian word of four bytes is the byte reversal of the
little-endian one. -/
theorem beWord_eq (m : Mem) (p : Addr) (off : Nat) :
    ByteLoad.beWord m p off = byteRev32 (m.readW (p + BitVec.ofNat 64 off) 32) := by
  rw [byteRev32_readW, ByteLoad.beWord]
  obtain e : ∀ k, p + BitVec.ofNat 64 off + BitVec.ofNat 64 k = p + BitVec.ofNat 64 (off + k) := by
    intro k; rw [BitVec.ofNat_add, BitVec.add_assoc]
  rw [← e 1, ← e 2, ← e 3]
  simp only [BitVec.add_assoc]
  rfl

/-- `storeBE 4`'s bytes are the little-endian write of the byte reversal. -/
theorem setWidth_shr8 (v : BitVec 32) (k : Nat) :
    ((v.setWidth 64) >>> k).setWidth 8 = (v >>> k).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  by_cases h : k + i < 32
  · simp [h, show k + i < 64 by omega_arith]
  · simp [show ¬ k + i < 32 from h, BitVec.getLsbD_of_ge v (k + i) (by omega_arith)]

theorem writeBytes_beBytes (m : Mem) (a : Addr) (v : BitVec 32) :
    writeBytes m a (ByteLoad.beBytes 4 (v.setWidth 64)) = m.writeW a (byteRev32 v) := by
  rw [show m.writeW a (byteRev32 v) = m.write a 4 (byteRev32 v) from rfl, write_eq_writeBytes]
  congr 1
  simp only [ByteLoad.beBytes]
  refine List.map_congr_left fun j hj => ?_
  obtain hj4 := List.mem_range.mp hj
  rw [byteRev32_byte _ hj4, setWidth_shr8]

theorem mem_arrA_of {w : Nat} (hw : w < 4) : arrSlot w ∈ arrays := by
  rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> decide

/-- What the copy into the arrays needs. -/
structure CopyPre (s : State) (p : Addr) (m : Nat) : Prop where
  room : Room s
  le : 1 ≤ m ∧ m ≤ 16
  read : ∀ b < m, ∀ w < 4, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (16 * b + 4 * w)) 4
  sep : Region.Disjoint ⟨p, 16 * m⟩ (arraysR s)

/-- The registers the copies write: their temporaries, cursors and counter. -/
def CopyRegs (r : Reg) : Prop := r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .t4

/-- After `j` blocks of the copy in. -/
structure CopyInInv (s₀ : State) (p : Addr) (m j : Nat) (s : State) : Prop where
  le : j ≤ m
  t3 : s.gpr .t3 = p + BitVec.ofNat 64 (16 * j)
  t4 : s.gpr .t4 = s₀.gpr sb + BitVec.ofNat 64 (4 * j)
  t2 : s.gpr .t2 = BitVec.ofNat 64 (m - j)
  lanes : ∀ w < 4, ∀ b < j, lv s (arrSlot w) b = bw s₀.mem p b w
  frame : Frame [arraysR s₀] s₀.mem s.mem
  regs : ∀ r, CopyRegs r → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem sb_copyRegs : CopyRegs sb := by unfold CopyRegs; decide

/-- The copy of word `w` of a block. -/
def inWord (w : Nat) : List Instr :=
  Impl.Words.RISCV64.loadBE32 .t0 .t1 .t3 (4 * w) ++ [.store .w .t0 .t4 (8 * arrSlot w)]

theorem copyInBody_eq : copyInBody = inWord 0 ++ (inWord 1 ++ (inWord 2 ++ (inWord 3 ++
    ([.addi .t3 .t3 16, .addi .t4 .t4 4, .addi .t2 .t2 (-1)] : List Instr)))) := by
  simp only [copyInBody, inWord, List.range_succ, List.range_zero, List.nil_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc, List.flatMap_append, List.cons_append,
    List.singleton_append]
  rfl

theorem arr_off (w j : Nat) (b : Addr) :
    b + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 (8 * arrSlot w) = b + BitVec.ofNat 64 (8 * arrSlot w + 4 * j) := by
  rw [Offset.add_add, Nat.add_comm]

theorem arr_ok {w : Nat} (hw : w < 4) : 8 * arrSlot w % 4 = 0 ∧ 8 * arrSlot w < 2048 := by
  unfold arrSlot; omega_arith


/-- One word of a block into its lane. -/
theorem copyInWord_ok {w j : Nat} (hw : w < 4) (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .t4 = s.gpr sb + BitVec.ofNat 64 (4 * j))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .t3 + BitVec.ofNat 64 (4 * w)) 4) :
    ∃ s', runBlock isa (inWord w) s = some s' ∧
      s'.mem = s.mem.writeW (laneA s (arrSlot w) j)
        (byteRev32 (s.mem.readW (s.gpr .t3 + BitVec.ofNat 64 (4 * w)) 32)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) := by
  obtain hL : arrSlot w ∈ arrays := mem_arrA_of hw
  obtain hla : s.gpr .t4 + BitVec.ofNat 64 (8 * arrSlot w) = laneA s (arrSlot w) j := by
    rw [hrb, arr_off _ _]; rfl
  obtain ⟨s1, e1, h1⟩ := run_of_wp (ByteLoad.loadBE32_ok (s := s) (d := .t0) (tmp := .t1) (n := .t3)
    (off := 4 * w) (by decide) (by decide) (by decide) (by omega_arith) hr)
  obtain g1 : ∀ r, r ≠ .t0 → r ≠ .t1 → s1.gpr r = s.gpr r := fun r a b => by
    rw [h1, gpr_write_of_ne _ _ a, gpr_write_of_ne _ _ b]
  obtain v1 : s1.gpr .t0 = (ByteLoad.beWord s.mem (s.gpr .t3) (4 * w)).setWidth 64 := by
    rw [h1, gpr_write_self]
  obtain m1 : s1.mem = s.mem := by rw [h1]; rfl
  obtain rd1 : s1.rd = s.rd := by rw [h1]; rfl
  obtain wr1 : s1.wr = s.wr := by rw [h1]; rfl
  obtain sp1 : s1.sp = s.sp := by rw [h1]; rfl
  obtain h4 : s1.gpr .t4 = s.gpr .t4 := g1 _ (by decide) (by decide)
  obtain e2 := exec_store_w (s := s1) (t := .t0) (n := .t4) (off := 8 * arrSlot w)
    (arr_ok hw).2 (by rw [h4, hla]; exact lane_al h hL hj)
    (by rw [h4, hla, wr1]; exact lane_wr h hL hj)
  refine ⟨{ s1 with mem := (s1.mem.writeW (s1.gpr .t4 + BitVec.ofNat 64 (8 * arrSlot w))
      ((s1.gpr .t0).setWidth 32)) },
    runBlock_trans e1 (by rw [runBlock_cons, e2, runStep_some, runBlock_nil]), ?_, rd1, wr1,
    sp1, fun r a b => g1 r a b⟩
  show s1.mem.writeW _ _ = _
  rw [h4, hla, v1, m1, lo32_ext, beWord_eq]

/-- The copy of one block into lane `j`, as writes of the block's words. -/
def inSpec (m : Mem) (q : Addr) : LaneSpec :=
  (List.range 4).map fun w => (arrSlot w, fun _ => byteRev32 (m.readW (q + BitVec.ofNat 64 (4 * w)) 32))

theorem inSpec_dests (m : Mem) (q : Addr) : ∀ kv ∈ inSpec m q, kv.1 ∈ arrays := by
  intro kv hkv
  simp only [inSpec, List.mem_map, List.mem_range] at hkv
  obtain ⟨w, hw, rfl⟩ := hkv
  exact mem_arrA_of hw

theorem copyInBody_ok {j : Nat} (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .t4 = s.gpr sb + BitVec.ofNat 64 (4 * j))
    (hr : ∀ w < 4, InRegions (s.rd ++ s.wr) (s.gpr .t3 + BitVec.ofNat 64 (4 * w)) 4)
    (hsep : ∀ w < 4, Region.Disjoint ⟨s.gpr .t3 + BitVec.ofNat 64 (4 * w), 4⟩ (arraysR s)) :
    ∃ s', runBlock isa copyInBody s = some s' ∧
      s'.mem = laneWrites s (inSpec s.mem (s.gpr .t3)) j ∧
      s'.gpr .t3 = s.gpr .t3 + 16 ∧ s'.gpr .t4 = s.gpr .t4 + 4 ∧
      s'.gpr .t2 = s.gpr .t2 - 1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, CopyRegs r → s'.gpr r = s.gpr r) := by
  -- The block's words keep their values while the lanes are written.
  obtain hkeep : ∀ (t : State), Frame [arraysR s] s.mem t.mem → ∀ w < 4,
      t.mem.readW (s.gpr .t3 + BitVec.ofNat 64 (4 * w)) 32 =
        s.mem.readW (s.gpr .t3 + BitVec.ofNat 64 (4 * w)) 32 := by
    intro t ht w hw
    refine ht.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'; exact hsep w hw
  obtain ⟨s1, e1, m1, rd1, wr1, sp1, g1⟩ := copyInWord_ok (w := 0) (by decide) hj s h hrb (hr 0 (by decide))
  obtain h1 : Room s1 := room_congr h (g1 _ (by decide) (by decide)) wr1
  obtain ⟨s2, e2, m2, rd2, wr2, sp2, g2⟩ := copyInWord_ok (w := 1) (by decide) hj s1 h1
    (by rw [g1 _ (by decide) (by decide), g1 _ (by decide) (by decide), hrb])
    (by rw [rd1, wr1, g1 _ (by decide) (by decide)]; exact hr 1 (by decide))
  obtain h2 : Room s2 := room_congr h1 (g2 _ (by decide) (by decide)) wr2
  obtain ⟨s3, e3, m3, rd3, wr3, sp3, g3⟩ := copyInWord_ok (w := 2) (by decide) hj s2 h2
    (by rw [g2 _ (by decide) (by decide), g2 _ (by decide) (by decide), g1 _ (by decide) (by decide),
      g1 _ (by decide) (by decide), hrb])
    (by rw [rd2, wr2, rd1, wr1, g2 _ (by decide) (by decide), g1 _ (by decide) (by decide)];
        exact hr 2 (by decide))
  obtain h3 : Room s3 := room_congr h2 (g3 _ (by decide) (by decide)) wr3
  obtain ⟨s4, e4, m4, rd4, wr4, sp4, g4⟩ := copyInWord_ok (w := 3) (by decide) hj s3 h3
    (by rw [g3 _ (by decide) (by decide), g3 _ (by decide) (by decide), g2 _ (by decide) (by decide),
      g2 _ (by decide) (by decide), g1 _ (by decide) (by decide), g1 _ (by decide) (by decide), hrb])
    (by rw [rd3, wr3, rd2, wr2, rd1, wr1, g3 _ (by decide) (by decide), g2 _ (by decide) (by decide),
        g1 _ (by decide) (by decide)];
        exact hr 3 (by decide))
  let s5 := s4.write .t3 (s4.gpr .t3 + BitVec.ofInt 64 16)
  let s6 := s5.write .t4 (s5.gpr .t4 + BitVec.ofInt 64 4)
  let s7 := s6.write .t2 (s6.gpr .t2 - 1)
  obtain hrun : runBlock isa copyInBody s = some s7 := by
    rw [copyInBody_eq]
    rw [runBlock_append, e1, Option.bind_some, runBlock_append, e2, Option.bind_some, runBlock_append, e3,
      Option.bind_some, runBlock_append, e4, Option.bind_some, runBlock_cons,
      exec_addi (show imm12 16 by decide), runStep_some, runBlock_cons,
      exec_addi (show imm12 4 by decide), runStep_some, runBlock_cons,
      exec_dec _ .t2, runStep_some, runBlock_nil]
  -- Registers through the words.
  obtain keep4 : ∀ r, r ≠ .t0 → r ≠ .t1 → s4.gpr r = s.gpr r := fun r a b => by
    rw [g4 _ a b, g3 _ a b, g2 _ a b, g1 _ a b]
  obtain sbs : ∀ t ∈ [s1, s2, s3, s4], t.gpr sb = s.gpr sb := by
    intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact g1 _ (by decide) (by decide)
    · rw [g2 _ (by decide) (by decide), g1 _ (by decide) (by decide)]
    · rw [g3 _ (by decide) (by decide), g2 _ (by decide) (by decide), g1 _ (by decide) (by decide)]
    · exact keep4 _ (by decide) (by decide)
  obtain t3s : ∀ t ∈ [s1, s2, s3, s4], t.gpr .t3 = s.gpr .t3 := by
    intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact g1 _ (by decide) (by decide)
    · rw [g2 _ (by decide) (by decide), g1 _ (by decide) (by decide)]
    · rw [g3 _ (by decide) (by decide), g2 _ (by decide) (by decide), g1 _ (by decide) (by decide)]
    · exact keep4 _ (by decide) (by decide)
  obtain lA : ∀ t ∈ [s1, s2, s3, s4], ∀ k, laneA t k j = laneA s k j := by
    intro t ht k; simp only [laneA, sbs t ht]
  -- Memory.
  let v (w : Nat) := byteRev32 (s.mem.readW (s.gpr .t3 + BitVec.ofNat 64 (4 * w)) 32)
  obtain f1 : Frame [arraysR s] s.mem s1.mem := by
    rw [m1]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (lane_inArrays (mem_arrA_of (by decide)) hj s)
  obtain f2 : Frame [arraysR s] s.mem s2.mem := by
    rw [m2, lA s1 (by simp)]; exact f1.writeW List.mem_cons_self _ (lane_inArrays (mem_arrA_of (by decide)) hj s)
  obtain f3 : Frame [arraysR s] s.mem s3.mem := by
    rw [m3, lA s2 (by simp)]; exact f2.writeW List.mem_cons_self _ (lane_inArrays (mem_arrA_of (by decide)) hj s)
  obtain mm : s4.mem = (((s.mem.writeW (laneA s (arrSlot 0) j) (v 0)).writeW (laneA s (arrSlot 1) j) (v 1)).writeW
      (laneA s (arrSlot 2) j) (v 2)).writeW (laneA s (arrSlot 3) j) (v 3) := by
    rw [m4, lA s3 (by simp), t3s s3 (by simp), hkeep s3 f3 3 (by decide), m3, lA s2 (by simp),
      t3s s2 (by simp), hkeep s2 f2 2 (by decide), m2, lA s1 (by simp), t3s s1 (by simp),
      hkeep s1 f1 1 (by decide), m1]
  refine ⟨s7, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · simp only [s7, s6, s5, mem_write]
    rw [mm]
    simp only [laneWrites, inSpec, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.foldl_cons, List.foldl_nil, List.singleton_append, List.cons_append,
      List.map_cons]
    rfl
  · simp [s7, s6, s5, gpr_write, keep4 .t3 (by decide) (by decide)] <;> rfl
  · simp [s7, s6, s5, gpr_write, keep4 .t4 (by decide) (by decide)] <;> rfl
  · simp [s7, s6, s5, gpr_write, keep4 .t2 (by decide) (by decide)]
  · simp only [s7, s6, s5, rd_write, rd4, rd3, rd2, rd1]
  · simp only [s7, s6, s5, wr_write, wr4, wr3, wr2, wr1]
  · simp only [s7, s6, s5, sp_write, sp4, sp3, sp2, sp1]
  · obtain ⟨h0, h1, h2, h3, h4⟩ := hr
    simp only [s7, s6, s5, gpr_write, h3, h2, h4, ↓reduceIte]
    exact keep4 r h0 h1

theorem cnt_ne_zero {k : Nat} (h1 : 2 ≤ k) (h2 : k ≤ 16) :
    (BitVec.ofNat 64 k - 1 != 0) = true := by
  simp only [bne_iff_ne, ne_eq]
  intro h0
  have := congrArg BitVec.toNat h0
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_arith)] at this
  omega_arith

theorem cnt_sub1 {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 16) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) :=
  a4_sub k h1 h2

theorem copyIn_loop {s₀ : State} {p : Addr} {m : Nat} (hpre : CopyPre s₀ p m) :
    ∀ k s, CopyInInv s₀ p m (m - k) s → 1 ≤ k → k ≤ m →
      WP isa (.loop (.block copyInBody) (.nonzero .t2)) s (fun s' => CopyInInv s₀ p m m s') := by
  intro k s hs hk1 hkm
  refine WP.loop (M := isa) (fun k t => CopyInInv s₀ p m (m - k) t ∧ 1 ≤ k ∧ k ≤ m) ?_ k s ⟨hs, hk1, hkm⟩
  intro k t ⟨inv, hk1, hkm⟩
  have hm16 := hpre.le.2
  let j := m - k
  obtain hj : j < 16 := by omega_arith
  obtain hsb : t.gpr sb = s₀.gpr sb := inv.regs _ sb_copyRegs
  obtain hroom : Room t := room_congr hpre.room hsb inv.wr
  obtain hrb : t.gpr .t4 = t.gpr sb + BitVec.ofNat 64 (4 * j) := by rw [inv.t4, hsb]
  obtain hdata : ∀ w < 4, t.gpr .t3 + BitVec.ofNat 64 (4 * w) = p + BitVec.ofNat 64 (16 * j + 4 * w) := by
    intro w _; rw [inv.t3, Offset.add_add]
  obtain hr : ∀ w < 4, InRegions (t.rd ++ t.wr) (t.gpr .t3 + BitVec.ofNat 64 (4 * w)) 4 := by
    intro w hw; rw [hdata w hw, inv.rd, inv.wr]; exact hpre.read j (by omega_arith) w hw
  obtain harr : arraysR t = arraysR s₀ := by simp [arraysR, hsb]
  obtain hsep : ∀ w < 4, Region.Disjoint ⟨t.gpr .t3 + BitVec.ofNat 64 (4 * w), 4⟩ (arraysR t) := by
    intro w hw
    rw [hdata w hw, harr]
    exact hpre.sep.sub_left (Offset.sub_base p (by omega_arith))
  obtain ⟨t', ht', hmem, hr10, hrbx, hrcx, hrd, hwr, hsp, hregs⟩ := copyInBody_ok hj t hroom hrb hr hsep
  refine WP.of_runBlock ⟨t', ht', ?_⟩
  obtain hsb' : t'.gpr sb = t.gpr sb := hregs _ sb_copyRegs
  obtain inv' : CopyInInv s₀ p m (j + 1) t' := by
    refine ⟨by omega_arith, ?_, ?_, ?_, fun w hw b hb => ?_, ?_, fun r hr => ?_, by rw [hsp, inv.sp],
      by rw [hrd, inv.rd], by rw [hwr, inv.wr]⟩
    · rw [hr10, inv.t3, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add]; congr 2
    · rw [hrbx, inv.t4, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    · rw [hrcx, inv.t2, show m - (m - k) = k by omega_arith, cnt_sub1 hk1 (by omega_arith)]
      exact congrArg (BitVec.ofNat 64) (by omega_arith)
    · have hl : lv t' (arrSlot w) b = (laneWrites t (inSpec t.mem (t.gpr .t3)) j).readW (laneA t (arrSlot w) b) 32 := by
        rw [← hmem]; simp only [lv, laneA, hsb']
      rw [hl, lv_laneWrites (inSpec_dests _ _) t (mem_arrA_of hw) (by omega_arith) hj]
      by_cases hbj : b = j
      · subst hbj
        simp only [ite_true, newVal, inSpec, List.range_succ, List.range_zero, List.nil_append,
          List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.singleton_append,
          List.cons_append]
        rw [bw, ← hdata w hw]
        obtain hkeep : t.mem.readW (t.gpr .t3 + BitVec.ofNat 64 (4 * w)) 32 =
            s₀.mem.readW (t.gpr .t3 + BitVec.ofNat 64 (4 * w)) 32 := by
          refine inv.frame.readW (Region.contains_self _ _) ?_ (by decide)
          intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'; rw [← harr]; exact hsep w hw
        rw [← hkeep]
        rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> simp [arrSlot]
      · rw [ite_eq_right hbj]; exact inv.lanes w hw b (by omega_arith)
    · refine inv.frame.trans ?_
      have := laneWrites_frame (inSpec_dests t.mem (t.gpr .t3)) t (b := j) hj
      rw [← hmem, harr] at this; exact this
    · rw [hregs r hr]; exact inv.regs r hr
  by_cases hk : k = 1
  · subst hk
    left
    obtain hjm : j + 1 = m := by omega_arith
    refine ⟨?_, hjm ▸ inv'⟩
    rw [RISCV64.Steps.eval_nonzero, hrcx, inv.t2, show m - (m - 1) = 1 by omega_arith]; rfl
  · right
    refine ⟨?_, k - 1, by omega_arith, ⟨by simpa [show j + 1 = m - (k - 1) by omega_arith] using inv', by omega_arith, by omega_arith⟩⟩
    rw [RISCV64.Steps.eval_nonzero, hrcx, inv.t2, show m - (m - k) = k by omega_arith,
      cnt_ne_zero (by omega_arith) (by omega_arith)]

/-! ## Copying out -/

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
    ((((m.writeW (a + BitVec.ofNat 64 0) (byteRev32 (y 0))).writeW (a + BitVec.ofNat 64 4) (byteRev32 (y 1))).writeW
      (a + BitVec.ofNat 64 8) (byteRev32 (y 2))).writeW (a + BitVec.ofNat 64 12) (byteRev32 (y 3)))
      (a + BitVec.ofNat 64 i) = (y (i / 4) >>> (8 * (3 - i % 4))).setWidth 8 := by
  rcases (show i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3 by omega_arith) with h | h | h | h
  · rw [writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW32_at _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      byteRev32_byte _ (by omega_arith), h]
    congr 3; omega_arith
  · rw [writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      writeW32_at _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), byteRev32_byte _ (by omega_arith), h]
    congr 3; omega_arith
  · rw [writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW32_at _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      byteRev32_byte _ (by omega_arith), h]
    congr 3; omega_arith
  · rw [writeW32_at _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), byteRev32_byte _ (by omega_arith), h]
    congr 3; omega_arith

/-- The copy of word `w` of a block out: the lane loaded, and stored
big-endian a byte at a time. -/
def outWord (w : Nat) : List Instr :=
  .load .w .t0 .t4 (8 * arrSlot ((w + 2) % 4)) :: Impl.Words.RISCV64.storeBE 4 .t0 .t1 .t3 (4 * w)

theorem copyOutBody_eq : copyOutBody = outWord 0 ++ (outWord 1 ++ (outWord 2 ++ (outWord 3 ++
    ([.addi .t3 .t3 16, .addi .t4 .t4 4, .addi .t2 .t2 (-1)] : List Instr)))) := by
  simp only [copyOutBody, outWord, List.range_succ, List.range_zero, List.nil_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc, List.flatMap_append, List.cons_append,
    List.singleton_append]
  rfl

theorem copyOutWord_ok {w j : Nat} (hw : w < 4) (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .t4 = s.gpr sb + BitVec.ofNat 64 (4 * j))
    (hwr : InRegions s.wr (s.gpr .t3 + BitVec.ofNat 64 (4 * w)) 4) :
    ∃ s', runBlock isa (outWord w) s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .t3 + BitVec.ofNat 64 (4 * w))
        (byteRev32 (lv s (arrSlot ((w + 2) % 4)) j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) := by
  obtain hw' : (w + 2) % 4 < 4 := Nat.mod_lt _ (by decide)
  obtain hL : arrSlot ((w + 2) % 4) ∈ arrays := mem_arrA_of hw'
  obtain hla : s.gpr .t4 + BitVec.ofNat 64 (8 * arrSlot ((w + 2) % 4)) = laneA s (arrSlot ((w + 2) % 4)) j := by
    rw [hrb, arr_off _ _]; rfl
  obtain ⟨s1, hs1⟩ : ∃ t, t = s.write .t0 ((lv s (arrSlot ((w + 2) % 4)) j).setWidth 64) := ⟨_, rfl⟩
  obtain e1 : exec (.load .w .t0 .t4 (8 * arrSlot ((w + 2) % 4))) s = some s1 := by
    rw [exec_load_w (arr_ok hw').2 (by rw [hla]; exact lane_al h hL hj) (by rw [hla]; exact lane_rw h hL hj),
      hla, hs1]; rfl
  obtain h3 : s1.gpr .t3 = s.gpr .t3 := by rw [hs1]; exact gpr_write_of_ne _ _ (by decide)
  obtain v1 : s1.gpr .t0 = (lv s (arrSlot ((w + 2) % 4)) j).setWidth 64 := by rw [hs1]; exact gpr_write_self _ _ _
  obtain m1 : s1.mem = s.mem := by rw [hs1]; rfl
  obtain rd1 : s1.rd = s.rd := by rw [hs1]; rfl
  obtain wr1 : s1.wr = s.wr := by rw [hs1]; rfl
  obtain sp1 : s1.sp = s.sp := by rw [hs1]; rfl
  obtain g1 : ∀ r, r ≠ .t0 → s1.gpr r = s.gpr r := fun r a => by rw [hs1]; exact gpr_write_of_ne _ _ a
  obtain hbytes : ∀ k < 4, InRegions s1.wr (s1.gpr .t3 + BitVec.ofNat 64 (4 * w + k)) 1 := by
    intro k hk
    rw [h3, wr1]
    exact ByteLoad.in_byte hwr hk
  obtain c1 : Reg.t1 ≠ Reg.t0 := by decide
  obtain c2 : Reg.t1 ≠ Reg.t3 := by decide
  obtain c3 : 4 * w + 4 ≤ 2048 := by omega_arith
  obtain hwp := ByteLoad.storeBE_ok (s := s1) (v := .t0) (tmp := .t1) (n := .t3)
    (off := 4 * w) (w := 4) c1 c2 (Nat.zero_lt_succ 3) (Nat.le_of_ble_eq_true rfl) c3 hbytes
  obtain ⟨s2, e2, h2⟩ := run_of_wp hwp
  refine ⟨s2, by rw [outWord, runBlock_cons, e1, runStep_some]; exact e2, ?_, by rw [h2]; exact rd1,
    by rw [h2]; exact wr1, by rw [h2]; exact sp1, fun r a b => ?_⟩
  · rw [h2, mem_write]
    show writeBytes s1.mem _ _ = _
    rw [h3, v1, writeBytes_beBytes, m1]
  · rw [h2, gpr_write_of_ne _ _ b]
    exact g1 r a

/-- The four words `y` of a block, byte-swapped, from `q`. -/
def outWrites (m : Mem) (q : Addr) (y : Nat → BitVec 32) : Mem :=
  (((m.writeW (q + BitVec.ofNat 64 0) (byteRev32 (y 0))).writeW (q + BitVec.ofNat 64 4) (byteRev32 (y 1))).writeW
    (q + BitVec.ofNat 64 8) (byteRev32 (y 2))).writeW (q + BitVec.ofNat 64 12) (byteRev32 (y 3))

theorem copyOutBody_ok {j : Nat} (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .t4 = s.gpr sb + BitVec.ofNat 64 (4 * j))
    (hwr : ∀ w < 4, InRegions s.wr (s.gpr .t3 + BitVec.ofNat 64 (4 * w)) 4)
    (hsep : Region.Disjoint ⟨s.gpr .t3, 16⟩ (arraysR s)) :
    ∃ s', runBlock isa copyOutBody s = some s' ∧
      s'.mem = outWrites s.mem (s.gpr .t3) (fun w => lv s (arrSlot ((w + 2) % 4)) j) ∧
      s'.gpr .t3 = s.gpr .t3 + 16 ∧ s'.gpr .t4 = s.gpr .t4 + 4 ∧
      s'.gpr .t2 = s.gpr .t2 - 1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, CopyRegs r → s'.gpr r = s.gpr r) := by
  -- The lanes keep their values while the block is written.
  obtain hkeep : ∀ (t : State), t.gpr sb = s.gpr sb → Frame [⟨s.gpr .t3, 16⟩] s.mem t.mem → ∀ w < 4,
      lv t (arrSlot ((w + 2) % 4)) j = lv s (arrSlot ((w + 2) % 4)) j := by
    intro t ht hf w hw
    simp only [lv, laneA, ht]
    refine hf.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'
    exact fun x h1 h2 => hsep x h2 (lane_inArrays (mem_arrA_of (Nat.mod_lt _ (by decide))) hj s
      |>.byte h1)
  obtain ⟨s1, e1, m1, rd1, wr1, sp1, g1⟩ := copyOutWord_ok (w := 0) (by decide) hj s h hrb (hwr 0 (by decide))
  obtain sb_1 : s1.gpr sb = s.gpr sb := g1 _ (by decide) (by decide)
  obtain h1 : Room s1 := room_congr h sb_1 wr1
  obtain hin : ∀ w < 4, (⟨s.gpr .t3, 16⟩ : Region).Contains (s.gpr .t3 + BitVec.ofNat 64 (4 * w)) (32 / 8) :=
    fun w hw => Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain f1 : Frame [⟨s.gpr .t3, 16⟩] s.mem s1.mem := by
    rw [m1]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (hin 0 (by decide))
  obtain ⟨s2, e2, m2, rd2, wr2, sp2, g2⟩ := copyOutWord_ok (w := 1) (by decide) hj s1 h1
    (by rw [g1 _ (by decide) (by decide), sb_1, hrb])
    (by rw [wr1, g1 _ (by decide) (by decide)]; exact hwr 1 (by decide))
  obtain sb_2 : s2.gpr sb = s.gpr sb := by rw [g2 _ (by decide) (by decide), sb_1]
  obtain h2 : Room s2 := room_congr h sb_2 (by rw [wr2, wr1])
  obtain t3_1 : s1.gpr .t3 = s.gpr .t3 := g1 _ (by decide) (by decide)
  obtain f2 : Frame [⟨s.gpr .t3, 16⟩] s.mem s2.mem := by
    rw [m2, t3_1]; exact f1.writeW List.mem_cons_self _ (hin 1 (by decide))
  obtain ⟨s3, e3, m3, rd3, wr3, sp3, g3⟩ := copyOutWord_ok (w := 2) (by decide) hj s2 h2
    (by rw [g2 _ (by decide) (by decide), g1 _ (by decide) (by decide), sb_2, hrb])
    (by rw [wr2, wr1, g2 _ (by decide) (by decide), t3_1]; exact hwr 2 (by decide))
  obtain sb_3 : s3.gpr sb = s.gpr sb := by rw [g3 _ (by decide) (by decide), sb_2]
  obtain h3 : Room s3 := room_congr h sb_3 (by rw [wr3, wr2, wr1])
  obtain t3_2 : s2.gpr .t3 = s.gpr .t3 := by rw [g2 _ (by decide) (by decide), t3_1]
  obtain f3 : Frame [⟨s.gpr .t3, 16⟩] s.mem s3.mem := by
    rw [m3, t3_2]; exact f2.writeW List.mem_cons_self _ (hin 2 (by decide))
  obtain ⟨s4, e4, m4, rd4, wr4, sp4, g4⟩ := copyOutWord_ok (w := 3) (by decide) hj s3 h3
    (by rw [g3 _ (by decide) (by decide), g2 _ (by decide) (by decide), g1 _ (by decide) (by decide),
      sb_3, hrb])
    (by rw [wr3, wr2, wr1, g3 _ (by decide) (by decide), t3_2]; exact hwr 3 (by decide))
  obtain t3_3 : s3.gpr .t3 = s.gpr .t3 := by rw [g3 _ (by decide) (by decide), t3_2]
  let s5 := s4.write .t3 (s4.gpr .t3 + BitVec.ofInt 64 16)
  let s6 := s5.write .t4 (s5.gpr .t4 + BitVec.ofInt 64 4)
  let s7 := s6.write .t2 (s6.gpr .t2 - 1)
  obtain hrun : runBlock isa copyOutBody s = some s7 := by
    rw [copyOutBody_eq, runBlock_append, e1, Option.bind_some, runBlock_append, e2, Option.bind_some,
      runBlock_append, e3, Option.bind_some, runBlock_append, e4, Option.bind_some, runBlock_cons,
      exec_addi (show imm12 16 by decide), runStep_some, runBlock_cons,
      exec_addi (show imm12 4 by decide), runStep_some,
      runBlock_cons, exec_dec _ .t2, runStep_some, runBlock_nil]
  obtain keep4 : ∀ r, r ≠ .t0 → r ≠ .t1 → s4.gpr r = s.gpr r := fun r a b => by
    rw [g4 _ a b, g3 _ a b, g2 _ a b, g1 _ a b]
  refine ⟨s7, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · simp only [s7, s6, s5, mem_write]
    rw [m4, t3_3, hkeep s3 sb_3 f3 3 (by decide), m3, t3_2,
      hkeep s2 sb_2 f2 2 (by decide), m2, t3_1, hkeep s1 sb_1 f1 1 (by decide), m1, outWrites]
  · simp [s7, s6, s5, gpr_write, keep4 .t3 (by decide) (by decide)] <;> rfl
  · simp [s7, s6, s5, gpr_write, keep4 .t4 (by decide) (by decide)] <;> rfl
  · simp [s7, s6, s5, gpr_write, keep4 .t2 (by decide) (by decide)]
  · simp only [s7, s6, s5, rd_write, rd4, rd3, rd2, rd1]
  · simp only [s7, s6, s5, wr_write, wr4, wr3, wr2, wr1]
  · simp only [s7, s6, s5, sp_write, sp4, sp3, sp2, sp1]
  · obtain ⟨h0, h1, h2, h3, h4⟩ := hr
    simp only [s7, s6, s5, gpr_write, h3, h2, h4, ↓reduceIte]
    exact keep4 r h0 h1

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
  t3 : s.gpr .t3 = p + BitVec.ofNat 64 (16 * j)
  t4 : s.gpr .t4 = s₀.gpr sb + BitVec.ofNat 64 (4 * j)
  t2 : s.gpr .t2 = BitVec.ofNat 64 (m - j)
  done : ∀ b < j, ∀ i < 16, s.mem (p + BitVec.ofNat 64 (16 * b + i)) = outByte s₀ b i
  frame : Frame [⟨p, 16 * m⟩] s₀.mem s.mem
  regs : ∀ r, CopyRegs r → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyOut_loop {s₀ : State} {p : Addr} {m : Nat} (hpre : CopyOutPre s₀ p m) :
    ∀ k s, CopyOutInv s₀ p m (m - k) s → 1 ≤ k → k ≤ m →
      WP isa (.loop (.block copyOutBody) (.nonzero .t2)) s (fun s' => CopyOutInv s₀ p m m s') := by
  intro k s hs hk1 hkm
  refine WP.loop (M := isa) (fun k t => CopyOutInv s₀ p m (m - k) t ∧ 1 ≤ k ∧ k ≤ m) ?_ k s ⟨hs, hk1, hkm⟩
  intro k t ⟨inv, hk1, hkm⟩
  have hm16 := hpre.le.2
  let j := m - k
  obtain hj : j < 16 := by omega_arith
  obtain hsb : t.gpr sb = s₀.gpr sb := inv.regs _ sb_copyRegs
  obtain hroom : Room t := room_congr hpre.room hsb inv.wr
  obtain hrb : t.gpr .t4 = t.gpr sb + BitVec.ofNat 64 (4 * j) := by rw [inv.t4, hsb]
  obtain hwr : ∀ w < 4, InRegions t.wr (t.gpr .t3 + BitVec.ofNat 64 (4 * w)) 4 := by
    intro w hw; rw [inv.t3, Offset.add_add, inv.wr]; exact hpre.write j (by omega_arith) w hw
  obtain harr : arraysR t = arraysR s₀ := by simp [arraysR, hsb]
  obtain hsep : Region.Disjoint ⟨t.gpr .t3, 16⟩ (arraysR t) := by
    rw [inv.t3, harr]; exact hpre.sep.sub_left (Offset.sub_base p (by omega_arith))
  obtain ⟨t', ht', hmem, hr10, hrbx, hrcx, hrd, hwr', hsp, hregs⟩ := copyOutBody_ok hj t hroom hrb hwr hsep
  refine WP.of_runBlock ⟨t', ht', ?_⟩
  -- The lanes, as they were.
  obtain hlanes : ∀ w < 4, lv t (arrSlot ((w + 2) % 4)) j = lv s₀ (arrSlot ((w + 2) % 4)) j := by
    intro w hw
    simp only [lv, laneA, hsb]
    refine inv.frame.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'
    exact fun x h1 h2 => hpre.sep x h2 (lane_inArrays (mem_arrA_of (Nat.mod_lt _ (by decide))) hj s₀ |>.byte h1)
  obtain inv' : CopyOutInv s₀ p m (j + 1) t' := by
    refine ⟨by omega_arith, ?_, ?_, ?_, fun b hb i hi => ?_, ?_, fun r hr => ?_, by rw [hsp, inv.sp],
      by rw [hrd, inv.rd], by rw [hwr', inv.wr]⟩
    · rw [hr10, inv.t3, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add]; congr 2
    · rw [hrbx, inv.t4, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    · rw [hrcx, inv.t2, show m - (m - k) = k by omega_arith, cnt_sub1 hk1 (by omega_arith)]
      exact congrArg (BitVec.ofNat 64) (by omega_arith)
    · rw [hmem]
      by_cases hbj : b = j
      · subst hbj
        rw [show p + BitVec.ofNat 64 (16 * (m - k) + i) = t.gpr .t3 + BitVec.ofNat 64 i by
          rw [inv.t3, Offset.add_add]]
        unfold outWrites
        rw [block_writes _ _ (fun w => lv t (arrSlot ((w + 2) % 4)) j) hi, outByte, hlanes _ (by omega_arith)]
      · rw [outWrites_off _ _ _ ?_]
        · exact inv.done b (by omega_arith) i hi
        · rw [inv.t3, Offset.sub_toNat' p (by omega_arith) (by omega_arith)]
          split <;> omega_arith
    · rw [hmem, inv.t3]
      exact outWrites_frame inv.frame (by omega_arith) (by omega_arith) _
    · rw [hregs r hr]; exact inv.regs r hr
  by_cases hk : k = 1
  · subst hk
    left
    obtain hjm : j + 1 = m := by omega_arith
    refine ⟨?_, hjm ▸ inv'⟩
    rw [RISCV64.Steps.eval_nonzero, hrcx, inv.t2, show m - (m - 1) = 1 by omega_arith]; rfl
  · right
    refine ⟨?_, k - 1, by omega_arith, ⟨by simpa [show j + 1 = m - (k - 1) by omega_arith] using inv', by omega_arith, by omega_arith⟩⟩
    rw [RISCV64.Steps.eval_nonzero, hrcx, inv.t2, show m - (m - k) = k by omega_arith,
      cnt_ne_zero (by omega_arith) (by omega_arith)]

end VG.Proof.Seed.RISCV64

end

end


/-!
# A batch on RISC-V

As on PPC64LE (`Proof/Seed/PPC64LE/Ecb.lean`): `batch_ok`: a batch
encrypts or decrypts the first `min n 16` blocks at `a1` in place
(`n = a2`), with the keys at `a0` (`keysAt`), and moves `a1` and `a2` past
them. It keeps `g16`'s masks (`Masks`), writing only the working area and
the blocks.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64 VG.Proof.Seed
open VG.Impl.Aes.RISCV64 (sb movR shrI)

/-! ## The batch size -/

theorem exec_movR (s : State) (d n : Reg) : exec (movR d n) s = some (s.write d (s.gpr n)) := by
  rw [movR, exec_addi (by decide)]
  simp

theorem batchSize_ok (s : State) :
    WP isa batchSize s (fun s' => s'.gpr .t2 = BitVec.ofNat 64 (min (s.gpr .a2).toNat 16) ∧
      (∀ r, r ≠ .t2 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp) := by
  let s₁ := s.write .t2 (s.gpr .a2 >>> 4)
  obtain e₁ : runBlock isa [shrI .t2 .a2 4] s = some s₁ := by
    rw [runBlock_cons, shrI, exec_shift_d (by decide), runStep_some, runBlock_nil]
  obtain g₁ : ∀ r, r ≠ .t2 → s₁.gpr r = s.gpr r := fun r hr => gpr_write_of_ne _ _ hr
  obtain hc : isa.eval (.nonzero .t2) s₁ = some (decide (16 ≤ (s.gpr .a2).toNat)) := by
    rw [RISCV64.Steps.eval_nonzero, gpr_write_self]
    congr 1
    by_cases h : 16 ≤ (s.gpr .a2).toNat
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
    obtain e : runBlock isa [.li .t2 16] s₁ = some (s₁.write .t2 (BitVec.ofInt 64 16)) := by
      rw [runBlock_cons, exec_li (by decide), runStep_some, runBlock_nil]
    refine WP.of_runBlock ⟨_, e, ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [gpr_write_self, Nat.min_eq_right (by omega_using [hge])]; rfl
    · rw [gpr_write_of_ne _ _ hr, g₁ r hr]
  · have hlt := of_decide_eq_false hb
    obtain e : runBlock isa [movR .t2 .a2] s₁ = some (s₁.write .t2 (s₁.gpr .a2)) := by
      rw [runBlock_cons, exec_movR, runStep_some, runBlock_nil]
    refine WP.of_runBlock ⟨_, e, ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [gpr_write_self, g₁ _ (by decide), Nat.min_eq_left (by omega_using [hlt]),
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [gpr_write_of_ne _ _ hr, g₁ r hr]

/-! ## Small steps -/

theorem copyStart_ok (s : State) :
    ∃ t, runBlock isa copyStart s = some t ∧ t.gpr .t3 = s.gpr .a1 ∧ t.gpr .t4 = s.gpr sb ∧
      (∀ r, r ≠ .t3 → r ≠ .t4 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp :=
  ⟨(s.write .t3 (s.gpr .a1)).write .t4 ((s.write .t3 (s.gpr .a1)).gpr sb),
    by rw [copyStart, runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_movR, runStep_some,
      runBlock_nil],
    by simp [gpr_write], by simp [gpr_write, show ¬ sb = Reg.t3 by decide],
    fun r h1 h2 => by simp [gpr_write, h1, h2],
    rfl, rfl, rfl, rfl⟩

theorem ofNat_zero_add (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-! ## Blocks and lanes -/

theorem quad_of_lanes {t : State} {m : Mem} {p : Addr} {b : Nat}
    (h : ∀ w < 4, lv t (arrSlot w) b = bw m p b w) :
    quad t b = decodeQ (Spec.Seed.blockAt m (p + BitVec.ofNat 64 (16 * b))) := by
  rw [decodeQ_blockAt]
  simp only [quad, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), bw,
    Offset.add_ofNat_add_ofNat, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul]

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
  masks : Masks s
  pos : 1 ≤ (s.gpr .a2).toNat
  data : ∀ b < min (s.gpr .a2).toNat 16, ∀ w < 4,
    InRegions s.wr (s.gpr .a1 + BitVec.ofNat 64 (16 * b + 4 * w)) 4
  dataSep : Region.Disjoint ⟨s.gpr .a1, 16 * min (s.gpr .a2).toNat 16⟩ (scratchR s)
  keys : KeysOk d s (s.gpr .a0)
  keyData : ∀ j < 16, Region.Disjoint ⟨kp d (s.gpr .a0) j, 8⟩ ⟨s.gpr .a1, 16 * min (s.gpr .a2).toNat 16⟩

structure BatchPost (d : Spec.Seed.Direction) (s s' : State) : Prop where
  done : ∀ b < min (s.gpr .a2).toNat 16,
    Spec.Seed.blockAt s'.mem (s.gpr .a1 + BitVec.ofNat 64 (16 * b)) =
      Spec.Seed.crypt (keysAt d s.mem (s.gpr .a0))
        (Spec.Seed.blockAt s.mem (s.gpr .a1 + BitVec.ofNat 64 (16 * b)))
  a1 : s'.gpr .a1 = s.gpr .a1 + BitVec.ofNat 64 (16 * min (s.gpr .a2).toNat 16)
  a2 : s'.gpr .a2 = s.gpr .a2 - BitVec.ofNat 64 (min (s.gpr .a2).toNat 16)
  regs : ∀ r ∈ [Reg.ra, .a0, .a3, .a5], s'.gpr r = s.gpr r
  masks : Masks s'
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [workR s, ⟨s.gpr .a1, 16 * min (s.gpr .a2).toNat 16⟩] s.mem s'.mem

theorem arraysR_sub_scratch (s : State) : Region.Sub (arraysR s) (scratchR s) := arraysR_sub s

theorem arraysR_sub_work (s : State) : Region.Sub (arraysR s) (workR s) := by
  show Region.Sub ⟨s.gpr sb + BitVec.ofNat 64 (8 * 40), 8 * 64⟩ ⟨s.gpr sb, 8 * 104⟩
  exact Offset.sub_base _ (by omega_using [])

theorem cr_a0 : CopyRegs .a0 := by unfold CopyRegs; decide
theorem cr_a2 : CopyRegs .a2 := by unfold CopyRegs; decide
theorem cr_a3 : CopyRegs .a3 := by unfold CopyRegs; decide

theorem batch_ok (d : Spec.Seed.Direction) {s : State} (h : BatchPre d s) :
    WP isa (batch d) s (BatchPost d s) := by
  let n := (s.gpr .a2).toNat
  let k := min n 16
  let p := s.gpr .a1
  obtain hk1 : 1 ≤ k := by have := h.pos; omega
  obtain hk16 : k ≤ 16 := by omega_using []
  have hpos := h.pos
  -- the copy in
  apply WP.seq
  apply WP.seq
  refine WP.mono (batchSize_ok s) fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  apply WP.seq
  obtain ⟨s₂, e₂, t3₂, t4₂, g₂, m₂, rd₂, wr₂, sp₂⟩ := copyStart_ok s₁
  refine WP.of_runBlock ⟨s₂, e₂, ?_⟩
  obtain G₂ : ∀ r, CopyRegs r → s₂.gpr r = s.gpr r := fun r hr =>
    (g₂ r hr.2.2.2.1 hr.2.2.2.2).trans (g₁ r hr.2.2.1)
  obtain sb₂ : s₂.gpr sb = s.gpr sb := G₂ _ sb_copyRegs
  obtain arr₂ : arraysR s₂ = arraysR s := by simp only [arraysR, sb₂]
  obtain room₂ : Room s₂ := room_congr h.room sb₂ (by rw [wr₂, wr₁])
  obtain pre₂ : CopyPre s₂ p k := by
    refine ⟨room₂, ⟨hk1, hk16⟩, fun b hb w hw => ?_, ?_⟩
    · obtain ⟨r, hr, hc⟩ := h.data b hb w hw
      exact ⟨r, by rw [rd₂, wr₂, rd₁, wr₁]; exact List.mem_append_right _ hr, hc⟩
    · rw [arr₂]; exact h.dataSep.sub_right (arraysR_sub_scratch s)
  obtain inv₂ : CopyInInv s₂ p k (k - k) s₂ := by
    refine ⟨by omega_using [], ?_, ?_, ?_, fun w _ b hb => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl,
      rfl⟩
    · rw [t3₂, Nat.sub_self, Nat.mul_zero, ofNat_zero_add, g₁ _ (by decide)]
    · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add, t4₂, g₂ _ (by decide) (by decide)]
    · rw [Nat.sub_self, Nat.sub_zero, g₂ _ (by decide) (by decide), c₁]
  refine WP.mono (copyIn_loop pre₂ k s₂ inv₂ hk1 (Nat.le_refl _)) fun s₃ i₃ => ?_
  obtain G₃ : ∀ r, CopyRegs r → s₃.gpr r = s.gpr r := fun r hr => (i₃.regs r hr).trans (G₂ r hr)
  obtain sb₃ : s₃.gpr sb = s.gpr sb := G₃ _ sb_copyRegs
  obtain rd₃ : s₃.rd = s.rd := by rw [i₃.rd, rd₂, rd₁]
  obtain wr₃ : s₃.wr = s.wr := by rw [i₃.wr, wr₂, wr₁]
  obtain sp₃ : s₃.sp = s.sp := by rw [i₃.sp, sp₂, sp₁]
  obtain room₃ : Room s₃ := room_congr h.room sb₃ wr₃
  obtain f₃ : Frame [arraysR s] s.mem s₃.mem := by
    have := i₃.frame; rw [arr₂, m₂, m₁] at this; exact this
  obtain masks₃ : Masks s₃ := h.masks.frame sb₃ (G₃ _ cr_a3) (scratch_of_arrays f₃)
  obtain scr₃ : scratchR s₃ = scratchR s := by simp only [scratchR, sb₃]
  obtain keys₃ : KeysOk d s₃ (s₃.gpr .a0) := by
    rw [G₃ .a0 cr_a0]
    intro j hj
    obtain ⟨a, b, c⟩ := h.keys j hj
    exact ⟨by rw [rd₃, wr₃]; exact a, by rw [rd₃, wr₃]; exact b, by rw [scr₃]; exact c⟩
  -- the keys are as on entry
  obtain hkeys : ∀ j < 16, keysAt d s₃.mem (s₃.gpr .a0) j = keysAt d s.mem (s.gpr .a0) j := by
    intro j hj
    rw [G₃ .a0 cr_a0]
    obtain ⟨-, -, hdis⟩ := h.keys j hj
    obtain hd : ∀ r ∈ [arraysR s], Region.Disjoint ⟨kp d (s.gpr .a0) j, 8⟩ r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact hdis.sub_right (arraysR_sub_scratch s)
    simp only [keysAt]
    refine congr (congrArg Prod.mk ?_) ?_
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
  refine WP.mono (rounds_ok d room₃ masks₃ keys₃) fun s₄ ⟨q₄, room₄, masks₄, rd₄, wr₄, sp₄, g₄, f₄⟩ => ?_
  obtain G₄ : ∀ r ∈ [Reg.ra, .a0, .a1, .a2, .a3, .a5], s₄.gpr r = s.gpr r := by
    intro r hr
    rw [g₄ r hr, G₃ r (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> (unfold CopyRegs; decide))]
  obtain sb₄ : s₄.gpr sb = s.gpr sb := G₄ _ (by simp [sb])
  obtain hq₄ : ∀ b < k, quad s₄ b = roundsN (keysAt d s.mem (s.gpr .a0)) 16
      (decodeQ (Spec.Seed.blockAt s.mem (p + BitVec.ofNat 64 (16 * b)))) := by
    intro b hb
    rw [q₄ b (by omega_using [hb]), hq₃ b hb]
    exact roundsN_congr 16 _ hkeys
  -- the copy out
  apply WP.seq
  refine WP.mono (batchSize_ok s₄) fun s₅ ⟨c₅, g₅, m₅, rd₅, wr₅, sp₅⟩ => ?_
  apply WP.seq
  obtain ⟨s₆, e₆, t3₆, t4₆, g₆, m₆, rd₆, wr₆, sp₆⟩ := copyStart_ok s₅
  refine WP.of_runBlock ⟨s₆, e₆, ?_⟩
  obtain G₆ : ∀ r, CopyRegs r → s₆.gpr r = s₄.gpr r := fun r hr =>
    (g₆ r hr.2.2.2.1 hr.2.2.2.2).trans (g₅ r hr.2.2.1)
  obtain sb₆ : s₆.gpr sb = s.gpr sb := (G₆ _ sb_copyRegs).trans sb₄
  obtain a2₄ : s₄.gpr .a2 = s.gpr .a2 := G₄ _ (by simp)
  obtain a1₄ : s₄.gpr .a1 = p := G₄ _ (by simp)
  obtain rd₆ : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  obtain wr₆ : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  obtain sp₆ : s₆.sp = s.sp := by rw [sp₆, sp₅, sp₄, sp₃]
  obtain arr₆ : arraysR s₆ = arraysR s := by simp only [arraysR, sb₆]
  obtain pre₆ : CopyOutPre s₆ p k := by
    refine ⟨room_congr h.room sb₆ wr₆, ⟨hk1, hk16⟩, fun b hb w hw => ?_, ?_⟩
    · rw [wr₆]; exact h.data b hb w hw
    · rw [arr₆]; exact h.dataSep.sub_right (arraysR_sub_scratch s)
  obtain inv₆ : CopyOutInv s₆ p k (k - k) s₆ := by
    refine ⟨by omega_using [], ?_, ?_, ?_, fun b hb => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl,
      rfl⟩
    · rw [t3₆, Nat.sub_self, Nat.mul_zero, ofNat_zero_add, g₅ _ (by decide), a1₄]
    · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add, t4₆, g₆ _ (by decide) (by decide)]
    · rw [Nat.sub_self, Nat.sub_zero, g₆ _ (by decide) (by decide), c₅, a2₄]
  obtain quad₆ : ∀ b, quad s₆ b = quad s₄ b := fun b => by
    simp only [quad, lv, laneA, m₆, m₅, sb₆, sb₄]
  apply WP.seq
  refine WP.mono (copyOut_loop pre₆ k s₆ inv₆ hk1 (Nat.le_refl _)) fun s₇ i₇ => ?_
  apply WP.seq
  refine WP.mono (batchSize_ok s₇) fun s₈ ⟨c₈, g₈, m₈, rd₈, wr₈, sp₈⟩ => ?_
  obtain G₇ : ∀ r, CopyRegs r → s₇.gpr r = s₄.gpr r := fun r hr => (i₇.regs r hr).trans (G₆ r hr)
  obtain a2₇ : s₇.gpr .a2 = s.gpr .a2 := (G₇ _ cr_a2).trans a2₄
  obtain c₈' : s₈.gpr .t2 = BitVec.ofNat 64 k := by rw [c₈, a2₇]
  obtain t3₈ : s₈.gpr .t3 = p + BitVec.ofNat 64 (16 * k) := by rw [g₈ _ (by decide), i₇.t3]
  let s₉ := s₈.write .a1 (s₈.gpr .t3)
  let s' := s₉.write .a2 (s₉.gpr .a2 - s₉.gpr .t2)
  obtain e' : runBlock isa [movR .a1 .t3, .sub .a2 .a2 .t2] s₈ = some s' := by
    rw [runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_sub, runStep_some, runBlock_nil]
  refine WP.of_runBlock ⟨s', e', ?_⟩
  obtain g' : ∀ r, r ≠ .a1 → r ≠ .a2 → s'.gpr r = s₈.gpr r := fun r a b => by
    simp [s', s₉, gpr_write, a, b]
  obtain a2₉ : s₉.gpr .a2 = s.gpr .a2 := by rw [gpr_write_of_ne _ _ (by decide), g₈ _ (by decide), a2₇]
  obtain t2₉ : s₉.gpr .t2 = BitVec.ofNat 64 k := by rw [gpr_write_of_ne _ _ (by decide), c₈']
  obtain mem' : s'.mem = s₇.mem := by simp only [s', s₉, mem_write, m₈]
  obtain G' : ∀ r ∈ [Reg.ra, .a0, .a3, .a5], s'.gpr r = s.gpr r := by
    intro r hr
    obtain hc : CopyRegs r ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .t2 ∧ r ∈ [Reg.ra, .a0, .a1, .a2, .a3, .a5] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨by unfold CopyRegs; decide, by decide, by decide,
        by decide, by simp⟩
    rw [g' _ hc.2.1 hc.2.2.1, g₈ _ hc.2.2.2.1, G₇ _ hc.1, G₄ _ hc.2.2.2.2]
  obtain sb' : s'.gpr sb = s.gpr sb := G' _ (by simp [sb])
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
        simp only [workR, sb₃]; exact List.mem_cons_self
    obtain c : Frame [workR s, ⟨p, 16 * k⟩] s₄.mem s₇.mem :=
      f₇.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact List.mem_cons_of_mem _ List.mem_cons_self
    exact (a.trans b).trans c
  obtain masks' : Masks s' := by
    refine masks₄.frame' (by rw [sb', sb₄])
      (show s'.gpr .a3 = s₄.gpr .a3 by rw [G' _ (by simp), G₄ _ (by simp)])
      (by rw [mem']; exact f₇) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    obtain hm : masksR s₄ = masksR s := by simp only [masksR, sb₄]
    rw [hm]
    exact (h.dataSep.sub_right (masksR_sub s)).symm
  refine ⟨fun b hb => ?_, ?_, ?_, G', masks', ?_, by simp only [s', s₉, rd_write, rd₈, i₇.rd, rd₆],
    by simp only [s', s₉, wr_write, wr₈, i₇.wr, wr₆], frame⟩
  · rw [crypt_eq, ← hq₄ b hb, ← quad₆ b, mem']
    refine blockAt_of_bytes fun i hi => ?_
    rw [Offset.add_ofNat_add_ofNat, i₇.done b hb i hi, encodeSwapped_get _ _ hi]
  · simp [s', s₉, gpr_write, t3₈]; rfl
  · simp only [s', gpr_write_self, a2₉, t2₉]; rfl
  · simp only [s', s₉, sp_write, sp₈, i₇.sp, sp₆]

end VG.Proof.Seed.RISCV64

end

end

/-! ### `Seed.RISCV64.Setup`, which this module and modules that import it used -/

section

/-!
# The functions' prologue

What ECB and the key expansion share before their work (`prologue_ok`):
the scratch buffer moved to `a5`, the callee-saved registers saved in its
slots 117–128 (`Spill.save_ok` on `savedOffs`), `g16`'s masks built in its
slots 104–116 (`storeKs_ok`), and `a3` pointed to them (`Masks`). The
epilogue restores the registers with `Spill.restore_wp`.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64
open VG.Impl.Aes.RISCV64 (sb t0 t1 movR stS ldS)

/-! ## The callee-saved registers -/

/-- The registers and their byte offsets in the scratch buffer. -/
def savedOffs : List (Reg × Nat) := seedSaved.map fun p => (p.1, 8 * p.2)

theorem seedSave_eq : seedSave = Spill.saveCode sb savedOffs := by
  simp only [seedSave, Spill.saveCode, savedOffs, List.map_map]; rfl

theorem seedRestore_eq : seedRestore = Spill.restoreCode sb savedOffs := by
  simp only [seedRestore, Spill.restoreCode, savedOffs, List.map_map]; rfl

theorem savedOffs_fits : Spill.Fits savedOffs := by decide

theorem savedOffs_restorable : Spill.Restorable sb savedOffs := by decide

theorem savedOffs_ho : ∀ p ∈ savedOffs, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem savedOffs_range : ∀ p ∈ savedOffs, 936 ≤ p.2 ∧ p.2 + 8 ≤ 936 + 96 := by decide

/-- The registers `savedOffs` saves are the preserved ones. -/
theorem savedOffs_regs : savedOffs.map Prod.fst = RISCV64.preserved := by decide

theorem not_saved : ∀ p ∈ savedOffs, p.1 ≠ sb ∧ p.1 ≠ kb ∧ p.1 ≠ .t0 ∧ p.1 ≠ .t1 := by decide

/-! ## The masks -/

/-- The masks' slots and values. -/
def kAbs : List (Nat × BitVec 64) := gKs.map fun p => (kSlot + p.1, p.2)

theorem buildMasks_eq :
    buildMasks = kAbs.flatMap fun p => Impl.Words64.RISCV64.movImm64 t0 t1 p.2 ++ [stS p.1 t0] := by
  simp only [buildMasks, kAbs, List.flatMap_map]

theorem kAbs_nodup : (kAbs.map Prod.fst).Nodup := by decide

theorem kAbs_range : ∀ p ∈ kAbs, kSlot ≤ p.1 ∧ p.1 < kSlot + 13 := by decide

theorem slot_al {B : Addr} (hB : B.toNat % 8 = 0) {k : Nat} (hk : k < 256) :
    (Straight.wordAddr B k).toNat % 8 = 0 :=
  Straight.wordAddr_al hB k (by omega_using [hk])

/-- The slots of `ks`. -/
def ksRegions (b : Addr) (ks : List (Nat × BitVec 64)) : List Region :=
  ks.map fun p => ⟨Straight.wordAddr b p.1, 8⟩

/-- Build the masks `ks` (slots in `[kSlot, kSlot + 13)`) through `t0` and `t1`. -/
theorem storeKs_ok {ks : List (Nat × BitVec 64)} {s : State} (h : Room s)
    (hnd : (ks.map Prod.fst).Nodup) (hk : ∀ p ∈ ks, kSlot ≤ p.1 ∧ p.1 < kSlot + 13) :
    WP isa (.block (ks.flatMap fun p => Impl.Words64.RISCV64.movImm64 t0 t1 p.2 ++ [stS p.1 t0])) s
      fun s' => (∀ k v, (k, v) ∈ ks → s'.mem.readW (Straight.wordAddr (s.gpr sb) k) 64 = v) ∧
        Frame (ksRegions (s.gpr sb) ks) s.mem s'.mem ∧ (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  induction ks generalizing s with
  | nil =>
    exact WP.block_nil ⟨fun _ _ h => absurd h List.not_mem_nil, Frame.refl _ _, fun _ _ _ => rfl,
      rfl, rfl, rfl⟩
  | cons p ks ih =>
    obtain ⟨k, v⟩ := p
    have hk0 := hk _ (List.mem_cons_self ..)
    simp only [List.flatMap_cons] at ih ⊢
    rw [List.append_assoc, WP.block_append_iff (M := isa)]
    refine WP.mono (Words64.movImm64_ok (d := t0) (tmp := t1) (by decide) v)
      fun s₁ ⟨v₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
    have b₁ : s₁.gpr sb = s.gpr sb := g₁ _ (by decide) (by decide)
    have h₁ : Room s₁ := room_congr h b₁ wr₁
    simp only [List.singleton_append, stS]
    have hk' : k < scratchSlots := by unfold kSlot at hk0; unfold scratchSlots; omega
    refine wp_sd (a := Straight.wordAddr (s.gpr sb) k) (by unfold kSlot at hk0; omega) (by rw [b₁])
      (slot_al h.1 (by unfold kSlot at hk0; omega))
      (h₁.wr (by simp only [scratchR, b₁]; exact Straight.slot_contains _ hk' (by unfold scratchSlots; decide)))
      fun s₂ u₂ => ?_
    have b₂ : s₂.gpr sb = s.gpr sb := by rw [u₂.gpr, b₁]
    have h₂ : Room s₂ := room_congr h b₂ (by rw [u₂.wr, wr₁])
    obtain ⟨hnk, hnd'⟩ := List.nodup_cons.mp hnd
    refine WP.mono (ih (s := s₂) h₂ hnd' (fun p hp => hk p (List.mem_cons_of_mem _ hp)))
      fun s₃ ⟨mk₃, f₃, g₃, rd₃, wr₃, sp₃⟩ => ?_
    rw [b₂] at mk₃ f₃
    have m₂ : s₂.mem = s.mem.writeW (Straight.wordAddr (s.gpr sb) k) v := by rw [u₂.mem, m₁, v₁]
    refine ⟨fun j w hj => ?_, ?_, fun r h1 h2 => by rw [g₃ r h1 h2, u₂.gpr, g₁ r h1 h2],
      by rw [rd₃, u₂.rd, rd₁], by rw [wr₃, u₂.wr, wr₁], by rw [sp₃, u₂.sp, sp₁]⟩
    · rcases List.mem_cons.mp hj with e | hj
      · cases e
        rw [f₃.readW (r := ⟨Straight.wordAddr (s.gpr sb) k, 8⟩) (by simp [Region.Contains]) (fun r hr => ?_)
          (by decide), m₂, Mem.readW_writeW_self64]
        simp only [ksRegions, List.mem_map] at hr
        obtain ⟨⟨j', w'⟩, hj', rfl⟩ := hr
        have hne : k ≠ j' := fun e => hnk (by
          simp only [List.mem_map]; exact ⟨(j', w'), hj', e.symm⟩)
        have h1 := hk _ (List.mem_cons_of_mem _ hj')
        simp only at h1
        exact Offset.disjoint (s.gpr sb) (by omega_using [hne]) (by unfold kSlot at h1 hk0; omega)
          (by unfold kSlot at h1 hk0; omega)
      · exact mk₃ j w hj
    · simp only [ksRegions, List.map_cons]
      refine Frame.trans (m₂ ▸ ?_) (f₃.mono fun r hr => List.mem_cons_of_mem _ hr)
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (by simp [Region.Contains])

/-- The masks, built in their slots. -/
theorem buildMasks_ok {s : State} (h : Room s) :
    WP isa (.block buildMasks) s fun s' =>
      (∀ j v, (j, v) ∈ gKs → s'.mem.readW (Straight.wordAddr (s.gpr sb + BitVec.ofNat 64 (8 * kSlot)) j) 64 = v) ∧
        Frame [masksR s] s.mem s'.mem ∧ (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [buildMasks_eq]
  refine WP.mono (storeKs_ok h kAbs_nodup kAbs_range) fun s' ⟨h1, h2, h3, h4, h5, h6⟩ =>
    ⟨fun j v hj => ?_, h2.sub fun r hr => ?_, h3, h4, h5, h6⟩
  · have := h1 (kSlot + j) v (List.mem_map.mpr ⟨(j, v), hj, rfl⟩)
    simp only [Straight.wordAddr] at this ⊢
    rw [Offset.add_add]
    rw [show 8 * (kSlot + j) = 8 * kSlot + 8 * j by omega_using []] at this
    exact this
  · simp only [ksRegions, List.mem_map] at hr
    obtain ⟨⟨k, v⟩, hk, rfl⟩ := hr
    have := kAbs_range _ hk
    refine ⟨masksR s, List.mem_singleton_self _, ?_⟩
    simp only [masksR, Straight.wordAddr] at this ⊢
    exact Offset.sub (s.gpr sb) (d := 8 * k) (n := 8) (e := 8 * kSlot) (k := 8 * 13) (by omega_using [this]) (by omega_using [this])

/-! ## The prologue -/

/-- What the prologue leaves: the scratch buffer in `a5`, the callee-saved
registers saved in it, the masks built and pointed to by `a3`. -/
structure Prologue (r : Reg) (s s' : State) : Prop where
  room : Room s'
  masks : Masks s'
  base : s'.gpr sb = s.gpr r
  regs : ∀ x, x ≠ sb → x ≠ kb → x ≠ t0 → x ≠ t1 → s'.gpr x = s.gpr x
  saved : Spill.Saved (s.gpr r) s.gpr savedOffs s'.mem
  frame : Frame [⟨s.gpr r, 8 * scratchSlots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem prologue_ok {r : Reg} {s : State} (hal : (s.gpr r).toNat % 8 = 0)
    (hscr : InRegions s.wr (s.gpr r) (8 * scratchSlots)) :
    WP isa (.block (prologue r)) s (Prologue r s) := by
  rw [prologue, WP.block_append_iff (M := isa), WP.block_append_iff (M := isa),
    WP.block_append_iff (M := isa)]
  simp only [movR]
  refine wp_mv fun s₁ u₁ => WP.block_nil ?_
  have room₁ : Room s₁ := ⟨by rw [u₁.gpr]; exact hal, by rw [u₁.gpr, u₁.wr]; exact hscr⟩
  rw [seedSave_eq]
  refine Spill.save_ok (rest := []) room₁.1 savedOffs_ho (fun p hp => room₁.wr ?_) (WP.block_nil ?_)
  · have := savedOffs_range p hp
    have h8 : p.2 + 8 ≤ 8 * scratchSlots := by unfold scratchSlots; omega_using [this]
    exact Offset.contains_base _ h8 (by omega_using [this])
  generalize hS : ({ s₁ with mem := Spill.saveMem s₁.mem (s₁.gpr sb) s₁.gpr savedOffs } : State) = s₂
  have g₂ : s₂.gpr = s₁.gpr := by rw [← hS]
  have mm₂ : s₂.mem = Spill.saveMem s₁.mem (s₁.gpr sb) s₁.gpr savedOffs := by rw [← hS]
  have rd₂ : s₂.rd = s₁.rd := by rw [← hS]
  have wr₂ : s₂.wr = s₁.wr := by rw [← hS]
  have sp₂ : s₂.sp = s₁.sp := by rw [← hS]
  have sb₂ : s₂.gpr sb = s.gpr r := by rw [g₂, u₁.gpr]
  have room₂ : Room s₂ := room_congr room₁ (by rw [g₂]) wr₂
  have sv₂ : Spill.Saved (s.gpr r) s.gpr savedOffs s₂.mem := by
    intro p hp
    rw [mm₂, u₁.gpr, Spill.saveMem_saved savedOffs_fits _ _ _ p hp]
    exact u₁.other _ (not_saved p hp).1
  have f₂ : Frame [⟨s.gpr r, 8 * scratchSlots⟩] s.mem s₂.mem := by
    rw [mm₂, u₁.mem, u₁.gpr]
    exact Spill.saveMem_frame_base (fun p hp => by have := savedOffs_range p hp; unfold scratchSlots; omega_using [this])
      (by unfold scratchSlots; omega_using []) _ _ _
  refine WP.mono (buildMasks_ok room₂) fun s₃ ⟨mk₃, fm₃, g₃, rd₃, wr₃, sp₃⟩ => ?_
  refine wp_addi (by unfold kSlot; omega_using []) fun s₄ u₄ => WP.block_nil ?_
  have sb₃ : s₃.gpr sb = s.gpr r := by rw [g₃ _ (by decide) (by decide), sb₂]
  have sb₄ : s₄.gpr sb = s.gpr r := by rw [u₄.other _ (by decide), sb₃]
  have mR : masksR s₂ = ⟨s.gpr r + BitVec.ofNat 64 (8 * kSlot), 8 * 13⟩ := by
    simp only [masksR, sb₂]
  rw [mR] at fm₃
  refine ⟨room_congr room₂ (by rw [sb₄, sb₂]) (by rw [u₄.wr, wr₃]), ⟨?_, fun j v hj => ?_⟩, sb₄,
    fun x h1 h2 h3 h4 => ?_, ?_, ?_, by rw [u₄.rd, rd₃, rd₂, u₁.rd], by rw [u₄.wr, wr₃, wr₂, u₁.wr],
    by rw [u₄.sp, sp₃, sp₂, u₁.sp]⟩
  · rw [u₄.gpr, sb₃, sb₄]
  · rw [u₄.gpr, sb₃, u₄.mem]
    have := mk₃ j v hj
    rw [sb₂] at this
    exact this
  · rw [u₄.other x h2, g₃ x h3 h4, g₂, u₁.other x h1]
  · rw [u₄.mem]
    refine sv₂.frame_in savedOffs_range fm₃ fun r' hr' => ?_
    simp only [List.mem_singleton] at hr'; subst hr'
    exact Offset.disjoint _ (by unfold kSlot; omega_using []) (by omega_using []) (by unfold kSlot; omega_using [])
  · rw [u₄.mem]
    exact f₂.trans (fm₃.sub fun r' hr' => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Offset.sub_base _ (by unfold kSlot scratchSlots; omega_using [])⟩)

end VG.Proof.Seed.RISCV64

end

end

/-!
# The function on RISC-V

As on PPC64LE (`Proof/Seed/PPC64LE/Ecb.lean`): after the prologue
(`Setup.lean`: the scratch buffer in `a5`, the callee-saved registers saved
in it, `g16`'s masks built), the function runs batches of up to 16 blocks
until none are left (`loop_ok`), then restores the registers (`ecb_ok`).
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64 VG.Proof.Seed
open VG.Impl.Aes.RISCV64 (sb movR)

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
  refine congr (congrArg Prod.mk ?_) ?_
  · exact hf.readW (contains_prefix (by decide)) hd (by decide)
  · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
    exact hf.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega_arith) (by omega_arith)) hd (by decide)

/-! ## The loop of batches -/

/-- What the loop may assume throughout, of the state it starts in. -/
structure BatchesEnv (d : Spec.Seed.Direction) (s₀ : State) (n : Nat) : Prop where
  room : Room s₀
  masks : Masks s₀
  dataIn : (⟨s₀.gpr .a1, 16 * n⟩ : Region) ∈ s₀.wr
  dataSep : Region.Disjoint ⟨s₀.gpr .a1, 16 * n⟩ (scratchR s₀)
  fit : 16 * n ≤ 2 ^ 64
  keys : KeysOk d s₀ (s₀.gpr .a0)
  keyData : ∀ j < 16, Region.Disjoint ⟨kp d (s₀.gpr .a0) j, 8⟩ ⟨s₀.gpr .a1, 16 * n⟩

/-- `m` blocks left, the first `n - m` done. -/
structure BatchesInv (d : Spec.Seed.Direction) (s₀ : State) (n m : Nat) (s : State) : Prop where
  pos : 1 ≤ m
  le : m ≤ n
  a2 : s.gpr .a2 = BitVec.ofNat 64 m
  a1 : s.gpr .a1 = s₀.gpr .a1 + BitVec.ofNat 64 (16 * (n - m))
  regs : ∀ r ∈ [Reg.ra, .a0, .a3, .a5], s.gpr r = s₀.gpr r
  masks : Masks s
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n - m, Spec.Seed.blockAt s.mem (s₀.gpr .a1 + BitVec.ofNat 64 (16 * b)) =
    Spec.Seed.crypt (keysAt d s₀.mem (s₀.gpr .a0))
      (Spec.Seed.blockAt s₀.mem (s₀.gpr .a1 + BitVec.ofNat 64 (16 * b)))
  frame : Frame [workR s₀, ⟨s₀.gpr .a1, 16 * (n - m)⟩] s₀.mem s.mem

structure BatchesPost (d : Spec.Seed.Direction) (s₀ : State) (n : Nat) (s : State) : Prop where
  regs : ∀ r ∈ [Reg.ra, .a0, .a3, .a5], s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n, Spec.Seed.blockAt s.mem (s₀.gpr .a1 + BitVec.ofNat 64 (16 * b)) =
    Spec.Seed.crypt (keysAt d s₀.mem (s₀.gpr .a0))
      (Spec.Seed.blockAt s₀.mem (s₀.gpr .a1 + BitVec.ofNat 64 (16 * b)))
  frame : Frame [workR s₀, ⟨s₀.gpr .a1, 16 * n⟩] s₀.mem s.mem

theorem BatchesInv.batchPre {d : Spec.Seed.Direction} {s₀ : State} {n m : Nat} (E : BatchesEnv d s₀ n)
    {s : State} (h : BatchesInv d s₀ n m s) : BatchPre d s := by
  have hp := h.pos
  have hl := h.le
  have hfit := E.fit
  obtain hm : (s.gpr .a2).toNat = m := by rw [h.a2]; exact toNat_ofNat_le h.le E.fit
  obtain r9 : s.gpr sb = s₀.gpr sb := h.regs _ (by simp [sb])
  obtain rdi : s.gpr .a0 = s₀.gpr .a0 := h.regs _ (by simp)
  obtain scr : scratchR s = scratchR s₀ := by simp only [scratchR, r9]
  let D := s₀.gpr .a1
  obtain hsub : Region.Sub ⟨s.gpr .a1, 16 * min (s.gpr .a2).toNat 16⟩ ⟨D, 16 * n⟩ := by
    rw [h.a1, hm]; exact Offset.sub_base _ (by omega_arith)
  refine ⟨room_congr E.room r9 h.wr, h.masks, by omega_arith, fun b hb w hw => ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [h.wr, h.a1, Offset.add_ofNat_add_ofNat]
    rw [hm] at hb
    exact ⟨_, E.dataIn, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [scr]; exact E.dataSep.sub_left hsub
  · rw [rdi]
    intro j hj
    obtain ⟨a, b, c⟩ := E.keys j hj
    exact ⟨by rw [h.rd, h.wr]; exact a, by rw [h.rd, h.wr]; exact b, by rw [scr]; exact c⟩
  · rw [rdi]; exact (E.keyData j hj).sub_right hsub

theorem loop_ok (d : Spec.Seed.Direction) {s₀ : State} {n : Nat} (E : BatchesEnv d s₀ n) (m : Nat) (s : State)
    (hs : BatchesInv d s₀ n m s) : WP isa (.loop (batch d) (.nonzero .a2)) s (BatchesPost d s₀ n) := by
  refine WP.loop (M := isa) (BatchesInv d s₀ n) ?_ m s hs
  intro m s h
  have hp := h.pos
  have hl := h.le
  have hfit := E.fit
  apply WP.mono (batch_ok d (h.batchPre E))
  intro s' q
  obtain hm : (s.gpr .a2).toNat = m := by rw [h.a2]; exact toNat_ofNat_le h.le E.fit
  obtain ⟨qdone, qrsi, qrdx, qregs, qmasks, qsp, qrd, qwr, qframe⟩ := q
  rw [hm] at qdone qrsi qrdx qframe
  generalize hk : min m 16 = k at qdone qrsi qrdx qframe
  obtain hk1 : 1 ≤ k := by omega_arith
  obtain hkm : k ≤ m := by omega_arith
  let D := s₀.gpr .a1
  let S := s₀.gpr .a0
  obtain r9 : s.gpr sb = s₀.gpr sb := h.regs _ (by simp [sb])
  obtain rdi : s.gpr .a0 = S := h.regs _ (by simp)
  obtain workR_eq : workR s = workR s₀ := by simp only [workR, r9]
  rw [h.a1, workR_eq] at qframe
  rw [h.a1] at qrsi qdone
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
  obtain rdx' : s'.gpr .a2 = BitVec.ofNat 64 (m - k) := by
    rw [qrdx, h.a2, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith) hkm]
  obtain zf' : isa.eval (.nonzero .a2) s' = some (BitVec.ofNat 64 (m - k) != 0) := by
    rw [RISCV64.Steps.eval_nonzero, rdx']
  obtain regs' : ∀ r ∈ [Reg.ra, .a0, .a3, .a5], s'.gpr r = s₀.gpr r := fun r hr =>
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
    refine ⟨?_, m - k, by omega_arith, ⟨by omega_arith, by omega_arith, rdx', ?_, regs', qmasks, sp', rd', wr',
      done', frame'⟩⟩
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
  scrAl : (s.gpr .a3).toNat % 8 = 0
  scratch : ∃ n, 8 * scratchSlots ≤ n ∧ (⟨s.gpr .a3, n⟩ : Region) ∈ s.wr
  dataIn : (⟨s.gpr .a1, 16 * (s.gpr .a2).toNat⟩ : Region) ∈ s.wr
  keyIn : (⟨s.gpr .a0, 128⟩ : Region) ∈ s.rd
  keyData : (⟨s.gpr .a0, 128⟩ : Region).Disjoint ⟨s.gpr .a1, 16 * (s.gpr .a2).toNat⟩
  keyBuf : (⟨s.gpr .a0, 128⟩ : Region).Disjoint ⟨s.gpr .a3, 8 * scratchSlots⟩
  dataBuf : (⟨s.gpr .a1, 16 * (s.gpr .a2).toNat⟩ : Region).Disjoint ⟨s.gpr .a3, 8 * scratchSlots⟩
  fit : 16 * (s.gpr .a2).toNat ≤ 2 ^ 64

/-- What the function does: every block of the data becomes its encryption or
decryption, the callee-saved registers and `ra` are as they were, and only
the scratch buffer and the data change. -/
structure EcbPost (d : Spec.Seed.Direction) (s s' : State) : Prop where
  saved : ∀ r ∈ RISCV64.preserved, s'.gpr r = s.gpr r
  ra : s'.gpr .ra = s.gpr .ra
  done : ∀ b < (s.gpr .a2).toNat, Spec.Seed.blockAt s'.mem (s.gpr .a1 + BitVec.ofNat 64 (16 * b)) =
    cipher d (Spec.Seed.scheduleAt s.mem (s.gpr .a0))
      (Spec.Seed.blockAt s.mem (s.gpr .a1 + BitVec.ofNat 64 (16 * b)))
  frame : Frame [⟨s.gpr .a3, 8 * scratchSlots⟩, ⟨s.gpr .a1, 16 * (s.gpr .a2).toNat⟩] s.mem s'.mem

theorem keyStart_lt (d : Spec.Seed.Direction) : keyStart d < 2048 := by cases d <;> decide

theorem ecb_ok (d : Spec.Seed.Direction) {s : State} (h : EcbPre s) : WP isa (ecb d) s (EcbPost d s) := by
  let n := (s.gpr .a2).toNat
  let D := s.gpr .a1
  let S := s.gpr .a0
  let X := s.gpr .a3
  have hn := h.fit
  rw [ecb]
  apply WP.seq
  rw [setup, WP.block_append_iff (M := isa)]
  obtain hscr : InRegions s.wr X (8 * scratchSlots) := by
    obtain ⟨n, hn, hm⟩ := h.scratch
    exact ⟨_, hm, contains_prefix hn⟩
  refine WP.mono (prologue_ok h.scrAl hscr) fun s₁ P => ?_
  refine RISCV64.Steps.wp_addi (keyStart_lt d) fun s₅ u => WP.block_nil ?_
  -- the state after the setup
  obtain G₅ : ∀ r, r ≠ sb → r ≠ kb → r ≠ .t0 → r ≠ .t1 → r ≠ .a0 → s₅.gpr r = s.gpr r :=
    fun r a b c e f => by rw [u.other r f, P.regs r a b c e]
  obtain sb₅ : s₅.gpr sb = X := by rw [u.other _ (by decide), P.base]
  obtain a0₅ : s₅.gpr .a0 = S + BitVec.ofNat 64 (keyStart d) := by
    rw [u.gpr, P.regs _ (by decide) (by decide) (by decide) (by decide)]
  obtain rd₅ : s₅.rd = s.rd := by rw [u.rd, P.rd]
  obtain wr₅ : s₅.wr = s.wr := by rw [u.wr, P.wr]
  obtain sp₅ : s₅.sp = s.sp := by rw [u.sp, P.sp]
  have mem₅ : s₅.mem = s₁.mem := u.mem
  obtain scr₅ : scratchR s₅ = ⟨X, 8 * scratchSlots⟩ := by simp only [scratchR, sb₅]
  obtain room₅ : Room s₅ := room_congr P.room (by rw [u.other _ (by decide)]) u.wr
  obtain masks₅ : Masks s₅ := P.masks.frame (u.other _ (by decide)) (u.other _ (by decide))
    (by rw [mem₅]; exact Frame.refl _ _)
  obtain f₅ : Frame [⟨X, 8 * scratchSlots⟩] s.mem s₅.mem := by rw [mem₅]; exact P.frame
  obtain zf₅ : isa.eval (.zero .a2) s₅ = some (s.gpr .a2 == 0) := by
    rw [RISCV64.Steps.eval_zero, G₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  obtain a1₅ : s₅.gpr .a1 = D := G₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain a2₅ : s₅.gpr .a2 = s.gpr .a2 := G₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ra₅ : s₅.gpr .ra = s.gpr .ra := G₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain saved₅ : Spill.Saved X s.gpr savedOffs s₅.mem := by rw [mem₅]; exact P.saved
  -- the keys, in the schedule
  obtain K₅ : ∀ j < 16, keysAt d s₅.mem (s₅.gpr .a0) j = keysAt d s.mem (S + BitVec.ofNat 64 (keyStart d)) j := by
    intro j hj
    rw [a0₅]
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
  obtain finish : ∀ s₆ : State, BatchesPost d s₅ n s₆ → WP isa (.block seedRestore) s₆ (EcbPost d s) := by
    intro s₆ p
    obtain sb₆ : s₆.gpr sb = X := (p.regs _ (by simp [sb])).trans sb₅
    obtain room₆ : Room s₆ := room_congr room₅ (p.regs _ (by simp [sb])) p.wr
    have pf := p.frame
    rw [a1₅] at pf
    obtain wX : workR s₅ = ⟨X, 8 * 104⟩ := by simp only [workR, sb₅]
    rw [wX] at pf
    obtain sv₆ : Spill.Saved X s.gpr savedOffs s₆.mem := by
      refine saved₅.frame_in savedOffs_range pf fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])
      · exact (h.dataBuf.sub_right (Offset.sub_base _ (by unfold scratchSlots; omega_using []))).symm
    rw [seedRestore_eq]
    refine WP.mono (Spill.restore_wp (B := X) (by rw [← sb₆]; exact room₆.1) sb₆ savedOffs_ho
      savedOffs_restorable (fun q hq => room₆.rw ?_) sv₆) fun s' R => ?_
    · rw [← sb₆]
      have := savedOffs_range q hq
      exact Offset.contains_base _ (by unfold scratchSlots; omega_using [this]) (by omega_using [this])
    obtain frame : Frame [⟨X, 8 * scratchSlots⟩, ⟨D, 16 * n⟩] s.mem s'.mem := by
      rw [R.mem]
      refine (f₅.mono (by simp)).trans (pf.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by unfold scratchSlots; omega_arith)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    refine ⟨fun r hr => ?_, ?_, fun b hb => ?_, frame⟩
    · rw [← savedOffs_regs] at hr
      exact R.gpr_of (Or.inl hr)
    · rw [R.other _ (by decide), p.regs _ (by simp), ra₅]
    · have e := p.done b hb
      rw [a1₅] at e
      rw [R.mem, e, B₅ b hb, crypt_congr K₅, crypt_keysAt]
  apply WP.seq
  apply WP.ite (s.gpr .a2 == 0) zf₅
  · intro hz
    apply WP.block_nil
    obtain hn0 : n = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz)
      simpa [n] using this
    refine finish s₅ ⟨fun _ _ => rfl, rfl, rfl, rfl, fun b hb => by omega_arith, ?_⟩
    rw [hn0]; exact Frame.refl _ _
  · intro hz
    obtain hn1 : 1 ≤ n := by
      have : s.gpr .a2 ≠ 0 := by simpa using hz
      have : (s.gpr .a2).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
      omega_arith
    obtain E : BatchesEnv d s₅ n := by
      refine ⟨room₅, masks₅, by rw [a1₅, wr₅]; exact h.dataIn, by rw [a1₅, scr₅]; exact h.dataBuf, hn,
        fun j hj => ?_, fun j hj => ?_⟩
      · rw [a0₅, kp_start _ _ hj, rd₅, wr₅, scr₅]
        obtain hle := keyOff_le d hj
        refine ⟨⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩, ?_,
          h.keyBuf.sub_left (Offset.sub_base _ hle)⟩
        rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_ofNat_add_ofNat]
        exact ⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
      · rw [a0₅, kp_start _ _ hj, a1₅]
        exact h.keyData.sub_left (Offset.sub_base _ (keyOff_le d hj))
    obtain I : BatchesInv d s₅ n n s₅ := by
      refine ⟨hn1, Nat.le_refl _, ?_, ?_, fun _ _ => rfl, masks₅, rfl, rfl, rfl, fun b hb => by omega_arith,
        by rw [Nat.sub_self]; exact Frame.refl _ _⟩
      · rw [a2₅]; exact BitVec.eq_of_toNat_eq (by simp [n])
      · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add]
    exact WP.mono (loop_ok d E n s₅ I) finish

end VG.Proof.Seed.RISCV64
