module

public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Seed.X86_64.Steps
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Seed.X86_64.Round
public import VerifiedGarbage.Proof.Seed.Rounds

/-! ### `Seed.X86_64.Batch`, which this module and modules that import it used -/

section

/-! ### `Seed.X86_64.Copy`, which this module and modules that import it used -/

section

/-! ### `Seed.X86_64.Rounds`, which this module and modules that import it used -/

section

/-!
# Sixteen rounds on x86-64

`rounds_ok`: `rounds d` does sixteen rounds on every lane, with round
`j + 1`'s key at `rdi + j * step` (`kp`), and moves `rdi` back.
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Proof.Seed

/-- The step of the key pointer. -/
def stepW (d : Spec.Seed.Direction) : BitVec 64 := (BitVec.ofInt 32 (keyStep d)).signExtend 64

/-- Where round `j + 1`'s key is, from `p`. -/
def kp (d : Spec.Seed.Direction) (p : Addr) (j : Nat) : Addr := p + BitVec.ofNat 64 j * stepW d

theorem kp_succ (d : Spec.Seed.Direction) (p : Addr) (j : Nat) : kp d p j + stepW d = kp d p (j + 1) := by
  simp only [kp, BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]

theorem step16 (d : Spec.Seed.Direction) :
    (BitVec.ofInt 32 (16 * keyStep d)).signExtend 64 = BitVec.ofNat 64 16 * stepW d := by
  cases d <;> decide

theorem kp_back (d : Spec.Seed.Direction) (p : Addr) :
    kp d p 16 - (BitVec.ofInt 32 (16 * keyStep d)).signExtend 64 = p := by
  rw [step16, kp, BitVec.add_sub_cancel]

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
  quads : ∀ b < 16, quad s b = roundsN (keysAt d s₀.mem (s₀.gpr .rdi)) (16 - m) (quad s₀ b)
  masks : MasksIn s
  room : Room s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rdi : s.gpr .rdi = kp d (s₀.gpr .rdi) (16 - m)
  r8 : s.gpr .r8 = BitVec.ofNat 64 m
  regs : ∀ r ∈ [Reg.rsi, .rdx, .r9, .rsp], s.gpr r = s₀.gpr r
  frame : Frame [workR s₀] s₀.mem s.mem

theorem contains_prefix {a : Addr} {k n : Nat} (h : k ≤ n) : (⟨a, n⟩ : Region).Contains a k := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

theorem r8_sub (m : Nat) (h : 1 ≤ m) (h' : m ≤ 16) :
    BitVec.ofNat 64 m - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (m - 1) := by
  rw [show (1 : BitVec 32).signExtend 64 = 1 from rfl]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem rounds_ok (d : Spec.Seed.Direction) {s : State} (h : Room s) (hm : MasksIn s)
    (hk : KeysOk d s (s.gpr .rdi)) :
    WP isa (rounds d) s (fun s' =>
      (∀ b < 16, quad s' b = roundsN (keysAt d s.mem (s.gpr .rdi)) 16 (quad s b)) ∧
      MasksIn s' ∧ Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.rdi, .rsi, .rdx, .r9, .rsp], s'.gpr r = s.gpr r) ∧
      Frame [workR s] s.mem s'.mem) := by
  let s1 := s.setReg .r8 ((16 : BitVec 32).signExtend 64)
  have e1 : runBlock isa [.mov .r8 (.imm 16)] s = some s1 := rfl
  have q1 : ∀ b, quad s1 b = quad s b := fun b => by
    simp only [quad, s1, lv_setReg _ _ (show ¬ Reg.r9 = .r8 by decide)]
  refine WP.seq (WP.of_runBlock ⟨s1, e1, ?_⟩)
  refine WP.seq (WP.loop (M := isa) (fun m t => RoundsInv d s m t) ?_ 16 s1 ?_)
  · intro m t inv
    have hi : 16 - m < 16 := by have := inv.le; omega_using [this]
    obtain ⟨hk0, hk1, hdis⟩ := hk (16 - m) hi
    have hk0' : InRegions (t.rd ++ t.wr) (t.gpr .rdi) 4 := by rw [inv.rd, inv.wr, inv.rdi]; exact hk0
    have hk1' : InRegions (t.rd ++ t.wr) (t.gpr .rdi + 4) 4 := by rw [inv.rd, inv.wr, inv.rdi]; exact hk1
    obtain ⟨t', ht', hq, hm', hroom, hrd, hwr, hrdi, hr8, hzf, hrsi, hrdx, hr9, hrsp, hfr⟩ :=
      round_ok d inv.room inv.masks hk0' hk1'
    -- The key, from the original memory.
    have hkey : (t.mem.readW (t.gpr .rdi) 32, t.mem.readW (t.gpr .rdi + 4) 32) =
        keysAt d s.mem (s.gpr .rdi) (16 - m) := by
      simp only [keysAt, inv.rdi]
      have hd : ∀ r ∈ [workR s], Region.Disjoint ⟨kp d (s.gpr .rdi) (16 - m), 8⟩ r := by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact hdis.sub_right (Region.sub_prefix (by unfold scratchSlots; omega_using []))
      refine congr (congrArg Prod.mk ?_) ?_
      · exact inv.frame.readW (contains_prefix (by decide)) hd (by decide)
      · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
        exact inv.frame.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega_using []) (by omega_using []))
          hd (by decide)
    refine WP.of_runBlock ⟨t', ht', ?_⟩
    have hquads : ∀ b < 16, quad t' b = roundsN (keysAt d s.mem (s.gpr .rdi)) (16 - (m - 1)) (quad s b) := by
      intro b hb
      rw [hq b hb, hkey, inv.quads b hb, show 16 - (m - 1) = 16 - m + 1 by have := inv.le; omega_using [this],
        roundsN_succ]
    have hr8' : t'.gpr .r8 = BitVec.ofNat 64 (m - 1) := by
      rw [hr8, inv.r8, r8_sub m inv.le.1 inv.le.2]
    have hregs : ∀ r ∈ [Reg.rsi, .rdx, .r9, .rsp], t'.gpr r = s.gpr r := by
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hrsi]; exact inv.regs _ (by simp)
      · rw [hrdx]; exact inv.regs _ (by simp)
      · rw [hr9]; exact inv.regs _ (by simp)
      · rw [hrsp]; exact inv.regs _ (by simp)
    have hframe : Frame [workR s] s.mem t'.mem := by
      refine inv.frame.trans ?_
      simpa [workR, inv.regs .r9 (by simp)] using hfr
    by_cases hm1 : m = 1
    · subst hm1
      left
      refine ⟨?_, ?_⟩
      · show t'.zf.map (!·) = some false
        rw [hzf, inv.r8, r8_sub 1 (by omega_using []) (by omega_using [])]; rfl
      · obtain ⟨u, eu, hu, -, hreg, hmem, hrd', hwr'⟩ := exec_sub_imm t' .rdi (BitVec.ofInt 32 (16 * keyStep d))
        refine WP.of_runBlock ⟨u, by rw [runBlock_cons, eu, runStep_some, runBlock_nil], ?_⟩
        have hu9 : u.gpr .r9 = t'.gpr .r9 := hreg _ (by decide)
        refine ⟨fun b hb => ?_, ?_, room_congr hroom hu9 hwr', by rw [hrd', hrd, inv.rd],
          by rw [hwr', hwr, inv.wr], fun r hr => ?_, by rw [hmem]; exact hframe⟩
        · have : quad u b = quad t' b := by simp only [quad, lv, laneA, hmem, hu9]
          rw [this, hquads b hb]
        · intro kv hkv
          show u.mem.readW (Straight.wordAddr (u.gpr .r9) kv.1) 64 = kv.2
          rw [hmem, hu9]; exact hm' kv hkv
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
          rcases hr with rfl | hr
          · rw [hu, hrdi, inv.rdi, show (BitVec.ofInt 32 (keyStep d)).signExtend 64 = stepW d from rfl,
              kp_succ, kp_back]
          · rw [hreg _ (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
            exact hregs _ (by simpa using hr)
    · right
      refine ⟨?_, m - 1, by omega_using [hi], ⟨by have := inv.le; omega_using [hm1, this], hquads, hm', hroom, by rw [hrd, inv.rd],
        by rw [hwr, inv.wr], ?_, hr8', hregs, hframe⟩⟩
      · show t'.zf.map (!·) = some true
        rw [hzf, inv.r8, r8_sub m inv.le.1 inv.le.2]
        have : (BitVec.ofNat 64 (m - 1) == 0) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          intro h0
          have hm2 : 2 ≤ m := by have := inv.le; omega_using [hi, hm1]
          have hm16 := inv.le.2
          have := congrArg BitVec.toNat h0
          rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mod_eq_of_lt (by omega_using [hm16])] at this
          omega_using [hi, hrdi, hr8, hrsi, hrdx, hr9, hrsp, hr8', hm1, h0, hm2, hm16, this]
        rw [this]; rfl
      · rw [hrdi, inv.rdi, show (BitVec.ofInt 32 (keyStep d)).signExtend 64 = stepW d from rfl,
          kp_succ, show 16 - m + 1 = 16 - (m - 1) by have := inv.le; omega_using [this]]
  · refine ⟨by omega_using [], fun b _ => by rw [q1]; rfl, fun kv hkv => hm kv hkv, room_congr h rfl rfl,
      rfl, rfl, by simp [s1, kp, gpr_setReg], rfl, fun r hr => ?_, Frame.refl _ _⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Seed.X86_64

end

end

/-!
# Copying blocks into the arrays and back

`copyIn_ok`: the loop of `copyInBody` copies `m` blocks from `p` into lanes
`0 … m - 1` of the arrays, each word byte-swapped (`bw`, a block's big-endian
word). `copyOut_ok`: the loop of `copyOutBody` copies them back, `R` first.
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64

-- The copies share one set of rewrites, not all of which each uses.
set_option linter.unusedSimpArgs false

/-- Word `w` of block `b` from `p`, big-endian. -/
def bw (m : Mem) (p : Addr) (b w : Nat) : BitVec 32 :=
  bswap32 (m.readW (p + BitVec.ofNat 64 (16 * b + 4 * w)) 32)

theorem ea_off (s : State) (r : Reg) (k : Nat) :
    s.ea { base := r, disp := ((k : Nat) : Int) } = s.gpr r + BitVec.ofNat 64 k := by
  show s.gpr r + BitVec.ofInt 64 ((k : Nat) : Int) = _
  rw [BitVec.ofInt_natCast]

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
  r10 : s.gpr .r10 = p + BitVec.ofNat 64 (16 * j)
  rbx : s.gpr .rbx = s₀.gpr .r9 + BitVec.ofNat 64 (4 * j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (m - j)
  lanes : ∀ w < 4, ∀ b < j, lv s (arrSlot w) b = bw s₀.mem p b w
  frame : Frame [arraysR s₀] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The copy of word `w` of a block. -/
def inWord (w : Nat) : List Instr :=
  [.mov32 .rax (.mem { base := .r10, disp := ((4 * w : Nat) : Int) }), .bswap32 .rax,
   .store32 (lane .rbx (arrSlot w) 0) .rax]

theorem copyInBody_eq : copyInBody = inWord 0 ++ (inWord 1 ++ (inWord 2 ++ (inWord 3 ++
    ([.alu .add .r10 (.imm 16), .alu .add .rbx (.imm 4), .alu .sub .rcx (.imm 1)] : List Instr)))) := rfl

/-- One word of a block into its lane. -/
theorem copyInWord_ok {w j : Nat} (hw : w < 4) (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .rbx = s.gpr .r9 + BitVec.ofNat 64 (4 * j))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 4) :
    ∃ s', runBlock isa (inWord w) s = some s' ∧
      s'.mem = s.mem.writeW (laneA s (arrSlot w) j)
        (bswap32 (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  obtain hL : arrSlot w ∈ arrays := mem_arrA_of hw
  unfold inWord
  obtain hea : ∀ t : State, t.gpr .rbx = s.gpr .rbx → t.ea (lane .rbx (arrSlot w) 0) = laneA s (arrSlot w) j := by
    intro t ht
    rw [ea_lane, ht, hrb, laneA, Nat.mul_zero, Nat.add_zero, Offset.add_add, Nat.add_comm]
  rw [runBlock_cons, exec_mov32_mem (by rw [ea_off]; exact hr), ea_off, runStep_some, runBlock_cons]
  rw [show exec (.bswap32 .rax) (s.setReg32 .rax (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32)) =
    some ((s.setReg32 .rax (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32)).setReg32 .rax
      (bswap32 (((s.setReg32 .rax (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32)).gpr .rax).setWidth 32)))
    from rfl, runStep_some, runBlock_cons]
  rw [exec_store32 (by rw [hea _ (by simp [State.setReg32, gpr_setReg])]; exact lane_wr h hL hj),
    hea _ (by simp [State.setReg32, gpr_setReg]), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, fun r hr => ?_⟩
  · simp [State.setReg32, gpr_setReg, mem_setReg, setWidth_setWidth_32]
  · simp [State.setReg32, gpr_setReg, hr]

/-- The copy of one block into lane `j`, as writes of the block's words. -/
def inSpec (m : Mem) (q : Addr) : LaneSpec :=
  (List.range 4).map fun w => (arrSlot w, fun _ => bswap32 (m.readW (q + BitVec.ofNat 64 (4 * w)) 32))

theorem inSpec_dests (m : Mem) (q : Addr) : ∀ kv ∈ inSpec m q, kv.1 ∈ arrays := by
  intro kv hkv
  simp only [inSpec, List.mem_map, List.mem_range] at hkv
  obtain ⟨w, hw, rfl⟩ := hkv
  exact mem_arrA_of hw

theorem copyInBody_ok {j : Nat} (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .rbx = s.gpr .r9 + BitVec.ofNat 64 (4 * j))
    (hr : ∀ w < 4, InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 4)
    (hsep : ∀ w < 4, Region.Disjoint ⟨s.gpr .r10 + BitVec.ofNat 64 (4 * w), 4⟩ (arraysR s)) :
    ∃ s', runBlock isa copyInBody s = some s' ∧
      s'.mem = laneWrites s (inSpec s.mem (s.gpr .r10)) j ∧
      s'.gpr .r10 = s.gpr .r10 + 16 ∧ s'.gpr .rbx = s.gpr .rbx + 4 ∧
      s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .r10 → s'.gpr r = s.gpr r) := by
  -- The block's words keep their values while the lanes are written.
  obtain hkeep : ∀ (t : State), Frame [arraysR s] s.mem t.mem → ∀ w < 4,
      t.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32 =
        s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32 := by
    intro t ht w hw
    refine ht.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'; exact hsep w hw
  obtain ⟨s1, e1, m1, rd1, wr1, g1⟩ := copyInWord_ok (w := 0) (by decide) hj s h hrb (hr 0 (by decide))
  obtain h1 : Room s1 := room_congr h (g1 _ (by decide)) wr1
  obtain ⟨s2, e2, m2, rd2, wr2, g2⟩ := copyInWord_ok (w := 1) (by decide) hj s1 h1
    (by rw [g1 _ (by decide), g1 _ (by decide), hrb]) (by rw [rd1, wr1, g1 _ (by decide)]; exact hr 1 (by decide))
  obtain h2 : Room s2 := room_congr h1 (g2 _ (by decide)) wr2
  obtain ⟨s3, e3, m3, rd3, wr3, g3⟩ := copyInWord_ok (w := 2) (by decide) hj s2 h2
    (by rw [g2 _ (by decide), g2 _ (by decide), g1 _ (by decide), g1 _ (by decide), hrb])
    (by rw [rd2, wr2, rd1, wr1, g2 _ (by decide), g1 _ (by decide)]; exact hr 2 (by decide))
  obtain h3 : Room s3 := room_congr h2 (g3 _ (by decide)) wr3
  obtain ⟨s4, e4, m4, rd4, wr4, g4⟩ := copyInWord_ok (w := 3) (by decide) hj s3 h3
    (by rw [g3 _ (by decide), g3 _ (by decide), g2 _ (by decide), g2 _ (by decide), g1 _ (by decide),
      g1 _ (by decide), hrb])
    (by rw [rd3, wr3, rd2, wr2, rd1, wr1, g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)];
        exact hr 3 (by decide))
  obtain ⟨s5, e5, r5, g5, mem5, rd5, wr5⟩ := exec_add_imm s4 .r10 16
  obtain ⟨s6, e6, r6, g6, mem6, rd6, wr6⟩ := exec_add_imm s5 .rbx 4
  obtain ⟨s7, e7, r7, z7, g7, mem7, rd7, wr7⟩ := exec_sub_imm s6 .rcx 1
  obtain hrun : runBlock isa copyInBody s = some s7 := by
    rw [copyInBody_eq]
    rw [runBlock_append, e1, Option.bind_some, runBlock_append, e2, Option.bind_some, runBlock_append, e3,
      Option.bind_some, runBlock_append, e4, Option.bind_some, runBlock_cons, e5, runStep_some, runBlock_cons,
      e6, runStep_some, runBlock_cons, e7, runStep_some, runBlock_nil]
  -- Registers through the words.
  obtain r9s : ∀ t ∈ [s1, s2, s3, s4], t.gpr .r9 = s.gpr .r9 := by
    intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact g1 _ (by decide)
    · rw [g2 _ (by decide), g1 _ (by decide)]
    · rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
    · rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  obtain r10s : ∀ t ∈ [s1, s2, s3, s4], t.gpr .r10 = s.gpr .r10 := by
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
  let v (w : Nat) := bswap32 (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32)
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
  obtain rbx_4 : s4.gpr .rbx = s.gpr .rbx := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  obtain rcx_4 : s4.gpr .rcx = s.gpr .rcx := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  refine ⟨s7, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_⟩
  · rw [mem7, mem6, mem5, mm]
    simp only [laneWrites, inSpec, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.foldl_cons, List.foldl_nil, List.singleton_append, List.cons_append,
      List.map_cons]
    rfl
  · rw [g7 _ (by decide), g6 _ (by decide), r5, r10_4]; rfl
  · rw [g7 _ (by decide), r6, g5 _ (by decide), rbx_4]; rfl
  · rw [r7, g6 _ (by decide), g5 _ (by decide), rcx_4]; rfl
  · rw [z7, g6 _ (by decide), g5 _ (by decide), rcx_4]; rfl
  · rw [rd7, rd6, rd5, rd4, rd3, rd2, rd1]
  · rw [wr7, wr6, wr5, wr4, wr3, wr2, wr1]
  · rw [g7 _ h3, g6 _ h2, g5 _ h4, g4 _ h1, g3 _ h1, g2 _ h1, g1 _ h1]

theorem cnt_ne_zero {k : Nat} (h1 : 2 ≤ k) (h2 : k ≤ 16) :
    (BitVec.ofNat 64 k - 1 == 0) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro h0
  have := congrArg BitVec.toNat h0
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_arith)] at this
  omega_arith

theorem cnt_sub1 {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 16) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  have := r8_sub k h1 h2
  rwa [show (1 : BitVec 32).signExtend 64 = 1 from rfl] at this

theorem copyIn_loop {s₀ : State} {p : Addr} {m : Nat} (hpre : CopyPre s₀ p m) :
    ∀ k s, CopyInInv s₀ p m (m - k) s → 1 ≤ k → k ≤ m →
      WP isa (.loop (.block copyInBody) .ne) s (fun s' => CopyInInv s₀ p m m s') := by
  intro k s hs hk1 hkm
  refine WP.loop (M := isa) (fun k t => CopyInInv s₀ p m (m - k) t ∧ 1 ≤ k ∧ k ≤ m) ?_ k s ⟨hs, hk1, hkm⟩
  intro k t ⟨inv, hk1, hkm⟩
  have hm16 := hpre.le.2
  let j := m - k
  obtain hj : j < 16 := by omega_arith
  obtain hr9 : t.gpr .r9 = s₀.gpr .r9 := inv.regs _ (by decide) (by decide) (by decide) (by decide)
  obtain hroom : Room t := room_congr hpre.room hr9 inv.wr
  obtain hrb : t.gpr .rbx = t.gpr .r9 + BitVec.ofNat 64 (4 * j) := by rw [inv.rbx, hr9]
  obtain hdata : ∀ w < 4, t.gpr .r10 + BitVec.ofNat 64 (4 * w) = p + BitVec.ofNat 64 (16 * j + 4 * w) := by
    intro w _; rw [inv.r10, Offset.add_add]
  obtain hr : ∀ w < 4, InRegions (t.rd ++ t.wr) (t.gpr .r10 + BitVec.ofNat 64 (4 * w)) 4 := by
    intro w hw; rw [hdata w hw, inv.rd, inv.wr]; exact hpre.read j (by omega_arith) w hw
  obtain harr : arraysR t = arraysR s₀ := by simp [arraysR, hr9]
  obtain hsep : ∀ w < 4, Region.Disjoint ⟨t.gpr .r10 + BitVec.ofNat 64 (4 * w), 4⟩ (arraysR t) := by
    intro w hw
    rw [hdata w hw, harr]
    exact hpre.sep.sub_left (Offset.sub_base p (by omega_arith))
  obtain ⟨t', ht', hmem, hr10, hrbx, hrcx, hzf, hrd, hwr, hregs⟩ := copyInBody_ok hj t hroom hrb hr hsep
  refine WP.of_runBlock ⟨t', ht', ?_⟩
  obtain hr9' : t'.gpr .r9 = t.gpr .r9 := hregs _ (by decide) (by decide) (by decide) (by decide)
  obtain inv' : CopyInInv s₀ p m (j + 1) t' := by
    refine ⟨by omega_arith, ?_, ?_, ?_, fun w hw b hb => ?_, ?_, fun r h1 h2 h3 h4 => ?_, by rw [hrd, inv.rd],
      by rw [hwr, inv.wr]⟩
    · rw [hr10, inv.r10, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add]; congr 2
    · rw [hrbx, inv.rbx, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    · rw [hrcx, inv.rcx, show m - j = k by omega_arith, cnt_sub1 hk1 (by omega_arith)]; congr 1; omega_arith
    · have hl : lv t' (arrSlot w) b = (laneWrites t (inSpec t.mem (t.gpr .r10)) j).readW (laneA t (arrSlot w) b) 32 := by
        rw [← hmem]; simp only [lv, laneA, hr9']
      rw [hl, lv_laneWrites (inSpec_dests _ _) t (mem_arrA_of hw) (by omega_arith) hj]
      by_cases hbj : b = j
      · subst hbj
        simp only [ite_true, newVal, inSpec, List.range_succ, List.range_zero, List.nil_append,
          List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.singleton_append,
          List.cons_append]
        rw [bw, ← hdata w hw]
        obtain hkeep : t.mem.readW (t.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32 =
            s₀.mem.readW (t.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32 := by
          refine inv.frame.readW (Region.contains_self _ _) ?_ (by decide)
          intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'; rw [← harr]; exact hsep w hw
        rw [← hkeep]
        rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> simp [arrSlot]
      · rw [ite_eq_right hbj]; exact inv.lanes w hw b (by omega_arith)
    · refine inv.frame.trans ?_
      have := laneWrites_frame (inSpec_dests t.mem (t.gpr .r10)) t (b := j) hj
      rw [← hmem, harr] at this; exact this
    · rw [hregs r h1 h2 h3 h4]; exact inv.regs r h1 h2 h3 h4
  by_cases hk : k = 1
  · subst hk
    left
    obtain hjm : j + 1 = m := by omega_arith
    refine ⟨?_, hjm ▸ inv'⟩
    show t'.zf.map (!·) = some false
    rw [hzf, inv.rcx, show m - (m - 1) = 1 by omega_arith]; rfl
  · right
    refine ⟨?_, k - 1, by omega_arith, ⟨by simpa [show j + 1 = m - (k - 1) by omega_arith] using inv', by omega_arith, by omega_arith⟩⟩
    show t'.zf.map (!·) = some true
    rw [hzf, inv.rcx, show m - (m - k) = k by omega_arith, cnt_ne_zero (by omega_arith) (by omega_arith)]; rfl

/-! ## Copying out -/

/-- Byte `j` (in memory order) of a byte-swapped word is byte `3 - j` of the word. -/
theorem bswap32_byte (x : BitVec 32) {j : Nat} (hj : j < 4) :
    (bswap32 x).extractLsb' (8 * j) 8 = (x >>> (8 * (3 - j))).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain h4 := Proof.Seed.getLsbD_append4 (x.extractLsb' 0 8) (x.extractLsb' 8 8) (x.extractLsb' 16 8)
    (x.extractLsb' 24 8) hi
  obtain e : ((bswap32 x).extractLsb' (8 * j) 8).getLsbD i = (bswap32 x).getLsbD (8 * j + i) := by
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [e]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  unfold bswap32
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
    ((((m.writeW (a + BitVec.ofNat 64 0) (bswap32 (y 0))).writeW (a + BitVec.ofNat 64 4) (bswap32 (y 1))).writeW
      (a + BitVec.ofNat 64 8) (bswap32 (y 2))).writeW (a + BitVec.ofNat 64 12) (bswap32 (y 3)))
      (a + BitVec.ofNat 64 i) = (y (i / 4) >>> (8 * (3 - i % 4))).setWidth 8 := by
  rcases (show i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3 by omega_arith) with h | h | h | h
  · rw [writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW32_at _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      bswap32_byte _ (by omega_arith), h]
    congr 3; omega_arith
  · rw [writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      writeW32_at _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), bswap32_byte _ (by omega_arith), h]
    congr 3; omega_arith
  · rw [writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW32_at _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      bswap32_byte _ (by omega_arith), h]
    congr 3; omega_arith
  · rw [writeW32_at _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), bswap32_byte _ (by omega_arith), h]
    congr 3; omega_arith

/-- The copy of word `w` of a block out. -/
def outWord (w : Nat) : List Instr :=
  [.mov32 .rax (.mem (lane .rbx (arrSlot ((w + 2) % 4)) 0)), .bswap32 .rax,
   .store32 { base := .r10, disp := ((4 * w : Nat) : Int) } .rax]

theorem copyOutBody_eq : copyOutBody = outWord 0 ++ (outWord 1 ++ (outWord 2 ++ (outWord 3 ++
    ([.alu .add .r10 (.imm 16), .alu .add .rbx (.imm 4), .alu .sub .rcx (.imm 1)] : List Instr)))) := rfl

theorem copyOutWord_ok {w j : Nat} (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .rbx = s.gpr .r9 + BitVec.ofNat 64 (4 * j))
    (hwr : InRegions s.wr (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 4) :
    ∃ s', runBlock isa (outWord w) s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r10 + BitVec.ofNat 64 (4 * w))
        (bswap32 (lv s (arrSlot ((w + 2) % 4)) j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  obtain hL : arrSlot ((w + 2) % 4) ∈ arrays := mem_arrA_of (Nat.mod_lt _ (by decide))
  obtain hea : s.ea (lane .rbx (arrSlot ((w + 2) % 4)) 0) = laneA s (arrSlot ((w + 2) % 4)) j := by
    rw [ea_lane, hrb, laneA, Nat.mul_zero, Nat.add_zero, Offset.add_add, Nat.add_comm]
  unfold outWord
  rw [runBlock_cons, exec_mov32_mem (by rw [hea]; exact lane_rw h hL hj), hea, lv_eq, runStep_some,
    runBlock_cons]
  rw [show exec (.bswap32 .rax) (s.setReg32 .rax (lv s (arrSlot ((w + 2) % 4)) j)) =
    some ((s.setReg32 .rax (lv s (arrSlot ((w + 2) % 4)) j)).setReg32 .rax
      (bswap32 (((s.setReg32 .rax (lv s (arrSlot ((w + 2) % 4)) j)).gpr .rax).setWidth 32))) from rfl,
    runStep_some, runBlock_cons]
  obtain hea2 : ∀ t : State, t.gpr .r10 = s.gpr .r10 →
      t.ea { base := .r10, disp := ((4 * w : Nat) : Int) } = s.gpr .r10 + BitVec.ofNat 64 (4 * w) := by
    intro t ht; rw [ea_off, ht]
  rw [exec_store32 (by rw [hea2 _ (by simp [State.setReg32, gpr_setReg])]; exact hwr),
    hea2 _ (by simp [State.setReg32, gpr_setReg]), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, fun r hr => ?_⟩
  · simp [State.setReg32, gpr_setReg, mem_setReg, setWidth_setWidth_32]
  · simp [State.setReg32, gpr_setReg, hr]

/-- The four words `y` of a block, byte-swapped, from `q`. -/
def outWrites (m : Mem) (q : Addr) (y : Nat → BitVec 32) : Mem :=
  (((m.writeW (q + BitVec.ofNat 64 0) (bswap32 (y 0))).writeW (q + BitVec.ofNat 64 4) (bswap32 (y 1))).writeW
    (q + BitVec.ofNat 64 8) (bswap32 (y 2))).writeW (q + BitVec.ofNat 64 12) (bswap32 (y 3))

theorem copyOutBody_ok {j : Nat} (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .rbx = s.gpr .r9 + BitVec.ofNat 64 (4 * j))
    (hwr : ∀ w < 4, InRegions s.wr (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 4)
    (hsep : Region.Disjoint ⟨s.gpr .r10, 16⟩ (arraysR s)) :
    ∃ s', runBlock isa copyOutBody s = some s' ∧
      s'.mem = outWrites s.mem (s.gpr .r10) (fun w => lv s (arrSlot ((w + 2) % 4)) j) ∧
      s'.gpr .r10 = s.gpr .r10 + 16 ∧ s'.gpr .rbx = s.gpr .rbx + 4 ∧
      s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .r10 → s'.gpr r = s.gpr r) := by
  -- The lanes keep their values while the block is written.
  obtain hkeep : ∀ (t : State), t.gpr .r9 = s.gpr .r9 → Frame [⟨s.gpr .r10, 16⟩] s.mem t.mem → ∀ w < 4,
      lv t (arrSlot ((w + 2) % 4)) j = lv s (arrSlot ((w + 2) % 4)) j := by
    intro t ht hf w hw
    simp only [lv, laneA, ht]
    refine hf.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'
    exact fun x h1 h2 => hsep x h2 (lane_inArrays (mem_arrA_of (Nat.mod_lt _ (by decide))) hj s
      |>.byte h1)
  obtain ⟨s1, e1, m1, rd1, wr1, g1⟩ := copyOutWord_ok (w := 0) hj s h hrb (hwr 0 (by decide))
  obtain r9_1 : s1.gpr .r9 = s.gpr .r9 := g1 _ (by decide)
  obtain h1 : Room s1 := room_congr h r9_1 wr1
  obtain hin : ∀ w < 4, (⟨s.gpr .r10, 16⟩ : Region).Contains (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) (32 / 8) :=
    fun w hw => Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain f1 : Frame [⟨s.gpr .r10, 16⟩] s.mem s1.mem := by
    rw [m1]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (hin 0 (by decide))
  obtain ⟨s2, e2, m2, rd2, wr2, g2⟩ := copyOutWord_ok (w := 1) hj s1 h1
    (by rw [g1 _ (by decide), r9_1, hrb]) (by rw [wr1, g1 _ (by decide)]; exact hwr 1 (by decide))
  obtain r9_2 : s2.gpr .r9 = s.gpr .r9 := by rw [g2 _ (by decide), r9_1]
  obtain h2 : Room s2 := room_congr h r9_2 (by rw [wr2, wr1])
  obtain r10_1 : s1.gpr .r10 = s.gpr .r10 := g1 _ (by decide)
  obtain f2 : Frame [⟨s.gpr .r10, 16⟩] s.mem s2.mem := by
    rw [m2, r10_1]; exact f1.writeW List.mem_cons_self _ (hin 1 (by decide))
  obtain ⟨s3, e3, m3, rd3, wr3, g3⟩ := copyOutWord_ok (w := 2) hj s2 h2
    (by rw [g2 _ (by decide), g1 _ (by decide), r9_2, hrb])
    (by rw [wr2, wr1, g2 _ (by decide), r10_1]; exact hwr 2 (by decide))
  obtain r9_3 : s3.gpr .r9 = s.gpr .r9 := by rw [g3 _ (by decide), r9_2]
  obtain h3 : Room s3 := room_congr h r9_3 (by rw [wr3, wr2, wr1])
  obtain r10_2 : s2.gpr .r10 = s.gpr .r10 := by rw [g2 _ (by decide), r10_1]
  obtain f3 : Frame [⟨s.gpr .r10, 16⟩] s.mem s3.mem := by
    rw [m3, r10_2]; exact f2.writeW List.mem_cons_self _ (hin 2 (by decide))
  obtain ⟨s4, e4, m4, rd4, wr4, g4⟩ := copyOutWord_ok (w := 3) hj s3 h3
    (by rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), r9_3, hrb])
    (by rw [wr3, wr2, wr1, g3 _ (by decide), r10_2]; exact hwr 3 (by decide))
  obtain r10_3 : s3.gpr .r10 = s.gpr .r10 := by rw [g3 _ (by decide), r10_2]
  obtain ⟨s5, e5, r5, g5, mem5, rd5, wr5⟩ := exec_add_imm s4 .r10 16
  obtain ⟨s6, e6, r6, g6, mem6, rd6, wr6⟩ := exec_add_imm s5 .rbx 4
  obtain ⟨s7, e7, r7, z7, g7, mem7, rd7, wr7⟩ := exec_sub_imm s6 .rcx 1
  obtain hrun : runBlock isa copyOutBody s = some s7 := by
    rw [copyOutBody_eq, runBlock_append, e1, Option.bind_some, runBlock_append, e2, Option.bind_some,
      runBlock_append, e3, Option.bind_some, runBlock_append, e4, Option.bind_some, runBlock_cons, e5,
      runStep_some, runBlock_cons, e6, runStep_some, runBlock_cons, e7, runStep_some, runBlock_nil]
  obtain rbx_4 : s4.gpr .rbx = s.gpr .rbx := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  obtain rcx_4 : s4.gpr .rcx = s.gpr .rcx := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  obtain r10_4 : s4.gpr .r10 = s.gpr .r10 := by rw [g4 _ (by decide), r10_3]
  refine ⟨s7, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_⟩
  · rw [mem7, mem6, mem5, m4, r10_3, hkeep s3 r9_3 f3 3 (by decide), m3, r10_2,
      hkeep s2 r9_2 f2 2 (by decide), m2, r10_1, hkeep s1 r9_1 f1 1 (by decide), m1, outWrites]
  · rw [g7 _ (by decide), g6 _ (by decide), r5, r10_4]; rfl
  · rw [g7 _ (by decide), r6, g5 _ (by decide), rbx_4]; rfl
  · rw [r7, g6 _ (by decide), g5 _ (by decide), rcx_4]; rfl
  · rw [z7, g6 _ (by decide), g5 _ (by decide), rcx_4]; rfl
  · rw [rd7, rd6, rd5, rd4, rd3, rd2, rd1]
  · rw [wr7, wr6, wr5, wr4, wr3, wr2, wr1]
  · rw [g7 _ h3, g6 _ h2, g5 _ h4, g4 _ h1, g3 _ h1, g2 _ h1, g1 _ h1]

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
  r10 : s.gpr .r10 = p + BitVec.ofNat 64 (16 * j)
  rbx : s.gpr .rbx = s₀.gpr .r9 + BitVec.ofNat 64 (4 * j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (m - j)
  done : ∀ b < j, ∀ i < 16, s.mem (p + BitVec.ofNat 64 (16 * b + i)) = outByte s₀ b i
  frame : Frame [⟨p, 16 * m⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyOut_loop {s₀ : State} {p : Addr} {m : Nat} (hpre : CopyOutPre s₀ p m) :
    ∀ k s, CopyOutInv s₀ p m (m - k) s → 1 ≤ k → k ≤ m →
      WP isa (.loop (.block copyOutBody) .ne) s (fun s' => CopyOutInv s₀ p m m s') := by
  intro k s hs hk1 hkm
  refine WP.loop (M := isa) (fun k t => CopyOutInv s₀ p m (m - k) t ∧ 1 ≤ k ∧ k ≤ m) ?_ k s ⟨hs, hk1, hkm⟩
  intro k t ⟨inv, hk1, hkm⟩
  have hm16 := hpre.le.2
  let j := m - k
  obtain hj : j < 16 := by omega_arith
  obtain hr9 : t.gpr .r9 = s₀.gpr .r9 := inv.regs _ (by decide) (by decide) (by decide) (by decide)
  obtain hroom : Room t := room_congr hpre.room hr9 inv.wr
  obtain hrb : t.gpr .rbx = t.gpr .r9 + BitVec.ofNat 64 (4 * j) := by rw [inv.rbx, hr9]
  obtain hwr : ∀ w < 4, InRegions t.wr (t.gpr .r10 + BitVec.ofNat 64 (4 * w)) 4 := by
    intro w hw; rw [inv.r10, Offset.add_add, inv.wr]; exact hpre.write j (by omega_arith) w hw
  obtain harr : arraysR t = arraysR s₀ := by simp [arraysR, hr9]
  obtain hsep : Region.Disjoint ⟨t.gpr .r10, 16⟩ (arraysR t) := by
    rw [inv.r10, harr]; exact hpre.sep.sub_left (Offset.sub_base p (by omega_arith))
  obtain ⟨t', ht', hmem, hr10, hrbx, hrcx, hzf, hrd, hwr', hregs⟩ := copyOutBody_ok hj t hroom hrb hwr hsep
  refine WP.of_runBlock ⟨t', ht', ?_⟩
  -- The lanes, as they were.
  obtain hlanes : ∀ w < 4, lv t (arrSlot ((w + 2) % 4)) j = lv s₀ (arrSlot ((w + 2) % 4)) j := by
    intro w hw
    simp only [lv, laneA, hr9]
    refine inv.frame.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'
    exact fun x h1 h2 => hpre.sep x h2 (lane_inArrays (mem_arrA_of (Nat.mod_lt _ (by decide))) hj s₀ |>.byte h1)
  obtain inv' : CopyOutInv s₀ p m (j + 1) t' := by
    refine ⟨by omega_arith, ?_, ?_, ?_, fun b hb i hi => ?_, ?_, fun r h1 h2 h3 h4 => ?_, by rw [hrd, inv.rd],
      by rw [hwr', inv.wr]⟩
    · rw [hr10, inv.r10, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add]; congr 2
    · rw [hrbx, inv.rbx, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    · rw [hrcx, inv.rcx, show m - j = k by omega_arith, cnt_sub1 hk1 (by omega_arith)]; congr 1; omega_arith
    · rw [hmem]
      by_cases hbj : b = j
      · subst hbj
        rw [show p + BitVec.ofNat 64 (16 * (m - k) + i) = t.gpr .r10 + BitVec.ofNat 64 i by
          rw [inv.r10, Offset.add_add]]
        unfold outWrites
        rw [block_writes _ _ (fun w => lv t (arrSlot ((w + 2) % 4)) j) hi, outByte, hlanes _ (by omega_arith)]
      · rw [outWrites_off _ _ _ ?_]
        · exact inv.done b (by omega_arith) i hi
        · rw [inv.r10, Offset.sub_toNat' p (by omega_arith) (by omega_arith)]
          split <;> omega_arith
    · rw [hmem, inv.r10]
      exact outWrites_frame inv.frame (by omega_arith) (by omega_arith) _
    · rw [hregs r h1 h2 h3 h4]; exact inv.regs r h1 h2 h3 h4
  by_cases hk : k = 1
  · subst hk
    left
    obtain hjm : j + 1 = m := by omega_arith
    refine ⟨?_, hjm ▸ inv'⟩
    show t'.zf.map (!·) = some false
    rw [hzf, inv.rcx, show m - (m - 1) = 1 by omega_arith]; rfl
  · right
    refine ⟨?_, k - 1, by omega_arith, ⟨by simpa [show j + 1 = m - (k - 1) by omega_arith] using inv', by omega_arith, by omega_arith⟩⟩
    show t'.zf.map (!·) = some true
    rw [hzf, inv.rcx, show m - (m - k) = k by omega_arith, cnt_ne_zero (by omega_arith) (by omega_arith)]; rfl

end VG.Proof.Seed.X86_64

end

end

/-!
# A batch on x86-64

`batch_ok`: a batch encrypts or decrypts the first `min n 16` blocks at
`rsi` in place (`n = rdx`), with the keys at `rdi` (`keysAt`), and moves
`rsi` and `rdx` past them.
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Impl.Aes.X86_64 VG.Proof.Seed

/-! ## The batch size -/

theorem batchSize_ok (s : State) :
    WP isa batchSize s (fun s' => s'.gpr .rcx = BitVec.ofNat 64 (min (s.gpr .rdx).toNat 16) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr) := by
  let v := s.setReg .rcx (s.gpr .rdx)
  let c := decide ((v.gpr .rcx).toNat < ((16 : BitVec 32).signExtend 64).toNat)
  let s₁ := arithFlags v (v.gpr .rcx - (16 : BitVec 32).signExtend 64) c
    (subOverflow (v.gpr .rcx) ((16 : BitVec 32).signExtend 64) (v.gpr .rcx - (16 : BitVec 32).signExtend 64))
  have e₁ : runBlock isa [movR .rcx .rdx, .alu .cmp .rcx (.imm 16)] s = some s₁ := rfl
  obtain g₁ : ∀ r, s₁.gpr r = v.gpr r := fun r => by simp only [s₁, gpr_arithFlags]
  obtain hc : c = decide ((s.gpr .rdx).toNat < 16) := by
    simp only [c, v, gpr_setReg_self]; rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.ite c (by show s₁.cf = some c; rfl) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · rw [hc] at hb
    obtain hlt := of_decide_eq_true hb
    refine ⟨by rw [g₁, gpr_setReg_self, Nat.min_eq_left (by omega_using [hlt]), BitVec.ofNat_toNat, BitVec.setWidth_eq],
      fun r hr => by rw [g₁, gpr_setReg_of_ne (s := s) _ hr], rfl, rfl, rfl⟩
  · rw [hc] at hb
    obtain hge := of_decide_eq_false hb
    let s₂ := s₁.setReg .rcx ((16 : BitVec 32).signExtend 64)
    refine WP.of_runBlock ⟨s₂, rfl, ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
    · rw [gpr_setReg_self, Nat.min_eq_right (by omega_using [hge])]; rfl
    · rw [gpr_setReg_of_ne (s := s₁) _ hr, g₁, gpr_setReg_of_ne (s := s) _ hr]

/-! ## Small steps -/

theorem copyStart_ok (s : State) :
    ∃ t, runBlock isa copyStart s = some t ∧ t.gpr .r10 = s.gpr .rsi ∧ t.gpr .rbx = s.gpr .r9 ∧
      (∀ r, r ≠ .r10 → r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  ⟨_, rfl, by simp [gpr_setReg], by simp [gpr_setReg],
    fun r h1 h2 => by simp [gpr_setReg, h1, h2], rfl, rfl, rfl⟩

theorem exec_sub_reg (s : State) (d r : Reg) :
    ∃ t, exec (.alu .sub d (.reg r)) s = some t ∧ t.gpr d = s.gpr d - s.gpr r ∧
      t.zf = some (s.gpr d - s.gpr r == 0) ∧
      (∀ x, x ≠ d → t.gpr x = s.gpr x) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  ⟨_, rfl, by simp [gpr_setReg], rfl, fun r h => by simp [gpr_setReg, h, gpr_arithFlags], rfl, rfl, rfl⟩

theorem exec_movR (s : State) (d r : Reg) :
    ∃ t, exec (movR d r) s = some t ∧ t.gpr d = s.gpr r ∧
      (∀ x, x ≠ d → t.gpr x = s.gpr x) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.zf = s.zf :=
  ⟨_, rfl, by simp [gpr_setReg], fun r h => by simp [gpr_setReg, h], rfl, rfl, rfl, rfl⟩

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

/-- The masks are outside a region apart from the scratch buffer. -/
theorem masks_of_frame {s s' : State} {R : Region} (hm : MasksIn s) (hr9 : s'.gpr .r9 = s.gpr .r9)
    (hfr : Frame [R] s.mem s'.mem) (hd : R.Disjoint (scratchR s)) : MasksIn s' := by
  intro kv hkv
  obtain hlt := maskSlots_lt kv hkv
  rw [← hm kv hkv]
  show s'.mem.readW (Straight.wordAddr (s'.gpr .r9) kv.1) 64 = s.mem.readW (Straight.wordAddr (s.gpr .r9) kv.1) 64
  rw [hr9]
  refine hfr.readW (r := ⟨Straight.wordAddr (s.gpr .r9) kv.1, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  refine (hd.sub_right ?_).symm
  show Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * kv.1), 8⟩ ⟨s.gpr .r9, 8 * scratchSlots⟩
  exact Offset.sub_base _ (by unfold scratchSlots; omega_using [hlt])

/-! ## The batch -/

/-- What a batch needs: the scratch buffer and the masks; the batch's blocks
writable, and they and the keys apart from the scratch buffer and each other. -/
structure BatchPre (d : Spec.Seed.Direction) (s : State) : Prop where
  room : Room s
  masks : MasksIn s
  pos : 1 ≤ (s.gpr .rdx).toNat
  data : ∀ b < min (s.gpr .rdx).toNat 16, ∀ w < 4,
    InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (16 * b + 4 * w)) 4
  dataSep : Region.Disjoint ⟨s.gpr .rsi, 16 * min (s.gpr .rdx).toNat 16⟩ (scratchR s)
  keys : KeysOk d s (s.gpr .rdi)
  keyData : ∀ j < 16, Region.Disjoint ⟨kp d (s.gpr .rdi) j, 8⟩ ⟨s.gpr .rsi, 16 * min (s.gpr .rdx).toNat 16⟩

structure BatchPost (d : Spec.Seed.Direction) (s s' : State) : Prop where
  done : ∀ b < min (s.gpr .rdx).toNat 16,
    Spec.Seed.blockAt s'.mem (s.gpr .rsi + BitVec.ofNat 64 (16 * b)) =
      Spec.Seed.crypt (keysAt d s.mem (s.gpr .rdi))
        (Spec.Seed.blockAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (16 * b)))
  rsi : s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 (16 * min (s.gpr .rdx).toNat 16)
  rdx : s'.gpr .rdx = s.gpr .rdx - BitVec.ofNat 64 (min (s.gpr .rdx).toNat 16)
  zf : s'.zf = some (s.gpr .rdx - BitVec.ofNat 64 (min (s.gpr .rdx).toNat 16) == 0)
  regs : ∀ r ∈ [Reg.rdi, .r9, .rsp], s'.gpr r = s.gpr r
  masks : MasksIn s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [workR s, ⟨s.gpr .rsi, 16 * min (s.gpr .rdx).toNat 16⟩] s.mem s'.mem

theorem arraysR_sub_scratch (s : State) : Region.Sub (arraysR s) (scratchR s) := by
  show Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * 61), 8 * 64⟩ ⟨s.gpr .r9, 8 * scratchSlots⟩
  exact Offset.sub_base _ (by unfold scratchSlots; omega_using [])

theorem arraysR_sub_work (s : State) : Region.Sub (arraysR s) (workR s) := by
  show Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * 61), 8 * 64⟩ ⟨s.gpr .r9, 8 * 125⟩
  exact Offset.sub_base _ (by omega_using [])

theorem batch_ok (d : Spec.Seed.Direction) {s : State} (h : BatchPre d s) :
    WP isa (batch d) s (BatchPost d s) := by
  let n := (s.gpr .rdx).toNat
  let k := min n 16
  let p := s.gpr .rsi
  obtain hk1 : 1 ≤ k := by have := h.pos; omega
  obtain hk16 : k ≤ 16 := by omega_using []
  have hpos := h.pos
  -- the copy in
  apply WP.seq
  apply WP.seq
  refine WP.mono (batchSize_ok s) fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  apply WP.seq
  obtain ⟨s₂, e₂, r10₂, rbx₂, g₂, m₂, rd₂, wr₂⟩ := copyStart_ok s₁
  refine WP.of_runBlock ⟨s₂, e₂, ?_⟩
  obtain G₂ : ∀ r, r ≠ .rcx → r ≠ .r10 → r ≠ .rbx → s₂.gpr r = s.gpr r := fun r a b c =>
    (g₂ r b c).trans (g₁ r a)
  obtain r9₂ : s₂.gpr .r9 = s.gpr .r9 := G₂ _ (by decide) (by decide) (by decide)
  obtain scr₂ : scratchR s₂ = scratchR s := by simp only [scratchR, r9₂]
  obtain arr₂ : arraysR s₂ = arraysR s := by simp only [arraysR, r9₂]
  obtain room₂ : Room s₂ := room_congr h.room r9₂ (by rw [wr₂, wr₁])
  obtain pre₂ : CopyPre s₂ p k := by
    refine ⟨room₂, ⟨hk1, hk16⟩, fun b hb w hw => ?_, ?_⟩
    · obtain ⟨r, hr, hc⟩ := h.data b hb w hw
      exact ⟨r, by rw [rd₂, wr₂, rd₁, wr₁]; exact List.mem_append_right _ hr, hc⟩
    · rw [arr₂]; exact h.dataSep.sub_right (arraysR_sub_scratch s)
  obtain inv₂ : CopyInInv s₂ p k (k - k) s₂ := by
    refine ⟨by omega_using [], ?_, ?_, ?_, fun w _ b hb => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩
    · rw [r10₂, Nat.sub_self, Nat.mul_zero, ofNat_zero_add, g₁ _ (by decide)]
    · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add, rbx₂, g₂ _ (by decide) (by decide)]
    · rw [Nat.sub_self, Nat.sub_zero, g₂ _ (by decide) (by decide), c₁]
  refine WP.mono (copyIn_loop pre₂ k s₂ inv₂ hk1 (Nat.le_refl _)) fun s₃ i₃ => ?_
  obtain r9₃ : s₃.gpr .r9 = s.gpr .r9 := (i₃.regs _ (by decide) (by decide) (by decide) (by decide)).trans r9₂
  obtain G₃ : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rsp], s₃.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .rax ∧ r ≠ .rbx ∧ r ≠ .rcx ∧ r ≠ .r10 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [i₃.regs _ this.1 this.2.1 this.2.2.1 this.2.2.2]
    exact G₂ _ this.2.2.1 this.2.2.2 this.2.1
  obtain rd₃ : s₃.rd = s.rd := by rw [i₃.rd, rd₂, rd₁]
  obtain wr₃ : s₃.wr = s.wr := by rw [i₃.wr, wr₂, wr₁]
  obtain room₃ : Room s₃ := room_congr h.room r9₃ wr₃
  obtain f₃ : Frame [arraysR s] s.mem s₃.mem := by
    have := i₃.frame; rw [arr₂, m₂, m₁] at this; exact this
  obtain masks₃ : MasksIn s₃ := masks_of_arrays h.masks r9₃ f₃
  obtain scr₃ : scratchR s₃ = scratchR s := by simp only [scratchR, r9₃]
  obtain keys₃ : KeysOk d s₃ (s₃.gpr .rdi) := by
    rw [G₃ .rdi (by simp)]
    intro j hj
    obtain ⟨a, b, c⟩ := h.keys j hj
    exact ⟨by rw [rd₃, wr₃]; exact a, by rw [rd₃, wr₃]; exact b, by rw [scr₃]; exact c⟩
  -- the keys are as on entry
  obtain hkeys : ∀ j < 16, keysAt d s₃.mem (s₃.gpr .rdi) j = keysAt d s.mem (s.gpr .rdi) j := by
    intro j hj
    rw [G₃ .rdi (by simp)]
    obtain ⟨-, -, hdis⟩ := h.keys j hj
    obtain hd : ∀ r ∈ [arraysR s], Region.Disjoint ⟨kp d (s.gpr .rdi) j, 8⟩ r := by
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
  refine WP.mono (rounds_ok d room₃ masks₃ keys₃) fun s₄ ⟨q₄, masks₄, room₄, rd₄, wr₄, g₄, f₄⟩ => ?_
  obtain G₄ : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .r9, .rsp], s₄.gpr r = s.gpr r := by
    intro r hr
    rw [g₄ r hr]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact G₃ _ (by simp)
    · exact G₃ _ (by simp)
    · exact G₃ _ (by simp)
    · exact r9₃
    · exact G₃ _ (by simp)
  obtain hq₄ : ∀ b < k, quad s₄ b = roundsN (keysAt d s.mem (s.gpr .rdi)) 16
      (decodeQ (Spec.Seed.blockAt s.mem (p + BitVec.ofNat 64 (16 * b)))) := by
    intro b hb
    rw [q₄ b (by omega_using [hb]), hq₃ b hb]
    exact roundsN_congr 16 _ hkeys
  -- the copy out
  apply WP.seq
  refine WP.mono (batchSize_ok s₄) fun s₅ ⟨c₅, g₅, m₅, rd₅, wr₅⟩ => ?_
  apply WP.seq
  obtain ⟨s₆, e₆, r10₆, rbx₆, g₆, m₆, rd₆, wr₆⟩ := copyStart_ok s₅
  refine WP.of_runBlock ⟨s₆, e₆, ?_⟩
  obtain G₆ : ∀ r, r ≠ .rcx → r ≠ .r10 → r ≠ .rbx → s₆.gpr r = s₄.gpr r := fun r a b c =>
    (g₆ r b c).trans (g₅ r a)
  obtain r9₆ : s₆.gpr .r9 = s.gpr .r9 := (G₆ _ (by decide) (by decide) (by decide)).trans (G₄ _ (by simp))
  obtain rdx₄ : s₄.gpr .rdx = s.gpr .rdx := G₄ _ (by simp)
  obtain rsi₄ : s₄.gpr .rsi = p := G₄ _ (by simp)
  obtain rd₆ : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  obtain wr₆ : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  obtain arr₆ : arraysR s₆ = arraysR s := by simp only [arraysR, r9₆]
  obtain pre₆ : CopyOutPre s₆ p k := by
    refine ⟨room_congr h.room r9₆ wr₆, ⟨hk1, hk16⟩, fun b hb w hw => ?_, ?_⟩
    · rw [wr₆]; exact h.data b hb w hw
    · rw [arr₆]; exact h.dataSep.sub_right (arraysR_sub_scratch s)
  obtain inv₆ : CopyOutInv s₆ p k (k - k) s₆ := by
    refine ⟨by omega_using [], ?_, ?_, ?_, fun b hb => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩
    · rw [r10₆, Nat.sub_self, Nat.mul_zero, ofNat_zero_add, g₅ _ (by decide), rsi₄]
    · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add, rbx₆, g₆ _ (by decide) (by decide)]
    · rw [Nat.sub_self, Nat.sub_zero, g₆ _ (by decide) (by decide), c₅, rdx₄]
  obtain quad₆ : ∀ b, quad s₆ b = quad s₄ b := fun b => by
    simp only [quad, lv, laneA, m₆, m₅, r9₆, G₄ .r9 (by simp)]
  apply WP.seq
  refine WP.mono (copyOut_loop pre₆ k s₆ inv₆ hk1 (Nat.le_refl _)) fun s₇ i₇ => ?_
  apply WP.seq
  refine WP.mono (batchSize_ok s₇) fun s₈ ⟨c₈, g₈, m₈, rd₈, wr₈⟩ => ?_
  obtain G₇ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .r10 → s₇.gpr r = s₄.gpr r :=
    fun r a b c e => (i₇.regs r a b c e).trans (G₆ r c e b)
  obtain rdx₇ : s₇.gpr .rdx = s.gpr .rdx := (G₇ _ (by decide) (by decide) (by decide) (by decide)).trans rdx₄
  obtain c₈' : s₈.gpr .rcx = BitVec.ofNat 64 k := by rw [c₈, rdx₇]
  obtain r10₈ : s₈.gpr .r10 = p + BitVec.ofNat 64 (16 * k) := by rw [g₈ _ (by decide), i₇.r10]
  obtain ⟨s₉, e₉, rsi₉, g₉, m₉, rd₉, wr₉, -⟩ := exec_movR s₈ .rsi .r10
  obtain ⟨s', e', rdx', zf', g', m', rd', wr'⟩ := exec_sub_reg s₉ .rdx .rcx
  refine WP.of_runBlock ⟨s', by rw [runBlock_cons, e₉, runStep_some, runBlock_cons, e', runStep_some,
    runBlock_nil], ?_⟩
  obtain rdx₉ : s₉.gpr .rdx = s.gpr .rdx := by rw [g₉ _ (by decide), g₈ _ (by decide), rdx₇]
  obtain rcx₉ : s₉.gpr .rcx = BitVec.ofNat 64 k := by rw [g₉ _ (by decide), c₈']
  obtain mem' : s'.mem = s₇.mem := by rw [m', m₉, m₈]
  obtain G' : ∀ r ∈ [Reg.rdi, .r9, .rsp], s'.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .rcx ∧ r ≠ .rax ∧ r ≠ .rbx ∧ r ≠ .r10 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    rw [g' _ this.1, g₉ _ this.2.1, g₈ _ this.2.2.1, G₇ _ this.2.2.2.1 this.2.2.2.2.1 this.2.2.1 this.2.2.2.2.2]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    exact G₄ _ (by rcases hr with rfl | rfl | rfl <;> simp)
  obtain r9' : s'.gpr .r9 = s.gpr .r9 := G' _ (by simp)
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
        simp only [workR, r9₃]; exact List.mem_cons_self
    obtain c : Frame [workR s, ⟨p, 16 * k⟩] s₄.mem s₇.mem :=
      f₇.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact List.mem_cons_of_mem _ List.mem_cons_self
    exact (a.trans b).trans c
  refine ⟨fun b hb => ?_, ?_, ?_, ?_, G', ?_, by rw [rd', rd₉, rd₈, i₇.rd, rd₆],
    by rw [wr', wr₉, wr₈, i₇.wr, wr₆], frame⟩
  · rw [crypt_eq, ← hq₄ b hb, ← quad₆ b, mem']
    refine blockAt_of_bytes fun i hi => ?_
    rw [Offset.add_ofNat_add_ofNat, i₇.done b hb i hi, encodeSwapped_get _ _ hi]
  · rw [g' _ (by decide), rsi₉, r10₈]
  · rw [rdx', rdx₉, rcx₉]
  · rw [zf', rdx₉, rcx₉]
  · refine masks_of_frame masks₄ (r9'.trans (G₄ _ (by simp)).symm) (by rw [mem']; exact f₇) ?_
    simp only [scratchR, G₄ .r9 (by simp)]
    exact h.dataSep

end VG.Proof.Seed.X86_64

end

end

/-! ### `Seed.X86_64.Setup`, which this module and modules that import it used -/

section

/-!
# Storing to scratch slots

`stores_ok`: stores of registers to distinct slots; `masks_ok`: `setMasks`,
constants through `t0` to distinct slots. Both write only the scratch
buffer.
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Impl.Aes.X86_64

theorem slot_in_scratch (s : State) {j : Nat} (hj : j < scratchSlots) :
    (scratchR s).Contains (wordAddr (s.gpr .r9) j) (64 / 8) :=
  slot_contains (s.gpr .r9) (n := scratchSlots) hj (by unfold scratchSlots; decide)

/-- The memory after storing `v` in slot `k`. -/
def stMem (s : State) (k : Nat) (v : BitVec 64) : Mem := s.mem.writeW (wordAddr (s.gpr .r9) k) v

theorem exec_st {s : State} (h : Room s) {k : Nat} (hk : k < scratchSlots) (r : Reg) :
    exec (st k r) s = some (setMem s (stMem s k (s.gpr r))) := by
  have hw : InRegions s.wr (wordAddr (s.gpr .r9) k) 8 := h.wr (slot_in_scratch s hk)
  have hea : s.ea (slotAt sb k) = wordAddr (s.gpr .r9) k := rfl
  simp only [st, exec, State.store64, hea, hw, ite_true, stMem]
  rfl

theorem slotW_stMem (s : State) {k : Nat} (hk : k < scratchSlots) (v : BitVec 64) {j : Nat}
    (hj : j < scratchSlots) : slotW (setMem s (stMem s k v)) j = if j = k then v else slotW s j := by
  unfold scratchSlots at hk hj
  show (stMem s k v).readW (wordAddr (s.gpr .r9) j) 64 = _
  simp only [stMem]
  split
  · subst j; exact Mem.readW_writeW_self64 _ _ _
  · rename_i hne
    rw [Mem.readW_writeW_sep (slot_sep _ (by omega_using [hj]) (by omega_using [hk]) hne) (by decide)]
    rfl

theorem stMem_frame {s : State} {k : Nat} (hk : k < scratchSlots) (v : BitVec 64) :
    Frame [scratchR s] s.mem (stMem s k v) :=
  (Frame.refl _ _).writeW List.mem_cons_self _ (slot_in_scratch s hk)

theorem slotW_setReg (s : State) {r : Reg} (hr : r ≠ .r9) (v : BitVec 64) (j : Nat) :
    slotW (s.setReg r v) j = slotW s j := by
  show s.mem.readW (wordAddr ((s.setReg r v).gpr .r9) j) 64 = s.mem.readW (wordAddr (s.gpr .r9) j) 64
  rw [gpr_setReg_of_ne (s := s) v (Ne.symm hr)]

/-- A block of stores of registers to distinct scratch slots. -/
theorem stores_ok {s : State} (h : Room s) (l : List (Nat × Reg)) (hl : ∀ p ∈ l, p.1 < scratchSlots)
    (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (l.map fun p => st p.1 p.2) s = some s' ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [scratchR s] s.mem s'.mem ∧
      (∀ p ∈ l, slotW s' p.1 = s.gpr p.2) ∧
      (∀ x < scratchSlots, (∀ p ∈ l, p.1 ≠ x) → slotW s' x = slotW s x) := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, rfl, rfl, Frame.refl _ _, (fun _ h => by cases h),
      fun _ _ _ => rfl⟩
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    have e := exec_st (r := p.2) h hp
    let s₁ : State := setMem s (stMem s p.1 (s.gpr p.2))
    have h₁ : Room s₁ := h
    have hd' : (l.map (·.1)).Nodup := (List.nodup_cons.mp hd).2
    have hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', g', rd', wr', f', set', keep'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hd'
    refine ⟨s', ?_, g', rd', wr', (stMem_frame hp _).trans f', fun q hq => ?_,
      fun x hx hne => ?_⟩
    · rw [List.map_cons, runBlock_cons, e, runStep_some]; exact run'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ hp (fun r hr he => hn (he ▸ List.mem_map_of_mem hr)), slotW_stMem s hp _ hp]
        simp
      · exact set' q hq
    · rw [keep' x hx (fun q hq => hne q (List.mem_cons_of_mem _ hq)), slotW_stMem s hp _ hx]
      simp [Ne.symm (hne p List.mem_cons_self)]

/-- `setMasks`: constants to distinct scratch slots, through `t0`. -/
theorem masks_ok {s : State} (h : Room s) (l : List (Nat × BitVec 64))
    (hl : ∀ p ∈ l, p.1 < scratchSlots) (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (setMasks l) s = some s' ∧ (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [scratchR s] s.mem s'.mem ∧
      (∀ p ∈ l, slotW s' p.1 = p.2) ∧
      (∀ x < scratchSlots, (∀ p ∈ l, p.1 ≠ x) → slotW s' x = slotW s x) := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, (fun _ h => by cases h),
      fun _ _ _ => rfl⟩
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    let s₀ := s.setReg t0 p.2
    have e₀ : exec (imm t0 p.2) s = some s₀ := rfl
    have r9₀ : s₀.gpr .r9 = s.gpr .r9 := gpr_setReg_of_ne (s := s) _ (by decide)
    have h₀ : Room s₀ := room_congr h r9₀ rfl
    have e := exec_st (r := t0) h₀ hp
    let s₁ : State := setMem s₀ (stMem s₀ p.1 (s₀.gpr t0))
    have h₁ : Room s₁ := h₀
    have hd' : (l.map (·.1)).Nodup := (List.nodup_cons.mp hd).2
    have hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', g', rd', wr', f', set', keep'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hd'
    have f₀ : Frame [scratchR s] s.mem s₁.mem := by
      have := stMem_frame (s := s₀) hp (s₀.gpr t0)
      simp only [scratchR, r9₀] at this
      exact this
    have f'' : Frame [scratchR s] s₁.mem s'.mem := by
      simpa only [scratchR, s₁, gpr_setMem, r9₀] using f'
    have sl₀ : ∀ j, slotW s₀ j = slotW s j := slotW_setReg s (by decide) _
    refine ⟨s', ?_, fun r hr => ?_, rd', wr', f₀.trans f'', fun q hq => ?_, fun x hx hne => ?_⟩
    · show runBlock isa ([imm t0 p.2, st p.1 t0] ++ setMasks l) s = some s'
      rw [List.cons_append, runBlock_cons, e₀, runStep_some, List.singleton_append, runBlock_cons, e,
        runStep_some]
      exact run'
    · rw [g' r hr]; exact gpr_setReg_of_ne (s := s) _ hr
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ hp (fun r hr he => hn (he ▸ List.mem_map_of_mem hr)), slotW_stMem s₀ hp _ hp]
        simp [s₀, gpr_setReg]
      · exact set' q hq
    · rw [keep' x hx (fun q hq => hne q (List.mem_cons_of_mem _ hq)), slotW_stMem s₀ hp _ hx,
        ite_eq_right_iff.mpr (fun h' => absurd h' (Ne.symm (hne p List.mem_cons_self))), sl₀]

theorem exec_ld {s : State} (h : Room s) {k : Nat} (hk : k < scratchSlots) (r : Reg) :
    exec (movS r k) s = some (s.setReg r (slotW s k)) := by
  have hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r9) k) 8 := h.rw (slot_in_scratch s hk)
  have hea : s.ea (slotAt sb k) = wordAddr (s.gpr .r9) k := rfl
  simp only [movS, exec, readSrc, State.load64, hea, hr, ite_true, Option.map_some]
  rfl

/-- A block of loads of distinct registers, other than `r9`, from scratch slots. -/
theorem loads_ok {s : State} (h : Room s) (l : List (Reg × Nat))
    (hl : ∀ p ∈ l, p.2 < scratchSlots ∧ p.1 ≠ .r9) (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (l.map fun p => movS p.1 p.2) s = some s' ∧ s'.mem = s.mem ∧
      (∀ p ∈ l, s'.gpr p.1 = slotW s p.2) ∧ (∀ r, (∀ p ∈ l, p.1 ≠ r) → s'.gpr r = s.gpr r) := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, (fun _ h => by cases h), fun _ _ => rfl⟩
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    have e := exec_ld h hp.1 p.1
    let s₁ := s.setReg p.1 (slotW s p.2)
    have c₁ : s₁.gpr .r9 = s.gpr .r9 := gpr_setReg_of_ne (s := s) _ (Ne.symm hp.2)
    have h₁ : Room s₁ := room_congr h c₁ rfl
    have hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', m', set', keep'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (List.nodup_cons.mp hd).2
    have sl₁ : ∀ j, slotW s₁ j = slotW s j := slotW_setReg s hp.2 _
    refine ⟨s', ?_, by rw [m']; rfl, fun q hq => ?_, fun r hr => ?_⟩
    · rw [List.map_cons, runBlock_cons, e, runStep_some]; exact run'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ (fun r hr he => hn (by rw [← he]; exact List.mem_map_of_mem hr))]
        simp [s₁, gpr_setReg]
      · rw [set' q hq, sl₁]
    · rw [keep' r (fun q hq => hr q (List.mem_cons_of_mem _ hq))]
      simp only [s₁]
      rw [gpr_setReg_of_ne (s := s) _ (Ne.symm (hr p List.mem_cons_self))]

end VG.Proof.Seed.X86_64

end

end

/-!
# The function on x86-64

After saving the callee-saved registers and writing the masks to the
scratch buffer, the function runs batches of up to 16 blocks until none are
left (`loop_ok`), then restores the registers (`ecb_ok`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Impl.Aes.X86_64 VG.Proof.Seed

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
  dataIn : (⟨s₀.gpr .rsi, 16 * n⟩ : Region) ∈ s₀.wr
  dataSep : Region.Disjoint ⟨s₀.gpr .rsi, 16 * n⟩ (scratchR s₀)
  fit : 16 * n ≤ 2 ^ 64
  keys : KeysOk d s₀ (s₀.gpr .rdi)
  keyData : ∀ j < 16, Region.Disjoint ⟨kp d (s₀.gpr .rdi) j, 8⟩ ⟨s₀.gpr .rsi, 16 * n⟩

/-- `m` blocks left, the first `n - m` done. -/
structure BatchesInv (d : Spec.Seed.Direction) (s₀ : State) (n m : Nat) (s : State) : Prop where
  pos : 1 ≤ m
  le : m ≤ n
  rdx : s.gpr .rdx = BitVec.ofNat 64 m
  rsi : s.gpr .rsi = s₀.gpr .rsi + BitVec.ofNat 64 (16 * (n - m))
  regs : ∀ r ∈ [Reg.rdi, .r9, .rsp], s.gpr r = s₀.gpr r
  masks : MasksIn s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n - m, Spec.Seed.blockAt s.mem (s₀.gpr .rsi + BitVec.ofNat 64 (16 * b)) =
    Spec.Seed.crypt (keysAt d s₀.mem (s₀.gpr .rdi))
      (Spec.Seed.blockAt s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 (16 * b)))
  frame : Frame [workR s₀, ⟨s₀.gpr .rsi, 16 * (n - m)⟩] s₀.mem s.mem

structure BatchesPost (d : Spec.Seed.Direction) (s₀ : State) (n : Nat) (s : State) : Prop where
  regs : ∀ r ∈ [Reg.rdi, .r9, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n, Spec.Seed.blockAt s.mem (s₀.gpr .rsi + BitVec.ofNat 64 (16 * b)) =
    Spec.Seed.crypt (keysAt d s₀.mem (s₀.gpr .rdi))
      (Spec.Seed.blockAt s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 (16 * b)))
  frame : Frame [workR s₀, ⟨s₀.gpr .rsi, 16 * n⟩] s₀.mem s.mem

theorem BatchesInv.batchPre {d : Spec.Seed.Direction} {s₀ : State} {n m : Nat} (E : BatchesEnv d s₀ n)
    {s : State} (h : BatchesInv d s₀ n m s) : BatchPre d s := by
  have hp := h.pos
  have hl := h.le
  have hfit := E.fit
  obtain hm : (s.gpr .rdx).toNat = m := by rw [h.rdx]; exact toNat_ofNat_le h.le E.fit
  obtain r9 : s.gpr .r9 = s₀.gpr .r9 := h.regs _ (by simp)
  obtain rdi : s.gpr .rdi = s₀.gpr .rdi := h.regs _ (by simp)
  obtain scr : scratchR s = scratchR s₀ := by simp only [scratchR, r9]
  let D := s₀.gpr .rsi
  obtain hsub : Region.Sub ⟨s.gpr .rsi, 16 * min (s.gpr .rdx).toNat 16⟩ ⟨D, 16 * n⟩ := by
    rw [h.rsi, hm]; exact Offset.sub_base _ (by omega_arith)
  refine ⟨room_congr E.room r9 h.wr, h.masks, by omega_arith, fun b hb w hw => ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [h.wr, h.rsi, Offset.add_ofNat_add_ofNat]
    rw [hm] at hb
    exact ⟨_, E.dataIn, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [scr]; exact E.dataSep.sub_left hsub
  · rw [rdi]
    intro j hj
    obtain ⟨a, b, c⟩ := E.keys j hj
    exact ⟨by rw [h.rd, h.wr]; exact a, by rw [h.rd, h.wr]; exact b, by rw [scr]; exact c⟩
  · rw [rdi]; exact (E.keyData j hj).sub_right hsub

theorem loop_ok (d : Spec.Seed.Direction) {s₀ : State} {n : Nat} (E : BatchesEnv d s₀ n) (m : Nat) (s : State)
    (hs : BatchesInv d s₀ n m s) : WP isa (.loop (batch d) .ne) s (BatchesPost d s₀ n) := by
  refine WP.loop (M := isa) (BatchesInv d s₀ n) ?_ m s hs
  intro m s h
  have hp := h.pos
  have hl := h.le
  have hfit := E.fit
  apply WP.mono (batch_ok d (h.batchPre E))
  intro s' q
  obtain hm : (s.gpr .rdx).toNat = m := by rw [h.rdx]; exact toNat_ofNat_le h.le E.fit
  obtain ⟨qdone, qrsi, qrdx, qzf, qregs, qmasks, qrd, qwr, qframe⟩ := q
  rw [hm] at qdone qrsi qrdx qzf qframe
  generalize hk : min m 16 = k at qdone qrsi qrdx qzf qframe
  obtain hk1 : 1 ≤ k := by omega_arith
  obtain hkm : k ≤ m := by omega_arith
  let D := s₀.gpr .rsi
  let S := s₀.gpr .rdi
  obtain r9 : s.gpr .r9 = s₀.gpr .r9 := h.regs _ (by simp)
  obtain rdi : s.gpr .rdi = S := h.regs _ (by simp)
  obtain workR_eq : workR s = workR s₀ := by simp only [workR, r9]
  rw [h.rsi, workR_eq] at qframe
  rw [h.rsi] at qrsi qdone
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
  obtain rdx' : s'.gpr .rdx = BitVec.ofNat 64 (m - k) := by
    rw [qrdx, h.rdx, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith) hkm]
  obtain zf' : s'.zf = some (BitVec.ofNat 64 (m - k) == 0) := by
    rw [qzf, h.rdx, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith) hkm]
  obtain regs' : ∀ r ∈ [Reg.rdi, .r9, .rsp], s'.gpr r = s₀.gpr r := fun r hr =>
    (qregs r hr).trans (h.regs r hr)
  obtain rd' := qrd.trans h.rd
  obtain wr' := qwr.trans h.wr
  by_cases hend : m ≤ 16
  · have hkm' : k = m := by omega_arith
    left
    refine ⟨?_, regs', rd', wr', ?_, ?_⟩
    · show s'.zf.map (!·) = some false
      rw [zf', hkm', Nat.sub_self]; rfl
    · rw [hkm', Nat.sub_self, Nat.sub_zero] at done'; exact done'
    · rw [hkm', Nat.sub_self, Nat.sub_zero] at frame'; exact frame'
  · have hk16 : k = 16 := by omega_arith
    right
    refine ⟨?_, m - k, by omega_arith, ⟨by omega_arith, by omega_arith, rdx', ?_, regs', qmasks, rd', wr', done', frame'⟩⟩
    · show s'.zf.map (!·) = some true
      rw [zf']
      have : (BitVec.ofNat 64 (m - k) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        rw [toNat_ofNat_le (show m - k ≤ n by omega_arith) E.fit] at this
        have z : (0 : BitVec 64).toNat = 0 := rfl
        omega_arith
      rw [this]; rfl
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
schedule readable, apart from each other and the return address. -/
structure EcbPre (s : State) : Prop where
  scratch : ∃ n, 8 * scratchSlots ≤ n ∧ (⟨s.gpr .rcx, n⟩ : Region) ∈ s.wr
  dataIn : (⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩ : Region) ∈ s.wr
  keyIn : (⟨s.gpr .rdi, 128⟩ : Region) ∈ s.rd
  keyData : (⟨s.gpr .rdi, 128⟩ : Region).Disjoint ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩
  keyBuf : (⟨s.gpr .rdi, 128⟩ : Region).Disjoint ⟨s.gpr .rcx, 8 * scratchSlots⟩
  dataBuf : (⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, 8 * scratchSlots⟩
  retData : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩
  retBuf : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 8 * scratchSlots⟩
  fit : 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64

/-- What the function does: every block of the data becomes its encryption or
decryption, the callee-saved registers and the return address are kept, and
only the scratch buffer and the data change. -/
structure EcbPost (d : Spec.Seed.Direction) (s s' : State) : Prop where
  gpr : gprPreserved s s'
  done : ∀ b < (s.gpr .rdx).toNat, Spec.Seed.blockAt s'.mem (s.gpr .rsi + BitVec.ofNat 64 (16 * b)) =
    cipher d (Spec.Seed.scheduleAt s.mem (s.gpr .rdi))
      (Spec.Seed.blockAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (16 * b)))
  frame : Frame [⟨s.gpr .rcx, 8 * scratchSlots⟩, ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩] s.mem s'.mem

theorem savedRegs_ok : ∀ p ∈ Impl.Seed.X86_64.savedRegs, p.2 < scratchSlots ∧ p.1 ≠ .r9 ∧ 125 ≤ p.2 := by decide

theorem setup_eq (d : Spec.Seed.Direction) : setup d =
    [movR .r9 .rcx] ++ (Impl.Seed.X86_64.savedRegs.map fun p => (p.2, p.1)).map (fun p => st p.1 p.2) ++ setG16Masks ++
      ([.alu .add .rdi (.imm (BitVec.ofNat 32 (keyStart d))), .alu .cmp .rdx (.imm 0)] : List Instr) := rfl

theorem restore_eq : restore = Impl.Seed.X86_64.savedRegs.map (fun p => movS p.1 p.2) := rfl

theorem keyStart_ext (d : Spec.Seed.Direction) :
    (BitVec.ofNat 32 (keyStart d)).signExtend 64 = BitVec.ofNat 64 (keyStart d) := by
  cases d <;> rfl

theorem ecb_ok (d : Spec.Seed.Direction) {s : State} (h : EcbPre s) : WP isa (ecb d) s (EcbPost d s) := by
  let n := (s.gpr .rdx).toNat
  let D := s.gpr .rsi
  let S := s.gpr .rdi
  have hn := h.fit
  rw [ecb]
  apply WP.seq
  -- `r9 := rcx`
  let s₁ := s.setReg .r9 (s.gpr .rcx)
  have e₁ : runBlock isa [movR .r9 .rcx] s = some s₁ := rfl
  obtain r9₁ : s₁.gpr .r9 = s.gpr .rcx := gpr_setReg_self (s := s) _ _
  obtain g₁ : ∀ r, r ≠ .r9 → s₁.gpr r = s.gpr r := fun r hr => gpr_setReg_of_ne (s := s) _ hr
  obtain scr₁ : scratchR s₁ = ⟨s.gpr .rcx, 8 * scratchSlots⟩ := by simp only [scratchR, r9₁]
  obtain room₁ : Room s₁ := by
    obtain ⟨n, hn, hm⟩ := h.scratch; exact ⟨n, hn, by rw [r9₁]; exact hm⟩
  -- the saved registers
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, f₂, set₂, keep₂⟩ := stores_ok room₁ (Impl.Seed.X86_64.savedRegs.map fun p => (p.2, p.1))
    (by decide) (by decide)
  obtain room₂ : Room s₂ := room_congr room₁ (by rw [g₂]) wr₂
  -- the masks
  obtain ⟨s₃, e₃, g₃, rd₃, wr₃, f₃, set₃, keep₃⟩ := masks_ok room₂ maskSlots (by decide) (by decide)
  obtain r9₃ : s₃.gpr .r9 = s.gpr .rcx := by rw [g₃ _ (by decide), g₂, r9₁]
  -- the key pointer and the test
  obtain ⟨s₄, e₄, rdi₄, g₄, m₄, rd₄, wr₄⟩ := exec_add_imm s₃ .rdi (BitVec.ofNat 32 (keyStart d))
  let s₅ := arithFlags s₄ (s₄.gpr .rdx - (0 : BitVec 32).signExtend 64)
    (decide ((s₄.gpr .rdx).toNat < ((0 : BitVec 32).signExtend 64).toNat))
    (subOverflow (s₄.gpr .rdx) ((0 : BitVec 32).signExtend 64) (s₄.gpr .rdx - (0 : BitVec 32).signExtend 64))
  have e₅ : exec (.alu .cmp .rdx (.imm 0)) s₄ = some s₅ := rfl
  refine WP.of_runBlock ⟨s₅, by
    rw [setup_eq]
    exact runBlock_trans (runBlock_trans (runBlock_trans e₁ e₂) e₃)
      (by rw [runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil]), ?_⟩
  -- the state after the setup
  obtain G₃ : ∀ r, r ≠ .r9 → r ≠ t0 → s₃.gpr r = s.gpr r := fun r a b => by rw [g₃ r b, g₂, g₁ r a]
  obtain G₅ : ∀ r, r ≠ .r9 → r ≠ t0 → r ≠ .rdi → s₅.gpr r = s.gpr r := fun r a b c => by
    rw [gpr_arithFlags, g₄ r c, G₃ r a b]
  obtain r9₅ : s₅.gpr .r9 = s.gpr .rcx := by rw [gpr_arithFlags, g₄ _ (by decide), r9₃]
  obtain rdi₅ : s₅.gpr .rdi = S + BitVec.ofNat 64 (keyStart d) := by
    rw [gpr_arithFlags, rdi₄, G₃ _ (by decide) (by decide), keyStart_ext]
  obtain rd₅ : s₅.rd = s.rd := by rw [rd_arithFlags, rd₄, rd₃, rd₂]; rfl
  obtain wr₅ : s₅.wr = s.wr := by rw [wr_arithFlags, wr₄, wr₃, wr₂]; rfl
  obtain mem₅ : s₅.mem = s₃.mem := by rw [mem_arithFlags, m₄]
  obtain slot₅ : ∀ k, slotW s₅ k = slotW s₃ k := fun k => by
    show s₅.mem.readW (Straight.wordAddr (s₅.gpr .r9) k) 64 = s₃.mem.readW (Straight.wordAddr (s₃.gpr .r9) k) 64
    rw [mem₅, r9₅, r9₃]
  obtain scr₅ : scratchR s₅ = ⟨s.gpr .rcx, 8 * scratchSlots⟩ := by simp only [scratchR, r9₅]
  obtain room₅ : Room s₅ := by
    obtain ⟨n, hn, hm⟩ := h.scratch; exact ⟨n, hn, by rw [r9₅, wr₅]; exact hm⟩
  obtain masks₅ : MasksIn s₅ := fun kv hkv => by rw [slot₅]; exact set₃ kv hkv
  obtain f₅ : Frame [⟨s.gpr .rcx, 8 * scratchSlots⟩] s.mem s₅.mem := by
    rw [mem₅, ← scr₁]
    refine f₂.trans ?_
    have : scratchR s₂ = scratchR s₁ := by simp only [scratchR, g₂]
    rw [← this]; exact f₃
  obtain zf₅ : s₅.zf = some (s.gpr .rdx == 0) := by
    rw [zf_arithFlags, g₄ _ (by decide), G₃ _ (by decide) (by decide),
      show s.gpr .rdx - BitVec.signExtend 64 (0 : BitVec 32) = s.gpr .rdx by simp]
  obtain rsi₅ : s₅.gpr .rsi = D := G₅ _ (by decide) (by decide) (by decide)
  obtain rdx₅ : s₅.gpr .rdx = s.gpr .rdx := G₅ _ (by decide) (by decide) (by decide)
  obtain rsp₅ : s₅.gpr .rsp = s.gpr .rsp := G₅ _ (by decide) (by decide) (by decide)
  obtain saved₅ : ∀ p ∈ Impl.Seed.X86_64.savedRegs, slotW s₅ p.2 = s.gpr p.1 := by
    intro p hp
    obtain hp' := savedRegs_ok p hp
    rw [slot₅, keep₃ _ hp'.1 (fun q hq => by have := maskSlots_lt q hq; omega)]
    rw [set₂ (p.2, p.1) (List.mem_map_of_mem hp), g₁ _ hp'.2.1]
  -- the keys, in the schedule
  obtain K₅ : ∀ j < 16, keysAt d s₅.mem (s₅.gpr .rdi) j = keysAt d s.mem (S + BitVec.ofNat 64 (keyStart d)) j := by
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
    obtain r9₆ : s₆.gpr .r9 = s₅.gpr .r9 := p.regs _ (by simp)
    obtain room₆ : Room s₆ := room_congr room₅ r9₆ p.wr
    obtain ⟨s', run', m', set', keep'⟩ := loads_ok room₆ Impl.Seed.X86_64.savedRegs
      (fun q hq => ⟨(savedRegs_ok q hq).1, (savedRegs_ok q hq).2.1⟩) (by decide)
    refine WP.of_runBlock ⟨s', by rw [restore_eq]; exact run', ?_⟩
    have pf := p.frame
    rw [rsi₅] at pf
    obtain frame : Frame [⟨s.gpr .rcx, 8 * scratchSlots⟩, ⟨D, 16 * n⟩] s.mem s'.mem := by
      rw [m']
      refine (f₅.mono (by simp)).trans (pf.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨_, List.mem_cons_self, ?_⟩
        simp only [workR, r9₅]
        exact Region.sub_prefix (by unfold scratchSlots; omega_arith)
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    refine ⟨⟨fun r hr => ?_, ?_⟩, fun b hb => ?_, frame⟩
    · have saved : ∀ q ∈ Impl.Seed.X86_64.savedRegs, s'.gpr q.1 = s.gpr q.1 := by
        intro q hq
        obtain hq' := savedRegs_ok q hq
        rw [set' q hq, ← saved₅ q hq]
        show s₆.mem.readW (Straight.wordAddr (s₆.gpr .r9) q.2) 64 =
          s₅.mem.readW (Straight.wordAddr (s₅.gpr .r9) q.2) 64
        rw [r9₆]
        refine pf.readW (r := ⟨Straight.wordAddr (s₅.gpr .r9) q.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simp only [workR]
          exact Offset.disjoint_base _ (by omega) (by unfold scratchSlots at hq'; omega)
        · rw [r9₅]
          exact (h.dataBuf.sub_right (Offset.sub_base _ (by unfold scratchSlots at hq' ⊢; omega))).symm
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact saved (.rbx, 125) (by decide)
      · exact saved (.rbp, 126) (by decide)
      · rw [keep' .rsp (by decide), p.regs _ (by simp), rsp₅]
      · exact saved (.r12, 127) (by decide)
      · exact saved (.r13, 128) (by decide)
      · exact saved (.r14, 129) (by decide)
      · exact saved (.r15, 130) (by decide)
    · refine frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.retBuf
      · exact h.retData
    · have e := p.done b hb
      rw [rsi₅] at e
      rw [m', e, B₅ b hb, crypt_congr K₅, crypt_keysAt]
  apply WP.seq
  apply WP.ite (s.gpr .rdx == 0) zf₅
  · intro hz
    apply WP.block_nil
    obtain hn0 : n = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz)
      simpa [n] using this
    refine finish s₅ ⟨fun _ _ => rfl, rfl, rfl, fun b hb => by omega_arith, ?_⟩
    rw [hn0]; exact Frame.refl _ _
  · intro hz
    obtain hn1 : 1 ≤ n := by
      have : s.gpr .rdx ≠ 0 := by simpa using hz
      have : (s.gpr .rdx).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
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
      refine ⟨hn1, Nat.le_refl _, ?_, ?_, fun _ _ => rfl, masks₅, rfl, rfl, fun b hb => by omega_arith,
        by rw [Nat.sub_self]; exact Frame.refl _ _⟩
      · rw [rdx₅]; exact BitVec.eq_of_toNat_eq (by simp [n])
      · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add]
    exact WP.mono (loop_ok d E n s₅ I) finish

end VG.Proof.Seed.X86_64
