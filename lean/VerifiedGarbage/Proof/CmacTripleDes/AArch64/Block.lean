import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Spread
import VerifiedGarbage.Proof.CmacTripleDes.Block
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Spill

/-!
# TDEA on AArch64: the passes and the block

`block` encrypts the 64-bit block in `x5` with the key schedule at `x14`
(`block_ok`): it spreads the 48 round keys into the scratch buffer at `x15`
(`spreadLoop_ok`), loads the tables and the constants and applies `IP`,
leaving `L` and `R` spread in `x11` and `x12` (`setup_ok`), runs three passes
of sixteen rounds (`pass_ok`, two rounds per iteration, the spread round
keys from `x10`, moving down in the middle pass, the halves exchanged after
the first two), and applies `IP⁻¹`. Only the scratch buffer's first 384
bytes change.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Straight VG.AArch64.Tbl VG.Bitslice VG.Impl.CmacTripleDes
  VG.Impl.CmacTripleDes.AArch64 VG.Impl.Tbl.AArch64 VG.Proof.CmacTripleDes

theorem ofNat_ne_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x != 0) = !decide (x = 0) := by
  have : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
      simpa using this
    · intro he; rw [he]; rfl
  rw [bne, this]

theorem eval_nonzero {s : State} {r : Reg} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr r = BitVec.ofNat 64 x) :
    isa.eval (.nonzero .x r) s = some !decide (x = 0) := by
  show some (s.read .x r != 0) = _
  rw [State.read, h, BitVec.setWidth_eq, ofNat_ne_zero hx]

theorem eval_zero {s : State} {r : Reg} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr r = BitVec.ofNat 64 x) :
    isa.eval (.zero .x r) s = some (decide (x = 0)) := by
  show some (s.read .x r == 0) = _
  rw [State.read, h, BitVec.setWidth_eq]
  have := ofNat_ne_zero hx
  rw [bne] at this
  cases hb : (BitVec.ofNat 64 x == 0) <;> rw [hb] at this <;> cases hd : decide (x = 0) <;> simp_all


/-- What the block needs: the key schedule at `x14` readable, and the first
456 bytes of the scratch buffer at `x15` writable, apart from it. -/
structure BlockPre (s : State) : Prop where
  sched : ∃ R ∈ s.rd ++ s.wr, R.base = s.gpr .x14 ∧ 384 ≤ R.len ∧ R.len < 2 ^ 64
  scr : ∃ R ∈ s.wr, R.base = s.gpr .x15 ∧ 456 ≤ R.len ∧ R.len < 2 ^ 64
  disj : Region.Disjoint ⟨s.gpr .x15, 456⟩ ⟨s.gpr .x14, 384⟩

/-- The spread round keys' slots. -/
abbrev xR (s₀ : State) : Region := ⟨s₀.gpr .x15, 384⟩

/-- The registers of the functions that the block keeps (with `x14` and `x15`). -/
def outer : List Reg := [.x1, .x2, .x3, .x4]

/-- What the block keeps. -/
structure Same (s₀ s : State) : Prop where
  x15 : s.gpr .x15 = s₀.gpr .x15
  keep : ∀ r ∈ outer, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [xR s₀] s₀.mem s.mem

theorem Same.refl (s : State) : Same s s := ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

/-- The key schedule. -/
abbrev sch (s₀ : State) : Spec.TripleDes.Schedule := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x14)

/-- The spread round keys, in the scratch buffer. -/
def Keys (s₀ : State) (m : Mem) (n : Nat) : Prop :=
  ∀ i < n, m.readW (s₀.gpr .x15 + BitVec.ofNat 64 (8 * i)) 64 = spread ((sch s₀).getD i 0)

theorem BlockPre.slot {s₀ : State} (hp : BlockPre s₀) {s : State} (h : Same s₀ s) {d n : Nat}
    (hd : d + n ≤ 384) : InRegions s.wr (s₀.gpr .x15 + BitVec.ofNat 64 d) n := by
  obtain ⟨X, hX, hXb, hXl, hXw⟩ := hp.scr
  rw [h.wr]
  exact ⟨X, hX, by rw [← hXb]; exact Offset.contains_base _ (by omega) (by omega)⟩

theorem BlockPre.key {s₀ : State} (hp : BlockPre s₀) {s : State} (h : Same s₀ s) {d n : Nat}
    (hd : d + n ≤ 384) : InRegions (s.rd ++ s.wr) (s₀.gpr .x14 + BitVec.ofNat 64 d) n := by
  obtain ⟨R, hR, hRb, hRl, hRw⟩ := hp.sched
  rw [h.rd, h.wr]
  exact ⟨R, hR, by rw [← hRb]; exact Offset.contains_base _ (by omega) (by omega)⟩

/-- The key schedule is unchanged while only the scratch buffer changes. -/
theorem sched_word {s₀ : State} (hp : BlockPre s₀) {m : Mem} (hf : Frame [xR s₀] s₀.mem m) {d : Nat}
    (hd : d + 8 ≤ 384) :
    m.readW (s₀.gpr .x14 + BitVec.ofNat 64 d) 64 = s₀.mem.readW (s₀.gpr .x14 + BitVec.ofNat 64 d) 64 :=
  (hf.readW (r := ⟨s₀.gpr .x14 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((hp.disj.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ hd)).symm)
    (by decide))

theorem ofNat_sub_one {k : Nat} (hk : 1 ≤ k) (hk' : k < 2 ^ 64) :
    BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-! ## Memory -/

theorem vdword_read (m : Mem) (a : Addr) {h : Nat} (hh : h < 2) :
    vdword (m.read a 16) h = m.readW (a + BitVec.ofNat 64 (8 * h)) 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_vdword _ hi, getLsbD_read m 16 a _ (by omega), getLsbD_readW64 _ _ hi,
    BitVec.add_assoc, ← BitVec.ofNat_add, show (64 * h + i) / 8 = 8 * h + i / 8 by omega,
    show (64 * h + i) % 8 = i % 8 by omega]

theorem readW_write16 (m : Mem) (a : Addr) (v : BitVec 128) {h : Nat} (hh : h < 2) :
    (m.write a 16 v).readW (a + BitVec.ofNat 64 (8 * h)) 64 = vdword v h := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_readW64 _ _ hi, getLsbD_vdword _ hi, BitVec.add_assoc, ← BitVec.ofNat_add, Mem.write,
    Mem.sub_ofNat_toNat a (by omega), ite_eq_left (by omega)]
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true, Bool.true_and]
  congr 1; omega

/-! ## Spreading the round keys -/

theorem exec_mov {s : State} {d n : Reg} : exec (mov d n) s = some (s.write .x d (s.gpr n)) := by
  rw [mov, exec_addImm_x (by decide)]
  simp [State.read]

theorem exec_movz_x {s : State} {d : Reg} {imm : BitVec 16} {hw : Nat} (h : hw < 4) :
    exec (.movz .x d imm hw) s = some (s.write .x d (imm.setWidth 64 <<< (16 * hw))) := by
  simp only [exec, Size.bits, show 16 * hw < 64 by omega, ite_true]

theorem exec_dupd (s : State) (d : VReg) (n : Reg) :
    exec (.vop (.dup .d2 d n)) s = some (s.setV d (ofVDwords (s.gpr n) (s.gpr n))) := rfl

/-- After `m` pairs of keys. -/
structure SInv (s₀ : State) (m : Nat) (s : State) : Prop where
  same : Same s₀ s
  x5 : s.gpr .x5 = s₀.gpr .x5
  x14 : s.gpr .x14 = s₀.gpr .x14
  x6 : s.gpr .x6 = s₀.gpr .x14 + BitVec.ofNat 64 (16 * m)
  x7 : s.gpr .x7 = s₀.gpr .x15 + BitVec.ofNat 64 (16 * m)
  x16 : s.gpr .x16 = BitVec.ofNat 64 (24 - m)
  g : s.v .v5 = ofVBytes gatherIndex
  c63 : s.v .v6 = bc 63
  off : s.v .v7 = ofVDwords offsets offsets
  keys : Keys s₀ s.mem (2 * m)

theorem spreadPre_eq : spreadPre = const128 .v5 (ofVBytes gatherIndex) ++
    (([.movz .x .x6 63 0, .vop (.dup .b16 .v6 .x6)] : List Instr) ++ (const64 .x6 offsets ++
      ([.vop (.dup .d2 .v7 .x6), mov .x6 .x14, mov .x7 .x15, .movz .x .x16 24 0] : List Instr))) := by
  simp only [spreadPre, List.append_assoc]

theorem spreadPre_ok (s₀ : State) : WP isa (.block spreadPre) s₀ (SInv s₀ 0) := by
  rw [spreadPre_eq, WP.block_append_iff]
  refine WP.mono (const128_ok s₀ .v5 _) fun a ⟨a5, av, ag, am, ard, awr, asp⟩ => ?_
  rw [WP.block_append_iff]
  let b := (a.write .x .x6 ((63 : BitVec 16).setWidth 64 <<< (16 * 0)))
  let b' := b.setV .v6 (bc ((b.gpr .x6).setWidth 8))
  refine WP.of_runBlock ⟨b', by
    rw [runBlock_cons, exec_movz_x (by decide), runStep_some, runBlock_cons, exec_dupb, runStep_some,
      runBlock_nil], ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok b' .x6 offsets) fun c ⟨c6, cg, ce⟩ => ?_
  let d₁ := c.setV .v7 (ofVDwords (c.gpr .x6) (c.gpr .x6))
  let d₂ := d₁.write .x .x6 (d₁.gpr .x14)
  let d₃ := d₂.write .x .x7 (d₂.gpr .x15)
  let d₄ := d₃.write .x .x16 ((24 : BitVec 16).setWidth 64 <<< (16 * 0))
  refine WP.of_runBlock ⟨d₄, by
    rw [runBlock_cons, exec_dupd, runStep_some, runBlock_cons, exec_mov, runStep_some, runBlock_cons,
      exec_mov, runStep_some, runBlock_cons, exec_movz_x (by decide), runStep_some, runBlock_nil], ?_⟩
  have cv : c.v = b'.v := by rw [ce]
  have cmem : c.mem = s₀.mem := by rw [ce]; exact am
  have g14 : c.gpr .x14 = s₀.gpr .x14 := by
    rw [cg .x14 (by decide)]; simp only [b', b, gpr_setV, gpr_write_of_ne _ _ _ (by decide : Reg.x14 ≠ .x6)]
    exact ag .x14 (by decide) (by decide)
  have g15 : c.gpr .x15 = s₀.gpr .x15 := by
    rw [cg .x15 (by decide)]; simp only [b', b, gpr_setV, gpr_write_of_ne _ _ _ (by decide : Reg.x15 ≠ .x6)]
    exact ag .x15 (by decide) (by decide)
  have gout : ∀ r ∈ outer, c.gpr r = s₀.gpr r := by
    intro r hr
    have h6 : r ≠ .x6 := by simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h7 : r ≠ .x7 := by simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [cg r h6]; simp only [b', b, gpr_setV, gpr_write_of_ne _ _ _ h6]; exact ag r h6 h7
  refine ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega)⟩
  · simp only [d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ (by decide : Reg.x15 ≠ .x16),
      gpr_write_of_ne _ _ _ (by decide : Reg.x15 ≠ .x7), gpr_write_of_ne _ _ _ (by decide : Reg.x15 ≠ .x6),
      gpr_setV, g15]
  · have h6 : r ≠ .x6 := by simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h7 : r ≠ .x7 := by simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h16 : r ≠ .x16 := by simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    simp only [d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ h16, gpr_write_of_ne _ _ _ h7,
      gpr_write_of_ne _ _ _ h6, gpr_setV, gout r hr]
  · simp only [d₄, d₃, d₂, d₁, sp_write, sp_setV]; rw [ce]; simp only [b', b, sp_setV, sp_write, asp]
  · simp only [d₄, d₃, d₂, d₁, rd_write, rd_setV]; rw [ce]; simp only [b', b, rd_setV, rd_write, ard]
  · simp only [d₄, d₃, d₂, d₁, wr_write, wr_setV]; rw [ce]; simp only [b', b, wr_setV, wr_write, awr]
  · simp only [d₄, d₃, d₂, d₁, mem_write, mem_setV, cmem]; exact Frame.refl _ _
  · simp only [d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x16),
      gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x7), gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x6),
      gpr_setV]
    rw [cg .x5 (by decide)]; simp only [b', b, gpr_setV, gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x6)]
    exact ag .x5 (by decide) (by decide)
  · simp only [d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ (by decide : Reg.x14 ≠ .x16),
      gpr_write_of_ne _ _ _ (by decide : Reg.x14 ≠ .x7), gpr_write_of_ne _ _ _ (by decide : Reg.x14 ≠ .x6),
      gpr_setV, g14]
  · simp only [d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ (by decide : Reg.x6 ≠ .x16),
      gpr_write_of_ne _ _ _ (by decide : Reg.x6 ≠ .x7), gpr_write_self, BitVec.setWidth_eq, gpr_setV, g14]
    simp
  · simp only [d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ (by decide : Reg.x7 ≠ .x16), gpr_write_self,
      BitVec.setWidth_eq, gpr_write_of_ne _ _ _ (by decide : Reg.x15 ≠ .x6), gpr_setV, g15]
    simp
  · simp only [d₄, gpr_write_self, BitVec.setWidth_eq]; decide
  · simp only [d₄, d₃, d₂, d₁, v_write, v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v7), cv, b',
      v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v6), b, v_write, a5]
  · simp only [d₄, d₃, d₂, d₁, v_write, v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v7), cv, b',
      v_setV_self, b, gpr_write_self, BitVec.setWidth_eq]
    rfl
  · simp only [d₄, d₃, d₂, d₁, v_write, v_setV_self, c6]

theorem spreadBody_eq : spreadBody = ([.ldrq .v0 .x6 0] : List Instr) ++ spreadV ++
    ([.strq .v4 .x7 0, .addImm .x .x6 .x6 16, .addImm .x .x7 .x7 16, .subImm .x .x16 .x16 1] : List Instr) :=
  rfl

theorem exec_ldrq0 (s : State) (t : VReg) (n : Reg) (h : InRegions (s.rd ++ s.wr) (s.gpr n) 16) :
    exec (.ldrq t n 0) s = some (s.setV t (s.mem.read (s.gpr n) 16)) := by
  simp only [exec, addr, show 0 % 16 = 0 from rfl, show 0 < 4096 * 16 by decide, and_self, ite_true,
    BitVec.add_zero, Option.bind_some, State.load, h, Option.map_some]

theorem exec_strq0 (s : State) (t : VReg) (n : Reg) (h : InRegions s.wr (s.gpr n) 16) :
    exec (.strq t n 0) s = some { s with mem := s.mem.write (s.gpr n) 16 (s.v t) } := by
  simp only [exec, addr, show 0 % 16 = 0 from rfl, show 0 < 4096 * 16 by decide, and_self, ite_true,
    BitVec.add_zero, Option.bind_some, State.store, h]

theorem spreadStep_ok {s₀ : State} (hp : BlockPre s₀) {m : Nat} (hm : m < 24) {s : State}
    (h : SInv s₀ m s) : WP isa (.block spreadBody) s (SInv s₀ (m + 1)) := by
  rw [spreadBody_eq, WP.block_append_iff, WP.block_append_iff]
  have rk : InRegions (s.rd ++ s.wr) (s.gpr .x6) 16 := by
    rw [h.x6]; exact hp.key h.same (by omega)
  let s₁ := s.setV .v0 (s.mem.read (s.gpr .x6) 16)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, exec_ldrq0 _ _ _ rk, runStep_some, runBlock_nil], ?_⟩
  obtain ⟨s₂, h₂, v4₂, v₂, e₂⟩ := spreadV_ok s₁
    (by simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v0), h.g])
    (by simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v0), h.c63])
    (by simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v7 ≠ .v0), h.off])
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  have g₂ : s₂.gpr = s.gpr := by rw [e₂]; rfl
  have m₂ : s₂.mem = s.mem := by rw [e₂]; rfl
  have wr₂ : s₂.wr = s.wr := by rw [e₂]; rfl
  have rd₂ : s₂.rd = s.rd := by rw [e₂]; rfl
  have sp₂ : s₂.sp = s.sp := by rw [e₂]; rfl
  have ws : InRegions s₂.wr (s₂.gpr .x7) 16 := by
    rw [wr₂, g₂, h.x7]; exact hp.slot h.same (by omega)
  let V := s₂.v .v4
  let s₃ : State := { s₂ with mem := s₂.mem.write (s₂.gpr .x7) 16 V }
  let s₄ := s₃.write .x .x6 (s₃.read .x .x6 + BitVec.ofNat _ 16)
  let s₅ := s₄.write .x .x7 (s₄.read .x .x7 + BitVec.ofNat _ 16)
  let s₆ := s₅.write .x .x16 (s₅.read .x .x16 - BitVec.ofNat _ 1)
  refine WP.of_runBlock ⟨s₆, by
    rw [runBlock_cons, exec_strq0 _ _ _ ws, runStep_some, runBlock_cons, exec_addImm_x (by decide),
      runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  have g₆ : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x16 → s₆.gpr r = s.gpr r := by
    intro r h6 h7 h16
    simp only [s₆, s₅, s₄, gpr_write_of_ne _ _ _ h16, gpr_write_of_ne _ _ _ h7, gpr_write_of_ne _ _ _ h6]
    show s₂.gpr r = s.gpr r
    rw [g₂]
  have v₆ : s₆.v = s₂.v := rfl
  have mem₆ : s₆.mem = s.mem.write (s₀.gpr .x15 + BitVec.ofNat 64 (16 * m)) 16 V := by
    show s₂.mem.write (s₂.gpr .x7) 16 V = _
    rw [m₂, g₂, h.x7]
  have hK : ∀ hh < 2, vdword (s₁.v .v0) hh = (sch s₀).getD (2 * m + hh) 0 := by
    intro hh hh2
    rw [show s₁.v .v0 = s.mem.read (s.gpr .x6) 16 from v_setV_self _ _ _, vdword_read _ _ hh2, h.x6,
      Offset.add_add, scheduleAt_getD _ _ (by omega),
      show 16 * m + 8 * hh = 8 * (2 * m + hh) by omega]
    exact sched_word hp h.same.frame (by omega)
  have outer_ne : ∀ r ∈ outer, r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x16 := by
    intro r hr; simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  refine ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₆ _ (by decide) (by decide) (by decide), h.same.x15]
  · obtain ⟨a, b, c⟩ := outer_ne r hr
    rw [g₆ r a b c, h.same.keep r hr]
  · show s₂.sp = _; rw [sp₂, h.same.sp]
  · show s₂.rd = _; rw [rd₂, h.same.rd]
  · show s₂.wr = _; rw [wr₂, h.same.wr]
  · rw [mem₆]
    exact h.same.frame.write (r := xR s₀) (by simp) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [g₆ _ (by decide) (by decide) (by decide), h.x5]
  · rw [g₆ _ (by decide) (by decide) (by decide), h.x14]
  · simp only [s₆, s₅, s₄, gpr_write_of_ne _ _ _ (by decide : Reg.x6 ≠ .x16),
      gpr_write_of_ne _ _ _ (by decide : Reg.x6 ≠ .x7), gpr_write_self, State.read,
      BitVec.setWidth_eq]
    show s₂.gpr .x6 + _ = _
    rw [g₂, h.x6, Offset.add_add, show 16 * m + 16 = 16 * (m + 1) by omega]
  · simp only [s₆, s₅, gpr_write_of_ne _ _ _ (by decide : Reg.x7 ≠ .x16), gpr_write_self, State.read,
      BitVec.setWidth_eq, s₄, gpr_write_of_ne _ _ _ (by decide : Reg.x7 ≠ .x6)]
    show s₂.gpr .x7 + _ = _
    rw [g₂, h.x7, Offset.add_add, show 16 * m + 16 = 16 * (m + 1) by omega]
  · simp only [s₆, gpr_write_self, State.read, BitVec.setWidth_eq, s₅,
      gpr_write_of_ne _ _ _ (by decide : Reg.x16 ≠ .x7), s₄, gpr_write_of_ne _ _ _ (by decide : Reg.x16 ≠ .x6)]
    show s₂.gpr .x16 - _ = _
    rw [g₂, h.x16]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Size.bits]
    omega
  · rw [v₆, v₂ _ (by decide) (by decide) (by decide) (by decide)]
    simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v0), h.g]
  · rw [v₆, v₂ _ (by decide) (by decide) (by decide) (by decide)]
    simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v0), h.c63]
  · rw [v₆, v₂ _ (by decide) (by decide) (by decide) (by decide)]
    simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v7 ≠ .v0), h.off]
  · intro i hi
    rw [mem₆]
    by_cases hnew : 2 * m ≤ i
    · have hh : i - 2 * m < 2 := by omega
      rw [show s₀.gpr .x15 + BitVec.ofNat 64 (8 * i) =
          s₀.gpr .x15 + BitVec.ofNat 64 (16 * m) + BitVec.ofNat 64 (8 * (i - 2 * m)) by
          rw [Offset.add_add]; congr 2; omega,
        readW_write16 _ _ _ hh]
      show vdword (s₂.v .v4) _ = _
      have hK' : vdword (s₁.v .v0) (i - 2 * m) = (sch s₀).getD i 0 := by
        rw [hK _ hh, show 2 * m + (i - 2 * m) = i by omega]
      rw [v4₂, ← hK']
      rcases (by omega : i - 2 * m = 0 ∨ i - 2 * m = 1) with e | e <;> rw [e]
      · rw [vdword_ofVDwords_0]
      · rw [vdword_ofVDwords_1]
    · have hsep : Mem.Sep (s₀.gpr .x15 + BitVec.ofNat 64 (8 * i)) 8
          (s₀.gpr .x15 + BitVec.ofNat 64 (16 * m)) 16 :=
        Offset.sep _ (by omega) (by omega) (by omega)
      rw [Mem.readW, Mem.read_write_sep hsep (by decide)]
      exact h.keys i (by omega)

theorem spreadLoop_ok {s₀ : State} (hp : BlockPre s₀) {s : State} (h : SInv s₀ 0 s) :
    WP isa (.loop (.block spreadBody) (.nonzero .x .x16)) s (SInv s₀ 24) := by
  refine WP.loop (M := isa) (body := .block spreadBody) (c := .nonzero .x .x16) (Q := SInv s₀ 24)
    (fun (n : Nat) (t : State) => ∃ m, n = 24 - m ∧ m < 24 ∧ SInv s₀ m t) ?_ 24 _ ⟨0, rfl, by decide, h⟩
  rintro n t ⟨m, rfl, hm, ht⟩
  refine WP.mono (spreadStep_ok hp hm ht) fun t' h' => ?_
  have ev := eval_nonzero (r := .x16) (x := 24 - (m + 1)) (by omega) h'.x16
  by_cases hz : m + 1 = 24
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [ev]; simp; omega, 24 - (m + 1), by omega, m + 1, rfl, by omega, h'⟩

/-! ## `IP` and `IP⁻¹` -/

/-- No memory. -/
theorem ipSrc_lt : ∀ j < 64, ipSrc j < 64 := by lit_decide

theorem fpSrc_lt : ∀ j < 64, fpSrc j < 64 := by lit_decide

/-- `IP`'s halves, rotated and spread, into `x11` and `x12`, from `x5` (input word 0). -/
def ipG11 (p : Nat) : List Nat := if xBit p then [ipSrc (32 + (xSrc p + 32 - rot) % 32)] else []
def ipG12 (p : Nat) : List Nat := if xBit p then [ipSrc ((xSrc p + 32 - rot) % 32)] else []

theorem ip_check :
    check (lanes 64 6) oCfg (linExt 1) ipCode (linEnv [(.x5, 0)])
      (linPost 6 [(.x11, ipG11), (.x12, ipG12)]) = true := by
  lit_decide

/-- `IP⁻¹(R ‖ L)` into `x5`, from `R` spread in `x12` (input word 0) and `L`
spread in `x11` (input word 1). -/
def fpG (j : Nat) : List Nat :=
  if 32 ≤ fpSrc j then [xPos ((fpSrc j - 32 + rot) % 32)] else [64 + xPos ((fpSrc j + rot) % 32)]

theorem fp_check :
    check (lanes 64 7) oCfg (linExt 2) fpCode (linEnv [(.x12, 0), (.x11, 1)]) (linPost 7 [(.x5, fpG)]) = true := by
  lit_decide

def blockKept : List Reg := [.x1, .x2, .x3, .x4, .x10, .x14, .x15]

theorem ip_kept : blockKept.all (fun r => ipCode.all fun i => dstOf i != some r) = true := by lit_decide

theorem fp_kept : blockKept.all (fun r => fpCode.all fun i => dstOf i != some r) = true := by lit_decide

theorem ip_v : ipCode.all (fun i => vdstOf i == none) = true := by lit_decide

theorem ip_masks : maskConsts.all (fun p => ipCode.all fun i => dstOf i != some p.1) = true := by
  lit_decide

theorem xPos_facts : ∀ e < 32, xPos e < 64 ∧ xBit (xPos e) = true ∧ xSrc (xPos e) = e := by decide

theorem ip_ok (s : State) :
    ∃ s', runBlock isa ipCode s = some s' ∧
      s'.gpr .x11 = spreadW (split (Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .x5))).1 ∧
      s'.gpr .x12 = spreadW (split (Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .x5))).2 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ blockKept, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.v = s.v ∧ (∀ p ∈ maskConsts, s'.gpr p.1 = s.gpr p.1) := by
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok ip_check (oCfg_ok s) (fun _ => s.gpr .x5)
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      obtain ⟨rfl, rfl⟩ := hri; exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  refine ⟨s', hs', ?_, ?_, hrd, hwr, hsp, fun r hr => hoth r (List.all_eq_true.mp ip_kept r hr),
    frame_oCfg hfr, runBlock_v ip_v hs', fun p hp => hoth p.1 (List.all_eq_true.mp ip_masks p hp)⟩
  · apply BitVec.eq_of_getLsbD_eq; intro p hp
    have hj := xSrc_rot_lt p hp
    rw [hout .x11 ipG11 (by simp) p hp, getLsbD_spreadW _ hp, ipG11]
    cases hx : xBit p
    · simp
    · have hs := ipSrc_lt (32 + (xSrc p + 32 - rot) % 32) (by omega)
      simp only [ite_true, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, Nat.mod_eq_of_lt hs,
        Bool.true_and, split, BitVec.getLsbD_setWidth, decide_eq_true hj,
        BitVec.getLsbD_ushiftRight]
      rw [getLsbD_permute _ _ (by decide) (show 32 + (xSrc p + 32 - rot) % 32 < 64 by omega)]
      rfl
  · apply BitVec.eq_of_getLsbD_eq; intro p hp
    have hj := xSrc_rot_lt p hp
    rw [hout .x12 ipG12 (by simp) p hp, getLsbD_spreadW _ hp, ipG12]
    cases hx : xBit p
    · simp
    · have hs := ipSrc_lt ((xSrc p + 32 - rot) % 32) (by omega)
      simp only [ite_true, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, Nat.mod_eq_of_lt hs,
        Bool.true_and, split, BitVec.getLsbD_setWidth, decide_eq_true hj]
      rw [getLsbD_permute _ _ (by decide) (show (xSrc p + 32 - rot) % 32 < 64 by omega)]
      rfl

theorem spreadW_xPos (w : BitVec 32) {k : Nat} (hk : k < 32) :
    (spreadW w).getLsbD (xPos ((k + rot) % 32)) = w.getLsbD k := by
  obtain ⟨h64, hx, hs⟩ := xPos_facts ((k + rot) % 32) (by omega)
  rw [getLsbD_spreadW _ h64, hx, hs, Bool.true_and]
  congr 1; simp only [rot]; omega

theorem fp_ok (s : State) {l r : BitVec 32} (hl : s.gpr .x11 = spreadW l) (hr : s.gpr .x12 = spreadW r) :
    ∃ s', runBlock isa fpCode s = some s' ∧
      s'.gpr .x5 = Spec.TripleDes.permute Spec.TripleDes.fp (r ++ l) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ blockKept, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem := by
  let W : Nat → BitVec 64 := fun i => if i = 0 then s.gpr .x12 else s.gpr .x11
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok fp_check (oCfg_ok s) W
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  refine ⟨s', hs', ?_, hrd, hwr, hsp, fun r hr => hoth r (List.all_eq_true.mp fp_kept r hr), frame_oCfg hfr⟩
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hs := fpSrc_lt j hj
  rw [hout .x5 fpG (by simp) j hj, getLsbD_permute _ _ (by decide) hj, BitVec.getLsbD_append,
    show 64 - Spec.TripleDes.fp.getD (64 - 1 - j) 1 = fpSrc j from rfl, fpG]
  by_cases h32 : 32 ≤ fpSrc j
  · obtain ⟨h64, -, -⟩ := xPos_facts ((fpSrc j - 32 + rot) % 32) (by omega)
    rw [ite_eq_left h32, ite_eq_right (by omega)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, Nat.div_eq_of_lt h64,
      Nat.mod_eq_of_lt h64, W, ite_true, hr]
    exact spreadW_xPos r (by omega)
  · obtain ⟨h64, -, -⟩ := xPos_facts ((fpSrc j + rot) % 32) (by omega)
    rw [ite_eq_right h32, ite_eq_left (by omega)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf,
      show (64 + xPos ((fpSrc j + rot) % 32)) / 64 = 1 by omega,
      show (64 + xPos ((fpSrc j + rot) % 32)) % 64 = xPos ((fpSrc j + rot) % 32) by omega, W,
      show (1 : Nat) ≠ 0 by decide, ite_false, hl]
    exact spreadW_xPos l (by omega)

/-! ## The setup -/

/-- The key schedule's slot before round `j` of pass `p`. -/
def kpos (p j : Nat) : Nat := if p % 2 = 1 then 16 * p + 15 - j else 16 * p + j

theorem kpos_lt {p j : Nat} (hp : p < 3) (hj : j < 16) : kpos p j < 48 := by
  simp only [kpos]; split <;> omega

/-- Before pass `p`, from the block `x`. -/
structure OInv (s₀ : State) (x : BitVec 64) (p : Nat) (s : State) : Prop where
  same : Same s₀ s
  x14 : s.gpr .x14 = s₀.gpr .x14
  x10 : s.gpr .x10 = s₀.gpr .x15 + BitVec.ofNat 64 (8 * kpos p 0)
  consts : Consts s
  masks : Masks s
  keys : Keys s₀ s.mem 48
  l : s.gpr .x11 = spreadW (passes (sch s₀) p (split (Spec.TripleDes.permute Spec.TripleDes.ip x))).1
  r : s.gpr .x12 = spreadW (passes (sch s₀) p (split (Spec.TripleDes.permute Spec.TripleDes.ip x))).2

theorem quarterConsts_ok (s : State) :
    ∃ s', runBlock isa quarterConsts s = some s' ∧ s'.v .v4 = bc 64 ∧ s'.v .v5 = bc 128 ∧
      s'.v .v6 = bc 192 ∧ (∀ w, w ≠ .v4 → w ≠ .v5 → w ≠ .v6 → s'.v w = s.v w) ∧
      (∀ r, r ≠ .x6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  refine ⟨_, rfl, ?_, ?_, ?_, fun w h4 h5 h6 => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v6), v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v5),
      v_setV_self, gpr_write_self, v_write, BitVec.setWidth_eq]
    rfl
  · simp only [v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v6), v_setV_self, gpr_write_self,
      v_write, BitVec.setWidth_eq]
    rfl
  · simp only [v_setV_self, gpr_write_self, BitVec.setWidth_eq]
    rfl
  · simp only [v_setV_of_ne _ _ h6, v_setV_of_ne _ _ h5, v_setV_of_ne _ _ h4, v_write]
  · simp only [gpr_setV, gpr_write_of_ne _ _ _ hr]

theorem maskSet_check :
    check (lanes 64 7) oCfg (linExt 2) maskSet (linEnv [])
      (fun e => maskConsts.all fun p => e.cst p.1 == some p.2) = true := by
  lit_decide

/-- The registers the masks' setup keeps. -/
def maskKept : List Reg := [.x1, .x2, .x3, .x4, .x5, .x14, .x15]

theorem maskSet_keeps : maskKept.all (fun r => maskSet.all fun i => dstOf i != some r) = true := by
  lit_decide

theorem maskSet_v : maskSet.all (fun i => vdstOf i == none) = true := by lit_decide

theorem maskSet_ok (s : State) :
    ∃ s', runBlock isa maskSet s = some s' ∧ Masks s' ∧ (∀ r ∈ maskKept, s'.gpr r = s.gpr r) ∧
      s'.v = s.v ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ maskSet_check
  have hrel : Rel (LaneRel 7 0) oCfg (linExt 2) (linEnv []) s :=
    ⟨fun r a h => (by simp [linEnv] at h), fun _ _ _ h => (by cases h),
      fun j _ hj _ => absurd hj (by simp [oCfg]), fun _ _ h => (by cases h)⟩
  obtain ⟨s', hs', p⟩ := run lanes_sound (oCfg_ok s) hrel he
  refine ⟨s', hs', fun r v hp => p.rel.cst r v ?_, fun r hr => p.other r fun h => ?_,
    runBlock_v maskSet_v hs', frame_oCfg p.frame, p.rd, p.wr, p.sp⟩
  · have := List.all_eq_true.mp hpost (r, v) hp
    simpa using this
  · rw [List.all_eq_true.mp maskSet_keeps r hr] at h; cases h

theorem setup_eq : setup = loadTable sTable ++ (quarterConsts ++ (maskSet ++
    (ipCode ++ ([mov .x10 .x15] : List Instr)))) := by
  simp only [setup, List.append_assoc]

theorem setup_ok {s₀ : State} {s : State} (h : SInv s₀ 24 s) :
    WP isa (.block setup) s (OInv s₀ (s₀.gpr .x5) 0) := by
  rw [setup_eq, WP.block_append_iff]
  refine WP.mono (loadTable_ok s sTable) fun a ⟨atab, av, ag, am, ard, awr, asp⟩ => ?_
  rw [WP.block_append_iff]
  obtain ⟨b₀, hb, b4, b5, b6, bv₀, bg₀, bm₀, brd₀, bwr₀, bsp₀⟩ := quarterConsts_ok a
  refine WP.of_runBlock ⟨b₀, hb, ?_⟩
  rw [WP.block_append_iff]
  obtain ⟨b, hbm, bmask, bk, bvv, bm₁, brd₁, bwr₁, bsp₁⟩ := maskSet_ok b₀
  refine WP.of_runBlock ⟨b, hbm, ?_⟩
  rw [WP.block_append_iff]
  have bv : ∀ w, w ≠ .v4 → w ≠ .v5 → w ≠ .v6 → b.v w = a.v w := fun w h4 h5 h6 => by
    rw [bvv]; exact bv₀ w h4 h5 h6
  have bg : ∀ r ∈ maskKept, r ≠ .x6 → b.gpr r = a.gpr r := fun r hr h6 => by
    rw [bk r hr]; exact bg₀ r h6
  have bm : b.mem = a.mem := by rw [bm₁, bm₀]
  have brd : b.rd = a.rd := by rw [brd₁, brd₀]
  have bwr : b.wr = a.wr := by rw [bwr₁, bwr₀]
  have bsp : b.sp = a.sp := by rw [bsp₁, bsp₀]
  replace b4 : b.v .v4 = bc 64 := by rw [bvv]; exact b4
  replace b5 : b.v .v5 = bc 128 := by rw [bvv]; exact b5
  replace b6 : b.v .v6 = bc 192 := by rw [bvv]; exact b6
  obtain ⟨c, hc, c11, c12, crd, cwr, csp, ck, cm, cv, cmask⟩ := ip_ok b
  refine WP.of_runBlock ⟨c, hc, ?_⟩
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_mov, runStep_some, runBlock_nil], ?_⟩
  have g : ∀ r ∈ maskKept, r ≠ .x6 → r ≠ .x7 → b.gpr r = s.gpr r := fun r hr h6 h7 => by
    rw [bg r hr h6, ag r h6 h7]
  have hc' : Consts c := by
    refine ⟨fun k hk => ?_, by rw [cv, b4], by rw [cv, b5], by rw [cv, b6]⟩
    rw [cv, tbyte_congr' (fun t ht => ?_) k hk, atab k hk]
    obtain ⟨-, -, -, -, h4, h5, h6, -⟩ := treg_ne8 t ht
    exact bv _ h4 h5 h6
  have x15c : c.gpr .x15 = s₀.gpr .x15 := by
    rw [ck .x15 (by simp [blockKept]), g _ (by simp [maskKept]) (by decide) (by decide), h.same.x15]
  refine ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, hc'.congr (fun _ _ _ _ _ => rfl), ?_, ?_, ?_, ?_⟩
  · rw [gpr_write_of_ne _ _ _ (by decide), x15c]
  · have hk : r ∈ blockKept := by
      simp only [outer, blockKept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    have h6 : r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x10 := by
      simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have hm : r ∈ maskKept := by
      simp only [outer, maskKept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    rw [gpr_write_of_ne _ _ _ h6.2.2, ck r hk, g r hm h6.1 h6.2.1, h.same.keep r hr]
  · rw [sp_write, csp, bsp, asp, h.same.sp]
  · rw [rd_write, crd, brd, ard, h.same.rd]
  · rw [wr_write, cwr, bwr, awr, h.same.wr]
  · rw [mem_write, cm, bm, am]; exact h.same.frame
  · rw [gpr_write_of_ne _ _ _ (by decide), ck .x14 (by simp [blockKept]), g _ (by simp [maskKept]) (by decide) (by decide),
      h.x14]
  · rw [gpr_write_self, BitVec.setWidth_eq, x15c]
    simp [kpos]
  · exact bmask.congr fun p hp => by
      rw [gpr_write_of_ne _ _ _ (maskRegs_ne p hp).2.1, cmask p hp]
  · rw [mem_write, cm, bm, am]
    exact h.keys
  · rw [gpr_write_of_ne _ _ _ (by decide), c11, g _ (by simp [maskKept]) (by decide) (by decide), h.x5]
    rfl
  · rw [gpr_write_of_ne _ _ _ (by decide), c12, g _ (by simp [maskKept]) (by decide) (by decide), h.x5]
    rfl

/-! ## The passes -/

/-- After `j` pairs of rounds of pass `p`, from the halves `lr`. -/
structure PInv (s₀ : State) (p : Nat) (lr : BitVec 32 × BitVec 32) (j : Nat) (s : State) : Prop where
  same : Same s₀ s
  x14 : s.gpr .x14 = s₀.gpr .x14
  x10 : s.gpr .x10 = s₀.gpr .x15 + BitVec.ofNat 64 (8 * kpos p (2 * j))
  x16 : s.gpr .x16 = BitVec.ofNat 64 (8 - j)
  consts : Consts s
  masks : Masks s
  keys : Keys s₀ s.mem 48
  l : s.gpr .x11 = spreadW (rounds (passKeys (sch s₀) p) (2 * j) lr).1
  r : s.gpr .x12 = spreadW (rounds (passKeys (sch s₀) p) (2 * j) lr).2

/-- The pass moves down the keys. -/
def downOf (p : Nat) : Bool := p % 2 == 1

theorem kpos_step (a : Addr) {p i : Nat} (hp : p < 3) (hi : i < 16) :
    (if downOf p then a + BitVec.ofNat 64 (8 * kpos p i) - 8 else a + BitVec.ofNat 64 (8 * kpos p i) + 8) =
      a + BitVec.ofNat 64 (8 * kpos p (i + 1)) := by
  simp only [downOf, kpos]
  by_cases h : p % 2 = 1
  · simp only [h, beq_self_eq_true, ite_true]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · simp only [h, ite_false, show (p % 2 == 1) = false by simp [h], Bool.false_eq_true]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

theorem passKeys_at (s₀ : State) {p j : Nat} (hj : j < 16) :
    passKeys (sch s₀) p j = ((sch s₀).getD (kpos p j) 0).setWidth 48 := by
  rw [passKeys_eq _ hj, kpos]
  by_cases h : p % 2 = 1
  · rw [ite_eq_left h, ite_eq_left h, show 16 * p + (15 - j) = 16 * p + 15 - j by omega]
  · rw [ite_eq_right h, ite_eq_right h]

theorem outer_ne {r : Reg} (h : r ∈ outer) :
    r ≠ .x5 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x16 := by
  simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem pairBody_eq (down : Bool) :
    (round .x11 .x12 down ++ round .x12 .x11 down ++ ([.subImm .x .x16 .x16 1] : List Instr)) =
      round .x11 .x12 down ++ (round .x12 .x11 down ++ ([.subImm .x .x16 .x16 1] : List Instr)) := by
  simp only [List.append_assoc]

/-- Two rounds of pass `p`. -/
theorem pairStep_ok {s₀ : State} (hp : BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {j : Nat} (hj : j < 8) {s : State} (h : PInv s₀ p lr j s) :
    WP isa (.block (round .x11 .x12 (downOf p) ++ round .x12 .x11 (downOf p) ++
      ([.subImm .x .x16 .x16 1] : List Instr))) s (PInv s₀ p lr (j + 1)) := by
  rw [pairBody_eq, WP.block_append_iff]
  have slot : ∀ {t : State}, Same s₀ t → ∀ i < 48,
      InRegions (t.rd ++ t.wr) (s₀.gpr .x15 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro t ht i hi
    obtain ⟨R, hR, hc⟩ := hp.slot ht (d := 8 * i) (n := 8) (by omega)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  have k0 := kpos_lt hp3 (show 2 * j < 16 by omega)
  have k1 := kpos_lt hp3 (show 2 * j + 1 < 16 by omega)
  obtain ⟨s₁, h₁, a₁, x10₁, g₁, c₁, mk₁, m₁, rd₁, wr₁, sp₁⟩ := round_ok (Or.inl ⟨rfl, rfl⟩) (downOf p)
    h.consts h.masks (by rw [h.x10]; exact slot h.same _ k0) h.l h.r
    (by rw [h.x10]; exact h.keys _ k0)
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  rw [WP.block_append_iff]
  have same₁ : Same s₀ s₁ := ⟨by rw [g₁ .x15 (by simp), h.same.x15],
    fun r hr => by rw [g₁ r (by simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl <;> simp), h.same.keep r hr],
    by rw [sp₁, h.same.sp], by rw [rd₁, h.same.rd], by rw [wr₁, h.same.wr], by rw [m₁]; exact h.same.frame⟩
  have x10₁' : s₁.gpr .x10 = s₀.gpr .x15 + BitVec.ofNat 64 (8 * kpos p (2 * j + 1)) := by
    rw [x10₁, h.x10, kpos_step _ hp3 (by omega)]
  obtain ⟨s₂, h₂, a₂, x10₂, g₂, c₂, mk₂, m₂, rd₂, wr₂, sp₂⟩ := round_ok (Or.inr ⟨rfl, rfl⟩) (downOf p)
    c₁ mk₁ (by rw [x10₁']; exact slot same₁ _ k1) (by rw [g₁ .x12 (by simp), h.r]) a₁
    (by rw [x10₁', m₁]; exact h.keys _ k1)
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  have hr₁ := rounds_succ (passKeys (sch s₀) p) (2 * j) lr
  have hr₂ := rounds_succ (passKeys (sch s₀) p) (2 * j + 1) lr
  refine ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gpr_write_of_ne _ _ _ (by decide), g₂ .x15 (by simp), same₁.x15]
  · rw [gpr_write_of_ne _ _ _ (outer_ne hr).2.2.2.2, g₂ r (by
      simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp), same₁.keep r hr]
  · rw [sp_write, sp₂, same₁.sp]
  · rw [rd_write, rd₂, same₁.rd]
  · rw [wr_write, wr₂, same₁.wr]
  · rw [mem_write, m₂]; exact same₁.frame
  · rw [gpr_write_of_ne _ _ _ (by decide), g₂ .x14 (by simp), g₁ .x14 (by simp), h.x14]
  · rw [gpr_write_of_ne _ _ _ (by decide), x10₂, x10₁', kpos_step _ hp3 (by omega),
      show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
  · rw [gpr_write_self, State.read, BitVec.setWidth_eq, BitVec.setWidth_eq, g₂ .x16 (by simp),
      g₁ .x16 (by simp), h.x16]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Size.bits]
    omega
  · exact c₂.congr fun _ _ _ _ _ => rfl
  · exact mk₂.congr fun p hp => gpr_write_of_ne _ _ _ (maskRegs_ne p hp).2.2.2.2.1
  · rw [mem_write, m₂, m₁]; exact h.keys
  · rw [gpr_write_of_ne _ _ _ (by decide), g₂ .x11 (by simp), a₁, show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      hr₂, hr₁, passKeys_at s₀ (show 2 * j < 16 by omega)]
  · rw [gpr_write_of_ne _ _ _ (by decide), a₂, show 2 * (j + 1) = 2 * j + 1 + 1 by omega, hr₂, hr₁,
      passKeys_at s₀ (show 2 * j < 16 by omega), passKeys_at s₀ (show 2 * j + 1 < 16 by omega)]

/-- Pass `p`: sixteen rounds from the halves `lr`. -/
theorem pass_ok {s₀ : State} (hp : BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {s : State} (h : Same s₀ s) (h14 : s.gpr .x14 = s₀.gpr .x14)
    (h10 : s.gpr .x10 = s₀.gpr .x15 + BitVec.ofNat 64 (8 * kpos p 0)) (hc : Consts s) (hm : Masks s)
    (hk : Keys s₀ s.mem 48) (hl : s.gpr .x11 = spreadW lr.1) (hr : s.gpr .x12 = spreadW lr.2) :
    WP isa (pass (downOf p)) s (PInv s₀ p lr 8) := by
  refine WP.seq (WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_movz_x (by decide), runStep_some, runBlock_nil], ?_⟩)
  have g : ∀ r, r ≠ .x16 → (s.write .x .x16 ((8 : BitVec 16).setWidth 64 <<< (16 * 0))).gpr r = s.gpr r :=
    fun r hr => gpr_write_of_ne _ _ _ hr
  have hI : PInv s₀ p lr 0 (s.write .x .x16 ((8 : BitVec 16).setWidth 64 <<< (16 * 0))) :=
    ⟨⟨by rw [g _ (by decide), h.x15], fun r hr => by rw [g _ (outer_ne hr).2.2.2.2, h.keep r hr],
      h.sp, h.rd, h.wr, h.frame⟩, by rw [g _ (by decide), h14], by rw [g _ (by decide), h10],
      by rw [gpr_write_self]; decide, hc.congr fun _ _ _ _ _ => rfl,
      hm.congr fun p hp => g _ (maskRegs_ne p hp).2.2.2.2.1, hk,
      by rw [g _ (by decide), hl]; rfl, by rw [g _ (by decide), hr]; rfl⟩
  refine WP.loop (M := isa)
    (body := .block (round .x11 .x12 (downOf p) ++ round .x12 .x11 (downOf p) ++ [.subImm .x .x16 .x16 1]))
    (c := .nonzero .x .x16) (Q := PInv s₀ p lr 8)
    (fun (n : Nat) (t : State) => ∃ j, n = 8 - j ∧ j < 8 ∧ PInv s₀ p lr j t) ?_ 8 _ ⟨0, rfl, by decide, hI⟩
  rintro n t ⟨j, rfl, hj, ht⟩
  refine WP.mono (pairStep_ok hp hp3 hj ht) fun t' h' => ?_
  have ev := eval_nonzero (r := .x16) (x := 8 - (j + 1)) (by omega) h'.x16
  by_cases hz : j + 1 = 8
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [ev]; simp; omega, 8 - (j + 1), by omega, j + 1, rfl, by omega, h'⟩

theorem passTail_ok (s : State) (d : Nat) (hd : d < 4096) :
    ∃ s', runBlock isa (passTail d) s = some s' ∧
      s'.gpr .x10 = s.gpr .x10 + BitVec.ofNat 64 d ∧ s'.gpr .x11 = s.gpr .x12 ∧
      s'.gpr .x12 = s.gpr .x11 ∧ (∀ r, r ≠ .x5 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧
      s'.v = s.v ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .x .x10 (s.read .x .x10 + BitVec.ofNat _ d)
  let s₂ := s₁.write .x .x5 (s₁.gpr .x11)
  let s₃ := s₂.write .x .x11 (s₂.gpr .x12)
  let s₄ := s₃.write .x .x12 (s₃.gpr .x5)
  refine ⟨s₄, by
    rw [passTail, runBlock_cons, exec_addImm_x hd, runStep_some, runBlock_cons, exec_mov, runStep_some,
      runBlock_cons, exec_mov, runStep_some, runBlock_cons, exec_mov, runStep_some, runBlock_nil],
    ?_, ?_, ?_, fun r h5 h10 h11 h12 => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [s₄, s₃, s₂, s₁, gpr_write_of_ne _ _ _ (by decide : Reg.x10 ≠ .x12),
      gpr_write_of_ne _ _ _ (by decide : Reg.x10 ≠ .x11), gpr_write_of_ne _ _ _ (by decide : Reg.x10 ≠ .x5),
      gpr_write_self, State.read, BitVec.setWidth_eq]
  · simp only [s₄, s₃, gpr_write_of_ne _ _ _ (by decide : Reg.x11 ≠ .x12), gpr_write_self,
      BitVec.setWidth_eq, s₂, gpr_write_of_ne _ _ _ (by decide : Reg.x12 ≠ .x5), s₁,
      gpr_write_of_ne _ _ _ (by decide : Reg.x12 ≠ .x10)]
  · simp only [s₄, gpr_write_self, BitVec.setWidth_eq, s₃, gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x11),
      s₂, s₁, gpr_write_of_ne _ _ _ (by decide : Reg.x11 ≠ .x10)]
  · simp only [s₄, s₃, s₂, s₁, gpr_write_of_ne _ _ _ h12, gpr_write_of_ne _ _ _ h11,
      gpr_write_of_ne _ _ _ h5, gpr_write_of_ne _ _ _ h10]

/-- One pass and the exchange after it (the first two passes). -/
theorem passStep_ok {s₀ : State} (hp : BlockPre s₀) {x : BitVec 64} {p : Nat} (hp2 : p < 2) {s : State}
    (h : OInv s₀ x p s) :
    WP isa (.seq (pass (downOf p)) (.block (passTail (if p = 0 then 120 else 136)))) s (OInv s₀ x (p + 1)) := by
  refine WP.seq (WP.mono (pass_ok hp (by omega) h.same h.x14 h.x10 h.consts h.masks h.keys h.l h.r) fun s₁ h₁ => ?_)
  obtain ⟨s₂, h₂, t10, t11, t12, tk, tv, tsp, tm, trd, twr⟩ :=
    passTail_ok s₁ (if p = 0 then 120 else 136) (by split <;> decide)
  refine WP.of_runBlock ⟨s₂, h₂, ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [tk .x15 (by decide) (by decide) (by decide) (by decide), h₁.same.x15]
  · obtain ⟨a, b, c, d, -⟩ := outer_ne hr
    rw [tk r a b c d, h₁.same.keep r hr]
  · rw [tsp, h₁.same.sp]
  · rw [trd, h₁.same.rd]
  · rw [twr, h₁.same.wr]
  · rw [tm]; exact h₁.same.frame
  · rw [tk .x14 (by decide) (by decide) (by decide) (by decide), h₁.x14]
  · rw [t10, h₁.x10, Offset.add_add]
    congr 2
    rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> decide
  · exact h₁.consts.congr fun _ _ _ _ _ => by rw [tv]
  · exact h₁.masks.congr fun p hp => by
      obtain ⟨a, b, c, d, -⟩ := maskRegs_ne p hp
      exact tk _ a b c d
  · rw [tm]; exact h₁.keys
  · rw [t11, h₁.r, passes, swap]
  · rw [t12, h₁.l, passes, swap]

/-- TDEA encryption of the block in `x5` (as a 64-bit integer) with the key
schedule at `x14`, into `x5`, but for the callee-saved registers. -/
theorem blockCore_ok {s₀ : State} (hp : BlockPre s₀) :
    WP isa blockCore s₀ fun s =>
      Same s₀ s ∧ s.gpr .x14 = s₀.gpr .x14 ∧ s.gpr .x5 = tdes (sch s₀) (s₀.gpr .x5) := by
  refine WP.seq (WP.mono (spreadPre_ok s₀) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (spreadLoop_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (setup_ok h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (passStep_ok hp (p := 0) (by decide) h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (passStep_ok hp (p := 1) (by decide) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (pass_ok hp (p := 2) (by decide) h₅.same h₅.x14 h₅.x10 h₅.consts h₅.masks h₅.keys
    h₅.l h₅.r) fun s₆ h₆ => ?_)
  obtain ⟨s₇, h₇, x5₇, rd₇, wr₇, sp₇, k₇, m₇⟩ := fp_ok s₆ h₆.l h₆.r
  refine WP.of_runBlock ⟨s₇, h₇, ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · rw [k₇ .x15 (by simp [blockKept]), h₆.same.x15]
  · have hk : r ∈ blockKept := by
      simp only [outer, blockKept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    rw [k₇ r hk, h₆.same.keep r hr]
  · rw [sp₇, h₆.same.sp]
  · rw [rd₇, h₆.same.rd]
  · rw [wr₇, h₆.same.wr]
  · rw [m₇]; exact h₆.same.frame
  · rw [k₇ .x14 (by simp [blockKept]), h₆.x14]
  · rw [x5₇, tdes_eq]
    rfl

/-- The key schedule is unchanged outside a frame. -/
theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 384⟩ : Region).Disjoint r) :
    Spec.TripleDes.scheduleAt m' p = Spec.TripleDes.scheduleAt m p := by
  apply Vector.ext
  intro n hn
  rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, scheduleAt_getD _ _ hn]
  exact hf.readW (r := ⟨p + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)

/-! ## Keeping the callee-saved registers -/

/-- The callee-saved mask registers' slots, after the spread round keys. -/
def saveSlots : List (Reg × Nat) := (List.range 9).map fun i => (savedReg i, 384 + 8 * i)

theorem save_eq : blockSave = Spill.saveCode .x15 saveSlots := by decide

theorem restore_eq : blockRestore = Spill.restoreCode .x15 saveSlots := by decide

theorem saveSlots_facts : (∀ p ∈ saveSlots, 384 ≤ p.2 ∧ p.2 + 8 ≤ 384 + 72) ∧
    (∀ p ∈ saveSlots, p.2 % 8 = 0 ∧ p.2 < 32768) ∧ Spill.Fits saveSlots ∧
    Spill.Restorable .x15 saveSlots ∧ .x15 ∉ saveSlots.map Prod.fst ∧ .x14 ∉ saveSlots.map Prod.fst ∧
    .x5 ∉ saveSlots.map Prod.fst ∧ (∀ r ∈ outer, r ∉ saveSlots.map Prod.fst) := by
  decide

/-- The callee-saved registers the block writes. -/
def savedRegs : List Reg := (List.range 9).map savedReg

theorem mem_savedRegs {r : Reg} (h : r ∈ savedRegs) : ∃ i < 9, r = savedReg i := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
  exact ⟨i, List.mem_range.mp hi, rfl⟩

theorem mem_saveSlots {i : Nat} (hi : i < 9) : (savedReg i, 384 + 8 * i) ∈ saveSlots :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

/-- What the block keeps: `Same`, with the saves' slots too. -/
structure SameB (s₀ s : State) : Prop where
  x15 : s.gpr .x15 = s₀.gpr .x15
  keep : ∀ r ∈ outer, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨s₀.gpr .x15, 456⟩] s₀.mem s.mem

/-- TDEA encryption of the block in `x5` (as a 64-bit integer) with the key
schedule at `x14`, into `x5`. -/
theorem block_ok {s₀ : State} (hp : BlockPre s₀) :
    WP isa block s₀ fun s =>
      SameB s₀ s ∧ s.gpr .x14 = s₀.gpr .x14 ∧ s.gpr .x5 = tdes (sch s₀) (s₀.gpr .x5) ∧
      ∀ i < 9, s.gpr (savedReg i) = s₀.gpr (savedReg i) := by
  obtain ⟨hl, ho, hf, hr, h15, h14, h5, hout⟩ := saveSlots_facts
  obtain ⟨X, hX, hXb, hXl, hXw⟩ := hp.scr
  have slotIn : ∀ p ∈ saveSlots, X.Contains ((s₀.gpr .x15) + BitVec.ofNat 64 p.2) 8 := fun p hp' => by
    rw [← hXb]; exact Offset.contains_base _ (by have := hl p hp'; omega) (by have := hl p hp'; omega)
  rw [block, save_eq]
  apply WP.seq
  refine WP.mono (Spill.save_wp ho fun p hp' => ⟨X, hX, slotIn p hp'⟩) fun s₁ st => ?_
  have saveF : Frame [⟨(s₀.gpr .x15) + BitVec.ofNat 64 384, 72⟩] s₀.mem s₁.mem := by
    rw [st.mem]; exact Spill.saveMem_frame hl (by decide) _ _ _
  have bp₁ : BlockPre s₁ :=
    ⟨by rw [st.rd, st.wr, st.gpr]; exact hp.sched, by rw [st.wr, st.gpr]; exact hp.scr,
      by rw [st.gpr]; exact hp.disj⟩
  have sch₁ : sch s₁ = sch s₀ := by
    simp only [sch, st.gpr]
    exact scheduleAt_frame saveF fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact (hp.disj.sub_left (Offset.sub_base _ (by decide))).symm
  apply WP.seq
  refine WP.mono (blockCore_ok bp₁) fun s₂ ⟨same₂, x14₂, x5₂⟩ => ?_
  have x15₂ : s₂.gpr .x15 = (s₀.gpr .x15) := by rw [same₂.x15, st.gpr]
  have sv : Spill.Saved (s₀.gpr .x15) s₀.gpr saveSlots s₂.mem := by
    have h := Spill.saveMem_saved hf s₀.mem (s₀.gpr .x15) s₀.gpr
    rw [← st.mem] at h
    refine h.frame_in hl same₂.frame fun r hr' => ?_
    simp only [List.mem_singleton] at hr'; subst hr'
    simp only [xR, st.gpr]
    exact Offset.disjoint_base _ (by decide) (by decide)
  rw [restore_eq]
  refine WP.mono (Spill.restore_wp x15₂ ho hr (fun p hp' => ?_) sv) fun s₃ h₃ => ?_
  · rw [same₂.rd, same₂.wr, st.rd, st.wr]
    exact ⟨X, List.mem_append_right _ hX, slotIn p hp'⟩
  refine ⟨⟨?_, fun r hr' => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, fun i hi => ?_⟩
  · rw [h₃.other _ h15, x15₂]
  · rw [h₃.other _ (hout r hr'), same₂.keep r hr', st.gpr]
  · rw [h₃.sp, same₂.sp, st.sp]
  · rw [h₃.rd, same₂.rd, st.rd]
  · rw [h₃.wr, same₂.wr, st.wr]
  · rw [h₃.mem]
    refine (saveF.sub fun r hr' => ?_).trans (same₂.frame.sub fun r hr' => ?_)
    · simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩
    · simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨_, List.mem_singleton_self _, by simp only [xR, st.gpr]; exact Region.sub_prefix (by decide)⟩
  · rw [h₃.other _ h14, x14₂, st.gpr]
  · rw [h₃.other _ h5, x5₂, sch₁, st.gpr]
  · exact h₃.gpr_of (.inl (List.mem_map.mpr ⟨_, mem_saveSlots hi, rfl⟩))

end VG.Proof.CmacTripleDes.AArch64
