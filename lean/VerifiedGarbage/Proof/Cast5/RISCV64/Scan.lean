module

public import VerifiedGarbage.Proof.Cast5.RISCV64.Run
public import VerifiedGarbage.Proof.Cast5.Table
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# CAST5 on RISC-V: the scan of a table

`scan` leaves in `s4 + k` word `k` of the entry of the table at `tbl` whose
number is in `s0 + k`, zero-extended (`scan_ok`). Pass `q` reads quadword
`q` of every entry, which holds words `2q` and `2q + 1`; each bit `i` of it
is looked up at index `2q` if it is in the low word, `2q + 1` if not
(`ixOf`), and the proof follows each bit: a selection keeps a bit of its
second operand where its mask's bit is set (`pick_bit`), so a tree of them
(`tree_ok`) gives the bit of the quadword of the block's entry whose number
is the index's low bits, and the last block whose mask sets the bit is the
index's (`PassAt`).
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Cast5.RISCV64

/-! ## Steps -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem upd_keep {s s' : State} {d : Reg} {v : BitVec 64} (u : Upd s s' d v) : Keep [d] s s' :=
  ⟨fun r hr => u.other r (by simpa using hr), u.rd, u.wr⟩

theorem wp_and {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_sra {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d ((s.gpr n).sshiftRight sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .sra .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

end

/-! ## Selections -/

/-- A selection's bit: `b`'s where `m`'s is set, else `a`'s. -/
theorem pick_bit (a b m : BitVec 64) (i : Nat) :
    (a ^^^ ((b ^^^ a) &&& m)).getLsbD i = if m.getLsbD i then b.getLsbD i else a.getLsbD i := by
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases m.getLsbD i <;> cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

/-- `pick a b m`: `a` := the selection of `b` by `m` over `a`. -/
theorem wp_pick {is : List Instr} {s : State} {Q : State → Prop} {a b m : Reg} (hab : a ≠ b)
    (hbm : b ≠ m)
    (k : ∀ s', s'.gpr a = s.gpr a ^^^ ((s.gpr b ^^^ s.gpr a) &&& s.gpr m) → Keep [b, a] s s' →
      s'.mem = s.mem → WP isa (.block is) s' Q) :
    WP isa (.block (pick a b m ++ is)) s Q := by
  unfold pick
  simp only [List.cons_append, List.nil_append]
  refine wp_xor fun s₁ u₁ => wp_and fun s₂ u₂ => wp_xor fun s₃ u₃ => k s₃ ?_ ?_ ?_
  · rw [u₃.gpr, u₂.gpr, u₂.other _ hab, u₁.other _ hab, u₁.gpr, u₁.other _ hbm.symm]
  · exact ((upd_keep u₁ |>.trans (upd_keep u₂)).trans (upd_keep u₃)).mono (by simp)
  · rw [u₃.mem, u₂.mem, u₁.mem]

/-- `n % 2 ^ (L + 1)` from `n % 2 ^ L` and bit `L`. -/
theorem mod_two_pow_succ' (n L : Nat) :
    n % 2 ^ (L + 1) = (if n.testBit L then 2 ^ L else 0) + n % 2 ^ L := by
  rw [Nat.pow_succ, Nat.mod_mul, Nat.testBit_eq_decide_div_mod_eq, Nat.add_comm]
  congr 1
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ L) with h | h <;> simp [h]

/-- The selection among the `2 ^ L` quadwords at `ep + o + 16 e` by the
masks of levels below `L`: each bit `i` of the first register is the bit
of the quadword at `e = ι i % 2 ^ L`, `ι i` being the number whose bit `c`
is bit `i` of level `c`'s mask. -/
theorem tree_ok (L : Nat) : ∀ (o : Nat) (a : Reg) (rs : List Reg) (s : State) (ι : Nat → Nat),
    L ≤ rs.length → (a :: rs).Nodup → (∀ r ∈ a :: rs, r ≠ ep ∧ ∀ c < L, r ≠ maskReg c) →
    (∀ c < L, ∀ i < 64, (s.gpr (maskReg c)).getLsbD i = (ι i).testBit c) →
    o + 16 * (2 ^ L - 1) < 2048 →
    (∀ e < 2 ^ L, (s.gpr ep + BitVec.ofNat 64 (o + 16 * e)).toNat % 8 = 0 ∧
      InRegions (s.rd ++ s.wr) (s.gpr ep + BitVec.ofNat 64 (o + 16 * e)) 8) →
    WP isa (.block (tree L o (a :: rs))) s fun t =>
      (∀ i < 64, (t.gpr a).getLsbD i =
        (s.mem.readW (s.gpr ep + BitVec.ofNat 64 (o + 16 * (ι i % 2 ^ L))) 64).getLsbD i) ∧
      Keep (a :: rs) s t ∧ t.mem = s.mem := by
  induction L with
  | zero =>
    intro o a rs s ι _ _ hne _ ho hal
    have h0 := hal 0 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    unfold tree
    refine wp_ld (by omega) rfl h0.1 h0.2 fun s' u => WP.block_nil ⟨fun i _ => ?_, (upd_keep u).mono (by simp),
      u.mem⟩
    rw [u.gpr, Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.add_zero]
  | succ L ih =>
    intro o a rs s ι hlen hnd hne hm ho hal
    obtain ⟨b, rs, rfl⟩ : ∃ b rs', rs = b :: rs' := by
      cases rs with
      | nil => simp at hlen
      | cons b rs' => exact ⟨b, rs', rfl⟩
    simp only [List.length_cons] at hlen
    have hab : a ≠ b := fun e => by subst e; simp at hnd
    have ha := hne a (by simp)
    have hb := hne b (by simp)
    unfold tree
    rw [WP.block_append_iff, WP.block_append_iff]
    -- The low half, into `a`.
    refine WP.mono (ih o a (b :: rs) s ι (by simp; omega) hnd
      (fun r hr => ⟨(hne r hr).1, fun c hc => (hne r hr).2 c (by omega)⟩)
      (fun c hc => hm c (by omega)) (by rw [Nat.pow_succ] at ho; omega)
      (fun e he => hal e (by rw [Nat.pow_succ]; omega))) fun t ⟨ta, tk, tm⟩ => ?_
    have tep : t.gpr ep = s.gpr ep := tk.gpr (by simpa using fun h => (hne ep h).1 rfl)
    have tmk (c : Nat) (hc : c < L + 1) : t.gpr (maskReg c) = s.gpr (maskReg c) :=
      tk.gpr fun h => (hne _ h).2 c hc rfl
    -- The high half, into `b`.
    refine WP.mono (ih (o + 16 * 2 ^ L) b rs t ι (by omega) (List.nodup_cons.mp hnd).2
      (fun r hr => ⟨(hne r (by simp [hr])).1, fun c hc => (hne r (by simp [hr])).2 c (by omega)⟩)
      (fun c hc => by rw [tmk c (by omega)]; exact hm c (by omega)) (by rw [Nat.pow_succ] at ho; omega)
      (fun e he => by
        rw [tep, tk.2.1, tk.2.2, show o + 16 * 2 ^ L + 16 * e = o + 16 * (2 ^ L + e) by rw [Nat.mul_add, Nat.add_assoc]]
        exact hal _ (by rw [Nat.pow_succ]; omega))) fun u ⟨ub, uk, um⟩ => ?_
    have ua : u.gpr a = t.gpr a := uk.gpr (List.nodup_cons.mp hnd).1
    have umk : u.gpr (maskReg L) = s.gpr (maskReg L) := by
      rw [uk.gpr fun h => (hne _ (by simp [h])).2 L (by omega) rfl, tmk L (by omega)]
    have hbm : b ≠ maskReg L := hb.2 L (by omega)
    -- The selection by level `L`.
    refine wp_pick hab hbm fun v va vk vm => WP.block_nil ⟨fun i hi => ?_, ?_, by rw [vm, um, tm]⟩
    · rw [va, pick_bit, umk, hm L (by omega) i hi, ub i hi, ua, ta i hi, tep, tm, mod_two_pow_succ']
      split
      · rw [Nat.mul_add, Nat.add_assoc]
      · rw [Nat.zero_add]
    · exact ((tk.trans uk).trans vk).mono (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with ((h | h | h) | h | h) | h | h <;> simp only [h, true_or, or_true])

/-! ## Masks -/

/-- Bit `i` of a level's mask: bit `c` of `x` in the low word, of `y` in the
high word. -/
theorem setup_bit (x y : BitVec 64) {c : Nat} (hc : c < 64) {i : Nat} (hi : i < 64) :
    ((((x <<< (63 - c)).sshiftRight 63) >>> 32) ||| (((y <<< (63 - c)).sshiftRight 63) <<< 32)).getLsbD i =
      if i < 32 then x.getLsbD c else y.getLsbD c := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
  have e : 63 - (63 - c) = c := by omega
  have f : ¬ 63 + (32 + i) < 64 := by omega
  by_cases h : i < 32
  · simp [h, e, f, show ¬ (64 ≤ 32 + i) by omega, show ¬ 63 < 63 - c by omega]
  · by_cases h' : 63 + (i - 32) < 64
    · simp [h, h', e, f, hi, show 64 ≤ 32 + i by omega, show ¬ 64 ≤ i - 32 by omega,
        show ¬ 63 < 63 - c by omega, show ¬ 63 + (i - 32) < 63 - c by omega, show 63 + (i - 32) - (63 - c) = c by omega]
    · simp [h, h', e, f, hi, show 64 ≤ 32 + i by omega, show ¬ 64 ≤ i - 32 by omega, show ¬ 63 < 63 - c by omega]

/-- The low word of a block's mask, from an index's block `h`, as all ones
if `h ≤ J` (`h - J - 1` is negative). -/
theorem blk_lo : ∀ h < 16, ∀ J < 16, (BitVec.ofNat 64 h - BitVec.ofNat 64 (J + 1)) >>> 32 =
    if h ≤ J then 0xFFFFFFFF#64 else 0#64 := by decide
/-- The high word of a block's mask. -/
theorem blk_hi : ∀ h < 16, ∀ J < 16, ((BitVec.ofNat 64 h - BitVec.ofNat 64 (J + 1)).sshiftRight 63) <<< 32 =
    if h ≤ J then 0xFFFFFFFF00000000#64 else 0#64 := by decide
/-- The bits of the words' masks. -/
theorem lo_bits : ∀ i < 64, (0xFFFFFFFF#64).getLsbD i = decide (i < 32) := by decide
theorem hi_bits : ∀ i < 64, (0xFFFFFFFF00000000#64).getLsbD i = decide (32 ≤ i) := by decide

/-- Bit `i` of a block's mask: set if the block `J` is at least the block
`hl` of the low word's index (`i < 32`), or `hh` of the high word's. -/
theorem blk_bit {hl hh J : Nat} (hl16 : hl < 16) (hh16 : hh < 16) (hJ : J < 16) {i : Nat} (hi : i < 64) :
    (((BitVec.ofNat 64 hl - BitVec.ofNat 64 (J + 1)) >>> 32) |||
      ((BitVec.ofNat 64 hh - BitVec.ofNat 64 (J + 1)).sshiftRight 63 <<< 32)).getLsbD i =
      decide ((if i < 32 then hl else hh) ≤ J) := by
  rw [BitVec.getLsbD_or, blk_lo hl hl16 J hJ, blk_hi hh hh16 J hJ]
  by_cases h : i < 32
  · rw [ite_eq_left h]
    split
    · rw [lo_bits i hi, decide_eq_true h, Bool.true_or, decide_eq_true (by assumption)]
    · rw [BitVec.getLsbD_zero, Bool.false_or, decide_eq_false (by assumption)]
      split
      · rw [hi_bits i hi, decide_eq_false (by omega)]
      · rw [BitVec.getLsbD_zero]
  · rw [ite_eq_right h]
    have e1 : (if hl ≤ J then 0xFFFFFFFF#64 else 0#64).getLsbD i = false := by
      split
      · rw [lo_bits i hi, decide_eq_false h]
      · rw [BitVec.getLsbD_zero]
    rw [e1, Bool.false_or]
    split
    · rw [hi_bits i hi, decide_eq_true (by omega), decide_eq_true (by assumption)]
    · rw [BitVec.getLsbD_zero, decide_eq_false (by assumption)]

/-! ## A pass -/

set_option hygiene false in
/-- A fact about the registers of pass `q < 2`, by cases. -/
local macro "regs" : tactic => `(tactic| (rcases (show q = 0 ∨ q = 1 by omega) with rfl | rfl <;> decide))

/-- Quadword `q` of entry `e` of the table at `T`. -/
abbrev qw (m : Mem) (T : Addr) (e q : Nat) : BitVec 64 :=
  m.readW (T + BitVec.ofNat 64 (16 * e + 8 * q)) 64

/-- The index bit `i` of quadword `q` is looked up at: index `2q` in the low
word, `2q + 1` in the high word. -/
def ixOf (idx : Nat → Nat) (q i : Nat) : Nat := if i < 32 then idx (2 * q) else idx (2 * q + 1)

/-- The registers pass `q` writes. -/
def passRegs (q : Nat) : List Reg :=
  [ep, maskReg 0, maskReg 1, maskReg 2, maskReg 3, idxReg (2 * q), idxReg (2 * q + 1), accReg (2 * q),
    accReg (2 * q + 1)] ++ treeRegs q

/-- Pass `q` of the scan of the table at `T` in the memory `m` at the
indices `idx`, from `sp`, with blocks `J … 15` done. -/
structure PassAt (sp : State) (m : Mem) (T : Addr) (idx : Nat → Nat) (q J : Nat) (s : State) : Prop where
  ep : s.gpr ep = T + BitVec.ofNat 64 (256 * J)
  zlo : s.gpr (idxReg (2 * q)) = BitVec.ofNat 64 (idx (2 * q) / 16) - BitVec.ofNat 64 (J + 1)
  zhi : s.gpr (idxReg (2 * q + 1)) = BitVec.ofNat 64 (idx (2 * q + 1) / 16) - BitVec.ofNat 64 (J + 1)
  mask : ∀ c < 4, ∀ i < 64, (s.gpr (maskReg c)).getLsbD i = (ixOf idx q i).testBit c
  acc : ∀ i < 64, J ≤ ixOf idx q i / 16 →
    (s.gpr (accReg (2 * q))).getLsbD i = (qw m T (ixOf idx q i) q).getLsbD i
  keep : Keep (passRegs q) sp s
  mem : s.mem = m

/-- An index's block less the blocks to go, one block on. -/
theorem z_step (h J : Nat) :
    BitVec.ofNat 64 h - BitVec.ofNat 64 (J + 1 + 1) + BitVec.ofNat 64 1 =
      BitVec.ofNat 64 h - BitVec.ofNat 64 (J + 1) := by
  rw [← BitVec.ofNat_add_ofNat (J + 1) 1, Offset.sub_add_eq, BitVec.sub_add_cancel]

/-- What a pass needs: the indices below 256 and the table's 4096 bytes at
`T`, a multiple of 64, readable. -/
structure PassPre (sp : State) (T : Addr) (idx : Nat → Nat) : Prop where
  idx : ∀ k < 4, idx k < 256
  tal : T.toNat % 64 = 0
  trd : (⟨T, 4096⟩ : Region) ∈ sp.rd ++ sp.wr

/-- Block `J` of pass `q`. -/
theorem body_ok {sp s : State} {m : Mem} {T : Addr} {idx : Nat → Nat} {q J : Nat} (hq : q < 2) (hJ : J < 16)
    (hp : PassPre sp T idx) (h : PassAt sp m T idx q (J + 1) s) :
    WP isa (.block (passBody q)) s (PassAt sp m T idx q J) := by
  have hrT : (⟨T, 4096⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.keep.2.1, h.keep.2.2]; exact hp.trd
  unfold passBody treeRegs
  simp only [List.cons_append, List.nil_append]
  -- `ep` to the block, the indices' blocks less `J + 1`.
  refine wp_subi (imm := 256) (by decide) fun s₁ u₁ => wp_addi (imm := 1) (by decide) fun s₂ u₂ =>
    wp_addi (imm := 1) (by decide) fun s₃ u₃ => ?_
  have k₃ : Keep [ep, idxReg (2 * q), idxReg (2 * q + 1)] s s₃ :=
    ((upd_keep u₁).trans (upd_keep u₂) |>.trans (upd_keep u₃)).mono (by simp)
  have g₃ (r : Reg) (hr : r ∉ [ep, idxReg (2 * q), idxReg (2 * q + 1)]) : s₃.gpr r = s.gpr r := k₃.gpr hr
  have e₃ : s₃.gpr ep = T + BitVec.ofNat 64 (256 * J) := by
    rw [u₃.other _ (by regs), u₂.other _ (by regs), u₁.gpr, h.ep,
      Offset.add_ofNat_sub _ (by omega), show 256 * (J + 1) - 256 = 256 * J by omega]
  have zl : s₃.gpr (idxReg (2 * q)) = BitVec.ofNat 64 (idx (2 * q) / 16) - BitVec.ofNat 64 (J + 1) := by
    rw [u₃.other _ (by regs), u₂.gpr, u₁.other _ (by regs), h.zlo, z_step]
  have zh : s₃.gpr (idxReg (2 * q + 1)) = BitVec.ofNat 64 (idx (2 * q + 1) / 16) - BitVec.ofNat 64 (J + 1) := by
    rw [u₃.gpr, u₂.other _ (by regs), u₁.other _ (by regs), h.zhi, z_step]
  have mk₃ (c : Nat) (hc : c < 4) : s₃.gpr (maskReg c) = s.gpr (maskReg c) :=
    g₃ _ (by rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;> regs)
  -- The block's selection.
  have hoff (e : Nat) (he : e < 2 ^ 4) : s₃.gpr ep + BitVec.ofNat 64 (8 * q + 16 * e) =
      T + BitVec.ofNat 64 (256 * J + 8 * q + 16 * e) := by
    rw [e₃, Offset.add_add, Nat.add_assoc]
  have hrT₃ : (⟨T, 4096⟩ : Region) ∈ s₃.rd ++ s₃.wr := by rw [k₃.2.1, k₃.2.2]; exact hrT
  have m₃ : s₃.mem = m := by rw [u₃.mem, u₂.mem, u₁.mem, h.mem]
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (tree_ok 4 (8 * q) (selReg q) [blkReg q, .a5, .t6, .s7] s₃ (ixOf idx q) (by simp)
    (by regs) (by regs) (fun c hc i hi => by rw [mk₃ c hc]; exact h.mask c hc i hi) (by omega)
    (fun e he => by
      rw [hoff e he]
      refine ⟨Sig.const_aligned hp.tal (by decide) ?_, ⟨_, hrT₃, Offset.contains_base _ (by omega) (by omega)⟩⟩
      exact Nat.dvd_add (Nat.dvd_add (Nat.dvd_trans (by decide) (Nat.dvd_mul_right 256 J))
        (Nat.dvd_mul_right 8 q)) (Nat.dvd_trans (by decide) (Nat.dvd_mul_right 16 e))))
    fun s₄ ⟨sa, sk, sm⟩ => ?_
  have g₄ (r : Reg) (hr : r ∉ treeRegs q) : s₄.gpr r = s₃.gpr r := sk.gpr hr
  -- The block's mask.
  simp only [List.cons_append]
  refine wp_srl (by decide) fun s₅ u₅ => wp_sra (by decide) fun s₆ u₆ => wp_sll (by decide) fun s₇ u₇ =>
    wp_or fun s₈ u₈ => ?_
  have k₈ : Keep [blkReg q, .a5] s₄ s₈ :=
    ((((upd_keep u₅).trans (upd_keep u₆)).trans (upd_keep u₇)).trans (upd_keep u₈)).mono (by simp)
  have b₈ : s₈.gpr (blkReg q) = ((BitVec.ofNat 64 (idx (2 * q) / 16) - BitVec.ofNat 64 (J + 1)) >>> 32) |||
      ((BitVec.ofNat 64 (idx (2 * q + 1) / 16) - BitVec.ofNat 64 (J + 1)).sshiftRight 63 <<< 32) := by
    rw [u₈.gpr, u₇.other _ (by regs), u₆.other _ (by regs), u₅.gpr, u₇.gpr, u₆.gpr, u₅.other _ (by regs),
      g₄ _ (by regs), g₄ _ (by regs), zl, zh]
  have g₈ (r : Reg) (hr : r ∉ treeRegs q) (hr' : r ∉ [blkReg q, .a5]) : s₈.gpr r = s₃.gpr r := by
    rw [k₈.gpr hr', g₄ r hr]
  -- The selection kept where the mask is set.
  rw [← List.append_nil (pick _ _ _)]
  refine wp_pick (by regs) (by regs) fun s₉ va vk vm => WP.block_nil ?_
  have g₉ (r : Reg) (hr : r ∉ [selReg q, accReg (2 * q)]) : s₉.gpr r = s₈.gpr r := vk.gpr (by simpa using hr)
  have hsel : s₈.gpr (selReg q) = s₄.gpr (selReg q) := k₈.gpr (by regs)
  refine ⟨?_, ?_, ?_, fun c hc i hi => ?_, fun i hi hJi => ?_, ?_, ?_⟩
  · rw [g₉ _ (by regs), g₈ _ (by regs) (by regs), e₃]
  · rw [g₉ _ (by regs), g₈ _ (by regs) (by regs), zl]
  · rw [g₉ _ (by regs), g₈ _ (by regs) (by regs), zh]
  · rw [g₉ _ (by rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;> regs),
      g₈ _ (by rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;> regs)
        (by rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;> regs),
      mk₃ c hc]
    exact h.mask c hc i hi
  · have hl := hp.idx (2 * q) (by omega)
    have hh := hp.idx (2 * q + 1) (by omega)
    rw [va, pick_bit, b₈, blk_bit (by omega) (by omega) hJ hi, hsel, sa i hi,
      show (if i < 32 then idx (2 * q) / 16 else idx (2 * q + 1) / 16) = ixOf idx q i / 16 by
        unfold ixOf; split <;> rfl]
    by_cases he : ixOf idx q i / 16 = J
    · rw [ite_eq_left (decide_eq_true (by omega)), m₃, hoff _ (Nat.mod_lt _ (by decide))]
      have := Nat.div_add_mod (ixOf idx q i) 16
      rw [show 256 * J + 8 * q + 16 * (ixOf idx q i % 16) = 16 * ixOf idx q i + 8 * q by omega]
    · rw [ite_eq_right (by rw [decide_eq_false (by omega)]; exact Bool.false_ne_true), g₈ _ (by regs) (by regs),
        g₃ _ (by regs)]
      exact h.acc i hi (by omega)
  · exact ((((h.keep.trans k₃).trans sk).trans k₈).trans vk).mono (by unfold passRegs treeRegs; regs)
  · rw [vm, u₈.mem, u₇.mem, u₆.mem, u₅.mem, sm, u₃.mem, u₂.mem, u₁.mem, h.mem]


/-- Level `c`'s mask of pass `q`, from the indices `x` (low word) and `y`
(high word). -/
theorem maskSetup_ok {is : List Instr} {s : State} {Q : State → Prop} {q c : Nat} (hq : q < 2) (hc : c < 4)
    (k : ∀ s', s'.gpr (maskReg c) = ((((s.gpr (idxReg (2 * q))) <<< (63 - c)).sshiftRight 63) >>> 32) |||
        ((((s.gpr (idxReg (2 * q + 1))) <<< (63 - c)).sshiftRight 63) <<< 32) →
      Keep [maskReg c, .a5] s s' → s'.mem = s.mem → WP isa (.block is) s' Q) :
    WP isa (.block (maskSetup q c ++ is)) s Q := by
  have r1 : maskReg c ≠ idxReg (2 * q) ∧ maskReg c ≠ idxReg (2 * q + 1) ∧ maskReg c ≠ .a5 ∧
      Reg.a5 ≠ idxReg (2 * q + 1) := by
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;> regs
  unfold maskSetup
  simp only [List.cons_append, List.nil_append]
  refine wp_sll (by omega) fun s₁ u₁ => wp_sra (by decide) fun s₂ u₂ => wp_srl (by decide) fun s₃ u₃ =>
    wp_sll (by omega) fun s₄ u₄ => wp_sra (by decide) fun s₅ u₅ => wp_sll (by decide) fun s₆ u₆ =>
    wp_or fun s₇ u₇ => k s₇ ?_ ?_ ?_
  · rw [u₇.gpr, u₆.other _ r1.2.2.1, u₆.gpr, u₅.other _ r1.2.2.1, u₅.gpr, u₄.other _ r1.2.2.1, u₄.gpr, u₃.gpr,
      u₃.other _ r1.2.1.symm, u₂.gpr, u₂.other _ r1.2.1.symm, u₁.gpr, u₁.other _ r1.2.1.symm]
  · exact ((((((upd_keep u₁).trans (upd_keep u₂)).trans (upd_keep u₃)).trans (upd_keep u₄)).trans
      (upd_keep u₅) |>.trans (upd_keep u₆)).trans (upd_keep u₇)).mono (by simp)
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

/-- Bit `i` of the mask of level `c` made from the indices. -/
theorem mask_bit {x y : Nat} {c i : Nat} (hc : c < 4) (hi : i < 64) :
    ((((BitVec.ofNat 64 x <<< (63 - c)).sshiftRight 63) >>> 32) |||
      (((BitVec.ofNat 64 y <<< (63 - c)).sshiftRight 63) <<< 32)).getLsbD i =
      (if i < 32 then x else y).testBit c := by
  rw [setup_bit _ _ (by omega) hi]
  split <;> rw [BitVec.getLsbD_ofNat, decide_eq_true (by omega : c < 64), Bool.true_and]

theorem shr4 (x : Nat) (hx : x < 256) : BitVec.ofNat 64 x >>> 4 = BitVec.ofNat 64 (x / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem passStart_eq (q : Nat) : passStart q = maskSetup q 0 ++ (maskSetup q 1 ++ (maskSetup q 2 ++
    (maskSetup q 3 ++ ([.shift .srl .d (idxReg (2 * q)) (idxReg (2 * q)) 4,
      .addi (idxReg (2 * q)) (idxReg (2 * q)) (-17), .shift .srl .d (idxReg (2 * q + 1)) (idxReg (2 * q + 1)) 4,
      .addi (idxReg (2 * q + 1)) (idxReg (2 * q + 1)) (-17), .addi ep tbl 2047, .addi ep ep 2047,
      .addi ep ep 2] : List Instr)))) := by
  simp only [passStart, List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- The start of pass `q`: no block done. -/
theorem passStart_ok {s : State} {m : Mem} {T : Addr} {idx : Nat → Nat} {q : Nat} (hq : q < 2)
    (hp : PassPre s T idx) (hlo : s.gpr (idxReg (2 * q)) = BitVec.ofNat 64 (idx (2 * q)))
    (hhi : s.gpr (idxReg (2 * q + 1)) = BitVec.ofNat 64 (idx (2 * q + 1))) (ht : s.gpr tbl = T)
    (hm : s.mem = m) :
    WP isa (.block (passStart q)) s (PassAt s m T idx q 16) := by
  have hl := hp.idx (2 * q) (by omega)
  have hh := hp.idx (2 * q + 1) (by omega)
  have hix (i : Nat) : ixOf idx q i < 256 := by unfold ixOf; split <;> omega
  -- A mask kept by what follows its making.
  have mk (c : Nat) (hc : c < 4) (t : State)
      (hv : t.gpr (maskReg c) = ((((s.gpr (idxReg (2 * q))) <<< (63 - c)).sshiftRight 63) >>> 32) |||
        ((((s.gpr (idxReg (2 * q + 1))) <<< (63 - c)).sshiftRight 63) <<< 32)) :
      ∀ i < 64, (t.gpr (maskReg c)).getLsbD i = (ixOf idx q i).testBit c := fun i hi => by
    rw [hv, hlo, hhi, mask_bit hc hi]; rfl
  rw [passStart_eq]
  refine maskSetup_ok hq (c := 0) (by decide) fun s₀ v₀ k₀ m₀ => ?_
  have l₀ : s₀.gpr (idxReg (2 * q)) = s.gpr (idxReg (2 * q)) := k₀.gpr (by regs)
  have h₀ : s₀.gpr (idxReg (2 * q + 1)) = s.gpr (idxReg (2 * q + 1)) := k₀.gpr (by regs)
  refine maskSetup_ok hq (c := 1) (by decide) fun s₁ v₁ k₁ m₁ => ?_
  rw [l₀, h₀] at v₁
  have l₁ : s₁.gpr (idxReg (2 * q)) = s.gpr (idxReg (2 * q)) := (k₁.gpr (by regs)).trans l₀
  have h₁ : s₁.gpr (idxReg (2 * q + 1)) = s.gpr (idxReg (2 * q + 1)) := (k₁.gpr (by regs)).trans h₀
  refine maskSetup_ok hq (c := 2) (by decide) fun s₂ v₂ k₂ m₂ => ?_
  rw [l₁, h₁] at v₂
  have l₂ : s₂.gpr (idxReg (2 * q)) = s.gpr (idxReg (2 * q)) := (k₂.gpr (by regs)).trans l₁
  have h₂ : s₂.gpr (idxReg (2 * q + 1)) = s.gpr (idxReg (2 * q + 1)) := (k₂.gpr (by regs)).trans h₁
  refine maskSetup_ok hq (c := 3) (by decide) fun s₃ v₃ k₃ m₃ => ?_
  rw [l₂, h₂] at v₃
  have l₃ : s₃.gpr (idxReg (2 * q)) = s.gpr (idxReg (2 * q)) := (k₃.gpr (by regs)).trans l₂
  have h₃ : s₃.gpr (idxReg (2 * q + 1)) = s.gpr (idxReg (2 * q + 1)) := (k₃.gpr (by regs)).trans h₂
  have kk : Keep [maskReg 0, .a5, maskReg 1, .a5, maskReg 2, .a5, maskReg 3, .a5] s s₃ :=
    ((k₀.trans k₁).trans k₂).trans k₃
  -- The masks, as they stay to the end.
  have M₃ (c : Nat) (hc : c < 4) : ∀ i < 64, (s₃.gpr (maskReg c)).getLsbD i = (ixOf idx q i).testBit c := by
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
    · exact mk 0 hc s₃ (by rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide), v₀])
    · exact mk 1 hc s₃ (by rw [k₃.gpr (by decide), k₂.gpr (by decide), v₁])
    · exact mk 2 hc s₃ (by rw [k₃.gpr (by decide), v₂])
    · exact mk 3 hc s₃ v₃
  refine wp_srl (by decide) fun t₁ w₁ => wp_subi (imm := 17) (by decide) fun t₂ w₂ =>
    wp_srl (by decide) fun t₃ w₃ => wp_subi (imm := 17) (by decide) fun t₄ w₄ =>
    wp_addi (imm := 2047) (by decide) fun t₅ w₅ => wp_addi (imm := 2047) (by decide) fun t₆ w₆ =>
    wp_addi (imm := 2) (by decide) fun t₇ w₇ => WP.block_nil ?_
  have kt : Keep [idxReg (2 * q), idxReg (2 * q), idxReg (2 * q + 1), idxReg (2 * q + 1), ep, ep, ep] s₃ t₇ :=
    ((((((upd_keep w₁).trans (upd_keep w₂)).trans (upd_keep w₃)).trans (upd_keep w₄)).trans (upd_keep w₅)).trans
      (upd_keep w₆)).trans (upd_keep w₇)
  refine ⟨?_, ?_, ?_, fun c hc i hi => ?_, fun i _ h16 => absurd h16 (by have := hix i; omega), ?_, ?_⟩
  · rw [w₇.gpr, w₆.gpr, w₅.gpr, w₄.other _ (by regs), w₃.other _ (by regs), w₂.other _ (by regs),
      w₁.other _ (by regs), kk.gpr (by regs), ht, Offset.add_add, Offset.add_add]
  · rw [w₇.other _ (by regs), w₆.other _ (by regs), w₅.other _ (by regs), w₄.other _ (by regs),
      w₃.other _ (by regs), w₂.gpr, w₁.gpr, l₃, hlo, shr4 _ hl]
  · rw [w₇.other _ (by regs), w₆.other _ (by regs), w₅.other _ (by regs), w₄.gpr, w₃.gpr,
      w₂.other _ (by regs), w₁.other _ (by regs), h₃, hhi, shr4 _ hh]
  · rw [kt.gpr (by rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;> regs)]
    exact M₃ c hc i hi
  · exact (kk.trans kt).mono (by unfold passRegs treeRegs; regs)
  · rw [w₇.mem, w₆.mem, w₅.mem, w₄.mem, w₃.mem, w₂.mem, w₁.mem, m₃, m₂, m₁, m₀, hm]


/-- Word `k` of entry `e` of the table at `T`, zero-extended. -/
abbrev tw (m : Mem) (T : Addr) (e k : Nat) : BitVec 64 := (ent m T e k).setWidth 64

/-- The words of value `2q` once every block is done. -/
theorem passEnd_ok {sp s : State} {m : Mem} {T : Addr} {idx : Nat → Nat} {q : Nat} (hq : q < 2)
    (h : PassAt sp m T idx q 0 s) :
    WP isa (.block (passEnd q)) s fun t =>
      t.gpr (accReg (2 * q)) = tw m T (idx (2 * q)) (2 * q) ∧
      t.gpr (accReg (2 * q + 1)) = tw m T (idx (2 * q + 1)) (2 * q + 1) ∧
      Keep (passRegs q) sp t ∧ t.mem = m := by
  have ha (i : Nat) (hi : i < 64) := h.acc i hi (Nat.zero_le _)
  unfold passEnd
  refine wp_srl (by decide) fun t₁ w₁ => wp_sll (by decide) fun t₂ w₂ => wp_srl (by decide) fun t₃ w₃ =>
    WP.block_nil ⟨?_, ?_, (h.keep.trans (((upd_keep w₁).trans (upd_keep w₂)).trans (upd_keep w₃))).mono
      (by unfold passRegs treeRegs; regs), by rw [w₃.mem, w₂.mem, w₁.mem, h.mem]⟩
  · rw [w₃.gpr, w₂.gpr, w₁.other _ (by regs), tw, ent, show 16 * idx (2 * q) + 4 * (2 * q) =
      16 * idx (2 * q) + 8 * q by omega, Mem.readW_lo32 rfl]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
    by_cases h32 : i < 32
    · rw [show 32 + i - 32 = i by omega, ha i (by omega), ixOf, ite_eq_left h32]
      simp [h32, show 32 + i < 64 by omega, show i < 64 by omega]
    · simp [h32, show ¬ 32 + i < 64 by omega]
  · rw [w₃.other _ (by regs), w₂.other _ (by regs), w₁.gpr, tw, ent, show 16 * idx (2 * q + 1) + 4 * (2 * q + 1) =
      16 * idx (2 * q + 1) + 8 * q + 4 by omega, ← Offset.add_add, Mem.readW_hi32 rfl]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
    by_cases h32 : i < 32
    · rw [ha (32 + i) (by omega), ixOf, ite_eq_right (by omega)]
      simp [h32, show i < 64 by omega]
    · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
      simp [h32]

/-- Pass `q`: values `2q` and `2q + 1` are words `2q` and `2q + 1` of the
entries their indices name. -/
theorem pass_ok {s : State} {m : Mem} {T : Addr} {idx : Nat → Nat} {q : Nat} (hq : q < 2)
    (hp : PassPre s T idx) (hlo : s.gpr (idxReg (2 * q)) = BitVec.ofNat 64 (idx (2 * q)))
    (hhi : s.gpr (idxReg (2 * q + 1)) = BitVec.ofNat 64 (idx (2 * q + 1))) (ht : s.gpr tbl = T)
    (hm : s.mem = m) :
    WP isa (pass q) s fun t =>
      t.gpr (accReg (2 * q)) = tw m T (idx (2 * q)) (2 * q) ∧
      t.gpr (accReg (2 * q + 1)) = tw m T (idx (2 * q + 1)) (2 * q + 1) ∧
      Keep (passRegs q) s t ∧ t.mem = m := by
  unfold pass
  refine WP.seq (WP.mono (passStart_ok hq hp hlo hhi ht hm) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := PassAt s m T idx q 0) ?_ fun s₂ h₂ => passEnd_ok hq h₂)
  refine WP.loop (fun n v => 0 < n ∧ n ≤ 16 ∧ PassAt s m T idx q n v) ?_ 16 s₁ ⟨by decide, Nat.le_refl _, h₁⟩
  rintro n v ⟨hn, hn16, hv⟩
  obtain ⟨J, rfl⟩ : ∃ J, n = J + 1 := ⟨n - 1, by omega⟩
  refine WP.mono (body_ok hq (by omega) hp hv) fun w hw => ?_
  have tw' : w.gpr tbl = T := by rw [hw.keep.gpr (by unfold passRegs treeRegs; regs), ht]
  have ev : isa.eval (.ne ep tbl) w = some (w.gpr ep != w.gpr tbl) := rfl
  by_cases hJ : J = 0
  · subst hJ
    refine .inl ⟨by rw [ev, hw.ep, tw', Nat.mul_zero]; simp, hw⟩
  · refine .inr ⟨?_, J, by omega, by omega, by omega, hw⟩
    rw [ev, hw.ep, tw', bne_iff_ne.mpr]
    intro e
    have := Offset.add_ofNat_ne T (a := 256 * J) (b := 0) (by omega) (by decide) (by omega)
    simp only [BitVec.add_zero] at this
    exact this e

/-! ## The scan -/

/-- The registers the scan writes. -/
def loopRegs : List Reg := [.t0, .t1, .t2, .t3, .t5, .t6, .a5, .s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7]

/-- What a scan needs: the indices below 256, and the table, 4096 bytes at
`tbl`, a multiple of 64, readable. -/
structure ScanPre (s : State) : Prop where
  idx : ∀ k < 4, (s.gpr (idxReg k)).toNat < 256
  tal : (s.gpr tbl).toNat % 64 = 0
  trd : (⟨s.gpr tbl, 4096⟩ : Region) ∈ s.rd ++ s.wr

/-- The scan: `s4 + k` is word `k` of the entry of the table whose number
is in `s0 + k`, zero-extended; only the scan's registers are written. -/
theorem scan_ok (s : State) (h : ScanPre s) :
    WP isa scan s fun t =>
      (∀ k < 4, t.gpr (accReg k) = tw s.mem (s.gpr tbl) (s.gpr (idxReg k)).toNat k) ∧
      Keep loopRegs s t ∧ t.mem = s.mem := by
  have hp : PassPre s (s.gpr tbl) fun k => (s.gpr (idxReg k)).toNat := ⟨h.idx, h.tal, h.trd⟩
  unfold scan
  refine WP.seq (WP.mono (pass_ok (q := 0) (by decide) hp (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    rfl rfl) fun t ⟨t0, t1, tk, tm⟩ => ?_)
  have tg (r : Reg) (hr : r ∉ passRegs 0) : t.gpr r = s.gpr r := tk.gpr hr
  have hp' : PassPre t (s.gpr tbl) fun k => (s.gpr (idxReg k)).toNat :=
    ⟨h.idx, h.tal, by rw [tk.2.1, tk.2.2]; exact h.trd⟩
  refine WP.mono (pass_ok (q := 1) (by decide) hp' (by rw [tg _ (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by rw [tg _ (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]) (tg _ (by decide)) tm)
    fun u ⟨u0, u1, uk, um⟩ => ⟨fun k hk => ?_, (tk.trans uk).mono (by decide), um⟩
  have ug (r : Reg) (hr : r ∉ passRegs 1) : u.gpr r = t.gpr r := uk.gpr hr
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [ug _ (by decide)]; exact t0
  · rw [ug _ (by decide)]; exact t1
  · exact u0
  · exact u1

end VG.Proof.Cast5.RISCV64
