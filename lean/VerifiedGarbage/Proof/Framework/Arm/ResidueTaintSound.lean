module

public import VerifiedGarbage.Proof.Framework.Arm.ResidueTaint
public import VerifiedGarbage.TCB.Arm.Residue
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Reduce

/-!
# The residue analysis is sound (ARMv7)

`Agree τ s₁ s₂` is what `τ` (`ResidueTaint.lean`) says of two states, from
the window's base, the stack pointer less the offset `τ.sp` (`wb`, 32 bits;
`wbA`, its address): the stack pointers and the public registers agree, and
the flags if `τ.fl`, the registers of `wp` and `bp` hold what they say, the
frames still open tile the window from `τ.sp` to its top (`Frames`), the
other writable regions and the readable ones are outside the window, and the
memory outside them agrees but at the bytes of the window that `τ.sec` lists.
The window is within the 32-bit address space (`wbW`), so an address the code
computes in it, 32 bits wide, is its offset from `wbA` (`addr_wb`). Each
transfer function keeps `Agree` (`step_sound`, …), which makes `rtaint` a
`TaintCT`, as on RISC-V64 (`Proof/Framework/RISCV64/ResidueTaintSound.lean`).
-/

@[expose] public section

namespace VG.Arm.RTaint

open VG.Arm VG.Arm.FrameStack

/-! ## Bit masks -/

theorem testBit_ones (w k : Nat) : (ones w).testBit k = decide (k < w) := Nat.testBit_two_pow_sub_one w k

theorem bit_range (d w k : Nat) :
    (decide (k ≥ d) && decide (k - d < w)) = (decide (d ≤ k) && decide (k < d + w)) := by
  by_cases h : d ≤ k
  · simp only [ge_iff_le, h, decide_true, Bool.true_and, decide_eq_decide]; omega
  · simp only [ge_iff_le, h, decide_false, Bool.false_and]

theorem testBit_bset (b d w k : Nat) :
    (bset b d w).testBit k = (b.testBit k || (decide (d ≤ k) && decide (k < d + w))) := by
  show (b ||| ones w <<< d).testBit k = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_ones, bit_range]

theorem testBit_bclr (b d w k : Nat) :
    (bclr b d w).testBit k = (b.testBit k && !(decide (d ≤ k) && decide (k < d + w))) := by
  show (b ^^^ (b &&& ones w <<< d)).testBit k = _
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, testBit_ones, bit_range]
  cases b.testBit k <;> cases (decide (d ≤ k) && decide (k < d + w)) <;> rfl

theorem bnone_bit {b d w k : Nat} (h : bnone b d w = true) (h₁ : d ≤ k) (h₂ : k < d + w) :
    b.testBit k = false := by
  have e : (b >>> d &&& ones w) = 0 := Nat.eq_of_beq_eq_true h
  have := congrArg (·.testBit (k - d)) e
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones, show k - d < w by omega, decide_true,
    Bool.and_true, show d + (k - d) = k by omega, Nat.zero_testBit] at this
  exact this

theorem bsub_bit {a b k : Nat} (h : bsub a b = true) (hk : a.testBit k = true) : b.testBit k = true := by
  have e : (a &&& b) = a := Nat.eq_of_beq_eq_true h
  rw [← e, Nat.testBit_and, Bool.and_eq_true] at hk
  exact hk.2

/-! ## What the analysis says of two states -/

/-- The window's base: the stack pointer less the offset the analysis knows
it at. -/
def wb (τ : T) (s : State) : BitVec 32 := s.sp - BitVec.ofNat 32 τ.sp

/-- The window's base, as an address. -/
def wbA (τ : T) (s : State) : Addr := State.addr (wb τ s)

/-- The offset of `x` from the window's base. -/
def off (τ : T) (s : State) (x : Addr) : Nat := (x - wbA τ s).toNat

/-- `x` is in the window. -/
def InWin (τ : T) (s : State) (x : Addr) : Prop := off τ s x < τ.W

/-- The frames `F`, innermost first, tile the window of `W` bytes at `w`
from offset `o` to its top. -/
def Frames (w : Addr) (W : Nat) : Nat → List Region → Prop
  | o, [] => o = W
  | o, f :: fs => f.base = w + BitVec.ofNat 64 o ∧ 0 < f.len ∧ Frames w W (o + f.len) fs

/-- The flags of two states agree. -/
def FlagsEq (s₁ s₂ : State) : Prop := s₁.n = s₂.n ∧ s₁.z = s₂.z ∧ s₁.c = s₂.c ∧ s₁.v = s₂.v

/-- What `τ` says of the two states (see the module's documentation). -/
structure AgreeOk (τ : T) (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  spNat : τ.sp ≤ s₁.sp.toNat
  wbW : (wb τ s₁).toNat + τ.W < 2 ^ 32
  pub : ∀ r ∈ τ.pub, s₁.gpr r = s₂.gpr r
  fl : τ.fl = true → FlagsEq s₁ s₂
  wp : ∀ e ∈ τ.wp, s₁.gpr e.1 = wb τ s₁ + BitVec.ofNat 32 e.2 ∧ s₂.gpr e.1 = s₁.gpr e.1
  bp : ∀ e ∈ τ.bp, s₂.gpr e.1 = s₁.gpr e.1 ∧
    ∀ i < e.2, ¬ InWin τ s₁ (State.addr (s₁.gpr e.1 + BitVec.ofNat 32 i))
  rd : s₁.rd = s₂.rd
  wr : s₁.wr = s₂.wr
  unk : s₁.unknowns = s₂.unknowns
  regions : ∃ F B, s₁.wr = F ++ B ∧ F.length = τ.nf ∧ Frames (wbA τ s₁) τ.W τ.sp F ∧
    (∀ g ∈ s₁.rd ++ B, ∀ x, g.Contains x 1 → ¬ InWin τ s₁ x) ∧
    ∀ x, (∀ g ∈ s₁.rd ++ B, ¬ g.Contains x 1) → (InWin τ s₁ x → τ.sec.testBit (off τ s₁ x) = false) →
      s₁.mem x = s₂.mem x

def Agree (τ : T) (s₁ s₂ : State) : Prop := τ.ok = true → AgreeOk τ s₁ s₂

/-! ## Writing a register -/

/-- `setR` describes a write of `d`: of the same value in both runs if `p`,
of byte `k` of the window if `k`, and of an address followed by `b` bytes
outside it if `b`. -/
theorem AgreeOk.setR {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) (d : Reg) {p : Bool}
    {k b : Option Nat} {v₁ v₂ : BitVec 32} (hp : p = true → v₁ = v₂)
    (hk : ∀ k', k = some k' → v₁ = wb τ s₁ + BitVec.ofNat 32 k' ∧ v₂ = v₁)
    (hb : ∀ b', b = some b' → v₂ = v₁ ∧ ∀ i < b', ¬ InWin τ s₁ (State.addr (v₁ + BitVec.ofNat 32 i))) :
    AgreeOk (RTaint.setR τ d p k b) (s₁.setReg d v₁) (s₂.setReg d v₂) := by
  obtain ⟨hsp, hspN, hwbW, hpub, hfl, hwp, hbp, hrd, hwr, hunk, hreg⟩ := h
  refine ⟨hsp, hspN, hwbW, fun r hr => ?_, hfl, fun e he => ?_, fun e he => ?_, hrd, hwr, hunk, hreg⟩
  · simp only [RTaint.setR] at hr
    simp only [RegUpd.gpr_setReg]
    split at hr
    · rename_i hp'
      rcases RegSet.mem_insert.mp hr with rfl | hr
      · simp [hp hp']
      · by_cases hrd : r = d
        · simp [hrd, hp hp']
        · simp [hrd, hpub r hr]
    · obtain ⟨hne, hr⟩ := RegSet.mem_erase.mp hr
      simp [hne, hpub r hr]
  · simp only [RTaint.setR, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at he
    rcases he with he | ⟨he, hne⟩
    · cases k with
      | none => simp at he
      | some k' =>
        simp only [List.mem_singleton] at he
        subst he
        obtain ⟨e1, e2⟩ := hk k' rfl
        simp only [RegUpd.gpr_setReg_self]
        exact ⟨e1, e2⟩
    · rw [RegUpd.gpr_setReg_of_ne _ _ hne, RegUpd.gpr_setReg_of_ne _ _ hne]
      exact hwp e he
  · simp only [RTaint.setR, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at he
    rcases he with he | ⟨he, hne⟩
    · cases b with
      | none => simp at he
      | some b' =>
        simp only [List.mem_singleton] at he
        subst he
        obtain ⟨e1, e2⟩ := hb b' rfl
        simp only [RegUpd.gpr_setReg_self]
        exact ⟨e1, e2⟩
    · rw [RegUpd.gpr_setReg_of_ne _ _ hne, RegUpd.gpr_setReg_of_ne _ _ hne]
      exact hbp e he

/-- A register written with the same value in both runs. -/
theorem AgreeOk.setPub {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) (d : Reg) {v : BitVec 32} :
    AgreeOk (RTaint.setR τ d true none none) (s₁.setReg d v) (s₂.setReg d v) :=
  h.setR d (fun _ => rfl) (fun _ h => nomatch h) (fun _ h => nomatch h)

/-- A register written with values that are the same if `p`. -/
theorem AgreeOk.setP {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) (d : Reg) {p : Bool}
    {v₁ v₂ : BitVec 32} (hp : p = true → v₁ = v₂) :
    AgreeOk (RTaint.setR τ d p none none) (s₁.setReg d v₁) (s₂.setReg d v₂) :=
  h.setR d hp (fun _ h => nomatch h) (fun _ h => nomatch h)

theorem AgreeOk.reg {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {r : Reg} (hr : pubR τ r = true) :
    s₁.gpr r = s₂.gpr r := h.pub r hr

theorem AgreeOk.withPub {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {n : Reg}
    (hn : s₁.gpr n = s₂.gpr n) : AgreeOk (RTaint.withPub τ n) s₁ s₂ := by
  obtain ⟨hsp, hspN, hwbW, hpub, hfl, hwp, hbp, hrd, hwr, hunk, hreg⟩ := h
  refine ⟨hsp, hspN, hwbW, fun r hr => ?_, hfl, hwp, hbp, hrd, hwr, hunk, hreg⟩
  rcases RegSet.mem_insert.mp hr with rfl | hr
  · exact hn
  · exact hpub r hr

/-- The flags of two states, set from public values (`p`) or not. -/
theorem AgreeOk.setF {τ : T} {s₁ s₂ s₁' s₂' : State} (h : AgreeOk τ s₁ s₂) {p : Bool}
    (hp : p = true → FlagsEq s₁' s₂') (e₁ : s₁' = { s₁ with n := s₁'.n, z := s₁'.z, c := s₁'.c, v := s₁'.v })
    (e₂ : s₂' = { s₂ with n := s₂'.n, z := s₂'.z, c := s₂'.c, v := s₂'.v }) :
    AgreeOk (RTaint.setF τ p) s₁' s₂' := by
  obtain ⟨hsp, hspN, hwbW, hpub, -, hwp, hbp, hrd, hwr, hunk, hreg⟩ := h
  rw [e₁, e₂]
  exact ⟨hsp, hspN, hwbW, hpub, fun h => by rw [← e₁, ← e₂]; exact hp h, hwp, hbp, hrd, hwr, hunk, hreg⟩

theorem op2_eq {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {op2 : Op2} (hp : op2Pub τ op2 = true) :
    op2.eval s₁ = op2.eval s₂ := by
  cases op2 with
  | imm v => rfl
  | reg r => simp only [Op2.eval, h.reg hp]
  | shifted r sh n => simp only [Op2.eval, h.reg (show pubR τ r = true from hp)]

/-! ## Addresses in the window -/

theorem toNat_ofNat_lt {j : Nat} (h : j < 2 ^ 64) : (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Byte `j` of the window is at offset `j`. -/
theorem off_base (τ : T) (s : State) {j : Nat} (hj : j < 2 ^ 64) :
    off τ s (wbA τ s + BitVec.ofNat 64 j) = j := by
  have e : wbA τ s + BitVec.ofNat 64 j - wbA τ s = BitVec.ofNat 64 j := by bv_omega
  simp only [off, e, toNat_ofNat_lt hj]

theorem toNat_wbA (τ : T) (s : State) : (wbA τ s).toNat = (wb τ s).toNat := by
  simp only [wbA, State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (wb τ s).isLt (by decide))

/-- An address the code computes in the window, as an offset from its base. -/
theorem addr_wb (τ : T) (s : State) {j : Nat} (h : (wb τ s).toNat + j < 2 ^ 32) :
    State.addr (wb τ s + BitVec.ofNat 32 j) = wbA τ s + BitVec.ofNat 64 j := addr_add h

/-- A byte in the window is below `2 ^ 32`. -/
theorem inWin_lt {τ : T} {s : State} {x : Addr} (hW : (wb τ s).toNat + τ.W < 2 ^ 32) (h : InWin τ s x) :
    x.toNat < 2 ^ 32 := by
  unfold InWin off at h
  have hw := toNat_wbA τ s
  have hx := x.isLt
  rw [BitVec.toNat_sub] at h
  by_cases hc : (wbA τ s).toNat ≤ x.toNat
  · rw [show 2 ^ 64 - (wbA τ s).toNat + x.toNat = (x.toNat - (wbA τ s).toNat) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    omega

/-- `x` is among the `n` bytes from byte `o` of the window. -/
theorem in_range (τ : T) (s : State) (x : Addr) {o n : Nat} (h : o + n ≤ 2 ^ 64) :
    (x - (wbA τ s + BitVec.ofNat 64 o)).toNat < n ↔ o ≤ off τ s x ∧ off τ s x < o + n :=
  Offset.lt_iff x (wbA τ s) h

theorem Frames.le {w : Addr} {W : Nat} : ∀ {o : Nat} {F : List Region}, Frames w W o F → o ≤ W
  | _, [], h => by simp only [Frames] at h; omega_using [h]
  | _, _ :: _, ⟨_, _, hf⟩ => by have := Frames.le hf; omega_using [this]

/-- A frame's bytes are in the window, from the offset of the frames on. -/
theorem Frames.contains {w : Addr} {W : Nat} (hw : W < 2 ^ 32) :
    ∀ {o : Nat} {F : List Region}, Frames w W o F → ∀ g ∈ F, ∀ x, g.Contains x 1 →
      o ≤ (x - w).toNat ∧ (x - w).toNat < W
  | _, [], _, _, hg, _, _ => nomatch hg
  | o, f :: fs, ⟨hb, hl, hf⟩, g, hg, x, hx => by
    have hle := Frames.le hf
    rcases List.mem_cons.mp hg with rfl | hg
    · simp only [Region.Contains] at hx
      rw [hb] at hx
      have := (Offset.lt_iff x w (d := o) (n := g.len) (by omega_using [hw, hle])).mp (by omega_using [hx])
      omega_using [this, hle]
    · have := Frames.contains hw hf g hg x hx
      omega_using [this]

/-- A byte of an access within a region is in it. -/
theorem contains_of_access {g : Region} {a x : Addr} {n : Nat} (hg : g.Contains a n)
    (hx : (x - a).toNat < n) : g.Contains x 1 := by
  simp only [Region.Contains] at hg ⊢
  have e : x - g.base = (a - g.base) + (x - a) := by bv_omega
  rw [e, BitVec.toNat_add]
  have h1 := (a - g.base).isLt
  have h2 := (x - a).isLt
  by_cases hc : (a - g.base).toNat + (x - a).toNat < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hc]; omega_using [hg, hx]
  · rw [show (a - g.base).toNat + (x - a).toNat = ((a - g.base).toNat + (x - a).toNat - 2 ^ 64) + 2 ^ 64
      by omega_using [hc], Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [h1, h2])]
    omega_using [hg, hx, h2]

theorem wpOf_mem {τ : T} {r : Reg} {k : Nat} (h : wpOf τ r = some k) : (r, k) ∈ τ.wp := by
  simp only [wpOf, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some he
  have := List.find?_some he
  simp only [beq_iff_eq] at this
  rw [← this]; exact hm

theorem bpOf_mem {τ : T} {r : Reg} {b : Nat} (h : bpOf τ r = some b) : (r, b) ∈ τ.bp := by
  simp only [bpOf, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some he
  have := List.find?_some he
  simp only [beq_iff_eq] at this
  rw [← this]; exact hm


theorem toNat_addr' (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide))

theorem addr_inj {a b : BitVec 32} (h : State.addr a = State.addr b) : a = b := by
  apply BitVec.eq_of_toNat_eq
  rw [← toNat_addr' a, ← toNat_addr' b, h]

/-- The address of an access through byte `k` of the window, at `ofs`. -/
theorem wp_addr {τ : T} {s : State} {v : BitVec 32} {k ofs : Nat} (h : v = wb τ s + BitVec.ofNat 32 k)
    (hk : (wb τ s).toNat + (k + ofs) < 2 ^ 32) :
    State.addr (v + BitVec.ofNat 32 ofs) = wbA τ s + BitVec.ofNat 64 (k + ofs) := by
  rw [h, BitVec.add_assoc, BitVec.ofNat_add_ofNat, addr_wb τ s hk]

/-- A byte of an access at `ofs` from a register with `b` bytes outside the
window after it, within them, is not in the window. -/
theorem bp_byte {τ : T} {s : State} {g : BitVec 32} {x : Addr} {ofs n b : Nat}
    (hW : (wb τ s).toNat + τ.W < 2 ^ 32)
    (hb : ∀ i < b, ¬ InWin τ s (State.addr (g + BitVec.ofNat 32 i))) (hn : ofs + n ≤ b) (h4 : n ≤ 4)
    (hx : (x - State.addr (g + BitVec.ofNat 32 ofs)).toNat < n) : ¬ InWin τ s x := by
  intro hin
  have hlt := inWin_lt hW hin
  generalize hy : g + BitVec.ofNat 32 ofs = y at hx
  generalize hj : (x - State.addr y).toNat = j at hx
  have ex : x = State.addr y + BitVec.ofNat 64 j := by
    rw [← hj, BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  have hy' := y.isLt
  by_cases hc : y.toNat + j < 2 ^ 32
  · refine hb (ofs + j) (by omega_using [hn, hx]) ?_
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, hy, addr_add hc, ← ex]
    exact hin
  · have : x.toNat = y.toNat + j := by
      rw [ex, BitVec.toNat_add, toNat_addr', toNat_ofNat_lt (by omega_using [hx, h4])]
      exact Nat.mod_eq_of_lt (by omega_using [hy', hx, h4])
    omega_using [this, hlt, hc]

/-- A byte written by a store that succeeded is in a frame or in a buffer. -/
theorem store_region {s : State} {F B : List Region} {a x : Addr} {n : Nat}
    (hw : s.wr = F ++ B) (hin : InRegions s.wr a n) (hx : (x - a).toNat < n) :
    (∃ g ∈ F, g.Contains x 1) ∨ ∃ g ∈ s.rd ++ B, g.Contains x 1 := by
  obtain ⟨g, hg, hc⟩ := hin
  have hcx := contains_of_access hc hx
  rw [hw] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact .inl ⟨g, hg, hcx⟩
  · exact .inr ⟨g, List.mem_append_right _ hg, hcx⟩

/-! ## Loads and stores -/

/-- The memory of a state with only its memory changed. -/
theorem AgreeOk.withMem {τ τ' : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {m₁ m₂ : Mem}
    (he : τ'.sp = τ.sp ∧ τ'.W = τ.W ∧ τ'.pub = τ.pub ∧ τ'.fl = τ.fl ∧ τ'.nf = τ.nf ∧
      τ'.wp = τ.wp ∧ τ'.bp = τ.bp)
    (hm : ∀ B, (∀ g ∈ s₁.rd ++ B, ∀ x, g.Contains x 1 → ¬ InWin τ s₁ x) →
      (∃ F, s₁.wr = F ++ B ∧ F.length = τ.nf ∧ Frames (wbA τ s₁) τ.W τ.sp F) →
      (∀ x, (∀ g ∈ s₁.rd ++ B, ¬ g.Contains x 1) → (InWin τ s₁ x → τ.sec.testBit (off τ s₁ x) = false) →
        s₁.mem x = s₂.mem x) →
      ∀ x, (∀ g ∈ s₁.rd ++ B, ¬ g.Contains x 1) → (InWin τ s₁ x → τ'.sec.testBit (off τ s₁ x) = false) →
        m₁ x = m₂ x) :
    AgreeOk τ' { s₁ with mem := m₁ } { s₂ with mem := m₂ } := by
  obtain ⟨hsp, hspN, hwbW, hpub, hfl, hwp, hbp, hrd, hwr, hunk, F, B, hw, hl, hf, hout, hmem⟩ := h
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := he
  have ewb : wb τ' { s₁ with mem := m₁ } = wb τ s₁ := by simp only [wb, e1]
  have ewbA : wbA τ' { s₁ with mem := m₁ } = wbA τ s₁ := by simp only [wbA, ewb]
  have ein : ∀ x, InWin τ' { s₁ with mem := m₁ } x ↔ InWin τ s₁ x := by
    intro x; simp only [InWin, off, ewbA, e2]
  refine ⟨hsp, by rw [e1]; exact hspN, by rw [ewb, e2]; exact hwbW, by rw [e3]; exact hpub,
    by rw [e4]; exact hfl, fun e he => ?_, fun e he => ?_, hrd, hwr, hunk,
    F, B, hw, by rw [e5]; exact hl, by rw [ewbA, e2, e1]; exact hf,
    fun g hg x hx => (not_congr (ein x)).mpr (hout g hg x hx), fun x hx hs => ?_⟩
  · rw [e6] at he; rw [ewb]; exact hwp e he
  · rw [e7] at he
    obtain ⟨h1, h2⟩ := hbp e he
    exact ⟨h1, fun i hi => (not_congr (ein _)).mpr (h2 i hi)⟩
  · exact hm B hout ⟨F, hw, hl, hf⟩ hmem x hx (fun hw' => by
      have := hs ((ein x).mpr hw')
      simpa only [off, ewbA] using this)

/-- A store of `n` bytes at `a` in both runs, of values that agree at each
byte where `τ'.sec` says the window is public, keeps what `τ` says of the
memory, with `τ'.sec` for the window's secret bytes, if `τ'.sec` makes secret
every byte not written that `τ.sec` does. -/
theorem AgreeOk.store {τ τ' : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {a : Addr} {n : Nat}
    {v₁ v₂ : BitVec (8 * n)}
    (he : τ'.sp = τ.sp ∧ τ'.W = τ.W ∧ τ'.pub = τ.pub ∧ τ'.fl = τ.fl ∧ τ'.nf = τ.nf ∧
      τ'.wp = τ.wp ∧ τ'.bp = τ.bp)
    (hwr : ∀ B, (∀ g ∈ s₁.rd ++ B, ∀ x, g.Contains x 1 → ¬ InWin τ s₁ x) →
      (∃ F, s₁.wr = F ++ B ∧ F.length = τ.nf ∧ Frames (wbA τ s₁) τ.W τ.sp F) →
      ∀ x, (x - a).toNat < n → (∀ g ∈ s₁.rd ++ B, ¬ g.Contains x 1) →
        (InWin τ s₁ x → τ'.sec.testBit (off τ s₁ x) = false) →
        v₁.extractLsb' (8 * (x - a).toNat) 8 = v₂.extractLsb' (8 * (x - a).toNat) 8)
    (hns : ∀ x, ¬ (x - a).toNat < n → InWin τ s₁ x → τ'.sec.testBit (off τ s₁ x) = false →
      τ.sec.testBit (off τ s₁ x) = false) :
    AgreeOk τ' { s₁ with mem := s₁.mem.write a n v₁ } { s₂ with mem := s₂.mem.write a n v₂ } := by
  refine h.withMem he fun B hout hF hmem x hx hs => ?_
  simp only [Mem.write]
  split
  · rename_i hw; exact hwr B hout hF x hw hx hs
  · rename_i hw; exact hmem x hx fun hw' => hns x hw hw' (hs hw')

/-- A store of `w` bytes (`0 < w ≤ 4`) through `n`, public, at `ofs`, of
values that are the same if `t` is public, keeps what `storeT` says. -/
theorem storeT_sound {τ : T} {s₁ s₂ : State} (ha : AgreeOk τ s₁ s₂) {n t : Reg} {ofs w : Nat}
    (hn : s₁.gpr n = s₂.gpr n) (hw4 : w ≤ 4) {v₁ v₂ : BitVec (8 * w)}
    (hin₁ : InRegions s₁.wr (State.addr (s₁.gpr n + BitVec.ofNat 32 ofs)) w)
    (hv : pubR τ t = true → v₁ = v₂) :
    AgreeOk (storeT τ (wpOf τ n) (bpOf τ n) ofs w (pubR τ t))
      { s₁ with mem := s₁.mem.write (State.addr (s₁.gpr n + BitVec.ofNat 32 ofs)) w v₁ }
      { s₂ with mem := s₂.mem.write (State.addr (s₂.gpr n + BitVec.ofNat 32 ofs)) w v₂ } := by
  rw [← hn]
  have hW : (wb τ s₁).toNat + τ.W < 2 ^ 32 := ha.wbW
  have hW64 : (wbA τ s₁).toNat + τ.W < 2 ^ 64 := by rw [toNat_wbA]; omega_using [hW]
  -- A public value, or the frames' bytes made secret.
  have pubCase : pubR τ t = true → AgreeOk τ
      { s₁ with mem := s₁.mem.write (State.addr (s₁.gpr n + BitVec.ofNat 32 ofs)) w v₁ }
      { s₂ with mem := s₂.mem.write (State.addr (s₁.gpr n + BitVec.ofNat 32 ofs)) w v₂ } := fun ht =>
    ha.store ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ _ _ x _ _ _ => by rw [hv ht]) (fun _ _ _ h => h)
  have frameCase : AgreeOk (framesSec τ)
      { s₁ with mem := s₁.mem.write (State.addr (s₁.gpr n + BitVec.ofNat 32 ofs)) w v₁ }
      { s₂ with mem := s₂.mem.write (State.addr (s₁.gpr n + BitVec.ofNat 32 ofs)) w v₂ } := by
    refine ha.store ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun B hout hF x hx hxo hsx => ?_) (fun x _ _ h => ?_)
    · obtain ⟨F, hw, -, hf⟩ := hF
      exfalso
      rcases store_region (B := B) hw hin₁ hx with ⟨g, hg, hc⟩ | ⟨g, hg, hc⟩
      · obtain ⟨h1, h2⟩ := Frames.contains (by omega_using [hW]) hf g hg x hc
        have hle := Frames.le hf
        have := hsx h2
        simp only [framesSec, testBit_bset, RTaint.off] at this
        simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
        omega_using [this.2, h1, h2, hle]
      · exact hxo g hg hc
    · simp only [framesSec, testBit_bset, Bool.or_eq_false_iff] at h; exact h.1
  have elseCase : AgreeOk (if pubR τ t = true then τ else framesSec τ)
      { s₁ with mem := s₁.mem.write (State.addr (s₁.gpr n + BitVec.ofNat 32 ofs)) w v₁ }
      { s₂ with mem := s₂.mem.write (State.addr (s₁.gpr n + BitVec.ofNat 32 ofs)) w v₂ } := by
    split
    · rename_i ht; exact pubCase ht
    · exact frameCase
  unfold storeT
  split
  · rename_i k hk
    obtain ⟨hk1, -⟩ := ha.wp _ (wpOf_mem hk)
    split
    · rename_i hinW
      have haddr := wp_addr (ofs := ofs) hk1 (by omega_using [hinW, hW])
      by_cases ht : pubR τ t = true
      · simp only [ht, ite_true]
        refine ha.store ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ _ _ x _ _ _ => by rw [hv ht])
          (fun x hx hw h => ?_)
        rw [haddr, in_range τ s₁ x (by omega_using [hinW, hW64])] at hx
        simp only [testBit_bclr, Bool.and_eq_false_iff, Bool.not_eq_false', Bool.and_eq_true,
          decide_eq_true_eq] at h
        rcases h with h | h
        · exact h
        · exact absurd h hx
      · simp only [ht, Bool.false_eq_true, ite_false]
        refine ha.store ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun B hout hF x hx hxo hsx => ?_)
          (fun x _ _ h => by simp only [testBit_bset, Bool.or_eq_false_iff] at h; exact h.1)
        exfalso
        rw [haddr, in_range τ s₁ x (by omega_using [hinW, hW64])] at hx
        have := hsx (by unfold InWin; omega_using [hx, hinW])
        simp only [testBit_bset, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
        omega_using [this.2, hx]
    · exact elseCase
  · split
    · rename_i b hb
      obtain ⟨-, hb2⟩ := ha.bp _ (bpOf_mem hb)
      split
      · rename_i hroom
        refine ha.store ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun B hout hF x hx hxo _ => ?_)
          (fun _ _ _ h => h)
        exfalso
        obtain ⟨F, hw, -, hf⟩ := hF
        have hnw := bp_byte hW hb2 hroom hw4 hx
        rcases store_region (B := B) hw hin₁ hx with ⟨g, hg, hc⟩ | ⟨g, hg, hc⟩
        · exact hnw (Frames.contains (by omega_using [hW]) hf g hg x hc).2
        · exact hxo g hg hc
      · exact elseCase
    · exact elseCase

/-- The `w` bytes at `ofs` from byte `k` of the window, if `loadPub` says
so, agree. -/
theorem load_bytes {τ : T} {s₁ s₂ : State} (ha : AgreeOk τ s₁ s₂) {k ofs w : Nat}
    (hp : loadPub τ (some k) ofs w = true) :
    ∀ j < w, s₁.mem (wbA τ s₁ + BitVec.ofNat 64 (k + ofs) + BitVec.ofNat 64 j) =
      s₂.mem (wbA τ s₁ + BitVec.ofNat 64 (k + ofs) + BitVec.ofNat 64 j) := by
  intro j hj
  simp only [loadPub, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨hin, hno⟩ := hp
  obtain ⟨F, B, -, -, -, hout, hmem⟩ := ha.regions
  have hW := ha.wbW
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hx : off τ s₁ (wbA τ s₁ + BitVec.ofNat 64 (k + ofs + j)) = k + ofs + j :=
    off_base τ s₁ (by omega_using [hin, hj, hW])
  refine hmem _ (fun g hg hc => hout g hg _ hc ?_) (fun _ => ?_)
  · unfold InWin; rw [hx]; omega_using [hin, hj]
  · rw [hx]; exact bnone_bit hno (by omega_using []) (by omega_using [hj])

theorem loadPub_some {τ : T} {k : Option Nat} {ofs w : Nat} (h : loadPub τ k ofs w = true) :
    ∃ k', k = some k' ∧ loadPub τ (some k') ofs w = true ∧ k' + ofs + w ≤ τ.W := by
  cases k with
  | none => cases h
  | some k' =>
    refine ⟨k', rfl, h, ?_⟩
    simp only [loadPub, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1

/-- A load of a word, at `ofs` from `v`, whose bytes `loadPub` says agree. -/
theorem load_word {τ : T} {s₁ s₂ : State} (ha : AgreeOk τ s₁ s₂) {v : BitVec 32} {kk : Option Nat}
    {ofs : Nat} (hv : ∀ k, kk = some k → v = wb τ s₁ + BitVec.ofNat 32 k)
    (hp : loadPub τ kk ofs 4 = true) :
    s₁.mem.readW (State.addr (v + BitVec.ofNat 32 ofs)) 32 = s₂.mem.readW (State.addr (v + BitVec.ofNat 32 ofs)) 32 := by
  obtain ⟨k, rfl, hp', hle⟩ := loadPub_some hp
  have hW := ha.wbW
  rw [wp_addr (hv k rfl) (by omega_using [hle, hW])]
  simp only [Mem.readW]
  rw [Mem.read_congr (load_bytes ha hp')]

/-- A load of a byte, at `ofs` from `v`, which `loadPub` says agrees. -/
theorem load_byte {τ : T} {s₁ s₂ : State} (ha : AgreeOk τ s₁ s₂) {v : BitVec 32} {kk : Option Nat}
    {ofs : Nat} (hv : ∀ k, kk = some k → v = wb τ s₁ + BitVec.ofNat 32 k)
    (hp : loadPub τ kk ofs 1 = true) :
    s₁.mem (State.addr (v + BitVec.ofNat 32 ofs)) = s₂.mem (State.addr (v + BitVec.ofNat 32 ofs)) := by
  obtain ⟨k, rfl, hp', hle⟩ := loadPub_some hp
  have hW := ha.wbW
  rw [wp_addr (hv k rfl) (by omega_using [hle, hW])]
  have := load_bytes ha hp' 0 (by decide)
  rwa [show BitVec.ofNat 64 0 = 0 from rfl, show ∀ a : Addr, a + 0 = a from fun a => BitVec.add_zero a] at this

/-- The stack pointer is at byte `τ.sp` of the window. -/
theorem sp_eq {τ : T} {s : State} : s.sp = wb τ s + BitVec.ofNat 32 τ.sp := by
  simp only [wb]; bv_omega

/-! ## Steps -/

theorem op2_val {τ : T} {s₁ s₂ : State} (ha : AgreeOk τ s₁ s₂) {op2 : Op2} (hp : op2Pub τ op2 = true)
    {y₁ y₂ : BitVec 32} (hy₁ : op2.eval s₁ = some y₁) (hy₂ : op2.eval s₂ = some y₂) : y₁ = y₂ := by
  rw [op2_eq ha hp, hy₂] at hy₁; cases hy₁; rfl

theorem imm_val {s : State} {v y : BitVec 32} (h : (Op2.imm v).eval s = some y) : y = v := by
  simp only [Op2.eval] at h
  split at h <;> [skip; cases h]
  cases h; rfl

theorem add_ofNat_toNat (a v : BitVec 32) (k : Nat) :
    a + BitVec.ofNat 32 k + v = a + BitVec.ofNat 32 (k + v.toNat) := by
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc]

theorem add_toNat_ofNat (g v : BitVec 32) (i : Nat) :
    g + v + BitVec.ofNat 32 i = g + BitVec.ofNat 32 (v.toNat + i) := by
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc]

theorem sub_ofNat_toNat (a v : BitVec 32) {k : Nat} (h : v.toNat ≤ k) :
    a + BitVec.ofNat 32 k - v = a + BitVec.ofNat 32 (k - v.toNat) := by
  have e : BitVec.ofNat 32 k = BitVec.ofNat 32 (k - v.toNat) + v := by
    calc BitVec.ofNat 32 k = BitVec.ofNat 32 (k - v.toNat) + BitVec.ofNat 32 v.toNat := by
          rw [← BitVec.ofNat_add, Nat.sub_add_cancel h]
      _ = BitVec.ofNat 32 (k - v.toNat) + v := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [e, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- A data-processing result of public operands is public. -/
theorem dp_gen {τ : T} {s₁ s₂ : State} (ha : AgreeOk τ s₁ s₂) {d n : Reg} {op2 : Op2} {y₁ y₂ : BitVec 32}
    (hy₁ : op2.eval s₁ = some y₁) (hy₂ : op2.eval s₂ = some y₂) {v₁ v₂ : BitVec 32}
    (hv : s₁.gpr n = s₂.gpr n → y₁ = y₂ → v₁ = v₂) :
    AgreeOk (RTaint.setR τ d (pubR τ n && op2Pub τ op2) none none) (s₁.setReg d v₁) (s₂.setReg d v₂) :=
  ha.setP d fun hp => by
    simp only [Bool.and_eq_true] at hp
    exact hv (ha.reg hp.1) (op2_val ha hp.2 hy₁ hy₂)

theorem stepB_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : AgreeOk τ s₁ s₂)
    (hb : ∀ n, base i = some n → pubR τ n = true) (hs : stepB τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') : AgreeOk τ' s₁' s₂' := by
  cases i with
  | blx | push | pop | alloc | free => simp only [stepB, reduceCtorEq] at hs
  | mov d op2 =>
    cases op2 with
    | reg r =>
      simp only [stepB, Option.some.injEq] at hs; subst hs
      simp only [reduceExec, Op2.eval, Option.map_some, Option.some.injEq] at e₁ e₂; subst e₁ e₂
      refine ha.setR d (fun hp => ha.reg hp) (fun k hk => ha.wp _ (wpOf_mem hk)) (fun b hb => ha.bp _ (bpOf_mem hb))
    | imm v =>
      simp only [stepB, Option.some.injEq] at hs; subst hs
      simp only [reduceExec, Option.map_eq_some_iff] at e₁ e₂
      obtain ⟨y₁, hy₁, rfl⟩ := e₁; obtain ⟨y₂, hy₂, rfl⟩ := e₂
      exact ha.setP d fun hp => by rw [op2_val ha hp hy₁ hy₂]
    | shifted r sh k =>
      simp only [stepB, Option.some.injEq] at hs; subst hs
      simp only [reduceExec, Option.map_eq_some_iff] at e₁ e₂
      obtain ⟨y₁, hy₁, rfl⟩ := e₁; obtain ⟨y₂, hy₂, rfl⟩ := e₂
      exact ha.setP d fun hp => by rw [op2_val ha hp hy₁ hy₂]
  | mvn d op2 =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, hy₁, rfl⟩ := e₁; obtain ⟨y₂, hy₂, rfl⟩ := e₂
    exact ha.setP d fun hp => by rw [op2_val ha hp hy₁ hy₂]
  | dp op d n op2 =>
    cases op <;> cases op2 <;> simp only [stepB, Option.some.injEq] at hs <;> subst hs <;>
      simp only [reduceExec, Option.map_eq_some_iff] at e₁ e₂ <;>
      obtain ⟨y₁, hy₁, rfl⟩ := e₁ <;> obtain ⟨y₂, hy₂, rfl⟩ := e₂ <;>
      first
      | exact dp_gen ha hy₁ hy₂ fun h1 h2 => by rw [h1, h2]
      | skip
    · -- `add d, n, #v`
      obtain rfl := imm_val hy₁; obtain rfl := imm_val hy₂
      refine ha.setR d (fun hp => by rw [ha.reg hp]) (fun k hk => ?_) (fun b hb => ?_)
      · simp only [Option.map_eq_some_iff] at hk
        obtain ⟨k₀, hk₀, rfl⟩ := hk
        obtain ⟨h1, h2⟩ := ha.wp _ (wpOf_mem hk₀)
        simp only at h1 h2
        exact ⟨by rw [h1, add_ofNat_toNat], by rw [h2]⟩
      · simp only [Option.bind_eq_some_iff] at hb
        obtain ⟨b₀, hb₀, hr⟩ := hb
        simp only [roomSub] at hr
        split at hr <;> [skip; cases hr]
        rename_i hle; cases hr
        obtain ⟨h1, h2⟩ := ha.bp _ (bpOf_mem hb₀)
        simp only at h1 h2
        refine ⟨by rw [h1], fun i hi => ?_⟩
        rw [add_toNat_ofNat]
        exact h2 _ (by omega_using [hi, hle])
    · -- `sub d, n, #v`
      obtain rfl := imm_val hy₁; obtain rfl := imm_val hy₂
      refine ha.setR d (fun hp => by rw [ha.reg hp]) (fun k hk => ?_) (fun _ h => nomatch h)
      simp only [Option.bind_eq_some_iff] at hk
      obtain ⟨k₀, hk₀, hr⟩ := hk
      simp only [offSub] at hr
      split at hr <;> [skip; cases hr]
      rename_i hle; cases hr
      obtain ⟨h1, h2⟩ := ha.wp _ (wpOf_mem hk₀)
      simp only at h1 h2
      exact ⟨by rw [h1, sub_ofNat_toNat _ _ hle], by rw [h2]⟩
  | adds d n op2 =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, hy₁, rfl⟩ := e₁; obtain ⟨y₂, hy₂, rfl⟩ := e₂
    have eq : (pubR τ n && op2Pub τ op2) = true → s₁.gpr n = s₂.gpr n ∧ y₁ = y₂ := fun hp => by
      simp only [Bool.and_eq_true] at hp
      exact ⟨ha.reg hp.1, op2_val ha hp.2 hy₁ hy₂⟩
    have hf := ha.setF (p := pubR τ n && op2Pub τ op2) (s₁' := addFlags s₁ (s₁.gpr n) y₁)
      (s₂' := addFlags s₂ (s₂.gpr n) y₂) (fun hp => by
        obtain ⟨h1, h2⟩ := eq hp
        simp only [FlagsEq, addFlags, h1, h2, and_self]) rfl rfl
    exact hf.setP d fun hp => by obtain ⟨h1, h2⟩ := eq hp; simp only [h1, h2]
  | subs d n op2 =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, hy₁, rfl⟩ := e₁; obtain ⟨y₂, hy₂, rfl⟩ := e₂
    have eq : (pubR τ n && op2Pub τ op2) = true → s₁.gpr n = s₂.gpr n ∧ y₁ = y₂ := fun hp => by
      simp only [Bool.and_eq_true] at hp
      exact ⟨ha.reg hp.1, op2_val ha hp.2 hy₁ hy₂⟩
    have hf := ha.setF (p := pubR τ n && op2Pub τ op2) (s₁' := subFlags s₁ (s₁.gpr n) y₁)
      (s₂' := subFlags s₂ (s₂.gpr n) y₂) (fun hp => by
        obtain ⟨h1, h2⟩ := eq hp
        simp only [FlagsEq, subFlags, h1, h2, and_self]) rfl rfl
    exact hf.setP d fun hp => by obtain ⟨h1, h2⟩ := eq hp; simp only [h1, h2]
  | cmp n op2 =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, hy₁, rfl⟩ := e₁; obtain ⟨y₂, hy₂, rfl⟩ := e₂
    exact ha.setF (fun hp => by
      simp only [Bool.and_eq_true] at hp
      simp only [FlagsEq, subFlags, ha.reg hp.1, op2_val ha hp.2 hy₁ hy₂, and_self]) rfl rfl
  | adc d n op2 =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, hy₁, rfl⟩ := e₁; obtain ⟨y₂, hy₂, rfl⟩ := e₂
    exact ha.setP d fun hp => by
      simp only [Bool.and_eq_true] at hp
      rw [ha.reg hp.1.1, op2_val ha hp.1.2 hy₁ hy₂, (ha.fl hp.2).2.2.1]
  | movw d imm =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ha.setPub d
  | movt d imm =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ha.setP d fun hp => by rw [ha.reg hp]
  | adrSym d name =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ha.setP d fun hp => nomatch hp
  | rev d m =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ha.setP d fun hp => by rw [ha.reg hp]
  | mul d n m =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ha.setP d fun hp => by simp only [Bool.and_eq_true] at hp; rw [ha.reg hp.1, ha.reg hp.2]
  | mla d n m a =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ha.setP d fun hp => by
      simp only [Bool.and_eq_true] at hp; rw [ha.reg hp.1.1, ha.reg hp.1.2, ha.reg hp.2]
  | umaal lo hi n m =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec] at e₁ e₂
    split at e₁ <;> [cases e₁; skip]
    rename_i hne
    simp only [hne, ↓reduceIte] at e₂
    simp only [Option.some.injEq] at e₁ e₂; subst e₁ e₂
    have eq : (pubR τ n && pubR τ m && pubR τ lo && pubR τ hi) = true →
        s₁.gpr n = s₂.gpr n ∧ s₁.gpr m = s₂.gpr m ∧ s₁.gpr lo = s₂.gpr lo ∧ s₁.gpr hi = s₂.gpr hi := by
      intro hp; simp only [Bool.and_eq_true] at hp
      exact ⟨ha.reg hp.1.1.1, ha.reg hp.1.1.2, ha.reg hp.1.2, ha.reg hp.2⟩
    exact (ha.setP lo fun hp => by obtain ⟨h1, h2, h3, h4⟩ := eq hp; rw [h1, h2, h3, h4]).setP hi
      fun hp => by obtain ⟨h1, h2, h3, h4⟩ := eq hp; rw [h1, h2, h3, h4]
  | ldr t n ofs =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    have hn := ha.reg (hb n rfl)
    simp only [reduceExec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hlt; simp only [hlt, ↓reduceIte] at e₂
    simp only [State.load32, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨x₁, hx₁, rfl⟩ := e₁; obtain ⟨x₂, hx₂, rfl⟩ := e₂
    split at hx₁ <;> [skip; cases hx₁]
    split at hx₂ <;> [skip; cases hx₂]
    cases hx₁; cases hx₂
    exact ha.setP t fun hp => by
      rw [← hn]; exact load_word ha (fun k hk => (ha.wp _ (wpOf_mem hk)).1) hp
  | ldrb t n ofs =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    have hn := ha.reg (hb n rfl)
    simp only [reduceExec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hlt; simp only [hlt, ↓reduceIte] at e₂
    simp only [State.load8, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨x₁, hx₁, rfl⟩ := e₁; obtain ⟨x₂, hx₂, rfl⟩ := e₂
    split at hx₁ <;> [skip; cases hx₁]
    split at hx₂ <;> [skip; cases hx₂]
    cases hx₁; cases hx₂
    exact ha.setP t fun hp => by
      rw [← hn, load_byte ha (fun k hk => (ha.wp _ (wpOf_mem hk)).1) hp]
  | ldrSp t ofs =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hlt; simp only [hlt, ↓reduceIte] at e₂
    simp only [State.load32, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨x₁, hx₁, rfl⟩ := e₁; obtain ⟨x₂, hx₂, rfl⟩ := e₂
    split at hx₁ <;> [skip; cases hx₁]
    split at hx₂ <;> [skip; cases hx₂]
    cases hx₁; cases hx₂
    exact ha.setP t fun hp => by
      rw [← ha.sp]; exact load_word ha (fun k hk => by cases hk; exact sp_eq) hp
  | str t n ofs =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    have hn := ha.reg (hb n rfl)
    simp only [reduceExec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hlt; simp only [hlt, ↓reduceIte] at e₂
    simp only [State.store32] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hin₁
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact storeT_sound (w := 4) ha hn (by decide) hin₁ fun ht => by rw [ha.reg ht]
  | strb t n ofs =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    have hn := ha.reg (hb n rfl)
    simp only [reduceExec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hlt; simp only [hlt, ↓reduceIte] at e₂
    simp only [State.store8] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hin₁
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact storeT_sound (w := 1) ha hn (by decide) hin₁ fun ht => by rw [ha.reg ht]
  | addSp d imm =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hlt; simp only [hlt, ↓reduceIte] at e₂
    simp only [Option.some.injEq] at e₁ e₂; subst e₁ e₂
    refine ha.setR d (fun _ => by rw [ha.sp]) (fun k' hk => ?_) (fun _ h => nomatch h)
    cases hk
    refine ⟨?_, by rw [ha.sp]⟩
    rw [sp_eq (τ := τ) (s := s₁), BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem base_eq {i : Instr} {n : Reg} (h : base i = some n) (s₁ s₂ : State)
    (ha : addrs i s₁ = addrs i s₂) : s₁.gpr n = s₂.gpr n := by
  cases i <;> simp only [base, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
  · simp only [addrs, List.cons.injEq, and_true] at ha
    exact (BitVec.add_left_inj _).mp (addr_inj ha)

theorem pubR_withPub (τ : T) (n : Reg) : pubR (RTaint.withPub τ n) n = true :=
  RegSet.mem_insert.mpr (.inl rfl)

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂')
    (hadr : addrs i s₁ = addrs i s₂) : Agree τ' s₁' s₂' := by
  intro _
  unfold step at hs
  split at hs <;> [skip; cases hs]
  rename_i hok
  have h := ha hok
  split at hs
  · rename_i n hn
    refine stepB_sound (h.withPub (base_eq hn s₁ s₂ hadr)) (fun n' hn' => ?_) hs e₁ e₂
    rw [hn] at hn'; cases hn'; exact pubR_withPub τ n
  · rename_i hn
    exact stepB_sound h (fun n' hn' => absurd hn' (by rw [hn]; simp)) hs e₁ e₂

theorem addrs_length (i : Instr) (s₁ s₂ : State) : (addrs i s₁).length = (addrs i s₂).length := by
  cases i <;> simp [addrs, words]

/-! ## Knowing less -/

/-- What `σ` says, `τ` says if it knows no more. -/
theorem AgreeOk.weaken {τ σ : T} {s₁ s₂ : State} (h : AgreeOk σ s₁ s₂) (hsp : τ.sp = σ.sp)
    (hW : τ.W = σ.W) (hnf : τ.nf = σ.nf) (hpub : ∀ r ∈ τ.pub, r ∈ σ.pub) (hfl : τ.fl = true → σ.fl = true)
    (hwp : ∀ e ∈ τ.wp, e ∈ σ.wp) (hbp : ∀ e ∈ τ.bp, ∃ b, (e.1, b) ∈ σ.bp ∧ e.2 ≤ b)
    (hsec : ∀ k, σ.sec.testBit k = true → τ.sec.testBit k = true) : AgreeOk τ s₁ s₂ := by
  obtain ⟨hsp', hspN, hwbW, hpub', hfl', hwp', hbp', hrd, hwr, hunk, F, B, hw, hl, hf, hout, hmem⟩ := h
  have ewb : wb τ s₁ = wb σ s₁ := by simp only [wb, hsp]
  have ewbA : wbA τ s₁ = wbA σ s₁ := by simp only [wbA, ewb]
  have ein : ∀ x, InWin τ s₁ x ↔ InWin σ s₁ x := by intro x; simp only [InWin, off, ewbA, hW]
  refine ⟨hsp', by rw [hsp]; exact hspN, by rw [ewb, hW]; exact hwbW, fun r hr => hpub' r (hpub r hr),
    fun h => hfl' (hfl h), fun e he => by rw [ewb]; exact hwp' e (hwp e he), fun e he => ?_, hrd, hwr, hunk,
    F, B, hw, by rw [hnf]; exact hl, by rw [ewbA, hW, hsp]; exact hf,
    fun g hg x hx => (not_congr (ein x)).mpr (hout g hg x hx), fun x hx hs => ?_⟩
  · obtain ⟨b, hb, hle⟩ := hbp e he
    obtain ⟨h1, h2⟩ := hbp' _ hb
    exact ⟨h1, fun i hi => (not_congr (ein _)).mpr (h2 i (by omega_using [hi, hle]))⟩
  · refine hmem x hx fun hw' => ?_
    have h1 := hs ((ein x).mpr hw')
    have e : off τ s₁ x = off σ s₁ x := by simp only [off, ewbA]
    rw [e] at h1
    cases hk : σ.sec.testBit (off σ s₁ x)
    · rfl
    · rw [hsec _ hk] at h1; cases h1

theorem meet_left {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₁ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ := by
  unfold meet
  split
  · rename_i hc
    intro _
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩ := hc
    refine (h h1).weaken rfl rfl rfl (fun r hr => (RegSet.mem_inter.mp hr).1)
      (fun hf => by simp only [Bool.and_eq_true] at hf; exact hf.1)
      (fun e he => (List.mem_filter.mp he).1) (fun e he => ?_) (fun k hk => ?_)
    · obtain ⟨e', he', hm⟩ := List.mem_filterMap.mp he
      split at hm
      · obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp hm
        exact ⟨e'.2, he', Nat.min_le_left _ _⟩
      · cases hm
    · show (τ₁.sec ||| τ₂.sec).testBit k = true
      rw [Nat.testBit_or, hk, Bool.true_or]
  · intro hok; simp only [bot] at hok; cases hok

theorem meet_right {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₂ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ := by
  unfold meet
  split
  · rename_i hc
    intro _
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨-, h2⟩, hW⟩, hsp⟩, hnf⟩ := hc
    refine (h h2).weaken hsp hW hnf (fun r hr => (RegSet.mem_inter.mp hr).2)
      (fun hf => by simp only [Bool.and_eq_true] at hf; exact hf.2)
      (fun e he => ?_) (fun e he => ?_) (fun k hk => ?_)
    · obtain ⟨-, hm⟩ := List.mem_filter.mp he
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      exact wpOf_mem hm.1
    · obtain ⟨e', -, hm⟩ := List.mem_filterMap.mp he
      split at hm
      · obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hm
        exact ⟨b, bpOf_mem hb, Nat.min_le_right _ _⟩
      · cases hm
    · show (τ₁.sec ||| τ₂.sec).testBit k = true
      rw [Nat.testBit_or, hk, Bool.or_true]
  · intro hok; simp only [bot] at hok; cases hok

theorem le_sound {τ σ : T} {s₁ s₂ : State} (hle : le τ σ = true) (h : Agree σ s₁ s₂) : Agree τ s₁ s₂ := by
  intro hok
  simp only [le, hok, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    at hle
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hσ, hW⟩, hsp⟩, hnf⟩, hpub⟩, hfl⟩, hwp⟩, hbp⟩, hsec⟩ := hle
  refine (h hσ).weaken hsp hW hnf (fun r hr => RegSet.mem_of_subset hpub hr)
    (fun hf => by simp only [hf, Bool.not_true, Bool.false_or] at hfl; exact hfl)
    (fun e he => wpOf_mem (hwp e he)) (fun e he => ?_) (fun k hk => bsub_bit hsec hk)
  have := hbp e he
  split at this
  · rename_i b hb
    exact ⟨b, bpOf_mem hb, Nat.le_of_ble_eq_true this⟩
  · cases this

/-! ## Frames -/

/-- The bytes of a frame of `b` bytes below the stack pointer are those from
offset `τ.sp - b` to `τ.sp` of the window. -/
theorem below_iff {τ : T} {s : State} (hW : (wb τ s).toNat + τ.W < 2 ^ 32) (hsp : τ.sp ≤ s.sp.toNat)
    (hle : τ.sp ≤ τ.W) {b : Nat} (hb : b ≤ τ.sp) (x : Addr) :
    (belowA s.sp b).Contains x 1 ↔ τ.sp - b ≤ off τ s x ∧ off τ s x < τ.sp := by
  have e : State.addr (s.sp - BitVec.ofNat 32 b) = wbA τ s + BitVec.ofNat 64 (τ.sp - b) := by
    rw [← addr_wb τ s (by omega_using [hW, hle, hb])]
    congr 1
    rw [sp_eq (τ := τ) (s := s), ← BitVec.ofNat_sub_ofNat_of_le (w := 32) _ _
      (by have := s.sp.isLt; omega_using [this, hsp, hb]) hb]
    bv_omega
  simp only [Region.Contains, e]
  rw [Nat.add_one_le_iff, Offset.lt_iff x (wbA τ s) (by omega_using [hW, hle, hb])]
  unfold off
  omega_using [hb]

/-- `wb` after the stack pointer moved down by `b` and the analysis's by as much. -/
theorem wb_down {τ : T} {s : State} {b : Nat} (hb : b ≤ τ.sp) (hsp : τ.sp ≤ s.sp.toNat) :
    (s.sp - BitVec.ofNat 32 b) - BitVec.ofNat 32 (τ.sp - b) = wb τ s := by
  simp only [wb]
  rw [← BitVec.ofNat_sub_ofNat_of_le (w := 32) _ _ (by have := s.sp.isLt; omega_using [this, hsp, hb]) hb]
  bv_omega

/-- A frame of `b` bytes opened below the others: the stack pointer `b`
bytes down, a writable region of them, and memory changed only within it,
where the bytes `sec'` says are public agree, `sec'` making secret every
other byte of the window `τ.sec` does. -/
theorem open_ok {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {b : Nat} (hb : b ≤ τ.sp)
    (hb0 : 0 < b) {sec' : Nat} {m₁ m₂ : Mem}
    (hf₁ : Frame [belowA s₁.sp b] s₁.mem m₁) (hf₂ : Frame [belowA s₁.sp b] s₂.mem m₂)
    (hin : ∀ x, (belowA s₁.sp b).Contains x 1 → sec'.testBit (off τ s₁ x) = false →
      (∀ g ∈ s₁.rd, ¬ g.Contains x 1) → m₁ x = m₂ x)
    (hout : ∀ x, ¬ (belowA s₁.sp b).Contains x 1 → InWin τ s₁ x → sec'.testBit (off τ s₁ x) = false →
      τ.sec.testBit (off τ s₁ x) = false) :
    AgreeOk { τ with sp := τ.sp - b, nf := τ.nf + 1, sec := sec' }
      { s₁ with sp := s₁.sp - BitVec.ofNat 32 b, mem := m₁, wr := ⟨State.addr (s₁.sp - BitVec.ofNat 32 b), b⟩ :: s₁.wr }
      { s₂ with sp := s₂.sp - BitVec.ofNat 32 b, mem := m₂, wr := ⟨State.addr (s₂.sp - BitVec.ofNat 32 b), b⟩ :: s₂.wr } := by
  obtain ⟨hsp, hspN, hwbW, hpub, hfl, hwp, hbp, hrd, hwr, hunk, F, B, hw, hl, hf, hout', hmem⟩ := h
  have hle : τ.sp ≤ τ.W := Frames.le hf
  have hbs : b ≤ s₁.sp.toNat := by omega_using [hb, hspN]
  have ewb : wb { τ with sp := τ.sp - b, nf := τ.nf + 1, sec := sec' }
      { s₁ with sp := s₁.sp - BitVec.ofNat 32 b, mem := m₁, wr := ⟨State.addr (s₁.sp - BitVec.ofNat 32 b), b⟩ :: s₁.wr } = wb τ s₁ := wb_down hb hspN
  have ewbA : wbA { τ with sp := τ.sp - b, nf := τ.nf + 1, sec := sec' }
      { s₁ with sp := s₁.sp - BitVec.ofNat 32 b, mem := m₁, wr := ⟨State.addr (s₁.sp - BitVec.ofNat 32 b), b⟩ :: s₁.wr } = wbA τ s₁ := by
    simp only [wbA, ewb]
  have hbi := below_iff hwbW hspN hle hb
  refine ⟨by rw [hsp], ?_, by rw [ewb]; exact hwbW, hpub, hfl, fun e he => by rw [ewb]; exact hwp e he,
    fun e he => ?_, hrd, by rw [hwr, hsp], hunk,
    ⟨State.addr (s₁.sp - BitVec.ofNat 32 b), b⟩ :: F, B, by rw [hw]; rfl,
    by simp only [List.length_cons, hl], ?_, ?_, ?_⟩
  · show τ.sp - b ≤ (s₁.sp - BitVec.ofNat 32 b).toNat
    rw [sub_toNat' hbs]
    omega_using [hspN]
  · obtain ⟨h1, h2⟩ := hbp e he
    exact ⟨h1, fun i hi => by unfold InWin off; rw [ewbA]; exact h2 i hi⟩
  · rw [ewbA]
    refine ⟨?_, hb0, ?_⟩
    · show State.addr (s₁.sp - BitVec.ofNat 32 b) = wbA τ s₁ + BitVec.ofNat 64 (τ.sp - b)
      rw [← addr_wb τ s₁ (by omega_using [hwbW, hle, hb]), ← wb_down hb hspN, BitVec.sub_add_cancel]
    · rw [show τ.sp - b + b = τ.sp by omega_using [hb]]; exact hf
  · intro g hg x hx
    unfold InWin off; rw [ewbA]; exact hout' g hg x hx
  · intro x hx hs
    have hs' : InWin τ s₁ x → sec'.testBit (off τ s₁ x) = false := fun hw' => by
      have := hs (by unfold InWin off; rw [ewbA]; exact hw')
      simpa only [off, ewbA] using this
    by_cases hc : (belowA s₁.sp b).Contains x 1
    · refine hin x hc (hs' ?_) (fun g hg => hx g (List.mem_append_left _ hg))
      unfold InWin; have := (hbi x).mp hc; omega_using [this, hle]
    · show m₁ x = m₂ x
      rw [hf₁ x (by simp only [List.mem_singleton]; rintro _ rfl; exact hc),
        hf₂ x (by simp only [List.mem_singleton]; rintro _ rfl; exact hc)]
      exact hmem x hx fun hw' => hout x hc hw' (hs' hw')

/-- What the words stored at `a` leave in their bytes does not depend on the
memory before. -/
theorem storeWords_in : ∀ (vs : List (BitVec 32)) (m₁ m₂ : Mem) (a : BitVec 32),
    a.toNat + 4 * vs.length ≤ 2 ^ 32 → ∀ x, (⟨State.addr a, 4 * vs.length⟩ : Region).Contains x 1 →
      storeWords m₁ a vs x = storeWords m₂ a vs x
  | [], _, _, _, _, x, hx => by simp only [Region.Contains, List.length_nil] at hx; omega_using [hx]
  | v :: vs, m₁, m₂, a, h, x, hx => by
    simp only [storeWords]
    simp only [List.length_cons] at h hx
    have h4 : a.toNat + 4 < 2 ^ 32 ∨ vs = [] := by
      cases vs with
      | nil => exact .inr rfl
      | cons _ _ => left; simp only [List.length_cons] at h; omega_using [h]
    by_cases hr : (⟨State.addr (a + 4), 4 * vs.length⟩ : Region).Contains x 1
    · exact storeWords_in vs _ _ (a + 4) (by
        rcases h4 with h4 | rfl
        · rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (a := 4) (by omega_using []), Nat.mod_eq_of_lt h4]; omega_using [h]
        · simp only [List.length_nil]; have := (a + 4).isLt; omega_using [this]) x hr
    · have hn₁ := storeWords_frame vs (m₁.writeW (State.addr a) v) (a + 4)
      have hn₂ := storeWords_frame vs (m₂.writeW (State.addr a) v) (a + 4)
      have hlen : (a + 4).toNat + 4 * vs.length ≤ 2 ^ 32 := by
        rcases h4 with h4 | rfl
        · rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (a := 4) (by omega_using []), Nat.mod_eq_of_lt h4]; omega_using [h]
        · simp only [List.length_nil]; have := (a + 4).isLt; omega_using [this]
      rw [hn₁ hlen x (by simp only [List.mem_singleton]; rintro _ rfl; exact hr),
        hn₂ hlen x (by simp only [List.mem_singleton]; rintro _ rfl; exact hr)]
      have hx4 : (x - State.addr a).toNat < 4 := by
        simp only [Region.Contains] at hx hr
        rcases h4 with h4 | rfl
        · rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, addr_add h4] at hr
          have hr' : ¬ (x - (State.addr a + BitVec.ofNat 64 4)).toNat < 4 * vs.length :=
            fun hc => hr (by omega_using [hc])
          rw [Offset.lt_iff x (State.addr a) (d := 4) (n := 4 * vs.length) (by omega_using [h])] at hr'
          omega_using [hr', hx]
        · simp only [List.length_nil] at hx; omega_using [hx]
      simp only [Mem.writeW, Mem.write, show (x - State.addr a).toNat < 32 / 8 from hx4, ite_true]

theorem alloc_sound {τ τ' : T} {b : Nat} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : push τ (.alloc b) = some τ') (e₁ : isa.push (.alloc b) s₁ = some s₁')
    (e₂ : isa.push (.alloc b) s₂ = some s₂') : Agree τ' s₁' s₂' := by
  intro _
  simp only [push] at hs
  split at hs <;> [skip; cases hs]
  rename_i hc
  cases hs
  simp only [Bool.and_eq_true, Nat.ble_eq] at hc
  simp only [isa, Arm.push] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  rename_i hc₁
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  have h := ha hc.1
  have hW := h.wbW
  have hle : τ.sp ≤ τ.W := by obtain ⟨F, B, -, -, hf, -⟩ := h.regions; exact Frames.le hf
  have := open_ok (sec' := τ.sec) (m₁ := s₁.mem) (m₂ := s₂.mem) h hc.2 hc₁.1 (Frame.refl _ _) (Frame.refl _ _)
    (fun x hx hs hrd => by
      obtain ⟨F, B, -, -, -, hout, hmem⟩ := h.regions
      have hi := (below_iff hW h.spNat hle hc.2 x).mp hx
      have hwin : InWin τ s₁ x := by unfold InWin; omega_using [hi, hle]
      refine hmem x (fun g hg hcx => ?_) (fun _ => hs)
      exact hout g hg x hcx hwin)
    (fun _ _ _ h => h)
  exact this

/-- A `push` of the registers `rs`: a frame of their words, public if they all are. -/
theorem pushRegs_sound {τ τ' : T} {rs : List Reg} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : push τ (.push rs) = some τ') (e₁ : isa.push (.push rs) s₁ = some s₁')
    (e₂ : isa.push (.push rs) s₂ = some s₂') : Agree τ' s₁' s₂' := by
  intro _
  simp only [push] at hs
  split at hs <;> [skip; cases hs]
  rename_i hc
  cases hs
  simp only [Bool.and_eq_true, Nat.ble_eq] at hc
  simp only [isa, Arm.push] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  rename_i hc₁
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  have h := ha hc.1
  have hW := h.wbW
  have hsp := h.sp
  have hle : τ.sp ≤ τ.W := by obtain ⟨F, B, -, -, hf, -⟩ := h.regions; exact Frames.le hf
  have hrs0 : 0 < rs.length := by
    cases rs with
    | nil => simp only [regList] at hc₁; exact absurd hc₁.1 (by decide)
    | cons _ _ => simp only [List.length_cons]; omega_using []
  have hbs : 4 * rs.length ≤ s₁.sp.toNat := hc₁.2
  have hlen : (s₁.sp - BitVec.ofNat 32 (4 * rs.length)).toNat + 4 * (rs.map s₁.gpr).length ≤ 2 ^ 32 := by
    rw [sub_toNat' hbs, List.length_map]; have := s₁.sp.isLt; omega_using [this, hbs]
  have hf₁ := storeWords_frame (rs.map s₁.gpr) s₁.mem _ hlen
  have hf₂ : Frame [belowA s₁.sp (4 * rs.length)] s₂.mem
      (storeWords s₂.mem (s₂.sp - BitVec.ofNat 32 (4 * rs.length)) (rs.map s₂.gpr)) := by
    rw [← hsp]
    have := storeWords_frame (rs.map s₂.gpr) s₂.mem (s₁.sp - BitVec.ofNat 32 (4 * rs.length))
      (by rw [List.length_map]; rw [List.length_map] at hlen; exact hlen)
    rwa [List.length_map] at this
  rw [List.length_map] at hf₁
  have hbi := below_iff hW h.spNat hle hc.2
  refine open_ok h hc.2 (by omega_using [hrs0]) hf₁ hf₂ (fun x hx hs _ => ?_) (fun x hx _ hs => ?_)
  · split at hs
    · rename_i hall
      have e : rs.map s₁.gpr = rs.map s₂.gpr := List.map_congr_left fun r hr => h.reg (List.all_eq_true.mp hall r hr)
      rw [e, ← hsp]
      exact storeWords_in _ _ _ _ (by rw [List.length_map]; rw [List.length_map] at hlen; exact hlen) x
        (by rw [List.length_map]; exact hx)
    · simp only [testBit_bset, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hs
      have := (hbi x).mp hx
      omega_using [hs.2, this]
  · split at hs
    · simp only [testBit_bclr, Bool.and_eq_false_iff, Bool.not_eq_false', Bool.and_eq_true,
        decide_eq_true_eq] at hs
      rcases hs with hs | hs
      · exact hs
      · exact absurd ((hbi x).mpr ⟨hs.1, by omega_using [hs.2, hc.2]⟩) hx
    · simp only [testBit_bset, Bool.or_eq_false_iff] at hs; exact hs.1

theorem push_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : push τ i = some τ') (e₁ : isa.push i s₁ = some s₁') (e₂ : isa.push i s₂ = some s₂')
    (_hadr : isa.addrs i s₁ = isa.addrs i s₂) : Agree τ' s₁' s₂' := by
  cases i with
  | alloc b => exact alloc_sound ha hs e₁ e₂
  | push rs => exact pushRegs_sound ha hs e₁ e₂
  | _ => simp only [push, reduceCtorEq] at hs

/-- The innermost frame, of `b` bytes, released. -/
theorem free_ok {τ : T} {b₁ b₂ : State} (h : AgreeOk τ b₁ b₂) {b : Nat} (hnf : 0 < τ.nf)
    (hle : τ.sp + b ≤ τ.W) (hhd : b₁.wr.head? = some ⟨State.addr b₁.sp, b⟩) :
    AgreeOk { τ with sp := τ.sp + b, nf := τ.nf - 1 }
      { b₁ with sp := b₁.sp + BitVec.ofNat 32 b, wr := b₁.wr.tail, mem := lose b₁.mem (State.addr b₁.sp) b b₁.unknowns, unknowns := fun k => b₁.unknowns (k + b / 2) }
      { b₂ with sp := b₂.sp + BitVec.ofNat 32 b, wr := b₂.wr.tail, mem := lose b₂.mem (State.addr b₂.sp) b b₂.unknowns, unknowns := fun k => b₂.unknowns (k + b / 2) } := by
  obtain ⟨hsp, hspN, hwbW, hpub, hfl, hwp, hbp, hrd, hwr, hunk, F, B, hw, hl, hf, hout, hmem⟩ := h
  obtain ⟨f, F', rfl⟩ : ∃ f F', F = f :: F' := by
    cases F with
    | nil => simp only [List.length_nil] at hl; omega_using [hl, hnf]
    | cons f F' => exact ⟨f, F', rfl⟩
  obtain ⟨hfb, hfl', hf'⟩ := hf
  have hfe : f = ⟨State.addr b₁.sp, b⟩ := by
    rw [hw] at hhd
    simpa using hhd
  have hlen : f.len = b := by rw [hfe]
  rw [hlen] at hf'
  have htn : (wb τ b₁).toNat + τ.sp = b₁.sp.toNat := by
    simp only [wb]; rw [sub_toNat' hspN]; omega_using [hspN]
  have ewb : wb { τ with sp := τ.sp + b, nf := τ.nf - 1 }
      { b₁ with sp := b₁.sp + BitVec.ofNat 32 b, wr := b₁.wr.tail, mem := lose b₁.mem (State.addr b₁.sp) b b₁.unknowns, unknowns := fun k => b₁.unknowns (k + b / 2) } =
      wb τ b₁ := by
    simp only [wb, BitVec.ofNat_add]; bv_omega
  have ewbA : wbA { τ with sp := τ.sp + b, nf := τ.nf - 1 }
      { b₁ with sp := b₁.sp + BitVec.ofNat 32 b, wr := b₁.wr.tail, mem := lose b₁.mem (State.addr b₁.sp) b b₁.unknowns, unknowns := fun k => b₁.unknowns (k + b / 2) } =
      wbA τ b₁ := by simp only [wbA, ewb]
  refine ⟨by rw [hsp], ?_, by rw [ewb]; exact hwbW, hpub, hfl, fun e he => by rw [ewb]; exact hwp e he,
    fun e he => ?_, hrd, by rw [hwr], by rw [hunk], F', B, by rw [hw]; rfl,
    by simp only [List.length_cons] at hl; show F'.length = τ.nf - 1; omega_using [hl],
    by rw [ewbA]; exact hf', ?_, ?_⟩
  · show τ.sp + b ≤ (b₁.sp + BitVec.ofNat 32 b).toNat
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := b) (by omega_using [htn, hle, hwbW]),
      Nat.mod_eq_of_lt (by omega_using [htn, hle, hwbW])]
    omega_using [hspN]
  · obtain ⟨h1, h2⟩ := hbp e he
    exact ⟨h1, fun i hi => by unfold InWin off; rw [ewbA]; exact h2 i hi⟩
  · intro g hg x hx
    unfold InWin off; rw [ewbA]; exact hout g hg x hx
  · intro x hx hs
    simp only [lose, hsp, hunk]
    split
    · split
      · exact hmem x hx fun hw' => by
          have := hs (by unfold InWin off; rw [ewbA]; exact hw')
          simpa only [off, ewbA] using this
      · rfl
    · exact hmem x hx fun hw' => by
        have := hs (by unfold InWin off; rw [ewbA]; exact hw')
        simpa only [off, ewbA] using this

/-- The first word of the innermost frame, read in both runs: the same if
its bytes are not secret. -/
theorem popRead_eq {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) (hle : τ.sp + 4 ≤ τ.W)
    (hno : bnone τ.sec τ.sp 4 = true) :
    s₁.mem.readW (State.addr s₁.sp) 32 = s₂.mem.readW (State.addr s₂.sp) 32 := by
  rw [← h.sp]
  have e : s₁.sp = s₁.sp + BitVec.ofNat 32 0 := (BitVec.add_zero s₁.sp).symm
  rw [e]
  exact load_word h (kk := some τ.sp) (fun k hk => by cases hk; exact sp_eq)
    (by simp only [loadPub, Nat.add_zero, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hle, hno⟩)

theorem pop_sound {τ τ' : T} {j : Instr} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (ha : Agree τ b₁ b₂)
    (hs : pop τ j = some τ') (e₁ : isa.pop j a₁ b₁ = some c₁) (e₂ : isa.pop j a₂ b₂ = some c₂)
    (_hadr : isa.addrs j b₁ = isa.addrs j b₂) : Agree τ' c₁ c₂ := by
  intro _
  cases j with
  | free b =>
    simp only [pop] at hs
    split at hs <;> [skip; cases hs]
    rename_i hc
    cases hs
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
    obtain ⟨⟨hok, hnf⟩, hle⟩ := hc
    simp only [isa, Arm.pop] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hc₁
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    obtain ⟨-, -, -, -, hsp₁, hwr₁, hhd⟩ := hc₁
    exact free_ok (ha hok) hnf hle (by rw [← hsp₁, ← hwr₁] at hhd; exact hhd)
  | pop t n =>
    simp only [pop] at hs
    split at hs <;> [skip; cases hs]
    rename_i hc
    cases hs
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
    obtain ⟨⟨⟨hok, hnf⟩, hle⟩, hle4⟩ := hc
    have h := ha hok
    simp only [isa, Arm.pop] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hc₁
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    obtain ⟨-, -, hsp₁, hwr₁, hhd⟩ := hc₁
    have hr := h.setP t (p := bnone τ.sec τ.sp 4)
      (v₁ := b₁.mem.readW (State.addr b₁.sp) 32) (v₂ := b₂.mem.readW (State.addr b₂.sp) 32)
      (fun hp => popRead_eq h hle4 hp)
    exact free_ok (b := n) hr hnf hle (by rw [← hsp₁, ← hwr₁] at hhd; exact hhd)
  | _ => simp only [pop, reduceCtorEq] at hs

/-! ## Calls -/

theorem call_sound {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂) (hs : RTaint.call τ = some τ')
    (e₁ : isa.call s₁ = some s₁') (e₂ : isa.call s₂ = some s₂')
    (_hadr : isa.callAddrs s₁ = isa.callAddrs s₂) : Agree τ' s₁' s₂' := by
  intro _
  simp only [RTaint.call] at hs
  split at hs <;> [skip; cases hs]
  rename_i hok
  cases hs
  simp only [isa, Arm.call, Option.some.injEq] at e₁ e₂
  subst e₁ e₂
  have h := ha hok
  have hu := h.unk
  have h2 := (h.setP .lr (p := true) (v₁ := s₁.unknowns 0) (v₂ := s₂.unknowns 0) fun _ => by rw [hu]).setP .r12
    (p := true) (v₁ := s₁.unknowns 1) (v₂ := s₂.unknowns 1) fun _ => by rw [hu]
  obtain ⟨hsp, hspN, hwbW, hpub, -, hwp, hbp, hrd, hwr, -, hreg⟩ := h2
  exact ⟨hsp, hspN, hwbW, hpub, fun _ => by simp only [FlagsEq, hu, and_self], hwp, hbp, hrd, hwr,
    by simp only [hu], hreg⟩

theorem ret_sound {τ τ' : T} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (ha : Agree τ b₁ b₂)
    (hs : RTaint.ret τ = some τ') (e₁ : isa.ret a₁ b₁ = some c₁) (e₂ : isa.ret a₂ b₂ = some c₂)
    (_hadr : isa.retAddrs b₁ = isa.retAddrs b₂) : Agree τ' c₁ c₂ := by
  simp only [RTaint.ret] at hs
  split at hs <;> [skip; cases hs]
  cases hs
  simp only [isa, Arm.ret] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  exact ha

end RTaint

open RTaint in
/-- The residue analysis, for two runs that leak the same (see `RTaint`). -/
def rtaint : VG.TaintCT isa where
  T := RTaint.T
  Agree := RTaint.Agree
  step := RTaint.stepK
  step_sound ha hs e₁ e₂ hadr := RTaint.step_sound ha ((RTaint.stepK_eq _ _).symm.trans hs) e₁ e₂ hadr
  addrs_length := RTaint.addrs_length
  meet := RTaint.meetK
  meet_left h := (RTaint.meetK_eq _ _).symm ▸ RTaint.meet_left h
  meet_right h := (RTaint.meetK_eq _ _).symm ▸ RTaint.meet_right h
  le := RTaint.le
  le_sound := RTaint.le_sound
  call := RTaint.callK
  call_sound ha hs e₁ e₂ hadr := RTaint.call_sound ha ((RTaint.callK_eq _).symm.trans hs) e₁ e₂ hadr
  callAddrs_length _ _ := rfl
  ret := RTaint.ret
  ret_sound ha hs e₁ e₂ hadr := RTaint.ret_sound ha hs e₁ e₂ hadr
  retAddrs_length _ _ := rfl
  push := RTaint.pushK
  push_sound ha hs e₁ e₂ hadr := RTaint.push_sound ha ((RTaint.pushK_eq _ _).symm.trans hs) e₁ e₂ hadr
  pop := RTaint.popK
  pop_sound ha hs e₁ e₂ hadr := RTaint.pop_sound ha ((RTaint.popK_eq _ _).symm.trans hs) e₁ e₂ hadr

namespace RTaint

open VG.Arm.FrameStack

/-- Where the analysis starts holds of two states that `NoResidue` compares,
whose window of `W` bytes below the stack pointer is outside every region
and outside the `e.2` bytes from what each register `e.1` of `bp0` holds. -/
theorem agree_init {W : Nat} {bp0 : List (Reg × Nat)} {s₁ s₂ : State} (ho : Outside 0 s₁ s₂)
    (hu : s₁.unknowns = s₂.unknowns) (hW : W ≤ s₁.sp.toNat)
    (hreg : ∀ g ∈ s₁.rd ++ s₁.wr, ∀ x, g.Contains x 1 →
      ¬ (x - State.addr (s₁.sp - BitVec.ofNat 32 W)).toNat < W)
    (hbp : ∀ e ∈ bp0, ∀ i < e.2,
      ¬ (State.addr (s₁.gpr e.1 + BitVec.ofNat 32 i) - State.addr (s₁.sp - BitVec.ofNat 32 W)).toNat < W) :
    Agree (init W bp0) s₁ s₂ := by
  intro _
  obtain ⟨hrd, hwr, hg, h01, hsp, hn, hz, hc, hv, hmem⟩ := ho
  have hall : ∀ r, s₁.gpr r = s₂.gpr r := by
    have e := h01
    simp only [BitVec.ushiftRight_zero] at e
    intro r
    by_cases h0 : r = .r0
    · subst h0
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (BitVec.getLsbD · i) e
      simp only [BitVec.getLsbD_append, hi, ↓reduceIte] at this
      exact this
    · by_cases h1 : r = .r1
      · subst h1
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        have := congrArg (BitVec.getLsbD · (i + 32)) e
        simp only [BitVec.getLsbD_append, show ¬ i + 32 < 32 by omega, ↓reduceIte,
          show i + 32 - 32 = i by omega] at this
        exact this
      · exact hg r h0 h1
  refine ⟨hsp, hW, ?_, (fun r _ => hall r), (fun _ => ⟨hn, hz, hc, hv⟩),
    (fun e he => nomatch he), (fun e he => ⟨(hall e.1).symm, fun i hi => hbp e he i hi⟩), hrd, hwr, hu,
    [], s₁.wr, rfl, rfl, rfl, (fun g hg x hx => hreg g hg x hx), (fun x hx _ => hmem x hx)⟩
  show (s₁.sp - BitVec.ofNat 32 W).toNat + W < 2 ^ 32
  rw [sub_toNat' hW]
  have := s₁.sp.isLt
  omega_using [hW, this]

/-- The registers a callee may change but the result's. -/
theorem not_preserved (r : Reg) (h0 : r ≠ .r0) (h1 : r ≠ .r1) (hr : r ∉ preserved) :
    r = .r2 ∨ r = .r3 ∨ r = .r12 := by
  revert h0 h1 hr; cases r <;> decide

theorem shr_hi {a₁ a₂ b₁ b₂ : BitVec 32} {rb : Nat} (h : a₁ = a₂) (hrb : 32 ≤ rb) :
    (a₁ ++ b₁) >>> rb = (a₂ ++ b₂) >>> rb := by
  subst h
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, show ¬ rb + i < 32 by omega, ↓reduceIte]

theorem shr_64 (x y : BitVec 64) {rb : Nat} (hrb : 64 ≤ rb) : x >>> rb = y >>> rb := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight]
  rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]

/-- Two runs whose analysis ends in `done rb`, from states that agree outside
their buffers, and that preserve what the calling convention preserves,
agree outside the buffers but the `rb` low bits of the result. -/
theorem outside_of_done {τ : T} {rb : Nat} {s₁ s₂ s₁' s₂' : State} (h : Agree τ s₁' s₂')
    (hd : done rb τ = true) (ho : Outside 0 s₁ s₂) (hp₁ : abiPreserved s₁ s₁') (hp₂ : abiPreserved s₂ s₂') :
    Outside rb s₁' s₂' := by
  simp only [done, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Nat.ble_eq] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hok, hnf⟩, -⟩, hsec⟩, h2⟩, h3⟩, h12⟩, hfl⟩, h64⟩, h32⟩ := hd
  obtain ⟨hsp, -, -, hpub, hfl', -, -, hrd, hwr, -, F, B, hw, hl, -, -, hmem⟩ := h hok
  obtain rfl : F = [] := List.eq_nil_of_length_eq_zero (by rw [hl, hnf])
  rw [List.nil_append] at hw
  obtain ⟨fn, fz, fc, fv⟩ := hfl' hfl
  refine ⟨hrd, hwr, fun q h0 h1 => ?_, ?_, hsp, fn, fz, fc, fv, fun x hx => ?_⟩
  · by_cases hq : q ∈ preserved
    · rw [hp₁.1 q hq, hp₂.1 q hq]; exact ho.2.2.1 q h0 h1
    · rcases not_preserved q h0 h1 hq with rfl | rfl | rfl
      · exact hpub _ h2
      · exact hpub _ h3
      · exact hpub _ h12
  · rcases h64 with h64 | h1
    · exact shr_64 _ _ h64
    · rcases h32 with h32 | h0
      · exact shr_hi (hpub _ h1) h32
      · rw [hpub _ h1, hpub _ h0]
  · refine hmem x (fun g hg hc => hx g (by rw [hw] at *; exact hg) hc) fun _ => ?_
    rw [hsec]; exact Nat.zero_testBit _

/-- Code verified against its contract, whose analysis from where it starts
(`init W bp0`, for states its precondition makes as `agree_init` needs) ends
in `done rb`, returns without secret residue with an `rb`-bit result. -/
theorem noResidue_of_verified {c : Prog isa} {k : Contract isa} {rb W : Nat} {bp0 : List (Reg × Nat)}
    (hv : Verified target c k)
    (hpre : ∀ s, k.pre s → W ≤ s.sp.toNat ∧
      (∀ g ∈ s.rd ++ s.wr, ∀ x, g.Contains x 1 → ¬ (x - State.addr (s.sp - BitVec.ofNat 32 W)).toNat < W) ∧
      ∀ e ∈ bp0, ∀ i < e.2,
        ¬ (State.addr (s.gpr e.1 + BitVec.ofNat 32 i) - State.addr (s.sp - BitVec.ofNat 32 W)).toNat < W)
    (h : ∃ hc, (rtaint.check (init W bp0) c hc).any (done rb) = true) : NoResidue c k rb := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho hu e₁ e₂
  obtain ⟨hc, h⟩ := h
  cases hτ : rtaint.check (init W bp0) c hc with
  | none => rw [hτ] at h; cases h
  | some τ' =>
    rw [hτ] at h
    obtain ⟨_, u₁, f₁, hp₁, -⟩ := hv.1 s₁ h₁
    obtain ⟨_, u₂, f₂, hp₂, -⟩ := hv.1 s₂ h₂
    obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
    obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
    obtain ⟨hW, hreg, hbp⟩ := hpre s₁ h₁
    exact outside_of_done (TaintCT.agree_of_check hv.2.1 hτ h₁ h₂ hp (agree_init ho hu hW hreg hbp) e₁ e₂)
      (by exact h) ho hp₁ hp₂

end VG.Arm.RTaint
