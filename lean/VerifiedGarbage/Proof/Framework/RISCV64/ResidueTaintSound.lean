module

public import VerifiedGarbage.Proof.Framework.RISCV64.ResidueTaint
public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The residue analysis is sound (64-bit RISC-V)

`Agree τ s₁ s₂` is what `τ` (`ResidueTaint.lean`) says of two states, from
the window's base, the stack pointer less the offset `τ.sp` (`wb`): the
stack pointers and the public registers agree, the registers of `wp` and `bp`
hold what they say, the frames still allocated tile the window from `τ.sp` to
its top (`Frames`), the other writable regions and the readable ones are
outside the window, and the memory outside them agrees but at the bytes of
the window that `τ.sec` lists. Each transfer function keeps it (`step_sound`,
…), which makes `rtaint` a `TaintCT`.
-/

@[expose] public section

namespace VG.RISCV64.RTaint

open VG.RISCV64

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
def wb (τ : T) (s : State) : Addr := s.sp - BitVec.ofNat 64 τ.sp

/-- The offset of `x` from the window's base. -/
def off (τ : T) (s : State) (x : Addr) : Nat := (x - wb τ s).toNat

/-- `x` is in the window. -/
def InWin (τ : T) (s : State) (x : Addr) : Prop := off τ s x < τ.W

/-- The frames `F`, innermost first, tile the window of `W` bytes at `w`
from offset `o` to its top. -/
def Frames (w : Addr) (W : Nat) : Nat → List Region → Prop
  | o, [] => o = W
  | o, f :: fs => f.base = w + BitVec.ofNat 64 o ∧ 0 < f.len ∧ Frames w W (o + f.len) fs

/-- What `τ` says of the two states (see the module's documentation). -/
structure AgreeOk (τ : T) (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  spNat : τ.sp ≤ s₁.sp.toNat
  wbW : (wb τ s₁).toNat + τ.W < 2 ^ 64
  pub : ∀ r ∈ τ.pub, s₁.gpr r = s₂.gpr r
  lo : s₁.gpr .a0 >>> τ.lo = s₂.gpr .a0 >>> τ.lo
  wp : ∀ e ∈ τ.wp, s₁.gpr e.1 = wb τ s₁ + BitVec.ofNat 64 e.2 ∧ s₂.gpr e.1 = s₁.gpr e.1
  bp : ∀ e ∈ τ.bp, s₂.gpr e.1 = s₁.gpr e.1 ∧ ∀ i < e.2, ¬ InWin τ s₁ (s₁.gpr e.1 + BitVec.ofNat 64 i)
  rd : s₁.rd = s₂.rd
  wr : s₁.wr = s₂.wr
  unk : s₁.unknowns = s₂.unknowns
  regions : ∃ F B, s₁.wr = F ++ B ∧ F.length = τ.nf ∧ Frames (wb τ s₁) τ.W τ.sp F ∧
    (∀ g ∈ s₁.rd ++ B, ∀ x, g.Contains x 1 → ¬ InWin τ s₁ x) ∧
    ∀ x, (∀ g ∈ s₁.rd ++ B, ¬ g.Contains x 1) → (InWin τ s₁ x → τ.sec.testBit (off τ s₁ x) = false) →
      s₁.mem x = s₂.mem x

def Agree (τ : T) (s₁ s₂ : State) : Prop := τ.ok = true → AgreeOk τ s₁ s₂

/-! ## Writing a register -/

theorem wb_write (τ : T) (s : State) (d : Reg) (v : BitVec 64) : wb τ (s.write d v) = wb τ s := rfl

theorem inWin_write (τ : T) (s : State) (d : Reg) (v : BitVec 64) (x : Addr) :
    InWin τ (s.write d v) x ↔ InWin τ s x := Iff.rfl

theorem off_write (τ : T) (s : State) (d : Reg) (v : BitVec 64) (x : Addr) :
    off τ (s.write d v) x = off τ s x := rfl

theorem shr64 (x : BitVec 64) : x >>> 64 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight]
  exact Nat.shiftRight_eq_zero _ _ (by have := x.isLt; omega)

/-- `setR` describes a write of `d`: of the same value in both runs if `p`,
of byte `k` of the window if `k`, and of an address followed by `b` bytes
outside it if `b`. -/
theorem AgreeOk.setR {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) (d : Reg) {p : Bool}
    {k b : Option Nat} {v₁ v₂ : BitVec 64} (hp : p = true → v₁ = v₂)
    (hk : ∀ k', k = some k' → v₁ = wb τ s₁ + BitVec.ofNat 64 k' ∧ v₂ = v₁)
    (hb : ∀ b', b = some b' → v₂ = v₁ ∧ ∀ i < b', ¬ InWin τ s₁ (v₁ + BitVec.ofNat 64 i)) :
    AgreeOk (RTaint.setR τ d p k b) (s₁.write d v₁) (s₂.write d v₂) := by
  obtain ⟨hsp, hspN, hwbW, hpub, hlo, hwp, hbp, hrd, hwr, hunk, hreg⟩ := h
  refine ⟨hsp, hspN, hwbW, fun r hr => ?_, ?_, fun e he => ?_, fun e he => ?_, hrd, hwr, hunk, hreg⟩
  · simp only [RTaint.setR] at hr
    simp only [RegUpd.gpr_write]
    split at hr
    · rename_i hp'
      rcases RegSet.mem_insert.mp hr with rfl | hr
      · simp [hp hp']
      · by_cases hrd : r = d
        · simp [hrd, hp hp']
        · simp [hrd, hpub r hr]
    · obtain ⟨hne, hr⟩ := RegSet.mem_erase.mp hr
      simp [hne, hpub r hr]
  · simp only [RTaint.setR]
    by_cases hd : d = .a0
    · subst hd
      simp only [beq_self_eq_true, ite_true, RegUpd.gpr_write_self]
      cases p
      · simp only [Bool.false_eq_true, ite_false, shr64]
      · simp only [ite_true, hp rfl]
    · have : (d == Reg.a0) = false := by simp [hd]
      simp only [this, Bool.false_eq_true, ite_false]
      rw [RegUpd.gpr_write_of_ne _ _ (Ne.symm hd), RegUpd.gpr_write_of_ne _ _ (Ne.symm hd)]
      exact hlo
  · simp only [RTaint.setR, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at he
    rw [wb_write]
    rcases he with he | ⟨he, hne⟩
    · cases k with
      | none => simp at he
      | some k' =>
        simp only [List.mem_singleton] at he
        subst he
        obtain ⟨e1, e2⟩ := hk k' rfl
        simp only [RegUpd.gpr_write_self]
        exact ⟨e1, e2⟩
    · rw [RegUpd.gpr_write_of_ne _ _ hne, RegUpd.gpr_write_of_ne _ _ hne]
      exact hwp e he
  · simp only [RTaint.setR, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at he
    rcases he with he | ⟨he, hne⟩
    · cases b with
      | none => simp at he
      | some b' =>
        simp only [List.mem_singleton] at he
        subst he
        obtain ⟨e1, e2⟩ := hb b' rfl
        simp only [RegUpd.gpr_write_self]
        exact ⟨e1, e2⟩
    · rw [RegUpd.gpr_write_of_ne _ _ hne, RegUpd.gpr_write_of_ne _ _ hne]
      obtain ⟨e1, e2⟩ := hbp e he
      exact ⟨e1, e2⟩

/-- A register written with the same value in both runs. -/
theorem AgreeOk.setPub {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) (d : Reg) {v : BitVec 64} :
    AgreeOk (RTaint.setR τ d true none none) (s₁.write d v) (s₂.write d v) :=
  h.setR d (fun _ => rfl) (fun _ h => nomatch h) (fun _ h => nomatch h)

/-- A register written with values the analysis knows nothing of. -/
theorem AgreeOk.setSec {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) (d : Reg) {v₁ v₂ : BitVec 64} :
    AgreeOk (RTaint.setR τ d false none none) (s₁.write d v₁) (s₂.write d v₂) :=
  h.setR d (fun h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)

theorem AgreeOk.reg {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {r : Reg} (hr : pubR τ r = true) :
    s₁.gpr r = s₂.gpr r := h.pub r hr

theorem AgreeOk.withPub {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {n : Reg}
    (hn : s₁.gpr n = s₂.gpr n) : AgreeOk (RTaint.withPub τ n) s₁ s₂ := by
  obtain ⟨hsp, hspN, hwbW, hpub, hlo, hwp, hbp, hrd, hwr, hunk, hreg⟩ := h
  unfold RTaint.withPub
  split
  · rename_i hna
    have hna : n = .a0 := by simpa using hna
    subst hna
    refine ⟨hsp, hspN, hwbW, fun r hr => ?_, by simp only [BitVec.ushiftRight_zero]; exact hn,
      hwp, hbp, hrd, hwr, hunk, hreg⟩
    rcases RegSet.mem_insert.mp hr with rfl | hr
    · exact hn
    · exact hpub r hr
  · refine ⟨hsp, hspN, hwbW, fun r hr => ?_, hlo, hwp, hbp, hrd, hwr, hunk, hreg⟩
    rcases RegSet.mem_insert.mp hr with rfl | hr
    · exact hn
    · exact hpub r hr

/-! ## Addresses in the window -/

theorem toNat_ofNat_lt {j : Nat} (h : j < 2 ^ 64) : (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Byte `j` of the window is at offset `j`. -/
theorem off_base (τ : T) (s : State) {j : Nat} (hj : j < 2 ^ 64) :
    off τ s (wb τ s + BitVec.ofNat 64 j) = j := by
  have e : wb τ s + BitVec.ofNat 64 j - wb τ s = BitVec.ofNat 64 j := by bv_omega
  simp only [off, e, toNat_ofNat_lt hj]

/-- `x` is among the `n` bytes from byte `o` of the window. -/
theorem in_range (τ : T) (s : State) (x : Addr) {o n : Nat} (h : o + n < 2 ^ 64) :
    (x - (wb τ s + BitVec.ofNat 64 o)).toNat < n ↔ o ≤ off τ s x ∧ off τ s x < o + n :=
  Scrub.off_lt x (wb τ s) o n h

theorem Frames.le {w : Addr} {W : Nat} : ∀ {o : Nat} {F : List Region}, Frames w W o F → o ≤ W
  | _, [], h => by simp only [Frames] at h; omega_using [h]
  | _, _ :: _, ⟨_, _, hf⟩ => by have := Frames.le hf; omega_using [this]

/-- A frame's bytes are in the window, from the offset of the frames on. -/
theorem Frames.contains {w : Addr} {W : Nat} (hw : w.toNat + W < 2 ^ 64) :
    ∀ {o : Nat} {F : List Region}, Frames w W o F → ∀ g ∈ F, ∀ x, g.Contains x 1 →
      o ≤ (x - w).toNat ∧ (x - w).toNat < W
  | _, [], _, _, hg, _, _ => nomatch hg
  | o, f :: fs, ⟨hb, hl, hf⟩, g, hg, x, hx => by
    have hle := Frames.le hf
    rcases List.mem_cons.mp hg with rfl | hg
    · simp only [Region.Contains] at hx
      rw [hb] at hx
      have := (Scrub.off_lt x w o g.len (by omega_using [hw, hle])).mp (by omega_using [hx])
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

theorem offAdd_eq {k j : Nat} {imm : Int} (h : offAdd k imm = some j) (w : Addr) :
    w + BitVec.ofNat 64 k + BitVec.ofInt 64 imm = w + BitVec.ofNat 64 j := by
  simp only [offAdd] at h
  split at h <;> [skip; cases h]
  rename_i hle; cases h
  rw [BitVec.add_assoc, ← BitVec.ofInt_natCast, ← BitVec.ofInt_add, ← BitVec.ofInt_natCast,
    Int.toNat_of_nonneg hle]

theorem roomAdd_eq {b b' : Nat} {imm : Int} (h : roomAdd b imm = some b') (g : Addr) (i : Nat) :
    g + BitVec.ofInt 64 imm + BitVec.ofNat 64 i = g + BitVec.ofNat 64 (imm.toNat + i) ∧
      (i < b' → imm.toNat + i < b) := by
  simp only [roomAdd] at h
  split at h <;> [skip; cases h]
  rename_i hle; cases h
  refine ⟨?_, fun hi => by omega_using [hi, hle.1, hle.2]⟩
  have e : BitVec.ofInt 64 imm = BitVec.ofNat 64 imm.toNat := by
    rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg hle.1]
  rw [BitVec.add_assoc, BitVec.ofNat_add, e]

/-! ## Loads and stores -/

theorem exec_load_inv {wd : Width} {t n : Reg} {off : Nat} {s s' : State}
    (h : exec (.load wd t n off) s = some s') :
    s' = s.write t ((s.mem.read (s.gpr n + BitVec.ofNat 64 off) wd.bytes).setWidth 64) := by
  simp only [exec, addr, Option.bind_eq_some_iff, State.load, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, v, hv, rfl⟩ := h
  split at ha <;> [skip; cases ha]
  cases ha
  split at hv <;> [skip; cases hv]
  cases hv; rfl

theorem exec_store_inv {wd : Width} {t n : Reg} {off : Nat} {s s' : State}
    (h : exec (.store wd t n off) s = some s') :
    InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) wd.bytes ∧
      s' = { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) wd.bytes ((s.gpr t).setWidth (8 * wd.bytes)) } := by
  simp only [exec, addr, Option.bind_eq_some_iff, State.store] at h
  obtain ⟨a, ha, hs⟩ := h
  split at ha <;> [skip; cases ha]
  cases ha
  split at hs <;> [skip; cases hs]
  rename_i hin; cases hs
  exact ⟨hin, rfl⟩

theorem width_pos (wd : Width) : 0 < wd.bytes := by cases wd <;> decide

theorem width_le (wd : Width) : wd.bytes ≤ 8 := by cases wd <;> decide

/-- The memory of a state with only its memory changed. -/
theorem AgreeOk.withMem {τ τ' : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {m₁ m₂ : Mem}
    (he : τ'.sp = τ.sp ∧ τ'.W = τ.W ∧ τ'.pub = τ.pub ∧ τ'.lo = τ.lo ∧ τ'.nf = τ.nf ∧
      τ'.wp = τ.wp ∧ τ'.bp = τ.bp)
    (hm : ∀ B, (∀ g ∈ s₁.rd ++ B, ∀ x, g.Contains x 1 → ¬ InWin τ s₁ x) →
      (∃ F, s₁.wr = F ++ B ∧ F.length = τ.nf ∧ Frames (wb τ s₁) τ.W τ.sp F) →
      (∀ x, (∀ g ∈ s₁.rd ++ B, ¬ g.Contains x 1) → (InWin τ s₁ x → τ.sec.testBit (off τ s₁ x) = false) →
        s₁.mem x = s₂.mem x) →
      ∀ x, (∀ g ∈ s₁.rd ++ B, ¬ g.Contains x 1) → (InWin τ s₁ x → τ'.sec.testBit (off τ s₁ x) = false) →
        m₁ x = m₂ x) :
    AgreeOk τ' { s₁ with mem := m₁ } { s₂ with mem := m₂ } := by
  obtain ⟨hsp, hspN, hwbW, hpub, hlo, hwp, hbp, hrd, hwr, hunk, F, B, hw, hl, hf, hout, hmem⟩ := h
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := he
  have ewb : wb τ' { s₁ with mem := m₁ } = wb τ s₁ := by simp only [wb, e1]
  have ein : ∀ x, InWin τ' { s₁ with mem := m₁ } x ↔ InWin τ s₁ x := by
    intro x; simp only [InWin, off, ewb, e2]
  refine ⟨hsp, by rw [e1]; exact hspN, by rw [ewb, e2]; exact hwbW, by rw [e3]; exact hpub,
    by rw [e4]; exact hlo, fun e he => ?_, fun e he => ?_, hrd, hwr, hunk,
    F, B, hw, by rw [e5]; exact hl, by rw [ewb, e2, e1]; exact hf,
    fun g hg x hx => (not_congr (ein x)).mpr (hout g hg x hx), fun x hx hs => ?_⟩
  · rw [e6] at he; rw [ewb]; exact hwp e he
  · rw [e7] at he
    obtain ⟨h1, h2⟩ := hbp e he
    exact ⟨h1, fun i hi => (not_congr (ein _)).mpr (h2 i hi)⟩
  · exact hm B hout ⟨F, hw, hl, hf⟩ hmem x hx (fun hw' => by
      have := hs ((ein x).mpr hw')
      simpa only [off, ewb] using this)

/-- A store of `n` bytes at `a` in both runs, of values that agree at each
byte `ok` allows, keeps what `τ` says of the memory, with `sec'` for the
window's secret bytes, if each byte written is one `ok` allows or one that
`sec'` makes secret or that is in a buffer, and `sec'` makes secret every byte
not written that `τ.sec` does. -/
theorem AgreeOk.store {τ τ' : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {a : Addr} {n : Nat}
    {v₁ v₂ : BitVec (8 * n)}
    (he : τ'.sp = τ.sp ∧ τ'.W = τ.W ∧ τ'.pub = τ.pub ∧ τ'.lo = τ.lo ∧ τ'.nf = τ.nf ∧
      τ'.wp = τ.wp ∧ τ'.bp = τ.bp)
    (hwr : ∀ B, (∀ g ∈ s₁.rd ++ B, ∀ x, g.Contains x 1 → ¬ InWin τ s₁ x) →
      (∃ F, s₁.wr = F ++ B ∧ F.length = τ.nf ∧ Frames (wb τ s₁) τ.W τ.sp F) →
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

/-- The address of a store through byte `k` of the window. -/
theorem wp_addr {τ : T} {s : State} {r : Reg} {k off : Nat} (h : s.gpr r = wb τ s + BitVec.ofNat 64 k) :
    s.gpr r + BitVec.ofNat 64 off = wb τ s + BitVec.ofNat 64 (k + off) := by
  rw [h, BitVec.ofNat_add, BitVec.add_assoc]

/-- A byte written through a register with `b` bytes outside the window
after it, within them, is not in the window. -/
theorem bp_byte {τ : T} {s : State} {g a x : Addr} {off n b : Nat}
    (hb : ∀ i < b, ¬ InWin τ s (g + BitVec.ofNat 64 i)) (ha : a = g + BitVec.ofNat 64 off)
    (hn : off + n ≤ b) (hx : (x - a).toNat < n) : ¬ InWin τ s x := by
  have e : x = g + BitVec.ofNat 64 (off + (x - a).toNat) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← ha, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  rw [e]; exact hb _ (by omega_using [hn, hx])

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

theorem store_sound {τ τ' : T} {wd : Width} {t n : Reg} {ofs : Nat} {s₁ s₂ s₁' s₂' : State}
    (ha : AgreeOk τ s₁ s₂) (hn : pubR τ n = true) (hs : stepB τ (.store wd t n ofs) = some τ')
    (e₁ : exec (.store wd t n ofs) s₁ = some s₁') (e₂ : exec (.store wd t n ofs) s₂ = some s₂') :
    AgreeOk τ' s₁' s₂' := by
  obtain ⟨hin₁, rfl⟩ := exec_store_inv e₁
  obtain ⟨-, rfl⟩ := exec_store_inv e₂
  rw [← ha.reg hn]
  have hW : (wb τ s₁).toNat + τ.W < 2 ^ 64 := ha.wbW
  -- What a public value or the frames' bytes made secret give.
  have pubCase : pubR τ t = true → ∀ τ'', τ''.sec = τ.sec → τ'' = τ → AgreeOk τ''
      { s₁ with mem := s₁.mem.write (s₁.gpr n + BitVec.ofNat 64 ofs) wd.bytes ((s₁.gpr t).setWidth (8 * wd.bytes)) }
      { s₂ with mem := s₂.mem.write (s₁.gpr n + BitVec.ofNat 64 ofs) wd.bytes ((s₂.gpr t).setWidth (8 * wd.bytes)) } := by
    intro ht τ'' _ e; subst e
    refine ha.store ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ _ _ x _ _ _ => by rw [ha.reg ht])
      (fun _ _ _ h => h)
  have frameCase : ∀ τ'', τ'' = { τ with sec := bset τ.sec τ.sp (τ.W - τ.sp) } → AgreeOk τ''
      { s₁ with mem := s₁.mem.write (s₁.gpr n + BitVec.ofNat 64 ofs) wd.bytes ((s₁.gpr t).setWidth (8 * wd.bytes)) }
      { s₂ with mem := s₂.mem.write (s₁.gpr n + BitVec.ofNat 64 ofs) wd.bytes ((s₂.gpr t).setWidth (8 * wd.bytes)) } := by
    intro τ'' e; subst e
    refine ha.store ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun B hout hF x hx hxo hsx => ?_) (fun x _ _ h => ?_)
    · obtain ⟨F, hw, -, hf⟩ := hF
      exfalso
      rcases store_region (B := B) hw hin₁ hx with ⟨g, hg, hc⟩ | ⟨g, hg, hc⟩
      · obtain ⟨h1, h2⟩ := Frames.contains hW hf g hg x hc
        have hle := Frames.le hf
        have := hsx h2
        simp only [testBit_bset, RTaint.off] at this
        simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
        omega_using [this.2, h1, h2, hle]
      · exact hxo g hg hc
    · simp only [testBit_bset, Bool.or_eq_false_iff] at h; exact h.1
  simp only [stepB] at hs
  split at hs
  · rename_i k hk
    obtain ⟨hk1, -⟩ := ha.wp _ (wpOf_mem hk)
    have haddr := wp_addr (off := ofs) hk1
    split at hs
    · rename_i hin
      cases hs
      by_cases ht : pubR τ t = true
      · simp only [ht, ite_true]
        refine ha.store ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ _ _ x _ _ _ => by rw [ha.reg ht])
          (fun x hx hw h => ?_)
        rw [haddr, in_range τ s₁ x (by omega_using [hin, hW, width_le wd])] at hx
        simp only [testBit_bclr, Bool.and_eq_false_iff, Bool.not_eq_false', Bool.and_eq_true,
          decide_eq_true_eq] at h
        rcases h with h | h
        · exact h
        · exact absurd h hx
      · simp only [ht, Bool.false_eq_true, ite_false]
        refine ha.store ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun B hout hF x hx hxo hsx => ?_)
          (fun x _ _ h => by simp only [testBit_bset, Bool.or_eq_false_iff] at h; exact h.1)
        exfalso
        rw [haddr, in_range τ s₁ x (by omega_using [hin, hW, width_le wd])] at hx
        have := hsx (by unfold InWin; omega_using [hx, hin])
        simp only [testBit_bset, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
        omega_using [this.2, hx]
    · split at hs
      · cases hs; rename_i ht; exact pubCase ht _ rfl rfl
      · cases hs; exact frameCase _ rfl
  · rename_i hk
    split at hs
    · rename_i b hb
      obtain ⟨-, hb2⟩ := ha.bp _ (bpOf_mem hb)
      split at hs
      · rename_i hroom
        cases hs
        refine ha.store ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun B hout hF x hx hxo _ => ?_)
          (fun _ _ _ h => h)
        exfalso
        obtain ⟨F, hw, -, hf⟩ := hF
        have hnw := bp_byte (off := ofs) hb2 rfl hroom hx
        rcases store_region (B := B) hw hin₁ hx with ⟨g, hg, hc⟩ | ⟨g, hg, hc⟩
        · exact hnw (Frames.contains hW hf g hg x hc).2
        · exact hxo g hg hc
      · split at hs
        · cases hs; rename_i ht; exact pubCase ht _ rfl rfl
        · cases hs; exact frameCase _ rfl
    · split at hs
      · cases hs; rename_i ht; exact pubCase ht _ rfl rfl
      · cases hs; exact frameCase _ rfl

/-- What a shift left of `a0` by `k` leaves comparable of it. -/
theorem shl_lo {x y : BitVec 64} {lo k : Nat} (h : x >>> lo = y >>> lo) :
    (x <<< k) >>> min 64 (lo + k) = (y <<< k) >>> min 64 (lo + k) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  have hb := congrArg (BitVec.getLsbD · (i + min 64 (lo + k) - k - lo)) h
  simp only [BitVec.getLsbD_ushiftRight] at hb
  by_cases h64 : min 64 (lo + k) + i < 64
  · have e : lo + (i + min 64 (lo + k) - k - lo) = min 64 (lo + k) + i - k := by omega
    rw [e] at hb
    simp only [h64, decide_true, Bool.true_and]
    by_cases hk : min 64 (lo + k) + i < k
    · simp only [hk, decide_true, Bool.not_true, Bool.false_and]
    · simp only [hk, decide_false, Bool.not_false, Bool.true_and]; exact hb
  · simp only [h64, decide_false, Bool.false_and]

/-- What a shift right of `a0` by `k` leaves comparable of it. -/
theorem ushr_ushr (x : BitVec 64) (a b : Nat) : x >>> a >>> b = x >>> (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_add]

theorem shr_lo {x y : BitVec 64} {lo k : Nat} (h : x >>> lo = y >>> lo) :
    (x >>> k) >>> (lo - k) = (y >>> k) >>> (lo - k) := by
  rw [ushr_ushr, ushr_ushr]
  by_cases hk : k ≤ lo
  · rw [show k + (lo - k) = lo by omega]; exact h
  · rw [show k + (lo - k) = lo + (k - lo) by omega, ← ushr_ushr, h, ushr_ushr]

theorem load_sound {τ τ' : T} {wd : Width} {t n : Reg} {ofs : Nat} {s₁ s₂ s₁' s₂' : State}
    (ha : AgreeOk τ s₁ s₂) (hn : pubR τ n = true) (hs : stepB τ (.load wd t n ofs) = some τ')
    (e₁ : exec (.load wd t n ofs) s₁ = some s₁') (e₂ : exec (.load wd t n ofs) s₂ = some s₂') :
    AgreeOk τ' s₁' s₂' := by
  rw [exec_load_inv e₁, exec_load_inv e₂, ← ha.reg hn]
  simp only [stepB, Option.some.injEq] at hs
  subst hs
  refine ha.setR t (fun hp => ?_) (fun _ h => nomatch h) (fun _ h => nomatch h)
  split at hp
  · rename_i k hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨hin, hno⟩ := hp
    obtain ⟨hk1, -⟩ := ha.wp _ (wpOf_mem hk)
    obtain ⟨F, B, -, -, -, hout, hmem⟩ := ha.regions
    have hW := ha.wbW
    congr 1
    refine Mem.read_congr fun j hj => ?_
    simp only at hk1
    rw [wp_addr (off := ofs) hk1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have hx : off τ s₁ (wb τ s₁ + BitVec.ofNat 64 (k + ofs + j)) = k + ofs + j :=
      off_base τ s₁ (by omega_using [hin, hj, hW])
    refine hmem _ (fun g hg hc => hout g hg _ hc ?_) (fun _ => ?_)
    · unfold InWin; rw [hx]; omega_using [hin, hj]
    · rw [hx]; exact bnone_bit hno (by omega_using []) (by omega_using [hj])
  · cases hp

theorem sext_eq {a b : BitVec 32} (h : a = b) : sext32 a = sext32 b := by rw [h]

theorem stepB_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : AgreeOk τ s₁ s₂)
    (hb : ∀ n, base i = some n → pubR τ n = true) (hs : stepB τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') : AgreeOk τ' s₁' s₂' := by
  cases i with
  | push | pop | alloc | free | jalr => simp only [stepB, reduceCtorEq] at hs
  | load wd t n ofs => exact load_sound ha (hb n rfl) hs e₁ e₂
  | store wd t n ofs => exact store_sound ha (hb n rfl) hs e₁ e₂
  | lla d name =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ha.setSec d
  | lui d imm =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ha.setPub d
  | li d imm =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
    cases e₁; cases e₂
    exact ha.setPub d
  | addSp d imm =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
    cases e₁; cases e₂
    refine ha.setR d (fun _ => by rw [ha.sp]) (fun k' hk => ?_) (fun _ h => nomatch h)
    cases hk
    refine ⟨?_, by rw [ha.sp]⟩
    simp only [wb, BitVec.ofNat_add]
    bv_omega
  | add d n m | sub d n m | addw d n m | subw d n m | sltu d n m | mul d n m | mulhu d n m
  | logic op d n m =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    refine ha.setR d (fun hp => ?_) (fun _ h => nomatch h) (fun _ h => nomatch h)
    simp only [Bool.and_eq_true] at hp
    rw [ha.reg hp.1, ha.reg hp.2]
  | shiftReg op sz d n m =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    cases sz <;>
    · simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
      refine ha.setR d (fun hp => ?_) (fun _ h => nomatch h) (fun _ h => nomatch h)
      simp only [Bool.and_eq_true] at hp
      rw [ha.reg hp.1, ha.reg hp.2]
  | addiw d n imm | logicImm op d n imm =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
    cases e₁; cases e₂
    exact ha.setR d (fun hp => by rw [ha.reg hp]) (fun _ h => nomatch h) (fun _ h => nomatch h)
  | addi d n imm =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
    cases e₁; cases e₂
    refine ha.setR d (fun hp => by rw [ha.reg hp]) (fun k' hk => ?_) (fun b' hb' => ?_)
    · simp only [Option.bind_eq_some_iff] at hk
      obtain ⟨k, hk, ho⟩ := hk
      obtain ⟨h1, h2⟩ := ha.wp _ (wpOf_mem hk)
      simp only at h1 h2
      rw [h2, h1]
      exact ⟨offAdd_eq ho _, rfl⟩
    · simp only [Option.bind_eq_some_iff] at hb'
      obtain ⟨b, hb, ho⟩ := hb'
      obtain ⟨h1, h2⟩ := ha.bp _ (bpOf_mem hb)
      simp only at h1 h2
      refine ⟨by rw [h1], fun i hi => ?_⟩
      obtain ⟨e, hlt⟩ := roomAdd_eq ho (s₁.gpr n) i
      rw [e]; exact h2 _ (hlt hi)
  | shift op sz d n sh =>
    simp only [stepB] at hs
    have base : ∀ {v₁ v₂ : BitVec 64}, (pubR τ n = true → v₁ = v₂) →
        AgreeOk (RTaint.setR τ d (pubR τ n) none none) (s₁.write d v₁) (s₂.write d v₂) :=
      fun hv => ha.setR d hv (fun _ h => nomatch h) (fun _ h => nomatch h)
    split at hs
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hpa⟩ := hc
      simp only [exec] at e₁ e₂
      split at e₁ <;> [skip; cases e₁]
      rename_i h
      rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
      cases e₁; cases e₂
      have hlo := ha.lo
      have hnp : pubR τ Reg.a0 = true → False := fun hp => by rw [hpa] at hp; cases hp
      cases op
      · cases hs
        have hb := base (v₁ := s₁.gpr .a0 <<< sh) (v₂ := s₂.gpr .a0 <<< sh) (fun hp => (hnp hp).elim)
        refine ⟨hb.sp, hb.spNat, hb.wbW, hb.pub, ?_, hb.wp, hb.bp, hb.rd, hb.wr, hb.unk, hb.regions⟩
        simp only [RegUpd.gpr_write_self]
        exact shl_lo hlo
      · cases hs
        have hb := base (v₁ := s₁.gpr .a0 >>> sh) (v₂ := s₂.gpr .a0 >>> sh) (fun hp => (hnp hp).elim)
        refine ⟨hb.sp, hb.spNat, hb.wbW, hb.pub, ?_, hb.wp, hb.bp, hb.rd, hb.wr, hb.unk, hb.regions⟩
        simp only [RegUpd.gpr_write_self]
        exact shr_lo hlo
      · cases hs
        exact base (fun hp => (hnp hp).elim)
    · cases hs
      cases sz <;>
      · simp only [exec] at e₁ e₂
        split at e₁ <;> [skip; cases e₁]
        rename_i h
        rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
        cases e₁; cases e₂
        exact base fun hp => by rw [ha.reg hp]

/-! ## Knowing less -/

theorem shr_mono {x y : BitVec 64} {a b : Nat} (h : x >>> a = y >>> a) (hab : a ≤ b) :
    x >>> b = y >>> b := by
  rw [show b = a + (b - a) by omega, ← ushr_ushr, ← ushr_ushr, h]

/-- What `σ` says, `τ` says if it knows no more. -/
theorem AgreeOk.weaken {τ σ : T} {s₁ s₂ : State} (h : AgreeOk σ s₁ s₂) (hsp : τ.sp = σ.sp)
    (hW : τ.W = σ.W) (hnf : τ.nf = σ.nf) (hpub : ∀ r ∈ τ.pub, r ∈ σ.pub) (hlo : σ.lo ≤ τ.lo)
    (hwp : ∀ e ∈ τ.wp, e ∈ σ.wp) (hbp : ∀ e ∈ τ.bp, ∃ b, (e.1, b) ∈ σ.bp ∧ e.2 ≤ b)
    (hsec : ∀ k, σ.sec.testBit k = true → τ.sec.testBit k = true) : AgreeOk τ s₁ s₂ := by
  obtain ⟨hsp', hspN, hwbW, hpub', hlo', hwp', hbp', hrd, hwr, hunk, F, B, hw, hl, hf, hout, hmem⟩ := h
  have ewb : wb τ s₁ = wb σ s₁ := by simp only [wb, hsp]
  have ein : ∀ x, InWin τ s₁ x ↔ InWin σ s₁ x := by intro x; simp only [InWin, off, ewb, hW]
  refine ⟨hsp', by rw [hsp]; exact hspN, by rw [ewb, hW]; exact hwbW, fun r hr => hpub' r (hpub r hr),
    shr_mono hlo' hlo, fun e he => by rw [ewb]; exact hwp' e (hwp e he), fun e he => ?_, hrd, hwr, hunk,
    F, B, hw, by rw [hnf]; exact hl, by rw [ewb, hW, hsp]; exact hf,
    fun g hg x hx => (not_congr (ein x)).mpr (hout g hg x hx), fun x hx hs => ?_⟩
  · obtain ⟨b, hb, hle⟩ := hbp e he
    obtain ⟨h1, h2⟩ := hbp' _ hb
    exact ⟨h1, fun i hi => (not_congr (ein _)).mpr (h2 i (by omega_using [hi, hle]))⟩
  · refine hmem x hx fun hw' => ?_
    have h1 := hs ((ein x).mpr hw')
    have e : off τ s₁ x = off σ s₁ x := by simp only [off, ewb]
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
    refine (h h1).weaken rfl rfl rfl (fun r hr => (RegSet.mem_inter.mp hr).1) (Nat.le_max_left _ _)
      (fun e he => (List.mem_filter.mp he).1) (fun e he => ?_) (fun k hk => ?_)
    · obtain ⟨e', he', hm⟩ := List.mem_filterMap.mp he
      split at hm
      · rename_i hb
        obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp hm
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
    refine (h h2).weaken hsp hW hnf (fun r hr => (RegSet.mem_inter.mp hr).2) (Nat.le_max_right _ _)
      (fun e he => ?_) (fun e he => ?_) (fun k hk => ?_)
    · obtain ⟨-, hm⟩ := List.mem_filter.mp he
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      have := wpOf_mem hm.1
      exact this
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
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hσ, hW⟩, hsp⟩, hnf⟩, hpub⟩, hlo⟩, hwp⟩, hbp⟩, hsec⟩ := hle
  refine (h hσ).weaken hsp hW hnf (fun r hr => RegSet.mem_of_subset hpub hr) (Nat.le_of_ble_eq_true hlo)
    (fun e he => ?_) (fun e he => ?_) (fun k hk => bsub_bit hsec hk)
  · exact wpOf_mem (hwp e he)
  · have := hbp e he
    split at this
    · rename_i b hb
      exact ⟨b, bpOf_mem hb, Nat.le_of_ble_eq_true this⟩
    · cases this

theorem toNat_sub_ofNat' (p : Addr) {b : Nat} (h : b ≤ p.toNat) :
    (p - BitVec.ofNat 64 b).toNat = p.toNat - b := Scrub.toNat_sub_ofNat p b h

theorem toNat_add_of_lt' (p : Addr) {b : Nat} (h : p.toNat + b < 2 ^ 64) :
    (p + BitVec.ofNat 64 b).toNat = p.toNat + b := Scrub.toNat_add_of_lt p b h

/-! ## Steps, frames and calls -/

theorem pubR_withPub (τ : T) (n : Reg) : pubR (RTaint.withPub τ n) n = true := by
  unfold RTaint.withPub pubR
  split <;> exact RegSet.mem_insert.mpr (.inl rfl)

theorem base_eq {i : Instr} {n : Reg} (h : base i = some n) (s₁ s₂ : State)
    (ha : addrs i s₁ = addrs i s₂) : s₁.gpr n = s₂.gpr n := by
  cases i <;> simp only [base, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
  · simp only [addrs, List.cons.injEq, and_true] at ha
    bv_omega

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
  cases i <;> rfl

theorem push_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : push τ i = some τ') (e₁ : isa.push i s₁ = some s₁') (e₂ : isa.push i s₂ = some s₂')
    (_hadr : isa.addrs i s₁ = isa.addrs i s₂) : Agree τ' s₁' s₂' := by
  intro _
  obtain ⟨b, rfl⟩ : ∃ b, i = .alloc b := by
    cases i <;> simp only [push, reduceCtorEq] at hs
    exact ⟨_, rfl⟩
  simp only [push] at hs
  split at hs <;> [skip; cases hs]
  rename_i hc
  cases hs
  simp only [Bool.and_eq_true, Nat.ble_eq] at hc
  obtain ⟨hok, hb⟩ := hc
  obtain ⟨hsp, hspN, hwbW, hpub, hlo, hwp, hbp, hrd, hwr, hunk, F, B, hw, hl, hf, hout, hmem⟩ := ha hok
  simp only [isa, RISCV64.push] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  rename_i hc₁
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  have ewb : wb { τ with sp := τ.sp - b, nf := τ.nf + 1 }
      { s₁ with sp := s₁.sp - BitVec.ofNat 64 b, wr := ⟨s₁.sp - BitVec.ofNat 64 b, b⟩ :: s₁.wr } =
      wb τ s₁ := by
    simp only [wb]
    rw [show BitVec.ofNat 64 (τ.sp - b) = BitVec.ofNat 64 τ.sp - BitVec.ofNat 64 b by
      rw [← BitVec.ofNat_sub_ofNat_of_le _ _ (Nat.lt_of_le_of_lt (Nat.le_trans hb hspN) s₁.sp.isLt) hb] ]
    bv_omega
  refine ⟨by rw [hsp], ?_, by rw [ewb]; exact hwbW, hpub, hlo, fun e he => ?_, fun e he => ?_, hrd,
    by rw [hwr, hsp], hunk, ⟨s₁.sp - BitVec.ofNat 64 b, b⟩ :: F, B, by rw [hw]; rfl,
    by simp only [List.length_cons, hl], ?_, ?_, ?_⟩
  · show τ.sp - b ≤ (s₁.sp - BitVec.ofNat 64 b).toNat
    rw [toNat_sub_ofNat' s₁.sp (by omega_using [hc₁.2.2.2, hb])]
    omega_using [hspN]
  · rw [ewb]; exact hwp e he
  · obtain ⟨h1, h2⟩ := hbp e he
    exact ⟨h1, fun i hi => by unfold InWin off; rw [ewb]; exact h2 i hi⟩
  · rw [ewb]
    refine ⟨?_, hc₁.1, ?_⟩
    · show s₁.sp - BitVec.ofNat 64 b = wb τ s₁ + BitVec.ofNat 64 (τ.sp - b)
      simp only [wb]
      rw [← BitVec.ofNat_sub_ofNat_of_le _ _ (Nat.lt_of_le_of_lt (Nat.le_trans hb hspN) s₁.sp.isLt) hb]
      bv_omega
    · rw [show τ.sp - b + b = τ.sp by omega_using [hb]]; exact hf
  · intro g hg x hx
    unfold InWin off; rw [ewb]; exact hout g hg x hx
  · intro x hx hs
    exact hmem x hx fun hw' => by
      have := hs (by unfold InWin off; rw [ewb]; exact hw')
      simpa only [off, ewb] using this

theorem pop_sound {τ τ' : T} {j : Instr} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (ha : Agree τ b₁ b₂)
    (hs : pop τ j = some τ') (e₁ : isa.pop j a₁ b₁ = some c₁) (e₂ : isa.pop j a₂ b₂ = some c₂)
    (_hadr : isa.addrs j b₁ = isa.addrs j b₂) : Agree τ' c₁ c₂ := by
  intro _
  obtain ⟨b, rfl⟩ : ∃ b, j = .free b := by
    cases j <;> simp only [pop, reduceCtorEq] at hs
    exact ⟨_, rfl⟩
  simp only [pop] at hs
  split at hs <;> [skip; cases hs]
  rename_i hc
  cases hs
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
  obtain ⟨⟨hok, hnf⟩, hle⟩ := hc
  obtain ⟨hsp, hspN, hwbW, hpub, hlo, hwp, hbp, hrd, hwr, hunk, F, B, hw, hl, hf, hout, hmem⟩ := ha hok
  simp only [isa, RISCV64.pop] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  rename_i hc₁
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  obtain ⟨-, -, -, hsp₁, hwr₁, hhd⟩ := hc₁
  obtain ⟨f, F', rfl⟩ : ∃ f F', F = f :: F' := by
    cases F with
    | nil => simp only [List.length_nil] at hl; omega_using [hl, hnf]
    | cons f F' => exact ⟨f, F', rfl⟩
  obtain ⟨hfb, hfl, hf'⟩ := hf
  have hfe : f = ⟨b₁.sp, b⟩ := by
    rw [← hsp₁, ← hwr₁, hw] at hhd
    simpa using hhd
  have hlen : f.len = b := by rw [hfe]
  rw [hlen] at hf'
  have hwb := hwbW
  have hspb : b₁.sp = wb τ b₁ + BitVec.ofNat 64 τ.sp := by simp only [wb]; bv_omega
  have htn : (wb τ b₁).toNat + τ.sp = b₁.sp.toNat := by
    simp only [wb]; rw [toNat_sub_ofNat' _ hspN]; omega_using [hspN]
  have ewb : wb { τ with sp := τ.sp + b, nf := τ.nf - 1 } { b₁ with sp := b₁.sp + BitVec.ofNat 64 b, wr := b₁.wr.tail, mem := lose b₁.mem b₁.sp b b₁.unknowns, unknowns := fun n => b₁.unknowns (n + b / 4) } = wb τ b₁ := by
    simp only [wb, BitVec.ofNat_add]; bv_omega
  refine ⟨by rw [hsp], ?_, by rw [ewb]; exact hwbW, hpub, hlo, fun e he => ?_, fun e he => ?_, hrd,
    by rw [hwr], by rw [hunk], F', B, by rw [hw]; rfl, by simp only [List.length_cons] at hl; show F'.length = τ.nf - 1; omega_using [hl],
    by rw [ewb]; exact hf', ?_, ?_⟩
  · show τ.sp + b ≤ (b₁.sp + BitVec.ofNat 64 b).toNat
    rw [toNat_add_of_lt' b₁.sp (by omega_using [htn, hle, hwb])]
    omega_using [hspN]
  · rw [ewb]; exact hwp e he
  · obtain ⟨h1, h2⟩ := hbp e he
    exact ⟨h1, fun i hi => by unfold InWin off; rw [ewb]; exact h2 i hi⟩
  · intro g hg x hx
    unfold InWin off; rw [ewb]; exact hout g hg x hx
  · intro x hx hs
    simp only [lose, hsp, hunk]
    split
    · split
      · exact hmem x hx fun hw' => by
          have := hs (by unfold InWin off; rw [ewb]; exact hw')
          simpa only [off, ewb] using this
      · rfl
    · exact hmem x hx fun hw' => by
        have := hs (by unfold InWin off; rw [ewb]; exact hw')
        simpa only [off, ewb] using this

/-- The state after a call. -/
def callS (s : State) : State :=
  { s with
    gpr := fun r =>
      match r with
      | .ra => s.unknowns 0 | .t0 => s.unknowns 1 | .t1 => s.unknowns 2
      | .t2 => s.unknowns 3 | .t3 => s.unknowns 4 | .t4 => s.unknowns 5
      | .t5 => s.unknowns 6 | .t6 => s.unknowns 7 | r => s.gpr r
    unknowns := fun n => s.unknowns (n + 8) }

theorem call_eq (s : State) : RISCV64.call s = some (callS s) := rfl

theorem call_gpr_out {s : State} {r : Reg} (hr : r ∉ callRegs) : (callS s).gpr r = s.gpr r := by
  cases r <;> simp_all [callRegs, callS]

theorem call_gpr_in {s₁ s₂ : State} (hu : s₁.unknowns = s₂.unknowns) {r : Reg} (hr : r ∈ callRegs) :
    (callS s₁).gpr r = (callS s₂).gpr r := by
  cases r <;> simp_all [callRegs, callS]

/-- What the analysis knows after making the registers `rs` public. -/
theorem foldl_setR : ∀ (rs : List Reg) (τ : T),
    let τ' := rs.foldl (fun τ r => RTaint.setR τ r true none none) τ
    τ'.ok = τ.ok ∧ τ'.W = τ.W ∧ τ'.sp = τ.sp ∧ τ'.nf = τ.nf ∧ τ'.sec = τ.sec ∧
      (∀ r ∈ τ'.pub, r ∈ rs ∨ r ∈ τ.pub) ∧ (∀ e ∈ τ'.wp, e ∈ τ.wp ∧ e.1 ∉ rs) ∧
      (∀ e ∈ τ'.bp, e ∈ τ.bp ∧ e.1 ∉ rs) ∧ (Reg.a0 ∉ rs → τ'.lo = τ.lo)
  | [], τ => ⟨rfl, rfl, rfl, rfl, rfl, fun _ h => .inr h, fun _ h => ⟨h, by simp⟩,
      fun _ h => ⟨h, by simp⟩, fun _ => rfl⟩
  | q :: rs, τ => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := foldl_setR rs (RTaint.setR τ q true none none)
    simp only [List.foldl_cons]
    refine ⟨h1, h2, h3, h4, h5, fun r hr => ?_, fun e he => ?_, fun e he => ?_, fun ha => ?_⟩
    · rcases h6 r hr with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · simp only [RTaint.setR, ite_true] at h
        rcases RegSet.mem_insert.mp h with rfl | h
        · exact .inl List.mem_cons_self
        · exact .inr h
    · obtain ⟨he, hn⟩ := h7 e he
      simp only [RTaint.setR, List.nil_append, List.mem_filter, bne_iff_ne, ne_eq] at he
      exact ⟨he.1, by simp only [List.mem_cons, not_or]; exact ⟨he.2, hn⟩⟩
    · obtain ⟨he, hn⟩ := h8 e he
      simp only [RTaint.setR, List.nil_append, List.mem_filter, bne_iff_ne, ne_eq] at he
      exact ⟨he.1, by simp only [List.mem_cons, not_or]; exact ⟨he.2, hn⟩⟩
    · simp only [List.mem_cons, not_or] at ha
      rw [h9 ha.2]
      have : (q == Reg.a0) = false := by simp only [beq_eq_false_iff_ne]; exact Ne.symm ha.1
      simp only [RTaint.setR, this, Bool.false_eq_true, ite_false]

theorem call_sound {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂) (hs : RTaint.call τ = some τ')
    (e₁ : isa.call s₁ = some s₁') (e₂ : isa.call s₂ = some s₂')
    (_hadr : isa.callAddrs s₁ = isa.callAddrs s₂) : Agree τ' s₁' s₂' := by
  intro _
  simp only [RTaint.call] at hs
  split at hs <;> [skip; cases hs]
  rename_i hok
  cases hs
  simp only [isa, call_eq, Option.some.injEq] at e₁ e₂
  subst e₁ e₂
  obtain ⟨hsp, hspN, hwbW, hpub, hlo, hwp, hbp, hrd, hwr, hunk, F, B, hw, hl, hf, hout, hmem⟩ := ha hok
  obtain ⟨-, hW, hsp', hnf, hsec, hp, hwp', hbp', hlo'⟩ := foldl_setR callRegs τ
  have ewb : wb (callRegs.foldl (fun τ r => RTaint.setR τ r true none none) τ) (callS s₁) = wb τ s₁ := by
    simp only [wb, hsp']; rfl
  have ein : ∀ x, InWin (callRegs.foldl (fun τ r => RTaint.setR τ r true none none) τ) (callS s₁) x ↔
      InWin τ s₁ x := by intro x; simp only [InWin, off, ewb, hW]
  refine ⟨hsp, by rw [hsp']; exact hspN, by rw [ewb, hW]; exact hwbW, fun r hr => ?_, ?_,
    fun e he => ?_, fun e he => ?_, hrd, hwr, by simp only [callS, hunk], F, B, hw, by rw [hnf]; exact hl,
    by rw [ewb, hW, hsp']; exact hf, fun g hg x hx => (not_congr (ein x)).mpr (hout g hg x hx),
    fun x hx hs => hmem x hx fun hw' => ?_⟩
  · rcases hp r hr with h | h
    · exact call_gpr_in hunk h
    · by_cases hc : r ∈ callRegs
      · exact call_gpr_in hunk hc
      · rw [call_gpr_out hc, call_gpr_out hc]; exact hpub r h
  · rw [hlo' (by decide), call_gpr_out (by decide), call_gpr_out (by decide)]; exact hlo
  · obtain ⟨he, hn⟩ := hwp' e he
    rw [ewb, call_gpr_out hn, call_gpr_out hn]; exact hwp e he
  · obtain ⟨he, hn⟩ := hbp' e he
    rw [call_gpr_out hn, call_gpr_out hn]
    obtain ⟨h1, h2⟩ := hbp e he
    exact ⟨h1, fun i hi => (not_congr (ein _)).mpr (h2 i hi)⟩
  · have := hs ((ein x).mpr hw')
    simp only [off, ewb, hsec] at this
    exact this

theorem ret_sound {τ τ' : T} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (ha : Agree τ b₁ b₂)
    (hs : RTaint.ret τ = some τ') (e₁ : isa.ret a₁ b₁ = some c₁) (e₂ : isa.ret a₂ b₂ = some c₂)
    (_hadr : isa.retAddrs b₁ = isa.retAddrs b₂) : Agree τ' c₁ c₂ := by
  simp only [RTaint.ret] at hs
  split at hs <;> [skip; cases hs]
  cases hs
  simp only [isa, RISCV64.ret] at e₁ e₂
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
  step := RTaint.step
  step_sound ha hs e₁ e₂ hadr := RTaint.step_sound ha hs e₁ e₂ hadr
  addrs_length := RTaint.addrs_length
  meet := RTaint.meet
  meet_left := RTaint.meet_left
  meet_right := RTaint.meet_right
  le := RTaint.le
  le_sound := RTaint.le_sound
  call := RTaint.call
  call_sound ha hs e₁ e₂ hadr := RTaint.call_sound ha hs e₁ e₂ hadr
  callAddrs_length _ _ := rfl
  ret := RTaint.ret
  ret_sound ha hs e₁ e₂ hadr := RTaint.ret_sound ha hs e₁ e₂ hadr
  retAddrs_length _ _ := rfl
  push := RTaint.push
  push_sound ha hs e₁ e₂ hadr := RTaint.push_sound ha hs e₁ e₂ hadr
  pop := RTaint.pop
  pop_sound ha hs e₁ e₂ hadr := RTaint.pop_sound ha hs e₁ e₂ hadr

namespace RTaint

/-- Where the analysis starts holds of two states that `NoResidue` compares,
whose window of `W` bytes below the stack pointer is outside every region
and outside the `e.2` bytes from what each register `e.1` of `bp0` holds. -/
theorem agree_init {W : Nat} {bp0 : List (Reg × Nat)} {s₁ s₂ : State} (ho : Outside 0 s₁ s₂)
    (hu : s₁.unknowns = s₂.unknowns) (hW : W ≤ s₁.sp.toNat)
    (hreg : ∀ g ∈ s₁.rd ++ s₁.wr, ∀ x, g.Contains x 1 → ¬ (x - (s₁.sp - BitVec.ofNat 64 W)).toNat < W)
    (hbp : ∀ e ∈ bp0, ∀ i < e.2, ¬ (s₁.gpr e.1 + BitVec.ofNat 64 i - (s₁.sp - BitVec.ofNat 64 W)).toNat < W) :
    Agree (init W bp0) s₁ s₂ := by
  intro _
  obtain ⟨hrd, hwr, hg, ha0, hsp, hmem⟩ := ho
  have hwb : wb (init W bp0) s₁ = s₁.sp - BitVec.ofNat 64 W := rfl
  have hall : ∀ r, s₁.gpr r = s₂.gpr r := by
    intro r
    by_cases h : r = .a0
    · subst h; simpa only [BitVec.ushiftRight_zero] using ha0
    · exact hg r h
  refine ⟨hsp, hW, ?_, (fun r _ => hall r), (by simp only [init, BitVec.ushiftRight_zero]; exact hall _),
    (fun e he => nomatch he), (fun e he => ⟨(hall e.1).symm, fun i hi => hbp e he i hi⟩), hrd, hwr, hu,
    [], s₁.wr, rfl, rfl, rfl, (fun g hg x hx => hreg g hg x hx), (fun x hx _ => hmem x hx)⟩
  rw [hwb, toNat_sub_ofNat' _ hW]
  have := s₁.sp.isLt
  show s₁.sp.toNat - W + W < 2 ^ 64
  omega_using [hW, this]

theorem mem_scratch_or {q : Reg} (hq : q ≠ .a0) : q ∈ scratch ∨ q ∈ preserved ∨ q = .ra := by
  cases q <;> simp_all [scratch, preserved]

/-- Two runs whose analysis ends in `done r`, from states that agree on what
the calling convention preserves, and that preserve it, agree outside the
buffers but the `r` low bits of `a0`. -/
theorem outside_of_done {τ : T} {r : Nat} {s₁ s₂ s₁' s₂' : State} (h : Agree τ s₁' s₂')
    (hd : done r τ = true) (ho : Outside 0 s₁ s₂) (hp₁ : abiPreserved s₁ s₁') (hp₂ : abiPreserved s₂ s₂') :
    Outside r s₁' s₂' := by
  simp only [done, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.ble_eq] at hd
  obtain ⟨⟨⟨⟨⟨hok, hnf⟩, -⟩, hsec⟩, hscr⟩, hlo⟩ := hd
  obtain ⟨hsp, -, -, hpub, hlo', -, -, hrd, hwr, -, F, B, hw, hl, -, -, hmem⟩ := h hok
  obtain rfl : F = [] := List.eq_nil_of_length_eq_zero (by rw [hl, hnf])
  rw [List.nil_append] at hw
  refine ⟨hrd, hwr, fun q hq => ?_, shr_mono hlo' hlo, hsp, fun x hx => ?_⟩
  · rcases mem_scratch_or hq with hs | hs | rfl
    · exact hpub q (hscr q hs)
    · rw [hp₁.1 q hs, hp₂.1 q hs]; exact ho.2.2.1 q (by cases hs' : q <;> simp_all [preserved])
    · rw [hp₁.2.2, hp₂.2.2]; exact ho.2.2.1 .ra (by decide)
  · refine hmem x (fun g hg hc => hx g (by rw [hw] at *; exact hg) hc) fun _ => ?_
    rw [hsec]; exact Nat.zero_testBit _

/-- Code verified against its contract, whose analysis from where it starts
(`init W bp0`, for states its precondition makes as `agree_init` needs) ends
in `done r`, returns without secret residue with an `r`-bit result. -/
theorem noResidue_of_verified {c : Prog isa} {k : Contract isa} {r W : Nat} {bp0 : List (Reg × Nat)}
    (hv : Verified target c k)
    (hpre : ∀ s, k.pre s → W ≤ s.sp.toNat ∧
      (∀ g ∈ s.rd ++ s.wr, ∀ x, g.Contains x 1 → ¬ (x - (s.sp - BitVec.ofNat 64 W)).toNat < W) ∧
      ∀ e ∈ bp0, ∀ i < e.2, ¬ (s.gpr e.1 + BitVec.ofNat 64 i - (s.sp - BitVec.ofNat 64 W)).toNat < W)
    (h : ∃ hc, (rtaint.check (init W bp0) c hc).any (done r) = true) : NoResidue c k r := by
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

end VG.RISCV64.RTaint
