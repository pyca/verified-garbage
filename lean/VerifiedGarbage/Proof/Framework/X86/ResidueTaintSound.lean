module

public import VerifiedGarbage.Proof.Framework.X86.ResidueTaint
public import VerifiedGarbage.TCB.X86.Residue
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Reduce

/-!
# The residue analysis is sound (x86, 32-bit)

`Agree τ s₁ s₂` is what `τ` (`ResidueTaint.lean`) says of two states, from
the window's base, `esp` less the offset `τ.sp` (`wb`, 32 bits; `wbA`, its
address), as on ARMv7 (`Proof/Framework/Arm/ResidueTaintSound.lean`): the
stack pointers and the public registers agree, and the flags (defined) if
`τ.fl`, and the XMM registers `τ.px` lists; the registers of `wp` hold what
they say; the items of the stack still open tile the window from `τ.sp` to
its top (`Frames`), their frames being the writable regions at the head of
`wr`; the other writable regions and the readable ones are outside the
window; the memory outside them agrees but at the bytes of the window that
`τ.sec` lists; and so do the `τ.an` bytes of arguments above the return
address on entry, while `τ.ak`. The window, its return address and the
arguments are within the 32-bit address space (`wbW`), so an address the
code computes in them, 32 bits wide, is its offset from `wbA` (`addr_wb`).
Each transfer function keeps `Agree` (`step_sound`, …), which makes `rtaint`
a `TaintCT`.
-/

@[expose] public section

namespace VG.X86.RTaint

open VG.X86

/-! ## Bit masks -/

theorem testBit_ones (w k : Nat) : (ones w).testBit k = decide (k < w) := Nat.testBit_two_pow_sub_one w k

/-- Bit `k` is one of the `w` bits from bit `d`, as `Nat.testBit_shiftLeft` and as an interval. -/
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

theorem bnone_bit {b d w k : Nat} (h : bnone b d w = true) (h₁ : d ≤ k) (h₂ : k < d + w) : b.testBit k = false := by
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

/-- The window's base: `esp` less the offset the analysis knows it at. -/
def wb (τ : T) (s : State) : BitVec 32 := s.gpr .esp - BitVec.ofNat 32 τ.sp

/-- The window's base, as an address. -/
def wbA (τ : T) (s : State) : Addr := (wb τ s).setWidth 64

/-- The offset of `x` from the window's base. -/
def off (τ : T) (s : State) (x : Addr) : Nat := (x - wbA τ s).toNat

/-- `x` is in the window. -/
def InWin (τ : T) (s : State) (x : Addr) : Prop := off τ s x < τ.W

/-- The items `st` of the stack, innermost first, tile the window of `W`
bytes at `w` from offset `o` to its top, their frames' regions being `F`. -/
def Frames (w : Addr) (W : Nat) : Nat → List Nat → List Region → Prop
  | o, [], F => o = W ∧ F = []
  | o, n :: st, F =>
    if n = 0 then Frames w W (o + 4) st F
    else ∃ F', F = ⟨w + BitVec.ofNat 64 o, n⟩ :: F' ∧ Frames w W (o + size n) st F'

/-- The flags of two states agree, and are defined. -/
def FlagsOk (s₁ s₂ : State) : Prop :=
  s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of ∧ FlagsDefined s₁

/-- The frames still open, and the memory outside the buffers. -/
def Regions (τ : T) (s₁ s₂ : State) : Prop :=
  ∃ F B, s₁.wr = F ++ B ∧ Frames (wbA τ s₁) τ.W τ.sp τ.stk F ∧
    (∀ g ∈ s₁.rd ++ B, ∀ x, g.Contains x 1 → ¬ InWin τ s₁ x) ∧
    ∀ x, (∀ g ∈ s₁.rd ++ B, ¬ g.Contains x 1) → (InWin τ s₁ x → τ.sec.testBit (off τ s₁ x) = false) →
      s₁.mem x = s₂.mem x

/-- The window's base is the same in states with the same `esp`, of analyses
with the same `sp`. -/
theorem wbA_congr {τ τ' : T} {s s' : State} (hsp : τ'.sp = τ.sp) (he : s'.gpr .esp = s.gpr .esp) :
    wbA τ' s' = wbA τ s := by simp only [wbA, wb, hsp, he]

theorem off_congr {τ τ' : T} {s s' : State} (hsp : τ'.sp = τ.sp) (he : s'.gpr .esp = s.gpr .esp) (x : Addr) :
    off τ' s' x = off τ s x := by simp only [off, wbA_congr hsp he]

theorem inWin_congr {τ τ' : T} {s s' : State} (hsp : τ'.sp = τ.sp) (hW : τ'.W = τ.W)
    (he : s'.gpr .esp = s.gpr .esp) (x : Addr) : InWin τ' s' x ↔ InWin τ s x := by
  simp only [InWin, off_congr hsp he, hW]

/-- `Regions` of states with the same stack pointer, regions and memory. -/
theorem Regions.congr {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (h : Regions τ s₁ s₂) (hsp : τ'.sp = τ.sp)
    (hW : τ'.W = τ.W) (hstk : τ'.stk = τ.stk) (hsec : τ'.sec = τ.sec) (he : s₁'.gpr .esp = s₁.gpr .esp)
    (hrd : s₁'.rd = s₁.rd) (hwr : s₁'.wr = s₁.wr) (hm₁ : s₁'.mem = s₁.mem) (hm₂ : s₂'.mem = s₂.mem) :
    Regions τ' s₁' s₂' := by
  obtain ⟨F, B, hw, hf, hout, hmem⟩ := h
  refine ⟨F, B, by rw [hwr]; exact hw, by rw [wbA_congr hsp he, hW, hsp, hstk]; exact hf,
    fun g hg x hx => (not_congr (inWin_congr hsp hW he x)).mpr (hout g (by rw [hrd] at hg; exact hg) x hx),
    fun x hx hs => ?_⟩
  rw [hm₁, hm₂]
  refine hmem x (fun g hg => hx g (by rw [hrd]; exact hg)) fun hw' => ?_
  have := hs ((inWin_congr hsp hW he x).mpr hw')
  rwa [hsec, off_congr hsp he] at this

/-- What `τ` says of the two states (see the module's documentation). -/
structure AgreeOk (τ : T) (s₁ s₂ : State) : Prop where
  sp : s₁.gpr .esp = s₂.gpr .esp
  spNat : τ.sp ≤ (s₁.gpr .esp).toNat
  wbW : (wb τ s₁).toNat + τ.W + 4 + τ.an ≤ 2 ^ 32
  pub : ∀ r ∈ τ.pub, s₁.gpr r = s₂.gpr r
  fl : τ.fl = true → FlagsOk s₁ s₂
  px : ∀ x, pubX τ x = true → s₁.xmm x = s₂.xmm x
  wp : ∀ e ∈ τ.wp, e.1 ≠ .esp ∧ s₁.gpr e.1 = wb τ s₁ + BitVec.ofNat 32 e.2 ∧ s₂.gpr e.1 = s₁.gpr e.1
  rd : s₁.rd = s₂.rd
  wr : s₁.wr = s₂.wr
  unk : s₁.unknowns = s₂.unknowns
  mm : s₁.mm = s₂.mm
  mmx : s₁.mmx = s₂.mmx
  mxcsr : s₁.mxcsr = s₂.mxcsr
  mcdt : s₁.mcdt = s₂.mcdt
  arg : τ.ak = true → ∀ j < τ.an,
    s₁.mem (wbA τ s₁ + BitVec.ofNat 64 (τ.W + 4 + j)) = s₂.mem (wbA τ s₁ + BitVec.ofNat 64 (τ.W + 4 + j))
  regions : Regions τ s₁ s₂

def Agree (τ : T) (s₁ s₂ : State) : Prop := τ.ok = true → AgreeOk τ s₁ s₂

/-! ## Registers -/

theorem isSp_false {r : Reg} (h : isSp r = false) : r ≠ .esp := by
  rintro rfl; cases h

theorem isSp_true {r : Reg} (h : isSp r = true) : r = .esp := by
  cases r <;> first | rfl | cases h

theorem regEq_iff {a b : Reg} : regEq a b = true ↔ a = b := by
  cases a <;> cases b <;> decide

theorem find_wp {l : List (Reg × Nat)} {r : Reg} {e : Reg × Nat}
    (h : l.find? (fun e => regEq e.1 r) = some e) : e ∈ l ∧ e.1 = r := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  exact regEq_iff.mp this

/-- The stack pointer is at byte `τ.sp` of the window. -/
theorem sp_eq {τ : T} {s : State} : s.gpr .esp = wb τ s + BitVec.ofNat 32 τ.sp := by
  simp only [wb]; bv_omega

/-- What `wpOf` says of a register. -/
theorem AgreeOk.wpOf {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {r : Reg} {k : Nat}
    (hk : RTaint.wpOf τ r = some k) : s₁.gpr r = wb τ s₁ + BitVec.ofNat 32 k ∧ s₂.gpr r = s₁.gpr r := by
  unfold RTaint.wpOf at hk
  split at hk
  · rename_i hs
    cases hk
    obtain rfl := isSp_true hs
    exact ⟨sp_eq, h.sp.symm⟩
  · simp only [Option.map_eq_some_iff] at hk
    obtain ⟨e, he, rfl⟩ := hk
    obtain ⟨hm, hr⟩ := find_wp he
    obtain ⟨-, h1, h2⟩ := h.wp e hm
    rw [hr] at h1 h2
    exact ⟨h1, h2⟩

/-- `setR` describes a write of `d` (not `esp`): of the same value in both
runs if `p`, of byte `k` of the window if `k`. -/
theorem AgreeOk.setR {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {d : Reg} (hd : d ≠ .esp) {p : Bool}
    {k : Option Nat} {v₁ v₂ : BitVec 32} (hp : p = true → v₁ = v₂)
    (hk : ∀ k', k = some k' → v₁ = wb τ s₁ + BitVec.ofNat 32 k' ∧ v₂ = v₁) :
    AgreeOk (RTaint.setR τ d p k) (s₁.setReg d v₁) (s₂.setReg d v₂) := by
  obtain ⟨hsp, hspN, hwbW, hpub, hfl, hpx, hwp, hrd, hwr, hunk, hmm, hmmx, hmx, hmc, harg, hreg⟩ := h
  have esp₁ : (s₁.setReg d v₁).gpr .esp = s₁.gpr .esp := RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hd)
  have esp₂ : (s₂.setReg d v₂).gpr .esp = s₂.gpr .esp := RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hd)
  have ewb : wb (RTaint.setR τ d p k) (s₁.setReg d v₁) = wb τ s₁ := by simp only [wb, esp₁]; rfl
  have ewbA : wbA (RTaint.setR τ d p k) (s₁.setReg d v₁) = wbA τ s₁ := by simp only [wbA, ewb]
  refine ⟨by rw [esp₁, esp₂, hsp], by rw [esp₁]; exact hspN, by rw [ewb]; exact hwbW, fun r hr => ?_, hfl,
    hpx, fun e he => ?_, hrd, hwr, hunk, hmm, hmmx, hmx, hmc, fun hak j hj => by rw [ewbA]; exact harg hak j hj,
    hreg.congr rfl rfl rfl rfl esp₁ rfl rfl rfl rfl⟩
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
  · simp only [RTaint.setR, List.mem_append, List.mem_filter, Bool.not_eq_true'] at he
    rw [ewb]
    rcases he with he | ⟨he, hne⟩
    · cases k with
      | none => simp at he
      | some k' =>
        simp only [List.mem_singleton] at he
        subst he
        obtain ⟨e1, e2⟩ := hk k' rfl
        simp only [RegUpd.gpr_setReg_self]
        exact ⟨hd, e1, e2⟩
    · have hne' : e.1 ≠ d := fun h => by rw [h] at hne; simp [regEq] at hne
      rw [RegUpd.gpr_setReg_of_ne _ _ hne', RegUpd.gpr_setReg_of_ne _ _ hne']
      exact hwp e he

/-- A register written with values that are the same if `p`. -/
theorem AgreeOk.setP {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {d : Reg} (hd : d ≠ .esp) {p : Bool}
    {v₁ v₂ : BitVec 32} (hp : p = true → v₁ = v₂) :
    AgreeOk (RTaint.setR τ d p none) (s₁.setReg d v₁) (s₂.setReg d v₂) :=
  h.setR hd hp (fun _ h => nomatch h)

theorem AgreeOk.reg {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {r : Reg} (hr : pubR τ r = true) :
    s₁.gpr r = s₂.gpr r := h.pub r hr

theorem AgreeOk.withPub {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {n : Reg}
    (hn : s₁.gpr n = s₂.gpr n) : AgreeOk (RTaint.withPub τ n) s₁ s₂ := by
  obtain ⟨hsp, hspN, hwbW, hpub, hfl, hpx, hwp, hrd, hwr, hunk, hmm, hmmx, hmx, hmc, harg, hreg⟩ := h
  refine ⟨hsp, hspN, hwbW, fun r hr => ?_, hfl, hpx, hwp, hrd, hwr, hunk, hmm, hmmx, hmx, hmc, harg, hreg⟩
  rcases RegSet.mem_insert.mp hr with rfl | hr
  · exact hn
  · exact hpub r hr

/-- The flags of two states set, public (and defined) if `p`. -/
theorem AgreeOk.setF {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {p : Bool} {c₁ z₁ n₁ o₁ c₂ z₂ n₂ o₂ : Option Bool}
    (hp : p = true → FlagsOk (s₁.setFlags c₁ o₁ z₁ n₁) (s₂.setFlags c₂ o₂ z₂ n₂)) :
    AgreeOk (RTaint.setF τ p) (s₁.setFlags c₁ o₁ z₁ n₁) (s₂.setFlags c₂ o₂ z₂ n₂) := by
  obtain ⟨hsp, hspN, hwbW, hpub, -, hpx, hwp, hrd, hwr, hunk, hmm, hmmx, hmx, hmc, harg, hreg⟩ := h
  exact ⟨hsp, hspN, hwbW, hpub, hp, hpx, hwp, hrd, hwr, hunk, hmm, hmmx, hmx, hmc, harg, hreg⟩

/-- An XMM register written with values that are the same if `p`. -/
theorem AgreeOk.setX {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) (x : XReg) {p : Bool}
    {v₁ v₂ : BitVec 128} (hp : p = true → v₁ = v₂) :
    AgreeOk (RTaint.setX τ x p) (s₁.setXmm x v₁) (s₂.setXmm x v₂) := by
  obtain ⟨hsp, hspN, hwbW, hpub, hfl, hpx, hwp, hrd, hwr, hunk, hmm, hmmx, hmx, hmc, harg, hreg⟩ := h
  refine ⟨hsp, hspN, hwbW, hpub, hfl, fun y hy => ?_, hwp, hrd, hwr, hunk, hmm, hmmx, hmx, hmc, harg, hreg⟩
  simp only [State.setXmm]
  by_cases hxy : y = x
  · subst hxy
    simp only [ite_true]
    cases p
    · simp only [pubX, RTaint.setX, Bool.false_eq_true, ite_false, testBit_bclr, Nat.le_refl, decide_true,
        Nat.lt_add_one, Bool.and_self, Bool.not_true, Bool.and_false] at hy
    · exact hp rfl
  · simp only [hxy, ite_false]
    refine hpx y ?_
    have hne : xidx y ≠ xidx x := by revert hxy; cases x <;> cases y <;> simp [xidx]
    simp only [pubX, RTaint.setX] at hy ⊢
    split at hy
    · change (τ.px ||| 2 ^ xidx x).testBit (xidx y) = true at hy
      rw [Nat.testBit_or, Nat.testBit_two_pow] at hy
      simpa [Ne.symm hne] using hy
    · rw [testBit_bclr] at hy
      simp only [Bool.and_eq_true] at hy
      exact hy.1

/-! ## Addresses in the window -/

theorem toNat_ofNat_lt {j : Nat} (h : j < 2 ^ 64) : (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Byte `j` of the window is at offset `j`. -/
theorem off_base (τ : T) (s : State) {j : Nat} (hj : j < 2 ^ 64) :
    off τ s (wbA τ s + BitVec.ofNat 64 j) = j := by
  have e : wbA τ s + BitVec.ofNat 64 j - wbA τ s = BitVec.ofNat 64 j := by bv_omega
  simp only [off, e, toNat_ofNat_lt hj]

theorem toNat_w64 (a : BitVec 32) : (a.setWidth 64).toNat = a.toNat := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide))

theorem toNat_wbA (τ : T) (s : State) : (wbA τ s).toNat = (wb τ s).toNat := toNat_w64 _

/-- A 32-bit sum that does not wrap, widened. -/
theorem addr_add {a : BitVec 32} {k : Nat} (h : a.toNat + k < 2 ^ 32) :
    (a + BitVec.ofNat 32 k).setWidth 64 = a.setWidth 64 + BitVec.ofNat 64 k := addr_eq h

/-- An address the code computes in the window, as an offset from its base. -/
theorem addr_wb (τ : T) (s : State) {j : Nat} (h : (wb τ s).toNat + j < 2 ^ 32) :
    (wb τ s + BitVec.ofNat 32 j).setWidth 64 = wbA τ s + BitVec.ofNat 64 j := addr_add h

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

theorem size_pos (n : Nat) : 0 < size n := by
  unfold size; split <;> [omega; split <;> omega]

theorem Frames.le {w : Addr} {W : Nat} : ∀ {o : Nat} {st : List Nat} {F : List Region},
    Frames w W o st F → o ≤ W
  | _, [], _, h => by simp only [Frames] at h; omega_using [h.1]
  | o, n :: st, F, h => by
    simp only [Frames] at h
    split at h
    · have := Frames.le h; omega_using [this]
    · obtain ⟨F', -, hf⟩ := h
      have h1 := Frames.le hf; have h2 := size_pos n; omega_using [h1, h2]

/-- A frame's bytes are in the window, from the offset of the frames on. -/
theorem Frames.contains {w : Addr} {W : Nat} (hw : W < 2 ^ 32) :
    ∀ {o : Nat} {st : List Nat} {F : List Region}, Frames w W o st F → ∀ g ∈ F, ∀ x, g.Contains x 1 →
      o ≤ (x - w).toNat ∧ (x - w).toNat < W
  | _, [], F, h, g, hg, _, _ => by simp only [Frames] at h; rw [h.2] at hg; exact nomatch hg
  | o, n :: st, F, h, g, hg, x, hx => by
    simp only [Frames] at h
    split at h
    · have := Frames.contains hw h g hg x hx; omega_using [this]
    · rename_i hn
      obtain ⟨F', rfl, hf⟩ := h
      have hle := Frames.le hf
      have hs : n ≤ size n := by unfold size; split <;> [omega; split <;> omega]
      rcases List.mem_cons.mp hg with rfl | hg
      · simp only [Region.Contains] at hx
        have := (Offset.lt_iff x w (d := o) (n := n) (by omega_using [hw, hle, hs])).mp (by omega_using [hx])
        omega_using [this, hle, hs]
      · have := Frames.contains hw hf g hg x hx
        have := size_pos n
        omega_using [this, ‹o + size n ≤ (x - w).toNat ∧ (x - w).toNat < W›]

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

/-- The address of an access through byte `k` of the window, at `ofs`. -/
theorem wp_addr {τ : T} {s : State} {v : BitVec 32} {k ofs : Nat} (h : v = wb τ s + BitVec.ofNat 32 k)
    (hk : (wb τ s).toNat + (k + ofs) < 2 ^ 32) :
    (v + BitVec.ofNat 32 ofs).setWidth 64 = wbA τ s + BitVec.ofNat 64 (k + ofs) := by
  rw [h, BitVec.add_assoc, BitVec.ofNat_add_ofNat, addr_wb τ s hk]

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

/-- An argument's byte is not in the window. -/
theorem arg_not_inWin {τ : T} {s : State} (hW : (wb τ s).toNat + τ.W + 4 + τ.an ≤ 2 ^ 32) {j : Nat}
    (hj : j < τ.an) : ¬ InWin τ s (wbA τ s + BitVec.ofNat 64 (τ.W + 4 + j)) := by
  unfold InWin
  rw [off_base τ s (by omega_using [hW, hj])]
  omega_using []

/-- Byte `j` of the arguments is not among `n` bytes at offset `o < W` of the window. -/
theorem arg_sep {τ : T} {s : State} (hW : (wb τ s).toNat + τ.W + 4 + τ.an ≤ 2 ^ 32) {j o n : Nat}
    (hj : j < τ.an) (ho : o + n ≤ τ.W) :
    ¬ (wbA τ s + BitVec.ofNat 64 (τ.W + 4 + j) - (wbA τ s + BitVec.ofNat 64 o)).toNat < n := by
  rw [in_range τ s _ (by omega_using [ho, hW]), off_base τ s (by omega_using [hW, hj])]
  omega_using [ho]

/-! ## Loads and stores -/

/-- A state with only its memory changed, where `τ'` differs from `τ` at
most in its mask and in whether the arguments are known. -/
theorem AgreeOk.withMem {τ τ' : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {m₁ m₂ : Mem}
    (he : τ'.sp = τ.sp ∧ τ'.W = τ.W ∧ τ'.an = τ.an ∧ τ'.pub = τ.pub ∧ τ'.fl = τ.fl ∧ τ'.px = τ.px ∧
      τ'.stk = τ.stk ∧ τ'.wp = τ.wp)
    (hm : ∀ B, (∀ g ∈ s₁.rd ++ B, ∀ x, g.Contains x 1 → ¬ InWin τ s₁ x) →
      (∃ F, s₁.wr = F ++ B ∧ Frames (wbA τ s₁) τ.W τ.sp τ.stk F) →
      (∀ x, (∀ g ∈ s₁.rd ++ B, ¬ g.Contains x 1) → (InWin τ s₁ x → τ.sec.testBit (off τ s₁ x) = false) →
        s₁.mem x = s₂.mem x) →
      ∀ x, (∀ g ∈ s₁.rd ++ B, ¬ g.Contains x 1) → (InWin τ s₁ x → τ'.sec.testBit (off τ s₁ x) = false) →
        m₁ x = m₂ x)
    (ha : τ'.ak = true → τ.ak = true ∧ ∀ j < τ.an,
      s₁.mem (wbA τ s₁ + BitVec.ofNat 64 (τ.W + 4 + j)) = s₂.mem (wbA τ s₁ + BitVec.ofNat 64 (τ.W + 4 + j)) →
      m₁ (wbA τ s₁ + BitVec.ofNat 64 (τ.W + 4 + j)) = m₂ (wbA τ s₁ + BitVec.ofNat 64 (τ.W + 4 + j))) :
    AgreeOk τ' { s₁ with mem := m₁ } { s₂ with mem := m₂ } := by
  obtain ⟨hsp, hspN, hwbW, hpub, hfl, hpx, hwp, hrd, hwr, hunk, hmm, hmmx, hmx, hmc, harg, F, B, hw, hf, hout,
    hmem⟩ := h
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := he
  have ewb : wb τ' { s₁ with mem := m₁ } = wb τ s₁ := by simp only [wb, e1]
  have ewbA : wbA τ' { s₁ with mem := m₁ } = wbA τ s₁ := by simp only [wbA, ewb]
  have ein : ∀ x, InWin τ' { s₁ with mem := m₁ } x ↔ InWin τ s₁ x := by
    intro x; simp only [InWin, off, ewbA, e2]
  refine ⟨hsp, by rw [e1]; exact hspN, by rw [ewb, e2, e3]; exact hwbW, by rw [e4]; exact hpub,
    by rw [e5]; exact hfl, fun x hx => hpx x (by simpa only [pubX, e6] using hx),
    fun e he => ?_, hrd, hwr, hunk, hmm, hmmx, hmx, hmc, fun hak j hj => ?_,
    F, B, hw, by rw [ewbA, e2, e1, e7]; exact hf,
    fun g hg x hx => (not_congr (ein x)).mpr (hout g hg x hx), fun x hx hs => ?_⟩
  · rw [e8] at he; rw [ewb]; exact hwp e he
  · obtain ⟨hak', hj'⟩ := ha hak
    rw [ewbA, e2]
    rw [e3] at hj
    exact hj' j hj (harg hak' j hj)
  · exact hm B hout ⟨F, hw, hf⟩ hmem x hx (fun hw' => by
      have := hs ((ein x).mpr hw')
      simpa only [off, ewbA] using this)

/-- A store of `w` bytes (`0 < w ≤ 16`) at `a`, whose address is
`(g + ofs)` for a register value `g` the same in both runs, within a
writable region, of values that are the same if `p`, keeps what `storeT`
says, `k` being `g`'s window offset if known. -/
theorem storeT_sound {τ : T} {s₁ s₂ : State} (ha : AgreeOk τ s₁ s₂) {g : BitVec 32} {kk : Option Nat}
    {ofs w : Nat} (hk : ∀ k, kk = some k → g = wb τ s₁ + BitVec.ofNat 32 k) (hw0 : 0 < w)
    {v₁ v₂ : BitVec (8 * w)} {p : Bool}
    (hin₁ : InRegions s₁.wr ((g + BitVec.ofNat 32 ofs).setWidth 64) w) (hv : p = true → v₁ = v₂) :
    AgreeOk (storeT τ kk ofs w p)
      { s₁ with mem := s₁.mem.write ((g + BitVec.ofNat 32 ofs).setWidth 64) w v₁ }
      { s₂ with mem := s₂.mem.write ((g + BitVec.ofNat 32 ofs).setWidth 64) w v₂ } := by
  generalize ha' : (g + BitVec.ofNat 32 ofs).setWidth 64 = a at hin₁ ⊢
  have hW : (wb τ s₁).toNat + τ.W + 4 + τ.an ≤ 2 ^ 32 := ha.wbW
  have hW64 : (wbA τ s₁).toNat + τ.W + 4 + τ.an < 2 ^ 64 := by rw [toNat_wbA]; omega_using [hW]
  -- What a store leaves, for each byte it writes and each it does not.
  have gen : ∀ τ' : T, τ'.sp = τ.sp ∧ τ'.W = τ.W ∧ τ'.an = τ.an ∧ τ'.pub = τ.pub ∧ τ'.fl = τ.fl ∧
      τ'.px = τ.px ∧ τ'.stk = τ.stk ∧ τ'.wp = τ.wp →
      (∀ B, (∀ g ∈ s₁.rd ++ B, ∀ x, g.Contains x 1 → ¬ InWin τ s₁ x) →
        (∃ F, s₁.wr = F ++ B ∧ Frames (wbA τ s₁) τ.W τ.sp τ.stk F) →
        ∀ x, (x - a).toNat < w → (∀ g ∈ s₁.rd ++ B, ¬ g.Contains x 1) →
          (InWin τ s₁ x → τ'.sec.testBit (off τ s₁ x) = false) →
          v₁.extractLsb' (8 * (x - a).toNat) 8 = v₂.extractLsb' (8 * (x - a).toNat) 8) →
      (∀ x, ¬ (x - a).toNat < w → InWin τ s₁ x → τ'.sec.testBit (off τ s₁ x) = false →
        τ.sec.testBit (off τ s₁ x) = false) →
      (τ'.ak = true → τ.ak = true ∧ ∀ j < τ.an,
        (wbA τ s₁ + BitVec.ofNat 64 (τ.W + 4 + j) - a).toNat < w →
          v₁.extractLsb' (8 * (wbA τ s₁ + BitVec.ofNat 64 (τ.W + 4 + j) - a).toNat) 8 =
            v₂.extractLsb' (8 * (wbA τ s₁ + BitVec.ofNat 64 (τ.W + 4 + j) - a).toNat) 8) →
      AgreeOk τ' { s₁ with mem := s₁.mem.write a w v₁ } { s₂ with mem := s₂.mem.write a w v₂ } := by
    intro τ' he hwr hns hak
    refine ha.withMem he (fun B hout hF hmem x hx hs => ?_) (fun h => ⟨(hak h).1, fun j hj e => ?_⟩)
    · simp only [Mem.write]
      split
      · rename_i hw; exact hwr B hout hF x hw hx hs
      · rename_i hw; exact hmem x hx fun hw' => hns x hw hw' (hs hw')
    · simp only [Mem.write]
      split
      · rename_i hw; exact (hak h).2 j hj hw
      · exact e
  -- A public value.
  have pubCase : p = true → AgreeOk τ { s₁ with mem := s₁.mem.write a w v₁ }
      { s₂ with mem := s₂.mem.write a w v₂ } := fun hp =>
    gen τ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ _ _ x _ _ _ => by rw [hv hp]) (fun _ _ _ h => h)
      (fun h => ⟨h, fun _ _ _ => by rw [hv hp]⟩)
  -- A secret the analysis cannot place.
  have frameCase : AgreeOk (framesSec τ) { s₁ with mem := s₁.mem.write a w v₁ }
      { s₂ with mem := s₂.mem.write a w v₂ } := by
    refine gen _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun B hout hF x hx hxo hsx => ?_)
      (fun x _ _ h => ?_) (fun h => nomatch h)
    · obtain ⟨F, hw, hf⟩ := hF
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
  have elseCase : AgreeOk (if p = true then τ else framesSec τ) { s₁ with mem := s₁.mem.write a w v₁ }
      { s₂ with mem := s₂.mem.write a w v₂ } := by
    split
    · rename_i hp; exact pubCase hp
    · exact frameCase
  cases kk with
  | none => exact elseCase
  | some k =>
    have hk1 := hk k rfl
    simp only [storeT]
    split
    · -- In the window.
      rename_i hinW
      have hinW : k + ofs + w ≤ τ.W := Nat.le_of_ble_eq_true hinW
      have haddr := wp_addr (ofs := ofs) hk1 (by omega_using [hinW, hW])
      rw [ha'] at haddr
      subst haddr
      have hnot : ∀ j < τ.an, ¬ (wbA τ s₁ + BitVec.ofNat 64 (τ.W + 4 + j) -
          (wbA τ s₁ + BitVec.ofNat 64 (k + ofs))).toNat < w := fun j hj => arg_sep hW hj hinW
      by_cases hp : p = true
      · simp only [hp, ite_true]
        refine gen _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ _ _ x _ _ _ => by rw [hv hp])
          (fun x hx hw h => ?_) (fun h => ⟨h, fun j hj hx => absurd hx (hnot j hj)⟩)
        rw [in_range τ s₁ x (by omega_using [hinW, hW64])] at hx
        simp only [testBit_bclr, Bool.and_eq_false_iff, Bool.not_eq_false', Bool.and_eq_true,
          decide_eq_true_eq] at h
        rcases h with h | h
        · exact h
        · exact absurd h hx
      · simp only [hp, Bool.false_eq_true, ite_false]
        refine gen _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun B hout hF x hx hxo hsx => ?_)
          (fun x _ _ h => by simp only [testBit_bset, Bool.or_eq_false_iff] at h; exact h.1)
          (fun h => ⟨h, fun j hj hx => absurd hx (hnot j hj)⟩)
        exfalso
        rw [in_range τ s₁ x (by omega_using [hinW, hW64])] at hx
        have := hsx (by unfold InWin; omega_using [hx, hinW])
        simp only [testBit_bset, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
        omega_using [this.2, hx]
    · split
      · -- Among the arguments.
        rename_i _ harg
        simp only [Bool.and_eq_true, Nat.ble_eq] at harg
        obtain ⟨h1, h2⟩ := harg
        have haddr := wp_addr (ofs := ofs) hk1 (by omega_using [h2, hW, h1, hw0])
        rw [ha'] at haddr
        subst haddr
        -- No byte it writes is in the window, nor so in a frame.
        have hout : ∀ x, (x - (wbA τ s₁ + BitVec.ofNat 64 (k + ofs))).toNat < w → ¬ InWin τ s₁ x := by
          intro x hx hwin
          rw [in_range τ s₁ x (by omega_using [h2, hW64])] at hx
          unfold InWin at hwin
          omega_using [hx, hwin, h1]
        have hB : ∀ B, (∃ F, s₁.wr = F ++ B ∧ Frames (wbA τ s₁) τ.W τ.sp τ.stk F) →
            ∀ x, (x - (wbA τ s₁ + BitVec.ofNat 64 (k + ofs))).toNat < w → ∃ g ∈ s₁.rd ++ B, g.Contains x 1 := by
          intro B ⟨F, hw, hf⟩ x hx
          rcases store_region (B := B) hw hin₁ hx with ⟨g, hg, hc⟩ | h
          · exact absurd (Frames.contains (by omega_using [hW]) hf g hg x hc).2 (hout x hx)
          · exact h
        by_cases hp : p = true
        · simp only [hp, ite_true]; exact pubCase hp
        · simp only [hp, Bool.false_eq_true, ite_false]
          refine gen _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun B _ hF x hx hxo _ => ?_)
            (fun _ _ _ h => h) (fun h => nomatch h)
          obtain ⟨g, hg, hc⟩ := hB B hF x hx
          exact absurd hc (hxo g hg)
      · exact elseCase

/-- The `w` bytes at `ofs` from byte `k` of the window, if `loadPub` says
so, agree. -/
theorem load_bytes {τ : T} {s₁ s₂ : State} (ha : AgreeOk τ s₁ s₂) {k ofs w : Nat}
    (hp : loadPub τ (some k) ofs w = true) :
    ∀ j < w, s₁.mem (wbA τ s₁ + BitVec.ofNat 64 (k + ofs) + BitVec.ofNat 64 j) =
      s₂.mem (wbA τ s₁ + BitVec.ofNat 64 (k + ofs) + BitVec.ofNat 64 j) := by
  intro j hj
  simp only [loadPub, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at hp
  have hW := ha.wbW
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rcases hp with ⟨hin, hno⟩ | ⟨⟨hak, h1⟩, h2⟩
  · obtain ⟨F, B, -, -, hout, hmem⟩ := ha.regions
    have hx : off τ s₁ (wbA τ s₁ + BitVec.ofNat 64 (k + ofs + j)) = k + ofs + j :=
      off_base τ s₁ (by omega_using [hin, hj, hW])
    refine hmem _ (fun g hg hc => hout g hg _ hc ?_) (fun _ => ?_)
    · unfold InWin; rw [hx]; omega_using [hin, hj]
    · rw [hx]; exact bnone_bit hno (by omega_using []) (by omega_using [hj])
  · have := ha.arg hak (k + ofs + j - (τ.W + 4)) (by omega_using [h1, h2, hj])
    rwa [show τ.W + 4 + (k + ofs + j - (τ.W + 4)) = k + ofs + j by omega_using [h1]] at this

theorem loadPub_some {τ : T} {k : Option Nat} {ofs w : Nat} (h : loadPub τ k ofs w = true) :
    ∃ k', k = some k' ∧ loadPub τ (some k') ofs w = true ∧ k' + ofs + w ≤ τ.W + 4 + τ.an := by
  cases k with
  | none => cases h
  | some k' =>
    refine ⟨k', rfl, h, ?_⟩
    simp only [loadPub, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
    omega_using [h]

/-- A load of `w` bytes, at `ofs` from `v`, whose bytes `loadPub` says agree. -/
theorem load_read {τ : T} {s₁ s₂ : State} (ha : AgreeOk τ s₁ s₂) {v : BitVec 32} {kk : Option Nat}
    {ofs w : Nat} (hv : ∀ k, kk = some k → v = wb τ s₁ + BitVec.ofNat 32 k)
    (hp : loadPub τ kk ofs w = true) :
    s₁.mem.read ((v + BitVec.ofNat 32 ofs).setWidth 64) w = s₂.mem.read ((v + BitVec.ofNat 32 ofs).setWidth 64) w := by
  obtain ⟨k, rfl, hp', hle⟩ := loadPub_some hp
  have hW := ha.wbW
  have hw0 : 0 < w ∨ w = 0 := by omega_using []
  rcases hw0 with hw0 | rfl
  · rw [wp_addr (hv k rfl) (by omega_using [hle, hW, hw0])]
    rw [Mem.read_congr (load_bytes ha hp')]
  · rfl

/-- A store of a `w'`-bit value (`writeW`), as `storeT_sound`. -/
theorem storeW_sound {τ : T} {s₁ s₂ : State} (ha : AgreeOk τ s₁ s₂) {g : BitVec 32} {kk : Option Nat}
    {ofs w' : Nat} (hk : ∀ k, kk = some k → g = wb τ s₁ + BitVec.ofNat 32 k) (hw0 : 0 < w' / 8)
    {v₁ v₂ : BitVec w'} {p : Bool}
    (hin₁ : InRegions s₁.wr ((g + BitVec.ofNat 32 ofs).setWidth 64) (w' / 8)) (hv : p = true → v₁ = v₂) :
    AgreeOk (storeT τ kk ofs (w' / 8) p)
      { s₁ with mem := s₁.mem.writeW ((g + BitVec.ofNat 32 ofs).setWidth 64) v₁ }
      { s₂ with mem := s₂.mem.writeW ((g + BitVec.ofNat 32 ofs).setWidth 64) v₂ } :=
  storeT_sound ha hk hw0 hin₁ fun h => by rw [hv h]

/-- The byte at `ofs` from `v`, which `loadPub` says agrees. -/
theorem load_byte {τ : T} {s₁ s₂ : State} (ha : AgreeOk τ s₁ s₂) {v : BitVec 32} {kk : Option Nat}
    {ofs : Nat} (hv : ∀ k, kk = some k → v = wb τ s₁ + BitVec.ofNat 32 k)
    (hp : loadPub τ kk ofs 1 = true) :
    s₁.mem ((v + BitVec.ofNat 32 ofs).setWidth 64) = s₂.mem ((v + BitVec.ofNat 32 ofs).setWidth 64) := by
  obtain ⟨k, rfl, hp', hle⟩ := loadPub_some hp
  have hW := ha.wbW
  rw [wp_addr (hv k rfl) (by omega_using [hle, hW])]
  have := load_bytes ha hp' 0 (by decide)
  rwa [show BitVec.ofNat 64 0 = 0 from rfl, show ∀ a : Addr, a + 0 = a from fun a => BitVec.add_zero a] at this

/-! ## Steps -/

theorem add_ofNat_toNat (a v : BitVec 32) (k : Nat) :
    a + BitVec.ofNat 32 k + v = a + BitVec.ofNat 32 (k + v.toNat) := by
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc]

theorem sub_ofNat_toNat (a v : BitVec 32) {k : Nat} (h : v.toNat ≤ k) :
    a + BitVec.ofNat 32 k - v = a + BitVec.ofNat 32 (k - v.toNat) := by
  have e : BitVec.ofNat 32 k = BitVec.ofNat 32 (k - v.toNat) + v := by
    calc BitVec.ofNat 32 k = BitVec.ofNat 32 (k - v.toNat) + BitVec.ofNat 32 v.toNat := by
          rw [← BitVec.ofNat_add, Nat.sub_add_cancel h]
      _ = BitVec.ofNat 32 (k - v.toNat) + v := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [e, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- What a source operand reads, if `srcPub` says it is public, from states
where its base register (if any) agrees. -/
theorem src_eq {τ : T} {s₁ s₂ : State} (ha : AgreeOk τ s₁ s₂) {src : Src} (hp : srcPub τ src = true)
    (hb : ∀ m, src = .mem m → s₁.gpr m.base = s₂.gpr m.base) {b₁ b₂ : BitVec 32}
    (h₁ : readSrc s₁ src = some b₁) (h₂ : readSrc s₂ src = some b₂) : b₁ = b₂ := by
  cases src with
  | reg r =>
    simp only [readSrc, Option.some.injEq] at h₁ h₂
    rw [← h₁, ← h₂]; exact ha.reg hp
  | imm v =>
    simp only [readSrc, Option.some.injEq] at h₁ h₂
    rw [← h₁, ← h₂]
  | mem m =>
    simp only [readSrc, State.load32] at h₁ h₂
    split at h₁ <;> [skip; cases h₁]
    split at h₂ <;> [skip; cases h₂]
    cases h₁; cases h₂
    rw [State.ea, State.ea, ← hb m rfl]
    simp only [Mem.readW]
    rw [load_read ha (fun k hk => (ha.wpOf hk).1) hp]

theorem setF_setR (τ : T) (d : Reg) (p q : Bool) (k : Option Nat) :
    setF (RTaint.setR τ d p k) q = RTaint.setR (setF τ q) d p k := rfl

/-- `arithFlags` are flags that agree, and are defined, if their inputs agree. -/
theorem flagsOk_arith {s₁ s₂ : State} {r₁ r₂ : BitVec 32} {c₁ c₂ o₁ o₂ : Bool} (hr : r₁ = r₂) (hc : c₁ = c₂)
    (ho : o₁ = o₂) : FlagsOk (arithFlags s₁ r₁ c₁ o₁) (arithFlags s₂ r₂ c₂ o₂) := by
  subst hr hc ho
  exact ⟨rfl, rfl, rfl, rfl, by simp [FlagsDefined, arithFlags, State.setFlags]⟩

/-- An ALU instruction, `d` not `esp`. -/
theorem alu_sound {τ : T} {op : AluOp} {d : Reg} {src : Src} {s₁ s₂ s₁' s₂' : State} (ha : AgreeOk τ s₁ s₂)
    (hd : d ≠ .esp) (hb : ∀ m, src = .mem m → s₁.gpr m.base = s₂.gpr m.base)
    (e₁ : execAlu op d src s₁ = some s₁') (e₂ : execAlu op d src s₂ = some s₂') :
    AgreeOk (aluT τ op d src) s₁' s₂' := by
  rw [Taint.execAlu_eq] at e₁ e₂
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
  obtain ⟨b₁, hb₁, ⟨r₁, c₁, o₁⟩, ho₁, rfl⟩ := e₁
  obtain ⟨b₂, hb₂, ⟨r₂, c₂, o₂⟩, ho₂, rfl⟩ := e₂
  unfold aluT
  split
  · -- `xor d, d` or `sub d, d`: zero.
    rename_i hz
    simp only [zeroIdiom] at hz
    cases src with
    | imm _ | mem _ => cases hz
    | reg r =>
      simp only [Bool.and_eq_true] at hz
      obtain ⟨hop, hr⟩ := hz
      obtain rfl := regEq_iff.mp hr
      simp only [readSrc, Option.some.injEq] at hb₁ hb₂
      subst hb₁ hb₂
      have hz : ∀ s : State, ∀ {out : BitVec 32 × Bool × Bool},
          Taint.aluOut op (s.gpr r) (s.gpr r) s.cf = some out → out = (0, false, false) := by
        intro s out h
        cases op <;> simp only [reduceCtorEq] at hop <;>
          simp only [Taint.aluOut, Option.some.injEq] at h <;> subst h
        · simp [subOverflow]
        · simp
      have z₁ := hz s₁ ho₁; have z₂ := hz s₂ ho₂
      simp only [Prod.mk.injEq] at z₁ z₂
      obtain ⟨rfl, rfl, rfl⟩ := z₁; obtain ⟨rfl, rfl, rfl⟩ := z₂
      have hw : Taint.writes op = true := by cases op <;> simp_all [Taint.writes]
      simp only [hw, ite_true]
      rw [setF_setR]
      exact (ha.setF (p := true) fun _ => flagsOk_arith rfl rfl rfl).setP hd fun _ => rfl
  · rename_i hnz
    -- The general case: the result and flags agree if the operands (and the carry, if read) do.
    have gen : ∀ {p : Bool}, (p = true → s₁.gpr d = s₂.gpr d ∧ b₁ = b₂ ∧ (Taint.usesCarry op = true → s₁.cf = s₂.cf)) →
        AgreeOk (if Taint.writes op then setF (RTaint.setR τ d p none) p else setF τ p)
          (if Taint.writes op then (arithFlags s₁ r₁ c₁ o₁).setReg d r₁ else arithFlags s₁ r₁ c₁ o₁)
          (if Taint.writes op then (arithFlags s₂ r₂ c₂ o₂).setReg d r₂ else arithFlags s₂ r₂ c₂ o₂) := by
      intro p hp
      have heq : p = true → r₁ = r₂ ∧ c₁ = c₂ ∧ o₁ = o₂ := fun h => by
        obtain ⟨h1, h2, h3⟩ := hp h
        have : Taint.aluOut op (s₁.gpr d) b₁ s₁.cf = Taint.aluOut op (s₂.gpr d) b₂ s₂.cf := by
          rw [h1, h2]
          cases hc : Taint.usesCarry op
          · exact Taint.aluOut_cf hc _ _ _ _
          · rw [h3 hc]
        rw [ho₁, ho₂, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at this
        exact this
      have hf := ha.setF (p := p) (c₁ := some c₁) (o₁ := some o₁) (z₁ := some (r₁ == 0)) (n₁ := some r₁.msb)
        (c₂ := some c₂) (o₂ := some o₂) (z₂ := some (r₂ == 0)) (n₂ := some r₂.msb) fun h => by
          obtain ⟨h1, h2, h3⟩ := heq h
          exact flagsOk_arith h1 h2 h3
      split
      · rw [setF_setR]
        exact hf.setP hd fun h => (heq h).1
      · exact hf
    have hcarry : ∀ {p : Bool}, (p = true → τ.fl = true ∨ Taint.usesCarry op = false) →
        p = true → Taint.usesCarry op = true → s₁.cf = s₂.cf := fun hp h hc => by
      rcases hp h with hf | hf
      · exact (ha.fl hf).1
      · rw [hc] at hf; cases hf
    split
    · -- `add d, imm`
      rename_i v
      simp only [readSrc, Option.some.injEq] at hb₁ hb₂
      subst hb₁ hb₂
      simp only [Taint.aluOut, Option.some.injEq] at ho₁ ho₂
      cases ho₁; cases ho₂
      simp only [Taint.writes, ite_true]
      rw [setF_setR]
      refine (ha.setF (p := pubR τ d) fun h => flagsOk_arith (by rw [ha.reg h]) (by rw [ha.reg h])
        (by rw [ha.reg h])).setR hd (fun h => by rw [ha.reg h]) fun k hk => ?_
      simp only [Option.map_eq_some_iff] at hk
      obtain ⟨k₀, hk₀, rfl⟩ := hk
      obtain ⟨h1, h2⟩ := ha.wpOf hk₀
      exact ⟨by show s₁.gpr d + v = wb τ s₁ + BitVec.ofNat 32 (k₀ + v.toNat); rw [h1, add_ofNat_toNat], by
        show s₂.gpr d + v = s₁.gpr d + v; rw [h2]⟩
    · -- `sub d, imm`
      rename_i v
      simp only [readSrc, Option.some.injEq] at hb₁ hb₂
      subst hb₁ hb₂
      simp only [Taint.aluOut, Option.some.injEq] at ho₁ ho₂
      cases ho₁; cases ho₂
      simp only [Taint.writes, ite_true]
      rw [setF_setR]
      refine (ha.setF (p := pubR τ d) fun h => flagsOk_arith (by rw [ha.reg h]) (by rw [ha.reg h])
        (by rw [ha.reg h])).setR hd (fun h => by rw [ha.reg h]) fun k hk => ?_
      simp only [Option.bind_eq_some_iff] at hk
      obtain ⟨k₀, hk₀, hr⟩ := hk
      simp only [offSub] at hr
      split at hr <;> [skip; cases hr]
      rename_i hle; cases hr
      obtain ⟨h1, h2⟩ := ha.wpOf hk₀
      exact ⟨by show s₁.gpr d - v = wb τ s₁ + BitVec.ofNat 32 (k₀ - v.toNat); rw [h1, sub_ofNat_toNat _ _ hle], by
        show s₂.gpr d - v = s₁.gpr d - v; rw [h2]⟩
    · exact gen fun h => by
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        exact ⟨ha.reg h1, src_eq ha h2 hb hb₁ hb₂, fun hc => by
          rcases h3 with h3 | h3
          · rw [hc] at h3; cases h3
          · exact (ha.fl h3).1⟩

/-- What an SSE instruction writes. -/
theorem xop_exec (op : XOp) (s : State) :
    ∃ v, op.exec s = s.setXmm (xdst op) v ∧ (xzero op = true → v = 0) := by
  cases op with
  | bin o d r =>
    refine ⟨_, rfl, fun h => ?_⟩
    cases o <;> simp only [xzero, Bool.false_eq_true] at h
    have : d = r := by revert h; cases d <;> cases r <;> decide
    subst this
    simp [XBinOp.eval]
  | _ => exact ⟨_, rfl, fun h => nomatch h⟩

theorem stepB_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : AgreeOk τ s₁ s₂)
    (hb : ∀ n, base i = some n → s₁.gpr n = s₂.gpr n) (hs : stepB τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') : AgreeOk τ' s₁' s₂' := by
  cases i with
  | symPush | push | pop | alloc | free | callr | mop | mmxStore | mmxEnter | emms | mcdtEnter | mcdtLeave =>
    simp only [stepB, reduceCtorEq] at hs
  | mov d src =>
    simp only [stepB] at hs
    split at hs <;> [cases hs; skip]
    rename_i hd
    have hd' := isSp_false (Bool.not_eq_true _ ▸ hd)
    simp only [reduceExec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, hy₁, rfl⟩ := e₁; obtain ⟨y₂, hy₂, rfl⟩ := e₂
    cases src with
    | reg r =>
      simp only [Option.some.injEq] at hs; subst hs
      simp only [readSrc, Option.some.injEq] at hy₁ hy₂; subst hy₁ hy₂
      exact ha.setR hd' (fun hp => ha.reg hp) (fun k hk => ha.wpOf hk)
    | imm v =>
      simp only [Option.some.injEq] at hs; subst hs
      exact ha.setP hd' fun hp => src_eq ha hp (fun _ h => nomatch h) hy₁ hy₂
    | mem m =>
      simp only [Option.some.injEq] at hs; subst hs
      exact ha.setP hd' fun hp => src_eq ha hp (fun m' h => by cases h; exact hb m.base rfl) hy₁ hy₂
  | store m r =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, State.store32] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hin₁
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    simp only [State.ea] at hin₁ ⊢
    rw [← hb m.base rfl]
    exact storeW_sound (w' := 32) ha (fun k hk => (ha.wpOf hk).1) (by decide) hin₁ fun hp => ha.reg hp
  | alu op d src =>
    simp only [stepB] at hs
    split at hs <;> [cases hs; skip]
    rename_i hd
    simp only [Option.some.injEq] at hs; subst hs
    simp only [reduceExec] at e₁ e₂
    exact alu_sound ha (isSp_false (Bool.not_eq_true _ ▸ hd))
      (fun m h => by subst h; exact hb m.base rfl) e₁ e₂
  | shift op d n =>
    simp only [stepB] at hs
    split at hs <;> [cases hs; skip]
    rename_i hd
    have hd' := isSp_false (Bool.not_eq_true _ ▸ hd)
    simp only [Option.some.injEq] at hs; subst hs
    simp only [reduceExec, execShift] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hn
    simp only [hn, and_self, ite_true] at e₂
    rw [setF_setR]
    cases op with
    | ror =>
      simp only [Option.some.injEq] at e₁ e₂; subst e₁ e₂
      refine (ha.setF fun h => ?_).setP hd' fun h => by rw [ha.reg h]
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨⟨hf, hp⟩, rfl⟩ := h
      obtain ⟨-, hz, hsn, -, -, hdz, hds, -⟩ := ha.fl hf
      refine ⟨by simp only [State.setFlags, ha.reg hp], by simp only [State.setFlags, hz],
        by simp only [State.setFlags, hsn], by simp only [State.setFlags, ha.reg hp, ite_true], ?_⟩
      refine ⟨by simp [State.setFlags], hdz, hds, by simp [State.setFlags]⟩
    | shr =>
      simp only [Option.some.injEq] at e₁ e₂; subst e₁ e₂
      refine (ha.setF fun h => ?_).setP hd' fun h => by rw [ha.reg h]
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨⟨-, hp⟩, rfl⟩ := h
      refine ⟨by simp only [State.setFlags, ha.reg hp], by simp only [State.setFlags, ha.reg hp],
        by simp only [State.setFlags, ha.reg hp], by simp only [State.setFlags, ha.reg hp, ite_true], ?_⟩
      exact ⟨by simp [State.setFlags], by simp [State.setFlags], by simp [State.setFlags], by simp [State.setFlags]⟩
  | bswap d =>
    simp only [stepB] at hs
    split at hs <;> [cases hs; skip]
    rename_i hd
    simp only [Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ha.setP (isSp_false (Bool.not_eq_true _ ▸ hd)) fun h => by rw [ha.reg h]
  | movzx8 d m =>
    simp only [stepB] at hs
    split at hs <;> [cases hs; skip]
    rename_i hd
    simp only [Option.some.injEq] at hs; subst hs
    simp only [reduceExec, State.load8, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, hy₁, rfl⟩ := e₁; obtain ⟨y₂, hy₂, rfl⟩ := e₂
    split at hy₁ <;> [skip; cases hy₁]
    split at hy₂ <;> [skip; cases hy₂]
    cases hy₁; cases hy₂
    simp only [State.ea]
    refine ha.setP (isSp_false (Bool.not_eq_true _ ▸ hd)) fun h => ?_
    rw [← hb m.base rfl, load_byte ha (fun k hk => (ha.wpOf hk).1) h]
  | store8 m r =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, State.store8] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hin₁
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    simp only [State.ea] at hin₁ ⊢
    rw [← hb m.base rfl]
    exact storeW_sound (w' := 8) ha (fun k hk => (ha.wpOf hk).1) (by decide) hin₁ fun hp => by rw [ha.reg hp]
  | mul r =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    simp only [execMul]
    rw [setF_setR, setF_setR]
    have hp : (pubR τ .eax && pubR τ r) = true → s₁.gpr .eax = s₂.gpr .eax ∧ s₁.gpr r = s₂.gpr r := fun h => by
      simp only [Bool.and_eq_true] at h; exact ⟨ha.reg h.1, ha.reg h.2⟩
    exact ((ha.setF (p := false) fun h => nomatch h).setP (d := .eax) (by decide) fun h => by
      rw [(hp h).1, (hp h).2]).setP (d := .edx) (by decide) fun h => by rw [(hp h).1, (hp h).2]
  | movdquLoad d m =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, -, rfl⟩ := e₁; obtain ⟨y₂, -, rfl⟩ := e₂
    exact ha.setX d fun h => nomatch h
  | movqLoad d m =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨y₁, -, rfl⟩ := e₁; obtain ⟨y₂, -, rfl⟩ := e₂
    exact ha.setX d fun h => nomatch h
  | pmuludq d r =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ha.setX d fun h => nomatch h
  | movdquStore m x =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, State.store128] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hin₁
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    simp only [State.ea] at hin₁ ⊢
    rw [← hb m.base rfl]
    exact storeW_sound (w' := 128) ha (fun k hk => (ha.wpOf hk).1) (by decide) hin₁ fun hp => ha.px x hp
  | movqStore m x =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, State.store64] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hin₁
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    simp only [State.ea] at hin₁ ⊢
    rw [← hb m.base rfl]
    exact storeW_sound (w' := 64) ha (fun k hk => (ha.wpOf hk).1) (by decide) hin₁ fun hp => by rw [ha.px x hp]
  | xop op =>
    simp only [stepB, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    obtain ⟨v₁, e₁, z₁⟩ := xop_exec op s₁
    obtain ⟨v₂, e₂, z₂⟩ := xop_exec op s₂
    rw [e₁, e₂]
    exact ha.setX _ fun h => by rw [z₁ h, z₂ h]

theorem setWidth64_inj {a b : BitVec 32} (h : a.setWidth 64 = b.setWidth 64) : a = b := by
  apply BitVec.eq_of_toNat_eq
  rw [← toNat_w64 a, ← toNat_w64 b, h]

theorem ea_base {m : MemOp} {s₁ s₂ : State} (h : s₁.ea m = s₂.ea m) : s₁.gpr m.base = s₂.gpr m.base :=
  (BitVec.add_left_inj _).mp (setWidth64_inj h)

theorem base_eq {i : Instr} {n : Reg} (h : base i = some n) (s₁ s₂ : State)
    (ha : addrs i s₁ = addrs i s₂) : s₁.gpr n = s₂.gpr n := by
  cases i with
  | mov _ src | alu _ _ src =>
    cases src <;> simp only [base, reduceCtorEq, Option.some.injEq] at h
    subst h
    simp only [addrs, srcAddrs, List.cons.injEq, and_true] at ha
    exact ea_base ha
  | store m _ | movzx8 _ m | store8 m _ | movdquLoad _ m | movdquStore m _ | movqLoad _ m | movqStore m _ =>
    simp only [base, Option.some.injEq] at h
    subst h
    simp only [addrs, List.cons.injEq, and_true] at ha
    exact ea_base ha
  | _ => simp only [base, reduceCtorEq] at h

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
    have hn' := base_eq hn s₁ s₂ hadr
    exact stepB_sound (h.withPub hn') (fun n' h' => by rw [hn] at h'; cases h'; exact hn') hs e₁ e₂
  · rename_i hn
    exact stepB_sound h (fun n' hn' => absurd hn' (by rw [hn]; simp)) hs e₁ e₂

/-! ## Knowing less -/

/-- What `σ` says, `τ` says if it knows no more. -/
theorem AgreeOk.weaken {τ σ : T} {s₁ s₂ : State} (h : AgreeOk σ s₁ s₂) (hsp : τ.sp = σ.sp)
    (hW : τ.W = σ.W) (han : τ.an = σ.an) (hstk : τ.stk = σ.stk) (hak : τ.ak = true → σ.ak = true)
    (hpub : ∀ r ∈ τ.pub, r ∈ σ.pub) (hfl : τ.fl = true → σ.fl = true)
    (hpx : ∀ x, pubX τ x = true → pubX σ x = true)
    (hwp : ∀ e ∈ τ.wp, e ∈ σ.wp ∨ (e.1 ≠ .esp ∧ RTaint.wpOf σ e.1 = some e.2))
    (hsec : ∀ k, σ.sec.testBit k = true → τ.sec.testBit k = true) : AgreeOk τ s₁ s₂ := by
  obtain ⟨hsp', hspN, hwbW, hpub', hfl', hpx', hwp', hrd, hwr, hunk, hmm, hmmx, hmx, hmc, harg, F, B, hw,
    hf, hout, hmem⟩ := h
  have ewb : wb τ s₁ = wb σ s₁ := by simp only [wb, hsp]
  have ewbA : wbA τ s₁ = wbA σ s₁ := by simp only [wbA, ewb]
  have ein : ∀ x, InWin τ s₁ x ↔ InWin σ s₁ x := by intro x; simp only [InWin, off, ewbA, hW]
  refine ⟨hsp', by rw [hsp]; exact hspN, by rw [ewb, hW, han]; exact hwbW, fun r hr => hpub' r (hpub r hr),
    fun h => hfl' (hfl h), fun x hx => hpx' x (hpx x hx), fun e he => ?_, hrd, hwr, hunk, hmm, hmmx, hmx, hmc,
    fun hk j hj => ?_, F, B, hw, by rw [ewbA, hW, hsp, hstk]; exact hf,
    fun g hg x hx => (not_congr (ein x)).mpr (hout g hg x hx), fun x hx hs => ?_⟩
  · rw [ewb]
    rcases hwp e he with he' | ⟨hne, he'⟩
    · exact hwp' e he'
    · exact ⟨hne, AgreeOk.wpOf ⟨hsp', hspN, hwbW, hpub', hfl', hpx', hwp', hrd, hwr, hunk, hmm, hmmx, hmx, hmc,
        harg, F, B, hw, hf, hout, hmem⟩ he'⟩
  · rw [ewbA, hW]; rw [han] at hj; exact harg (hak hk) j hj
  · refine hmem x hx fun hw' => ?_
    have h1 := hs ((ein x).mpr hw')
    have e : off τ s₁ x = off σ s₁ x := by simp only [off, ewbA]
    rw [e] at h1
    cases hk : σ.sec.testBit (off σ s₁ x)
    · rfl
    · rw [hsec _ hk] at h1; cases h1

theorem pubX_land {a b : T} {x : XReg} (h : Nat.testBit (Nat.land a.px b.px) (xidx x) = true) :
    pubX a x = true ∧ pubX b x = true := by
  change (a.px &&& b.px).testBit (xidx x) = true at h
  rw [Nat.testBit_and, Bool.and_eq_true] at h
  exact h

theorem meet_left {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₁ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ := by
  unfold meet
  split
  · rename_i hc
    intro _
    simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
    have ha := h h1
    refine ha.weaken rfl rfl rfl rfl (fun hk => by simp only [Bool.and_eq_true] at hk; exact hk.1)
      (fun r hr => (RegSet.mem_inter.mp hr).1)
      (fun hf => by simp only [Bool.and_eq_true] at hf; exact hf.1) (fun x hx => (pubX_land hx).1)
      (fun e he => .inl (List.mem_filter.mp he).1) (fun k hk => ?_)
    · show (τ₁.sec ||| τ₂.sec).testBit k = true
      rw [Nat.testBit_or, hk, Bool.true_or]
  · intro hok; simp only [bot] at hok; cases hok

theorem meet_right {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₂ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ := by
  unfold meet
  split
  · rename_i hc
    intro _
    simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨-, h2⟩, hW⟩, han⟩, hsp⟩, hstk⟩ := hc
    have ha := h h2
    refine ha.weaken hsp hW han hstk (fun hk => by simp only [Bool.and_eq_true] at hk; exact hk.2)
      (fun r hr => (RegSet.mem_inter.mp hr).2)
      (fun hf => by simp only [Bool.and_eq_true] at hf; exact hf.2) (fun x hx => (pubX_land hx).2)
      (fun e he => ?_) (fun k hk => ?_)
    · obtain ⟨-, hm⟩ := List.mem_filter.mp he
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
      exact .inr ⟨isSp_false hm.1, hm.2⟩
    · show (τ₁.sec ||| τ₂.sec).testBit k = true
      rw [Nat.testBit_or, hk, Bool.or_true]
  · intro hok; simp only [bot] at hok; cases hok

theorem le_sound {τ σ : T} {s₁ s₂ : State} (hle : le τ σ = true) (h : Agree σ s₁ s₂) : Agree τ s₁ s₂ := by
  intro hok
  simp only [le, hok, Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.beq_eq, beq_iff_eq,
    List.all_eq_true] at hle
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hσ, hW⟩, han⟩, hsp⟩, hstk⟩, hak⟩, hpub⟩, hfl⟩, hpx⟩, hwp⟩, hsec⟩ := hle
  refine (h hσ).weaken hsp hW han hstk
    (fun hk => by simp only [hk, Bool.not_true, Bool.false_or] at hak; exact hak)
    (fun r hr => RegSet.mem_of_subset hpub hr)
    (fun hf => by simp only [hf, Bool.not_true, Bool.false_or] at hfl; exact hfl)
    (fun x hx => bsub_bit hpx hx) (fun e he => ?_) (fun k hk => bsub_bit hsec hk)
  have := hwp e he
  exact .inr ⟨isSp_false (by simpa using this.1), this.2⟩

/-! ## The stack -/

theorem sub_toNat' {sp : BitVec 32} {k : Nat} (h : k ≤ sp.toNat) :
    (sp - BitVec.ofNat 32 k).toNat = sp.toNat - k := by
  have := sp.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_using [h])]
  rw [show 2 ^ 32 - k + sp.toNat = (sp.toNat - k) + 2 ^ 32 by omega_using [h], Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega_using [])]

theorem sub_setWidth' {e : BitVec 32} {m : Nat} (h : m ≤ e.toNat) :
    (e - BitVec.ofNat 32 m).setWidth 64 = e.setWidth 64 - BitVec.ofNat 64 m := by
  apply BitVec.eq_of_toNat_eq
  have := e.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := m) (by omega_using [h]), Nat.mod_eq_of_lt (a := m) (by omega_using [h]),
    Nat.mod_eq_of_lt (a := e.toNat) (by omega_using [])]
  omega_using [h]

/-- `esp` is `sp` bytes above the window's base, without wrapping. -/
theorem AgreeOk.esp_toNat {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) :
    (s₁.gpr .esp).toNat = (wb τ s₁).toNat + τ.sp := by
  simp only [wb]; rw [sub_toNat' h.spNat]; have := h.spNat; omega_using [this]

/-- The `b` bytes below `esp`. -/
def belowR (e : BitVec 32) (b : Nat) : Region := ⟨(e - BitVec.ofNat 32 b).setWidth 64, b⟩

/-- The bytes of the `b` bytes below `esp` are those from offset `τ.sp - b`
to `τ.sp` of the window. -/
theorem below_iff {τ : T} {s : State} (hW : (wb τ s).toNat + τ.W + 4 + τ.an ≤ 2 ^ 32)
    (hspN : τ.sp ≤ (s.gpr .esp).toNat) (hle : τ.sp ≤ τ.W) {b : Nat} (hb : b ≤ τ.sp) (x : Addr) :
    (belowR (s.gpr .esp) b).Contains x 1 ↔ τ.sp - b ≤ off τ s x ∧ off τ s x < τ.sp := by
  have he : (s.gpr .esp - BitVec.ofNat 32 b).setWidth 64 = wbA τ s + BitVec.ofNat 64 (τ.sp - b) := by
    rw [← addr_wb τ s (by omega_using [hW, hle, hb])]
    congr 1
    rw [sp_eq (τ := τ) (s := s), ← BitVec.ofNat_sub_ofNat_of_le (w := 32) _ _
      (by have := (s.gpr .esp).isLt; omega_using [this, hb, hspN]) hb]
    bv_omega
  simp only [belowR, Region.Contains, he]
  rw [Nat.add_one_le_iff, Offset.lt_iff x (wbA τ s) (by omega_using [hW, hle, hb])]
  unfold off
  omega_using [hb]

/-- The base of the `b` bytes below `esp`, from the window's. -/
theorem below_base {τ : T} {s : State} (hW : (wb τ s).toNat + τ.W + 4 + τ.an ≤ 2 ^ 32)
    (hspN : τ.sp ≤ (s.gpr .esp).toNat) (hle : τ.sp ≤ τ.W) {b : Nat} (hb : b ≤ τ.sp) :
    (s.gpr .esp - BitVec.ofNat 32 b).setWidth 64 = wbA τ s + BitVec.ofNat 64 (τ.sp - b) := by
  rw [← addr_wb τ s (by omega_using [hW, hle, hb])]
  congr 1
  rw [sp_eq (τ := τ) (s := s), ← BitVec.ofNat_sub_ofNat_of_le (w := 32) _ _
    (by have := (s.gpr .esp).isLt; omega_using [this, hb, hspN]) hb]
  bv_omega

/-- The window's base after `esp` and the analysis's offset moved down by `b`. -/
theorem wb_down {τ τ' : T} {s s' : State} {b : Nat} (hb : b ≤ τ.sp) (hspN : τ.sp ≤ (s.gpr .esp).toNat)
    (hsp' : τ'.sp = τ.sp - b) (he : s'.gpr .esp = s.gpr .esp - BitVec.ofNat 32 b) : wb τ' s' = wb τ s := by
  simp only [wb, hsp', he]
  rw [← BitVec.ofNat_sub_ofNat_of_le (w := 32) _ _
    (by have := (s.gpr .esp).isLt; omega_using [this, hspN, hb]) hb]
  bv_omega

/-- The window's base after `esp` and the analysis's offset moved up by `b`. -/
theorem wb_up {τ τ' : T} {s s' : State} {b : Nat} (hsp' : τ'.sp = τ.sp + b)
    (he : s'.gpr .esp = s.gpr .esp + BitVec.ofNat 32 b) : wb τ' s' = wb τ s := by
  simp only [wb, hsp', he, BitVec.ofNat_add]; bv_omega

/-- What the frames' tiling says of an item opened below the others. -/
theorem Frames.open {w : Addr} {W o n : Nat} {st : List Nat} {F : List Region} (hf : Frames w W o st F)
    (hb : size n ≤ o) : Frames w W (o - size n) (n :: st)
      ((if n = 0 then [] else [⟨w + BitVec.ofNat 64 (o - size n), n⟩]) ++ F) := by
  simp only [Frames]
  split
  · rename_i hn
    simp only [hn, List.nil_append]
    simp only [hn, size, ite_true] at hb
    rw [show o - size 0 + 4 = o by simp only [size, ite_true]; omega_using [hb]]
    exact hf
  · rename_i hn
    simp only [List.singleton_append]
    exact ⟨F, rfl, by rw [show o - size n + size n = o by omega_using [hb]]; exact hf⟩

/-- An item of `size n` bytes opened below the others, the frame of its
region (if `n` is not a return address) at the head of the writable
regions, with memory changed only in those bytes, where the bytes `τ'.sec`
says are public agree, `τ'.sec` making secret every other byte of the
window `τ.sec` does. What the new states say of the registers, the flags
and the rest is the caller's. -/
theorem open_ok {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (h : AgreeOk τ s₁ s₂) {n : Nat} (hb : size n ≤ τ.sp)
    (hsp' : τ'.sp = τ.sp - size n) (hW' : τ'.W = τ.W) (han : τ'.an = τ.an) (hak : τ'.ak = τ.ak)
    (hstk : τ'.stk = n :: τ.stk)
    (he₁ : s₁'.gpr .esp = s₁.gpr .esp - BitVec.ofNat 32 (size n))
    (he₂ : s₂'.gpr .esp = s₂.gpr .esp - BitVec.ofNat 32 (size n))
    (hwr₁ : s₁'.wr = (if n = 0 then [] else [⟨(s₁.gpr .esp - BitVec.ofNat 32 (size n)).setWidth 64, n⟩]) ++ s₁.wr)
    (hwr₂ : s₂'.wr = (if n = 0 then [] else [⟨(s₂.gpr .esp - BitVec.ofNat 32 (size n)).setWidth 64, n⟩]) ++ s₂.wr)
    (hrd₁ : s₁'.rd = s₁.rd) (hrd₂ : s₂'.rd = s₂.rd)
    (hf₁ : ∀ x, ¬ (belowR (s₁.gpr .esp) (size n)).Contains x 1 → s₁'.mem x = s₁.mem x)
    (hf₂ : ∀ x, ¬ (belowR (s₁.gpr .esp) (size n)).Contains x 1 → s₂'.mem x = s₂.mem x)
    (hin : ∀ x, (belowR (s₁.gpr .esp) (size n)).Contains x 1 → τ'.sec.testBit (off τ s₁ x) = false →
      s₁'.mem x = s₂'.mem x)
    (hout : ∀ x, ¬ (belowR (s₁.gpr .esp) (size n)).Contains x 1 → InWin τ s₁ x →
      τ'.sec.testBit (off τ s₁ x) = false → τ.sec.testBit (off τ s₁ x) = false)
    (hpub : ∀ r ∈ τ'.pub, s₁'.gpr r = s₂'.gpr r) (hfl : τ'.fl = true → FlagsOk s₁' s₂')
    (hpx : ∀ x, pubX τ' x = true → s₁'.xmm x = s₂'.xmm x)
    (hwp : ∀ e ∈ τ'.wp, e.1 ≠ .esp ∧ s₁'.gpr e.1 = wb τ s₁ + BitVec.ofNat 32 e.2 ∧ s₂'.gpr e.1 = s₁'.gpr e.1)
    (hunk : s₁'.unknowns = s₂'.unknowns) (hmm : s₁'.mm = s₂'.mm) (hmmx : s₁'.mmx = s₂'.mmx)
    (hmx : s₁'.mxcsr = s₂'.mxcsr) (hmc : s₁'.mcdt = s₂'.mcdt) : AgreeOk τ' s₁' s₂' := by
  obtain ⟨hsp, hspN, hwbW, -, -, -, -, hrd, hwr, -, -, -, -, -, harg, F, B, hw, hf, hout', hmem⟩ := h
  have hle : τ.sp ≤ τ.W := Frames.le hf
  have ewb : wb τ' s₁' = wb τ s₁ := wb_down hb hspN hsp' he₁
  have ewbA : wbA τ' s₁' = wbA τ s₁ := by simp only [wbA, ewb]
  have eoff : ∀ x, off τ' s₁' x = off τ s₁ x := fun x => by simp only [off, ewbA]
  have ein : ∀ x, InWin τ' s₁' x ↔ InWin τ s₁ x := fun x => by simp only [InWin, eoff, hW']
  have hbi := below_iff hwbW hspN hle hb
  refine ⟨by rw [he₁, he₂, hsp], ?_, by rw [ewb, hW', han]; exact hwbW, hpub, hfl, hpx,
    fun e he => by rw [ewb]; exact hwp e he, by rw [hrd₁, hrd₂, hrd], by rw [hwr₁, hwr₂, hwr, hsp], hunk,
    hmm, hmmx, hmx, hmc, fun hk j hj => ?_,
    (if n = 0 then [] else [⟨(s₁.gpr .esp - BitVec.ofNat 32 (size n)).setWidth 64, n⟩]) ++ F, B,
    by rw [hwr₁, hw, List.append_assoc], ?_, ?_, ?_⟩
  · rw [hsp', he₁, sub_toNat' (by omega_using [hb, hspN])]
    omega_using [hspN]
  · rw [han] at hj; rw [hak] at hk
    rw [ewbA, hW']
    have hnb : ¬ (belowR (s₁.gpr .esp) (size n)).Contains (wbA τ s₁ + BitVec.ofNat 64 (τ.W + 4 + j)) 1 := by
      rw [hbi, off_base τ s₁ (by omega_using [hwbW, hj])]; omega_using [hle]
    rw [hf₁ _ hnb, hf₂ _ hnb]
    exact harg hk j hj
  · rw [ewbA, hW', hsp', hstk, below_base hwbW hspN hle hb]
    exact Frames.open hf hb
  · intro g hg x hx
    rw [hrd₁] at hg
    exact (not_congr (ein x)).mpr (hout' g hg x hx)
  · intro x hx hs
    rw [hrd₁] at hx
    have hs' : InWin τ s₁ x → τ'.sec.testBit (off τ s₁ x) = false := fun hw' => by
      have := hs ((ein x).mpr hw'); rwa [eoff] at this
    by_cases hc : (belowR (s₁.gpr .esp) (size n)).Contains x 1
    · refine hin x hc (hs' ?_)
      unfold InWin; have := (hbi x).mp hc; omega_using [this, hle]
    · rw [hf₁ x hc, hf₂ x hc]
      exact hmem x hx fun hw' => hout x hc hw' (hs' hw')

/-- The `b` bytes below `w + o`, as offsets from `w`. -/
theorem below_off {w : BitVec 32} {o b : Nat} (hb : b ≤ o) (ho : w.toNat + o < 2 ^ 32) (x : Addr) :
    (belowR (w + BitVec.ofNat 32 o) b).Contains x 1 ↔
      o - b ≤ (x - w.setWidth 64).toNat ∧ (x - w.setWidth 64).toNat < o := by
  have he : (w + BitVec.ofNat 32 o - BitVec.ofNat 32 b).setWidth 64 = w.setWidth 64 + BitVec.ofNat 64 (o - b) := by
    rw [show w + BitVec.ofNat 32 o - BitVec.ofNat 32 b = w + (BitVec.ofNat 32 o - BitVec.ofNat 32 b) by
      rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc], Offset.ofNat_sub_ofNat hb,
      addr_add (by omega_using [ho, hb])]
  simp only [belowR, Region.Contains, he]
  rw [Nat.add_one_le_iff, Offset.lt_iff x _ (by omega_using [ho, hb])]
  omega_using [hb]

/-- A byte of the window that the analysis says is public agrees. -/
theorem AgreeOk.win_eq {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {x : Addr} (hx : InWin τ s₁ x)
    (hs : τ.sec.testBit (off τ s₁ x) = false) : s₁.mem x = s₂.mem x := by
  obtain ⟨F, B, -, -, hout, hmem⟩ := h.regions
  exact hmem x (fun g hg hc => hout g hg x hc hx) fun _ => hs

/-- The innermost item of the stack, `n`, released: `esp` and the analysis's
offset up by its size, its frame (if any) removed from the head of the
writable regions, the memory changed only as `lose` does, which keeps every
byte the two runs agree on. What the new states say of the registers and the
rest is the caller's. -/
theorem close_ok {τ τ' : T} {b₁ b₂ c₁ c₂ : State} (h : AgreeOk τ b₁ b₂) {n : Nat} {st : List Nat}
    (hstk0 : τ.stk = n :: st) (hle : τ.sp + size n ≤ τ.W)
    (hsp' : τ'.sp = τ.sp + size n) (hW' : τ'.W = τ.W) (han : τ'.an = τ.an) (hak : τ'.ak = τ.ak)
    (hstk : τ'.stk = st) (hsec : τ'.sec = τ.sec)
    (he₁ : c₁.gpr .esp = b₁.gpr .esp + BitVec.ofNat 32 (size n))
    (he₂ : c₂.gpr .esp = b₂.gpr .esp + BitVec.ofNat 32 (size n))
    (hwr₁ : c₁.wr = if n = 0 then b₁.wr else b₁.wr.tail) (hwr₂ : c₂.wr = if n = 0 then b₂.wr else b₂.wr.tail)
    (hrd₁ : c₁.rd = b₁.rd) (hrd₂ : c₂.rd = b₂.rd)
    (hmem : ∀ x, b₁.mem x = b₂.mem x → c₁.mem x = c₂.mem x)
    (hpub : ∀ r ∈ τ'.pub, c₁.gpr r = c₂.gpr r) (hfl : τ'.fl = true → FlagsOk c₁ c₂)
    (hpx : ∀ x, pubX τ' x = true → c₁.xmm x = c₂.xmm x)
    (hwp : ∀ e ∈ τ'.wp, e.1 ≠ .esp ∧ c₁.gpr e.1 = wb τ b₁ + BitVec.ofNat 32 e.2 ∧ c₂.gpr e.1 = c₁.gpr e.1)
    (hunk : c₁.unknowns = c₂.unknowns) (hmm : c₁.mm = c₂.mm) (hmmx : c₁.mmx = c₂.mmx)
    (hmx : c₁.mxcsr = c₂.mxcsr) (hmc : c₁.mcdt = c₂.mcdt) : AgreeOk τ' c₁ c₂ := by
  have htn := h.esp_toNat
  obtain ⟨hsp, hspN, hwbW, -, -, -, -, hrd, hwr, -, -, -, -, -, harg, F, B, hw, hf, hout, hmem'⟩ := h
  have ewb : wb τ' c₁ = wb τ b₁ := wb_up hsp' he₁
  have ewbA : wbA τ' c₁ = wbA τ b₁ := by simp only [wbA, ewb]
  have eoff : ∀ x, off τ' c₁ x = off τ b₁ x := fun x => by simp only [off, ewbA]
  have ein : ∀ x, InWin τ' c₁ x ↔ InWin τ b₁ x := fun x => by simp only [InWin, eoff, hW']
  rw [hstk0] at hf
  simp only [Frames] at hf
  have hreg : ∃ F', c₁.wr = F' ++ B ∧ Frames (wbA τ b₁) τ.W (τ.sp + size n) st F' := by
    split at hf
    · rename_i hn
      subst hn
      exact ⟨F, by simp only [hwr₁, ↓reduceIte, hw], by simpa only [size, ite_true] using hf⟩
    · rename_i hn
      obtain ⟨F', rfl, hf'⟩ := hf
      exact ⟨F', by simp only [hwr₁, hn, ↓reduceIte, hw]; rfl, hf'⟩
  obtain ⟨F', hw', hf'⟩ := hreg
  refine ⟨by rw [he₁, he₂, hsp], ?_, by rw [ewb, hW', han]; exact hwbW, hpub, hfl, hpx,
    fun e he => by rw [ewb]; exact hwp e he, by rw [hrd₁, hrd₂, hrd], by rw [hwr₁, hwr₂, hwr], hunk,
    hmm, hmmx, hmx, hmc, fun hk j hj => ?_, F', B, hw', by rw [ewbA, hW', hsp', hstk]; exact hf', ?_, ?_⟩
  · rw [hsp', he₁, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := size n) (by omega_using [hle, hwbW]),
      Nat.mod_eq_of_lt (by omega_using [htn, hle, hwbW])]
    omega_using [hspN]
  · rw [han] at hj; rw [hak] at hk
    rw [ewbA, hW']
    exact hmem _ (harg hk j hj)
  · intro g hg x hx
    rw [hrd₁] at hg
    exact (not_congr (ein x)).mpr (hout g hg x hx)
  · intro x hx hs
    rw [hrd₁] at hx
    refine hmem x (hmem' x hx fun hw' => ?_)
    have := hs ((ein x).mpr hw'); rwa [eoff, hsec] at this

/-- `lose` keeps every byte two memories agree on. -/
theorem lose_congr {m₁ m₂ : Mem} {a : Addr} {n : Nat} {u : Nat → BitVec 32} {x : Addr} (h : m₁ x = m₂ x) :
    lose m₁ a n u x = lose m₂ a n u x := by
  simp only [lose]; split <;> [split <;> [exact h; rfl]; exact h]

theorem size_frame {n : Nat} (h0 : 0 < n) (h4 : n % 4 = 0) : size n = n := by
  unfold size; split <;> [omega; split <;> omega]

/-- The registers of a state whose only register changed is `esp`, down or up
the same in both runs. -/
theorem pub_esp {τ : T} {s₁ s₂ s₁' s₂' : State} (h : AgreeOk τ s₁ s₂)
    (he : s₁'.gpr .esp = s₂'.gpr .esp) (h₁ : ∀ r, r ≠ .esp → s₁'.gpr r = s₁.gpr r)
    (h₂ : ∀ r, r ≠ .esp → s₂'.gpr r = s₂.gpr r) : ∀ r ∈ τ.pub, s₁'.gpr r = s₂'.gpr r := by
  intro r hr
  by_cases hre : r = .esp
  · subst hre; exact he
  · rw [h₁ r hre, h₂ r hre]; exact h.pub r hr

theorem wp_esp {τ : T} {s₁ s₂ s₁' s₂' : State} (h : AgreeOk τ s₁ s₂)
    (h₁ : ∀ r, r ≠ .esp → s₁'.gpr r = s₁.gpr r) (h₂ : ∀ r, r ≠ .esp → s₂'.gpr r = s₂.gpr r) :
    ∀ e ∈ τ.wp, e.1 ≠ .esp ∧ s₁'.gpr e.1 = wb τ s₁ + BitVec.ofNat 32 e.2 ∧ s₂'.gpr e.1 = s₁'.gpr e.1 := by
  intro e he
  obtain ⟨hne, e1, e2⟩ := h.wp e he
  exact ⟨hne, by rw [h₁ _ hne, e1], by rw [h₁ _ hne, h₂ _ hne, e2]⟩

/-! ### Pushes -/

theorem pushRegs_xmm (s : State) (rs : List Reg) : (pushRegs s rs).xmm = s.xmm := by
  induction rs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem pushRegs_keepR (s : State) (rs : List Reg) :
    (pushRegs s rs).unknowns = s.unknowns ∧ (pushRegs s rs).mm = s.mm ∧ (pushRegs s rs).mmx = s.mmx ∧
      (pushRegs s rs).mxcsr = s.mxcsr ∧ (pushRegs s rs).mcdt = s.mcdt := by
  induction rs generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons x xs ih => exact ih _

/-- Two pushes of registers that agree, at the same `esp`, leave memories
that agree on the bytes they store, and on every byte the memories did. -/
theorem pushRegs_agree (rs : List Reg) (hrs : .esp ∉ rs) : ∀ (s₁ s₂ : State), s₁.gpr .esp = s₂.gpr .esp →
    (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) → 4 * rs.length ≤ (s₁.gpr .esp).toNat → ∀ x,
      ((belowR (s₁.gpr .esp) (4 * rs.length)).Contains x 1 ∨ s₁.mem x = s₂.mem x) →
      (pushRegs s₁ rs).mem x = (pushRegs s₂ rs).mem x := by
  induction rs with
  | nil =>
    intro s₁ s₂ _ _ _ x hx
    rcases hx with hx | hx
    · simp only [belowR, Region.Contains, List.length_nil, Nat.mul_zero] at hx; omega_using [hx]
    · exact hx
  | cons r rs ih =>
    intro s₁ s₂ he hr hn x hx
    simp only [List.mem_cons, not_or] at hrs
    simp only [List.length_cons] at hn hx
    let t₁ : State := { s₁.setReg .esp (s₁.gpr .esp - 4) with
      mem := s₁.mem.writeW ((s₁.gpr .esp - 4).setWidth 64) (s₁.gpr r) }
    let t₂ : State := { s₂.setReg .esp (s₂.gpr .esp - 4) with
      mem := s₂.mem.writeW ((s₂.gpr .esp - 4).setWidth 64) (s₂.gpr r) }
    have ht₁ : t₁.gpr .esp = s₁.gpr .esp - 4 := by simp [t₁, State.setReg]
    have ht₂ : t₂.gpr .esp = s₂.gpr .esp - 4 := by simp [t₂, State.setReg]
    have hg₁ : ∀ q, q ≠ .esp → t₁.gpr q = s₁.gpr q := fun q h => by simp [t₁, State.setReg, h]
    have hg₂ : ∀ q, q ≠ .esp → t₂.gpr q = s₂.gpr q := fun q h => by simp [t₂, State.setReg, h]
    have hE := (s₁.gpr .esp).isLt
    -- Offsets from the base of the frame.
    generalize hw : s₁.gpr .esp - BitVec.ofNat 32 (4 * (rs.length + 1)) = w at *
    have hesp : s₁.gpr .esp = w + BitVec.ofNat 32 (4 * (rs.length + 1)) := by rw [← hw]; bv_omega
    have hwt : w.toNat + 4 * (rs.length + 1) = (s₁.gpr .esp).toNat := by
      rw [← hw, sub_toNat' hn]; omega_using [hn]
    have ht : t₁.gpr .esp = w + BitVec.ofNat 32 (4 * rs.length) := by
      rw [ht₁, hesp]; rw [show 4 * (rs.length + 1) = 4 * rs.length + 4 by omega_using []]
      rw [BitVec.ofNat_add]; bv_omega
    have hword : ∀ y, (y - (s₁.gpr .esp - 4).setWidth 64).toNat < 4 ↔
        4 * rs.length ≤ (y - w.setWidth 64).toNat ∧ (y - w.setWidth 64).toNat < 4 * rs.length + 4 := by
      intro y
      have := below_off (w := w) (o := 4 * (rs.length + 1)) (b := 4) (by omega_using []) (by omega_using [hwt, hE]) y
      simp only [belowR, Region.Contains, ← hesp] at this
      rw [show (s₁.gpr .esp - BitVec.ofNat 32 4) = s₁.gpr .esp - 4 from rfl] at this
      omega_using [this]
    have hbig := below_off (w := w) (o := 4 * (rs.length + 1)) (b := 4 * (rs.length + 1)) (by omega_using [])
      (by omega_using [hwt, hE])
    rw [← hesp] at hbig
    have hsmall := below_off (w := w) (o := 4 * rs.length) (b := 4 * rs.length) (by omega_using [])
      (by omega_using [hwt, hE])
    rw [← ht] at hsmall
    have ihr := ih hrs.2 t₁ t₂ (by rw [ht₁, ht₂, he]) (fun q hq => by
        rw [hg₁ q (fun h => hrs.2 (h ▸ hq)), hg₂ q (fun h => hrs.2 (h ▸ hq))]
        exact hr q (List.mem_cons_of_mem _ hq))
      (by rw [ht]; rw [Offset.toNat_add_ofNat]; omega_using [hwt, hE]) x
    refine ihr ?_
    by_cases hin : (x - (s₁.gpr .esp - 4).setWidth 64).toNat < 4
    · right
      show s₁.mem.writeW _ (s₁.gpr r) x = s₂.mem.writeW _ (s₂.gpr r) x
      simp only [Mem.writeW, Mem.write, ← he, hin, ite_true, hr r List.mem_cons_self]
    · rcases hx with hx | hx
      · left
        rw [hsmall]
        rw [hbig] at hx
        rw [hword] at hin
        omega_using [hx, hin]
      · right
        show s₁.mem.writeW _ (s₁.gpr r) x = s₂.mem.writeW _ (s₂.gpr r) x
        simp only [Mem.writeW, Mem.write, ← he, hin, ite_false]
        exact hx

theorem AgreeOk.sp_le {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) : τ.sp ≤ τ.W := by
  obtain ⟨F, B, -, hf, -⟩ := h.regions; exact Frames.le hf

/-- A byte of the `b` bytes below `esp` is in the window. -/
theorem AgreeOk.below_win {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {b : Nat} (hb : b ≤ τ.sp) {x : Addr}
    (hx : (belowR (s₁.gpr .esp) b).Contains x 1) :
    InWin τ s₁ x ∧ τ.sp - b ≤ off τ s₁ x ∧ off τ s₁ x < τ.sp := by
  have := (below_iff h.wbW h.spNat h.sp_le hb x).mp hx
  exact ⟨by unfold InWin; have := h.sp_le; omega_using [this, ‹τ.sp - b ≤ off τ s₁ x ∧ off τ s₁ x < τ.sp›], this⟩

/-- The `m` bytes at `esp - k`, as offsets of the window. -/
theorem AgreeOk.word_iff {τ : T} {s₁ s₂ : State} (h : AgreeOk τ s₁ s₂) {k m : Nat} (hk : k ≤ τ.sp)
    (hm : m ≤ k) (x : Addr) :
    (x - (s₁.gpr .esp - BitVec.ofNat 32 k).setWidth 64).toNat < m ↔
      τ.sp - k ≤ off τ s₁ x ∧ off τ s₁ x < τ.sp - k + m := by
  have hW := h.wbW
  have hle := h.sp_le
  rw [below_base hW h.spNat hle hk, in_range τ s₁ x (by omega_using [hW, hle, hk, hm])]

/-- What a `bclr` of the `w` bytes at `d` leaves of a byte outside them. -/
theorem bclr_out {sec d w k : Nat} (hk : ¬ (d ≤ k ∧ k < d + w)) (h : (bclr sec d w).testBit k = false) :
    sec.testBit k = false := by
  rw [testBit_bclr] at h
  simp only [Bool.and_eq_false_iff, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact h
  · exact absurd h hk

theorem bset_out {sec d w k : Nat} (h : (bset sec d w).testBit k = false) : sec.testBit k = false := by
  rw [testBit_bset, Bool.or_eq_false_iff] at h; exact h.1

theorem bset_in {sec d w k : Nat} (hk : d ≤ k ∧ k < d + w) : (bset sec d w).testBit k = true := by
  rw [testBit_bset]; simp [hk.1, hk.2]

theorem alloc_sound {τ τ' : T} {b : Nat} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : push τ (.alloc b) = some τ') (e₁ : isa.push (.alloc b) s₁ = some s₁')
    (e₂ : isa.push (.alloc b) s₂ = some s₂') : Agree τ' s₁' s₂' := by
  intro _
  simp only [push] at hs
  split at hs <;> [skip; cases hs]
  rename_i hc
  cases hs
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.blt_eq] at hc
  obtain ⟨⟨⟨hok, hb⟩, h4⟩, h0⟩ := hc
  simp only [isa, X86.push] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  have h := ha hok
  have hsz := size_frame h0 h4
  have hb' : size b ≤ τ.sp := by rw [hsz]; exact hb
  have he : ∀ s : State, ({ s.setReg .esp (s.gpr .esp - BitVec.ofNat 32 b) with
      wr := ⟨(s.gpr .esp - BitVec.ofNat 32 b).setWidth 64, b⟩ :: s.wr } : State).gpr .esp =
      s.gpr .esp - BitVec.ofNat 32 (size b) := fun s => by rw [hsz]; simp [State.setReg]
  have hg : ∀ s : State, ∀ r, r ≠ .esp → ({ s.setReg .esp (s.gpr .esp - BitVec.ofNat 32 b) with
      wr := ⟨(s.gpr .esp - BitVec.ofNat 32 b).setWidth 64, b⟩ :: s.wr } : State).gpr r = s.gpr r :=
    fun s r hr => RegUpd.gpr_setReg_of_ne _ _ hr
  refine open_ok (n := b) h hb' (by simp only [opened, hsz]) rfl rfl rfl rfl (he s₁) (he s₂)
    (by simp only [Nat.ne_of_gt h0, ↓reduceIte, hsz, List.singleton_append])
    (by simp only [Nat.ne_of_gt h0, ↓reduceIte, hsz, List.singleton_append]) rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun x hx hs => ?_) (fun _ _ _ h => h)
    (pub_esp (τ := τ) h (by rw [he, he, h.sp]) (hg s₁) (hg s₂)) h.fl h.px (wp_esp (τ := τ) h (hg s₁) (hg s₂)) h.unk h.mm h.mmx
    h.mxcsr h.mcdt
  exact h.win_eq (h.below_win hb' hx).1 hs

theorem pushRegs_sound {τ τ' : T} {rs : List Reg} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : push τ (.push rs) = some τ') (e₁ : isa.push (.push rs) s₁ = some s₁')
    (e₂ : isa.push (.push rs) s₂ = some s₂') : Agree τ' s₁' s₂' := by
  intro _
  simp only [push] at hs
  split at hs <;> [skip; cases hs]
  rename_i hc
  cases hs
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
  obtain ⟨⟨hok, hb⟩, h0⟩ := hc
  simp only [isa, X86.push] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  rename_i hc₁
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  have h := ha hok
  obtain ⟨-, hrs, hn⟩ := hc₁
  have hsz := size_frame h0 (by omega_using [])
  have hb' : size (4 * rs.length) ≤ τ.sp := by rw [hsz]; exact hb
  obtain ⟨rd₁, wr₁, sp₁, g₁⟩ := pushRegs_eq s₁ rs
  obtain ⟨rd₂, wr₂, sp₂, g₂⟩ := pushRegs_eq s₂ rs
  obtain ⟨c₁, z₁, n₁, o₁⟩ := pushRegs_rest s₁ rs
  obtain ⟨c₂, z₂, n₂, o₂⟩ := pushRegs_rest s₂ rs
  obtain ⟨u₁, m₁, x₁, mx₁, mc₁⟩ := pushRegs_keepR s₁ rs
  obtain ⟨u₂, m₂, x₂, mx₂, mc₂⟩ := pushRegs_keepR s₂ rs
  have hf₁ := (pushRegs_mem s₁ rs hrs hn).1
  have hf₂ := (pushRegs_mem s₂ rs hrs (by rw [← h.sp]; exact hn)).1
  have hbi := below_iff h.wbW h.spNat h.sp_le hb'
  refine open_ok (n := 4 * rs.length) h hb' (by simp only [opened, hsz]) rfl rfl rfl rfl
    (by show (pushRegs s₁ rs).gpr .esp = _; rw [sp₁, hsz])
    (by show (pushRegs s₂ rs).gpr .esp = _; rw [sp₂, hsz])
    (by simp only [Nat.ne_of_gt h0, ↓reduceIte, hsz, List.singleton_append])
    (by simp only [Nat.ne_of_gt h0, ↓reduceIte, hsz, List.singleton_append]) rd₁ rd₂
    (fun x hx => hf₁ x (by rw [hsz] at hx; exact hx))
    (fun x hx => hf₂ x (by rw [hsz, h.sp] at hx; exact hx)) (fun x hx hs => ?_) (fun x hx hw' hs => ?_)
    (pub_esp (τ := τ) h (by show (pushRegs s₁ rs).gpr .esp = (pushRegs s₂ rs).gpr .esp; rw [sp₁, sp₂, h.sp]) g₁ g₂)
    (fun hf => by
      obtain ⟨a, b', c, d, e⟩ := h.fl hf
      exact ⟨by rw [c₁, c₂, a], by rw [z₁, z₂, b'], by rw [n₁, n₂, c], by rw [o₁, o₂, d],
        by obtain ⟨e1, e2, e3, e4⟩ := e; exact ⟨by rw [c₁]; exact e1, by rw [z₁]; exact e2,
          by rw [n₁]; exact e3, by rw [o₁]; exact e4⟩⟩)
    (fun x hx => by
      show (pushRegs s₁ rs).xmm x = (pushRegs s₂ rs).xmm x
      rw [pushRegs_xmm, pushRegs_xmm]; exact h.px x hx)
    (wp_esp (τ := τ) h g₁ g₂) (by show (pushRegs s₁ rs).unknowns = (pushRegs s₂ rs).unknowns; rw [u₁, u₂, h.unk])
    (by show (pushRegs s₁ rs).mm = (pushRegs s₂ rs).mm; rw [m₁, m₂, h.mm])
    (by show (pushRegs s₁ rs).mmx = (pushRegs s₂ rs).mmx; rw [x₁, x₂, h.mmx])
    (by show (pushRegs s₁ rs).mxcsr = (pushRegs s₂ rs).mxcsr; rw [mx₁, mx₂, h.mxcsr])
    (by show (pushRegs s₁ rs).mcdt = (pushRegs s₂ rs).mcdt; rw [mc₁, mc₂, h.mcdt])
  · simp only [opened] at hs
    split at hs
    · rename_i hall
      show (pushRegs s₁ rs).mem x = (pushRegs s₂ rs).mem x
      exact pushRegs_agree rs hrs s₁ s₂ h.sp (fun r hr => h.reg (List.all_eq_true.mp hall r hr)) hn x
        (.inl (by rw [hsz] at hx; exact hx))
    · rw [hsz] at hx
      have := (hbi x).mp (by rw [hsz]; exact hx)
      rw [bset_in (by rw [hsz] at this; omega_using [this])] at hs
      cases hs
  · simp only [opened] at hs
    split at hs
    · refine bclr_out (fun hk => hx ?_) hs
      rw [hbi]; rw [hsz]; omega_using [hk, hb]
    · exact bset_out hs

/-- A word stored at `esp - k`, within the `b` bytes below `esp`, changes no
byte outside them. -/
theorem writeW_out {m : Mem} {e : BitVec 32} {k b : Nat} {v : BitVec 32} (hk : 4 ≤ k) (hkb : k ≤ b)
    (he : b ≤ e.toNat) {x : Addr} (hx : ¬ (belowR e b).Contains x 1) :
    m.writeW ((e - BitVec.ofNat 32 k).setWidth 64) v x = m x := by
  have hE := e.isLt
  have hw : e = (e - BitVec.ofNat 32 b) + BitVec.ofNat 32 b := by bv_omega
  have hwt : (e - BitVec.ofNat 32 b).toNat + b = e.toNat := by rw [sub_toNat' he]; omega_using [he]
  have hbo := below_off (w := e - BitVec.ofNat 32 b) (o := b) (b := b) (Nat.le_refl _) (by omega_using [hwt, hE]) x
  rw [← hw] at hbo
  have hka : (e - BitVec.ofNat 32 k).setWidth 64 = (e - BitVec.ofNat 32 b).setWidth 64 + BitVec.ofNat 64 (b - k) := by
    rw [← addr_add (by omega_using [hwt, hE, hkb])]
    congr 1
    rw [Offset.ofNat_sub_ofNat (w := 32) hkb |>.symm]
    bv_omega
  simp only [Mem.writeW, Mem.write]
  split
  · rename_i hc
    exfalso
    apply hx
    rw [hbo]
    rw [hka, Offset.lt_iff x _ (by omega_using [hwt, hE, hkb])] at hc
    omega_using [hc, hkb, hk]
  · rfl

/-- A word stored elsewhere leaves a byte as it was. -/
theorem writeW_skip {m : Mem} {a : Addr} {v : BitVec 32} {x : Addr} (h : ¬ (x - a).toNat < 4) :
    m.writeW a v x = m x := by
  simp only [Mem.writeW, Mem.write]
  split
  · rename_i hc; exact absurd hc h
  · rfl

/-- A word stored at the same address in two memories, of the same value,
keeps their agreeing on its bytes and on every byte they agreed on. -/
theorem writeW_eq {m₁ m₂ : Mem} {a : Addr} {v : BitVec 32} {x : Addr}
    (h : (x - a).toNat < 4 ∨ m₁ x = m₂ x) : m₁.writeW a v x = m₂.writeW a v x := by
  simp only [Mem.writeW, Mem.write]
  split
  · rfl
  · rename_i hc
    rcases h with h | h
    · exact absurd h hc
    · exact h

theorem symPush_sound {τ τ' : T} {d : Reg} {name : String} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : push τ (.symPush d name) = some τ') (e₁ : isa.push (.symPush d name) s₁ = some s₁')
    (e₂ : isa.push (.symPush d name) s₂ = some s₂') : Agree τ' s₁' s₂' := by
  intro _
  simp only [push] at hs
  split at hs <;> [skip; cases hs]
  rename_i hc
  cases hs
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.ble_eq] at hc
  obtain ⟨⟨hok, hd⟩, h4⟩ := hc
  have hd' : d ≠ .esp := isSp_false hd
  simp only [isa, X86.push] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  rename_i hc₁
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  have h := ha hok
  have hn := hc₁.2
  have hsz : size 4 = 4 := rfl
  have hb' : size 4 ≤ τ.sp := h4
  have hesp : ∀ s : State, ∀ v, (((arithFlags s v false false).setReg .esp (s.gpr .esp - 4)).setReg d
      (s.syms name)).gpr .esp = s.gpr .esp - BitVec.ofNat 32 (size 4) := fun s v => by
    simp [State.setReg, Ne.symm hd', arithFlags, State.setFlags]; rfl
  refine open_ok (n := 4) h hb' rfl rfl rfl rfl rfl
    (by simp [State.setReg, Ne.symm hd', arithFlags, State.setFlags]; rfl)
    (by simp [State.setReg, Ne.symm hd', arithFlags, State.setFlags]; rfl)
    (by simp; rfl) (by simp; rfl) rfl rfl
    (fun x hx => writeW_out (k := 4) (b := 4) (by decide) (Nat.le_refl _) hn hx)
    (fun x hx => writeW_out (k := 4) (b := 4) (by decide) (Nat.le_refl _) (by rw [← h.sp]; exact hn)
      (by rw [← h.sp]; exact hx))
    (fun x hx _ => ?_) (fun x hx hw' hs => ?_) (fun r hr => ?_) (fun hf => nomatch hf)
    (fun x hx => h.px x hx) (fun e he => ?_) (by simp only [h.unk]) h.mm h.mmx h.mxcsr h.mcdt
  · show s₁.mem.writeW _ (s₁.unknowns 0) x = s₂.mem.writeW _ (s₂.unknowns 0) x
    rw [← h.unk, ← h.sp]
    refine writeW_eq (.inl ?_)
    have := (h.word_iff (k := 4) (m := 4) h4 (Nat.le_refl _) x).mpr (by
      have := (h.below_win hb' hx).2; omega_using [this, hsz])
    exact this
  · simp only [setF, RTaint.setR, opened] at hs
    refine bclr_out (fun hk => hx ?_) hs
    rw [below_iff h.wbW h.spNat h.sp_le hb' x]
    omega_using [hk, h4, hsz]
  · simp only [setF, RTaint.setR, opened, Bool.false_eq_true, ite_false] at hr
    obtain ⟨hne, hr⟩ := RegSet.mem_erase.mp hr
    simp only [State.setReg, hne, ite_false, arithFlags, State.setFlags]
    by_cases hre : r = .esp
    · simp only [hre, ite_true, h.sp]
    · simp only [hre, ite_false]; exact h.pub r hr
  · simp only [setF, RTaint.setR, opened, List.nil_append, List.mem_filter, Bool.not_eq_true'] at he
    obtain ⟨he, hne⟩ := he
    have hne' : e.1 ≠ d := fun h' => by rw [h'] at hne; simp [regEq] at hne
    obtain ⟨hes, e1, e2⟩ := h.wp e he
    refine ⟨hes, ?_, ?_⟩ <;> simp only [State.setReg, hne', hes, ite_false, arithFlags, State.setFlags]
    · exact e1
    · exact e2

theorem mcdtEnter_sound {τ τ' : T} {r : Reg} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : push τ (.mcdtEnter r) = some τ') (e₁ : isa.push (.mcdtEnter r) s₁ = some s₁')
    (e₂ : isa.push (.mcdtEnter r) s₂ = some s₂') : Agree τ' s₁' s₂' := by
  intro _
  simp only [push] at hs
  split at hs <;> [skip; cases hs]
  rename_i hc
  cases hs
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.ble_eq] at hc
  obtain ⟨⟨hok, hd⟩, h12⟩ := hc
  have hd' : r ≠ .esp := isSp_false hd
  simp only [isa, X86.push] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  rename_i hc₁
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  have h := ha hok
  have hn := hc₁.2
  have hb' : size 9 ≤ τ.sp := h12
  have hs9 : size 9 = 12 := rfl
  -- The two words the push stores, and the four bytes above them it leaves.
  have hlo : ∀ x, (belowR (s₁.gpr .esp) 12).Contains x 1 →
      (x - (s₁.gpr .esp - BitVec.ofNat 32 12).setWidth 64).toNat < 4 ∨
      (x - (s₁.gpr .esp - BitVec.ofNat 32 8).setWidth 64).toNat < 4 ∨
      τ.sp - 4 ≤ off τ s₁ x ∧ off τ s₁ x < τ.sp := by
    intro x hx
    have hb := (h.below_win hb' hx).2
    rw [h.word_iff (k := 12) (m := 4) h12 (by decide) x, h.word_iff (k := 8) (m := 4) (by omega_using [h12])
      (by decide) x]
    omega_using [hb, h12, hs9]
  refine open_ok (n := 9) h hb' rfl rfl rfl rfl rfl
    (by simp [State.setReg, Ne.symm hd']; rfl) (by simp [State.setReg, Ne.symm hd']; rfl)
    (by simp; rfl) (by simp; rfl) rfl rfl
    (fun x hx => (writeW_out (k := 12) (b := 12) (by decide) (Nat.le_refl _) hn hx).trans
        (writeW_out (k := 8) (b := 12) (by decide) (by decide) hn hx))
    (fun x hx => by
      have hn' : 12 ≤ (s₂.gpr .esp).toNat := by rw [← h.sp]; exact hn
      have hx' : ¬ (belowR (s₂.gpr .esp) 12).Contains x 1 := by rw [← h.sp]; exact hx
      exact (writeW_out (k := 12) (b := 12) (by decide) (Nat.le_refl _) hn' hx').trans
        (writeW_out (k := 8) (b := 12) (by decide) (by decide) hn' hx'))
    (fun x hx hs => ?_) (fun x hx hw' hs => ?_) (fun q hq => ?_) h.fl
    (fun x hx => h.px x hx) (fun e he => ?_) h.unk h.mm h.mmx h.mxcsr (by simp only [h.mcdt])
  · show (s₁.mem.writeW _ _).writeW _ _ x = (s₂.mem.writeW _ _).writeW _ _ x
    rw [← h.sp, ← h.mcdt, ← h.mxcsr]
    refine writeW_eq ?_
    rcases hlo x hx with hw | hw | hw
    · exact .inl hw
    · exact .inr (writeW_eq (.inl hw))
    · right
      have hfar : ∀ k, (k = 12 ∨ k = 8) → ¬ (x - (s₁.gpr .esp - BitVec.ofNat 32 k).setWidth 64).toNat < 4 := by
        rintro k (rfl | rfl) hc
        · rw [h.word_iff (k := 12) (m := 4) h12 (by decide) x] at hc; omega_using [hc, hw, h12]
        · rw [h.word_iff (k := 8) (m := 4) (by omega_using [h12]) (by decide) x] at hc; omega_using [hc, hw, h12]
      simp only [opened, RTaint.setR, ite_true] at hs
      refine (writeW_skip (hfar 8 (.inr rfl))).trans ((h.win_eq (h.below_win hb' hx).1
        (bclr_out (fun hk => ?_) hs)).trans (writeW_skip (hfar 8 (.inr rfl))).symm)
      omega_using [hk, hw, h12]
  · simp only [opened, RTaint.setR, ite_true] at hs
    refine bclr_out (fun hk => hx ?_) hs
    rw [below_iff h.wbW h.spNat h.sp_le hb' x]
    have hs9 : size 9 = 12 := rfl
    omega_using [hk, h12, hs9]
  · simp only [opened, RTaint.setR, ite_true] at hq
    simp only [State.setReg]
    rcases RegSet.mem_insert.mp hq with rfl | hq
    · simp only [ite_true]
    · by_cases hqr : q = r
      · simp only [hqr, ite_true]
      · by_cases hqe : q = .esp
        · simp only [hqe, ite_true, h.sp]
        · simp only [hqr, hqe, ite_false]; exact h.pub q hq
  · simp only [opened, RTaint.setR, List.nil_append, List.mem_filter, Bool.not_eq_true'] at he
    obtain ⟨he, hne⟩ := he
    have hne' : e.1 ≠ r := fun h' => by rw [h'] at hne; simp [regEq] at hne
    obtain ⟨hes, e1, e2⟩ := h.wp e he
    refine ⟨hes, ?_, ?_⟩ <;> simp only [State.setReg, hne', hes, ite_false]
    · exact e1
    · exact e2

theorem push_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : push τ i = some τ') (e₁ : isa.push i s₁ = some s₁') (e₂ : isa.push i s₂ = some s₂')
    (_hadr : isa.addrs i s₁ = isa.addrs i s₂) : Agree τ' s₁' s₂' := by
  cases i with
  | alloc b => exact alloc_sound ha hs e₁ e₂
  | push rs => exact pushRegs_sound ha hs e₁ e₂
  | symPush d n => exact symPush_sound ha hs e₁ e₂
  | mcdtEnter r => exact mcdtEnter_sound ha hs e₁ e₂
  | _ => simp only [push, reduceCtorEq] at hs

/-! ### Pops, calls and returns -/

/-- What `topIs` says of the stack. -/
theorem of_topIs {τ : T} {n : Nat} (h : topIs τ n = true) :
    τ.ok = true ∧ ∃ st, τ.stk = n :: st ∧ τ.sp + size n ≤ τ.W := by
  simp only [topIs, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨hok, hm⟩, hle⟩ := h
  refine ⟨hok, ?_⟩
  cases hst : τ.stk with
  | nil => rw [hst] at hm; cases hm
  | cons m st =>
    rw [hst] at hm
    exact ⟨st, by rw [Nat.eq_of_beq_eq_true hm], hle⟩

/-- `pop r k` leaves in `r` the frame's last word. -/
theorem popReg_last (r : Reg) (hr : r ≠ .esp) : ∀ (k : Nat) (s : State),
    (popReg s r (k + 1)).gpr r = s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 (4 * k)).setWidth 64) 32
  | 0, s => by
    simp only [popReg]
    rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setReg_self]
    simp
  | k + 1, s => by
    rw [popReg, popReg_last r hr k]
    simp only [RegUpd.mem_setReg]
    rw [RegUpd.gpr_setReg_self, BitVec.add_assoc]
    congr 3
    rw [show 4 * (k + 1) = 4 + 4 * k by omega_using [], BitVec.ofNat_add]; rfl

theorem popReg_xmm (s : State) (r : Reg) (k : Nat) : (popReg s r k).xmm = s.xmm := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih _

theorem popReg_keepR (s : State) (d : Reg) (k : Nat) :
    (popReg s d k).unknowns = s.unknowns ∧ (popReg s d k).mm = s.mm ∧ (popReg s d k).mmx = s.mmx ∧
      (popReg s d k).mxcsr = s.mxcsr ∧ (popReg s d k).mcdt = s.mcdt := by
  induction k generalizing s with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih => exact ih _

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
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
    obtain ⟨⟨ht, h0⟩, h4⟩ := hc
    obtain ⟨hok, st, hst, hle⟩ := of_topIs ht
    have h := ha hok
    have hsz := size_frame h0 h4
    simp only [isa, X86.pop] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    have hg : ∀ s : State, ∀ q, q ≠ .esp → (s.setReg .esp (s.gpr .esp + BitVec.ofNat 32 b)).gpr q = s.gpr q :=
      fun s q hq => RegUpd.gpr_setReg_of_ne _ _ hq
    refine close_ok (n := b) h hst hle (by simp only [close, hsz]) rfl rfl rfl (by simp [close, hst]) rfl
      (by simp [State.setReg, hsz]) (by simp [State.setReg, hsz])
      (by simp [Nat.ne_of_gt h0]) (by simp [Nat.ne_of_gt h0]) rfl rfl
      (fun x hx => by show lose _ _ _ _ x = lose _ _ _ _ x; rw [h.sp, h.unk]; exact lose_congr hx)
      (pub_esp (τ := τ) h (by simp [State.setReg, h.sp]) (hg _) (hg _)) h.fl h.px
      (wp_esp (τ := τ) h (hg _) (hg _)) (by simp only [h.unk]) h.mm h.mmx h.mxcsr h.mcdt
  | pop r k =>
    simp only [pop] at hs
    split at hs <;> [skip; cases hs]
    rename_i hc
    cases hs
    simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at hc
    obtain ⟨⟨ht, h0⟩, hr⟩ := hc
    have hr' := isSp_false hr
    obtain ⟨hok, st, hst, hle⟩ := of_topIs ht
    have h := ha hok
    have hsz := size_frame (n := 4 * k) (by omega_using [h0]) (by omega_using [])
    simp only [isa, X86.pop] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    obtain ⟨rd₁, wr₁, sp₁, g₁⟩ := popReg_eq b₁ r k
    obtain ⟨rd₂, wr₂, sp₂, g₂⟩ := popReg_eq b₂ r k
    obtain ⟨-, c₁, z₁, n₁, o₁⟩ := popReg_rest b₁ r k
    obtain ⟨-, c₂, z₂, n₂, o₂⟩ := popReg_rest b₂ r k
    obtain ⟨-, m₁, x₁, mx₁, mc₁⟩ := popReg_keepR b₁ r k
    obtain ⟨-, m₂, x₂, mx₂, mc₂⟩ := popReg_keepR b₂ r k
    have hle' : τ.sp + 4 * k ≤ τ.W := by rw [← hsz]; exact hle
    refine close_ok (n := 4 * k) h hst hle (by simp only [close, RTaint.setR, hsz]) rfl rfl rfl
      (by simp [close, RTaint.setR, hst]) rfl
      (by show (popReg b₁ r k).gpr .esp = _; rw [sp₁, hsz]) (by show (popReg b₂ r k).gpr .esp = _; rw [sp₂, hsz])
      (by simp only [show 4 * k ≠ 0 by omega_using [h0], ↓reduceIte])
      (by simp only [show 4 * k ≠ 0 by omega_using [h0], ↓reduceIte]) rd₁ rd₂
      (fun x hx => by show lose _ _ _ _ x = lose _ _ _ _ x; rw [h.sp, h.unk]; exact lose_congr hx)
      (fun q hq => ?_)
      (fun hf => by
        obtain ⟨a, b', c, d, e⟩ := h.fl hf
        exact ⟨by show (popReg b₁ r k).cf = (popReg b₂ r k).cf; rw [c₁, c₂, a],
          by show (popReg b₁ r k).zf = (popReg b₂ r k).zf; rw [z₁, z₂, b'],
          by show (popReg b₁ r k).sf = (popReg b₂ r k).sf; rw [n₁, n₂, c],
          by show (popReg b₁ r k).of = (popReg b₂ r k).of; rw [o₁, o₂, d],
          by obtain ⟨e1, e2, e3, e4⟩ := e
             exact ⟨by show (popReg b₁ r k).cf ≠ none; rw [c₁]; exact e1,
               by show (popReg b₁ r k).zf ≠ none; rw [z₁]; exact e2,
               by show (popReg b₁ r k).sf ≠ none; rw [n₁]; exact e3,
               by show (popReg b₁ r k).of ≠ none; rw [o₁]; exact e4⟩⟩)
      (fun x hx => by
        show (popReg b₁ r k).xmm x = (popReg b₂ r k).xmm x
        rw [popReg_xmm, popReg_xmm]; exact h.px x hx)
      (fun e he => ?_) (by simp only [h.unk]) (by show (popReg b₁ r k).mm = (popReg b₂ r k).mm; rw [m₁, m₂, h.mm])
      (by show (popReg b₁ r k).mmx = (popReg b₂ r k).mmx; rw [x₁, x₂, h.mmx])
      (by show (popReg b₁ r k).mxcsr = (popReg b₂ r k).mxcsr; rw [mx₁, mx₂, h.mxcsr])
      (by show (popReg b₁ r k).mcdt = (popReg b₂ r k).mcdt; rw [mc₁, mc₂, h.mcdt])
    · show (popReg b₁ r k).gpr q = (popReg b₂ r k).gpr q
      simp only [close, RTaint.setR] at hq
      by_cases hqr : q = r
      · subst hqr
        split at hq
        · rename_i hp
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega_using [h0]⟩
          rw [popReg_last q hr' k' b₁, popReg_last q hr' k' b₂, ← h.sp]
          simp only [Mem.readW]
          rw [load_read (w := 32 / 8) h (kk := some τ.sp) (fun k' hk => by cases hk; exact sp_eq) (by
            simp only [loadPub, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq]
            exact .inl ⟨by omega_using [hle', h0], hp⟩)]
        · exact absurd (RegSet.mem_erase.mp hq).1 (by simp)
      · have hq' : q ∈ τ.pub := by
          split at hq
          · rcases RegSet.mem_insert.mp hq with h' | h'
            · exact absurd h' hqr
            · exact h'
          · exact (RegSet.mem_erase.mp hq).2
        by_cases hqe : q = .esp
        · subst hqe; rw [sp₁, sp₂, h.sp]
        · rw [g₁ q hqe hqr, g₂ q hqe hqr]; exact h.pub q hq'
    · simp only [close, RTaint.setR, List.nil_append, List.mem_filter, Bool.not_eq_true'] at he
      obtain ⟨he, hne⟩ := he
      have hne' : e.1 ≠ r := fun h' => by rw [h'] at hne; simp [regEq] at hne
      obtain ⟨hes, e1, e2⟩ := h.wp e he
      exact ⟨hes, by show (popReg b₁ r k).gpr e.1 = _; rw [g₁ _ hes hne', e1],
        by show (popReg b₂ r k).gpr e.1 = (popReg b₁ r k).gpr e.1; rw [g₁ _ hes hne', g₂ _ hes hne', e2]⟩
  | mcdtLeave =>
    simp only [pop] at hs
    split at hs <;> [skip; cases hs]
    rename_i ht
    cases hs
    obtain ⟨hok, st, hst, hle⟩ := of_topIs ht
    have h := ha hok
    simp only [isa, X86.pop] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    have hg : ∀ s : State, ∀ q, q ≠ .esp → (s.setReg .esp (s.gpr .esp + 12)).gpr q = s.gpr q :=
      fun s q hq => RegUpd.gpr_setReg_of_ne _ _ hq
    refine close_ok (n := 9) h hst hle rfl rfl rfl rfl (by simp [close, hst]) rfl
      (by simp [State.setReg]; rfl) (by simp [State.setReg]; rfl)
      (by simp) (by simp) rfl rfl
      (fun x hx => by show lose _ _ _ _ x = lose _ _ _ _ x; rw [h.sp, h.unk]; exact lose_congr hx)
      (pub_esp (τ := τ) h (by simp [State.setReg, h.sp]) (hg _) (hg _)) h.fl h.px
      (wp_esp (τ := τ) h (hg _) (hg _)) (by simp only [h.unk]) h.mm h.mmx h.mxcsr (by simp only [h.mcdt])
  | _ => simp only [pop, reduceCtorEq] at hs

theorem call_sound {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂) (hs : RTaint.call τ = some τ')
    (e₁ : isa.call s₁ = some s₁') (e₂ : isa.call s₂ = some s₂')
    (_hadr : isa.callAddrs s₁ = isa.callAddrs s₂) : Agree τ' s₁' s₂' := by
  intro _
  simp only [RTaint.call] at hs
  split at hs <;> [skip; cases hs]
  rename_i hc
  cases hs
  simp only [Bool.and_eq_true, Nat.ble_eq] at hc
  obtain ⟨hok, h4⟩ := hc
  simp only [isa, X86.call, Option.some.injEq] at e₁ e₂
  subst e₁ e₂
  have h := ha hok
  have hsz : size 0 = 4 := rfl
  have hb' : size 0 ≤ τ.sp := h4
  have hn : 4 ≤ (s₁.gpr .esp).toNat := by have := h.spNat; omega_using [this, h4]
  have hg : ∀ s : State, ∀ q, q ≠ .esp → (s.setReg .esp (s.gpr .esp - 4)).gpr q = s.gpr q :=
    fun s q hq => RegUpd.gpr_setReg_of_ne _ _ hq
  refine open_ok (n := 0) h hb' rfl rfl rfl rfl rfl (by simp [State.setReg]; rfl) (by simp [State.setReg]; rfl)
    (by simp) (by simp) rfl rfl
    (fun x hx => writeW_out (k := 4) (b := 4) (by decide) (Nat.le_refl _) hn hx)
    (fun x hx => writeW_out (k := 4) (b := 4) (by decide) (Nat.le_refl _) (by rw [← h.sp]; exact hn)
      (by rw [← h.sp]; exact hx))
    (fun x hx _ => ?_) (fun x hx hw' hs => ?_)
    (pub_esp (τ := τ) h (by simp [State.setReg, h.sp]) (hg _) (hg _)) h.fl h.px (wp_esp (τ := τ) h (hg _) (hg _))
    (by simp only [h.unk]) h.mm h.mmx h.mxcsr h.mcdt
  · show s₁.mem.writeW _ (s₁.unknowns 0) x = s₂.mem.writeW _ (s₂.unknowns 0) x
    rw [← h.unk, ← h.sp]
    refine writeW_eq (.inl ?_)
    exact (h.word_iff (k := 4) (m := 4) h4 (Nat.le_refl _) x).mpr (by
      have := (h.below_win hb' hx).2; omega_using [this, hsz])
  · simp only [opened] at hs
    refine bclr_out (fun hk => hx ?_) hs
    rw [below_iff h.wbW h.spNat h.sp_le hb' x]
    omega_using [hk, h4, hsz]

theorem ret_sound {τ τ' : T} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (ha : Agree τ b₁ b₂)
    (hs : RTaint.ret τ = some τ') (e₁ : isa.ret a₁ b₁ = some c₁) (e₂ : isa.ret a₂ b₂ = some c₂)
    (_hadr : isa.retAddrs b₁ = isa.retAddrs b₂) : Agree τ' c₁ c₂ := by
  intro _
  simp only [RTaint.ret] at hs
  split at hs <;> [skip; cases hs]
  rename_i ht
  cases hs
  obtain ⟨hok, st, hst, hle⟩ := of_topIs ht
  have h := ha hok
  simp only [isa, X86.ret] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  have hg : ∀ s : State, ∀ q, q ≠ .esp → (s.setReg .esp (s.gpr .esp + 4)).gpr q = s.gpr q :=
    fun s q hq => RegUpd.gpr_setReg_of_ne _ _ hq
  exact close_ok (n := 0) h hst hle rfl rfl rfl rfl (by simp [close, hst]) rfl (by simp [State.setReg]; rfl)
    (by simp [State.setReg]; rfl) (by simp) (by simp) rfl rfl (fun _ hx => hx)
    (pub_esp (τ := τ) h (by simp [State.setReg, h.sp]) (hg _) (hg _)) h.fl h.px (wp_esp (τ := τ) h (hg _) (hg _))
    h.unk h.mm h.mmx h.mxcsr h.mcdt

end RTaint

open RTaint in
/-- The residue analysis, for two runs that leak the same (see `RTaint`). -/
def rtaint : VG.TaintCT isa where
  T := RTaint.T
  Agree := RTaint.Agree
  step := RTaint.stepK
  step_sound ha hs e₁ e₂ hadr := RTaint.step_sound ha ((RTaint.stepK_eq _ _).symm.trans hs) e₁ e₂ hadr
  addrs_length i s₁ s₂ := by
    cases i <;> (try cases ‹Src›) <;> (try cases ‹MOp›) <;> (try cases ‹MSrc›) <;>
      simp [addrs, srcAddrs, MOp.addrs, MSrc.addrs]
  meet := RTaint.meetK
  meet_left h := (RTaint.meetK_eq _ _).symm ▸ RTaint.meet_left h
  meet_right h := (RTaint.meetK_eq _ _).symm ▸ RTaint.meet_right h
  le := RTaint.le
  le_sound := RTaint.le_sound
  call := RTaint.callK
  call_sound ha hs e₁ e₂ hadr := RTaint.call_sound ha ((RTaint.callK_eq _).symm.trans hs) e₁ e₂ hadr
  callAddrs_length _ _ := rfl
  ret := RTaint.retK
  ret_sound ha hs e₁ e₂ hadr := RTaint.ret_sound ha ((RTaint.retK_eq _).symm.trans hs) e₁ e₂ hadr
  retAddrs_length _ _ := rfl
  push := RTaint.pushK
  push_sound ha hs e₁ e₂ hadr := RTaint.push_sound ha ((RTaint.pushK_eq _ _).symm.trans hs) e₁ e₂ hadr
  pop := RTaint.popK
  pop_sound ha hs e₁ e₂ hadr := RTaint.pop_sound ha ((RTaint.popK_eq _ _).symm.trans hs) e₁ e₂ hadr

namespace RTaint

/-- Two states that `Outside 0` relates agree on every register. -/
theorem outside_gpr {s₁ s₂ : State} (ho : Outside 0 s₁ s₂) (r : Reg) : s₁.gpr r = s₂.gpr r := by
  obtain ⟨-, -, hg, h01, -⟩ := ho
  simp only [BitVec.ushiftRight_zero] at h01
  by_cases h0 : r = .eax
  · subst h0
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have := congrArg (BitVec.getLsbD · i) h01
    simp only [BitVec.getLsbD_append, hi, ↓reduceIte] at this
    exact this
  · by_cases h2 : r = .edx
    · subst h2
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (BitVec.getLsbD · (i + 32)) h01
      simp only [BitVec.getLsbD_append, show ¬ i + 32 < 32 by omega, ↓reduceIte,
        show i + 32 - 32 = i by omega] at this
      exact this
    · exact hg r h0 h2

theorem mem_allRegs (r : Reg) : r ∈ RegSet.ofList allRegs := by
  cases r <;> decide

/-- Where the analysis starts holds of two states that `NoResidue` compares,
whose window of `W` bytes below `esp`, its return address and `an` bytes of
arguments above it are within the address space, whose window is outside
every region, and which agree on those arguments. -/
theorem agree_init {W an : Nat} {s₁ s₂ : State} (ho : Outside 0 s₁ s₂)
    (hu : s₁.unknowns = s₂.unknowns) (hW : W ≤ (s₁.gpr .esp).toNat)
    (htop : (s₁.gpr .esp).toNat + 4 + an ≤ 2 ^ 32)
    (hreg : ∀ g ∈ s₁.rd ++ s₁.wr, ∀ x, g.Contains x 1 →
      ¬ (x - (s₁.gpr .esp - BitVec.ofNat 32 W).setWidth 64).toNat < W)
    (hargs : ∀ j < an, s₁.mem ((s₁.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + j)) =
      s₂.mem ((s₁.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + j))) :
    Agree (init W an) s₁ s₂ := by
  intro _
  have hall := outside_gpr ho
  obtain ⟨hrd, hwr, -, -, hcf, hzf, hsf, hof, hx, hmm, hmmx, hmx, hmc, hmem⟩ := ho
  have hwbt : (wb (init W an) s₁).toNat = (s₁.gpr .esp).toNat - W := sub_toNat' hW
  refine ⟨hall _, hW, (by show (wb (init W an) s₁).toNat + W + 4 + an ≤ 2 ^ 32; rw [hwbt]; omega_using [hW, htop]), fun r _ => hall r, (fun h => nomatch h),
    fun x _ => congrFun hx x, (fun e he => nomatch he), hrd, hwr, hu, hmm, hmmx, hmx, hmc, fun _ j hj => ?_,
    ⟨[], s₁.wr, rfl, ⟨rfl, rfl⟩, fun g hg x hx => hreg g hg x hx, fun x hx _ => hmem x hx⟩⟩
  have e : wbA (init W an) s₁ + BitVec.ofNat 64 ((init W an).W + 4 + j) =
      (s₁.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + j) := by
    simp only [wbA, wb, init]
    rw [sub_setWidth' hW]
    rw [show W + 4 + j = W + (4 + j) by omega_using [], ← BitVec.ofNat_add_ofNat]
    bv_omega
  rw [e]; exact hargs j hj

/-- A register a callee may change, other than the result's, is `ecx`. -/
theorem saved_or_ecx (r : Reg) (h0 : r ≠ .eax) (h2 : r ≠ .edx) : r = .ecx ∨ r ∈ calleeSaved := by
  revert h0 h2; cases r <;> decide

theorem shr_hi {a₁ a₂ b₁ b₂ : BitVec 32} {rb : Nat} (h : a₁ = a₂) (hrb : 32 ≤ rb) :
    (a₁ ++ b₁) >>> rb = (a₂ ++ b₂) >>> rb := by
  subst h
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, show ¬ rb + i < 32 by omega, ↓reduceIte]

theorem shr_64 (x y : BitVec 64) {rb : Nat} (hrb : 64 ≤ rb) : x >>> rb = y >>> rb := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight]
  rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]

theorem pubX_all {τ : T} (h : τ.px = 255) (x : XReg) : pubX τ x = true := by
  simp only [pubX, h]; cases x <;> decide

/-- Two runs whose analysis ends in `done rb`, from states that agree outside
their buffers, and that preserve what the calling convention preserves,
agree outside the buffers but the `rb` low bits of the result, with every
flag defined. -/
theorem outside_of_done {τ : T} {rb : Nat} {s₁ s₂ s₁' s₂' : State} (h : Agree τ s₁' s₂')
    (hd : done rb τ = true) (ho : Outside 0 s₁ s₂) (hp₁ : abiPreserved s₁ s₁') (hp₂ : abiPreserved s₂ s₂') :
    Outside rb s₁' s₂' ∧ FlagsDefined s₁' := by
  simp only [done, Bool.and_eq_true, Nat.beq_eq, Bool.or_eq_true, Nat.ble_eq, List.isEmpty_iff] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hok, hstk⟩, -⟩, hsec⟩, hcx⟩, hfl⟩, hpx⟩, h64⟩, h32⟩ := hd
  obtain ⟨-, -, -, hpub, hfl', hpx', -, hrd, hwr, -, hmm, hmmx, hmx, hmc, -, ⟨F, B, hw, hf, -, hmem⟩⟩ := h hok
  rw [hstk] at hf
  obtain rfl : F = [] := hf.2
  rw [List.nil_append] at hw
  obtain ⟨fc, fz, fs, fo, fd⟩ := hfl' hfl
  refine ⟨⟨hrd, hwr, fun q h0 h2 => ?_, ?_, fc, fz, fs, fo, funext fun x => hpx' x (pubX_all hpx x), hmm, hmmx,
    hmx, hmc, fun x hx => ?_⟩, fd⟩
  · rcases saved_or_ecx q h0 h2 with rfl | hq
    · exact hpub _ hcx
    · rw [hp₁.1 q hq, hp₂.1 q hq]; exact outside_gpr ho q
  · rcases h64 with h64 | h2
    · exact shr_64 _ _ h64
    · rcases h32 with h32 | h0
      · exact shr_hi (hpub _ h2) h32
      · rw [hpub _ h2, hpub _ h0]
  · refine hmem x (fun g hg hc => hx g (by rw [hw] at *; exact hg) hc) fun _ => ?_
    rw [hsec]; exact Nat.zero_testBit _

/-- Code verified against its contract, whose analysis from where it starts
(`init W an`, for states its precondition makes as `agree_init` needs, and
that agree on the arguments it takes as public if their contract's `pub`
relates them) ends in `done rb`, returns without secret residue with an
`rb`-bit result. -/
theorem noResidue_of_verified {c : Prog isa} {k : Contract isa} {rb W an : Nat}
    (hv : Verified target c k)
    (hpre : ∀ s, k.pre s → W ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + an ≤ 2 ^ 32 ∧
      ∀ g ∈ s.rd ++ s.wr, ∀ x, g.Contains x 1 → ¬ (x - (s.gpr .esp - BitVec.ofNat 32 W).setWidth 64).toNat < W)
    (hargs : ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Outside 0 s₁ s₂ → ∀ j < an,
      s₁.mem ((s₁.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + j)) =
        s₂.mem ((s₁.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + j)))
    (h : ∃ hc, (rtaint.check (init W an) c hc).any (done rb) = true) : NoResidue c k rb := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho hu e₁ e₂
  obtain ⟨hc, h⟩ := h
  cases hτ : rtaint.check (init W an) c hc with
  | none => rw [hτ] at h; cases h
  | some τ' =>
    rw [hτ] at h
    obtain ⟨_, u₁, f₁, hp₁, -⟩ := hv.1 s₁ h₁
    obtain ⟨_, u₂, f₂, hp₂, -⟩ := hv.1 s₂ h₂
    obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
    obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
    obtain ⟨hW, htop, hreg⟩ := hpre s₁ h₁
    exact outside_of_done (TaintCT.agree_of_check hv.2.1 hτ h₁ h₂ hp
      (agree_init ho hu hW htop hreg (hargs s₁ s₂ h₁ h₂ hp ho)) e₁ e₂) (by exact h) ho hp₁ hp₂

end VG.X86.RTaint
