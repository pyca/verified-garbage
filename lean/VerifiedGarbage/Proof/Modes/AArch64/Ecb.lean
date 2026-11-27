module

public import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
public import VerifiedGarbage.Impl.Modes.AArch64.Ecb
public import VerifiedGarbage.Proof.Modes.AArch64.Setup
public import VerifiedGarbage.Proof.Modes.Ctr
import VerifiedGarbage.Proof.Modes.AArch64.Ctr
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.Cbc
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ECB on AArch64, for any core

`ecb_wp`: `c.ecb data n scr` replaces each of the `n` blocks at `D` with the
core's cipher of it, and keeps the callee-saved registers. As CBC
decryption's (`CbcGroup.lean`, `CbcDecChained.lean`) without the chaining
value: `ecbGroup_wp` is one group (its blocks to the buffer, `crypt`, and
back: `copyBack_wp` is `copyBlocks_wp` with where `x14` ends, from which the
data's address moves on), `ecbLoop_wp` the groups.
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS eorR)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- Block `j` of ECB's output: the cipher of block `j` of the data in `m₀`. -/
def ecbOut (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (j : Nat) : List Byte :=
  ciph (bytesAt m₀ (D + BitVec.ofNat 64 (L * j)) L)

/-- `copyBlocks_wp`, with where `x14` ends. -/
theorem copyBack_wp {S T : Addr} {n : Nat} {s₀ : State} (hbw : 0 < c.bw) (hbw2 : c.bw ≤ 2) (hn : 0 < n)
    (hfit : 8 * c.bw * n < 2 ^ 63)
    (hS : ∀ t < c.bw * n, InRegions (s₀.rd ++ s₀.wr) (S + BitVec.ofNat 64 (8 * t)) 8)
    (hT : ∀ t < c.bw * n, InRegions s₀.wr (T + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨S, 8 * c.bw * n⟩ ⟨T, 8 * c.bw * n⟩) (ha : s₀.gpr .x14 = T) (hb : s₀.gpr .x15 = S)
    (hc : s₀.gpr .x17 = BitVec.ofNat 64 n) :
    WP isa c.copyBlocks s₀ fun s => CopyInv c S T n s₀ n s ∧ s.gpr .x14 = T + BitVec.ofNat 64 (8 * c.bw * n) := by
  obtain hn64 : n ≤ 8 * c.bw * n := Nat.le_mul_of_pos_left n (by omega_arith)
  unfold Core.copyBlocks
  refine WP.mono (blockLoop_wp (c := c) _ (CopyInv c S T n s₀) (by omega_arith) hn (by omega_arith)
    (fun j s s' h hm hrd hwr hg => ⟨fun t ht => by rw [hm]; exact h.copied t ht, by rw [hm]; exact h.frame,
      fun r h1 h2 h3 h4 => by rw [hg r h2 h3 h4, h.regs r h1 h2 h3 h4], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩)
    (fun j hj s hi hax hbx => ?_) ⟨fun t ht => by omega_arith, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩ ha hb hc)
    fun _ h => ⟨h.1, h.2.1⟩
  obtain hlt := idx_lt (L := 8 * c.bw) hj
  obtain hw : ∀ w, 8 * c.bw * j + 8 * w = 8 * (c.bw * j + w) := fun w => by rw [Nat.mul_add, Nat.mul_assoc]
  obtain hbj : ∀ w < c.bw, c.bw * j + w < c.bw * n := fun w hw' => by have := idx_lt (L := c.bw) hj; omega_arith
  obtain hSs : ∀ t < 8 * c.bw * n, s.mem (S + BitVec.ofNat 64 t) = s₀.mem (S + BitVec.ofNat 64 t) := fun t ht =>
    hi.frame.bytes (R := ⟨S, 8 * c.bw * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega_arith) ht
  obtain hPT : Region.Sub ⟨T + BitVec.ofNat 64 (8 * c.bw * j), 8 * c.bw⟩ ⟨T, 8 * c.bw * n⟩ :=
    VG.Offset.sub_base T (by omega_arith)
  refine WP.mono (copyN_wp (k := c.bw) (P := T + BitVec.ofNat 64 (8 * c.bw * j)) (u := .x8)
    (Q := S + BitVec.ofNat 64 (8 * c.bw * j)) ⟨by rw [hax]; simp, by rw [hbx]; simp,
    by decide, by decide, by decide, by decide, by decide, by decide, by omega_arith, by omega_arith,
    fun w hw' => by rw [hi.wr, addr_add, hw w]; exact hT _ (hbj w hw'),
    fun w hw' => by rw [hi.rd, hi.wr, addr_add, hw w]; exact hS _ (hbj w hw'),
    (hsep.symm.sub_left hPT).sub_right (VG.Offset.sub_base S (by omega_arith)), by omega_arith⟩) fun s' h' => ?_
  refine ⟨⟨fun t ht => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 => by
      rw [h'.regs r h1 h1, hi.regs r h1 h2 h3 h4], by rw [h'.rd, hi.rd], by rw [h'.wr, hi.wr]⟩,
    h'.regs _ (by decide) (by decide), h'.regs _ (by decide) (by decide), h'.regs _ (by decide) (by decide)⟩
  · have : 8 * c.bw * (j + 1) = 8 * c.bw * j + 8 * c.bw := Nat.mul_succ _ _
    rw [h'.mem]
    by_cases h1 : 8 * c.bw * j ≤ t
    · rw [show T + BitVec.ofNat 64 t = T + BitVec.ofNat 64 (8 * c.bw * j) + BitVec.ofNat 64 (t - 8 * c.bw * j) by
        rw [addr_add, show 8 * c.bw * j + (t - 8 * c.bw * j) = t by omega_arith], over_at (by omega_arith) (by omega_arith), addr_add,
        show 8 * c.bw * j + (t - 8 * c.bw * j) = t by omega_arith, hSs t (by omega_arith)]
    · rw [over_out (off_sub_not T (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))]
      exact hi.copied t (by omega_arith)
  · rw [h'.mem]
    exact over_out fun h => hx _ (List.mem_singleton_self _) (hPT x (by simp only [Region.Contains]; omega_arith))

/-- The buffer's address to `x15`, the data's to `x14`, the count to `x17`. -/
theorem backArgs_ok (hbI : 8 * c.buf < 4096) (hd15 : c.dataReg ≠ .x15) (s : State) {B : Addr} (hB : s.gpr sb = B) :
    ∃ s', runBlock isa c.backArgs s = some s' ∧ s'.gpr .x15 = B + BitVec.ofNat 64 (8 * c.buf) ∧
      s'.gpr .x14 = s.gpr c.dataReg ∧ s'.gpr .x17 = s.gpr .x16 ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .x15 sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .x15 .x15 hbI
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .x14 c.dataReg
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .x17 .x16
  refine ⟨s₄, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁],
    by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [Core.backArgs, show ([movR .x15 sb, .addImm .x .x15 .x15 (8 * c.buf), movR .x14 c.dataReg,
        movR .x17 .x16] : List Instr) = [movR .x15 sb] ++ (([.addImm .x .x15 .x15 (8 * c.buf)] :
        List Instr) ++ (([movR .x14 c.dataReg] : List Instr) ++ [movR .x17 .x16])) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · rw [o₄ _ (by decide), o₃ _ (by decide), r₂, r₁, hB]
  · rw [o₄ _ (by decide), r₃, o₂ _ hd15, o₁ _ hd15]
  · rw [r₄, o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide)]
  · rw [o₄ r h3, o₃ r h1, o₂ r h2, o₁ r h2]

/-- On past the group's blocks: the data's address from `x14`, the count
from `x16` off the blocks left. -/
theorem ecbAdvance_ok (hdl : c.dataReg ≠ c.leftReg) (hd16 : c.dataReg ≠ .x16) (s : State) :
    ∃ s', runBlock isa c.ecbAdvance s = some s' ∧ s'.gpr c.dataReg = s.gpr .x14 ∧
      s'.gpr c.leftReg = s.gpr c.leftReg - s.gpr .x16 ∧
      (∀ r, r ≠ c.dataReg → r ≠ c.leftReg → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s c.dataReg .x14
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := subReg_ok s₁ c.leftReg c.leftReg .x16
  obtain l₁ : s₁.gpr c.leftReg = s.gpr c.leftReg := o₁ _ (Ne.symm hdl)
  obtain t₁ : s₁.gpr .x16 = s.gpr .x16 := o₁ _ (Ne.symm hd16)
  refine ⟨s₂, ?_, by rw [o₂ _ hdl, r₁], by rw [r₂, l₁, t₁],
    fun r h1 h2 => by rw [o₂ r h2, o₁ r h1], by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  rw [Core.ecbAdvance, show ([movR c.dataReg .x14, .sub .x c.leftReg c.leftReg .x16] : List Instr) =
    [movR c.dataReg .x14] ++ [.sub .x c.leftReg c.leftReg .x16] from rfl, runBlock_app, e₁, Option.bind_some, e₂]

/-- The data loop, before group `g`, with the key `k`. -/
structure EcbInv (cs : BlockSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (g : Nat) (s : State) :
    Prop where
  base : s.gpr sb = B
  ready : cs.Ready s B k
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * (c.G * g))
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - c.G * g)
  lt : c.G * g < n
  data : DInv (8 * c.bw) s₀.mem s.mem D n (c.G * g) (ecbOut (8 * c.bw) (cs.cipher k) s₀.mem D)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure EcbDone (cs : BlockSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (s : State) : Prop where
  base : s.gpr sb = B
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv (8 * c.bw) s₀.mem s.mem D n n (ecbOut (8 * c.bw) (cs.cipher k) s₀.mem D)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ecbGroup_wp (cs : BlockSpec c) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key}
    (hp : GPre c s₀ B D n (8 * c.bw)) {g : Nat} {s : State} (hi : EcbInv cs s₀ B D n k g s) :
    WP isa c.ecbGroup s fun s' =>
      (isa.eval (.nonzero .x c.leftReg) s' = some false ∧ EcbDone cs s₀ B D n k s') ∨
      (isa.eval (.nonzero .x c.leftReg) s' = some true ∧ EcbInv cs s₀ B D n k (g + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  obtain hL0 : 0 < 8 * c.bw := by omega_using [hbw0]
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨down, dsb, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨lown, lsb, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨-, -, -, -, -, d13, d14, d15, d16, -⟩ := not_own down
  obtain ⟨-, -, -, -, -, l13, -, -, -, -⟩ := not_own lown
  obtain hN : 8 * c.total < 2 ^ 64 := by omega_using [hsm]
  let v := n - c.G * g
  let cc := min v c.G
  obtain h8n : 8 * n ≤ 8 * c.bw * n := Nat.mul_le_mul_right n (by omega_using [hL0])
  obtain hv : v < 2 ^ 64 := by omega_using [hfitD, h8n]
  obtain hc0 : 0 < cc := by omega_using [hG0, hk]
  obtain hcG : cc ≤ c.G := by omega_using []
  obtain hkc : 8 * c.bw * (c.G * g) + 8 * c.bw * cc ≤ 8 * c.bw * n := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega_using [hc0])
  obtain hbwcc : 8 * c.bw * cc = 8 * (c.bw * cc) := Nat.mul_assoc _ _ _
  obtain hbG : c.bw * cc ≤ c.bw * c.G := Nat.mul_le_mul_left _ hcG
  obtain hcc1 : 8 * c.bw ≤ 8 * c.bw * cc := Nat.le_mul_of_pos_right _ hc0
  let A := D + BitVec.ofNat 64 (8 * c.bw * (c.G * g))
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  obtain hwS : (⟨B, 8 * c.total⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  obtain hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain subS : ∀ {d l : Nat}, d + l ≤ 8 * c.total → Region.Sub ⟨B + BitVec.ofNat 64 d, l⟩ ⟨B, 8 * c.total⟩ :=
    fun h => VG.Offset.sub_base B h
  obtain subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.total⟩ :=
    Region.sub_prefix (by omega_using [hroom])
  obtain subA : Region.Sub ⟨A, 8 * c.bw * cc⟩ ⟨D, 8 * c.bw * n⟩ := VG.Offset.sub_base D hkc
  obtain subT : Region.Sub ⟨T, 8 * c.bw * cc⟩ ⟨B, 8 * c.total⟩ := subS (by omega_using [hroom, hbuf, hbwcc, hbG])
  obtain subTbuf : Region.Sub ⟨T, 8 * c.bw * cc⟩ (blkRegion c B) := Region.sub_prefix (Nat.mul_le_mul_left _ hcG)
  obtain dDS : ∀ {r : Region}, Region.Sub r ⟨B, 8 * c.total⟩ → Region.Disjoint ⟨D, 8 * c.bw * n⟩ r :=
    fun h => hp.sep.sub_right h
  obtain dAT : Region.Disjoint ⟨A, 8 * c.bw * cc⟩ ⟨T, 8 * c.bw * cc⟩ := (dDS subT).sub_left subA
  obtain inT : ∀ t, t < c.bw * cc → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := fun t ht =>
    ⟨_, hwS, by rw [addr_add]; exact VG.Offset.contains_base B (by omega_using [hroom, hbuf, hbG, ht]) (by omega_using [hroom, hbuf, hN, hbG, ht])⟩
  obtain inA : ∀ t, t < c.bw * cc → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := fun t ht =>
    ⟨_, hwD, by rw [addr_add]; exact VG.Offset.contains_base D (by omega_using [hkc, hbwcc, ht]) (by omega_using [hfitD, hkc, hbwcc, ht])⟩
  unfold Core.ecbGroup
  -- The count, the addresses, and the blocks to the buffer.
  refine WP.seq (WP.mono_syms (groupCount_wp hL.lgG_lt l13 hi.leftR hv) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ sy₁ => ?_)
  obtain base₁ : s₁.gpr sb = B := by rw [o₁ _ (by decide) (by decide), hi.base]
  obtain ⟨s₂, e₂, a₂, b₂, t₂, o₂, m₂, rd₂, wr₂⟩ := xorArgs_ok hL.bufImm d14 s₁ base₁
  refine WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  refine WP.seq (WP.mono_syms (copyBlocks_wp (S := A) (T := T) hbw0 hbw2 hc0 (by omega_using [hsm, hroom, hbuf, hbwcc, hbG])
    (fun t ht => by rw [rd₂', wr₂']; exact inRd (inA t ht)) (fun t ht => by rw [wr₂']; exact inT t ht) dAT
    (by rw [a₂]) (by rw [b₂, o₁ _ d13 d16, hi.dataR]) (by rw [t₂, c₁])) fun s₃ ⟨h₃, _⟩ sy₃ => ?_)
  obtain keep₃ : ∀ r, r ∉ ownRegs → s₃.gpr r = s.gpr r := fun r hr => by
    obtain ⟨-, -, h8, -, -, h13, h14, h15, h16, h17⟩ := not_own hr
    rw [h₃.regs r h8 h14 h15 h17, o₂ r h14 h15 h17, o₁ r h13 h16]
  obtain base₃ : s₃.gpr sb = B := by rw [keep₃ _ (by decide), hi.base]
  obtain rd₃' : s₃.rd = s.rd := by rw [h₃.rd, rd₂']
  obtain wr₃' : s₃.wr = s.wr := by rw [h₃.wr, wr₂']
  obtain f₃ : Frame [⟨T, 8 * c.bw * cc⟩] s.mem s₃.mem := by rw [← mem₂]; exact h₃.frame
  obtain ready₃ : cs.Ready s₃ B k := cs.ready_frame hi.ready f₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr subTbuf)
    ⟨fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, hwS, subT⟩, rd₃', wr₃',
      by rw [sy₃, runBlock_syms e₂, sy₁]⟩ fun r hr => by
    obtain ⟨h1, -, -⟩ := of_not_modeRegs hr
    exact keep₃ r h1
  -- The cipher.
  refine WP.seq (WP.mono (cs.crypt_wp base₃ ⟨by rw [wr₃']; exact hwS, hfit⟩ ready₃)
    fun s₄ ⟨base₄, dr₄, lr₄, ready₄, f₄, ks₄, rd₄, wr₄⟩ => ?_)
  obtain left₄ : s₄.gpr c.leftReg = BitVec.ofNat 64 v := by rw [lr₄, keep₃ _ lown, hi.leftR]
  obtain data₄ : s₄.gpr c.dataReg = A := by rw [dr₄, keep₃ _ down, hi.dataR]
  refine WP.seq (WP.mono_syms (groupCount_wp hL.lgG_lt l13 left₄ hv) fun s₅ ⟨c₅, o₅, m₅, rd₅, wr₅⟩ sy₅ => ?_)
  obtain base₅ : s₅.gpr sb = B := by rw [o₅ _ (by decide) (by decide), base₄]
  obtain ⟨s₆, e₆, a₆, b₆, t₆, o₆, m₆, rd₆, wr₆⟩ := backArgs_ok hL.bufImm d15 s₅ base₅
  refine WP.seq (WP.of_runBlock ⟨s₆, e₆, ?_⟩)
  obtain mem₆ : s₆.mem = s₄.mem := by rw [m₆, m₅]
  obtain rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃']
  obtain wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃']
  -- The blocks back to the data.
  refine WP.seq (WP.mono_syms (copyBack_wp (S := T) (T := A) hbw0 hbw2 hc0 (by omega_using [hsm, hroom, hbuf, hbwcc, hbG])
    (fun t ht => by rw [rd₆', wr₆']; exact inRd (inT t ht)) (fun t ht => by rw [wr₆']; exact inA t ht) dAT.symm
    (by rw [b₆, o₅ _ d13 d16, data₄]) (by rw [a₆]) (by rw [t₆, c₅])) fun s₇ ⟨h₇, x14₇⟩ sy₇ => ?_)
  obtain f₇ : Frame [⟨A, 8 * c.bw * cc⟩] s₄.mem s₇.mem := by rw [← mem₆]; exact h₇.frame
  obtain g₇ : ∀ r, r ∉ ownRegs → s₇.gpr r = s₄.gpr r := fun r hr => by
    obtain ⟨-, -, h8, -, -, h13, h14, h15, h16, h17⟩ := not_own hr
    rw [h₇.regs r h8 h14 h15 h17, o₆ r h14 h15 h17, o₅ r h13 h16]
  obtain left₇ : s₇.gpr c.leftReg = BitVec.ofNat 64 v := by rw [g₇ _ lown, left₄]
  obtain x16₇ : s₇.gpr .x16 = BitVec.ofNat 64 cc := by
    rw [h₇.regs _ (by decide) (by decide) (by decide) (by decide), o₆ _ (by decide) (by decide) (by decide), c₅]
  -- On to the next group.
  obtain ⟨s₈, e₈, d₈, l₈, o₈, m₈, rd₈, wr₈⟩ := ecbAdvance_ok hdl d16 s₇
  refine WP.of_runBlock ⟨s₈, e₈, ?_⟩
  obtain left₈ : s₈.gpr c.leftReg = BitVec.ofNat 64 (v - cc) := by
    rw [l₈, left₇, x16₇, VG.Offset.ofNat_sub_ofNat (by omega_using [])]
  obtain hz : isa.eval (.nonzero .x c.leftReg) s₈ = some !(decide (v = cc)) := by
    rw [eval_nonzero, left₈, ofNat_beq_zero (by omega_using [hv]), decide_eq_decide.mpr (show v - cc = 0 ↔ v = cc by omega_using [])]
  obtain keep₈ : ∀ r, r ∉ modeRegs c → s₈.gpr r = s₄.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3⟩ := of_not_modeRegs hr
    rw [o₈ r h2 h3, g₇ r h1]
  obtain w₄ : s₄.wr = s.wr := by rw [wr₄, wr₃']
  obtain ready₈ : cs.Ready s₈ B k := by
    refine cs.ready_frame ready₄ (by rw [m₈]; exact f₇) (fun r hr => ?_) ⟨fun r hr => ?_, ?_, ?_, ?_⟩ keep₈
    · simp only [List.mem_singleton] at hr; subst hr
      exact .inl (((dDS subCore).sub_left subA).symm)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by rw [w₄]; exact hwD, subA⟩
    · rw [rd₈, h₇.rd, rd₆', rd₄, rd₃']
    · rw [wr₈, h₇.wr, wr₆', wr₄, wr₃']
    · rw [runBlock_syms e₈, sy₇, runBlock_syms e₆, sy₅]
  -- The bytes, through the steps.
  obtain hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega_using [hfitD]
  obtain outCore : ∀ {R : Region}, Region.Disjoint R (coreRegion c B) → R.len ≤ 2 ^ 64 →
      ∀ i < R.len, s₄.mem (R.base + BitVec.ofNat 64 i) = s₃.mem (R.base + BitVec.ofNat 64 i) := fun hd hl i hi =>
    f₄.bytes (R := _) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hl hi
  obtain outT : ∀ {R : Region}, Region.Disjoint R ⟨T, 8 * c.bw * cc⟩ → R.len ≤ 2 ^ 64 →
      ∀ i < R.len, s₃.mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) := fun hd hl i hi =>
    f₃.bytes (R := _) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hl hi
  -- The data before the copy back: as on entry.
  obtain dat₄ : ∀ i < 8 * c.bw * n, s₄.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := fun i hin => by
    rw [outCore (R := ⟨D, 8 * c.bw * n⟩) (dDS subCore) hn64 i hin,
      outT (R := ⟨D, 8 * c.bw * n⟩) (dDS subT) hn64 i hin]
  obtain dat0 : ∀ i, 8 * c.bw * (c.G * g) ≤ i → i < 8 * c.bw * n →
      s.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) :=
    fun i h1 h2 => by rw [hi.data i h2, ite_eq_right (by omega_using [h1])]
  -- The cipher's blocks in the buffer.
  obtain dec₄ : ∀ j < cc, ∀ u < 8 * c.bw, s₄.mem (T + BitVec.ofNat 64 (8 * c.bw * j + u)) =
      (cs.cipher k (bytesAt s₀.mem (D + BitVec.ofNat 64 (8 * c.bw * (c.G * g + j))) (8 * c.bw))).getD u 0 := by
    intro j hj u hu
    obtain hjl := idx_lt (L := 8 * c.bw) hj
    obtain eT : T + BitVec.ofNat 64 (8 * c.bw * j + u) = blkAddr c B j + BitVec.ofNat 64 u := by
      simp only [T, blkAddr]; rw [addr_add, addr_add, Nat.add_assoc]
    rw [eT, ← bytesAt_getD s₄.mem _ hu, ks₄ _ (by omega_using [hj])]
    congr 2
    apply List.ext_getElem (by simp [bytesAt])
    intro x h1 _
    obtain hx : x < 8 * c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range, blkAddr]
    rw [addr_add, show 8 * c.buf + 8 * c.bw * j + x = 8 * c.buf + (8 * c.bw * j + x) by omega_using [], ← addr_add,
      h₃.copied _ (by omega_using [hjl, hx]), mem₂, addr_add, addr_add, Nat.mul_add, Nat.add_assoc,
      dat0 _ (by omega_using []) (by omega_using [hkc, hjl, hx])]
  obtain eA : ∀ t, D + BitVec.ofNat 64 (8 * c.bw * (c.G * g) + t) = A + BitVec.ofNat 64 t := fun t => by
    rw [← addr_add]
  obtain hdata : DInv (8 * c.bw) s₀.mem s₈.mem D n (c.G * g + cc) (ecbOut (8 * c.bw) (cs.cipher k) s₀.mem D) := by
    refine dinv_of_blocks hL0 fun q hq r hr => ?_
    rw [m₈]
    obtain hqn := idx_lt (L := 8 * c.bw) hq
    by_cases hin : c.G * g ≤ q ∧ q < c.G * g + cc
    · obtain ⟨j, rfl⟩ : ∃ j, q = c.G * g + j := ⟨q - c.G * g, by omega_using [hin]⟩
      obtain hjc : j < cc := by omega_using [hin]
      obtain hjl := idx_lt (L := 8 * c.bw) hjc
      rw [Nat.mul_add, Nat.add_assoc, eA, h₇.copied _ (by omega_using [hr, hjl]), mem₆, dec₄ j hjc r hr,
        ite_eq_left hin.2, ecbOut]
    · have hlo : q < c.G * g → 8 * c.bw * q + r < 8 * c.bw * (c.G * g) := fun h => by
        have := idx_lt (L := 8 * c.bw) h; omega_using [hr, this]
      obtain hhi : c.G * g + cc ≤ q → 8 * c.bw * (c.G * g) + 8 * c.bw * cc ≤ 8 * c.bw * q := fun h => by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ h
      obtain hout : ∀ R ∈ [(⟨A, 8 * c.bw * cc⟩ : Region)],
          ¬ R.Contains (D + BitVec.ofNat 64 (8 * c.bw * q + r)) 1 := fun R hR => by
        simp only [List.mem_singleton] at hR; subst hR
        exact not_contains_off D (by omega_using [hin, hlo, hhi]) (by omega_using [hn64, hr, hqn]) (by omega_using [hcc1, hr]) (by omega_using [hkc, hn64])
      rw [f₇ _ hout, dat₄ _ (by omega_using [hr, hqn]), hi.data _ (by omega_using [hr, hqn]), idx_div hr, idx_mod hr]
      by_cases h2 : q < c.G * g
      · rw [ite_eq_left (hlo h2), ite_eq_left (by omega_using [h2])]
      · rw [ite_eq_right (by have := Nat.mul_le_mul_left (8 * c.bw) (Nat.le_of_not_lt h2); omega_using [this]),
          ite_eq_right (by omega_using [hin, h2])]
  -- The slots.
  obtain saved₈ : ∀ i < 10, s₈.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi10 => by
    rw [m₈, ← hi.saved i hi10]
    refine (f₇.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (((dDS (subS (show 8 * (c.slots + i) + 8 ≤ 8 * c.total by omega_using [hroom, hi10]))).sub_left
        subA).symm)) (by decide)).trans ?_
    refine (f₄.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base B (by omega_using []) (by omega_using [hroom, hN, hi10])) (by decide)).trans ?_
    exact f₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint B (.inr (by omega_using [hbuf, hbwcc, hbG])) (by omega_using [hroom, hN, hi10]) (by omega_using [hroom, hbuf, hN, hbwcc, hbG])) (by decide)
  obtain fr : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s₈.mem := by
    rw [m₈]
    refine hi.frame.trans (((f₃.sub fun r hr => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; exact subT⟩).trans
      (f₄.sub fun r hr => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subCore⟩)).trans (f₇.sub fun r hr => ?_))
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subA⟩
  obtain base₈ : s₈.gpr sb = B := by rw [o₈ _ (Ne.symm dsb) (Ne.symm lsb), g₇ _ (by decide), base₄]
  obtain rd₈' : s₈.rd = s₀.rd := by rw [rd₈, h₇.rd, rd₆', hi.rd]
  obtain wr₈' : s₈.wr = s₀.wr := by rw [wr₈, h₇.wr, wr₆', hi.wr]
  by_cases hdone : v = cc
  · refine .inl ⟨by rw [hz, decide_eq_true hdone]; rfl, base₈, saved₈, ?_, fr, rd₈', wr₈'⟩
    rw [show n = c.G * g + cc by omega_using [hc0, hdone]] at hdata ⊢
    exact hdata
  · have hcc : cc = c.G := by omega_using [hdone]
    obtain hg1 : c.G * (g + 1) = c.G * g + cc := by rw [hcc, Nat.mul_succ]
    refine .inr ⟨by rw [hz, decide_eq_false hdone]; rfl, base₈, ready₈, saved₈, ?_, ?_, by omega_using [hdone, hg1],
      by rw [hg1]; exact hdata, fr, rd₈', wr₈'⟩
    · rw [d₈, x14₇, addr_add, hg1, Nat.mul_add]
    · rw [left₈, hg1]; congr 1; omega_using []

/-- The data loop. -/
theorem ecbLoop_wp (cs : BlockSpec c) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key}
    (hp : GPre c s₀ B D n (8 * c.bw)) {s : State} (hi : EcbInv cs s₀ B D n k 0 s) :
    WP isa (.loop c.ecbGroup (.nonzero .x c.leftReg)) s (EcbDone cs s₀ B D n k) := by
  refine WP.loop (M := isa) (fun m s => ∃ g, m = n - c.G * g ∧ EcbInv cs s₀ B D n k g s) (fun m s hs => ?_) n s
    ⟨0, by simp, hi⟩
  obtain ⟨g, rfl, hg⟩ := hs
  refine WP.mono (ecbGroup_wp cs hp hg) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · have hG := cs.layout.G_pos
    exact .inr ⟨z, n - c.G * (g + 1),
      by have := d.lt; have := hg.lt; rw [Nat.mul_succ] at *; omega_arith, g + 1, rfl, d⟩

/-- ECB: every block of the data replaced with the core's cipher of it. -/
theorem ecb_wp (cs : BlockSpec c) {data nR scr : Reg} (hds : data ≠ sb) (hns : nR ≠ sb) (hdn : c.dataReg ≠ nR)
    {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr scr = B) (hD : s₀.gpr data = D)
    (hn : (s₀.gpr nR).toNat = n) (hs : ScrIn s₀ B c.total) (hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s₀.wr)
    (sDS : Region.Disjoint ⟨D, 8 * c.bw * n⟩ ⟨B, 8 * c.total⟩) (fitD : D.toNat + 8 * c.bw * n ≤ 2 ^ 64)
    (hk : cs.KeyArgs s₀ [⟨B, 8 * c.total⟩] k) :
    WP isa (c.ecb data nR scr) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Core.savedRegs.getD i .x19) = s₀.gpr (Core.savedRegs.getD i .x19)) ∧
      blocksOf (8 * c.bw) s'.mem D n = (blocksOf (8 * c.bw) s₀.mem D n).map (cs.cipher k) ∧
      Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  obtain hN : 8 * c.total < 2 ^ 64 := by omega_arith
  obtain hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega_arith
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨-, dsb, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨-, lsb, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain subMode : Region.Sub (modeRegion c B) ⟨B, 8 * c.total⟩ := VG.Offset.sub_base B (by omega_arith)
  -- The entry.
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok hsm hroom (r := Core.ecbRegs data nR scr) s₀ hB hs
  obtain ⟨s₁, e₁b, dr₁, lr₁, g₁b, m₁b, rd₁b, wr₁b⟩ := ctrArgs_ok sE (Core.ecbRegs data nR scr) hdn hdl
  obtain e₁ : runBlock isa (c.ctrEntry (Core.ecbRegs data nR scr) ++ c.ctrArgs (Core.ecbRegs data nR scr)) s₀ =
      some s₁ := by rw [runBlock_app, eE, Option.bind_some, e₁b]
  unfold Core.ecb
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  obtain b₁ : s₁.gpr sb = B := by rw [g₁b _ (Ne.symm dsb) (Ne.symm lsb), bE]
  obtain rd₁ : s₁.rd = s₀.rd := by rw [rd₁b, rdE]
  obtain wr₁ : s₁.wr = s₀.wr := by rw [wr₁b, wrE]
  obtain sv₁ : ∀ i < 10, s₁.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .x19) :=
    fun i hi => by rw [m₁b, svE i hi]
  obtain kr := keyRegs_ne cs.keyRegs_ok
  obtain f₁' : Frame [⟨B, 8 * c.total⟩] s₀.mem s₁.mem := by
    rw [m₁b]
    exact fE.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_cons_self, subMode⟩
  obtain hk₁ : cs.KeyArgs s₁ [⟨B, 8 * c.total⟩] k :=
    cs.keyArgs_congr hk (fun x hx => by
        rw [g₁b x (fun e => dk (e ▸ hx)) (fun e => lk (e ▸ hx)), gE x (not_setupRegs (kr x hx)).1]) rd₁ wr₁
      (by rw [runBlock_syms e₁]) f₁'
  -- The key.
  refine WP.seq (WP.mono (cs.prepare_wp b₁ ⟨by rw [wr₁]; exact hs.wr, hs.fit⟩ List.mem_cons_self hk₁)
    fun s₂ ⟨ready₂, b₂, dr₂, lr₂, f₂, rd₂, wr₂⟩ => ?_)
  obtain keep₂ : ∀ j, c.slots ≤ j → j < c.total →
      s₂.mem.readW (wordAddr B j) 64 = s₁.mem.readW (wordAddr B j) 64 := fun j h1 h2 =>
    f₂.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.disjoint_base B (by omega_arith) (by omega_arith)) (by decide)
  obtain wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  obtain rd₂' : s₂.rd = s₀.rd := by rw [rd₂, rd₁]
  obtain left₂ : s₂.gpr c.leftReg = s₀.gpr nR := by rw [lr₂, lr₁]; exact gE _ hns
  obtain hz₂ : isa.eval (.zero .x c.leftReg) s₂ = some (decide (n = 0)) := by
    rw [eval_zero, left₂]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  obtain hp : GPre c s₂ B D n (8 * c.bw) := ⟨⟨by rw [wr₂']; exact hs.wr, hs.fit⟩, by rw [wr₂']; exact hwD, sDS, fitD⟩
  -- The groups.
  refine WP.seq (WP.mono (M := isa) (Q := EcbDone cs s₂ B D n k)
    (WP.ite (decide (n = 0)) hz₂ (fun h0 => ?_) (fun h0 => ?_)) fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₂, fun _ _ => rfl, fun i hi' => by rw [hn0, Nat.mul_zero] at hi'; omega_arith, Frame.refl _ _,
      rfl, rfl⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine ecbLoop_wp cs hp ⟨b₂, ready₂, fun _ _ => rfl, ?_, ?_, by omega_arith,
      fun i _ => by rw [ite_eq_right (by omega_arith)], Frame.refl _ _, rfl, rfl⟩
    · rw [dr₂, dr₁]; show sE.gpr data = _; rw [gE _ hds, hD]; simp
    · rw [left₂, Nat.mul_zero, Nat.sub_zero, ← hn]; simp
  -- The exit.
  obtain hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  obtain hinj : ∀ i < 10, ∀ j < 10, Core.savedRegs.getD i .x19 = Core.savedRegs.getD j .x19 → i = j := by decide
  obtain ⟨s₅, e₅, v₅, -, m₅, rd₅, wr₅⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₄
    d₄.base hsv hinj (by omega_arith) (fun i hi' => by
      rw [d₄.rd, d₄.wr, rd₂', wr₂']
      exact inRd (slot_wr hs.wr hN (by omega_arith)))
  obtain subCore : ∀ x ∈ [coreRegion c B], Region.Sub x ⟨B, 8 * c.total⟩ := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by omega_arith)
  obtain f₀₂ : Frame [⟨B, 8 * c.total⟩] s₀.mem s₂.mem :=
    f₁'.trans (f₂.sub fun x hx => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, subCore x hx⟩)
  obtain f₄ : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s₄.mem :=
    (f₀₂.mono fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_self).trans d₄.frame
  refine WP.of_runBlock ⟨s₅, e₅, fun i hi' => ?_, ?_, by rw [m₅]; exact f₄, by rw [rd₅, d₄.rd, rd₂'],
    by rw [wr₅, d₄.wr, wr₂']⟩
  · rw [v₅ i hi', d₄.saved i hi', keep₂ _ (by omega_arith) (by omega_arith), sv₁ i hi']
  · rw [m₅, blocksOf_of_dinv (fun j => cs.cipher_len k _) d₄.data,
      ← blocksOf_frame f₀₂ (by omega_arith) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact sDS)]
    simp only [blocksOf, List.map_map]
    rfl

end VG.Proof.Modes.AArch64
