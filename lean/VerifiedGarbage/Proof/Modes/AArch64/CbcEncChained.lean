module

import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
public import VerifiedGarbage.Proof.Modes.CbcEnc
public import VerifiedGarbage.Impl.Modes.AArch64.CbcEnc
public import VerifiedGarbage.Proof.Modes.AArch64.Setup
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Modes.AArch64.Fb
import VerifiedGarbage.Proof.Modes.CbcNext
public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained
import VerifiedGarbage.Proof.Modes.AArch64.Ctr

/-! ### `Modes.AArch64.CbcEncLoop`, which only this module used -/

section

/-!
# CBC encryption on AArch64, for any core: the data loop

`cbcEncBlock_wp`: one iteration encrypts block `j`, which holds
`Pⱼ ⊕ Cⱼ₋₁`, in the buffer (`encIn`, `BlockSpec.crypt_wp`), stores `Cⱼ`
back (`encOut`) and, unless it was the last, XORs it into block `j + 1`
(`encChain`). Each is `copyN_wp` or `xorN_wp`; blocks are `8 bw` bytes. As on
x86-64 (`Proof/Modes/X86_64/CbcEncLoop.lean`).
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- Byte `r` of block `q` of the data before block `j`: the ciphertext's
below it, block `j` as `Pⱼ ⊕ Cⱼ₋₁`, the plaintext's above. -/
def encByte (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (j q r : Nat) : Byte :=
  if q < j then (cbcEncC L ciph m₀ D iv q).getD r 0
  else if q = j then m₀ (D + BitVec.ofNat 64 (L * q + r)) ^^^ (cbcEncPrev L ciph m₀ D iv j).getD r 0
  else m₀ (D + BitVec.ofNat 64 (L * q + r))

/-- The data loop, before block `j`; `m₀` is the memory on entry. -/
structure EInv (cs : BlockSpec c) (s₀ : State) (m₀ : Mem) (B D : Addr) (n : Nat) (k : cs.Key) (iv : List Byte)
    (j : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  ready : cs.Ready s B k
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * j)
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - j)
  lt : j < n
  data : ∀ q < n, ∀ r < 8 * c.bw, s.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
    encByte (8 * c.bw) (cs.cipher k) m₀ D iv j q r
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure EDone (cs : BlockSpec c) (s₀ : State) (m₀ : Mem) (B D : Addr) (n : Nat) (k : cs.Key) (iv : List Byte)
    (s : State) : Prop where
  base : s.gpr sb = B
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv (8 * c.bw) m₀ s.mem D n n (cbcEncC (8 * c.bw) (cs.cipher k) m₀ D iv)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  /-- The buffer's first block holds the last ciphertext block. -/
  last : n ≠ 0 → ∀ u < 8 * c.bw, s.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
    (cbcEncC (8 * c.bw) (cs.cipher k) m₀ D iv (n - 1)).getD u 0

theorem cbcEncBlock_wp (cs : BlockSpec c) {s₀ : State} {m₀ : Mem} {B D : Addr} {n : Nat} {k : cs.Key}
    {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : GPre c s₀ B D n (8 * c.bw)) {j : Nat} {s : State}
    (hi : EInv cs s₀ m₀ B D n k iv j s) :
    WP isa c.cbcEncBlock s fun s' =>
      (isa.eval (.nonzero .x c.leftReg) s' = some false ∧ EDone cs s₀ m₀ B D n k iv s') ∨
      (isa.eval (.nonzero .x c.leftReg) s' = some true ∧ EInv cs s₀ m₀ B D n k iv (j + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hj := hi.lt
  obtain hL0 : 0 < 8 * c.bw := by omega_using [hbw0]
  obtain hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  obtain hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  obtain hLG' : 8 * c.bw * c.G = 8 * (c.bw * c.G) := Nat.mul_assoc _ _ _
  obtain hLn : 8 * c.bw * n = 8 * (c.bw * n) := Nat.mul_assoc _ _ _
  obtain h8n : 8 * n ≤ 8 * c.bw * n := Nat.mul_le_mul_right n (by omega_using [hL0])
  obtain hjl := idx_lt (L := 8 * c.bw) hj
  obtain hj1 : 8 * c.bw * (j + 1) = 8 * c.bw * j + 8 * c.bw := Nat.mul_succ _ _
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨down, dsb, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨lown, lsb, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨d6, d7, -⟩ := not_own down
  obtain ⟨l6, l7, -⟩ := not_own lown
  obtain hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega_using [hfitD]
  obtain p0 : ∀ X : Addr, X + BitVec.ofNat 64 0 = X := fun X => by simp
  let ciph := cs.cipher k
  let A := D + BitVec.ofNat 64 (8 * c.bw * j)
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  obtain hwS : (⟨B, 8 * c.total⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  obtain hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain subT : Region.Sub ⟨T, 8 * c.bw⟩ ⟨B, 8 * c.total⟩ :=
    VG.Offset.sub_base B (by omega_using [hroom, hbuf, hLG, hLG'])
  obtain subTbuf : Region.Sub ⟨T, 8 * c.bw⟩ (blkRegion c B) := Region.sub_prefix hLG
  obtain subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.total⟩ :=
    Region.sub_prefix (by omega_using [hroom])
  obtain subA : Region.Sub ⟨A, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ := VG.Offset.sub_base D hjl
  obtain dDS : ∀ {r : Region}, Region.Sub r ⟨B, 8 * c.total⟩ → Region.Disjoint ⟨D, 8 * c.bw * n⟩ r :=
    fun h => hp.sep.sub_right h
  obtain dAT : Region.Disjoint ⟨A, 8 * c.bw⟩ ⟨T, 8 * c.bw⟩ := (dDS subT).sub_left subA
  obtain hw : ∀ w, 8 * c.bw * j + 8 * w = 8 * (c.bw * j + w) := fun w => by rw [Nat.mul_add, Nat.mul_assoc]
  obtain hbj : ∀ w < c.bw, c.bw * j + w < c.bw * n := fun w hw' => by have := idx_lt (L := c.bw) hj; omega_using [hw', this]
  obtain inT : ∀ w < c.bw, InRegions s.wr (T + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
    ⟨_, hwS, by rw [addr_add]; exact VG.Offset.contains_base B (by omega_using [hroom, hbuf, hLG, hLG', hw']) (by omega_using [hroom, hbuf, hfit, hLG, hLG', hw'])⟩
  obtain inA : ∀ w < c.bw, InRegions s.wr (A + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
    ⟨_, hwD, by rw [addr_add, hw]; exact VG.Offset.contains_base D (by have := hbj w hw'; omega_using [hLn, this]) (by have := hbj w hw'; omega_using [hLn, hn64, this])⟩
  -- The data, outside the buffer and the core.
  obtain dT : ∀ q < n, ∀ r < 8 * c.bw, Region.Disjoint ⟨T, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ :=
    fun _ _ _ _ => (dDS subT).symm
  obtain hqr : ∀ {q r}, q < n → r < 8 * c.bw → 8 * c.bw * q + r < 8 * c.bw * n := fun hq hr => by
    have := idx_lt (L := 8 * c.bw) hq; omega_using [hr, this]
  -- Block `j` to the buffer.
  unfold Core.cbcEncBlock
  refine WP.seq (WP.mono_syms (copyN_wp (k := c.bw) (P := T) (Q := A) (t := .x6) (u := .x6) ⟨by rw [hi.base],
    by rw [hi.dataR, p0], by decide, Ne.symm d6, by decide, Ne.symm d6, by omega_using [], by decide, by omega_using [hsm, hroom, hbuf, hLG, hLG'], by omega_using [hbw2],
    inT, fun w hw' => inRd (inA w hw'), dAT.symm, by omega_using [hjl, hn64]⟩) fun s₁ h₁ sy₁ => ?_)
  obtain base₁ : s₁.gpr sb = B := by rw [h₁.regs _ (by decide) (by decide), hi.base]
  obtain f₁ : Frame [⟨T, 8 * c.bw⟩] s.mem s₁.mem := by rw [h₁.mem]; exact over_frame _ _ _ _
  obtain ready₁ : cs.Ready s₁ B k := cs.ready_frame hi.ready f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr subTbuf)
    ⟨fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, hwS, subT⟩, h₁.rd, h₁.wr, sy₁⟩
    fun r hr => by
    obtain ⟨h1, -⟩ := of_not_modeRegs hr; exact h₁.regs r (not_own h1).1 (not_own h1).1
  -- Encrypted.
  refine WP.seq (WP.mono (cs.crypt_wp base₁ ⟨by rw [h₁.wr]; exact hwS, hfit⟩ ready₁)
    fun s₂ ⟨base₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩ => ?_)
  obtain eT : blkAddr c B 0 = T := by simp only [blkAddr, T, Nat.mul_zero, Nat.add_zero]
  obtain hpl : (cbcEncPrev (8 * c.bw) ciph m₀ D iv j).length = 8 * c.bw := by
    unfold cbcEncPrev; split
    · exact hiv
    · generalize j - 1 = t; cases t <;> exact cs.cipher_len k _
  obtain blk : bytesAt s.mem A (8 * c.bw) =
      Spec.Cbc.xor (bytesAt m₀ A (8 * c.bw)) (cbcEncPrev (8 * c.bw) ciph m₀ D iv j) := by
    apply List.ext_getElem (by simp [bytesAt, Spec.Cbc.xor, hpl])
    intro u h1 _
    obtain hu : u < 8 * c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range, Spec.Cbc.xor, List.getElem_zipWith]
    rw [addr_add, hi.data j hj u hu, encByte, ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl,
      ← List.getElem_eq_getD (h := by rw [hpl]; exact hu)]
  obtain C₂ : ∀ u < 8 * c.bw, s₂.mem (T + BitVec.ofNat 64 u) = (cbcEncC (8 * c.bw) ciph m₀ D iv j).getD u 0 :=
    fun u hu => by
      rw [← bytesAt_getD s₂.mem T hu, ← eT, ks₂ 0 hG0, eT]
      congr 2
      rw [cbcEncC_eq]
      congr 1
      rw [← blk]
      apply List.ext_getElem (by simp [bytesAt])
      intro v h1 _
      obtain hv : v < 8 * c.bw := by simpa [bytesAt] using h1
      simp only [bytesAt, List.getElem_map, List.getElem_range]
      rw [h₁.mem, over_at hv (by omega_using [hjl, hn64])]
  obtain D₂ : ∀ q < n, ∀ r < 8 * c.bw, s₂.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
      s.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) := fun q hq r hr => by
    rw [f₂.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact dDS subCore) hn64 (hqr hq hr), h₁.mem,
      over_sep (dDS subT).symm (hqr hq hr) hn64]
  -- Back to the data, and the count.
  obtain data₂ : s₂.gpr c.dataReg = A := by rw [dr₂, h₁.regs _ d6 d6, hi.dataR]
  refine WP.seq (WP.block_append (WP.mono_syms (copyN_wp (k := c.bw) (P := A) (Q := T) (t := .x6) (u := .x6)
    ⟨by rw [data₂, p0], by rw [base₂], Ne.symm d6, by decide, Ne.symm d6, by decide, by decide, by omega_using [], by omega_using [hbw2],
    by omega_using [hsm, hroom, hbuf, hLG, hLG'], fun w hw' => by rw [wr₂, h₁.wr]; exact inA w hw',
    fun w hw' => by rw [rd₂, wr₂, h₁.rd, h₁.wr]; exact inRd (inT w hw'), dAT, by omega_using [hjl, hn64]⟩) fun s₃a h₃a sy₃a => ?_))
  obtain ⟨s₃, e₃, l₃, o₃, m₃, rd₃, wr₃⟩ := subImm_ok s₃a c.leftReg c.leftReg (v := 1) (by decide)
  refine WP.of_runBlock ⟨s₃, e₃, ?_⟩
  obtain left₂ : s₃a.gpr c.leftReg = BitVec.ofNat 64 (n - j) := by
    rw [h₃a.regs _ l6 l6, lr₂, h₁.regs _ l6 l6, hi.leftR]
  obtain left₃ : s₃.gpr c.leftReg = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [l₃, left₂, VG.Offset.ofNat_sub_ofNat (by omega_using [hj]), show n - j - 1 = n - (j + 1) by omega_using []]
  obtain hz₃ : isa.eval (.zero .x c.leftReg) s₃ = some (decide (j + 1 = n)) := by
    rw [eval_zero, left₃, ofNat_beq_zero (by omega_using [h8n, hn64]), decide_eq_decide.mpr (show n - (j + 1) = 0 ↔ j + 1 = n by omega_using [hj])]
  obtain g₃ : ∀ x, x ≠ .x6 → x ≠ c.leftReg → s₃.gpr x = s₂.gpr x := fun x h1 h2 => by
    rw [o₃ x h2, h₃a.regs x h1 h1]
  obtain base₃ : s₃.gpr sb = B := by rw [g₃ _ (by decide) (Ne.symm lsb), base₂]
  obtain data₃ : s₃.gpr c.dataReg = A := by rw [g₃ _ d6 hdl, data₂]
  obtain mem₃ : s₃.mem = over s₂.mem A (8 * c.bw) fun i => s₂.mem (T + BitVec.ofNat 64 i) := by rw [m₃, h₃a.mem]
  obtain f₃ : Frame [⟨A, 8 * c.bw⟩] s₂.mem s₃.mem := by rw [mem₃]; exact over_frame _ _ _ _
  obtain D₃ : ∀ q < n, ∀ r < 8 * c.bw, s₃.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
      if q = j then (cbcEncC (8 * c.bw) ciph m₀ D iv j).getD r 0
      else s.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) := fun q hq r hr => by
    rw [mem₃, over_blk _ _ _ hj hq hr hn64]
    split
    · exact C₂ r hr
    · exact D₂ q hq r hr
  obtain T₃ : ∀ u < 8 * c.bw, s₃.mem (T + BitVec.ofNat 64 u) = (cbcEncC (8 * c.bw) ciph m₀ D iv j).getD u 0 :=
    fun u hu => by rw [mem₃, over_sep dAT hu (by omega_using [hjl, hn64]), C₂ u hu]
  -- The slots.
  obtain slotOut : ∀ i < 10, ∀ {R : Region}, (Region.Sub R ⟨D, 8 * c.bw * n⟩ ∨ R = ⟨T, 8 * c.bw⟩ ∨
      R = coreRegion c B) → Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ R := fun i hi10 R hR => by
    rcases hR with h | rfl | rfl
    · exact ((dDS (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.total by
        omega_using [hroom, hi10]))).sub_left h).symm
    · exact VG.Offset.disjoint B (.inr (by omega_using [hbuf, hLG, hLG'])) (by omega_using [hroom, hfit, hi10]) (by omega_using [hroom, hbuf, hfit, hLG, hLG'])
    · exact VG.Offset.disjoint_base B (by omega_using []) (by omega_using [hroom, hfit, hi10])
  obtain saved₃ : ∀ i < 10, s₃.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi10 => by
    rw [← hi.saved i hi10]
    refine (f₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slotOut i hi10 (.inl subA)) (by decide)).trans ?_
    refine (f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slotOut i hi10 (.inr (.inr rfl))) (by decide)).trans ?_
    exact f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slotOut i hi10 (.inr (.inl rfl))) (by decide)
  obtain fr₃ : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s₃.mem :=
    hi.frame.trans (((f₁.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; exact subT⟩).trans
      (f₂.sub fun r hr => ⟨_, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subCore⟩)).trans
      (f₃.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subA⟩))
  obtain rd₃' : s₃.rd = s₀.rd := by rw [rd₃, h₃a.rd, rd₂, h₁.rd, hi.rd]
  obtain wr₃' : s₃.wr = s₀.wr := by rw [wr₃, h₃a.wr, wr₂, h₁.wr, hi.wr]
  obtain ready₃ : cs.Ready s₃ B k := cs.ready_frame ready₂ f₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inl ((dDS subCore).sub_left subA).symm)
    ⟨fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by rw [wr₂, h₁.wr]; exact hwD, subA⟩,
      by rw [rd₃, h₃a.rd], by rw [wr₃, h₃a.wr], by rw [runBlock_syms e₃, sy₃a]⟩ fun r hr => by
    obtain ⟨h1, -, h3⟩ := of_not_modeRegs hr; exact g₃ r (not_own h1).1 h3
  -- The last block, or on to the next.
  obtain hAL : A + BitVec.ofNat 64 (8 * c.bw) = D + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := by rw [addr_add, hj1]
  refine WP.seq (WP.mono_syms (Q := fun s₄ => (∀ x, x ≠ .x6 → x ≠ .x7 → s₄.gpr x = s₃.gpr x) ∧ s₄.rd = s₃.rd ∧
      s₄.wr = s₃.wr ∧ (j + 1 = n → s₄.mem = s₃.mem) ∧ (j + 1 < n → s₄.mem = over s₃.mem (D + BitVec.ofNat 64 (8 * c.bw * (j + 1))) (8 * c.bw)
        fun i => s₃.mem ((D + BitVec.ofNat 64 (8 * c.bw * (j + 1))) + BitVec.ofNat 64 i) ^^^ s₃.mem (T + BitVec.ofNat 64 i)))
    (WP.ite (decide (j + 1 = n)) hz₃ (fun h => ?_) (fun h => ?_)) fun s₄ h₄ sy₄ => ?_)
  · exact WP.block_nil ⟨fun _ _ _ => rfl, rfl, rfl, fun _ => rfl, fun h' => by simp at h; omega_using [h', h]⟩
  · have hjn : j + 1 < n := by simp at h; omega_using [hj, h]
    obtain hjl' := idx_lt (L := 8 * c.bw) hjn
    obtain subN' : Region.Sub ⟨D + BitVec.ofNat 64 (8 * c.bw * (j + 1)), 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ :=
      VG.Offset.sub_base D hjl'
    obtain hw' : ∀ w, 8 * c.bw * (j + 1) + 8 * w = 8 * (c.bw * (j + 1) + w) := fun w => by
      rw [Nat.mul_add 8, Nat.mul_assoc]
    obtain hbj' : ∀ w < c.bw, c.bw * (j + 1) + w < c.bw * n := fun w hw'' => by
      have := idx_lt (L := c.bw) hjn; omega_using [hw'', this]
    exact WP.mono (xorN_wp (k := c.bw) (P := D + BitVec.ofNat 64 (8 * c.bw * (j + 1))) (Q := T) (t := .x6)
      (u := .x7) ⟨by rw [data₃, hAL], by rw [base₃], Ne.symm d6, by decide, Ne.symm d7, by decide, by omega_using [], by omega_using [],
      by omega_using [hbw2], by omega_using [hsm, hroom, hbuf, hLG, hLG'], fun w hw'' => ⟨_, by rw [wr₃', ← hi.wr]; exact hwD, by
        rw [addr_add, hw']
        exact VG.Offset.contains_base D (by have := hbj' w hw''; omega_using [hLn, this]) (by have := hbj' w hw''; omega_using [hLn, hn64, this])⟩,
      fun w hw'' => by rw [rd₃', wr₃', ← hi.rd, ← hi.wr]; exact inRd (inT w hw''),
      (dDS subT).sub_left subN', by omega_using [hn64, hjl']⟩ (by decide)) fun s₄ h₄ =>
      ⟨h₄.regs, h₄.rd, h₄.wr, fun h' => by omega_using [hjn, h'], fun _ => h₄.mem⟩
  obtain ⟨g₄, rd₄, wr₄, mDone, mMore⟩ := h₄
  obtain ⟨s₆, e₆, a₆, o₆, m₆, rd₆, wr₆⟩ := addImm_ok s₄ c.dataReg c.dataReg (v := 8 * c.bw) (by omega_using [hbw2])
  refine WP.of_runBlock ⟨s₆, e₆, ?_⟩
  obtain keep₆ : ∀ x, x ≠ .x6 → x ≠ .x7 → x ≠ c.dataReg → s₆.gpr x = s₃.gpr x := fun x h1 h2 h3 => by
    rw [o₆ x h3, g₄ x h1 h2]
  obtain left₆ : s₆.gpr c.leftReg = BitVec.ofNat 64 (n - (j + 1)) := by rw [keep₆ _ l6 l7 (Ne.symm hdl), left₃]
  obtain hz : isa.eval (.nonzero .x c.leftReg) s₆ = some !(decide (j + 1 = n)) := by
    rw [eval_nonzero, left₆, ofNat_beq_zero (by omega_using [h8n, hn64]), decide_eq_decide.mpr (show n - (j + 1) = 0 ↔ j + 1 = n by omega_using [hj])]
  have mem₆ : s₆.mem = s₄.mem := m₆
  obtain base₆ : s₆.gpr sb = B := by rw [keep₆ _ (by decide) (by decide) (Ne.symm dsb), base₃]
  obtain rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₄, rd₃']
  obtain wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₄, wr₃']
  by_cases hdone : j + 1 = n
  · have hm : s₆.mem = s₃.mem := by rw [mem₆, mDone hdone]
    refine .inl ⟨by rw [hz, decide_eq_true hdone]; rfl, base₆, by rw [hm]; exact saved₃,
      dinv_of_blocks hL0 fun q hq r hr => ?_, by rw [hm]; exact fr₃, rd₆', wr₆',
      fun _ u hu => by rw [hm, ← hdone, Nat.add_sub_cancel]; exact T₃ u hu⟩
    rw [hm, D₃ q hq r hr, ite_eq_left hq]
    split
    · rename_i h; subst h; rfl
    · rw [hi.data q hq r hr, encByte, ite_eq_left (by omega_arith)]
  · have hjn : j + 1 < n := by omega_using [hj, hdone]
    obtain hm := mMore hjn
    rw [← mem₆] at hm
    obtain subN : Region.Sub ⟨D + BitVec.ofNat 64 (8 * c.bw * (j + 1)), 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ :=
      VG.Offset.sub_base D (idx_lt hjn)
    obtain fN : Frame [⟨D + BitVec.ofNat 64 (8 * c.bw * (j + 1)), 8 * c.bw⟩] s₃.mem s₆.mem := by
      rw [hm]; exact over_frame _ _ _ _
    refine .inr ⟨by rw [hz, decide_eq_false hdone]; rfl, base₆, ?_, fun i hi10 => ?_, ?_, left₆, hjn,
      fun q hq r hr => ?_, fr₃.trans (fN.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subN⟩), rd₆', wr₆'⟩
    · exact cs.ready_frame ready₃ fN (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inl ((dDS subCore).sub_left subN).symm)
        ⟨fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by rw [wr₃', ← hi.wr]; exact hwD, subN⟩,
          by rw [rd₆', rd₃'], by rw [wr₆', wr₃'], by rw [runBlock_syms e₆, sy₄]⟩
        fun r hr => by
          obtain ⟨h1, h2, -⟩ := of_not_modeRegs hr
          exact keep₆ r (not_own h1).1 (not_own h1).2.1 h2
    · rw [← saved₃ i hi10]
      exact fN.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact slotOut i hi10 (.inl subN)) (by decide)
    · rw [a₆, g₄ _ d6 d7, data₃, hAL]
    · rw [hm, over_blk _ _ _ hjn hq hr hn64]
      split
      · rename_i h; subst h
        rw [addr_add, D₃ _ hjn r hr, ite_eq_right (by omega_using []), hi.data _ hjn r hr, T₃ r hr, encByte,
          ite_eq_right (by omega_using []), ite_eq_right (by omega_using []), encByte, ite_eq_right (Nat.lt_irrefl _),
          ite_eq_left rfl, cbcEncPrev, ite_eq_right (by omega_using []), Nat.add_sub_cancel]
      · rename_i h
        rw [D₃ q hq r hr]
        split
        · rename_i h'; subst h'; rw [encByte, ite_eq_left (by omega_using [])]
        · rename_i h'
          rw [hi.data q hq r hr, encByte, encByte]
          by_cases h3 : q < j
          · rw [ite_eq_left h3, ite_eq_left (by omega_using [h3])]
          · rw [ite_eq_right h3, ite_eq_right h', ite_eq_right (show ¬ q < j + 1 by omega_using [h', h3]), ite_eq_right h]

/-- The data loop. -/
theorem cbcEncLoop_wp (cs : BlockSpec c) {s₀ : State} {m₀ : Mem} {B D : Addr} {n : Nat} {k : cs.Key}
    {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : GPre c s₀ B D n (8 * c.bw)) {s : State}
    (hi : EInv cs s₀ m₀ B D n k iv 0 s) :
    WP isa (.loop c.cbcEncBlock (.nonzero .x c.leftReg)) s (EDone cs s₀ m₀ B D n k iv) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = n - j ∧ EInv cs s₀ m₀ B D n k iv j s) (fun m s hs => ?_) n s
    ⟨0, by simp, hi⟩
  obtain ⟨j, rfl, hj⟩ := hs
  refine WP.mono (cbcEncBlock_wp cs hiv hp hj) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, n - (j + 1), by have := d.lt; have := hj.lt; omega_arith, j + 1, rfl, d⟩

end VG.Proof.Modes.AArch64

end

end


/-!
# CBC encryption on AArch64 that updates the chaining value, for any core

`cbcEncryptChained_wp`: `c.cbcEncryptChained r ivR` is CBC encryption of
the data, which also replaces the IV at `P` with the last
ciphertext block (`Spec.Cbc.next`): the IV's address stays in `ivR`, which
the core's `prepare` and `crypt` keep (`KeepsReg`, as for OFB and CFB), and
after the last block the buffer, which still holds it (`EDone.last`), is
copied back to the IV. As on x86-64 (`Proof/Modes/X86_64/CbcEncChained.lean`).
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS eorR)
open VG.Spec.Aes (bytesAt)

theorem copyW_keepsReg {r t rd rs : Reg} {od os w : Nat} (h : r ≠ t) :
    (copyW t rd rs od os w).all (keepsReg r) = true := by
  simp [copyW, keepsReg, clobbers, dstOf, Ne.symm h]

theorem xorW_keepsReg {r t u rd rs : Reg} {od os w : Nat} (ht : r ≠ t) (hu : r ≠ u) :
    (xorW t u rd rs od os w).all (keepsReg r) = true := by
  simp [xorW, eorR, keepsReg, clobbers, dstOf, Ne.symm ht, Ne.symm hu]

theorem flatMap_keepsReg {r : Reg} {f : Nat → List Instr} (h : ∀ w, (f w).all (keepsReg r) = true) (k : Nat) :
    ((List.range k).flatMap f).all (keepsReg r) = true := by
  simp only [List.all_flatMap, List.all_eq_true]
  intro w _ i hi
  exact List.all_eq_true.mp (h w) i hi

variable {c : Core}

/-- The data loop of CBC encryption keeps a register that the core keeps and
the mode does not write. -/
theorem keepsReg_cbcEncBlock {r : Reg} (hm : r ∉ modeRegs c) (h : KeepsReg r c.crypt) :
    KeepsReg r c.cbcEncBlock := by
  obtain ⟨own, hd, hl⟩ := of_not_modeRegs hm
  obtain ⟨h6, h7, -⟩ := not_own own
  obtain hc : ∀ {rd rs : Reg} {od os : Nat}, ((List.range c.bw).flatMap (copyW .x6 rd rs od os)).all (keepsReg r) = true :=
    flatMap_keepsReg (fun _ => copyW_keepsReg h6) _
  refine KeepsReg.seq (keepsReg_of_regSafe hc) (KeepsReg.seq h (KeepsReg.seq (keepsReg_of_regSafe ?_)
    (KeepsReg.seq (KeepsReg.ite (keepsReg_of_regSafe rfl)
      (keepsReg_of_regSafe (flatMap_keepsReg (fun _ => xorW_keepsReg h6 h7) _)))
      (keepsReg_of_regSafe ?_))))
  · simp only [regSafe, Core.encOut, List.all_append, hc, Bool.true_and]
    simp [keepsReg, clobbers, dstOf, Ne.symm hl]
  · simp [regSafe, Core.encNext, keepsReg, clobbers, dstOf, Ne.symm hd]

/-- After the blocks: `EDone`, the IV written as well. -/
structure EDoneC (cs : BlockSpec c) (s₀ : State) (m₀ : Mem) (B P D : Addr) (n : Nat) (k : cs.Key)
    (iv : List Byte) (s : State) : Prop where
  base : s.gpr sb = B
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv (8 * c.bw) m₀ s.mem D n n (cbcEncC (8 * c.bw) (cs.cipher k) m₀ D iv)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s.mem
  ivOut : bytesAt s.mem P (8 * c.bw) = Spec.Cbc.next iv (Spec.Cbc.encrypt (cs.cipher k) iv (blocksOf (8 * c.bw) m₀ D n))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem cbcEncryptChained_wp (cs : BlockSpec c) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n) {ivR : Reg}
    (hiv : IvRegOk c r ivR) {s₀ : State} {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B)
    (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D) (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.total)
    (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr) (hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s₀.wr)
    (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.total⟩) (sDS : Region.Disjoint ⟨D, 8 * c.bw * n⟩ ⟨B, 8 * c.total⟩)
    (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩) (fitD : D.toNat + 8 * c.bw * n ≤ 2 ^ 64)
    (hk : cs.KeyArgs s₀ [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] k)
    (hsc : KeepsReg ivR c.prepare ∧ KeepsReg ivR c.crypt) :
    WP isa (c.cbcEncryptChained r ivR) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Core.savedRegs.getD i .x19) = s₀.gpr (Core.savedRegs.getD i .x19)) ∧
      blocksOf (8 * c.bw) s'.mem D n =
        Spec.Cbc.encrypt (cs.cipher k) (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n) ∧
      bytesAt s'.mem P (8 * c.bw) = Spec.Cbc.next (bytesAt s₀.mem P (8 * c.bw))
        (Spec.Cbc.encrypt (cs.cipher k) (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n)) ∧
      Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧
      s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hbI := hL.bufImm
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  obtain hL0 : 0 < 8 * c.bw := by omega_arith
  obtain h8n : 8 * n ≤ 8 * c.bw * n := Nat.mul_le_mul_right n (by omega_arith)
  obtain hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega_arith
  obtain hqr : ∀ {q r}, q < n → r < 8 * c.bw → 8 * c.bw * q + r < 8 * c.bw * n := fun hq hr => by
    have := idx_lt (L := 8 * c.bw) hq; omega_arith
  obtain hN : 8 * c.total < 2 ^ 64 := by omega_arith
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨down, dsb, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨lown, lsb, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨d6, d7, -⟩ := not_own down
  obtain ⟨l6, l7, -⟩ := not_own lown
  obtain ⟨cs', c6, c7, -⟩ := not_setupRegs hr.ctr
  obtain ⟨ds', dd6, dd7, -⟩ := not_setupRegs hr.data
  obtain ⟨ns', n6, n7, -⟩ := not_setupRegs hr.n
  obtain ⟨iown, idr, ilr⟩ := of_not_modeRegs hiv.mode
  obtain ⟨i6, i7, -⟩ := not_own iown
  obtain ⟨isb, -, -, -⟩ := not_setupRegs hiv.setup
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  obtain subMode : Region.Sub (modeRegion c B) ⟨B, 8 * c.total⟩ := VG.Offset.sub_base B (by omega_arith)
  obtain subT : Region.Sub ⟨T, (8 * c.bw)⟩ ⟨B, 8 * c.total⟩ := VG.Offset.sub_base B (by omega_arith)
  obtain dTP : Region.Disjoint ⟨T, (8 * c.bw)⟩ ⟨P, (8 * c.bw)⟩ := (sPS.sub_right subT).symm
  obtain inS : ∀ {d m : Nat}, d + m ≤ 8 * c.total → InRegions s₀.wr (B + BitVec.ofNat 64 d) m := fun h =>
    ⟨_, hs.wr, VG.Offset.contains_base B h (by omega_arith)⟩
  -- The entry, and the IV's address to `ivR`.
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  obtain ⟨s₁, eS, xS, gS, mS, rdS, wrS⟩ := movR_ok sE ivR r.ctr
  unfold Core.cbcEncryptChained
  refine WP.seq (WP.of_runBlock ⟨s₁, by rw [runBlock_app, eE, Option.bind_some, eS], ?_⟩)
  obtain g₁ : ∀ x, x ≠ sb → x ≠ ivR → s₁.gpr x = s₀.gpr x := fun x h1 h2 => by rw [gS x h2, gE x h1]
  obtain b₁ : s₁.gpr sb = B := by rw [gS _ (Ne.symm isb), bE]
  obtain iv₁ : s₁.gpr ivR = P := by rw [xS, gE _ cs', hP]
  obtain ctr₁ : s₁.gpr r.ctr = P := by
    by_cases h : r.ctr = ivR
    · rw [h, iv₁]
    · rw [g₁ _ cs' h, hP]
  obtain sv₁ : ∀ i < 10, s₁.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .x19) :=
    fun i hi => by rw [mS, svE i hi]
  obtain f₁ : Frame [modeRegion c B] s₀.mem s₁.mem := by rw [mS]; exact fE
  obtain rd₁ : s₁.rd = s₀.rd := by rw [rdS, rdE]
  obtain wr₁ : s₁.wr = s₀.wr := by rw [wrS, wrE]
  obtain sy₁ : s₁.syms = s₀.syms := by rw [runBlock_syms eS, runBlock_syms eE]
  obtain mP : ∀ u < 8 * c.bw, s₁.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu =>
    f₁.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sPS.sub_right subMode)
      (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
  obtain mD : ∀ i < 8 * c.bw * n, s₁.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi =>
    f₁.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subMode) hn64 hi
  -- The IV into the first block.
  obtain hz₁ : isa.eval (.zero .x r.n) s₁ = some (decide (n = 0)) := by
    rw [eval_zero, g₁ _ ns' (Ne.symm hiv.n)]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  let Qw : State → Prop := fun s₂ => s₂.gpr sb = B ∧ (∀ x, x ≠ .x6 → x ≠ .x7 → s₂.gpr x = s₁.gpr x) ∧
    s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ Frame [⟨D, 8 * c.bw * n⟩] s₁.mem s₂.mem ∧
    ∀ q < n, ∀ r < 8 * c.bw, s₂.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
      if q = 0 then s₀.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) ^^^ s₀.mem (P + BitVec.ofNat 64 r)
      else s₀.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r))
  obtain hw : WP isa (c.cbcWhiten r) s₁ Qw := by
    unfold Core.cbcWhiten
    refine WP.ite (decide (n = 0)) hz₁ (fun h0 => ?_) (fun h0 => ?_)
    · exact WP.block_nil ⟨b₁, fun x _ _ => rfl, rfl, rfl, Frame.refl _ _, fun q hq => by simp at h0; omega_arith⟩
    · have hn0 : 0 < n := by simp at h0; omega_arith
      obtain sub0 : Region.Sub ⟨D + BitVec.ofNat 64 (8 * c.bw * 0), 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ :=
        VG.Offset.sub_base D (idx_lt hn0)
      refine WP.mono (xorN_wp (k := c.bw) (P := D + BitVec.ofNat 64 (8 * c.bw * 0)) (Q := P) (t := .x6) (u := .x7)
        ⟨by rw [g₁ _ ds' (Ne.symm hiv.data), hD]; simp, by rw [ctr₁]; simp, Ne.symm dd6,
          Ne.symm c6, Ne.symm dd7, Ne.symm c7,
          by decide, by decide, by omega_arith, by omega_arith, fun w hw' => ⟨_, by rw [wr₁]; exact hwD, by
            rw [addr_add]
            exact VG.Offset.contains_base D (by
              have := idx_lt (L := c.bw) hn0; rw [Nat.mul_zero] at this ⊢; have := Nat.mul_assoc 8 c.bw n; omega_arith)
              (by rw [Nat.mul_zero]; omega_arith)⟩,
          fun w hw' => by
            rw [rd₁, wr₁]
            exact inRd ⟨_, hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩,
          sPD.symm.sub_left sub0, by omega_arith⟩ (by decide)) fun s₂ h₂ => ?_
      refine ⟨by rw [h₂.regs _ (by decide) (by decide), b₁], fun x h1 h2 => h₂.regs x h1 h2, h₂.rd, h₂.wr, ?_,
        fun q hq r hr => ?_⟩
      · rw [h₂.mem]
        exact (over_frame _ _ _ _).sub fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_singleton_self _, sub0⟩
      rw [h₂.mem, over_blk _ _ _ hn0 hq hr hn64]
      split
      · rename_i h; subst h; rw [addr_add, mD _ (hqr hq hr), mP r hr]
      · exact mD _ (hqr hq hr)
  obtain hwK : KeepsReg ivR (c.cbcWhiten r) := by
    unfold Core.cbcWhiten
    exact KeepsReg.ite (keepsReg_of_regSafe rfl) (keepsReg_of_regSafe (flatMap_keepsReg (fun _ => xorW_keepsReg i6 i7) _))
  refine WP.seq (WP.mono_syms (WP.keepReg hwK hw) fun s₂ ⟨⟨b₂, g₂, rd₂, wr₂, f₂, d₂⟩, iv₂⟩ sy₂ => ?_)
  -- The data's address and `n`.
  obtain ⟨s₃, e₃, dr₃, lr₃, g₃, m₃, rd₃, wr₃⟩ := ctrArgs_ok s₂ r hdn hdl
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  obtain iv₃ : s₃.gpr ivR = P := by rw [g₃ _ idr ilr, iv₂, iv₁]
  obtain g₃' : ∀ x, x ∉ SetupRegs → x ≠ ivR → x ≠ c.dataReg → x ≠ c.leftReg → s₃.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 => by
      obtain ⟨h5, h6, h7, -⟩ := not_setupRegs h1
      rw [g₃ x h3 h4, g₂ x h6 h7, g₁ x h5 h2]
  obtain b₃ : s₃.gpr sb = B := by rw [g₃ _ (Ne.symm dsb) (Ne.symm lsb), b₂]
  obtain rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, rd₁]
  obtain wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, wr₁]
  obtain f₃ : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s₃.mem := by
    rw [m₃]
    exact (f₁.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_cons_self, subMode⟩).trans
      (f₂.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  obtain kr := keyRegs_ne cs.keyRegs_ok
  obtain hk₃ : cs.KeyArgs s₃ [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] k :=
    cs.keyArgs_congr hk (fun x hx => g₃' x (kr x hx) (fun e => hiv.key (e ▸ hx)) (fun e => dk (e ▸ hx))
      (fun e => lk (e ▸ hx))) rd₃' wr₃' (by rw [runBlock_syms e₃, sy₂, sy₁]) f₃
  -- The key.
  refine WP.seq (WP.mono (WP.keepReg hsc.1 (cs.prepare_wp b₃ ⟨by rw [wr₃']; exact hs.wr, hs.fit⟩
    List.mem_cons_self hk₃)) fun s₄ ⟨⟨ready₄, b₄, dr₄, lr₄, f₄, rd₄, wr₄⟩, iv₄⟩ => ?_)
  obtain rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃']
  obtain wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃']
  obtain ivR₄ : s₄.gpr ivR = P := by rw [iv₄, iv₃]
  obtain left₄ : s₄.gpr c.leftReg = s₀.gpr r.n := by rw [lr₄, lr₃, g₂ _ n6 n7, g₁ _ ns' (Ne.symm hiv.n)]
  obtain hz₄ : isa.eval (.zero .x c.leftReg) s₄ = some (decide (n = 0)) := by
    rw [eval_zero, left₄]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  let iv := bytesAt s₀.mem P (8 * c.bw)
  obtain hivl : iv.length = 8 * c.bw := by simp [iv, bytesAt]
  obtain hp : GPre c s₄ B D n (8 * c.bw) := ⟨⟨by rw [wr₄']; exact hs.wr, hs.fit⟩, by rw [wr₄']; exact hwD, sDS, fitD⟩
  obtain dCore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨D, 8 * c.bw * n⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right (Region.sub_prefix (by omega_arith))
  obtain m₄P : ∀ u < 8 * c.bw, s₄.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    rw [f₄.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact sPS.sub_right (Region.sub_prefix (by omega_arith))) (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu]
    exact f₃.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact sPS
        · exact sPD) (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
  -- The blocks, and the last back to the IV.
  refine WP.seq (WP.mono (M := isa) (Q := EDoneC cs s₄ s₀.mem B P D n k iv)
    (WP.ite (decide (n = 0)) hz₄ (fun h0 => ?_) (fun h0 => ?_)) fun s₆ d₆ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    subst hn0
    refine WP.block_nil ⟨b₄, fun _ _ => rfl, fun i hi' => by rw [Nat.mul_zero] at hi'; omega_arith,
      Frame.refl _ _, ?_, rfl, rfl⟩
    rw [show blocksOf (8 * c.bw) s₀.mem D 0 = [] from rfl, show Spec.Cbc.encrypt (cs.cipher k) iv [] = [] from rfl,
      next_nil]
    exact bytesAt_of_getD hivl fun u hu => by rw [m₄P u hu]; exact (bytesAt_getD _ _ hu).symm
  · have hn0 : n ≠ 0 := by simpa using h0
    refine WP.seq (WP.mono (WP.keepReg (KeepsReg.loop (keepsReg_cbcEncBlock hiv.mode hsc.2))
      (cbcEncLoop_wp cs (m₀ := s₀.mem) hivl hp ⟨b₄, ready₄, fun _ _ => rfl, ?_, ?_, by omega_arith, fun q hq r hr => ?_,
        Frame.refl _ _, rfl, rfl⟩)) fun s₆ ⟨d₆, iv₆⟩ => ?_)
    · rw [dr₄, dr₃, g₂ _ dd6 dd7, g₁ _ ds' (Ne.symm hiv.data), hD]; simp
    · rw [left₄, Nat.sub_zero, ← hn]; simp
    · rw [f₄.bytes (R := ⟨D, 8 * c.bw * n⟩) dCore hn64 (hqr hq hr), m₃, d₂ q hq r hr, encByte,
        ite_eq_right (Nat.not_lt_zero _)]
      split
      · rw [cbcEncPrev, ite_eq_left rfl, bytesAt_getD _ _ hr]
      · rfl
    -- The buffer, the last ciphertext block, back to the IV.
    obtain rd₆ : s₆.rd = s₀.rd := by rw [d₆.rd, rd₄']
    obtain wr₆ : s₆.wr = s₀.wr := by rw [d₆.wr, wr₄']
    obtain ivR₆ : s₆.gpr ivR = P := by rw [iv₆, ivR₄]
    refine WP.mono (copyN_wp (k := c.bw) (t := .x6) (u := .x6) (rd := ivR) (rs := sb) (od := 0)
      (os := 8 * c.buf) (P := P) (Q := T)
      ⟨by rw [ivR₆]; simp, by rw [d₆.base], Ne.symm i6, by decide, Ne.symm i6, by decide, by decide, by omega_arith,
        by omega_arith, by omega_arith, fun w hw => by rw [wr₆]; exact ⟨_, hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩,
        fun w hw => by
          rw [rd₆, wr₆, addr_add]
          exact inRd (inS (by omega_arith)),
        dTP.symm, by omega_arith⟩) fun s₇ h₇ => ?_
    have mem₇ : s₇.mem = over s₆.mem P (8 * c.bw) fun i => s₆.mem (T + BitVec.ofNat 64 i) := h₇.mem
    obtain f₇ : Frame [⟨P, 8 * c.bw⟩] s₆.mem s₇.mem := by rw [mem₇]; exact over_frame _ _ _ _
    refine ⟨by rw [h₇.regs _ (by decide) (by decide), d₆.base], fun i hi => ?_, fun i hi => ?_, ?_, ?_,
      by rw [h₇.rd, d₆.rd], by rw [h₇.wr, d₆.wr]⟩
    · rw [← d₆.saved i hi]
      exact f₇.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact (sPS.sub_right (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.total by
          omega_arith))).symm) (by decide)
    · rw [f₇.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact sPD.symm) hn64 hi]
      exact d₆.data i hi
    · exact (d₆.frame.mono fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self).trans
        (f₇.mono fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · rw [next_encrypt _ _ _ _ hn0]
      refine bytesAt_of_getD (by generalize n - 1 = t; cases t <;> exact cs.cipher_len k _) fun u hu => ?_
      rw [mem₇, over_at hu (by omega_arith)]
      exact d₆.last hn0 u hu
  -- The exit.
  obtain hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  obtain hinj : ∀ i < 10, ∀ j < 10, Core.savedRegs.getD i .x19 = Core.savedRegs.getD j .x19 → i = j := by decide
  obtain ⟨s₇, e₇, v₇, -, m₇, rd₇, wr₇⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₆
    d₆.base hsv hinj (by omega_arith) (fun i hi' => by
      rw [d₆.rd, d₆.wr, rd₄', wr₄']
      exact inRd (slot_wr hs.wr hN (by omega_arith)))
  refine WP.of_runBlock ⟨s₇, e₇, fun i hi' => ?_, ?_, ?_, ?_, by rw [rd₇, d₆.rd, rd₄'], by rw [wr₇, d₆.wr, wr₄']⟩
  · rw [v₇ i hi', d₆.saved i hi', ← sv₁ i hi']
    refine (f₄.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.disjoint_base B (by omega_arith) (by omega_arith)) (by decide)).trans ?_
    rw [m₃]
    exact f₂.readW (Region.contains_self _ _) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact (sDS.sub_right (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.total by
        omega_arith))).symm) (by decide)
  · rw [m₇]; exact cbcEnc_of_dinv (cs.cipher_len k) d₆.data
  · rw [m₇]; exact d₆.ivOut
  · rw [m₇]
    exact (((f₃.trans (f₄.sub fun x hx => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hx; subst hx; exact Region.sub_prefix (by omega_arith)⟩)).mono fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self)).trans d₆.frame

end VG.Proof.Modes.AArch64
