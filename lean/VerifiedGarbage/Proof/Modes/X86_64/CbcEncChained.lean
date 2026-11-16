module

public import VerifiedGarbage.Proof.Modes.CbcEnc
public import VerifiedGarbage.Impl.Modes.X86_64.CbcEnc
public import VerifiedGarbage.Proof.Modes.X86_64.Group
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Modes.X86_64.FbLoop
import VerifiedGarbage.Proof.Modes.CbcNext
public import VerifiedGarbage.Impl.Modes.X86_64.CbcChained
public import VerifiedGarbage.Proof.Modes.X86_64.Setup
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Modes.X86_64.Fb
import VerifiedGarbage.Proof.Modes.X86_64.Ctr
import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep

/-! ### `Modes.X86_64.CbcEncLoop`, which only this module used -/

section

/-!
# CBC encryption on x86-64, for any core: the data loop

`cbcEncBlock_wp`: one iteration encrypts block `j`, which holds
`Pⱼ ⊕ Cⱼ₋₁`, in the buffer (`encIn`, `BlockSpec.crypt_wp`), stores `Cⱼ`
back (`encOut`) and, unless it was the last, XORs it into block `j + 1`
(`encChain`). Each is `copyN_wp` or `xorN_wp`; blocks are `8 bw` bytes.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
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
  rsp : s.gpr .rsp = s₀.gpr .rsp
  ready : cs.Ready s B k
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * j)
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - j)
  lt : j < n
  data : ∀ q < n, ∀ r < 8 * c.bw, s.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
    encByte (8 * c.bw) (cs.cipher k) m₀ D iv j q r
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure EDone (cs : BlockSpec c) (s₀ : State) (m₀ : Mem) (B D : Addr) (n : Nat) (k : cs.Key) (iv : List Byte)
    (s : State) : Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv (8 * c.bw) m₀ s.mem D n n (cbcEncC (8 * c.bw) (cs.cipher k) m₀ D iv)
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  /-- The buffer's first block holds the last ciphertext block. -/
  last : n ≠ 0 → ∀ u < 8 * c.bw, s.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
    (cbcEncC (8 * c.bw) (cs.cipher k) m₀ D iv (n - 1)).getD u 0

theorem cbcEncBlock_wp (cs : BlockSpec c) {s₀ : State} {m₀ : Mem} {B D : Addr} {n : Nat} {k : cs.Key}
    {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : GPre c s₀ B D n (8 * c.bw)) {j : Nat} {s : State}
    (hi : EInv cs s₀ m₀ B D n k iv j s) :
    WP isa c.cbcEncBlock s fun s' => (s'.zf = some true ∧ EDone cs s₀ m₀ B D n k iv s') ∨
      (s'.zf = some false ∧ EInv cs s₀ m₀ B D n k iv (j + 1) s') := by
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
  obtain hL0 : 0 < 8 * c.bw := by omega_arith
  obtain hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  obtain hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  obtain hLG' : 8 * c.bw * c.G = 8 * (c.bw * c.G) := Nat.mul_assoc _ _ _
  obtain hLn : 8 * c.bw * n = 8 * (c.bw * n) := Nat.mul_assoc _ _ _
  obtain h8n : 8 * n ≤ 8 * c.bw * n := Nat.mul_le_mul_right n (by omega_arith)
  obtain hjl := idx_lt (L := 8 * c.bw) hj
  obtain hj1 : 8 * c.bw * (j + 1) = 8 * c.bw * j + 8 * c.bw := Nat.mul_succ _ _
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, -, -, -, -, dsb, dsp, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, -, -, -, -, lsb, lsp, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega_arith
  obtain p0 : ∀ X : Addr, X + BitVec.ofNat 64 0 = X := fun X => by simp
  let ciph := cs.cipher k
  let A := D + BitVec.ofNat 64 (8 * c.bw * j)
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  obtain hwS : (⟨B, 8 * c.ctrSlots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  obtain hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain subT : Region.Sub ⟨T, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩ :=
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith)
  obtain subTbuf : Region.Sub ⟨T, 8 * c.bw⟩ (blkRegion c B) := Region.sub_prefix hLG
  obtain subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.ctrSlots⟩ :=
    Region.sub_prefix (by simp only [Core.ctrSlots]; omega_arith)
  obtain subA : Region.Sub ⟨A, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ := VG.Offset.sub_base D hjl
  obtain dDS : ∀ {r : Region}, Region.Sub r ⟨B, 8 * c.ctrSlots⟩ → Region.Disjoint ⟨D, 8 * c.bw * n⟩ r :=
    fun h => hp.sep.sub_right h
  obtain dAT : Region.Disjoint ⟨A, 8 * c.bw⟩ ⟨T, 8 * c.bw⟩ := (dDS subT).sub_left subA
  obtain hw : ∀ w, 8 * c.bw * j + 8 * w = 8 * (c.bw * j + w) := fun w => by rw [Nat.mul_add, Nat.mul_assoc]
  obtain hbj : ∀ w < c.bw, c.bw * j + w < c.bw * n := fun w hw' => by have := idx_lt (L := c.bw) hj; omega_arith
  obtain inT : ∀ w < c.bw, InRegions s.wr (T + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
    ⟨_, hwS, by rw [addr_add]; exact VG.Offset.contains_base B (by simp only [Core.ctrSlots]; omega_arith) (by omega_arith)⟩
  obtain inA : ∀ w < c.bw, InRegions s.wr (A + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
    ⟨_, hwD, by rw [addr_add, hw]; exact VG.Offset.contains_base D (by have := hbj w hw'; omega_arith) (by have := hbj w hw'; omega_arith)⟩
  -- The data, outside the buffer and the core.
  obtain dT : ∀ q < n, ∀ r < 8 * c.bw, Region.Disjoint ⟨T, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ :=
    fun _ _ _ _ => (dDS subT).symm
  obtain hqr : ∀ {q r}, q < n → r < 8 * c.bw → 8 * c.bw * q + r < 8 * c.bw * n := fun hq hr => by
    have := idx_lt (L := 8 * c.bw) hq; omega_arith
  -- Block `j` to the buffer.
  unfold Core.cbcEncBlock
  refine WP.seq (WP.mono_syms (copyN_wp (k := c.bw) (P := T) (Q := A) ⟨by rw [hi.base], by rw [hi.dataR, p0],
    by decide, Ne.symm da, inT, fun w hw' => inRd (inA w hw'), dAT.symm, by omega_arith⟩) fun s₁ h₁ sy₁ => ?_)
  obtain base₁ : s₁.gpr sb = B := by rw [h₁.regs _ (by decide), hi.base]
  obtain f₁ : Frame [⟨T, 8 * c.bw⟩] s.mem s₁.mem := by rw [h₁.mem]; exact over_frame _ _ _ _
  obtain ready₁ : cs.Ready s₁ B k := cs.ready_frame hi.ready f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr subTbuf)
    ⟨fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, hwS, subT⟩, h₁.rd, h₁.wr, sy₁⟩ fun r hr => by
    obtain ⟨h1, -⟩ := of_not_modeRegs hr; exact h₁.regs r h1
  -- Encrypted.
  refine WP.seq (WP.mono (cs.crypt_wp base₁ ⟨by rw [h₁.wr]; exact hwS, hfit⟩ ready₁)
    fun s₂ ⟨base₂, rsp₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩ => ?_)
  rw [show s₁.gpr .rsp = s₀.gpr .rsp by rw [h₁.regs _ (by decide), hi.rsp]] at f₂
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
      rw [h₁.mem, over_at hv (by omega_arith)]
  obtain D₂ : ∀ q < n, ∀ r < 8 * c.bw, s₂.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
      s.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) := fun q hq r hr => by
    rw [f₂.bytes (R := ⟨D, 8 * c.bw * n⟩) (hp.stk.coreFrame_disj (dDS subCore) ⟨_, hp.dat, fun _ h => h⟩)
        hn64 (hqr hq hr), h₁.mem,
      over_sep (dDS subT).symm (hqr hq hr) hn64]
  -- Back to the data, and the count.
  obtain data₂ : s₂.gpr c.dataReg = A := by rw [dr₂, h₁.regs _ da, hi.dataR]
  refine WP.seq (WP.block_append (WP.mono_syms (copyN_wp (k := c.bw) (P := A) (Q := T) ⟨by rw [data₂, p0],
    by rw [base₂], Ne.symm da, by decide, fun w hw' => by rw [wr₂, h₁.wr]; exact inA w hw',
    fun w hw' => by rw [rd₂, wr₂, h₁.rd, h₁.wr]; exact inRd (inT w hw'), dAT, by omega_arith⟩) fun s₃a h₃a sy₃a => ?_))
  obtain ⟨s₃, e₃, l₃, z₃, o₃, m₃, rd₃, wr₃⟩ := subImm_ok s₃a c.leftReg 1
  refine WP.of_runBlock ⟨s₃, e₃, ?_⟩
  obtain left₂ : s₃a.gpr c.leftReg = BitVec.ofNat 64 (n - j) := by
    rw [h₃a.regs _ la, lr₂, h₁.regs _ la, hi.leftR]
  obtain left₃ : s₃.gpr c.leftReg = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [l₃, left₂, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat (by omega_arith), show n - j - 1 = n - (j + 1) by omega_arith]
  obtain hz₃ : s₃.zf = some (decide (j + 1 = n)) := by
    rw [z₃, left₂, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
    simp only [Option.some.injEq, decide_eq_decide]; omega_arith
  obtain g₃ : ∀ x, x ≠ .rax → x ≠ c.leftReg → s₃.gpr x = s₂.gpr x := fun x h1 h2 => by
    rw [o₃ x h2, h₃a.regs x h1]
  obtain base₃ : s₃.gpr sb = B := by rw [g₃ _ (by decide) (Ne.symm lsb), base₂]
  obtain data₃ : s₃.gpr c.dataReg = A := by rw [g₃ _ da hdl, data₂]
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
    fun u hu => by rw [mem₃, over_sep dAT hu (by omega_arith), C₂ u hu]
  -- The slots.
  obtain slotOut : ∀ i < 6, ∀ {R : Region}, (Region.Sub R ⟨D, 8 * c.bw * n⟩ ∨ R = ⟨T, 8 * c.bw⟩ ∨
      R = coreRegion c B) → Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ R := fun i hi6 R hR => by
    rcases hR with h | rfl | rfl
    · exact ((dDS (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by
        simp only [Core.ctrSlots]; omega_arith))).sub_left h).symm
    · exact VG.Offset.disjoint B (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact VG.Offset.disjoint_base B (by omega_arith) (by omega_arith)
  obtain saved₃ : ∀ i < 6, s₃.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi6 => by
    rw [← hi.saved i hi6]
    refine (f₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slotOut i hi6 (.inl subA)) (by decide)).trans ?_
    refine (f₂.readW (Region.contains_self _ _) (hp.stk.coreFrame_disj (slotOut i hi6 (.inr (.inr rfl)))
      ⟨_, hp.scr.wr, VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by
        simp only [Core.ctrSlots]; omega_arith)⟩) (by decide)).trans ?_
    exact f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slotOut i hi6 (.inr (.inl rfl))) (by decide)
  obtain fr₃ : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s₃.mem :=
    hi.frame.trans (((f₁.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; exact subT⟩).trans
      (f₂.sub (coreFrame_sub ⟨_, List.mem_cons_self, subCore⟩))).trans
      (f₃.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subA⟩))
  obtain rsp₃ : s₃.gpr .rsp = s₀.gpr .rsp := by
    rw [g₃ _ (by decide) (Ne.symm lsp), rsp₂, h₁.regs _ (by decide), hi.rsp]
  obtain rd₃' : s₃.rd = s₀.rd := by rw [rd₃, h₃a.rd, rd₂, h₁.rd, hi.rd]
  obtain wr₃' : s₃.wr = s₀.wr := by rw [wr₃, h₃a.wr, wr₂, h₁.wr, hi.wr]
  obtain ready₃ : cs.Ready s₃ B k := cs.ready_frame ready₂ f₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inl ((dDS subCore).sub_left subA).symm)
    ⟨fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by rw [wr₂, h₁.wr]; exact hwD, subA⟩,
      by rw [rd₃, h₃a.rd], by rw [wr₃, h₃a.wr], by rw [runBlock_syms e₃, sy₃a]⟩ fun r hr => by
    obtain ⟨h1, -, -, -, -, -, h7⟩ := of_not_modeRegs hr; exact g₃ r h1 h7
  -- The last block, or on to the next.
  obtain hAL : A + BitVec.ofNat 64 (8 * c.bw) = D + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := by rw [addr_add, hj1]
  refine WP.seq (WP.mono_syms (Q := fun s₄ => (∀ x, x ≠ .rax → s₄.gpr x = s₃.gpr x) ∧ s₄.rd = s₃.rd ∧
      s₄.wr = s₃.wr ∧ (j + 1 = n → s₄.mem = s₃.mem) ∧ (j + 1 < n → s₄.mem = over s₃.mem (D + BitVec.ofNat 64 (8 * c.bw * (j + 1))) (8 * c.bw)
        fun i => s₃.mem ((D + BitVec.ofNat 64 (8 * c.bw * (j + 1))) + BitVec.ofNat 64 i) ^^^ s₃.mem (T + BitVec.ofNat 64 i)))
    (WP.ite (decide (j + 1 = n)) (by simp [X86_64.eval, hz₃]) (fun h => ?_) (fun h => ?_)) fun s₄ h₄ sy₄ => ?_)
  · exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, fun _ => rfl, fun h' => by simp at h; omega_arith⟩
  · have hjn : j + 1 < n := by simp at h; omega_arith
    obtain hjl' := idx_lt (L := 8 * c.bw) hjn
    obtain subN' : Region.Sub ⟨D + BitVec.ofNat 64 (8 * c.bw * (j + 1)), 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ :=
      VG.Offset.sub_base D hjl'
    obtain hw' : ∀ w, 8 * c.bw * (j + 1) + 8 * w = 8 * (c.bw * (j + 1) + w) := fun w => by
      rw [Nat.mul_add 8, Nat.mul_assoc]
    obtain hbj' : ∀ w < c.bw, c.bw * (j + 1) + w < c.bw * n := fun w hw'' => by
      have := idx_lt (L := c.bw) hjn; omega_arith
    exact WP.mono (xorN_wp (k := c.bw) (P := D + BitVec.ofNat 64 (8 * c.bw * (j + 1))) (Q := T)
      ⟨by rw [data₃, hAL], by rw [base₃], Ne.symm da, by decide, fun w hw'' => ⟨_, by rw [wr₃', ← hi.wr]; exact hwD, by
        rw [addr_add, hw']
        exact VG.Offset.contains_base D (by have := hbj' w hw''; omega_arith) (by have := hbj' w hw''; omega_arith)⟩,
      fun w hw'' => by rw [rd₃', wr₃', ← hi.rd, ← hi.wr]; exact inRd (inT w hw''),
      (dDS subT).sub_left subN', by omega_arith⟩) fun s₄ h₄ =>
      ⟨h₄.regs, h₄.rd, h₄.wr, fun h' => by omega_arith, fun _ => h₄.mem⟩
  obtain ⟨g₄, rd₄, wr₄, mDone, mMore⟩ := h₄
  obtain ⟨s₅, e₅, a₅, o₅, m₅, rd₅, wr₅⟩ := addImm_ok s₄ c.dataReg (BitVec.ofNat 32 (8 * c.bw))
  obtain ⟨s₆, e₆, z₆, g₆, m₆, rd₆, wr₆⟩ := testSelf_ok s₅ c.leftReg
  refine WP.of_runBlock ⟨s₆, by
    rw [Core.encNext, show ([.alu .add c.dataReg (.imm (BitVec.ofNat 32 (8 * c.bw))),
      .alu .test c.leftReg (.reg c.leftReg)] : List Instr) = [.alu .add c.dataReg (.imm (BitVec.ofNat 32 (8 * c.bw)))] ++
      [.alu .test c.leftReg (.reg c.leftReg)] from rfl, runBlock_app, e₅, Option.bind_some, e₆], ?_⟩
  obtain keep₆ : ∀ x, x ≠ .rax → x ≠ c.dataReg → s₆.gpr x = s₃.gpr x := fun x h1 h2 => by
    rw [g₆, o₅ x h2, g₄ x h1]
  obtain left₆ : s₆.gpr c.leftReg = BitVec.ofNat 64 (n - (j + 1)) := by rw [keep₆ _ la (Ne.symm hdl), left₃]
  obtain hz : s₆.zf = some (decide (j + 1 = n)) := by
    rw [z₆, ← g₆, keep₆ _ la (Ne.symm hdl), l₃, left₂, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
    simp only [Option.some.injEq, decide_eq_decide]; omega_arith
  obtain mem₆ : s₆.mem = s₄.mem := by rw [m₆, m₅]
  obtain base₆ : s₆.gpr sb = B := by rw [keep₆ _ (by decide) (Ne.symm dsb), base₃]
  obtain rsp₆ : s₆.gpr .rsp = s₀.gpr .rsp := by rw [keep₆ _ (by decide) (Ne.symm dsp), rsp₃]
  obtain rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, rd₃']
  obtain wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, wr₃']
  by_cases hdone : j + 1 = n
  · have hm : s₆.mem = s₃.mem := by rw [mem₆, mDone hdone]
    refine .inl ⟨by rw [hz, decide_eq_true hdone], base₆, rsp₆, by rw [hm]; exact saved₃,
      dinv_of_blocks hL0 fun q hq r hr => ?_, by rw [hm]; exact fr₃, rd₆', wr₆',
      fun _ u hu => by rw [hm, ← hdone, Nat.add_sub_cancel]; exact T₃ u hu⟩
    rw [hm, D₃ q hq r hr, ite_eq_left hq]
    split
    · rename_i h; subst h; rfl
    · rw [hi.data q hq r hr, encByte, ite_eq_left (by omega_arith)]
  · have hjn : j + 1 < n := by omega_arith
    obtain hm := mMore hjn
    rw [← mem₆] at hm
    obtain subN : Region.Sub ⟨D + BitVec.ofNat 64 (8 * c.bw * (j + 1)), 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ :=
      VG.Offset.sub_base D (idx_lt hjn)
    obtain fN : Frame [⟨D + BitVec.ofNat 64 (8 * c.bw * (j + 1)), 8 * c.bw⟩] s₃.mem s₆.mem := by
      rw [hm]; exact over_frame _ _ _ _
    refine .inr ⟨by rw [hz, decide_eq_false hdone], base₆, rsp₆, ?_, fun i hi6 => ?_, ?_, left₆, hjn,
      fun q hq r hr => ?_, fr₃.trans (fN.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subN⟩), rd₆', wr₆'⟩
    · exact cs.ready_frame ready₃ fN (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inl ((dDS subCore).sub_left subN).symm)
        ⟨fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by rw [wr₃', ← hi.wr]; exact hwD, subN⟩,
          by rw [rd₆', rd₃'], by rw [wr₆', wr₃'], by rw [runBlock_syms e₆, runBlock_syms e₅, sy₄]⟩
        fun r hr => by obtain ⟨h1, -, -, -, -, h6, -⟩ := of_not_modeRegs hr; exact keep₆ r h1 h6
    · rw [← saved₃ i hi6]
      exact fN.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact slotOut i hi6 (.inl subN)) (by decide)
    · rw [g₆, a₅, g₄ _ da, data₃, signExtend_small (by omega_arith), hAL]
    · rw [hm, over_blk _ _ _ hjn hq hr hn64]
      split
      · rename_i h; subst h
        rw [addr_add, D₃ _ hjn r hr, ite_eq_right (by omega_arith), hi.data _ hjn r hr, T₃ r hr, encByte,
          ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), encByte, ite_eq_right (Nat.lt_irrefl _),
          ite_eq_left rfl, cbcEncPrev, ite_eq_right (by omega_arith), Nat.add_sub_cancel]
      · rename_i h
        rw [D₃ q hq r hr]
        split
        · rename_i h'; subst h'; rw [encByte, ite_eq_left (by omega_arith)]
        · rename_i h'
          rw [hi.data q hq r hr, encByte, encByte]
          by_cases h3 : q < j
          · rw [ite_eq_left h3, ite_eq_left (by omega_arith)]
          · rw [ite_eq_right h3, ite_eq_right h', ite_eq_right (show ¬ q < j + 1 by omega_arith), ite_eq_right h]

/-- The data loop. -/
theorem cbcEncLoop_wp (cs : BlockSpec c) {s₀ : State} {m₀ : Mem} {B D : Addr} {n : Nat} {k : cs.Key}
    {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : GPre c s₀ B D n (8 * c.bw)) {s : State}
    (hi : EInv cs s₀ m₀ B D n k iv 0 s) :
    WP isa (.loop c.cbcEncBlock .ne) s (EDone cs s₀ m₀ B D n k iv) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = n - j ∧ EInv cs s₀ m₀ B D n k iv j s) (fun m s hs => ?_) n s
    ⟨0, by simp, hi⟩
  obtain ⟨j, rfl, hj⟩ := hs
  refine WP.mono (cbcEncBlock_wp cs hiv hp hj) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩
  · exact .inr ⟨by simp [X86_64.eval, z], n - (j + 1), by have := d.lt; have := hj.lt; omega_arith, j + 1, rfl, d⟩

end VG.Proof.Modes.X86_64

end

end


/-!
# CBC encryption on x86-64 that updates the chaining value, for any core

`cbcEncryptChained_wp`: `c.cbcEncryptChained r` is CBC encryption of the
data, which also replaces the IV at `P` with the last
ciphertext block (`Spec.Cbc.next`): the IV's address stays in `ivX`, which
the core's `prepare` and `crypt` keep (`KeepsIv`, as for OFB and CFB), and
after the last block the buffer, which still holds it (`EDone.last`), is
copied back to the IV. `keepsIv_seq`, `keepsIv_ite` and `keepsIv_loop`
carry `KeepsIv` through the data loop.
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

/-! ## `KeepsIv` of composite code -/

theorem keepsIv_seq {a b : Prog isa} (ha : KeepsIv a) (hb : KeepsIv b) : KeepsIv (.seq a b) := by
  intro s t s' e hz
  cases e with
  | seq e₁ e₂ =>
    obtain h₁ := ha _ _ _ e₁ hz
    rw [hb _ _ _ e₂ (by rw [h₁]; exact hz), h₁]

theorem keepsIv_ite {cc : Cond} {a b : Prog isa} (ha : KeepsIv a) (hb : KeepsIv b) : KeepsIv (.ite cc a b) := by
  intro s t s' e hz
  cases e with
  | iteT _ e₁ => exact ha _ _ _ e₁ hz
  | iteF _ e₁ => exact hb _ _ _ e₁ hz

theorem keepsIv_loop {b : Prog isa} {cc : Cond} (hb : KeepsIv b) : KeepsIv (.loop b cc) := by
  intro s t s' e
  generalize hp : (Code.loop b cc : Prog isa) = p at e
  induction e with
  | icall | icallNext => cases hp
  | loopExit e₁ _ => cases hp; exact hb _ _ _ e₁
  | loopNext e₁ _ _ _ ih =>
    cases hp
    intro hz
    obtain h₁ := hb _ _ _ e₁ hz
    rw [ih rfl (by rw [h₁]; exact hz), h₁]
  | block => cases hp
  | seq => cases hp
  | iteT => cases hp
  | iteF => cases hp
  | call => cases hp
  | frame => cases hp

theorem keepsIv_cbcEncBlock {c : Core} (h : KeepsIv c.crypt) : KeepsIv c.cbcEncBlock := by
  obtain hOut : scalCode (.block c.encOut) = true := by
    simp only [scalCode, Core.encOut, List.all_append, flatMap_scal (copyW_scal _ _ _ _ _), Bool.true_and]; rfl
  exact keepsIv_seq (keepsIv_of_scal (flatMap_scal (copyW_scal _ _ _ _ _) _)) (keepsIv_seq h
    (keepsIv_seq (keepsIv_of_scal hOut) (keepsIv_seq (keepsIv_ite (keepsIv_of_scal rfl)
      (keepsIv_of_scal (flatMap_scal (xorW_scal _ _ _ _ _) _))) (keepsIv_of_scal rfl))))

/-! ## The whole function -/

variable {c : Core}

/-- After the blocks: `EDone`, the IV written as well. -/
structure EDoneC (cs : BlockSpec c) (s₀ : State) (m₀ : Mem) (B P D : Addr) (n : Nat) (k : cs.Key)
    (iv : List Byte) (s : State) : Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv (8 * c.bw) m₀ s.mem D n n (cbcEncC (8 * c.bw) (cs.cipher k) m₀ D iv)
  frame : Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩, ⟨P, 8 * c.bw⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s.mem
  ivOut : bytesAt s.mem P (8 * c.bw) = Spec.Cbc.next iv (Spec.Cbc.encrypt (cs.cipher k) iv (blocksOf (8 * c.bw) m₀ D n))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem cbcEncryptChained_wp (cs : BlockSpec c) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n)
    {s₀ : State} {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B) (hP : s₀.gpr r.ctr = P)
    (hD : s₀.gpr r.data = D) (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.ctrSlots)
    (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr)
    (hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s₀.wr) (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sDS : Region.Disjoint ⟨D, 8 * c.bw * n⟩ ⟨B, 8 * c.ctrSlots⟩)
    (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩) (fitD : D.toNat + 8 * c.bw * n ≤ 2 ^ 64)
    (hk : cs.KeyArgs s₀ [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] k)
    (hsc : KeepsIv c.prepare ∧ KeepsIv c.crypt) (hstk : StkOk c s₀ := by exact Or.inl rfl) :
    WP isa (c.cbcEncryptChained r) s₀ fun s' => (∀ x ∈ calleeSaved, s'.gpr x = s₀.gpr x) ∧
      blocksOf (8 * c.bw) s'.mem D n =
        Spec.Cbc.encrypt (cs.cipher k) (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n) ∧
      bytesAt s'.mem P (8 * c.bw) = Spec.Cbc.next (bytesAt s₀.mem P (8 * c.bw))
        (Spec.Cbc.encrypt (cs.cipher k) (bytesAt s₀.mem P (8 * c.bw)) (blocksOf (8 * c.bw) s₀.mem D n)) ∧
      Frame ([⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩, ⟨P, 8 * c.bw⟩] ++ stkList c (s₀.gpr .rsp)) s₀.mem s'.mem ∧
      s'.rd = s₀.rd ∧
      s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  obtain hL0 : 0 < 8 * c.bw := by omega_arith
  obtain hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  obtain hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  obtain h8n : 8 * n ≤ 8 * c.bw * n := Nat.mul_le_mul_right n (by omega_arith)
  obtain hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega_arith
  obtain hLn : 8 * c.bw * n = 8 * (c.bw * n) := Nat.mul_assoc _ _ _
  obtain hqr : ∀ {q r}, q < n → r < 8 * c.bw → 8 * c.bw * q + r < 8 * c.bw * n := fun hq hr => by
    have := idx_lt (L := 8 * c.bw) hq; omega_arith
  obtain hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega_arith
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, db, -, -, -, dsb, dsp, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, lb, -, -, -, lsb, lsp, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  let S : Region := ⟨B, 8 * c.ctrSlots⟩
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  obtain subMode : Region.Sub (modeRegion c B) S := VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith)
  obtain subT : Region.Sub ⟨T, 8 * c.bw⟩ S := VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega_arith)
  obtain dTP : Region.Disjoint ⟨T, 8 * c.bw⟩ ⟨P, 8 * c.bw⟩ := (sPS.sub_right subT).symm
  obtain inS : ∀ {d m : Nat}, d + m ≤ 8 * c.ctrSlots → InRegions s₀.wr (B + BitVec.ofNat 64 d) m := fun h =>
    ⟨_, hs.wr, VG.Offset.contains_base B h (by omega_arith)⟩
  -- The entry, and the IV's address to `ivX`.
  obtain ⟨sE, eE, b₁, sv₁, f₁, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  obtain ⟨s₁, eS, xS, gS, mS, rdS, wrS⟩ := movqX_ok sE Core.ivX r.ctr
  obtain g₁ : ∀ x, x ≠ sb → s₁.gpr x = s₀.gpr x := fun x h => by rw [gS, gE x h]
  obtain x₁ : s₁.xmm Core.ivX = (0 : BitVec 64) ++ P := by rw [xS, gE _ hr.ctr.1, hP]
  unfold Core.cbcEncryptChained
  refine WP.seq (WP.of_runBlock ⟨s₁, by rw [runBlock_app, eE, Option.bind_some, eS], ?_⟩)
  obtain b₁ : s₁.gpr sb = B := by rw [gS, b₁]
  obtain sv₁ : ∀ i < 6, s₁.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .rbx) :=
    fun i hi => by rw [mS, sv₁ i hi]
  obtain f₁ : Frame [modeRegion c B] s₀.mem s₁.mem := by rw [mS]; exact f₁
  obtain rd₁ : s₁.rd = s₀.rd := by rw [rdS, rdE]
  obtain wr₁ : s₁.wr = s₀.wr := by rw [wrS, wrE]
  obtain sy₁ : s₁.syms = s₀.syms := by rw [runBlock_syms eS, runBlock_syms eE]
  obtain mP : ∀ u < 8 * c.bw, s₁.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu =>
    f₁.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sPS.sub_right subMode) (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
  obtain mD : ∀ i < 8 * c.bw * n, s₁.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi =>
    f₁.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subMode) hn64 hi
  -- The IV into the first block.
  obtain ⟨s₂a, e₂a, z₂a, g₂a, m₂a, rd₂a, wr₂a⟩ := testSelf_ok s₁ r.n
  obtain hz₂ : s₂a.zf = some (decide (n = 0)) := by
    rw [z₂a, g₁ _ hr.n.1]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  let Qw : State → Prop := fun s₂ => s₂.gpr sb = B ∧ (∀ x, x ≠ .rax → s₂.gpr x = s₁.gpr x) ∧ s₂.rd = s₁.rd ∧
    s₂.wr = s₁.wr ∧ Frame [⟨D, 8 * c.bw * n⟩] s₁.mem s₂.mem ∧
    ∀ q < n, ∀ r < 8 * c.bw, s₂.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
      if q = 0 then s₀.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) ^^^ s₀.mem (P + BitVec.ofNat 64 r)
      else s₀.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r))
  obtain hw : WP isa (c.cbcWhiten r) s₁ Qw := by
    unfold Core.cbcWhiten
    refine WP.seq (WP.of_runBlock ⟨s₂a, e₂a, WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₂])
      (fun h0 => ?_) (fun h0 => ?_)⟩)
    · exact WP.block_nil ⟨by rw [g₂a, b₁], fun x _ => by rw [g₂a], rd₂a, wr₂a, by rw [m₂a]; exact Frame.refl _ _,
        fun q hq => by simp at h0; omega_arith⟩
    · have hn0 : 0 < n := by simp at h0; omega_arith
      obtain sub0 : Region.Sub ⟨D + BitVec.ofNat 64 (8 * c.bw * 0), 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ :=
        VG.Offset.sub_base D (idx_lt hn0)
      refine WP.mono (xorN_wp (k := c.bw) (P := D + BitVec.ofNat 64 (8 * c.bw * 0)) (Q := P)
        ⟨by rw [g₂a, g₁ _ hr.data.1, hD]; simp, by rw [g₂a, g₁ _ hr.ctr.1, hP]; simp, Ne.symm hr.data.2.1,
          Ne.symm hr.ctr.2.1, fun w hw' => ⟨_, by rw [wr₂a, wr₁]; exact hwD, by
            rw [addr_add]
            exact VG.Offset.contains_base D (by have := idx_lt (L := c.bw) hn0; omega_arith) (by omega_arith)⟩,
          fun w hw' => by
            rw [rd₂a, wr₂a, rd₁, wr₁]
            exact inRd ⟨_, hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩,
          sPD.symm.sub_left sub0, by omega_arith⟩) fun s₂ h₂ => ?_
      refine ⟨by rw [h₂.regs _ (by decide), g₂a, b₁], fun x hx => by rw [h₂.regs x hx, g₂a], by rw [h₂.rd, rd₂a],
        by rw [h₂.wr, wr₂a], ?_, fun q hq r hr => ?_⟩
      · rw [h₂.mem, m₂a]
        exact (over_frame _ _ _ _).sub fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_singleton_self _, sub0⟩
      rw [h₂.mem, m₂a, over_blk _ _ _ hn0 hq hr hn64]
      split
      · rename_i h; subst h; rw [addr_add, mD _ (hqr hq hr), mP r hr]
      · exact mD _ (hqr hq hr)
  obtain hwS : scalCode (c.cbcWhiten r) = true := by
    simp only [scalCode, Core.cbcWhiten, Bool.and_eq_true]
    exact ⟨rfl, rfl, flatMap_scal (xorW_scal _ _ _ _ _) _⟩
  refine WP.seq (WP.mono_syms (WP.vecKeep hwS hw) fun s₂ ⟨⟨b₂, g₂, rd₂, wr₂, f₂, d₂⟩, x₂, _⟩ sy₂ => ?_)
  -- The data's address and `n`.
  obtain ⟨s₃, e₃, dr₃, lr₃, g₃, m₃, rd₃, wr₃⟩ := ctrArgs_ok s₂ r hdn hdl
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  obtain x₃ : s₃.xmm Core.ivX = (0 : BitVec 64) ++ P := by rw [runBlock_vec rfl e₃, x₂, x₁]
  obtain g₃' : ∀ x, x ≠ sb → x ≠ .rax → x ≠ c.dataReg → x ≠ c.leftReg → s₃.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 => by rw [g₃ x h3 h4, g₂ x h2, g₁ x h1]
  obtain b₃ : s₃.gpr sb = B := by rw [g₃ _ (Ne.symm dsb) (Ne.symm lsb), b₂]
  obtain rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, rd₁]
  obtain wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, wr₁]
  obtain f₃ : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s₃.mem := by
    rw [m₃]
    exact (f₁.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_cons_self, subMode⟩).trans
      (f₂.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  obtain kr := keyRegs_ne cs.keyRegs_ok
  obtain hk₃ : cs.KeyArgs s₃ [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] k :=
    cs.keyArgs_congr hk (fun x hx => g₃' x (kr x hx).1 (kr x hx).2.1 (fun e => dk (e ▸ hx))
      (fun e => lk (e ▸ hx))) rd₃' wr₃'
      (by rw [runBlock_syms e₃, sy₂, sy₁]) f₃
  -- The key.
  refine WP.seq (WP.mono (WP.keepIv hsc.1 (by rw [x₃]; exact hi_zero_append _)
    (cs.prepare_wp b₃ ⟨by rw [wr₃']; exact hs.wr, hs.fit⟩ List.mem_cons_self hk₃))
    fun s₄ ⟨⟨ready₄, b₄, rsp₄, dr₄, lr₄, f₄, rd₄, wr₄⟩, x₄⟩ => ?_)
  rw [show s₃.gpr .rsp = s₀.gpr .rsp from g₃' _ (by decide) (by decide) (Ne.symm dsp) (Ne.symm lsp)] at f₄
  obtain rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃']
  obtain wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃']
  -- Any blocks?
  obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := testSelf_ok s₄ c.leftReg
  refine WP.seq (WP.of_runBlock ⟨s₅, e₅, ?_⟩)
  obtain x₅ : s₅.xmm Core.ivX = (0 : BitVec 64) ++ P := by rw [runBlock_vec rfl e₅, x₄, x₃]
  obtain left₅ : s₅.gpr c.leftReg = s₀.gpr r.n := by
    rw [g₅, lr₄, lr₃, g₂ _ hr.n.2.1, g₁ _ hr.n.1]
  obtain hz₅ : s₅.zf = some (decide (n = 0)) := by
    rw [z₅, ← g₅, left₅]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  have mem₅ : s₅.mem = s₄.mem := m₅
  obtain b₅ : s₅.gpr sb = B := by rw [g₅, b₄]
  obtain rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by
    rw [g₅, rsp₄, g₃' _ (by decide) (by decide) (Ne.symm dsp) (Ne.symm lsp)]
  obtain rd₅' : s₅.rd = s₀.rd := by rw [rd₅, rd₄']
  obtain wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄']
  let iv := bytesAt s₀.mem P (8 * c.bw)
  obtain hiv : iv.length = 8 * c.bw := by simp [iv, bytesAt]
  obtain hp : GPre c s₅ B D n (8 * c.bw) :=
    ⟨⟨by rw [wr₅']; exact hs.wr, hs.fit⟩, by rw [wr₅']; exact hwD, sDS, fitD, hstk.congr rsp₅ wr₅'⟩
  obtain dCore : ∀ x ∈ coreFrame c B (s₀.gpr .rsp), Region.Disjoint ⟨D, 8 * c.bw * n⟩ x :=
    hstk.coreFrame_disj (sDS.sub_right (Region.sub_prefix (by simp only [Core.ctrSlots]; omega_arith)))
      ⟨_, hwD, fun _ h => h⟩
  -- The IV as it was before the loop.
  obtain m₅P : ∀ u < 8 * c.bw, s₅.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    rw [mem₅, f₄.bytes (R := ⟨P, 8 * c.bw⟩) (hstk.coreFrame_disj
        (sPS.sub_right (Region.sub_prefix (by simp only [Core.ctrSlots]; omega_arith))) ⟨_, hwP, fun _ h => h⟩)
        (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu]
    exact f₃.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact sPS
        · exact sPD) (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
  -- The blocks, and the last back to the IV.
  refine WP.seq (WP.mono (M := isa) (Q := EDoneC cs s₅ s₀.mem B P D n k iv)
    (WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₅]) (fun h0 => ?_) (fun h0 => ?_)) fun s₆ d₆ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    subst hn0
    refine WP.block_nil ⟨b₅, rfl, fun _ _ => rfl, fun i hi' => by rw [Nat.mul_zero] at hi'; omega_arith,
      Frame.refl _ _, ?_, rfl, rfl⟩
    rw [show blocksOf (8 * c.bw) s₀.mem D 0 = [] from rfl, show Spec.Cbc.encrypt (cs.cipher k) iv [] = [] from rfl,
      next_nil]
    exact bytesAt_of_getD hiv fun u hu => by rw [m₅P u hu]; exact (bytesAt_getD _ _ hu).symm
  · have hn0 : n ≠ 0 := by simpa using h0
    refine WP.seq (WP.mono (WP.keepIv (keepsIv_loop (keepsIv_cbcEncBlock hsc.2)) (by rw [x₅]; exact hi_zero_append _)
      (cbcEncLoop_wp cs (m₀ := s₀.mem) hiv hp ⟨b₅, rfl, cs.ready_frame ready₄ (by rw [mem₅]; exact Frame.refl [] _)
        (fun _ h => by simp at h) ⟨fun _ h => by simp at h, rd₅, wr₅, runBlock_syms e₅⟩ (fun r _ => by rw [g₅]),
        fun _ _ => rfl, ?_, ?_, by omega_arith, fun q hq r hr => ?_, Frame.refl _ _, rfl, rfl⟩))
      fun s₆ ⟨d₆, x₆⟩ => ?_)
    · rw [g₅, dr₄, dr₃, g₂ _ hr.data.2.1, g₁ _ hr.data.1, hD]; simp
    · rw [left₅, Nat.sub_zero, ← hn]; simp
    · rw [mem₅, f₄.bytes (R := ⟨D, 8 * c.bw * n⟩) dCore hn64 (hqr hq hr), m₃, d₂ q hq r hr, encByte,
        ite_eq_right (Nat.not_lt_zero _)]
      split
      · rw [cbcEncPrev, ite_eq_left rfl, bytesAt_getD _ _ hr]
      · rfl
    -- The buffer, the last ciphertext block, back to the IV.
    obtain rd₆ : s₆.rd = s₀.rd := by rw [d₆.rd, rd₅']
    obtain wr₆ : s₆.wr = s₀.wr := by rw [d₆.wr, wr₅']
    obtain ⟨s₇a, e₇a, ax₇a, o₇a, m₇a, rd₇a, wr₇a, -⟩ := movqR_ok s₆ .rax Core.ivX
    obtain ax₇ : s₇a.gpr .rax = P := by rw [ax₇a, x₆, x₅, extract_zero_append]
    refine WP.block_append (WP.of_runBlock ⟨s₇a, e₇a, WP.mono (copyN_wp (k := c.bw)
      (t := .rbp) (rd := .rax) (rs := sb) (od := 0) (os := 8 * c.buf) (P := P) (Q := T)
      ⟨by rw [ax₇]; simp, by rw [o₇a _ (by decide), d₆.base], by decide, by decide,
        fun w hw => by rw [wr₇a, wr₆]; exact ⟨_, hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩,
        fun w hw => by
          rw [rd₇a, wr₇a, rd₆, wr₆, addr_add]
          exact inRd (inS (by simp only [Core.ctrSlots]; omega_arith)),
        dTP.symm, by omega_arith⟩) fun s₇ h₇ => ?_⟩)
    obtain mem₇ : s₇.mem = over s₆.mem P (8 * c.bw) fun i => s₆.mem (T + BitVec.ofNat 64 i) := by rw [h₇.mem, m₇a]
    obtain f₇ : Frame [⟨P, 8 * c.bw⟩] s₆.mem s₇.mem := by rw [mem₇]; exact over_frame _ _ _ _
    refine ⟨by rw [h₇.regs _ (by decide), o₇a _ (by decide), d₆.base],
      by rw [h₇.regs _ (by decide), o₇a _ (by decide), d₆.rsp], fun i hi => ?_, fun i hi => ?_, ?_, ?_,
      by rw [h₇.rd, rd₇a, d₆.rd], by rw [h₇.wr, wr₇a, d₆.wr]⟩
    · rw [← d₆.saved i hi]
      exact f₇.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact (sPS.sub_right (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by
          simp only [Core.ctrSlots]; omega_arith))).symm) (by decide)
    · rw [f₇.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact sPD.symm) hn64 hi]
      exact d₆.data i hi
    · exact (d₆.frame.mono fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_append_right _ hx).trans
        (f₇.mono fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · rw [next_encrypt _ _ _ _ hn0]
      refine bytesAt_of_getD (by generalize n - 1 = t; cases t <;> exact cs.cipher_len k _) fun u hu => ?_
      rw [mem₇, over_at hu (by omega_arith)]
      exact d₆.last hn0 u hu
  -- The exit.
  obtain hsv : ∀ i < 6, Core.savedRegs.getD i .rbx ≠ sb := by decide
  obtain hinj : ∀ i < 6, ∀ j < 6, Core.savedRegs.getD i .rbx = Core.savedRegs.getD j .rbx → i = j := by decide
  obtain ⟨s₈, e₈, v₈, o₈, m₈, rd₈, wr₈⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .rbx) 6 s₆
    d₆.base hsv hinj (fun i hi' => by
      rw [d₆.rd, d₆.wr, rd₅', wr₅']
      exact inRd (slot_wr hs.wr hN (by simp only [Core.ctrSlots]; omega_arith)))
  refine WP.of_runBlock ⟨s₈, e₈, fun x hx => ?_, ?_, ?_, ?_, by rw [rd₈, d₆.rd, rd₅'], by rw [wr₈, d₆.wr, wr₅']⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain hsaved : ∀ i < 6, s₈.gpr (Core.savedRegs.getD i .rbx) = s₀.gpr (Core.savedRegs.getD i .rbx) :=
      fun i hi' => by
        rw [v₈ i hi', d₆.saved i hi', mem₅, ← sv₁ i hi']
        refine (f₄.readW (Region.contains_self _ _) (hstk.coreFrame_disj
          (VG.Offset.disjoint_base B (by omega_arith) (by omega_arith)) ⟨_, hs.wr, VG.Offset.sub_base B
            (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by simp only [Core.ctrSlots]; omega_arith)⟩) (by decide)).trans ?_
        rw [m₃]
        exact f₂.readW (Region.contains_self _ _) (fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx
          exact (sDS.sub_right (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by
            simp only [Core.ctrSlots]; omega_arith))).symm) (by decide)
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0 (by decide)
    · exact hsaved 1 (by decide)
    · rw [o₈ _ (fun i hi' => by revert i; decide), d₆.rsp, rsp₅]
    · exact hsaved 2 (by decide)
    · exact hsaved 3 (by decide)
    · exact hsaved 4 (by decide)
    · exact hsaved 5 (by decide)
  · rw [m₈]; exact cbcEnc_of_dinv (cs.cipher_len k) d₆.data
  · rw [m₈]; exact d₆.ivOut
  · rw [m₈]
    refine ((((f₃.mono fun x hx => List.mem_append_left _ hx).trans
      (f₄.sub (coreFrame_sub (rs := [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩]) ⟨_, List.mem_cons_self,
        Region.sub_prefix (by simp only [Core.ctrSlots]; omega_arith)⟩))).mono fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_append_right _ hx)).trans ?_
    rw [← mem₅, ← rsp₅]
    exact d₆.frame

end VG.Proof.Modes.X86_64
