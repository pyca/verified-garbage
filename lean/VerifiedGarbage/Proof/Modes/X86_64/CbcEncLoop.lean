import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
import VerifiedGarbage.Proof.Modes.CbcEnc
import VerifiedGarbage.Impl.Modes.X86_64.CbcEnc

/-!
# CBC encryption on x86-64, for any core: the data loop

`cbcEncBlock_wp`: one iteration encrypts block `j`, which holds
`Pⱼ ⊕ Cⱼ₋₁`, in the buffer (`encIn`, `BlockSpec.crypt_wp`), stores `Cⱼ`
back (`encOut`) and, unless it was the last, XORs it into block `j + 1`
(`encChain`). Each is `copyN_wp` or `xorN_wp`; blocks are `8 bw` bytes.
-/

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
  frame : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure EDone (cs : BlockSpec c) (s₀ : State) (m₀ : Mem) (B D : Addr) (n : Nat) (k : cs.Key) (iv : List Byte)
    (s : State) : Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv (8 * c.bw) m₀ s.mem D n n (cbcEncC (8 * c.bw) (cs.cipher k) m₀ D iv)
  frame : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

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
  have hL0 : 0 < 8 * c.bw := by omega
  have hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hLG' : 8 * c.bw * c.G = 8 * (c.bw * c.G) := Nat.mul_assoc _ _ _
  have hLn : 8 * c.bw * n = 8 * (c.bw * n) := Nat.mul_assoc _ _ _
  have h8n : 8 * n ≤ 8 * c.bw * n := Nat.mul_le_mul_right n (by omega)
  have hjl := idx_lt (L := 8 * c.bw) hj
  have hj1 : 8 * c.bw * (j + 1) = 8 * c.bw * j + 8 * c.bw := Nat.mul_succ _ _
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, -, -, -, -, dsb, dsp, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, -, -, -, -, lsb, lsp, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  have hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega
  have p0 : ∀ X : Addr, X + BitVec.ofNat 64 0 = X := fun X => by simp
  let ciph := cs.cipher k
  let A := D + BitVec.ofNat 64 (8 * c.bw * j)
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have hwS : (⟨B, 8 * c.ctrSlots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have subT : Region.Sub ⟨T, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩ :=
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega)
  have subTbuf : Region.Sub ⟨T, 8 * c.bw⟩ (blkRegion c B) := Region.sub_prefix hLG
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.ctrSlots⟩ :=
    Region.sub_prefix (by simp only [Core.ctrSlots]; omega)
  have subA : Region.Sub ⟨A, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ := VG.Offset.sub_base D hjl
  have dDS : ∀ {r : Region}, Region.Sub r ⟨B, 8 * c.ctrSlots⟩ → Region.Disjoint ⟨D, 8 * c.bw * n⟩ r :=
    fun h => hp.sep.sub_right h
  have dAT : Region.Disjoint ⟨A, 8 * c.bw⟩ ⟨T, 8 * c.bw⟩ := (dDS subT).sub_left subA
  have hw : ∀ w, 8 * c.bw * j + 8 * w = 8 * (c.bw * j + w) := fun w => by rw [Nat.mul_add, Nat.mul_assoc]
  have hbj : ∀ w < c.bw, c.bw * j + w < c.bw * n := fun w hw' => by have := idx_lt (L := c.bw) hj; omega
  have inT : ∀ w < c.bw, InRegions s.wr (T + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
    ⟨_, hwS, by rw [addr_add]; exact VG.Offset.contains_base B (by simp only [Core.ctrSlots]; omega) (by omega)⟩
  have inA : ∀ w < c.bw, InRegions s.wr (A + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
    ⟨_, hwD, by rw [addr_add, hw]; exact VG.Offset.contains_base D (by have := hbj w hw'; omega) (by have := hbj w hw'; omega)⟩
  -- The data, outside the buffer and the core.
  have dT : ∀ q < n, ∀ r < 8 * c.bw, Region.Disjoint ⟨T, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ :=
    fun _ _ _ _ => (dDS subT).symm
  have hqr : ∀ {q r}, q < n → r < 8 * c.bw → 8 * c.bw * q + r < 8 * c.bw * n := fun hq hr => by
    have := idx_lt (L := 8 * c.bw) hq; omega
  -- Block `j` to the buffer.
  unfold Core.cbcEncBlock
  refine WP.seq (WP.mono (copyN_wp (k := c.bw) (P := T) (Q := A) ⟨by rw [hi.base], by rw [hi.dataR, p0],
    by decide, Ne.symm da, inT, fun w hw' => inRd (inA w hw'), dAT.symm, by omega⟩) fun s₁ h₁ => ?_)
  have base₁ : s₁.gpr sb = B := by rw [h₁.regs _ (by decide), hi.base]
  have f₁ : Frame [⟨T, 8 * c.bw⟩] s.mem s₁.mem := by rw [h₁.mem]; exact over_frame _ _ _ _
  have ready₁ : cs.Ready s₁ B k := cs.ready_frame hi.ready f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr subTbuf) fun r hr => by
    obtain ⟨h1, -⟩ := of_not_modeRegs hr; exact h₁.regs r h1
  -- Encrypted.
  refine WP.seq (WP.mono (cs.crypt_wp base₁ ⟨by rw [h₁.wr]; exact hwS, hfit⟩ ready₁)
    fun s₂ ⟨base₂, rsp₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩ => ?_)
  have eT : blkAddr c B 0 = T := by simp only [blkAddr, T, Nat.mul_zero, Nat.add_zero]
  have hpl : (cbcEncPrev (8 * c.bw) ciph m₀ D iv j).length = 8 * c.bw := by
    unfold cbcEncPrev; split
    · exact hiv
    · generalize j - 1 = t; cases t <;> exact cs.cipher_len k _
  have blk : bytesAt s.mem A (8 * c.bw) =
      Spec.Cbc.xor (bytesAt m₀ A (8 * c.bw)) (cbcEncPrev (8 * c.bw) ciph m₀ D iv j) := by
    apply List.ext_getElem (by simp [bytesAt, Spec.Cbc.xor, hpl])
    intro u h1 _
    have hu : u < 8 * c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range, Spec.Cbc.xor, List.getElem_zipWith]
    rw [addr_add, hi.data j hj u hu, encByte, ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl,
      ← List.getElem_eq_getD (h := by rw [hpl]; exact hu)]
  have C₂ : ∀ u < 8 * c.bw, s₂.mem (T + BitVec.ofNat 64 u) = (cbcEncC (8 * c.bw) ciph m₀ D iv j).getD u 0 :=
    fun u hu => by
      rw [← bytesAt_getD s₂.mem T hu, ← eT, ks₂ 0 hG0, eT]
      congr 2
      rw [cbcEncC_eq]
      congr 1
      rw [← blk]
      apply List.ext_getElem (by simp [bytesAt])
      intro v h1 _
      have hv : v < 8 * c.bw := by simpa [bytesAt] using h1
      simp only [bytesAt, List.getElem_map, List.getElem_range]
      rw [h₁.mem, over_at hv (by omega)]
  have D₂ : ∀ q < n, ∀ r < 8 * c.bw, s₂.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
      s.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) := fun q hq r hr => by
    rw [f₂.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact dDS subCore) hn64 (hqr hq hr), h₁.mem,
      over_sep (dDS subT).symm (hqr hq hr) hn64]
  -- Back to the data, and the count.
  have data₂ : s₂.gpr c.dataReg = A := by rw [dr₂, h₁.regs _ da, hi.dataR]
  refine WP.seq (WP.block_append (WP.mono (copyN_wp (k := c.bw) (P := A) (Q := T) ⟨by rw [data₂, p0],
    by rw [base₂], Ne.symm da, by decide, fun w hw' => by rw [wr₂, h₁.wr]; exact inA w hw',
    fun w hw' => by rw [rd₂, wr₂, h₁.rd, h₁.wr]; exact inRd (inT w hw'), dAT, by omega⟩) fun s₃a h₃a => ?_))
  obtain ⟨s₃, e₃, l₃, z₃, o₃, m₃, rd₃, wr₃⟩ := subImm_ok s₃a c.leftReg 1
  refine WP.of_runBlock ⟨s₃, e₃, ?_⟩
  have left₂ : s₃a.gpr c.leftReg = BitVec.ofNat 64 (n - j) := by
    rw [h₃a.regs _ la, lr₂, h₁.regs _ la, hi.leftR]
  have left₃ : s₃.gpr c.leftReg = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [l₃, left₂, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat (by omega), show n - j - 1 = n - (j + 1) by omega]
  have hz₃ : s₃.zf = some (decide (j + 1 = n)) := by
    rw [z₃, left₂, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
    simp only [Option.some.injEq, decide_eq_decide]; omega
  have g₃ : ∀ x, x ≠ .rax → x ≠ c.leftReg → s₃.gpr x = s₂.gpr x := fun x h1 h2 => by
    rw [o₃ x h2, h₃a.regs x h1]
  have base₃ : s₃.gpr sb = B := by rw [g₃ _ (by decide) (Ne.symm lsb), base₂]
  have data₃ : s₃.gpr c.dataReg = A := by rw [g₃ _ da hdl, data₂]
  have mem₃ : s₃.mem = over s₂.mem A (8 * c.bw) fun i => s₂.mem (T + BitVec.ofNat 64 i) := by rw [m₃, h₃a.mem]
  have f₃ : Frame [⟨A, 8 * c.bw⟩] s₂.mem s₃.mem := by rw [mem₃]; exact over_frame _ _ _ _
  have D₃ : ∀ q < n, ∀ r < 8 * c.bw, s₃.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
      if q = j then (cbcEncC (8 * c.bw) ciph m₀ D iv j).getD r 0
      else s.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) := fun q hq r hr => by
    rw [mem₃, over_blk _ _ _ hj hq hr hn64]
    split
    · exact C₂ r hr
    · exact D₂ q hq r hr
  have T₃ : ∀ u < 8 * c.bw, s₃.mem (T + BitVec.ofNat 64 u) = (cbcEncC (8 * c.bw) ciph m₀ D iv j).getD u 0 :=
    fun u hu => by rw [mem₃, over_sep dAT hu (by omega), C₂ u hu]
  -- The slots.
  have slotOut : ∀ i < 6, ∀ {R : Region}, (Region.Sub R ⟨D, 8 * c.bw * n⟩ ∨ R = ⟨T, 8 * c.bw⟩ ∨
      R = coreRegion c B) → Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ R := fun i hi6 R hR => by
    rcases hR with h | rfl | rfl
    · exact ((dDS (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by
        simp only [Core.ctrSlots]; omega))).sub_left h).symm
    · exact VG.Offset.disjoint B (.inr (by omega)) (by omega) (by omega)
    · exact VG.Offset.disjoint_base B (by omega) (by omega)
  have saved₃ : ∀ i < 6, s₃.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi6 => by
    rw [← hi.saved i hi6]
    refine (f₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slotOut i hi6 (.inl subA)) (by decide)).trans ?_
    refine (f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slotOut i hi6 (.inr (.inr rfl))) (by decide)).trans ?_
    exact f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slotOut i hi6 (.inr (.inl rfl))) (by decide)
  have fr₃ : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s₃.mem :=
    hi.frame.trans (((f₁.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; exact subT⟩).trans
      (f₂.sub fun r hr => ⟨_, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subCore⟩)).trans
      (f₃.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subA⟩))
  have rsp₃ : s₃.gpr .rsp = s₀.gpr .rsp := by
    rw [g₃ _ (by decide) (Ne.symm lsp), rsp₂, h₁.regs _ (by decide), hi.rsp]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, h₃a.rd, rd₂, h₁.rd, hi.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, h₃a.wr, wr₂, h₁.wr, hi.wr]
  have ready₃ : cs.Ready s₃ B k := cs.ready_frame ready₂ f₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inl ((dDS subCore).sub_left subA).symm) fun r hr => by
    obtain ⟨h1, -, -, -, -, -, h7⟩ := of_not_modeRegs hr; exact g₃ r h1 h7
  -- The last block, or on to the next.
  have hAL : A + BitVec.ofNat 64 (8 * c.bw) = D + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := by rw [addr_add, hj1]
  refine WP.seq (WP.mono (M := isa) (Q := fun s₄ => (∀ x, x ≠ .rax → s₄.gpr x = s₃.gpr x) ∧ s₄.rd = s₃.rd ∧
      s₄.wr = s₃.wr ∧ (j + 1 = n → s₄.mem = s₃.mem) ∧ (j + 1 < n → s₄.mem = over s₃.mem (D + BitVec.ofNat 64 (8 * c.bw * (j + 1))) (8 * c.bw)
        fun i => s₃.mem ((D + BitVec.ofNat 64 (8 * c.bw * (j + 1))) + BitVec.ofNat 64 i) ^^^ s₃.mem (T + BitVec.ofNat 64 i)))
    (WP.ite (decide (j + 1 = n)) (by simp [X86_64.eval, hz₃]) (fun h => ?_) (fun h => ?_)) fun s₄ h₄ => ?_)
  · exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, fun _ => rfl, fun h' => by simp at h; omega⟩
  · have hjn : j + 1 < n := by simp at h; omega
    have hjl' := idx_lt (L := 8 * c.bw) hjn
    have subN' : Region.Sub ⟨D + BitVec.ofNat 64 (8 * c.bw * (j + 1)), 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ :=
      VG.Offset.sub_base D hjl'
    have hw' : ∀ w, 8 * c.bw * (j + 1) + 8 * w = 8 * (c.bw * (j + 1) + w) := fun w => by
      rw [Nat.mul_add 8, Nat.mul_assoc]
    have hbj' : ∀ w < c.bw, c.bw * (j + 1) + w < c.bw * n := fun w hw'' => by
      have := idx_lt (L := c.bw) hjn; omega
    exact WP.mono (xorN_wp (k := c.bw) (P := D + BitVec.ofNat 64 (8 * c.bw * (j + 1))) (Q := T)
      ⟨by rw [data₃, hAL], by rw [base₃], Ne.symm da, by decide, fun w hw'' => ⟨_, by rw [wr₃', ← hi.wr]; exact hwD, by
        rw [addr_add, hw']
        exact VG.Offset.contains_base D (by have := hbj' w hw''; omega) (by have := hbj' w hw''; omega)⟩,
      fun w hw'' => by rw [rd₃', wr₃', ← hi.rd, ← hi.wr]; exact inRd (inT w hw''),
      (dDS subT).sub_left subN', by omega⟩) fun s₄ h₄ =>
      ⟨h₄.regs, h₄.rd, h₄.wr, fun h' => by omega, fun _ => h₄.mem⟩
  obtain ⟨g₄, rd₄, wr₄, mDone, mMore⟩ := h₄
  obtain ⟨s₅, e₅, a₅, o₅, m₅, rd₅, wr₅⟩ := addImm_ok s₄ c.dataReg (BitVec.ofNat 32 (8 * c.bw))
  obtain ⟨s₆, e₆, z₆, g₆, m₆, rd₆, wr₆⟩ := testSelf_ok s₅ c.leftReg
  refine WP.of_runBlock ⟨s₆, by
    rw [Core.encNext, show ([.alu .add c.dataReg (.imm (BitVec.ofNat 32 (8 * c.bw))),
      .alu .test c.leftReg (.reg c.leftReg)] : List Instr) = [.alu .add c.dataReg (.imm (BitVec.ofNat 32 (8 * c.bw)))] ++
      [.alu .test c.leftReg (.reg c.leftReg)] from rfl, runBlock_app, e₅, Option.bind_some, e₆], ?_⟩
  have keep₆ : ∀ x, x ≠ .rax → x ≠ c.dataReg → s₆.gpr x = s₃.gpr x := fun x h1 h2 => by
    rw [g₆, o₅ x h2, g₄ x h1]
  have left₆ : s₆.gpr c.leftReg = BitVec.ofNat 64 (n - (j + 1)) := by rw [keep₆ _ la (Ne.symm hdl), left₃]
  have hz : s₆.zf = some (decide (j + 1 = n)) := by
    rw [z₆, ← g₆, keep₆ _ la (Ne.symm hdl), l₃, left₂, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
    simp only [Option.some.injEq, decide_eq_decide]; omega
  have mem₆ : s₆.mem = s₄.mem := by rw [m₆, m₅]
  have base₆ : s₆.gpr sb = B := by rw [keep₆ _ (by decide) (Ne.symm dsb), base₃]
  have rsp₆ : s₆.gpr .rsp = s₀.gpr .rsp := by rw [keep₆ _ (by decide) (Ne.symm dsp), rsp₃]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, rd₃']
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, wr₃']
  by_cases hdone : j + 1 = n
  · have hm : s₆.mem = s₃.mem := by rw [mem₆, mDone hdone]
    refine .inl ⟨by rw [hz, decide_eq_true hdone], base₆, rsp₆, by rw [hm]; exact saved₃,
      dinv_of_blocks hL0 fun q hq r hr => ?_, by rw [hm]; exact fr₃, rd₆', wr₆'⟩
    rw [hm, D₃ q hq r hr, ite_eq_left hq]
    split
    · rename_i h; subst h; rfl
    · rw [hi.data q hq r hr, encByte, ite_eq_left (by omega)]
  · have hjn : j + 1 < n := by omega
    have hm := mMore hjn
    rw [← mem₆] at hm
    have subN : Region.Sub ⟨D + BitVec.ofNat 64 (8 * c.bw * (j + 1)), 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ :=
      VG.Offset.sub_base D (idx_lt hjn)
    have fN : Frame [⟨D + BitVec.ofNat 64 (8 * c.bw * (j + 1)), 8 * c.bw⟩] s₃.mem s₆.mem := by
      rw [hm]; exact over_frame _ _ _ _
    refine .inr ⟨by rw [hz, decide_eq_false hdone], base₆, rsp₆, ?_, fun i hi6 => ?_, ?_, left₆, hjn,
      fun q hq r hr => ?_, fr₃.trans (fN.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subN⟩), rd₆', wr₆'⟩
    · exact cs.ready_frame ready₃ fN (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inl ((dDS subCore).sub_left subN).symm)
        fun r hr => by obtain ⟨h1, -, -, -, -, h6, -⟩ := of_not_modeRegs hr; exact keep₆ r h1 h6
    · rw [← saved₃ i hi6]
      exact fN.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact slotOut i hi6 (.inl subN)) (by decide)
    · rw [g₆, a₅, g₄ _ da, data₃, signExtend_small (by omega), hAL]
    · rw [hm, over_blk _ _ _ hjn hq hr hn64]
      split
      · rename_i h; subst h
        rw [addr_add, D₃ _ hjn r hr, ite_eq_right (by omega), hi.data _ hjn r hr, T₃ r hr, encByte,
          ite_eq_right (by omega), ite_eq_right (by omega), encByte, ite_eq_right (Nat.lt_irrefl _),
          ite_eq_left rfl, cbcEncPrev, ite_eq_right (by omega), Nat.add_sub_cancel]
      · rename_i h
        rw [D₃ q hq r hr]
        split
        · rename_i h'; subst h'; rw [encByte, ite_eq_left (by omega)]
        · rename_i h'
          rw [hi.data q hq r hr, encByte, encByte]
          by_cases h3 : q < j
          · rw [ite_eq_left h3, ite_eq_left (by omega)]
          · rw [ite_eq_right h3, ite_eq_right h', ite_eq_right (show ¬ q < j + 1 by omega), ite_eq_right h]

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
  · exact .inr ⟨by simp [X86_64.eval, z], n - (j + 1), by have := d.lt; have := hj.lt; omega, j + 1, rfl, d⟩

end VG.Proof.Modes.X86_64
