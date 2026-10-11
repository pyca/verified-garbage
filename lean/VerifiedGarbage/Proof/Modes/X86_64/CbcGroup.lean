import VerifiedGarbage.Proof.Modes.X86_64.Group
import VerifiedGarbage.Proof.Modes.X86_64.Unchain
import VerifiedGarbage.Proof.Modes.Cbc

/-!
# CBC on x86-64, for any core: the entry and one group of decryption

`entry_ok`: the entry block of both directions moves the scratch buffer to
`sb` and stores the callee-saved registers. `cbcDecGroup_wp`: one iteration
of decryption's data loop copies the group's ciphertext blocks to the
core's buffer (`copyBlocks_wp`), decrypts them there (`BlockSpec.crypt_wp`,
the core's cipher being the inverse cipher), unchains them into the data
(`unchainBlocks_wp`) and steps to the next group. Block `j` of the data
becomes CBC's plaintext block `j` (`cbcOut`). Blocks are `8 bw` bytes.
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- The chaining value's `bw` words, from the mode's `hiSlot`. -/
abbrev chainAddr (c : Core) (B : Addr) : Addr := wordAddr B c.hiSlot

/-- The entry: the scratch buffer to `sb`, the callee-saved registers to the
mode's slots. -/
theorem entry_ok (hsm : 8 * c.total < 2 ^ 31) (hroom : c.slots + 8 ≤ c.total) {r : CtrRegs} (s : State) {B : Addr}
    (hB : s.gpr r.scr = B) (hs : ScrIn s B c.ctrSlots) :
    ∃ s', runBlock isa (c.ctrEntry r) s = some s' ∧ s'.gpr sb = B ∧
      (∀ i < 6, s'.mem.readW (wordAddr B (c.slots + i)) 64 = s.gpr (Core.savedRegs.getD i .rbx)) ∧
      Frame [modeRegion c B] s.mem s'.mem ∧ (∀ x, x ≠ sb → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega
  obtain ⟨s₁, e₁, b₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s sb r.scr
  have b₁' : s₁.gpr sb = B := by rw [b₁, hB]
  obtain ⟨s₂, e₂, v₂, f₂, g₂, rd₂, wr₂⟩ := stores_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .rbx) 6 s₁ b₁'
    (fun i hi => by rw [wr₁]; exact slot_wr hs.wr hN (by simp only [Core.ctrSlots]; omega)) (by omega)
  have hsv : ∀ i < 6, Core.savedRegs.getD i .rbx ≠ sb := by decide
  refine ⟨s₂, by rw [ctrEntry_eq, runBlock_app, e₁, Option.bind_some, e₂], by rw [g₂, b₁'],
    fun i hi => by rw [v₂ i hi, o₁ _ (hsv i hi)], ?_, fun x hx => by rw [g₂, o₁ x hx], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁]⟩
  rw [← m₁]
  exact f₂.sub fun x hx => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hx; subst hx; exact VG.Offset.sub B (by omega) (by omega)⟩

/-- The data loop, before group `g`, from the IV `iv` with the key `k`. -/
structure CInv (cs : BlockSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (iv : List Byte) (g : Nat)
    (s : State) : Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  ready : cs.Ready s B k
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * (c.G * g))
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - c.G * g)
  lt : c.G * g < n
  chain : ∀ u < 8 * c.bw, s.mem (chainAddr c B + BitVec.ofNat 64 u) =
    (cbcPrev (8 * c.bw) s₀.mem D iv (c.G * g)).getD u 0
  data : DInv (8 * c.bw) s₀.mem s.mem D n (c.G * g) (cbcOut (8 * c.bw) (cs.cipher k) s₀.mem D iv)
  frame : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure CDone (cs : BlockSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (iv : List Byte) (s : State) :
    Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  saved : ∀ i < 6, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv (8 * c.bw) s₀.mem s.mem D n n (cbcOut (8 * c.bw) (cs.cipher k) s₀.mem D iv)
  frame : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem cbcDecGroup_wp (cs : BlockSpec c) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} {iv : List Byte}
    (hiv : iv.length = 8 * c.bw) (hp : GPre c s₀ B D n (8 * c.bw)) {g : Nat} {s : State}
    (hi : CInv cs s₀ B D n k iv g s) :
    WP isa c.cbcDecGroup s fun s' => (s'.zf = some true ∧ CDone cs s₀ B D n k iv s') ∨
      (s'.zf = some false ∧ CInv cs s₀ B D n k iv (g + 1) s') := by
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
  have hL0 : 0 < 8 * c.bw := by omega
  have hGb : c.G ≤ c.bw * c.G := Nat.le_mul_of_pos_left _ hbw0
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, db, dc, dbp, d10, dsb, dsp, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, lb, lc, lbp, l10, lsb, lsp, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega
  let v := n - c.G * g
  let cc := min v c.G
  have h8n : 8 * n ≤ 8 * c.bw * n := Nat.mul_le_mul_right n (by omega)
  have hv : v < 2 ^ 64 := by omega
  have hc0 : 0 < cc := by omega
  have hcG : cc ≤ c.G := by omega
  have hkc : 8 * c.bw * (c.G * g) + 8 * c.bw * cc ≤ 8 * c.bw * n := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  have hbwcc : 8 * c.bw * cc = 8 * (c.bw * cc) := Nat.mul_assoc _ _ _
  have hbG : c.bw * cc ≤ c.bw * c.G := Nat.mul_le_mul_left _ hcG
  have hcc1 : 8 * c.bw ≤ 8 * c.bw * cc := Nat.le_mul_of_pos_right _ hc0
  let A := D + BitVec.ofNat 64 (8 * c.bw * (c.G * g))
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  let H := chainAddr c B
  have hwS : (⟨B, 8 * c.ctrSlots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have subS : ∀ {d l : Nat}, d + l ≤ 8 * c.ctrSlots → Region.Sub ⟨B + BitVec.ofNat 64 d, l⟩ ⟨B, 8 * c.ctrSlots⟩ :=
    fun h => VG.Offset.sub_base B h
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.ctrSlots⟩ :=
    Region.sub_prefix (by simp only [Core.ctrSlots]; omega)
  have subA : Region.Sub ⟨A, 8 * c.bw * cc⟩ ⟨D, 8 * c.bw * n⟩ := VG.Offset.sub_base D hkc
  have subT : Region.Sub ⟨T, 8 * c.bw * cc⟩ ⟨B, 8 * c.ctrSlots⟩ := subS (by simp only [Core.ctrSlots]; omega)
  have subH : Region.Sub ⟨H, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩ :=
    subS (by simp only [Core.hiSlot, Core.ctrSlots]; omega)
  have subTbuf : Region.Sub ⟨T, 8 * c.bw * cc⟩ (blkRegion c B) := Region.sub_prefix (Nat.mul_le_mul_left _ hcG)
  have dDS : ∀ {r : Region}, Region.Sub r ⟨B, 8 * c.ctrSlots⟩ → Region.Disjoint ⟨D, 8 * c.bw * n⟩ r :=
    fun h => hp.sep.sub_right h
  have dAT : Region.Disjoint ⟨A, 8 * c.bw * cc⟩ ⟨T, 8 * c.bw * cc⟩ := (dDS subT).sub_left subA
  have dTH : Region.Disjoint ⟨T, 8 * c.bw * cc⟩ ⟨H, 8 * c.bw⟩ :=
    VG.Offset.disjoint B (.inl (by simp only [Core.hiSlot]; omega)) (by omega) (by simp only [Core.hiSlot]; omega)
  have dAH : Region.Disjoint ⟨A, 8 * c.bw * cc⟩ ⟨H, 8 * c.bw⟩ := (dDS subH).sub_left subA
  have dHcore : Region.Disjoint ⟨H, 8 * c.bw⟩ (coreRegion c B) :=
    VG.Offset.disjoint_base B (by simp only [Core.hiSlot]; omega) (by simp only [Core.hiSlot]; omega)
  have inT : ∀ t, t < c.bw * cc → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := fun t ht =>
    ⟨_, hwS, by rw [addr_add]; exact VG.Offset.contains_base B (by simp only [Core.ctrSlots]; omega) (by omega)⟩
  have inA : ∀ t, t < c.bw * cc → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := fun t ht =>
    ⟨_, hwD, by rw [addr_add]; exact VG.Offset.contains_base D (by omega) (by omega)⟩
  have inH : ∀ w < c.bw, InRegions s.wr (H + BitVec.ofNat 64 (8 * w)) 8 := fun w hw =>
    ⟨_, hwS, by
      rw [addr_add]
      exact VG.Offset.contains_base B (by simp only [Core.hiSlot, Core.ctrSlots]; omega)
        (by simp only [Core.hiSlot]; omega)⟩
  unfold Core.cbcDecGroup
  -- The count, the addresses, and the ciphertext blocks to the buffer.
  have left₀ : s.gpr c.leftReg = BitVec.ofNat 64 v := hi.leftR
  refine WP.seq (WP.mono (groupCount_wp (by omega) lc left₀ hv) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_)
  have base₁ : s₁.gpr sb = B := by rw [o₁ _ (by decide), hi.base]
  obtain ⟨s₂, e₂, a₂, b₂, t₂, o₂, m₂, rd₂, wr₂⟩ := xorArgs_ok (by omega) da s₁ base₁
  refine WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)
  have mem₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  have keep₂ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .r10 → s₂.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [o₂ r h1 h2 h4, o₁ r h3]
  refine WP.seq (WP.mono (copyBlocks_wp (S := A) (T := T) hbw0 (by omega) hc0 (by omega)
    (fun t ht => by rw [rd₂', wr₂']; exact inRd (inA t ht)) (fun t ht => by rw [wr₂']; exact inT t ht) dAT
    (by rw [a₂]) (by rw [b₂, o₁ _ dc, hi.dataR])
    (by rw [o₂ _ (by decide) (by decide) (by decide), c₁])) fun s₃ h₃ => ?_)
  have keep₃ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → r ≠ .r10 → s₃.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [h₃.regs r h1 h2 h3 h4, keep₂ r h1 h2 h3 h5]
  have base₃ : s₃.gpr sb = B := by rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.base]
  have rd₃' : s₃.rd = s.rd := by rw [h₃.rd, rd₂']
  have wr₃' : s₃.wr = s.wr := by rw [h₃.wr, wr₂']
  have f₃ : Frame [⟨T, 8 * c.bw * cc⟩] s.mem s₃.mem := by rw [← mem₂]; exact h₃.frame
  have ready₃ : cs.Ready s₃ B k := cs.ready_frame hi.ready f₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr subTbuf) fun r hr => by
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := of_not_modeRegs hr
    exact keep₃ r h1 h2 h3 h4 h5
  -- Decrypted.
  refine WP.seq (WP.mono (cs.crypt_wp base₃ ⟨by rw [wr₃']; exact hwS, hfit⟩ ready₃)
    fun s₄ ⟨base₄, rsp₄, dr₄, lr₄, ready₄, f₄, ks₄, rd₄, wr₄⟩ => ?_)
  have left₄ : s₄.gpr c.leftReg = BitVec.ofNat 64 v := by
    rw [lr₄, keep₃ _ la lb lc lbp l10, hi.leftR]
  have data₄ : s₄.gpr c.dataReg = A := by rw [dr₄, keep₃ _ da db dc dbp d10, hi.dataR]
  refine WP.seq (WP.mono (groupCount_wp (by omega) lc left₄ hv) fun s₅ ⟨c₅, o₅, m₅, rd₅, wr₅⟩ => ?_)
  have base₅ : s₅.gpr sb = B := by rw [o₅ _ (by decide), base₄]
  obtain ⟨s₆, e₆, a₆, b₆, t₆, o₆, m₆, rd₆, wr₆⟩ := xorArgs_ok (by omega) da s₅ base₅
  refine WP.seq (WP.of_runBlock ⟨s₆, e₆, ?_⟩)
  have mem₆ : s₆.mem = s₄.mem := by rw [m₆, m₅]
  have rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃']
  have wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃']
  have base₆ : s₆.gpr sb = B := by rw [o₆ _ (by decide) (by decide) (by decide), base₅]
  -- The plaintext blocks.
  refine WP.seq (WP.mono (unchainBlocks_wp (c := c) (B := B) (T := T) (A := A) (H := H) hbw0 (by omega) hc0
    (by omega) base₆ rfl (fun t ht => by rw [wr₆']; exact inT t ht) (fun t ht => by rw [wr₆']; exact inA t ht)
    (fun w hw => by rw [wr₆']; exact inH w hw) dAT.symm dTH dAH (by rw [a₆]) (by rw [b₆, o₅ _ dc, data₄])
    (by rw [o₆ _ (by decide) (by decide) (by decide), c₅])) fun s₇ ⟨h₇, rbx₇⟩ => ?_)
  have f₇ : Frame [⟨T, 8 * c.bw * cc⟩, ⟨A, 8 * c.bw * cc⟩, ⟨H, 8 * c.bw⟩] s₄.mem s₇.mem := by
    rw [← mem₆]; exact h₇.frame
  have g₇ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → r ≠ .r10 → s₇.gpr r = s₄.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [h₇.regs r h1 h2 h3 h4, o₆ r h1 h2 h5, o₅ r h3]
  have left₇ : s₇.gpr c.leftReg = BitVec.ofNat 64 v := by rw [g₇ _ la lb lc lbp l10, left₄]
  have r10₇ : s₇.gpr .r10 = BitVec.ofNat 64 cc := by
    rw [h₇.regs _ (by decide) (by decide) (by decide) (by decide), t₆, c₅]
  -- On to the next group.
  obtain ⟨s₈, e₈, d₈, l₈, z₈, o₈, m₈, rd₈, wr₈⟩ := advance_ok hdl d10 s₇
  refine WP.of_runBlock ⟨s₈, e₈, ?_⟩
  have hz : s₈.zf = some (decide (v = cc)) := by
    rw [z₈, left₇, r10₇, VG.Offset.ofNat_sub_ofNat_beq hv (by omega)]
  have keep₈ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → r ≠ .r10 → r ≠ c.dataReg → r ≠ c.leftReg →
      s₈.gpr r = s₄.gpr r := fun r h1 h2 h3 h4 h5 h6 h7 => by rw [o₈ r h6 h7, g₇ r h1 h2 h3 h4 h5]
  have ready₈ : cs.Ready s₈ B k := by
    refine cs.ready_frame ready₄ (by rw [m₈]; exact f₇) (fun r hr => ?_) fun r hr => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr subTbuf
      · exact .inl (((dDS subCore).sub_left subA).symm)
      · exact .inl dHcore.symm
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := of_not_modeRegs hr
      exact keep₈ r h1 h2 h3 h4 h5 h6 h7
  -- The bytes, through the steps.
  have hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega
  have outCore : ∀ {R : Region}, Region.Disjoint R (coreRegion c B) → R.len ≤ 2 ^ 64 →
      ∀ i < R.len, s₄.mem (R.base + BitVec.ofNat 64 i) = s₃.mem (R.base + BitVec.ofNat 64 i) := fun hd hl i hi =>
    f₄.bytes (R := _) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hl hi
  have outT : ∀ {R : Region}, Region.Disjoint R ⟨T, 8 * c.bw * cc⟩ → R.len ≤ 2 ^ 64 →
      ∀ i < R.len, s₃.mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) := fun hd hl i hi =>
    f₃.bytes (R := _) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hl hi
  -- The data before the unchaining: as on entry.
  have dat₄ : ∀ i < 8 * c.bw * n, s₄.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := fun i hin => by
    rw [outCore (R := ⟨D, 8 * c.bw * n⟩) (dDS subCore) hn64 i hin,
      outT (R := ⟨D, 8 * c.bw * n⟩) (dDS subT) hn64 i hin]
  have chain₄ : ∀ u < 8 * c.bw, s₄.mem (H + BitVec.ofNat 64 u) = s.mem (H + BitVec.ofNat 64 u) := fun u hu => by
    rw [outCore (R := ⟨H, 8 * c.bw⟩) dHcore (show 8 * c.bw ≤ 2 ^ 64 by omega) u hu, outT (R := ⟨H, 8 * c.bw⟩) dTH.symm (show 8 * c.bw ≤ 2 ^ 64 by omega) u hu]
  have dat0 : ∀ i, 8 * c.bw * (c.G * g) ≤ i → i < 8 * c.bw * n →
      s.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) :=
    fun i h1 h2 => by rw [hi.data i h2, ite_eq_right (by omega)]
  -- The decrypted blocks in the buffer.
  have dec₄ : ∀ j < cc, ∀ u < 8 * c.bw, s₄.mem (T + BitVec.ofNat 64 (8 * c.bw * j + u)) =
      (cs.cipher k (bytesAt s₀.mem (D + BitVec.ofNat 64 (8 * c.bw * (c.G * g + j))) (8 * c.bw))).getD u 0 := by
    intro j hj u hu
    have hjl := idx_lt (L := 8 * c.bw) hj
    have eT : T + BitVec.ofNat 64 (8 * c.bw * j + u) = blkAddr c B j + BitVec.ofNat 64 u := by
      simp only [T, blkAddr]; rw [addr_add, addr_add, Nat.add_assoc]
    rw [eT, ← bytesAt_getD s₄.mem _ hu, ks₄ _ (by omega)]
    congr 2
    apply List.ext_getElem (by simp [bytesAt])
    intro x h1 _
    have hx : x < 8 * c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range, blkAddr]
    rw [addr_add, show 8 * c.buf + 8 * c.bw * j + x = 8 * c.buf + (8 * c.bw * j + x) by omega, ← addr_add,
      h₃.copied _ (by omega), mem₂, addr_add, addr_add, Nat.mul_add, Nat.add_assoc,
      dat0 _ (by omega) (by omega)]
  -- Offsets within the data.
  have eA : ∀ t, D + BitVec.ofNat 64 (8 * c.bw * (c.G * g) + t) = A + BitVec.ofNat 64 t := fun t => by
    rw [← addr_add]
  have prevEq : ∀ {j u : Nat}, 0 < j → 8 * c.bw * (c.G * g) + (8 * c.bw * (j - 1) + u) =
      8 * c.bw * (c.G * g + j - 1) + u := fun {j u} hj => by
    have := Nat.mul_sub_one (8 * c.bw) j
    have := Nat.mul_sub_one (8 * c.bw) (c.G * g + j)
    have := Nat.mul_add (8 * c.bw) (c.G * g) j
    have := Nat.le_mul_of_pos_right (8 * c.bw) hj
    omega
  have hdata : DInv (8 * c.bw) s₀.mem s₈.mem D n (c.G * g + cc) (cbcOut (8 * c.bw) (cs.cipher k) s₀.mem D iv) := by
    refine dinv_of_blocks hL0 fun q hq r hr => ?_
    rw [m₈]
    have hqn := idx_lt (L := 8 * c.bw) hq
    by_cases hin : c.G * g ≤ q ∧ q < c.G * g + cc
    · obtain ⟨j, rfl⟩ : ∃ j, q = c.G * g + j := ⟨q - c.G * g, by omega⟩
      have hjc : j < cc := by omega
      have hjl := idx_lt (L := 8 * c.bw) hjc
      rw [Nat.mul_add, Nat.add_assoc, eA, h₇.out _ (by omega), mem₆, dec₄ j hjc r hr, ite_eq_left hin.2,
        cbcOut_getD (cs.cipher_len k) _ _ hiv _ hr]
      congr 1
      by_cases hj0 : j = 0
      · subst hj0
        rw [Nat.mul_zero, Nat.zero_add, ite_eq_left hr, chain₄ r hr, hi.chain r hr, Nat.add_zero]
      · have := Nat.le_mul_of_pos_right (8 * c.bw) (Nat.pos_of_ne_zero hj0)
        rw [ite_eq_right (by omega), show 8 * c.bw * j + r - 8 * c.bw = 8 * c.bw * (j - 1) + r by
            have := Nat.mul_sub_one (8 * c.bw) j; omega,
          ← eA, dat₄ _ (by have := idx_lt (L := 8 * c.bw) (show j - 1 < cc by omega); omega),
          dat0 _ (by omega) (by have := idx_lt (L := 8 * c.bw) (show j - 1 < cc by omega); omega), cbcPrev,
          ite_eq_right (by omega), bytesAt_getD _ _ hr, addr_add, prevEq (Nat.pos_of_ne_zero hj0)]
    · have hlo : q < c.G * g → 8 * c.bw * q + r < 8 * c.bw * (c.G * g) := fun h => by
        have := idx_lt (L := 8 * c.bw) h; omega
      have hhi : c.G * g + cc ≤ q → 8 * c.bw * (c.G * g) + 8 * c.bw * cc ≤ 8 * c.bw * q := fun h => by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ h
      have hout : ∀ R ∈ [(⟨T, 8 * c.bw * cc⟩ : Region), ⟨A, 8 * c.bw * cc⟩, ⟨H, 8 * c.bw⟩],
          ¬ R.Contains (D + BitVec.ofNat 64 (8 * c.bw * q + r)) 1 := fun R hR => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
        rcases hR with rfl | rfl | rfl
        · exact fun h => (dDS subT) _ (VG.Offset.contains_base D (by omega) (by omega)) h
        · exact not_contains_off D (by omega) (by omega) (by omega) (by omega)
        · exact fun h => (dDS subH) _ (VG.Offset.contains_base D (by omega) (by omega)) h
      rw [f₇ _ hout, dat₄ _ (by omega), hi.data _ (by omega), idx_div hr, idx_mod hr]
      by_cases h2 : q < c.G * g
      · rw [ite_eq_left (hlo h2), ite_eq_left (by omega)]
      · rw [ite_eq_right (by have := Nat.mul_le_mul_left (8 * c.bw) (Nat.le_of_not_lt h2); omega),
          ite_eq_right (by omega)]
  -- The chaining value: the group's last ciphertext block.
  have chain₈ : ∀ u < 8 * c.bw, s₈.mem (H + BitVec.ofNat 64 u) =
      (cbcPrev (8 * c.bw) s₀.mem D iv (c.G * g + cc)).getD u 0 := by
    intro u hu
    have hl := idx_lt (L := 8 * c.bw) (show cc - 1 < cc by omega)
    rw [m₈, h₇.chain u hu, ite_eq_right (by omega), mem₆, ← eA, dat₄ _ (by omega), dat0 _ (by omega) (by omega),
      cbcPrev, ite_eq_right (by omega), bytesAt_getD _ _ hu, addr_add, prevEq hc0]
  -- The slots.
  have wS : ∀ j, c.slots ≤ j → j < c.slots + 6 → ∀ r ∈ [(⟨T, 8 * c.bw * cc⟩ : Region), ⟨A, 8 * c.bw * cc⟩,
      ⟨H, 8 * c.bw⟩], Region.Disjoint ⟨wordAddr B j, 8⟩ r := fun j h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Offset.disjoint B (.inr (by omega)) (by omega) (by omega)
    · exact (((dDS (subS (show 8 * j + 8 ≤ 8 * c.ctrSlots by simp only [Core.ctrSlots]; omega))).sub_left
        subA).symm)
    · exact VG.Offset.disjoint B (.inl (by simp only [Core.hiSlot]; omega)) (by omega)
        (by simp only [Core.hiSlot]; omega)
  have saved₈ : ∀ i < 6, s₈.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi6 => by
    rw [m₈, ← hi.saved i hi6]
    refine (f₇.readW (Region.contains_self _ _) (wS _ (by omega) (by omega)) (by decide)).trans ?_
    refine (f₄.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base B (by omega) (by omega)) (by decide)).trans ?_
    exact f₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint B (.inr (by omega)) (by omega) (by omega)) (by decide)
  have fr : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s₈.mem := by
    rw [m₈]
    refine hi.frame.trans (((f₃.sub fun r hr => ⟨⟨B, 8 * c.ctrSlots⟩, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; exact subT⟩).trans
      (f₄.sub fun r hr => ⟨⟨B, 8 * c.ctrSlots⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subCore⟩)).trans (f₇.sub fun r hr => ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, subT⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subA⟩
    · exact ⟨_, List.mem_cons_self, subH⟩
  have base₈ : s₈.gpr sb = B := by rw [o₈ _ (Ne.symm dsb) (Ne.symm lsb), g₇ _ (by decide) (by decide)
    (by decide) (by decide) (by decide), base₄]
  have rsp₈ : s₈.gpr .rsp = s₀.gpr .rsp := by
    rw [o₈ _ (Ne.symm dsp) (Ne.symm lsp), g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), rsp₄,
      keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.rsp]
  have rd₈' : s₈.rd = s₀.rd := by rw [rd₈, h₇.rd, rd₆', hi.rd]
  have wr₈' : s₈.wr = s₀.wr := by rw [wr₈, h₇.wr, wr₆', hi.wr]
  by_cases hdone : v = cc
  · refine .inl ⟨by rw [hz, decide_eq_true hdone], base₈, rsp₈, saved₈, ?_, fr, rd₈', wr₈'⟩
    rw [show n = c.G * g + cc by omega] at hdata ⊢
    exact hdata
  · have hcc : cc = c.G := by omega
    have hg1 : c.G * (g + 1) = c.G * g + cc := by rw [hcc, Nat.mul_succ]
    refine .inr ⟨by rw [hz, decide_eq_false hdone], base₈, rsp₈, ready₈, saved₈, ?_, ?_, by omega, ?_,
      by rw [hg1]; exact hdata, fr, rd₈', wr₈'⟩
    · rw [d₈, rbx₇, addr_add, hg1, Nat.mul_add]
    · rw [l₈, left₇, r10₇, VG.Offset.ofNat_sub_ofNat (by omega), hg1]; congr 1; omega
    · rw [hg1]; exact chain₈

/-- The data loop. -/
theorem cbcDecLoop_wp (cs : BlockSpec c) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} {iv : List Byte}
    (hiv : iv.length = 8 * c.bw) (hp : GPre c s₀ B D n (8 * c.bw)) {s : State} (hi : CInv cs s₀ B D n k iv 0 s) :
    WP isa (.loop c.cbcDecGroup .ne) s (CDone cs s₀ B D n k iv) := by
  refine WP.loop (M := isa) (fun m s => ∃ g, m = n - c.G * g ∧ CInv cs s₀ B D n k iv g s) (fun m s hs => ?_) n s
    ⟨0, by simp, hi⟩
  obtain ⟨g, rfl, hg⟩ := hs
  refine WP.mono (cbcDecGroup_wp cs hiv hp hg) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩
  · have hG := cs.layout.G_pos
    exact .inr ⟨by simp [X86_64.eval, z], n - c.G * (g + 1),
      by have := d.lt; have := hg.lt; rw [Nat.mul_succ] at *; omega, g + 1, rfl, d⟩

end VG.Proof.Modes.X86_64
