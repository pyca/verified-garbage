import VerifiedGarbage.Proof.Modes.AArch64.Group
import VerifiedGarbage.Proof.Modes.AArch64.Unchain
import VerifiedGarbage.Proof.Modes.Cbc

/-!
# CBC decryption on AArch64, for any core: entry and one group

`cbcSetup_ok`: the entry block of `cbcDecrypt` moves the scratch buffer to
`sb`, stores the callee-saved registers and reads the IV into the chaining
value's slots. `cbcDecGroup_wp`: one iteration of the data loop copies the
group's ciphertext blocks to the core's buffer (`copyBlocks_wp`), decrypts
them there (`CoreSpec.crypt_wp`, the core's cipher being the inverse
cipher), unchains them into the data (`unchainBlocks_wp`) and steps to the
next group. Block `j` of the data becomes CBC's plaintext block `j`
(`cbcOut`). As on x86-64 (`Proof/Modes/X86_64/CbcGroup.lean`).
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- The chaining value's 16 bytes, at the mode's `hiSlot` and `loSlot`. -/
abbrev chainAddr (c : Core) (B : Addr) : Addr := wordAddr B c.hiSlot

theorem chainAddr_lo (c : Core) (B : Addr) : wordAddr B c.loSlot = chainAddr c B + BitVec.ofNat 64 8 := by
  simp only [chainAddr, wordAddr, Core.loSlot, Core.hiSlot]; rw [addr_add]; congr 2

theorem cbcSetup_eq (c : Core) (r : CtrRegs) : c.cbcSetup r =
    ([.ldr .x .x6 r.ctr 0] : List Instr) ++ (([.ldr .x .x7 r.ctr 8] : List Instr) ++
    (([stS c.hiSlot .x6] : List Instr) ++ [stS c.loSlot .x7])) := rfl

/-- What a register outside the modes' own is not. -/
theorem not_own {r : Reg} (h : r ∉ ownRegs) : r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x13 ∧
    r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x16 ∧ r ≠ .x17 := by
  simp only [ownRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h; exact h

/-- The entry: the scratch buffer to `sb`, the callee-saved registers to the
mode's slots, the IV at `r.ctr` to the chaining value's. -/
theorem cbcSetup_ok (hL : Layout c) {r : CtrRegs} (hr : RegsOk r) (s : State) {B P : Addr}
    (hB : s.gpr r.scr = B) (hs : ScrIn s B c.total) (hP : s.gpr r.ctr = P) (hrP : (⟨P, 16⟩ : Region) ∈ s.rd)
    (hsep : Region.Disjoint ⟨P, 16⟩ ⟨B, 8 * c.total⟩) :
    ∃ s', runBlock isa (c.ctrEntry r ++ c.cbcSetup r) s = some s' ∧ s'.gpr sb = B ∧
      (∀ i < 10, s'.mem.readW (wordAddr B (c.slots + i)) 64 = s.gpr (Core.savedRegs.getD i .x19)) ∧
      (∀ u < 16, s'.mem (chainAddr c B + BitVec.ofNat 64 u) = s.mem (P + BitVec.ofNat 64 u)) ∧
      Frame [modeRegion c B] s.mem s'.mem ∧
      (∀ x, x ∉ SetupRegs → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsm := hL.small
  have hroom := hL.room
  have hN : 8 * c.total < 2 ^ 64 := by omega
  have sl : ∀ k, c.slots ≤ k → k < c.total → InRegions s.wr (wordAddr B k) 8 := fun k _ hk =>
    slot_wr hs.wr hN hk
  have p0 : P + BitVec.ofNat 64 0 = P := by simp
  obtain ⟨cs, c6, c7, c10⟩ := not_setupRegs hr.ctr
  obtain ⟨s₁, e₁, b₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s sb r.scr
  have b₁' : s₁.gpr sb = B := by rw [b₁, hB]
  obtain ⟨s₂, e₂, v₂, f₂, g₂, rd₂, wr₂⟩ := stores_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₁
    b₁' (fun i hi => by rw [wr₁]; exact sl _ (by omega) (by omega)) (by omega)
  have keep₂ : ∀ x, x ≠ sb → s₂.gpr x = s.gpr x := fun x hx => by rw [g₂, o₁ x hx]
  have P₂ : s₂.gpr r.ctr = P := by rw [keep₂ _ cs, hP]
  have fe : Frame [modeRegion c B] s.mem s₂.mem := by
    rw [← m₁]
    exact f₂.sub fun x hx => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.sub B (by omega) (by omega)⟩
  have dPm : Region.Disjoint ⟨P, 16⟩ (modeRegion c B) := hsep.sub_right (VG.Offset.sub_base B (by omega))
  have inP : ∀ d, d + 8 ≤ 16 → InRegions (s₂.rd ++ s₂.wr) (P + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [rd₂, wr₂, rd₁, wr₁]; exact ⟨_, List.mem_append_left _ hrP, VG.Offset.contains_base P hd (by omega)⟩
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := ldr_ok s₂ .x6 r.ctr (off := 0) (by decide)
    (by rw [P₂]; exact inP 0 (by decide))
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := ldr_ok s₃ .x7 r.ctr (off := 8) (by decide)
    (by rw [rd₃, wr₃, o₃ _ c6, P₂]; exact inP 8 (by decide))
  have b₄ : s₄.gpr sb = B := by rw [o₄ _ (by decide), o₃ _ (by decide), g₂, b₁']
  have hH : c.hiSlot < c.total := by simp only [Core.hiSlot]; omega
  have hLo : c.loSlot < c.total := by simp only [Core.loSlot]; omega
  obtain ⟨s₅, e₅, m₅, g₅, rd₅, wr₅⟩ := stS_ok (s := s₄) (b := B) (k := c.hiSlot) .x6 b₄ (by omega)
    (by rw [wr₄, wr₃, wr₂, wr₁]; exact sl _ (by simp only [Core.hiSlot]; omega) hH)
  obtain ⟨s₆, e₆, m₆, g₆, rd₆, wr₆⟩ := stS_ok (s := s₅) (b := B) (k := c.loSlot) .x7 (by rw [g₅, b₄]) (by omega)
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact sl _ (by simp only [Core.loSlot]; omega) hLo)
  let H := chainAddr c B
  have mem₆ : s₆.mem = (s₂.mem.writeW H (s₂.mem.readW P 64)).writeW (H + BitVec.ofNat 64 8)
      (s₂.mem.readW (P + BitVec.ofNat 64 8) 64) := by
    rw [m₆, m₅, g₅, r₄, o₄ _ (by decide), r₃, m₄, m₃, o₃ _ c6, P₂, p0, chainAddr_lo]
  have hPm : ∀ u < 16, s₂.mem (P + BitVec.ofNat 64 u) = s.mem (P + BitVec.ofNat 64 u) := fun u hu =>
    fe.bytes (R := ⟨P, 16⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact dPm)
      (show 16 ≤ 2 ^ 64 by decide) hu
  have fS : Frame [modeRegion c B] s₂.mem s₆.mem := by
    rw [mem₆, ← chainAddr_lo]
    have hm : modeRegion c B ∈ [modeRegion c B] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains B (by simp only [Core.hiSlot]; omega)
      (by simp only [Core.hiSlot]; omega) (by omega))).writeW hm _
      (VG.Offset.contains B (by simp only [Core.loSlot]; omega) (by simp only [Core.loSlot]; omega) (by omega))
  have b8 : ∀ k, k < c.total → 8 * k < 2 ^ 64 := fun k hk => by omega
  have hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  refine ⟨s₆, ?_, by rw [g₆, g₅, b₄], fun i hi => ?_, fun u hu => ?_, fe.trans fS, fun x hx => ?_,
    by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [runBlock_app, ctrEntry_eq, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, cbcSetup_eq,
      runBlock_app, e₃, Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, e₆]
  · have k2 : c.slots + i < c.total := by omega
    rw [m₆, m₅, readW_slot_write _ (b8 _ k2) (b8 _ hLo), ite_eq_right (by simp only [Core.loSlot]; omega),
      readW_slot_write _ (b8 _ k2) (b8 _ hH), ite_eq_right (by simp only [Core.hiSlot]; omega), m₄, m₃,
      v₂ i hi, o₁ _ (hsv i hi)]
  · rw [mem₆, writeW_readW_apply]
    by_cases h8 : 8 ≤ u
    · rw [ite_eq_left (by rw [off_sub_toNat H h8 (by omega)]; omega), off_sub_toNat H h8 (by omega), addr_add,
        show 8 + (u - 8) = u by omega, hPm u hu]
    · rw [ite_eq_right (off_sub_not H (Or.inl (by omega)) (by omega) (by decide) (by decide)),
        writeW_readW_apply, ite_eq_left (by rw [off_self H (by omega)]; omega), off_self H (by omega), hPm u hu]
  · obtain ⟨h1, h2, h3, -⟩ := not_setupRegs hx
    rw [g₆, g₅, o₄ x h3, o₃ x h2, keep₂ x h1]

/-- The data loop, before group `g`, from the IV `iv` with the key `k`. -/
structure CInv (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (iv : List Byte) (g : Nat)
    (s : State) : Prop where
  base : s.gpr sb = B
  ready : cs.Ready s B k
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (16 * (c.G * g))
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - c.G * g)
  lt : c.G * g < n
  chain : ∀ u < 16, s.mem (chainAddr c B + BitVec.ofNat 64 u) = (cbcPrev s₀.mem D iv (c.G * g)).getD u 0
  data : DInv s₀.mem s.mem D n (c.G * g) (cbcOut (cs.cipher k) s₀.mem D iv)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure CDone (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (iv : List Byte) (s : State) :
    Prop where
  base : s.gpr sb = B
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv s₀.mem s.mem D n n (cbcOut (cs.cipher k) s₀.mem D iv)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem cbcDecGroup_wp (cs : CoreSpec c) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} {iv : List Byte}
    (hiv : iv.length = 16) (hp : GPre c s₀ B D n) {g : Nat} {s : State} (hi : CInv cs s₀ B D n k iv g s) :
    WP isa c.cbcDecGroup s fun s' => (isa.eval (.nonzero .x c.leftReg) s' = some false ∧ CDone cs s₀ B D n k iv s') ∨
      (isa.eval (.nonzero .x c.leftReg) s' = some true ∧ CInv cs s₀ B D n k iv (g + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG0 := hL.G_pos
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨down, dsb, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨lown, lsb, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨-, -, -, -, -, d13, d14, -, d16, -⟩ := not_own down
  obtain ⟨-, -, -, -, -, l13, -, -, -, -⟩ := not_own lown
  have hN : 8 * c.total < 2 ^ 64 := by omega
  let v := n - c.G * g
  let cc := min v c.G
  have hv : v < 2 ^ 64 := by omega
  have hc0 : 0 < cc := by omega
  have hcG : cc ≤ c.G := by omega
  have hkc : 16 * (c.G * g) + 16 * cc ≤ 16 * n := by omega
  let A := D + BitVec.ofNat 64 (16 * (c.G * g))
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  let H := chainAddr c B
  have hwS : (⟨B, 8 * c.total⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have subS : ∀ {d l : Nat}, d + l ≤ 8 * c.total → Region.Sub ⟨B + BitVec.ofNat 64 d, l⟩ ⟨B, 8 * c.total⟩ :=
    fun h => VG.Offset.sub_base B h
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.total⟩ := Region.sub_prefix (by omega)
  have subA : Region.Sub ⟨A, 16 * cc⟩ ⟨D, 16 * n⟩ := VG.Offset.sub_base D (by omega)
  have subT : Region.Sub ⟨T, 16 * cc⟩ ⟨B, 8 * c.total⟩ := subS (by omega)
  have subH : Region.Sub ⟨H, 16⟩ ⟨B, 8 * c.total⟩ := subS (by simp only [Core.hiSlot]; omega)
  have subTbuf : Region.Sub ⟨T, 16 * cc⟩ (bufRegion c B) := VG.Offset.sub B (by omega) (by omega)
  have dDS : ∀ {r : Region}, Region.Sub r ⟨B, 8 * c.total⟩ → Region.Disjoint ⟨D, 16 * n⟩ r :=
    fun h => hp.sep.sub_right h
  have dAT : Region.Disjoint ⟨A, 16 * cc⟩ ⟨T, 16 * cc⟩ := (dDS subT).sub_left subA
  have dTH : Region.Disjoint ⟨T, 16 * cc⟩ ⟨H, 16⟩ :=
    VG.Offset.disjoint B (by simp only [Core.hiSlot]; omega) (by omega) (by simp only [Core.hiSlot]; omega)
  have dAH : Region.Disjoint ⟨A, 16 * cc⟩ ⟨H, 16⟩ := (dDS subH).sub_left subA
  have dHcore : Region.Disjoint ⟨H, 16⟩ (coreRegion c B) :=
    VG.Offset.disjoint_base B (by simp only [Core.hiSlot]; omega) (by simp only [Core.hiSlot]; omega)
  have inT : ∀ t, t < 2 * cc → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := fun t ht =>
    ⟨_, hwS, by rw [addr_add]; exact VG.Offset.contains_base B (by omega) (by omega)⟩
  have inA : ∀ t, t < 2 * cc → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := fun t ht =>
    ⟨_, hwD, by rw [addr_add]; exact VG.Offset.contains_base D (by omega) (by omega)⟩
  have inH : ∀ w < 2, InRegions s.wr (wordAddr B (c.hiSlot + w)) 8 := fun w hw =>
    slot_wr hp.scr.wr hN (by simp only [Core.hiSlot]; omega) |>.elim fun r ⟨h1, h2⟩ =>
      ⟨r, by rw [hi.wr]; exact h1, h2⟩
  unfold Core.cbcDecGroup
  -- The count, the addresses, and the ciphertext blocks to the buffer.
  refine WP.seq (WP.mono (groupCount_wp hL l13 hi.leftR hv) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_)
  have base₁ : s₁.gpr sb = B := by rw [o₁ _ (by decide) (by decide), hi.base]
  obtain ⟨s₂, e₂, a₂, b₂, t₂, o₂, m₂, rd₂, wr₂⟩ := xorArgs_ok hL d14 s₁ base₁
  refine WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)
  have mem₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  refine WP.seq (WP.mono (copyBlocks_wp (S := A) (T := T) hc0 (by omega)
    (fun t ht => by rw [rd₂', wr₂']; exact inRd (inA t ht)) (fun t ht => by rw [wr₂']; exact inT t ht) dAT
    ⟨by rw [a₂]; simp [T], by rw [b₂, o₁ _ d13 d16, hi.dataR]; simp [A],
      by rw [t₂, c₁, Nat.sub_zero], fun t ht => by omega,
      Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₃ h₃ => ?_)
  have keep₃ : ∀ r, r ∉ ownRegs → s₃.gpr r = s.gpr r := fun r hr => by
    obtain ⟨-, -, h8, -, -, h13, h14, h15, h16, h17⟩ := not_own hr
    rw [h₃.regs r h8 h14 h15 h17, o₂ r h14 h15 h17, o₁ r h13 h16]
  have base₃ : s₃.gpr sb = B := by rw [keep₃ _ (by decide), hi.base]
  have rd₃' : s₃.rd = s.rd := by rw [h₃.rd, rd₂']
  have wr₃' : s₃.wr = s.wr := by rw [h₃.wr, wr₂']
  have f₃ : Frame [⟨T, 16 * cc⟩] s.mem s₃.mem := by rw [← mem₂]; exact h₃.frame
  have ready₃ : cs.Ready s₃ B k := cs.ready_frame hi.ready f₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr subTbuf) fun r hr => by
    obtain ⟨h1, h2, h3⟩ := of_not_modeRegs hr
    exact keep₃ r h1
  -- Decrypted.
  refine WP.seq (WP.mono (cs.crypt_wp base₃ ⟨by rw [wr₃']; exact hwS, hfit⟩ ready₃)
    fun s₄ ⟨base₄, dr₄, lr₄, ready₄, f₄, ks₄, rd₄, wr₄⟩ => ?_)
  have left₄ : s₄.gpr c.leftReg = BitVec.ofNat 64 v := by rw [lr₄, keep₃ _ lown, hi.leftR]
  have data₄ : s₄.gpr c.dataReg = A := by rw [dr₄, keep₃ _ down, hi.dataR]
  refine WP.seq (WP.mono (groupCount_wp hL l13 left₄ hv) fun s₅ ⟨c₅, o₅, m₅, rd₅, wr₅⟩ => ?_)
  have base₅ : s₅.gpr sb = B := by rw [o₅ _ (by decide) (by decide), base₄]
  obtain ⟨s₆, e₆, a₆, b₆, t₆, o₆, m₆, rd₆, wr₆⟩ := xorArgs_ok hL d14 s₅ base₅
  refine WP.seq (WP.of_runBlock ⟨s₆, e₆, ?_⟩)
  have mem₆ : s₆.mem = s₄.mem := by rw [m₆, m₅]
  have rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃']
  have wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃']
  have base₆ : s₆.gpr sb = B := by rw [o₆ _ (by decide) (by decide) (by decide), base₅]
  -- The plaintext blocks.
  refine WP.seq (WP.mono (unchainBlocks_wp (c := c) hL (B := B) (A := T) (E := A) hc0 (by omega) base₆
    (fun t ht => by rw [wr₆']; exact inT t ht) (fun t ht => by rw [wr₆']; exact inA t ht)
    (fun w hw => by rw [wr₆']; exact inH w hw) dAT.symm dTH dAH
    (UInv.init (by rw [a₆]) (by rw [b₆, o₅ _ d13 d16, data₄]) (by rw [t₆, c₅])))
    fun s₇ h₇ => ?_)
  have f₇ : Frame [⟨T, 16 * cc⟩, ⟨A, 16 * cc⟩, ⟨H, 16⟩] s₄.mem s₇.mem := by rw [← mem₆]; exact h₇.frame
  have g₇ : ∀ r, r ∉ ownRegs → s₇.gpr r = s₄.gpr r := fun r hr => by
    obtain ⟨-, -, h8, h9, -, h13, h14, h15, h16, h17⟩ := not_own hr
    rw [h₇.regs r h14 h15 h17 h8 h9, o₆ r h14 h15 h17, o₅ r h13 h16]
  have left₇ : s₇.gpr c.leftReg = BitVec.ofNat 64 v := by rw [g₇ _ lown, left₄]
  have x16₇ : s₇.gpr .x16 = BitVec.ofNat 64 cc := by
    rw [h₇.regs _ (by decide) (by decide) (by decide) (by decide) (by decide), o₆ _ (by decide) (by decide)
      (by decide), c₅]
  -- On to the next group.
  obtain ⟨s₈, e₈, d₈, l₈, o₈, m₈, rd₈, wr₈⟩ := advance_ok hdl d16 s₇
  refine WP.of_runBlock ⟨s₈, e₈, ?_⟩
  have left₈ : s₈.gpr c.leftReg = BitVec.ofNat 64 (v - cc) := by
    rw [l₈, left₇, x16₇, VG.Offset.ofNat_sub_ofNat (by omega)]
  have hz : isa.eval (.nonzero .x c.leftReg) s₈ = some !(decide (v = cc)) := by
    rw [eval_nonzero, left₈, ofNat_beq_zero (by omega)]
    congr 2
    exact decide_eq_decide.mpr (by omega)
  have keep₈ : ∀ r, r ∉ modeRegs c → s₈.gpr r = s₄.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3⟩ := of_not_modeRegs hr
    rw [o₈ r h2 h3, g₇ r h1]
  have ready₈ : cs.Ready s₈ B k := by
    refine cs.ready_frame ready₄ (by rw [m₈]; exact f₇) (fun r hr => ?_) keep₈
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr subTbuf
    · exact .inl (((dDS subCore).sub_left subA).symm)
    · exact .inl dHcore.symm
  -- The bytes, through the steps.
  have hn64 : 16 * n ≤ 2 ^ 64 := by omega
  have outCore : ∀ {R : Region}, Region.Disjoint R (coreRegion c B) → R.len ≤ 2 ^ 64 →
      ∀ i < R.len, s₄.mem (R.base + BitVec.ofNat 64 i) = s₃.mem (R.base + BitVec.ofNat 64 i) := fun hd hl i hi =>
    f₄.bytes (R := _) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hl hi
  have outT : ∀ {R : Region}, Region.Disjoint R ⟨T, 16 * cc⟩ → R.len ≤ 2 ^ 64 →
      ∀ i < R.len, s₃.mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) := fun hd hl i hi =>
    f₃.bytes (R := _) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hl hi
  -- The data before the unchaining: as on entry.
  have dat₄ : ∀ i < 16 * n, s₄.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := fun i hin => by
    rw [outCore (R := ⟨D, 16 * n⟩) (dDS subCore) hn64 i hin, outT (R := ⟨D, 16 * n⟩) (dDS subT) hn64 i hin]
  have chain₄ : ∀ u < 16, s₄.mem (H + BitVec.ofNat 64 u) = s.mem (H + BitVec.ofNat 64 u) := fun u hu => by
    rw [outCore (R := ⟨H, 16⟩) dHcore (show 16 ≤ 2 ^ 64 by decide) u hu,
      outT (R := ⟨H, 16⟩) dTH.symm (show 16 ≤ 2 ^ 64 by decide) u hu]
  have dat0 : ∀ i, 16 * (c.G * g) ≤ i → i < 16 * n → s.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) :=
    fun i h1 h2 => by rw [hi.data i h2, ite_eq_right (by omega)]
  -- The decrypted blocks in the buffer.
  have dec₄ : ∀ t < 16 * cc, s₄.mem (T + BitVec.ofNat 64 t) =
      (cs.cipher k (bytesAt s₀.mem (D + BitVec.ofNat 64 (16 * (c.G * g + t / 16))) 16)).getD (t % 16) 0 := by
    intro t ht
    have hj : t / 16 < c.G := by omega
    have hu : t % 16 < 16 := Nat.mod_lt _ (by decide)
    have eT : T + BitVec.ofNat 64 t = bufAddr c B (t / 16) + BitVec.ofNat 64 (t % 16) := by
      simp only [T, bufAddr]
      rw [addr_add, addr_add, show 8 * c.buf + 16 * (t / 16) + t % 16 = 8 * c.buf + t by omega]
    rw [eT, ← bytesAt_getD s₄.mem _ hu, ks₄ _ hj]
    congr 2
    apply List.ext_getElem (by simp [bytesAt])
    intro u h1 _
    have hu' : u < 16 := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range, bufAddr]
    rw [addr_add, show 8 * c.buf + 16 * (t / 16) + u = 8 * c.buf + (16 * (t / 16) + u) by omega, ← addr_add,
      h₃.copied _ (by omega), mem₂, addr_add, addr_add,
      show 16 * (c.G * g) + (16 * (t / 16) + u) = 16 * (c.G * g + t / 16) + u by omega,
      dat0 _ (by omega) (by omega)]
  have hdata : DInv s₀.mem s₈.mem D n (c.G * g + cc) (cbcOut (cs.cipher k) s₀.mem D iv) := by
    intro i hin
    rw [m₈]
    by_cases hin1 : 16 * (c.G * g) ≤ i ∧ i < 16 * (c.G * g) + 16 * cc
    · let t := i - 16 * (c.G * g)
      have htd : t = i - 16 * (c.G * g) := rfl
      have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 t := by
        rw [addr_add, show 16 * (c.G * g) + t = i by omega]
      rw [e1, h₇.out t (by omega), mem₆, dec₄ t (by omega), ite_eq_left (show i < 16 * (c.G * g + cc) by omega),
        cbcOut_getD (cs.cipher_len k) _ _ hiv _ (Nat.mod_lt _ (by decide)),
        show c.G * g + t / 16 = i / 16 by omega, show t % 16 = i % 16 by omega]
      congr 1
      by_cases h16 : t < 16
      · rw [ite_eq_left h16, chain₄ t h16, hi.chain t h16, show c.G * g = i / 16 by omega,
          show t = i % 16 by omega]
      · rw [ite_eq_right h16, addr_add, dat₄ (16 * (c.G * g) + (t - 16)) (by omega),
          dat0 (16 * (c.G * g) + (t - 16)) (by omega) (by omega), cbcPrev,
          ite_eq_right (show i / 16 ≠ 0 by omega), bytesAt_getD _ _ (Nat.mod_lt _ (by decide)), addr_add,
          show 16 * (c.G * g) + (t - 16) = 16 * (i / 16 - 1) + i % 16 by omega]
    · have hout : ∀ r ∈ [(⟨T, 16 * cc⟩ : Region), ⟨A, 16 * cc⟩, ⟨H, 16⟩], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 :=
        fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact fun h => (dDS subT) _ (VG.Offset.contains_base D (by omega) (by omega)) h
          · exact not_contains_off D (by omega) (by omega) (by omega) (by omega)
          · exact fun h => (dDS subH) _ (VG.Offset.contains_base D (by omega) (by omega)) h
      rw [f₇ _ hout, dat₄ i hin, hi.data i hin]
      by_cases h2 : i < 16 * (c.G * g)
      · rw [ite_eq_left h2, ite_eq_left (show i < 16 * (c.G * g + cc) by omega)]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ i < 16 * (c.G * g + cc) by omega)]
  -- The chaining value: the group's last ciphertext block.
  have chain₈ : ∀ u < 16, s₈.mem (H + BitVec.ofNat 64 u) = (cbcPrev s₀.mem D iv (c.G * g + cc)).getD u 0 := by
    intro u hu
    rw [m₈, h₇.chain u hu, ite_eq_right (by omega), mem₆, addr_add, dat₄ (16 * (c.G * g) + (16 * (cc - 1) + u))
      (by omega), dat0 (16 * (c.G * g) + (16 * (cc - 1) + u)) (by omega) (by omega), cbcPrev,
      ite_eq_right (by omega), bytesAt_getD _ _ hu, addr_add,
      show 16 * (c.G * g) + (16 * (cc - 1) + u) = 16 * (c.G * g + cc - 1) + u by omega]
  -- The slots.
  have wS : ∀ j, c.slots ≤ j → j < c.slots + 10 → ∀ r ∈ [(⟨T, 16 * cc⟩ : Region), ⟨A, 16 * cc⟩, ⟨H, 16⟩],
      Region.Disjoint ⟨wordAddr B j, 8⟩ r := fun j h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Offset.disjoint B (by omega) (by omega) (by omega)
    · exact (((dDS (subS (show 8 * j + 8 ≤ 8 * c.total by omega))).sub_left subA).symm)
    · exact VG.Offset.disjoint B (by simp only [Core.hiSlot]; omega) (by omega) (by simp only [Core.hiSlot]; omega)
  have saved₈ : ∀ i < 10, s₈.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi10 => by
    rw [m₈, ← hi.saved i hi10]
    refine (f₇.readW (Region.contains_self _ _) (wS _ (by omega) (by omega)) (by decide)).trans ?_
    refine (f₄.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base B (by omega) (by omega)) (by decide)).trans ?_
    exact f₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint B (by omega) (by omega) (by omega)) (by decide)
  have fr : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s₀.mem s₈.mem := by
    rw [m₈]
    refine hi.frame.trans (((f₃.sub fun r hr => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; exact subT⟩).trans
      (f₄.sub fun r hr => ⟨⟨B, 8 * c.total⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subCore⟩)).trans (f₇.sub fun r hr => ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, subT⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subA⟩
    · exact ⟨_, List.mem_cons_self, subH⟩
  have base₈ : s₈.gpr sb = B := by rw [o₈ _ (Ne.symm dsb) (Ne.symm lsb), g₇ _ (by decide), base₄]
  have rd₈' : s₈.rd = s₀.rd := by rw [rd₈, h₇.rd, rd₆', hi.rd]
  have wr₈' : s₈.wr = s₀.wr := by rw [wr₈, h₇.wr, wr₆', hi.wr]
  by_cases hdone : v = cc
  · refine .inl ⟨by rw [hz, decide_eq_true hdone]; rfl, base₈, saved₈, ?_, fr, rd₈', wr₈'⟩
    rw [show n = c.G * g + cc by omega] at hdata ⊢
    exact hdata
  · have hcc : cc = c.G := by omega
    refine .inr ⟨by rw [hz, decide_eq_false hdone]; rfl, base₈, ready₈, saved₈, ?_, ?_,
      by rw [Nat.mul_succ]; omega, ?_,
      by rw [show c.G * (g + 1) = c.G * g + cc by rw [hcc, Nat.mul_succ]]; exact hdata, fr, rd₈', wr₈'⟩
    · rw [d₈, h₇.x15, addr_add, hcc,
        show 16 * (c.G * g) + 16 * c.G = 16 * (c.G * (g + 1)) by rw [Nat.mul_succ]; omega]
    · rw [left₈, hcc, show v - c.G = n - c.G * (g + 1) by rw [Nat.mul_succ]; omega]
    · rw [show c.G * (g + 1) = c.G * g + cc by rw [hcc, Nat.mul_succ]]; exact chain₈

/-- The data loop. -/
theorem cbcDecLoop_wp (cs : CoreSpec c) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} {iv : List Byte}
    (hiv : iv.length = 16) (hp : GPre c s₀ B D n) {s : State} (hi : CInv cs s₀ B D n k iv 0 s) :
    WP isa (.loop c.cbcDecGroup (.nonzero .x c.leftReg)) s (CDone cs s₀ B D n k iv) := by
  refine WP.loop (M := isa) (fun m s => ∃ g, m = n - c.G * g ∧ CInv cs s₀ B D n k iv g s) (fun m s hs => ?_) n s
    ⟨0, by simp, hi⟩
  obtain ⟨g, rfl, hg⟩ := hs
  refine WP.mono (cbcDecGroup_wp cs hiv hp hg) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · have hG := cs.layout.G_pos
    exact .inr ⟨z, n - c.G * (g + 1),
      by have := d.lt; have := hg.lt; rw [Nat.mul_succ] at *; omega, g + 1, rfl, d⟩

end VG.Proof.Modes.AArch64
