module

public import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
public import VerifiedGarbage.Impl.Modes.AArch64.FbFinal
public import VerifiedGarbage.Proof.Modes.AArch64.FbFinalTail
public import VerifiedGarbage.Proof.Modes.FbFinal
import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# OFB and CFB of a message's last piece on AArch64, for any core: the loop

As on x86-64 (`Proof/Modes/X86_64/FbFinalLoop.lean`). `fbSeg_wp`: one
segment of `fbFinal`'s loop enciphers its input block `Iⱼ` in the buffer
(`BlockSpec.crypt_wp`), giving `Oⱼ`; `x8 := leftReg >> lg` is zero exactly
when fewer than `L` bytes are left (`lsr_beq`, `two_pow_fbLg`). If a whole
block of the `len` bytes is left, it makes the block `fbOut` and the buffer
`Iⱼ₊₁` (`fbIn`), as `fb`'s (`fbBlock_wp`); if `r < L` bytes are left, it
XORs the first `r` bytes of `Oⱼ` into them (`xorLoop_wp`), which are then
those of `fbOut j`, and leaves `Oⱼ` in the buffer. Blocks are `L = 8 bw`
bytes.
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Modes (FbMode)
open VG.Impl.Aes.AArch64 (sb movR ldS stS eorR)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- `x8 := leftReg >> lg` tests for fewer than a block's `8 bw` bytes. -/
theorem two_pow_fbLg (h0 : 0 < c.bw) (h2 : c.bw ≤ 2) : 2 ^ c.fbLg = 8 * c.bw := by
  have : ∀ b < 3, 0 < b → 2 ^ (2 + b) = 8 * b := by decide
  exact this c.bw (by omega) h0

/-- What the loop works on: the scratch buffer at `B`, the `len` bytes at
`D`. -/
structure FPre (c : Core) (s₀ : State) (B D : Addr) (len : Nat) : Prop where
  scr : ScrIn s₀ B c.total
  dat : (⟨D, len⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, len⟩ ⟨B, 8 * c.total⟩
  fitD : D.toNat + len ≤ 2 ^ 64
  small : len < 2 ^ 64

/-- The loop, before segment `j`; `m₀` is the memory on entry, `iv` the IV. -/
structure FInvF (cs : BlockSpec c) (mo : FbMode) (ivR : Reg) (s₀ : State) (m₀ : Mem) (B D : Addr) (len : Nat)
    (k : cs.Key) (iv : List Byte) (j : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  ready : cs.Ready s B k
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * j)
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (len - 8 * c.bw * j)
  lt : 8 * c.bw * j < len
  buf : ∀ u < 8 * c.bw, s.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
    (fbIn mo (8 * c.bw) (cs.cipher k) m₀ D iv j).getD u 0
  data : ∀ i < len, s.mem (D + BitVec.ofNat 64 i) =
    if i < 8 * c.bw * j then (fbOut mo (8 * c.bw) (cs.cipher k) m₀ D iv (i / (8 * c.bw))).getD (i % (8 * c.bw)) 0
    else m₀ (D + BitVec.ofNat 64 i)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, len⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ivK : s.gpr ivR = s₀.gpr ivR

/-- The loop, done. -/
structure FDoneF (cs : BlockSpec c) (mo : FbMode) (ivR : Reg) (s₀ : State) (m₀ : Mem) (B D : Addr) (len : Nat)
    (k : cs.Key) (iv : List Byte) (s : State) : Prop where
  base : s.gpr sb = B
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  buf : ∀ u < 8 * c.bw, s.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
    (fbNextF mo (8 * c.bw) (cs.cipher k) m₀ D iv len).getD u 0
  data : ∀ i < len, s.mem (D + BitVec.ofNat 64 i) =
    (fbOut mo (8 * c.bw) (cs.cipher k) m₀ D iv (i / (8 * c.bw))).getD (i % (8 * c.bw)) 0
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, len⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ivK : s.gpr ivR = s₀.gpr ivR

theorem fbSeg_wp (cs : BlockSpec c) (mo : FbMode) {ivR : Reg} (hivR : ivR ∉ modeRegs c) {s₀ : State} {m₀ : Mem}
    {B D : Addr} {len : Nat} {k : cs.Key} {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : FPre c s₀ B D len)
    (hsc : KeepsReg ivR c.crypt) {j : Nat} {s : State} (hi : FInvF cs mo ivR s₀ m₀ B D len k iv j s) :
    WP isa (c.fbSeg mo) s fun s' =>
      (isa.eval (.nonzero .x c.leftReg) s' = some false ∧ FDoneF cs mo ivR s₀ m₀ B D len k iv s') ∨
      (isa.eval (.nonzero .x c.leftReg) s' = some true ∧ FInvF cs mo ivR s₀ m₀ B D len k iv (j + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hbI := hL.bufImm
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hj := hi.lt
  have hL0 : 0 < 8 * c.bw := by omega_arith
  have hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hj1 : 8 * c.bw * (j + 1) = 8 * c.bw * j + 8 * c.bw := Nat.mul_succ _ _
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨down, dsb, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨lown, lsb, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨d6, d7, d8, d9, -⟩ := not_own down
  obtain ⟨l6, l7, l8, l9, -⟩ := not_own lown
  obtain ⟨iown, idr, ilr⟩ := of_not_modeRegs hivR
  obtain ⟨i6, i7, i8, i9, -⟩ := not_own iown
  have hlen64 : len ≤ 2 ^ 64 := by omega_arith
  have hsmall := hp.small
  let ciph := cs.cipher k
  let A := D + BitVec.ofNat 64 (8 * c.bw * j)
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have hwS : (⟨B, 8 * c.total⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, len⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have subT : Region.Sub ⟨T, 8 * c.bw⟩ ⟨B, 8 * c.total⟩ := VG.Offset.sub_base B (by omega_arith)
  have subTbuf : Region.Sub ⟨T, 8 * c.bw⟩ (blkRegion c B) := Region.sub_prefix hLG
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.total⟩ := Region.sub_prefix (by omega_arith)
  have dDS : ∀ {r : Region}, Region.Sub r ⟨B, 8 * c.total⟩ → Region.Disjoint ⟨D, len⟩ r :=
    fun h => hp.sep.sub_right h
  have hw : ∀ w, 8 * c.bw * j + 8 * w = 8 * (c.bw * j + w) := fun w => by rw [Nat.mul_add, Nat.mul_assoc]
  have inT : ∀ w < c.bw, InRegions s.wr (T + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
    ⟨_, hwS, by rw [addr_add]; exact VG.Offset.contains_base B (by omega_arith) (by omega_arith)⟩
  -- Enciphered.
  unfold Core.fbSeg
  refine WP.seq (WP.mono (WP.keepReg hsc (cs.crypt_wp hi.base ⟨hwS, hfit⟩ hi.ready))
    fun s₂ ⟨⟨base₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩, i₂⟩ => ?_)
  have eT : blkAddr c B 0 = T := by simp only [blkAddr, T, Nat.mul_zero, Nat.add_zero]
  have hin : bytesAt s.mem T (8 * c.bw) = fbIn mo (8 * c.bw) ciph m₀ D iv j := by
    apply List.ext_getElem (by
      simp only [bytesAt, List.length_map, List.length_range]; rw [fbIn_length (cs.cipher_len k) m₀ D hiv])
    intro u h1 _
    have hu : u < 8 * c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [hi.buf u hu, List.getElem_eq_getD 0]
  have E₂ : ∀ u < 8 * c.bw, s₂.mem (T + BitVec.ofNat 64 u) = (ciph (fbIn mo (8 * c.bw) ciph m₀ D iv j)).getD u 0 :=
    fun u hu => by rw [← bytesAt_getD s₂.mem T hu, ← eT, ks₂ 0 hG0, eT, hin]
  have D₂ : ∀ i < len, s₂.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := fun i hi' =>
    f₂.bytes (R := ⟨D, len⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact dDS subCore) hlen64 hi'
  have mA : ∀ u, 8 * c.bw * j + u < len → s.mem (A + BitVec.ofNat 64 u) = m₀ (A + BitVec.ofNat 64 u) := fun u hu => by
    rw [addr_add, hi.data _ hu, ite_eq_right (by omega_arith)]
  have D₂' : ∀ u, 8 * c.bw * j + u < len → s₂.mem (A + BitVec.ofNat 64 u) = s.mem (A + BitVec.ofNat 64 u) :=
    fun u hu => by rw [addr_add]; exact D₂ _ hu
  -- Whether a whole block is left.
  have hleft : s₂.gpr c.leftReg = BitVec.ofNat 64 (len - 8 * c.bw * j) := by rw [lr₂, hi.leftR]
  obtain ⟨s₃, e₃, x8₃, g₃, m₃, rd₃, wr₃⟩ := lsr_ok s₂ .x8 c.leftReg (sh := c.fbLg)
    (by simp only [Core.fbLg]; omega_arith)
  have hz₃ : isa.eval (.zero .x .x8) s₃ = some (decide (len - 8 * c.bw * j < 8 * c.bw)) := by
    rw [eval_zero, x8₃, hleft, lsr_beq (by omega_arith), two_pow_fbLg hbw0 hbw2]
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have sy₃ : s₃.syms = s₂.syms := runBlock_syms e₃
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, hi.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, hi.wr]
  have data₃ : s₃.gpr c.dataReg = A := by rw [g₃ _ d8, dr₂, hi.dataR]
  have base₃ : s₃.gpr sb = B := by rw [g₃ _ (by decide), base₂]
  -- The slots: none of the core's, nor in the data or the buffer's first block.
  have slotOut : ∀ i < 10, ∀ {R : Region}, (Region.Sub R ⟨D, len⟩ ∨ R = ⟨T, 8 * c.bw⟩ ∨
      R = coreRegion c B) → Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ R := fun i hi10 R hR => by
    rcases hR with h | rfl | rfl
    · exact ((dDS (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.total by
        omega_arith))).sub_left h).symm
    · exact VG.Offset.disjoint B (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact VG.Offset.disjoint_base B (by omega_arith) (by omega_arith)
  have saved₂ : ∀ i < 10, s₂.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64 :=
    fun i hi10 => by
      rw [← hi.saved i hi10]
      exact f₂.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact slotOut i hi10 (.inr (.inr rfl))) (by decide)
  have fr₂ : Frame [⟨B, 8 * c.total⟩, ⟨D, len⟩] s₀.mem s₂.mem :=
    hi.frame.trans (f₂.sub fun x hx => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hx; subst hx; exact subCore⟩)
  refine WP.ite (decide (len - 8 * c.bw * j < 8 * c.bw)) hz₃ (fun hb => ?_) (fun hb => ?_)
  · -- A partial segment: `r` bytes.
    have hb' : len - 8 * c.bw * j < 8 * c.bw := by simpa using hb
    let r := len - 8 * c.bw * j
    have hr0 : 0 < r := by omega_arith
    have hdiv : len / (8 * c.bw) = j := by
      rw [show len = 8 * c.bw * j + r by omega_arith]; exact idx_div hb'
    have hmod : len % (8 * c.bw) = r := by
      rw [show len = 8 * c.bw * j + r by omega_arith]; exact idx_mod hb'
    obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ .x9 sb (v := 8 * c.buf) hbI
    have x9₄ : s₄.gpr .x9 = T := by rw [a₄, base₃]
    have g₄ : ∀ x, x ≠ .x9 → x ≠ .x8 → s₄.gpr x = s₂.gpr x := fun x h1 h2 => by rw [o₄ x h1, g₃ x h2]
    have mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₃]
    have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃']
    have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃']
    have subTr : Region.Sub ⟨T, r⟩ ⟨T, 8 * c.bw⟩ := Region.sub_prefix (by omega_arith)
    have subAr : Region.Sub ⟨A, r⟩ ⟨D, len⟩ := VG.Offset.sub_base D (by omega_arith)
    have hxp : XPre s₄ T A r c.dataReg c.leftReg :=
      { pos := hr0
        small := by omega_arith
        disj := ((dDS subT).sub_left subAr).sub_right subTr |>.symm
        rdK := fun q hq => by
          rw [rd₄', wr₄']
          exact inRd ⟨_, hp.scr.wr, by
            rw [addr_add]; exact VG.Offset.contains_base B (by omega_arith) (by omega_arith)⟩
        wrR := fun q hq => by
          rw [wr₄']
          exact ⟨_, hp.dat, by rw [addr_add]; exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)⟩
        dl := hdl
        d9 := ⟨d9, l9⟩
        d6 := ⟨d6, l6⟩
        d7 := ⟨d7, l7⟩ }
    have hx0 : XInv s₄ T A r c.dataReg c.leftReg 0 s₄ :=
      { x9 := by rw [x9₄]; simp
        dat := by rw [g₄ _ d9 d8, dr₂, hi.dataR]; simp [A]
        left := by rw [g₄ _ l9 l8, hleft, Nat.sub_zero]
        lt := hr0
        data := fun q hq => by rw [ite_eq_right (Nat.not_lt_zero _)]
        frame := Frame.refl _ _
        rd := rfl
        wr := rfl
        gpr := fun _ _ _ _ _ _ => rfl }
    refine WP.seq (WP.of_runBlock ⟨s₄, e₄, WP.mono (xorLoop_wp hxp hx0) fun s₅ d₅ => .inl ⟨by
      rw [eval_nonzero, d₅.left]; rfl, ?_⟩⟩)
    have f₅ : Frame [⟨A, r⟩] s₂.mem s₅.mem := by rw [← mem₄]; exact d₅.frame
    have g₅ : ∀ x, x ≠ .x9 → x ≠ .x6 → x ≠ .x7 → x ≠ .x8 → x ≠ c.dataReg → x ≠ c.leftReg →
        s₅.gpr x = s₂.gpr x :=
      fun x h1 h2 h3 h4 h5 h6 => by rw [d₅.gpr x h1 h2 h3 h5 h6, g₄ x h1 h4]
    have kT : ∀ u < 8 * c.bw, s₅.mem (T + BitVec.ofNat 64 u) = s₂.mem (T + BitVec.ofNat 64 u) := fun u hu =>
      f₅.bytes (R := ⟨T, 8 * c.bw⟩) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact ((dDS subT).sub_left subAr).symm)
        (show 8 * c.bw ≤ 2 ^ 64 by omega_arith) hu
    refine ⟨by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (Ne.symm dsb) (Ne.symm lsb), base₂],
      fun i hi10 => ?_, fun u hu => ?_, fun i hi' => ?_, ?_, by rw [d₅.rd, rd₄'], by rw [d₅.wr, wr₄'],
      by rw [g₅ _ i9 i6 i7 i8 idr ilr, i₂, hi.ivK]⟩
    · rw [← saved₂ i hi10]
      exact f₅.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact slotOut i hi10 (.inl subAr)) (by decide)
    · rw [kT u hu, E₂ u hu, fbNextF, ite_eq_right (by rw [hmod]; omega_arith), hdiv]
    · by_cases hlt : i < 8 * c.bw * j
      · have out : ∀ R ∈ [(⟨A, r⟩ : Region)], ¬ R.Contains (D + BitVec.ofNat 64 i) 1 := fun R hR => by
          simp only [List.mem_singleton] at hR; subst hR
          exact not_contains_off D (.inl hlt) (by omega_arith) hr0 (by omega_arith)
        rw [f₅ _ out, D₂ i hi', hi.data i hi', ite_eq_left hlt]
      · obtain ⟨q, rfl⟩ : ∃ q, i = 8 * c.bw * j + q := ⟨i - 8 * c.bw * j, by omega_arith⟩
        have hq : q < r := by omega_arith
        have e := d₅.data q hq
        rw [mem₄] at e
        rw [← addr_add, e, idx_div (by omega_arith), idx_mod (by omega_arith), D₂' q (by omega_arith),
          mA q (by omega_arith), fbOut_getD mo (cs.cipher_len k) m₀ D iv j (by omega_arith), E₂ q (by omega_arith),
          addr_add]
    · exact fr₂.trans (f₅.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subAr⟩)
  · -- A whole block.
    have hb' : 8 * c.bw ≤ len - 8 * c.bw * j := by simpa using hb
    have hjl : 8 * c.bw * j + 8 * c.bw ≤ len := by omega_arith
    have subA : Region.Sub ⟨A, 8 * c.bw⟩ ⟨D, len⟩ := VG.Offset.sub_base D hjl
    have dAT : Region.Disjoint ⟨A, 8 * c.bw⟩ ⟨T, 8 * c.bw⟩ := (dDS subT).sub_left subA
    have inA : ∀ w < c.bw, InRegions s.wr (A + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
      ⟨_, hwD, by rw [addr_add]; exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)⟩
    refine WP.block_append (WP.mono_syms (fbOp_wp mo (by omega_arith) (by omega_arith) data₃ (by rw [base₃]) d6 d7
      (fun w hw' => by rw [wr₃, wr₂]; exact inA w hw') (fun w hw' => by rw [wr₃, wr₂]; exact inT w hw') dAT
      (by omega_arith)) fun s₃a ⟨g₃a, rd₃a, wr₃a, mA₃, mT₃, f₃a⟩ sy₃a => ?_)
    obtain ⟨s₃b, e₃b, a₃b, o₃b, m₃b, rd₃b, wr₃b⟩ := addImm_ok s₃a c.dataReg c.dataReg (v := 8 * c.bw)
      (by omega_arith)
    obtain ⟨s₄, e₄, l₄, o₄, m₄, rd₄, wr₄⟩ := subImm_ok s₃b c.leftReg c.leftReg (v := 8 * c.bw) (by omega_arith)
    refine WP.of_runBlock ⟨s₄, by
      rw [Core.fbNextBytes, show ([.addImm .x c.dataReg c.dataReg (8 * c.bw),
        .subImm .x c.leftReg c.leftReg (8 * c.bw)] : List Instr) =
        [.addImm .x c.dataReg c.dataReg (8 * c.bw)] ++ [.subImm .x c.leftReg c.leftReg (8 * c.bw)] from rfl,
        runBlock_app, e₃b, Option.bind_some, e₄], ?_⟩
    have keep₄ : ∀ x, x ≠ .x6 → x ≠ .x7 → x ≠ .x8 → x ≠ c.dataReg → x ≠ c.leftReg → s₄.gpr x = s₂.gpr x :=
      fun x h1 h2 h3 h4 h5 => by rw [o₄ x h5, o₃b x h4, g₃a x h1 h2, g₃ x h3]
    have left₃ : s₃b.gpr c.leftReg = BitVec.ofNat 64 (len - 8 * c.bw * j) := by
      rw [o₃b _ (Ne.symm hdl), g₃a _ l6 l7, g₃ _ l8, hleft]
    have left₄ : s₄.gpr c.leftReg = BitVec.ofNat 64 (len - 8 * c.bw * (j + 1)) := by
      rw [l₄, left₃, VG.Offset.ofNat_sub_ofNat hb', hj1, Nat.sub_sub]
    have hz₄ : isa.eval (.nonzero .x c.leftReg) s₄ = some !(decide (8 * c.bw * (j + 1) = len)) := by
      rw [eval_nonzero, left₄, ofNat_beq_zero (by omega_arith),
        decide_eq_decide.mpr (show len - 8 * c.bw * (j + 1) = 0 ↔ 8 * c.bw * (j + 1) = len by omega_arith)]
    have hAL : A + BitVec.ofNat 64 (8 * c.bw) = D + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := by rw [addr_add, hj1]
    have data₄ : s₄.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := by
      rw [o₄ _ hdl, a₃b, g₃a _ d6 d7, data₃, hAL]
    have mem₄ : s₄.mem = s₃a.mem := by rw [m₄, m₃b]
    have base₄ : s₄.gpr sb = B := by
      rw [keep₄ _ (by decide) (by decide) (by decide) (Ne.symm dsb) (Ne.symm lsb), base₂]
    have ivK₄ : s₄.gpr ivR = s₀.gpr ivR := by rw [keep₄ _ i6 i7 i8 idr ilr, i₂, hi.ivK]
    have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃b, rd₃a, rd₃']
    have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃b, wr₃a, wr₃']
    have f₃ : Frame [⟨A, 8 * c.bw⟩, ⟨T, 8 * c.bw⟩] s₂.mem s₄.mem := by rw [mem₄, ← m₃]; exact f₃a
    have saved₄ : ∀ i < 10, s₄.mem.readW (wordAddr B (c.slots + i)) 64 =
        s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi10 => by
      rw [← saved₂ i hi10]
      exact f₃.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact slotOut i hi10 (.inl subA)
        · exact slotOut i hi10 (.inr (.inl rfl))) (by decide)
    have fr₄ : Frame [⟨B, 8 * c.total⟩, ⟨D, len⟩] s₀.mem s₄.mem :=
      fr₂.trans (f₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subA⟩
        · exact ⟨_, List.mem_cons_self, subT⟩)
    have ready₄ : cs.Ready s₄ B k := cs.ready_frame ready₂ f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl ((dDS subCore).sub_left subA).symm
      · exact .inr subTbuf)
      ⟨fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, by rw [wr₂]; exact hwD, subA⟩
        · exact ⟨_, by rw [wr₂]; exact hwS, subT⟩,
        by rw [rd₄, rd₃b, rd₃a, rd₃], by rw [wr₄, wr₃b, wr₃a, wr₃],
        by rw [runBlock_syms e₄, runBlock_syms e₃b, sy₃a, sy₃]⟩
      fun r hr => by
      obtain ⟨h1, h2, h3⟩ := of_not_modeRegs hr
      obtain ⟨n6, n7, n8, -⟩ := not_own h1
      exact keep₄ r n6 n7 n8 h2 h3
    have buf₄ : ∀ u < 8 * c.bw, s₄.mem (T + BitVec.ofNat 64 u) =
        (fbIn mo (8 * c.bw) ciph m₀ D iv (j + 1)).getD u 0 := fun u hu => by
      rw [mem₄, mT₃ u hu, m₃, E₂ u hu, D₂' u (by omega_arith), mA u (by omega_arith),
        fbIn_succ_getD mo (cs.cipher_len k) m₀ D iv j hu, addr_add]
    have data₄' : ∀ i < len, s₄.mem (D + BitVec.ofNat 64 i) =
        if i < 8 * c.bw * (j + 1) then (fbOut mo (8 * c.bw) ciph m₀ D iv (i / (8 * c.bw))).getD (i % (8 * c.bw)) 0
        else m₀ (D + BitVec.ofNat 64 i) := fun i hi' => by
      by_cases hin : 8 * c.bw * j ≤ i ∧ i < 8 * c.bw * (j + 1)
      · obtain ⟨q, rfl⟩ : ∃ q, i = 8 * c.bw * j + q := ⟨i - 8 * c.bw * j, by omega_arith⟩
        have hq : q < 8 * c.bw := by omega_arith
        rw [ite_eq_left hin.2, idx_div hq, idx_mod hq, fbOut_getD mo (cs.cipher_len k) m₀ D iv j hq, mem₄, ← addr_add,
          mA₃ q hq, m₃, E₂ q hq, D₂' q (by omega_arith), mA q (by omega_arith)]
      · have out : ∀ R ∈ [(⟨A, 8 * c.bw⟩ : Region), ⟨T, 8 * c.bw⟩],
            ¬ R.Contains (D + BitVec.ofNat 64 i) 1 := fun R hR => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
          rcases hR with rfl | rfl
          · exact not_contains_off D (by omega_arith) (by omega_arith) hL0 (by omega_arith)
          · exact fun hc => dDS subT _ (VG.Offset.contains_base D (by omega_arith) (by omega_arith)) hc
        rw [mem₄, f₃a _ out, m₃, D₂ i hi', hi.data i hi']
        by_cases h3 : i < 8 * c.bw * j
        · rw [ite_eq_left h3, ite_eq_left (by omega_arith)]
        · rw [ite_eq_right h3, ite_eq_right (by omega_arith)]
    by_cases hdone : 8 * c.bw * (j + 1) = len
    · refine .inl ⟨by rw [hz₄, decide_eq_true hdone]; rfl, base₄, saved₄, fun u hu => ?_,
        fun i hi' => by rw [data₄' i hi', ite_eq_left (by omega_arith)], fr₄, rd₄', wr₄', ivK₄⟩
      have hmod : len % (8 * c.bw) = 0 := by rw [← hdone]; exact Nat.mul_mod_right _ _
      have hdiv : len / (8 * c.bw) = j + 1 := by rw [← hdone]; exact Nat.mul_div_cancel_left _ hL0
      rw [buf₄ u hu, fbNextF, ite_eq_left hmod, hdiv]
    · exact .inr ⟨by rw [hz₄, decide_eq_false hdone]; rfl, base₄, ready₄, saved₄, data₄, left₄, by omega_arith,
        buf₄, data₄', fr₄, rd₄', wr₄', ivK₄⟩

/-- The loop. -/
theorem fbFinalLoop_wp (cs : BlockSpec c) (mo : FbMode) {ivR : Reg} (hivR : ivR ∉ modeRegs c) {s₀ : State}
    {m₀ : Mem} {B D : Addr} {len : Nat} {k : cs.Key} {iv : List Byte} (hiv : iv.length = 8 * c.bw)
    (hp : FPre c s₀ B D len) (hsc : KeepsReg ivR c.crypt) {s : State}
    (hi : FInvF cs mo ivR s₀ m₀ B D len k iv 0 s) :
    WP isa (.loop (c.fbSeg mo) (.nonzero .x c.leftReg)) s (FDoneF cs mo ivR s₀ m₀ B D len k iv) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = len - 8 * c.bw * j ∧ FInvF cs mo ivR s₀ m₀ B D len k iv j s)
    (fun m s hs => ?_) len s ⟨0, by simp, hi⟩
  obtain ⟨j, rfl, hj⟩ := hs
  have hbw0 := cs.layout.bw_pos
  refine WP.mono (fbSeg_wp cs mo hivR hiv hp hsc hj) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, len - 8 * c.bw * (j + 1), by
      have := d.lt; have := hj.lt; rw [Nat.mul_succ]; omega, j + 1, rfl, d⟩

end VG.Proof.Modes.AArch64
