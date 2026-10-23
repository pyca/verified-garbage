module

public import VerifiedGarbage.Proof.RsaPss.Arm.CtComp
public import VerifiedGarbage.Proof.RsaPss.Arm.CtSel
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.CtPad
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.Arm.Step
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS on ARMv7: hashing, the compression loop

`compLoop_vp`: every one of `Y`'s `nbm` blocks compressed into the hash
value at `oSt`, and the hash value after block `lb` (the last of the padded
message, `⌊(ℓ + L) / B⌋`, under a mask) selected into `oSel`: it is that of
`Y`'s first `lb + 1` blocks.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)
open VG.Proof.MdStream (Md)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- What the compression loop writes. -/
abbrev loopW (L : Lay) (scr : BitVec 32) : List Region :=
  [sR scr oSt h.N, sR scr oCW h.H.md.so, sR scr oSel h.N, slotR L sBi]

/-- The memory of the loop's state after `b` blocks, from `Y`'s bytes `yv`
(`T` of them), with `lb` the last block of the padded message. -/
structure CM (L : Lay) (scr : BitVec 32) (T : Nat) (yv : Nat → Byte) (lb b : Nat) (m : Mem) : Prop where
  y : ∀ i < T, m (sa scr (oY + i)) = yv i
  bi : m.readW (L.fr sBi) 32 = BitVec.ofNat 32 b
  st : h.md.stateAt m (sa scr oSt) = h.md.compressList h.ok.iv (ylist yv T) b
  sel : lb < b → h.md.stateAt m (sa scr oSel) = h.md.compressList h.ok.iv (ylist yv T) (lb + 1)

theorem ofNat_shl {x : Nat} (hx : x * h.B < 2 ^ 32) : BitVec.ofNat 32 x <<< lgB h.H = BitVec.ofNat 32 (x * h.B) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, h.pow_lg,
    Nat.mod_eq_of_lt (a := x) (by have := Nat.le_mul_of_pos_right x (show 0 < h.B by have := h.B_ge; omega); omega)]

theorem slot_frame (L : Lay) (m : Mem) (d : Nat) (v : BitVec 32) : Frame [slotR L d] m (m.writeW (L.fr d) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem neg_bit (c : Prop) [Decidable c] : (0 : BitVec 32) - (if c then 1 else 0) = maskOf c := by
  by_cases hc : c <;> simp [maskOf, hc]

theorem neg_bit' (c : Prop) [Decidable c] : 0#32 - (if c then 1 else 0) = maskOf c := neg_bit c

/-- The compression loop. -/
theorem compLoop_vp (hg : Geo L scr) {nbm : Nat} (hnb : nbm * h.B ≤ 2048) (hnb0 : 0 < nbm)
    {yv : State → Nat → Byte} {ℓ : State → Nat} (hℓ : ∀ σ, (ℓ σ + h.L) / h.B < nbm) (hℓ2 : ∀ σ, ℓ σ < 2048)
    {Inv : State → Mem → Prop} (hI : ∀ σ m m', Inv σ m → Frame (loopW h L scr) m m' → Inv σ m')
    (hsl : ∀ σ m, Inv σ m → m.readW (L.fr sL) 32 = BitVec.ofNat 32 (ℓ σ))
    (hsn : ∀ σ m, Inv σ m → m.readW (L.fr sNb) 32 = BitVec.ofNat 32 nbm) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ (∀ i < nbm * h.B, s.mem (sa scr (oY + i)) = yv σ i) ∧
        h.md.stateAt s.mem (sa scr oSt) = h.ok.iv)
      (compLoop h.H)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ h.md.stateAt s.mem (sa scr oSel) =
        h.md.compressList h.ok.iv (ylist (yv σ) (nbm * h.B)) ((ℓ σ + h.L) / h.B + 1)) := by
  have hN := h.N_le
  have hBl := h.B_le
  have hB64 := h.B_ge
  have hL := h.L_le
  have hso := h.so_le
  have fit := hg.fit
  obtain ⟨σ', ok⟩ := hg.ok
  have nbB : nbm ≤ nbm * h.B := Nat.le_mul_of_pos_right nbm (by omega_arith)
  generalize hT : nbm * h.B = T at hnb nbB ⊢
  -- Disjointness of what the loop writes from what it keeps.
  have dY : ∀ r ∈ loopW h L scr, Region.Disjoint (sR scr oY T) r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Geo.sep (by pomega) (by pomega) (by pomega)
    · exact Geo.sep (by pomega) (by pomega) (by pomega)
    · exact Geo.sep (by pomega) (by pomega) (by pomega)
    · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm
  have dB : ∀ r ∈ [sR scr oSt h.N, sR scr oCW h.H.md.so, sR scr oSel h.N], (slotR L sBi).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg.slot ok (by pomega) (by rw [hg.F]; decide)
  have dBN : ∀ r ∈ [slotR L sBi], (slotR L sNb).Disjoint r ∧ (slotR L sL).Disjoint r ∧ (slotR L sS).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨Lay.fr_sep (by decide) (by decide) (by decide), Lay.fr_sep (by decide) (by decide) (by decide),
      Lay.fr_sep (by decide) (by decide) (by decide)⟩
  have sp_eq : ∀ {F : State → State → Prop}, (∀ σ s, F σ s → Ctx L scr σ s) →
      ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.sp = s₂.sp :=
    fun hF _ _ _ _ h₁ h₂ => (hF _ _ h₁).st.sp.trans (hF _ _ h₂).st.sp.symm
  let CS : Nat → State → State → Prop := fun b σ s =>
    Ctx L scr σ s ∧ Inv σ s.mem ∧ CM h L scr T (yv σ) (((ℓ σ + h.L) / h.B)) b s.mem
  -- The first block.
  refine VP.seq (G := CS 0) (VP.blk (blkOk rfl) (sp_eq fun _ _ h => h.1) fun σ s ⟨hc, hi, hy, hst⟩ => ?_) ?_
  · have hw : WP isa (.block compInit) s fun t => t.mem = s.mem.writeW (L.fr sBi) (0 : BitVec 32) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [compInit, sp0, mw, st, hc.st.sp, hc.aFr hg, hc.wFr hg]
    refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
    have fr : Frame [slotR L sBi] s.mem t.mem := by rw [m]; exact slot_frame L _ _ _
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ((dBN r hr).2.2)) rd wr sp, hI σ _ _ hi (fr.mono ?_),
      ⟨sbytes_keep fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dY _ (by simp [loopW])) (by pomega) hy, ?_, ?_, fun h0 => absurd h0 (Nat.not_lt_zero _)⟩⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.FR, List.mem_cons_self, Offset.sub_base _ (by rw [hg.F]; decide)⟩
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp
    · rw [m, Mem.readW_writeW_self32]; rfl
    · rw [stateAt_keep h fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm),
        hst, Md.compressList_zero]
  -- The loop.
  have hlbT : ∀ σ, (ℓ σ + h.L) / h.B < nbm := hℓ
  refine (VP.loop (I := fun n σ s => n ≤ nbm ∧ CS (nbm - n) σ s) (fun n => ?_) (nbm - 1)).mono
    (fun σ s hs => ⟨by omega_arith, by rw [show nbm - (nbm - 1 + 1) = 0 by omega_arith]; exact hs⟩) fun _ _ h => h
  have keepI : ∀ σ m m' (rs : List Region), Inv σ m → (∀ r ∈ rs, r ∈ loopW h L scr) → Frame rs m m' → Inv σ m' :=
    fun σ m m' rs hi hs fr => hI σ m m' hi (fr.mono hs)
  -- Block `b`.
  by_cases hn : n + 1 ≤ nbm
  swap
  · exact VP.empty fun σ s ⟨h, _⟩ => hn h
  generalize hb : nbm - (n + 1) = b
  have hbn : b < nbm := by omega_arith
  have hbB : b * h.B + h.B ≤ T := by rw [← hT, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega_arith)
  have hbB32 : b * h.B < 2 ^ 32 := by omega_arith
  -- What each stage keeps of memory.
  let X2 : State → Mem → Prop := fun σ m => Inv σ m ∧ (∀ i < T, m (sa scr (oY + i)) = yv σ i) ∧
    m.readW (L.fr sBi) 32 = BitVec.ofNat 32 b ∧ h.md.stateAt m (sa scr oSt) = h.md.compressList h.ok.iv (ylist (yv σ) T) (b + 1) ∧
    (((ℓ σ + h.L) / h.B) < b → h.md.stateAt m (sa scr oSel) = h.md.compressList h.ok.iv (ylist (yv σ) T) (((ℓ σ + h.L) / h.B) + 1))
  let X4 : State → Mem → Prop := fun σ m => Inv σ m ∧ (∀ i < T, m (sa scr (oY + i)) = yv σ i) ∧
    m.readW (L.fr sBi) 32 = BitVec.ofNat 32 b ∧ h.md.stateAt m (sa scr oSt) = h.md.compressList h.ok.iv (ylist (yv σ) T) (b + 1) ∧
    (((ℓ σ + h.L) / h.B) < b + 1 → h.md.stateAt m (sa scr oSel) = h.md.compressList h.ok.iv (ylist (yv σ) T) (((ℓ σ + h.L) / h.B) + 1))
  have hsub : ∀ rs : List Region, (∀ r ∈ rs, r ∈ loopW h L scr) → ∀ r ∈ rs, Region.Disjoint (sR scr oY T) r :=
    fun rs hs r hr => dY r (hs r hr)
  show VP _ (.seq (.block (compSet h.H)) (.seq h.H.md.compressBlock (.seq (.block (selSet h.H))
    (.seq (countLoop selBody) (.block compNext))))) _
  refine VP.seq (G := fun σ s => CS b σ s ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧ s.gpr .r3 = scr ∧
      s.gpr .r6 = scr + BitVec.ofNat 32 (oY + b * h.B)) ?_
    (VP.seq (G := fun σ s => Ctx L scr σ s ∧ X2 σ s.mem) ?_
    (VP.seq (G := fun σ s => (Ctx L scr σ s ∧ X2 σ s.mem) ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧
        s.gpr .r1 = scr + BitVec.ofNat 32 oSel ∧ s.gpr .lr = BitVec.ofNat 32 h.N ∧
        s.gpr .r2 = maskOf (b * h.B = ((ℓ σ + h.L) / h.B) * h.B)) ?_
    (VP.seq (G := fun σ s => Ctx L scr σ s ∧ X4 σ s.mem) ?_ ?_)))
  · -- The compression's registers.
    refine VP.blk (blkOk rfl) (sp_eq fun _ _ h => h.2.1) fun σ s ⟨_, hc, hi, hm⟩ => ?_
    have hw : WP isa (.block (compSet h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧ t.gpr .r3 = scr ∧
        t.gpr .r6 = scr + BitVec.ofNat 32 (oY + b * h.B) := by
      prun [compSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hm.bi,
        movw_val (show oSt < 2 ^ 16 by decide), movw_val (show oY < 2 ^ 16 by decide),
        show (BitVec.ofNat 16 oCW).setWidth 32 = 0 from rfl, ofNat_shl h hbB32, h.lg_range, dpVal,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat, show scr + 0 = scr from BitVec.add_zero scr]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r3, r6⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hi, m ▸ hm⟩, r0, r3, r6⟩
  · -- The compression.
    refine (comp_vp h hg (o := oY + b * h.B) (by pomega) (by pomega) (X := fun σ m => Inv σ m ∧
        CM h L scr T (yv σ) (((ℓ σ + h.L) / h.B)) b m)).mono (fun σ s ⟨⟨hc, hi, hm⟩, r0, r3, r6⟩ => ⟨hc, ⟨hi, hm⟩, r0, r3, r6⟩)
      fun σ s ⟨hc, m₀, ⟨hi, hm⟩, fr, e⟩ => ⟨hc, keepI σ _ _ _ hi (by simp) fr, ?_, ?_, ?_, ?_⟩
    · exact sbytes_keep fr (hsub _ (by simp)) (by pomega) hm.y
    · exact slot_keep fr (fun r hr => dB r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h' | h' <;> simp [h'])) hm.bi
    · rw [e, hm.st, Md.compressList_succ]
      refine congrArg _ (h.md.parse_congr fun k hk => ?_)
      rw [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← sa, show oY + b * h.B + k = oY + (b * h.B + k) by omega_arith,
        hm.y _ (by pomega), ylist_getD (by have := Nat.mul_comm b h.B; pomega), Nat.mul_comm]
    · intro hl
      have dsel : ∀ r ∈ compW h scr, Region.Disjoint (sR scr oSel h.N) r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Geo.sep (by pomega) (by pomega) (by pomega)
        · exact Geo.sep (by pomega) (by pomega) (by pomega)
      rw [stateAt_keep h fr dsel, hm.sel hl]
  · -- The selection's registers.
    refine VP.blk (blkOk rfl) (sp_eq fun _ _ h => h.1) fun σ s ⟨hc, hx⟩ => ?_
    have l2 : ℓ σ + h.L < 2 ^ 32 := by have := hℓ2 σ; omega_arith
    have e1 : BitVec.ofNat 32 (ℓ σ) + BitVec.ofNat 32 h.L = BitVec.ofNat 32 (ℓ σ + h.L) := BitVec.ofNat_add_ofNat ..
    have e2 : BitVec.ofNat 32 (ℓ σ + h.L) >>> lgB h.H = BitVec.ofNat 32 (((ℓ σ + h.L) / h.B)) := by
      rw [VG.Proof.MdStream.Arm.ofNat_shr l2, h.pow_lg]
    have e3 : BitVec.ofNat 32 (((ℓ σ + h.L) / h.B)) <<< lgB h.H = BitVec.ofNat 32 (((ℓ σ + h.L) / h.B) * h.B) :=
      ofNat_shl h (by have := Nat.div_mul_le_self (ℓ σ + h.L) h.B; omega_arith)
    have e4 := eqBit (a := b * h.B) (b := ((ℓ σ + h.L) / h.B) * h.B) (by omega_arith)
      (by have := Nat.div_mul_le_self (ℓ σ + h.L) h.B; have := hℓ2 σ; omega_arith)
    have hw : WP isa (.block (selSet h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧ t.gpr .r1 = scr + BitVec.ofNat 32 oSel ∧
        t.gpr .lr = BitVec.ofNat 32 h.N ∧ t.gpr .r2 = maskOf (b * h.B = ((ℓ σ + h.L) / h.B) * h.B) := by
      prun [selSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hx.2.2.1, hsl σ _ hx.1,
        movw_val (show oSt < 2 ^ 16 by decide), movw_val (show oSel < 2 ^ 16 by decide),
        movw_val (show h.L < 2 ^ 16 by omega_arith), movw_val (show h.N < 2 ^ 16 by omega_arith),
        movw_val (show 0 < 2 ^ 16 by decide), ofNat_shl h hbB32, e1, e2, e3, e4, neg_bit, neg_bit', h.lg_range, dpVal]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r2⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hx⟩, r0, r1, lr, r2⟩
  · -- The selection.
    refine (sel_vp h hg (c := fun σ => b * h.B = ((ℓ σ + h.L) / h.B) * h.B) (X := X2)).mono
      (fun σ s ⟨⟨hc, hx⟩, r0, r1, lr, r2⟩ => ⟨hc, hx, r0, r1, lr, r2⟩)
      fun σ s ⟨hc, m₀, ⟨hi, hy, hbi, hst, hsel⟩, fr, hb'⟩ => ⟨hc, keepI σ _ _ _ hi (by simp) fr, ?_, ?_, ?_, ?_⟩
    · exact sbytes_keep fr (hsub _ (by simp)) (by pomega) hy
    · exact slot_keep fr (fun r hr => dB r (by simp only [List.mem_singleton] at hr; simp [hr])) hbi
    · rw [stateAt_keep h fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)), hst]
    · intro hl
      by_cases e : b * h.B = ((ℓ σ + h.L) / h.B) * h.B
      · have eb : b = ((ℓ σ + h.L) / h.B) := Nat.eq_of_mul_eq_mul_right (by omega_arith) e
        rw [← eb, ← hst]
        refine h.ok.reloc _ _ _ _ fun i hi' => ?_
        rw [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← sa, hb' i hi', ite_eq_left e]
        simp only [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      · have hl' : ((ℓ σ + h.L) / h.B) < b := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hl with h' | h'
          · exact h'
          · exact absurd (by rw [h']) e
        rw [← hsel hl']
        refine h.md.stateAt_congr fun i hi' => ?_
        rw [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← sa, hb' i hi', ite_eq_right e]
  · -- The next block.
    refine VP.blk (blkOk rfl) (sp_eq fun _ _ h => h.1) fun σ s ⟨hc, hi, hy, hbi, hst, hsel⟩ => ?_
    have hw : WP isa (.block compNext) s fun t => t.mem = s.mem.writeW (L.fr sBi) (BitVec.ofNat 32 (b + 1)) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.z = decide (b + 1 = nbm) := by
      prun [compNext, sp0, ld, st, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, hbi, hsn σ _ hi, dpVal,
        VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, VG.Proof.MdStream.Arm.sub_beq (show b + 1 < 2 ^ 32 by omega_arith)
          (show nbm < 2 ^ 32 by omega_arith)]
      rw [Mem.readW_writeW_sep (Offset.sep _ (by left; decide) (by decide) (by decide)) (by decide), hsn σ _ hi]
      exact VG.Proof.MdStream.Arm.sub_beq (by omega_arith) (by omega_arith)
    refine WP.mono hw fun t ⟨m, rd, wr, sp, z⟩ => ?_
    have fr : Frame [slotR L sBi] s.mem t.mem := by rw [m]; exact slot_frame L _ _ _
    have hc' : Ctx L scr σ t := hc.write fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.FR, List.mem_cons_self, Offset.sub_base _ (by rw [hg.F]; decide)⟩)
      (fun r hr => (dBN r hr).2.2) rd wr sp
    have hi' : Inv σ t.mem := keepI σ _ _ _ hi (by simp) fr
    have hsel' : ((ℓ σ + h.L) / h.B) < b + 1 → h.md.stateAt t.mem (sa scr oSel) = h.md.compressList h.ok.iv (ylist (yv σ) T) (((ℓ σ + h.L) / h.B) + 1) := fun hl => by
      rw [stateAt_keep h fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm),
        hsel hl]
    have dz : decide (b + 1 = nbm) = decide (n = 0) := by simp only [decide_eq_decide]; omega_arith
    refine ⟨by rw [VG.Proof.X25519.Arm.eval_ne, z, dz]; cases n <;> simp,
      fun h0 => ⟨hc', hi', hsel' (by have := hlbT σ; omega_arith)⟩, fun hp => ⟨by omega_arith, ?_⟩⟩
    rw [show nbm - n = b + 1 by omega_arith]
    refine ⟨hc', hi', sbytes_keep fr (hsub _ (by simp)) (by pomega) hy, by rw [m, Mem.readW_writeW_self32], ?_, hsel'⟩
    rw [stateAt_keep h fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm), hst]

end VG.Proof.RsaPss.Arm
