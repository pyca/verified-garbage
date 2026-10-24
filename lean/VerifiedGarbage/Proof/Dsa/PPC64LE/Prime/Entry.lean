module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Pre
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# DSA's probable-prime test on PPC64LE: the entry

`entry_ok`: the return address and our caller's registers saved in `ws`
from `saveOff` (`Spill.save_ok`); the header's values computed into
registers (`values_ok`) and stored (`Spill.save_ok` again): `EntryPost`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.Bignum (word off Outside)

/-- The registers `values` writes. -/
def valRegs : List Reg :=
  [.r10, .r11, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29,
    .r30, .r31]

theorem arrReg_ne {j : Nat} (hj : j < 8) :
    arrReg j ≠ .r0 ∧ arrReg j ≠ .r3 ∧ arrReg j ≠ .r5 ∧ arrReg j ≠ .r6 ∧ arrReg j ≠ .r7 ∧ arrReg j ≠ .r10 ∧
      arrReg j ≠ .r11 ∧ arrReg j ≠ .r14 ∧ arrReg j ≠ .r15 ∧ arrReg j ≠ .r16 ∧ arrReg j ≠ .r17 ∧
      arrReg j ≠ .r18 ∧ arrReg j ≠ .r19 ∧ arrReg j ≠ .r20 ∧ arrReg j ≠ .r21 ∧ arrReg j ≠ .r29 ∧ arrReg j ≠ .r31 := by
  revert j; decide

/-- The header's values in the registers, for the working space at `ws`. -/
structure HRegs (bits : Nat) (ws : Addr) (g : Reg → BitVec 64) : Prop where
  r31 : g .r31 = ws + BitVec.ofNat 64 keyOff
  r14 : g .r14 = BitVec.ofNat 64 (keyWords bits)
  r15 : g .r15 = BitVec.ofNat 64 0
  r16 : g .r16 = BitVec.ofNat 64 (words bits)
  r29 : g .r29 = BitVec.ofNat 64 (8 * (words bits + 2))
  arr : ∀ j < 8, g (arrReg j) = ws + BitVec.ofNat 64 (keyOff + (hdrBytes + j * (8 * (words bits + 2))))
  r17 : g .r17 = BitVec.ofNat 64 (draw bits)
  r18 : g .r18 = BitVec.ofNat 64 (2 ^ topBits bits - 1)
  r19 : g .r19 = BitVec.ofNat 64 (topOff bits)
  r20 : g .r20 = BitVec.ofNat 64 (checks bits)
  r21 : g .r21 = BitVec.ofNat 64 (count bits)
  r10 : g .r10 = ws + BitVec.ofNat 64 (keyOff + hdrBytes)
  r11 : g .r11 = BitVec.ofNat 64 (2 * words bits)

/-- What `values` leaves. -/
structure Vals (bits : Nat) (s v : State) : Prop where
  regs : HRegs bits (s.gpr .r3) v.gpr
  mem : v.mem = s.mem
  keep : Keep valRegs s v

theorem mask_val {b : Nat} (hb1 : 1 ≤ b) (hb : b ≤ 64) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 1) >>> (64 - b) = BitVec.ofNat 64 (2 ^ b - 1) := by
  apply BitVec.eq_of_toNat_eq
  have h2 : 2 ^ b ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hb
  have h3 : (2 : Nat) ^ 64 = 2 ^ b * 2 ^ (64 - b) := by rw [← Nat.pow_add]; congr 1; omega
  have e1 : (BitVec.ofNat 64 0 - BitVec.ofNat 64 1).toNat = 2 ^ 64 - 1 := by decide
  rw [BitVec.toNat_ushiftRight, e1, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
  have hX1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hP1 : 1 ≤ 2 ^ (64 - b) := Nat.one_le_two_pow
  rw [h3]
  generalize 2 ^ b = X at *
  generalize 2 ^ (64 - b) = P at *
  have hXP : P ≤ X * P := Nat.le_mul_of_pos_left _ (by omega)
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_mul, Nat.one_mul]; omega
  · rw [Nat.sub_add_cancel hX1]; omega

/-- The header's values into registers. -/
theorem values_ok {bits : Nat} (hs : Shape bits) (s : State) :
    WP isa (.block (values bits)) s (Vals bits s) := by
  have hkw := hs.kw
  have hw48 := hs.w48
  have hst := hs.stride
  have ha7 := hs.arr7
  have e : values bits = [.addi .r31 .r3 keyOff, .li .r14 (keyWords bits), .li .r15 0, .li .r16 (words bits),
      .li .r29 (8 * (words bits + 2)),
      .addi .r22 .r31 (hdrBytes + 0 * (8 * (words bits + 2))), .addi .r23 .r31 (hdrBytes + 1 * (8 * (words bits + 2))),
      .addi .r24 .r31 (hdrBytes + 2 * (8 * (words bits + 2))), .addi .r25 .r31 (hdrBytes + 3 * (8 * (words bits + 2))),
      .addi .r26 .r31 (hdrBytes + 4 * (8 * (words bits + 2))), .addi .r27 .r31 (hdrBytes + 5 * (8 * (words bits + 2))),
      .addi .r28 .r31 (hdrBytes + 6 * (8 * (words bits + 2))), .addi .r30 .r31 (hdrBytes + 7 * (8 * (words bits + 2))),
      .li .r17 (draw bits), .li .r18 0, .subi .r18 .r18 1, .lsr .d .r18 .r18 (64 - topBits bits),
      .li .r19 (topOff bits), .li .r20 (checks bits), .li .r21 (count bits), .addi .r10 .r31 hdrBytes,
      .li .r11 (2 * words bits)] := rfl
  rw [e]
  refine WP.mono (Q := fun (v : State) => (v.gpr .r31 = s.gpr .r3 + BitVec.ofNat 64 keyOff ∧ v.gpr .r14 = BitVec.ofNat 64 (keyWords bits) ∧
      v.gpr .r15 = BitVec.ofNat 64 0 ∧ v.gpr .r16 = BitVec.ofNat 64 (words bits) ∧
      v.gpr .r29 = BitVec.ofNat 64 (8 * (words bits + 2)) ∧
      v.gpr .r22 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + (hdrBytes + 0 * (8 * (words bits + 2)))) ∧
      v.gpr .r23 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + (hdrBytes + 1 * (8 * (words bits + 2)))) ∧
      v.gpr .r24 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + (hdrBytes + 2 * (8 * (words bits + 2)))) ∧
      v.gpr .r25 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + (hdrBytes + 3 * (8 * (words bits + 2)))) ∧
      v.gpr .r26 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + (hdrBytes + 4 * (8 * (words bits + 2)))) ∧
      v.gpr .r27 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + (hdrBytes + 5 * (8 * (words bits + 2)))) ∧
      v.gpr .r28 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + (hdrBytes + 6 * (8 * (words bits + 2)))) ∧
      v.gpr .r30 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + (hdrBytes + 7 * (8 * (words bits + 2)))) ∧
      v.gpr .r17 = BitVec.ofNat 64 (draw bits) ∧ v.gpr .r18 = BitVec.ofNat 64 (2 ^ topBits bits - 1) ∧
      v.gpr .r19 = BitVec.ofNat 64 (topOff bits) ∧ v.gpr .r20 = BitVec.ofNat 64 (checks bits) ∧
      v.gpr .r21 = BitVec.ofNat 64 (count bits) ∧
      v.gpr .r10 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + hdrBytes) ∧
      v.gpr .r11 = BitVec.ofNat 64 (2 * words bits) ∧ v.mem = s.mem) ∧ Keep valRegs s v) (WP.keep _ ?_ rfl)
    fun v ⟨⟨a31, a14, a15, a16, a29, a22, a23, a24, a25, a26, a27, a28, a30, a17, a18, a19, a20, a21, a10, a11, am⟩, kv⟩ =>
      ⟨⟨a31, a14, a15, a16, a29, fun j hj => by
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [a22, a23, a24, a25, a26, a27, a28, a30], a17, a18, a19, a20, a21, a10, a11⟩, am, kv⟩
  have hdraw : draw bits < 2 ^ 15 := by rw [hs.hdraw]; have := hs.tw; omega
  have htopo : topOff bits < 2 ^ 15 := by rw [hs.hoff]; have := hs.tw; omega
  have hchk : checks bits < 2 ^ 15 := by unfold checks; split <;> decide
  have hcnt : count bits < 2 ^ 15 := by unfold count; split <;> decide
  have hj : ∀ j ≤ 7, hdrBytes + j * (8 * (words bits + 2)) < 2 ^ 15 := fun j hj => by
    have := Nat.mul_le_mul_right (8 * (words bits + 2)) hj; simp only [hdrBytes]; omega
  prun [hkw, hdraw, htopo, hchk, hcnt, mask_val hs.b1 hs.b64, hs.maskb, show words bits < 2 ^ 15 by omega,
    show 2 * words bits < 2 ^ 15 by omega, show keyOff < 2 ^ 15 by decide, hst, hj 0 (by decide), hj 1 (by decide),
    hj 2 (by decide), hj 3 (by decide), hj 4 (by decide), hj 5 (by decide), hj 6 (by decide), hj 7 (by decide),
    show hdrBytes < 2 ^ 15 by decide]

/-- After the entry. -/
structure EntryPost (bits : Nat) (σ s : State) : Prop where
  regs : HRegs bits (σ.gpr .r3) s.gpr
  other : ∀ r, r ∉ valRegs → r ≠ .r0 → s.gpr r = σ.gpr r
  svd : Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots s.mem
  hdr : Spill.Saved (s.gpr .r31) s.gpr hdrSlots s.mem
  frame : Frame [⟨σ.gpr .r3 + BitVec.ofNat 64 saveOff, 168⟩, ⟨σ.gpr .r3 + BitVec.ofNat 64 keyOff, 256⟩] σ.mem s.mem
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  lr : s.lr = σ.lr

theorem savedSlots_fits : Spill.Fits savedSlots := by decide
theorem hdrSlots_fits : Spill.Fits hdrSlots := by decide
theorem savedSlots_in : ∀ p ∈ savedSlots, saveOff ≤ p.2 ∧ p.2 + 8 ≤ saveOff + 168 := by decide
theorem hdrSlots_in : ∀ p ∈ hdrSlots, 0 ≤ p.2 ∧ p.2 + 8 ≤ 0 + 256 := by decide

/-- The entry: the registers saved, the header. -/
theorem entry_ok {bits : Nat} (hs : Shape bits) {σ : State} (h : CIn bits σ) :
    WP isa (.block (save ++ setup bits)) σ (EntryPost bits σ) := by
  have hsz := h.size
  have hfw := h.fw
  have hkey := hs.key
  have hw48 := hs.w48
  have hwsW : (⟨σ.gpr .r3, (σ.gpr .r4).toNat * 8⟩ : Region) ∈ σ.wr := by rw [h.wr]; exact List.mem_cons_self
  have inWs : ∀ d, d + 8 ≤ (σ.gpr .r4).toNat * 8 → InRegions σ.wr (σ.gpr .r3 + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨_, hwsW, by
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]; omega⟩
  simp only [save, setup, List.cons_append]
  refine WP.cons (exec_mflr) ?_
  have r3w : (σ.write .r0 σ.lr).gpr .r3 = σ.gpr .r3 := rfl
  refine Spill.save_ok (b := .r3) (l := savedSlots) (by decide) savedSlots_fits.1 (fun p hp => by
    rw [r3w]; exact inWs _ (by have := savedSlots_in p hp; simp only [saveOff, keyOff] at *; omega)) ?_
  generalize hM : Spill.saveMem (σ.write .r0 σ.lr).mem ((σ.write .r0 σ.lr).gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots = M
  rw [WP.block_append_iff]
  refine WP.mono (values_ok hs _) fun v hv => ?_
  have v31 : v.gpr .r31 = σ.gpr .r3 + BitVec.ofNat 64 keyOff := hv.regs.r31
  refine Spill.save_ok (b := .r31) (l := hdrSlots) (by decide) hdrSlots_fits.1 (fun p hp => by
    rw [hv.keep.wr, v31, Offset.add_add]
    exact inWs _ (by have := hdrSlots_in p hp; simp only [keyOff] at *; omega)) ?_
  refine WP.block_nil ⟨hv.regs, fun r hr h0 => by rw [hv.keep.gpr r hr]; simp [State.write, h0], ?_, ?_, ?_,
    hv.keep.sp, hv.keep.rd, hv.keep.wr, hv.keep.lr⟩
  · have hvm : v.mem = M := hv.mem
    have sM : Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots v.mem := by
      rw [hvm, ← hM]; exact Spill.saveMem_saved savedSlots_fits _ _ _
    refine sM.frame (Spill.saveMem_frame (lo := 0) (n := 256) hdrSlots_in (by decide) _ _ _) fun p hp r hr => ?_
    rw [List.mem_singleton] at hr
    subst hr
    rw [v31, Offset.add_add]
    have := savedSlots_in p hp
    exact Offset.disjoint _ (by simp only [saveOff, keyOff] at *; omega) (by simp only [saveOff] at *; omega)
      (by simp only [keyOff]; omega)
  · exact Spill.saveMem_saved hdrSlots_fits _ _ _
  · have f1 : Frame [⟨σ.gpr .r3 + BitVec.ofNat 64 saveOff, 168⟩] σ.mem M := by
      rw [← hM]; exact Spill.saveMem_frame savedSlots_in (by decide) _ _ _
    have hvm : v.mem = M := hv.mem
    rw [← hvm] at f1
    have f2 := Spill.saveMem_frame (lo := 0) (n := 256) hdrSlots_in (by decide) v.mem (v.gpr .r31) v.gpr
    have eb : v.gpr .r31 + BitVec.ofNat 64 0 = σ.gpr .r3 + BitVec.ofNat 64 keyOff := by rw [BitVec.add_zero, v31]
    refine (f1.mono (by simp)).trans (f2.mono fun r hr => ?_)
    rw [List.mem_singleton] at hr
    rw [hr, eb]
    simp

end VG.Proof.Dsa.PPC64LE.Prime
