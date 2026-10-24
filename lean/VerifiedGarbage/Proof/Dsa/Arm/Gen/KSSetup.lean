module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.KSOps
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Dsa.Arm.Gen.CT
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP

/-! # DSA parameter generation on ARMv7: the key working space set up

`ksSetup` (`ksSetup_vp`): the count `w` into the division's header (word
16), every array zeroed, and `[aOne] := 1`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.Bignum.Arm (zero_ok ZeroInv)
open VG.Impl.Rsa.Arm.Keys (hdr setOne)
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp wp_mul op2_imm op2_reg op2_lsr dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- The arrays after the setup: all zero but `[aOne] = 1`. -/
abbrev A0 : Nat → Nat := KU (fun _ => 0) aOne 1

/-- Every array. -/
abbrev allArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

theorem allArrs_lt : ∀ j ∈ allArrs, j < nArrs := by decide

section
variable {G : GP} {c : Cfg} {X : State → Prop}

theorem ksSetup_vp :
    VP (St G c X) ksSetup (St G { c with A := A0, live := allArrs, KV := KU c.KV 16 G.w, kls := [16] } X) := by
  refine ks_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9]) ksSetup, rfl⟩
    (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have l := h.lens
  have nw := hw.nowrap
  have wl : G.w ≤ 96 := by simp only [GP.w]; omega
  have w1 : 1 ≤ G.w := by simp only [GP.w]; omega
  have fits : hdr + 4 * (nArrs * (G.w + 2)) ≤ kz G.pLen := by
    simp only [hdr, nArrs, kz, GP.w]; omega
  refine h.ksWP rfl (P := fun t => Arrs t.mem G.KB G.w A0 allArrs ∧ slot t.mem G.KB 16 = G.w ∧
      Rest VG.Proof.Rsa.Arm.Keys.opRegs (G.ksState s) t) ?_
    fun t ⟨a, sl, R⟩ hr hw' f => ⟨?_, x⟩
  swap
  · have R' : Rest VG.Proof.Rsa.Arm.Keys.opRegs s t := ⟨R.gpr, hr, hw', R.sp⟩
    have hk : ∀ d ∈ [16], slot t.mem G.KB d = KU c.KV 16 G.w d := fun d hd => by
      rw [List.mem_singleton] at hd; subst hd
      rw [KU, VG.Proof.Rsa.Arm.Keys.upd_self]; exact sl
    have hko : ∀ d ∈ [16], KlsOk d := fun d hd => by
      rw [List.mem_singleton] at hd; subst hd; decide
    exact h.of_ks R' f a allArrs_lt hk hko
  -- The count, the pointer and the number of words.
  unfold ksSetup
  refine WP.seq (wp_strSlot hw (d := 16) (by decide) fun s₁ u₁ => ?_)
  have hw₁ := hw.of_mupd u₁
  have o₁ := writeW32_outside (G.ksState s).mem (State.addr G.KB) (d := 16) ((G.ksState s).gpr .r9) (by decide)
  rw [← u₁.mem] at o₁
  refine wp_dp (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_mul fun s₄ u₄ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₅ u₅ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have R₆ : Rest [.r0, .lr, .r3] s₁ s₆ := (u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans
    ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))))
  have m₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have hw₆ := hw₁.rest R₆
  have p0 : s₆.gpr .r0 = G.KB + BitVec.ofNat 32 hdr := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      dpVal, hw₁.r8]
  have plr : s₆.gpr .lr = BitVec.ofNat 32 (nArrs * (G.w + 2)) := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide), hw₁.r7]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [nArrs, S]
    rw [Nat.mod_eq_of_lt (a := 15) (by decide), Nat.mod_eq_of_lt (a := 4 * (G.w + 2)) (by omega),
      Nat.mod_eq_of_lt (a := 15 * (4 * (G.w + 2))) (by omega), Nat.mod_eq_of_lt (a := 15 * (G.w + 2)) (by omega)]
    omega
  have p3 : s₆.gpr .r3 = 0 := u₆.gpr
  -- Zero, then 1.
  refine WP.seq (WP.mono (zero_ok s₆ (base := G.KB) (size := kz G.pLen) (o := hdr) (n := nArrs * (G.w + 2))
    ⟨nw, fits, ⟨G.rK, by rw [R₆.wr, u₁.wr]; exact List.mem_singleton_self _, Region.contains_self _ _⟩⟩
    (by simp only [nArrs]; omega) p0 plr p3) fun s₇ z => ?_)
  have hw₇ := hw₆.rest z.rest
  rw [← List.append_nil (setOne aOne)]
  refine setOne_ok hw₇ (j := aOne) (by decide) (by decide) fun t w₈ k₈ v₈ R₈ => WP.block_nil ?_
  have zv : ∀ j < nArrs, num s₇.mem G.KB G.w j = 0 := fun j hj => by
    have := VG.Proof.Rsa.KeyWorkspace.val32_zero_part z.value (a := j * (G.w + 2)) (c := G.w) (by
      have := Nat.mul_le_mul_right (G.w + 2) (show j + 1 ≤ nArrs by omega)
      rw [Nat.succ_mul] at this; omega)
    simpa only [arr, S, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · show num t.mem G.KB G.w j = KU (fun _ => 0) aOne 1 j
    simp only [KU]
    by_cases e : j = aOne
    · subst e; rw [VG.Proof.Rsa.Arm.Keys.upd_self, v₈, zv _ (by decide)]
    · rw [VG.Proof.Rsa.Arm.Keys.upd_ne _ _ e, k₈.num (by simpa using Ne.symm e) (by simp)
        (hw₇.fit64 (allArrs_lt j hj)), zv _ (allArrs_lt j hj)]
  · rw [k₈.slot (by decide) (by simp)]
    show w32 s₇.mem _ 16 = G.w
    rw [z.outside.w32 (d := 16) (by simp only [hdr]; omega) (by decide), m₆]
    show (s₁.mem.readW (off (State.addr G.KB) 16) 32).toNat = G.w
    rw [u₁.mem, Mem.readW_writeW_self32, show (G.ksState s).gpr .r9 = s.gpr .r9 from rfl, h.r9,
      BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  · exact (u₁.rest ..).trans (R₆.mono (by simp) |>.trans ((z.rest.mono (by simp)).trans (R₈.mono (by simp))))

end

end VG.Proof.Dsa.Arm.Gen
