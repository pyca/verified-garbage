module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Pieces
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The Miller–Rabin round on ARMv7: more of its steps as pieces

The top bit of `c`'s copy shifted out (`St.pbitOut`), the flag and the count
(`St.pflag`), and the flag and the count set (`St.pinit`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Spec.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- The flag's arithmetic on bits. -/
theorem flag_bv {b e1 e2 f : Nat} (hb : b ≤ 1) (h1 : e1 ≤ 1) (h2 : e2 ≤ 1) (hf : f ≤ 1) :
    (((BitVec.ofNat 32 e1 &&& BitVec.ofNat 32 b) ||| BitVec.ofNat 32 e2) |||
      (BitVec.ofNat 32 f &&& (BitVec.ofNat 32 b ^^^ 1))).toNat =
      (if b = 1 then (decide (e1 = 1) || decide (e2 = 1)) else (decide (f = 1) || decide (e2 = 1))).toNat := by
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> rcases (by omega : e1 = 0 ∨ e1 = 1) with rfl | rfl <;>
    rcases (by omega : e2 = 0 ∨ e2 = 1) with rfl | rfl <;> rcases (by omega : f = 0 ∨ f = 1) with rfl | rfl <;>
    decide

section
variable {P : MP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- After the pointer of `c`'s copy, the count and the carry in. -/
abbrev BitH (P : MP) (E : State → Prop) (A : State → Nat → Nat) (L : List Nat) (V : State → Nat → Nat)
    (LS : List Nat) (σ s : State) : Prop :=
  St P E A L V LS σ s ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W aE) ∧ s.gpr .lr = BitVec.ofNat 32 (2 * P.w) ∧
    s.gpr .r11 = 0

/-- The top bit of `[aE]` shifted out into `sBit`. -/
theorem St.pbitOut (hE : aE ∈ L) (hEv : ∀ σ, E σ → A σ aE < P.R) :
    VP (St P E A L V LS) (seqs bitOut)
      (St P E (fun σ => upd (A σ) aE (2 * A σ aE % P.R)) L (fun σ => upd (V σ) sBit (2 * A σ aE / P.R))
        (sBit :: LS)) := by
  simp only [bitOut, seqs]
  let G2 := fun σ s => St P E (fun σ => upd (A σ) aE (2 * A σ aE % P.R)) L V LS σ s ∧
    (s.gpr .r11).toNat = 2 * A σ aE / P.R
  refine VP.seq (G := BitH P E A L V LS) ?_ (VP.seq (G := G2) ?_ ?_)
  -- The pointer, the count and the carry.
  · refine VP.kv bitHead_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
    have w128 := h.pre.w128
    refine ptr_ok hw (r := .r0) (by decide) (j := aE) (by decide) fun s1 p1 r1 m1 hw1 => ?_
    refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
    refine wp_mov (op2_imm (by decide)) fun t u3 => WP.block_nil ?_
    have rt : Rest [.r0, .lr, .r11] s t := (r1.mono (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp)))
    have mt : t.mem = s.mem := u3.mem.trans (u2.mem.trans m1)
    refine ⟨⟨e, h.of_rest rt mt,
      (hw1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide) (by decide) (by decide)⟩, ?_, ?_, ?_⟩
    · rw [u3.other _ (by decide), u2.other _ (by decide), p1]
    · rw [u3.other _ (by decide), u2.gpr, dpVal, hw1.r9, show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by simp only [MP.W]; omega)]
      show BitVec.ofNat 32 (2 * P.w + 2 - 2) = _
      rw [Nat.add_sub_cancel]
    · rw [u3.gpr]
  -- The shift.
  · refine VP.of_ct (fun σ₁ σ₂ => ?_) fun σ s ⟨⟨e, h, hw⟩, r0, lr, r11⟩ => ?_
    · intro s₁ s₂ t₁ t₂ u₁ u₂ hp e₁ e₂
      exact ⟨shiftLeft_ct s₁ s₂ t₁ t₂ u₁ u₂ trivial trivial
        ⟨hp.1.2.1.trans hp.2.2.1.symm, hp.1.2.2.1.trans hp.2.2.2.1.symm⟩ e₁ e₂, trivial⟩
    · have pre := h.pre
      have hS := pre.S_eq
      have hW : P.W = 2 * P.w + 2 := rfl
      have fitE := hw.arr_fit (j := aE) (by decide)
      rw [hS] at fitE
      have ev := hEv σ e
      have hR : 2 ^ (32 * (2 * P.w)) = P.R := by simp only [MP.R]; rw [← Nat.mul_assoc]
      have nE := h.arrs aE hE
      have split : ∀ m : Mem, num m P.B P.W aE = val32 m (State.addr P.B) (arr P.W aE) (2 * P.w) +
          P.R * val32 m (State.addr P.B) (arr P.W aE + 4 * (2 * P.w)) 2 := fun m => by
        simp only [num, MP.W]; rw [val32_append, hR]
      have lowS : val32 s.mem (State.addr P.B) (arr P.W aE) (2 * P.w) = A σ aE := by
        rw [val32_low _ _ _ (2 * P.w) 2, show 2 * P.w + 2 = P.W from rfl, hR]
        simp only [num] at nE; rw [nE]; exact Nat.mod_eq_of_lt ev
      have padS : val32 s.mem (State.addr P.B) (arr P.W aE + 4 * (2 * P.w)) 2 = 0 := by
        have := split s.mem; rw [nE, lowS] at this
        rcases Nat.eq_zero_or_pos (val32 s.mem (State.addr P.B) (arr P.W aE + 4 * (2 * P.w)) 2) with z | z
        · exact z
        · have := Nat.le_mul_of_pos_right P.R z; omega
      have ctx : ShiftLeftCtx s P.B P.Z (arr P.W aE) (2 * P.w) :=
        ⟨hw.nowrap, by omega, hw.writable⟩
      refine WP.mono (shiftLeft_ok s ctx (by have := pre.w4; omega) r0 lr (by rw [r11]; decide))
        fun t inv => ?_
      obtain ⟨vt, ct⟩ := inv.result
      have z0 : (0 : BitVec 32).toNat = 0 := rfl
      rw [r11, lowS, z0, Nat.add_zero, hR] at vt ct
      have k : Keep P.B P.W [aE] [] s.mem t.mem := Keep.of_arr (d := 0) (by simpa using inv.outside)
        (by rw [hS]; omega) (by simp)
      have padT : val32 t.mem (State.addr P.B) (arr P.W aE + 4 * (2 * P.w)) 2 = 0 := by
        rw [inv.outside.val32 (by omega) (by have := pre.Z_le; omega), padS]
      have hl := h.write1 k (by decide) (by simp) inv.rest.sp inv.rest.rd inv.rest.wr
        (x := 2 * A σ aE % P.R) (by rw [split, vt, padT, Nat.mul_zero, Nat.add_zero]) (by simp)
      refine ⟨⟨e, hl.mono (fun j hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩),
        hw.rest inv.rest⟩, ct⟩
  -- The bit stored.
  · refine VP.kv bitStore_taint (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, r11⟩ => ?_
    refine h.str hw (d := sBit) (by decide) (r := .r11) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
    rwa [r11] at ht

/-- `str t, [r8, #d]`, keeping the flags. -/
theorem KS.strz {σ s : State} {A : Nat → Nat} {V : Nat → Nat} {d : Nat} (h : KS P σ A L V LS s)
    (hw : Ws s P.B P.Z P.W nArr) (hd : d ∈ wDs) {r : Reg} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A L (upd V d (s.gpr r).toNat) (d :: LS) t → Ws t P.B P.Z P.W nArr → t.z = s.z →
      t.gpr = s.gpr → WP isa (.block rest) t Q) :
    WP isa (.block (.str r .r8 d :: rest)) s Q := by
  have hd' := wDs_hdr d hd
  have hz := hw.hdr_le
  refine wp_str_z (by simp only [hdr] at hd'; omega) (slot_addr hw (by omega)) (hw.write (by omega)) fun t m z => ?_
  have kt : Keep P.B P.W [] [d] s.mem t.mem := by
    rw [m.mem]; exact keep_write _ _ (by simp) (by simp only [hdr] at hd'; omega)
  exact k t (h.slot1 kt hd m.sp m.rd m.wr (by rw [m.mem, slot_write_self])) (hw.of_mupd m) z m.gpr

/-- The new flag. -/
def flagv (V : Nat → Nat) : Nat :=
  (if V sBit = 1 then (decide (V sE1 = 1) || decide (V sE2 = 1)) else (decide (V sF = 1) || decide (V sE2 = 1))).toNat

/-- The flag, and the count decremented. -/
theorem St.pflag (hb : sBit ∈ LS) (h1 : sE1 ∈ LS) (h2 : sE2 ∈ LS) (hf : sF ∈ LS) (hk : sK ∈ LS)
    (vb : ∀ σ, E σ → V σ sBit ≤ 1) (v1 : ∀ σ, E σ → V σ sE1 ≤ 1) (v2 : ∀ σ, E σ → V σ sE2 ≤ 1)
    (vf : ∀ σ, E σ → V σ sF ≤ 1) (vk1 : ∀ σ, E σ → 1 ≤ V σ sK) (vk2 : ∀ σ, E σ → V σ sK < 2 ^ 32) :
    VP (St P E A L V LS) (.block (flagUpd ++ cntNext))
      (fun σ s => St P E A L (fun σ => upd (upd (V σ) sF (flagv (V σ))) sK (V σ sK - 1)) (sK :: sF :: LS) σ s ∧
        s.z = decide (V σ sK - 1 = 0)) := by
  refine VP.kv flag_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  have hr : ∀ r : Reg, r ∈ [Reg.r1, .r2, .r3, .r4] → r ∉ [Reg.r7, .r8, .r9] := by decide
  simp only [flagUpd, cntNext, List.cons_append, List.nil_append]
  refine h.ldr hw hb (r := .r1) (by decide) fun s1 h1' hw1 u1 => ?_
  refine h1'.ldr hw1 h1 (r := .r2) (by decide) fun s2 h2' hw2 u2 => ?_
  refine h2'.ldr hw2 h2 (r := .r3) (by decide) fun s3 h3' hw3 u3 => ?_
  refine h3'.ldr hw3 hf (r := .r4) (by decide) fun s4 h4' hw4 u4 => ?_
  refine wp_dp (op2_reg _ _) fun s5 u5 => ?_
  refine wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
  refine wp_dp (op2_reg _ _) fun s7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun s8 u8 => ?_
  refine wp_dp (op2_reg _ _) fun s9 u9 => ?_
  have r59 : Rest [.r1, .r2, .r4] s4 s9 := (u5.rest (by simp)).trans ((u6.rest (by simp)).trans
    ((u7.rest (by simp)).trans ((u8.rest (by simp)).trans (u9.rest (by simp)))))
  have m59 : s9.mem = s4.mem := u9.mem.trans (u8.mem.trans (u7.mem.trans (u6.mem.trans u5.mem)))
  have h9 := h4'.of_rest r59 m59
  have hw9 := hw4.rest r59
  have g1 : s4.gpr .r1 = BitVec.ofNat 32 (V σ sBit) := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
  have g2 : s4.gpr .r2 = BitVec.ofNat 32 (V σ sE1) := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr]
  have g3 : s4.gpr .r3 = BitVec.ofNat 32 (V σ sE2) := by rw [u4.other _ (by decide), u3.gpr]
  have g4 : s4.gpr .r4 = BitVec.ofNat 32 (V σ sF) := u4.gpr
  have g5 : s5.gpr .r2 = BitVec.ofNat 32 (V σ sE1) &&& BitVec.ofNat 32 (V σ sBit) := by
    rw [u5.gpr, dpVal, g2, g1]
  have g6 : s6.gpr .r1 = BitVec.ofNat 32 (V σ sBit) ^^^ 1 := by
    rw [u6.gpr, dpVal, u5.other _ (by decide), g1]
  have g7 : s7.gpr .r4 = BitVec.ofNat 32 (V σ sF) &&& (BitVec.ofNat 32 (V σ sBit) ^^^ 1) := by
    rw [u7.gpr, dpVal, u6.other _ (by decide), u5.other _ (by decide), g4, g6]
  have g8 : s8.gpr .r2 = (BitVec.ofNat 32 (V σ sE1) &&& BitVec.ofNat 32 (V σ sBit)) ||| BitVec.ofNat 32 (V σ sE2) := by
    rw [u8.gpr, dpVal, u7.other _ (by decide), u6.other _ (by decide), g5, u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), g3]
  have val : (s9.gpr .r2).toNat = flagv (V σ) := by
    rw [u9.gpr, dpVal, g8, u8.other _ (by decide), g7]
    exact flag_bv (vb σ e) (v1 σ e) (v2 σ e) (vf σ e)
  refine h9.str hw9 (d := sF) (by decide) (r := .r2) fun s10 h10 hw10 _ => ?_
  rw [val] at h10
  have hk' : sK ∈ sF :: LS := List.mem_cons_of_mem _ hk
  refine h10.ldr hw10 hk' (r := .r1) (by decide) fun s11 h11 hw11 u11 => ?_
  have kv : upd (V σ) sF (flagv (V σ)) sK = V σ sK := upd_ne _ _ (by decide)
  rw [kv] at u11
  refine wp_subs (op2_imm (by decide)) fun s12 u12 z12 => ?_
  have h12 := h11.of_rest (u12.rest (ws := [.r1]) (by simp)) u12.mem
  have hw12 := hw11.of_upd u12 (by decide) (by decide) (by decide)
  refine KS.strz h12 hw12 (d := sK) (by decide) (r := .r1) fun t ht hwt zt _ => WP.block_nil ⟨⟨e, ?_, hwt⟩, ?_⟩
  · have e12 : (s12.gpr .r1).toNat = V σ sK - 1 := by
      rw [u12.gpr, u11.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (vk1 σ e), BitVec.toNat_ofNat]
      have := vk2 σ e; omega
    rwa [e12] at ht
  · rw [zt, z12, u11.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (vk1 σ e), ofNat_beq_zero (by have := vk2 σ e; omega)]

/-- The flag 0 and the count `64 w − 1`. -/
theorem St.pinit :
    VP (St P E A L V LS) (.block initBlock)
      (St P E A L (fun σ => upd (upd (V σ) sF 0) sK (64 * P.w - 1)) (sK :: sF :: LS)) := by
  refine VP.kv init_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  have w128 := h.pre.w128
  have w4 := h.pre.w4
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  have h1 := h.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
  have hw1 := hw.of_upd u1 (by decide) (by decide) (by decide)
  refine h1.str hw1 (d := sF) (by decide) (r := .r1) fun s2 h2 hw2 m2 => ?_
  rw [u1.gpr] at h2
  refine wp_mov (op2_lsl (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  have r34 : Rest [.r1] s2 s4 := (u3.rest (by simp)).trans (u4.rest (by simp))
  have h4 := h2.of_rest r34 (u4.mem.trans u3.mem)
  have hw4 := hw2.rest r34
  refine h4.str hw4 (d := sK) (by decide) (r := .r1) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
  have e4 : (s4.gpr .r1).toNat = 64 * P.w - 1 := by
    rw [u4.gpr, dpVal, u3.gpr, m2.gpr, u1.other _ (by decide), hw.r9,
      show (65 : BitVec 32) = BitVec.ofNat 32 65 from rfl]
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      simp only [MP.W]; omega), BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [MP.W]; omega
  rw [e4, show (0 : BitVec 32).toNat = 0 from rfl] at ht
  exact ht

end

end VG.Proof.MillerRabin.Arm
