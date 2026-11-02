module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Pieces
import VerifiedGarbage.Proof.MillerRabin.Arm.Ops
import VerifiedGarbage.Proof.Rsa.Arm.RvKS

/-! # The Miller–Rabin round on ARMv7: the blocks on the header words as pieces

The counts (`St.ptabCnt`, `St.pcnt`, `St.pwinCnt`, `St.psqFour`), a
squaring's flag (`St.psqFlag`) and a window's end (`St.pwinEnd`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

theorem ofNat_toNat32 {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 32 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_shr32 {v : Nat} (h : v < 2 ^ 32) (n : Nat) : BitVec.ofNat 32 v >>> n = BitVec.ofNat 32 (v / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, ofNat_toNat32 h, Nat.shiftRight_eq_div_pow,
    ofNat_toNat32 (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

/-- The flag of a squaring on bits. -/
theorem sqflag_bits (f e m : Bool) :
    (BitVec.ofNat 32 f.toNat ||| (BitVec.ofNat 32 e.toNat &&& BitVec.ofNat 32 m.toNat)).toNat = (f || (m && e)).toNat := by
  cases f <;> cases e <;> cases m <;> decide

section
variable {P : MP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- `str t, [r8, #d]`, keeping the flags. -/
theorem KS.strz {σ s : State} {A : Nat → Nat} {V : Nat → Nat} {d : Nat} (h : KS P σ A L V LS s)
    (hw : Ws s P.B P.Z P.W nArr) (hd : d ∈ wDs) {r : Reg} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A L (upd V d (s.gpr r).toNat) (d :: LS) t → Ws t P.B P.Z P.W nArr → t.z = s.z →
      t.gpr = s.gpr → WP isa (.block rest) t Q) :
    WP isa (.block (.str r .r8 d :: rest)) s Q := by
  have hd' := wDs_hdr d hd
  have hz := hw.hdr_le
  refine wp_str_z (by simp only [hdr] at hd'; omega_arith) (slot_addr hw (by omega_arith)) (hw.write (by omega_arith)) fun t m z => ?_
  have kt : Keep P.B P.W [] [d] s.mem t.mem := by
    rw [m.mem]; exact keep_write _ _ (by simp) (by simp only [hdr] at hd'; omega_arith)
  exact k t (h.slot1 kt hd m.sp m.rd m.wr (by rw [m.mem, slot_write_self])) (hw.of_mupd m) z m.gpr

/-- The count of the table's entries. -/
theorem St.ptabCnt :
    VP (St P E A L V LS) (.block tabCnt) (St P E A L (fun σ => upd (V σ) sK 14) (sK :: LS)) := by
  refine VP.kv tabCnt_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  have h1 := h.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
  have hw1 := hw.of_upd u1 (by decide) (by decide) (by decide)
  refine h1.str hw1 (d := sK) (by decide) (r := .r1) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
  rw [u1.gpr] at ht; exact ht

/-- The count decremented. -/
theorem St.pcnt {n : Nat} (hk : sK ∈ LS) (vk : ∀ σ, E σ → V σ sK = n + 1) (hn : n + 1 < 2 ^ 32) :
    VP (St P E A L V LS) (.block cntNext)
      (fun σ s => St P E A L (fun σ => upd (V σ) sK n) (sK :: LS) σ s ∧ s.z = decide (n = 0)) := by
  refine VP.kv cnt_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  simp only [cntNext]
  refine h.ldr hw hk (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
  rw [vk σ e] at u1
  refine wp_subs (op2_imm (by decide)) fun s2 u2 z2 => ?_
  have h2 := h1.of_rest (u2.rest (ws := [.r1]) (by simp)) u2.mem
  have hw2 := hw1.of_upd u2 (by decide) (by decide) (by decide)
  have e2 : s2.gpr .r1 = BitVec.ofNat 32 n := by
    rw [u2.gpr, u1.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), Nat.add_sub_cancel]
  refine KS.strz h2 hw2 (d := sK) (by decide) (r := .r1) fun t ht hwt zt _ => WP.block_nil ⟨⟨e, ?_, hwt⟩, ?_⟩
  · rwa [e2, ofNat_toNat32 (by omega_arith)] at ht
  · rw [zt, z2, show s1.gpr .r1 - 1 = s2.gpr .r1 from u2.gpr.symm, e2, ofNat_beq_zero (by omega_arith)]

/-- The flag 0 and the count of windows `16 w`. -/
theorem St.pwinCnt :
    VP (St P E A L V LS) (.block winCnt)
      (St P E A L (fun σ => upd (upd (V σ) sF 0) sK (16 * P.w)) (sK :: sF :: LS)) := by
  refine VP.kv winCnt_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  have w128 := h.pre.w128
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
  have e4 : (s4.gpr .r1).toNat = 16 * P.w := by
    rw [u4.gpr, dpVal, u3.gpr, m2.gpr, u1.other _ (by decide), hw.r9,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl]
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      simp only [MP.W]; omega_arith), BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [MP.W]; omega_arith
  rw [e4, show (0 : BitVec 32).toNat = 0 from rfl] at ht
  exact ht

/-- Four squarings' count and threshold. -/
theorem St.psqFour :
    VP (St P E A L V LS) (.block sqFour)
      (St P E A L (fun σ => upd (upd (V σ) sR 0) sQ 4) (sQ :: sR :: LS)) := by
  refine VP.kv sqFour_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  have h1 := h.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
  have hw1 := hw.of_upd u1 (by decide) (by decide) (by decide)
  refine h1.str hw1 (d := sR) (by decide) (r := .r1) fun s2 h2 hw2 m2 => ?_
  rw [u1.gpr] at h2
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have h3 := h2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
  have hw3 := hw2.of_upd u3 (by decide) (by decide) (by decide)
  refine h3.str hw3 (d := sQ) (by decide) (r := .r1) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
  rw [u3.gpr] at ht; exact ht

/-- A squaring's flag: or'ed with `e₂` if the threshold is below the count
`k + 1`; the count decremented. -/
theorem St.psqFlag {k : Nat} {r : State → Nat} {fb eb : State → Bool} (hq : sQ ∈ LS) (hr : sR ∈ LS)
    (he : sE2 ∈ LS) (hf : sF ∈ LS) (vq : ∀ σ, E σ → V σ sQ = k + 1) (vr : ∀ σ, E σ → V σ sR = r σ)
    (rl : ∀ σ, E σ → r σ < 2 ^ 31) (hk : k + 1 < 2 ^ 31)
    (ve : ∀ σ, E σ → V σ sE2 = (eb σ).toNat) (vf : ∀ σ, E σ → V σ sF = (fb σ).toNat) :
    VP (St P E A L V LS) (.block sqFlag)
      (fun σ s => St P E A L (fun σ => upd (upd (V σ) sF (fb σ || (decide (r σ < k + 1) && eb σ)).toNat) sQ k)
        (sQ :: sF :: LS) σ s ∧ s.z = decide (k = 0)) := by
  refine VP.kv sqFlag_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  simp only [sqFlag]
  refine h.ldr hw hq (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
  refine h1.ldr hw1 hr (r := .r2) (by decide) fun s2 h2 hw2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  have r34 : Rest [.r2] s2 s4 := (u3.rest (by simp)).trans (u4.rest (by simp))
  have h4 := h2.of_rest r34 (u4.mem.trans u3.mem)
  have hw4 := hw2.rest r34
  refine h4.ldr hw4 he (r := .r3) (by decide) fun s5 h5 hw5 u5 => ?_
  refine wp_dp (op2_reg _ _) fun s6 u6 => ?_
  have h6 := h5.of_rest (u6.rest (ws := [.r3]) (by simp)) u6.mem
  have hw6 := hw5.of_upd u6 (by decide) (by decide) (by decide)
  refine h6.ldr hw6 hf (r := .r4) (by decide) fun s7 h7 hw7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun s8 u8 => ?_
  have h8 := h7.of_rest (u8.rest (ws := [.r4]) (by simp)) u8.mem
  have hw8 := hw7.of_upd u8 (by decide) (by decide) (by decide)
  have g1 : s8.gpr .r1 = BitVec.ofNat 32 (k + 1) := by
    rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide),
      u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr, vq σ e]
  have a1 : s2.gpr .r1 = BitVec.ofNat 32 (k + 1) := by rw [u2.other _ (by decide), u1.gpr, vq σ e]
  have a2 : s2.gpr .r2 = BitVec.ofNat 32 (r σ) := by rw [u2.gpr, vr σ e]
  have g4 : s4.gpr .r2 = BitVec.ofNat 32 (decide (r σ < k + 1)).toNat := by
    rw [u4.gpr, u3.gpr, dpVal, a1, a2]
    apply BitVec.eq_of_toNat_eq
    rw [mask_lt (rl σ e) hk, ofNat_toNat32 (by cases decide (r σ < k + 1) <;> decide)]
  have g8 : (s8.gpr .r4).toNat = (fb σ || (decide (r σ < k + 1) && eb σ)).toNat := by
    rw [u8.gpr, dpVal, u7.gpr, vf σ e, u7.other _ (by decide), u6.gpr, dpVal, u5.gpr, ve σ e,
      u5.other _ (by decide), g4]
    exact sqflag_bits _ _ _
  refine h8.str hw8 (d := sF) (by decide) (r := .r4) fun s9 h9 hw9 m9 => ?_
  rw [g8] at h9
  refine wp_subs (op2_imm (by decide)) fun s10 u10 z10 => ?_
  have h10 := h9.of_rest (u10.rest (ws := [.r1]) (by simp)) u10.mem
  have hw10 := hw9.of_upd u10 (by decide) (by decide) (by decide)
  have e10 : s10.gpr .r1 = BitVec.ofNat 32 k := by
    rw [u10.gpr, m9.gpr, g1, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), Nat.add_sub_cancel]
  refine KS.strz h10 hw10 (d := sQ) (by decide) (r := .r1) fun t ht hwt zt _ => WP.block_nil ⟨⟨e, ?_, hwt⟩, ?_⟩
  · rwa [e10, ofNat_toNat32 (by omega_arith)] at ht
  · rw [zt, z10, m9.gpr, g1, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), Nat.add_sub_cancel, ofNat_beq_zero (by omega_arith)]

/-- The digit at the top of the word `v`. -/
abbrev digitOf (v : Nat) : Nat := v / 2 ^ 28

/-- A window's end: the flag `y = 1 ∨ y = −1` if the digit is not 0, the
word shifted, the count of windows decremented, Z at the word's end. -/
theorem St.pwinEnd {K : Nat} {v : State → Nat} {e1 e2 fb : State → Bool} (hv : sV ∈ LS) (h1 : sE1 ∈ LS)
    (h2 : sE2 ∈ LS) (hf : sF ∈ LS) (hk : sK ∈ LS) (vv : ∀ σ, E σ → V σ sV = v σ) (vl : ∀ σ, E σ → v σ < 2 ^ 32)
    (v1 : ∀ σ, E σ → V σ sE1 = (e1 σ).toNat) (v2 : ∀ σ, E σ → V σ sE2 = (e2 σ).toNat)
    (vf : ∀ σ, E σ → V σ sF = (fb σ).toNat) (vk : ∀ σ, E σ → V σ sK = K + 1) (hK : K + 1 < 2 ^ 32) :
    VP (St P E A L V LS) (.block winEnd)
      (fun σ s => St P E A L (fun σ => upd (upd (upd (V σ) sF
          (if digitOf (v σ) = 0 then fb σ else (e1 σ || e2 σ)).toNat) sV (BitVec.ofNat 32 (v σ) <<< 4).toNat) sK K)
        (sK :: sV :: sF :: LS) σ s ∧ s.z = decide (K % 8 = 0)) := by
  refine VP.kv winEnd_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  have dl : digitOf (v σ) < 16 := by have := vl σ e; simp only [digitOf]; omega_arith
  simp only [winEnd]
  refine h.ldr hw hv (r := .r1) (by decide) fun s1 h1' hw1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  have r5 : Rest [.r2, .r3] s1 s5 :=
    (u2.rest (by simp)).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp))))
  have h5 := h1'.of_rest r5 (u5.mem.trans (u4.mem.trans (u3.mem.trans u2.mem)))
  have hw5 := hw1.rest r5
  refine h5.ldr hw5 h1 (r := .r4) (by decide) fun s6 h6 hw6 u6 => ?_
  refine h6.ldr hw6 h2 (r := .r5) (by decide) fun s7 h7 hw7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun s8 u8 => ?_
  refine wp_dp (op2_reg _ _) fun s9 u9 => ?_
  have r9 : Rest [.r4] s7 s9 := (u8.rest (by simp)).trans (u9.rest (by simp))
  have h9 := h7.of_rest r9 (u9.mem.trans u8.mem)
  have hw9 := hw7.rest r9
  refine h9.ldr hw9 hf (r := .r5) (by decide) fun s10 h10 hw10 u10 => ?_
  refine wp_dp (op2_reg _ _) fun s11 u11 => ?_
  refine wp_dp (op2_reg _ _) fun s12 u12 => ?_
  have r12 : Rest [.r4, .r5] s10 s12 := (u11.rest (by simp)).trans (u12.rest (by simp))
  have h12 := h10.of_rest r12 (u12.mem.trans u11.mem)
  have hw12 := hw10.rest r12
  -- The values.
  have gz : s4.gpr .r2 = BitVec.ofNat 32 (decide (digitOf (v σ) = 0)).toNat := by
    rw [u4.gpr, u3.gpr, dpVal, u2.gpr, u1.gpr, vv σ e, ofNat_shr32 (vl σ e)]
    apply BitVec.eq_of_toNat_eq
    rw [mask_zero _ dl, ofNat_toNat32 (by cases decide (digitOf (v σ) = 0) <;> decide)]
  have x5 : s5.gpr .r3 = BitVec.ofNat 32 (decide (digitOf (v σ) = 0)).toNat ^^^ 1 := by
    rw [u5.gpr, dpVal, gz]
  have x7r3 : s7.gpr .r3 = s5.gpr .r3 := by rw [u7.other _ (by decide), u6.other _ (by decide)]
  have x7r4 : s7.gpr .r4 = BitVec.ofNat 32 (e1 σ).toNat := by rw [u7.other _ (by decide), u6.gpr, v1 σ e]
  have x7r5 : s7.gpr .r5 = BitVec.ofNat 32 (e2 σ).toNat := by rw [u7.gpr, v2 σ e]
  have x9 : s9.gpr .r4 = (BitVec.ofNat 32 (e1 σ).toNat ||| BitVec.ofNat 32 (e2 σ).toNat) &&&
      (BitVec.ofNat 32 (decide (digitOf (v σ) = 0)).toNat ^^^ 1) := by
    rw [u9.gpr, dpVal, u8.gpr, dpVal, x7r4, x7r5, u8.other _ (by decide), x7r3, x5]
  have x10r2 : s10.gpr .r2 = s4.gpr .r2 := by
    rw [u10.other _ (by decide), r9.gpr _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide)]
  have x11 : s11.gpr .r5 = BitVec.ofNat 32 (fb σ).toNat &&& BitVec.ofNat 32 (decide (digitOf (v σ) = 0)).toNat := by
    rw [u11.gpr, dpVal, u10.gpr, vf σ e, x10r2, gz]
  have gF : (s12.gpr .r4).toNat = (if digitOf (v σ) = 0 then fb σ else (e1 σ || e2 σ)).toNat := by
    rw [u12.gpr, dpVal, x11, u11.other _ (by decide), u10.other _ (by decide), x9]
    have := flag_bits (decide (digitOf (v σ) = 0)) (e1 σ) (e2 σ) (fb σ)
    simp only [decide_eq_true_eq] at this
    exact this
  refine h12.str hw12 (d := sF) (by decide) (r := .r4) fun s13 h13 hw13 m13 => ?_
  rw [gF] at h13
  refine wp_mov (op2_lsl (by decide)) fun s14 u14 => ?_
  have h14 := h13.of_rest (u14.rest (ws := [.r1]) (by simp)) u14.mem
  have hw14 := hw13.of_upd u14 (by decide) (by decide) (by decide)
  have g14 : s14.gpr .r1 = BitVec.ofNat 32 (v σ) <<< 4 := by
    rw [u14.gpr, m13.gpr, u12.other _ (by decide), u11.other _ (by decide), u10.other _ (by decide),
      u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      r5.gpr _ (by decide), u1.gpr, vv σ e]
  refine h14.str hw14 (d := sV) (by decide) (r := .r1) fun s15 h15 hw15 m15 => ?_
  rw [g14] at h15
  refine h15.ldr hw15 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hk)) (r := .r1) (by decide)
    fun s16 h16 hw16 u16 => ?_
  have k16 : upd (upd (V σ) sF (if digitOf (v σ) = 0 then fb σ else (e1 σ || e2 σ)).toNat)
      sV (BitVec.ofNat 32 (v σ) <<< 4).toNat sK = K + 1 := by
    simp only [upd, show sK ≠ sV by decide, show sK ≠ sF by decide, ↓reduceIte]; exact vk σ e
  rw [k16] at u16
  refine wp_dp (op2_imm (by decide)) fun s17 u17 => ?_
  have h17 := h16.of_rest (u17.rest (ws := [.r1]) (by simp)) u17.mem
  have hw17 := hw16.of_upd u17 (by decide) (by decide) (by decide)
  have e17 : s17.gpr .r1 = BitVec.ofNat 32 K := by
    rw [u17.gpr, dpVal, u16.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), Nat.add_sub_cancel]
  refine h17.str hw17 (d := sK) (by decide) (r := .r1) fun s18 h18 hw18 m18 => ?_
  rw [e17, ofNat_toNat32 (by omega_arith)] at h18
  refine wp_dp (op2_imm (by decide)) fun s19 u19 => ?_
  refine wp_cmp (op2_imm (by decide)) fun t u20 z20 => WP.block_nil ⟨⟨e, ?_, ?_⟩, ?_⟩
  · exact h18.of_rest ((u19.rest (ws := [.r1]) (by simp)).trans (u20.rest _)) (u20.mem.trans u19.mem)
  · exact (hw18.of_upd u19 (by decide) (by decide) (by decide)).rest (u20.rest [])
  · rw [z20, u19.gpr, dpVal, m18.gpr, e17]
    have : BitVec.ofNat 32 K &&& 7 = BitVec.ofNat 32 (K % 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, ofNat_toNat32 (by omega_arith), show (7 : BitVec 32).toNat = 2 ^ 3 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, ofNat_toNat32 (by omega_arith)]
    rw [this, show BitVec.ofNat 32 (K % 8) - 0 = BitVec.ofNat 32 (K % 8) from BitVec.sub_zero _,
      ofNat_beq_zero (by omega_arith)]

end

end VG.Proof.MillerRabin.Arm
