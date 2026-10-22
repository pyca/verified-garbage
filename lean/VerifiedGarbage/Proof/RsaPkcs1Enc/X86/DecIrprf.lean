module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecPrf
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecTaint

/-!
# RSAES-PKCS1-v1_5 decryption on x86: `CL` and `AM`

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecIrprf.lean`): the two IRPRF loops
(`Prf`): `CL = IRPRF(KDK, "length", 256)` at `scratch + sCL`
(`clLoop_vp`), keeping `KDK`, and `AM = IRPRF(KDK, "message", k)` at
`scratch + sAM` (`amLoop_vp`), keeping `CL` (`IR`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.RsaPkcs1Enc (prfBlock)

variable {P : EP}

theorem ascii_length : Spec.RsaPkcs1Enc.ascii "length" = lengthLabel.map (BitVec.ofNat 8) := by decide

theorem ascii_message : Spec.RsaPkcs1Enc.ascii "message" = messageLabel.map (BitVec.ofNat 8) := by decide

/-- `CL`. -/
abbrev clV (P : EP) (σ : State) : List Byte :=
  Spec.RsaPkcs1Enc.irprf (kdkV P σ) (Spec.RsaPkcs1Enc.ascii "length") 256

/-- `AM`. -/
abbrev amV (P : EP) (σ : State) : List Byte :=
  Spec.RsaPkcs1Enc.irprf (kdkV P σ) (Spec.RsaPkcs1Enc.ascii "message") P.K

/-- The loop of `CL`, keeping `KDK`. -/
def RCL (P : EP) : Prf P where
  vs := lengthLabel
  len := clLen
  L := 256
  dst := sCL
  nb := 8
  xo := sKDK
  xn := 32
  xv := kdkV P
  vs_len := by decide
  nb1 := by decide
  nb_le := by decide
  dst_lo := by decide
  dst_hi := by decide
  x_lo := by decide
  x_hi := by decide
  x_sep := .inl (by decide)
  lenOk := @fun _ _ _ _ _ bx _ h _ k => clLen_wp rfl bx h k

/-- `CL`'s blocks. -/
abbrev clBlocks (P : EP) (σ : State) : List Byte :=
  (List.range 8).flatMap (prfBlock (kdkV P σ) (lengthLabel.map (BitVec.ofNat 8)) 256)

/-- The loop of `AM`, keeping `CL`, for `64 ≤ k ≤ 1024`. -/
def RAM (P : EP) (hK : 64 ≤ P.K ∧ P.K ≤ 1024) : Prf P where
  vs := messageLabel
  len := amLen
  L := P.K
  dst := sAM
  nb := (P.K + 31) / 32
  xo := sCL
  xn := 256
  xv := clBlocks P
  vs_len := by decide
  nb1 := by omega
  nb_le := by omega
  dst_lo := by decide
  dst_hi := by simp only [sAM]; omega
  x_lo := by decide
  x_hi := by decide
  x_sep := .inl (by decide)
  lenOk := @fun _ _ _ _ _ bx dx h _ k => amLen_wp rfl hK.2 bx dx h k

theorem certsCL : Certs (RCL P) := ⟨msgCL_taint, prfUpdCL_taint, prfFinCL_taint⟩

theorem certsAM {hK : 64 ≤ P.K ∧ P.K ≤ 1024} : Certs (RAM P hK) := ⟨msgAM_taint, prfUpdAM_taint, prfFinAM_taint⟩

/-- `mov eax, 0; mov [oI], eax`, then the number of blocks `nb` (from `is`)
to its slot: the counter's and the number's slots written. -/
theorem slots_frame {s t : State} {nb : Nat}
    (h : t.mem = (s.mem.writeW (P.lay.fr oI) (BitVec.ofNat 32 0)).writeW (P.lay.fr oNB) (BitVec.ofNat 32 nb)) :
    Frame [⟨P.lay.fr oI, 4⟩, ⟨P.lay.fr oNB, 4⟩] s.mem t.mem := by
  rw [h]
  exact ((Frame.refl _ _).writeW List.mem_cons_self (BitVec.ofNat 32 0) (Region.contains_self _ _)).writeW
    (List.mem_cons_of_mem _ List.mem_cons_self) (BitVec.ofNat 32 nb) (Region.contains_self _ _)

/-- The loop starts: what it keeps, and the slots. -/
theorem b0_start {R : Prf P} {σ s t : State} (hb : Base P σ s) (st : P.lay.St σ t)
    (hk : Spec.Rsa.bytesAt s.mem (sc P sKDK 32).base 32 = kdkV P σ)
    (hx : Spec.Rsa.bytesAt s.mem (sc P R.xo R.xn).base R.xn = R.xv σ)
    (h : t.mem = (s.mem.writeW (P.lay.fr oI) (BitVec.ofNat 32 0)).writeW (P.lay.fr oNB) (BitVec.ofNat 32 R.nb)) :
    B0 P R 0 σ t := by
  have hs := hb.1
  have fr := slots_frame h
  have sd : ∀ r ∈ [(⟨P.lay.fr oI, 4⟩ : Region), ⟨P.lay.fr oNB, 4⟩],
      Safe P r ∧ (sc P sKDK 32).Disjoint r ∧ (sc P R.xo R.xn).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨hs.1.safe_fr (by decide) (by simp only [oR, oI]; decide),
        (hs.1.fr_sc (by simp only [oI, frameBytes]; decide) (by decide)).symm,
        (hs.1.fr_sc (by simp only [oI, frameBytes]; decide) (by have := R.x_hi; omega)).symm⟩
    · exact ⟨hs.1.safe_fr (by decide) (by simp only [oR, oNB]; decide),
        (hs.1.fr_sc (by simp only [oNB, frameBytes]; decide) (by decide)).symm,
        (hs.1.fr_sc (by simp only [oNB, frameBytes]; decide) (by have := R.x_hi; omega)).symm⟩
  refine ⟨⟨Nat.zero_le _, hb.frame st fr fun r hr => (sd r hr).1,
    (Proof.RsaPkcs1Sig.bytesAt_frame fr (fun r hr => (sd r hr).2.1) (by decide)).trans hk,
    (Proof.RsaPkcs1Sig.bytesAt_frame fr (fun r hr => (sd r hr).2.2) (by have := R.x_hi; omega)).trans hx,
    ?_, by simp [Spec.Rsa.bytesAt]⟩, ?_⟩
  · rw [h, Mem.readW_writeW_self32]
  · rw [h, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

theorem clInit_vp : VP (K6 P) (.block clInit) (B0 P (RCL P) 0) :=
  VP.taint [.esp] clInit_taint (sp_agree fun _ _ h => h.1.1) fun σ s h => by
    obtain ⟨hb, kd⟩ := h
    have hs := hb.1
    simp only [clInit]
    refine St.movi hs (d := .eax) (by decide) 0 fun t1 s1 u1 => ?_
    refine s1.2.wp_strFr (d := oI) (by show oI + 4 ≤ frameBytes; decide) fun t2 st2 m2 => ?_
    refine St.movi ⟨hs.1, st2⟩ (d := .eax) (by decide) 8 fun t3 s3 u3 => ?_
    refine s3.2.wp_strFr (d := oNB) (by show oNB + 4 ≤ frameBytes; decide) fun t4 st4 m4 => WP.block_nil ?_
    have kd' : Spec.Rsa.bytesAt s.mem (sc P sKDK 32).base 32 = kdkV P σ := by
      rw [← hs.1.sr_eq (by decide)]; exact kd
    exact b0_start (R := RCL P) hb st4 kd' kd' (by rw [m4.mem, u3.gpr, u3.mem, m2.mem, u1.gpr, u1.mem]; rfl)

theorem nb_val {K : Nat} (hK : K ≤ 1024) :
    (BitVec.ofNat 32 K + BitVec.ofNat 32 31) >>> 5 = BitVec.ofNat 32 ((K + 31) / 32) := by
  rw [BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem amInit_vp (hK : 64 ≤ P.K ∧ P.K ≤ 1024) : VP (CI P (RCL P) 8) (.block amInit) (B0 P (RAM P hK) 0) :=
  VP.taint [.esp] amInit_taint (sp_agree fun _ _ h => h.S) fun σ s h => by
    have hs := h.S
    simp only [amInit]
    refine St.movi hs (d := .eax) (by decide) 0 fun t1 s1 u1 => ?_
    refine s1.2.wp_strFr (d := oI) (by show oI + 4 ≤ frameBytes; decide) fun t2 st2 m2 => ?_
    refine St.argv ⟨hs.1, st2⟩ (j := 4) (by decide) (d := .eax) (by decide) fun t3 s3 u3 => ?_
    refine wp_addi fun t4 u4 => ?_
    refine wp_shr (n := 5) (by decide) fun t5 u5 _ => ?_
    have st5 := (s3.2.upd u4 (by decide)).upd u5 (by decide)
    refine st5.wp_strFr (d := oNB) (by show oNB + 4 ≤ frameBytes; decide) fun t6 st6 m6 => WP.block_nil ?_
    have ax : t5.gpr .eax = BitVec.ofNat 32 ((P.K + 31) / 32) := by
      rw [u5.gpr, u4.gpr, u3.gpr]; exact nb_val hK.2
    refine b0_start (R := RAM P hK) h.base st6 h.kdk h.blk ?_
    rw [m6.mem, ax, u5.mem, u4.mem, u3.mem, m2.mem, u1.gpr, u1.mem]; rfl

/-! ## The loops -/

/-- `CL` and `AM` in `scratch`. -/
def IR (P : EP) (σ s : State) : Prop :=
  Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sCL 256).base 256 = clV P σ ∧
    Spec.Rsa.bytesAt s.mem (sc P sAM P.K).base P.K = amV P σ

theorem flatMap_blocks_length (kd lab : List Byte) (L : Nat) :
    ∀ n, ((List.range n).flatMap (prfBlock kd lab L)).length = 32 * n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, flatMap_blocks_length kd lab L n,
      List.flatMap_singleton, prfBlock, hmac_len]
    omega

theorem bytesAt_take (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) :
    Spec.Rsa.bytesAt m p k = (Spec.Rsa.bytesAt m p n).take k := by
  simp only [Spec.Rsa.bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem clV_eq (P : EP) (σ : State) : clV P σ = clBlocks P σ := by
  rw [clV, Proof.RsaPkcs1Enc.irprf_eq, ascii_length]
  exact List.take_of_length_le (by rw [flatMap_blocks_length])

theorem ir_of {σ s : State} {hK : 64 ≤ P.K ∧ P.K ≤ 1024} (h : CI P (RAM P hK) ((P.K + 31) / 32) σ s) :
    IR P σ s := by
  refine ⟨h.base, by rw [clV_eq]; exact h.x, ?_⟩
  have hb := h.blk
  simp only [RAM] at hb
  rw [amV, Proof.RsaPkcs1Enc.irprf_eq, ascii_message, ← hb, ← bytesAt_take _ _ (by omega)]

theorem clLoop_vp (v : Backend) : VP (K6 P) (clLoop v.F) (CI P (RCL P) 8) :=
  clInit_vp.seq (loop_vp (R := RCL P) v certsCL)

theorem amLoop_vp (v : Backend) : VP (CI P (RCL P) 8) (amLoop v.F) (IR P) := by
  by_cases hK : 64 ≤ P.K ∧ P.K ≤ 1024
  · exact (amInit_vp hK).seq ((loop_vp (R := RAM P hK) v certsAM).mono (fun _ _ h => h) fun _ _ h => ir_of h)
  · exact VP.of_false fun _ _ h => hK ⟨h.S.1.k64, h.S.1.k1024⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
