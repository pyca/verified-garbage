module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecValid
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecTaint

/-!
# RSAES-PKCS1-v1_5 decryption on x86: `*msg_len` and the output

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecValid.lean`,
`Proof/RsaPkcs1Enc/Arm/DecSel.lean`): the masked length written as a 64-bit
word to `*msg_len` (`mlRest_vp`); byte `i` of `out` (`obV`): `EM[i]` or
`AM[i]` as the validity selects, if `i ≥ k - len` and the private-key
operation succeeded, and zero otherwise (`selLoop_vp`); then the result
returned (`finR_vp`), which is what the shared contract states (`res_of`,
`Res`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Mont.X86 (wp_storeS wp_subS)
open VG.Proof.RsaPkcs1Enc (outByte)

variable {P : EP}

/-! ## `*msg_len` -/

/-- A 64-bit word written as two 32-bit halves, the high one zero. -/
theorem readW_pair (m : Mem) (a : Addr) {L : Nat} (hL : L < 2 ^ 32) :
    ((m.writeW a (BitVec.ofNat 32 L)).writeW (a + BitVec.ofNat 64 4) (BitVec.ofNat 32 0)).readW a 64 =
      BitVec.ofNat 64 L := by
  show (Mem.read _ a 8).setWidth 64 = _
  rw [Mem.read_eq_of_bytes (n := 8) (v := BitVec.ofNat 64 L) fun i hi => ?_]
  · exact BitVec.setWidth_eq _
  by_cases h4 : i < 4
  · have e1 : ¬ (a + BitVec.ofNat 64 i - (a + BitVec.ofNat 64 4)).toNat < 32 / 8 := by
      rw [show a + BitVec.ofNat 64 i - (a + BitVec.ofNat 64 4) = BitVec.ofNat 64 i - BitVec.ofNat 64 4 by
        rw [Offset.add_sub_add_left]]
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    simp only [Mem.writeW]
    rw [Mem.write_apply e1]
    simp only [Mem.write, Mem.sub_ofNat_toNat a (by omega : i < 2 ^ 64), show i < 32 / 8 by omega, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show L < 2 ^ (8 * (32 / 8)) from hL),
      Nat.mod_eq_of_lt (show L < 2 ^ (8 * 8) from Nat.lt_of_lt_of_le hL (by decide))]
    rw [show 8 * (32 / 8) = 32 from rfl, Nat.mod_eq_of_lt hL]
  · have e : a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 4 + BitVec.ofNat 64 (i - 4) := by
      rw [Offset.add_add, show 4 + (i - 4) = i by omega]
    simp only [Mem.writeW, Mem.write]
    rw [e, Mem.sub_ofNat_toNat _ (by omega : i - 4 < 2 ^ 64)]
    simp only [show i - 4 < 32 / 8 by omega, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have : 2 ^ 32 ≤ 2 ^ (8 * i) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.div_eq_of_lt (by omega : L % 2 ^ 64 < 2 ^ (8 * i))]
    simp

theorem In.ml_fit {σ : State} (h : In P σ) : P.ml.toNat + 8 ≤ 2 ^ 32 := by
  have := h.ok.fits P.ML (by simp)
  simp only [BitVec.toNat_setWidth] at this
  rwa [Nat.mod_eq_of_lt (by have := P.ml.isLt; omega)] at this

theorem In.out_ml {σ : State} (h : In P σ) : P.OUT.Disjoint P.ML := by
  have := h.ok.wrw
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at this
  exact this.1.1

theorem SB.keep_ml {σ s t : State} (h : SB P σ s) (st : P.lay.St σ t) (hf : Frame [P.ML] s.mem t.mem) :
    SB P σ t := by
  have hs := h.S
  have hK := hs.1.k1024
  have fr : ∀ d, d + 4 ≤ frameBytes → Region.Disjoint ⟨P.lay.fr d, 4⟩ P.ML := fun d hd =>
    hs.1.ok.stk_fr (R := P.ML) (.inr (by simp)) (by show d + 4 ≤ frameBytes + 16; omega)
  have one : ∀ {R : Region}, R.Disjoint P.ML → ∀ r ∈ [P.ML], R.Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  obtain ⟨⟨⟨hb, cl, am⟩, al⟩, out, rc⟩ := h
  refine ⟨⟨⟨hb.frame st hf fun r hr => ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨hs.1.out_ml, fr oR (by decide)⟩
  · rw [Proof.RsaPkcs1Sig.bytesAt_frame hf (one (hs.1.sc_ml (by decide))) (by decide)]; exact cl
  · rw [Proof.RsaPkcs1Sig.bytesAt_frame hf (one (hs.1.sc_ml (by simp only [sAM]; omega))) (by omega)]
    exact am
  · rw [slot_keep hf (one (fr oAL (by decide)))]; exact al
  · rw [Proof.RsaPkcs1Sig.bytesAt_frame hf (one hs.1.out_ml) (by omega)]; exact out
  · rw [slot_keep hf (one (fr oR (by decide)))]; exact rc

/-- What the output needs: `out`, `AM`, the result and the masks in their slots, and `k - len`. -/
def VK (P : EP) (σ s : State) : Prop :=
  SB P σ s ∧ s.mem.readW (P.lay.fr oV) 32 = mk (vB P σ) ∧ s.mem.readW (P.lay.fr oOK) 32 = mk (okB P σ) ∧
    s.gpr .ebx = BitVec.ofNat 32 (P.K - lselV P σ)

/-- After the load of `msg_len`. -/
def VM (P : EP) (σ s : State) : Prop := VB P σ s ∧ s.gpr .esi = P.ml

/-- `*msg_len` written. -/
def VW (P : EP) (σ s : State) : Prop :=
  VK P σ s ∧ Spec.Rsa.wordsAt s.mem (P.ml.setWidth 64) 1 = [BitVec.ofNat 64 (if okB P σ then lselV P σ else 0)]

theorem mlHead_vp : VP (VB P) (.block (mlStore.take 1)) (VM P) :=
  VP.taint [.esp] mlHead_taint (sp_agree fun _ _ h => h.1.S) fun σ s h => by
    have hs := h.1.S
    refine St.argv hs (j := 2) (by decide) (d := .esi) (by decide) fun t1 s1 u1 => WP.block_nil ?_
    obtain ⟨hb, v, ok, bx, dx⟩ := h
    exact ⟨⟨hb.of_mem s1.2 u1.mem, by rw [u1.mem]; exact v, by rw [u1.mem]; exact ok,
      by rw [u1.other _ (by decide), bx], by rw [u1.other _ (by decide), dx]⟩, u1.gpr⟩

theorem mlRest_vp : VP (VM P) (.block (mlStore.drop 1)) (VW P) :=
  VP.taint [.esi] mlRest_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun σ s h => by
    obtain ⟨⟨hb, v, ok, bx, dx⟩, si⟩ := h
    have hs := hb.S
    have hK := hs.1.k1024
    have fit := hs.1.ml_fit
    have win : ∀ d, d + 4 ≤ 8 → InRegions s.wr (P.ml.setWidth 64 + BitVec.ofNat 64 d) 4 := fun d hd =>
      ⟨P.ML, hs.2.inRw (by simp), Offset.contains_base _ hd (by omega)⟩
    simp only [mlStore, List.drop_succ_cons, List.drop_zero]
    refine wp_storeS (a := P.ml.setWidth 64 + BitVec.ofNat 64 0)
      (by show s.ea ⟨.esi, 0⟩ = _; rw [ea_at, si]; exact addr_eq (by omega)) (win 0 (by decide)) fun t1 m1 => ?_
    refine wp_movi fun t2 u2 => ?_
    refine wp_storeS (a := P.ml.setWidth 64 + BitVec.ofNat 64 4)
      (by show t2.ea ⟨.esi, 4⟩ = _; rw [ea_at, u2.other _ (by decide), m1.gpr, si]; exact addr_eq (by omega))
      (by rw [u2.wr, m1.wr]; exact win 4 (by decide)) fun t3 m3 => WP.block_nil ?_
    have mm : t3.mem = (s.mem.writeW (P.ml.setWidth 64 + BitVec.ofNat 64 0) (s.gpr .edx)).writeW
        (P.ml.setWidth 64 + BitVec.ofNat 64 4) (BitVec.ofNat 32 0) := by
      rw [m3.mem, u2.gpr, u2.mem, m1.mem]
    have fr : Frame [P.ML] s.mem t3.mem := by
      rw [mm]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (s.gpr .edx)
        (Offset.contains_base _ (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
    have st : P.lay.St σ t3 := hs.2.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.ML, by simp, fun _ h => h⟩)
      (by rw [m3.rd, u2.rd, m1.rd]) (by rw [m3.wr, u2.wr, m1.wr])
      (by rw [m3.gpr, u2.other _ (by decide), m1.gpr])
    have frd : ∀ d, d + 4 ≤ frameBytes → ∀ r ∈ [P.ML], Region.Disjoint ⟨P.lay.fr d, 4⟩ r := fun d hd r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hs.1.ok.stk_fr (R := P.ML) (.inr (by simp)) (by show d + 4 ≤ frameBytes + 16; omega)
    refine ⟨⟨hb.keep_ml st fr, by rw [slot_keep fr (frd oV (by decide))]; exact v,
      by rw [slot_keep fr (frd oOK (by decide))]; exact ok, by rw [m3.gpr, u2.other _ (by decide), m1.gpr, bx]⟩, ?_⟩
    have hl : (if okB P σ then lselV P σ else 0) < 2 ^ 32 := by
      have := lsel_le P σ (by have := hs.1.k64; omega); split <;> omega
    show [t3.mem.readW (P.ml.setWidth 64 + BitVec.ofNat 64 (8 * 0)) 64] = _
    rw [mm, dx, show 8 * 0 = 0 from rfl]
    exact congrArg (· :: []) (by rw [BitVec.add_zero]; exact readW_pair _ _ hl)

/-! ## The output -/

/-- Byte `i` of the output. -/
abbrev obV (P : EP) (σ : State) (i : Nat) : Byte :=
  outByte (vB P σ) (okB P σ) (P.K - lselV P σ) i ((emOf P σ).getD i 1) ((amV P σ).getD i 0)

/-- `j` bytes of `out` written. -/
def SL (P : EP) (j : Nat) (σ s : State) : Prop :=
  S P σ s ∧
    (∀ i < P.K, s.mem (P.out.setWidth 64 + BitVec.ofNat 64 i) = if i < j then obV P σ i else (emOf P σ).getD i 1) ∧
    Spec.Rsa.bytesAt s.mem (sc P sAM P.K).base P.K = amV P σ ∧ s.mem.readW (P.lay.fr oR) 32 = rcOf P σ ∧
    Spec.Rsa.wordsAt s.mem (P.ml.setWidth 64) 1 = [BitVec.ofNat 64 (if okB P σ then lselV P σ else 0)] ∧
    s.mem.readW (P.lay.fr oV) 32 = mk (vB P σ) ∧ s.mem.readW (P.lay.fr oOK) 32 = mk (okB P σ) ∧
    s.gpr .esi = P.out + BitVec.ofNat 32 j ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 (sAM + j) ∧
    s.gpr .edx = BitVec.ofNat 32 j ∧ s.gpr .ecx = BitVec.ofNat 32 (P.K - j) ∧
    s.gpr .ebx = BitVec.ofNat 32 (P.K - lselV P σ) ∧ (emOf P σ).length = P.K

theorem selInit_vp : VP (VW P) (.block selInit) (SL P 0) :=
  VP.taint [.esp] selInit_taint (sp_agree fun _ _ h => h.1.1.S) fun σ s h => by
    obtain ⟨⟨hb, v, ok, bx⟩, ml⟩ := h
    have hs := hb.S
    simp only [selInit, List.cons_append, List.append_assoc]
    refine St.argv hs (j := 0) (by decide) (d := .esi) (by decide) fun t1 s1 u1 => ?_
    refine St.scrW s1 (d := .edi) (by decide) sAM fun t2 s2 u2 => ?_
    refine St.movi s2 (d := .edx) (by decide) 0 fun t3 s3 u3 => ?_
    refine St.argv s3 (j := 4) (by decide) (d := .ecx) (by decide) fun t4 s4 u4 => WP.block_nil ?_
    have mm : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨s4, fun i hi => ?_, by rw [mm]; exact hb.1.1.2.2, by rw [mm]; exact hb.2.2, by rw [mm]; exact ml,
      by rw [mm]; exact v, by rw [mm]; exact ok, ?_, ?_, ?_, ?_, ?_, emOf_length hb⟩
    · rw [mm, hb.byte hi]; simp
    · rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
      exact (BitVec.add_zero _).symm
    · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr]; rfl
    · rw [u4.other _ (by decide), u3.gpr]
    · rw [u4.gpr]; rfl
    · simp (disch := decide) only [u4.other, u3.other, u2.other, u1.other]; exact bx

theorem selByte (e a : Byte) (v c : Bool) :
    ((if v then e.setWidth 32 else a.setWidth 32) &&& mk c).setWidth 8 = if c then (if v then e else a) else 0 := by
  have h8 : ∀ b : Byte, (b.setWidth 32).setWidth 8 = b := fun b => by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]
  cases c <;> cases v <;> simp only [mk, Bool.false_eq_true, ↓reduceIte, BitVec.and_zero, BitVec.and_allOnes, h8]
    <;> rfl

theorem outByte_eq (v ok : Bool) (kl i : Nat) (e a : Byte) :
    outByte v ok kl i e a = if (!decide (i < kl) && ok) then (if v then e else a) else 0 := by
  simp only [outByte]
  by_cases h : i < kl <;> cases ok <;> simp [h] <;> omega

/-- `m` bytes left. -/
def SLM (P : EP) (m : Nat) (σ s : State) : Prop := m ≤ P.K ∧ SL P (P.K - m) σ s

theorem selBody_vp (n : Nat) : VP (SLM P (n + 1)) (.block selBody) fun σ s =>
    isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → SL P P.K σ s) ∧ (0 < n → SLM P n σ s) := by
  refine VP.taint [.esp, .esi, .edi, .ecx] selBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.2.1.2.sp, h₂.2.1.2.sp]
    · rw [h₁.2.2.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.2.2.1]
    · rw [h₁.2.2.2.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.2.2.2.1]
    · rw [h₁.2.2.2.2.2.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.2.2.2.2.2.1]
  obtain ⟨hn, hs, ob, am, rc, ml, sv, sok, si, di, dx, cx, bx, hEM⟩ := h
  generalize hj : P.K - (n + 1) = j at ob si di dx cx
  have hK := hs.1.k64
  have hK' := hs.1.k1024
  have hjK : j < P.K := by omega
  have hl := lsel_le P σ (by omega)
  simp only [selBody]
  refine wp_movzx8 (a := P.out.setWidth 64 + BitVec.ofNat 64 j)
    (by show s.ea ⟨.esi, 0⟩ = _; rw [ea_at, si, hs.1.outA (d := 0) (by omega)]; rfl)
    (St.out_r hs (by omega)) fun t1 u1 => ?_
  refine wp_movzx8 (a := P.scr.setWidth 64 + BitVec.ofNat 64 (sAM + j))
    (by show t1.ea ⟨.edi, 0⟩ = _
        rw [ea_at, u1.other _ (by decide), di, hs.1.addrSc (by simp only [sAM]; omega)]; rfl)
    (by rw [u1.rd, u1.wr]; exact St.sc_r hs (by simp only [sAM]; omega)) fun t2 u2 => ?_
  refine wp_xor fun t3 u3 => ?_
  have st3 := ((hs.2.upd u1 (by decide)).upd u2 (by decide)).upd u3 (by decide)
  refine wp_andS (st3.readSlot (d := oV) (by show oV + 4 ≤ frameBytes; decide)) fun t4 u4 => ?_
  refine wp_xor fun t5 u5 => ?_
  refine wp_mov fun t6 u6 => ?_
  refine wp_subS (readSrc_reg _ _) fun t7 u7 c7 => ?_
  refine wp_sbb_self c7 fun t8 u8 => ?_
  refine wp_xorI fun t9 u9 => ?_
  have st9 := ((((((st3.upd u4 (by decide)).upd u5 (by decide)).upd u6 (by decide)).upd u7 (by decide)).upd u8
    (by decide)).upd u9 (by decide))
  refine wp_andS (st9.readSlot (d := oOK) (by show oOK + 4 ≤ frameBytes; decide)) fun t10 u10 => ?_
  refine wp_and fun t11 u11 => ?_
  have m11 : t11.mem = s.mem := by
    rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine wp_store8 (a := P.out.setWidth 64 + BitVec.ofNat 64 j)
    (by show t11.ea ⟨.esi, 0⟩ = _
        rw [ea_at]
        simp (disch := decide) only [u11.other, u10.other, u9.other, u8.other, u7.other, u6.other, u5.other,
          u4.other, u3.other, u2.other, u1.other]
        rw [si, hs.1.outA (d := 0) (by omega)]; rfl)
    (by rw [u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
        exact St.out_w hs (by omega)) fun t12 m12 => ?_
  refine wp_addi fun t13 u13 => ?_
  refine wp_addi fun t14 u14 => ?_
  refine wp_addi fun t15 u15 => ?_
  refine wp_subi fun t16 u16 _ hz => WP.block_nil ?_
  -- The values.
  have e1 : t1.gpr .eax = ((emOf P σ).getD j 1).setWidth 32 := by
    rw [u1.gpr, ob j hjK]; simp only [Nat.lt_irrefl, ↓reduceIte]
  have a2 : t2.gpr .ebp = ((amV P σ).getD j 0).setWidth 32 := by
    rw [u2.gpr, u1.mem, ← am, Proof.RsaPkcs1Sig.bytesAt_getD hjK, Offset.add_add]
  have v5 : t5.gpr .eax = if vB P σ then ((emOf P σ).getD j 1).setWidth 32 else ((amV P σ).getD j 0).setWidth 32 := by
    rw [u5.gpr, u4.gpr, u3.gpr, u4.other _ (by decide), u3.other _ (by decide), a2, u2.other _ (by decide), e1,
      u3.mem, u2.mem, u1.mem, sv, sel2]
  have kl7 : decide ((t6.gpr .ebp).toNat < (t6.gpr .ebx).toNat) = decide (j < P.K - lselV P σ) := by
    rw [u6.gpr]
    simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]
    rw [dx, bx, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have m9 : t9.mem = s.mem := by rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have bp10 : t10.gpr .ebp = mk (!decide (j < P.K - lselV P σ) && okB P σ) := by
    rw [u10.gpr, u9.gpr, u8.gpr, sbb_mk, kl7, mk_not, m9, sok, mk_and]
  have bv : ((t11.gpr .eax).setWidth 8) = obV P σ j := by
    rw [u11.gpr, bp10, u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide),
      u7.other _ (by decide), u6.other _ (by decide), v5, selByte]
    exact (outByte_eq _ _ _ _ _ _).symm
  have mm : t16.mem = s.mem.writeW (P.out.setWidth 64 + BitVec.ofNat 64 j) (obV P σ j) := by
    rw [u16.mem, u15.mem, u14.mem, u13.mem, m12.mem, m11, show Reg8.al.reg = .eax from rfl, bv]
  have W1 : Region.Sub ⟨P.out.setWidth 64 + BitVec.ofNat 64 j, 1⟩ P.OUT := Offset.sub_base _ (by omega)
  have fr : Frame [⟨P.out.setWidth 64 + BitVec.ofNat 64 j, 1⟩] s.mem t16.mem := by
    rw [mm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) (obV P σ j) (Region.contains_self _ _)
  have st : P.lay.St σ t16 := hs.2.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.OUT, by simp, W1⟩)
    (by rw [u16.rd, u15.rd, u14.rd, u13.rd, m12.rd, u11.rd, u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd,
      u3.rd, u2.rd, u1.rd])
    (by rw [u16.wr, u15.wr, u14.wr, u13.wr, m12.wr, u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr,
      u3.wr, u2.wr, u1.wr])
    (by simp (disch := decide) only [u16.other, u15.other, u14.other, u13.other, m12.gpr, u11.other, u10.other,
      u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other])
  have one : ∀ {R : Region}, R.Disjoint P.OUT → ∀ r ∈ [(⟨P.out.setWidth 64 + BitVec.ofNat 64 j, 1⟩ : Region)],
      R.Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd.sub_right W1
  have frO : ∀ d, d + 4 ≤ frameBytes → Region.Disjoint ⟨P.lay.fr d, 4⟩ P.OUT := fun d hd =>
    hs.1.ok.stk_fr (R := P.OUT) (.inr (by simp)) (by show d + 4 ≤ frameBytes + 16; omega)
  have gg : ∀ r, r ≠ .eax → r ≠ .ebp → t12.gpr r = s.gpr r := fun r h1 h2 => by
    rw [m12.gpr]
    simp (disch := first | exact h1 | exact h2 | exact Ne.symm h1 | exact Ne.symm h2) only [u11.other,
      u10.other, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]
  have sit : t16.gpr .esi = P.out + BitVec.ofNat 32 (j + 1) := by
    rw [u16.other _ (by decide), u15.other _ (by decide), u14.other _ (by decide), u13.gpr,
      gg _ (by decide) (by decide), si, BitVec.add_assoc]
    exact congrArg (P.out + ·) (Proof.Pbkdf2.Stream.X86.ofNat_succ32 _)
  have dit : t16.gpr .edi = P.scr + BitVec.ofNat 32 (sAM + (j + 1)) := by
    rw [u16.other _ (by decide), u15.other _ (by decide), u14.gpr, u13.other _ (by decide),
      gg _ (by decide) (by decide), di, BitVec.add_assoc, ← Nat.add_assoc]
    exact congrArg (P.scr + ·) (Proof.Pbkdf2.Stream.X86.ofNat_succ32 _)
  have dxt : t16.gpr .edx = BitVec.ofNat 32 (j + 1) := by
    rw [u16.other _ (by decide), u15.gpr, u14.other _ (by decide), u13.other _ (by decide),
      gg _ (by decide) (by decide), dx]
    exact Proof.Pbkdf2.Stream.X86.ofNat_succ32 _
  have cx15 : t15.gpr .ecx = BitVec.ofNat 32 (n + 1) := by
    rw [u15.other _ (by decide), u14.other _ (by decide), u13.other _ (by decide),
      gg _ (by decide) (by decide), cx, show P.K - j = n + 1 by omega]
  have cxt : t16.gpr .ecx = BitVec.ofNat 32 n := by
    rw [u16.gpr, cx15]; exact Offset.ofNat_sub_ofNat (d := 1) (by omega)
  have obt : ∀ i < P.K, t16.mem (P.out.setWidth 64 + BitVec.ofNat 64 i) =
      if i < j + 1 then obV P σ i else (emOf P σ).getD i 1 := by
    intro i hi
    rw [mm, WriteBytes.writeW8_apply]
    by_cases e : i = j
    · subst e; simp
    · simp only [Offset.add_ofNat_ne (P.out.setWidth 64) (by omega) (by omega) e, ↓reduceIte]
      rw [ob i hi]
      simp only [show (i < j + 1) = (i < j) by apply propext; omega]
  have sl : SL P (j + 1) σ t16 :=
    ⟨⟨hs.1, st⟩, obt,
      (Proof.RsaPkcs1Sig.bytesAt_frame fr (one (hs.1.sc_out (by simp only [sAM]; omega))) (by omega)).trans am,
      by rw [slot_keep fr (one (frO oR (by decide)))]; exact rc,
      (Proof.RsaPkcs1Sig.wordsAt_frame' fr (one hs.1.out_ml.symm) (by decide)).trans ml,
      by rw [slot_keep fr (one (frO oV (by decide)))]; exact sv,
      by rw [slot_keep fr (one (frO oOK (by decide)))]; exact sok,
      sit, dit, dxt, by rw [cxt, show P.K - (j + 1) = n by omega],
      by rw [u16.other _ (by decide), u15.other _ (by decide), u14.other _ (by decide), u13.other _ (by decide),
        gg _ (by decide) (by decide), bx], hEM⟩
  refine ⟨?_, fun h0 => ?_, fun h0 => ⟨by omega, by rw [show P.K - n = j + 1 by omega]; exact sl⟩⟩
  · show eval .ne t16 = _
    rw [cx15, show BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n from
      Offset.ofNat_sub_ofNat (d := 1) (by omega), ofNat_beq_zero (by omega)] at hz
    simp only [eval, hz]
    by_cases h0 : n = 0 <;> simp [h0] <;> omega
  · rw [show P.K = j + 1 by omega]; exact sl

theorem selLoop_vp : VP (SL P 0) selLoop (SL P P.K) := by
  refine (VP.loop (I := SLM P) selBody_vp (P.K - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  have hK := h.1.1.k64
  exact ⟨by omega, by rw [show P.K - (P.K - 1 + 1) = 0 by omega]; exact h⟩

/-! ## The result -/

/-- What the shared contract states of the result `r` and the memory `m`. -/
def Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.RsaPkcs1Enc.writtenMsg m (P.out.setWidth 64) (P.ml.setWidth 64) P.K r
    (Spec.RsaPkcs1Enc.decrypt P.nB P.eB (dB P σ) (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (cB P σ))

/-- The end of the body. -/
def Fin (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .eax)

theorem amV_length (P : EP) (σ : State) : (amV P σ).length = P.K := by
  rw [amV, VG.Proof.RsaPkcs1Enc.irprf_eq, List.length_take, flatMap_blocks_length]
  omega

theorem res_of {σ : State} {m : Mem} (hin : In P σ) (hEM : (emOf P σ).length = P.K)
    (hout : ∀ i < P.K, m (P.out.setWidth 64 + BitVec.ofNat 64 i) = obV P σ i)
    (hml : Spec.Rsa.wordsAt m (P.ml.setWidth 64) 1 = [BitVec.ofNat 64 (if okB P σ then lselV P σ else 0)]) :
    Res P σ m (rcOf P σ) := by
  have hK := hin.k64
  have hn : P.nB.length = P.K := by rw [← hin.nB, Proof.RsaPkcs1Sig.bytesAt_len]
  have hC : (cB P σ).length = P.K := Proof.RsaPkcs1Sig.bytesAt_len _ _ _
  have hb : Spec.Rsa.bytesAt m (P.out.setWidth 64) P.K = (List.range P.K).map (obV P σ) :=
    List.map_congr_left fun i hi => hout i (List.mem_range.mp hi)
  unfold Res Spec.RsaPkcs1Enc.decrypt
  rw [hn]
  cases ho : privO P σ with
  | ok EM =>
    have e1 : emOf P σ = EM := by simp only [emOf, ho]
    have r1 : rcOf P σ = 1 := by simp only [rcOf, ho]
    have ok1 : okB P σ = true := by simp only [okB, r1]; rfl
    have hEM' : EM.length = P.K := e1 ▸ hEM
    rw [VG.Proof.RsaPkcs1Enc.decryptWith_of_ok hC (by omega) ho]
    obtain ⟨hl, hm⟩ := VG.Proof.RsaPkcs1Enc.sel_eq (EM := EM) (AM := amV P σ) (al := alV P σ) hEM'
      (amV_length P σ) (by omega) (alV_le P σ)
    have hM : Spec.RsaPkcs1Enc.implicitDecode (dB P σ) (cB P σ) EM =
        (if Spec.RsaPkcs1Enc.valid EM then Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.msgLength EM) EM
          else Spec.RsaPkcs1Enc.lastN (alV P σ) (amV P σ)) := by
      simp only [Spec.RsaPkcs1Enc.implicitDecode, Spec.RsaPkcs1Enc.alternative, hEM']
    rw [hM]
    refine ⟨r1, ?_, ?_⟩
    · rw [hb, ← hm]
      refine List.map_congr_left fun i _ => ?_
      simp only [obV, vB, lselV, sepV, fz, e1, ok1]
    · rw [hml, ok1, ← hl]
      simp only [lselV, vB, sepV, fz, e1, ↓reduceIte]
  | invalid =>
    have r0 : rcOf P σ = 0 := by simp only [rcOf, ho]
    have ok0 : okB P σ = false := by simp only [okB, r0]; rfl
    rw [VG.Proof.RsaPkcs1Enc.decryptWith_of_invalid (C := cB P σ)
      (rsadp := fun C => Spec.Rsa.privateChecked P.nB P.eB C (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ)) ho]
    refine ⟨r0, ?_, by rw [hml, ok0]; rfl⟩
    have z : ∀ i, obV P σ i = 0 := fun i => by
      simp only [obV, ok0]; exact VG.Proof.RsaPkcs1Enc.outByte_false _ _ _ _ _
    rw [hb, List.map_congr_left (g := fun _ => (0 : Byte)) fun i _ => z i, List.map_const', List.length_range]
  | fault =>
    have r2 : rcOf P σ = 2 := by simp only [rcOf, ho]
    have ok0 : okB P σ = false := by simp only [okB, r2]; rfl
    rw [VG.Proof.RsaPkcs1Enc.decryptWith_of_fault hC (by omega) ho]
    refine ⟨r2, ?_, by rw [hml, ok0]; rfl⟩
    have z : ∀ i, obV P σ i = 0 := fun i => by
      simp only [obV, ok0]; exact VG.Proof.RsaPkcs1Enc.outByte_false _ _ _ _ _
    rw [hb, List.map_congr_left (g := fun _ => (0 : Byte)) fun i _ => z i, List.map_const', List.length_range]

theorem finR_vp : VP (SL P P.K) (.block fin) (Fin P) :=
  VP.taint [.esp] fin_taint (sp_agree fun _ _ h => h.1) fun σ s h => by
    obtain ⟨hs, ob, -, rc, ml, -, -, -, -, -, -, -, hEM⟩ := h
    refine hs.2.wp_slot (d := oR) (by show oR + 4 ≤ frameBytes; decide) (r := .eax) (by decide)
      fun t1 st1 u1 => WP.block_nil ⟨⟨hs.1, st1⟩, ?_⟩
    rw [u1.gpr, rc, u1.mem]
    exact res_of hs.1 hEM (fun i hi => by rw [ob i hi]; simp [hi]) ml

end VG.Proof.RsaPkcs1Enc.X86.Dec
