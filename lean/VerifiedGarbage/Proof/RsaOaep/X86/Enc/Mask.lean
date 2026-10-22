module

public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Em
public import VerifiedGarbage.Proof.RsaOaep.X86.MgfSlots
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP encryption with a precomputed public key on x86: `EM` masked

As on ARMv7 (`Proof/RsaOaep/Arm/EncMask.lean`): `DB` (after the seed)
masked with MGF1 of the seed, then the seed with MGF1 of the masked `DB`
(`mgf_vp`, with the slots that `dbArgs` and `seedArgs` set, `MgfSlots.lean`):
`EM = Proof.RsaOaep.emOf …` (`mask_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Enc

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm arg ld st mi atS addi sCtr sDone)

variable (h g : OHash)

/-! ## The pieces -/

/-- `DB` before masking. -/
abbrev dbB (P : EP) (σ : State) : List Byte :=
  lhB h P σ ++ Spec.RsaOaep.zeros (P.K - P.ml - 2 * h.H.D - 2) ++ 0x01 :: msgB P σ

/-- `DB` masked. -/
abbrev mdbB (P : EP) (σ : State) : List Byte :=
  Spec.Mgf1.xorBytes (dbB h P σ) (Spec.Mgf1.mgf1 g.G (seedB h P σ) (P.K - h.H.D - 1))

/-- What the masking keeps: `EM`'s first byte, zero. -/
abbrev X0 (P : EP) (σ : State) (m : Mem) : Prop := K0 h P σ ∧ emV P.scr m 0 = 0

theorem lhB_length (P : EP) (σ : State) : (lhB h P σ).length = h.H.D := by
  rw [lhB, h.valid.2, h.glen]

theorem seedB_length (P : EP) (σ : State) : (seedB h P σ).length = h.H.D := RsaPkcs1Sig.bytesAt_len _ _ _

theorem dbB_length {P : EP} (hf : fits h P) (σ : State) : (dbB h P σ).length = P.K - h.H.D - 1 := by
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  simp only [dbB, List.length_append, List.length_cons, lhB_length, msgB_length, Spec.RsaOaep.zeros,
    List.length_replicate]
  omega

theorem mdbB_length {P : EP} (hf : fits h P) (σ : State) : (mdbB h g P σ).length = P.K - h.H.D - 1 := by
  rw [mdbB, Proof.Mgf1.xorBytes_length, dbB_length h hf, Proof.Mgf1.mgf1_length g.valid]; omega

theorem x0_keep {P : EP} (hg : Geo (P.lay h.H.D) P.scr) {dOff dl : Nat} (hfd : dOff + dl ≤ oBuf)
    (h0 : oEm + 1 ≤ dOff) :
    ∀ σ m m', X0 h P σ m → Frame (mgfW g (P.lay h.H.D) P.scr dOff dl) m m' → X0 h P σ m' :=
  fun _ _ _ ⟨k, z⟩ hf => ⟨k, by
    rw [emV, ← z]
    exact hf _ fun r hr => mgfW_byte g hg hfd (o := oEm + 0) (by oomega) (by oomega) (by omega) r hr _
      (Region.contains_self _ _)⟩

/-- Four slots written, and the memory around them. -/
theorem slots4 {P : EP} {σ s t : State} (hc : Ctx (P.lay h.H.D) P.scr σ s) (hg : Geo (P.lay h.H.D) P.scr)
    {v1 v2 v3 v4 : BitVec 32}
    (m : t.mem = (((s.mem.writeW ((P.lay h.H.D).fr sDst) v1).writeW ((P.lay h.H.D).fr sDstLen) v2).writeW
      ((P.lay h.H.D).fr sSrc) v3).writeW ((P.lay h.H.D).fr sSrcLen) v4)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.gpr .esp = s.gpr .esp) (bp : t.gpr .ebp = s.gpr .ebp) :
    Ctx (P.lay h.H.D) P.scr σ t ∧
      Frame [slotR (P.lay h.H.D) sDst, slotR (P.lay h.H.D) sDstLen, slotR (P.lay h.H.D) sSrc,
        slotR (P.lay h.H.D) sSrcLen] s.mem t.mem ∧
      t.mem.readW ((P.lay h.H.D).fr sSrc) 32 = v3 ∧ t.mem.readW ((P.lay h.H.D).fr sSrcLen) 32 = v4 ∧
      t.mem.readW ((P.lay h.H.D).fr sDst) 32 = v1 ∧ t.mem.readW ((P.lay h.H.D).fr sDstLen) 32 = v2 := by
  have fr : Frame [slotR (P.lay h.H.D) sDst, slotR (P.lay h.H.D) sDstLen, slotR (P.lay h.H.D) sSrc,
      slotR (P.lay h.H.D) sSrcLen] s.mem t.mem := by
    rw [m]
    exact (((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp)) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  refine ⟨hc.write fr (fun r hr => ?_) rd wr sp bp, fr, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotW hg (by decide)
  · rw [m, Lay.readW_fr_other (d := sSrc) (e := sSrcLen) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, Lay.readW_fr_other (d := sDst) (e := sSrcLen) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sDst) (e := sSrc) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sDst) (e := sDstLen) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, Lay.readW_fr_other (d := sDstLen) (e := sSrcLen) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sDstLen) (e := sSrc) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]

/-- The slots' frame misses our part of `scratch`. -/
theorem slots4_dis {P : EP} (hg : Geo (P.lay h.H.D) P.scr) :
    ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR (P.lay h.H.D) sDst, slotR (P.lay h.H.D) sDstLen,
      slotR (P.lay h.H.D) sSrc, slotR (P.lay h.H.D) sSrcLen], (sR P.scr o n).Disjoint r := by
  obtain ⟨σ', ok⟩ := hg.ok
  intro o n hon r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm

/-- The slots for masking `DB` with the seed. -/
theorem db_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ Proof.RsaOaep.EmAt (emV P.scr s.mem) P.K h.H.D (seedB h P σ) (lhB h P σ)
        (msgB P σ) P.ml)
      (.block (dbArgs h.H 3))
      (fun σ s => Ctx (P.lay h.H.D) P.scr σ s ∧
        (X0 h P σ s.mem ∧ Sl (P.lay h.H.D) P.scr (oEm + 1) h.H.D (oEm + 1 + h.H.D) (P.K - h.H.D - 1) s.mem) ∧
        (∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) = (dbB h P σ).getD i 0) ∧
        ∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = (seedB h P σ).getD i 0) := by
  refine VP.taint [.esp, .ebp] h.certs.dbArgs3 (sp_bp fun _ _ h => h.1.1) fun σ s ⟨⟨hc, hi, hf⟩, em⟩ => ?_
  have hg := hi.geo
  have hK := hi.k1024
  have hD := h.D_le
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  simp only [dbArgs, atS, addi, ld, st, mi, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  refine ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).wp_st hg (by decide) fun t3 c3 m3 => ?_
  refine c3.wp_arg hg (enc_arg (j := 3) (by decide)) (by decide) (by decide) fun t4 c4 u4 => ?_
  refine wp_subi fun t5 u5 _ _ => (c4.upd u5 (by decide) (by decide)).wp_st hg (by decide) fun t6 c6 m6 => ?_
  refine wp_mov fun t7 u7 => wp_addi fun t8 u8 => ?_
  refine ((c6.upd u7 (by decide) (by decide)).upd u8 (by decide) (by decide)).wp_st hg (by decide) fun t9 c9 m9 => ?_
  refine wp_movi fun t10 u10 => (c9.upd u10 (by decide) (by decide)).wp_st hg (by decide) fun t11 c11 m11 =>
    WP.block_nil ?_
  have e2 : t2.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) := by rw [u2.gpr, u1.gpr, hc.ebp]
  have e5 : t5.gpr .eax = BitVec.ofNat 32 (P.K - h.H.D - 1) := by
    rw [u5.gpr, u4.gpr]; show BitVec.ofNat 32 P.K - BitVec.ofNat 32 (h.H.D + 1) = _
    rw [sub_ofNat (by omega), Nat.sub_add_eq]
  have e8 : t8.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + 1) := by
    rw [u8.gpr, u7.gpr, m6.gpr, u5.other _ (by decide), u4.other _ (by decide), m3.gpr, u2.other _ (by decide),
      u1.other _ (by decide), hc.ebp]
  have m11 : t11.mem = (((s.mem.writeW ((P.lay h.H.D).fr sDst) (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D))).writeW
      ((P.lay h.H.D).fr sDstLen) (BitVec.ofNat 32 (P.K - h.H.D - 1))).writeW ((P.lay h.H.D).fr sSrc)
        (P.scr + BitVec.ofNat 32 (oEm + 1))).writeW ((P.lay h.H.D).fr sSrcLen) (BitVec.ofNat 32 h.H.D) := by
    rw [m11.mem, u10.gpr, u10.mem, m9.mem, e8, u8.mem, u7.mem, m6.mem, e5, u5.mem, u4.mem, m3.mem, e2, u2.mem, u1.mem]
  obtain ⟨c, fr, r1, r2, r3, r4⟩ := slots4 h hc hg m11 (by rw [c11.st.rd, hc.st.rd]) (by rw [c11.st.wr, hc.st.wr])
    (by rw [c11.st.sp, hc.st.sp]) (by rw [c11.ebp, hc.ebp])
  have dis := slots4_dis h hg
  have db := em.db (lhB_length h P σ) (msgB_length P σ) hfit
  refine ⟨c, ⟨⟨⟨hi, hf⟩, ?_⟩, r1, r2, r3, r4⟩, fun i hi' => ?_, fun i hi' => ?_⟩
  · rw [emV, ← em.z0]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) (o := oEm) (n := 1) (f := fun _ => s.mem (sa P.scr oEm))
      (fun i hi => by rw [show i = 0 by omega, Nat.add_zero]) 0 (by decide)
  · rw [← db i hi', emV, show oEm + (1 + h.H.D + i) = oEm + 1 + h.H.D + i by oomega]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) (o := oEm + 1 + h.H.D) (n := P.K - h.H.D - 1)
      (f := fun i => s.mem (sa P.scr (oEm + 1 + h.H.D + i))) (fun _ _ => rfl) i hi'
  · rw [← em.sd i hi', emV, show oEm + (1 + i) = oEm + 1 + i by oomega]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) (o := oEm + 1) (n := h.H.D)
      (f := fun i => s.mem (sa P.scr (oEm + 1 + i))) (fun _ _ => rfl) i hi'

/-- The slots for masking the seed with the masked `DB`. -/
theorem seed_vp (P : EP) :
    VP (fun σ s => Ctx (P.lay h.H.D) P.scr σ s ∧
        (X0 h P σ s.mem ∧ Sl (P.lay h.H.D) P.scr (oEm + 1) h.H.D (oEm + 1 + h.H.D) (P.K - h.H.D - 1) s.mem) ∧
        (∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) =
          (dbB h P σ).getD i 0 ^^^ (Spec.Mgf1.mgf1 g.G (seedB h P σ) (P.K - h.H.D - 1)).getD i 0) ∧
        ∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = (seedB h P σ).getD i 0)
      (.block (seedArgs h.H 3))
      (fun σ s => Ctx (P.lay h.H.D) P.scr σ s ∧
        (X0 h P σ s.mem ∧ Sl (P.lay h.H.D) P.scr (oEm + 1 + h.H.D) (P.K - h.H.D - 1) (oEm + 1) h.H.D s.mem) ∧
        (∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = (seedB h P σ).getD i 0) ∧
        ∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) = (mdbB h g P σ).getD i 0) := by
  refine VP.taint [.esp, .ebp] h.certs.seedArgs3 (sp_bp fun _ _ h => h.1)
    fun σ s ⟨hc, ⟨⟨⟨hi, hf⟩, z0⟩, _⟩, hdb, hsd⟩ => ?_
  have hg := hi.geo
  have hK := hi.k1024
  have hD := h.D_le
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  simp only [seedArgs, atS, addi, ld, st, mi, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  refine ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).wp_st hg (by decide) fun t3 c3 m3 => ?_
  refine wp_movi fun t4 u4 => (c3.upd u4 (by decide) (by decide)).wp_st hg (by decide) fun t5 c5 m5 => ?_
  refine wp_mov fun t6 u6 => wp_addi fun t7 u7 => ?_
  refine ((c5.upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)).wp_st hg (by decide) fun t8 c8 m8 => ?_
  refine c8.wp_arg hg (enc_arg (j := 3) (by decide)) (by decide) (by decide) fun t9 c9 u9 => ?_
  refine wp_subi fun t10 u10 _ _ => (c9.upd u10 (by decide) (by decide)).wp_st hg (by decide) fun t11 c11 m11 =>
    WP.block_nil ?_
  have e2 : t2.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + 1) := by rw [u2.gpr, u1.gpr, hc.ebp]
  have e7 : t7.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) := by
    rw [u7.gpr, u6.gpr, m5.gpr, u4.other _ (by decide), m3.gpr, u2.other _ (by decide), u1.other _ (by decide),
      hc.ebp]
  have e10 : t10.gpr .eax = BitVec.ofNat 32 (P.K - h.H.D - 1) := by
    rw [u10.gpr, u9.gpr]; show BitVec.ofNat 32 P.K - BitVec.ofNat 32 (h.H.D + 1) = _
    rw [sub_ofNat (by omega), Nat.sub_add_eq]
  have m11 : t11.mem = (((s.mem.writeW ((P.lay h.H.D).fr sDst) (P.scr + BitVec.ofNat 32 (oEm + 1))).writeW
      ((P.lay h.H.D).fr sDstLen) (BitVec.ofNat 32 h.H.D)).writeW ((P.lay h.H.D).fr sSrc)
        (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D))).writeW ((P.lay h.H.D).fr sSrcLen)
          (BitVec.ofNat 32 (P.K - h.H.D - 1)) := by
    rw [m11.mem, e10, u10.mem, u9.mem, m8.mem, e7, u7.mem, u6.mem, m5.mem, u4.gpr, u4.mem, m3.mem, e2, u2.mem, u1.mem]
  obtain ⟨c, fr, r1, r2, r3, r4⟩ := slots4 h hc hg m11 (by rw [c11.st.rd, hc.st.rd]) (by rw [c11.st.wr, hc.st.wr])
    (by rw [c11.st.sp, hc.st.sp]) (by rw [c11.ebp, hc.ebp])
  have dis := slots4_dis h hg
  have hdl := dbB_length h hf σ
  have hml := Proof.Mgf1.mgf1_length g.valid (seedB h P σ) (P.K - h.H.D - 1)
  refine ⟨c, ⟨⟨⟨hi, hf⟩, ?_⟩, r1, r2, r3, r4⟩, sbytes_keep fr (dis _ _ (by oomega)) (by oomega) hsd, fun i hi' => ?_⟩
  · rw [emV, ← z0]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) (o := oEm) (n := 1) (f := fun _ => s.mem (sa P.scr oEm))
      (fun i hi => by rw [show i = 0 by omega, Nat.add_zero]) 0 (by decide)
  · rw [mdbB, Proof.Mgf1.xorBytes_getD (by omega) (by omega)]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) hdb i hi'

/-! ## `EM` masked -/

/-- `EM` masked, as the specification has it. -/
abbrev emB (P : EP) (σ : State) : List Byte :=
  Proof.RsaOaep.emOf g.G h.H.D P.K P.ml (seedB h P σ) (lhB h P σ) (msgB P σ)

/-- A state of the body with `EM` masked at `scratch + oEm`. -/
abbrev E1 (P : EP) (σ s : State) : Prop :=
  E0 h P σ s ∧ ∀ i < P.K, emV P.scr s.mem i = (emB h g P σ).getD i 0

/-- `EM` masked, byte by byte. -/
theorem emB_getD {P : EP} (hf : fits h P) (σ : State) {i : Nat} (hi : i < P.K) :
    (emB h g P σ).getD i 0 = if i = 0 then 0 else if i < 1 + h.H.D then
      (seedB h P σ).getD (i - 1) 0 ^^^ (Spec.Mgf1.mgf1 g.G (mdbB h g P σ) h.H.D).getD (i - 1) 0
      else (mdbB h g P σ).getD (i - 1 - h.H.D) 0 := by
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  have hsl := seedB_length h P σ
  have hml := Proof.Mgf1.mgf1_length g.valid (mdbB h g P σ) h.H.D
  show (0 :: (Spec.Mgf1.xorBytes (seedB h P σ) (Spec.Mgf1.mgf1 g.G (mdbB h g P σ) h.H.D) ++ mdbB h g P σ)).getD i 0 = _
  cases i with
  | zero => rfl
  | succ i =>
    rw [List.getD_cons_succ, ite_eq_right (by omega), Proof.Mgf1.getD_append, Proof.Mgf1.xorBytes_length, hsl, hml,
      Nat.min_self, Nat.add_sub_cancel]
    by_cases h1 : i < h.H.D
    · rw [ite_eq_left h1, ite_eq_left (by omega), Proof.Mgf1.xorBytes_getD (by omega) (by omega)]
    · rw [ite_eq_right h1, ite_eq_right (by omega)]

/-- `EM` masked, from `EM` before masking, then `k`. -/
theorem mask_vp (P : EP) {c : Prog isa} {Q : State → State → Prop} (k : VP (E1 h g P) c Q) :
    VP (fun σ s => E0 h P σ s ∧ Proof.RsaOaep.EmAt (emV P.scr s.mem) P.K h.H.D (seedB h P σ) (lhB h P σ)
        (msgB P σ) P.ml)
      (.seq (.block (dbArgs h.H 3)) (.seq (mgfXor g.H) (.seq (.block (seedArgs h.H 3)) (.seq (mgfXor g.H) c))))
      Q := by
  by_cases hP : ∃ σ, In h.H.D P σ ∧ fits h P
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1, hs.1.2.2⟩
  obtain ⟨σ₀, hi₀, hf⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  have P1 := mpOf g hg (so := oEm + 1) (sl := h.H.D) (dOff := oEm + 1 + h.H.D) (dl := P.K - h.H.D - 1) hD0
    (by omega) (by oomega) (by oomega) (by oomega) (by oomega) (.inl (Nat.le_refl _)) (seed := seedB h P)
    (seedB_length h P) (x0_keep h g hg (by oomega) (by oomega))
  have P2 := mpOf g hg (so := oEm + 1 + h.H.D) (sl := P.K - h.H.D - 1) (dOff := oEm + 1) (dl := h.H.D)
    (by omega) hD0 (by oomega) (by oomega) (by oomega) (by oomega) (.inr (Nat.le_refl _)) (seed := mdbB h g P)
    (mdbB_length h g hf) (x0_keep h g hg (by oomega) (by oomega))
  refine VP.seq (db_vp h P) (VP.seq (mgf_vp g P1 (dstv := fun σ i => (dbB h P σ).getD i 0))
    (VP.seq (seed_vp h g P) (VP.seq ((mgf_vp g P2 (dstv := fun σ i => (seedB h P σ).getD i 0)).mono
      (fun _ _ hh => hh) fun σ s ⟨hc, ⟨⟨⟨hi, _⟩, z0⟩, _⟩, hsd, hdb⟩ => ⟨⟨hc, hi, hf⟩, fun i hi' => ?_⟩) k)))
  rw [emB_getD h g hf σ hi']
  by_cases h0 : i = 0
  · rw [ite_eq_left h0, h0]; exact z0
  rw [ite_eq_right h0]
  by_cases h1 : i < 1 + h.H.D
  · rw [ite_eq_left h1, emV, show oEm + i = oEm + 1 + (i - 1) by oomega]
    exact hsd _ (by omega)
  · rw [ite_eq_right h1, emV, show oEm + i = oEm + 1 + h.H.D + (i - 1 - h.H.D) by oomega]
    exact hdb _ (by omega)

end VG.Proof.RsaOaep.X86.Enc
