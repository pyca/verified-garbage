module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfShift
public import VerifiedGarbage.Proof.RsaPss.Arm.VfY
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: a salt of any length

`M' = 0⁸ ‖ mHash ‖` the bytes of `DB` after its first nonzero byte (`Ma`):
`DB` copied after `mHash` and shifted into place, hashed over the blocks of
the longest salt, and compared with `H` (`any_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- `M'`. -/
abbrev Ma (P : EP) (τ : State) : List Byte :=
  Spec.RsaPss.zeros 8 ++ digB h P τ ++ (dbL h P τ).drop (pzF h P τ + 1)

/-- Its blocks, those of the longest salt. -/
abbrev nbA (P : EP) : Nat := (dbN h P + (7 + h.D + h.L)) / h.B + 1

theorem pre_length (P : EP) (τ : State) : (Spec.RsaPss.zeros 8 ++ digB h P τ).length = 8 + h.D := by
  simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.Arm.bytesAt_length]

theorem dbL_length (P : EP) (τ : State) : (dbL h P τ).length = dbN h P := by simp [dbL]

theorem Ma_length (P : EP) (τ : State) : (Ma h P τ).length = 8 + h.D + (dbN h P - (pzF h P τ + 1)) := by
  rw [Ma, List.length_append, pre_length, List.length_drop, dbL_length]

theorem Ma_getD {P : EP} {τ : State} {j : Nat} :
    (Ma h P τ).getD (8 + h.D + j) 0 = Dp h P τ (j + aV h P τ) := by
  rw [Ma, RsaPss.getD_app, pre_length, ite_eq_right (by omega_arith), Nat.add_sub_cancel_left]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [← List.getD_eq_getElem?_getD]
  unfold Dp aV
  by_cases e : j + (pzF h P τ + 1) < dbN h P
  · rw [ite_eq_left e, Nat.add_comm, ← dbL_getD h e]
  · rw [ite_eq_right e, getD_ge (by rw [dbL_length]; omega_arith)]

/-- `DB` after `mHash`. -/
theorem cpDb_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ True) ∧ Y1 h P τ s.mem)
      (.seq (.block (cpDb h.H)) Impl.Bignum.Arm.copyBytes)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ j) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hi₀ hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  refine VP.seq (G := fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ True) ∧ Y1 h P τ s.mem) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧ s.gpr .r1 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧
      s.gpr .lr = BitVec.ofNat 32 (dbN h P))
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hy⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oY + 8 + h.D) (n := dbN h P) (by omega_arith) (by omega_arith))
      (hg.rbuf (o := oEm + lo P) (n := dbN h P) (by omega_arith) (by omega_arith))
      (by rw [hg.addr (by omega_arith), hg.addr (by omega_arith)]; exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
      (f := fun τ i => dbF h P τ i)
      (Inv := fun τ m => Kq h P τ m ∧ ∀ j, dbN h P ≤ j → j < 2040 - h.D → m (sa P.scr (oY + 8 + h.D + j)) = 0)
      fun τ m m' ⟨hk, hz⟩ hf' => ?_).mono
      (fun τ s ⟨⟨hc, ⟨hk, _⟩, hy⟩, r0, r1, lr⟩ => ⟨hc, ⟨⟨hk, fun i hi => hy i (by omega_arith)⟩, fun j hj hj' => ?_⟩, r0, r1, lr, fun i hi => ?_⟩)
      fun τ s ⟨hc, ⟨hk, hz⟩, hs⟩ => ⟨hc, hk, fun j hj => ?_⟩)
  · have hw : WP isa (.block (cpDb h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧ t.gpr .r1 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧
        t.gpr .lr = BitVec.ofNat 32 (dbN h P) := by
      prun [cpDb, atS, atDb, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hk.1.2.2.1.2.1,
        hk.1.2.2.1.2.2.1, movw_val (show oY + 8 + dig h.H < 2 ^ 16 by show oY + 8 + h.D < 2 ^ 16; omega_arith),
        movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ hy⟩, r0, r1, lr⟩
  · rw [hg.addr (by omega_arith)] at hf'
    refine ⟨⟨K2.keep h hk.1 hf' fun r hr => ?_, sbytes_keep hf' (fun r hr => ?_) (by omega_arith) hk.2⟩,
      fun j hj hj' => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by omega_arith) (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)
    · rw [← hz j hj hj']
      exact hf' _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oY + 8 + h.D + j) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _
          (Region.contains_self _ _)
  · rw [show oY + 8 + h.D + j = oY + (8 + h.D + j) by omega_arith, hy _ (by omega_arith)]
    exact getD_ge (by rw [pre_length]; omega_arith)
  · rw [hg.byteAt_scr (by omega_arith), show oEm + lo P + i = oEm + lo P + i from rfl]; exact hk.2.2.2.1 i hi
  · unfold Dp
    by_cases e : j < dbN h P
    · rw [ite_eq_left e, ← hs j e, hg.byteAt_scr (by omega_arith)]
    · rw [ite_eq_right e]; exact hz j (by omega_arith) hj

/-- `M'`'s length and blocks. -/
theorem anyLen_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ (j + aV h P τ)) (.block (anyLen h.H))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kt h P (Ma h P) (nbA h P) τ s.mem ∧
        ∀ i < 2048, s.mem (sa P.scr (oY + i)) = (Ma h P τ).getD i 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hy⟩ => ?_
  have hi := hk.1.1
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hi hk.1.2.1
  have hpz := pzF_lt h (τ := τ) hdb
  have hL := h.L_le
  have hB := h.B_ge
  have e3 : oY = 2048 := rfl
  have e1 : BitVec.ofNat 32 (dbN h P + (7 + h.D + h.L)) >>> lgB h.H =
      BitVec.ofNat 32 ((dbN h P + (7 + h.D + h.L)) / h.B) := by
    rw [VG.Proof.MdStream.Arm.ofNat_shr (by omega_arith), h.pow_lg]
  have w1 : ∀ v, (s.mem.writeW ((P.lay h.D).fr sL) v).readW ((P.lay h.D).fr sDb) 32 = BitVec.ofNat 32 (dbN h P) :=
    fun v => by rw [slot_ww _ _ (by decide) (by decide) (by decide)]; exact hk.1.2.2.1.2.2.1
  have es : BitVec.ofNat 32 (dbN h P) - BitVec.ofNat 32 (pzF h P τ) = BitVec.ofNat 32 (dbN h P - pzF h P τ) :=
    Offset.ofNat_sub_ofNat (w := 32) (by omega_arith)
  have hw : WP isa (.block (anyLen h.H)) s fun t =>
      t.mem = (s.mem.writeW ((P.lay h.D).fr sL) (BitVec.ofNat 32 (dbN h P - pzF h P τ + (7 + h.D)))).writeW
        ((P.lay h.D).fr sNb) (BitVec.ofNat 32 (nbA h P)) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [anyLen, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hk.1.2.2.1.2.2.1, hk.1.2.2.2.2.2.1, w1, es,
      slotAt hi (d := sL) (by decide), slotAt hi (d := sNb) (by decide),
      hc.st.inFr (d := sL) (n := 4) (by show sL + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sNb) (n := 4) (by show sNb + 4 ≤ frameBytes; decide),
      movw_val (show 7 + dig h.H < 2 ^ 16 by show 7 + h.D < 2 ^ 16; omega_arith),
      movw_val (show 7 + dig h.H + lenL h.H < 2 ^ 16 by show 7 + h.D + h.L < 2 ^ 16; omega_arith),
      BitVec.ofNat_add_ofNat, e1, h.lg_range, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr : Frame [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb] s.mem t.mem := by
    rw [m]
    exact (slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  obtain ⟨σ', ok⟩ := hg.ok
  have aw : ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb],
      Region.Disjoint (sR P.scr o n) r := fun o n hon r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  have e2 : oRsa = 8192 := rfl
  have hy' := sbytes_keep fr (aw _ _ (by omega_arith)) (by omega_arith) hy
  have hp' := sbytes_keep fr (aw _ _ (by omega_arith)) (by omega_arith) hk.2
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨K2.keep h hk.1 fr fun r hr => ?_, ?_, ?_⟩,
    fun i hi' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact away2_slot hg (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, Ma_length]
    congr 1; omega_arith
  · rw [m, Mem.readW_writeW_self32]
  · by_cases e : i < 8 + h.D
    · rw [hp' i e, Ma, RsaPss.getD_app (l := Spec.RsaPss.zeros 8 ++ digB h P τ), pre_length, ite_eq_left e]
    · have := hy' (i - (8 + h.D)) (by omega_arith)
      rw [show oY + 8 + h.D + (i - (8 + h.D)) = oY + i by omega_arith] at this
      rw [this, show i = 8 + h.D + (i - (8 + h.D)) by omega_arith, Ma_getD]
      congr 1; omega_arith

/-- A salt of any length. -/
theorem any_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧ True) (anyPath h.H)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧
        s.gpr .r0 = if acc2 h P τ = 0 ∧ HOk h P τ (Ma h P τ) then 1 else 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.2.1
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have hL := h.L_le
  have hB := h.B_le
  have hB0 : 0 < h.B := by have := h.B_ge; omega_arith
  obtain ⟨hlo, hdb, hdD, hD', hD0⟩ := shB h hi₀ hf
  have q1 := Nat.lt_mul_div_succ (dbN h P + (7 + h.D + h.L)) hB0
  have q2 := Nat.mul_div_le (dbN h P + (7 + h.D + h.L)) h.B
  have hT : nbA h P * h.B ≤ 2048 := by
    show ((dbN h P + (7 + h.D + h.L)) / h.B + 1) * h.B ≤ 2048
    rw [Nat.succ_mul, Nat.mul_comm]; omega_arith
  show VP _ (.seq (yDig h.H 4) (.seq (.block (cpDb h.H)) (.seq Impl.Bignum.Arm.copyBytes (.seq (shift h.H)
    (.seq (.block (anyLen h.H)) (.seq (ctHash h.H) (cmpH h.H))))))) _
  refine (yDig_vf h P ⟨σ₀, hi₀⟩ True).seq (VP.assoc ((cpDb_vp h P ⟨σ₀, hi₀⟩).seq ((shift_vp h P ⟨σ₀, hi₀⟩).seq
    ((anyLen_vp h P ⟨σ₀, hi₀⟩).seq ?_))))
  exact (tail_vp h P ⟨σ₀, hi₀⟩ hT (Nat.succ_pos _) (msg := Ma h P) fun τ => by
      rw [Ma_length]; show _ ≤ ((dbN h P + (7 + h.D + h.L)) / h.B + 1) * h.B; rw [Nat.mul_comm]; omega_arith).mono
    (fun τ s ⟨hc, hk, hy⟩ => ⟨hc, hk, fun i hi => hy i (by omega_arith)⟩) fun τ s ⟨hc, hk, r0⟩ => ⟨hc, hk, r0⟩

end VG.Proof.RsaPss.Arm.Vf
