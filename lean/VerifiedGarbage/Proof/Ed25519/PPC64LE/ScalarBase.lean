module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointScalar
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Encode
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Comb
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.BaseContract
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarMulAdd
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.ScalarBase
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Field
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Layout
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# `vg_ed25519_scalar_base` on PPC64LE: correctness

The function saves the nonvolatile registers it uses and the link register
in `scratch`, multiplies the base point by the 256-bit scalar with the comb
(`combMultiply_ok`), which reads the static `combSym`, encodes the product at
`FR` (`pointEncode_ok`), and copies it to `out`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (decodeLE bytesAt)

section
variable {b : Addr}

/-- The registers the engine writes. -/
abbrev baseR : List Reg := .r7 :: .r8 :: .r9 :: stepR

theorem scalarBaseEngine_ok {s : State} (hc : Ctx8 b s) {p T : Addr} (h14 : s.gpr .r14 = p)
    (hin : ∀ i < 32, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hpd : (⟨p, 32⟩ : Region).Disjoint ⟨b, 8192⟩) (hT : TblAt s T) (hsym : s.syms combSym = T)
    (apart : (TBL T).Disjoint ⟨b, 8192⟩) :
    WP isa scalarBaseEngine s fun t =>
      Rest baseR s t ∧ Frame (combW b) s.mem t.mem ∧
      Spec.Ed25519.encodeLE 32 (V t.mem b FR) = Spec.Ed25519.scalarBase (bytesAt s.mem p 32) := by
  unfold scalarBaseEngine
  refine WP.seq (WP.mono_syms (initFields_ok hc.ctx) fun s1 ⟨r1, f1⟩ sy1 => ?_)
  have hc1 : Ctx8 b s1 := hc.of_rest r1 (by decide)
  have hb1 : bytesAt s1.mem p 32 = bytesAt s.mem p 32 := by
    simp only [Spec.Ed25519.bytesAt, List.map_inj_left]
    intro i hi
    exact bytes_ws f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_arith)) hpd
      (by decide) (List.mem_range.mp hi)
  have hT1 : TblAt s1 T := hT.of_frame (by rw [r1.rd, r1.wr]) f1 fun r hr => by
    rw [List.mem_singleton.mp hr]; exact apart.sub_right (Offset.sub_base _ (by decide))
  refine WP.seq (WP.mono_syms (combMultiply_ok hc1 (by rw [r1.gpr _ (by decide), h14])
    (fun i hi => by rw [r1.rd, r1.wr]; exact hin i hi) hpd hT1 (by rw [sy1, hsym]) apart)
    fun s3 ⟨r3, f3, p3⟩ _ => ?_)
  rw [hb1] at p3
  have hc3 : Ctx8 b s3 := hc1.of_rest r3 (by decide)
  refine WP.mono (pointEncode_ok hc3) fun t ⟨rt, ft, vt⟩ => ⟨?_, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((r3.mono (by decide)).trans (rt.mono (by decide)))
  · exact (f1.mono (by simp)).trans (f3.trans (ft.mono (by simp)))
  · rw [vt, ← encodePoint_eq, encodePoint_rep p3, Spec.Ed25519.scalarBase,
      encodePoint_rep (pointMul_rep _ basePoint_rep)]

/-- What the engine writes misses the saved registers' slots. -/
theorem combW_saves (lo n : Nat) (h1 : 1024 ≤ lo) (h2 : lo + n ≤ 1152) :
    ∀ r ∈ combW b, Region.Disjoint ⟨b + BitVec.ofNat 64 lo, n⟩ r := by
  intro r hr
  have hS : SCAL = 1152 := rfl
  have hG : SGN = 56 := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)

/-- What an engine between `scalarBaseSetup` and `scalarBaseFinish` does, as the comb's: from the
working space at `b` and the scalar at `p` in `r14`, the result `R` of the scalar's bytes at `FR`,
writing only `baseR` and `combW b`. -/
def EngineOk (e : Prog isa) (R : List Byte → List Byte) : Prop :=
  ∀ {b : Addr} {s : State} {p T : Addr}, Ctx8 b s → s.gpr .r14 = p →
    (∀ i < 32, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1) →
    (⟨p, 32⟩ : Region).Disjoint ⟨b, 8192⟩ → TblAt s T → s.syms combSym = T →
    (TBL T).Disjoint ⟨b, 8192⟩ →
    WP isa e s fun t => Rest baseR s t ∧ Frame (combW b) s.mem t.mem ∧
      Spec.Ed25519.encodeLE 32 (V t.mem b FR) = R (bytesAt s.mem p 32)

theorem scalarBaseEngine_ok' : EngineOk scalarBaseEngine Spec.Ed25519.scalarBase :=
  fun hc h14 hin hpd hT hsym apart => scalarBaseEngine_ok hc h14 hin hpd hT hsym apart

/-- `scalarBaseSetup`, an engine and `scalarBaseFinish`: the engine's result at `out`, and the
nonvolatile registers and `lr` restored. -/
theorem baseWrap_ok {e : Prog isa} {R : List Byte → List Byte} (he : EngineOk e R) {s : State}
    (hp : BasePre s) :
    WP isa (.seq (.block scalarBaseSetup) (.seq e (.block scalarBaseFinish))) s fun t =>
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      bytesAt t.mem (s.gpr .r3) 32 = R (bytesAt s.mem (s.gpr .r4) 32) := by
  have hV := SAVE_eq
  have hL := LRS_eq
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .r5 := ⟨_, rfl⟩
  have hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  have hout : (⟨s.gpr .r3, 32⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  unfold scalarBaseSetup
  rw [scalarSave_eq]
  have hsin : ∀ p ∈ saveList, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 p.2) 8 := fun p hpl => by
    have := saveList_in p hpl
    rw [← hb]; exact in_base hws (by omega_arith) (by omega_arith)
  refine WP.seq (WP.of_syms (Spill.save_ok (b := .r5) (by decide) saveList_fits hsin ?_))
  generalize hs1 : ({ s with mem := Spill.saveMem s.mem (s.gpr .r5) s.gpr saveList } : State) = s1
  have hsv : Spill.Saved b s.gpr saveList s1.mem := by rw [← hs1, hb]; exact Spill.saveMem_saved (by decide) _ _ _
  have hf1 : Frame [⟨b, 8192⟩] s.mem s1.mem := by
    rw [← hs1, hb]
    exact Spill.saveMem_frame_base (fun p hpl => by have := saveList_in p hpl; omega_arith) (by decide) _ _ _
  have hg1 : s1.gpr = s.gpr := by rw [← hs1]
  have hrd1 : s1.rd = s.rd := by rw [← hs1]
  have hwr1 : s1.wr = s.wr := by rw [← hs1]
  have hlr1 : s1.lr = s.lr := by rw [← hs1]
  have hsp1 : s1.sp = s.sp := by rw [← hs1]
  refine wp_addiL (by decide) (by decide) fun s2 u2 l2 => wp_addiL (by decide) (by decide) fun s3 u3 l3 =>
    wp_mflr fun s4 u4 l4 => ?_
  have e6 : s4.gpr .r6 = b := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, hg1, BitVec.add_zero, hb]
  have e7 : s4.gpr .r7 = s.lr := by rw [u4.gpr, l3, l2, hlr1]
  have hr4 : Rest [.r6, .r7, .r27] s1 s4 :=
    (u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide)))
  -- The link register's slot.
  refine Spill.save_ok (b := .r6) (l := [(.r7, LRS)]) (rest := [.addi .r14 .r4 0]) (by decide) (by decide)
    (fun p hpl => by
      rw [List.mem_singleton.mp hpl, e6, hr4.wr, hwr1]; exact in_base hws (by omega_arith) (by omega_arith)) ?_
  generalize hs5 : ({ s4 with mem := Spill.saveMem s4.mem (s4.gpr .r6) s4.gpr [(.r7, LRS)] } : State) = s5
  have hsvL : Spill.Saved b s4.gpr [(.r7, LRS)] s5.mem := by
    rw [← hs5, ← e6]; exact Spill.saveMem_saved (by decide) _ _ _
  have hf5 : Frame [⟨b + BitVec.ofNat 64 LRS, 8⟩] s4.mem s5.mem := by
    rw [← hs5, e6]
    exact Spill.saveMem_frame (lo := LRS) (n := 8) (fun p hpl => by rw [List.mem_singleton.mp hpl]; omega_arith)
      (by decide) _ _ _
  have hg5 : s5.gpr = s4.gpr := by rw [← hs5]
  have hrd5 : s5.rd = s4.rd := by rw [← hs5]
  have hwr5 : s5.wr = s4.wr := by rw [← hs5]
  have hsp5 : s5.sp = s4.sp := by rw [← hs5]
  refine wp_addiL (by decide) (by decide) fun s6 u6 _ => WP.block_nil fun sy6 => ?_
  have hR6 : Rest [.r6, .r7, .r14, .r27] s s6 := by
    refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · rw [u6.other _ (by revert hr; cases r <;> decide), hg5, hr4.gpr _ (by revert hr; cases r <;> decide), hg1]
    · rw [u6.rd, hrd5, hr4.rd, hrd1]
    · rw [u6.wr, hwr5, hr4.wr, hwr1]
    · rw [u6.sp, hsp5, hr4.sp, hsp1]
  have hm6 : s6.mem = s5.mem := u6.mem
  have hc6 : Ctx8 b s6 := ⟨by rw [u6.other _ (by decide), hg5, e6], by rw [hR6.wr]; exact hws⟩
  have e14 : s6.gpr .r14 = s.gpr .r4 := by rw [u6.gpr, hg5, u4.other _ (by decide), u3.other _ (by decide),
    u2.other _ (by decide), hg1, BitVec.add_zero]
  have hpd : (⟨s.gpr .r4, 32⟩ : Region).Disjoint ⟨b, 8192⟩ := hb ▸ hp.sc_ws
  -- The scalar's bytes, kept by the saves.
  have hsc : bytesAt s6.mem (s.gpr .r4) 32 = bytesAt s.mem (s.gpr .r4) 32 := by
    simp only [Spec.Ed25519.bytesAt, List.map_inj_left]
    intro i hi
    have hi' := List.mem_range.mp hi
    rw [hm6, hf5 _ fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact fun hc => hpd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (Offset.sub_base b (by omega_arith) _ hc),
      (show s4.mem = s1.mem by rw [u4.mem, u3.mem, u2.mem])]
    exact hf1 _ fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hpd _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  have hin6 : ∀ i < 32, InRegions (s6.rd ++ s6.wr) (s.gpr .r4 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [hR6.rd, hR6.wr, hp.rd]
    exact in_base (List.mem_append_left _ List.mem_cons_self) (by omega_arith) (by omega_arith)
  have hT6 : TblAt s6 (s.syms combSym) :=
    ⟨hp.tfit, ⟨TBL (s.syms combSym), by rw [hR6.rd, hp.rd]; simp, by
      simpa only [BitVec.add_zero] using Offset.contains_base (s.syms combSym) (d := 0) (n := 49152) (k := 49152)
        (by omega) (by omega)⟩,
      fun q hq => by
        have tw : (TBL (s.syms combSym)).Disjoint ⟨b, 8192⟩ := hb ▸ hp.tbl_ws
        rw [hm6, ← hp.words q hq,
          hf5.readW (r := TBL (s.syms combSym)) (Offset.contains_base _ (by omega) (by omega))
            (by simp only [List.mem_singleton, forall_eq]; exact tw.sub_right (Offset.sub_base _ (by decide)))
            (by decide),
          (show s4.mem = s1.mem by rw [u4.mem, u3.mem, u2.mem])]
        exact hf1.readW (r := TBL (s.syms combSym)) (Offset.contains_base _ (by omega) (by omega))
          (by simp only [List.mem_singleton, forall_eq]; exact tw) (by decide)⟩
  have hsym6 : s6.syms combSym = s.syms combSym := congrFun sy6 combSym
  have e27 : s6.gpr .r27 = s.gpr .r3 := by
    rw [u6.other _ (by decide), hg5, u4.other _ (by decide), u3.gpr, u2.other _ (by decide), hg1, BitVec.add_zero]
  refine WP.seq (WP.mono (he hc6 e14 hin6 hpd hT6 hsym6 (hb ▸ hp.tbl_ws))
    fun s7 ⟨r7, f7, v7⟩ => ?_)
  rw [hsc] at v7
  -- The link register restored, then the result and the registers.
  unfold scalarBaseFinish
  rw [show ([.load .d .r7 .r6 LRS, .mtlr .r7, .addi .r14 .r27 0] : List Instr) =
    Spill.restoreCode .r6 [(.r7, LRS)] ++ [.mtlr .r7, .addi .r14 .r27 0] from rfl]
  simp only [List.append_assoc]
  have hsvL7 : Spill.Saved b s4.gpr [(.r7, LRS)] s7.mem := by
    rw [← hm6] at hsvL
    exact hsvL.frame_in (lo := LRS) (n := 8) (fun p hpl => by rw [List.mem_singleton.mp hpl]; omega_arith) f7
      (combW_saves LRS 8 (by omega_arith) (by omega_arith))
  have hc7 : Ctx8 b s7 := hc6.of_rest r7 (by decide)
  refine Spill.restore_ok (b := .r6) (B := b) (by decide) hc7.r6 (by decide) (by decide)
    (fun p hpl => by rw [List.mem_singleton.mp hpl]; exact hc7.inR (by omega_arith)) hsvL7 fun s8 h8 => ?_
  refine wp_mtlr ?_
  generalize hu : ({ s8 with lr := s8.gpr .r7 } : State) = u
  have hlu : u.lr = s.lr := by rw [← hu]; simp only []; rw [h8.gpr _ (List.mem_singleton_self _)]; exact e7
  have hgu : u.gpr = s8.gpr := by rw [← hu]
  have hmu : u.mem = s7.mem := by rw [← hu]; exact h8.mem
  have hwru : u.wr = s.wr := by rw [← hu]; simp only []; rw [h8.wr, r7.wr, hR6.wr]
  have hspu : u.sp = s.sp := by rw [← hu]; simp only []; rw [h8.sp, r7.sp, hR6.sp]
  have hgo : ∀ r, r ∉ [Reg.r7] → r ∉ baseR → r ∉ [Reg.r6, .r7, .r14, .r27] → u.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [hgu, h8.other _ (by simpa using h1), r7.gpr _ h2, hR6.gpr _ h3]
  have hsv7 : Spill.Saved b s.gpr saveList u.mem := by
    rw [hmu]
    have h4 : Spill.Saved b s.gpr saveList s4.mem := by rw [u4.mem, u3.mem, u2.mem]; exact hsv
    have h5 := h4.frame_in (lo := SAVE) (n := 96) saveList_in hf5 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    rw [← hm6] at h5
    exact h5.frame_in (lo := SAVE) (n := 96) saveList_in f7 (combW_saves SAVE 96 (by omega_arith) (by omega_arith))
  have hcu : Ctx b u := ⟨by rw [hgu, h8.other _ (by decide), hc7.r6], 8192, by decide, by rw [hwru]; exact hws⟩
  refine WP.mono (WP.keep_lr (scalarOut_ok hcu (a := FR) (by decide) (P := .r27) (by decide)
    (by rw [hgu, h8.other _ (by decide), r7.gpr _ (by decide), e27]) (by rw [hwru]; exact hout) (hb ▸ hp.out_ws)
    (by rw [hwru]; exact hws) hsv7) (by rw [← Code.allInstrs_eq]; decide +kernel))
    fun t ⟨⟨hg, ho, hsp, hbytes⟩, hlr⟩ => ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · by_cases hm : r ∈ savedRegs
    · exact hg r hm
    · have h1 : r ≠ .r7 := by revert hr; cases r <;> decide
      have h2 : r ≠ .r14 := by revert hm; cases r <;> decide
      rw [ho r hm h1 h2, hgo r (by revert hr; cases r <;> decide) (by revert hr hm; cases r <;> decide)
        (by revert hr hm; cases r <;> decide)]
  · rw [hsp, hspu]
  · rw [hlr, hlu]
  · rw [hbytes, hmu, v7]

end

theorem scalarBase_ok {s : State} (hp : BasePre s) :
    WP isa scalarBase s fun t =>
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      bytesAt t.mem (s.gpr .r3) 32 = Spec.Ed25519.scalarBase (bytesAt s.mem (s.gpr .r4) 32) :=
  baseWrap_ok scalarBaseEngine_ok' hp

theorem base_ok : BaseOk := fun _ hs => by
  obtain ⟨t, s', he, hg, hsp, hlr, hb⟩ := scalarBase_ok hs
  exact ⟨t, s', he, ⟨hg, hsp, hlr⟩, hb⟩

end VG.Proof.Ed25519.PPC64LE
