module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointMul
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Encode
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarMulAdd
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.ScalarBase
import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
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
in `scratch`, puts the base point in slots 0–3, multiplies it by the 256-bit
scalar (`pointFromScalar_ok`), encodes the product at `FR`
(`pointEncode_ok`), and copies it to `out`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (decodeLE bytesAt)

section
variable {b : Addr}

theorem initFields_ok {s : State} (hc : Ctx b s) :
    WP isa (.block initFields) s fun t => Rest [.r7] s t ∧ Frame [FA b] s.mem t.mem := by
  unfold initFields
  refine wp_li (by decide) fun s1 u1 => ?_
  refine WP.mono (stores_ok (r := .r7) (o := 64) (n := 176) (by omega)
    (hc.of_rest (u1.rest (ws := [.r7]) (by decide)) (by decide))) fun t ⟨_, h2, _, h4⟩ =>
      ⟨(u1.rest (by decide)).trans (h4.mono (by decide)), ?_⟩
  rw [← u1.mem]
  exact h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩

theorem env_const16 (e : Env) : point (evalOps [.const 16 Spec.Ed25519.d] e) 0 1 2 3 = point e 0 1 2 3 ∧
    evalOps [.const 16 Spec.Ed25519.d] e 16 = Spec.Ed25519.d := ⟨rfl, rfl⟩

/-- **`[S] P`** for the `2 count` bytes at `r14`. -/
theorem pointFromScalar_ok {s : State} (hc : Ctx8 b s) {count : Nat} (hc1 : 1 ≤ count) (hc32 : count ≤ 32)
    {p : Addr} (h14 : s.gpr .r14 = p) (hin : ∀ i < 2 * count, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hpd : (⟨p, 2 * count⟩ : Region).Disjoint ⟨b, 8192⟩) :
    WP isa (pointFromScalar count) s fun t =>
      Rest (.r19 :: .r7 :: batchR) s t ∧ Frame (mulW b) s.mem t.mem ∧
      point (env t.mem b) 0 1 2 3 =
        Spec.Ed25519.pointMul (decodeLE (bytesAt s.mem p (2 * count))) (point (env s.mem b) 0 1 2 3) := by
  unfold pointFromScalar
  refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
  have hc1' : Ctx8 b s1 := hc.of_rest (u1.rest (ws := [.r19]) (by decide)) (by decide)
  refine WP.seq (WP.mono (fieldCode_ok _ hc1'.ctx) fun s2 ⟨k2, e2⟩ => ?_)
  obtain ⟨p2, d2⟩ := env_const16 (env s1.mem b)
  rw [← e2] at p2 d2
  have hc2 : Ctx8 b s2 := hc1'.of_keep k2
  have hb2 : bytesAt s2.mem p (2 * count) = bytesAt s.mem p (2 * count) := by
    simp only [Spec.Ed25519.bytesAt, List.map_inj_left]
    intro i hi
    rw [← u1.mem]
    exact bytes_ws k2.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega)) hpd
      (by omega) (List.mem_range.mp hi)
  refine WP.mono (pointMultiply_ok hc2 d2 (p := p) hc1 hc32
    (by rw [k2.rest.gpr _ (by decide), u1.gpr, h14, BitVec.add_zero])
    (fun i hi => by rw [k2.rest.rd, k2.rest.wr, u1.rd, u1.wr]; exact hin i hi) hpd) fun t ⟨rt, ft, pt, _⟩ =>
      ⟨?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((k2.rest.mono (by decide)).trans (rt.mono (by decide)))
  · rw [← u1.mem]
    exact (k2.frame.mono (by simp)).trans ft
  · rw [pt, hb2, p2, u1.mem]

/-- The registers the engine writes. -/
abbrev baseR : List Reg := .r17 :: .r19 :: .r7 :: batchR

theorem scalarBaseEngine_ok {s : State} (hc : Ctx8 b s) {p : Addr} (h14 : s.gpr .r14 = p)
    (hin : ∀ i < 32, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hpd : (⟨p, 32⟩ : Region).Disjoint ⟨b, 8192⟩) :
    WP isa scalarBaseEngine s fun t =>
      Rest baseR s t ∧ Frame (mulW b) s.mem t.mem ∧
      V t.mem b FR = encodeNum (Spec.Ed25519.pointMul (decodeLE (bytesAt s.mem p 32)) Spec.Ed25519.basePoint) := by
  unfold scalarBaseEngine
  refine WP.seq (WP.mono (initFields_ok hc.ctx) fun s1 ⟨r1, f1⟩ => ?_)
  have hc1 : Ctx8 b s1 := hc.of_rest r1 (by decide)
  unfold constPoint
  refine WP.seq (WP.mono (fieldCode_ok _ hc1.ctx) fun s2 ⟨k2, e2⟩ => ?_)
  have p2 := (env_constPoint (env s1.mem b) Spec.Ed25519.basePoint).1
  rw [← e2] at p2
  have hc2 : Ctx8 b s2 := hc1.of_keep k2
  have hF2 : Frame [FA b] s.mem s2.mem := f1.trans k2.frame
  have hb2 : bytesAt s2.mem p 32 = bytesAt s.mem p 32 := by
    simp only [Spec.Ed25519.bytesAt, List.map_inj_left]
    intro i hi
    exact bytes_ws hF2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega)) hpd (by decide)
      (List.mem_range.mp hi)
  have hR2 : Rest baseR s s2 := (r1.mono (by decide)).trans (k2.rest.mono (by decide))
  have hR2' : Rest fclob s s2 := (r1.mono (by decide)).trans k2.rest
  refine WP.seq (WP.mono (pointFromScalar_ok hc2 (count := 16) (by decide) (by decide) (p := p)
    (by rw [hR2'.gpr _ (by decide), h14])
    (fun i hi => by rw [hR2.rd, hR2.wr]; exact hin i hi) hpd) fun s3 ⟨r3, f3, p3⟩ => ?_)
  rw [hb2, p2] at p3
  have hc3 : Ctx8 b s3 := hc2.of_rest r3 (by decide)
  refine WP.mono (pointEncode_ok hc3) fun t ⟨rt, ft, vt⟩ => ⟨?_, ?_, ?_⟩
  · exact hR2.trans ((r3.mono (by decide)).trans (rt.mono (by decide)))
  · exact (hF2.mono (by simp)).trans (f3.trans (ft.mono (by simp)))
  · rw [vt, p3]

/-- A block that writes no link register keeps it. -/
theorem WP.keep_lr {is : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block is) s Q)
    (hl : (instrs (.block is : Prog isa)).all (fun i => !i.writesLr) = true) :
    WP isa (.block is) s fun t => Q t ∧ t.lr = s.lr := by
  obtain ⟨tr, t, he, hq⟩ := h
  exact ⟨tr, t, he, hq, Exec.lr he rfl hl⟩

theorem wp_mflr {d : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Upd s s' d s.lr → s'.lr = s.lr → WP isa (.block is) s' Q) : WP isa (.block (.mflr d :: is)) s Q :=
  WP.cons exec_mflr (k _ (Upd.write _ _ _) rfl)

/-- `addi`, keeping the link register. -/
theorem wp_addiL {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm < 2 ^ 15) {is : List Instr} {s : State}
    {Q : State → Prop} (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → s'.lr = s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n imm :: is)) s Q :=
  WP.cons (exec_addi hn h) (k _ (Upd.write _ _ _) rfl)

theorem wp_mtlr {r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : WP isa (.block is) { s with lr := s.gpr r } Q) : WP isa (.block (.mtlr r :: is)) s Q :=
  WP.cons exec_mtlr k

theorem LRS_eq : LRS = 1120 := rfl

/-- The precondition, by register: `out` in `r3`, `scalar` in `r4`, `scratch` in `r5`. -/
structure BasePre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 32⟩]
  wr : s.wr = [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r5, 8192⟩]
  out_ws : (⟨s.gpr .r3, 32⟩ : Region).Disjoint ⟨s.gpr .r5, 8192⟩
  sc_ws : (⟨s.gpr .r4, 32⟩ : Region).Disjoint ⟨s.gpr .r5, 8192⟩

theorem mulW_saves {B : Addr} (lo n : Nat) (h1 : 1024 ≤ lo) (h2 : lo + n ≤ 1632) :
    ∀ r ∈ mulW B, Region.Disjoint ⟨B + BitVec.ofNat 64 lo, n⟩ r := by
  intro r hr
  have hB : BITSB = 32 := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)

theorem scalarBase_ok {s : State} (hp : BasePre s) :
    WP isa scalarBase s fun t =>
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      bytesAt t.mem (s.gpr .r3) 32 = Spec.Ed25519.scalarBase (bytesAt s.mem (s.gpr .r4) 32) := by
  have hV := SAVE_eq
  have hL := LRS_eq
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .r5 := ⟨_, rfl⟩
  have hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  have hout : (⟨s.gpr .r3, 32⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  unfold scalarBase scalarBaseSetup
  rw [scalarSave_eq]
  have hsin : ∀ p ∈ saveList, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 p.2) 8 := fun p hpl => by
    have := saveList_in p hpl
    rw [← hb]; exact in_base hws (by omega) (by omega)
  refine WP.seq (Spill.save_ok (b := .r5) (by decide) saveList_fits hsin ?_)
  generalize hs1 : ({ s with mem := Spill.saveMem s.mem (s.gpr .r5) s.gpr saveList } : State) = s1
  have hsv : Spill.Saved b s.gpr saveList s1.mem := by rw [← hs1, hb]; exact Spill.saveMem_saved (by decide) _ _ _
  have hf1 : Frame [⟨b, 8192⟩] s.mem s1.mem := by
    rw [← hs1, hb]
    exact Spill.saveMem_frame_base (fun p hpl => by have := saveList_in p hpl; omega) (by decide) _ _ _
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
      rw [List.mem_singleton.mp hpl, e6, hr4.wr, hwr1]; exact in_base hws (by omega) (by omega)) ?_
  generalize hs5 : ({ s4 with mem := Spill.saveMem s4.mem (s4.gpr .r6) s4.gpr [(.r7, LRS)] } : State) = s5
  have hsvL : Spill.Saved b s4.gpr [(.r7, LRS)] s5.mem := by
    rw [← hs5, ← e6]; exact Spill.saveMem_saved (by decide) _ _ _
  have hf5 : Frame [⟨b + BitVec.ofNat 64 LRS, 8⟩] s4.mem s5.mem := by
    rw [← hs5, e6]
    exact Spill.saveMem_frame (lo := LRS) (n := 8) (fun p hpl => by rw [List.mem_singleton.mp hpl]; omega)
      (by decide) _ _ _
  have hg5 : s5.gpr = s4.gpr := by rw [← hs5]
  have hrd5 : s5.rd = s4.rd := by rw [← hs5]
  have hwr5 : s5.wr = s4.wr := by rw [← hs5]
  have hsp5 : s5.sp = s4.sp := by rw [← hs5]
  refine wp_addiL (by decide) (by decide) fun s6 u6 _ => WP.block_nil ?_
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
        exact fun hc => hpd _ (Offset.contains_base _ (by omega) (by omega)) (Offset.sub_base b (by omega) _ hc),
      (show s4.mem = s1.mem by rw [u4.mem, u3.mem, u2.mem])]
    exact hf1 _ fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hpd _ (Offset.contains_base _ (by omega) (by omega))
  have hin6 : ∀ i < 32, InRegions (s6.rd ++ s6.wr) (s.gpr .r4 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [hR6.rd, hR6.wr, hp.rd]
    exact in_base (List.mem_append_left _ (List.mem_singleton_self _)) (by omega) (by omega)
  have e27 : s6.gpr .r27 = s.gpr .r3 := by
    rw [u6.other _ (by decide), hg5, u4.other _ (by decide), u3.gpr, u2.other _ (by decide), hg1, BitVec.add_zero]
  refine WP.seq (WP.mono (scalarBaseEngine_ok hc6 e14 hin6 hpd) fun s7 ⟨r7, f7, v7⟩ => ?_)
  rw [hsc] at v7
  -- The link register restored, then the result and the registers.
  unfold scalarBaseFinish
  rw [show ([.load .d .r7 .r6 LRS, .mtlr .r7, .addi .r14 .r27 0] : List Instr) =
    Spill.restoreCode .r6 [(.r7, LRS)] ++ [.mtlr .r7, .addi .r14 .r27 0] from rfl]
  simp only [List.append_assoc]
  have hsvL7 : Spill.Saved b s4.gpr [(.r7, LRS)] s7.mem := by
    rw [← hm6] at hsvL
    exact hsvL.frame_in (lo := LRS) (n := 8) (fun p hpl => by rw [List.mem_singleton.mp hpl]; omega) f7
      (mulW_saves LRS 8 (by omega) (by omega))
  have hc7 : Ctx8 b s7 := hc6.of_rest r7 (by decide)
  refine Spill.restore_ok (b := .r6) (B := b) (by decide) hc7.r6 (by decide) (by decide)
    (fun p hpl => by rw [List.mem_singleton.mp hpl]; exact hc7.inR (by omega)) hsvL7 fun s8 h8 => ?_
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
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    rw [← hm6] at h5
    exact h5.frame_in (lo := SAVE) (n := 96) saveList_in f7 (mulW_saves SAVE 96 (by omega) (by omega))
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
  · rw [hbytes, hmu, v7]; rfl

end

end VG.Proof.Ed25519.PPC64LE
