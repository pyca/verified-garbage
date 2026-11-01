module

public import VerifiedGarbage.Proof.Ed25519.Contract
public import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyFn
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Encode
public import VerifiedGarbage.Impl.Ed25519.RISCV64.ScalarBase
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointScalar
import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
import VerifiedGarbage.Proof.Ed25519.RISCV64.Freeze
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ed25519_scalar_base` on RISC-V: correctness

The function moves `scratch`, aligned to 8 bytes, to `a3`, saves the
callee-saved registers and `ra` there, puts the base point in slots 0–3,
multiplies it by the 256-bit scalar (`pointFromScalar_ok`), encodes the
product at `FR` (`pointEncode_ok`), and copies it to `out`
(`packField_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (decodeLE bytesAt)

section
variable {b : Addr}

/-- The registers the engine writes. -/
abbrev baseR : List Reg := .t6 :: .s5 :: .a4 :: batchR

theorem scalarBaseEngine_ok {s : State} (hc : Ctx8 b s) {p : Addr} (h14 : s.gpr .s0 = p)
    (hin : ∀ i < 32, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hpd : (⟨p, 32⟩ : Region).Disjoint ⟨b, 8192⟩) :
    WP isa scalarBaseEngine s fun t =>
      Rest baseR s t ∧ Frame (pmulW b) s.mem t.mem ∧
      V t.mem b FR = encodeNum (Spec.Ed25519.pointMul (decodeLE (bytesAt s.mem p 32)) Spec.Ed25519.basePoint) := by
  unfold scalarBaseEngine
  refine WP.seq (WP.mono (initFields_ok hc.ctx) fun s1 ⟨r1, f1⟩ => ?_)
  have hc1 : Ctx8 b s1 := hc.of_rest r1 (by decide)
  unfold constPoint
  refine WP.seq (WP.mono (fieldCode_ok _ hc1.ctx hc1.ws) fun s2 ⟨k2, e2⟩ => ?_)
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
    (fun i hi => by rw [hR2.rd, hR2.wr]; exact hin i hi) hpd) fun s3 ⟨r3, f3, p3, _⟩ => ?_)
  rw [hb2, p2] at p3
  have hc3 : Ctx8 b s3 := hc2.of_rest r3 (by decide)
  refine WP.mono (pointEncode_ok hc3) fun t ⟨rt, ft, vt⟩ => ⟨?_, ?_, ?_⟩
  · exact hR2.trans ((r3.mono (by decide)).trans (rt.mono (by decide)))
  · exact (hF2.mono (by simp)).trans (f3.trans (ft.mono (by simp)))
  · rw [vt, p3]

end

/-- The precondition, by register: `out` in `a0`, `scalar` in `a1`, `scratch`, aligned, in `a2`. -/
structure BasePre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, 32⟩]
  wr : s.wr = [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a2, 8192⟩]
  al : (s.gpr .a2).toNat % 8 = 0
  out_ws : (⟨s.gpr .a0, 32⟩ : Region).Disjoint ⟨s.gpr .a2, 8192⟩
  sc_ws : (⟨s.gpr .a1, 32⟩ : Region).Disjoint ⟨s.gpr .a2, 8192⟩

/-- The saved registers' slots. -/
def baseList : List (Reg × Nat) := (List.range 7).map fun i => (baseSaved.getD i .s0, SAVE + 8 * i)

theorem baseSave_eq : baseSave = Spill.saveCode .a3 baseList := by
  simp only [baseSave, Spill.saveCode, baseList, List.map_map]; rfl

theorem baseRestore_eq : baseRestore = Spill.restoreCode .a3 baseList := by
  simp only [baseRestore, Spill.restoreCode, baseList, List.map_map]; rfl

theorem baseList_in : ∀ p ∈ baseList, 1024 ≤ p.2 ∧ p.2 + 8 ≤ 1024 + 104 := by decide

theorem baseList_fits : ∀ p ∈ baseList, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem baseList_restorable : Spill.Restorable .a3 baseList := by decide

theorem baseList_regs : baseList.map Prod.fst = baseSaved := by decide

theorem baseList_not_a3 : ∀ p ∈ baseList, p.1 ≠ .a3 := by decide

theorem scalarBase_ok {s : State} (hp : BasePre s) :
    WP isa scalarBase s fun t =>
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.gpr .ra = s.gpr .ra ∧
      bytesAt t.mem (s.gpr .a0) 32 = Spec.Ed25519.scalarBase (bytesAt s.mem (s.gpr .a1) 32) := by
  have hV : SAVE = 1024 := rfl
  have hX := FR_eq
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .a2 := ⟨_, rfl⟩
  have hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  have hout : (⟨s.gpr .a0, 32⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hal : b.toNat % 8 = 0 := by rw [hb]; exact hp.al
  unfold scalarBase scalarBaseSetup
  rw [baseSave_eq]
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun s1 u1 => ?_)
  have e1 : s1.gpr .a3 = b := by rw [u1.gpr, hb]
  have hsin : ∀ p ∈ baseList, InRegions s1.wr (s1.gpr .a3 + BitVec.ofNat 64 p.2) 8 := fun p hpl => by
    have := baseList_in p hpl
    rw [e1, u1.wr]; exact in_base hws (by omega) (by omega)
  refine Spill.save_ok (b := .a3) (by rw [e1]; exact hal) baseList_fits hsin ?_
  generalize hs2 : ({ s1 with mem := Spill.saveMem s1.mem (s1.gpr .a3) s1.gpr baseList } : State) = s2
  have hsv : Spill.Saved b s.gpr baseList s2.mem := by
    have h := Spill.saveMem_saved (l := baseList) (by decide) s1.mem (s1.gpr .a3) s1.gpr
    rw [← hs2, ← e1]
    exact fun p hpl => by rw [h p hpl, u1.other _ (baseList_not_a3 p hpl)]
  have hf2 : Frame [⟨b, 8192⟩] s.mem s2.mem := by
    rw [← hs2, ← u1.mem, ← e1]
    exact Spill.saveMem_frame_base (fun p hpl => by have := baseList_in p hpl; omega) (by decide) _ _ _
  have hg2 : s2.gpr = s1.gpr := by rw [← hs2]
  have hrd2 : s2.rd = s1.rd := by rw [← hs2]
  have hwr2 : s2.wr = s1.wr := by rw [← hs2]
  have hsp2 : s2.sp = s1.sp := by rw [← hs2]
  refine wp_mv fun s3 u3 => wp_mv fun s4 u4 => WP.block_nil ?_
  have hR4 : Rest [.a3, .s3, .s0] s s4 := by
    have h34 : Rest [.s3, .s0] s2 s4 := (u3.rest (by decide)).trans (u4.rest (by decide))
    refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · rw [h34.gpr _ (by revert hr; cases r <;> decide), hg2, u1.other _ (by revert hr; cases r <;> decide)]
    · rw [h34.rd, hrd2, u1.rd]
    · rw [h34.wr, hwr2, u1.wr]
    · rw [h34.sp, hsp2, u1.sp]
  have hm4 : s4.mem = s2.mem := by rw [u4.mem, u3.mem]
  have hc4 : Ctx8 b s4 := ⟨by rw [u4.other _ (by decide), u3.other _ (by decide), hg2, e1], hal,
    by rw [hR4.wr]; exact hws⟩
  have e14 : s4.gpr .s0 = s.gpr .a1 := by
    rw [u4.gpr, u3.other _ (by decide), hg2, u1.other _ (by decide)]
  have e27 : s4.gpr .s3 = s.gpr .a0 := by
    rw [u4.other _ (by decide), u3.gpr, hg2, u1.other _ (by decide)]
  have hpd : (⟨s.gpr .a1, 32⟩ : Region).Disjoint ⟨b, 8192⟩ := hb ▸ hp.sc_ws
  have hsub : ∀ r ∈ [(⟨b, 8192⟩ : Region)], Region.Sub r ⟨b, 8192⟩ := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact fun _ h => h
  have hsc : bytesAt s4.mem (s.gpr .a1) 32 = bytesAt s.mem (s.gpr .a1) 32 := by
    rw [hm4]; exact bytesAt_ws hf2 hsub hpd (by decide)
  have hin4 : ∀ i < 32, InRegions (s4.rd ++ s4.wr) (s.gpr .a1 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [hR4.rd, hR4.wr, hp.rd]
    exact in_base (List.mem_append_left _ (List.mem_singleton_self _)) (by omega) (by omega)
  refine WP.seq (WP.mono (scalarBaseEngine_ok hc4 e14 hin4 hpd) fun s7 ⟨r7, f7, v7⟩ => ?_)
  rw [hsc] at v7
  -- The encoding to `out`, then the registers restored.
  unfold scalarBaseFinish
  rw [baseRestore_eq]
  simp only [List.cons_append, List.nil_append]
  have hc7 : Ctx8 b s7 := hc4.of_rest r7 (by decide)
  refine wp_mv fun v uv => ?_
  have hcv : Ctx8 b v := hc7.of_rest (uv.rest (ws := [.s0]) (by decide)) (by decide)
  have ev : v.gpr .s0 = s.gpr .a0 := by rw [uv.gpr, r7.gpr _ (by decide), e27]
  have hwv : v.wr = s.wr := by rw [uv.wr, r7.wr, hR4.wr]
  have hdo : (⟨s.gpr .a0 + BitVec.ofNat 64 0, 32⟩ : Region).Disjoint ⟨b, 8192⟩ := by
    rw [BitVec.add_zero]; exact hb ▸ hp.out_ws
  refine WP.block_append_iff.mpr (WP.mono (packField_ok hcv.ctx (p := .s0) (by decide) ev (a := FR) (dst := 0)
    (by omega) (by omega) (by decide)
    (fun k hk => by rw [hwv]; exact in_base hout (by omega) (by omega))
    (hdo.sub_right (Offset.sub_base b (by omega)))) fun w hw => ?_)
  have hsvw : Spill.Saved b s.gpr baseList w.mem := by
    have h7 : Spill.Saved b s.gpr baseList s7.mem := by
      rw [← hm4] at hsv
      exact hsv.frame_in (lo := 1024) (n := 104) baseList_in f7 (mulW_saves 1024 104 (by omega) (by omega))
    rw [← uv.mem] at h7
    exact h7.frame_in (lo := 1024) (n := 104) baseList_in hw.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hdo.sub_right (Offset.sub_base b (d := 1024) (n := 104) (by omega))).symm
  have e6w : w.gpr .a3 = b := by rw [hw.rest.gpr _ (by decide), hcv.a3]
  rw [← List.append_nil (Spill.restoreCode .a3 baseList)]
  refine Spill.restore_ok (b := .a3) (B := b) hal e6w baseList_fits baseList_restorable
    (fun p hpl => by
      have := baseList_in p hpl
      rw [hw.rest.rd, hw.rest.wr, hwv, uv.rd, r7.rd, hR4.rd]
      exact in_base (List.mem_append_right _ hws) (by omega) (by omega)) hsvw fun t ht => WP.block_nil
      ⟨fun r hr => ?_, by rw [ht.sp, hw.rest.sp, uv.sp, r7.sp, hR4.sp], ?_, ?_⟩
  · by_cases hm : r ∈ baseSaved
    · exact ht.gpr_of (.inl (by rw [baseList_regs]; exact hm))
    · have hn : r ∉ baseList.map Prod.fst := by rw [baseList_regs]; exact hm
      rw [ht.other _ hn, hw.rest.gpr _ (by revert hr; cases r <;> decide),
        uv.other _ (by revert hr hm; cases r <;> decide), r7.gpr _ (by revert hr hm; cases r <;> decide),
        hR4.gpr _ (by revert hr hm; cases r <;> decide)]
  · exact ht.gpr_of (.inl (by rw [baseList_regs]; decide))
  · rw [ht.mem]
    have hv' : V v.mem b FR = encodeNum (Spec.Ed25519.pointMul (decodeLE (bytesAt s.mem (s.gpr .a1) 32))
        Spec.Ed25519.basePoint) := by rw [uv.mem]; exact v7
    rw [out_bytes (b := b) (a := FR) (fun j hj => by rw [← Nat.zero_add (4 * j)]; exact hw.outs j hj) hv']
    rfl

/-- `scalarBaseContract` by register. -/
def baseRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 32⟩
    let sc : Region := ⟨s.gpr .a1, 32⟩
    let ws : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [sc] ∧ s.wr = [out, ws] ∧ (s.gpr .a2).toNat % 8 = 0 ∧ out.Disjoint ws ∧ sc.Disjoint ws
  post s s' := bytesAt s'.mem (s.gpr .a0) 32 = Spec.Ed25519.scalarBase (bytesAt s.mem (s.gpr .a1) 32)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

theorem base_ok' (s : State) (hs : baseRV.pre s) :
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ baseRV.post s s' := by
  obtain ⟨a, b, c, d, e⟩ := hs
  obtain ⟨t, s', he, hg, hsp, hra, hb⟩ := scalarBase_ok ⟨a, b, c, d, e⟩
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hb⟩

end VG.Proof.Ed25519.RISCV64
