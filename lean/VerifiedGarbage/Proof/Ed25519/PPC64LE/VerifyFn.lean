module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.VerifyBody
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarReduce
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointTable
import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ed25519_verify_equation` on PPC64LE

The nonvolatile registers saved at `SAVE` and `lr` at `LRS` of `scratch`
(`r6`), the pointers moved to `r29`–`r31`, the body (`verifyBody_ok`), and
its result returned in `r3` (`verify_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (decodeLE bytesAt)

/-- The precondition, by register: `pk` in `r3`, the signature in `r4`, the challenge in `r5` and
`scratch` in `r6`. -/
structure VerifyPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r4, 64⟩, ⟨s.gpr .r5, 64⟩]
  wr : s.wr = [⟨s.gpr .r6, 8192⟩]
  pk_ws : (⟨s.gpr .r3, 32⟩ : Region).Disjoint ⟨s.gpr .r6, 8192⟩
  sig_ws : (⟨s.gpr .r4, 64⟩ : Region).Disjoint ⟨s.gpr .r6, 8192⟩
  ch_ws : (⟨s.gpr .r5, 64⟩ : Region).Disjoint ⟨s.gpr .r6, 8192⟩

/-- The regions the verification writes are clear of the saved registers'. -/
theorem verW_saves {B : Addr} (lo n : Nat) (h1 : 1024 ≤ lo) (h2 : lo + n ≤ 1632) :
    ∀ r ∈ verW B, Region.Disjoint ⟨B + BitVec.ofNat 64 lo, n⟩ r := by
  intro r hr
  have hS : SIGN = 24 := rfl
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  exact mulW_saves lo n h1 h2 r hr

/-- **The setup**: the registers saved, `lr` saved, the pointers in `r29`–`r31`. -/
theorem verifySetup_ok {s : State} (hp : VerifyPre s) :
    WP isa (.block verifySetup) s fun t =>
      VCtx (s.gpr .r6) (s.gpr .r3) (s.gpr .r4) (s.gpr .r5) t ∧ Rest [.r7, .r29, .r30, .r31] s t ∧
      t.lr = s.lr ∧ Frame [⟨s.gpr .r6, 8192⟩] s.mem t.mem ∧ Spill.Saved (s.gpr .r6) s.gpr saveList t.mem ∧
      ∃ g : Reg → BitVec 64, g .r7 = s.lr ∧ Spill.Saved (s.gpr .r6) g [(.r7, LRS)] t.mem := by
  have hV := SAVE_eq
  have hL := LRS_eq
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .r6 := ⟨_, rfl⟩
  have hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  unfold verifySetup
  rw [scalarSave_eq]
  have hsin : ∀ p ∈ saveList, InRegions s.wr (s.gpr .r6 + BitVec.ofNat 64 p.2) 8 := fun p hpl => by
    have := saveList_in p hpl
    rw [← hb]; exact in_base hws (by omega) (by omega)
  refine Spill.save_ok (b := .r6) (by decide) saveList_fits hsin ?_
  generalize hs1 : ({ s with mem := Spill.saveMem s.mem (s.gpr .r6) s.gpr saveList } : State) = s1
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
    wp_addiL (by decide) (by decide) fun s3' u3' l3' => wp_mflr fun s4 u4 l4 => ?_
  have hr4 : Rest [.r7, .r29, .r30, .r31] s1 s4 :=
    (u2.rest (by decide)).trans ((u3.rest (by decide)).trans ((u3'.rest (by decide)).trans (u4.rest (by decide))))
  have e6 : s4.gpr .r6 = b := by rw [hr4.gpr _ (by decide), hg1, hb]
  have e7 : s4.gpr .r7 = s.lr := by rw [u4.gpr, l3', l3, l2, hlr1]
  -- The link register's slot.
  rw [← List.append_nil [Instr.store .d .r7 .r6 LRS]]
  refine Spill.save_ok (b := .r6) (l := [(.r7, LRS)]) (rest := []) (by decide) (by decide)
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
  have hR5 : Rest [.r7, .r29, .r30, .r31] s s5 := by
    refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · rw [hg5, hr4.gpr _ hr, hg1]
    · rw [← hs5]; simp only []; rw [hr4.rd, hrd1]
    · rw [← hs5]; simp only []; rw [hr4.wr, hwr1]
    · rw [← hs5]; simp only []; rw [hr4.sp, hsp1]
  have hm4 : s4.mem = s1.mem := by rw [u4.mem, u3'.mem, u3.mem, u2.mem]
  have hF5 : Frame [⟨b, 8192⟩] s.mem s5.mem :=
    hf1.trans (by rw [← hm4]; exact hf5.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base b (by omega)⟩)
  have hv5 : VCtx b (s.gpr .r3) (s.gpr .r4) (s.gpr .r5) s5 := {
    ctx := ⟨by rw [hR5.gpr _ (by decide), hb], by rw [hR5.wr]; exact hws⟩
    r29 := by rw [hg5, u4.other _ (by decide), u3'.other _ (by decide), u3.other _ (by decide), u2.gpr, hg1,
      BitVec.add_zero]
    r30 := by rw [hg5, u4.other _ (by decide), u3'.other _ (by decide), u3.gpr, u2.other _ (by decide), hg1,
      BitVec.add_zero]
    r31 := by rw [hg5, u4.other _ (by decide), u3'.gpr, u3.other _ (by decide), u2.other _ (by decide), hg1,
      BitVec.add_zero]
    pkR := by rw [hR5.rd, hp.rd]; simp
    sigR := by rw [hR5.rd, hp.rd]; simp
    chR := by rw [hR5.rd, hp.rd]; simp
    pkD := hb ▸ hp.pk_ws
    sigD := hb ▸ hp.sig_ws
    chD := hb ▸ hp.ch_ws }
  refine WP.block_nil ⟨hb ▸ hv5, hR5, by rw [← hs5]; simp only []; rw [l4, l3', l3, l2, hlr1], hb ▸ hF5,
    hb ▸ ((hm4 ▸ hsv).frame_in (lo := SAVE) (n := 96) saveList_in hf5 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)),
    s4.gpr, e7, hb ▸ hsvL⟩

theorem verify_ok {s : State} (hp : VerifyPre s) :
    WP isa Impl.Ed25519.PPC64LE.verifyEquation s fun t =>
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      t.gpr .r3 = if Spec.Ed25519.verifyEquation (bytesAt s.mem (s.gpr .r3) 32) (bytesAt s.mem (s.gpr .r4) 64)
        (bytesAt s.mem (s.gpr .r5) 64) then 1 else 0 := by
  have hV := SAVE_eq
  have hL := LRS_eq
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .r6 := ⟨_, rfl⟩
  have hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  unfold Impl.Ed25519.PPC64LE.verifyEquation
  refine WP.seq (WP.mono (verifySetup_ok hp) fun s5 ⟨hv5, hR5, _, hF5, hsv, g, hg, hsvL⟩ => ?_)
  rw [← hb] at hv5 hF5 hsv hsvL
  have hsub : ∀ r ∈ [(⟨b, 8192⟩ : Region)], Region.Sub r ⟨b, 8192⟩ := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact fun _ h => h
  have hbytes : Spec.Ed25519.verifyEquation (bytesAt s5.mem (s.gpr .r3) 32) (bytesAt s5.mem (s.gpr .r4) 64)
      (bytesAt s5.mem (s.gpr .r5) 64) = Spec.Ed25519.verifyEquation (bytesAt s.mem (s.gpr .r3) 32)
        (bytesAt s.mem (s.gpr .r4) 64) (bytesAt s.mem (s.gpr .r5) 64) := by
    rw [bytesAt_ws hF5 hsub hv5.pkD (by decide), bytesAt_ws hF5 hsub hv5.sigD (by decide),
      bytesAt_ws hF5 hsub hv5.chD (by decide)]
  refine WP.seq (WP.mono (verifyBody_ok hv5) fun s7 ⟨r7, f7, e17⟩ => ?_)
  rw [hbytes] at e17
  -- The link register restored, the result, and the registers.
  unfold verifyFinish
  rw [scalarRestore_eq, show ([.load .d .r7 .r6 LRS, .mtlr .r7, .addi .r3 .r17 0] : List Instr) =
    Spill.restoreCode .r6 [(.r7, LRS)] ++ [.mtlr .r7, .addi .r3 .r17 0] from rfl]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hsvL7 : Spill.Saved b g [(.r7, LRS)] s7.mem :=
    hsvL.frame_in (lo := LRS) (n := 8) (fun p hpl => by rw [List.mem_singleton.mp hpl]; omega) f7
      (verW_saves LRS 8 (by omega) (by omega))
  have hc7 : Ctx8 b s7 := hv5.ctx.of_rest r7 (by decide)
  refine Spill.restore_ok (b := .r6) (B := b) (by decide) hc7.r6 (by decide) (by decide)
    (fun p hpl => by rw [List.mem_singleton.mp hpl]; exact hc7.inR (by omega)) hsvL7 fun s8 h8 => ?_
  refine wp_mtlr ?_
  generalize hu : ({ s8 with lr := s8.gpr .r7 } : State) = u
  have hlu : u.lr = s.lr := by rw [← hu]; simp only []; rw [h8.gpr _ (List.mem_singleton_self _)]; exact hg
  have hgu : u.gpr = s8.gpr := by rw [← hu]
  have hmu : u.mem = s7.mem := by rw [← hu]; exact h8.mem
  have hrdu : u.rd = s.rd := by rw [← hu]; simp only []; rw [h8.rd, r7.rd, hR5.rd]
  have hwru : u.wr = s.wr := by rw [← hu]; simp only []; rw [h8.wr, r7.wr, hR5.wr]
  have hspu : u.sp = s.sp := by rw [← hu]; simp only []; rw [h8.sp, r7.sp, hR5.sp]
  refine wp_addiL (by decide) (by decide) fun v uv lv => ?_
  have hsv7 : Spill.Saved b s.gpr saveList v.mem := by
    rw [uv.mem, hmu]
    exact hsv.frame_in (lo := SAVE) (n := 96) saveList_in f7 (verW_saves SAVE 96 (by omega) (by omega))
  have e6v : v.gpr .r6 = b := by rw [uv.other _ (by decide), hgu, h8.other _ (by decide), hc7.r6]
  refine Spill.restore_ok (b := .r6) (B := b) (by decide) e6v saveList_fits saveList_restorable
    (fun p hpl => by
      have := saveList_in p hpl
      rw [uv.rd, uv.wr, hrdu, hwru]
      exact in_base (List.mem_append_right _ hws) (by omega) (by omega)) hsv7 fun t ht => WP.block_nil
      ⟨fun r hr => ?_, by rw [ht.sp, uv.sp, hspu], by rw [ht.lr, lv, hlu], ?_⟩
  · by_cases hm : r ∈ savedRegs
    · rw [← saveList_regs] at hm
      exact ht.gpr_of (.inl hm)
    · rw [← saveList_regs] at hm
      rw [ht.other _ hm, uv.other _ (by revert hr; cases r <;> decide), hgu,
        h8.other _ (by revert hr; cases r <;> decide), r7.gpr _ (by revert hr hm; cases r <;> decide),
        hR5.gpr _ (by revert hr hm; cases r <;> decide)]
  · rw [ht.other _ (by decide), uv.gpr, hgu, h8.other _ (by decide), BitVec.add_zero, e17]

end VG.Proof.Ed25519.PPC64LE
