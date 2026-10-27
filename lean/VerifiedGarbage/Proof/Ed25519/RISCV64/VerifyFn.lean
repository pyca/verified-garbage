module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyBody
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointTable
import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ed25519_verify_equation` on RISC-V

The callee-saved registers and `ra` saved at `SAVE` of `scratch` (`a3`),
which is aligned to 8 bytes, the pointers moved to `s9`–`s11`, the body
(`verifyBody_ok`), and its result returned in `a0` (`verify_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (decodeLE bytesAt)

/-- The precondition, by register: `pk` in `a0`, the signature in `a1`, the challenge in `a2` and
`scratch`, aligned, in `a3`. -/
structure VerifyPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a1, 64⟩, ⟨s.gpr .a2, 64⟩]
  wr : s.wr = [⟨s.gpr .a3, 8192⟩]
  al : (s.gpr .a3).toNat % 8 = 0
  pk_ws : (⟨s.gpr .a0, 32⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  sig_ws : (⟨s.gpr .a1, 64⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  ch_ws : (⟨s.gpr .a2, 64⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩

/-- The saved registers' slots. -/
def saveList : List (Reg × Nat) := (List.range 13).map fun i => (savedRegs.getD i .s0, SAVE + 8 * i)

theorem regsSave_eq : regsSave = Spill.saveCode .a3 saveList := by
  simp only [regsSave, Spill.saveCode, saveList, List.map_map]; rfl

theorem regsRestore_eq : regsRestore = Spill.restoreCode .a3 saveList := by
  simp only [regsRestore, Spill.restoreCode, saveList, List.map_map]; rfl

theorem saveList_in : ∀ p ∈ saveList, 1024 ≤ p.2 ∧ p.2 + 8 ≤ 1024 + 104 := by decide

theorem saveList_fits : ∀ p ∈ saveList, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem saveList_restorable : Spill.Restorable .a3 saveList := by decide

theorem saveList_regs : saveList.map Prod.fst = savedRegs := by decide

theorem mulW_saves {B : Addr} (lo n : Nat) (h1 : 1024 ≤ lo) (h2 : lo + n ≤ 1632) :
    ∀ r ∈ pmulW B, Region.Disjoint ⟨B + BitVec.ofNat 64 lo, n⟩ r := by
  intro r hr
  have hB : BITSB = 32 := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)

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

/-- **The setup**: the registers saved, the pointers in `s9`–`s11`. -/
theorem verifySetup_ok {s : State} (hp : VerifyPre s) :
    WP isa (.block verifySetup) s fun t =>
      VCtx (s.gpr .a3) (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) t ∧ Rest [.s9, .s10, .s11] s t ∧
      Frame [⟨s.gpr .a3, 8192⟩] s.mem t.mem ∧ Spill.Saved (s.gpr .a3) s.gpr saveList t.mem := by
  have hV : SAVE = 1024 := rfl
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .a3 := ⟨_, rfl⟩
  have hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  unfold verifySetup
  rw [regsSave_eq]
  have hsin : ∀ p ∈ saveList, InRegions s.wr (s.gpr .a3 + BitVec.ofNat 64 p.2) 8 := fun p hpl => by
    have := saveList_in p hpl
    rw [← hb]; exact in_base hws (by omega) (by omega)
  refine Spill.save_ok (b := .a3) hp.al saveList_fits hsin ?_
  generalize hs1 : ({ s with mem := Spill.saveMem s.mem (s.gpr .a3) s.gpr saveList } : State) = s1
  have hsv : Spill.Saved b s.gpr saveList s1.mem := by
    rw [← hs1, hb]; exact Spill.saveMem_saved (by decide) _ _ _
  have hf1 : Frame [⟨b, 8192⟩] s.mem s1.mem := by
    rw [← hs1, hb]
    exact Spill.saveMem_frame_base (fun p hpl => by have := saveList_in p hpl; omega) (by decide) _ _ _
  have hg1 : s1.gpr = s.gpr := by rw [← hs1]
  have hrd1 : s1.rd = s.rd := by rw [← hs1]
  have hwr1 : s1.wr = s.wr := by rw [← hs1]
  have hsp1 : s1.sp = s.sp := by rw [← hs1]
  refine wp_mv fun s2 u2 => wp_mv fun s3 u3 => wp_mv fun s4 u4 => WP.block_nil ?_
  have hr4 : Rest [.s9, .s10, .s11] s1 s4 :=
    (u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide)))
  have hR4 : Rest [.s9, .s10, .s11] s s4 :=
    ⟨fun r hr => by rw [hr4.gpr _ hr, hg1], by rw [hr4.rd, hrd1], by rw [hr4.wr, hwr1], by rw [hr4.sp, hsp1]⟩
  have hm4 : s4.mem = s1.mem := by rw [u4.mem, u3.mem, u2.mem]
  have hv4 : VCtx b (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) s4 := {
    ctx := ⟨by rw [hR4.gpr _ (by decide), hb], by rw [hb]; exact hp.al, by rw [hR4.wr]; exact hws⟩
    s9 := by rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, hg1]
    s10 := by rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), hg1]
    s11 := by rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), hg1]
    pkR := by rw [hR4.rd, hp.rd]; simp
    sigR := by rw [hR4.rd, hp.rd]; simp
    chR := by rw [hR4.rd, hp.rd]; simp
    pkD := hb ▸ hp.pk_ws
    sigD := hb ▸ hp.sig_ws
    chD := hb ▸ hp.ch_ws }
  exact ⟨hb ▸ hv4, hR4, hb ▸ (by rw [hm4]; exact hf1), hb ▸ (by rw [hm4]; exact hsv)⟩

theorem verify_ok {s : State} (hp : VerifyPre s) :
    WP isa Impl.Ed25519.RISCV64.verifyEquation s fun t =>
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.gpr .ra = s.gpr .ra ∧
      t.gpr .a0 = if Spec.Ed25519.verifyEquation (bytesAt s.mem (s.gpr .a0) 32) (bytesAt s.mem (s.gpr .a1) 64)
        (bytesAt s.mem (s.gpr .a2) 64) then 1 else 0 := by
  have hV : SAVE = 1024 := rfl
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .a3 := ⟨_, rfl⟩
  have hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  unfold Impl.Ed25519.RISCV64.verifyEquation
  refine WP.seq (WP.mono (verifySetup_ok hp) fun s5 ⟨hv5, hR5, hF5, hsv⟩ => ?_)
  rw [← hb] at hv5 hF5 hsv
  have hsub : ∀ r ∈ [(⟨b, 8192⟩ : Region)], Region.Sub r ⟨b, 8192⟩ := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact fun _ h => h
  have hbytes : Spec.Ed25519.verifyEquation (bytesAt s5.mem (s.gpr .a0) 32) (bytesAt s5.mem (s.gpr .a1) 64)
      (bytesAt s5.mem (s.gpr .a2) 64) = Spec.Ed25519.verifyEquation (bytesAt s.mem (s.gpr .a0) 32)
        (bytesAt s.mem (s.gpr .a1) 64) (bytesAt s.mem (s.gpr .a2) 64) := by
    rw [bytesAt_ws hF5 hsub hv5.pkD (by decide), bytesAt_ws hF5 hsub hv5.sigD (by decide),
      bytesAt_ws hF5 hsub hv5.chD (by decide)]
  refine WP.seq (WP.mono (verifyBody_ok hv5) fun s7 ⟨r7, f7, e17⟩ => ?_)
  rw [hbytes] at e17
  -- The result, then the registers restored.
  unfold verifyFinish
  rw [regsRestore_eq]
  have hc7 : Ctx8 b s7 := hv5.ctx.of_rest r7 (by decide)
  refine wp_mv fun v uv => ?_
  have hsv7 : Spill.Saved b s.gpr saveList v.mem := by
    rw [uv.mem]
    exact hsv.frame_in (lo := 1024) (n := 104) saveList_in f7 (verW_saves 1024 104 (by omega) (by omega))
  have e6v : v.gpr .a3 = b := by rw [uv.other _ (by decide), hc7.a3]
  rw [← List.append_nil (Spill.restoreCode .a3 saveList)]
  refine Spill.restore_ok (b := .a3) (B := b) hc7.al e6v saveList_fits saveList_restorable
    (fun p hpl => by
      have := saveList_in p hpl
      rw [uv.rd, uv.wr, r7.rd, r7.wr, hR5.rd, hR5.wr]
      exact in_base (List.mem_append_right _ hws) (by omega) (by omega)) hsv7 fun t ht => WP.block_nil
      ⟨fun r hr => ?_, by rw [ht.sp, uv.sp, r7.sp, hR5.sp], ?_, ?_⟩
  · exact ht.gpr_of (.inl (by rw [saveList_regs]; revert hr; cases r <;> decide))
  · exact ht.gpr_of (.inl (by rw [saveList_regs]; decide))
  · rw [ht.other _ (by decide), uv.gpr, e17]

end VG.Proof.Ed25519.RISCV64
