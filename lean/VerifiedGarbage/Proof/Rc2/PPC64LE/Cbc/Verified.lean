module

import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Body
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Run
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Lit
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Body
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Run
meta import VerifiedGarbage.Proof.Rc2.Memory
meta import VerifiedGarbage.Proof.Rc2.CbcMemory
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Lit
public import VerifiedGarbage.Impl.Rc2.PPC64LE.Cbc
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-! # Verified RC2-CBC on PPC64LE -/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE.Cbc

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE VG.Impl.Rc2.PPC64LE.Cbc

/-- The CBC contract as the code sees it. -/
def cbcC (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 128⟩
    let iv : Region := ⟨s.gpr .r4, 8⟩
    let data : Region := ⟨s.gpr .r5, 8 * (s.gpr .r6).toNat⟩
    let buf : Region := ⟨s.gpr .r7, 512⟩
    s.rd = [key] ∧ s.wr = [iv, data, buf] ∧ key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧
      (s.gpr .r5).toNat + 8 * (s.gpr .r6).toNat ≤ 2 ^ 64
  post s s' :=
    let result := Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .r3)) d (Spec.Rc2.blockAt s.mem (s.gpr .r4))
      (Spec.Rc2.blocksAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    Spec.Rc2.blocksAt s'.mem (s.gpr .r5) (s.gpr .r6).toNat = result.1 ∧
      Spec.Rc2.blockAt s'.mem (s.gpr .r4) = result.2
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

theorem save_eq : save = .mflr .r0 :: Spill.saveCode .r7 saved := rfl
theorem restore_eq : restore = Spill.restoreCode .r30 saved ++ ([.mtlr .r0] : List Instr) := rfl

theorem cbc_wp (d : Spec.Rc2.Direction) (s : State) (hs : (cbcC d).pre s) :
    WP isa (cbc d) s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧ (cbcC d).post s s' := by
  obtain ⟨hrd, hwr, TI, TD, TW, ID, IW, DW, fit⟩ := hs
  let T := s.gpr .r3
  let I := s.gpr .r4
  let D := s.gpr .r5
  let n := (s.gpr .r6).toNat
  let W := s.gpr .r7
  have R : Regions T I D W n := ⟨TI, TD, TW, ID, IW, DW, by omega_arith⟩
  let s₁ := s.write .r0 s.lr
  let g := s₁.gpr
  have wW : ∀ p ∈ saved, InRegions s₁.wr (s₁.gpr .r7 + BitVec.ofNat 64 p.2) 8 := fun p hp => by
    have hb := saved_in p hp
    show InRegions s.wr (W + BitVec.ofNat 64 p.2) 8
    rw [hwr]; exact ⟨⟨W, 512⟩, by simp [W], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  unfold cbc
  apply WP.seq
  rw [save_eq, List.cons_append]
  refine WP.block_cons_iff.mpr ⟨s₁, exec_mflr, ?_⟩
  refine Spill.save_ok (by decide) saved_fits wW ?_
  let M₀ := Spill.saveMem s₁.mem (s₁.gpr .r7) g saved
  have F₀ : Frame [⟨W, 512⟩] s.mem M₀ := Spill.saveMem_frame_base (fun p hp => by have := saved_in p hp; omega_arith)
    (by decide) _ _ _
  refine WP.mono (WP.keep [.r26, .r27, .r28, .r29, .r30] (c := .block setup) (Q := fun t =>
      t.gpr .r26 = T ∧ t.gpr .r27 = I ∧ t.gpr .r28 = D ∧ t.gpr .r29 = s.gpr .r6 ∧ t.gpr .r30 = W ∧ t.mem = M₀)
    (by unfold setup; rrun [mov, s₁, T, I, D, W, M₀, g]) (by rfl) rfl)
    fun t₀ ⟨⟨a26, a27, a28, a29, a30, m₀⟩, k₀⟩ => ?_
  have H₀ : Inv d T I D W n g M₀ s 0 t₀ := by
    refine ⟨by rw [k₀.2.1]; exact hrd, by rw [k₀.2.2]; exact hwr, a26, a27, by rw [a28]; simp, by
      rw [a29, Nat.sub_zero]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm, a30,
      fun r hr hn => ?_, by rw [m₀]; exact Spill.saveMem_saved (by decide) _ _ _, by rw [m₀], by rw [m₀]; rfl,
      by rw [m₀]; rfl, fun i _ _ => by rw [m₀]⟩
    have hr0 : r ≠ .r0 := by revert r; decide
    rw [k₀.gpr (by revert hn; revert r; decide)]
    simp only [s₁, State.write, hr0, ite_false]
  apply WP.seq
  have loop : WP isa (.ite (.zero .d .r29) (.block []) (.loop (body d) (.nonzero .d .r29))) t₀
      (Inv d T I D W n g M₀ s n) := by
    have hz : isa.eval (.zero .d .r29) t₀ = some (decide (n = 0)) := by
      rw [eval_zero, H₀.r29, Nat.sub_zero, ofNat_beq_zero (by omega_arith)]
    refine WP.ite _ hz (fun h => WP.block_nil ?_) (fun h => countLoop _ _ _ n
      (fun j hj t H => body_run d R hj t H) 0 (by have := of_decide_eq_false h; omega_arith) t₀ H₀)
    have e : n = 0 := of_decide_eq_true h
    rw [e]; rw [e] at H₀; exact H₀
  refine WP.mono loop fun t H => ?_
  rw [restore_eq, WP.block_append_iff]
  refine WP.mono (Spill.restore_wp (by decide) H.r30 saved_fits (by decide) (fun p hp => ?_) H.saved)
    fun t' Rs => WP.block_cons_iff.mpr ⟨_, exec_mtlr, WP.block_nil ⟨fun r hr => ?_, ?_, ?_⟩⟩
  · have hb := saved_in p hp
    rw [H.rd, H.wr]
    exact ⟨⟨W, 512⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · show t'.gpr r = s.gpr r
    by_cases h : r ∈ saved.map Prod.fst
    · have hr0 : r ≠ .r0 := by revert r; decide
      rw [Rs.gpr_of (.inl h)]
      simp only [g, s₁, State.write, hr0, ite_false]
    · rw [Rs.other r h, H.pres r hr h]
  · show t'.gpr .r0 = s.lr
    rw [Rs.gpr (.r0, 304) (by decide)]
    simp [g, s₁, State.write]
  · have hS : Spec.Rc2.scheduleAt M₀ T = Spec.Rc2.scheduleAt s.mem T :=
      Proof.Rc2.scheduleAt_frame F₀ T (by simpa using TW)
    have hI : Spec.Rc2.blockAt M₀ I = Spec.Rc2.blockAt s.mem I := Proof.Rc2.blockAt_frame F₀ I (by simpa using IW)
    have hD : Spec.Rc2.blocksAt M₀ D n = Spec.Rc2.blocksAt s.mem D n :=
      Proof.Rc2.blocksAt_frame F₀ D n (by simpa using DW)
    show Spec.Rc2.blocksAt t'.mem D n = _ ∧ Spec.Rc2.blockAt t'.mem I = _
    rw [Rs.mem, H.done, H.iv, hS, hI, hD]
    exact ⟨rfl, rfl⟩

theorem cbc_ok (d : Spec.Rc2.Direction) (s : State) (hs : (cbcC d).pre s) :
    ∃ t s', Exec isa (cbc d) s t s' ∧ abiPreserved s s' ∧ (cbcC d).post s s' := by
  obtain ⟨t, s', he, hp, hl, hq⟩ := cbc_wp d s hs
  exact ⟨t, s', he, ⟨hp, Exec.sp he, hl⟩, hq⟩

theorem cbc_agree (d : Spec.Rc2.Direction) : ∀ s₁ s₂, (cbcC d).pre s₁ → (cbcC d).pre s₂ → (cbcC d).pub s₁ s₂ →
    taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) s₁ s₂ := by
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1

theorem encrypt_ct : ConstantTime isa (cbcC .encrypt).pre (cbcC .encrypt).pub encrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) (cbc_agree .encrypt) (by taint_decide)

theorem decrypt_ct : ConstantTime isa (cbcC .decrypt).pre (cbcC .decrypt).pub decrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) (cbc_agree .decrypt) (by taint_decide)

def cbcSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 512⟩]

theorem encrypt_verified : Verified target encrypt (Proof.Rc2.cbcEncryptContract abi) := by
  refine Verified.of_correct (k := cbcC .encrypt) (cbc_ok .encrypt) encrypt_ct ?_
  sig_implies [Proof.Rc2.cbcEncryptContract, Proof.Rc2.cbcContract, Proof.Rc2.cbcSig, abi, argRegs, cbcC]
    [cbcSat] using cbcSat

theorem decrypt_verified : Verified target decrypt (Proof.Rc2.cbcDecryptContract abi) := by
  refine Verified.of_correct (k := cbcC .decrypt) (cbc_ok .decrypt) decrypt_ct ?_
  sig_implies [Proof.Rc2.cbcDecryptContract, Proof.Rc2.cbcContract, Proof.Rc2.cbcSig, abi, argRegs, cbcC]
    [cbcSat] using cbcSat

end VG.Proof.Rc2.PPC64LE.Cbc
