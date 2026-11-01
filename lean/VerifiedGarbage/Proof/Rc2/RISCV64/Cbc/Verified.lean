module

import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Body
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Rc2.RISCV64.Run
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Body
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Run
meta import VerifiedGarbage.Proof.Rc2.Memory
meta import VerifiedGarbage.Proof.Rc2.CbcMemory
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
public import VerifiedGarbage.Impl.Rc2.RISCV64.Cbc
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-! # Verified RC2-CBC on RISCV64 -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Cbc

/-- The CBC contract as the code sees it. -/
def cbcC (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 128⟩
    let iv : Region := ⟨s.gpr .a1, 8⟩
    let data : Region := ⟨s.gpr .a2, 8 * (s.gpr .a3).toNat⟩
    let buf : Region := ⟨s.gpr .a4, 512⟩
    s.rd = [key] ∧ s.wr = [iv, data, buf] ∧ (s.gpr .a4).toNat % 8 = 0 ∧ key.Disjoint iv ∧ key.Disjoint data ∧
      key.Disjoint buf ∧ iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧
      (s.gpr .a2).toNat + 8 * (s.gpr .a3).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + 512 ≤ 2 ^ 64
  post s s' :=
    let result := Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .a0)) d (Spec.Rc2.blockAt s.mem (s.gpr .a1))
      (Spec.Rc2.blocksAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    Spec.Rc2.blocksAt s'.mem (s.gpr .a2) (s.gpr .a3).toNat = result.1 ∧
      Spec.Rc2.blockAt s'.mem (s.gpr .a1) = result.2
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

theorem save_eq : save = Spill.saveCode .a4 saved := rfl
theorem restore_eq : restore = Spill.restoreCode .s5 saved := rfl

theorem cbc_wp (d : Spec.Rc2.Direction) (s : State) (hs : (cbcC d).pre s) :
    WP isa (cbc d) s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.gpr .ra = s.gpr .ra ∧
      (cbcC d).post s s' := by
  obtain ⟨hrd, hwr, hal, TI, TD, TW, ID, IW, DW, fit, fitW⟩ := hs
  let T := s.gpr .a0
  let I := s.gpr .a1
  let D := s.gpr .a2
  let n := (s.gpr .a3).toNat
  let W := s.gpr .a4
  have R : Regions T I D W n := ⟨TI, TD, TW, ID, IW, DW, fit, fitW, hal⟩
  let g := s.gpr
  have wW : ∀ p ∈ saved, InRegions s.wr (s.gpr .a4 + BitVec.ofNat 64 p.2) 8 := fun p hp => by
    have hb := saved_in p hp
    rw [hwr]; exact ⟨⟨W, 512⟩, by simp [W], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  unfold cbc
  apply WP.seq
  rw [save_eq]
  refine Spill.save_ok hal saved_fits wW ?_
  let M₀ := Spill.saveMem s.mem (s.gpr .a4) g saved
  have F₀ : Frame [⟨W, 512⟩] s.mem M₀ := Spill.saveMem_frame_base (fun p hp => by have := saved_in p hp; omega_arith)
    (by decide) _ _ _
  refine WP.mono (WP.keep [.s1, .s2, .s3, .s4, .s5] (c := .block setup) (Q := fun t =>
      t.gpr .s1 = T ∧ t.gpr .s2 = I ∧ t.gpr .s3 = D ∧ t.gpr .s4 = s.gpr .a3 ∧ t.gpr .s5 = W ∧ t.mem = M₀)
    (by unfold setup; rrun [mov, T, I, D, W, M₀, g]) (by rfl) rfl)
    fun t₀ ⟨⟨a26, a27, a28, a29, a30, m₀⟩, k₀⟩ => ?_
  have H₀ : Inv d T I D W n g M₀ s 0 t₀ := by
    refine ⟨by rw [k₀.2.1]; exact hrd, by rw [k₀.2.2]; exact hwr, a26, a27, by rw [a28]; simp, by
      rw [a29, Nat.sub_zero]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm, a30,
      fun r hr hn => ?_, by rw [m₀]; exact Spill.saveMem_saved (by decide) _ _ _, by rw [m₀], by rw [m₀]; rfl,
      by rw [m₀]; rfl, fun i _ _ => by rw [m₀]⟩
    rw [k₀.gpr (by revert hn; revert r; decide)]
  apply WP.seq
  have loop : WP isa (.ite (.zero .s4) (.block []) (.loop (body d) (.nonzero .s4))) t₀
      (Inv d T I D W n g M₀ s n) := by
    have hz : isa.eval (.zero .s4) t₀ = some (decide (n = 0)) := by
      rw [Steps.eval_zero, H₀.s4, Nat.sub_zero, Steps.ofNat_beq_zero (by omega_arith)]
    refine WP.ite _ hz (fun h => WP.block_nil ?_) (fun h => countLoop _ _ _ n
      (fun j hj t H => body_run d R hj t H) 0 (by have := of_decide_eq_false h; omega_arith) t₀ H₀)
    have e : n = 0 := of_decide_eq_true h
    rw [e]; rw [e] at H₀; exact H₀
  refine WP.mono loop fun t H => ?_
  rw [restore_eq]
  refine WP.mono (Spill.restore_wp hal H.s5 saved_fits (by decide) (fun p hp => ?_) H.saved)
    fun t' Rs => ⟨fun r hr => ?_, ?_, ?_⟩
  · have hb := saved_in p hp
    rw [H.rd, H.wr]
    exact ⟨⟨W, 512⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · by_cases h : r ∈ saved.map Prod.fst
    · exact Rs.gpr_of (.inl h)
    · rw [Rs.other r h, H.pres r hr h]
  · exact Rs.gpr_of (.inl (by decide))
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
  obtain ⟨t, s', he, ⟨hp, hra, hq⟩, _, _, hsp⟩ := WP.rdwr (cbc_wp d s hs)
  exact ⟨t, s', he, ⟨hp, hsp, hra⟩, hq⟩

theorem cbc_agree (d : Spec.Rc2.Direction) : ∀ s₁ s₂, (cbcC d).pre s₁ → (cbcC d).pre s₂ → (cbcC d).pub s₁ s₂ →
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) s₁ s₂ := by
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
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) (cbc_agree .encrypt) (by taint_decide)

theorem decrypt_ct : ConstantTime isa (cbcC .decrypt).pre (cbcC .decrypt).pub decrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) (cbc_agree .decrypt) (by taint_decide)

def cbcSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 512⟩]

theorem encrypt_verified : Verified RISCV64.target encrypt (Proof.Rc2.cbcEncryptContract RISCV64.abi) := by
  refine Verified.of_correct (k := cbcC .encrypt) (cbc_ok .encrypt) encrypt_ct ?_
  sig_implies [Proof.Rc2.cbcEncryptContract, Proof.Rc2.cbcContract, Proof.Rc2.cbcSig, RISCV64.abi,
    RISCV64.argRegs, cbcC]
    [cbcSat] using cbcSat

theorem decrypt_verified : Verified RISCV64.target decrypt (Proof.Rc2.cbcDecryptContract RISCV64.abi) := by
  refine Verified.of_correct (k := cbcC .decrypt) (cbc_ok .decrypt) decrypt_ct ?_
  sig_implies [Proof.Rc2.cbcDecryptContract, Proof.Rc2.cbcContract, Proof.Rc2.cbcSig, RISCV64.abi,
    RISCV64.argRegs, cbcC]
    [cbcSat] using cbcSat

end VG.Proof.Rc2.RISCV64.Cbc
