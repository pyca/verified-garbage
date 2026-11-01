module
public import VerifiedGarbage.Proof.Sm4.AArch64.Ecb
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Depth

import VerifiedGarbage.Proof.Sm4.AArch64.Verified
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sm4.AArch64.CryptSum
import VerifiedGarbage.Proof.Sm4.AArch64.LayersLit
meta import VerifiedGarbage.Proof.Sm4.AArch64.Ecb
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.Depth
meta import VerifiedGarbage.Proof.Sm4.AArch64.Verified
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Sm4.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.AArch64.CryptSum
meta import VerifiedGarbage.Proof.Sm4.AArch64.LayersLit
public import VerifiedGarbage.Proof.Sm4.Contract

/-!
# SM4 ECB on AArch64: the functions of one direction

`vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt` (`ecbCall`) set `decrypt` and
call `vg_sm4_ecb` (`ecbAny_framed`), in a frame saving `x30`: 16 bytes of
stack below the callee's 3168. `ecbCall_verified` proves them against the
ECB contracts with `stack = 3184`.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.Impl.Sm4.AArch64
open VG.Proof.Sm4 (specDirA)

/-- `vg_sm4_ecb`'s code: `ecbAny` with its working space on the stack. -/
abbrev ecbAnyFramed : Prog isa := Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x4 396 ecbAny

/-- The ECB contracts with `stack = 3184`, as `sig_pre` evaluates them. -/
def ecbCallAArch64 (dir : Dir) : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat * 16⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 3184, 3184⟩
    3184 ≤ s.sp.toNat ∧ s.rd = [sched] ∧ s.wr = [data] ∧ sched.Disjoint data ∧ stk.Disjoint sched ∧
      stk.Disjoint data ∧ (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat * 16 ≤ 2 ^ 64
  post s s' :=
    Spec.Sm4.blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem (s.gpr .x0)) (specDirA dir)
        (Spec.Sm4.blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2

/-- The value `ecbCall dir` sets `decrypt` to. -/
def dirFlag : Dir → Nat
  | .encrypt => 0
  | .decrypt => 1

theorem ecbCall_eq (dir : Dir) :
    ecbCall dir ecbAnyFramed = .frame (.push .x30)
      (.seq (.block [.movz .x .x3 (BitVec.ofNat 16 (dirFlag dir)) 0]) (.call "vg_sm4_ecb" ecbAnyFramed))
      (.pop .x30) := by
  cases dir <;> rfl

theorem specDirA_dirFlag (dir : Dir) :
    specDirA dir = Proof.Sm4.directionOf (BitVec.ofNat 64 (dirFlag dir)).toNat := by
  cases dir <;> rfl

theorem movz_sp_ok (s : State) (d : Reg) {v : Nat} (hv : v < 65536) :
    ∃ s', runBlock isa [.movz .x d (BitVec.ofNat 16 v) 0] s = some s' ∧ s'.gpr d = BitVec.ofNat 64 v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ s'.v = s.v := by
  refine ⟨s.write .x d ((BitVec.ofNat 16 v).setWidth 64 <<< (16 * 0)), ?_, ?_,
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [runBlock_cons]; rfl
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega

theorem ecbCall_depth (dir : Dir) :
    16 * (Code.seq (.block [.movz .x .x3 (BitVec.ofNat 16 (dirFlag dir)) 0])
      (.call "vg_sm4_ecb" ecbAnyFramed) : Prog isa).aarch64Depth + 16 < 2 ^ 64 := by
  cases dir <;> lit_decide

theorem ecbCall_correct (dir : Dir) (s₀ : State) (hs : (ecbCallAArch64 dir).pre s₀) :
    ∃ t s', Exec isa (ecbCall dir ecbAnyFramed) s₀ t s' ∧ abiPreserved s₀ s' ∧
      (ecbCallAArch64 dir).post s₀ s' := by
  obtain ⟨hsp, hrd, hwr, dKD, dSK, dSD, fitK, fitD⟩ := hs
  have hk : dirFlag dir ≤ 1 := by cases dir <;> decide
  -- The frame's slot and the callee's stack, below the stack the contract reserves.
  have frameSub : Region.Sub ⟨s₀.sp - BitVec.ofNat 64 16, 16⟩ ⟨s₀.sp - BitVec.ofNat 64 3184, 3184⟩ :=
    fun x hx => Offset.below_mono s₀.sp (by decide) (by decide) x hx
  have slotSub : Region.Sub ⟨s₀.sp - BitVec.ofNat 64 16, 8⟩ ⟨s₀.sp - BitVec.ofNat 64 3184, 3184⟩ :=
    fun x hx => frameSub x (Region.sub_prefix (by decide) x hx)
  have spSub : s₀.sp - BitVec.ofNat 64 16 - BitVec.ofNat 64 3168 = s₀.sp - BitVec.ofNat 64 3184 := by
    rw [← Offset.sub_add_eq, BitVec.ofNat_add_ofNat]
  rw [ecbCall_eq]
  refine (WP.frameReg (r := .x30) (s₀ := s₀) (by omega) (fun R hR => ?_) ?_ (ecbCall_depth dir)).elim
    fun t ⟨s', he, hq⟩ => ⟨t, s', he, hq⟩
  · rw [hwr, List.mem_singleton] at hR; subst hR
    exact dSD.sub_left frameSub
  obtain ⟨σ, e₂, x3₂, o₂, m₂, rd₂, wr₂, sp₂, v₂⟩ := movz_sp_ok
    { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) } .x3 (v := dirFlag dir)
    (by omega)
  refine WP.seq (WP.of_runBlock ⟨σ, e₂, ?_⟩)
  have g₂ : ∀ r, r ≠ .x3 → σ.gpr r = s₀.gpr r := fun r h => o₂ r h
  have hsp₂ : σ.sp = s₀.sp - BitVec.ofNat 64 16 := sp₂
  refine WP.callFV (k := Proof.Sm4.ecbDirContract AArch64.abi 3168) ecbAny_framed.1 (rd := s₀.rd) (wr := s₀.wr)
    ?_ (fun _ _ h => by rw [rd₂, wr₂]; exact h) (fun _ _ h => by rw [wr₂]; exact h) ?_ (by lit_decide)
  · have e0 : σ.gpr .x0 = s₀.gpr .x0 := g₂ _ (by decide)
    have e1 : σ.gpr .x1 = s₀.gpr .x1 := g₂ _ (by decide)
    have e2 : σ.gpr .x2 = s₀.gpr .x2 := g₂ _ (by decide)
    sig_pre [Proof.Sm4.ecbDirContract, Proof.Sm4.ecbDirSig, Spec.Sm4.ecbSig, AArch64.abi, AArch64.argRegs]
    simp only [e0, e1, e2, x3₂, hsp₂, spSub]
    refine ⟨?_, hrd, hwr, dKD, dSK.sub_left (Region.sub_prefix (by decide)),
      dSD.sub_left (Region.sub_prefix (by decide)), fitK, fitD, ?_⟩
    · rw [Offset.toNat_sub_ofNat]; omega
    · rw [BitVec.toNat_ofNat]; omega
  · intro s' rd' wr' sp' hf hg hv hpost
    sig_reduce [Proof.Sm4.ecbDirContract, Proof.Sm4.ecbDirSig, Spec.Sm4.ecbSig, AArch64.abi, AArch64.argRegs] at hpost
    have e0 : σ.gpr .x0 = s₀.gpr .x0 := g₂ _ (by decide)
    have e1 : σ.gpr .x1 = s₀.gpr .x1 := g₂ _ (by decide)
    have e2 : σ.gpr .x2 = s₀.gpr .x2 := g₂ _ (by decide)
    rw [e0, e1, e2, x3₂, BitVec.setWidth_eq, BitVec.setWidth_eq] at hpost
    have hfr : Frame [⟨s₀.sp - BitVec.ofNat 64 16, 8⟩] s₀.mem σ.mem := by
      rw [m₂]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hsch : Spec.Sm4.scheduleAt σ.mem (s₀.gpr .x0) = Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .x0) :=
      Proof.Sm4.scheduleAt_frame hfr fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact (dSK.sub_left slotSub).symm
    have hblk : Spec.Sm4.blocksAt σ.mem (s₀.gpr .x1) (s₀.gpr .x2).toNat =
        Spec.Sm4.blocksAt s₀.mem (s₀.gpr .x1) (s₀.gpr .x2).toNat :=
      Proof.Sm4.blocksAt_frame hfr (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact (dSD.sub_left slotSub).symm) (by omega)
    refine ⟨⟨fun r hr => ?_, rfl, fun r hr => (hv r hr).trans (by rw [v₂])⟩, ?_⟩
    · show (s'.write .x .x30 (s₀.gpr .x30)).gpr r = s₀.gpr r
      by_cases h : r = .x30
      · subst h; rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
      · have h3 : r ≠ .x3 := fun h3 => by subst h3; exact absurd hr (by decide)
        rw [RegUpd.gpr_write_of_ne _ _ _ h, hg r hr h, g₂ r h3]
    · show Spec.Sm4.blocksAt s'.mem (s₀.gpr .x1) (s₀.gpr .x2).toNat = _
      rw [hpost, hsch, hblk, specDirA_dirFlag]


theorem ecbCallTaint_agree (dir : Dir) (s₁ s₂ : State) (_ : (ecbCallAArch64 dir).pre s₁)
    (_ : (ecbCallAArch64 dir).pre s₂) (hp : (ecbCallAArch64 dir).pub s₁ s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2]) s₁ s₂ := by
  obtain ⟨hsp, h1, h2, h3⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

theorem ecbCall_ct (dir : Dir) :
    ConstantTime isa (ecbCallAArch64 dir).pre (ecbCallAArch64 dir).pub (ecbCall dir ecbAnyFramed) := by
  cases dir
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) (ecbCallTaint_agree .encrypt)
      (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) (ecbCallTaint_agree .decrypt)
      (by taint_decide)

/-- A state satisfying the ECB functions' precondition with `stack = 3184`:
the schedule at `0x1000`, one block at `0x3000`. -/
def ecbCallSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩]

/-- `vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt`: a call of `vg_sm4_ecb`. -/
theorem ecbCall_verified (dir : Dir) :
    Verified AArch64.target (ecbCall dir ecbAnyFramed) (Spec.Sm4.ecbContract AArch64.abi (specDirA dir) 3184) :=
  Verified.of_correct (ecbCall_correct dir) (ecbCall_ct dir) (by
    cases dir <;>
    sig_implies [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Spec.Sm4.ecbPost, ecbCallAArch64, specDirA,
      AArch64.abi, AArch64.argRegs] [ecbCallSat] using ecbCallSat)

end VG.Proof.Sm4.AArch64
