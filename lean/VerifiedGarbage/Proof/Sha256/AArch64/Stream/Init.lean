module
public import VerifiedGarbage.Impl.Sha256.AArch64.Stream
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Sha256.AArch64.Contract
public import VerifiedGarbage.Proof.Sha256.StateMem
public import VerifiedGarbage.TCB.AArch64.Target

import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Sha256.AArch64.Stream
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Sha256.AArch64.Contract
meta import VerifiedGarbage.Proof.Sha256.StateMem
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MdStream.AArch64.Common
import VerifiedGarbage.Proof.Sha256.AArch64.Compress
meta import VerifiedGarbage.Proof.MdStream.AArch64.Common
meta import VerifiedGarbage.Proof.Sha256.AArch64.Compress

/-!
# Streaming SHA-256 on AArch64: `init`
-/

@[expose] public section

namespace VG.Proof.Sha256.AArch64.Stream

open VG VG.AArch64 VG.Impl.Sha256.AArch64.Stream
open VG.Proof.Sha256.AArch64 (writeState stateAt_writeState contains_offset)
open VG.Proof.MdStream.AArch64 (WP.cons)
open VG.Spec.Sha256 (stateAt H0)

/-- Two pairs of words, as `ldrqTbl` loads them: the vector of the four words. -/
theorem append_pairs (a b c d : BitVec 32) :
    ((d ++ c : BitVec 64) ++ (b ++ a : BitVec 64)) = ofVWords a b c d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofVWords, BitVec.getLsbD_append]
  by_cases h0 : i < 32
  · simp [h0, show i < 64 by omega]
  by_cases h1 : i < 64
  · simp [h0, h1, show i - 32 < 32 by omega]
  by_cases h2 : i < 96
  · simp [h0, h1, show ¬ i - 32 < 32 by omega, show i - 32 - 32 = i - 64 by omega, show i - 64 < 32 by omega]
  · simp [h0, h1, show ¬ i - 32 < 32 by omega, show ¬ i - 32 - 32 < 32 by omega,
      show ¬ i - 64 < 32 by omega, show i - 32 - 32 - 32 = i - 64 - 32 by omega]

variable (iv : Spec.Sha256.HashValue)

/-- Loading sixteen bytes of `iv`'s table, at `x9`. -/
theorem exec_ivld (r : VReg) (off : Nat) (ho : off = 0 ∨ off = 16) {s : State}
    (hx : s.gpr .x9 = s.syms (ivName iv)) :
    exec (.ldrqTbl r .x9 off (ivName iv) (ivTable iv)) s =
      some (s.setV r ((ivTable iv).getD (off / 8 + 1) 0 ++ (ivTable iv).getD (off / 8) 0)) := by
  have hc : s.gpr .x9 = s.syms (ivName iv) ∧ off % 16 = 0 ∧ off < 65536 ∧
      off / 8 + 2 ≤ (ivTable iv).length := ⟨hx, by omega, by omega, by simp [ivTable]; omega⟩
  simp only [exec, ite_eq_left_of_eq_true _ _ (eq_true hc)]

theorem write_iv (m : Mem) (p : Addr) :
    (m.write (p + BitVec.ofNat 64 0) 16 ((ivTable iv).getD (0 / 8 + 1) 0 ++ (ivTable iv).getD (0 / 8) 0)).write
        (p + BitVec.ofNat 64 16) 16 ((ivTable iv).getD (16 / 8 + 1) 0 ++ (ivTable iv).getD (16 / 8) 0) =
      writeState m p iv := by
  have e0 : (ivTable iv).getD (0 / 8 + 1) 0 ++ (ivTable iv).getD (0 / 8) 0 = ofVWords iv[0] iv[1] iv[2] iv[3] :=
    append_pairs _ _ _ _
  have e1 : (ivTable iv).getD (16 / 8 + 1) 0 ++ (ivTable iv).getD (16 / 8) 0 =
      ofVWords iv[4] iv[5] iv[6] iv[7] :=
    append_pairs _ _ _ _
  rw [e0, e1, write16, write16]
  simp only [writeState, Offset.add_add, Nat.reduceMul, Nat.reduceAdd]

theorem initQ_correct {s₀ : State} (hp : (Proof.Sha256.initAArch64 iv).pre s₀) :
    WP isa (initQ iv) s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Sha256.initAArch64 iv).post s₀ s' := by
  apply WP.withPreservedV (hc := by rfl)
  obtain ⟨-, hwr⟩ := hp
  have o : ∀ d, d + 16 ≤ 32 → InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 d) 16 :=
    fun d hd => ⟨⟨s₀.gpr .x0, 96⟩, by simp [hwr], contains_offset (by omega) (by omega)⟩
  have hx : (s₀.write .x .x9 (s₀.syms (ivName iv))).gpr .x9 =
      (s₀.write .x .x9 (s₀.syms (ivName iv))).syms (ivName iv) := RegUpd.gpr_write_self _ _ _ _
  refine WP.block_cons_iff.mpr ⟨_, exec_adrSym, WP.block_cons_iff.mpr ⟨_, exec_ivld iv .v0 0 (.inl rfl) hx,
    WP.block_cons_iff.mpr ⟨_, exec_ivld iv .v1 16 (.inr rfl) hx, ?_⟩⟩⟩
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, runBlock_cons, runStep_some,
    runBlock_nil, exec, addr, State.store, Option.bind_some, and_self, isa, RegUpd.gpr_setV,
    RegUpd.v_setV, RegUpd.wr_setV, RegUpd.gpr_write_of_ne _ _ _ (show Reg.x0 ≠ .x9 by decide),
    RegUpd.wr_write, o 0 (by decide), o 16 (by decide), reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, rfl⟩, ?_⟩
  · have : r ≠ .x9 := by rintro rfl; simp [preserved] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ this
  · show Spec.Sha256.ReprFrom iv _ (s₀.gpr .x0) []
    rw [write_iv]
    exact Proof.Sha256.Stream.reprFrom_nil (stateAt_writeState _ _ _)

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 96⟩]

/-- `initQ iv` is verified, given that the taint analysis, which the
kernel can only run on a literal `iv`, accepts it. -/
theorem initQ_verified {hc} (hct : (taint.check (Taint.ofRegs [.x0]) (initQ iv) hc).isSome = true) :
    Verified AArch64.target (initQ iv) (Proof.Sha256.initAArch64 iv) := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, rfl, rfl⟩⟩
  · obtain ⟨t, s', he, h⟩ := initQ_correct iv hs
    exact ⟨t, s', he, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0]) ?_ hct
    intro s₁ s₂ _ _ h
    refine ⟨h.2, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.1

theorem init_verified : Verified AArch64.target init (Proof.Sha256.initAArch64 H0) :=
  initQ_verified _ (hct := by taint_decide)

theorem init224_verified : Verified AArch64.target init224 (Proof.Sha256.initAArch64 Spec.Sha256.H0_224) :=
  initQ_verified _ (hct := by taint_decide)

end VG.Proof.Sha256.AArch64.Stream
