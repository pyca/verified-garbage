module

public import VerifiedGarbage.Impl.AesGcm.Arm.Contiguous
public import VerifiedGarbage.Proof.AesGcm.Arm.Args
public import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.AesGcm.Arm.Run
meta import VerifiedGarbage.Proof.AesGcm.Arm.Run

/-! The contiguous payload takes both pointers from the same fixed stack layout. -/

@[expose] public section
namespace VG.Proof.AesGcm.Arm.Contiguous

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Impl.AesGcm.Arm.Contiguous (cryptArgs)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

theorem cryptArgs_run {b s : State} (argsKept : ArgsKeep 7 b s)
    (fit : b.sp.toNat + 4 * 7 ≤ 2 ^ 32) (readable : args b 7 ∈ b.rd) :
    ∃ t, runBlock isa cryptArgs s = some t ∧
      t.gpr .r4 = arg b 5 ∧ t.gpr .r5 = arg b 3 ∧ t.gpr .r6 = arg b 2 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → t.gpr r = s.gpr r) ∧ Keeps s t := by
  obtain ⟨a5, v5⟩ := argsKept.at fit readable 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨a3, v3⟩ := argsKept.at fit readable 3 (by decide) (show 4 * 3 = 12 from rfl)
  obtain ⟨a2, v2⟩ := argsKept.at fit readable 2 (by decide) (show 4 * 2 = 8 from rfl)
  refine ⟨_, by simp only [cryptArgs]; arun [a5, v5, a3, v3, a2, v2], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r x y z; simp [gpr_setReg, x, y, z]
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem initial {s : State} {c st w sp k7 k8 src dst : BitVec 32} {n : Nat} (icb : Block)
    (env : Env c st w sp k7 k8 s) (rounds : k8.toNat = 10 ∨ k8.toNat = 12 ∨ k8.toNat = 14)
    (rs : s.gpr .r4 = src) (rn : s.gpr .r5 = BitVec.ofNat 32 n) (rt : s.gpr .r6 = dst)
    (readable : DataOk st w sp s src n) (writable : DataW c st w sp k7 k8 s dst n)
    (mode : CrMode true c st w sp src dst n) :
    CrMidG true c st w sp k7 k8 k8.toNat icb 0 src dst n s.mem 0 s :=
  ⟨env, Nat.zero_le _, by simpa using rs, by simpa using rn, by simpa using env.r8,
    rounds, writable, fun hc => by simpa using hc,
    fun _ => by simp [bytesAt]; rfl, by simp, .inr (by decide), Frame.refl _ _,
    fun _ => by simpa using rt, readable, mode⟩

/-- The payload instructions set up the two pointers and encrypt from the
original source memory, including when the destination has the same address. -/
theorem payload_wp {b s : State} {c st w sp k7 : BitVec 32} {icb : Block}
    (layout : Lay c st w sp) (env : Env c st w sp k7 (b.gpr .r1) s)
    (rounds : (b.gpr .r1).toNat = 10 ∨ (b.gpr .r1).toNat = 12 ∨ (b.gpr .r1).toNat = 14)
    (hk : ArgsKeep 7 b s) (fit : b.sp.toNat + 4 * 7 ≤ 2 ^ 32) (rd : args b 7 ∈ b.rd)
    (src : DataOk st w sp s (arg b 5) (arg b 3).toNat)
    (dst : DataW c st w sp k7 (b.gpr .r1) s (arg b 2) (arg b 3).toNat)
    (mode : CrMode true c st w sp (arg b 5) (arg b 2) (arg b 3).toNat) :
    WP isa (.seq (.block cryptArgs) cryptTo) s
      (CrOutG true c st w sp k7 (b.gpr .r1) (b.gpr .r1).toNat icb 0
        (arg b 5) (arg b 2) (arg b 3).toNat s.mem) := by
  obtain ⟨t, run, h4, h5, h6, regs, keep⟩ := cryptArgs_run hk fit rd
  refine WP.seq (WP.of_runBlock ⟨t, run, ?_⟩)
  have et := env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact regs _ (by decide) (by decide) (by decide))
    keep.sp keep.rd keep.wr
  rw [← keep.mem]
  apply cryptTo_ok layout
  exact initial icb et rounds h4 (by simpa using h5) h6 (src.of_eq keep.rd keep.wr)
    (dst.of_eq keep.rd keep.wr) mode

end VG.Proof.AesGcm.Arm.Contiguous
