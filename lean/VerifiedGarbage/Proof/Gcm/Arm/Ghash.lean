module

public import VerifiedGarbage.Impl.Gcm.Arm
public import VerifiedGarbage.Proof.Gcm.Spec
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Gcm.Arm.Lit
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Gcm.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-!
# GHASH on ARM: the contract

Untrusted: everything here is checked by Lean. What callers need of
`vg_ghash`; that it meets its contract is `GhashLaw`, whose instance is in
`Proof/Gcm/Arm/Law.lean`, so that its callers need not import the proof.
-/

@[expose] public section

namespace VG.Proof.Gcm

open Spec.Gcm

open VG.Arm in
/-- ARM contract for `vg_ghash(h: *const [u8; 16], y: *mut [u8; 16], data:
*const [u8; 16], n: usize, scratch: *mut [u32; 64])`, `scratch` on the stack:
replaces the block `Y` at `y` with `GHASH_H` continued from `Y` over the `n`
blocks at `data`, where `H` is the block at `h`. The pointers and `n` are
public; `H`, `Y` and the data are secret. -/
def ghashArm : Contract Arm.isa where
  pre s :=
    let h : Region := ⟨State.addr (s.gpr .r0), 16⟩
    let y : Region := ⟨State.addr (s.gpr .r1), 16⟩
    let data : Region := ⟨State.addr (s.gpr .r2), 16 * (s.gpr .r3).toNat⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 256⟩
    s.rd = [h, data, args] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧ data.Disjoint scratch ∧
    y.Disjoint args ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + 16 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 16 ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + 16 * (s.gpr .r3).toNat ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 256 ≤ 2 ^ 32 ∧
    s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' :=
    blockAt s'.mem (State.addr (s.gpr .r1)) =
      ghashFrom (blockAt s.mem (State.addr (s.gpr .r0))) (blockAt s.mem (State.addr (s.gpr .r1)))
        (blocksAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Gcm

namespace VG.Proof.Gcm.Arm

open VG VG.Arm
open VG.Spec.Gcm (Block blockAt)

/-- `vg_ghash` meets its contract. -/
class GhashLaw : Prop where
  ok : ∀ s, ghashArm.pre s → ∃ t s', Exec isa Impl.Gcm.Arm.ghash s t s' ∧ abiPreserved s s' ∧ ghashArm.post s s'

theorem ghash_correct [GhashLaw] (s : State) (hs : ghashArm.pre s) :
    ∃ t s', Exec isa Impl.Gcm.Arm.ghash s t s' ∧ abiPreserved s s' ∧ ghashArm.post s s' := GhashLaw.ok s hs

/-- Four words, the first the most significant. -/
abbrev w4 (a b c d : BitVec 32) : BitVec 128 := a ++ b ++ c ++ d

theorem bytes8 (a b c d e f g h : BitVec 8) :
    (a ++ b ++ c ++ d ++ e ++ f ++ g ++ h : BitVec 64) =
      ((a ++ b ++ c ++ d : BitVec 32) ++ (e ++ f ++ g ++ h : BitVec 32) : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_append]
  omega

/-- The two halves of a block's words. -/
theorem w4_eq (a b c d : BitVec 32) : w4 a b c d = ((a ++ b : BitVec 64) ++ (c ++ d : BitVec 64) : BitVec 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [w4, toNat_append]
  omega

/-- Four loads and byte reversals read a block. -/
theorem blockAt_rev (m : Mem) (p : Addr) :
    blockAt m p = w4 (rev (m.readW p 32)) (rev (m.readW (p + BitVec.ofNat 64 4) 32))
      (rev (m.readW (p + BitVec.ofNat 64 8) 32)) (rev (m.readW (p + BitVec.ofNat 64 12) 32)) := by
  have h : Spec.Aes.bytesAt m p 16 =
      [m (p + BitVec.ofNat 64 0), m (p + BitVec.ofNat 64 1), m (p + BitVec.ofNat 64 2), m (p + BitVec.ofNat 64 3),
        m (p + BitVec.ofNat 64 4), m (p + BitVec.ofNat 64 5), m (p + BitVec.ofNat 64 6), m (p + BitVec.ofNat 64 7),
        m (p + BitVec.ofNat 64 8), m (p + BitVec.ofNat 64 9), m (p + BitVec.ofNat 64 10), m (p + BitVec.ofNat 64 11),
        m (p + BitVec.ofNat 64 12), m (p + BitVec.ofNat 64 13), m (p + BitVec.ofNat 64 14),
        m (p + BitVec.ofNat 64 15)] := rfl
  have e : ∀ j : Nat, p + BitVec.ofNat 64 j + 1 = p + BitVec.ofNat 64 (j + 1) := fun j => Offset.add_add p j 1
  have e0 : p = p + BitVec.ofNat 64 0 := (BitVec.add_zero p).symm
  rw [show m.readW p 32 = m.readW (p + BitVec.ofNat 64 0) 32 from congrArg (fun q => m.readW q 32) e0]
  simp only [rev_readW, e, Nat.reduceAdd]
  rw [blockAt, h, ofBytes_16]
  rw [w4_eq, bytes8, bytes8]

/-- The stack argument is the base of `scratch`, writable region 1, and `r1`
is `y`'s, region 0. -/
def ctTaint : VG.Arm.Taint.T :=
  { regs := RegSet.ofList [.r0, .r1, .r2, .r3], flags := false, lens := [16, 256], bases := [(.r1, 0)],
    argLen := 4, argBases := [(0, 1)] }

theorem ghash_ct : ConstantTime isa ghashArm.pre ghashArm.pub Impl.Gcm.Arm.ghash := by
  refine VG.Taint.constantTime (A := taint) ctTaint ?_ (by taint_decide)
  intro s₁ s₂ h₁ h₂ ⟨hsp, h0, h1, h2, h3, ha⟩
  have hwf : ∀ s : State, ghashArm.pre s → VG.Arm.Taint.Wf ctTaint s := by
    intro s ⟨_, hw, _, _, _, ys, _, ya, sa, _, hy, _, hs, hp⟩
    have e0 : s.sp + BitVec.ofNat 32 (4 * 0) = s.sp := BitVec.add_zero _
    simp only [stackArgAddr, e0] at ya sa
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, ?_, fun _ => ⟨hp, ?_⟩, ?_⟩
    · rw [hw]; exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
    · rw [hw]; simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil, false_implies,
        implies_true, List.Pairwise.nil, and_true]
      exact ys
    · rw [hw]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show (BitVec.setWidth 64 _).toNat + 16 ≤ _
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_using [hy])]; exact hy
      · show (BitVec.setWidth 64 _).toNat + 256 ≤ _
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_using [hs])]; exact hs
    · intro p hp
      simp only [ctTaint, List.mem_singleton] at hp
      subst hp
      simp only [VG.Arm.Taint.region, hw, List.getD_cons_zero]
    · rw [hw]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ya.symm
      · exact sa.symm
    · intro p hp
      simp only [ctTaint, List.mem_singleton] at hp
      subst hp
      refine ⟨Nat.le_refl _, ?_⟩
      simp only [VG.Arm.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
      rfl
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, hwf _ h₁, hwf _ h₂, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => hsp, ?_⟩
  · have hr := RegSet.mem_ofList.mp hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, h1, ha]
  · refine argMem_of (j := 1) hsp h₁.2.2.2.2.2.2.2.2.2.2.2.2.2 fun i hi => ?_
    obtain rfl : i = 0 := by omega
    exact ha

end VG.Proof.Gcm.Arm
