module

-- separate module: the contract of the tables' own function, for any caller of a table of `MdHash`, not RSASSA-PSS's alone

public import VerifiedGarbage.Impl.MdHashTable.Arm
public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Words
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-!
# The digest of a hash value on ARMv7

`digestK H`: the contract of `digest out` (`Impl/MdHashTable/Arm.lean`) for
a hash function `H` whose digest code is `out` (`OutOk`): it writes
`H.digest` of the hash value at `r0` to `r1`, keeping every register the
calling convention preserves (`digest_ok`).
-/

@[expose] public section

namespace VG.Proof.MdHashTable.Arm

open VG VG.Arm VG.Proof.MdStream VG.Proof.Pbkdf2.Md.Arm
open VG.Impl.MdHashTable.Arm (digest)
open VG.Arm.RegUpd

variable {B N L : Nat} (H : Md B N L)

/-- The contract of `digest(value = r0, out = r1)`: the `N` bytes of the
hash value readable, the `N` bytes of `out` writable, apart; `out` then
holds the digest of the hash value. -/
def digestK : Contract isa where
  pre s :=
    s.rd = [⟨State.addr (s.gpr .r0), N⟩] ∧ s.wr = [⟨State.addr (s.gpr .r1), N⟩] ∧
      (s.gpr .r0).toNat + N ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + N ≤ 2 ^ 32 ∧
      Region.Disjoint ⟨State.addr (s.gpr .r0), N⟩ ⟨State.addr (s.gpr .r1), N⟩
  post s s' := s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr (s.gpr .r1))
    (H.digest (H.stateAt s.mem (State.addr (s.gpr .r0))))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1

variable {H} {out : List Instr}

theorem digest_ok (ho : OutOk H out) {s : State} (hpre : (digestK H).pre s) :
    ∃ t s', Exec isa (digest out) s t s' ∧ abiPreserved s s' ∧ (digestK H).post s s' := by
  obtain ⟨hrd, hwr, f0, f1, hd⟩ := hpre
  refine WP.mono (Q := fun s' => abiPreserved s s' ∧ (digestK H).post s s') ?_ fun _ h => h
  unfold digest
  rw [WP.block_append_iff, WP.block_append_iff]
  let t := (((s.setReg .r2 (s.gpr .r6)).setReg .r3 (s.gpr .r9)).setReg .r12 (s.gpr .r10)).setReg .r6 (s.gpr .r1)
  refine WP.mono (Q := fun u => u = t) ?_ fun u hu => ?_
  · apply WP.of_runBlock
    simp [runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, gpr_setReg, t]
  subst hu
  have e0 : t.gpr .r0 = s.gpr .r0 := by simp [t, gpr_setReg]
  have e6 : t.gpr .r6 = s.gpr .r1 := by simp [t, gpr_setReg]
  refine WP.mono (ho t (by rw [e0]; exact f0) (by rw [e6]; exact f1)
    (by rw [e0]; exact ⟨_, List.mem_append_left _ (by rw [show t.rd = s.rd from rfl, hrd]; exact List.mem_singleton_self _),
      Region.contains_self _ _⟩)
    (by rw [e6]; exact ⟨_, by rw [show t.wr = s.wr from rfl, hwr]; exact List.mem_singleton_self _,
      Region.contains_self _ _⟩)
    (by rw [e0, e6]; exact hd)) fun u ⟨hg, _, _, hsp, hm⟩ => ?_
  refine WP.mono (Q := fun v => v = ((u.setReg .r6 (u.gpr .r2)).setReg .r9 (u.gpr .r3)).setReg .r10 (u.gpr .r12))
    (by apply WP.of_runBlock; simp [runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, gpr_setReg]) fun v hv => ?_
  subst hv
  have k : ∀ r, r ≠ .r9 → r ≠ .r10 → u.gpr r = t.gpr r := hg
  refine ⟨⟨fun r hr => ?_, by simp only [sp_setReg, hsp]; rfl⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gpr_setReg, k, t]
  · show (_ : State).mem = _
    rw [mem_setReg, mem_setReg, mem_setReg, hm, e0, e6]; rfl

theorem digest_ct (hc : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1]) (digest out) hc).isSome = true) :
    ConstantTime isa (digestK H).pre (digestK H).pub (digest out) :=
  VG.Taint.constantTime_of_exists _ (fun _ _ _ _ hp => VG.Arm.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.1
    · exact hp.2) hc

end VG.Proof.MdHashTable.Arm
