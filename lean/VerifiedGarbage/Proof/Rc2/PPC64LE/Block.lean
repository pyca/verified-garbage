module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Cipher
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Rc2.PPC64LE.BlockIO
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Cipher
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.BlockIO
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Lit

/-! # Verified RC2 block encryption and decryption on PPC64LE -/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

/-- The block contract as the code sees it. -/
def blockC (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .r3, 128⟩] ∧ s.wr = [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 256⟩]
  post s s' := Spec.Rc2.blockAt s'.mem (s.gpr .r4) =
    cipher d (Spec.Rc2.scheduleAt s.mem (s.gpr .r3)) (Spec.Rc2.blockAt s.mem (s.gpr .r4))
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.sp = s₂.sp

theorem block_wp (d : Spec.Rc2.Direction) (s : State) (hs : (blockC d).pre s) :
    WP isa (blockCode d) s fun s' => (blockC d).post s s' := by
  obtain ⟨hrd, hwr⟩ := hs
  unfold blockCode
  apply WP.seq
  refine WP.mono (blockLoad_run s (by rw [hwr]; exact ⟨_, by simp, Region.contains_self _ _⟩))
    fun t₁ ⟨H₁, m₁, k₁⟩ => ?_
  apply WP.seq
  have E : KeyEnv (s.gpr .r3) t₁ := ⟨k₁.gpr (by decide), fun o n hn => by
    rw [k₁.2.1, k₁.2.2, hrd]; exact ⟨_, by simp, Offset.contains_base _ hn (by omega)⟩⟩
  refine WP.mono (rounds_runsTo d t₁ E rfl _ H₁) fun t₂ ⟨H₂, m₂, k₂⟩ => ?_
  have p4 : t₂.gpr .r4 = s.gpr .r4 := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (blockStore_run t₂ H₂ (by rw [p4, k₂.2.2, k₁.2.2, hwr]; exact ⟨_, by simp, Region.contains_self _ _⟩))
    fun t₃ ⟨m₃, _⟩ => ?_
  change Spec.Rc2.blockAt t₃.mem (s.gpr .r4) = _
  rw [m₃, p4, m₂, Proof.Rc2.blockAt_write64, cipher_rounds, m₁]

/-- The registers the block functions write. -/
def blockRegs : List Reg := [.r0, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem block_ok (d : Spec.Rc2.Direction) (hw : writesOnly blockRegs (blockCode d) = true)
    (hn : (blockCode d).noCalls = true) (hl : (instrs (blockCode d)).all (fun i => !i.writesLr) = true)
    (s : State) (hs : (blockC d).pre s) :
    ∃ t s', Exec isa (blockCode d) s t s' ∧ abiPreserved s s' ∧ (blockC d).post s s' := by
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep blockRegs (block_wp d s hs) hw hn
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) hn hl, hp⟩

end VG.Proof.Rc2.PPC64LE
