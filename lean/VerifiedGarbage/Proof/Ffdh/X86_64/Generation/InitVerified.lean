module

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitCorrect
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitCT
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # Verified native parameter-generation initialization -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation

def initPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 128⟩] ∧ (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 128⟩

def initPost (s t : State) : Prop :=
  match Spec.Ffdh.parameterInit (s.gpr .rsi).toNat ((s.gpr .rdx).setWidth 32).toNat with
  | none => ((t.gpr .rax).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .rdi) 4 = List.replicate 4 0
  | some values => ((t.gpr .rax).setWidth 32).toNat = 1 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .rdi) 4 = values.map (BitVec.ofNat 64)

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

private theorem init_values {bits generator : Nat} {values : List Nat}
    (h : Spec.Ffdh.parameterInit bits generator = some values) :
    values = [Spec.Ffdh.parameterAttempts bits, (bits + 7) / 8,
      Spec.Ffdh.parameterEntropy bits, 512 * ((bits + 7) / 8)] := by
  unfold Spec.Ffdh.parameterInit at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

private theorem result_post {s t : State}
    (h : InitPost (s.gpr .rsi).toNat ((s.gpr .rdx).setWidth 32).toNat s.mem (s.gpr .rdi) t) :
    initPost s t := by
  unfold InitPost at h
  unfold initPost
  cases he : Spec.Ffdh.parameterInit (s.gpr .rsi).toNat ((s.gpr .rdx).setWidth 32).toNat with
  | none =>
    simp only [he] at h
    refine ⟨?_, ?_⟩
    · rw [h.1]; rfl
    · rw [h.2]; exact cleared_words _ _
  | some values =>
    simp only [he] at h
    refine ⟨?_, ?_⟩
    · rw [h.1]; rfl
    · rw [h.2, init_values he]
      exact initialized_words _ _ _

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨_, hwr, hroom, hret⟩ := h
  have scr : Scr s (s.gpr .rdi) 128 := Scr.of_mem (by rw [hwr]; simp) hroom
  obtain ⟨tr, t, he, hp, k⟩ := WP.keep [.rax, .rdx, .rcx, .rsi] (init_ok scr rfl) (by decide +kernel)
  have safe : SpSafe init := SpSafe.of_all (Code.all_of_allInstrs (by decide +kernel))
  have hd : init.x86_64Depth = 0 := rfl
  have hf := Exec.stackFrame safe he (by rw [hd]; decide)
  rw [hwr, hd] at hf
  have hr : t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
    refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hret
    · exact Offset.base_disjoint_below _ (by decide)
  refine ⟨tr, t, he, abiPreserved_of_exec (by decide +kernel) he ⟨?_, hr⟩, result_post hp⟩
  intro r hr
  exact k.gpr (by revert r; decide)

private def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 512 | .rdx => 2 | .rsp => 0x3000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩]

theorem init_verified : Verified target init (Spec.Ffdh.parameterInitContract abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp h₁ h₂
    exact init_constantTime s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hp h₁ h₂
  · sig_implies [Spec.Ffdh.parameterInitContract, Spec.Ffdh.parameterInitSig,
      initContract, initPre, initPost, initPub, abi, argRegs] [initSat] using initSat

end VG.Proof.Ffdh.X86_64.Generation
