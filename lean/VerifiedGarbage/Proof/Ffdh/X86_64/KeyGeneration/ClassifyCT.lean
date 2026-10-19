module

public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.AttemptCT
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.LeafCT
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Classify
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Rejects
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Live
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.AttemptCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.LeafCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Classify
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Rejects
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Live
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # The attempt's classification branches on its status alone -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.KeyGeneration
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

/-- The status of the attempt at a point: the first still to come. -/
def KeyPoint.status (q : KeyPoint) : Nat := q.statuses.head?.getD 0

/-- The attempt's status at a point, for each run's tape. -/
theorem attempt_status {q : KeyPoint} {original s : State}
    (h : KeyLive q.inputs original q.used q.keys q.scalars s)
    (hst : (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses)
    (hk : q.keys ≠ 0) (hs : q.scalars ≠ 0) (hr : q.used + q.inputs.len ≤ q.inputs.randLen) :
    attemptStatus q.inputs.a q.inputs.len ((keyRand original).drop q.used) = q.status := by
  have hlen : (keyRand original).length = q.inputs.randLen := by
    rw [← h.random]; simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have hhead := keyTail_statuses_head (a := q.inputs.a) (len := q.inputs.len)
    (rand := keyRand original) (used := q.used) hk hs (by rw [hlen]; omega)
  rw [hst] at hhead
  simp only [KeyPoint.status, hhead, Option.getD_some]

theorem key_attempted_pins : Pins KeyAttempted [.r12, .rsp] := by
  intro q s t ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [h₁.r12.trans h₂.r12.symm, h₁.rsp.trans h₂.rsp.symm]

/-- The status in `rax`, compared with `k`. -/
def KeyGuard (k : Nat) (q : KeyPoint) (t : State) : Prop :=
  KeyAny q.inputs t ∧ t.gpr .rax = BitVec.ofNat 64 q.status ∧
    eval .e t = some (decide (q.status = k)) ∧ q.status < 4

private theorem first_ready (q : KeyPoint) (s : State) (h : KeyAttempted q s) :
    WP isa (.block (([.mov32 .rax (.reg .rax)] : List Instr) ++ advance ++
      ([.alu .cmp .rax (.imm 1)] : List Instr))) s
      (KeyGuard 1 q) := by
  obtain ⟨original, h, hst, hk, hs, hr, hp⟩ := h
  have he := attempt_status h hst hk hs hr
  have h4 : q.status < 4 := by
    rw [← he]
    rcases attemptStatus_cases q.inputs.a q.inputs.len ((keyRand original).drop q.used) with
      h | h | h <;> omega
  refine WP.mono (key_classify_head h hr hp) fun t ⟨ht, _, hax, hev⟩ => ?_
  exact ⟨⟨original, _, _, _, ht⟩, by rw [hax, he], by rw [hev, he], h4⟩

private theorem next_ready (j : Nat) (n : BitVec 32) (k : Nat)
    (hn : BitVec.signExtend 64 n = BitVec.ofNat 64 k) (hk : k < 2 ^ 64) (q : KeyPoint) (s : State)
    (h : KeyGuard j q s ∧ eval .e s = some false) :
    WP isa (.block [.alu .cmp .rax (.imm n)]) s (KeyGuard k q) := by
  obtain ⟨⟨⟨o, u, a, c, hl⟩, ha, _, h4⟩, _⟩ := h
  refine WP.mono (rax_guard ha (by omega) n k hn hk) fun t ⟨⟨he, hm, hr⟩, kt⟩ => ?_
  exact ⟨⟨o, u, a, c, hl.keep kt hm (by decide)⟩, hr.trans ha, he, h4⟩

private theorem leaf {k : Nat} {b : Bool} {c : Prog isa} (hc : RelCT isa (Two KeyAny) c fun _ _ => True) :
    RelCT isa (Two fun q s => KeyGuard k q s ∧ eval .e s = some b) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q.inputs, h₁.1.1, h₂.1.1⟩) fun _ _ h => h

private theorem guard_eq (k : Nat) (q : KeyPoint) (s₁ s₂ : State) (h₁ : KeyGuard k q s₁)
    (h₂ : KeyGuard k q s₂) : eval .e s₁ = eval .e s₂ :=
  h₁.2.2.1.trans h₂.2.2.1.symm

private theorem no_pins (k : Nat) : Pins (KeyGuard k) [] := fun _ _ _ _ _ _ h => by cases h

theorem key_classify_ct : RelCT isa (Two KeyAttempted) classify (fun _ _ => True) := by
  unfold classify
  refine RelCT.seq (two_piece [.r12, .rsp] key_attempted_pins (by taint_decide) first_ready) ?_
  refine two_ite (guard_eq 1) (leaf key_accepted_ct) ?_
  refine RelCT.seq (two_post ((two_taint [] (no_pins 1) (by taint_decide)).mono
    (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.1, h₂.1⟩) fun _ _ h => h)
    (next_ready 1 2 2 (by decide) (by decide))) ?_
  refine two_ite (guard_eq 2) (leaf key_rejected_scalar_ct) ?_
  refine RelCT.seq (two_post ((two_taint [] (no_pins 2) (by taint_decide)).mono
    (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.1, h₂.1⟩) fun _ _ h => h)
    (next_ready 2 3 3 (by decide) (by decide))) ?_
  exact two_ite (guard_eq 3) (leaf key_rejected_public_ct) (leaf key_exhausted_ct)

end VG.Proof.Ffdh.X86_64.KeyGeneration
