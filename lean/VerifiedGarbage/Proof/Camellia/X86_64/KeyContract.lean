import VerifiedGarbage.Impl.Camellia.X86_64.ExpandKey
import VerifiedGarbage.Spec.Camellia.Contract
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono

/-!
# The Camellia key schedule on x86-64: contract and constant time

`expandKeyX86_64`: `expandKey` with its working space at `rcx`
(`scratch`), as the frame calls it. `expandKey_ct`: it is constant time,
by the taint analysis: the pointers, the key's length and the stack
pointer are public, and so is everything the code computes from them,
which it keeps in registers or public slots (the key's length, at
`dataSlot`); the key's words, and everything computed from them, are
secret.
-/

namespace VG.Proof.Camellia

open VG VG.X86_64 VG.Impl.Camellia.X86_64

/-- The key schedule on x86-64 with its working space at `rcx`. -/
def expandKeyX86_64 : Contract X86_64.isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let sched : Region := ⟨s.gpr .rdx, 272⟩
    let scratch : Region := ⟨s.gpr .rcx, 8 * slots⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧ key.Disjoint sched ∧ key.Disjoint scratch ∧
      sched.Disjoint scratch ∧ ret.Disjoint sched ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 272 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 8 * slots ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 16 ∨ (s.gpr .rsi).toNat = 24 ∨ (s.gpr .rsi).toNat = 32)
  post s s' :=
    Spec.Camellia.bytesAt s'.mem (s.gpr .rdx)
        (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds (s.gpr .rsi).toNat)) =
      Spec.Camellia.scheduleBytes
        (Spec.Camellia.expandKey (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat))
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Camellia

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.Impl.Camellia.X86_64

def expandKeyTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .rsp], flags := false,
    lens := [272, 8 * slots], bases := [(.rdx, 0, 0), (.rcx, 1, 0)] }

theorem expandKeyTaint_wf (s : State) (hs : expandKeyX86_64.pre s) : Taint.Wf expandKeyTaint s := by
  obtain ⟨_, hwr, _, _, dSS, _, _, _, fitS, fitB, _⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 272 ≤ 272; omega)
        (List.Forall₂.cons (by change 8 * slots ≤ 8 * slots; omega) List.Forall₂.nil)
    · exact List.Pairwise.cons
        (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dSS)
        (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · change 272 ≤ 2 ^ 64; omega
      · change 8 * slots ≤ 2 ^ 64; omega
  · intro p hp
    simp only [expandKeyTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · unfold Taint.region
      rw [hwr]
      change s.gpr .rdx = s.gpr .rdx + (0 : BitVec 64)
      exact (BitVec.add_zero _).symm
    · unfold Taint.region
      rw [hwr]
      change s.gpr .rcx = s.gpr .rcx + (0 : BitVec 64)
      exact (BitVec.add_zero _).symm

theorem expandKeyTaint_agree (s t : State) (hs : expandKeyX86_64.pre s) (ht : expandKeyX86_64.pre t)
    (hp : expandKeyX86_64.pub s t) : X86_64.Taint.Agree expandKeyTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hp
  refine ⟨?_, ?_, expandKeyTaint_wf s hs, expandKeyTaint_wf t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩
  · constructor
    · intro r hr
      simp only [expandKeyTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [p1, p2, p3, p4, p5]
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.2.1, ht.2.1, p3, p4]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [expandKeyTaint, RegSet.not_mem_empty] at hr

theorem expandKey_ct : ConstantTime isa expandKeyX86_64.pre expandKeyX86_64.pub expandKey :=
  VG.Taint.constantTime (A := taint) expandKeyTaint expandKeyTaint_agree (by taint_decide)

end VG.Proof.Camellia.X86_64
