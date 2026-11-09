module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckPre
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Call
public import VerifiedGarbage.Proof.Dsa.Contract

/-! # The wrapper's initial domain-checking call -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom.CheckCall
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

def callWrites (s₀ : State) : List Region := callWr s₀ ++ [⟨rCall s₀, 112⟩]

def callResult (s₀ t : State) : Bool :=
  Spec.Dsa.checkParametersBytes (X86.arg s₀ 5).toNat (X86.arg s₀ 6).toNat
    (Spec.Rsa.bytesAt t.mem (argumentPointer s₀ 3) (X86.arg s₀ 4).toNat)

theorem call_covers {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) :
    Covers (callRd s₀ ++ callWr s₀) (t.rd ++ t.wr) ∧ Covers (callWr s₀) t.wr := by
  have hF : (⟨rBase s₀, KeyRandom.frameBytes⟩ : Region) ∈ t.wr := by rw [h.wr]; exact List.mem_cons_self
  have hS : argRegion s₀ 9 ((X86.arg s₀ 10).toNat * 8) ∈ t.wr := by rw [h.wr, A.wr]; simp
  have hK : argRegion s₀ 3 (X86.arg s₀ 4).toNat ∈ t.rd := by rw [h.rd, A.rd]; simp
  have hw : ∀ r ∈ callWr s₀, ∃ r' ∈ t.wr, ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hS, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, hF, 0, (BitVec.add_zero _).symm, by unfold KeyRandom.frameBytes; simp⟩
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub hw⟩
  rcases List.mem_append.mp hr with hr | hr
  · obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_append_left _ hK, 0, (BitVec.add_zero _).symm, by simp⟩
  · obtain ⟨r', hr', o, ho⟩ := hw r hr
    exact ⟨r', List.mem_append_right _ hr', o, ho⟩

end VG.Proof.Dsa.X86.KeyRandom.CheckCall
