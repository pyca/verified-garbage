module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallPre
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Calling the key derivation (x86)

`call_ok` runs the call of a verified `vg_dsa_derive_key` with the
arguments `callArgs` stored: it returns the callee's status, writes its
result to `out`, and changes memory only in `out`, `scratch`, the frame's
argument words and the stack below the frame.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

/-- Where the call may write. -/
def callWrites (s₀ : State) : List Region := callWr s₀ ++ [⟨rCall s₀, 112⟩]

/-- What the callee returns, from the bytes of the state `t` it is called in. -/
def callResult (s₀ t : State) : Option (List Byte) :=
  Spec.Dsa.deriveKeyBytes (X86.arg s₀ 5).toNat (X86.arg s₀ 6).toNat
    (Spec.Rsa.bytesAt t.mem (argumentPointer s₀ 3) (X86.arg s₀ 4).toNat)
    (Spec.Rsa.bytesAt t.mem (off (rLow s₀) 112) (X86.arg s₀ 6).toNat)

theorem rBytes_frame {m m' : Mem} {p : Addr} {n : Nat} {rs : List Region}
    (frame : Frame rs m m') (sep : ∀ r ∈ rs, (Region.mk p n).Disjoint r) (bound : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  exact frame.bytes sep bound (List.mem_range.mp hi)

theorem call_covers {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) :
    Covers (callRd s₀ ++ callWr s₀) (t.rd ++ t.wr) ∧ Covers (callWr s₀) t.wr := by
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hF : (⟨rBase s₀, KeyRandom.frameBytes⟩ : Region) ∈ t.wr := by rw [h.wr]; exact List.mem_cons_self
  have hO : argRegion s₀ 0 (X86.arg s₀ 1).toNat ∈ t.wr := by rw [h.wr, A.wr]; simp
  have hS : argRegion s₀ 9 ((X86.arg s₀ 10).toNat * 8) ∈ t.wr := by rw [h.wr, A.wr]; simp
  have hK : argRegion s₀ 3 (X86.arg s₀ 4).toNat ∈ t.rd := by rw [h.rd, A.rd]; simp
  have hw : ∀ r ∈ callWr s₀, ∃ r' ∈ t.wr, ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, hO, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, hS, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, hF, 0, (BitVec.add_zero _).symm, by unfold KeyRandom.frameBytes; simp⟩
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub hw⟩
  rcases List.mem_append.mp hr with hr | hr
  · simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_append_left _ hK, 0, (BitVec.add_zero _).symm, by simp⟩
    · refine ⟨_, List.mem_append_right _ hF, 88, ?_, ?_⟩
      · show off (rLow s₀) 112 = off (rLow s₀) 24 + BitVec.ofNat 64 88
        rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      · show 88 + (X86.arg s₀ 6).toNat ≤ KeyRandom.frameBytes
        unfold KeyRandom.frameBytes; omega
  · obtain ⟨r', hr', o, ho⟩ := hw r hr
    exact ⟨r', List.mem_append_right _ hr', o, ho⟩

end VG.Proof.Dsa.X86.KeyRandom
