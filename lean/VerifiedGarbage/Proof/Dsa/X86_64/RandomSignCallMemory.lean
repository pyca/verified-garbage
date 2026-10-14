module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallPre
import VerifiedGarbage.Proof.Framework.Omega

/-! Memory retained across calls to the supplied-nonce signer. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

theorem random_calleeFrame_sub (extra : Nat) (s : State) :
    Region.Sub (below (randomBase s) (extra + 8)) (below (s.gpr .rsp) (extra + 256)) := by
  change Region.Sub ⟨randomBase s - BitVec.ofNat 64 (extra + 8), extra + 8⟩ _
  rw [random_frameBase extra s]
  unfold off
  rw [BitVec.add_sub_cancel]
  exact Region.sub_prefix (by omega)

/-- The callee cannot overwrite any byte of the wrapper's private frame. -/
theorem random_call_frameBytes {extra : Nat} {s : State} {m m' : Mem} (h : RandomSignABI extra s)
    (hf : Frame (randomCallWr s ++ [below (randomBase s) (extra + 8)]) m m') :
    ∀ i < Random.frameBytes, m' (off (randomBase s) i) = m (off (randomBase s) i) := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  intro i hi
  apply hf.bytes (R := ⟨randomBase s, Random.frameBytes⟩) _ (by change 248 ≤ 2 ^ 64; decide) hi
  intro r hr
  simp only [randomCallWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.stackOut.sub_left (random_frame_sub h)
  · exact h.stackScratch.sub_left (random_frame_sub h)
  · exact Offset.base_disjoint_below _ (by unfold Random.frameBytes; omega)

/-- An input disjoint from the output, scratch, and reserved stack is retained. -/
theorem random_call_inputBytes {extra : Nat} {s : State} {m m' : Mem} {p : Addr} {n : Nat}
    (hf : Frame (randomCallWr s ++ [below (randomBase s) (extra + 8)]) m m')
    (hout : (⟨p, n⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩)
    (hscratch : (⟨p, n⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩)
    (hstack : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  apply hf.bytes (R := ⟨p, n⟩) _ hn (List.mem_range.mp hi)
  intro r hr
  simp only [randomCallWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hout
  · exact hscratch
  · exact (hstack.sub_left (random_calleeFrame_sub extra s)).symm

/-- Writing the return address leaves every disjoint input byte unchanged. -/
theorem random_callEntry_bytes {s : State} {B p : Addr} {n : Nat} (hsp : s.gpr .rsp = B)
    (hsep : Mem.Sep p n (B - 8) 8) (hn : n < 2 ^ 64) :
    Spec.Rsa.bytesAt s.callEntry.mem p n = Spec.Rsa.bytesAt s.mem p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [State.callEntry_mem, hsp]
  apply Mem.write_apply
  apply hsep
  rw [Mem.sub_ofNat_toNat _ (by omega)]
  exact hi'

end VG.Proof.Dsa.X86_64
