module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! Memory layout of the supplied-nonce call within the randomized wrapper. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

def randomCallRd (s : State) : List Region :=
  [⟨s.gpr .x3, (s.gpr .x4).toNat⟩,
    ⟨off (randomBase s) Random.oNonce, (s.gpr .x6).toNat⟩,
    ⟨s.gpr .x7, (stackArg s 0).toNat⟩, ⟨randomBase s, 24⟩]

def randomCallWr (s : State) : List Region :=
  [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]

def randomCallArg (s : State) (i : Nat) : BitVec 64 :=
  match i with
  | 0 => stackArg s 0
  | 1 => stackArg s 3
  | _ => stackArg s 4

theorem random_call_stackArg {t : State} {B : Addr} (hsp : t.sp = B)
    (rd wr : List Region) (i : Nat) :
    stackArg (t.callEntry.withRegions rd wr) i = word t.mem B (8 * i) := by
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp,
    State.callEntry_sp, State.callEntry_mem, hsp]

theorem random_call_stackArgAddr {t : State} {B : Addr} (hsp : t.sp = B)
    (rd wr : List Region) : stackArgAddr (t.callEntry.withRegions rd wr) 0 = B := by
  simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hsp,
    Nat.mul_zero, BitVec.add_zero]

/-- The call's read and write permissions are covered by the wrapper's permissions. -/
theorem random_call_covers {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    Covers (randomCallRd s ++ randomCallWr s) (t.rd ++ t.wr) ∧ Covers (randomCallWr s) t.wr := by
  have hq : (s.gpr .x6).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega
  have hf : (⟨randomBase s, Random.frameBytes⟩ : Region) ∈ t.wr := by rw [hwr]; exact .head _
  have ho : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
  have hs : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
  have zero (p : Addr) : p = p + BitVec.ofNat 64 0 := (BitVec.add_zero p).symm
  have cw : Covers (randomCallWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [randomCallWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, ho, 0, zero _, by simp⟩
    · exact ⟨_, hs, 0, zero _, by simp⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  simp only [randomCallRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_append_left _ (by rw [hrd, h.rd]; simp), 0, zero _, by simp⟩
  · exact ⟨_, List.mem_append_right _ hf, 200, rfl, by change 200 + (s.gpr .x6).toNat ≤ 256; omega⟩
  · exact ⟨_, List.mem_append_left _ (by rw [hrd, h.rd]; simp), 0, zero _, by simp⟩
  · exact ⟨_, List.mem_append_right _ hf, 0, zero _, by change 0 + 24 ≤ 256; decide⟩

end VG.Proof.Dsa.AArch64
