module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! Memory layout of the supplied-nonce call within the randomized wrapper. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

def randomCallRd (s : State) : List Region :=
  [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩,
    ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨randomBase s, 40⟩]

def randomCallWr (s : State) : List Region :=
  [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩]

def randomCallArg (s : State) (i : Nat) : BitVec 64 :=
  match i with
  | 0 => stackArg s 0
  | 1 => stackArg s 1
  | 2 => stackArg s 2
  | 3 => stackArg s 5
  | _ => stackArg s 6

theorem random_call_stackArg {t : State} {B : Addr} (hsp : t.gpr .rsp = B)
    (rd wr : List Region) {i : Nat} (hi : i < 5) :
    stackArg (t.callEntry.withRegions rd wr) i = word t.mem B (8 * i) := by
  have he : B - 8 + BitVec.ofNat 64 (8 * (i + 1)) = off B (8 * i) := by
    rw [show 8 * (i + 1) = 8 + 8 * i by omega, BitVec.ofNat_add,
      ← BitVec.add_assoc, show BitVec.ofNat 64 8 = (8 : BitVec 64) from rfl, BitVec.sub_add_cancel]
  have hsep : Mem.Sep (B - 8 + BitVec.ofNat 64 (8 * (i + 1))) 8 (B - 8) 8 :=
    fun x hx hy => Offset.sep_base (B - 8) (by omega) (by omega) x hy hx
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_rsp, State.callEntry_mem, hsp]
  rw [Mem.readW_writeW_sep hsep (by decide), he]

theorem random_call_stackArgAddr {t : State} {B : Addr} (hsp : t.gpr .rsp = B)
    (rd wr : List Region) : stackArgAddr (t.callEntry.withRegions rd wr) 0 = B := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp]
  exact BitVec.sub_add_cancel _ _

/-- The call's read and write permissions are covered by the wrapper's permissions. -/
theorem random_call_covers {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    Covers (randomCallRd s ++ randomCallWr s) (t.rd ++ t.wr) ∧ Covers (randomCallWr s) t.wr := by
  have hq : (stackArg s 0).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega
  have hf : (⟨randomBase s, Random.frameBytes⟩ : Region) ∈ t.wr := by rw [hwr]; exact .head _
  have ho : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
  have hs : (⟨stackArg s 5, (stackArg s 6).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
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
  · exact ⟨_, List.mem_append_right _ hf, 200, rfl, by change 200 + (stackArg s 0).toNat ≤ 248; omega⟩
  · exact ⟨_, List.mem_append_left _ (by rw [hrd, h.rd]; simp), 0, zero _, by simp⟩
  · exact ⟨_, List.mem_append_right _ hf, 0, zero _, by change 0 + 40 ≤ 248; decide⟩

end VG.Proof.Dsa.X86_64
