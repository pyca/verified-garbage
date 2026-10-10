import VerifiedGarbage.Proof.Sha256.X86.Stream.Base
import VerifiedGarbage.Proof.Sha256.X86.Compress
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Impl.Sha256.X86.Stream
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Sha256.X86.Lit

/-!
# Streaming SHA-256 on x86 (32-bit): common lemmas

The call of the compression function, shared by the x86 proofs that import
it; the lemmas about 32-bit code they use are in `Base.lean`.
-/

namespace VG.Proof.Sha256.X86.Stream

open VG VG.X86 VG.Impl.Sha256.X86.Stream
open VG.Spec.Sha256 (HashValue blockAt compressBlocks compress)

/-! ## The call of the compression function -/

/-- The 20 bytes of stack below `E`, as the contracts write them. -/
theorem stk_eq {E : BitVec 32} (h : 20 ≤ E.toNat) : below E 20 = ⟨E.setWidth 64 - 20, 20⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

theorem arg_eq (s : State) (i : Nat) : arg s i = s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 := rfl

theorem compress_nosp : NoSp Impl.Sha256.X86.compress := NoSp.of_all (by lit_decide)

theorem compress_stack : stackUse Impl.Sha256.X86.compress = 0 := by lit_decide

/-- A region within one of `rs'`, at offset `o`. -/
theorem within {r : Region} {rs' : List Region} (r' : Region) (hr' : r' ∈ rs') (o : Nat)
    (hb : r.base = r'.base + BitVec.ofNat 64 o) (hl : o + r.len ≤ r'.len) :
    ∃ r' ∈ rs', ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len :=
  ⟨r', hr', o, hb, hl⟩

end VG.Proof.Sha256.X86.Stream
