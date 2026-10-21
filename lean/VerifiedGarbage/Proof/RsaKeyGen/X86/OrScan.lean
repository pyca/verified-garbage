module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.OrScan
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The native OR scan detects exactly a zero integer without writing memory -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.OrScan
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.OrScan

theorem code_ok {s : State} {base : Addr} {size n src : Nat}
    (scratch : Scr s base size) (positive : 0 < n) (fit : src + 4 * n ≤ size) :
    WP isa (code n src) s fun t =>
      (t.gpr .ebx = 0#32 ↔ val32 s.mem base src n = 0) ∧
      t.mem = s.mem ∧ Keeps [.ebx, .ebp, .edx] s t := by
  let Inv := fun j t => t.mem = s.mem ∧ Keeps [.ebx, .ebp, .edx] s t ∧
    (t.gpr .ebx = 0#32 ↔ val32 s.mem base src j = 0)
  have stable : LoopStable Inv := by
    rintro j u t ⟨M, K, Z⟩ ⟨Mt, Rd, Wr, R⟩
    refine ⟨Mt.trans M, ⟨?_, Rd.trans K.2.1, Wr.trans K.2.2⟩, ?_⟩
    · intro r mem
      exact (R r (by intro eq; subst r; simp at mem) (by intro eq; subst r; simp at mem)).trans (K.1 r mem)
    · rw [R .ebx (by decide) (by decide)]
      exact Z
  unfold code
  refine WP.seq (wp_movS rfl fun a A _ => WP.block_nil ?_)
  refine wordLoop_ok Inv positive (by have := scratch.size_lt; omega) stable
    ⟨A.mem, A.keeps.mono (by decide), by rw [A.gpr]; exact ⟨fun _ => rfl, fun _ => rfl⟩⟩ ?_ ?_
  · intro j index t ⟨M, K, Z⟩ pointer
    have St := scratch.of_keeps K (by decide)
    refine wp_orS (readSrc_at' St pointer (d := src) (by omega)) fun u U => WP.block_nil ?_
    refine ⟨⟨U.mem.trans M, K.widen U.keeps, ?_⟩, U.other .ebp (by decide), U.other .edi (by decide)⟩
    rw [U.gpr, BitVec.or_eq_zero_iff, Z, M]
    have wordZero : s.mem.readW (off base (src + 4 * j)) 32 = 0#32 ↔ w32 s.mem base (src + 4 * j) = 0 :=
      ⟨fun H => congrArg BitVec.toNat H, fun H => BitVec.eq_of_toNat_eq H⟩
    rw [wordZero, val32_succ]
    have power : 0 < 2 ^ (32 * j) := Nat.two_pow_pos _
    constructor
    · rintro ⟨left, right⟩
      rw [left, right, Nat.mul_zero]
    · intro sum
      have product : 2 ^ (32 * j) * w32 s.mem base (src + 4 * j) = 0 := by omega
      exact ⟨by omega, (Nat.mul_eq_zero.mp product).resolve_left (Nat.ne_of_gt power)⟩
  · intro t ⟨M, K, Z⟩
    exact ⟨Z, M, K⟩

end VG.Proof.RsaKeyGen.X86.OrScan
