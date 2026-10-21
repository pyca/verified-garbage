module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Body
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Run exactly 128 binary GCD steps on the two native-word banks -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Gcd64

theorem code_iter {s : State} {base : Addr} {size count : Nat}
    (W : Ws s base size 2 count) (space : 15 ≤ count) :
    WP isa code s (LoopState s base size count 64) := by
  unfold code
  refine WP.seq (wp_movS rfl fun a A _ => WP.block_nil ?_)
  let Inv := fun q t => ∃ i, i + q = 64 ∧ 0 < q ∧ LoopState s base size count i t
  refine WP.loop (M := isa) Inv ?_ 64 a ?_
  · rintro q t ⟨i, counter, positive, T⟩
    refine WP.mono (body_ok space T (by omega)) fun u ⟨U, Z⟩ => ?_
    by_cases done : i + 1 = 64
    · left
      refine ⟨?_, done ▸ U⟩
      change u.zf.map Bool.not = some false
      rw [Z, decide_eq_true done]
      rfl
    · right
      refine ⟨?_, q - 1, by omega, i + 1, by omega, by omega, U⟩
      change u.zf.map Bool.not = some true
      rw [Z, decide_eq_false done]
      rfl
  · refine ⟨0, by decide, by decide, W.rest A.keeps (by decide) (by decide), ?_, A.keeps.mono (by decide), A.gpr, ?_⟩
    · rw [A.mem]
      exact Keep.refl _ _ _ _ _
    · rw [A.mem]
      rfl

end VG.Proof.RsaKeyGen.X86.Gcd64
