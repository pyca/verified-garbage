module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateLoad
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.Proof.Mont.Words

/-! # Candidate import consumes exactly one native-width random block -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateLoad
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.CandidateLoad

theorem count_ok {s : State} {base : Addr} {size w : Nat} (S : Scr s base size)
    (header : 160 ≤ size) (bound : 8 * w < 2 ^ 32) :
    WP isa (.block (count w)) s fun t =>
      word t.mem base 152 = BitVec.ofNat 64 (8 * w) ∧
      Outside base 152 8 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold count
  refine wp_movS rfl fun a A _ =>
    wp_storeS ((S.of_keeps A.keeps (by decide)).ea (d := 152) (by omega))
      ((S.of_keeps A.keeps (by decide)).write (by omega)) fun b B =>
    wp_movS rfl fun c C _ => ?_
  have Kc := (A.keeps.widen (B.keeps [])).trans C.keeps
  have Sc := S.of_keeps Kc (by decide)
  refine wp_storeS (Sc.ea (d := 156) (by omega)) (Sc.write (by omega)) fun t T => WP.block_nil ?_
  have pair : (0#32 ++ BitVec.ofNat 32 (8 * w)) = BitVec.ofNat 64 (8 * w) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or,
      Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt (Nat.lt_trans bound (by decide : 2 ^ 32 < 2 ^ 64))]
  have memory : t.mem = s.mem.writeW (off base 152) (BitVec.ofNat 64 (8 * w)) := by
    rw [T.mem, C.mem, B.mem, A.mem, C.gpr, A.gpr]
    have high : off base 156 = off base 152 + BitVec.ofNat 64 4 := by
      simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [high, ← VG.Proof.Rc2.Word32.write64_pair]
    change s.mem.writeW (off base 152) (0#32 ++ BitVec.ofNat 32 (8 * w)) = _
    rw [pair]
  refine ⟨?_, ?_, Kc.widen (T.keeps [])⟩
  · rw [memory]
    exact Mem.readW_writeW_self64 _ _ _
  · rw [memory]
    exact writeW_outside _ _ _ (by decide)

end VG.Proof.RsaKeyGen.X86.CandidateLoad
