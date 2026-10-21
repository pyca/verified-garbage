module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Reuse width-specific I/O without duplicating key arithmetic -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem dispatchIO_ok {s : State} {w : Nat} {part : Nat → Prog isa} {Q : State → Prop}
    (small : w < 2 ^ 32) (choices : List Nat) (member : w ∈ choices)
    (bounded : ∀ v ∈ choices, v < 2 ^ 32) (value : s.gpr .eax = BitVec.ofNat 32 w)
    (correct : ∀ t, Keeps [] s t → t.mem = s.mem → WP isa (part (4 * w)) t Q) :
    WP isa (dispatchIO part choices) s Q := by
  induction choices generalizing s with
  | nil => cases member
  | cons v rest ih =>
    unfold dispatchIO
    refine WP.seq (wp_cmpS rfl fun a A Z => WP.block_nil ?_)
    have condition : isa.eval .e a = some (decide (w = v)) := by
      change a.zf = _
      rw [Z, value]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      rw [BitVec.sub_eq_iff_eq_add]
      change (BitVec.ofNat 32 w = 0#32 + BitVec.ofNat 32 v) ↔ w = v
      rw [BitVec.zero_add, ← BitVec.toNat_inj]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt (bounded v List.mem_cons_self)]
    by_cases same : w = v
    · refine WP.ite true (by rw [condition, decide_eq_true same]) (fun _ => ?_) (fun bad => nomatch bad)
      rw [← same]
      exact correct a (A.keeps []) A.mem
    · refine WP.ite false (by rw [condition, decide_eq_false same]) (fun bad => nomatch bad) (fun _ => ?_)
      exact ih (List.mem_cons.mp member |>.resolve_left same)
        (fun j hj => bounded j (List.mem_cons_of_mem _ hj))
        (by rw [A.gpr]; exact value)
        (fun t K memory => correct t ((A.keeps []).trans K) (memory.trans A.mem))

end VG.Proof.RsaKeyGen.X86.KeyRuntime
