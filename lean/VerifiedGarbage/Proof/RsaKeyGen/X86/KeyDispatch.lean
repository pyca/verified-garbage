module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySized
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Public width dispatch selects the complete native key operation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem dispatch_ok {E : Environment} {s : State} {w : Nat} (h : Input E s)
    (size : E.n = 4 * w) (small : w < 2 ^ 32) (value : s.gpr .eax = BitVec.ofNat 32 w)
    (choices : List Nat) (member : w ∈ choices) (bounded : ∀ v ∈ choices, v < 2 ^ 32) :
    WP isa (dispatch choices) s fun t =>
      Ws t E.base E.size E.n 32 ∧ BodyOutcome E s.mem t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  induction choices generalizing s with
  | nil => cases member
  | cons v rest ih =>
    unfold dispatch
    refine WP.seq (wp_cmpS rfl fun a A Z => WP.block_nil ?_)
    have ha : Input E a := h.keep (h.ws.rest (A.keeps [])) (A.keeps []) (by intro d hd; rw [A.mem])
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
      rw [← same, ← size]
      refine WP.mono (sized_ok ha) fun t ⟨ht, result, F, K⟩ => ?_
      rw [A.mem] at result F
      exact ⟨ht, result, F, (A.keeps _).trans K⟩
    · refine WP.ite false (by rw [condition, decide_eq_false same]) (fun bad => nomatch bad) (fun _ => ?_)
      refine WP.mono (ih ha (by rw [A.gpr]; exact value) (List.mem_cons.mp member |>.resolve_left same)
        (fun j hj => bounded j (List.mem_cons_of_mem _ hj))) fun t ⟨ht, result, F, K⟩ => ?_
      rw [A.mem] at result F
      exact ⟨ht, result, F, (A.keeps _).trans K⟩

end VG.Proof.RsaKeyGen.X86.Key
