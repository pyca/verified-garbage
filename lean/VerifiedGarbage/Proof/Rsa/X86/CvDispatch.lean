module

public import VerifiedGarbage.Impl.Rsa.X86.CrtValues
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.X86.ByteOps
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.TCB.X86.State

/-! # Dispatch every permitted RSA modulus width using only its public length -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.CrtValues

theorem dispatch_ok (widths : List Nat) {s : State} {n : Nat} {Q : State → Prop}
    (member : n ∈ widths) (bound : ∀ w ∈ widths, w < 2 ^ 32)
    (width : s.gpr .eax = BitVec.ofNat 32 n)
    (body : ∀ t, Keeps [] s t → t.mem = s.mem → WP isa (sized n) t Q) :
    WP isa (dispatch widths) s Q := by
  induction widths generalizing s with
  | nil => simp only [List.not_mem_nil] at member
  | cons w rest ih =>
    have hn := bound n member
    have hw := bound w List.mem_cons_self
    unfold dispatch
    refine WP.seq (wp_cmpS rfl fun t F Z => WP.block_nil ?_)
    have K := F.keeps ([] : List Reg)
    have flag : t.zf = some (decide (n = w)) := by
      rw [Z, width, sub_beq hn hw]
    by_cases eq : n = w
    · refine WP.ite true (by simp only [eval, flag, eq, decide_true])
        (fun _ => ?_) (fun h => Bool.noConfusion h)
      rw [← eq]
      exact body t K F.mem
    · refine WP.ite false (by simp only [eval, flag, eq, decide_false])
        (fun h => Bool.noConfusion h) (fun _ => ?_)
      apply ih (by simpa only [List.mem_cons, eq, false_or] using member)
        (fun v hv => bound v (List.mem_cons_of_mem w hv)) (by rw [F.gpr, width])
      intro u Ku Mu
      exact body u (K.trans Ku) (Mu.trans F.mem)

end VG.Proof.Rsa.X86.CrtValues
