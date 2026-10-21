module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderPointers
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderStore

/-! # Complete initialization of the public prepared header -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.Header

def headerMemory (base : Addr) (p : BitVec 32) (w : Nat) (m : Mem) : Mem :=
  (List.range 8).foldl (pointerMemory base p w)
    ((m.writeW (off base 48) (0#32 ++ BitVec.ofNat 32 w)).writeW
      (off base 224) (0#32 ++ BitVec.ofNat 32 (stride w)))

theorem code_ok {s : State} {base : Addr} {size w : Nat}
    (scratch : Scr s base size) (fit : 256 ≤ size) :
    WP isa (.block (code w)) s fun t =>
      t.mem = headerMemory base (s.gpr .edi) w s.mem ∧ Keeps [.eax, .edx] s t := by
  unfold code
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS rfl fun a A _ => ?_
  refine WP.block_append (WP.mono (literal_ok (scratch.of_keeps A.keeps (by decide)) (by omega) A.gpr)
    fun b ⟨Mb, _, Kb⟩ => ?_)
  have K : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).widen Kb
  have zeroB : b.gpr .edx = 0#32 := (Kb.1 .edx (by decide)).trans A.gpr
  refine WP.block_append (WP.mono (literal_ok (scratch.of_keeps K (by decide)) (by omega) zeroB)
    fun c ⟨Mc, _, Kc⟩ => ?_)
  have K' : Keeps [.eax, .edx] s c := K.widen Kc
  have zeroC : c.gpr .edx = 0#32 := (Kc.1 .edx (by decide)).trans zeroB
  refine WP.mono (pointers_ok (List.range 8) (scratch.of_keeps K' (by decide))
    (fun i mem => by have := List.mem_range.mp mem; omega) zeroC) fun t ⟨Mt, Kt⟩ => ?_
  refine ⟨?_, K'.widen Kt⟩
  rw [Mt, K'.1 .edi (by decide), Mc, Mb, A.mem]
  rfl

end VG.Proof.RsaKeyGen.X86.Header
