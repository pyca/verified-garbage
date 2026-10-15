module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Checks
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public meta import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # FFDH on x86-64: comparisons in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Only pointers and the number of words are public after the header loads. -/
def CmpRegs (a b : Nat) (L : Ws) (s : State) : Prop :=
  s.gpr .r12 = BitVec.ofNat 64 L.w ∧ s.gpr .rbx = off L.B (slot L.w a) ∧
    s.gpr .r10 = off L.B (slot L.w b)

private theorem pins_cmpRegs (a b : Nat) : Pins (CmpRegs a b) [.r12, .rbx, .r10] :=
  pins_of (fun L r => if r = .r12 then BitVec.ofNat 64 L.w else
    if r = .rbx then off L.B (slot L.w a) else off L.B (slot L.w b)) fun L s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2

private theorem ptrs_cmpRegs {a b : Nat} (ha : a < 8) (hb : b < 8) (L : Ws) (s : State) (h : GoodW L s) :
    WP isa (.block (ptrs a b)) s (CmpRegs a b L) := by
  obtain ⟨_, hg, hZ⟩ := h
  exact WP.mono (ptrs_ok hg hZ ha hb) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

private theorem cmp_ct {a b : Nat} (ha : a < 8) (hb : b < 8) {c : Prog isa}
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (ptrs a b)) hc₁).isSome = true)
    (hT' : (taint.check (Taint.ofRegs [.r12, .rbx, .r10]) c hc₂).isSome = true) :
    RelCT isa (Two GoodW) (.seq (.block (ptrs a b)) c) fun _ _ => True :=
  RelCT.seq (two_piece [.rdi] pins_goodW hT (ptrs_cmpRegs ha hb))
    (two_taint [.r12, .rbx, .r10] (pins_cmpRegs a b) hT')

/-- Secret operands change neither the addresses nor the loop count. -/
theorem ltArr_ct {a b : Nat} (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (ptrs a b)) hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (ltArr a b)) fun _ _ => True :=
  cmp_ct ha hb hT (by taint_decide)

theorem geArr_ct {a b : Nat} (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (ptrs a b)) hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (geArr a b)) fun _ _ => True :=
  cmp_ct ha hb hT (by taint_decide)

theorem eqArr_ct {a b : Nat} (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (ptrs a b)) hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (eqArr a b)) fun _ _ => True :=
  cmp_ct ha hb hT (by taint_decide)

end VG.Proof.Ffdh.X86_64
