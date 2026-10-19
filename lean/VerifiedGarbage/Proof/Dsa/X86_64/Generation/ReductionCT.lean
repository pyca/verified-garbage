module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Reduce
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Reduce
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops

/-! # Public-width arithmetic pieces used in p-candidate reduction -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation

variable {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
  (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a))

include hws

theorem doubleArray_ct (dst : Nat) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.seq (.block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base dst .rbx)) (wordLoop 0 shlBody)) hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (doubleArray dst) s (Ψ a)) :
    RelCT isa (Two Φ) (doubleArray dst) (Two Ψ) := by
  unfold doubleArray at *
  simp only [List.append_assoc] at hw ⊢
  exact ws_ct B Z w hws ht hw

theorem subtractRemainder_ct (dst x rem : Nat) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.seq (.block (([.mov32 .rbp (.imm 0)] : List Instr) ++ (base x .r8 ++ (base rem .r10 ++ base dst .rsi))))
        (wordLoop 0 subBody)) hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (subtractRemainder dst x rem) s (Ψ a)) :
    RelCT isa (Two Φ) (subtractRemainder dst x rem) (Two Ψ) := by
  unfold subtractRemainder at *
  simp only [List.append_assoc] at hw ⊢
  exact ws_ct B Z w hws ht hw

theorem incrementEven_ct (dst : Nat) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.block (base dst .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .add .rax (.imm 1),
        .store (at0 .rbx) .rax] : List Instr))) hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.block (incrementEven dst)) s (Ψ a)) :
    RelCT isa (Two Φ) (.block (incrementEven dst)) (Two Ψ) := by
  unfold incrementEven at *
  simp only [List.append_assoc] at hw ⊢
  exact ws_block_ct B Z w hws ht hw

theorem candidateDivmod_ct
    (hw : ∀ a s, Φ a s → WP isa (divmod 0 1 2 3) s (Ψ a)) :
    RelCT isa (Two Φ) (divmod 0 1 2 3) (Two Ψ) := by
  have e : divmod 0 1 2 3 = .seq (.block (ws ++ (base 1 .r8 ++ ([.mov .r11 (.reg .r12)] ++
      (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++ [.mov32 .r13 (.imm 0)])))))
      (.seq zeroAccLoop (.loop (divStep 0 1 2 3) .ne)) := by
    simp only [divmod, divInit, seqs, List.append_assoc]
  rw [e] at hw ⊢
  exact ws_ct B Z w hws (by taint_decide) hw

end VG.Proof.Dsa.X86_64.Generation
