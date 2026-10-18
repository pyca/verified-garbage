module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ControllerDepth
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateDepth

/-! # Stack bound for the complete parameter-generation entry point -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

theorem seedAttempt_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round)
    (pLen qLen : Nat) : generationDepth (seedAttempt H1 H256 sq mul round pLen qLen) := by
  have finish : generationDepth (finishDomain sq mul pLen qLen) :=
    (show generationDepth (pack pLen qLen) by exact (show 0 ≤ 128 by decide)).seq (validate_depth sq mul hs hm pLen qLen)
  exact ((show generationDepth (.block (seedArguments qLen)) by exact (show 0 ≤ 128 by decide)).seq
    (subgroup_depth h1 h256 mul round hm hr qLen)).seq
    (onSuccess_depth ((primeSearch_depth h1 h256 mul round hm hr pLen qLen).seq
      (onSuccess_depth ((generatorSearch_depth sq mul hs hm pLen).seq (onSuccess_depth finish)))))

theorem generate_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round)
    (pLen qLen : Nat) : generationDepth (generate H1 H256 sq mul round pLen qLen) :=
  (tapeLoop_depth (seedAttempt_depth h1 h256 sq mul round hs hm hr pLen qLen) _ _).seq
    (show generationDepth finishOutput by exact (show 0 ≤ 128 by decide))

theorem dispatch_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round) :
    generationDepth (dispatch H1 H256 sq mul round) := by
  have h128 := generate_depth h1 h256 sq mul round hs hm hr 128 20
  have h256' := generate_depth h1 h256 sq mul round hs hm hr 256 32
  have h384 := generate_depth h1 h256 sq mul round hs hm hr 384 32
  exact (show generationDepth (.block [.mov .rax (.mem (Impl.Mgf1.X86_64.sp 136)),
    .alu .cmp .rax (.imm 128)]) by exact (show 0 ≤ 128 by decide)).seq
    (h128.ite ((show generationDepth (.block [.alu .cmp .rax (.imm 256)]) by exact (show 0 ≤ 128 by decide)).seq
      (h256'.ite h384 .e)) .e)

theorem entry_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round) :
    (code H1 H256 sq mul round).x86_64Depth ≤ 472 := by
  have body := dispatch_depth h1 h256 sq mul round hs hm hr
  unfold generationDepth at body
  simp only [code, entryBody, Code.x86_64Depth, Instr.frameBytes, Nat.zero_max, Nat.max_zero]
  exact Nat.add_le_add_right (Nat.add_le_add_right body 296) 48

end VG.Proof.Dsa.X86_64.Generation
