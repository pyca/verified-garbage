module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.PrecomputeSat
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.PrecomputeCT

/-! # FFDH's context on x86-64: verified, with the Montgomery multiplications called

The precomputation is proven with each backend's multiplication inline
(`precomputeInline`) and emitted with calls of it (`precomputeCode`), which
inline to it (`Verified.of_inline_verified`). -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Cached
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64 (R2Impl)
open VG.Proof.Bignum.X86_64 (inlineOk_seqs inline_seqs inline_of_noCalls map_inline_of_noCalls allInstrs_inline)

def codeWith (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Cached.Precompute.code mul (.seq (.block r2Head) (R2Words.choice mul))

private theorem all_seqs (p : Instr → Bool) (l : List (Prog isa)) :
    (seqs l).allInstrs p = l.all (fun c => c.allInstrs p) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [seqs, List.all_cons, List.all_nil, Bool.and_true]
    | cons b l => simp only [seqs, Code.allInstrs, List.all_cons] at ih ⊢; rw [ih]

private theorem i_seq (p : Instr → Bool) (a b : Prog isa) :
    (Code.seq a b).allInstrs p = (a.allInstrs p && b.allInstrs p) := rfl
private theorem i_ite (p : Instr → Bool) (c : Cond) (a b : Prog isa) :
    (Code.ite c a b).allInstrs p = (a.allInstrs p && b.allInstrs p) := rfl
private theorem i_loop (p : Instr → Bool) (a : Prog isa) (c : Cond) :
    (Code.loop a c).allInstrs p = a.allInstrs p := rfl
private theorem i_empty (p : Instr → Bool) :
    (Code.block ([] : List Instr) : Prog isa).allInstrs p = true := rfl

private theorem template_instrs (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa)
    (hp : (codeWith (fun _ _ _ => .block [])).allInstrs p = true)
    (hm : ∀ o a b, (mul o a b).allInstrs p = true) :
    (codeWith mul).allInstrs p = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Cached.Precompute.code VG.Impl.Ffdh.X86_64.Cached.Precompute.body VG.Impl.Ffdh.X86_64.Cached.Precompute.main VG.Impl.Ffdh.X86_64.Cached.Precompute.table VG.Impl.Ffdh.X86_64.Cached.Precompute.initial
    VG.Impl.Ffdh.X86_64.Cached.Precompute.column VG.Impl.Ffdh.X86_64.Cached.Precompute.product VG.Impl.Ffdh.X86_64.Cached.Precompute.squares R2Words.choice R2Words.fast R2Words.old
    VG.Impl.Bignum.X86_64.Public.R2Squares.run VG.Impl.Bignum.X86_64.Public.R2Squares.init
    VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  repeat' first
    | rw [all_seqs] at *
    | rw [i_seq] at *
    | rw [i_ite] at *
    | rw [i_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  repeat' rw [i_empty] at hp
  exact hp

private theorem k_seq (a b : Prog isa) : (Code.seq a b).InlineOk = (a.InlineOk && b.InlineOk) := rfl
private theorem k_ite (c : Cond) (a b : Prog isa) : (Code.ite c a b).InlineOk = (a.InlineOk && b.InlineOk) := rfl
private theorem k_loop (a : Prog isa) (c : Cond) : (Code.loop a c).InlineOk = a.InlineOk := rfl
private theorem k_empty : (Code.block ([] : List Instr) : Prog isa).InlineOk = true := rfl

private theorem template_inlineOk (mul : Nat → Nat → Nat → Prog isa)
    (hp : (codeWith (fun _ _ _ => .block [])).InlineOk = true)
    (hm : ∀ o a b, (mul o a b).InlineOk = true) :
    (codeWith mul).InlineOk = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Cached.Precompute.code VG.Impl.Ffdh.X86_64.Cached.Precompute.body VG.Impl.Ffdh.X86_64.Cached.Precompute.main VG.Impl.Ffdh.X86_64.Cached.Precompute.table VG.Impl.Ffdh.X86_64.Cached.Precompute.initial
    VG.Impl.Ffdh.X86_64.Cached.Precompute.column VG.Impl.Ffdh.X86_64.Cached.Precompute.product VG.Impl.Ffdh.X86_64.Cached.Precompute.squares R2Words.choice R2Words.fast R2Words.old
    VG.Impl.Bignum.X86_64.Public.R2Squares.run VG.Impl.Bignum.X86_64.Public.R2Squares.init
    VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  repeat' first
    | rw [inlineOk_seqs] at *
    | rw [k_seq] at *
    | rw [k_ite] at *
    | rw [k_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  repeat' rw [k_empty] at hp
  exact hp

private theorem template_inline (mul : Nat → Nat → Nat → Prog isa) :
    (codeWith mul).inline = codeWith (fun o a b => (mul o a b).inline) := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Cached.Precompute.code VG.Impl.Ffdh.X86_64.Cached.Precompute.body VG.Impl.Ffdh.X86_64.Cached.Precompute.main VG.Impl.Ffdh.X86_64.Cached.Precompute.table VG.Impl.Ffdh.X86_64.Cached.Precompute.initial
    VG.Impl.Ffdh.X86_64.Cached.Precompute.column VG.Impl.Ffdh.X86_64.Cached.Precompute.product VG.Impl.Ffdh.X86_64.Cached.Precompute.squares R2Words.choice R2Words.fast R2Words.old
    VG.Impl.Bignum.X86_64.Public.R2Squares.run VG.Impl.Bignum.X86_64.Public.R2Squares.init
    VG.Impl.Bignum.X86_64.Public.R2Squares.next
  simp only [Code.inline, inline_seqs, List.map_append, List.map_cons, List.map_nil]
  simp (disch := decide) only [inline_of_noCalls, map_inline_of_noCalls]

/-- The precomputation as proven: `mont.mm` inline. -/
def precomputeInline (v : RoundImpl) : Prog isa := codeWith v.mont.mm

/-- The precomputation as emitted: `mm`, which inlines to `precomputeInline`. -/
def precomputeCode (v : RoundImpl) : Prog isa := codeWith v.mm

theorem precomputeCode_inline (v : RoundImpl) : (precomputeCode v).inline = precomputeInline v := by
  have h := template_inline v.mm
  simp only [v.mmInline] at h
  exact h

theorem precomputeCode_inlineOk (v : RoundImpl) : (precomputeCode v).InlineOk = true :=
  template_inlineOk v.mm (by decide +kernel) v.mmOk

private theorem precomputeCode_safe (v : RoundImpl) :
    (precomputeCode v).allInstrs (fun i => !loadsMxcsr i && !isa.writesSp i) = true := by
  rw [← allInstrs_inline, precomputeCode_inline]
  exact template_instrs _ _ (by decide +kernel) v.arithSafe

theorem precomputeInline_mx (v : RoundImpl) :
    (precomputeInline v).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h := precomputeCode_safe v
  rw [← allInstrs_inline, precomputeCode_inline] at h
  rw [Code.allInstrs_eq] at h ⊢
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).1

theorem precomputeCode_sp (v : RoundImpl) :
    (precomputeCode v).all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  have h := precomputeCode_safe v
  rw [Code.allInstrs_eq] at h ⊢
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).2

theorem precomputeInline_verified (v : RoundImpl) : Verified target (precomputeInline v) pcContract := by
  refine ⟨pc_correct v.mont (R2Impl.words v.mont) (precomputeInline_mx v),
    pc_constantTime v.mont (R2Impl.words v.mont), ?_⟩
  obtain ⟨s, hs⟩ := precompute_sat
  exact ⟨s, pc_implies.pre s hs⟩

/-- With calls of `v.mm`, which need 8 bytes of stack for the return address. -/
theorem precomputeCode_verified (v : RoundImpl) : Verified target (precomputeCode v)
    (Spec.Ffdh.generationPrecomputeContract (abi.withConsts VG.Impl.Ffdh.X86_64.VettedValidation.tableConsts) 8) := by
  have hv := precomputeInline_verified v
  rw [← precomputeCode_inline] at hv
  refine VG.Proof.Bignum.X86_64.Verified.of_inline_verified (precomputeCode_inlineOk v) hv pc_implies
    (fun _ h => Sig.clear_of_pre_consts h) (fun s b hv u hs hp => ?_)
    (fun s₁ s₂ h₁ h₂ hp => (pc_implies.pub s₁ s₂ h₁ h₂ hp).1.1)
  have hc := Sig.clear_of_pre_consts hs
  obtain ⟨hpre, _⟩ := pc_implies.pre s hs
  obtain ⟨_, _, hwr, _, _, _, _, _, nc, _⟩ := hpre
  obtain ⟨hr, hw⟩ := hp
  simp only [stripConsts_gpr] at nc
  refine ⟨hr, ?_⟩
  change _ = some (Spec.Rsa.wordsAt (overlay _ hv b.mem) (s.gpr .rdi) (s.gpr .rsi).toNat)
  rw [VG.Proof.Bignum.X86_64.wordsAt_overlay fun i hi => VG.Proof.Bignum.X86_64.Clear.wr_miss hc (p := s.gpr .rdi) (n := (s.gpr .rsi).toNat * 8)
    (by change _ ∈ (stripConsts VG.Impl.Ffdh.X86_64.VettedValidation.tableConsts s).wr; rw [hwr]; simp)
    (by omega) (by omega)]
  exact hw

end VG.Proof.Ffdh.X86_64.Cached
