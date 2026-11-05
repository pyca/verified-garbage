module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Impl.Ffdh.X86_64.Cached
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptContract
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptSat
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
meta import VerifiedGarbage.Impl.Ffdh.X86_64.Cached

/-! # FFDH key generation from the context on x86-64: verified, with the Montgomery multiplications called

The attempt is proven with each backend's multiplication inline
(`attemptInline`) and emitted with calls of it (`attemptCode`), which inline
to it (`Verified.of_inline_verified`). -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Cached
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64 (R2Impl Verified.of_inline_verified bytesAt_overlay)
open VG.Proof.Bignum.X86_64 (inlineOk_seqs inline_seqs inline_of_noCalls map_inline_of_noCalls allInstrs_inline)

def attemptWith (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Cached.Generate.code mul (.seq (.block r2Head) (R2Words.choice mul))

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
    (hp : (attemptWith (fun _ _ _ => .block [])).allInstrs p = true)
    (hm : ∀ o a b, (mul o a b).allInstrs p = true) :
    (attemptWith mul).allInstrs p = true := by
  unfold attemptWith VG.Impl.Ffdh.X86_64.Cached.Generate.code VG.Impl.Ffdh.X86_64.Cached.Generate.body
    VG.Impl.Ffdh.X86_64.Cached.Generate.main VG.Impl.Ffdh.X86_64.Cached.Generate.core
    VG.Impl.Ffdh.X86_64.Cached.Generate.tail VG.Impl.Ffdh.X86_64.Cached.Generate.comb
    VG.Impl.Ffdh.X86_64.Cached.Generate.step R2Words.choice R2Words.fast R2Words.old
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
    (hp : (attemptWith (fun _ _ _ => .block [])).InlineOk = true)
    (hm : ∀ o a b, (mul o a b).InlineOk = true) :
    (attemptWith mul).InlineOk = true := by
  unfold attemptWith VG.Impl.Ffdh.X86_64.Cached.Generate.code VG.Impl.Ffdh.X86_64.Cached.Generate.body
    VG.Impl.Ffdh.X86_64.Cached.Generate.main VG.Impl.Ffdh.X86_64.Cached.Generate.core
    VG.Impl.Ffdh.X86_64.Cached.Generate.tail VG.Impl.Ffdh.X86_64.Cached.Generate.comb
    VG.Impl.Ffdh.X86_64.Cached.Generate.step R2Words.choice R2Words.fast R2Words.old
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
    (attemptWith mul).inline = attemptWith (fun o a b => (mul o a b).inline) := by
  unfold attemptWith VG.Impl.Ffdh.X86_64.Cached.Generate.code VG.Impl.Ffdh.X86_64.Cached.Generate.body
    VG.Impl.Ffdh.X86_64.Cached.Generate.main VG.Impl.Ffdh.X86_64.Cached.Generate.core
    VG.Impl.Ffdh.X86_64.Cached.Generate.tail VG.Impl.Ffdh.X86_64.Cached.Generate.comb
    VG.Impl.Ffdh.X86_64.Cached.Generate.step R2Words.choice R2Words.fast R2Words.old
    VG.Impl.Bignum.X86_64.Public.R2Squares.run VG.Impl.Bignum.X86_64.Public.R2Squares.init
    VG.Impl.Bignum.X86_64.Public.R2Squares.next
  simp only [Code.inline, inline_seqs, List.map_append, List.map_cons, List.map_nil]
  simp (disch := decide) only [inline_of_noCalls, map_inline_of_noCalls]

/-- The attempt as proven: `mont.mm` inline. -/
def attemptInline (v : RoundImpl) : Prog isa := attemptWith v.mont.mm

/-- The attempt as emitted: `mm`, which inlines to `attemptInline`. -/
def attemptCode (v : RoundImpl) : Prog isa := attemptWith v.mm

theorem attemptCode_inline (v : RoundImpl) : (attemptCode v).inline = attemptInline v := by
  have h := template_inline v.mm
  simp only [v.mmInline] at h
  exact h

theorem attemptCode_inlineOk (v : RoundImpl) : (attemptCode v).InlineOk = true :=
  template_inlineOk v.mm (by decide +kernel) v.mmOk

private theorem attemptCode_safe (v : RoundImpl) :
    (attemptCode v).allInstrs (fun i => !loadsMxcsr i && !isa.writesSp i) = true := by
  rw [← allInstrs_inline, attemptCode_inline]
  exact template_instrs _ _ (by decide +kernel) v.arithSafe

theorem attemptInline_mx (v : RoundImpl) :
    (attemptInline v).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h := attemptCode_safe v
  rw [← allInstrs_inline, attemptCode_inline] at h
  rw [Code.allInstrs_eq] at h ⊢
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).1

theorem attemptCode_sp (v : RoundImpl) :
    (attemptCode v).all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  have h := attemptCode_safe v
  rw [Code.allInstrs_eq] at h ⊢
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).2

theorem attemptInline_verified (v : RoundImpl) :
    Verified target (attemptInline v) (Spec.Ffdh.cachedGenerateKeyContract abi) :=
  Verified.of_correct (cg_correct v.mont (R2Impl.words v.mont) (attemptInline_mx v))
    (cg_constantTime v.mont (R2Impl.words v.mont)) cg_implies

/-- With calls of `v.mm`, which need 8 bytes of stack for the return address. -/
theorem attemptCode_verified (v : RoundImpl) : Verified target (attemptCode v)
    (Spec.Ffdh.cachedGenerateKeyContract abi 8) := by
  have hv := attemptInline_verified v
  rw [← attemptCode_inline] at hv
  refine Verified.of_inline_verified (attemptCode_inlineOk v) hv
    ((Contract.Implies.refl hv.2.2).stack8_abi attempt_sat8) (fun _ h => Sig.clear_of_pre h)
    (fun s b hv u hs hp => ?_) (fun _ _ _ _ h => Sig.rsp_of_pub h)
  obtain ⟨-, -, hw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hxl, hyl, -, -, -, -, -⟩ := cg_implies.pre s (Sig.pre_stack0_abi hs)
  have hx := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := (s.gpr .rsi).toNat)
    (by rw [hw]; simp) (Nat.le_of_lt (s.gpr .rsi).isLt)
  have hy := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := (s.gpr .rcx).toNat)
    (by rw [hw]; simp) (Nat.le_of_lt (s.gpr .rcx).isLt)
  rw [hxl] at hx
  rw [hyl] at hy
  sig_post [Spec.Ffdh.cachedGenerateKeyContract, Spec.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi,
    argRegs, stackArgs_seven, List.append_eq] at hp ⊢
  rw [bytesAt_overlay hx, bytesAt_overlay hy]
  exact hp

end VG.Proof.Ffdh.X86_64.Cached
