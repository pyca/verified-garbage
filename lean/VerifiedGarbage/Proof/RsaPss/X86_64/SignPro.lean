module

public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
import Mathlib.Tactic.Set
import Mathlib.Data.Int.GCD
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.X86_64.SignEnc
public import VerifiedGarbage.Proof.Sha256.X86_64.Lit
import VerifiedGarbage.Proof.RsaPss.MgfBytes
public import VerifiedGarbage.Proof.RsaPss.X86_64.Mgf
import VerifiedGarbage.Proof.RsaPss.X86_64.Params
public import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashOk
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64
public import VerifiedGarbage.Impl.RsaPss.X86_64
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
public import VerifiedGarbage.Proof.RsaPss.X86_64.Basic
public import VerifiedGarbage.Proof.RsaPss.X86_64.Loops
public import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Spec.Hmac
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCtx
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Spec.RsaPss.Contract
public import VerifiedGarbage.Spec.RsaPss.MdTable

/-! ### `RsaPss.X86_64.SignCtx`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS signing on x86-64: the contract on the registers

`signK tsH tsG` states `Spec.RsaPss.signMdTableContract` with the tables
`tsH` of `MdHash` and `tsG` of `MdHash` (`Abi.withTables`, with the stack the
frame and the calls use, `signStack`) on the registers and the stack
(`sign_implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The stack below the stack pointer: the frame, the return address of
its calls, and what `vg_rsa_private_checked` uses below that. -/
def signStack : Nat := 392 + 8 + Proof.Rsa.X86_64.stackBytes

theorem stackArgs_eighteen (s : State) :
    List.map (stackArg s) (List.range 18) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16,
      stackArg s 17] := rfl

/-- The functions of the tables `ts`. -/
def tabFns (ts : List FnTable) : List String := (ts.map (·.fns)).flatten

variable (tsH tsG : List FnTable)

/-- `sign(out = rdi, out_len = rsi, n = rdx, n_len = rcx, e = r8, e_len = r9,
p = [rsp + 8], p_len, q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len,
digest = [rsp + 88], digest_len, salt, salt_len, scratch, scratch_len,
hash = [rsp + 136], mgf1 = [rsp + 144])`, `hash` one of the tables `tsH`
and `mgf1` one of `tsG`. -/
def signK : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let p : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let q : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let dp : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let dq : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let qi : Region := ⟨stackArg s 8, (stackArg s 9).toNat⟩
    let dg : Region := ⟨stackArg s 10, (stackArg s 11).toNat⟩
    let sa : Region := ⟨stackArg s 12, (stackArg s 13).toNat⟩
    let scr : Region := ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
    let tH : Region := ⟨stackArg s 16, 88⟩
    let tG : Region := ⟨stackArg s 17, 88⟩
    let args : Region := ⟨stackArgAddr s 0, 144⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩
    signStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 152 ≤ 2 ^ 64 ∧
      (∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s T)) ∧
      (∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 17) (FnTable.words isa s T)) ∧
      (tabFns tsH ++ tabFns tsG).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g) ∧
      s.rd = [n, e, p, q, dp, dq, qi, dg, sa, tH, tG, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint p ∧ out.Disjoint q ∧ out.Disjoint dp ∧
      out.Disjoint dq ∧ out.Disjoint qi ∧ out.Disjoint dg ∧ out.Disjoint sa ∧ out.Disjoint scr ∧
      out.Disjoint tH ∧ out.Disjoint tG ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ dp.Disjoint scr ∧
      dq.Disjoint scr ∧ qi.Disjoint scr ∧ dg.Disjoint scr ∧ sa.Disjoint scr ∧ scr.Disjoint tH ∧
      scr.Disjoint tG ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint p ∧ ret.Disjoint q ∧
      ret.Disjoint dp ∧ ret.Disjoint dq ∧ ret.Disjoint qi ∧ ret.Disjoint dg ∧ ret.Disjoint sa ∧
      ret.Disjoint scr ∧ ret.Disjoint tH ∧ ret.Disjoint tG ∧ ret.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint p ∧ stk.Disjoint q ∧
      stk.Disjoint dp ∧ stk.Disjoint dq ∧ stk.Disjoint qi ∧ stk.Disjoint dg ∧ stk.Disjoint sa ∧
      stk.Disjoint scr ∧ stk.Disjoint tH ∧ stk.Disjoint tG ∧ stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧ (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧ (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64 ∧
      (stackArg s 10).toNat + (stackArg s 11).toNat ≤ 2 ^ 64 ∧
      (stackArg s 12).toNat + (stackArg s 13).toNat ≤ 2 ^ 64 ∧
      (stackArg s 14).toNat + (stackArg s 15).toNat * 8 ≤ 2 ^ 64 ∧ (stackArg s 16).toNat + 88 ≤ 2 ^ 64 ∧
      (stackArg s 17).toNat + 88 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .rcx).toNat ∧
      1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat ∧
      1 ≤ (stackArg s 1).toNat ∧ (stackArg s 1).toNat < (s.gpr .rcx).toNat ∧ 1 ≤ (stackArg s 3).toNat ∧
      (stackArg s 3).toNat < (s.gpr .rcx).toNat ∧ (stackArg s 5).toNat = (stackArg s 1).toNat ∧
      (stackArg s 9).toNat = (stackArg s 1).toNat ∧ (stackArg s 7).toNat = (stackArg s 3).toNat ∧
      Spec.RsaPss.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 15).toNat ∧
      Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 16) (stackArg s 11)
  post s s' := ∀ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some H →
    Spec.MdHashTable.hashAt 64 s.mem (stackArg s 17) = some G →
    Spec.Rsa.writtenOutcome s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.RsaPss.sign H G (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 10) H.len)
        (Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (List.range 18).map (stackArg s₁) = (List.range 18).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat ∧
      (∀ f ∈ tabFns tsH ++ tabFns tsG, s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ tsH, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 16) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 16) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ tsG, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 17) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 17) (FnTable.words isa s₂ T))

end VG.Proof.RsaPss.X86_64

end

end

/-! ### `RsaPss.X86_64.Safe`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS on x86-64: no writes to `rsp`, no loads of MXCSR

Every instruction of `ctHash` (and of what it calls) neither writes `rsp`
(`SpSafe`) nor loads MXCSR (`ctHash_safe`), given that of every function its
calls through the tables' slots may reach (`MdFnsSafe`, `FnsSafe`), and how
much stack each piece uses (`ctHash_xd`, `mgfXor_xd`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- Neither writes `rsp` nor loads MXCSR. -/
def safeI (i : Instr) : Bool := !isa.writesSp i && !loadsMxcsr i

theorem allInstrs_and (f g : Instr → Bool) (c : Prog isa) :
    c.allInstrs (fun i => f i && g i) = (c.allInstrs f && c.allInstrs g) := by
  simp only [Code.allInstrs_eq]
  induction instrs c with
  | nil => rfl
  | cons i is ih =>
    simp only [List.all_cons, ih]
    cases f i <;> cases g i <;> simp

theorem safeI_eq : safeI = fun i => !isa.writesSp i && !loadsMxcsr i := rfl

theorem safe_sp {c : Prog isa} (h : c.allInstrs safeI = true) : SpSafe c := by
  rw [Code.allInstrs_eq] at h
  intro i hi
  have := List.all_eq_true.mp h i hi
  simp only [safeI, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact this.1

theorem safe_mx {c : Prog isa} (h : c.allInstrs safeI = true) : c.allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [safeI_eq, allInstrs_and] at h
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem rec_all (p : Instr → Bool) (l : List Instr) :
    List.rec (motive := fun _ => Bool) true (fun i _ ih => p i && ih) l = l.all p := by
  induction l with
  | nil => rfl
  | cons i is ih => simp only [List.all_cons, ← ih]

/-! ## The calls through the tables' slots -/

/-- Every function of `ts` is `safeI` and uses at most `d` bytes of stack. -/
def FSafe (ts : List (String × Prog isa)) (d : Nat) : Prop :=
  ∀ q ∈ ts, q.2.allInstrs safeI = true ∧ q.2.x86_64Depth ≤ d

theorem icalls_safe {d : Nat} : ∀ {ts : List (String × Prog isa)}, FSafe ts d →
    (Code.icalls (.callr .r11) ts).allInstrs safeI = true ∧ (Code.icalls (.callr .r11) ts).x86_64Depth ≤ d + 8
  | [], _ => ⟨rfl, Nat.zero_le _⟩
  | q :: ts, h => by
    have hq := h q (List.mem_cons_self ..)
    have ih := icalls_safe (ts := ts) fun r hr => h r (List.mem_cons_of_mem _ hr)
    refine ⟨?_, ?_⟩
    · simp only [Code.icalls, Code.allInstrs, hq.1, ih.1, Bool.and_true]; rfl
    · simp only [Code.icalls, Code.x86_64Depth, Nat.max_le]; omega

theorem scall_safe {d s : Nat} {ts : List (String × Prog isa)} (h : FSafe ts d) :
    (scall s ts).allInstrs safeI = true ∧ (scall s ts).x86_64Depth ≤ d + 8 := by
  have := icalls_safe h
  refine ⟨?_, ?_⟩
  · simp only [scall, Code.allInstrs, this.1, Bool.and_true]; rfl
  · simp only [scall, Code.x86_64Depth, Nat.max_le]; omega

/-- The functions the calls through the slots of the table of `MdHash` reach
use no stack. -/
structure MdFnsSafe (f : MdFns) : Prop where
  init : FSafe f.init 0
  comp : FSafe f.comp 0
  dig : FSafe f.dig 0

/-- And those through the slots of the table of `MdHash` at most 8 bytes. -/
structure FnsSafe (g : Impl.Mgf1.X86_64.Table.Fns) : Prop where
  init : FSafe g.init 8
  upd : FSafe g.upd 8
  fin : FSafe g.fin 8

variable {H : Hash} (hH : HashOK H) {f : MdFns} (hf : MdFnsSafe f) {g : Impl.Mgf1.X86_64.Table.Fns}
  (hg : FnsSafe g)

include hH hf in
theorem ctHashWith_safe {padding : Prog isa} (hp : padding.allInstrs safeI = true) :
    (ctHashWith f H padding).allInstrs safeI = true := by
  have hl : H.P.len.all safeI = true := hH.taints.lenSafe
  simp only [ctHashWith, hp, seqs, ctInit, lenLoop, compLoop, select, Code.allInstrs, (scall_safe hf.init).1,
    (scall_safe hf.comp).1, (scall_safe hf.dig).1, rec_all, lenField, digestOut, digestAt, List.all_append, hl,
    byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include hH hf in
theorem ctHash_safe : (ctHash f H).allInstrs safeI = true := ctHashWith_safe hH hf rfl

include hf in
theorem ctHashWith_xd {padding : Prog isa} (hp : padding.x86_64Depth = 0) :
    (ctHashWith f H padding).x86_64Depth ≤ 8 := by
  have := (scall_safe (s := sIniH) hf.init).2
  have := (scall_safe (s := sCmpH) hf.comp).2
  have := (scall_safe (s := sDigH) hf.dig).2
  simp only [ctHashWith, hp, seqs, ctInit, lenLoop, compLoop, select, digestOut, digestAt, byteLoop,
    Code.x86_64Depth, Nat.max_le]
  omega_arith

include hf in
theorem ctHash_xd : (ctHash f H).x86_64Depth ≤ 8 := ctHashWith_xd hf rfl

theorem copyWords64_safe (src dst : Reg) (so doff n : Nat) :
    (copyWords64 src dst so doff n).all safeI = true := by
  simp only [copyWords64, List.all_flatMap]
  apply List.all_eq_true.mpr
  intro j _
  rfl

theorem lenLast_safe : (lenLast H).allInstrs safeI = true := by
  unfold lenLast
  split
  · simp only [Code.allInstrs, rec_all, copyWords64_safe, List.all_append, Bool.and_true]
    rfl
  · rfl

theorem lenLast_xd : (lenLast H).x86_64Depth = 0 := by
  unfold lenLast
  split <;> rfl

include hH hf in
theorem fixedHash_safe : (fixedHash f H).allInstrs safeI = true := by
  have hl : H.P.len.all safeI = true := hH.taints.lenSafe
  simp only [fixedHash, seqs, ctInit, lenLast_safe (H := H), compAll, Code.allInstrs, (scall_safe hf.init).1,
    (scall_safe hf.comp).1, (scall_safe hf.dig).1, rec_all, lenField, digestAt, List.all_append, hl, Bool.and_true]
  rfl

include hf in
theorem fixedHash_xd : (fixedHash f H).x86_64Depth ≤ 8 := by
  have := (scall_safe (s := sIniH) hf.init).2
  have := (scall_safe (s := sCmpH) hf.comp).2
  have := (scall_safe (s := sDigH) hf.dig).2
  simp only [fixedHash, seqs, ctInit, lenLast_xd (H := H), compAll, digestAt, Code.x86_64Depth, Nat.max_le]
  omega_arith

include hg in
theorem mgfXor_safe : (mgfXor H g).allInstrs safeI = true := by
  simp only [mgfXor, mgfRound, mgfSeed, seqs, Code.allInstrs, (scall_safe hg.init).1, (scall_safe hg.upd).1,
    (scall_safe hg.fin).1, Impl.Mgf1.X86_64.Table.xorOut, Impl.Mgf1.X86_64.seqs, Impl.Mgf1.X86_64.byteLoop,
    rec_all, List.all_append, Bool.and_true, Bool.true_and]
  rfl

include hg in
theorem mgfXor_xd : (mgfXor H g).x86_64Depth ≤ 16 := by
  have := (scall_safe (s := sIniG) hg.init).2
  have := (scall_safe (s := sUpdG) hg.upd).2
  have := (scall_safe (s := sFinG) hg.fin).2
  simp only [mgfXor, mgfRound, seqs, Impl.Mgf1.X86_64.Table.xorOut, Impl.Mgf1.X86_64.seqs,
    Impl.Mgf1.X86_64.byteLoop, Code.x86_64Depth, Nat.max_le]
  omega_arith

include hH hf hg in
theorem signEnc_safe : (signEnc f H g).allInstrs safeI = true := by
  simp only [signEnc, seqs, clearY, copyDigest, copySaltY, clearEm, putSalt, putH, Code.allInstrs,
    ctHash_safe hH hf, mgfXor_safe hg, rec_all, List.all_append, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include hf hg in
theorem signEnc_xd : (signEnc f H g).x86_64Depth ≤ 16 := by
  have := ctHash_xd (H := H) hf
  have := mgfXor_xd (H := H) hg
  simp only [signEnc, seqs, clearY, copyDigest, copySaltY, clearEm, putSalt, putH, byteLoop, Code.x86_64Depth,
    Nat.max_le]
  omega_arith

/-- Code that is `safeI` and uses at most 16 bytes of stack keeps memory
outside the writable regions and the 16 bytes below `rsp`. -/
theorem WP.keepIn {c : Prog isa} (hc : c.allInstrs safeI = true) (hd : c.x86_64Depth ≤ 16) {u : State}
    {Q : State → Prop} (h : WP isa c u Q) :
    WP isa c u fun v => Q v ∧ ∀ a, (∀ r ∈ u.wr, ¬ r.Contains a 1) → ¬ (below (u.gpr .rsp) 16).Contains a 1 →
      v.mem a = u.mem a := by
  refine WP.mono (X86_64.WP.stackFrame (safe_sp hc) (by omega_using [hd]) h) fun v ⟨hq, hf⟩ => ⟨hq, fun a h1 h2 => ?_⟩
  refine Frame.below_mono hf hd (by decide) a fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact h1 r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact h2

end VG.Proof.RsaPss.X86_64

end

end

/-! ### `RsaPss.X86_64.SignFrame`, which this module and modules that import it used -/

section

/-! ### `RsaPss.X86_64.SignMain`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS on x86-64: the encoding

After the checks, `signEnc` leaves `EM` (`k` bytes, `emT`) at
`scratch + oEm` (`signEnc_ok`), from the digest and the salt, which it
reads where nothing it writes is.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off off_off)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)

/-- An address that no writable region of `wr` holds, nor the 16 bytes
below `F`. -/
def Outside (wr : List Region) (F a : Addr) : Prop :=
  (∀ r ∈ wr, ¬ r.Contains a 1) ∧ ¬ (below F 16).Contains a 1

/-- Bytes outside are not in our working space. -/
theorem Outside.ne {u : State} {F S : Addr} (L : Lay u F S) {a : Addr} (h : Outside u.wr F a) {x : Nat}
    (hx : x < oRsa) : a ≠ off S x := by
  intro he
  obtain ⟨r, hr, hc⟩ := L.sst8 (d := x) (by omega_using [hx])
  exact h.1 r hr (he ▸ hc)

theorem chain {u v v' : State} {F : Addr} (hw : v.wr = u.wr) (hsp : v.gpr .rsp = F)
    (hS : ∀ a, Outside u.wr F a → v.mem a = u.mem a)
    (hk : ∀ a, (∀ r ∈ v.wr, ¬ r.Contains a 1) → ¬ (below (v.gpr .rsp) 16).Contains a 1 → v'.mem a = v.mem a) :
    ∀ a, Outside u.wr F a → v'.mem a = u.mem a :=
  fun a ha => (hk a (hw ▸ ha.1) (hsp ▸ ha.2)).trans (hS a ha)

/-- Safety of a piece of code, by unfolding it. -/
macro "safe_by " "[" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| plain_simp_names (
                   simp only [$ds,*, Code.allInstrs, rec_all, List.all_append, byteLoop, step, Bool.and_true, Bool.true_and]
                   rfl))

/-- The bytes `n` at `p`, as a function. -/
def bytesF (m : Mem) (p : Addr) : Nat → Byte := fun i => m (p + BitVec.ofNat 64 i)

theorem getD_map_range (f : Nat → Byte) (n i : Nat) :
    ((List.range n).map f).getD i 0 = if i < n then f i else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  split
  · rename_i h; rw [List.getElem?_range h]; rfl
  · rename_i h; rw [List.getElem?_eq_none (by simp; omega_using [h])]; rfl

variable {H : Hash} (hH : HashOK H) (K : Callees H)

include hH in
theorem validG {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D) :
    Proof.Mgf1.Valid G := by
  refine ⟨hGl ▸ hH.hD0, fun x => ?_⟩
  rw [hGh, hH.hash, List.length_take, MdStream.Md.hash, hH.md.digest_length, hGl]
  exact Nat.min_eq_left hH.hDN

/-- `EM` from the bytes the blocks leave: `V5` (with `H` at `oDig`) cleared
over `EM`, `0x01` and the salt `sf`, `H` and `0xbc`, the mask XORed into
`DB` and its first byte ANDed with `c`. -/
theorem em_bytes {G : Spec.Mgf1.Hash} {V5 V9 sf : Nat → Byte} {k lo db sl D : Nat} {h saltB : List Byte}
    {c : Byte} (hdig : ∀ j < D, V5 (oDig + j) = h.getD j 0) (hh : h.length = D) (_hsl : saltB.length = sl)
    (hsf : ∀ j < sl, sf j = saltB.getD j 0) (hk : k ≤ 1024) (hlo : lo ≤ 1) (hdb : lo + db + D + 1 = k)
    (hfit : sl + 1 ≤ db) (hD : 0 < D) (hDk : D ≤ 64)
    (h9 : ∀ o < oRsa, ctOut o →
      V9 o = mixV (upd (cpV (cpV (upd (clrV V5 oEm k) (oEm + lo + db - sl - 1) 1) sf (oEm + lo + db - sl - 1 + 1) sl)
        (fun i => cpV (upd (clrV V5 oEm k) (oEm + lo + db - sl - 1) 1) sf (oEm + lo + db - sl - 1 + 1) sl (oDig + i))
        (oEm + lo + db) D) (oEm + k - 1) 0xbc)
        (Spec.Mgf1.mgf1 G ((List.range D).map fun i => upd (cpV (cpV (upd (clrV V5 oEm k) (oEm + lo + db - sl - 1) 1)
          sf (oEm + lo + db - sl - 1 + 1) sl) (fun i => cpV (upd (clrV V5 oEm k) (oEm + lo + db - sl - 1) 1) sf
            (oEm + lo + db - sl - 1 + 1) sl (oDig + i)) (oEm + lo + db) D) (oEm + k - 1) 0xbc (oEm + lo + db + i)) db)
        (oEm + lo) db o) :
    ∀ i < k, upd V9 (oEm + lo) (V9 (oEm + lo) &&& c) (oEm + i) = RsaPss.emT lo db sl saltB h (Spec.Mgf1.mgf1 G h db) c i := by
  generalize hP : oEm + lo + db - sl - 1 = P at h9
  generalize hK : oEm + k - 1 = K at h9
  obtain hP' : P + sl + 1 = oEm + lo + db := by rw [← hP]; have : oEm = 2560 := rfl; omega_using [hfit]
  obtain hK' : K + 1 = oEm + k := by rw [← hK]; have : oEm = 2560 := rfl; omega_using [this]
  clear hP hK
  have c1 : oEm = 2560 := rfl
  have c3 : oDig = 2304 := rfl
  have c5 : oRsa = 8192 := rfl
  have c6 : oLen = 2368 := rfl
  have c7 : oY = 3584 := rfl
  -- `V7`: `EM` with `0x01` and the salt, and `H` at `oDig` still.
  obtain hV7 : ∀ x, cpV (upd (clrV V5 oEm k) (P) 1) sf (P + 1) sl x =
      if oEm ≤ x ∧ x < oEm + k then
        (if (P + 1) ≤ x ∧ x < oEm + lo + db then saltB.getD (x - ((P + 1))) 0
          else if x = P then 1 else 0)
      else V5 x := fun x => by
    simp only [cpV, upd, clrV]
    by_cases h1 : P + 1 ≤ x ∧ x < P + 1 + sl
    · rw [ifp h1, ifp (by omega_using [hdb, hfit, hP', h1]), ifp (by omega_using [hP', h1]), hsf _ (by omega_using [h1]), show x - (P + 1) =
        x - ((P + 1)) by omega_using []]
    · rw [ifn h1]
      by_cases h2 : x = P
      · rw [ifp h2, ifp (by omega_using [hdb, hfit, hP', h2]), ifn (by omega_using [h2]), ifp h2]
      · rw [ifn h2]
        by_cases h3 : oEm ≤ x ∧ x < oEm + k
        · rw [ifp h3, ifp h3, ifn (by omega_using [hP', h1]), ifn h2]
        · rw [ifn h3, ifn h3]
  -- `H` after `DB`.
  obtain hHB : (List.range D).map (fun i => upd (cpV (cpV (upd (clrV V5 oEm k) (P) 1) sf
      (P + 1) sl) (fun i => cpV (upd (clrV V5 oEm k) (P) 1) sf
        (P + 1) sl (oDig + i)) (oEm + lo + db) D) (K) 0xbc (oEm + lo + db + i)) = h := by
    rw [← List.take_of_length_le (Nat.le_of_eq hh), ← range_map_getD (Nat.le_of_eq hh.symm)]
    refine List.map_congr_left fun j hj => ?_
    obtain hj := List.mem_range.mp hj
    simp only [upd, cpV, clrV]
    rw [ifn (by omega_using [hdb, hK', hj]), ifp (by omega_using [hj]), Nat.add_sub_cancel_left,
        ifn (by omega_using [hfit, hDk, hP', c1, c3, hj]), ifn (by omega_using [hfit, hDk, hP', c1, c3, hj]),
        ifn (by omega_using [hDk, c1, c3, hj]),
      hdig j hj]
  -- `V8`, over `EM`.
  obtain hV8 : ∀ x, oEm ≤ x → x < oEm + k → upd (cpV (cpV (upd (clrV V5 oEm k) (P) 1) sf
      (P + 1) sl) (fun i => cpV (upd (clrV V5 oEm k) (P) 1) sf
        (P + 1) sl (oDig + i)) (oEm + lo + db) D) (K) 0xbc x =
      if x = K then 0xbc else if oEm + lo + db ≤ x then h.getD (x - (oEm + lo + db)) 0
      else if (P + 1) ≤ x then saltB.getD (x - ((P + 1))) 0
      else if x = P then 1 else 0 := fun x h1 h2 => by
    simp only [upd]
    by_cases hx : x = K
    · rw [ifp hx, ifp hx]
    rw [ifn hx, ifn hx]
    simp only [cpV]
    by_cases hy : oEm + lo + db ≤ x
    · rw [ifp (show oEm + lo + db ≤ x ∧ x < oEm + lo + db + D by omega_using [hdb, hK', h2, hx, hy]), ifp hy,
        ifn (by omega_using [hdb, hfit, hDk, hP', c1, c3, h2])]
      simp only [upd, clrV]
      rw [ifn (by omega_using [hdb, hfit, hDk, hP', c1, c3, h2]), ifn (by omega_using [hdb, hDk, c1, c3, h2]),
          hdig _ (by omega_using [hdb, hK', h2, hx, hy])]
    rw [ifn (show ¬(oEm + lo + db ≤ x ∧ x < oEm + lo + db + D) by omega_using [hy]), ifn hy]
    have := hV7 x
    simp only [cpV] at this
    rw [this, ifp (show oEm ≤ x ∧ x < oEm + k by omega_using [h1, h2])]
    by_cases hz : (P + 1) ≤ x
    · rw [ifp (show (P + 1) ≤ x ∧ x < oEm + lo + db by omega_using [hy, hz]), ifp hz]
    · rw [ifn (show ¬((P + 1) ≤ x ∧ x < oEm + lo + db) by omega_using [hz]), ifn hz]
  intro i hi
  obtain hco : ctOut (oEm + i) := ⟨by omega_using [c1, c6], by omega_using [hk, c1, c7, hi]⟩
  simp only [upd, RsaPss.emT]
  by_cases hz : i = lo
  · rw [hz] at hco hi ⊢
    rw [ifp rfl, h9 _ (by omega_using [hlo, c1, c5]) hco, hHB, mixV, hV8 _ (by omega_using []) (by omega_using [hi])]
    simp (disch := omega_arith) only [↓ifp, ↓ifn, Nat.sub_self]
    by_cases hdz : db - sl - 1 = 0
    · simp (disch := omega_arith) only [↓ifp, ↓ifn]
    · simp (disch := omega_using [hh, _hsl, hk, hlo, hdb, hfit, hD, hDk, hP', hK', c1, c3, c5, c6, c7, hi, hz, hdz]) only [↓ifp, ↓ifn]
  · rw [ifn (show ¬ oEm + i = oEm + lo by omega_using [hz]), h9 _ (by omega_using [hk, c1, c5, hi]) hco, hHB, mixV,
      hV8 _ (by omega_using []) (by omega_using [hi])]
    rw [hh]
    by_cases hl : i < lo
    · simp (disch := omega_arith) only [↓ifp, ↓ifn]
    by_cases hj : i - lo < db
    · rw [show oEm + i - (oEm + lo) = i - lo by omega_using []]
      by_cases hs : db - sl ≤ i - lo
      · rw [show oEm + i - ((P + 1)) = i - lo - (db - sl) by omega_using [hfit, hP']]
        simp (disch := omega_arith) only [↓ifp, ↓ifn]
      · by_cases ho : i - lo = db - sl - 1
        · simp (disch := omega_arith) only [↓ifp, ↓ifn]
        · simp (disch := omega_arith) only [↓ifp, ↓ifn]
    · by_cases hH : i - lo < db + D
      · rw [show oEm + i - (oEm + lo + db) = i - lo - db by omega_using []]
        simp (disch := omega_arith) only [↓ifp, ↓ifn]
      · simp (disch := omega_arith) only [↓ifp, ↓ifn]

include K in
theorem signEnc_ok (lk : MgfLink H hH) {G : Stream} (hG : StreamOK G) {Gs : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {dn : String}
    {f : MdFns} {g : Impl.Mgf1.X86_64.Table.Fns} (hf : MdFnsSafe f) (hdk : DigOK H) {u : State} {F S : Addr}
    (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) (hT : HT H dn f W u.syms) (hGT : GT G g W u.syms)
    {k lo sl : Nat} {c : Byte} {dig q : Addr}
    (hk : W 17 = BitVec.ofNat 64 k) (hlo : W 26 = BitVec.ofNat 64 lo) (hc : W 25 = BitVec.setWidth 64 c)
    (hdg : W 37 = dig) (hq : W 39 = q) (hsl : W 40 = BitVec.ofNat 64 sl)
    (hk2 : k ≤ 1024) (hlo1 : lo ≤ 1) (hfit : H.D + sl + 2 ≤ k - lo)
    (hax : u.gpr .rax = BitVec.ofNat 64 (k - lo - (H.D + 2)))
    (hdR : ∀ i < H.D, InRegions (u.rd ++ u.wr) (dig + BitVec.ofNat 64 i) 1)
    (hdO : ∀ i < H.D, Outside u.wr F (dig + BitVec.ofNat 64 i))
    (hqR : ∀ i < sl, InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 i) 1)
    (hqO : ∀ i < sl, Outside u.wr F (q + BitVec.ofNat 64 i)) :
    let db := k - lo - H.D - 1
    let saltB := (List.range sl).map (bytesF u.mem q)
    let h := lk.G.hash (Spec.RsaPss.zeros 8 ++ (List.range H.D).map (bytesF u.mem dig) ++ saltB)
    WP isa (signEnc f H g) u fun u' => Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      ∃ V' W', Rep u'.mem F S V' W' ∧ (∀ j < nW, j < 23 ∨ 32 < j → W' j = W j) ∧
        ∀ i < k, V' (oEm + i) = RsaPss.emT lo db sl saltB h (Spec.Mgf1.mgf1 Gs h db) c i := by
  intro db saltB h
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c5 : oRsa = 8192 := rfl
  obtain hdb : k - lo - (H.D + 2) + 1 = db := by omega_using [hfit]
  rw [signEnc]
  simp only [seqs]
  -- `DB`'s slots.
  refine WP.seq (X86_64.WP.mono_syms (WP.keepIn (by safe_by [dbSlots]) (by exact Nat.zero_le 16)
    (dbSlots_ok L R hlo hax)) fun u1 ⟨⟨L1, k1, R1⟩, f1⟩ s1 => ?_)
  obtain hS1 := chain (u := u) rfl L.rsp (fun _ _ => rfl) f1
  rw [hdb] at R1
  -- `Y` cleared.
  refine WP.seq (X86_64.WP.mono_syms (WP.keepIn (by safe_by [clearY]) (by exact Nat.zero_le 16)
    (clearY_ok L1 R1)) fun u2 ⟨⟨L2, k2, hcx2, R2⟩, f2⟩ s2 => ?_)
  obtain hS2 := chain (u := u) k1.2.2 L1.rsp hS1 f2
  -- `mHash`.
  refine WP.seq (X86_64.WP.mono_syms (WP.keepIn (by safe_by [copyDigest]) (by exact Nat.zero_le 16)
    (copyDigest_ok hH L2 R2 (p := dig) (by simp [upd, hdg]) hcx2
      (fun i hi => by rw [k2.2.1, k2.2.2, k1.2.1, k1.2.2]; exact hdR i hi)
      (fun i hi j hj => Outside.ne L2 (by rw [k2.2.2, k1.2.2]; exact hdO i hi) (by omega_using [hDN, hN, c2, c5, hj]))))
    fun u3 ⟨⟨L3, k3, R3⟩, f3⟩ s3 => ?_)
  obtain hS3 := chain (u := u) (k2.2.2.trans k1.2.2) L2.rsp hS2 f3
  -- The salt.
  refine WP.seq (X86_64.WP.mono_syms (WP.keepIn (by safe_by [copySaltY]) (by exact Nat.zero_le 16)
    (copySaltY_ok hH L3 R3 (q := q) (sl := sl) (by simp [upd, hq]) (by simp [upd, hsl]) (by omega_using [hk2, hfit])
      ((k3.gpr (by decide)).trans hcx2)
      (fun i hi => by rw [k3.2.1, k3.2.2, k2.2.1, k2.2.2, k1.2.1, k1.2.2]; exact hqR i hi)
      (fun i hi j hj => Outside.ne L3 (by rw [k3.2.2, k2.2.2, k1.2.2]; exact hqO i hi) (by omega_using [hk2, hfit, c2, c5, hj]))))
    fun u4 ⟨⟨L4, k4, R4⟩, f4⟩ s4 => ?_)
  obtain hS4 := chain (u := u) (k3.2.2.trans (k2.2.2.trans k1.2.2)) L3.rsp hS3 f4
  -- The length of `M'`.
  refine WP.seq (X86_64.WP.mono_syms (WP.keepIn (by safe_by [signLen]) (by exact Nat.zero_le 16)
    (signLen_ok hH L4 R4 (sl := sl) (by simp [upd, hsl]) (by omega_using [hk2, hfit])))
    fun u5 ⟨⟨L5, k5, R5⟩, f5⟩ s5 => ?_)
  obtain sy5 : u5.syms = u.syms := s5.trans (s4.trans (s3.trans (s2.trans s1)))
  obtain hS5 := chain (u := u) (k4.2.2.trans (k3.2.2.trans (k2.2.2.trans k1.2.2))) L4.rsp hS4 f5
  -- `H`.
  set digB := (List.range H.D).map (bytesF u.mem dig) with hdigB
  set msg := Spec.RsaPss.zeros 8 ++ digB ++ saltB with hmsg
  obtain hml : msg.length = 8 + H.D + sl := by
    simp only [hmsg, hdigB, saltB, List.length_append, RsaPss.zeros_length, List.length_map, List.length_range]
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hL := hH.dims.L
  obtain hnb1 := Nat.lt_div_mul_add (a := 8 + H.D + sl + H.P.L) (b := H.P.B) hB0
  obtain hnb2 := Nat.div_mul_le_self (8 + H.D + sl + H.P.L) H.P.B
  refine WP.seq (X86_64.WP.mono_syms (WP.keepIn (ctHash_safe hH hf) (Nat.le_trans (ctHash_xd hf) (by decide))
    (ctHash_ok hH K L5 R5 (msg := msg) (nbm := (8 + H.D + sl + H.P.L) / H.P.B + 1)
      (by simp [upd, hml]) (by simp [upd]) (by rw [hml, Nat.succ_mul]; omega_using [hnb1])
          (by rw [Nat.succ_mul]; omega_using [hk2, hfit, hBl, hL, hnb2])
      (fun i hi => ?_) (by rw [sy5]; exact hT.congr rfl (by simp [upd]) (by simp [upd]) (by simp [upd])) hdk))
    fun u6 ⟨⟨L6, rd6, wr6, cs6, V5, W3, R6, hout6, hW6, hdig6⟩, f6⟩ s6 => ?_)
  · have hi' : i < 2048 := by rw [Nat.succ_mul] at hi; omega_using [hk2, hfit, hBl, hL, hnb2, hi]
    simp only [cpV, clrV, hmsg, getD_app, List.length_append, RsaPss.zeros_length, hdigB, saltB, List.length_map,
      List.length_range, getD_map_range, bytesF]
    by_cases h1 : i < 8
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega_using [h1]),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D) by omega_using [h1]),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + 2048 by omega_using [h1]), ifp (show i < 8 + H.D by omega_using [h1]), ifp h1,
        RsaPss.zeros_getD]
    by_cases h2 : i < 8 + H.D
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega_using [h2]),
        ifp (show oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D by omega_using [h1, h2]), ifp h2, ifn h1,
        ifp (show i - 8 < H.D by omega_using [h1, h2]), show oY + i - (oY + 8) = i - 8 by omega_using []]
      exact hS2 _ (hdO _ (by omega_using [h1, h2]))
    by_cases h3 : i < 8 + H.D + sl
    · rw [ifp (show oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl by omega_using [h2, h3]), ifn h2,
        ifp (show i - (8 + H.D) < sl by omega_using [h2, h3]), show oY + i - (oY + (8 + H.D)) = i - (8 + H.D) by omega_using []]
      exact hS3 _ (hqO _ (by omega_using [h2, h3]))
    · rw [ifn (show ¬(oY + (8 + H.D) ≤ oY + i ∧ oY + i < oY + (8 + H.D) + sl) by omega_using [h3]),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + H.D) by omega_using [h3]),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + 2048 by omega_using [hi']), ifn h2, ifn (show ¬ i - (8 + H.D) < sl by omega_using [h3])]
  obtain hS6 := chain (u := u) (k5.2.2.trans (k4.2.2.trans (k3.2.2.trans (k2.2.2.trans k1.2.2)))) L5.rsp hS5 f6
  obtain wr6' : u6.wr = u.wr := wr6.trans (k5.2.2.trans (k4.2.2.trans (k3.2.2.trans (k2.2.2.trans k1.2.2))))
  obtain rd6' : u6.rd = u.rd := rd6.trans (k5.2.1.trans (k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1))))
  obtain hW3 : ∀ j < nW, j ≠ 23 → j ≠ 24 → j ≠ 27 → j ≠ 28 → j ≠ 29 → j ≠ 30 → W3 j = W j := fun j hj a b c d e f => by
    rw [hW6 j hj e f]; simp [upd, a, b, c, d]
  obtain hW3' : ∀ j, j < nW → (j < 23 ∨ j = 25 ∨ j = 26 ∨ 30 < j) → W3 j = W j := fun j hj hj' =>
    hW3 j hj (by omega_using [hj']) (by omega_using [hj']) (by omega_using [hj']) (by omega_using [hj'])
        (by omega_using [hj']) (by omega_using [hj'])
  obtain h23 : W3 23 = off S (oEm + lo) := by rw [hW6 23 (by decide) (by decide) (by decide)]; simp [upd]
  obtain h24 : W3 24 = BitVec.ofNat 64 db := by rw [hW6 24 (by decide) (by decide) (by decide)]; simp [upd]
  -- `EM` cleared.
  refine WP.seq (X86_64.WP.mono_syms (WP.keepIn (by decide) (by exact Nat.zero_le 16)
    (clearEm_ok L6 R6 (k := k) (by rw [hW3' 17 (by decide) (by decide)]; exact hk) (by omega_using [hdb]) hk2))
    fun u7 ⟨⟨L7, k7, R7⟩, f7⟩ s7 => ?_)
  obtain hS7 := chain (u := u) wr6' L6.rsp hS6 f7
  -- `0x01` and the salt.
  refine WP.seq (X86_64.WP.mono_syms (putSalt_ok L7 R7 (e := oEm + lo) (db := db) (q := q) (sl := sl) h23 h24
    (by rw [hW3' 39 (by decide) (by decide)]; exact hq)
    (by rw [hW3' 40 (by decide) (by decide)]; exact hsl)
    (by omega_using [hfit]) (by omega_using [hk2, c1, c5, hdb]) (fun i hi => by rw [k7.2.1, k7.2.2, rd6', wr6']; exact hqR i hi)
    (fun i hi j hj => Outside.ne L7 (by rw [k7.2.2, wr6']; exact hqO i hi) (by omega_using [hk2, hfit, c1, c5, hj])))
    fun u8 ⟨L8, k8, R8⟩ s8 => ?_)
  -- `H` and `0xbc`.
  refine WP.seq (X86_64.WP.mono_syms (putH_ok hH L8 R8 (e := oEm + lo) (db := db) (k := k) h23 h24
    (by rw [hW3' 17 (by decide) (by decide)]; exact hk)
    (by omega_using []) (by omega_using [hdb]) hk2) fun u9 ⟨L9, k9, R9⟩ s9 => ?_)
  -- The mask.
  obtain T9 : GT G g W3 u9.syms := hGT.congr (s9.trans (s8.trans (s7.trans (s6.trans sy5)))) fun j h1 h2 =>
    hW3' j (by unfold nW frameBytes; omega_using [h2]) (Or.inl (by omega_using [h2]))
  refine WP.seq (WP.mono (mgfXor_ok hG hGh hGl hGv H L9 R9 T9 (e := oEm + lo) (db := db)
    ⟨by omega_using [], by omega_using [hdb], by omega_using [hk2, hdb]⟩ h23 h24) fun u10 ⟨L10, rd10, wr10, cs10, V9,
        W4, R10, hW10, hV10⟩ => ?_)
  -- The top bits.
  obtain h23' : W4 23 = off S (oEm + lo) := by rw [hW10 23 (by decide) (by omega_using []), h23]
  obtain h25' : W4 25 = BitVec.setWidth 64 c := by rw [hW10 25 (by decide) (by omega_using []), hW3' 25 (by decide) (by decide)]; exact hc
  refine WP.mono (clearTop_ok L10 R10 (e := oEm + lo) (c := c) h23' h25' (by omega_using [hlo1, c1, c5])) fun u11 ⟨L11, k11, R11⟩ => ?_
  refine ⟨L11, by rw [k11.2.1, rd10, k9.2.1, k8.2.1, k7.2.1, rd6'], by rw [k11.2.2, wr10, k9.2.2, k8.2.2, k7.2.2, wr6'],
    fun r hr => ?_, _, _, R11, fun j hj h' => by rw [hW10 j hj (by omega_using [h']), hW3' j hj (by omega_using [h'])], fun i hi => ?_⟩
  · rw [keep_cs k11 (by decide) r hr, cs10 r hr, keep_cs k9 (by decide) r hr, keep_cs k8 (by decide) r hr,
      keep_cs k7 (by decide) r hr, cs6 r hr, keep_cs k5 (by decide) r hr, keep_cs k4 (by decide) r hr,
      keep_cs k3 (by decide) r hr, keep_cs k2 (by decide) r hr, keep_cs k1 (by decide) r hr]
  -- The digest `H`, at `scratch + oDig`.
  obtain hh : h.length = H.D := by rw [← lk.len]; exact (validG hH lk.hash lk.len).2 _
  obtain hdig : ∀ j < H.D, V5 (oDig + j) = h.getD j 0 := fun j hj => by
    rw [map_range_getD hdig6 hj, ← lk.hash]
  refine em_bytes (V5 := V5) (sf := fun j => u7.mem (q + BitVec.ofNat 64 j)) (saltB := saltB) hdig hh
    (by simp [saltB]) (fun j hj => ?_) hk2 hlo1 (by omega_using [hdb]) (by omega_using [hfit]) hD (by omega_using [hDN, hN]) hV10 i hi
  simp only [saltB, getD_map_range, ifp hj, bytesF]
  exact hS7 _ (hqO j hj)

end VG.Proof.RsaPss.X86_64

end

end

/-!
# RSASSA-PSS signing on x86-64: the precondition by name, and the frame

`SPre` names the facts of `signK.pre`; the frame is the `frameBytes` bytes
below `rsp` (`fb`), within the stack the function uses (`stkR`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64

variable (tsH tsG : List FnTable)

/-- `signK.pre`, by name. -/
structure SPre (s : State) : Prop where
  sp1 : signStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 152 ≤ 2 ^ 64
  tabH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s T)
  tabG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 17) (FnTable.words isa s T)
  hsy : (tabFns tsH ++ tabFns tsG).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g)
  hrd : ∀ r ∈ ([⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩, ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩, ⟨stackArg s 8, (stackArg s 9).toNat⟩, ⟨stackArg s 10, (stackArg s 11).toNat⟩, ⟨stackArg s 12, (stackArg s 13).toNat⟩, ⟨stackArg s 16, 88⟩, ⟨stackArg s 17, 88⟩] : List Region), r ∈ s.rd
  hra : ∃ A, 144 ≤ A ∧ (⟨stackArgAddr s 0, A⟩ : Region) ∈ s.rd
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩]
  dOn : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dOe : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dOp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dOq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dOdp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dOdq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dOqi : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dOdg : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 10, (stackArg s 11).toNat⟩
  dOsa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dOtH : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 16, 88⟩
  dOtG : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 17, 88⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 144⟩
  dns : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  des : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dps : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dqs : (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  ddps : (⟨stackArg s 4, (stackArg s 5).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  ddqs : (⟨stackArg s 6, (stackArg s 7).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dqis : (⟨stackArg s 8, (stackArg s 9).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  ddgs : (⟨stackArg s 10, (stackArg s 11).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dsas : (⟨stackArg s 12, (stackArg s 13).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dstH : (⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 16, 88⟩
  dstG : (⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 17, 88⟩
  dsa : (⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 144⟩
  dRo : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRn : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dRe : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dRp : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dRq : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dRdp : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dRdq : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dRqi : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dRdg : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 10, (stackArg s 11).toNat⟩
  dRsa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dRtH : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 16, 88⟩
  dRtG : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 17, 88⟩
  dRa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 144⟩
  dKo : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dKp : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dKq : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dKdp : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dKdq : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dKqi : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dKdg : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 10, (stackArg s 11).toNat⟩
  dKsa : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dKtH : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 16, 88⟩
  dKtG : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 17, 88⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 144⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wN : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wP : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wQ : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wDp : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wDq : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  wQi : (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64
  wDg : (stackArg s 10).toNat + (stackArg s 11).toNat ≤ 2 ^ 64
  wSa : (stackArg s 12).toNat + (stackArg s 13).toNat ≤ 2 ^ 64
  wS : (stackArg s 14).toNat + (stackArg s 15).toNat * 8 ≤ 2 ^ 64
  wTH : (stackArg s 16).toNat + 88 ≤ 2 ^ 64
  wTG : (stackArg s 17).toNat + 88 ≤ 2 ^ 64
  lv : Spec.Rsa.lenValid (s.gpr .rcx).toNat
  hsi : (s.gpr .rsi).toNat = (s.gpr .rcx).toNat
  L1 : 1 ≤ (s.gpr .r9).toNat
  L2 : (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat
  pl1 : 1 ≤ (stackArg s 1).toNat
  pl2 : (stackArg s 1).toNat < (s.gpr .rcx).toNat
  ql1 : 1 ≤ (stackArg s 3).toNat
  ql2 : (stackArg s 3).toNat < (s.gpr .rcx).toNat
  hdpl : (stackArg s 5).toNat = (stackArg s 1).toNat
  hqil : (stackArg s 9).toNat = (stackArg s 1).toNat
  hdql : (stackArg s 7).toNat = (stackArg s 3).toNat
  hsw : Spec.RsaPss.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 15).toNat
  hdl : Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 16) (stackArg s 11)

variable {tsH tsG}

/-- A stack argument is in a region the caller reads. -/
theorem SPre.argIn {s u : State} (hp : SPre tsH tsG s) (hrd : u.rd = s.rd) {j : Nat} (hj : j < 18) :
    InRegions (u.rd ++ u.wr) (stackArgAddr s j) 8 := by
  obtain ⟨A, hA, hm⟩ := hp.hra
  refine ⟨_, List.mem_append_left _ (by rw [hrd]; exact hm), ?_⟩
  have e : stackArgAddr s j - stackArgAddr s 0 = BitVec.ofNat 64 (8 * j) := by
    rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []]
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  show (stackArgAddr s j - stackArgAddr s 0).toNat + 8 ≤ A
  rw [e, BitVec.toNat_ofNat]; omega_using [hj, hA]

/-- A region of the precondition's list is read. -/
theorem SPre.rdIn {s u : State} (hp : SPre tsH tsG s) (hrd : u.rd = s.rd) {r : Region}
    (hr : r ∈ ([⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩, ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩, ⟨stackArg s 8, (stackArg s 9).toNat⟩, ⟨stackArg s 10, (stackArg s 11).toNat⟩, ⟨stackArg s 12, (stackArg s 13).toNat⟩, ⟨stackArg s 16, 88⟩, ⟨stackArg s 17, 88⟩] : List Region)) :
    r ∈ u.rd ++ u.wr :=
  List.mem_append_left _ (by rw [hrd]; exact hp.hrd r hr)

theorem SPre.k1 {s : State} (hp : SPre tsH tsG s) : 64 ≤ (s.gpr .rcx).toNat := hp.lv.1
theorem SPre.k2 {s : State} (hp : SPre tsH tsG s) : (s.gpr .rcx).toNat ≤ 1024 := hp.lv.2
theorem SPre.hsl {s : State} (hp : SPre tsH tsG s) : 16 * (s.gpr .rcx).toNat + 32 + 1024 ≤ (stackArg s 15).toNat := by
  have := hp.hsw; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]

/-! ## The frame -/

/-- The frame's base: `rsp` in the frame. -/
abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses, below `rsp`. -/
def stkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩

theorem sub_sub' (p : Addr) (a b : Nat) : p - BitVec.ofNat 64 a - BitVec.ofNat 64 b = p - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

theorem frame_sub (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (stkR s) :=
  Offset.sub_below _ (by decide) (by decide)

theorem ret_sub (s : State) : Region.Sub (below (fb s) 16) (stkR s) := by
  simp only [below, fb, sub_sub']
  exact Offset.sub_below _ (by decide) (by decide)

theorem ret8_sub (s : State) : Region.Sub (below (fb s) 8) (stkR s) := by
  simp only [below, fb, sub_sub']
  exact Offset.sub_below _ (by decide) (by decide)

end VG.Proof.RsaPss.X86_64

end

end

/-!
# RSASSA-PSS signing on x86-64: the prologue

From the entry state, after the frame's push, `signPrologue` saves `rbx`,
`rbp` and `r12` and the arguments to their slots, and `n0` reads the
modulus' first byte (`signPro_ok`): the working space and the frame as
`Rep` says, with nothing else written.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable {tsH tsG : List FnTable}

theorem fb_toNat {s : State} (hp : SPre tsH tsG s) : (fb s).toNat + frameBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; unfold signStack Proof.Rsa.X86_64.stackBytes at this
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega_using [this]

theorem SPre.geo {s : State} (hp : SPre tsH tsG s) : Geo (fb s) (stackArg s 14) := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hsl := hp.hsl
  have hk := hp.k1
  have wS := hp.wS
  have sS : Region.Sub ⟨stackArg s 14, oRsa⟩ ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ :=
    Region.sub_prefix (by unfold oRsa; omega_using [hsl])
  refine ⟨by omega_using [hF, this], by unfold oRsa; omega_using [hsl, wS], ((hp.dKs.sub_left (frame_sub s)).sub_right sS),
    ((hp.dKs.sub_left (ret_sub s)).sub_right sS)⟩

/-- The address of stack argument `j`, from the frame. -/
theorem argAddr (s : State) (j : Nat) : off (fb s) (frameBytes + 8 + 8 * j) = stackArgAddr s j := by
  simp only [off, fb, stackArgAddr]
  rw [show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega_using [], BitVec.ofNat_add, ← BitVec.add_assoc,
    BitVec.sub_add_cancel]

theorem allocState_gpr' (bytes : Nat) (s : State) (r : Reg) :
    (allocState bytes s).gpr r = if r = .rsp then s.gpr .rsp - BitVec.ofNat 64 bytes else s.gpr r := rfl

/-- The frame's region. -/
abbrev frR (s : State) : Region := ⟨fb s, frameBytes⟩

/-- Stack argument `j`, read from memory changed only in the frame. -/
theorem arg_read {s : State} (hp : SPre tsH tsG s) {m : Mem} (hf : Frame [frR s] s.mem m) {j : Nat} (hj : j < 18) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := ⟨stackArgAddr s 0, 144⟩) ?_ (fun r' hr' => ?_) (by decide)
  · rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.dKa.sub_left (frame_sub s)).symm

/-- One stack argument copied to a slot. -/
theorem copy1_ok {s : State} (hp : SPre tsH tsG s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j d : Nat} (hj : j < 18) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block [.mov .rax (.mem (arg j)), .store (sp d) .rax]) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by omega_using [hF])
  have hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    rw [argAddr]; exact hp.argIn hrd hj
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm, hm ▸ hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd, hF]))⟩
  xrun [arg, ea_sp, hsp, hin, arg_read hp hf hj, hsc.st (d := d) hd]

theorem frame_w {s : State} (hp : SPre tsH tsG s) {m m' : Mem} (hf : Frame [frR s] m m') {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : Frame [frR s] m (m'.writeW (off (fb s) d) v) := by
  have hF := fb_toNat hp
  have := hp.sp2
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd, hF]))

/-- The slots `signPrologue` stores to, and what. -/
def proW (s : State) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (fun k => word s.mem (fb s) (8 * k))
    41 (s.gpr .rbx)) 42 (s.gpr .rbp)) 43 (s.gpr .r12)) 16 (s.gpr .rdi)) 18 (s.gpr .rdx)) 17 (s.gpr .rcx))
    19 (s.gpr .r8)) 20 (s.gpr .r9)) 37 (stackArg s 10)) 39 (stackArg s 12)) 40 (stackArg s 13)) 21 (stackArg s 14))
    22 (stackArg s 15)

theorem signPrologue_eq : signPrologue =
    ([.store (sp sRbx) .rbx, .store (sp sRbp) .rbp, .store (sp sR12) .r12, .store (sp sOut) .rdi,
      .store (sp sN) .rdx, .store (sp sK) .rcx, .store (sp sE) .r8, .store (sp sEl) .r9] : List Instr) ++
    ([.mov .rax (.mem (arg 10)), .store (sp sDig) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 12)), .store (sp sSalt) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 13)), .store (sp sSaltLen) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 14)), .store (sp sScr) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 15)), .store (sp sScrLen) .rax] : List Instr) := rfl

/-- The prologue: the slots as `proW` says, the working space untouched. -/
theorem signPro_ok {s : State} (hp : SPre tsH tsG s) :
    WP isa (.block signPrologue) (allocState frameBytes s) fun t => Keep [.rax] (allocState frameBytes s) t ∧
      Lay t (fb s) (stackArg s 14) ∧ Rep t.mem (fb s) (stackArg s 14) (fun o => s.mem (off (stackArg s 14) o)) (proW s) ∧
      Frame [frR s] s.mem t.mem := by
  have hF := fb_toNat hp
  have := hp.sp2
  have G' := hp.geo
  set A := allocState frameBytes s with hA
  have hsp : A.gpr .rsp = fb s := rfl
  have hfr : frR s ∈ A.wr := List.mem_cons_self ..
  have hsc : Scr A (fb s) frameBytes := Scr.of_mem hfr (by omega_using [hF])
  have R0 : Rep s.mem (fb s) (stackArg s 14) (fun o => s.mem (off (stackArg s 14) o))
      (fun k => word s.mem (fb s) (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [signPrologue_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  have R1 := ((((((((R0.wf G' (k := 41) (by decide) (s.gpr .rbx)).wf G' (k := 42) (by decide) (s.gpr .rbp)).wf G'
    (k := 43) (by decide) (s.gpr .r12)).wf G' (k := 16) (by decide) (s.gpr .rdi)).wf G' (k := 18) (by decide)
    (s.gpr .rdx)).wf G' (k := 17) (by decide) (s.gpr .rcx)).wf G' (k := 19) (by decide) (s.gpr .r8)).wf G'
    (k := 20) (by decide) (s.gpr .r9))
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = (((((((s.mem.writeW (off (fb s) (8 * 41)) (s.gpr .rbx)).writeW
      (off (fb s) (8 * 42)) (s.gpr .rbp)).writeW (off (fb s) (8 * 43)) (s.gpr .r12)).writeW (off (fb s) (8 * 16))
      (s.gpr .rdi)).writeW (off (fb s) (8 * 18)) (s.gpr .rdx)).writeW (off (fb s) (8 * 17)) (s.gpr .rcx)).writeW
      (off (fb s) (8 * 19)) (s.gpr .r8)).writeW (off (fb s) (8 * 20)) (s.gpr .r9)) ?_ rfl) fun t1 ⟨hm1, k1⟩ => ?_
  · xrun [ea_sp, hsp, hsc.st (d := sRbx) (by decide), hsc.st (d := sRbp) (by decide), hsc.st (d := sR12) (by decide),
      hsc.st (d := sOut) (by decide), hsc.st (d := sN) (by decide), hsc.st (d := sK) (by decide),
      hsc.st (d := sE) (by decide), hsc.st (d := sEl) (by decide), allocState_gpr']
    rfl
  have f1 : Frame [frR s] s.mem t1.mem := by
    rw [hm1]
    exact frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp (frame_w hp
      (Frame.refl _ _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _)
      (by decide) _) (by decide) _
  have sp1 : t1.gpr .rsp = fb s := k1.gpr (by decide)
  refine WP.mono (copy1_ok hp sp1 (k1.2.2 ▸ hfr) k1.2.1 f1 (j := 10) (d := sDig) (by decide) (by decide))
    fun t2 ⟨k2, hm2, f2⟩ => ?_
  refine WP.mono (copy1_ok hp ((k2.gpr (by decide)).trans sp1) (k2.2.2 ▸ k1.2.2 ▸ hfr) (k2.2.1.trans k1.2.1) f2
    (j := 12) (d := sSalt) (by decide) (by decide)) fun t3 ⟨k3, hm3, f3⟩ => ?_
  have k23 := k2.trans k3
  refine WP.mono (copy1_ok hp ((k23.gpr (by decide)).trans sp1) (k23.2.2 ▸ k1.2.2 ▸ hfr) (k23.2.1.trans k1.2.1) f3
    (j := 13) (d := sSaltLen) (by decide) (by decide)) fun t4 ⟨k4, hm4, f4⟩ => ?_
  have k24 := k23.trans k4
  refine WP.mono (copy1_ok hp ((k24.gpr (by decide)).trans sp1) (k24.2.2 ▸ k1.2.2 ▸ hfr) (k24.2.1.trans k1.2.1) f4
    (j := 14) (d := sScr) (by decide) (by decide)) fun t5 ⟨k5, hm5, f5⟩ => ?_
  have k25 := k24.trans k5
  refine WP.mono (copy1_ok hp ((k25.gpr (by decide)).trans sp1) (k25.2.2 ▸ k1.2.2 ▸ hfr) (k25.2.1.trans k1.2.1) f5
    (j := 15) (d := sScrLen) (by decide) (by decide)) fun t6 ⟨k6, hm6, f6⟩ => ?_
  have k16 : Keep [.rax] A t6 := (k1.trans (k25.trans k6)).mono (by decide)
  have R6 : Rep t6.mem (fb s) (stackArg s 14) (fun o => s.mem (off (stackArg s 14) o)) (proW s) := by
    rw [hm6, hm5, hm4, hm3, hm2, hm1]
    exact ((((R1.wf G' (k := 37) (by decide) (stackArg s 10)).wf G' (k := 39) (by decide) (stackArg s 12)).wf G'
      (k := 40) (by decide) (stackArg s 13)).wf G' (k := 21) (by decide) (stackArg s 14)).wf G' (k := 22) (by decide)
      (stackArg s 15)
  have h392 : frameBytes = 392 := rfl
  have hss : signStack = 3656 := rfl
  have := hp.sp1
  refine ⟨k16, ⟨(k16.gpr (by decide)).trans hsp, k16.2.2 ▸ hfr, by omega_using [hF, h392, hss, this], by omega_arith, ?_, ?_, G'.dFS, G'.dRS⟩, R6, f6⟩
  · have hsl := hp.hsl
    have hk := hp.k1
    refine ⟨⟨stackArg s 14, 0, (stackArg s 15).toNat * 8, by rw [k16.2.2, hA]; simp [allocState, hp.hwr], (BitVec.add_zero _).symm,
      by unfold oRsa; omega_using [hsl], hp.wS.trans' (by omega_using [])⟩, G'.Sw⟩
  · rw [show sScr = 8 * 21 from rfl]
    exact (R6.fr 21 (by decide)).trans (by simp [proW, upd])

end VG.Proof.RsaPss.X86_64
