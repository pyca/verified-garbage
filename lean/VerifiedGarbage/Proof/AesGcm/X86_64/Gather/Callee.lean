import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Contract

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: the functions called

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather`
calls `vg_aes_gcm_stream_init`, `vg_aes_gcm_stream_aad`,
`vg_aes_gcm_stream_encrypt_to` and `vg_aes_gcm_stream_finish` as artifacts,
each with its working space in a frame of its own, so what the proof needs
of each is its shared contract (`Spec/Gcm/Contract.lean`,
`Spec/Gcm/OutOfPlace.lean`), in the terms of this target: a contract whose
precondition is the layout the call gives it (`initK`, `aadK`, `toK`,
`finK`), which implies the shared one's, and whose postcondition is the
shared one's (`CallFn.ofSpec`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64
open VG.Impl.AesGcm.X86_64 (Fn)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args ret rounds)

/-- An implementation of a function, by the contract `k`, that writes `rsp`
only in its frames, uses at most `d` bytes of stack and loads no `mxcsr`. -/
structure CallFn (k : Contract isa) (d : Nat) where
  fn : Fn
  ok : ∀ s, k.pre s → ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ k.post s s'
  ct : ConstantTime isa k.pre k.pub fn.code
  sp : SpSafe fn.code
  xd : fn.code.x86_64Depth ≤ d
  mx : fn.code.allInstrs (fun i => !loadsMxcsr i) = true
  spAll : fn.code.all (fun i => !X86_64.isa.writesSp i) = true

/-- A function by `k`, from its proof against a contract `k'` that `k`'s
precondition and public data imply, and whose postcondition implies `k`'s. -/
def CallFn.ofSpec {k k' : Contract isa} {d : Nat} (f : Fn) (hv : Verified X86_64.target f.code k')
    (hpre : ∀ s, k.pre s → k'.pre s) (hpost : ∀ s s', k.pre s → k'.post s s' → k.post s s')
    (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → k'.pub s₁ s₂)
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ d)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : CallFn k d where
  fn := f
  ok s h := by
    obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (hpre s h)
    exact ⟨t, s', he, ha, hpost s s' h hp⟩
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂ := hv.2.1 s₁ s₂ t₁ t₂ s₁' s₂' (hpre _ h₁) (hpre _ h₂) (hpub _ _ hq) e₁ e₂
  sp := SpSafe.of_all sp
  xd := xd
  mx := mx
  spAll := sp

/-! ## `vg_aes_gcm_stream_init(ctx = rdi, nonce = rsi, nonce_len = rdx, state = rcx)` -/

def initPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let nonce : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
  let st : Region := ⟨s.gpr .rcx, 80⟩
  let stk : Region := below (s.gpr .rsp) 2576
  s.rd = [ctx, nonce] ∧ s.wr = [st] ∧ ctx.Disjoint st ∧ nonce.Disjoint st ∧
    (ret s).Disjoint ctx ∧ (ret s).Disjoint nonce ∧ (ret s).Disjoint st ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint st ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + 80 ≤ 2 ^ 64 ∧ 2576 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 8 ≤ 2 ^ 64

def initPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

def initK : Contract isa where
  pre := initPre
  post := Proof.AesGcm.streamInitX86_64.post
  pub := initPub

theorem initSpec_pre {s : State} (h : initPre s) : (Spec.Gcm.streamInitContract X86_64.abi 2576).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅⟩ := h
  sig_pre [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, X86_64.abi, X86_64.argRegs,
    Proof.AesGcm.ret, VG.X86_64.below, List.getD, List.range, List.range.loop]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.ret, VG.X86_64.below, Nat.mul_one] at *
  all_goals first
    | with_reducible assumption
    | trivial
    | omega

theorem initSpec_post {s s' : State} (h : (Spec.Gcm.streamInitContract X86_64.abi 2576).post s s') :
    Proof.AesGcm.streamInitX86_64.post s s' := by
  sig_post [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, X86_64.abi, X86_64.argRegs,
    Spec.Gcm.streamInitPost] at h
  sig_reduce [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, X86_64.abi, X86_64.argRegs] at h
  exact h

theorem initSpec_pub {s₁ s₂ : State} (h : initPub s₁ s₂) :
    (Spec.Gcm.streamInitContract X86_64.abi 2576).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅⟩ := h
  sig_pub [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, X86_64.abi, X86_64.argRegs]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-! ## `vg_aes_gcm_stream_aad(ctx = rdi, state = rsi, aad_len = rdx, data = rcx, len = r8)` -/

def aadPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let st : Region := ⟨s.gpr .rsi, 80⟩
  let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let stk : Region := below (s.gpr .rsp) 2576
  s.rd = [ctx, data] ∧ s.wr = [st] ∧ ctx.Disjoint st ∧ st.Disjoint data ∧
    (ret s).Disjoint ctx ∧ (ret s).Disjoint st ∧ (ret s).Disjoint data ∧
    stk.Disjoint ctx ∧ stk.Disjoint st ∧ stk.Disjoint data ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ 2576 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 8 ≤ 2 ^ 64

def aadPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

def aadK : Contract isa where
  pre := aadPre
  post := Proof.AesGcm.streamAadX86_64.post
  pub := aadPub

theorem aadSpec_pre {s : State} (h : aadPre s) : (Spec.Gcm.streamAadContract X86_64.abi 2576).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅⟩ := h
  sig_pre [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, X86_64.abi, X86_64.argRegs,
    Proof.AesGcm.ret, VG.X86_64.below, List.getD, List.range, List.range.loop]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.ret, VG.X86_64.below, Nat.mul_one] at *
  all_goals first
    | with_reducible assumption
    | trivial
    | omega

theorem aadSpec_post {s s' : State} (h : (Spec.Gcm.streamAadContract X86_64.abi 2576).post s s') :
    Proof.AesGcm.streamAadX86_64.post s s' := by
  sig_post [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, X86_64.abi, X86_64.argRegs,
    Spec.Gcm.streamAadPost] at h
  sig_reduce [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, X86_64.abi, X86_64.argRegs] at h
  exact h

theorem aadSpec_pub {s₁ s₂ : State} (h : aadPub s₁ s₂) :
    (Spec.Gcm.streamAadContract X86_64.abi 2576).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := h
  sig_pub [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, X86_64.abi, X86_64.argRegs]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-! ## `vg_aes_gcm_stream_finish(ctx = rdi, rounds = rsi, state = rdx, aad_len = rcx, text_len = r8, tag = r9)` -/

def finPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let st : Region := ⟨s.gpr .rdx, 80⟩
  let tag : Region := ⟨s.gpr .r9, 16⟩
  let stk : Region := below (s.gpr .rsp) 2584
  s.rd = [ctx] ∧ s.wr = [st, tag] ∧ ctx.Disjoint st ∧ ctx.Disjoint tag ∧ st.Disjoint tag ∧
    (ret s).Disjoint ctx ∧ (ret s).Disjoint st ∧ (ret s).Disjoint tag ∧
    stk.Disjoint ctx ∧ stk.Disjoint st ∧ stk.Disjoint tag ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 16 ≤ 2 ^ 64 ∧
    2584 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 8 ≤ 2 ^ 64 ∧ rounds s

def finPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp

def finK : Contract isa where
  pre := finPre
  post := Proof.AesGcm.streamFinishX86_64.post
  pub := finPub

theorem finSpec_pre {s : State} (h : finPre s) : (Spec.Gcm.streamFinishContract X86_64.abi 2584).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇⟩ := h
  sig_pre [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre, X86_64.abi,
    X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre, X86_64.abi,
    X86_64.argRegs, Proof.AesGcm.ret, VG.X86_64.below, List.getD, List.range, List.range.loop]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.ret, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds] at *
  all_goals first
    | with_reducible assumption
    | trivial
    | omega

theorem finSpec_post {s s' : State} (hR : rounds s) (h : (Spec.Gcm.streamFinishContract X86_64.abi 2584).post s s') :
    Proof.AesGcm.streamFinishX86_64.post s s' := by
  sig_post [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre, X86_64.abi,
    X86_64.argRegs, Spec.Gcm.streamFinishPost] at h
  sig_reduce [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, X86_64.abi, X86_64.argRegs] at h
  exact h hR

theorem finSpec_pub {s₁ s₂ : State} (h : finPub s₁ s₂) :
    (Spec.Gcm.streamFinishContract X86_64.abi 2584).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩ := h
  sig_pub [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, X86_64.abi, X86_64.argRegs]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-! ## `vg_aes_gcm_stream_encrypt_to(ctx = rdi, rounds = rsi, state = rdx, aad_len = rcx,
text_len = r8, src = r9, len = [rsp + 8], dst = [rsp + 16], dst_len = [rsp + 24])` -/

/-- What a call of `vg_aes_gcm_stream_encrypt_to` needs, for a key context
of kind `M`: the layout of its shared contract with 4856 bytes of stack. -/
def toPre (M : CtxMode) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, M.len⟩
  let st : Region := ⟨s.gpr .rdx, 80⟩
  let src : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let dst : Region := ⟨arg s 1, (arg s 2).toNat⟩
  let stk : Region := below (s.gpr .rsp) 4856
  s.rd = [ctx, src, args s 3] ∧ s.wr = [st, dst] ∧ arg s 2 = arg s 0 ∧
    ctx.Disjoint st ∧ ctx.Disjoint dst ∧ st.Disjoint src ∧ st.Disjoint dst ∧ st.Disjoint (args s 3) ∧
    src.Disjoint dst ∧ dst.Disjoint (args s 3) ∧
    (ret s).Disjoint ctx ∧ (ret s).Disjoint st ∧ (ret s).Disjoint src ∧ (ret s).Disjoint dst ∧
    (ret s).Disjoint (args s 3) ∧
    stk.Disjoint ctx ∧ stk.Disjoint st ∧ stk.Disjoint src ∧ stk.Disjoint dst ∧ stk.Disjoint (args s 3) ∧
    (s.gpr .rdi).toNat + M.len ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (arg s 0).toNat ≤ 2 ^ 64 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 64 ∧
    4856 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 ∧ rounds s ∧ M.ok s.mem (s.gpr .rdi)

def toPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2

def toK (M : CtxMode) : Contract isa where
  pre := toPre M
  post := Proof.AesGcm.streamToPost
  pub := toPub

theorem toSpec_pre {s : State} (h : toPre CtxMode.base s) :
    (Spec.Gcm.streamEncryptToContract X86_64.abi 4856).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, -⟩ := h
  sig_pre [Spec.Gcm.streamEncryptToContract, Spec.Gcm.streamEncryptToSig, Spec.Gcm.streamEncryptToPre,
    X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamEncryptToContract, Spec.Gcm.streamEncryptToSig, Spec.Gcm.streamEncryptToPre,
    X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.base] at *
  all_goals first
    | with_reducible assumption
    | omega
    | exact congrArg (BitVec.setWidth 64) a₃

theorem toSpecP_pre {s : State} (h : toPre CtxMode.powers s) :
    (Spec.Gcm.streamEncryptToPrecomputedContract X86_64.abi 4856).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈⟩ := h
  sig_pre [Spec.Gcm.streamEncryptToPrecomputedContract, Spec.Gcm.streamEncryptToPrecomputedSig,
    Spec.Gcm.streamEncryptToPrecomputedPre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamEncryptToPrecomputedContract, Spec.Gcm.streamEncryptToPrecomputedSig,
    Spec.Gcm.streamEncryptToPrecomputedPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg,
    X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.powers] at *
  all_goals first
    | with_reducible assumption
    | omega
    | exact congrArg (BitVec.setWidth 64) a₃

theorem toSpec_post {s s' : State} (hR : rounds s) (h : (Spec.Gcm.streamEncryptToContract X86_64.abi 4856).post s s') :
    Proof.AesGcm.streamToPost s s' := by
  sig_post [Spec.Gcm.streamEncryptToContract, Spec.Gcm.streamEncryptToSig, Spec.Gcm.streamEncryptToPre,
    X86_64.abi, X86_64.argRegs, Spec.Gcm.streamEncryptToPost] at h
  sig_reduce [Spec.Gcm.streamEncryptToContract, Spec.Gcm.streamEncryptToSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem toSpecP_post {s s' : State} (hR : rounds s)
    (h : (Spec.Gcm.streamEncryptToPrecomputedContract X86_64.abi 4856).post s s') :
    Proof.AesGcm.streamToPost s s' := by
  sig_post [Spec.Gcm.streamEncryptToPrecomputedContract, Spec.Gcm.streamEncryptToPrecomputedSig,
    Spec.Gcm.streamEncryptToPrecomputedPre, X86_64.abi, X86_64.argRegs, Spec.Gcm.streamEncryptToPost] at h
  sig_reduce [Spec.Gcm.streamEncryptToPrecomputedContract, Spec.Gcm.streamEncryptToPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem toSpec_pub {s₁ s₂ : State} (h : toPub s₁ s₂) :
    (Spec.Gcm.streamEncryptToContract X86_64.abi 4856).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀⟩ := h
  sig_pub [Spec.Gcm.streamEncryptToContract, Spec.Gcm.streamEncryptToSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamEncryptToContract, Spec.Gcm.streamEncryptToSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

theorem toSpecP_pub {s₁ s₂ : State} (h : toPub s₁ s₂) :
    (Spec.Gcm.streamEncryptToPrecomputedContract X86_64.abi 4856).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀⟩ := h
  sig_pub [Spec.Gcm.streamEncryptToPrecomputedContract, Spec.Gcm.streamEncryptToPrecomputedSig, X86_64.abi,
    X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamEncryptToPrecomputedContract, Spec.Gcm.streamEncryptToPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-! ## The functions called -/

abbrev InitFn := CallFn initK 2576
abbrev AadFn := CallFn aadK 2576
abbrev FinFn := CallFn finK 2584
abbrev ToFn (M : CtxMode) := CallFn (toK M) 4856

/-- `vg_aes_gcm_stream_init` from its shared contract. -/
def InitFn.ofSpec (f : Fn) (hv : Verified X86_64.target f.code (Spec.Gcm.streamInitContract X86_64.abi 2576))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2576)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : InitFn :=
  CallFn.ofSpec f hv (fun _ h => initSpec_pre h) (fun _ _ _ h => initSpec_post h) (fun _ _ h => initSpec_pub h)
    sp xd mx

/-- `vg_aes_gcm_stream_aad` from its shared contract. -/
def AadFn.ofSpec (f : Fn) (hv : Verified X86_64.target f.code (Spec.Gcm.streamAadContract X86_64.abi 2576))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2576)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : AadFn :=
  CallFn.ofSpec f hv (fun _ h => aadSpec_pre h) (fun _ _ _ h => aadSpec_post h) (fun _ _ h => aadSpec_pub h)
    sp xd mx

/-- `vg_aes_gcm_stream_finish` from its shared contract. -/
def FinFn.ofSpec (f : Fn) (hv : Verified X86_64.target f.code (Spec.Gcm.streamFinishContract X86_64.abi 2584))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2584)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : FinFn :=
  CallFn.ofSpec f hv (fun _ h => finSpec_pre h)
    (fun _ _ h h' => finSpec_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 h') (fun _ _ h => finSpec_pub h) sp xd mx

/-- `vg_aes_gcm_stream_encrypt_to` from its shared contract. -/
def ToFn.ofBase (f : Fn) (hv : Verified X86_64.target f.code (Spec.Gcm.streamEncryptToContract X86_64.abi 4856))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 4856)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : ToFn CtxMode.base :=
  CallFn.ofSpec f hv (fun _ h => toSpec_pre h)
    (fun _ _ h h' => toSpec_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h')
    (fun _ _ h => toSpec_pub h) sp xd mx

/-- `vg_aes_gcm_stream_encrypt_to_precomputed` from its shared contract. -/
def ToFn.ofPowers (f : Fn)
    (hv : Verified X86_64.target f.code (Spec.Gcm.streamEncryptToPrecomputedContract X86_64.abi 4856))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 4856)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : ToFn CtxMode.powers :=
  CallFn.ofSpec f hv (fun _ h => toSpecP_pre h)
    (fun _ _ h h' => toSpecP_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h')
    (fun _ _ h => toSpecP_pub h) sp xd mx

end VG.Proof.AesGcm.X86_64.Gather
