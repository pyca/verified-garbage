import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Contract
import VerifiedGarbage.Proof.AesGcm.X86_64.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Spec.Gcm.Precomputed
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.AesGcm.X86_64

/-!
# AES-GCM streaming encryption out of place, x86-64: the functions called

Untrusted: everything here is checked by Lean. What
`vg_aes_gcm_stream_encrypt_to` needs of the functions it calls, by their
contracts in the terms of this target: `vg_aes_gcm_encrypt_blocks_to`
(`BlkToFn`, by `encryptBlocksToX86_64M`) and `vg_aes_gcm_stream_encrypt`
(`EncFn`, by `encK`). The latter is called as an artifact, with its working
space in a frame of its own, so its proof is its shared contract's
(`Spec.Gcm.streamEncryptContract`, or `_precomputed`'s), which `encK`'s
precondition implies (`encSpec_pre`), and whose postcondition is `encK`'s
(`encSpec_post`): `EncFn.ofBase` and `EncFn.ofPowers`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64
open VG.Impl.AesGcm.X86_64 (Fn)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args)

/-- What a call of `vg_aes_gcm_stream_encrypt(ctx = rdi, rounds = rsi,
state = rdx, aad_len = rcx, text_len = r8, data = r9, len = [rsp + 8])`
needs, for a key context of kind `M`: the layout of its shared contract with
2608 bytes of stack. -/
def encCallPre (M : CtxMode) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, M.len⟩
  let st : Region := ⟨s.gpr .rdx, 80⟩
  let data : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let stk : Region := below (s.gpr .rsp) 2608
  s.rd = [ctx, args s 1] ∧ s.wr = [st, data] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ st.Disjoint data ∧ st.Disjoint (args s 1) ∧ data.Disjoint (args s 1) ∧
    (Proof.AesGcm.ret s).Disjoint ctx ∧ (Proof.AesGcm.ret s).Disjoint st ∧ (Proof.AesGcm.ret s).Disjoint data ∧
    (Proof.AesGcm.ret s).Disjoint (args s 1) ∧
    stk.Disjoint ctx ∧ stk.Disjoint st ∧ stk.Disjoint data ∧ stk.Disjoint (args s 1) ∧
    (s.gpr .rdi).toNat + M.len ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (arg s 0).toNat ≤ 2 ^ 64 ∧
    2608 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧ Proof.AesGcm.rounds s ∧
    M.ok s.mem (s.gpr .rdi)

/-- The public arguments of `vg_aes_gcm_stream_encrypt`. -/
def encCallPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ arg s₁ 0 = arg s₂ 0

/-- `vg_aes_gcm_stream_encrypt`, called with the layout of its shared
contract, for a key context of kind `M`. -/
def encK (M : CtxMode) : Contract isa where
  pre := encCallPre M
  post := Proof.AesGcm.streamEncryptX86_64.post
  pub := encCallPub

theorem encSpec_pre {s : State} (h : encCallPre CtxMode.base s) :
    (Spec.Gcm.streamEncryptContract X86_64.abi 2608).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁
  clear h
  sig_pre [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre, X86_64.abi,
    X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre, X86_64.abi,
    X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr,
    List.getD, List.range, List.range.loop, VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr,
    VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.base] at *
  all_goals first
    | with_reducible assumption
    | omega

theorem encSpecP_pre {s : State} (h : encCallPre CtxMode.powers s) :
    (Spec.Gcm.streamEncryptPrecomputedContract X86_64.abi 2608).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁
  have a₂₂ := h
  clear h
  sig_pre [Spec.Gcm.streamEncryptPrecomputedContract, Spec.Gcm.streamCryptPrecomputedSig,
    Spec.Gcm.streamTextPrecomputedPre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamEncryptPrecomputedContract, Spec.Gcm.streamCryptPrecomputedSig,
    Spec.Gcm.streamTextPrecomputedPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr,
    VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.powers] at *
  all_goals first
    | with_reducible assumption
    | omega

theorem encSpec_post {s s' : State} (hR : Proof.AesGcm.rounds s)
    (h : (Spec.Gcm.streamEncryptContract X86_64.abi 2608).post s s') :
    Proof.AesGcm.streamEncryptX86_64.post s s' := by
  sig_post [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre, X86_64.abi,
    X86_64.argRegs, Spec.Gcm.streamEncryptPost] at h
  sig_reduce [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem encSpecP_post {s s' : State} (hR : Proof.AesGcm.rounds s)
    (h : (Spec.Gcm.streamEncryptPrecomputedContract X86_64.abi 2608).post s s') :
    Proof.AesGcm.streamEncryptX86_64.post s s' := by
  sig_post [Spec.Gcm.streamEncryptPrecomputedContract, Spec.Gcm.streamCryptPrecomputedSig,
    Spec.Gcm.streamTextPrecomputedPre, X86_64.abi, X86_64.argRegs, Spec.Gcm.streamEncryptPost] at h
  sig_reduce [Spec.Gcm.streamEncryptPrecomputedContract, Spec.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem encSpec_pub {s₁ s₂ : State} (h : encCallPub s₁ s₂) :
    (Spec.Gcm.streamEncryptContract X86_64.abi 2608).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h
  sig_pub [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

theorem encSpecP_pub {s₁ s₂ : State} (h : encCallPub s₁ s₂) :
    (Spec.Gcm.streamEncryptPrecomputedContract X86_64.abi 2608).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h
  sig_pub [Spec.Gcm.streamEncryptPrecomputedContract, Spec.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs]
  sig_reduce [Spec.Gcm.streamEncryptPrecomputedContract, Spec.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-- An implementation of `vg_aes_gcm_stream_encrypt` for a key context of
kind `M`, by `encK M`, that writes `rsp` only in its frames, uses at most
2608 bytes of stack and loads no `mxcsr`. -/
structure EncFn (M : CtxMode) where
  fn : Fn
  ok : ∀ s, (encK M).pre s → ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (encK M).post s s'
  ct : ConstantTime isa (encK M).pre (encK M).pub fn.code
  sp : SpSafe fn.code
  xd : fn.code.x86_64Depth ≤ 2608
  mx : fn.code.allInstrs (fun i => !loadsMxcsr i) = true
  spAll : fn.code.all (fun i => !X86_64.isa.writesSp i) = true

/-- `vg_aes_gcm_stream_encrypt` from its shared contract. -/
def EncFn.ofBase (f : Fn) (hv : Verified X86_64.target f.code (Spec.Gcm.streamEncryptContract X86_64.abi 2608))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2608)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : EncFn CtxMode.base where
  fn := f
  ok s h := by
    obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (encSpec_pre h)
    exact ⟨t, s', he, ha, encSpec_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp⟩
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂ := hv.2.1 s₁ s₂ t₁ t₂ s₁' s₂' (encSpec_pre h₁) (encSpec_pre h₂)
    (encSpec_pub hq) e₁ e₂
  sp := SpSafe.of_all sp
  xd := xd
  mx := mx
  spAll := sp

/-- `vg_aes_gcm_stream_encrypt_precomputed` from its shared contract. -/
def EncFn.ofPowers (f : Fn)
    (hv : Verified X86_64.target f.code (Spec.Gcm.streamEncryptPrecomputedContract X86_64.abi 2608))
    (sp : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (xd : f.code.x86_64Depth ≤ 2608)
    (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true) : EncFn CtxMode.powers where
  fn := f
  ok s h := by
    obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (encSpecP_pre h)
    exact ⟨t, s', he, ha, encSpecP_post h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp⟩
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂ := hv.2.1 s₁ s₂ t₁ t₂ s₁' s₂' (encSpecP_pre h₁) (encSpecP_pre h₂)
    (encSpecP_pub hq) e₁ e₂
  sp := SpSafe.of_all sp
  xd := xd
  mx := mx
  spAll := sp

/-- An implementation of `vg_aes_gcm_encrypt_blocks_to` for a key context of
kind `M`, by `encryptBlocksToX86_64M M`, that writes `rsp` only in its
frames, uses at most 24 bytes of stack and loads no `mxcsr`. -/
structure BlkToFn (M : CtxMode) where
  fn : Fn
  ok : ∀ s, (Proof.AesGcm.encryptBlocksToX86_64M M).pre s →
    ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.AesGcm.encryptBlocksToX86_64M M).post s s'
  ct : ConstantTime isa (Proof.AesGcm.encryptBlocksToX86_64M M).pre Proof.AesGcm.blocksToPub fn.code
  sp : SpSafe fn.code
  xd : fn.code.x86_64Depth ≤ 24
  mx : fn.code.allInstrs (fun i => !loadsMxcsr i) = true
  spAll : fn.code.all (fun i => !X86_64.isa.writesSp i) = true

end VG.Proof.AesGcm.X86_64.StreamTo
