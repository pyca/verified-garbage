module

public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Gcm.Compose
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Contract
public import VerifiedGarbage.Impl.AesGcm.X86_64.StreamTo
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Proof.Gcm.PrecomputedContract
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Sig

/-! ### `AesGcm.X86_64.StreamTo.Callee`, which this module and modules that import it used -/

section

/-!
# AES-GCM streaming encryption out of place, x86-64: the functions called

Untrusted: everything here is checked by Lean. What
`vg_aes_gcm_stream_encrypt_to` needs of the functions it calls, by their
contracts in the terms of this target: `vg_aes_gcm_encrypt_blocks_to`
(`BlkToFn`, by `encryptBlocksToX86_64M`) and `vg_aes_gcm_stream_encrypt`
(`EncFn`, by `encK`). The latter is called as an artifact, with its working
space in a frame of its own, so its proof is its shared contract's
(`Proof.AesGcm.streamEncryptRoundsContract`, or `_precomputed`'s), which `encK`'s
precondition implies (`encSpec_pre`), and whose postcondition is `encK`'s
(`encSpec_post`): `EncFn.ofBase` and `EncFn.ofPowers`.
-/

@[expose] public section

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
    s₁.gpr .rsp = s₂.gpr .rsp ∧ arg s₁ 0 = arg s₂ 0 ∧ s₁.mxcsr = s₂.mxcsr

/-- `vg_aes_gcm_stream_encrypt`, called with the layout of its shared
contract, for a key context of kind `M`. -/
def encK (M : CtxMode) : Contract isa where
  pre := encCallPre M
  post := Proof.AesGcm.streamEncryptX86_64.post
  pub := encCallPub

theorem encSpec_pre {s : State} (h : encCallPre CtxMode.base s) :
    (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁
  clear h
  sig_pre [Proof.AesGcm.streamEncryptRoundsContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre, X86_64.abi,
    X86_64.argRegs]
  sig_reduce [Proof.AesGcm.streamEncryptRoundsContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre, X86_64.abi,
    X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr,
    List.getD, List.range, List.range.loop, VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr,
    VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.base] at *
  all_goals first
    | with_reducible assumption
    | omega

theorem encSpecP_pre {s : State} (h : encCallPre CtxMode.powers s) :
    (Proof.AesGcm.streamEncryptPrecomputedRoundsContract X86_64.abi 2608).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁
  have a₂₂ := h
  clear h
  sig_pre [Proof.AesGcm.streamEncryptPrecomputedRoundsContract, Proof.Gcm.streamCryptPrecomputedSig,
    Proof.Gcm.streamTextPrecomputedPre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.streamEncryptPrecomputedRoundsContract, Proof.Gcm.streamCryptPrecomputedSig,
    Proof.Gcm.streamTextPrecomputedPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.arg, Proof.AesGcm.args,
    Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop,
    VG.X86_64.below]
  sig_and_intros
  all_goals simp only [Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, X86_64.stackArg, X86_64.stackArgAddr,
    VG.X86_64.below, Nat.mul_one, Proof.AesGcm.rounds, CtxMode.powers] at *
  all_goals first
    | with_reducible assumption
    | omega

theorem encSpec_post {s s' : State} (hR : Proof.AesGcm.rounds s)
    (h : (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608).post s s') :
    Proof.AesGcm.streamEncryptX86_64.post s s' := by
  sig_post [Proof.AesGcm.streamEncryptRoundsContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre, X86_64.abi,
    X86_64.argRegs, Proof.AesGcm.streamEncryptRoundsPost] at h
  sig_reduce [Proof.AesGcm.streamEncryptRoundsContract, Spec.Gcm.streamCryptSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem encSpecP_post {s s' : State} (hR : Proof.AesGcm.rounds s)
    (h : (Proof.AesGcm.streamEncryptPrecomputedRoundsContract X86_64.abi 2608).post s s') :
    Proof.AesGcm.streamEncryptX86_64.post s s' := by
  sig_post [Proof.AesGcm.streamEncryptPrecomputedRoundsContract, Proof.Gcm.streamCryptPrecomputedSig,
    Proof.Gcm.streamTextPrecomputedPre, X86_64.abi, X86_64.argRegs, Proof.AesGcm.streamEncryptRoundsPost] at h
  sig_reduce [Proof.AesGcm.streamEncryptPrecomputedRoundsContract, Proof.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hR

theorem encSpec_pub {s₁ s₂ : State} (h : encCallPub s₁ s₂) :
    (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, aMd⟩ := h
  sig_pub [Proof.AesGcm.streamEncryptRoundsContract, Spec.Gcm.streamCryptSig, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.AesGcm.streamEncryptRoundsContract, Spec.Gcm.streamCryptSig, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

theorem encSpecP_pub {s₁ s₂ : State} (h : encCallPub s₁ s₂) :
    (Proof.AesGcm.streamEncryptPrecomputedRoundsContract X86_64.abi 2608).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, aMd⟩ := h
  sig_pub [Proof.AesGcm.streamEncryptPrecomputedRoundsContract, Proof.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs]
  sig_reduce [Proof.AesGcm.streamEncryptPrecomputedRoundsContract, Proof.Gcm.streamCryptPrecomputedSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop, Proof.AesGcm.arg]
  simp only [Proof.AesGcm.arg, X86_64.stackArg, X86_64.stackArgAddr] at a₈
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-- A call in a frame of pushes, of code that loads no MXCSR, loads none. -/
theorem call_frame_mx {rs : List Reg} {r : Reg} {k : Nat} {n : String} {c : Prog isa}
    (h : c.allInstrs (fun i => !loadsMxcsr i) = true) :
    (Code.frame (.push rs) (.call n c) (.pop r k) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [Code.allInstrs, h, Bool.and_true]
  rfl

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
def EncFn.ofBase (f : Fn) (hv : Verified X86_64.target f.code (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608))
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
    (hv : Verified X86_64.target f.code (Proof.AesGcm.streamEncryptPrecomputedRoundsContract X86_64.abi 2608))
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

end

end

/-! ### `AesGcm.X86_64.StreamTo.Steps`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.StreamTo.Mid`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.StreamTo.Base`, which this module and modules that import it used -/

section

/-!
# AES-GCM streaming encryption out of place, x86-64: the setting

Untrusted: everything here is checked by Lean. The arguments of the entry
state `s` (`K`, `St`, `AL`, `TL`, `Src`, `L`, `Dst`, `W`), their regions, and
the facts of `streamToPreM` by name (`SP'`); the entry, which keeps the
arguments in `work` (`entry_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.StreamTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

section
variable (s : State)

abbrev K : Addr := s.gpr .rdi
abbrev St : Addr := s.gpr .rdx
abbrev AL : BitVec 64 := s.gpr .rcx
abbrev TL : BitVec 64 := s.gpr .r8
abbrev Src : Addr := s.gpr .r9
abbrev L : Nat := (stackArg s 0).toNat
abbrev Dst : Addr := stackArg s 1
abbrev W : Addr := stackArg s 3
abbrev SP : Addr := s.gpr .rsp
abbrev stR : Region := ⟨St s, 80⟩
abbrev srcR : Region := ⟨Src s, L s⟩
abbrev dR : Region := ⟨Dst s, L s⟩
abbrev wkR : Region := ⟨W s, 2192⟩
/-- The stack arguments `len`, `dst`, `dst_len` and `work`. -/
abbrev aR : Region := ⟨SP s + BitVec.ofNat 64 8, 32⟩
/-- What the code writes: the state, the output and `work`. -/
abbrev wR : List Region := [stR s, dR s, wkR s]
/-- The stack the calls use. -/
abbrev tR : Region := below (SP s) 2624

end

/-- The key context, of kind `M`. -/
abbrev kR (M : CtxMode) (s : State) : Region := ⟨K s, M.len⟩

/-- `streamToPreM M`, by name (with the output's length `dst_len` replaced
by `len`, which it equals). -/
structure SP' (M : CtxMode) (s : State) : Prop where
  rd : s.rd = [kR M s, srcR s, aR s]
  wr : s.wr = wR s
  dl : stackArg s 2 = stackArg s 0
  k_st : (kR M s).Disjoint (stR s)
  k_d : (kR M s).Disjoint (dR s)
  k_w : (kR M s).Disjoint (wkR s)
  st_r : (stR s).Disjoint (srcR s)
  st_d : (stR s).Disjoint (dR s)
  st_w : (stR s).Disjoint (wkR s)
  st_a : (stR s).Disjoint (aR s)
  r_d : (srcR s).Disjoint (dR s)
  r_w : (srcR s).Disjoint (wkR s)
  d_w : (dR s).Disjoint (wkR s)
  d_a : (dR s).Disjoint (aR s)
  w_a : (wkR s).Disjoint (aR s)
  t_st : (⟨SP s, 8⟩ : Region).Disjoint (stR s)
  t_d : (⟨SP s, 8⟩ : Region).Disjoint (dR s)
  t_w : (⟨SP s, 8⟩ : Region).Disjoint (wkR s)
  b_k : (tR s).Disjoint (kR M s)
  b_st : (tR s).Disjoint (stR s)
  b_r : (tR s).Disjoint (srcR s)
  b_d : (tR s).Disjoint (dR s)
  b_w : (tR s).Disjoint (wkR s)
  w_k : (K s).toNat + M.len ≤ 2 ^ 64
  w_st : (St s).toNat + 80 ≤ 2 ^ 64
  w_r : (Src s).toNat + L s ≤ 2 ^ 64
  w_d : (Dst s).toNat + L s ≤ 2 ^ 64
  w_w : (W s).toNat + 2192 ≤ 2 ^ 64
  w_t : 2624 ≤ (SP s).toNat
  w_sp : (SP s).toNat + 40 ≤ 2 ^ 64
  rounds : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14
  ok : M.ok s.mem (K s)

theorem SP'.ofM {M : CtxMode} {s : State} (h : Proof.AesGcm.streamToPreM M s) : SP' M s := by
  simp only [Proof.AesGcm.streamToPreM, Proof.AesGcm.args, Proof.AesGcm.arg, Proof.AesGcm.ret,
    Proof.AesGcm.stkS, Proof.AesGcm.rounds] at h
  obtain hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇
    a₂₈ a₂₉ a₃₀ a₃₁
  have a₃₂ := h
  clear h
  rw [hA] at a₁ a₁₀ a₁₄ a₁₅
  rw [a₃] at a₂ a₅ a₈ a₁₁ a₁₃ a₁₄ a₁₇ a₂₂ a₂₇
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂⟩

/-! ## The arguments kept -/

/-- The arguments kept in `work` at `W`, with `o` bytes done. -/
structure Kept (s : State) (o : Nat) (m : Mem) : Prop where
  ctx : m.readW (W s) 64 = K s
  rounds : m.readW (W s + BitVec.ofNat 64 8) 64 = s.gpr .rsi
  st : m.readW (W s + BitVec.ofNat 64 16) 64 = St s
  aad : m.readW (W s + BitVec.ofNat 64 24) 64 = AL s
  tl : m.readW (W s + BitVec.ofNat 64 32) 64 = TL s
  src : m.readW (W s + BitVec.ofNat 64 40) 64 = Src s
  len : m.readW (W s + BitVec.ofNat 64 48) 64 = stackArg s 0
  dst : m.readW (W s + BitVec.ofNat 64 56) 64 = Dst s
  done : m.readW (W s + BitVec.ofNat 64 64) 64 = BitVec.ofNat 64 o

/-- The slots of the arguments kept. -/
abbrev kR' (s : State) : Region := ⟨W s, 72⟩

/-- The slot of the number of bytes of the head, across its call. -/
abbrev hR (s : State) : Region := ⟨W s + BitVec.ofNat 64 72, 8⟩

/-- The working space of `vg_aes_gcm_encrypt_blocks_to`. -/
abbrev scR (s : State) : Region := ⟨W s + BitVec.ofNat 64 80, 2112⟩

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

theorem w_in {d k : Nat} (h : d + k ≤ 2192) : InRegions s.wr (W s + BitVec.ofNat 64 d) k :=
  in_off (rs := s.wr) (by rw [hp.wr]; exact covers_of_mem (by simp)) h (by decide)

theorem w_in' {d k : Nat} (h : d + k ≤ 2192) : InRegions (s.rd ++ s.wr) (W s + BitVec.ofNat 64 d) k :=
  in_left (w_in hp h)

/-- The stack argument `i` (of four) is readable. -/
theorem a_in {i : Nat} (hi : i < 4) : InRegions (s.rd ++ s.wr) (SP s + BitVec.ofNat 64 (8 * (i + 1))) 8 :=
  ⟨aR s, by rw [hp.rd]; simp, Offset.contains _ (by omega_using []) (by omega_using [hi]) (by have := hp.w_sp; omega_using [])⟩

omit hp in
theorem kR'_sub : (kR' s).Sub (wkR s) := Region.sub_prefix (by decide)

omit hp in
theorem scR_sub : (scR s).Sub (wkR s) := Offset.sub_base _ (by decide)

omit hp in
theorem kR'_scR : (kR' s).Disjoint (scR s) := Offset.base_disjoint _ (by decide) (by decide)

omit hp in
theorem hR_sub : (hR s).Sub (wkR s) := Offset.sub_base _ (by decide)

omit hp in
theorem kR'_hR : (kR' s).Disjoint (hR s) := Offset.base_disjoint _ (by decide) (by decide)

/-- What a frame of the regions written and the stack below keeps: the
stack arguments. -/
theorem keep_a {m m' : Mem} (hf : Frame (wR s ++ [tR s]) m m') {i : Nat} (hi : i < 4) :
    m'.readW (SP s + BitVec.ofNat 64 (8 * (i + 1))) 64 = m.readW (SP s + BitVec.ofNat 64 (8 * (i + 1))) 64 :=
  hf.readW (r := ⟨SP s + BitVec.ofNat 64 (8 * (i + 1)), 8⟩) (Region.contains_self _ _) (fun r hr => by
    obtain hs : Region.Sub ⟨SP s + BitVec.ofNat 64 (8 * (i + 1)), 8⟩ (aR s) := by
      obtain e : SP s + BitVec.ofNat 64 (8 * (i + 1)) = SP s + BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * i) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_using []
      rw [e]; exact Offset.sub_base _ (by omega_using [hi])
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact hp.st_a.symm.sub_left hs
    · exact hp.d_a.symm.sub_left hs
    · exact hp.w_a.symm.sub_left hs
    · exact (Offset.disjoint_below (SP s) (n := 2624) (d := 8 * (i + 1)) (k := 8) (by omega_using [hi])).sub_left
        (fun _ h => h)) (by decide)

/-- The entry: the arguments kept, with `work` in `r11`, and none done. -/
theorem entry_ok : WP isa (.block entry) s fun s₁ => s₁.gpr .r11 = W s ∧
    (∀ r, r ≠ .r11 → r ≠ .rax → r ≠ .r10 → s₁.gpr r = s.gpr r) ∧
    Kept s 0 s₁.mem ∧ Frame [kR' s] s.mem s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 72 → InRegions s.wr (W s + BitVec.ofNat 64 d) (64 / 8) := fun d h => w_in hp (by omega_using [h])
  have a₀ : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 := a_in hp (i := 0) (by decide)
  have a₁ : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 16) 8 := a_in hp (i := 1) (by decide)
  have a₃ : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 32) 8 := a_in hp (i := 3) (by decide)
  have e₀ : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s 0 := rfl
  have e₁ : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 16) 64 = Dst s := rfl
  have e₃ : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 32) 64 = W s := rfl
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 72 → d + 8 ≤ 72 →
      Mem.Sep (W s + BitVec.ofNat 64 a) (64 / 8) (W s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega_using [ha]) (by have := hp.w_w; omega_using [hd])
  have s0 : ∀ d, 8 ≤ d → d + 8 ≤ 72 → Mem.Sep (W s) (64 / 8) (W s + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => by
    have := sep 0 d (by omega_using [h₁]) (by decide) h₂; simpa using this
  have s₀₁ := s0 8 (by decide) (by decide)
  have s₀₂ := s0 16 (by decide) (by decide)
  have s₀₃ := s0 24 (by decide) (by decide)
  have s₀₄ := s0 32 (by decide) (by decide)
  have s₀₅ := s0 40 (by decide) (by decide)
  have s₀₆ := s0 48 (by decide) (by decide)
  have s₀₇ := s0 56 (by decide) (by decide)
  have s₀₈ := s0 64 (by decide) (by decide)
  have s₁₂ := sep 8 16 (by decide) (by decide) (by decide)
  have s₁₃ := sep 8 24 (by decide) (by decide) (by decide)
  have s₁₄ := sep 8 32 (by decide) (by decide) (by decide)
  have s₁₅ := sep 8 40 (by decide) (by decide) (by decide)
  have s₁₆ := sep 8 48 (by decide) (by decide) (by decide)
  have s₁₇ := sep 8 56 (by decide) (by decide) (by decide)
  have s₁₈ := sep 8 64 (by decide) (by decide) (by decide)
  have s₂₃ := sep 16 24 (by decide) (by decide) (by decide)
  have s₂₄ := sep 16 32 (by decide) (by decide) (by decide)
  have s₂₅ := sep 16 40 (by decide) (by decide) (by decide)
  have s₂₆ := sep 16 48 (by decide) (by decide) (by decide)
  have s₂₇ := sep 16 56 (by decide) (by decide) (by decide)
  have s₂₈ := sep 16 64 (by decide) (by decide) (by decide)
  have s₃₄ := sep 24 32 (by decide) (by decide) (by decide)
  have s₃₅ := sep 24 40 (by decide) (by decide) (by decide)
  have s₃₆ := sep 24 48 (by decide) (by decide) (by decide)
  have s₃₇ := sep 24 56 (by decide) (by decide) (by decide)
  have s₃₈ := sep 24 64 (by decide) (by decide) (by decide)
  have s₄₅ := sep 32 40 (by decide) (by decide) (by decide)
  have s₄₆ := sep 32 48 (by decide) (by decide) (by decide)
  have s₄₇ := sep 32 56 (by decide) (by decide) (by decide)
  have s₄₈ := sep 32 64 (by decide) (by decide) (by decide)
  have s₅₆ := sep 40 48 (by decide) (by decide) (by decide)
  have s₅₇ := sep 40 56 (by decide) (by decide) (by decide)
  have s₅₈ := sep 40 64 (by decide) (by decide) (by decide)
  have s₆₇ := sep 48 56 (by decide) (by decide) (by decide)
  have s₆₈ := sep 48 64 (by decide) (by decide) (by decide)
  have s₇₈ := sep 56 64 (by decide) (by decide) (by decide)
  have hz : BitVec.setWidth 64 (BitVec.ofNat 32 0) = BitVec.ofNat 64 0 := by decide
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [entry, wCtx, wRounds, wState, wAad, wTlen, wSrc, wLen, wDst, wDone]
    xrun [a₀, a₁, a₃, e₀, e₁, e₃, w 0 (by decide), w 8 (by decide), w 16 (by decide), w 24 (by decide), w 32 (by decide),
      w 40 (by decide), w 48 (by decide), w 56 (by decide), w 64 (by decide)],
    ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r hr hr' hr''; simp [gpr_setReg, hr, hr', hr'']
  all_goals try simp (disch := first | decide | with_reducible assumption) only [gpr_setReg, ite_true,
    reduceCtorEq, ↓reduceIte, Mem.readW_writeW_self64, Mem.readW_writeW_sep, BitVec.add_zero, mem_setReg, hz]
  · have c : ∀ d, d + 8 ≤ 72 → (kR' s).Contains (W s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₂ => Offset.contains_base _ h₂ (by have := hp.w_w; omega_using [h₂])
    have c0 : (kR' s).Contains (W s) (64 / 8) := by simpa using c 0 (by decide)
    exact (((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW
      (List.mem_singleton_self _) _ (c 8 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 16 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 24 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 32 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 40 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 48 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 56 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 64 (by decide))

end

end VG.Proof.AesGcm.X86_64.StreamTo

end

end

/-!
# AES-GCM streaming encryption out of place, x86-64: between the calls

Untrusted: everything here is checked by Lean. With `o` bytes done, the
state and the output are those of the text so far followed by the first
`o` bytes of the plaintext (`Sem`), and the arguments are kept with the
memory changed only where the code may write (`Mid`); after the entry,
`Mid s 0` (`mid_entry`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxCiph ctxH gctr inc32 j0)

section
variable (s : State)

/-- The rounds. -/
abbrev R : Nat := (s.gpr .rsi).toNat
/-- The cipher and the hash subkey of the key context. -/
abbrev ciph : Block → Block := ctxCiph s.mem (K s) (R s)
abbrev hk : Block := ctxH s.mem (K s)
/-- The first `o` bytes of the plaintext. -/
abbrev pt (o : Nat) : List Byte := bytesAt s.mem (Src s) o

end

/-- With `o` bytes done, in memory `m`: the state represents the text so far
followed by the first `o` bytes of the plaintext, and the output holds
their encryption. -/
def Sem (s : State) (o : Nat) (m : Mem) : Prop :=
  ∀ iv a p, StreamRepr s.mem (St s) (ciph s) (hk s) iv a (gctr (ciph s) (inc32 (j0 (hk s) iv)) p) →
    AL s = BitVec.ofNat 64 a.length → (TL s).toNat = p.length →
    StreamRepr m (St s) (ciph s) (hk s) iv a (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ pt s o)) ∧
      bytesAt m (Dst s) o = (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ pt s o)).drop p.length

/-- `o` bytes done, in state `st`. -/
structure Mid (s : State) (o : Nat) (st : State) : Prop where
  o_le : o ≤ L s
  tl : (TL s).toNat + o < 2 ^ 64
  rsp : st.gpr .rsp = SP s
  saved : ∀ r ∈ calleeSaved, st.gpr r = s.gpr r
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  kept : Kept s o st.mem
  frame : Frame (wR s ++ [tR s]) s.mem st.mem
  sem : Sem s o st.mem
  mx : st.mxcsr = s.mxcsr

/-- `Mid` through code that changes no memory, `rsp` or callee-saved register. -/
theorem Mid.regs {s : State} {o : Nat} {st st' : State} (h : Mid s o st) (hm : st'.mem = st.mem)
    (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr)
    (hmx : st'.mxcsr = st.mxcsr) : Mid s o st' :=
  ⟨h.o_le, h.tl, by rw [hcs _ (by decide), h.rsp], fun r hr => by rw [hcs r hr, h.saved r hr],
    hrd.trans h.rd, hwr.trans h.wr, hm ▸ h.kept, hm ▸ h.frame, hm ▸ h.sem, hmx.trans h.mx⟩

/-- A streaming state is what it is outside a frame. -/
theorem streamRepr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 80⟩ : Region).Disjoint r) {ciph : Block → Block} {h : Block}
    {iv a c : List Byte} (hr : StreamRepr m p ciph h iv a c) : StreamRepr m' p ciph h iv a c := by
  have sub : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ rs, (⟨p + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hk r hr => (hd r hr).sub_left (Offset.sub_base _ hk)
  have e : ∀ d : Nat, p + (OfNat.ofNat d : Addr) = p + BitVec.ofNat 64 d := fun _ => rfl
  rw [Proof.Gcm.streamRepr_iff, e, e, e] at hr ⊢
  obtain ⟨hj, ha, hc⟩ := hr
  have e0 := blockAt_frame hf (sub (d := 0) (k := 16) (by decide))
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e0
  refine ⟨by rw [e0, hj], ha.congr (blockAt_frame hf (sub (by decide)))
    (bytesAt_frame hf (sub (d := 32) (k := (Spec.Gcm.ghashInput a c).length % 16) (by omega_using [])) (by omega_using [])),
    hc.congr (blockAt_frame hf (sub (by decide))) (blockAt_frame hf (sub (by decide)))⟩

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- The key context, outside a frame of the regions written and the stack. -/
theorem k_disj : ∀ r ∈ wR s ++ [tR s], (kR M s).Disjoint r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl
  exacts [hp.k_st, hp.k_d, hp.k_w, hp.b_k.symm]

/-- The plaintext, outside a frame of the regions written and the stack. -/
theorem r_disj : ∀ r ∈ wR s ++ [tR s], (srcR s).Disjoint r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl
  exacts [hp.st_r.symm, hp.r_d, hp.r_w, hp.b_r.symm]

/-- The cipher, through a frame of the regions written and the stack. -/
theorem ciph_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) : ctxCiph m (K s) (R s) = ciph s := by
  have hRb : 16 * (R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  simp only [ciph, ctxCiph]
  rw [bytesAt_frame hf (fun r hr => (k_disj hp r hr).sub_left (Region.sub_prefix (Nat.le_trans hRb M.ge)))
    (by have := hp.w_k; have := M.ge; omega_using [hRb])]

/-- The hash subkey, through a frame of the regions written and the stack. -/
theorem hk_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) : ctxH m (K s) = hk s := by
  simp only [hk, ctxH]
  exact blockAt_frame hf fun r hr => (k_disj hp r hr).sub_left (Offset.sub_base _ (by have := M.ge; omega))

omit hp in
theorem Kept.frame {o : Nat} {m m' : Mem} (h : Kept s o m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (kR' s).Disjoint r) : Kept s o m' := by
  have k : ∀ d, d + 8 ≤ 72 → m'.readW (W s + BitVec.ofNat 64 d) 64 = m.readW (W s + BitVec.ofNat 64 d) 64 :=
    fun d hd' => hf.readW (Offset.contains_base _ hd' (by omega_using [hd'])) hd (by decide)
  have k0 : m'.readW (W s) 64 = m.readW (W s) 64 := by simpa using k 0 (by decide)
  exact ⟨by rw [k0]; exact h.ctx, by rw [k 8 (by decide)]; exact h.rounds, by rw [k 16 (by decide)]; exact h.st,
    by rw [k 24 (by decide)]; exact h.aad, by rw [k 32 (by decide)]; exact h.tl,
    by rw [k 40 (by decide)]; exact h.src, by rw [k 48 (by decide)]; exact h.len,
    by rw [k 56 (by decide)]; exact h.dst, by rw [k 64 (by decide)]; exact h.done⟩

omit hp in
/-- A frame of the slots kept is one of the regions written. -/
theorem frame_kR' {m m' : Mem} (hf : Frame [kR' s] m m') : Frame (wR s ++ [tR s]) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wkR s, by simp, kR'_sub⟩

/-- After the entry: nothing done. -/
theorem mid_entry {s₁ : State} (hsp : s₁.gpr .rsp = s.gpr .rsp)
    (hcs : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r)
    (hk : Kept s 0 s₁.mem) (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr)
    (hmx : s₁.mxcsr = s.mxcsr) : Mid s 0 s₁ := by
  refine ⟨Nat.zero_le _, by have := (TL s).isLt; omega_using [], hsp, hcs, hrd, hwr, hk, frame_kR' hf,
    fun iv a p hr _ hl => ⟨?_, ?_⟩, hmx⟩
  all_goals have z : pt s 0 = [] := rfl
  · rw [z, List.append_nil]
    exact streamRepr_frame hf (fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hp.st_w.sub_right kR'_sub) hr
  · rw [z, List.append_nil, List.drop_eq_nil_of_le (by rw [Proof.Gcm.length_gctr])]
    rfl

end

/-- `Sem` through a frame of the slots kept. -/
theorem Sem.kR' {M : CtxMode} {s : State} (hp : SP' M s) {o : Nat} {m m' : Mem} (h : Sem s o m)
    (hf : Frame [kR' s] m m') (ho : o ≤ L s) : Sem s o m' := fun iv a p hr hal hpl => by
  obtain ⟨sr, dd⟩ := h iv a p hr hal hpl
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  refine ⟨streamRepr_frame hf (fun r hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hp.st_w.sub_right kR'_sub) sr, ?_⟩
  rw [← dd]
  exact bytesAt_frame hf (fun r hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.d_w.sub_left (Region.sub_prefix ho)).sub_right kR'_sub) (by omega_using [ho, hL])

end VG.Proof.AesGcm.X86_64.StreamTo

end

end

/-!
# AES-GCM streaming encryption out of place, x86-64: the blocks between the calls

Untrusted: everything here is checked by Lean. What each block of
instructions of `blocks` and `rest` does (`hd1_ok` … `restArgs_ok`), from
the arguments kept in `work`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.StreamTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- `stackArg` of the state a call enters, from the caller's stack. -/
theorem stackArg_entry {t : State} {F : Addr} (hsp : t.gpr .rsp = F) (hF : 8 ≤ F.toNat) (rd wr : List Region)
    {i : Nat} (hi : F.toNat + 8 * i + 8 ≤ 2 ^ 64) :
    stackArg (t.callEntry.withRegions rd wr) i = t.mem.readW (F + BitVec.ofNat 64 (8 * i)) 64 := by
  have hb : F - 8 + BitVec.ofNat 64 (8 * (i + 1)) = F + BitVec.ofNat 64 (8 * i) := by
    rw [show 8 * (i + 1) = 8 + 8 * i by omega_using [], BitVec.ofNat_add, ← BitVec.add_assoc,
      show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.sub_add_cancel]
  have hsep := Offset.sep (F - 8) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega_using []) (by omega_using [hF, hi]) (by omega_using [])
  rw [show F - 8 + BitVec.ofNat 64 0 = F - 8 from BitVec.add_zero _, hb] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, hb]
  exact Mem.readW_writeW_sep hsep (by decide)

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `test r8, r8`, through `rax`: whether there is no text so far. -/
theorem hd1_ok {st : State} :
    WP isa (.block [.mov .rax (.reg .r8), .alu .test .rax (.reg .rax)]) st fun st' =>
      st'.gpr .rax = st.gpr .r8 ∧ st'.zf = some (st.gpr .r8 == 0) ∧
      (∀ r, r ≠ .rax → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp only [zf_arithFlags, gpr_setReg, ite_true, BitVec.and_self]
  · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- `mov rax, rcx`: `aad_len`, after no text. -/
theorem mvc_ok {st : State} :
    WP isa (.block [.mov .rax (.reg .rcx)]) st fun st' =>
      st'.gpr .rax = st.gpr .rcx ∧ (∀ r, r ≠ .rax → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧
        st'.rd = st.rd ∧ st'.wr = st.wr := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r hr; simp [gpr_setReg, hr]
  all_goals simp [mem_setReg, rd_setReg, wr_setReg]

/-- `and rax, 15`: whether the text so far ends a block. -/
theorem hd2_ok {st : State} {T : BitVec 64} (hax : st.gpr .rax = T) :
    WP isa (.block [.alu .and .rax (imm 15)]) st fun st' =>
      st'.zf = some (BitVec.ofNat 64 (T.toNat % 16) == 0) ∧
      (∀ r, r ≠ .rax → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have e15 := and15 T
  rw [imm_eq (by decide)] at e15
  apply WP.of_runBlock
  refine ⟨_, by simp only [imm]; xrun [hax], ?_, ?_, ?_, ?_, ?_⟩
  · simp [zf_arithFlags, gpr_setReg, e15]
  · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- `work`'s slot `d`, readable. -/
theorem slot_in {st : State} (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) {d : Nat} (hd : d + 8 ≤ 80) :
    InRegions (st.rd ++ st.wr) (W s + BitVec.ofNat 64 d) 8 := by
  rw [hrd, hwr]; exact w_in' hp (by omega_using [hd])

/-- `work` from the stack, through a frame of the regions written and the
stack. -/
theorem w_stack' {st : State} (hsp : st.gpr .rsp = SP s) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr)
    (hf : Frame (wR s ++ [tR s]) s.mem st.mem) :
    InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 32) 8 ∧
      st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 32) 64 = W s := by
  refine ⟨by rw [hrd, hwr, hsp]; exact a_in hp (i := 3) (by decide), ?_⟩
  rw [hsp, show (32 : Nat) = 8 * (3 + 1) from rfl, keep_a hp hf (by decide)]; rfl

/-- `work` from the stack. -/
theorem w_stack {o : Nat} {st : State} (h : Mid s o st) :
    InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 32) 8 ∧
      st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 32) 64 = W s :=
  w_stack' hp h.rsp h.rd h.wr h.frame

/-- `work`, `aad_len`, and the text so far and the `o` bytes done. -/
theorem blocksLoad_ok {o : Nat} {st : State} (h : Mid s o st) :
    WP isa (.block blocksLoad) st fun st' =>
      st'.gpr .r11 = W s ∧ st'.gpr .rcx = AL s ∧ st'.gpr .r8 = TL s + BitVec.ofNat 64 o ∧
      (∀ r, r ≠ .r11 → r ≠ .rcx → r ≠ .r8 → r ≠ .rax → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧
      st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain ⟨a₃, hW⟩ := w_stack hp h
  have r₃ := slot_in hp h.rd h.wr (d := 24) (by decide)
  have r₄ := slot_in hp h.rd h.wr (d := 32) (by decide)
  have r₈ := slot_in hp h.rd h.wr (d := 64) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [blocksLoad, wAad, wTlen, wDone]
    xrun [a₃, hW, r₃, r₄, r₈, h.kept.aad, h.kept.tl, h.kept.done], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [gpr_setReg, gpr_arithFlags]; done)
  · intro r a b c d; simp [gpr_setReg, gpr_arithFlags, a, b, c, d]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The number of whole blocks of the plaintext left after the `o` bytes
done, and whether there is none. -/
theorem blocksCount_ok {st : State} {o : Nat} (h11 : st.gpr .r11 = W s) (hk : Kept s o st.mem) (ho : o ≤ L s)
    (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) :
    WP isa (.block blocksCount) st
      fun st' => st'.gpr .rax = BitVec.ofNat 64 ((L s - o) / 16) ∧ st'.zf = some (decide ((L s - o) / 16 = 0)) ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
        st'.wr = st.wr := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have q₁ := slot_in hp hrd hwr (d := 48) (by decide)
  have q₂ := slot_in hp hrd hwr (d := 64) (by decide)
  have hlen : st.mem.readW (W s + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 (L s) := by
    rw [hk.len, ofNat_toNat]
  have hsub := ofNat_sub ho hL
  have h4 := shr4 (L s - o) (by omega_using [hL])
  have hz := and_self_beq (show (L s - o) / 16 < 2 ^ 64 by omega_using [hL])
  apply WP.of_runBlock
  refine ⟨_, by simp only [blocksCount, wLen, wDone]; xrun [h11, q₁, q₂, hlen, hk.done, hsub, h4], ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, h4]
  · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, ite_true, h4, hz]
  · intro r hr hr'; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr, hr']
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags]

end

/-- `16 q`, by doubling four times. -/
theorem dbl (x : Nat) : BitVec.ofNat 64 x + BitVec.ofNat 64 x = BitVec.ofNat 64 (2 * x) := by
  rw [← BitVec.ofNat_add]; congr 1; omega_using []

/-- The number of whole blocks into `r9`, their bytes into `rax`, and
whether the text so far and they would exceed 2⁶⁴ bytes. -/
theorem len_ok {st : State} {q : Nat} {T : BitVec 64} (hax : st.gpr .rax = BitVec.ofNat 64 q) (h8 : st.gpr .r8 = T) :
    WP isa (.block blocksLen) st fun st' =>
      st'.gpr .r9 = BitVec.ofNat 64 q ∧ st'.gpr .rax = BitVec.ofNat 64 (16 * q) ∧
      st'.cf = some (decide (2 ^ 64 ≤ T.toNat + (BitVec.ofNat 64 (16 * q)).toNat)) ∧
      (∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .rcx → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
      st'.wr = st.wr := by
  have d₁ := dbl q
  have d₂ := dbl (2 * q)
  have d₃ := dbl (2 * (2 * q))
  have d₄ := dbl (2 * (2 * (2 * q)))
  have e16 : 2 * (2 * (2 * (2 * q))) = 16 * q := by omega_using []
  rw [e16] at d₄
  apply WP.of_runBlock
  refine ⟨_, by simp only [blocksLen]; xrun [hax, h8, d₁, d₂, d₃, d₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags, d₄]
  · simp only [cf_arithFlags, cf_setReg]
  · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- The bytes done, `o + 16 q`, kept, and the arguments of
`vg_aes_gcm_encrypt_blocks_to`, past the `o` bytes done before. -/
theorem blocksArgs_ok {st : State} {o q : Nat} (h11 : st.gpr .r11 = W s)
    (hax : st.gpr .rax = BitVec.ofNat 64 (16 * q)) (hk : Kept s o st.mem) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) :
    WP isa (.block blocksArgs) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rdx = St s + BitVec.ofNat 64 48 ∧
      st'.gpr .rcx = St s + BitVec.ofNat 64 16 ∧ st'.gpr .r8 = Src s + BitVec.ofNat 64 o ∧
      st'.gpr .r10 = Dst s + BitVec.ofNat 64 o ∧ st'.gpr .rax = W s + BitVec.ofNat 64 80 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r10 → r ≠ .rax → st'.gpr r = st.gpr r) ∧
      Kept s (o + 16 * q) st'.mem ∧ Frame [kR' s] st.mem st'.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have w64 : InRegions st.wr (W s + BitVec.ofNat 64 64) (64 / 8) := by rw [hwr]; exact w_in hp (by decide)
  have r₀ := slot_in hp hrd hwr (d := 0) (by decide)
  have r₁ := slot_in hp hrd hwr (d := 8) (by decide)
  have r₂ := slot_in hp hrd hwr (d := 16) (by decide)
  have r₅ := slot_in hp hrd hwr (d := 40) (by decide)
  have r₇ := slot_in hp hrd hwr (d := 56) (by decide)
  have r₈ := slot_in hp hrd hwr (d := 64) (by decide)
  have sep : ∀ d : Nat, d + 8 ≤ 64 →
      Mem.Sep (W s + BitVec.ofNat 64 d) (64 / 8) (W s + BitVec.ofNat 64 64) (64 / 8) :=
    fun d hd => Offset.sep _ (.inl hd) (by omega_using [hd]) (by have := hp.w_w; omega_using [])
  have s₀ := sep 0 (by decide)
  have s₁ := sep 8 (by decide)
  have s₂ := sep 16 (by decide)
  have s₅ := sep 40 (by decide)
  have s₇ := sep 56 (by decide)
  have k0 : st.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s := by simpa using hk.ctx
  have hdn := hk.done
  have hsum : BitVec.ofNat 64 (16 * q) + BitVec.ofNat 64 o = BitVec.ofNat 64 (o + 16 * q) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [blocksArgs, wDone, wCtx, wRounds, wState, wSrc, wDst, wScr, imm]
    xrun [h11, hax, w64, r₀, r₁, r₂, r₅, r₇, r₈, s₀, s₁, s₂, s₅, s₇, k0, hk.rounds, hk.st, hk.src, hk.dst, hdn,
      hsum],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rfl, by rfl⟩
  iterate 7
    simp (disch := first | decide | with_reducible assumption) only [gpr_setReg, gpr_arithFlags,
      ite_true, reduceCtorEq, ↓reduceIte, Mem.readW_writeW_sep, k0, hk.rounds, hk.st, hk.src, hk.dst, hdn, h11]
  · intro r a b c d e f g; simp [gpr_setReg, gpr_arithFlags, a, b, c, d, e, f, g]
  · have k : ∀ d, d + 8 ≤ 64 → (st.mem.writeW (W s + BitVec.ofNat 64 64) (BitVec.ofNat 64 (o + 16 * q))).readW
        (W s + BitVec.ofNat 64 d) 64 = st.mem.readW (W s + BitVec.ofNat 64 d) 64 :=
      fun d hd => Mem.readW_writeW_sep (sep d hd) (by decide)
    have k0' : (st.mem.writeW (W s + BitVec.ofNat 64 64) (BitVec.ofNat 64 (o + 16 * q))).readW (W s) 64 =
        st.mem.readW (W s) 64 := by simpa using k 0 (by decide)
    simp only [mem_setReg, mem_arithFlags]
    exact ⟨by rw [k0']; exact hk.ctx, by rw [k 8 (by decide)]; exact hk.rounds, by rw [k 16 (by decide)]; exact hk.st,
      by rw [k 24 (by decide)]; exact hk.aad, by rw [k 32 (by decide)]; exact hk.tl,
      by rw [k 40 (by decide)]; exact hk.src, by rw [k 48 (by decide)]; exact hk.len,
      by rw [k 56 (by decide)]; exact hk.dst, Mem.readW_writeW_self64 _ _ _⟩
  · simp only [mem_setReg, mem_arithFlags]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (show 64 + 64 / 8 ≤ 72 by decide) (by have := hp.w_w; omega_using []))

end

/-! ## The head -/

/-- The bytes of the head: those that end the block the text so far ends
inside, or all the plaintext if fewer. -/
abbrev Hd (s : State) : Nat := min ((16 - (TL s).toNat % 16) % 16) (L s)

/-- `-T mod 16`, as `and` computes it. -/
theorem neg_and15 (T : BitVec 64) : -T &&& 15#64 = BitVec.ofNat 64 ((16 - T.toNat % 16) % 16) := by
  have e := and15 (-T)
  rw [imm_eq (by decide)] at e
  rw [e]
  congr 1
  rw [BitVec.toNat_neg]
  have := T.isLt
  omega_using []

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- The bytes of the head into `rax`, and whether there are none. -/
theorem headLen_ok {st : State} {o : Nat} (h11 : st.gpr .r11 = W s) (h8 : st.gpr .r8 = TL s)
    (hk : Kept s o st.mem) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) :
    WP isa (.block headLen) st fun st' =>
      st'.gpr .rax = BitVec.ofNat 64 (Hd s) ∧ st'.zf = some (decide (Hd s = 0)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
      st'.wr = st.wr := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have q₁ := slot_in hp hrd hwr (d := 48) (by decide)
  have hlen : st.mem.readW (W s + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 (L s) := by
    rw [hk.len, ofNat_toNat]
  have hn := neg_and15 (TL s)
  have hn₀ : BitVec.setWidth 64 (BitVec.ofNat 32 0) - TL s &&& 15#64 =
      BitVec.ofNat 64 ((16 - (TL s).toNat % 16) % 16) := by
    rw [← hn, show BitVec.setWidth 64 (BitVec.ofNat 32 0) = 0#64 from rfl, BitVec.zero_sub]
  have hpad : (BitVec.ofNat 64 ((16 - (TL s).toNat % 16) % 16)).toNat = (16 - (TL s).toNat % 16) % 16 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [])
  have hLn : (BitVec.ofNat 64 (L s)).toNat = L s := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hL
  have hz := and_self_beq (show Hd s < 2 ^ 64 from Nat.lt_of_le_of_lt (Nat.min_le_right _ _) hL)
  apply WP.of_runBlock
  by_cases hc : L s < (16 - (TL s).toNat % 16) % 16
  · have e : Hd s = L s := by simp only [Hd]; omega_using [hc]
    refine ⟨_, by
      simp only [headLen, wLen]
      xrun [h11, h8, q₁, hlen, hn₀, hn, execCmov, eval, hpad, hLn, hc, decide_true, e], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, e]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, e] at hz ⊢; rw [hz]
    · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  · have e : Hd s = (16 - (TL s).toNat % 16) % 16 := by simp only [Hd]; omega_using [hc]
    refine ⟨_, by
      simp only [headLen, wLen]
      xrun [h11, h8, q₁, hlen, hn₀, hn, execCmov, eval, hpad, hLn, hc, decide_false, e], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, e]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, e] at hz ⊢; rw [hz]
    · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

end

/-- Whether the text so far and the `k` bytes of the head would exceed 2⁶⁴
bytes. -/
theorem headOver_ok {st : State} {k : Nat} {T : BitVec 64} (hax : st.gpr .rax = BitVec.ofNat 64 k)
    (h8 : st.gpr .r8 = T) (hk : k < 2 ^ 64) :
    WP isa (.block headOver) st fun st' =>
      st'.cf = some (decide (2 ^ 64 ≤ T.toNat + k)) ∧ (∀ r, r ≠ .rcx → st'.gpr r = st.gpr r) ∧
      st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have hkn : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hk
  apply WP.of_runBlock
  refine ⟨_, by simp only [headOver]; xrun [hax, h8], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cf_arithFlags, cf_setReg, hkn]
  · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- The `k` bytes of the head kept in their slot, and the pointers and the
length of their copy. -/
theorem headPtrs_ok {st : State} {o k : Nat} (h11 : st.gpr .r11 = W s) (hax : st.gpr .rax = BitVec.ofNat 64 k)
    (hk : Kept s o st.mem) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) :
    WP isa (.block headPtrs) st fun st' =>
      st'.gpr .rcx = BitVec.ofNat 64 k ∧ st'.gpr .rsi = Src s ∧ st'.gpr .rdi = Dst s ∧
      st'.mem.readW (W s + BitVec.ofNat 64 72) 64 = BitVec.ofNat 64 k ∧
      (∀ r, r ≠ .rcx → r ≠ .rsi → r ≠ .rdi → st'.gpr r = st.gpr r) ∧ Frame [hR s] st.mem st'.mem ∧
      st'.rd = st.rd ∧ st'.wr = st.wr := by
  have w72 : InRegions st.wr (W s + BitVec.ofNat 64 72) (64 / 8) := by rw [hwr]; exact w_in hp (by decide)
  have r₅ := slot_in hp hrd hwr (d := 40) (by decide)
  have r₇ := slot_in hp hrd hwr (d := 56) (by decide)
  have sep : ∀ d : Nat, d + 8 ≤ 72 →
      Mem.Sep (W s + BitVec.ofNat 64 d) (64 / 8) (W s + BitVec.ofNat 64 72) (64 / 8) :=
    fun d hd => Offset.sep _ (.inl hd) (by omega_using [hd]) (by have := hp.w_w; omega_using [])
  have s₅ := sep 40 (by decide)
  have s₇ := sep 56 (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [headPtrs, wHead, wSrc, wDst]
    xrun [h11, hax, w72, r₅, r₇, s₅, s₇, hk.src, hk.dst], ?_, ?_, ?_, ?_, ?_, ?_, by rfl, by rfl⟩
  all_goals try (simp (disch := first | decide | with_reducible assumption) only [gpr_setReg, ite_true,
    reduceCtorEq, ↓reduceIte, Mem.readW_writeW_sep, hk.src, hk.dst, hax]; done)
  · simp only [mem_setReg]; exact Mem.readW_writeW_self64 _ _ _
  · intro r a b c; simp [gpr_setReg, a, b, c]
  · simp only [mem_setReg]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-- The arguments of `vg_aes_gcm_stream_encrypt` on the `k` bytes of the
head, their number from its slot. -/
theorem headArgs_ok {o k : Nat} {st : State} (h : Mid s o st)
    (h72 : st.mem.readW (W s + BitVec.ofNat 64 72) 64 = BitVec.ofNat 64 k) :
    WP isa (.block headArgs) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rdx = St s ∧ st'.gpr .rcx = AL s ∧
      st'.gpr .r8 = TL s + BitVec.ofNat 64 0 ∧ st'.gpr .r9 = Dst s + BitVec.ofNat 64 0 ∧
      st'.gpr .r10 = BitVec.ofNat 64 k ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain ⟨a₃, hW⟩ := w_stack hp h
  have r₀ := slot_in hp h.rd h.wr (d := 0) (by decide)
  have r₁ := slot_in hp h.rd h.wr (d := 8) (by decide)
  have r₂ := slot_in hp h.rd h.wr (d := 16) (by decide)
  have r₃ := slot_in hp h.rd h.wr (d := 24) (by decide)
  have r₄ := slot_in hp h.rd h.wr (d := 32) (by decide)
  have r₇ := slot_in hp h.rd h.wr (d := 56) (by decide)
  have r₉ := slot_in hp h.rd h.wr (d := 72) (by decide)
  have k0 : st.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s := by simpa using h.kept.ctx
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [headArgs, wCtx, wRounds, wState, wAad, wTlen, wDst, wHead]
    xrun [a₃, hW, r₀, r₁, r₂, r₃, r₄, r₇, r₉, k0, h.kept.rounds, h.kept.st, h.kept.aad, h.kept.tl, h.kept.dst, h72],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [gpr_setReg]; done)
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  all_goals simp [mem_setReg, rd_setReg, wr_setReg]

/-- The `k` bytes of the head, from their slot, done. -/
theorem headDone_ok {o k : Nat} {st : State} (hsp : st.gpr .rsp = SP s) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr)
    (hf : Frame (wR s ++ [tR s]) s.mem st.mem) (hk : Kept s o st.mem)
    (h72 : st.mem.readW (W s + BitVec.ofNat 64 72) 64 = BitVec.ofNat 64 k) :
    WP isa (.block headDone) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ Kept s k st'.mem ∧ Frame [kR' s] st.mem st'.mem ∧
      st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain ⟨a₃, hW⟩ := w_stack' hp hsp hrd hwr hf
  have r₉ := slot_in hp hrd hwr (d := 72) (by decide)
  have w64 : InRegions st.wr (W s + BitVec.ofNat 64 64) (64 / 8) := by rw [hwr]; exact w_in hp (by decide)
  have sep : ∀ d : Nat, d + 8 ≤ 64 →
      Mem.Sep (W s + BitVec.ofNat 64 d) (64 / 8) (W s + BitVec.ofNat 64 64) (64 / 8) :=
    fun d hd => Offset.sep _ (.inl hd) (by omega_using [hd]) (by have := hp.w_w; omega_using [])
  apply WP.of_runBlock
  refine ⟨_, by simp only [headDone, wHead, wDone]; xrun [a₃, hW, r₉, h72, w64], ?_, ?_, ?_, by rfl, by rfl⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  · have e : ∀ d, d + 8 ≤ 64 → (st.mem.writeW (W s + BitVec.ofNat 64 64) (BitVec.ofNat 64 k)).readW
        (W s + BitVec.ofNat 64 d) 64 = st.mem.readW (W s + BitVec.ofNat 64 d) 64 :=
      fun d hd => Mem.readW_writeW_sep (sep d hd) (by decide)
    have e0 : (st.mem.writeW (W s + BitVec.ofNat 64 64) (BitVec.ofNat 64 k)).readW (W s) 64 =
        st.mem.readW (W s) 64 := by simpa using e 0 (by decide)
    simp only [mem_setReg]
    exact ⟨by rw [e0]; exact hk.ctx, by rw [e 8 (by decide)]; exact hk.rounds, by rw [e 16 (by decide)]; exact hk.st,
      by rw [e 24 (by decide)]; exact hk.aad, by rw [e 32 (by decide)]; exact hk.tl,
      by rw [e 40 (by decide)]; exact hk.src, by rw [e 48 (by decide)]; exact hk.len,
      by rw [e 56 (by decide)]; exact hk.dst, Mem.readW_writeW_self64 _ _ _⟩
  · simp only [mem_setReg]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (show 64 + 64 / 8 ≤ 72 by decide) (by have := hp.w_w; omega_using []))

end

end VG.Proof.AesGcm.X86_64.StreamTo

end

end

/-!
# AES-GCM streaming encryption out of place, x86-64: the call of the whole blocks

Untrusted: everything here is checked by Lean. The call of
`vg_aes_gcm_encrypt_blocks_to` on `q ≥ 1` whole blocks, with `dst`, `q` and
the working space pushed for it (`blkCall_ok`): what it needs, from the
layout of `s` (`blkPre`), and what it leaves.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

theorem sub_add_ofNat (p : Addr) {b d : Nat} (h : d ≤ b) :
    p - BitVec.ofNat 64 b + BitVec.ofNat 64 d = p - BitVec.ofNat 64 (b - d) := by
  rw [Offset.sub_ofNat_eq p (show b - d ≤ b by omega_arith), Nat.sub_sub_self h]

/-- A prefix of a region covered is covered. -/
theorem covers_prefix {b : Addr} {k L : Nat} {ts : List Region} (h : (⟨b, L⟩ : Region) ∈ ts) (hk : k ≤ L) :
    Covers [⟨b, k⟩] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx
  exact ⟨_, h, by simp only [Region.Contains] at hc ⊢; omega_arith⟩

/-- A part of a region covered is covered. -/
theorem covers_off {p : Addr} {k d m : Nat} {ts : List Region} (h : (⟨p, k⟩ : Region) ∈ ts) (hd : d + m ≤ k)
    (hd' : d < 2 ^ 64) : Covers [⟨p + BitVec.ofNat 64 d, m⟩] ts := by
  intro a j ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨_, h, ?_⟩
  simp only [Region.Contains] at hc ⊢
  obtain e : a - p = (a - (p + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d := by
    rw [Offset.sub_add_eq]; exact (BitVec.sub_add_cancel _ _).symm
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) hd']
  have := Nat.mod_le ((a - (p + BitVec.ofNat 64 d)).toNat + d) (2 ^ 64)
  omega_arith

/-- A part of a buffer that does not wrap around does not either. -/
theorem off_bound {p : Addr} {o n L : Nat} (hw : p.toNat + L ≤ 2 ^ 64) (h : o + n ≤ L) :
    (p + BitVec.ofNat 64 o).toNat + n ≤ 2 ^ 64 := by
  by_cases hn : n = 0
  · subst hn; have := (p + BitVec.ofNat 64 o).isLt; omega_arith
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

theorem covers_cons' {r : Region} {rs ts : List Region} (h₁ : Covers [r] ts) (h₂ : Covers rs ts) :
    Covers (r :: rs) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁ a n ⟨x, List.mem_singleton_self _, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

theorem covers_nil' {ts : List Region} : Covers [] ts := by
  intro a n ⟨x, hx, _⟩; cases hx

section
variable (s : State)

/-- The counter block and `Y` of the state. -/
abbrev ctrR : Region := ⟨St s + BitVec.ofNat 64 48, 16⟩
abbrev yR : Region := ⟨St s + BitVec.ofNat 64 16, 16⟩

/-- What the call reads and writes, on `q` whole blocks after the `o`
bytes done. -/
abbrev blkRd (M : CtxMode) (o q : Nat) : List Region :=
  [kR M s, ⟨Src s + BitVec.ofNat 64 o, q * 16⟩, ⟨SP s - BitVec.ofNat 64 24, 24⟩]
abbrev blkWr (o q : Nat) : List Region := [ctrR s, yR s, ⟨Dst s + BitVec.ofNat 64 o, q * 16⟩, scR s]

end

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

omit hp in
theorem ctr_sub : (ctrR s).Sub (stR s) := Offset.sub_base _ (by decide)
omit hp in
theorem y_sub : (yR s).Sub (stR s) := Offset.sub_base _ (by decide)

omit hp in
theorem pre_sub {o q : Nat} (hq : o + 16 * q ≤ L s) : Region.Sub ⟨Src s + BitVec.ofNat 64 o, q * 16⟩ (srcR s) :=
  Offset.sub_base _ (by omega_arith)
omit hp in
theorem dst_sub {o q : Nat} (hq : o + 16 * q ≤ L s) : Region.Sub ⟨Dst s + BitVec.ofNat 64 o, q * 16⟩ (dR s) :=
  Offset.sub_base _ (by omega_arith)

omit hp in
/-- A region of the stack below `SP - a`, in the stack the code uses. -/
theorem stk_sub {a n : Nat} (ha : a ≤ 2624) (hn : n ≤ a) :
    Region.Sub ⟨SP s - BitVec.ofNat 64 a, n⟩ (tR s) := Offset.sub_below _ (by omega_arith) (by omega_arith)

/-- What the call of `vg_aes_gcm_encrypt_blocks_to` needs. -/
theorem blkPre {o q : Nat} (hq : o + 16 * q ≤ L s) {u : State}
    (hrsp : u.gpr .rsp = SP s - BitVec.ofNat 64 32) (hrd : u.rd = blkRd s M o q) (hwr : u.wr = blkWr s o q)
    (h_di : u.gpr .rdi = K s) (h_si : u.gpr .rsi = s.gpr .rsi) (h_dx : u.gpr .rdx = St s + BitVec.ofNat 64 48)
    (h_cx : u.gpr .rcx = St s + BitVec.ofNat 64 16) (h_8 : u.gpr .r8 = Src s + BitVec.ofNat 64 o) (h_9 : u.gpr .r9 = BitVec.ofNat 64 q)
    (a0 : stackArg u 0 = Dst s + BitVec.ofNat 64 o) (a1 : stackArg u 1 = BitVec.ofNat 64 q) (a2 : stackArg u 2 = W s + BitVec.ofNat 64 80)
    (hok : M.ok u.mem (K s)) :
    (Proof.AesGcm.encryptBlocksToX86_64M M).pre u := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  obtain hqn : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  have wt := hp.w_t
  have wsp := hp.w_sp
  obtain pr := pre_sub (s := s) hq
  obtain ds := dst_sub (s := s) hq
  have wst := hp.w_st
  obtain hargs : (Proof.AesGcm.args u 3) = ⟨SP s - BitVec.ofNat 64 24, 24⟩ := by
    simp only [Proof.AesGcm.args, stackArgAddr, hrsp]
    rw [sub_add_ofNat _ (by decide)]
  obtain hret : (Proof.AesGcm.ret u) = ⟨SP s - BitVec.ofNat 64 32, 8⟩ := by simp only [Proof.AesGcm.ret, hrsp]
  obtain hstk : (Proof.AesGcm.stk24 u) = ⟨SP s - BitVec.ofNat 64 56, 24⟩ := by
    simp only [Proof.AesGcm.stk24, below, hrsp]
    rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
  obtain tA : Region.Sub ⟨SP s - BitVec.ofNat 64 24, 24⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  obtain tR' : Region.Sub ⟨SP s - BitVec.ofNat 64 32, 8⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  obtain tS : Region.Sub ⟨SP s - BitVec.ofNat 64 56, 24⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  obtain ws : (W s + BitVec.ofNat 64 80).toNat = (W s).toNat + 80 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 80) (by decide)]
    have := hp.w_w; omega_arith
  obtain st48 : (St s + BitVec.ofNat 64 48).toNat = (St s).toNat + 48 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 48) (by decide)]; omega_arith
  obtain st16 : (St s + BitVec.ofNat 64 16).toNat = (St s).toNat + 16 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide)]; omega_arith
  obtain hsp32 : (SP s - BitVec.ofNat 64 32).toNat = (SP s).toNat - 32 := toNat_sub_ofNat (by omega_arith)
  simp only [Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPreM, Proof.AesGcm.arg, hargs, hret,
    hstk, hrd, hwr, h_di, h_si, h_dx, h_cx, h_8, h_9, a0, a1, a2, hqn, hrsp, Proof.AesGcm.rounds]
  refine ⟨trivial, trivial, trivial, hp.k_st.sub_right ctr_sub, hp.k_st.sub_right y_sub, hp.k_d.sub_right ds,
    hp.k_w.sub_right scR_sub,
    Offset.disjoint _ (.inr (by decide)) (by omega_arith) (by omega_arith), (hp.st_r.sub_left ctr_sub).sub_right pr,
    (hp.st_d.sub_left ctr_sub).sub_right ds, (hp.st_w.sub_left ctr_sub).sub_right scR_sub,
    (hp.b_st.symm.sub_left ctr_sub).sub_right tA,
    (hp.st_r.sub_left y_sub).sub_right pr, (hp.st_d.sub_left y_sub).sub_right ds,
    (hp.st_w.sub_left y_sub).sub_right scR_sub, (hp.b_st.symm.sub_left y_sub).sub_right tA,
    (hp.r_d.sub_left pr).sub_right ds, (hp.r_w.sub_left pr).sub_right scR_sub,
    (hp.d_w.sub_left ds).sub_right scR_sub, (hp.b_d.symm.sub_left ds).sub_right tA,
    (hp.b_w.symm.sub_left scR_sub).sub_right tA,
    (hp.b_st.sub_left tR').sub_right ctr_sub, (hp.b_st.sub_left tR').sub_right y_sub,
    (hp.b_d.sub_left tR').sub_right ds, (hp.b_w.sub_left tR').sub_right scR_sub,
    hp.b_k.sub_left tS, (hp.b_st.sub_left tS).sub_right ctr_sub, (hp.b_st.sub_left tS).sub_right y_sub,
    (hp.b_r.sub_left tS).sub_right pr, (hp.b_d.sub_left tS).sub_right ds, (hp.b_w.sub_left tS).sub_right scR_sub,
    hp.w_k, by rw [st48]; omega_arith, by rw [st16]; omega_arith, off_bound hp.w_r (by omega_arith), off_bound hp.w_d (by omega_arith),
    by rw [ws]; have := hp.w_w; omega_arith, by rw [hsp32]; omega_arith, by rw [hsp32]; omega_arith, hp.rounds, hok⟩

end

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

omit hp in
/-- A frame of a region of the stack below `SP - a` is one of the stack the
code uses. -/
theorem frame_stk {m m' : Mem} {a n : Nat} (ha : a ≤ 2624) (hn : n ≤ a)
    (hf : Frame [⟨SP s - BitVec.ofNat 64 a, n⟩] m m') : Frame (wR s ++ [tR s]) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨tR s, by simp, stk_sub (s := s) ha hn⟩

/-- What the call of `vg_aes_gcm_encrypt_blocks_to` needs, after the push. -/
theorem blkEntry {o q : Nat} (hq : o + 16 * q ≤ L s) {st : State}
    (hsp : st.gpr .rsp = SP s) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hf : Frame (wR s ++ [tR s]) s.mem st.mem)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = St s + BitVec.ofNat 64 48)
    (h_cx : st.gpr .rcx = St s + BitVec.ofNat 64 16) (h_8 : st.gpr .r8 = Src s + BitVec.ofNat 64 o) (h_9 : st.gpr .r9 = BitVec.ofNat 64 q)
    (h_10 : st.gpr .r10 = Dst s + BitVec.ofNat 64 o) (h_ax : st.gpr .rax = W s + BitVec.ofNat 64 80) :
    (Proof.AesGcm.encryptBlocksToX86_64M M).pre ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)) ∧
      Covers (blkRd s M o q ++ blkWr s o q) ((pushed [.rax, .r9, .r10] st).rd ++ (pushed [.rax, .r9, .r10] st).wr) ∧
      Covers (blkWr s o q) (pushed [.rax, .r9, .r10] st).wr ∧
      stackArg ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)) 0 =
        Dst s + BitVec.ofNat 64 o ∧
      stackArg ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)) 1 = BitVec.ofNat 64 q ∧
      stackArg ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)) 2 =
        W s + BitVec.ofNat 64 80 := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have wt := hp.w_t
  have wsp := hp.w_sp
  obtain hn8 : 8 * [Reg.rax, .r9, .r10].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax, .r9, .r10] (by decide) hn8
  obtain hpj' : ∀ j (hj : j < 3), (pushed [.rax, .r9, .r10] st).mem.readW (SP s - BitVec.ofNat 64 (8 * (j + 1))) 64 =
      st.gpr ([Reg.rax, .r9, .r10][j]'hj) := fun j hj => by rw [← hsp]; exact hpj j hj
  obtain hP : (pushed [.rax, .r9, .r10] st).gpr .rsp = SP s - BitVec.ofNat 64 24 := by rw [pushed_rsp, hsp]; rfl
  obtain hpf' : Frame [⟨SP s - BitVec.ofNat 64 24, 24⟩] st.mem (pushed [.rax, .r9, .r10] st).mem := by
    rw [hsp] at hpf; exact hpf
  obtain hE : Frame [⟨SP s - BitVec.ofNat 64 32, 8⟩] (pushed [.rax, .r9, .r10] st).mem
      (pushed [.rax, .r9, .r10] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax, .r9, .r10] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  -- The memory the call starts from, from `s`'s.
  obtain fU : Frame (wR s ++ [tR s]) s.mem (pushed [.rax, .r9, .r10] st).callEntry.mem :=
    (hf.trans (frame_stk (s := s) (by decide) (by decide) hpf')).trans (frame_stk (s := s) (by decide) (by decide) hE)
  obtain fS : Frame (wR s ++ [tR s]) st.mem (pushed [.rax, .r9, .r10] st).callEntry.mem :=
    (frame_stk (s := s) (by decide) (by decide) hpf').trans (frame_stk (s := s) (by decide) (by decide) hE)
  obtain hPsp8 : 8 ≤ (SP s - BitVec.ofNat 64 24).toNat := by rw [toNat_sub_ofNat (by omega_arith)]; omega_arith
  obtain hPt : (SP s - BitVec.ofNat 64 24).toNat = (SP s).toNat - 24 := toNat_sub_ofNat (by omega_arith)
  obtain ea : ∀ i, i < 3 → stackArg ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)) i =
      (pushed [.rax, .r9, .r10] st).mem.readW (SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * i)) 64 :=
    fun i hi => stackArg_entry hP hPsp8 _ _ (by rw [hPt]; omega_arith)
  obtain a0 := ea 0 (by decide)
  obtain a1 := ea 1 (by decide)
  obtain a2 := ea 2 (by decide)
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 0) = SP s - BitVec.ofNat 64 (8 * (2 + 1)) from
    by simp, hpj' 2 (by decide)] at a0
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 1) = SP s - BitVec.ofNat 64 (8 * (1 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 1 (by decide)] at a1
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 2) = SP s - BitVec.ofNat 64 (8 * (0 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 0 (by decide)] at a2
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at a0 a1 a2
  obtain gU : ∀ r, r ≠ .rsp →
      ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  obtain hU : ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)).gpr .rsp =
      SP s - BitVec.ofNat 64 32 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hP, ← Offset.sub_add_eq]; rfl
  obtain hok : M.ok ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)).mem (K s) := by
    rw [State.withRegions_mem]
    exact M.frame fU (k_disj hp) hp.w_k hp.ok
  obtain hpre := blkPre hp hq hU rfl rfl (by rw [gU _ (by decide)]; exact h_di) (by rw [gU _ (by decide)]; exact h_si)
    (by rw [gU _ (by decide)]; exact h_dx) (by rw [gU _ (by decide)]; exact h_cx) (by rw [gU _ (by decide)]; exact h_8)
    (by rw [gU _ (by decide)]; exact h_9) (by rw [a0, h_10]) (by rw [a1, h_9]) (by rw [a2, h_ax]) hok
  obtain hPw : (pushed [.rax, .r9, .r10] st).wr = ⟨SP s - BitVec.ofNat 64 24, 24⟩ :: wR s := by
    rw [pushed_wr, hsp, hwr, hp.wr]; rfl
  obtain hPr : (pushed [.rax, .r9, .r10] st).rd = [kR M s, srcR s, aR s] := by rw [pushed_rd, hrd, hp.rd]
  obtain cC : ∀ {ts : List Region}, stR s ∈ ts → Covers [ctrR s] ts := fun h =>
    covers_off (k := 80) (d := 48) (m := 16) h (by decide) (by decide)
  obtain cY : ∀ {ts : List Region}, stR s ∈ ts → Covers [yR s] ts := fun h =>
    covers_off (k := 80) (d := 16) (m := 16) h (by decide) (by decide)
  obtain cSc : ∀ {ts : List Region}, wkR s ∈ ts → Covers [scR s] ts := fun h =>
    covers_off (k := 2192) (d := 80) (m := 2112) h (by decide) (by decide)
  obtain cD : ∀ {ts : List Region}, dR s ∈ ts → Covers [⟨Dst s + BitVec.ofNat 64 o, q * 16⟩] ts := fun h =>
    covers_off (k := L s) h (by omega_arith) (by omega_arith)
  obtain cR : ∀ {ts : List Region}, srcR s ∈ ts → Covers [⟨Src s + BitVec.ofNat 64 o, q * 16⟩] ts := fun h =>
    covers_off (k := L s) h (by omega_arith) (by omega_arith)
  obtain cw : Covers (blkWr s o q) (pushed [.rax, .r9, .r10] st).wr := by
    rw [hPw]
    exact covers_cons' (cC (by simp)) (covers_cons' (cY (by simp)) (covers_cons' (cD (by simp))
      (covers_cons' (cSc (by simp)) covers_nil')))
  obtain cr : Covers (blkRd s M o q ++ blkWr s o q) ((pushed [.rax, .r9, .r10] st).rd ++ (pushed [.rax, .r9, .r10] st).wr) := by
    rw [hPr, hPw]
    exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (cR (by simp))
      (covers_cons' (covers_of_mem (by simp)) (covers_cons' (cC (by simp)) (covers_cons' (cY (by simp))
      (covers_cons' (cD (by simp)) (covers_cons' (cSc (by simp)) covers_nil'))))))
  exact ⟨hpre, cr, cw, by rw [a0, h_10], by rw [a1, h_9], by rw [a2, h_ax]⟩

/-- The call of `vg_aes_gcm_encrypt_blocks_to` on `q` whole blocks, with
`dst`, `q` and the working space pushed for it. -/
theorem blkCall_ok (T : BlkToFn M) {o q : Nat} (hq : o + 16 * q ≤ L s) {st : State}
    (hsp : st.gpr .rsp = SP s) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hf : Frame (wR s ++ [tR s]) s.mem st.mem)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = St s + BitVec.ofNat 64 48)
    (h_cx : st.gpr .rcx = St s + BitVec.ofNat 64 16) (h_8 : st.gpr .r8 = Src s + BitVec.ofNat 64 o) (h_9 : st.gpr .r9 = BitVec.ofNat 64 q)
    (h_10 : st.gpr .r10 = Dst s + BitVec.ofNat 64 o) (h_ax : st.gpr .rax = W s + BitVec.ofNat 64 80) :
    WP isa (.frame (.push [.rax, .r9, .r10]) (.call T.fn.name T.fn.code) (.pop .rax 3)) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      Frame (blkWr s o q ++ [tR s]) st.mem st'.mem ∧
      blocksAt st'.mem (Dst s + BitVec.ofNat 64 o) q =
        ctr32 (ciph s) (blockAt st.mem (St s + BitVec.ofNat 64 48)) (blocksAt st.mem (Src s + BitVec.ofNat 64 o) q) ∧
      blockAt st'.mem (St s + BitVec.ofNat 64 48) = Nat.repeat inc32 q (blockAt st.mem (St s + BitVec.ofNat 64 48)) ∧
      blockAt st'.mem (St s + BitVec.ofNat 64 16) =
        ghashFrom (hk s) (blockAt st.mem (St s + BitVec.ofNat 64 16)) (blocksAt st'.mem (Dst s + BitVec.ofNat 64 o) q) := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have wt := hp.w_t
  have wsp := hp.w_sp
  obtain hn8 : 8 * [Reg.rax, .r9, .r10].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax, .r9, .r10] (by decide) hn8
  obtain hpj' : ∀ j (hj : j < 3), (pushed [.rax, .r9, .r10] st).mem.readW (SP s - BitVec.ofNat 64 (8 * (j + 1))) 64 =
      st.gpr ([Reg.rax, .r9, .r10][j]'hj) := fun j hj => by rw [← hsp]; exact hpj j hj
  obtain hP : (pushed [.rax, .r9, .r10] st).gpr .rsp = SP s - BitVec.ofNat 64 24 := by rw [pushed_rsp, hsp]; rfl
  obtain hpf' : Frame [⟨SP s - BitVec.ofNat 64 24, 24⟩] st.mem (pushed [.rax, .r9, .r10] st).mem := by
    rw [hsp] at hpf; exact hpf
  obtain hE : Frame [⟨SP s - BitVec.ofNat 64 32, 8⟩] (pushed [.rax, .r9, .r10] st).mem
      (pushed [.rax, .r9, .r10] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax, .r9, .r10] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  -- The memory the call starts from, from `s`'s.
  obtain fU : Frame (wR s ++ [tR s]) s.mem (pushed [.rax, .r9, .r10] st).callEntry.mem :=
    (hf.trans (frame_stk (s := s) (by decide) (by decide) hpf')).trans (frame_stk (s := s) (by decide) (by decide) hE)
  obtain fS : Frame (wR s ++ [tR s]) st.mem (pushed [.rax, .r9, .r10] st).callEntry.mem :=
    (frame_stk (s := s) (by decide) (by decide) hpf').trans (frame_stk (s := s) (by decide) (by decide) hE)
  obtain hPsp8 : 8 ≤ (SP s - BitVec.ofNat 64 24).toNat := by rw [toNat_sub_ofNat (by omega_arith)]; omega_arith
  obtain hPt : (SP s - BitVec.ofNat 64 24).toNat = (SP s).toNat - 24 := toNat_sub_ofNat (by omega_arith)
  obtain ea : ∀ i, i < 3 → stackArg ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)) i =
      (pushed [.rax, .r9, .r10] st).mem.readW (SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * i)) 64 :=
    fun i hi => stackArg_entry hP hPsp8 _ _ (by rw [hPt]; omega_arith)
  obtain a0 := ea 0 (by decide)
  obtain a1 := ea 1 (by decide)
  obtain a2 := ea 2 (by decide)
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 0) = SP s - BitVec.ofNat 64 (8 * (2 + 1)) from
    by simp, hpj' 2 (by decide)] at a0
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 1) = SP s - BitVec.ofNat 64 (8 * (1 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 1 (by decide)] at a1
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 2) = SP s - BitVec.ofNat 64 (8 * (0 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 0 (by decide)] at a2
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at a0 a1 a2
  obtain gU : ∀ r, r ≠ .rsp →
      ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  obtain hU : ((pushed [.rax, .r9, .r10] st).callEntry.withRegions (blkRd s M o q) (blkWr s o q)).gpr .rsp =
      SP s - BitVec.ofNat 64 32 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hP, ← Offset.sub_add_eq]; rfl
  obtain ⟨hpre, cr, cw, -, -, -⟩ := blkEntry hp hq hsp hrd hwr hf h_di h_si h_dx h_cx h_8 h_9 h_10 h_ax
  -- What the push and the return address leave as it was.
  obtain keep : ∀ {p : Addr} {n : Nat}, (⟨p, n⟩ : Region).Disjoint (tR s) → n ≤ 2 ^ 64 →
      bytesAt (pushed [.rax, .r9, .r10] st).callEntry.mem p n = bytesAt st.mem p n := fun hd hn => by
    rw [bytesAt_frame hE (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd.sub_right (stk_sub (s := s) (by decide) (by decide))) hn,
      bytesAt_frame hpf' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd.sub_right (stk_sub (s := s) (by decide) (by decide))) hn]
  obtain keepB : ∀ {p : Addr}, (⟨p, 16⟩ : Region).Disjoint (tR s) →
      blockAt (pushed [.rax, .r9, .r10] st).callEntry.mem p = blockAt st.mem p := fun hd => by
    rw [blockAt, blockAt, keep hd (by decide)]
  obtain keepBs : ∀ {p : Addr} {n : Nat}, (⟨p, 16 * n⟩ : Region).Disjoint (tR s) → 16 * n ≤ 2 ^ 64 →
      blocksAt (pushed [.rax, .r9, .r10] st).callEntry.mem p n = blocksAt st.mem p n := fun hd hn => by
    rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, keep hd hn]
  obtain pr := pre_sub (s := s) hq
  obtain eC := keepB (hp.b_st.symm.sub_left ctr_sub)
  obtain eY := keepB (hp.b_st.symm.sub_left y_sub)
  obtain eS := keepBs (n := q) (hp.b_r.symm.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith)
  obtain hqn : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.call_sp_mx (k := Proof.AesGcm.encryptBlocksToX86_64M M)
    T.ok T.sp (by have := T.xd; omega_arith) hpre cr cw fun s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, _, hpost⟩ _ => ?_)
  obtain r₃ := hcs _ (by decide : Reg.rsp ∈ calleeSaved)
  simp only [Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPost, Proof.AesGcm.arg, a0,
    State.withRegions_mem, gU _ (by decide : Reg.rdi ≠ .rsp), gU _ (by decide : Reg.rsi ≠ .rsp),
    gU _ (by decide : Reg.rdx ≠ .rsp), gU _ (by decide : Reg.rcx ≠ .rsp), gU _ (by decide : Reg.r8 ≠ .rsp),
    gU _ (by decide : Reg.r9 ≠ .rsp), h_di, h_si, h_dx, h_cx, h_8, h_9, h_10, hqn, hm₂, ciph_eq hp fU, hk_eq hp fU,
    eC, eY, eS] at hpost
  obtain ⟨o₁, o₂, o₃⟩ := hpost
  refine ⟨r₃, hwr', fun r hr => ?_, by rw [popped_rd, hrd', pushed_rd], by rw [popped_wr, hwr', pushed_wr]; rfl,
    ?_, ?_, ?_, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, hP, hsp]
      show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 24 = SP s
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), hcs r hr, pushed_gpr _ _ hr']
  · rw [popped_mem]
    obtain b32 : Region.Sub (below ((pushed [.rax, .r9, .r10] st).gpr .rsp) (T.fn.code.x86_64Depth + 8)) (tR s) := by
      obtain h₁ := below_sub (sp := (pushed [.rax, .r9, .r10] st).gpr .rsp) (a := T.fn.code.x86_64Depth + 8) (b := 32)
        (by have := T.xd; omega_arith) (by decide)
      obtain e : below (SP s - BitVec.ofNat 64 24) 32 = ⟨SP s - BitVec.ofNat 64 56, 32⟩ := by
        simp only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add]
      rw [hP] at h₁ ⊢
      rw [e] at h₁
      exact fun a h => stk_sub (s := s) (by decide) (by decide) a (h₁ a h)
    refine (hpf'.sub fun r hr => ?_).trans (hfr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨tR s, by simp, stk_sub (s := s) (by decide) (by decide)⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨tR s, by simp, b32⟩
  · rw [popped_mem]; exact o₁
  · rw [popped_mem]; exact o₂
  · rw [popped_mem, o₁]; exact o₃

end

end VG.Proof.AesGcm.X86_64.StreamTo
