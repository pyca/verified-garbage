import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.AesCcm.X86_64.Frame
import VerifiedGarbage.Proof.Ocb.Stretch32
import VerifiedGarbage.Impl.AesOcb.X86_64
import VerifiedGarbage.Proof.CmacAes.X86_64.Verified
import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Contract`. -/
section

/-!
# AES-OCB on x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ocb/Contract.lean`, with the working space as a
last argument (`Proof/AesOcb/Scratch.lean`), which imply these
(`Verified.lean`). The functions call `vg_aes_encrypt_blocks`,
`vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch`, which use no stack: the
return address of a call is in the 8 bytes below the stack pointer (`stk8`),
which no buffer overlaps, nor the return address (`ret`).
-/

namespace VG.Proof.AesOcb

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (ctxCiph ctxInv ctxLstar encryptWith decryptWith lengthsOk zeros KeyRepr)

/-- The return address. -/
abbrev ret (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- The stack the calls use. -/
abbrev stk8 (s : State) : Region := below (s.gpr .rsp) 8

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 64 := stackArg s i

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (s : State) : Prop :=
  (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14

/-- The key context. -/
abbrev aCtx (s : State) : Region := ⟨s.gpr .rdi, 256⟩

/-- The nonce. -/
abbrev aNonce (s : State) : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩

/-- The associated data. -/
abbrev aAad (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩

/-- The data. -/
abbrev aData (s : State) : Region := ⟨VG.Proof.AesOcb.arg s 0, (VG.Proof.AesOcb.arg s 1).toNat⟩

/-- The tag. -/
abbrev aTag (s : State) : Region := ⟨VG.Proof.AesOcb.arg s 2, (VG.Proof.AesOcb.arg s 3).toNat⟩

/-- The working space. -/
abbrev aWork (s : State) : Region := ⟨VG.Proof.AesOcb.arg s 4, 2560⟩

/-- What `vg_aes_ocb_seal` and `vg_aes_ocb_open` need of their arguments
`(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx, aad = r8,
aad_len = r9, data = [rsp + 8], len = [rsp + 16], tag = [rsp + 24],
tag_len = [rsp + 32], work = [rsp + 40])`, but for what they may access. -/
def oneFacts (s : State) : Prop :=
  (VG.Proof.AesOcb.aCtx s).Disjoint (VG.Proof.AesOcb.aData s) ∧ (VG.Proof.AesOcb.aCtx s).Disjoint (VG.Proof.AesOcb.aWork s) ∧ (VG.Proof.AesOcb.aNonce s).Disjoint (VG.Proof.AesOcb.aData s) ∧
    (VG.Proof.AesOcb.aNonce s).Disjoint (VG.Proof.AesOcb.aWork s) ∧ (VG.Proof.AesOcb.aAad s).Disjoint (VG.Proof.AesOcb.aData s) ∧ (VG.Proof.AesOcb.aAad s).Disjoint (VG.Proof.AesOcb.aWork s) ∧
    (VG.Proof.AesOcb.aTag s).Disjoint (VG.Proof.AesOcb.aData s) ∧ (VG.Proof.AesOcb.aTag s).Disjoint (VG.Proof.AesOcb.aWork s) ∧
    (VG.Proof.AesOcb.aData s).Disjoint (VG.Proof.AesOcb.aWork s) ∧ (VG.Proof.AesOcb.aData s).Disjoint (VG.Proof.AesOcb.args s 5) ∧ (VG.Proof.AesOcb.aWork s).Disjoint (VG.Proof.AesOcb.args s 5) ∧
    (VG.Proof.AesOcb.ret s).Disjoint (VG.Proof.AesOcb.aData s) ∧ (VG.Proof.AesOcb.ret s).Disjoint (VG.Proof.AesOcb.aWork s) ∧ (VG.Proof.AesOcb.ret s).Disjoint (VG.Proof.AesOcb.aTag s) ∧
    (VG.Proof.AesOcb.stk8 s).Disjoint (VG.Proof.AesOcb.aCtx s) ∧ (VG.Proof.AesOcb.stk8 s).Disjoint (VG.Proof.AesOcb.aNonce s) ∧ (VG.Proof.AesOcb.stk8 s).Disjoint (VG.Proof.AesOcb.aAad s) ∧
    (VG.Proof.AesOcb.stk8 s).Disjoint (VG.Proof.AesOcb.aData s) ∧ (VG.Proof.AesOcb.stk8 s).Disjoint (VG.Proof.AesOcb.aWork s) ∧ (VG.Proof.AesOcb.stk8 s).Disjoint (VG.Proof.AesOcb.aTag s) ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (VG.Proof.AesOcb.arg s 0).toNat + (VG.Proof.AesOcb.arg s 1).toNat ≤ 2 ^ 64 ∧
    (VG.Proof.AesOcb.arg s 2).toNat + (VG.Proof.AesOcb.arg s 3).toNat ≤ 2 ^ 64 ∧
    (VG.Proof.AesOcb.arg s 4).toNat + 2560 ≤ 2 ^ 64 ∧ 8 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧
    VG.Proof.AesOcb.rounds s ∧ lengthsOk (VG.Proof.AesOcb.arg s 3).toNat (s.gpr .rcx).toNat = true

/-- What `vg_aes_ocb_seal` needs: it may write the data, the tag and the
working space. -/
def sealPreX (s : State) : Prop :=
  s.rd = [VG.Proof.AesOcb.aCtx s, VG.Proof.AesOcb.aNonce s, VG.Proof.AesOcb.aAad s, VG.Proof.AesOcb.args s 5] ∧ s.wr = [VG.Proof.AesOcb.aData s, VG.Proof.AesOcb.aTag s, VG.Proof.AesOcb.aWork s] ∧
    (VG.Proof.AesOcb.aTag s).Disjoint (VG.Proof.AesOcb.args s 5) ∧ (VG.Proof.AesOcb.aCtx s).Disjoint (VG.Proof.AesOcb.aTag s) ∧ (VG.Proof.AesOcb.aNonce s).Disjoint (VG.Proof.AesOcb.aTag s) ∧
    (VG.Proof.AesOcb.aAad s).Disjoint (VG.Proof.AesOcb.aTag s) ∧ VG.Proof.AesOcb.oneFacts s

/-- What `vg_aes_ocb_open` needs: it may write the data and the working
space, and read the tag. -/
def openPreX (s : State) : Prop :=
  s.rd = [VG.Proof.AesOcb.aCtx s, VG.Proof.AesOcb.aNonce s, VG.Proof.AesOcb.aAad s, VG.Proof.AesOcb.aTag s, VG.Proof.AesOcb.args s 5] ∧ s.wr = [VG.Proof.AesOcb.aData s, VG.Proof.AesOcb.aWork s] ∧ VG.Proof.AesOcb.oneFacts s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ ∀ i < 5, VG.Proof.AesOcb.arg s₁ i = VG.Proof.AesOcb.arg s₂ i

/-- `OCB-DECRYPT` of what `vg_aes_ocb_open` is given. -/
def openOut (s : State) : Option (List Byte) :=
  VG.Spec.Ocb.decryptWith (VG.Spec.Ocb.ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxInv s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    (ctxLstar s.mem (s.gpr .rdi)) (VG.Proof.AesOcb.arg s 3).toNat (VG.Spec.Aes.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (VG.Spec.Aes.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (VG.Spec.Aes.bytesAt s.mem (VG.Proof.AesOcb.arg s 0) (VG.Proof.AesOcb.arg s 1).toNat)
    (VG.Spec.Aes.bytesAt s.mem (VG.Proof.AesOcb.arg s 2) (VG.Proof.AesOcb.arg s 3).toNat)

/-- `vg_aes_ocb_seal`. -/
def sealX86_64 : Contract isa where
  pre := VG.Proof.AesOcb.sealPreX
  post s s' :=
    VG.Spec.Ocb.encryptWith (VG.Spec.Ocb.ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxLstar s.mem (s.gpr .rdi)) (VG.Proof.AesOcb.arg s 3).toNat
        (VG.Spec.Aes.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (VG.Spec.Aes.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (VG.Spec.Aes.bytesAt s.mem (VG.Proof.AesOcb.arg s 0) (VG.Proof.AesOcb.arg s 1).toNat) =
      (VG.Spec.Aes.bytesAt s'.mem (VG.Proof.AesOcb.arg s 0) (VG.Proof.AesOcb.arg s 1).toNat, VG.Spec.Aes.bytesAt s'.mem (VG.Proof.AesOcb.arg s 2) (VG.Proof.AesOcb.arg s 3).toNat)
  pub := VG.Proof.AesOcb.onePub

/-- What `vg_aes_ocb_open` may leak (`Spec.Ocb.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬VG.Proof.AesOcb.rounds s then [] else [if (VG.Proof.AesOcb.openOut s).isSome then 1 else 0]

/-- `vg_aes_ocb_open`. -/
def openX86_64 : Contract isa where
  pre := VG.Proof.AesOcb.openPreX
  post s s' :=
    match VG.Proof.AesOcb.openOut s with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ VG.Spec.Aes.bytesAt s'.mem (VG.Proof.AesOcb.arg s 0) (VG.Proof.AesOcb.arg s 1).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ VG.Spec.Aes.bytesAt s'.mem (VG.Proof.AesOcb.arg s 0) (VG.Proof.AesOcb.arg s 1).toNat = VG.Spec.Ocb.zeros (VG.Proof.AesOcb.arg s 1).toNat
  pub s₁ s₂ := VG.Proof.AesOcb.onePub s₁ s₂ ∧ VG.Proof.AesOcb.openLeak s₁ = VG.Proof.AesOcb.openLeak s₂

/-- `vg_aes_ocb_init(key = rdi, key_len = rsi, ctx = rdx, scratch = rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let ctx : Region := ⟨s.gpr .rdx, 256⟩
    let scr : Region := ⟨s.gpr .rcx, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (VG.Proof.AesOcb.ret s).Disjoint ctx ∧ (VG.Proof.AesOcb.ret s).Disjoint scr ∧
      (VG.Proof.AesOcb.stk8 s).Disjoint key ∧ (VG.Proof.AesOcb.stk8 s).Disjoint ctx ∧ (VG.Proof.AesOcb.stk8 s).Disjoint scr ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 256 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 2560 ≤ 2 ^ 64 ∧ 8 ≤ (s.gpr .rsp).toNat ∧
      ((s.gpr .rsi).toNat = 16 ∨ (s.gpr .rsi).toNat = 24 ∨ (s.gpr .rsi).toNat = 32)
  post s s' := VG.Spec.Ocb.KeyRepr s'.mem (s.gpr .rdx) (VG.Spec.Aes.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.AesOcb

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Env`. -/
section

/-!
# AES-OCB on x86-64: where everything is

Untrusted: everything here is checked by Lean. The key context (256 bytes
at `K`), the working space (2560 bytes at `W`) and the 8 bytes of stack
below `SP` that the calls use (`Lay`); what a state may access (`Perm`); the
registers holding `K` and `W` and the stack pointer (`Env`); and the public
values the entry keeps in `W` (`Slots`). The pieces write the parts of `W`
in `mutR` (and the data, and the stack below `SP`), so the slots and our
caller's registers saved in `W` stay as the entry left them.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.X86_64 (covers_off in_off in_left covers_left)

/-! ## The regions -/

/-- The key context, `W` and the stack below `SP` used by the calls. -/
structure Lay (K W SP : Addr) : Prop where
  kw : K.toNat + 256 ≤ 2 ^ 64
  ww : W.toNat + 2560 ≤ 2 ^ 64
  k_w : (⟨K, 256⟩ : Region).Disjoint ⟨W, 2560⟩
  stk_k : (below SP 8).Disjoint ⟨K, 256⟩
  stk_w : (below SP 8).Disjoint ⟨W, 2560⟩
  sp : 8 ≤ SP.toNat

/-- What a state may access. -/
structure Perm (K W : Addr) (s : State) : Prop where
  k : Covers [⟨K, 256⟩] (s.rd ++ s.wr)
  w : Covers [⟨W, 2560⟩] s.wr

/-- The registers holding the key context, `W` and the stack pointer, and
what the state may access. -/
structure Env (K W SP : Addr) (s : State) : Prop where
  r14 : s.gpr .r14 = K
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = SP
  perm : VG.Proof.AesOcb.X86_64.Perm K W s

theorem Perm.of_eq {K W : Addr} {s s' : State} (h : VG.Proof.AesOcb.X86_64.Perm K W s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesOcb.X86_64.Perm K W s' := ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps `r14`, `r15`, `rsp` and the permissions. -/
theorem Env.keep {K W SP : Addr} {s s' : State} (h : VG.Proof.AesOcb.X86_64.Env K W SP s)
    (hg : ∀ r ∈ [Reg.r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesOcb.X86_64.Env K W SP s' :=
  ⟨by rw [hg _ (by simp), h.r14], by rw [hg _ (by simp), h.r15], by rw [hg _ (by simp), h.rsp],
    h.perm.of_eq hrd hwr⟩

theorem Env.of_saved {K W SP : Addr} {s s' : State} (h : VG.Proof.AesOcb.X86_64.Env K W SP s)
    (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesOcb.X86_64.Env K W SP s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg _ (by decide)) hrd hwr

namespace Lay

theorem kSub {K : Addr} {d n : Nat} (h : d + n ≤ 256) : Region.Sub ⟨K + BitVec.ofNat 64 d, n⟩ ⟨K, 256⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

variable {K W SP : Addr} (L : VG.Proof.AesOcb.X86_64.Lay K W SP)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

theorem k_w' {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 2560) :
    (⟨K + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  (L.k_w.sub_left (VG.Proof.AesOcb.X86_64.Lay.kSub ha)).sub_right (VG.Proof.AesOcb.X86_64.Lay.wSub hd)

theorem stk_w' {a n : Nat} (ha : a + n ≤ 2560) : (below SP 8).Disjoint ⟨W + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (VG.Proof.AesOcb.X86_64.Lay.wSub ha)

theorem stk_k' {a n : Nat} (ha : a + n ≤ 256) : (below SP 8).Disjoint ⟨K + BitVec.ofNat 64 a, n⟩ :=
  L.stk_k.sub_right (VG.Proof.AesOcb.X86_64.Lay.kSub ha)

end Lay

namespace Perm

variable {K W : Addr} {s : State} (P : VG.Proof.AesOcb.X86_64.Perm K W s)
include P

theorem kR {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 d) n :=
  VG.Proof.AesCcm.X86_64.in_off P.k h (by decide)

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (W + BitVec.ofNat 64 d) n :=
  VG.Proof.AesCcm.X86_64.in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem kC {d n : Nat} (h : d + n ≤ 256) : Covers [⟨K + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_off P.k h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at `D` that the code may read, apart from `W` and
the stack below `SP`. -/
structure Buf (W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  lt : n < 2 ^ 64
  wrap : D.toNat + n ≤ 2 ^ 64
  w : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩
  stk : (below SP 8).Disjoint ⟨D, n⟩

namespace Buf

variable {W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : VG.Proof.AesOcb.X86_64.Buf W SP s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesOcb.X86_64.Buf W SP s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : VG.Proof.AesOcb.X86_64.Buf W SP s (D + BitVec.ofNat 64 k) (n - k) where
  rd := covers_off h.rd (by omega) h.lt
  lt := by have := h.lt; omega
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega)]
    have := Nat.mod_le (D.toNat + k) (2 ^ 64)
    omega
  w := h.w.sub_left (Offset.sub_base D (by omega))
  stk := h.stk.sub_right (Offset.sub_base D (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : VG.Proof.AesOcb.X86_64.Buf W SP s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : VG.Proof.AesOcb.X86_64.Buf W SP s (D + BitVec.ofNat 64 a) k :=
  (h.drop (k := a) (by omega)).take (by omega)

end Buf

/-- The data: a buffer that the code may also write, apart from the key
context. -/
structure DBuf (K W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop extends VG.Proof.AesOcb.X86_64.Buf W SP s D n where
  wr : Covers [⟨D, n⟩] s.wr
  k : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩

namespace DBuf

variable {K W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : VG.Proof.AesOcb.X86_64.DBuf K W SP s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesOcb.X86_64.DBuf K W SP s' D n :=
  { h.toBuf.of_eq hrd hwr with wr := by rw [hwr]; exact h.wr, k := h.k }

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : VG.Proof.AesOcb.X86_64.DBuf K W SP s (D + BitVec.ofNat 64 a) k where
  toBuf := h.toBuf.slice hk
  wr := by
    have := (h.toBuf.drop (k := a) (by omega))
    exact fun x m hx => covers_off h.wr (d := a) (n := k) hk h.lt x m hx
  k := h.k.sub_right ((Offset.sub_base D (by omega)))

end DBuf

/-! ## The slots -/

/-- The public values the entry keeps in `W`: the data and its length, the
tag length, the rounds, the associated data, the nonce and its length. -/
structure Slots (W : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (m : Mem) : Prop where
  data : m.readW (W + BitVec.ofNat 64 208) 64 = D
  len : m.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n
  tl : m.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 tl
  rounds : m.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R
  aad : m.readW (W + BitVec.ofNat 64 240) 64 = A
  nonce : m.readW (W + BitVec.ofNat 64 288) 64 = N
  nlen : m.readW (W + BitVec.ofNat 64 296) 64 = BitVec.ofNat 64 nl

/-- The parts of `W` the pieces write: the blocks at `[0, 160)`, `[248, 288)`
(the length of the associated data, `bottom` and `Offset_0`) and
`[384, 2560)`. -/
abbrev wA (W : Addr) : Region := ⟨W, 160⟩
abbrev wB (W : Addr) : Region := ⟨W + BitVec.ofNat 64 248, 40⟩
abbrev wC (W : Addr) : Region := ⟨W + BitVec.ofNat 64 384, 2176⟩

/-- What the pieces may change: those parts of `W`, the stack below `SP`
and the data. -/
abbrev mutR (W SP D : Addr) (n : Nat) : List Region := [VG.Proof.AesOcb.X86_64.wA W, VG.Proof.AesOcb.X86_64.wB W, VG.Proof.AesOcb.X86_64.wC W, below SP 8, ⟨D, n⟩]

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {K W SP D : Addr} {n : Nat} (L : VG.Proof.AesOcb.X86_64.Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {d k : Nat} (hd : 160 ≤ d ∧ d + k ≤ 248 ∨ 288 ≤ d ∧ d + k ≤ 384) :
    ∀ r ∈ VG.Proof.AesOcb.X86_64.mutR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := k) (d := 0) (k := 160) (.inr (by omega)) (by omega) (by decide)
  · rcases hd with hd | hd
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w' (by omega)).symm
  · exact (hD.sub_right (Lay.wSub (by omega))).symm

/-- The key context misses the parts the pieces write. -/
theorem k_mut {K W SP D : Addr} {n : Nat} (L : VG.Proof.AesOcb.X86_64.Lay K W SP) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ r ∈ VG.Proof.AesOcb.X86_64.mutR W SP D n, (⟨K, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.k_w.sub_right (Region.sub_prefix (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.stk_k.symm
  · exact hD

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Run`. -/
section

/-!
# AES-OCB on x86-64: running straight-line blocks

Untrusted: everything here is checked by Lean. `orun [facts]` runs a block
symbolically (`runBlock_cons`, `runStep_some`, the semantics of the
instructions the code uses, and reads through the writes with `RegUpd`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Proof.AesCcm.X86_64 (imm_eq offset_nat setWidth_imm)

/-- Runs a block of the instructions the AES-OCB code uses. -/
macro "orun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [imm_eq, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, execShift, State.load64, State.store64, State.load8, State.store8, State.ea,
    offset_nat, at_, ld, st, mvr, addi, tagO, ofsO, ckO, sumO, ldO, l0O, lO, tmpO, t2O, ohO, savO,
    dataO, lenO, tlO, tgO, rndO, aadO, alenO, botO, o0O, nO, nlO, bufO, scrO, List.cons_append,
    List.nil_append, List.append_assoc, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
    gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags,
    wr_setReg, wr_arithFlags, wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags,
    ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff,
    Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, setWidth_imm, and_self, and_true, true_and, $ts,*]) <;> try rfl)

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Words`. -/
section

/-!
# AES-OCB on x86-64: blocks of `W`, two words at a time

Untrusted: everything here is checked by Lean. `zero16`, `copy16`, `xor16`
and `dbl` write a block of `W` (`BlkStep`): zeros, a copy, the XOR with a
block and `double` of a block (`zero16_ok`, `copy16_ok`, `xor16_ok`,
`dbl_ok`), as blocks of memory (`blockAtMem`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Ocb (Block blockAtMem double)
open VG.Proof.Cmac (le8 le8_readW xor_words bytesAt_store2)
open VG.Proof.AesCcm.X86_64 (in_left)

/-- What a step writing the block at `W + d` does: it writes only there,
the block `v`, and keeps the registers but `clob`. -/
structure BlkStep (W : Addr) (d : Nat) (v : Block) (clob : List Reg) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (W + BitVec.ofNat 64 d) = v
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem frame_store2 (m : Mem) (p : Addr) (w₀ w₁ : BitVec 64) :
    Frame [⟨p, 16⟩] m ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains p (d := 0) (n := 8) (e := 0) (k := 16) (by decide) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _
    (by simpa using Offset.contains p (d := 8) (n := 8) (e := 0) (k := 16) (by decide) (by decide) (by decide))

theorem blockAtMem_store2 (m : Mem) (p : Addr) (w₀ w₁ : BitVec 64) :
    blockAtMem ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) p = Spec.Ocb.ofBytes (le8 w₀ ++ le8 w₁) := by
  rw [blockAtMem, bytesAt_store2]

/-- The two words of a block, XORed with those of another, are the XOR of
the blocks. -/
theorem blockAtMem_xor_words (m : Mem) (p q : Addr) :
    Spec.Ocb.ofBytes (le8 (m.readW p 64 ^^^ m.readW q 64) ++
      le8 (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64)) =
      blockAtMem m p ^^^ blockAtMem m q := by
  rw [xor_words, ← Proof.Ocb.xor_eq, Proof.Ocb.ofBytes_xor (by simp [Spec.Aes.bytesAt])
    (by simp [Spec.Aes.bytesAt])]
  rfl

theorem blockAtMem_words (m : Mem) (p : Addr) :
    Spec.Ocb.ofBytes (le8 (m.readW p 64) ++ le8 (m.readW (p + BitVec.ofNat 64 8) 64)) = blockAtMem m p := by
  rw [le8_readW, le8_readW, ← Proof.Cmac.bytesAt_split]; rfl

theorem blockAtMem_zero : Spec.Ocb.ofBytes (le8 0 ++ le8 0) = 0 := by decide

theorem addr8 (p : Addr) (d : Nat) : p + BitVec.ofNat 64 d + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (d + 8) :=
  Offset.add_add p d 8

/-- `zero16 d`: `W + d ← 0`. -/
theorem zero16_ok {W : Addr} {s : State} {d : Nat} (h15 : s.gpr .r15 = W)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (zero16 d) s = some s' ∧ VG.Proof.AesOcb.X86_64.BlkStep W d 0 [.rax] s s' := by
  refine ⟨_, by orun [zero16, h15, w₀, w₁], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, BitVec.xor_self]; rw [← VG.Proof.AesOcb.X86_64.addr8 W d]; exact VG.Proof.AesOcb.X86_64.frame_store2 _ _ _ _
  · simp only [mem_setReg, mem_arithFlags, BitVec.xor_self]; rw [← VG.Proof.AesOcb.X86_64.addr8 W d, VG.Proof.AesOcb.X86_64.blockAtMem_store2]; decide
  · simp only [List.mem_singleton] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]

/-- `copy16 a d`: `W + d ← W + a`. -/
theorem copy16_ok {W : Addr} {s : State} {a d : Nat} (h15 : s.gpr .r15 = W)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (copy16 a d) s = some s' ∧
      VG.Proof.AesOcb.X86_64.BlkStep W d (blockAtMem s.mem (W + BitVec.ofNat 64 a)) [.rax, .rdx] s s' := by
  refine ⟨_, by orun [copy16, h15, r₀, r₁, w₀, w₁], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [mem_setReg]; rw [← VG.Proof.AesOcb.X86_64.addr8 W d]; exact VG.Proof.AesOcb.X86_64.frame_store2 _ _ _ _
  · simp only [mem_setReg]; rw [← VG.Proof.AesOcb.X86_64.addr8 W d, VG.Proof.AesOcb.X86_64.blockAtMem_store2, ← VG.Proof.AesOcb.X86_64.addr8 W a, VG.Proof.AesOcb.X86_64.blockAtMem_words]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2, ite_false]

/-- `xor16 b a d`: `W + d ← W + d ⊕ (B + a)`, `B` in `b`. -/
theorem xor16_ok {W B : Addr} {s : State} {b : Reg} {a d : Nat} (h15 : s.gpr .r15 = W) (hb : s.gpr b = B)
    (hba : b ≠ .rax) (hbd : b ≠ .rdx)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (xor16 b a d) s = some s' ∧
      VG.Proof.AesOcb.X86_64.BlkStep W d (blockAtMem s.mem (W + BitVec.ofNat 64 d) ^^^ blockAtMem s.mem (B + BitVec.ofNat 64 a))
        [.rax, .rdx] s s' := by
  have v₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 := in_left w₀
  have v₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (d + 8)) 8 := in_left w₁
  refine ⟨_, by orun [xor16, h15, hb, hba, hbd, r₀, r₁, v₀, v₁, w₀, w₁], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags]; rw [← VG.Proof.AesOcb.X86_64.addr8 W d]; exact VG.Proof.AesOcb.X86_64.frame_store2 _ _ _ _
  · simp only [mem_setReg, mem_arithFlags]
    rw [← VG.Proof.AesOcb.X86_64.addr8 W d, VG.Proof.AesOcb.X86_64.blockAtMem_store2, ← VG.Proof.AesOcb.X86_64.addr8 B a, VG.Proof.AesOcb.X86_64.blockAtMem_xor_words]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]

theorem mask87 : BitVec.signExtend 64 (0x87 : BitVec 32) = BitVec.ofNat 64 135 := by decide

/-- `double` of the block at `p`, from its byte-reversed words. -/
theorem dbl_mem (m : Mem) (p : Addr) :
    let hi := bswap64 (m.readW p 64)
    let lo := bswap64 (m.readW (p + BitVec.ofNat 64 8) 64)
    Spec.Ocb.ofBytes (le8 (bswap64 ((hi + hi) ||| (lo >>> 63))) ++
      le8 (bswap64 ((lo + lo) ^^^ (((0 : BitVec 64) - (hi >>> 63)) &&& BitVec.ofNat 64 135)))) =
      double (blockAtMem m p) := by
  intro hi lo
  rw [Proof.CmacAes.X86_64.le8_bswap, ← Proof.Ocb.toBytes_eq, Proof.Ocb.ofBytes_toBytes, ← VG.Proof.AesOcb.X86_64.mask87,
    Proof.CmacAes.X86_64.dbl_words, Proof.Ocb.double_eq]
  congr 1
  have e0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p
  show hi ++ lo = Spec.Gcm.blockAt m p
  rw [← Proof.Gcm.X86_64.blockAt_bswap, e0]

/-- `dbl b a d`: `W + d ← double(B + a)`, `B` in `b`. -/
theorem dbl_ok {W B : Addr} {s : State} {b : Reg} {a d : Nat} (h15 : s.gpr .r15 = W) (hb : s.gpr b = B)
    (hba : b ≠ .rax)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (dbl b a d) s = some s' ∧
      VG.Proof.AesOcb.X86_64.BlkStep W d (double (blockAtMem s.mem (B + BitVec.ofNat 64 a))) [.rax, .rdx, .rcx, .r8] s s' := by
  refine ⟨_, by orun [dbl, h15, hb, hba, r₀, r₁, w₀, w₁], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]; rw [← VG.Proof.AesOcb.X86_64.addr8 W d]; exact VG.Proof.AesOcb.X86_64.frame_store2 _ _ _ _
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, BitVec.xor_self]
    rw [← VG.Proof.AesOcb.X86_64.addr8 W d, VG.Proof.AesOcb.X86_64.blockAtMem_store2, ← VG.Proof.AesOcb.X86_64.addr8 B a]
    exact VG.Proof.AesOcb.X86_64.dbl_mem _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Callee`. -/
section

/-!
# AES-OCB on x86-64: the functions called

Untrusted: everything here is checked by Lean. Calls of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` (of any implementation
`v`) and of `vg_aes_expand_key_scratch` from their contracts (with `WP.call`): what
they need (`BCall`, `KCall`), what they leave (`BPost`, `KPost`), and that two
calls with the same arguments leak the same (`blk_rel`, `key_rel`). A block
the call transforms is `ENCIPHER` (or `DECIPHER`) of the key schedule
(`BPost.enc`, `BPost.dec`), as OCB's blocks in memory (`blockAtMem`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem aesWith aesInvWith)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (bytesAt_frame callEntry_frame disj_below toNat_rounds toNat_ofNat_of_lt)

/-! ## States and blocks -/

theorem bytesAt_toList (m : Mem) (p : Addr) : bytesAt m p 16 = (Spec.Aes.stateAt m p).toList := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ h₂
  simp [bytesAt, Spec.Aes.stateAt]

theorem stateAt_eq (m : Mem) (p : Addr) :
    Spec.Aes.stateAt m p = Vector.ofFn fun i => (Spec.Ocb.toBytes (blockAtMem m p)).getD i.1 0 := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (by simp [bytesAt])]
  apply Vector.ext
  intro i hi
  simp [Spec.Aes.stateAt, bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The block at `p`, after a function of states replaced the state there. -/
theorem blockAtMem_of_state {m m' : Mem} {p : Addr} (g : Spec.Aes.State → Spec.Aes.State)
    (h : Spec.Aes.stateAt m' p = g (Spec.Aes.stateAt m p)) :
    blockAtMem m' p = Spec.Ocb.ofBytes (g (Vector.ofFn fun i => (Spec.Ocb.toBytes (blockAtMem m p)).getD i.1 0)).toList := by
  rw [blockAtMem, VG.Proof.AesOcb.X86_64.bytesAt_toList, h, VG.Proof.AesOcb.X86_64.stateAt_eq]

theorem stateAt_of_statesAt {m m' : Mem} {D : Addr} {n : Nat} {g : Spec.Aes.State → Spec.Aes.State}
    (h : Spec.Aes.statesAt m' D n = (Spec.Aes.statesAt m D n).map g) {i : Nat} (hi : i < n) :
    Spec.Aes.stateAt m' (D + BitVec.ofNat 64 (16 * i)) = g (Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * i))) := by
  have := congrArg (·[i]?) h
  simpa [Spec.Aes.statesAt, hi] using this

theorem blockAtMem_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAtMem m' p = blockAtMem m p := by
  rw [blockAtMem, blockAtMem, VG.Proof.AesCcm.X86_64.bytesAt_frame hf hd (by decide)]

/-! ## `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` -/

/-- What a call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` needs:
the key schedule at `K` for `R` rounds, `n` blocks at `D` and working space
at `S`. -/
structure BCall (s : State) (K D S : Addr) (R n : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = D
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  r8 : s.gpr .r8 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  kd : (⟨K, 240⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ks : (⟨K, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2048⟩
  stkK : (below (s.gpr .rsp) 8).Disjoint ⟨K, 240⟩
  stkD : (below (s.gpr .rsp) 8).Disjoint ⟨D, 16 * n⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 2048⟩
  reads : Covers ([⟨K, 240⟩] ++ [⟨D, 16 * n⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨D, 16 * n⟩, ⟨S, 2048⟩] s.wr

/-- What a call of a function with the contract `blocksX86_64 f` leaves. -/
structure BPost (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s : State) (K D S : Addr) (R n : Nat)
    (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨D, 16 * n⟩, ⟨S, 2048⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : Spec.Aes.statesAt s'.mem D n = (Spec.Aes.statesAt s.mem D n).map (f R (bytesAt s.mem K (16 * (R + 1))))

theorem BCall.pre {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State} {K D S : Addr} {R n : Nat}
    (h : VG.Proof.AesOcb.X86_64.BCall s K D S R n) :
    (Proof.Aes.blocksX86_64 f).pre (s.callEntry.withRegions [⟨K, 240⟩] [⟨D, 16 * n⟩, ⟨S, 2048⟩]) := by
  have hR := VG.Proof.AesCcm.X86_64.toNat_rounds h.rounds
  have hn := VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (show n < 2 ^ 64 by have := h.wrap; omega)
  simp only [Proof.Aes.blocksX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hn]
  exact ⟨trivial, trivial, h.kd, h.ks, h.ds, h.stkD, h.stkS, h.wrap, h.rounds⟩

theorem blk_call {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp c) (depth : c.depth = 0) {s : State} {K D S : Addr} {R n : Nat} (h : VG.Proof.AesOcb.X86_64.BCall s K D S R n) :
    WP isa (.call name c) s (VG.Proof.AesOcb.X86_64.BPost f s K D S R n) := by
  have hR := VG.Proof.AesCcm.X86_64.toNat_rounds h.rounds
  have hn := VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (show n < 2 ^ 64 by have := h.wrap; omega)
  refine WP.call (k := Proof.Aes.blocksX86_64 f) ok nosp (by rw [depth]; decide)
    (rd := [⟨K, 240⟩]) (wr := [⟨D, 16 * n⟩, ⟨S, 2048⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [depth] at hf
  simp only [Proof.Aes.blocksX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, hR, hn, hm₂] at hpost
  have fE := VG.Proof.AesCcm.X86_64.callEntry_frame s
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with rfl | rfl | rfl <;> decide
  have eK := VG.Proof.AesCcm.X86_64.bytesAt_frame fE (p := K) (n := 16 * (R + 1))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stkK.sub_right (Region.sub_prefix hRb)).symm) (by omega)
  have eD : Spec.Aes.statesAt s.callEntry.mem D n = Spec.Aes.statesAt s.mem D n := by
    simp only [Spec.Aes.statesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    simp only [Spec.Aes.stateAt]
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_ofFn]
    rw [Offset.add_add]
    exact fE.bytes (R := ⟨D, 16 * n⟩) (VG.Proof.AesCcm.X86_64.disj_below h.stkD) (by show 16 * n ≤ 2 ^ 64; have := h.wrap; omega) (by show 16 * i + j < 16 * n; omega)
  rw [eK, eD] at hpost
  exact ⟨hrd, hwr, hcs, by simpa using hf, hpost⟩

/-- Block `i` after `vg_aes_encrypt_blocks`. -/
theorem BPost.enc {s s' : State} {K D S : Addr} {R n : Nat} (h : VG.Proof.AesOcb.X86_64.BPost Spec.Aes.cipher s K D S R n s') {i : Nat}
    (hi : i < n) :
    blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      aesWith R (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) :=
  VG.Proof.AesOcb.X86_64.blockAtMem_of_state _ (VG.Proof.AesOcb.X86_64.stateAt_of_statesAt h.out hi)

/-- Block `i` after `vg_aes_decrypt_blocks`. -/
theorem BPost.dec {s s' : State} {K D S : Addr} {R n : Nat} (h : VG.Proof.AesOcb.X86_64.BPost Spec.Aes.invCipher s K D S R n s') {i : Nat}
    (hi : i < n) :
    blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      aesInvWith R (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) :=
  VG.Proof.AesOcb.X86_64.blockAtMem_of_state _ (VG.Proof.AesOcb.X86_64.stateAt_of_statesAt h.out hi)

theorem blk_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub c)
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K D S : Addr, ∃ R n : Nat,
      VG.Proof.AesOcb.X86_64.BCall s₁ K D S R n ∧ VG.Proof.AesOcb.X86_64.BCall s₂ K D S R n ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call name c) fun _ _ => True := by
  refine RelCT.callEx ok ct fun s₁ s₂ hp => ?_
  obtain ⟨K, D, S, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.blocksX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key_scratch` -/

/-- What a call of `vg_aes_expand_key_scratch` needs: the key `Kp` of `KL` bytes,
the schedule `C` and the working space `S`. -/
structure KCall (s : State) (Kp C S : Addr) (KL : Nat) : Prop where
  rdi : s.gpr .rdi = Kp
  rsi : s.gpr .rsi = BitVec.ofNat 64 KL
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = S
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32
  kc : (⟨Kp, KL⟩ : Region).Disjoint ⟨C, 240⟩
  ks : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 512⟩
  cs : (⟨C, 240⟩ : Region).Disjoint ⟨S, 512⟩
  stkK : (below (s.gpr .rsp) 8).Disjoint ⟨Kp, KL⟩
  stkC : (below (s.gpr .rsp) 8).Disjoint ⟨C, 240⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 512⟩
  reads : Covers ([⟨Kp, KL⟩] ++ [⟨C, 240⟩, ⟨S, 512⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 240⟩, ⟨S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key_scratch` leaves. -/
structure KPost (s : State) (Kp C S : Addr) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 240⟩, ⟨S, 512⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : bytesAt s'.mem C (16 * (Spec.Aes.rounds (KL / 4) + 1)) = Spec.Aes.expandKey (bytesAt s.mem Kp KL)

theorem KCall.pre {s : State} {Kp C S : Addr} {KL : Nat} (h : VG.Proof.AesOcb.X86_64.KCall s Kp C S KL) :
    Proof.Aes.expandKeyX86_64.pre (s.callEntry.withRegions [⟨Kp, KL⟩] [⟨C, 240⟩, ⟨S, 512⟩]) := by
  have hK := VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (n := KL) (by rcases h.klen with h | h | h <;> omega)
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, hK]
  exact ⟨trivial, trivial, h.kc, h.ks, h.cs, h.stkC, h.stkS, h.klen⟩

theorem key_call (v : BlocksImpl) {s : State} {Kp C S : Addr} {KL : Nat} (h : VG.Proof.AesOcb.X86_64.KCall s Kp C S KL) :
    WP isa (.call v.expand.name v.expand.code) s (VG.Proof.AesOcb.X86_64.KPost s Kp C S KL) := by
  have hK := VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (n := KL) (by rcases h.klen with h | h | h <;> omega)
  refine WP.call (k := Proof.Aes.expandKeyX86_64) v.expandOk v.expandNosp
    (by rw [v.expandDepth]; decide) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [v.expandDepth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx, hK] at hpost
  rw [← hm₂, hpost, VG.Proof.AesCcm.X86_64.bytesAt_frame (VG.Proof.AesCcm.X86_64.callEntry_frame s) (VG.Proof.AesCcm.X86_64.disj_below h.stkK)
    (by rcases h.klen with h | h | h <;> omega)]

theorem key_rel (v : BlocksImpl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ Kp C S : Addr, ∃ KL : Nat,
      VG.Proof.AesOcb.X86_64.KCall s₁ Kp C S KL ∧ VG.Proof.AesOcb.X86_64.KCall s₂ Kp C S KL ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call v.expand.name v.expand.code) fun _ _ => True := by
  refine RelCT.callEx v.expandOk v.expandCt fun s₁ s₂ hp => ?_
  obtain ⟨Kp, C, S, KL, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Args`. -/
section

/-!
# AES-OCB on x86-64: the calls of the block functions

Untrusted: everything here is checked by Lean. `callBlocks b args` sets up
a call of `b` (`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks`) with the
key schedule of the key context, the rounds kept in `W`, the `n` blocks at
`D` that `args` sets (`Dst`: blocks of `W` below 512, `dstW`, or the data,
`dstD`) and the working space at `W + 512` (`callBlocks_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.X86_64 (covers_left covers_cons covers_nil covers_append covers_off runBlock_append)

/-- `n` blocks at `D` for a call: apart from the key context, the working
space at `W + 512` and the stack below `SP`, and readable and writable. -/
structure Dst (K W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  k : (⟨K, 256⟩ : Region).Disjoint ⟨D, 16 * n⟩
  scr : (⟨D, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩
  stk : (below SP 8).Disjoint ⟨D, 16 * n⟩
  rd : Covers [⟨D, 16 * n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, 16 * n⟩] s.wr

theorem covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
    Covers [⟨p, n⟩] rs := fun a m ⟨r, hr, hc⟩ => by
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

theorem toNat_W {W : Addr} (hw : W.toNat + 2560 ≤ 2 ^ 64) {d : Nat} (hd : d < 2560) :
    (W + BitVec.ofNat 64 d).toNat = W.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Blocks of `W` below 512. -/
theorem dstW {K W SP : Addr} {s : State} (L : VG.Proof.AesOcb.X86_64.Lay K W SP) (P : VG.Proof.AesOcb.X86_64.Perm K W s) {d n : Nat} (h : d + 16 * n ≤ 512) :
    VG.Proof.AesOcb.X86_64.Dst K W SP s (W + BitVec.ofNat 64 d) n where
  wrap := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt (W + BitVec.ofNat 64 d).isLt
    · rw [VG.Proof.AesOcb.X86_64.toNat_W L.ww (by omega)]; have := L.ww; omega
  k := L.k_w.sub_right (Lay.wSub (by omega))
  scr := L.w_w (.inl (by omega)) (by omega) (by decide)
  stk := L.stk_w' (by omega)
  rd := covers_left (P.wC (by omega))
  wr := P.wC (by omega)

/-- Blocks of the data. -/
theorem dstD {K W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : VG.Proof.AesOcb.X86_64.DBuf K W SP s D (16 * n)) :
    VG.Proof.AesOcb.X86_64.Dst K W SP s D n where
  wrap := h.wrap
  k := h.k
  scr := h.w.sub_right (Lay.wSub (by decide))
  stk := h.stk
  rd := h.rd
  wr := h.wr

theorem Dst.of_eq {K W SP : Addr} {s s' : State} {D : Addr} {n : Nat} (h : VG.Proof.AesOcb.X86_64.Dst K W SP s D n)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesOcb.X86_64.Dst K W SP s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd, wr := by rw [hwr]; exact h.wr }

/-- What the arguments `args` of a call set: `rdx` and `rcx` (to `D` and `n`),
nothing else but `rax`. -/
def ArgsOk (args : List Instr) (s : State) (D : Addr) (n : Nat) : Prop :=
  ∃ s₁, runBlock isa args s = some s₁ ∧ s₁.gpr .rdx = D ∧ s₁.gpr .rcx = BitVec.ofNat 64 n ∧
    (∀ r, r ≠ .rdx → r ≠ .rcx → r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
    s₁.wr = s.wr

theorem wp_seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

theorem sext1 : BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 := by decide

theorem sext0 : BitVec.signExtend 64 (0 : BitVec 32) = BitVec.ofNat 64 0 := by decide

/-- One block at `W + d`. -/
theorem oneBlock_ok {W : Addr} {s : State} (h15 : s.gpr .r15 = W) (d : Nat) (hd : d < 2 ^ 31) :
    VG.Proof.AesOcb.X86_64.ArgsOk (oneBlock d) s (W + BitVec.ofNat 64 d) 1 := by
  refine ⟨_, by orun [oneBlock, h15], ?_, ?_, fun r h1 h2 _ => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, VG.Proof.AesOcb.X86_64.sext1]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, h1, h2]
  all_goals rfl

theorem BPost.congr {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ s s' : State} {K D S : Addr}
    {R n : Nat} (h : VG.Proof.AesOcb.X86_64.BPost f s K D S R n s') (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hg : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r) (hsp : s.gpr .rsp = s₀.gpr .rsp) :
    VG.Proof.AesOcb.X86_64.BPost f s₀ K D S R n s' where
  rd := by rw [h.rd, hrd]
  wr := by rw [h.wr, hwr]
  saved r hr := by rw [h.saved r hr, hg r hr]
  frame := by rw [← hm, ← hsp]; exact h.frame
  out := by rw [← hm]; exact h.out

/-- A call of `b`, after `args`. -/
theorem callArgs_ok {K W SP : Addr} (L : VG.Proof.AesOcb.X86_64.Lay K W SP) {s : State} (E : VG.Proof.AesOcb.X86_64.Env K W SP s) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {args : List Instr} {D : Addr} {n : Nat} (ha : VG.Proof.AesOcb.X86_64.ArgsOk args s D n) (hD : VG.Proof.AesOcb.X86_64.Dst K W SP s D n) :
    WP isa (.block (args ++ [mvr .rdi .r14, VG.Impl.AesOcb.X86_64.ld .rsi .r15 rndO, mvr .r8 .r15, addi .r8 scrO])) s fun s₂ =>
      VG.Proof.AesOcb.X86_64.BCall s₂ K D (W + BitVec.ofNat 64 512) R n ∧ s₂.gpr .rsp = SP ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧
        s₂.wr = s.wr ∧ ∀ r ∈ calleeSaved, s₂.gpr r = s.gpr r := by
  obtain ⟨s₁, run₁, rdx₁, rcx₁, g₁, m₁, rd₁, wr₁⟩ := ha
  have r₁ : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 232) 8 := by
    rw [rd₁, wr₁]; exact E.perm.wR (by decide)
  have h15 : s₁.gpr .r15 = W := by rw [g₁ _ (by decide) (by decide) (by decide), E.r15]
  have h14 : s₁.gpr .r14 = K := by rw [g₁ _ (by decide) (by decide) (by decide), E.r14]
  have hrnd₁ : s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by rw [m₁, hrnd]
  obtain ⟨s₂, run₂, rdi₂, rsi₂, rdx₂, rcx₂, r8₂, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂,
      runBlock isa [mvr .rdi .r14, VG.Impl.AesOcb.X86_64.ld .rsi .r15 rndO, mvr .r8 .r15, addi .r8 scrO] s₁ = some s₂ ∧
      s₂.gpr .rdi = K ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = D ∧ s₂.gpr .rcx = BitVec.ofNat 64 n ∧
      s₂.gpr .r8 = W + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by orun [h14, h15, r₁, hrnd₁], ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h14]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15, hrnd₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, rdx₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, rcx₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, h1, h2, h3]
    all_goals rfl
  have hs : s₂.gpr .rsp = SP := by
    rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide), E.rsp]
  have hD₂ := hD.of_eq (s' := s₂) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have hc : VG.Proof.AesOcb.X86_64.BCall s₂ K D (W + BitVec.ofNat 64 512) R n :=
    { rdi := rdi₂, rsi := rsi₂, rdx := rdx₂, rcx := rcx₂, r8 := r8₂, rounds := hR, wrap := hD.wrap
      kd := hD.k.sub_left (Region.sub_prefix (by decide))
      ks := (L.k_w.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
      ds := hD.scr
      stkK := by rw [hs]; exact L.stk_k.sub_right (Region.sub_prefix (by decide))
      stkD := by rw [hs]; exact hD.stk
      stkS := by rw [hs]; exact L.stk_w' (by decide)
      reads := covers_append (covers_cons (VG.Proof.AesOcb.X86_64.covers_prefix (by rw [rd₂, rd₁, wr₂, wr₁]; exact E.perm.k)
          (by decide)) covers_nil)
        (covers_cons hD₂.rd (covers_cons (covers_left (by rw [wr₂, wr₁]; exact E.perm.wC (by decide))) covers_nil))
      writes := covers_cons hD₂.wr (covers_cons (by rw [wr₂, wr₁]; exact E.perm.wC (by decide)) covers_nil) }
  refine WP.of_runBlock ⟨s₂, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some, run₂], hc, hs, by rw [m₂, m₁],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun r hr => ?_⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [g₂ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    g₁ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]

theorem callBlocks_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    {K W SP : Addr} (L : VG.Proof.AesOcb.X86_64.Lay K W SP) {s : State} (E : VG.Proof.AesOcb.X86_64.Env K W SP s) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {args : List Instr} {D : Addr} {n : Nat} (ha : VG.Proof.AesOcb.X86_64.ArgsOk args s D n) (hD : VG.Proof.AesOcb.X86_64.Dst K W SP s D n) :
    WP isa (callBlocks b args) s (VG.Proof.AesOcb.X86_64.BPost f s K D (W + BitVec.ofNat 64 512) R n) := by
  exact WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.callArgs_ok L E hR hrnd ha hD) fun s₂ ⟨hc, hs, m₂, rd₂, wr₂, g₂⟩ =>
    WP.mono (VG.Proof.AesOcb.X86_64.blk_call ok nosp depth hc) fun s' h => h.congr m₂ rd₂ wr₂ g₂ (by rw [hs, E.rsp]))

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Entry`. -/
section

/-!
# AES-OCB on x86-64: the entry and the exit (`entry`, `restore`)

Untrusted: everything here is checked by Lean. `entry` reads `W` from the
stack, saves our caller's registers at `W + savO`, keeps the arguments in
`W`, the address of the tag at `W + tgO`, computes `L_$` and `L_0` from
`L_*` and zeroes the checksum (`entry_ok`); `restore` reads the registers
back (`restore_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxLstar lDollar lAt)
open VG.Proof.AesCcm.X86_64 (runBlock_append in_off add_ofNat_assoc)

/-- Our caller's registers, saved at `W + savO`. -/
def Saved (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Prop :=
  ∀ p ∈ saved, m.readW (W + BitVec.ofNat 64 p.2) 64 = g p.1

/-- The parts of `W` that `entry` writes. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 32, 352⟩

theorem readW_writeW_off {m : Mem} {W : Addr} {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (W + BitVec.ofNat 64 e) v).readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep W h hd he) (by decide)

/-- A stack argument kept in `W`. -/
theorem argSlot_ok {SP W : Addr} {s : State} {a d : Nat} {v : BitVec 64} (hsp : s.gpr .rsp = SP)
    (h15 : s.gpr .r15 = W) (hv : s.mem.readW (SP + BitVec.ofNat 64 a) 64 = v)
    (ra : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 a) 8) (wd : InRegions s.wr (W + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [VG.Impl.AesOcb.X86_64.ld .rax .rsp a, st .r15 d .rax] s = some s' ∧
      s'.mem = s.mem.writeW (W + BitVec.ofNat 64 d) v ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by orun [hsp, h15, hv, ra, wd], ?_, fun r h => ?_, ?_, ?_⟩
  · simp only [mem_setReg]
  · simp only [gpr_setReg, h, ite_false]
  all_goals rfl

/-- What `entry` leaves. -/
structure EntryPost (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (T : Addr) (s s₁ : State) :
    Prop where
  env : VG.Proof.AesOcb.X86_64.Env K W SP s₁
  slots : VG.Proof.AesOcb.X86_64.Slots W R N A D nl n tl s₁.mem
  tg : s₁.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T
  alen : s₁.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 al
  saved : VG.Proof.AesOcb.X86_64.Saved s₁.mem W s.gpr
  ld : blockAtMem s₁.mem (W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem K)
  l0 : blockAtMem s₁.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0
  ck : blockAtMem s₁.mem (W + BitVec.ofNat 64 ckO) = 0
  frame : Frame [VG.Proof.AesOcb.X86_64.entryR W] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

/-- `entry`. -/
theorem entry_ok {K W SP : Addr} (L : VG.Proof.AesOcb.X86_64.Lay K W SP) {s : State} (P : VG.Proof.AesOcb.X86_64.Perm K W s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} {T : Addr} (hsp : s.gpr .rsp = SP)
    (hargs : Covers [⟨SP + BitVec.ofNat 64 8, 40⟩] (s.rd ++ s.wr))
    (hargsW : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    ∃ s₁, runBlock isa VG.Impl.AesOcb.X86_64.entry s = some s₁ ∧ VG.Proof.AesOcb.X86_64.EntryPost K W SP R N A D nl al n tl T s s₁ := by
  have a₈ := in_off (d := 0) (n := 8) hargs (by decide) (by decide)
  have a₁₆ := in_off (d := 8) (n := 8) hargs (by decide) (by decide)
  have a₂₄ := in_off (d := 16) (n := 8) hargs (by decide) (by decide)
  have a₃₂ := in_off (d := 24) (n := 8) hargs (by decide) (by decide)
  have a₄₀ := in_off (d := 32) (n := 8) hargs (by decide) (by decide)
  rw [add_ofNat_assoc, show 8 + 0 = 8 from rfl] at a₈
  rw [add_ofNat_assoc] at a₁₆ a₂₄ a₃₂ a₄₀
  have w₁ := P.wW (show 160 + 8 ≤ 2560 by decide)
  have w₂ := P.wW (show 168 + 8 ≤ 2560 by decide)
  have w₃ := P.wW (show 176 + 8 ≤ 2560 by decide)
  have w₄ := P.wW (show 184 + 8 ≤ 2560 by decide)
  have w₅ := P.wW (show 192 + 8 ≤ 2560 by decide)
  have w₆ := P.wW (show 200 + 8 ≤ 2560 by decide)
  have w₇ := P.wW (show 232 + 8 ≤ 2560 by decide)
  have w₈ := P.wW (show 288 + 8 ≤ 2560 by decide)
  have w₉ := P.wW (show 296 + 8 ≤ 2560 by decide)
  have w₁₀ := P.wW (show 240 + 8 ≤ 2560 by decide)
  have w₁₁ := P.wW (show 248 + 8 ≤ 2560 by decide)
  -- The registers saved, `W` and `K` in `r15` and `r14`, the arguments in registers kept.
  obtain ⟨s₁, run₁, hsp₁, h15₁, h14₁, rd₁, wr₁, f₁, sv₁, s232, s288, s296, s240, s248⟩ : ∃ s₁, runBlock isa
      ([.mov .rax (.mem (at_ .rsp 40))] ++ save .rax ++
        [mvr .r15 .rax, mvr .r14 .rdi, st .r15 rndO .rsi, st .r15 nO .rdx, st .r15 nlO .rcx,
          st .r15 aadO .r8, st .r15 alenO .r9]) s = some s₁ ∧
      s₁.gpr .rsp = SP ∧ s₁.gpr .r15 = W ∧ s₁.gpr .r14 = K ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 160, 144⟩] s.mem s₁.mem ∧ VG.Proof.AesOcb.X86_64.Saved s₁.mem W s.gpr ∧
      s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R ∧ s₁.mem.readW (W + BitVec.ofNat 64 288) 64 = N ∧
      s₁.mem.readW (W + BitVec.ofNat 64 296) 64 = BitVec.ofNat 64 nl ∧
      s₁.mem.readW (W + BitVec.ofNat 64 240) 64 = A ∧
      s₁.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 al := by
    have cE : ∀ d, 160 ≤ d → d + 8 ≤ 304 → (⟨W + BitVec.ofNat 64 160, 144⟩ : Region).Contains
        (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains W h₁ (by omega) (by decide)
    refine ⟨_, by orun [save, saved, List.map_cons, List.map_nil, hW, hsp, a₄₀, w₁, w₂, w₃, w₄, w₅, w₆, w₇,
      w₈, w₉, w₁₀, w₁₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hsp]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hdi]
    · rfl
    · rfl
    · simp only [mem_setReg]
      repeat (first | exact Frame.refl _ _ |
        refine Frame.writeW ?_ (List.mem_singleton_self _) _ (cE _ (by decide) (by decide)))
    · intro p hp
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (disch := decide) only [savO, Nat.reduceAdd, mem_setReg, VG.Proof.AesOcb.X86_64.readW_writeW_off, Mem.readW_writeW_self64]
    all_goals simp (disch := decide) only [mem_setReg, VG.Proof.AesOcb.X86_64.readW_writeW_off, Mem.readW_writeW_self64, gpr_setReg,
      ite_true, ite_false, reduceCtorEq, hsi, hdx, hcx, hr8, hr9]
  -- The arguments on the stack.
  have dA : ∀ {a d k : Nat}, 8 ≤ a → a + 8 ≤ 48 → d + k ≤ 2560 →
      (⟨SP + BitVec.ofNat 64 a, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ := fun {a d k} h₁ h₂ h₃ => by
    have e : SP + BitVec.ofNat 64 a = SP + BitVec.ofNat 64 8 + BitVec.ofNat 64 (a - 8) := by
      rw [add_ofNat_assoc, show 8 + (a - 8) = a by omega]
    rw [e]; exact (hargsW.sub_left (Offset.sub_base _ (by omega))).sub_right (Lay.wSub h₃)
  have kA : ∀ {a : Nat}, 8 ≤ a → a + 8 ≤ 48 →
      s₁.mem.readW (SP + BitVec.ofNat 64 a) 64 = s.mem.readW (SP + BitVec.ofNat 64 a) 64 := fun {a} h₁ h₂ =>
    f₁.readW (r := ⟨SP + BitVec.ofNat 64 a, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dA h₁ h₂ (by decide)) (by decide)
  have sW : ∀ {a d : Nat}, 8 ≤ a → a + 8 ≤ 48 → d + 8 ≤ 2560 → Mem.Sep (SP + BitVec.ofNat 64 a) (64 / 8)
      (W + BitVec.ofNat 64 d) (64 / 8) := fun h₁ h₂ h₃ =>
    (dA h₁ h₂ h₃).sep (Region.contains_self _ _) (Region.contains_self _ _)
  obtain ⟨s₂, run₂, m₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86_64.argSlot_ok (s := s₁) (a := 8) (d := dataO) hsp₁ h15₁
    (by rw [kA (by decide) (by decide), hD]) (by rw [rd₁, wr₁]; exact a₈) (by rw [wr₁]; exact P.wW (by decide))
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := VG.Proof.AesOcb.X86_64.argSlot_ok (s := s₂) (a := 16) (d := lenO)
    (by rw [g₂ _ (by decide), hsp₁]) (by rw [g₂ _ (by decide), h15₁])
    (by rw [m₂, Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide),
      kA (by decide) (by decide), hn])
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact a₁₆) (by rw [wr₂, wr₁]; exact P.wW (by decide))
  obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ := VG.Proof.AesOcb.X86_64.argSlot_ok (s := s₃) (a := 32) (d := tlO)
    (by rw [g₃ _ (by decide), g₂ _ (by decide), hsp₁]) (by rw [g₃ _ (by decide), g₂ _ (by decide), h15₁])
    (by rw [m₃, Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide), m₂,
      Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide), kA (by decide) (by decide), htl])
    (by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact a₃₂) (by rw [wr₃, wr₂, wr₁]; exact P.wW (by decide))
  obtain ⟨s₄', run₄', m₄', g₄', rd₄', wr₄'⟩ := VG.Proof.AesOcb.X86_64.argSlot_ok (s := s₄) (a := 24) (d := tgO)
    (by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), hsp₁])
    (by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), h15₁])
    (by rw [m₄, Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide), m₃,
      Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide), m₂,
      Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide), kA (by decide) (by decide), hT])
    (by rw [rd₄, wr₄, rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact a₂₄) (by rw [wr₄, wr₃, wr₂, wr₁]; exact P.wW (by decide))
  have E₄ : VG.Proof.AesOcb.X86_64.Env K W SP s₄' := ⟨by rw [g₄' _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), h14₁],
    by rw [g₄' _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), h15₁],
    by rw [g₄' _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), hsp₁],
    P.of_eq (by rw [rd₄', rd₄, rd₃, rd₂, rd₁]) (by rw [wr₄', wr₄, wr₃, wr₂, wr₁])⟩
  -- What the writes of the arguments keep.
  have k₄ : ∀ {d : Nat}, (d + 8 ≤ 208 ∨ 232 ≤ d ∧ d + 8 ≤ 304) → d + 8 ≤ 2560 →
      s₄'.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ => by
    rw [m₄', VG.Proof.AesOcb.X86_64.readW_writeW_off _ (by simp only [tgO]; omega) (by omega) (by decide),
      m₄, VG.Proof.AesOcb.X86_64.readW_writeW_off _ (by simp only [tlO]; omega) (by omega) (by decide), m₃,
      VG.Proof.AesOcb.X86_64.readW_writeW_off _ (by simp only [lenO]; omega) (by omega) (by decide), m₂,
      VG.Proof.AesOcb.X86_64.readW_writeW_off _ (by simp only [dataO]; omega) (by omega) (by decide)]
  have fr₄ : Frame [⟨W + BitVec.ofNat 64 208, 104⟩] s₁.mem s₄'.mem := by
    rw [m₄', m₄, m₃, m₂]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains W (d := 208) (n := 8) (e := 208)
      (k := 104) (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains W (d := 216) (n := 8) (e := 208) (k := 104) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains W (d := 224) (n := 8) (e := 208) (k := 104) (by decide) (by decide)
        (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains W (d := 304) (n := 8) (e := 208) (k := 104) (by decide) (by decide)
        (by decide))
  have f₁₄ : Frame [⟨W + BitVec.ofNat 64 160, 144⟩, ⟨W + BitVec.ofNat 64 208, 104⟩] s.mem s₄'.mem :=
    (f₁.mono (by simp)).trans (fr₄.mono (by simp))
  -- `L_$`, `L_0` and the checksum.
  have l₄ : blockAtMem s₄'.mem (K + BitVec.ofNat 64 240) = ctxLstar s.mem K := by
    rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame f₁₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact (L.k_w.sub_left (Lay.kSub (by decide))).sub_right (Lay.wSub (by decide)))]
    rfl
  obtain ⟨s₅, run₅, B₅⟩ := VG.Proof.AesOcb.X86_64.dbl_ok (s := s₄') (b := .r14) (a := 240) (d := ldO) E₄.r15 E₄.r14 (by decide)
    (E₄.perm.kR (by decide)) (E₄.perm.kR (by decide)) (E₄.perm.wW (by decide)) (E₄.perm.wW (by decide))
  have nE : ∀ r ∈ [Reg.r14, .r15, .rsp], r ∉ [Reg.rax, .rdx, .rcx, .r8] := by decide
  have E₅ : VG.Proof.AesOcb.X86_64.Env K W SP s₅ := E₄.keep (fun r hr => B₅.gpr r (nE r hr)) B₅.rd B₅.wr
  obtain ⟨s₆, run₆, B₆⟩ := VG.Proof.AesOcb.X86_64.dbl_ok (s := s₅) (b := .r15) (a := ldO) (d := l0O) E₅.r15 E₅.r15 (by decide)
    (E₅.perm.wR (by decide)) (E₅.perm.wR (by decide)) (E₅.perm.wW (by decide)) (E₅.perm.wW (by decide))
  have E₆ : VG.Proof.AesOcb.X86_64.Env K W SP s₆ := E₅.keep (fun r hr => B₆.gpr r (nE r hr)) B₆.rd B₆.wr
  obtain ⟨s₇, run₇, B₇⟩ := VG.Proof.AesOcb.X86_64.zero16_ok (s := s₆) (d := ckO) E₆.r15 (E₆.perm.wW (by decide)) (E₆.perm.wW (by decide))
  have E₇ : VG.Proof.AesOcb.X86_64.Env K W SP s₇ := E₆.keep (fun r hr => B₇.gpr r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide))
    B₇.rd B₇.wr
  have fr₇ : Frame [⟨W + BitVec.ofNat 64 32, 64⟩] s₄'.mem s₇.mem :=
    ((B₅.frame.sub fun r hr => ?_).trans (B₆.frame.sub fun r hr => ?_)).trans (B₇.frame.sub fun r hr => ?_)
  rotate_left
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  have k₇ : ∀ {d : Nat}, 96 ≤ d → d + 8 ≤ 2560 →
      s₇.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄'.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ =>
    fr₇.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega)) h₂ (by decide)) (by decide)
  have k : ∀ {d : Nat}, 232 ≤ d → d + 8 ≤ 304 →
      s₇.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ => by
    rw [k₇ (by omega) (by omega), k₄ (.inr ⟨h₁, h₂⟩) (by omega)]
  have kd : ∀ {d : Nat}, 208 ≤ d → d + 8 ≤ 2560 →
      s₇.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄'.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ =>
    k₇ (by omega) (by omega)
  refine ⟨s₇, ?_, ⟨E₇, ⟨?_, ?_, ?_, by rw [k (by decide) (by decide), s232], by rw [k (by decide) (by decide), s240],
    by rw [k (by decide) (by decide), s288], by rw [k (by decide) (by decide), s296]⟩, ?_,
    by rw [show alenO = 248 from rfl, k (by decide) (by decide), s248], fun p hp => ?_, ?_, ?_, B₇.val, ?_,
    by rw [B₇.rd, B₆.rd, B₅.rd, rd₄', rd₄, rd₃, rd₂, rd₁], by rw [B₇.wr, B₆.wr, B₅.wr, wr₄', wr₄, wr₃, wr₂, wr₁]⟩⟩
  · rw [show VG.Impl.AesOcb.X86_64.entry = ([.mov .rax (.mem (at_ .rsp 40))] ++ save .rax ++
        [mvr .r15 .rax, mvr .r14 .rdi, st .r15 rndO .rsi, st .r15 nO .rdx, st .r15 nlO .rcx,
          st .r15 aadO .r8, st .r15 alenO .r9]) ++ [VG.Impl.AesOcb.X86_64.ld .rax .rsp 8, st .r15 dataO .rax] ++
        [VG.Impl.AesOcb.X86_64.ld .rax .rsp 16, st .r15 lenO .rax] ++ [VG.Impl.AesOcb.X86_64.ld .rax .rsp 32, st .r15 tlO .rax] ++
        [VG.Impl.AesOcb.X86_64.ld .rax .rsp 24, st .r15 tgO .rax] ++ dbl .r14 240 ldO ++
        dbl .r15 ldO l0O ++ zero16 ckO by
      simp only [VG.Impl.AesOcb.X86_64.entry, lsetup, List.append_assoc, List.cons_append, List.nil_append],
      VG.Proof.AesCcm.X86_64.runBlock_append, VG.Proof.AesCcm.X86_64.runBlock_append, VG.Proof.AesCcm.X86_64.runBlock_append, VG.Proof.AesCcm.X86_64.runBlock_append, VG.Proof.AesCcm.X86_64.runBlock_append, VG.Proof.AesCcm.X86_64.runBlock_append,
      VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, run₄,
      Option.bind_some, run₄', Option.bind_some, run₅, Option.bind_some, run₆, Option.bind_some, run₇]
  · rw [kd (by decide) (by decide), m₄', VG.Proof.AesOcb.X86_64.readW_writeW_off _ (by decide) (by decide) (by decide), m₄,
      VG.Proof.AesOcb.X86_64.readW_writeW_off _ (by decide) (by decide) (by decide), m₃,
      VG.Proof.AesOcb.X86_64.readW_writeW_off _ (by decide) (by decide) (by decide), m₂]
    exact Mem.readW_writeW_self64 ..
  · rw [kd (by decide) (by decide), m₄', VG.Proof.AesOcb.X86_64.readW_writeW_off _ (by decide) (by decide) (by decide), m₄,
      VG.Proof.AesOcb.X86_64.readW_writeW_off _ (by decide) (by decide) (by decide), m₃]
    exact Mem.readW_writeW_self64 ..
  · rw [kd (by decide) (by decide), m₄', VG.Proof.AesOcb.X86_64.readW_writeW_off _ (by decide) (by decide) (by decide), m₄]
    exact Mem.readW_writeW_self64 ..
  · rw [kd (by decide) (by decide), m₄']
    exact Mem.readW_writeW_self64 ..
  · have hp' := hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rw [← sv₁ p hp]
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k₇ (by decide) (by decide), k₄ (.inl (by decide)) (by decide)]
  · rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame B₇.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
      VG.Proof.AesOcb.X86_64.blockAtMem_frame B₆.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
      B₅.val, l₄]
    rfl
  · rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame B₇.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
      B₆.val, B₅.val, l₄]
    rfl
  · refine (((f₁₄.mono (rs' := [⟨W + BitVec.ofNat 64 160, 144⟩, ⟨W + BitVec.ofNat 64 208, 104⟩,
      ⟨W + BitVec.ofNat 64 32, 64⟩]) (by simp)).trans (fr₇.mono (by simp)))).sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩

/-- `restore`: our caller's registers back. -/
theorem restore_ok {K W SP : Addr} {s : State} (E : VG.Proof.AesOcb.X86_64.Env K W SP s) {g : Reg → BitVec 64} (hs : VG.Proof.AesOcb.X86_64.Saved s.mem W g) :
    ∃ s', runBlock isa VG.Impl.AesOcb.X86_64.restore s = some s' ∧ (∀ p ∈ saved, s'.gpr p.1 = g p.1) ∧ s'.mem = s.mem ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rax = s.gpr .rax := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 160 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 168 + 8 ≤ 2560 by decide)
  have r₃ := E.perm.wR (show 176 + 8 ≤ 2560 by decide)
  have r₄ := E.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have r₅ := E.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have r₆ := E.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have v₁ := hs (.rbx, 160) (by decide)
  have v₂ := hs (.rbp, 168) (by decide)
  have v₃ := hs (.r12, 176) (by decide)
  have v₄ := hs (.r13, 184) (by decide)
  have v₅ := hs (.r14, 192) (by decide)
  have v₆ := hs (.r15, 200) (by decide)
  refine ⟨_, by orun [VG.Impl.AesOcb.X86_64.restore, saved, List.map_cons, List.map_nil, h15, r₁, r₂, r₃, r₄, r₅, r₆], ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, v₁, v₂, v₃, v₄, v₅, v₆]
  · rfl
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]

end VG.Proof.AesOcb.X86_64

end
