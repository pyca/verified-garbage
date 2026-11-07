module

public import VerifiedGarbage.Impl.AesGcm.X86.OpenTo
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.X86.Gather.Copy
public import VerifiedGarbage.Proof.AesGcm.X86.Gather.Loop
public import VerifiedGarbage.Proof.AesGcm.X86.Callee
public import VerifiedGarbage.Proof.Zeroize.Common
import VerifiedGarbage.Proof.AesGcm.X86.Gather.Callee
import VerifiedGarbage.Proof.AesGcm.X86.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.X86.Contract
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.AesGcm.X86.Env
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.VariantProof
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM decryption out of place, by a copy, x86: the function

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_aes_gcm_open_to` is written against (`toK`), which the shared one implies
(`OpenTo/Verified.lean`), and its proof (`openTo_wp`). It calls an instance
of `vg_aes_gcm_open` as an artifact, with its working space in a frame of
its own, so what the proof needs of it is its shared contract
(`Proof.AesGcm.openRoundsContract`, with 2636 bytes of stack, `OpenFn`).

With `B` the base of the 2688 bytes of stack below the stack pointer
(`esp = B + 2688`), the function allocates its frame of 48 bytes at
`P = B + 2640` (`WP.alloc`), keeps our caller's `esi` and `edi` in it and
lays out the call's ten arguments (`entered_wp`). It copies the `len` bytes
at `src` to `dst` (`copied_wp`, by `Gather.copySlice_wp`, from the
descriptor that our arguments `src` and `len` form), calls
`vg_aes_gcm_open` on `dst` in place (`called_wp`), which writes only `dst`,
its arguments and the stack below them, and zeroes `dst` if it returned 0
(`after_wp`, `wipe_wp`); then it restores the registers (`ret_wp`). Every
write is to `dst` or to the stack below `esp`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86.OpenTo

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.Impl.AesGcm.X86.OpenTo VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH openResult)
open VG.Impl.AesGcm.X86.SealGather (sp copySlice)
open VG.Proof.AesGcm.X86.Gather (SlicePre Keeps copyRegs copySlice_wp sw32 allocated allocated_esp allocated_gpr
  allocated_mem allocated_rd allocated_wr freed WP.alloc add_ofNat_sub_ofNat sub_toNat32 w64_sub contains_off covers_of_mem')

/-! ## The arguments and the contract -/

section
variable (s : State)

/-- The arguments `(ctx, rounds, nonce, nonce_len, aad, aad_len, src, len,
dst, dst_len, tag, tag_len)`. -/
abbrev K : BitVec 32 := arg s 0
abbrev Nn : BitVec 32 := arg s 2
abbrev NL : Nat := (arg s 3).toNat
abbrev Ad : BitVec 32 := arg s 4
abbrev AL : Nat := (arg s 5).toNat
abbrev Src : BitVec 32 := arg s 6
abbrev L : Nat := (arg s 7).toNat
abbrev Dst : BitVec 32 := arg s 8
abbrev Tg : BitVec 32 := arg s 10
abbrev TL : Nat := (arg s 11).toNat

/-- The regions: the key context, the nonce, the additional data, the
ciphertext, the output, the tag, the arguments, the return address and the
stack below it. -/
abbrev kR : Region := ⟨w64 (K s), 256⟩
abbrev nR : Region := ⟨w64 (Nn s), NL s⟩
abbrev aR : Region := ⟨w64 (Ad s), AL s⟩
abbrev sR : Region := ⟨w64 (Src s), L s⟩
abbrev dR : Region := ⟨w64 (Dst s), L s⟩
abbrev tR : Region := ⟨w64 (Tg s), TL s⟩
abbrev argR : Region := ⟨argAddr s 0, 48⟩
abbrev retR : Region := ⟨w64 (s.gpr .esp), 4⟩
abbrev stkR : Region := ⟨w64 (s.gpr .esp) - BitVec.ofNat 64 2688, 2688⟩

/-- `vg_aes_gcm_open`'s result on the ciphertext at `src`. -/
abbrev res : Option (List Byte) :=
  openResult (ctxCiph s.mem (w64 (K s)) (arg s 1).toNat) (ctxH s.mem (w64 (K s))) (TL s)
    (bytesAt s.mem (w64 (Nn s)) (NL s)) (bytesAt s.mem (w64 (Src s)) (L s)) (bytesAt s.mem (w64 (Ad s)) (AL s))
    (bytesAt s.mem (w64 (Tg s)) (TL s))

end

/-- What the proof of `vg_aes_gcm_open_to` needs: the layout of its shared
contract, with 2688 bytes of stack, `dst_len` its `len`. -/
structure ToPre (s : State) : Prop where
  w₁ : 2688 ≤ (s.gpr .esp).toNat
  w₂ : (s.gpr .esp).toNat + 4 + 48 ≤ 2 ^ 32
  rd : s.rd = [kR s, nR s, aR s, sR s, tR s]
  wr : s.wr = [dR s, argR s]
  kd : (kR s).Disjoint (dR s)
  nd : (nR s).Disjoint (dR s)
  ad : (aR s).Disjoint (dR s)
  sd : (sR s).Disjoint (dR s)
  dt : (dR s).Disjoint (tR s)
  da : (dR s).Disjoint (argR s)
  ed : (retR s).Disjoint (dR s)
  bk : (stkR s).Disjoint (kR s)
  bn : (stkR s).Disjoint (nR s)
  ba : (stkR s).Disjoint (aR s)
  bs : (stkR s).Disjoint (sR s)
  bd : (stkR s).Disjoint (dR s)
  bt : (stkR s).Disjoint (tR s)
  ok : (K s).toNat + 256 ≤ 2 ^ 32
  on : (Nn s).toNat + NL s ≤ 2 ^ 32
  oa : (Ad s).toNat + AL s ≤ 2 ^ 32
  os : (Src s).toNat + L s ≤ 2 ^ 32
  od : (Dst s).toNat + L s ≤ 2 ^ 32
  ot : (Tg s).toNat + TL s ≤ 2 ^ 32
  hR : (arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14

/-- `openToRoundsPost`, for the rounds of `ToPre`, with the result in `eax`. -/
def toPost (s s' : State) : Prop :=
  match res s with
  | some pt => s'.gpr .eax = 1 ∧ bytesAt s'.mem (w64 (Dst s)) (L s) = pt
  | none => s'.gpr .eax = 0 ∧ bytesAt s'.mem (w64 (Dst s)) (L s) = List.replicate (L s) 0

/-- What `vg_aes_gcm_open_to` may leak: whether it succeeds. -/
def toLeak (s : State) : List Nat :=
  if ¬((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) then []
  else [if (res s).isSome = true then 1 else 0]

/-- What two runs agree on: the stack pointer, the arguments and the leak. -/
def toPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .esp = s₂.gpr .esp ∧ toLeak s₁ = toLeak s₂ ∧ ∀ i < 12, arg s₁ i = arg s₂ i

/-- `vg_aes_gcm_open_to`. -/
def toK : Contract isa where
  pre := ToPre
  post := toPost
  pub := toPub

/-! ## The function called -/

/-- An instance of `vg_aes_gcm_open`, by its shared contract, which never
writes `esp` and whose calls and frames use at most the 2636 bytes below the
stack pointer that the contract reserves. -/
structure OpenFn where
  name : String
  code : Prog isa
  verified : Verified X86.target code (Proof.AesGcm.openRoundsContract X86.abi 2636)
  noSp : NoSp code
  depth : stackUse code ≤ 2636

/-- What a call of `vg_aes_gcm_open(ctx, rounds, nonce, nonce_len, aad,
aad_len, data, len, tag, tag_len)` needs. -/
def callPre (s : State) : Prop :=
  let ctx : Region := ⟨w64 (arg s 0), 256⟩
  let nonce : Region := ⟨w64 (arg s 2), (arg s 3).toNat⟩
  let aad : Region := ⟨w64 (arg s 4), (arg s 5).toNat⟩
  let data : Region := ⟨w64 (arg s 6), (arg s 7).toNat⟩
  let tag : Region := ⟨w64 (arg s 8), (arg s 9).toNat⟩
  let args : Region := ⟨argAddr s 0, 40⟩
  let ret : Region := ⟨w64 (s.gpr .esp), 4⟩
  let stk : Region := ⟨w64 (s.gpr .esp) - BitVec.ofNat 64 2636, 2636⟩
  2636 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + 40 ≤ 2 ^ 32 ∧
    s.rd = [ctx, nonce, aad, tag] ∧ s.wr = [data, args] ∧
    ctx.Disjoint data ∧ ctx.Disjoint args ∧ nonce.Disjoint data ∧ nonce.Disjoint args ∧ aad.Disjoint data ∧
    aad.Disjoint args ∧ data.Disjoint tag ∧ data.Disjoint args ∧ tag.Disjoint args ∧
    ret.Disjoint ctx ∧ ret.Disjoint nonce ∧ ret.Disjoint aad ∧ ret.Disjoint data ∧ ret.Disjoint tag ∧
    ret.Disjoint args ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint args ∧
    (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32 ∧
    (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32 ∧
    ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)

/-- The shared contract's precondition, from the layout the call gives. -/
theorem openSpec_pre {s : State} (h : callPre s) : (Proof.AesGcm.openRoundsContract X86.abi 2636).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄ a₂₅ a₂₆ a₂₇
    a₂₈ a₂₉ a₃₀
  have a₃₁ := h
  clear h
  sig_pre [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, X86.abi, argVal, ↓reduceIte,
    Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32,
    toNat_w64]
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁⟩

/-- `vg_aes_gcm_open`'s result on the arguments of a call. -/
abbrev callRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (w64 (arg s 0)) (arg s 1).toNat) (ctxH s.mem (w64 (arg s 0))) (arg s 9).toNat
    (bytesAt s.mem (w64 (arg s 2)) (arg s 3).toNat) (bytesAt s.mem (w64 (arg s 6)) (arg s 7).toNat)
    (bytesAt s.mem (w64 (arg s 4)) (arg s 5).toNat) (bytesAt s.mem (w64 (arg s 8)) (arg s 9).toNat)

/-- Its postcondition, for rounds of 10, 12 or 14. -/
theorem openSpec_post {s s' : State} (h : (Proof.AesGcm.openRoundsContract X86.abi 2636).post s s')
    (hR : (arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) :
    match callRes s with
    | some pt => s'.gpr .eax = 1 ∧ bytesAt s'.mem (w64 (arg s 6)) (arg s 7).toNat = pt
    | none => s'.gpr .eax = 0 := by
  sig_post [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Proof.AesGcm.openRoundsPost, X86.abi, argVal,
    ↓reduceIte, Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceMul, sw32, toNat_w64] at h
  have h' := h hR
  split
  · rename_i pt heq
    dsimp only [callRes, w64] at heq
    rw [heq] at h'
    exact ⟨(ret32_eq _ _).symm.trans h'.1, h'.2⟩
  · rename_i heq
    dsimp only [callRes, w64] at heq
    rw [heq] at h'
    exact (ret32_eq _ _).symm.trans h'.1

/-- The public data of a call: whether it succeeds. -/
def callLeak (s : State) : List Nat :=
  if ¬((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) then []
  else [if (callRes s).isSome = true then 1 else 0]

/-- Its public data, from the arguments and the leak. -/
theorem openSpec_pub {s₁ s₂ : State} (h : s₁.gpr .esp = s₂.gpr .esp ∧ callLeak s₁ = callLeak s₂ ∧
    ∀ i < 10, arg s₁ i = arg s₂ i) : (Proof.AesGcm.openRoundsContract X86.abi 2636).pub s₁ s₂ := by
  obtain ⟨a₁, l, a₂⟩ := h
  sig_pub [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openLeak, X86.abi, argVal, ↓reduceIte,
    Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32,
    toNat_w64]
  exact ⟨a₁, l, a₂ 0 (by decide), a₂ 1 (by decide), a₂ 2 (by decide), a₂ 3 (by decide), a₂ 4 (by decide),
    a₂ 5 (by decide), a₂ 6 (by decide), a₂ 7 (by decide), a₂ 8 (by decide), a₂ 9 (by decide)⟩

/-! ## Words of the frame -/

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 100 ≤ 2 ^ 32)
include hP

theorem aP {d : Nat} (hd : d < 100) : w64 (P + BitVec.ofNat 32 d) = w64 P + BitVec.ofNat 64 d :=
  w64_add (by omega_arith)

/-- A word of the frame (or above it) after a write of another. -/
theorem rdw {d e : Nat} (v : BitVec 32) (hd : d + 4 ≤ 100) (he : e + 4 ≤ 100) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (w64 (P + BitVec.ofNat 32 e)) v).readW (w64 (P + BitVec.ofNat 32 d)) 32 =
      m.readW (w64 (P + BitVec.ofNat 32 d)) 32 := by
  rw [aP hP (by omega_arith), aP hP (by omega_arith)]
  exact Mem.readW_writeW_sep (Offset.sep _ h (by omega_arith) (by omega_arith)) (by decide)

theorem rdw0 {e : Nat} (v : BitVec 32) (he : e + 4 ≤ 100) (h : 4 ≤ e) :
    (m.writeW (w64 (P + BitVec.ofNat 32 e)) v).readW (w64 P) 32 = m.readW (w64 P) 32 := by
  have := rdw hP (m := m) (d := 0) v (by decide) he (.inl h)
  rwa [add_zero32] at this

theorem rd0w {d : Nat} (v : BitVec 32) (hd : d + 4 ≤ 100) (h : 4 ≤ d) :
    (m.writeW (w64 P) v).readW (w64 (P + BitVec.ofNat 32 d)) 32 = m.readW (w64 (P + BitVec.ofNat 32 d)) 32 := by
  have := rdw hP (m := m) (d := d) (e := 0) v hd (by decide) (.inr h)
  rwa [add_zero32] at this

omit hP in
theorem rds (v : BitVec 32) (a : Addr) : (m.writeW a v).readW a 32 = v :=
  Mem.readW_writeW_self m a 4 v (by decide)

end

/-- The memory after the entry, at the frame `P`: our caller's `esi` and
`edi` at `P + 40` and `P + 44`, and our arguments `ctx`, `rounds`, `nonce`,
`nonce_len`, `aad`, `aad_len`, `dst`, `len`, `tag` and `tag_len` (at
`P + 52` … `P + 72`, `P + 84`, `P + 80`, `P + 92` and `P + 96`) at `P` …
`P + 36`. -/
def eMem (m : Mem) (P : BitVec 32) (esi edi : BitVec 32) : Mem :=
  let w (m : Mem) (d : Nat) (v : BitVec 32) := m.writeW (w64 (P + BitVec.ofNat 32 d)) v
  let r (d : Nat) := m.readW (w64 (P + BitVec.ofNat 32 d)) 32
  w (w (w (w (w (w (w (w (w ((w (w m 40 esi) 44 edi).writeW (w64 P) (r 52)) 4 (r 56)) 8 (r 60)) 12 (r 64))
    16 (r 68)) 20 (r 72)) 24 (r 84)) 28 (r 80)) 32 (r 92)) 36 (r 96)

theorem entry_ok (a : State) (hP : (a.gpr .esp).toNat + 100 ≤ 2 ^ 32)
    (hw : ∀ d, d + 4 ≤ 48 → InRegions a.wr (w64 (a.gpr .esp + BitVec.ofNat 32 d)) 4)
    (hr : ∀ d, 52 ≤ d → d + 4 ≤ 100 → InRegions (a.rd ++ a.wr) (w64 (a.gpr .esp + BitVec.ofNat 32 d)) 4) :
    WP isa (.block entry) a fun e =>
      e.mem = eMem a.mem (a.gpr .esp) (a.gpr .esi) (a.gpr .edi) ∧
      e.gpr .esi = a.gpr .esp + BitVec.ofNat 32 76 ∧
      e.gpr .edx = a.mem.readW (w64 (a.gpr .esp + BitVec.ofNat 32 84)) 32 ∧
      (∀ r, r ≠ .eax → r ≠ .edx → r ≠ .esi → e.gpr r = a.gpr r) ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  have hw0 : InRegions a.wr (w64 (a.gpr .esp)) 4 := by simpa only [add_zero32] using hw 0 (by decide)
  refine WP.of_runBlock ⟨_, by
    xrun [OpenTo.entry, sp, hw 40 (by decide), hw 44 (by decide), hw0, hw 4 (by decide),
      hw 8 (by decide), hw 12 (by decide), hw 16 (by decide), hw 20 (by decide), hw 24 (by decide),
      hw 28 (by decide), hw 32 (by decide), hw 36 (by decide), hr 52 (by decide) (by decide),
      hr 56 (by decide) (by decide), hr 60 (by decide) (by decide), hr 64 (by decide) (by decide),
      hr 68 (by decide) (by decide), hr 72 (by decide) (by decide), hr 80 (by decide) (by decide),
      hr 84 (by decide) (by decide), hr 92 (by decide) (by decide), hr 96 (by decide) (by decide), add_zero32,
      rdw hP, rdw0 hP, rd0w hP], ?_⟩
  refine ⟨?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_⟩
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rfl
  · regs []
  · regs []
  · simp [gpr_setMem, gpr_setReg, gpr_arithFlags, h₁, h₂, h₃]
  · simp only [rd_setMem, rd_setReg, rd_arithFlags]
  · simp only [wr_setMem, wr_setReg, wr_arithFlags]

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 100 ≤ 2 ^ 32) (esi edi : BitVec 32)
include hP

/-- The entry writes only the frame. -/
theorem eMem_frame : Frame [⟨w64 P, 48⟩] m (eMem m P esi edi) := by
  have c (d : Nat) (hd : d + 4 ≤ 48) : (⟨w64 P, 48⟩ : Region).Contains (w64 (P + BitVec.ofNat 32 d)) 4 := by
    rw [aP hP (by omega_arith)]; exact Offset.contains_base _ hd (by omega_arith)
  have c0 : (⟨w64 P, 48⟩ : Region).Contains (w64 P) 4 := by simp [Region.Contains]
  have hm := List.mem_singleton_self (⟨w64 P, 48⟩ : Region)
  unfold eMem; dsimp only
  refine Frame.writeW ?_ hm _ (c 36 (by decide)); refine Frame.writeW ?_ hm _ (c 32 (by decide))
  refine Frame.writeW ?_ hm _ (c 28 (by decide)); refine Frame.writeW ?_ hm _ (c 24 (by decide))
  refine Frame.writeW ?_ hm _ (c 20 (by decide)); refine Frame.writeW ?_ hm _ (c 16 (by decide))
  refine Frame.writeW ?_ hm _ (c 12 (by decide)); refine Frame.writeW ?_ hm _ (c 8 (by decide))
  refine Frame.writeW ?_ hm _ (c 4 (by decide)); refine Frame.writeW ?_ hm _ c0
  refine Frame.writeW ?_ hm _ (c 44 (by decide)); refine Frame.writeW ?_ hm _ (c 40 (by decide))
  exact Frame.refl _ _

/-- The words of the frame after the entry. -/
theorem eMem_words :
    let e := eMem m P esi edi
    let r (m : Mem) (d : Nat) := m.readW (w64 (P + BitVec.ofNat 32 d)) 32
    e.readW (w64 P) 32 = r m 52 ∧ r e 4 = r m 56 ∧ r e 8 = r m 60 ∧ r e 12 = r m 64 ∧ r e 16 = r m 68 ∧
      r e 20 = r m 72 ∧ r e 24 = r m 84 ∧ r e 28 = r m 80 ∧ r e 32 = r m 92 ∧ r e 36 = r m 96 ∧ r e 40 = esi ∧
      r e 44 = edi := by
  simp (disch := first | decide | omega_arith) only [eMem, rdw hP, rdw0 hP, rd0w hP, rds]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial⟩

end

/-! ## The layout -/

section
variable (s : State)

/-- The frame, the base of the 2688 bytes of stack below the stack pointer,
and the frame as a region. -/
abbrev Pf : BitVec 32 := s.gpr .esp - BitVec.ofNat 32 48
abbrev Bs : Addr := w64 (s.gpr .esp) - BitVec.ofNat 64 2688
abbrev FR : Region := ⟨w64 (Pf s), 48⟩

/-- The memory after the entry. -/
abbrev eM : Mem := eMem s.mem (Pf s) (s.gpr .esi) (s.gpr .edi)

/-- The memory once the ciphertext is copied to `dst`. -/
abbrev cM : Mem := writeBytes (eM s) (w64 (Dst s)) (bytesAt s.mem (w64 (Src s)) (L s))

end

/-- What `ToPre` gives, with the frame at `Pf s` and the stack below the
stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : ToPre s
  hP : (Pf s).toNat + 100 ≤ 2 ^ 32
  hPn : (Pf s).toNat = (s.gpr .esp).toNat - 48
  hBn : (Bs s).toNat + 2740 ≤ 2 ^ 32
  hA0 : w64 (Pf s) = Bs s + BitVec.ofNat 64 2640
  hE : w64 (s.gpr .esp) = Bs s + BitVec.ofNat 64 2688
  sa : ∀ i, i < 12 → s.mem.readW (w64 (Pf s + BitVec.ofNat 32 (52 + 4 * i))) 32 = arg s i

theorem lay {s : State} (hs : ToPre s) : Lay s := by
  have w₁ := hs.w₁
  have w₂ := hs.w₂
  have hPn : (Pf s).toNat = (s.gpr .esp).toNat - 48 := sub_toNat32 (by omega_arith)
  have hB : Bs s = w64 (s.gpr .esp - BitVec.ofNat 32 2688) := (w64_sub (by omega_arith)).symm
  have hBn : (Bs s).toNat = (s.gpr .esp).toNat - 2688 := by rw [hB, toNat_w64, sub_toNat32 (by omega_arith)]
  have hE : w64 (s.gpr .esp) = Bs s + BitVec.ofNat 64 2688 := (BitVec.sub_add_cancel _ _).symm
  have hA0 : w64 (Pf s) = Bs s + BitVec.ofNat 64 2640 := by
    rw [w64_sub (by omega_arith), hE, add_ofNat_sub_ofNat _ (by decide)]
  refine ⟨hs, by omega_arith, hPn, by omega_arith, hA0, hE, fun i hi => ?_⟩
  show _ = s.mem.readW (w64 (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i))) 32
  rw [show 52 + 4 * i = 48 + (4 + 4 * i) by omega_arith, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
    BitVec.sub_add_cancel]

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 2688) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 2688⟩ :=
  Offset.sub_base _ h'

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem hA {d : Nat} (hd : d < 100) : w64 (Pf s + BitVec.ofNat 32 d) = Bs s + BitVec.ofNat 64 (2640 + d) := by
  rw [aP h.hP hd, h.hA0, Offset.add_ofNat_add_ofNat]

theorem fr_sub : (FR s).Sub ⟨Bs s, 2688⟩ := by
  show Region.Sub ⟨w64 (Pf s), 48⟩ _; rw [h.hA0]; exact stk_sub s 2640 48 (by decide)

theorem hArg : argR s = ⟨Bs s + BitVec.ofNat 64 2692, 48⟩ := by
  show (⟨w64 (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)), 48⟩ : Region) = _
  have := h.hPn
  have := h.hP
  rw [w64_add (by omega_arith), h.hE, Offset.add_ofNat_add_ofNat]

theorem argIn : argR s ∈ s.wr := by rw [h.pre.wr]; simp

/-- The words of the arguments are readable. -/
theorem inArg (d : Nat) (h₁ : 52 ≤ d) (h₂ : d + 4 ≤ 100) (rs : List Region) :
    InRegions (rs ++ s.wr) (w64 (Pf s + BitVec.ofNat 32 d)) 4 :=
  ⟨_, List.mem_append_right _ h.argIn, by
    rw [h.hArg, h.hA (by omega_arith)]; exact contains_off _ (by omega_arith) (by omega_arith) (by omega_arith)⟩

/-- The frame's words are writable. -/
theorem inFr (d : Nat) (h₂ : d + 4 ≤ 48) (rs : List Region) :
    InRegions (FR s :: rs) (w64 (Pf s + BitVec.ofNat 32 d)) 4 :=
  ⟨_, List.mem_cons_self .., by rw [aP h.hP (by omega_arith)]; exact Offset.contains_base _ h₂ (by omega_arith)⟩

theorem sa' (i d : Nat) (hi : i < 12) (hd : d = 52 + 4 * i) :
    s.mem.readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 = arg s i := by
  subst hd; exact h.sa i hi

theorem eM_frame : Frame [FR s] s.mem (eM s) := eMem_frame h.hP _ _

/-- The memory the entry left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint ⟨Bs s, 2688⟩) {x : Addr} (hx : r.Contains x 1) : eM s x = s.mem x :=
  h.eM_frame x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (h.fr_sub x hc)

/-- A word above the frame, after the entry. -/
theorem eAbove (d : Nat) (h₁ : 48 ≤ d) (h₂ : d + 4 ≤ 100) :
    (eM s).readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 = s.mem.readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 := by
  refine h.eM_frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  show Region.Disjoint ⟨w64 (Pf s + BitVec.ofNat 32 d), 4⟩ ⟨w64 (Pf s), 48⟩
  rw [h.hA (by omega_arith), h.hA0]
  exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by have := h.hBn; omega_arith)

/-- The bytes at `src`, after the entry. -/
theorem srcE : bytesAt (eM s) (w64 (Src s)) (L s) = bytesAt s.mem (w64 (Src s)) (L s) :=
  bytesAt_frame h.eM_frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.pre.bs.symm.sub_right h.fr_sub) (by have := h.pre.os; omega_arith)

omit h in
theorem hlen : (bytesAt s.mem (w64 (Src s)) (L s)).length = L s := Proof.Cmac.bytesAt_length _ _ _

omit h in
theorem frame_cM : Frame [dR s] (eM s) (cM s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Lay.hlen, Nat.le_refl]

/-- The words of the stack, from the frame up to our arguments, are apart from `dst`. -/
theorem dsep (d : Nat) (hd : d + 4 ≤ 2688 ∨ d = 2688 ∨ (2692 ≤ d ∧ d + 4 ≤ 2740)) :
    (⟨Bs s + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint (dR s) := by
  rcases hd with hd | rfl | ⟨h₁, h₂⟩
  · exact h.pre.bd.sub_left (stk_sub s d 4 hd)
  · rw [← h.hE]; exact h.pre.ed
  · have da := h.pre.da
    rw [h.hArg] at da
    exact (da.sub_right (Offset.sub _ h₁ (by omega_arith))).symm

/-- A word of the frame or above it, once the ciphertext is copied. -/
theorem cWord (d : Nat) (hd : d + 4 ≤ 48 ∨ d = 48 ∨ (52 ≤ d ∧ d + 4 ≤ 100)) :
    (cM s).readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 = (eM s).readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 := by
  rw [h.hA (by omega_arith)]
  refine Frame.readW Lay.frame_cM (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact h.dsep _ (by omega_arith)

end Lay

/-! ## The phases -/

/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eM s
  esi : e.gpr .esi = Pf s + BitVec.ofNat 32 76
  edx : e.gpr .edx = Dst s
  gpr : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .esi → r ≠ .esp → e.gpr r = s.gpr r
  esp : e.gpr .esp = Pf s
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (allocated 48 s) (Entered s) := by
  have ae : (allocated 48 s).gpr .esp = Pf s := allocated_esp 48 s
  refine WP.mono (entry_ok (allocated 48 s) (by rw [ae]; exact h.hP)
      (fun d hd => by rw [ae, allocated_wr]; exact h.inFr d hd _)
      (fun d h₁ h₂ => by
        rw [ae, allocated_rd, allocated_wr, show s.rd ++ FR s :: s.wr = (s.rd ++ [FR s]) ++ s.wr by simp]
        exact h.inArg d h₁ h₂ _)) fun e ⟨me, esi, edx, ge, rde, wre⟩ => ?_
  rw [ae] at me esi edx
  simp only [allocated_mem] at me edx
  rw [allocated_gpr _ _ (by decide), allocated_gpr _ _ (by decide)] at me
  refine ⟨me, esi, edx.trans (h.sa' 8 84 (by decide) rfl), fun r h₀ h₁ h₂ hsp => ?_, ?_, rde, wre⟩
  · rw [ge r h₀ h₁ h₂, allocated_gpr _ _ hsp]
  · rw [ge _ (by decide) (by decide) (by decide), ae]

theorem a80 (P : BitVec 32) : P + BitVec.ofNat 32 76 + BitVec.ofNat 32 4 = P + BitVec.ofNat 32 80 := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The copy's precondition after the entry: the descriptor is our
arguments `src` and `len`. -/
theorem slicePre_of {s e : State} (h : Lay s) (he : Entered s e) :
    SlicePre e (Pf s + BitVec.ofNat 32 76) (Src s) (Dst s) (L s) := by
  have hin (d : Nat) (h₁ : 52 ≤ d) (h₂ : d + 4 ≤ 100) :
      InRegions (e.rd ++ e.wr) (w64 (Pf s + BitVec.ofNat 32 d)) 4 := by
    rw [he.rd, he.wr, show s.rd ++ FR s :: s.wr = (s.rd ++ [FR s]) ++ s.wr by simp]
    exact h.inArg d h₁ h₂ _
  have w (d : Nat) (h₁ : 52 ≤ d) (h₂ : d + 4 ≤ 100) :
      e.mem.readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 = s.mem.readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 := by
    rw [he.mem]; exact h.eAbove d (by omega_arith) h₂
  exact { esi := he.esi
          edx := he.edx
          d0 := hin 76 (by decide) (by decide)
          d4 := by rw [a80]; exact hin 80 (by decide) (by decide)
          w0 := (w 76 (by decide) (by decide)).trans (h.sa' 6 76 (by decide) rfl)
          w4 := by
            rw [a80, w 80 (by decide) (by decide), h.sa' 7 80 (by decide) rfl, BitVec.ofNat_toNat,
              BitVec.setWidth_eq]
          lt := (arg s 7).isLt
          fitS := h.pre.os
          fitD := h.pre.od
          rd := covers_of_mem' (List.mem_append_left _ (by rw [he.rd, h.pre.rd]; simp))
          wr := fun _ => covers_of_mem' (by rw [he.wr, h.pre.wr]; simp)
          disj := h.pre.sd
          dd := by rw [a80, h.hA (by decide)]; exact h.dsep 2720 (.inr (.inr ⟨by decide, by decide⟩)) }

/-- After the copy. -/
structure Copied (s c : State) : Prop where
  mem : c.mem = cM s
  gpr : ∀ r, r ∉ copyRegs → r ≠ .esi → r ≠ .esp → c.gpr r = s.gpr r
  esp : c.gpr .esp = Pf s
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr

theorem copied_wp {s e : State} (h : Lay s) (he : Entered s e) : WP isa copySlice e (Copied s) := by
  refine WP.mono (copySlice_wp e (slicePre_of h he)) fun c ⟨mc, _, kc⟩ => ?_
  rw [he.mem, h.srcE] at mc
  refine ⟨mc, fun r hr hsi hsp => ?_, ?_, kc.rd.trans he.rd, kc.wr.trans he.wr⟩
  · have hr' := hr
    simp only [copyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [kc.gpr r hr, he.gpr r hr'.1 hr'.2.2.1 hsi hsp]
  · rw [kc.gpr _ (by decide), he.esp]

section
variable (s : State)

/-- The regions the call of `vg_aes_gcm_open` reads and writes: its
arguments are the first 40 bytes of our frame. -/
abbrev rdC : List Region := [kR s, nR s, aR s, tR s]
abbrev wrC : List Region := [dR s, ⟨Bs s + BitVec.ofNat 64 2640, 40⟩]

/-- The call's state, with its permissions. -/
abbrev xS (c : State) : State := c.callEntry.withRegions (rdC s) (wrC s)

end

section
variable {s c : State} (h : Lay s) (hc : Copied s c)
include h hc

theorem Copied.espN : (c.gpr .esp).toNat = (s.gpr .esp).toNat - 48 := by rw [hc.esp]; exact h.hPn

/-- The callee's stack pointer, below its return address. -/
theorem Copied.cesp : w64 ((xS s c).gpr .esp) = Bs s + BitVec.ofNat 64 2636 := by
  have := h.pre.w₁
  have := h.hPn
  simp only [State.withRegions_gpr, State.callEntry_esp, hc.esp]
  rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, w64_sub (by omega_arith), h.hA0,
    add_ofNat_sub_ofNat _ (by decide)]

theorem Copied.cargAddr : argAddr (xS s c) 0 = Bs s + BitVec.ofNat 64 2640 := by
  have e : argAddr (xS s c) 0 = argAddr c.callEntry 0 := rfl
  rw [e, argAddr_callEntry, hc.esp, Nat.mul_zero, add_zero32]; exact h.hA0

/-- The callee's arguments: words of our frame. -/
theorem Copied.args :
    arg (xS s c) 0 = K s ∧ arg (xS s c) 1 = arg s 1 ∧ arg (xS s c) 2 = Nn s ∧ arg (xS s c) 3 = arg s 3 ∧
      arg (xS s c) 4 = Ad s ∧ arg (xS s c) 5 = arg s 5 ∧ arg (xS s c) 6 = Dst s ∧ arg (xS s c) 7 = arg s 7 ∧
      arg (xS s c) 8 = Tg s ∧ arg (xS s c) 9 = arg s 11 := by
  have := h.pre.w₁
  have := h.hP
  have := h.hPn
  have e (j : Nat) (hj : j < 10) : arg (xS s c) j = (eM s).readW (w64 (Pf s + BitVec.ofNat 32 (4 * j))) 32 := by
    show arg c.callEntry j = _
    rw [arg_callEntry (by rw [hc.esp]; omega_arith) (by rw [hc.esp]; omega_arith), hc.mem, hc.esp,
      h.cWord (4 * j) (.inl (by omega_arith))]
  obtain ⟨w0, w4, w8, w12, w16, w20, w24, w28, w32, w36, -⟩ :=
    eMem_words (m := s.mem) h.hP (s.gpr .esi) (s.gpr .edi)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e 0 (by decide), Nat.mul_zero, add_zero32]; exact w0.trans (h.sa' 0 52 (by decide) rfl)
  · rw [e 1 (by decide)]; exact w4.trans (h.sa' 1 56 (by decide) rfl)
  · rw [e 2 (by decide)]; exact w8.trans (h.sa' 2 60 (by decide) rfl)
  · rw [e 3 (by decide)]; exact w12.trans (h.sa' 3 64 (by decide) rfl)
  · rw [e 4 (by decide)]; exact w16.trans (h.sa' 4 68 (by decide) rfl)
  · rw [e 5 (by decide)]; exact w20.trans (h.sa' 5 72 (by decide) rfl)
  · rw [e 6 (by decide)]; exact w24.trans (h.sa' 8 84 (by decide) rfl)
  · rw [e 7 (by decide)]; exact w28.trans (h.sa' 7 80 (by decide) rfl)
  · rw [e 8 (by decide)]; exact w32.trans (h.sa' 10 92 (by decide) rfl)
  · rw [e 9 (by decide)]; exact w36.trans (h.sa' 11 96 (by decide) rfl)

/-- What the call needs. -/
theorem Copied.call : callPre (xS s c) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧ Covers (wrC s) c.wr := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hc.args h
  have cesp := hc.cesp h
  have carg := hc.cargAddr h
  have hesp := hc.espN h
  have pre := h.pre
  have := h.pre.w₁
  have := h.hP
  have := h.hBn
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, cesp,
      carg, BitVec.add_sub_cancel]
    have espc : ((xS s c).gpr .esp).toNat = (s.gpr .esp).toNat - 52 := by
      simp only [State.withRegions_gpr, State.callEntry_esp]
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_toNat32 (by omega_arith), hesp]; omega_arith
    have stkArg : (⟨Bs s, 2636⟩ : Region).Disjoint ⟨Bs s + BitVec.ofNat 64 2640, 40⟩ := by
      have := Offset.disjoint (Bs s) (d := 0) (n := 2636) (e := 2640) (k := 40) (.inl (by decide)) (by decide)
        (by decide)
      rwa [BitVec.add_zero] at this
    have retArg : (⟨Bs s + BitVec.ofNat 64 2636, 4⟩ : Region).Disjoint ⟨Bs s + BitVec.ofNat 64 2640, 40⟩ :=
      Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    have sb (d n : Nat) (hd : d + n ≤ 2688) {r : Region} (hr : (stkR s).Disjoint r) :
        (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := hr.sub_left (stk_sub s d n hd)
    refine ⟨by omega_arith, by omega_arith, trivial, trivial, pre.kd, (sb 2640 40 (by decide) pre.bk).symm, pre.nd,
      (sb 2640 40 (by decide) pre.bn).symm, pre.ad, (sb 2640 40 (by decide) pre.ba).symm, pre.dt,
      (sb 2640 40 (by decide) pre.bd).symm, (sb 2640 40 (by decide) pre.bt).symm,
      sb 2636 4 (by decide) pre.bk, sb 2636 4 (by decide) pre.bn, sb 2636 4 (by decide) pre.ba,
      sb 2636 4 (by decide) pre.bd, sb 2636 4 (by decide) pre.bt, retArg,
      pre.bk.sub_left (Region.sub_prefix (by decide)), pre.bn.sub_left (Region.sub_prefix (by decide)),
      pre.ba.sub_left (Region.sub_prefix (by decide)), pre.bd.sub_left (Region.sub_prefix (by decide)),
      pre.bt.sub_left (Region.sub_prefix (by decide)), stkArg, pre.ok, pre.on, pre.oa, pre.od, pre.ot, pre.hR⟩
  · have inRd {r : Region} (h' : r ∈ [kR s, nR s, aR s, tR s]) : Covers [r] (c.rd ++ c.wr) := by
      refine covers_of_mem' (List.mem_append_left _ ?_)
      rw [hc.rd, pre.rd]; simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl | rfl <;> simp
    have hfr : Covers [⟨Bs s + BitVec.ofNat 64 2640, 48⟩] (c.rd ++ c.wr) := by
      rw [← h.hA0]; exact covers_of_mem' (List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..))
    have hd' : Covers [dR s] (c.rd ++ c.wr) :=
      covers_of_mem' (List.mem_append_right _ (by rw [hc.wr, pre.wr]; simp))
    intro a n ⟨r, hr, hcn⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl)
    · exact inRd (by simp) a n ⟨_, List.mem_singleton_self _, hcn⟩
    · exact inRd (by simp) a n ⟨_, List.mem_singleton_self _, hcn⟩
    · exact inRd (by simp) a n ⟨_, List.mem_singleton_self _, hcn⟩
    · exact inRd (by simp) a n ⟨_, List.mem_singleton_self _, hcn⟩
    · exact hd' a n ⟨_, List.mem_singleton_self _, hcn⟩
    · exact hfr a n ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hcn ⊢; omega_arith⟩
  · intro a n ⟨r, hr, hcn⟩
    rw [hc.wr, pre.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, hcn⟩
    · refine ⟨FR s, List.mem_cons_self .., ?_⟩
      show Region.Contains ⟨w64 (Pf s), 48⟩ a n
      rw [h.hA0]; simp only [Region.Contains] at hcn ⊢; omega_arith

/-- The call's result, on the call's state. -/
theorem Copied.xres : callRes (xS s c) = res s := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hc.args h
  have pre := h.pre
  have cesp := hc.cesp h
  -- The callee's memory: ours, with its return address below our frame.
  have fx : Frame [⟨Bs s + BitVec.ofNat 64 2636, 4⟩] c.mem (xS s c).mem := by
    show Frame _ c.mem (c.mem.writeW (w64 (c.gpr .esp - 4)) (c.unknowns 0))
    have e4 : w64 (c.gpr .esp - 4) = Bs s + BitVec.ofNat 64 2636 := by
      simpa only [State.withRegions_gpr, State.callEntry_esp] using cesp
    rw [e4]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hfc : Frame [FR s, dR s, ⟨Bs s + BitVec.ofNat 64 2636, 4⟩] s.mem (xS s c).mem := by
    have m₁ : Frame [FR s, dR s, ⟨Bs s + BitVec.ofNat 64 2636, 4⟩] s.mem (eM s) :=
      h.eM_frame.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
    have m₂ : Frame [FR s, dR s, ⟨Bs s + BitVec.ofNat 64 2636, 4⟩] (eM s) c.mem := by
      rw [hc.mem]; exact Lay.frame_cM.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
    have m₃ : Frame [FR s, dR s, ⟨Bs s + BitVec.ofNat 64 2636, 4⟩] c.mem (xS s c).mem :=
      fx.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
    exact (m₁.trans m₂).trans m₃
  have apart {r : Region} (h₁ : (stkR s).Disjoint r) (h₂ : r.Disjoint (dR s)) :
      ∀ r' ∈ [FR s, dR s, ⟨Bs s + BitVec.ofNat 64 2636, 4⟩], r.Disjoint r' := by
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact h₁.symm.sub_right h.fr_sub
    · exact h₂
    · exact (h₁.sub_left (stk_sub s 2636 4 (by decide))).symm
  obtain ⟨hc', hh⟩ := Proof.AesGcm.ctx_frame hfc (apart pre.bk pre.kd) pre.hR
  have hn : bytesAt (xS s c).mem (w64 (Nn s)) (NL s) = bytesAt s.mem (w64 (Nn s)) (NL s) :=
    Proof.Cmac.bytesAt_frame hfc (apart pre.bn pre.nd) (by have := pre.on; omega_arith)
  have ha : bytesAt (xS s c).mem (w64 (Ad s)) (AL s) = bytesAt s.mem (w64 (Ad s)) (AL s) :=
    Proof.Cmac.bytesAt_frame hfc (apart pre.ba pre.ad) (by have := pre.oa; omega_arith)
  have ht : bytesAt (xS s c).mem (w64 (Tg s)) (TL s) = bytesAt s.mem (w64 (Tg s)) (TL s) :=
    Proof.Cmac.bytesAt_frame hfc (apart pre.bt pre.dt.symm) (by have := pre.ot; omega_arith)
  have hd : bytesAt (xS s c).mem (w64 (Dst s)) (L s) = bytesAt s.mem (w64 (Src s)) (L s) := by
    rw [Proof.Cmac.bytesAt_frame fx (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.dsep 2636 (.inl (by decide))).symm) (by have := pre.od; omega_arith), hc.mem]
    have := Proof.AesGcm.bytesAt_writeBytes_self (eM s) (w64 (Dst s)) (bytesAt s.mem (w64 (Src s)) (L s))
      (by rw [Lay.hlen]; show (arg s 7).toNat < _; have := (arg s 7).isLt; omega_arith)
    rwa [Lay.hlen] at this
  simp only [callRes, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  rw [hc', hh, hn, hd, ha, ht]

end

/-- What the call leaves of `dst` and `eax`: `vg_aes_gcm_open`'s result. -/
def Out (s : State) (e : BitVec 32) (m : Mem) : Prop :=
  match res s with
  | some pt => e = 1 ∧ bytesAt m (w64 (Dst s)) (L s) = pt
  | none => e = 0

/-- After the call. -/
structure Called (s z : State) : Prop where
  esi : z.mem.readW (w64 (Pf s + BitVec.ofNat 32 40)) 32 = s.gpr .esi
  edi : z.mem.readW (w64 (Pf s + BitVec.ofNat 32 44)) 32 = s.gpr .edi
  ret : z.mem.readW (w64 (Pf s + BitVec.ofNat 32 48)) 32 = s.mem.readW (w64 (Pf s + BitVec.ofNat 32 48)) 32
  a7 : z.mem.readW (w64 (Pf s + BitVec.ofNat 32 80)) 32 = arg s 7
  a8 : z.mem.readW (w64 (Pf s + BitVec.ofNat 32 84)) 32 = arg s 8
  out : Out s (z.gpr .eax) z.mem
  ebx : z.gpr .ebx = s.gpr .ebx
  ebp : z.gpr .ebp = s.gpr .ebp
  esp : z.gpr .esp = Pf s
  rd : z.rd = s.rd
  wr : z.wr = FR s :: s.wr

theorem Called.congr {s z t : State} (hz : Called s z) (hm : t.mem = z.mem) (hg : ∀ r, t.gpr r = z.gpr r)
    (hrd : t.rd = z.rd) (hwr : t.wr = z.wr) : Called s t :=
  ⟨by rw [hm]; exact hz.esi, by rw [hm]; exact hz.edi, by rw [hm]; exact hz.ret, by rw [hm]; exact hz.a7,
    by rw [hm]; exact hz.a8, by rw [hm, hg]; exact hz.out, by rw [hg]; exact hz.ebx, by rw [hg]; exact hz.ebp,
    by rw [hg]; exact hz.esp, hrd.trans hz.rd, hwr.trans hz.wr⟩

theorem called_wp (F : OpenFn) {s c : State} (h : Lay s) (hc : Copied s c) :
    WP isa (.call F.name F.code) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hc.args h
  have hdep := F.depth
  have hesp := hc.espN h
  have := h.pre.w₁
  have := h.hBn
  have := h.hP
  refine WP.call F.verified.1 F.noSp (by omega_arith) (openSpec_pre hcp) hcov hw
    fun s' rd' wr' cs' fr' _ ⟨s₂, m₂, g₂, post'⟩ => ?_
  have hpost := openSpec_post post' (by rw [a1]; exact h.pre.hR)
  rw [hc.xres h, a6, a7, m₂, g₂ .eax (by decide)] at hpost
  -- What the call kept: our frame above its arguments, and our arguments.
  have hbelow : below (c.gpr .esp) (stackUse F.code + 4) =
      ⟨Bs s + BitVec.ofNat 64 (2640 - (stackUse F.code + 4)), stackUse F.code + 4⟩ := by
    show (⟨w64 (c.gpr .esp - BitVec.ofNat 32 (stackUse F.code + 4)), _⟩ : Region) = _
    rw [w64_sub (by omega_arith), hc.esp, h.hA0, add_ofNat_sub_ofNat _ (by omega_arith)]
  have kept (d : Nat) (h₁ : 2680 ≤ d) (h₂ : d + 4 ≤ 2688 ∨ d = 2688 ∨ (2692 ≤ d ∧ d + 4 ≤ 2740)) :
      s'.mem.readW (Bs s + BitVec.ofNat 64 d) 32 = c.mem.readW (Bs s + BitVec.ofNat 64 d) 32 := by
    refine Frame.readW fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, hbelow] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact h.dsep d h₂
    · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  have word (d : Nat) (h₁ : 40 ≤ d) (h₂ : d + 4 ≤ 48 ∨ d = 48 ∨ (52 ≤ d ∧ d + 4 ≤ 100)) :
      s'.mem.readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 = (eM s).readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 := by
    rw [← h.cWord d h₂, ← hc.mem, h.hA (by omega_arith), kept _ (by omega_arith) (by omega_arith)]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, w40, w44⟩ := eMem_words (m := s.mem) h.hP (s.gpr .esi) (s.gpr .edi)
  refine ⟨(word 40 (by decide) (.inl (by decide))).trans w40, (word 44 (by decide) (.inl (by decide))).trans w44,
    ?_, ?_, ?_, hpost, ?_, ?_, ?_, rd'.trans hc.rd, wr'.trans hc.wr⟩
  · rw [word 48 (by decide) (.inr (.inl rfl))]; exact h.eAbove 48 (by decide) (by decide)
  · rw [word 80 (by decide) (.inr (.inr ⟨by decide, by decide⟩)), h.eAbove 80 (by decide) (by decide)]
    exact h.sa' 7 80 (by decide) rfl
  · rw [word 84 (by decide) (.inr (.inr ⟨by decide, by decide⟩)), h.eAbove 84 (by decide) (by decide)]
    exact h.sa' 8 84 (by decide) rfl
  · rw [cs' .ebx (by decide), hc.gpr .ebx (by decide) (by decide) (by decide)]
  · rw [cs' .ebp (by decide), hc.gpr .ebp (by decide) (by decide) (by decide)]
  · rw [cs' .esp (by decide), hc.esp]

/-! ## After the call -/

/-- `test eax, eax`: whether the call returned 0. -/
theorem test_ok (z : State) : WP isa (.block [.alu .test .eax (.reg .eax)]) z fun t =>
    t.mem = z.mem ∧ (∀ r, t.gpr r = z.gpr r) ∧ t.zf = some (z.gpr .eax == 0) ∧ t.rd = z.rd ∧ t.wr = z.wr := by
  refine WP.of_runBlock ⟨_, by xrun [], ?_⟩
  refine ⟨?_, fun r => ?_, ?_, ?_, ?_⟩
  · simp only [mem_arithFlags]
  · simp only [gpr_arithFlags]
  · simp only [zf_arithFlags, BitVec.and_self]
  · simp only [rd_arithFlags]
  · simp only [wr_arithFlags]

/-- `cmp ecx, 0`: whether there are bytes to zero. -/
theorem cmp0_ok (u : State) {n : Nat} (hn : n < 2 ^ 32) (h₂ : u.gpr .ecx = BitVec.ofNat 32 n) :
    WP isa (.block [.alu .cmp .ecx (imm 0)]) u fun t => t.mem = u.mem ∧ (∀ r, t.gpr r = u.gpr r) ∧
      t.zf = some (decide (n = 0)) ∧ t.rd = u.rd ∧ t.wr = u.wr := by
  refine WP.of_runBlock ⟨_, by xrun [], ?_⟩
  refine ⟨?_, fun r => ?_, ?_, ?_, ?_⟩
  · simp only [mem_arithFlags]
  · simp only [gpr_arithFlags]
  · simp only [zf_arithFlags, h₂, BitVec.sub_zero, VG.X86.Wp.ofNat_beq_zero hn]
  · simp only [rd_arithFlags]
  · simp only [wr_arithFlags]

/-- One step of the wipe: the byte at `D + j` zeroed. -/
theorem zeroStep_ok (t : State) {D : BitVec 32} {j : Nat} (hd : t.gpr .edx = D + BitVec.ofNat 32 j)
    (ha : t.gpr .eax = 0) (w : InRegions t.wr (w64 (D + BitVec.ofNat 32 j)) 1) :
    ∃ t', runBlock isa [.store8 (at_ .edx 0) .al, .alu .add .edx (imm 1), .alu .sub .ecx (imm 1)] t = some t' ∧
      t'.mem = t.mem.writeW (w64 (D + BitVec.ofNat 32 j)) (0 : BitVec 8) ∧
      t'.gpr .edx = D + BitVec.ofNat 32 (j + 1) ∧ t'.gpr .ecx = t.gpr .ecx - BitVec.ofNat 32 1 ∧
      t'.zf = some (t.gpr .ecx - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by xrun [hd, add_zero32, w], ?_, ?_, ?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_⟩
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    rw [show Reg8.al.reg = Reg.eax from rfl, ha, show BitVec.setWidth 8 (0 : BitVec 32) = 0 by decide]
  · regs [hd, succ_ofNat32]
  · regs []
  · simp only [zf_setMem, zf_setReg, zf_arithFlags, gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false,
      reduceCtorEq]
  · simp [gpr_setMem, gpr_setReg, gpr_arithFlags, h₁, h₂]
  · simp only [rd_setMem, rd_setReg, rd_arithFlags]
  · simp only [wr_setMem, wr_setReg, wr_arithFlags]

/-- `wipeLoop`: the `n` bytes at `D` zeroed, from `edx = D`, `ecx = n` and
`eax = 0`. -/
theorem wipeLoop_wp (u : State) {D : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) (hD : D.toNat + n ≤ 2 ^ 32)
    (h₁ : u.gpr .edx = D) (h₂ : u.gpr .ecx = BitVec.ofNat 32 n) (h₀ : u.gpr .eax = 0)
    (hw : Covers [⟨w64 D, n⟩] u.wr) :
    WP isa wipeLoop u fun u' => Proof.Zeroize.Prefix u'.mem (w64 D) n ∧ Frame [⟨w64 D, n⟩] u.mem u'.mem ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  unfold wipeLoop
  refine WP.seq (WP.mono (cmp0_ok u hn h₂) fun t ⟨tm, tg, tz, trd, twr⟩ => ?_)
  refine WP.ite (decide (n = 0)) tz (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), by rw [tm]; exact Frame.refl _ _,
      fun r _ _ => tg r, trd, twr⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.loop (M := isa)
      (body := .block [.store8 (at_ .edx 0) .al, .alu .add .edx (imm 1), .alu .sub .ecx (imm 1)]) (c := .ne)
      (fun (w : Nat) (v : State) => ∃ i, w = n - i ∧ i < n ∧ v.gpr .edx = D + BitVec.ofNat 32 i ∧
        v.gpr .ecx = BitVec.ofNat 32 (n - i) ∧ (∀ r, r ≠ .ecx → r ≠ .edx → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧
        v.wr = u.wr ∧ Frame [⟨w64 D, n⟩] u.mem v.mem ∧ Proof.Zeroize.Prefix v.mem (w64 D) i) ?_ (n - 0) _
      ⟨0, rfl, by omega, by rw [tg, h₁, add_zero32], by rw [tg, h₂, Nat.sub_zero], fun r _ _ => tg r, trd, twr,
        by rw [tm]; exact Frame.refl _ _, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    rintro w v ⟨i, rfl, hi, edx, ecx, gv, rdv, wrv, fv, pv⟩
    have aD : w64 (D + BitVec.ofNat 32 i) = w64 D + BitVec.ofNat 64 i := w64_add (by omega)
    have hcn : (⟨w64 D, n⟩ : Region).Contains (w64 D + BitVec.ofNat 64 i) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    have win : InRegions v.wr (w64 (D + BitVec.ofNat 32 i)) 1 := by
      rw [wrv, aD]; exact hw _ _ ⟨_, List.mem_singleton_self _, hcn⟩
    obtain ⟨v', run', mem', edx', ecx', zf', g', rd', wr'⟩ :=
      zeroStep_ok v edx (by rw [gv _ (by decide) (by decide), h₀]) win
    refine WP.of_runBlock ⟨v', run', ?_⟩
    have f' : Frame [⟨w64 D, n⟩] u.mem v'.mem := by
      rw [mem', aD]; exact fv.writeW (List.mem_singleton_self _) _ hcn
    have p' : Proof.Zeroize.Prefix v'.mem (w64 D) (i + 1) := by
      rw [mem', aD]; exact Proof.Zeroize.prefix_writeW (w := 8) pv (by omega)
    have g'' : ∀ r, r ≠ .ecx → r ≠ .edx → v'.gpr r = u.gpr r := fun r a b => by rw [g' r a b, gv r a b]
    have hz : v'.zf = some (decide (i + 1 = n)) := by rw [zf', ecx, pred_beq hi hn]
    by_cases he : i + 1 = n
    · left
      exact ⟨by simp [eval, hz, he], by rw [← he]; exact p', f', g'', rd'.trans rdv, wr'.trans wrv⟩
    · right
      exact ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, edx',
        by rw [ecx', ecx, pred_count hi hn], g'', rd'.trans rdv, wr'.trans wrv, f', p'⟩

/-- The zeros of `Prefix`, as bytes. -/
theorem bytesAt_zeros {m : Mem} {D : Addr} {n : Nat} (h : Proof.Zeroize.Prefix m D n) :
    bytesAt m D n = List.replicate n 0 := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact h i (by simpa [bytesAt] using h₁)

/-- After `wipeArgs`: `dst` in `edx`, `len` in `ecx` and zero in `eax`. -/
structure WArgs (s z a : State) : Prop where
  edx : a.gpr .edx = Dst s
  ecx : a.gpr .ecx = BitVec.ofNat 32 (L s)
  eax : a.gpr .eax = 0
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → a.gpr r = z.gpr r
  mem : a.mem = z.mem
  rd : a.rd = z.rd
  wr : a.wr = z.wr

theorem wipeArgs_wp {s z : State} (h : Lay s) (hz : Called s z) : WP isa (.block wipeArgs) z (WArgs s z) := by
  have hr (d : Nat) (h₁ : 52 ≤ d) (h₂ : d + 4 ≤ 100) :
      InRegions (z.rd ++ z.wr) (w64 (z.gpr .esp + BitVec.ofNat 32 d)) 4 := by
    rw [hz.esp, hz.rd, hz.wr, show s.rd ++ FR s :: s.wr = (s.rd ++ [FR s]) ++ s.wr by simp]
    exact h.inArg d h₁ h₂ _
  refine WP.of_runBlock ⟨_, by
    xrun [OpenTo.wipeArgs, sp, hr 80 (by decide) (by decide), hr 84 (by decide) (by decide)], ?_⟩
  refine ⟨?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_, ?_⟩
  · regs [hz.esp, hz.a8]
  · regs [hz.esp, hz.a7]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · regs []; rfl
  · simp [gpr_setReg, h₁, h₂, h₃]
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]

/-- Where `after` leaves the state: what follows the call, with `dst` and
`eax` as `toPost` has them. -/
structure Done (s u : State) : Prop where
  post : toPost s u
  esi : u.mem.readW (w64 (Pf s + BitVec.ofNat 32 40)) 32 = s.gpr .esi
  edi : u.mem.readW (w64 (Pf s + BitVec.ofNat 32 44)) 32 = s.gpr .edi
  ret : u.mem.readW (w64 (Pf s + BitVec.ofNat 32 48)) 32 = s.mem.readW (w64 (Pf s + BitVec.ofNat 32 48)) 32
  ebx : u.gpr .ebx = s.gpr .ebx
  ebp : u.gpr .ebp = s.gpr .ebp
  esp : u.gpr .esp = Pf s
  rd : u.rd = s.rd
  wr : u.wr = FR s :: s.wr

/-- When the call failed: `dst` zeroed. -/
theorem wipe_wp {s z : State} (h : Lay s) (hz : Called s z) (hres : res s = none) : WP isa wipe z (Done s) := by
  unfold wipe
  refine WP.seq (WP.mono (wipeArgs_wp h hz) fun a ha => ?_)
  have hw : Covers [⟨w64 (Dst s), L s⟩] a.wr := by
    rw [ha.wr, hz.wr, h.pre.wr]; exact covers_of_mem' (by simp)
  refine WP.mono (wipeLoop_wp a (arg s 7).isLt h.pre.od ha.edx ha.ecx ha.eax hw)
    fun u ⟨pz, fu, gu, rdu, wru⟩ => ?_
  have g' : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → u.gpr r = z.gpr r := fun r a b c => by
    rw [gu r b c, ha.gpr r a b c]
  have keep (d : Nat) (hd : d + 4 ≤ 48 ∨ d = 48) :
      u.mem.readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 = z.mem.readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 := by
    rw [← ha.mem, h.hA (by omega_arith)]
    refine fu.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact h.dsep _ (by omega_arith)
  refine ⟨?_, (keep 40 (.inl (by decide))).trans hz.esi, (keep 44 (.inl (by decide))).trans hz.edi,
    (keep 48 (.inr rfl)).trans hz.ret, by rw [g' _ (by decide) (by decide) (by decide)]; exact hz.ebx,
    by rw [g' _ (by decide) (by decide) (by decide)]; exact hz.ebp,
    by rw [g' _ (by decide) (by decide) (by decide)]; exact hz.esp, by rw [rdu, ha.rd, hz.rd],
    by rw [wru, ha.wr, hz.wr]⟩
  show match res s with | some pt => _ | none => _
  rw [hres]
  exact ⟨by rw [gu _ (by decide) (by decide)]; exact ha.eax, bytesAt_zeros pz⟩

/-- After the call: `dst` zeroed if it failed. -/
theorem after_wp {s z : State} (h : Lay s) (hz : Called s z) : WP isa after z (Done s) := by
  unfold after
  refine WP.seq (WP.mono (test_ok z) fun t ⟨tm, tg, tz, trd, twr⟩ => ?_)
  have ht := hz.congr tm tg trd twr
  have o := ht.out
  unfold Out at o
  cases hr : res s with
  | none =>
    rw [hr] at o
    exact WP.ite true (by show t.zf = _; rw [tz, ← tg, o]; rfl) (fun _ => wipe_wp h ht hr)
      (fun h' => absurd h' (by decide))
  | some pt =>
    rw [hr] at o
    refine WP.ite false (by show t.zf = _; rw [tz, ← tg, o.1]; rfl) (fun h' => absurd h' (by decide))
      (fun _ => WP.block_nil ⟨?_, ht.esi, ht.edi, ht.ret, ht.ebx, ht.ebp, ht.esp, ht.rd, ht.wr⟩)
    show match res s with | some pt => _ | none => _
    rw [hr]
    exact o

/-- Our caller's registers back from the frame, and the frame freed. -/
theorem ret_wp {s u : State} (h : Lay s) (hu : Done s u) :
    WP isa (.block OpenTo.restore) u fun z => abiPreserved s (freed 48 z) ∧ toPost s (freed 48 z) := by
  have hr (d : Nat) (hd : d + 4 ≤ 48) : InRegions (u.rd ++ u.wr) (w64 (u.gpr .esp + BitVec.ofNat 32 d)) 4 := by
    rw [hu.esp, hu.wr]
    obtain ⟨r, hr, hc⟩ := h.inFr d hd s.wr
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.of_runBlock ⟨_, by xrun [OpenTo.restore, sp, hr 40 (by decide), hr 44 (by decide)], ?_⟩
  have hret : Pf s + BitVec.ofNat 32 48 = s.gpr .esp := BitVec.sub_add_cancel _ _
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [freed]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · simp [gpr_setReg, hu.ebx]
    · simp [gpr_setReg, hu.esp, hu.esi]
    · simp [gpr_setReg, hu.esp, hu.edi]
    · simp [gpr_setReg, hu.ebp]
    · simp [gpr_setReg, hu.esp]; exact BitVec.sub_add_cancel _ _
  · simp only [freed, mem_setReg]; rw [← hret]; exact hu.ret
  · have p := hu.post
    show match res s with | some pt => _ | none => _
    revert p
    show (match res s with | some pt => _ | none => _) → _
    cases res s with
    | some pt => intro p; simpa [freed, gpr_setReg, mem_setReg] using p
    | none => intro p; simpa [freed, gpr_setReg, mem_setReg] using p

/-- The body of the frame never writes `esp`. -/
theorem body_noSp (F : OpenFn) :
    NoSp (.seq (.block entry) (.seq copySlice (.seq (.call F.name F.code) (.seq after (.block OpenTo.restore)))) :
      Prog isa) := by
  have he : NoSp (.block entry : Prog isa) := NoSp.of_all (by decide)
  have hc : NoSp copySlice := NoSp.of_all (by decide)
  have ha : NoSp after := NoSp.of_all (by decide)
  have hr : NoSp (.block OpenTo.restore : Prog isa) := NoSp.of_all (by decide)
  intro i hi
  simp only [instrs, List.mem_append] at hi
  rcases hi with hi | hi | hi | hi | hi
  exacts [he i hi, hc i hi, F.noSp i hi, ha i hi, hr i hi]

theorem openTo_wp (F : OpenFn) {s : State} (hs : ToPre s) :
    WP isa (openTo F.name F.code) s fun z => abiPreserved s z ∧ toPost s z := by
  have h := lay hs
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := hs.w₁; omega_arith) (body_noSp F) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (copied_wp h he) fun c hc => ?_)
  refine WP.seq (WP.mono (called_wp F h hc) fun z hz => ?_)
  refine WP.seq (WP.mono (after_wp h hz) fun u hu => ?_)
  exact ret_wp h hu

end VG.Proof.AesGcm.X86.OpenTo
