module

public import VerifiedGarbage.Proof.AesOcb.X86_64.Body
public import VerifiedGarbage.Proof.AesOcb.X86_64.Env
public import VerifiedGarbage.Impl.AesOcb.X86_64
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.AesOcb.X86_64.Callee
import VerifiedGarbage.Proof.AesOcb.X86_64.Words
import VerifiedGarbage.Proof.AesOcb.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.AesOcb.X86_64.Hash
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.AesOcb.X86_64.PadTo
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
public import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `AesOcb.X86_64.Contract`, which this module and modules that import it used -/

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

@[expose] public section

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
abbrev aData (s : State) : Region := ⟨arg s 0, (arg s 1).toNat⟩

/-- The tag. -/
abbrev aTag (s : State) : Region := ⟨arg s 2, (arg s 3).toNat⟩

/-- The working space, of `wn` bytes (3584 for the functions over the AES
block functions). -/
abbrev aWork (s : State) (wn : Nat := 3584) : Region := ⟨arg s 4, wn⟩

/-- What `vg_aes_ocb_seal` and `vg_aes_ocb_open` need of their arguments
`(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx, aad = r8,
aad_len = r9, data = [rsp + 8], len = [rsp + 16], tag = [rsp + 24],
tag_len = [rsp + 32], work = [rsp + 40])`, but for what they may access. -/
def oneFacts (s : State) (wn : Nat := 3584) : Prop :=
  (aCtx s).Disjoint (aData s) ∧ (aCtx s).Disjoint (aWork s wn) ∧ (aNonce s).Disjoint (aData s) ∧
    (aNonce s).Disjoint (aWork s wn) ∧ (aAad s).Disjoint (aData s) ∧ (aAad s).Disjoint (aWork s wn) ∧
    (aTag s).Disjoint (aData s) ∧ (aTag s).Disjoint (aWork s wn) ∧
    (aData s).Disjoint (aWork s wn) ∧ (aData s).Disjoint (args s 5) ∧ (aWork s wn).Disjoint (args s 5) ∧
    (ret s).Disjoint (aData s) ∧ (ret s).Disjoint (aWork s wn) ∧ (ret s).Disjoint (aTag s) ∧
    (stk8 s).Disjoint (aCtx s) ∧ (stk8 s).Disjoint (aNonce s) ∧ (stk8 s).Disjoint (aAad s) ∧
    (stk8 s).Disjoint (aData s) ∧ (stk8 s).Disjoint (aWork s wn) ∧ (stk8 s).Disjoint (aTag s) ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 64 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 64 ∧
    (arg s 4).toNat + wn ≤ 2 ^ 64 ∧ 8 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧
    rounds s ∧ lengthsOk (arg s 3).toNat (s.gpr .rcx).toNat = true

/-- What `vg_aes_ocb_seal` needs: it may write the data, the tag and the
working space. -/
def sealPreX (s : State) (wn : Nat := 3584) : Prop :=
  s.rd = [aCtx s, aNonce s, aAad s, args s 5] ∧ s.wr = [aData s, aTag s, aWork s wn] ∧
    (aTag s).Disjoint (args s 5) ∧ (aCtx s).Disjoint (aTag s) ∧ (aNonce s).Disjoint (aTag s) ∧
    (aAad s).Disjoint (aTag s) ∧ oneFacts s wn

/-- What `vg_aes_ocb_open` needs: it may write the data and the working
space, and read the tag. -/
def openPreX (s : State) (wn : Nat := 3584) : Prop :=
  s.rd = [aCtx s, aNonce s, aAad s, aTag s, args s 5] ∧ s.wr = [aData s, aWork s wn] ∧ oneFacts s wn

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `OCB-DECRYPT` of what `vg_aes_ocb_open` is given. -/
def openOut (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxInv s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    (ctxLstar s.mem (s.gpr .rdi)) (arg s 3).toNat (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (bytesAt s.mem (arg s 0) (arg s 1).toNat)
    (bytesAt s.mem (arg s 2) (arg s 3).toNat)

/-- `vg_aes_ocb_seal`. -/
def sealX86_64 : Contract isa where
  pre := sealPreX
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxLstar s.mem (s.gpr .rdi)) (arg s 3).toNat
        (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (bytesAt s.mem (arg s 0) (arg s 1).toNat) =
      (bytesAt s'.mem (arg s 0) (arg s 1).toNat, bytesAt s'.mem (arg s 2) (arg s 3).toNat)
  pub := onePub

/-- What `vg_aes_ocb_open` may leak (`Spec.Ocb.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬rounds s then [] else [if (openOut s).isSome then 1 else 0]

/-- `vg_aes_ocb_open`. -/
def openX86_64 : Contract isa where
  pre := openPreX
  post s s' :=
    match openOut s with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (arg s 0) (arg s 1).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (arg s 0) (arg s 1).toNat = zeros (arg s 1).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

/-- `vg_aes_ocb_init(key = rdi, key_len = rsi, ctx = rdx, scratch = rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let ctx : Region := ⟨s.gpr .rdx, 256⟩
    let scr : Region := ⟨s.gpr .rcx, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (ret s).Disjoint ctx ∧ (ret s).Disjoint scr ∧
      (stk8 s).Disjoint key ∧ (stk8 s).Disjoint ctx ∧ (stk8 s).Disjoint scr ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 256 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 2560 ≤ 2 ^ 64 ∧ 8 ≤ (s.gpr .rsp).toNat ∧
      ((s.gpr .rsi).toNat = 16 ∨ (s.gpr .rsi).toNat = 24 ∨ (s.gpr .rsi).toNat = 32)
  post s s' := KeyRepr s'.mem (s.gpr .rdx) (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `initX86_64`, with only the 24 bytes `init` writes itself of `scratch`,
when the functions it calls need no working space. -/
def initX86_64F : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let ctx : Region := ⟨s.gpr .rdx, 256⟩
    let scr : Region := ⟨s.gpr .rcx, 24⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (ret s).Disjoint ctx ∧ (ret s).Disjoint scr ∧
      (stk8 s).Disjoint key ∧ (stk8 s).Disjoint ctx ∧ (stk8 s).Disjoint scr ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 256 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 24 ≤ 2 ^ 64 ∧ 8 ≤ (s.gpr .rsp).toNat ∧
      ((s.gpr .rsi).toNat = 16 ∨ (s.gpr .rsi).toNat = 24 ∨ (s.gpr .rsi).toNat = 32)
  post := initX86_64.post
  pub := initX86_64.pub

end VG.Proof.AesOcb

end

end

/-! ### `AesOcb.X86_64.Entry`, which only this module used -/

section

/-!
# AES-OCB on x86-64: the entry and the exit (`entry`, `restore`)

Untrusted: everything here is checked by Lean. `entry` reads `W` from the
stack, saves our caller's registers at `W + savO`, keeps the arguments in
`W`, the address of the tag at `W + tgO`, computes `L_$` and `L_0` from
`L_*` and zeroes the checksum (`entry_ok`); `restore` reads the registers
back (`restore_ok`).
-/

@[expose] public section

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
    ∃ s', runBlock isa [ld .rax .rsp a, st .r15 d .rax] s = some s' ∧
      s'.mem = s.mem.writeW (W + BitVec.ofNat 64 d) v ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by orun [hsp, h15, hv, ra, wd], ?_, fun r h => ?_, ?_, ?_⟩
  · simp only [mem_setReg]
  · simp only [gpr_setReg, h, ite_false]
  all_goals rfl

/-- What `entry` leaves. -/
structure EntryPostN (K W SP : Addr) (wn : Nat) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (T : Addr)
    (s s₁ : State) : Prop where
  env : EnvN K W SP wn s₁
  slots : Slots W R N A D nl n tl s₁.mem
  tg : s₁.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T
  alen : s₁.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 al
  saved : Saved s₁.mem W s.gpr
  ld : blockAtMem s₁.mem (W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem K)
  l0 : blockAtMem s₁.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0
  ck : blockAtMem s₁.mem (W + BitVec.ofNat 64 ckO) = 0
  frame : Frame [entryR W] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  rdi : s₁.gpr .rdi = s.gpr .rdi

abbrev EntryPost (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (T : Addr) (s s₁ : State) : Prop :=
  EntryPostN K W SP 3584 R N A D nl al n tl T s s₁

/-- `entry`. -/
theorem entry_ok {K W SP : Addr} {wn : Nat} (L : LayN K W SP wn) {s : State} (P : PermN K W wn s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} {T : Addr} (hsp : s.gpr .rsp = SP)
    (hargs : Covers [⟨SP + BitVec.ofNat 64 8, 40⟩] (s.rd ++ s.wr))
    (hargsW : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, wn⟩)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al)
    (hwn : 640 ≤ wn := by decide) (hwlt : wn < 2 ^ 64 := by decide) :
    ∃ s₁, runBlock isa entry s = some s₁ ∧ EntryPostN K W SP wn R N A D nl al n tl T s s₁ := by
  have a₈ := in_off (d := 0) (n := 8) hargs (by decide) (by decide)
  have a₁₆ := in_off (d := 8) (n := 8) hargs (by decide) (by decide)
  have a₂₄ := in_off (d := 16) (n := 8) hargs (by decide) (by decide)
  have a₃₂ := in_off (d := 24) (n := 8) hargs (by decide) (by decide)
  have a₄₀ := in_off (d := 32) (n := 8) hargs (by decide) (by decide)
  rw [add_ofNat_assoc, show 8 + 0 = 8 from rfl] at a₈
  rw [add_ofNat_assoc] at a₁₆ a₂₄ a₃₂ a₄₀
  have w₁ := P.wW6 hwn hwlt (show 160 + 8 ≤ 640 by decide)
  have w₂ := P.wW6 hwn hwlt (show 168 + 8 ≤ 640 by decide)
  have w₃ := P.wW6 hwn hwlt (show 176 + 8 ≤ 640 by decide)
  have w₄ := P.wW6 hwn hwlt (show 184 + 8 ≤ 640 by decide)
  have w₅ := P.wW6 hwn hwlt (show 192 + 8 ≤ 640 by decide)
  have w₆ := P.wW6 hwn hwlt (show 200 + 8 ≤ 640 by decide)
  have w₇ := P.wW6 hwn hwlt (show 232 + 8 ≤ 640 by decide)
  have w₈ := P.wW6 hwn hwlt (show 288 + 8 ≤ 640 by decide)
  have w₉ := P.wW6 hwn hwlt (show 296 + 8 ≤ 640 by decide)
  have w₁₀ := P.wW6 hwn hwlt (show 240 + 8 ≤ 640 by decide)
  have w₁₁ := P.wW6 hwn hwlt (show 248 + 8 ≤ 640 by decide)
  -- The registers saved, `W` and `K` in `r15` and `r14`, the arguments in registers kept.
  obtain ⟨s₁, run₁, hsp₁, h15₁, h14₁, rd₁, wr₁, f₁, sv₁, s232, s288, s296, s240, s248, di₁⟩ : ∃ s₁, runBlock isa
      ([.mov .rax (.mem (at_ .rsp 40))] ++ save .rax ++
        [mvr .r15 .rax, mvr .r14 .rdi, st .r15 rndO .rsi, st .r15 nO .rdx, st .r15 nlO .rcx,
          st .r15 aadO .r8, st .r15 alenO .r9]) s = some s₁ ∧
      s₁.gpr .rsp = SP ∧ s₁.gpr .r15 = W ∧ s₁.gpr .r14 = K ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 160, 144⟩] s.mem s₁.mem ∧ Saved s₁.mem W s.gpr ∧
      s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R ∧ s₁.mem.readW (W + BitVec.ofNat 64 288) 64 = N ∧
      s₁.mem.readW (W + BitVec.ofNat 64 296) 64 = BitVec.ofNat 64 nl ∧
      s₁.mem.readW (W + BitVec.ofNat 64 240) 64 = A ∧
      s₁.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 al ∧ s₁.gpr .rdi = s.gpr .rdi := by
    have cE : ∀ d, 160 ≤ d → d + 8 ≤ 304 → (⟨W + BitVec.ofNat 64 160, 144⟩ : Region).Contains
        (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains W h₁ (by omega_using [h₂]) (by decide)
    refine ⟨_, by orun [save, saved, List.map_cons, List.map_nil, hW, hsp, a₄₀, w₁, w₂, w₃, w₄, w₅, w₆, w₇,
      w₈, w₉, w₁₀, w₁₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        simp (disch := decide) only [savO, Nat.reduceAdd, mem_setReg, readW_writeW_off, Mem.readW_writeW_self64]
    all_goals simp (disch := decide) only [mem_setReg, readW_writeW_off, Mem.readW_writeW_self64, gpr_setReg,
      ite_true, ite_false, reduceCtorEq, hsi, hdx, hcx, hr8, hr9]
  -- The arguments on the stack.
  have dA : ∀ {a d k : Nat}, 8 ≤ a → a + 8 ≤ 48 → d + k ≤ 640 →
      (⟨SP + BitVec.ofNat 64 a, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ := fun {a d k} h₁ h₂ h₃ => by
    have e : SP + BitVec.ofNat 64 a = SP + BitVec.ofNat 64 8 + BitVec.ofNat 64 (a - 8) := by
      rw [add_ofNat_assoc, show 8 + (a - 8) = a by omega_using [h₁]]
    rw [e]; exact (hargsW.sub_left (Offset.sub_base _ (by omega_using [h₂]))).sub_right (LayN.wSub6 hwn h₃)
  have kA : ∀ {a : Nat}, 8 ≤ a → a + 8 ≤ 48 →
      s₁.mem.readW (SP + BitVec.ofNat 64 a) 64 = s.mem.readW (SP + BitVec.ofNat 64 a) 64 := fun {a} h₁ h₂ =>
    f₁.readW (r := ⟨SP + BitVec.ofNat 64 a, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dA h₁ h₂ (by decide)) (by decide)
  have sW : ∀ {a d : Nat}, 8 ≤ a → a + 8 ≤ 48 → d + 8 ≤ 640 → Mem.Sep (SP + BitVec.ofNat 64 a) (64 / 8)
      (W + BitVec.ofNat 64 d) (64 / 8) := fun h₁ h₂ h₃ =>
    (dA h₁ h₂ h₃).sep (Region.contains_self _ _) (Region.contains_self _ _)
  obtain ⟨s₂, run₂, m₂, g₂, rd₂, wr₂⟩ := argSlot_ok (s := s₁) (a := 8) (d := dataO) hsp₁ h15₁
    (by rw [kA (by decide) (by decide), hD]) (by rw [rd₁, wr₁]; exact a₈) (by rw [wr₁]; exact P.wW6 hwn hwlt (by decide))
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := argSlot_ok (s := s₂) (a := 16) (d := lenO)
    (by rw [g₂ _ (by decide), hsp₁]) (by rw [g₂ _ (by decide), h15₁])
    (by rw [m₂, Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide),
      kA (by decide) (by decide), hn])
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact a₁₆) (by rw [wr₂, wr₁]; exact P.wW6 hwn hwlt (by decide))
  obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ := argSlot_ok (s := s₃) (a := 32) (d := tlO)
    (by rw [g₃ _ (by decide), g₂ _ (by decide), hsp₁]) (by rw [g₃ _ (by decide), g₂ _ (by decide), h15₁])
    (by rw [m₃, Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide), m₂,
      Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide), kA (by decide) (by decide), htl])
    (by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact a₃₂) (by rw [wr₃, wr₂, wr₁]; exact P.wW6 hwn hwlt (by decide))
  obtain ⟨s₄', run₄', m₄', g₄', rd₄', wr₄'⟩ := argSlot_ok (s := s₄) (a := 24) (d := tgO)
    (by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), hsp₁])
    (by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), h15₁])
    (by rw [m₄, Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide), m₃,
      Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide), m₂,
      Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide), kA (by decide) (by decide), hT])
    (by rw [rd₄, wr₄, rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact a₂₄) (by rw [wr₄, wr₃, wr₂, wr₁]; exact P.wW6 hwn hwlt (by decide))
  have E₄ : EnvN K W SP wn s₄' := ⟨by rw [g₄' _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), h14₁],
    by rw [g₄' _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), h15₁],
    by rw [g₄' _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), hsp₁],
    P.of_eq (by rw [rd₄', rd₄, rd₃, rd₂, rd₁]) (by rw [wr₄', wr₄, wr₃, wr₂, wr₁])⟩
  -- What the writes of the arguments keep.
  have k₄ : ∀ {d : Nat}, (d + 8 ≤ 208 ∨ 232 ≤ d ∧ d + 8 ≤ 304) → d + 8 ≤ 640 →
      s₄'.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ => by
    rw [m₄', readW_writeW_off _ (by simp only [tgO]; omega_using [h₁]) (by omega_using [h₁]) (by decide),
      m₄, readW_writeW_off _ (by simp only [tlO]; omega_using [h₁]) (by omega_using [h₁]) (by decide), m₃,
      readW_writeW_off _ (by simp only [lenO]; omega_using [h₁]) (by omega_using [h₁]) (by decide), m₂,
      readW_writeW_off _ (by simp only [dataO]; omega_using [h₁]) (by omega_using [h₁]) (by decide)]
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
    rw [blockAtMem_frame f₁₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact (L.k_w.sub_left (Lay.kSub (by decide))).sub_right (LayN.wSub6 hwn (by decide)))]
    rfl
  obtain ⟨s₅, run₅, B₅⟩ := dbl_ok (s := s₄') (b := .r14) (a := 240) (d := ldO) E₄.r15 E₄.r14 (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (E₄.perm.kR (by decide)) (E₄.perm.kR (by decide)) (E₄.perm.wW6 hwn hwlt (by decide)) (E₄.perm.wW6 hwn hwlt (by decide))
  have nE : ∀ r ∈ [Reg.r14, .r15, .rsp], r ∉ [Reg.rax, .rdx, .rcx, .r8] := by decide
  have E₅ : EnvN K W SP wn s₅ := E₄.keep (fun r hr => B₅.gpr r (nE r hr)) B₅.rd B₅.wr
  obtain ⟨s₆, run₆, B₆⟩ := dbl_ok (s := s₅) (b := .r15) (a := ldO) (d := l0O) E₅.r15 E₅.r15 (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (E₅.perm.wR6 hwn hwlt (by decide)) (E₅.perm.wR6 hwn hwlt (by decide)) (E₅.perm.wW6 hwn hwlt (by decide)) (E₅.perm.wW6 hwn hwlt (by decide))
  have E₆ : EnvN K W SP wn s₆ := E₅.keep (fun r hr => B₆.gpr r (nE r hr)) B₆.rd B₆.wr
  obtain ⟨s₇, run₇, B₇⟩ := zero16_ok (s := s₆) (d := ckO) E₆.r15 (E₆.perm.wW6 hwn hwlt (by decide)) (E₆.perm.wW6 hwn hwlt (by decide))
  have E₇ : EnvN K W SP wn s₇ := E₆.keep (fun r hr => B₇.gpr r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide))
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
  have k₇ : ∀ {d : Nat}, 96 ≤ d → d + 8 ≤ 640 →
      s₇.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄'.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ =>
    fr₇.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w6 hwn (.inr (by omega_using [h₁])) h₂ (by decide)) (by decide)
  have k : ∀ {d : Nat}, 232 ≤ d → d + 8 ≤ 304 →
      s₇.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ => by
    rw [k₇ (by omega_using [h₁]) (by omega_using [h₂]), k₄ (.inr ⟨h₁, h₂⟩) (by omega_using [h₂])]
  have kd : ∀ {d : Nat}, 208 ≤ d → d + 8 ≤ 640 →
      s₇.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄'.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ =>
    k₇ (by omega_using [h₁]) (by omega_using [h₂])
  refine ⟨s₇, ?_, ⟨E₇, ⟨?_, ?_, ?_, by rw [k (by decide) (by decide), s232], by rw [k (by decide) (by decide), s240],
    by rw [k (by decide) (by decide), s288], by rw [k (by decide) (by decide), s296]⟩, ?_,
    by rw [show alenO = 248 from rfl, k (by decide) (by decide), s248], fun p hp => ?_, ?_, ?_, B₇.val, ?_,
    by rw [B₇.rd, B₆.rd, B₅.rd, rd₄', rd₄, rd₃, rd₂, rd₁], by rw [B₇.wr, B₆.wr, B₅.wr, wr₄', wr₄, wr₃, wr₂, wr₁],
    by rw [B₇.gpr _ (by decide), B₆.gpr _ (by decide), B₅.gpr _ (by decide), g₄' _ (by decide), g₄ _ (by decide),
      g₃ _ (by decide), g₂ _ (by decide), di₁]⟩⟩
  · rw [show entry = ([.mov .rax (.mem (at_ .rsp 40))] ++ save .rax ++
        [mvr .r15 .rax, mvr .r14 .rdi, st .r15 rndO .rsi, st .r15 nO .rdx, st .r15 nlO .rcx,
          st .r15 aadO .r8, st .r15 alenO .r9]) ++ [ld .rax .rsp 8, st .r15 dataO .rax] ++
        [ld .rax .rsp 16, st .r15 lenO .rax] ++ [ld .rax .rsp 32, st .r15 tlO .rax] ++
        [ld .rax .rsp 24, st .r15 tgO .rax] ++ dbl .r14 240 .r15 ldO ++
        dbl .r15 ldO .r15 l0O ++ zero16 ckO by
      simp only [entry, lsetup, List.append_assoc, List.cons_append, List.nil_append],
      runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append,
      runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, run₄,
      Option.bind_some, run₄', Option.bind_some, run₅, Option.bind_some, run₆, Option.bind_some, run₇]
  · rw [kd (by decide) (by decide), m₄', readW_writeW_off _ (by decide) (by decide) (by decide), m₄,
      readW_writeW_off _ (by decide) (by decide) (by decide), m₃,
      readW_writeW_off _ (by decide) (by decide) (by decide), m₂]
    exact Mem.readW_writeW_self64 ..
  · rw [kd (by decide) (by decide), m₄', readW_writeW_off _ (by decide) (by decide) (by decide), m₄,
      readW_writeW_off _ (by decide) (by decide) (by decide), m₃]
    exact Mem.readW_writeW_self64 ..
  · rw [kd (by decide) (by decide), m₄', readW_writeW_off _ (by decide) (by decide) (by decide), m₄]
    exact Mem.readW_writeW_self64 ..
  · rw [kd (by decide) (by decide), m₄']
    exact Mem.readW_writeW_self64 ..
  · have hp' := hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rw [← sv₁ p hp]
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k₇ (by decide) (by decide), k₄ (.inl (by decide)) (by decide)]
  · rw [blockAtMem_frame B₇.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w6 hwn (.inr (by decide)) (by decide) (by decide)),
      blockAtMem_frame B₆.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w6 hwn (.inl (by decide)) (by decide) (by decide)),
      B₅.val, l₄]
    rfl
  · rw [blockAtMem_frame B₇.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w6 hwn (.inr (by decide)) (by decide) (by decide)),
      B₆.val, B₅.val, l₄]
    rfl
  · refine (((f₁₄.mono (rs' := [⟨W + BitVec.ofNat 64 160, 144⟩, ⟨W + BitVec.ofNat 64 208, 104⟩,
      ⟨W + BitVec.ofNat 64 32, 64⟩]) (by simp)).trans (fr₇.mono (by simp)))).sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩

/-- `restore`: our caller's registers back. -/
theorem restore_ok {K W SP : Addr} {s : State} {wn : Nat} (E : EnvN K W SP wn s) {g : Reg → BitVec 64} (hs : Saved s.mem W g)
    (hwn : 640 ≤ wn := by decide) (hwlt : wn < 2 ^ 64 := by decide) :
    ∃ s', runBlock isa restore s = some s' ∧ (∀ p ∈ saved, s'.gpr p.1 = g p.1) ∧ s'.mem = s.mem ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rax = s.gpr .rax := by
  have h15 := E.r15
  obtain r₁ := E.perm.wR6 hwn hwlt (show 160 + 8 ≤ 640 by decide)
  obtain r₂ := E.perm.wR6 hwn hwlt (show 168 + 8 ≤ 640 by decide)
  obtain r₃ := E.perm.wR6 hwn hwlt (show 176 + 8 ≤ 640 by decide)
  obtain r₄ := E.perm.wR6 hwn hwlt (show 184 + 8 ≤ 640 by decide)
  obtain r₅ := E.perm.wR6 hwn hwlt (show 192 + 8 ≤ 640 by decide)
  obtain r₆ := E.perm.wR6 hwn hwlt (show 200 + 8 ≤ 640 by decide)
  obtain v₁ := hs (.rbx, 160) (by decide)
  obtain v₂ := hs (.rbp, 168) (by decide)
  obtain v₃ := hs (.r12, 176) (by decide)
  obtain v₄ := hs (.r13, 184) (by decide)
  obtain v₅ := hs (.r14, 192) (by decide)
  obtain v₆ := hs (.r15, 200) (by decide)
  refine ⟨_, by orun [restore, saved, List.map_cons, List.map_nil, h15, r₁, r₂, r₃, r₄, r₅, r₆], ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, v₁, v₂, v₃, v₄, v₅, v₆]
  · rfl
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]

end VG.Proof.AesOcb.X86_64

end

end


/-!
# AES-OCB on x86-64: `vg_aes_ocb_seal`

Untrusted: everything here is checked by Lean. The preconditions `sealPreX`
and `openPreX` give the facts the proofs use about the arguments (`Args`,
`sealArgs_of`, `openArgs_of`). `seal` is `front`: `entry`, the table of
`L_j` (`table`), `Offset_0` (`nonce`), `HASH` (`hash`), the data (`body`)
and the tag at `W` (`tag`)
(`sealFront_wp`); then the copy of the tag to `tag` (`tagOut`) and
`restore` (`seal_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append length_bytesAt bytesAt_frame covers_left covers_of_mem)

/-- What `seal` and `open` are given: the key context at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`), the working
space at `W` and the stack pointer `SP`. -/
structure ArgsN (s : State) (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) (wn : Nat) : Prop where
  lay : LayN K W SP wn
  perm : PermN K W wn s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : BufN W SP wn s N nl
  aad : BufN W SP wn s A al
  data : DBufN K W SP wn s D n
  tag : BufN W SP wn s T tl
  nd : (⟨N, nl⟩ : Region).Disjoint ⟨D, n⟩
  td : (⟨T, tl⟩ : Region).Disjoint ⟨D, n⟩
  ad : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩
  n1 : 1 ≤ nl
  n15 : nl ≤ 15
  t1 : 1 ≤ tl
  t16 : tl ≤ 16
  retW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, wn⟩
  retD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  retT : (⟨SP, 8⟩ : Region).Disjoint ⟨T, tl⟩
  args : Covers [⟨SP + BitVec.ofNat 64 8, 40⟩] (s.rd ++ s.wr)
  argsW : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, wn⟩

abbrev Args (s : State) (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) : Prop :=
  ArgsN s K W SP N A D R nl al n tl T 3584

/-- `Args` from the facts both preconditions give, for a state that may
read the key context, the nonce, the associated data, the tag and the
arguments on the stack, and write the data and `W`. -/
theorem args_of {s : State} {wn : Nat} (h : oneFacts s wn)
    (mrd : ∀ r ∈ [aCtx s, aNonce s, aAad s, args s 5, aTag s], Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [aData s, aWork s wn], Covers [r] s.wr) :
    ArgsN s (s.gpr .rdi) (arg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (arg s 0) (s.gpr .rsi).toNat
      (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat (arg s 2) wn := by
  sig_split h
  rename_i d3 d4 d5 d6 d7 d8 t1 t2 d9 _ d11 d12 d13 t3 d14 d15 d16 d17 d18 t4 b19 b20 b21 b22 bt b23 b24 _ hR
  have hv := h
  clear h
  simp only [Spec.Ocb.lengthsOk, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨ht1, ht16⟩, hn1⟩, hn15⟩ := hv
  exact {
    lay := ⟨b19, b23, d4, d14, d18, b24⟩
    perm := ⟨mrd _ (by simp), mwr _ (by simp)⟩
    rounds := hR
    nonce := ⟨mrd _ (by simp), BitVec.isLt _, b20, d6, d15⟩
    aad := ⟨mrd _ (by simp), BitVec.isLt _, b21, d8, d16⟩
    data := ⟨⟨covers_left (mwr _ (by simp)), BitVec.isLt _, b22, d9, d17⟩, mwr _ (by simp), d3⟩
    tag := ⟨mrd _ (by simp), BitVec.isLt _, bt, t2, t4⟩
    nd := d5
    ad := d7
    td := t1
    n1 := hn1
    n15 := hn15
    t1 := ht1
    t16 := ht16
    retW := d13
    retD := d12
    retT := t3
    args := mrd (args s 5) (by simp)
    argsW := d11.symm }

theorem sealArgs_of {s : State} {wn : Nat} (h : sealPreX s wn) :
    ArgsN s (s.gpr .rdi) (arg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (arg s 0) (s.gpr .rsi).toNat
      (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat (arg s 2) wn := by
  obtain ⟨hrd, hwr, -, -, -, -, hf⟩ := h
  refine args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_of_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_of_mem (by simp))

theorem openArgs_of {s : State} {wn : Nat} (h : openPreX s wn) :
    ArgsN s (s.gpr .rdi) (arg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (arg s 0) (s.gpr .rsi).toNat
      (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat (arg s 2) wn := by
  obtain ⟨hrd, hwr, hf⟩ := h
  refine args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_of_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_of_mem (by simp))

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

section
variable {K W SP D : Addr} {n : Nat} {m m' : Mem}

theorem saved_mut (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩)
    (hf : Frame (mutR W SP D n) m m') {g : Reg → BitVec 64} (S : Saved m W g) : Saved m' W g := by
  intro p hp
  rw [← S p hp]
  obtain hd : 160 ≤ p.2 ∧ p.2 + 8 ≤ 248 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact hf.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (w := 64) (Region.contains_self _ _) (kept_mut L hD (.inl hd))
    (by decide)

theorem buf_mut {s : State} {P : Addr} {len : Nat} (hP : Buf W SP s P len)
    (hPD : (⟨P, len⟩ : Region).Disjoint ⟨D, n⟩) (hf : Frame (mutR W SP D n) m m') :
    bytesAt m' P len = bytesAt m P len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
    · exact hPD
    · exact hP.w.sub_right (Lay.wSub (by decide))) (by have := hP.lt; omega_arith)

theorem lstar_mut (L : Lay K W SP) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩) (hf : Frame (mutR W SP D n) m m') :
    ctxLstar m' K = ctxLstar m K :=
  blockAtMem_frame hf fun r hr => (k_mut L hD r hr).sub_left (Lay.kSub (by decide))

end

/-- What `tag d` writes, within the parts the pieces write. -/
theorem tagR_mut {W SP D : Addr} {n d : Nat} (hd : d + 16 ≤ 160) {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩, wC W, below SP 8] m m') :
    Frame (mutR W SP D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., sub_wA hd⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The return address is outside what the functions write. -/
theorem ret_disj {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 3584⟩)
    (hD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩) : ∀ r ∈ entryR W :: mutR W SP D n, (⟨SP, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Region.sub_prefix (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below SP (by have := L.sp; omega_arith)
  · exact hD
  · exact hW.sub_right (Lay.wSub (by decide))

/-- The first `t ≤ 16` bytes of a block. -/
theorem bytesAt_take_block (m : Mem) (p : Addr) {t : Nat} (h : t ≤ 16) :
    bytesAt m p t = (Spec.Ocb.toBytes (blockAtMem m p)).take t := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = t + (16 - t) by omega_arith,
    Proof.Ocb.bytesAt_append, List.take_left' (length_bytesAt _ _ _)]

/-- What the pieces before the data leave: the offset, the checksum, `L_$`,
the table of `L_j` and `HASH`. -/
structure Pre (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) (s s' : State) : Prop where
  env : Env K W SP s'
  frame : Frame (entryR W :: mutR W SP D n) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  slots : Slots W R N A D nl n tl s'.mem
  tg : s'.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T
  saved : Saved s'.mem W s.gpr
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) =
    Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) =
    Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
  ck : blockAtMem s'.mem (W + BitVec.ofNat 64 ckO) = 0
  ld : blockAtMem s'.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K)
  tbl : TblL W (ctxLstar s.mem K) n s'.mem
  sum : blockAtMem s'.mem (W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al)
  ciph : ctxCiph s'.mem K R = ctxCiph s.mem K R
  lstar : ctxLstar s'.mem K = ctxLstar s.mem K
  data : bytesAt s'.mem D n = bytesAt s.mem D n

/-- The table misses what `nonce` writes. -/
theorem wT_nonceR {K W SP : Addr} (L : Lay K W SP) : ∀ r ∈ nonceR W SP, (wT W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.wT_w (by decide)
  · exact L.wT_w (by decide)
  · exact L.wT_w (by decide)
  · exact (L.stk_w' (by decide)).symm

/-- The table misses what `HASH` writes. -/
theorem wT_hashR {K W SP : Addr} (L : Lay K W SP) : ∀ r ∈ hashR W SP, (wT W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.wT_w (by decide)
  · exact L.wT_w (by decide)
  · exact L.wT_w (by decide)
  · exact L.wT_w (by decide)
  · exact (L.stk_w' (by decide)).symm

/-- A frame within the table is within what the pieces write. -/
theorem wT_mut {W SP D : Addr} {n : Nat} {m m' : Mem} (h : Frame [wT W] m m') : Frame (mutR W SP D n) m m' :=
  h.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩

/-- `entry`, `table`, `nonce` and `hash`. -/
theorem pre_wp' (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W SP N A D R nl al n tl T) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa (.seq (.block entry) (.seq table (.seq (nonce (callees v)) (hash (callees v))))) s
      (Pre K W SP N A D R nl al n tl T s) := by
  have L : Lay _ _ _ := Ar.lay
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  obtain ⟨s₀, run₀, P₀⟩ := entry_ok L Ar.perm hsp Ar.args Ar.argsW hD hn hT htl hW hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₀, run₀, ?_⟩)
  -- The table.
  refine WP.seq (WP.mono (table_ok P₀.env Ar.data.lt Ar.aad.lt P₀.slots.len P₀.alen P₀.l0) fun s₁ Q₁ => ?_)
  obtain F₁ : Frame (mutR W SP D n) s₀.mem s₁.mem := wT_mut Q₁.frame
  obtain kW₁ : ∀ {d : Nat}, d + 16 ≤ 2560 →
      blockAtMem s₁.mem (W + BitVec.ofNat 64 d) = blockAtMem s₀.mem (W + BitVec.ofNat 64 d) := fun hd =>
    blockAtMem_frame Q₁.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.wT_w hd).symm
  obtain S₁ := Slots.of_mut L Ar.data.w F₁ P₀.slots
  obtain rd₁ : s₁.rd = s.rd := by rw [Q₁.rd, P₀.rd]
  obtain wr₁ : s₁.wr = s.wr := by rw [Q₁.wr, P₀.wr]
  obtain eK : ctxCiph s₁.mem K R = ctxCiph s.mem K R := by
    rw [ctxCiph_mut L Ar.data.k F₁ Ar.rounds]
    unfold ctxCiph
    rw [bytesAt_frame P₀.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))) (by omega_arith)]
  obtain eL : ctxLstar s₁.mem K = ctxLstar s.mem K := by
    rw [lstar_mut L Ar.data.k F₁]
    exact blockAtMem_frame P₀.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Lay.kSub (by decide))).sub_right (Lay.wSub (by decide)))
  obtain eB : ∀ {P : Addr} {k : Nat}, Buf W SP s P k → bytesAt s₁.mem P k = bytesAt s.mem P k := fun hP => by
    rw [bytesAt_frame Q₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega_arith)]
    exact bytesAt_frame P₀.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega_arith)
  obtain alen₁ : s₁.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 al := by
    rw [Q₁.frame.readW (r := ⟨W + BitVec.ofNat 64 alenO, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.wT_w (by decide)).symm) (by decide), P₀.alen]
  -- `Offset_0`.
  refine WP.seq (WP.mono (nonce_ok v L Q₁.env Ar.rounds S₁.rounds S₁.nonce S₁.nlen S₁.tl
    Ar.n1 Ar.n15 (by have := Ar.t16; omega_arith) (Ar.nonce.of_eq rd₁ wr₁) Ar.data.k Ar.data.w) fun s₂ P₂ => ?_)
  obtain F₂ : Frame (mutR W SP D n) s₁.mem s₂.mem := nonceR_mut P₂.frame
  obtain S₂ := Slots.of_mut L Ar.data.w F₂ S₁
  obtain c₂ : ctxCiph s₂.mem K R = ctxCiph s.mem K R := (ctxCiph_mut L Ar.data.k F₂ Ar.rounds).trans eK
  obtain l₂ : ctxLstar s₂.mem K = ctxLstar s.mem K := (lstar_mut L Ar.data.k F₂).trans eL
  obtain a₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := (buf_mut Ar.aad Ar.ad F₂).trans (eB Ar.aad)
  -- `HASH`.
  obtain C : HCtx K W SP D n R (ctxCiph s.mem K R) (ctxLstar s.mem K) A (bytesAt s.mem A al) s₂ :=
    { lay := L, rounds := Ar.rounds, ciph := c₂, lstar := l₂
      buf := by rw [length_bytesAt]; exact Ar.aad.of_eq (P₂.rd.trans rd₁) (P₂.wr.trans wr₁)
      aad := by rw [length_bytesAt, a₂]
      ad := by rw [length_bytesAt]; exact Ar.ad
      kd := Ar.data.k, dw := Ar.data.w, rnd := S₂.rounds
      short := by rw [length_bytesAt]; exact Ar.aad.lt
      tbl := by
        rw [length_bytesAt]
        exact ⟨_, Q₁.tbl.frame P₂.frame (wT_nonceR L), Nat.div_le_div_right Nat.right_le_or⟩ }
  refine WP.mono (hash_ok v C P₂.env S₂.aad (by rw [P₂.alen, alen₁, length_bytesAt]))
    fun s₃ ⟨E₃, F₃, sum₃, rd₃, wr₃⟩ => ?_
  obtain F₃' : Frame (mutR W SP D n) s₂.mem s₃.mem := hashR_mut F₃
  obtain k₃ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (256 ≤ d ∧ d + 16 ≤ 384)) →
      blockAtMem s₃.mem (W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (W + BitVec.ofNat 64 d) := fun {d} hd =>
    blockAtMem_frame F₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
      · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
      · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
      · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
      · exact (L.stk_w' (by omega_arith)).symm
  refine ⟨E₃, ?_, by rw [rd₃, P₂.rd, rd₁], by rw [wr₃, P₂.wr, wr₁], Slots.of_mut L Ar.data.w F₃' S₂,
    by rw [kept_read L Ar.data.w (F₁.trans (F₂.trans F₃')) (d := tgO) (by decide), P₀.tg],
    saved_mut L Ar.data.w (F₁.trans (F₂.trans F₃')) P₀.saved, ?_, ?_, ?_, ?_, ?_, by rw [sum₃],
    (ctxCiph_mut L Ar.data.k F₃' Ar.rounds).trans c₂, (lstar_mut L Ar.data.k F₃').trans l₂, ?_⟩
  · exact (P₀.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩).trans
      ((F₁.trans (F₂.trans F₃')).sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  · rw [k₃ (d := ofsO) (by decide), P₂.ofs, eK, eB Ar.nonce]
  · rw [k₃ (d := o0O) (by decide), P₂.o0, eK, eB Ar.nonce]
  · rw [k₃ (d := ckO) (by decide), P₂.keep (by decide) (by decide), kW₁ (by decide), P₀.ck]
  · rw [k₃ (d := ldO) (by decide), P₂.keep (by decide) (by decide), kW₁ (by decide), P₀.ld]
  · exact ⟨_, (Q₁.tbl.frame P₂.frame (wT_nonceR L)).frame F₃ (wT_hashR L),
      Nat.div_le_div_right Nat.left_le_or⟩
  · have hd := Ar.data
    rw [bytesAt_frame F₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.stk.symm) (by have := hd.lt; omega_arith),
      bytesAt_frame P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.stk.symm) (by have := hd.lt; omega_arith), eB hd.toBufN]

/-- `entry`, `table`, `nonce` and `hash`, then `k`. -/
theorem pre_wp (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W SP N A D R nl al n tl T) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al)
    {k : Prog isa} {Q : State → Prop} (hk : ∀ s', Pre K W SP N A D R nl al n tl T s s' → WP isa k s' Q) :
    WP isa (.seq (.block entry) (.seq table (.seq (nonce (callees v)) (.seq (hash (callees v)) k)))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (pre_wp' v Ar hsp hD hn hT htl hW hdi hsi hdx hcx hr8 hr9)) fun _ h₁ =>
    WP.seq (WP.mono (WP.seq_iff.mp h₁) fun _ h₂ => wp_seq_assoc (WP.seq (WP.mono h₂ hk))))

/-- `body`'s frame misses a block of `W` outside the offset, the checksum and
`[96, 144)`. -/
theorem body_keep {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) {m m' : Mem}
    (h : Frame (bodyR W SP D n) m m') {d : Nat} (hd : d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (144 ≤ d ∧ d + 16 ≤ 384)) :
    blockAtMem m' (W + BitVec.ofNat 64 d) = blockAtMem m (W + BitVec.ofNat 64 d) :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
    · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
    · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
    · exact (L.stk_w' (by omega_arith)).symm
    · exact (hD.sub_right (Lay.wSub (by omega_arith))).symm

/-- What `front` leaves for `seal`: the environment, the slots and the
address of the tag, our caller's registers, the encrypted data and the tag
at `W`. -/
structure SFront (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) (s s' : State) : Prop where
  env : Env K W SP s'
  frame : Frame (entryR W :: mutR W SP D n) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  slots : Slots W R N A D nl n tl s'.mem
  tg : s'.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T
  saved : Saved s'.mem W s.gpr
  out : Spec.Ocb.encryptWith (ctxCiph s.mem K R) (ctxLstar s.mem K) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
    (bytesAt s.mem D n) = (bytesAt s'.mem D n, bytesAt s'.mem W tl)

/-- `seal`'s `front`, for its arguments. -/
theorem sealFront_wp' (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W SP N A D R nl al n tl T) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa (front (callees v) true tagO) s (SFront K W SP N A D R nl al n tl T s) := by
  have L : Lay _ _ _ := Ar.lay
  unfold front
  refine pre_wp v Ar hsp hD hn hT htl hW hdi hsi hdx hcx hr8 hr9 fun s₃ P₃ => ?_
  obtain hD₃ : DBuf K W SP s₃ D n := Ar.data.of_eq P₃.rd P₃.wr
  refine WP.seq (WP.mono (bodySeal_ok v L P₃.env Ar.rounds P₃.slots.rounds hD₃ P₃.slots.data P₃.slots.len P₃.ofs
    P₃.o0 P₃.ck (by rw [P₃.lstar]; exact P₃.tbl)) fun s₄ B => ?_)
  obtain F₄ : Frame (mutR W SP D n) s₃.mem s₄.mem := bodyR_mut B.frame
  obtain cK₄ : ctxCiph s₄.mem K R = ctxCiph s.mem K R := (ctxCiph_mut L Ar.data.k F₄ Ar.rounds).trans P₃.ciph
  obtain ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K) := by
    rw [body_keep L Ar.data.w B.frame (d := ldO) (by decide), P₃.ld]
  obtain sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al) := by
    rw [body_keep L Ar.data.w B.frame (d := sumO) (by decide), P₃.sum]
  -- The tag.
  refine WP.mono (tag_ok v L B.env Ar.rounds ((kept_read L Ar.data.w F₄ (d := 232) (by decide)).trans
    P₃.slots.rounds) (.inl rfl)) fun s₅ T₅ => ?_
  obtain F₅ : Frame (mutR W SP D n) s₄.mem s₅.mem := tagR_mut (by decide) T₅.frame
  refine ⟨T₅.env, P₃.frame.trans ((F₄.trans F₅).sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩),
    by rw [T₅.rd, B.rd, P₃.rd], by rw [T₅.wr, B.wr, P₃.wr], Slots.of_mut L Ar.data.w (F₄.trans F₅) P₃.slots,
    by rw [kept_read L Ar.data.w (F₄.trans F₅) (d := tgO) (by decide), P₃.tg],
    saved_mut L Ar.data.w (F₄.trans F₅) P₃.saved, ?_⟩
  -- The ciphertext and the tag.
  have hout := B.out
  rw [P₃.ciph, P₃.lstar, P₃.data] at hout
  have hofs := B.ofs
  rw [P₃.lstar] at hofs
  have hck := B.ck
  rw [P₃.data] at hck
  obtain d₅ : bytesAt s₅.mem D n = bytesAt s₄.mem D n :=
    bytesAt_frame T₅.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.stk.symm) (by have := Ar.data.lt; omega_arith)
  have tv := T₅.val
  rw [show W + BitVec.ofNat 64 tagO = W from BitVec.add_zero W] at tv
  obtain t₅ : bytesAt s₅.mem W tl = (Spec.Ocb.toBytes (blockAtMem s₅.mem W)).take tl :=
    bytesAt_take_block _ _ Ar.t16
  rw [Proof.Ocb.encryptWith_eq, d₅, hout, t₅, tv, hck, hofs, ld₄, sum₄, cK₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < n % 16
  · have h' : n - 16 * (n / 16) > 0 := by omega_arith
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega_arith
    simp only [h', hr, ↓reduceIte]

/-- The arguments of `copyLoop` for the copy of the tag: from `W` to the
tag, whose address is at `W + tgO`. -/
theorem tagOutArgs_ok {K W SP : Addr} {s : State} {wn : Nat} (E : EnvN K W SP wn s) {T : Addr} {tl : Nat}
    (htg : s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (hwn : 640 ≤ wn := by decide) (hwlt : wn < 2 ^ 64 := by decide) :
    ∃ s', runBlock isa [mvr .rbx .r15, ld .rsi .r15 tgO, ld .r12 .r15 tlO, .mov .rcx (.imm 0)] s = some s' ∧
      s'.gpr .rbx = W ∧ s'.gpr .rsi = T ∧ s'.gpr .r12 = BitVec.ofNat 64 tl ∧ s'.gpr .rcx = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → r ≠ .r12 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [tgO, tlO] at htg htl
  obtain r₁ := E.perm.wR6 hwn hwlt (show 304 + 8 ≤ 640 by decide)
  obtain r₂ := E.perm.wR6 hwn hwlt (show 224 + 8 ≤ 640 by decide)
  refine ⟨_, by orun [E.r15, r₁, r₂, htg, htl], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15, htg]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15, htl]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sext0]
  · simp only [gpr_setReg, h₁, h₂, h₃, h₄, ite_false]
  all_goals rfl

/-- The received tag's arguments of `copyLoop`: from the tag, whose address
is at `W + tgO`, to `W`. -/
theorem recvArgs_ok {K W SP : Addr} {s : State} {wn : Nat} (E : EnvN K W SP wn s) {T : Addr} {tl : Nat}
    (htg : s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (hwn : 640 ≤ wn := by decide) (hwlt : wn < 2 ^ 64 := by decide) :
    ∃ s', runBlock isa [ld .rbx .r15 tgO, mvr .rsi .r15, ld .r12 .r15 tlO, .mov .rcx (.imm 0)] s = some s' ∧
      s'.gpr .rbx = T ∧ s'.gpr .rsi = W ∧ s'.gpr .r12 = BitVec.ofNat 64 tl ∧ s'.gpr .rcx = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → r ≠ .r12 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [tgO, tlO] at htg htl
  obtain r₁ := E.perm.wR6 hwn hwlt (show 304 + 8 ≤ 640 by decide)
  obtain r₂ := E.perm.wR6 hwn hwlt (show 224 + 8 ≤ 640 by decide)
  refine ⟨_, by orun [E.r15, r₁, r₂, htg, htl], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15, htg]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15, htl]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sext0]
  · simp only [gpr_setReg, h₁, h₂, h₃, h₄, ite_false]
  all_goals rfl

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag at `T`, which the
state may write. -/
theorem tagOut_ok {K W SP : Addr} {s : State} {wn : Nat} (E : EnvN K W SP wn s) {T : Addr} {tl : Nat} (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (htg : s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (hT : Covers [⟨T, tl⟩] s.wr) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, wn⟩)
    (hwn : 640 ≤ wn := by decide) (hwlt : wn < 2 ^ 64 := by decide) :
    WP isa tagOut s fun t => t.mem = writeBytes s.mem T (bytesAt s.mem W tl) ∧
      (∀ r ∈ [Reg.r14, .r15, .rsp], t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s₁, run₁, rbx₁, rsi₁, r12₁, rcx₁, g₁, m₁, rd₁, wr₁⟩ := tagOutArgs_ok E htg htl (hwn := hwn) (hwlt := hwlt)
  unfold tagOut
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (copyLoop_ok s₁ (S := W) (Dd := T) (n := tl) (by omega_arith) (by omega_arith) rbx₁ rsi₁ rcx₁ r12₁
    (by rw [rd₁, wr₁]; exact covers_left (covers_prefix E.perm.w (by omega_arith))) (by rw [wr₁]; exact hT)
    (hTW.sub_right (Region.sub_prefix (by omega_arith))).symm) fun t ⟨m, _, g, rd, wr⟩ => ⟨by rw [m, m₁], ?_,
      by rw [rd, rd₁], by rw [wr, wr₁]⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> rw [g _ (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide)]

/-- `vg_aes_ocb_seal`, for its arguments. -/
theorem seal_wp' (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W SP N A D R nl al n tl T) (hTw : Covers [⟨T, tl⟩] s.wr) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa («seal» (callees v)) s fun s' => gprPreserved s s' ∧
      Spec.Ocb.encryptWith (ctxCiph s.mem K R) (ctxLstar s.mem K) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
        (bytesAt s.mem D n) = (bytesAt s'.mem D n, bytesAt s'.mem T tl) := by
  have L : Lay _ _ _ := Ar.lay
  unfold «seal»
  refine WP.seq (WP.mono (sealFront_wp' v Ar hsp hD hn hT htl hW hdi hsi hdx hcx hr8 hr9) fun s₅ F => ?_)
  -- The copy of the tag.
  refine WP.seq (WP.mono (tagOut_ok F.env Ar.t1 Ar.t16 F.tg F.slots.tl (by rw [F.wr]; exact hTw) Ar.tag.w)
    fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => ?_)
  obtain E₆ : Env K W SP s₆ := F.env.keep g₆ rd₆ wr₆
  obtain F₆ : Frame [⟨T, tl⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  obtain S₆ : Saved s₆.mem W s.gpr := fun p hp => by
    rw [← F.saved p hp]
    exact F₆.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain hd : p.2 + 8 ≤ 3584 := by
        simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (Ar.tag.w.sub_right (Lay.wSub hd)).symm) (by decide)
  -- `restore`.
  obtain ⟨s₇, run₇, hg₇, hm₇, hsp₇, _⟩ := restore_ok E₆ S₆
  refine WP.of_runBlock ⟨s₇, run₇, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₇ (.rbx, savO) (by decide)
    · exact hg₇ (.rbp, savO + 8) (by decide)
    · rw [hsp₇, E₆.rsp, hsp]
    · exact hg₇ (.r12, savO + 16) (by decide)
    · exact hg₇ (.r13, savO + 24) (by decide)
    · exact hg₇ (.r14, savO + 32) (by decide)
    · exact hg₇ (.r15, savO + 40) (by decide)
  · rw [hm₇, hsp, F₆.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.retT) (by decide)]
    exact F.frame.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · -- The ciphertext and the tag.
    have hn := Ar.data.lt
    have ht := Ar.tag.lt
    rw [F.out, hm₇, bytesAt_frame F₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.td.symm) (by omega_arith), m₆,
      Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]) ht, length_bytesAt,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil]

/-- `vg_aes_ocb_seal`. -/
theorem seal_wp (v : BlocksImpl) {s : State} (h : sealPreX s) :
    WP isa («seal» (callees v)) s fun s' => gprPreserved s s' ∧ sealX86_64.post s s' :=
  seal_wp' v (sealArgs_of h) (covers_of_mem (by rw [h.2.1]; simp)) rfl rfl (ofNat_toNat64 _).symm rfl
    (ofNat_toNat64 _).symm rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesOcb.X86_64
