import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.AesGcm.AArch64.Body
import VerifiedGarbage.Proof.Ocb.Stretch32
import VerifiedGarbage.Impl.AesOcb.AArch64
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.CmacAes.AArch64.Verified
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesOcb.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Contract`. -/
section

/-!
# AES-OCB on AArch64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ocb/Contract.lean`, with the working space as a
last argument (`Proof/AesOcb/Scratch.lean`), which imply these
(`Verified.lean`). A call (`bl`) stores nothing in memory, so no stack is
used; `seal` and `open` read `tag`, `tag_len` and `work` from the stack,
which they may only read.
-/

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (ctxCiph ctxInv ctxLstar encryptWith decryptWith lengthsOk zeros KeyRepr)

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 12 ∨ r.toNat = 14

/-- The key context. -/
abbrev aCtx (s : State) : Region := ⟨s.gpr .x0, 256⟩

/-- The nonce. -/
abbrev aNonce (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩

/-- The associated data. -/
abbrev aAad (s : State) : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩

/-- The data. -/
abbrev aData (s : State) : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩

/-- The tag. -/
abbrev aTag (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩

/-- The working space. -/
abbrev aWork (s : State) : Region := ⟨stackArg s 2, 2560⟩

/-- What `vg_aes_ocb_seal` and `vg_aes_ocb_open` need of their arguments
`(ctx = x0, rounds = x1, nonce = x2, nonce_len = x3, aad = x4, aad_len = x5,
data = x6, len = x7, tag = [sp], tag_len = [sp + 8], work = [sp + 16])`, but
for what they may access. -/
def oneFacts (s : State) : Prop :=
  (VG.Proof.AesOcb.AArch64.aCtx s).Disjoint (VG.Proof.AesOcb.AArch64.aData s) ∧ (VG.Proof.AesOcb.AArch64.aCtx s).Disjoint (VG.Proof.AesOcb.AArch64.aWork s) ∧ (VG.Proof.AesOcb.AArch64.aNonce s).Disjoint (VG.Proof.AesOcb.AArch64.aData s) ∧
    (VG.Proof.AesOcb.AArch64.aNonce s).Disjoint (VG.Proof.AesOcb.AArch64.aWork s) ∧ (VG.Proof.AesOcb.AArch64.aAad s).Disjoint (VG.Proof.AesOcb.AArch64.aData s) ∧ (VG.Proof.AesOcb.AArch64.aAad s).Disjoint (VG.Proof.AesOcb.AArch64.aWork s) ∧
    (VG.Proof.AesOcb.AArch64.aTag s).Disjoint (VG.Proof.AesOcb.AArch64.aData s) ∧ (VG.Proof.AesOcb.AArch64.aTag s).Disjoint (VG.Proof.AesOcb.AArch64.aWork s) ∧
    (VG.Proof.AesOcb.AArch64.aData s).Disjoint (VG.Proof.AesOcb.AArch64.aWork s) ∧ (VG.Proof.AesOcb.AArch64.aData s).Disjoint (VG.Proof.AesOcb.AArch64.args s 3) ∧ (VG.Proof.AesOcb.AArch64.aWork s).Disjoint (VG.Proof.AesOcb.AArch64.args s 3) ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + 2560 ≤ 2 ^ 64 ∧ s.sp.toNat + 24 ≤ 2 ^ 64 ∧ VG.Proof.AesOcb.AArch64.rounds (s.gpr .x1) ∧
    lengthsOk (stackArg s 1).toNat (s.gpr .x3).toNat = true

/-- What `vg_aes_ocb_seal` needs: it may write the data, the tag and the
working space. -/
def sealPreA (s : State) : Prop :=
  s.rd = [VG.Proof.AesOcb.AArch64.aCtx s, VG.Proof.AesOcb.AArch64.aNonce s, VG.Proof.AesOcb.AArch64.aAad s, VG.Proof.AesOcb.AArch64.args s 3] ∧ s.wr = [VG.Proof.AesOcb.AArch64.aData s, VG.Proof.AesOcb.AArch64.aTag s, VG.Proof.AesOcb.AArch64.aWork s] ∧
    (VG.Proof.AesOcb.AArch64.aTag s).Disjoint (VG.Proof.AesOcb.AArch64.args s 3) ∧ (VG.Proof.AesOcb.AArch64.aCtx s).Disjoint (VG.Proof.AesOcb.AArch64.aTag s) ∧ (VG.Proof.AesOcb.AArch64.aNonce s).Disjoint (VG.Proof.AesOcb.AArch64.aTag s) ∧
    (VG.Proof.AesOcb.AArch64.aAad s).Disjoint (VG.Proof.AesOcb.AArch64.aTag s) ∧ VG.Proof.AesOcb.AArch64.oneFacts s

/-- What `vg_aes_ocb_open` needs: it may write the data and the working
space, and read the tag. -/
def openPreA (s : State) : Prop :=
  s.rd = [VG.Proof.AesOcb.AArch64.aCtx s, VG.Proof.AesOcb.AArch64.aNonce s, VG.Proof.AesOcb.AArch64.aAad s, VG.Proof.AesOcb.AArch64.aTag s, VG.Proof.AesOcb.AArch64.args s 3] ∧ s.wr = [VG.Proof.AesOcb.AArch64.aData s, VG.Proof.AesOcb.AArch64.aWork s] ∧ VG.Proof.AesOcb.AArch64.oneFacts s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧ ∀ i < 3, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_ocb_seal`. -/
def sealAArch64 : Contract isa where
  pre := VG.Proof.AesOcb.AArch64.sealPreA
  post s s' :=
    VG.Spec.Ocb.encryptWith (VG.Spec.Ocb.ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxLstar s.mem (s.gpr .x0)) (stackArg s 1).toNat
        (VG.Spec.Aes.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (VG.Spec.Aes.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (VG.Spec.Aes.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat) =
      (VG.Spec.Aes.bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat, VG.Spec.Aes.bytesAt s'.mem (stackArg s 0) (stackArg s 1).toNat)
  pub := VG.Proof.AesOcb.AArch64.onePub

/-- `OCB-DECRYPT` of what `vg_aes_ocb_open` is given. -/
def openOut (s : State) : Option (List Byte) :=
  VG.Spec.Ocb.decryptWith (VG.Spec.Ocb.ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxInv s.mem (s.gpr .x0) (s.gpr .x1).toNat)
    (ctxLstar s.mem (s.gpr .x0)) (stackArg s 1).toNat (VG.Spec.Aes.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    (VG.Spec.Aes.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (VG.Spec.Aes.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
    (VG.Spec.Aes.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- What `vg_aes_ocb_open` may leak (`Spec.Ocb.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬VG.Proof.AesOcb.AArch64.rounds (s.gpr .x1) then [] else [if (VG.Proof.AesOcb.AArch64.openOut s).isSome then 1 else 0]

/-- `vg_aes_ocb_open`. -/
def openAArch64 : Contract isa where
  pre := VG.Proof.AesOcb.AArch64.openPreA
  post s s' :=
    match VG.Proof.AesOcb.AArch64.openOut s with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ VG.Spec.Aes.bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ VG.Spec.Aes.bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat = VG.Spec.Ocb.zeros (s.gpr .x7).toNat
  pub s₁ s₂ := VG.Proof.AesOcb.AArch64.onePub s₁ s₂ ∧ VG.Proof.AesOcb.AArch64.openLeak s₁ = VG.Proof.AesOcb.AArch64.openLeak s₂

/-- `vg_aes_ocb_init(key = x0, key_len = x1, ctx = x2, scratch = x3)`. -/
def initAArch64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let ctx : Region := ⟨s.gpr .x2, 256⟩
    let scr : Region := ⟨s.gpr .x3, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (s.gpr .x2).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 16 ∨ (s.gpr .x1).toNat = 24 ∨ (s.gpr .x1).toNat = 32)
  post s s' := VG.Spec.Ocb.KeyRepr s'.mem (s.gpr .x2) (VG.Spec.Aes.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Env`. -/
section

/-!
# AES-OCB on AArch64: where everything is

Untrusted: everything here is checked by Lean. The key context (256 bytes
at `K`) and the working space (2560 bytes at `W`) (`Lay`); what a state may
access (`Perm`); the registers holding `W`, `K`, the data `D`, the rounds
`R` and the data's length `n` throughout, and the stack pointer (`Env`); the
public arguments the entry keeps in `W` (`Slots`). The pieces write the
parts of `W` in `mutR` (and the data), so the slots and our caller's
registers saved in `W` stay as the entry left them. `orun` runs a block
symbolically.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (covers_off in_off in_left covers_left)

theorem write8 (m : Mem) (a : Addr) (v : BitVec (8 * 8)) : m.write a 8 v = m.writeW a v := by
  simp [Mem.writeW]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp [Mem.readW]

theorem imm_lit (k : Nat) (h : k < 2 ^ 16) : BitVec.setWidth 64 (BitVec.ofNat 16 k) <<< (16 * 0) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- Runs a block of the instructions the AES-OCB code uses. -/
macro "orun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.AArch64.addr,
    State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write,
    sp_write, ite_true, ite_false, Option.bind_some, Option.map_some, BitVec.setWidth_eq, and_self,
    Impl.AesGcm.AArch64.mov, Impl.AesGcm.AArch64.ptr, Impl.AesGcm.AArch64.imm, ld, st,
    tagO, ofsO, ckO, sumO, ldO, l0O, lO, tmpO, t2O, ohO, savO, tlO, aadO, alenO, nO, nlO, botO, o0O, bufO, scrO,
    List.cons_append, List.nil_append, List.append_assoc, reduceCtorEq, ↓reduceIte, Nat.reduceLT,
    Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
    and_true, true_and, eq_self_iff_true, write8, read8, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.add_zero, $ts,*]) <;> try rfl)

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons x a ih =>
    show (VG.AArch64.exec x s).bind (runBlock isa (a ++ b)) = ((VG.AArch64.exec x s).bind (runBlock isa a)).bind (runBlock isa b)
    rw [Option.bind_assoc]
    congr 1
    funext u
    exact ih u

/-! ## The regions -/

/-- The key context and `W`. -/
structure Lay (K W : Addr) : Prop where
  kw : K.toNat + 256 ≤ 2 ^ 64
  ww : W.toNat + 2560 ≤ 2 ^ 64
  k_w : (⟨K, 256⟩ : Region).Disjoint ⟨W, 2560⟩

/-- What a state may access. -/
structure Perm (K W : Addr) (s : State) : Prop where
  k : Covers [⟨K, 256⟩] (s.rd ++ s.wr)
  w : Covers [⟨W, 2560⟩] s.wr

/-- The registers holding `W`, the key context, the data, the rounds and the
data's length, the stack pointer, and what the state may access. -/
structure Env (K W D : Addr) (R n : Nat) (SP : Addr) (s : State) : Prop where
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = K
  x21 : s.gpr .x21 = D
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  x28 : s.gpr .x28 = BitVec.ofNat 64 n
  sp : s.sp = SP
  perm : VG.Proof.AesOcb.AArch64.Perm K W s

/-- The registers `Env` fixes. -/
abbrev envRegs : List Reg := [.x19, .x20, .x21, .x22, .x28]

theorem Perm.of_eq {K W : Addr} {s s' : State} (h : VG.Proof.AesOcb.AArch64.Perm K W s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesOcb.AArch64.Perm K W s' := ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps its registers, the stack pointer
and the permissions. -/
theorem Env.keep {K W D : Addr} {R n : Nat} {SP : Addr} {s s' : State} (h : VG.Proof.AesOcb.AArch64.Env K W D R n SP s)
    (hg : ∀ r ∈ VG.Proof.AesOcb.AArch64.envRegs, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesOcb.AArch64.Env K W D R n SP s' :=
  ⟨by rw [hg _ (by simp), h.x19], by rw [hg _ (by simp), h.x20], by rw [hg _ (by simp), h.x21],
    by rw [hg _ (by simp), h.x22], by rw [hg _ (by simp), h.x28], by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- An environment, after code that writes only the registers `rs`. -/
theorem Env.others {K W D : Addr} {R n : Nat} {SP : Addr} {s s' : State} (h : VG.Proof.AesOcb.AArch64.Env K W D R n SP s)
    {rs : List Reg} (hg : ∀ r, r ∉ rs → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hd : ∀ r ∈ VG.Proof.AesOcb.AArch64.envRegs, r ∉ rs := by decide) : VG.Proof.AesOcb.AArch64.Env K W D R n SP s' :=
  h.keep (fun r hr => hg r (hd r hr)) hsp hrd hwr

/-- An environment, after a call. -/
theorem Env.of_saved {K W D : Addr} {R n : Nat} {SP : Addr} {s s' : State} (h : VG.Proof.AesOcb.AArch64.Env K W D R n SP s)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesOcb.AArch64.Env K W D R n SP s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

namespace Lay

theorem kSub {K : Addr} {d n : Nat} (h : d + n ≤ 256) : Region.Sub ⟨K + BitVec.ofNat 64 d, n⟩ ⟨K, 256⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

variable {K W : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

theorem k_w' {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 2560) :
    (⟨K + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  (L.k_w.sub_left (VG.Proof.AesOcb.AArch64.Lay.kSub ha)).sub_right (VG.Proof.AesOcb.AArch64.Lay.wSub hd)

end Lay

namespace Perm

variable {K W : Addr} {s : State} (P : VG.Proof.AesOcb.AArch64.Perm K W s)
include P

theorem kR {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 d) n :=
  in_off P.k h (by decide)

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem kC {d n : Nat} (h : d + n ≤ 256) : Covers [⟨K + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_off P.k h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at `D` that the code may read, apart from `W`. -/
structure Buf (W : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  lt : n < 2 ^ 64
  wrap : D.toNat + n ≤ 2 ^ 64
  w : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩

namespace Buf

variable {W : Addr} {s : State} {D : Addr} {n : Nat} (h : VG.Proof.AesOcb.AArch64.Buf W s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesOcb.AArch64.Buf W s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : VG.Proof.AesOcb.AArch64.Buf W s (D + BitVec.ofNat 64 k) (n - k) where
  rd := covers_off h.rd (by omega) h.lt
  lt := by have := h.lt; omega
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega)]
    have := Nat.mod_le (D.toNat + k) (2 ^ 64)
    omega
  w := h.w.sub_left (Offset.sub_base D (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : VG.Proof.AesOcb.AArch64.Buf W s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  w := h.w.sub_left (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : VG.Proof.AesOcb.AArch64.Buf W s (D + BitVec.ofNat 64 a) k :=
  (h.drop (k := a) (by omega)).take (by omega)

end Buf

/-- The data: a buffer that the code may also write, apart from the key
context. -/
structure DBuf (K W : Addr) (s : State) (D : Addr) (n : Nat) : Prop extends VG.Proof.AesOcb.AArch64.Buf W s D n where
  wr : Covers [⟨D, n⟩] s.wr
  k : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩

namespace DBuf

variable {K W : Addr} {s : State} {D : Addr} {n : Nat} (h : VG.Proof.AesOcb.AArch64.DBuf K W s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesOcb.AArch64.DBuf K W s' D n :=
  { h.toBuf.of_eq hrd hwr with wr := by rw [hwr]; exact h.wr, k := h.k }

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : VG.Proof.AesOcb.AArch64.DBuf K W s (D + BitVec.ofNat 64 a) k where
  toBuf := h.toBuf.slice hk
  wr := fun x m hx => covers_off h.wr (d := a) (n := k) hk h.lt x m hx
  k := h.k.sub_right ((Offset.sub_base D (by omega)))

end DBuf

/-! ## The slots -/

/-- The public values the entry keeps in `W`: the tag length, the associated
data and its length, the nonce and its length. -/
structure Slots (W : Addr) (N A : Addr) (nl al tl : Nat) (m : Mem) : Prop where
  tl : m.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl
  aad : m.readW (W + BitVec.ofNat 64 aadO) 64 = A
  alen : m.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 al
  nonce : m.readW (W + BitVec.ofNat 64 nO) 64 = N
  nlen : m.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl

/-- The parts of `W` the pieces write: `[0, 160)` and `[288, 2560)`. -/
abbrev wA (W : Addr) : Region := ⟨W, 160⟩
abbrev wB (W : Addr) : Region := ⟨W + BitVec.ofNat 64 288, 2272⟩

/-- What the pieces may change: those parts of `W` and the data. -/
abbrev mutR (W D : Addr) (n : Nat) : List Region := [VG.Proof.AesOcb.AArch64.wA W, VG.Proof.AesOcb.AArch64.wB W, ⟨D, n⟩]

theorem sub_wA {W : Addr} {d k : Nat} (h : d + k ≤ 160) : Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ (VG.Proof.AesOcb.AArch64.wA W) := by
  simpa using Offset.sub W (d := d) (n := k) (e := 0) (k := 160) (by omega) (by omega)

theorem sub_wB {W : Addr} {d k : Nat} (h₁ : 288 ≤ d) (h : d + k ≤ 2560) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ (VG.Proof.AesOcb.AArch64.wB W) := Offset.sub W (by omega) (by omega)

/-- A part of `W` within `[0, 160)`, as a part the pieces may write. -/
theorem in_mutA {W D : Addr} {n d k : Nat} (h : d + k ≤ 160) :
    ∃ r' ∈ VG.Proof.AesOcb.AArch64.mutR W D n, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' := ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.AArch64.sub_wA h⟩

/-- A part of `W` from 288 on, as a part the pieces may write. -/
theorem in_mutB {W D : Addr} {n d k : Nat} (h₁ : 288 ≤ d) (h : d + k ≤ 2560) :
    ∃ r' ∈ VG.Proof.AesOcb.AArch64.mutR W D n, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), VG.Proof.AesOcb.AArch64.sub_wB h₁ h⟩

/-- The data, as a part the pieces may write. -/
theorem in_mutD {W D : Addr} {n : Nat} {r : Region} (h : Region.Sub r ⟨D, n⟩) :
    ∃ r' ∈ VG.Proof.AesOcb.AArch64.mutR W D n, Region.Sub r r' := ⟨_, by simp, h⟩

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {K W D : Addr} {n : Nat} (L : VG.Proof.AesOcb.AArch64.Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {d k : Nat} (hd : 160 ≤ d ∧ d + k ≤ 288) :
    ∀ r ∈ VG.Proof.AesOcb.AArch64.mutR W D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := k) (d := 0) (k := 160) (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (hD.sub_right (Lay.wSub (by omega))).symm

/-- The key context misses the parts the pieces write. -/
theorem k_mut {K W D : Addr} {n : Nat} (L : VG.Proof.AesOcb.AArch64.Lay K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ r ∈ VG.Proof.AesOcb.AArch64.mutR W D n, (⟨K, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.k_w.sub_right (Region.sub_prefix (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact hD

/-- A word of `W` that the pieces do not write. -/
theorem kept_read {K W D : Addr} {n : Nat} (L : VG.Proof.AesOcb.AArch64.Lay K W) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {m m' : Mem} (h : Frame (VG.Proof.AesOcb.AArch64.mutR W D n) m m') {d : Nat} (hd : 160 ≤ d ∧ d + 8 ≤ 288) :
    m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  h.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (VG.Proof.AesOcb.AArch64.kept_mut L hDW hd) (by decide)

/-- The slots, after a frame within the parts the pieces write. -/
theorem Slots.of_mut {K W D : Addr} {n : Nat} (L : VG.Proof.AesOcb.AArch64.Lay K W) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {m m' : Mem} (h : Frame (VG.Proof.AesOcb.AArch64.mutR W D n) m m') {N A : Addr} {nl al tl : Nat}
    (S : VG.Proof.AesOcb.AArch64.Slots W N A nl al tl m) : VG.Proof.AesOcb.AArch64.Slots W N A nl al tl m' where
  tl := by rw [VG.Proof.AesOcb.AArch64.kept_read L hDW h (by decide), S.tl]
  aad := by rw [VG.Proof.AesOcb.AArch64.kept_read L hDW h (by decide), S.aad]
  alen := by rw [VG.Proof.AesOcb.AArch64.kept_read L hDW h (by decide), S.alen]
  nonce := by rw [VG.Proof.AesOcb.AArch64.kept_read L hDW h (by decide), S.nonce]
  nlen := by rw [VG.Proof.AesOcb.AArch64.kept_read L hDW h (by decide), S.nlen]

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Words`. -/
section

/-!
# AES-OCB on AArch64: blocks of `W`, two words at a time

Untrusted: everything here is checked by Lean. `zero16`, `copy16`, `xor16`
and `dbl` write a block of `W` (`BlkStep`): zeros, a copy, the XOR with a
block and `double` of a block (`zero16_ok`, `copy16_ok`, `xor16_ok`,
`dbl_ok`), as blocks of memory (`blockAtMem`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Ocb (Block blockAtMem double)
open VG.Proof.Cmac (le8 le8_readW xor_words bytesAt_store2)
open VG.Proof.AesGcm.AArch64 (in_left)

/-- What a step writing the block at `W + d` does: it writes only there,
the block `v`, and keeps the registers but `clob`. -/
structure BlkStep (W : Addr) (d : Nat) (v : Block) (clob : List Reg) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (W + BitVec.ofNat 64 d) = v
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

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

theorem addr8 (p : Addr) (d : Nat) : p + BitVec.ofNat 64 d + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (d + 8) :=
  Offset.add_add p d 8

theorem imm0 : BitVec.setWidth 64 (BitVec.ofNat 16 0) <<< (16 * 0) = (0 : BitVec 64) := by decide

/-- `zero16 d`: `W + d ← 0`. -/
theorem zero16_ok {W : Addr} {s : State} {d : Nat} (hd : d % 8 = 0 ∧ d + 8 < 32768) (h19 : s.gpr .x19 = W)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (zero16 d) s = some s' ∧ VG.Proof.AesOcb.AArch64.BlkStep W d 0 [.x9] s s' := by
  refine ⟨_, by orun [zero16, h19, w₀, w₁, hd.1, Nat.add_mod_right, show d < 32768 by omega, hd.2], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [VG.Proof.AesOcb.AArch64.imm0]; rw [← VG.Proof.AesOcb.AArch64.addr8 W d]; exact Proof.Cmac.frame_store2 _ _ _
  · simp only [VG.Proof.AesOcb.AArch64.imm0]; rw [← VG.Proof.AesOcb.AArch64.addr8 W d, VG.Proof.AesOcb.AArch64.blockAtMem_store2]; decide
  · simp only [List.mem_singleton] at hr
    simp only [gpr_write, hr, ite_false]

/-- `copy16 a d`: `W + d ← W + a`. -/
theorem copy16_ok {W : Addr} {s : State} {a d : Nat} (ha : a % 8 = 0 ∧ a + 8 < 32768)
    (hd : d % 8 = 0 ∧ d + 8 < 32768) (h19 : s.gpr .x19 = W)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (copy16 a d) s = some s' ∧
      VG.Proof.AesOcb.AArch64.BlkStep W d (blockAtMem s.mem (W + BitVec.ofNat 64 a)) [.x9, .x10] s s' := by
  refine ⟨_, by orun [copy16, h19, r₀, r₁, w₀, w₁, ha.1, hd.1, Nat.add_mod_right, show a < 32768 by omega,
    show d < 32768 by omega, ha.2, hd.2], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [← VG.Proof.AesOcb.AArch64.addr8 W d]; exact Proof.Cmac.frame_store2 _ _ _
  · rw [← VG.Proof.AesOcb.AArch64.addr8 W d, VG.Proof.AesOcb.AArch64.blockAtMem_store2, ← VG.Proof.AesOcb.AArch64.addr8 W a, VG.Proof.AesOcb.AArch64.blockAtMem_words]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2, ite_false]

/-- `xor16 b a d`: `W + d ← W + d ⊕ (B + a)`, `B` in `b`. -/
theorem xor16_ok {W B : Addr} {s : State} {b : Reg} {a d : Nat} (ha : a % 8 = 0 ∧ a + 8 < 32768)
    (hd : d % 8 = 0 ∧ d + 8 < 32768) (h19 : s.gpr .x19 = W) (hb : s.gpr b = B)
    (hb9 : b ≠ .x9) (hb10 : b ≠ .x10) (hb11 : b ≠ .x11)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (xor16 b a d) s = some s' ∧
      VG.Proof.AesOcb.AArch64.BlkStep W d (blockAtMem s.mem (W + BitVec.ofNat 64 d) ^^^ blockAtMem s.mem (B + BitVec.ofNat 64 a))
        [.x9, .x10, .x11, .x12] s s' := by
  have v₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 := in_left w₀
  have v₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (d + 8)) 8 := in_left w₁
  refine ⟨_, by orun [xor16, h19, hb, hb9, hb10, hb11, r₀, r₁, v₀, v₁, w₀, w₁, ha.1, hd.1, Nat.add_mod_right,
    show a < 32768 by omega, show d < 32768 by omega, ha.2, hd.2], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [← VG.Proof.AesOcb.AArch64.addr8 W d]; exact Proof.Cmac.frame_store2 _ _ _
  · rw [← VG.Proof.AesOcb.AArch64.addr8 W d, VG.Proof.AesOcb.AArch64.blockAtMem_store2, ← VG.Proof.AesOcb.AArch64.addr8 B a, VG.Proof.AesOcb.AArch64.blockAtMem_xor_words]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- `double` of the block at `p`, from its byte-reversed words. -/
theorem dbl_mem (m : Mem) (p : Addr) :
    let hi := rev64 (m.readW p 64)
    let lo := rev64 (m.readW (p + BitVec.ofNat 64 8) 64)
    Spec.Ocb.ofBytes (le8 (rev64 (Proof.CmacAes.AArch64.dblHi hi lo)) ++
      le8 (rev64 (Proof.CmacAes.AArch64.dblLo hi lo))) = double (blockAtMem m p) := by
  intro hi lo
  rw [Proof.CmacAes.AArch64.le8_rev, ← Proof.Ocb.toBytes_eq, Proof.Ocb.ofBytes_toBytes,
    Proof.CmacAes.AArch64.dbl_words, Proof.Ocb.double_eq]
  congr 1
  have e0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p
  have := Proof.Gcm.AArch64.blockAt_rev m p
  rw [e0] at this
  exact this

/-- `dbl b a d`: `W + d ← double(B + a)`, `B` in `b`. -/
theorem dbl_ok {W B : Addr} {s : State} {b : Reg} {a d : Nat} (ha : a % 8 = 0 ∧ a + 8 < 32768)
    (hd : d % 8 = 0 ∧ d + 8 < 32768) (h19 : s.gpr .x19 = W) (hb : s.gpr b = B) (hb9 : b ≠ .x9)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (dbl b a d) s = some s' ∧
      VG.Proof.AesOcb.AArch64.BlkStep W d (double (blockAtMem s.mem (B + BitVec.ofNat 64 a))) [.x9, .x10, .x11, .x12, .x13] s s' := by
  refine ⟨_, by orun [dbl, h19, hb, hb9, r₀, r₁, w₀, w₁, ha.1, hd.1, Nat.add_mod_right,
    show a < 32768 by omega, show d < 32768 by omega, ha.2, hd.2], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [← VG.Proof.AesOcb.AArch64.addr8 W d]; exact Proof.Cmac.frame_store2 _ _ _
  · rw [← VG.Proof.AesOcb.AArch64.addr8 W d, VG.Proof.AesOcb.AArch64.blockAtMem_store2, ← VG.Proof.AesOcb.AArch64.addr8 B a]
    exact VG.Proof.AesOcb.AArch64.dbl_mem _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Callee`. -/
section

/-!
# AES-OCB on AArch64: the functions called

Untrusted: everything here is checked by Lean. Calls of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` (of any implementation
`v`) from their contract (with `WP.call`): what they need (`BCall`), what
they leave (`BPost`), and that two calls with the same arguments leak the
same (`blk_rel`). A block the call transforms is `ENCIPHER` (or `DECIPHER`)
of the key schedule (`BPost.enc`, `BPost.dec`), as OCB's blocks in memory
(`blockAtMem`). `vg_aes_expand_key_scratch` is called as AES-GCM calls it
(`keyImpl`, with `Proof.AesGcm.AArch64.key_call`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem aesWith aesInvWith)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (toNat_ofNat_lt toNat_rounds callEntry_x0 callEntry_x1 callEntry_x2 callEntry_x3
  callEntry_x4)
open VG.Proof.Ocb (blockAtMem_of_state stateAt_of_statesAt)

/-- The implementation of `vg_aes_expand_key_scratch` that goes with `v`, as AES-GCM's
proofs take it. -/
def keyImpl (v : BlocksImpl) : Proof.AesGcm.AArch64.KeyImpl where
  fn := ⟨v.expand.name, v.expand.code⟩
  noFrames := v.expandNoFrames
  ok := v.expandOk
  ct := v.expandCt
  keepsV := v.expandKeepsV

/-- What a call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` needs:
the key schedule at `K` for `R` rounds, `n` blocks at `D` and working space
at `S`. -/
structure BCall (s : State) (K D S : Addr) (R n : Nat) : Prop where
  x0 : s.gpr .x0 = K
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = D
  x3 : s.gpr .x3 = BitVec.ofNat 64 n
  x4 : s.gpr .x4 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  kd : (⟨K, 240⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ks : (⟨K, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2048⟩
  reads : Covers ([⟨K, 240⟩] ++ [⟨D, 16 * n⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨D, 16 * n⟩, ⟨S, 2048⟩] s.wr

/-- What a call of a function with the contract `blocksAArch64 f` leaves. -/
structure BPost (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s : State) (K D S : Addr) (R n : Nat)
    (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨D, 16 * n⟩, ⟨S, 2048⟩] s.mem s'.mem
  out : Spec.Aes.statesAt s'.mem D n = (Spec.Aes.statesAt s.mem D n).map (f R (bytesAt s.mem K (16 * (R + 1))))

theorem BCall.n_lt {s : State} {K D S : Addr} {R n : Nat} (h : VG.Proof.AesOcb.AArch64.BCall s K D S R n) : n < 2 ^ 64 := by
  have := h.wrap; omega

theorem BCall.pre {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State} {K D S : Addr} {R n : Nat}
    (h : VG.Proof.AesOcb.AArch64.BCall s K D S R n) :
    (Proof.Aes.blocksAArch64 f).pre (s.callEntry.withRegions [⟨K, 240⟩] [⟨D, 16 * n⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_lt h.n_lt
  simp only [Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4,
    h.x0, h.x1, h.x2, h.x3, h.x4, hR, hn]
  exact ⟨trivial, trivial, h.kd, h.ks, h.ds, h.wrap, h.rounds⟩

theorem blk_call {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : c.noFrames = true) {s : State} {K D S : Addr} {R n : Nat} (h : VG.Proof.AesOcb.AArch64.BCall s K D S R n) :
    WP isa (.call name c) s (VG.Proof.AesOcb.AArch64.BPost f s K D S R n) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_lt h.n_lt
  refine WP.call (k := Proof.Aes.blocksAArch64 f) ok (rd := [⟨K, 240⟩])
    (wr := [⟨D, 16 * n⟩, ⟨S, 2048⟩]) h.pre h.reads h.writes ?_ nf
  intro s' hrd hwr hsp hf hsaved _ hpost
  simp only [Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, h.x0, h.x1, h.x2, h.x3, hR, hn] at hpost
  exact ⟨hrd, hwr, hsp, hsaved, hf, hpost⟩

/-- Block `i` after `vg_aes_encrypt_blocks`. -/
theorem BPost.enc {s s' : State} {K D S : Addr} {R n : Nat} (h : VG.Proof.AesOcb.AArch64.BPost Spec.Aes.cipher s K D S R n s') {i : Nat}
    (hi : i < n) :
    blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      aesWith R (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) :=
  blockAtMem_of_state _ (stateAt_of_statesAt h.out hi)

/-- Block `i` after `vg_aes_decrypt_blocks`. -/
theorem BPost.dec {s s' : State} {K D S : Addr} {R n : Nat} (h : VG.Proof.AesOcb.AArch64.BPost Spec.Aes.invCipher s K D S R n s') {i : Nat}
    (hi : i < n) :
    blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      aesInvWith R (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) :=
  blockAtMem_of_state _ (stateAt_of_statesAt h.out hi)

/-- The one block of a call on one block. -/
theorem BPost.enc0 {s s' : State} {K D S : Addr} {R : Nat} (h : VG.Proof.AesOcb.AArch64.BPost Spec.Aes.cipher s K D S R 1 s') :
    blockAtMem s'.mem D = aesWith R (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem D) := by
  have := h.enc (i := 0) (by decide)
  simpa using this

theorem blk_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub c)
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K D S : Addr, ∃ R n : Nat,
      VG.Proof.AesOcb.AArch64.BCall s₁ K D S R n ∧ VG.Proof.AesOcb.AArch64.BCall s₂ K D S R n ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call name c) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨K, D, S, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine RelCT.call (P := fun a b => a = s₁ ∧ b = s₂) ok ct [⟨K, 240⟩] [⟨D, 16 * n⟩, ⟨S, 2048⟩]
    (fun a b hab => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  obtain ⟨rfl, rfl⟩ := hab
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Args`. -/
section

/-!
# AES-OCB on AArch64: the calls of the block functions

Untrusted: everything here is checked by Lean. `callBlocks b args` sets up
a call of `b` (`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks`) with the
key schedule of the key context, the rounds in `x22`, the `n` blocks at `D`
that `args` sets (`Dst`: blocks of `W` below 512, `dstW`, or the data,
`dstD`) and the working space at `W + 512` (`callBlocks_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (covers_left covers_cons covers_nil covers_append covers_off covers_prefix)
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- The functions an instance calls. -/
def callees (v : BlocksImpl) : Callees := ⟨v.enc, v.dec, v.expand⟩

/-- `n` blocks at `D` for a call: apart from the key context and the working
space at `W + 512`, and readable and writable. -/
structure Dst (K W : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  k : (⟨K, 256⟩ : Region).Disjoint ⟨D, 16 * n⟩
  scr : (⟨D, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩
  rd : Covers [⟨D, 16 * n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, 16 * n⟩] s.wr

theorem toNat_W {W : Addr} (hw : W.toNat + 2560 ≤ 2 ^ 64) {d : Nat} (hd : d < 2560) :
    (W + BitVec.ofNat 64 d).toNat = W.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Blocks of `W` below 512. -/
theorem dstW {K W : Addr} {s : State} (L : VG.Proof.AesOcb.AArch64.Lay K W) (P : VG.Proof.AesOcb.AArch64.Perm K W s) {d n : Nat} (h : d + 16 * n ≤ 512) :
    VG.Proof.AesOcb.AArch64.Dst K W s (W + BitVec.ofNat 64 d) n where
  wrap := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt (W + BitVec.ofNat 64 d).isLt
    · rw [VG.Proof.AesOcb.AArch64.toNat_W L.ww (by omega)]; have := L.ww; omega
  k := L.k_w.sub_right (Lay.wSub (by omega))
  scr := L.w_w (.inl (by omega)) (by omega) (by decide)
  rd := covers_left (P.wC (by omega))
  wr := P.wC (by omega)

/-- Blocks of the data. -/
theorem dstD {K W : Addr} {s : State} {D : Addr} {n : Nat} (h : VG.Proof.AesOcb.AArch64.DBuf K W s D (16 * n)) : VG.Proof.AesOcb.AArch64.Dst K W s D n where
  wrap := h.wrap
  k := h.k
  scr := h.w.sub_right (Lay.wSub (by decide))
  rd := h.rd
  wr := h.wr

theorem Dst.of_eq {K W : Addr} {s s' : State} {D : Addr} {n : Nat} (h : VG.Proof.AesOcb.AArch64.Dst K W s D n)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesOcb.AArch64.Dst K W s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd, wr := by rw [hwr]; exact h.wr }

/-- What the arguments `args` of a call set: `x2` and `x3` (to `D` and `n`),
and nothing else. -/
def ArgsOk (args : List Instr) (s : State) (D : Addr) (n : Nat) : Prop :=
  ∃ s₁, runBlock isa args s = some s₁ ∧ s₁.gpr .x2 = D ∧ s₁.gpr .x3 = BitVec.ofNat 64 n ∧
    (∀ r, r ≠ .x2 → r ≠ .x3 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧
    s₁.wr = s.wr

/-- One block at `W + d`. -/
theorem oneBlock_ok {W : Addr} {s : State} (h19 : s.gpr .x19 = W) (d : Nat) (hd : d < 4096) :
    VG.Proof.AesOcb.AArch64.ArgsOk (oneBlock d) s (W + BitVec.ofNat 64 d) 1 := by
  refine ⟨_, by orun [oneBlock, h19, hd], ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write]
  · simp [gpr_write, VG.Proof.AesOcb.AArch64.imm_lit 1 (by decide)]
  · simp [gpr_write, h1, h2]
  all_goals rfl

theorem BPost.congr {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ s s' : State} {K D S : Addr}
    {R n : Nat} (h : VG.Proof.AesOcb.AArch64.BPost f s K D S R n s') (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → s.gpr r = s₀.gpr r) (hsp : s.sp = s₀.sp) :
    VG.Proof.AesOcb.AArch64.BPost f s₀ K D S R n s' where
  rd := by rw [h.rd, hrd]
  wr := by rw [h.wr, hwr]
  sp := by rw [h.sp, hsp]
  saved r hr h30 := by rw [h.saved r hr h30, hg r hr h30]
  frame := by rw [← hm]; exact h.frame
  out := by rw [← hm]; exact h.out

/-- The arguments of a call of `b`, after `args`. -/
theorem callArgs_ok {K W D : Addr} {R n : Nat} {SP : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {s : State}
    (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP s) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {args : List Instr} {D' : Addr} {k : Nat} (ha : VG.Proof.AesOcb.AArch64.ArgsOk args s D' k) (hD : VG.Proof.AesOcb.AArch64.Dst K W s D' k) :
    WP isa (.block (args ++ [Impl.AesGcm.AArch64.mov .x0 .x20, Impl.AesGcm.AArch64.mov .x1 .x22,
        Impl.AesGcm.AArch64.ptr .x4 .x19 scrO])) s fun s₂ =>
      VG.Proof.AesOcb.AArch64.BCall s₂ K D' (W + BitVec.ofNat 64 512) R k ∧ s₂.mem = s.mem ∧ s₂.sp = s.sp ∧ s₂.rd = s.rd ∧
        s₂.wr = s.wr ∧ ∀ r ∈ preserved, r ≠ .x30 → s₂.gpr r = s.gpr r := by
  obtain ⟨s₁, run₁, x2₁, x3₁, g₁, m₁, sp₁, rd₁, wr₁⟩ := ha
  have h19 : s₁.gpr .x19 = W := by rw [g₁ _ (by decide) (by decide), E.x19]
  have h20 : s₁.gpr .x20 = K := by rw [g₁ _ (by decide) (by decide), E.x20]
  have h22 : s₁.gpr .x22 = BitVec.ofNat 64 R := by rw [g₁ _ (by decide) (by decide), E.x22]
  obtain ⟨s₂, run₂, x0₂, x1₂, x2₂, x3₂, x4₂, g₂, m₂, sp₂, rd₂, wr₂⟩ : ∃ s₂,
      runBlock isa [Impl.AesGcm.AArch64.mov .x0 .x20, Impl.AesGcm.AArch64.mov .x1 .x22,
        Impl.AesGcm.AArch64.ptr .x4 .x19 scrO] s₁ = some s₂ ∧
      s₂.gpr .x0 = K ∧ s₂.gpr .x1 = BitVec.ofNat 64 R ∧ s₂.gpr .x2 = D' ∧ s₂.gpr .x3 = BitVec.ofNat 64 k ∧
      s₂.gpr .x4 = W + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x4 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.sp = s₁.sp ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by orun [], ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, h20]
    · simp [gpr_write, h22]
    · simp [gpr_write, x2₁]
    · simp [gpr_write, x3₁]
    · simp [gpr_write, h19]
    · simp [gpr_write, h1, h2, h3]
    all_goals rfl
  have hD₂ := hD.of_eq (s' := s₂) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have hc : VG.Proof.AesOcb.AArch64.BCall s₂ K D' (W + BitVec.ofNat 64 512) R k :=
    { x0 := x0₂, x1 := x1₂, x2 := x2₂, x3 := x3₂, x4 := x4₂, rounds := hR, wrap := hD.wrap
      kd := hD.k.sub_left (Region.sub_prefix (by decide))
      ks := (L.k_w.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
      ds := hD.scr
      reads := covers_append (covers_cons (covers_prefix (by rw [rd₂, rd₁, wr₂, wr₁]; exact E.perm.k)
          (by decide)) covers_nil)
        (covers_cons hD₂.rd (covers_cons (covers_left (by rw [wr₂, wr₁]; exact E.perm.wC (by decide))) covers_nil))
      writes := covers_cons hD₂.wr (covers_cons (by rw [wr₂, wr₁]; exact E.perm.wC (by decide)) covers_nil) }
  refine WP.of_runBlock ⟨s₂, by rw [VG.Proof.AesOcb.AArch64.runBlock_append, run₁, Option.bind_some, run₂], hc,
    by rw [m₂, m₁], by rw [sp₂, sp₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun r hr h30 => ?_⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [g₂ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    g₁ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]

theorem callBlocks_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : b.code.noFrames = true)
    {K W D : Addr} {R n : Nat} {SP : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {s : State} (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP s)
    (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {args : List Instr} {D' : Addr} {k : Nat} (ha : VG.Proof.AesOcb.AArch64.ArgsOk args s D' k) (hD : VG.Proof.AesOcb.AArch64.Dst K W s D' k) :
    WP isa (callBlocks b args) s (VG.Proof.AesOcb.AArch64.BPost f s K D' (W + BitVec.ofNat 64 512) R k) :=
  WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.callArgs_ok L E hR ha hD) fun _ ⟨hc, m₂, sp₂, rd₂, wr₂, g₂⟩ =>
    WP.mono (VG.Proof.AesOcb.AArch64.blk_call ok nf hc) fun _ h => h.congr m₂ rd₂ wr₂ g₂ sp₂)

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.LNtz`. -/
section

/-!
# AES-OCB on AArch64: `L_{ntz(i)}` (`lNtz`)

Untrusted: everything here is checked by Lean. `lNtz` copies `L_0` to
`W + lO` and doubles it while the block index `i` (in `x25`), shifted right
once more each time (in `x11`), is even: `ntz(i)` times (`lNtz_ok`). The
invariant: after `j` doublings, `W + lO` holds `L_j`, `x11` is `i / 2^j`,
which is positive, and `ntz(i) = j + ntz(i / 2^j)`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Ocb (Block blockAtMem double lAt ntz)
open VG.Proof.AesGcm.AArch64 (eval_zero toNat_ofNat_of_lt)

theorem and1 {v : Nat} (hv : v < 2 ^ 64) : BitVec.ofNat 64 v &&& 1#64 = BitVec.ofNat 64 (v % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, VG.Proof.AesGcm.AArch64.toNat_ofNat_of_lt hv, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod,
    VG.Proof.AesGcm.AArch64.toNat_ofNat_of_lt (by omega)]

theorem shr1 {v : Nat} (hv : v < 2 ^ 64) : BitVec.ofNat 64 v >>> 1 = BitVec.ofNat 64 (v / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, VG.Proof.AesGcm.AArch64.toNat_ofNat_of_lt hv, VG.Proof.AesGcm.AArch64.toNat_ofNat_of_lt (by omega), Nat.shiftRight_eq_div_pow]

/-- The registers `lNtz` writes. -/
abbrev ntzRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14]

/-- What `lNtz` leaves. -/
structure LNtzPost (W : Addr) (l : Block) (i : Nat) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (W + BitVec.ofNat 64 lO) = lAt l (ntz i)
  gpr : ∀ r, r ∉ VG.Proof.AesOcb.AArch64.ntzRegs → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `x12 ← x14 ∧ 1`, after `x14 ← v`. -/
theorem low1_ok (s : State) {v : Nat} (hv : v < 2 ^ 64) (h14 : s.gpr .x14 = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa low1 s = some s' ∧ s'.gpr .x12 = BitVec.ofNat 64 (v % 2) ∧ s'.gpr .x14 = BitVec.ofNat 64 v ∧
      (∀ r, r ≠ .x12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by orun [low1], ?_, ?_, fun r h1 => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h14, VG.Proof.AesOcb.AArch64.and1 hv]
  · simp [gpr_write, h14]
  · simp [gpr_write, h1]
  all_goals rfl

theorem lNtz_ok {W : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {l : Block} {i : Nat}
    (hi : 0 < i) (hi' : i < 2 ^ 64) (h25 : s.gpr .x25 = BitVec.ofNat 64 i)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa lNtz s (VG.Proof.AesOcb.AArch64.LNtzPost W l i s) := by
  have wW : ∀ {d n : Nat}, d + n ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 d) n := fun h =>
    Proof.AesGcm.AArch64.in_off hw h (by decide)
  obtain ⟨s₁, run₁, B₁⟩ := VG.Proof.AesOcb.AArch64.copy16_ok (s := s) (a := l0O) (d := lO) (by decide) (by decide) h19
    (Proof.AesGcm.AArch64.in_left (wW (by decide))) (Proof.AesGcm.AArch64.in_left (wW (by decide)))
    (wW (by decide)) (wW (by decide))
  obtain ⟨s₁', run₁', x14₁', g₁', m₁', sp₁', rd₁', wr₁'⟩ : ∃ s', runBlock isa [Impl.AesGcm.AArch64.mov .x14 .x25] s₁ =
      some s' ∧ s'.gpr .x14 = BitVec.ofNat 64 i ∧ (∀ r, r ≠ .x14 → s'.gpr r = s₁.gpr r) ∧ s'.mem = s₁.mem ∧
      s'.sp = s₁.sp ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr := by
    have h25₁ : s₁.gpr .x25 = BitVec.ofNat 64 i := by rw [B₁.gpr _ (by decide), h25]
    refine ⟨_, by orun [], ?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, h25₁]
    · simp [gpr_write, h]
    all_goals rfl
  obtain ⟨s₂, run₂, x12₂, x14₂, g₂, m₂, sp₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.AArch64.low1_ok s₁' hi' x14₁'
  have post_of : ∀ t : State, Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem →
      blockAtMem t.mem (W + BitVec.ofNat 64 lO) = lAt l (ntz i) →
      (∀ r, r ∉ VG.Proof.AesOcb.AArch64.ntzRegs → t.gpr r = s₂.gpr r) → t.sp = s.sp →
      t.rd = s.rd → t.wr = s.wr → VG.Proof.AesOcb.AArch64.LNtzPost W l i s t := fun t fr v g sp rd wr =>
    ⟨fr, v, fun r hr => by
      simp only [VG.Proof.AesOcb.AArch64.ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r (by simp [VG.Proof.AesOcb.AArch64.ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]),
        g₂ r hr.2.2.2.1, g₁' r hr.2.2.2.2.2, B₁.gpr r (by simp [hr.1, hr.2.1])], sp, rd, wr⟩
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s₂.mem := by rw [m₂, m₁']; exact B₁.frame
  have v₂ : blockAtMem s₂.mem (W + BitVec.ofNat 64 lO) = lAt l 0 := by rw [m₂, m₁', B₁.val, hl0]
  have sp₂' : s₂.sp = s.sp := by rw [sp₂, sp₁', B₁.sp]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁', B₁.rd]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁', B₁.wr]
  have h19₂ : s₂.gpr .x19 = W := by rw [g₂ _ (by decide), g₁' _ (by decide), B₁.gpr _ (by decide), h19]
  unfold lNtz
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [VG.Proof.AesOcb.AArch64.runBlock_append, VG.Proof.AesOcb.AArch64.runBlock_append, run₁, Option.bind_some, run₁',
    Option.bind_some, run₂], ?_⟩)
  refine WP.ite (decide (i % 2 = 0)) (eval_zero x12₂ (by omega)) (fun hb => ?_)
    (fun hb => WP.block_nil (post_of s₂ fr₂ ?_ (fun _ _ => rfl) sp₂' rd₂' wr₂'))
  rotate_left
  · rw [v₂, Proof.Ocb.ntz_odd (by simp at hb; omega)]
  have he : i % 2 = 0 := of_decide_eq_true hb
  refine WP.loop (M := isa)
    (fun (k : Nat) (t : State) => ∃ j, k = i / 2 ^ j ∧ 0 < i / 2 ^ j ∧ i / 2 ^ j % 2 = 0 ∧
      ntz i = j + ntz (i / 2 ^ j) ∧ t.gpr .x14 = BitVec.ofNat 64 (i / 2 ^ j) ∧
      Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem ∧ blockAtMem t.mem (W + BitVec.ofNat 64 lO) = lAt l j ∧
      (∀ r, r ∉ VG.Proof.AesOcb.AArch64.ntzRegs → t.gpr r = s₂.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (i / 2 ^ 0) _
    ⟨0, rfl, by simpa using hi, by simpa using he, by simp, by simpa using x14₂, fr₂, v₂,
      fun _ _ => rfl, sp₂', rd₂', wr₂'⟩
  rintro k t ⟨j, rfl, hpos, hev, hntz, x14, fr, v, g, sp, rd, wr⟩
  have hv : i / 2 ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi'
  have h19t : t.gpr .x19 = W := by rw [g _ (by decide), h19₂]
  obtain ⟨t₁, runt₁, D₁⟩ := VG.Proof.AesOcb.AArch64.dbl_ok (s := t) (b := .x19) (a := lO) (d := lO) (by decide) (by decide) h19t h19t
    (by decide) (by rw [rd, wr]; exact Proof.AesGcm.AArch64.in_left (wW (by decide)))
    (by rw [rd, wr]; exact Proof.AesGcm.AArch64.in_left (wW (by decide)))
    (by rw [wr]; exact wW (by decide)) (by rw [wr]; exact wW (by decide))
  have e : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  obtain ⟨t₂, runt₂, x14₂', g₂', m₂', sp₂'', rd₂'', wr₂''⟩ : ∃ t₂, runBlock isa [.lsr .x .x14 .x14 1] t₁ = some t₂ ∧
      t₂.gpr .x14 = BitVec.ofNat 64 (i / 2 ^ (j + 1)) ∧ (∀ r, r ≠ .x14 → t₂.gpr r = t₁.gpr r) ∧ t₂.mem = t₁.mem ∧
      t₂.sp = t₁.sp ∧ t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr := by
    have x14₁ : t₁.gpr .x14 = BitVec.ofNat 64 (i / 2 ^ j) := by rw [D₁.gpr _ (by decide), x14]
    refine ⟨_, by orun [], ?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, x14₁, VG.Proof.AesOcb.AArch64.shr1 hv, e]
    · simp [gpr_write, h]
    all_goals rfl
  obtain ⟨t₃, runt₃, x12₃, x14₃, g₃, m₃, sp₃, rd₃, wr₃⟩ := VG.Proof.AesOcb.AArch64.low1_ok t₂ (by omega) x14₂'
  refine WP.of_runBlock ⟨t₃, by rw [VG.Proof.AesOcb.AArch64.runBlock_append, VG.Proof.AesOcb.AArch64.runBlock_append, runt₁, Option.bind_some, runt₂,
    Option.bind_some, runt₃], ?_⟩
  have fr' : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t₃.mem := by
    rw [m₃, m₂']
    exact fun x hx => (D₁.frame x hx).trans (fr x hx)
  have v' : blockAtMem t₃.mem (W + BitVec.ofNat 64 lO) = lAt l (j + 1) := by rw [m₃, m₂', D₁.val, v]; rfl
  have g' : ∀ r, r ∉ VG.Proof.AesOcb.AArch64.ntzRegs → t₃.gpr r = s₂.gpr r := fun r hr => by
    simp only [VG.Proof.AesOcb.AArch64.ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₃ r hr.2.2.2.1, g₂' r hr.2.2.2.2.2, D₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1]),
      g r (by simp [VG.Proof.AesOcb.AArch64.ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
  have sp' : t₃.sp = s.sp := by rw [sp₃, sp₂'', D₁.sp, sp]
  have rd' : t₃.rd = s.rd := by rw [rd₃, rd₂'', D₁.rd, rd]
  have wr' : t₃.wr = s.wr := by rw [wr₃, wr₂'', D₁.wr, wr]
  have hntz' : ntz i = (j + 1) + ntz (i / 2 ^ (j + 1)) := by
    rw [hntz, Proof.Ocb.ntz_even hpos hev, e]; omega
  have hv' : i / 2 ^ (j + 1) < 2 ^ 64 := by omega
  by_cases hodd : i / 2 ^ (j + 1) % 2 = 0
  · right
    refine ⟨(eval_zero x12₃ (by omega)).trans (by simp [hodd]), i / 2 ^ (j + 1), by rw [e]; omega, j + 1, rfl,
      by rw [e]; omega, hodd, hntz', x14₃, fr', v', g', sp', rd', wr'⟩
  · left
    refine ⟨(eval_zero x12₃ (by omega)).trans (by simp [hodd]), post_of t₃ fr' ?_ g' sp' rd' wr'⟩
    rw [v', hntz', Proof.Ocb.ntz_odd (by omega)]

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.PadTo`. -/
section

/-!
# AES-OCB on AArch64: padding a string (`padTo`)

Untrusted: everything here is checked by Lean. `padTo d` writes `pad(S)`
(§4.1) of the `n < 16` bytes `S` at `x23` to `W + d`: zeros, the bytes
(AES-GCM's `copyLoop`), and `0x80` after them (`padTo_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem pad)
open VG.Proof.AesGcm.AArch64 (copyLoop_ok LoopPre in_left in_off)
open VG.Proof.Ocb (length_bytesAt bytesAt_writeBytes_base)

theorem write1 (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v = m.writeW a (v : Byte) := by
  simp [Mem.writeW]

theorem contains_pre (p : Addr) {j n : Nat} (h : j ≤ n) : (⟨p, n⟩ : Region).Contains p j := by
  simpa using Offset.contains_base p (d := 0) (n := j) (k := n) (by omega) (by decide)

theorem toBytes_zero : Spec.Ocb.toBytes 0 = Spec.Ocb.zeros 16 := by decide

/-- The 16 bytes of a block that is zero. -/
theorem bytesAt_of_zero {m : Mem} {p : Addr} (h : blockAtMem m p = 0) : bytesAt m p 16 = Spec.Ocb.zeros 16 := by
  rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt m p 16), ← VG.Proof.AesOcb.AArch64.toBytes_zero, ← h]; rfl

/-- The registers `padTo` writes. -/
abbrev padRegs : List Reg := [.x9, .x11, .x12, .x13, .x14, .x15]

/-- `padTo d`: `W + d ← pad(S)`, for the `n` bytes `S` at `x23`, `0 < n < 16`. -/
theorem padTo_ok {W : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {S : Addr}
    {n d : Nat} (hn : 0 < n) (hn' : n < 16) (hd : d % 8 = 0 ∧ d + 16 ≤ 2560) (h23 : s.gpr .x23 = S)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 n) (hS : Covers [⟨S, n⟩] (s.rd ++ s.wr))
    (hSD : (⟨S, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 16⟩) :
    WP isa (padTo d) s fun t => Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (W + BitVec.ofNat 64 d) = pad (bytesAt s.mem S n) ∧
      (∀ r, r ∉ VG.Proof.AesOcb.AArch64.padRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have wW : ∀ {e k : Nat}, e + k ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 e) k := fun h => in_off hw h (by decide)
  obtain ⟨s₁, run₁, B₁⟩ := VG.Proof.AesOcb.AArch64.zero16_ok (s := s) (d := d) ⟨hd.1, by omega⟩ h19 (wW (by omega)) (wW (by omega))
  obtain ⟨s₂, run₂, x11₂, x12₂, x13₂, g₂, m₂, sp₂, rd₂, wr₂⟩ : ∃ s₂,
      runBlock isa [Impl.AesGcm.AArch64.ptr .x11 .x19 d, Impl.AesGcm.AArch64.mov .x12 .x23,
        Impl.AesGcm.AArch64.mov .x13 .x24] s₁ = some s₂ ∧
      s₂.gpr .x11 = W + BitVec.ofNat 64 d ∧ s₂.gpr .x12 = S ∧ s₂.gpr .x13 = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.sp = s₁.sp ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have h19₁ : s₁.gpr .x19 = W := by rw [B₁.gpr _ (by decide), h19]
    have h23₁ : s₁.gpr .x23 = S := by rw [B₁.gpr _ (by decide), h23]
    have h24₁ : s₁.gpr .x24 = BitVec.ofNat 64 n := by rw [B₁.gpr _ (by decide), h24]
    refine ⟨_, by orun [show d < 4096 by omega], ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, h19₁]
    · simp [gpr_write, h23₁]
    · simp [gpr_write, h24₁]
    · simp [gpr_write, h1, h2, h3]
    all_goals rfl
  have hS₂ : Covers [⟨S, n⟩] (s₂.rd ++ s₂.wr) := by rw [rd₂, wr₂, B₁.rd, B₁.wr]; exact hS
  have hD₂ : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s₂.wr := by
    rw [wr₂, B₁.wr]; exact Proof.AesGcm.AArch64.covers_off hw (by omega) (by decide)
  have hSD' : (⟨S, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ := hSD.sub_right (Region.sub_prefix (by omega))
  have eS : bytesAt s₂.mem S n = bytesAt s.mem S n := by
    rw [m₂]
    exact Proof.Cmac.bytesAt_frame B₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hSD) (by omega)
  have z₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 d) 16 = Spec.Ocb.zeros 16 := by
    rw [m₂]; exact VG.Proof.AesOcb.AArch64.bytesAt_of_zero B₁.val
  unfold padTo
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [VG.Proof.AesOcb.AArch64.runBlock_append, run₁, Option.bind_some, run₂], ?_⟩)
  refine WP.seq (WP.mono (copyLoop_ok s₂ x12₂ x11₂ x13₂ hn ⟨by omega, hS₂, hD₂, hSD'⟩) fun s₃ h₃ => ?_)
  obtain ⟨m₃, _, x11₃, g₃, sp₃, rd₃, wr₃⟩ := h₃
  have w₃ : InRegions s₃.wr (W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) 1 := by
    rw [wr₃, wr₂, B₁.wr, Offset.add_add]; exact wW (by omega)
  refine WP.of_runBlock ⟨_, by orun [x11₃, w₃, VG.Proof.AesOcb.AArch64.write1], ?_⟩
  have hlen : (bytesAt s.mem S n).length = n := length_bytesAt _ _ _
  have key : ∀ (m : Mem) (b : Byte), (writeBytes m (W + BitVec.ofNat 64 d) (bytesAt s.mem S n)).writeW
      (W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) b = writeBytes m (W + BitVec.ofNat 64 d) (bytesAt s.mem S n ++ [b]) :=
    fun m b => by rw [writeBytes_snoc _ _ _ _ (by omega), hlen]
  refine ⟨?_, ?_, fun r hr => ?_, by rw [sp₃, sp₂, B₁.sp], by rw [rd₃, rd₂, B₁.rd], by rw [wr₃, wr₂, B₁.wr]⟩
  · dsimp only
    rw [m₃, eS, key]
    intro x hx
    rw [writeBytes_frame _ _ _ (by simp [hlen]; exact VG.Proof.AesOcb.AArch64.contains_pre _ (by omega)) x hx, m₂]
    exact B₁.frame x hx
  · dsimp only
    rw [m₃, eS, key, blockAtMem, bytesAt_writeBytes_base _ _ _ (by simp [hlen]; omega) (by decide), z₂]
    simp only [pad, hlen, List.length_append, List.length_singleton, Spec.Ocb.zeros, List.drop_replicate,
      List.append_assoc, List.singleton_append, show 16 - (n + 1) = 15 - n by omega]
    rfl
  · simp only [VG.Proof.AesOcb.AArch64.padRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    dsimp only
    rw [gpr_write_of_ne _ _ _ hr.1, g₃ r (by simp [Proof.AesGcm.AArch64.loopRegs, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]),
      g₂ r hr.2.1 hr.2.2.1 hr.2.2.2.1, B₁.gpr r (by simp [hr.1])]

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.NonceBlock`. -/
section

/-!
# AES-OCB on AArch64: the block `Nonce` (`nonceBlock`)

Untrusted: everything here is checked by Lean. `nonceBlock` writes `Nonce`
(§4.2) with its last 6 bits cleared to `W + tmpO`, and `bottom` to
`W + botO` (`nonceBlock_ok`): zeros, the 1 before where the nonce goes, the
nonce copied to the end (`copyLoop`), `TAGLEN mod 128` ORed into the first
byte, and the last byte split into `bottom` and the rest. The 16 bytes are
followed as a list through the writes, and compared with `nb`
(`Proof.Ocb.nonceN_masked_byte`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (nonceN nb nbase length_bytesAt bytesAt_writeBytes_at bytesAt_writeW8_at bytesAt_writeW8_base
  toNat_ofNat_of_lt)
open VG.Proof.AesGcm.AArch64 (copyLoop_ok in_left in_off read_one and15 lsl4_ofNat)

theorem or_byte (b : Byte) (v : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b) ||| BitVec.ofNat 64 v)) =
      b ||| BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_ofNat, show i < 32 by omega,
    show i < 64 by omega, hi, decide_true, Bool.true_and]

theorem and_byte (b : Byte) (v : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b) &&& BitVec.ofNat 64 v)) =
      b &&& BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_ofNat, show i < 32 by omega,
    show i < 64 by omega, hi, decide_true, Bool.true_and]

theorem and63 (b : Byte) :
    BitVec.setWidth 64 (BitVec.setWidth 32 b) &&& BitVec.ofNat 64 63 = BitVec.ofNat 64 (b.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega), Nat.mod_eq_of_lt (a := b.toNat) (by omega),
    show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem one_byte : BitVec.setWidth 8 (BitVec.setWidth 32 (1#64 : BitVec 64)) = (1 : Byte) := by decide

theorem getD_bytesAt_eq (m : Mem) (p : Addr) {k n : Nat} (hk : k < n) :
    m (p + BitVec.ofNat 64 k) = (bytesAt m p n).getD k 0 := by
  rw [List.getD_eq_getElem?_getD]; simp [bytesAt, hk]

/-- A byte written into a list of 16. -/
theorem getD_set16 (L : List Byte) (hL : L.length = 16) {o : Nat} (ho : o < 16) (b : Byte) {k : Nat}
    (hk : k < 16) : (L.take o ++ [b] ++ L.drop (o + 1)).getD k 0 = if k = o then b else L.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_trichotomy k o with h | rfl | h
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_take_of_lt h]
    simp [show k ≠ o by omega]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp [show min k L.length = k by omega]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_take, List.length_singleton, List.getElem?_drop,
      show ¬ k = o by omega, ↓reduceIte]
    congr 2; omega

/-- What `nonceBlock` leaves. -/
structure NoncePost (W : Addr) (t : Nat) (nonce : List Byte) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 botO, 8⟩] s.mem s'.mem
  blk : blockAtMem s'.mem (W + BitVec.ofNat 64 tmpO) = nonceN t nonce &&& ~~~(63 : Block)
  bot : s'.mem.readW (W + BitVec.ofNat 64 botO) 64 = BitVec.ofNat 64 ((nonceN t nonce).extractLsb' 0 6).toNat
  gpr : ∀ r, r ∉ [.x9, .x10, .x11, .x12, .x13, .x14, .x15] → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The first block of `nonceBlock`: zeros, and the nonce's address and length. -/
theorem nonceHead_ok {W N : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {nl : Nat}
    (hN : s.mem.readW (W + BitVec.ofNat 64 nO) 64 = N)
    (hnl : s.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl) :
    ∃ s₁, runBlock isa (zero16 tmpO ++ [ld .x12 .x19 nO, ld .x13 .x19 nlO]) s = some s₁ ∧
      s₁.gpr .x12 = N ∧ s₁.gpr .x13 = BitVec.ofNat 64 nl ∧
      (∀ r, r ≠ .x9 → r ≠ .x12 → r ≠ .x13 → s₁.gpr r = s.gpr r) ∧
      Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩] s.mem s₁.mem ∧ blockAtMem s₁.mem (W + BitVec.ofNat 64 tmpO) = 0 ∧
      s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have wW : ∀ {e k : Nat}, e + k ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 e) k := fun h => in_off hw h (by decide)
  obtain ⟨s₁, run₁, B₁⟩ := VG.Proof.AesOcb.AArch64.zero16_ok (s := s) (d := tmpO) (by decide) h19 (wW (by decide)) (wW (by decide))
  have h19₁ : s₁.gpr .x19 = W := by rw [B₁.gpr _ (by decide), h19]
  have kept : ∀ {d}, (d + 8 ≤ 112 ∨ 128 ≤ d) → d + 8 ≤ 2560 →
      s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ =>
    B₁.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [tmpO]; exact Offset.disjoint W (by omega) (by omega) (by omega)) (by decide)
  have r₁ : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 nO) 8 := by rw [B₁.rd, B₁.wr]; exact in_left (wW (by decide))
  have r₂ : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 nlO) 8 := by rw [B₁.rd, B₁.wr]; exact in_left (wW (by decide))
  have hN₁ := (kept (d := nO) (by decide) (by decide)).trans hN
  have hnl₁ := (kept (d := nlO) (by decide) (by decide)).trans hnl
  simp only [nO, nlO] at r₁ r₂ hN₁ hnl₁
  obtain ⟨s₂, run₂, h₂⟩ : ∃ s₂, runBlock isa [ld .x12 .x19 nO, ld .x13 .x19 nlO] s₁ = some s₂ ∧ s₂ = _ :=
    ⟨_, by orun [h19₁, r₁, r₂], rfl⟩
  subst h₂
  refine ⟨_, by rw [VG.Proof.AesOcb.AArch64.runBlock_append, run₁, Option.bind_some, run₂], ?_, ?_, fun r h1 h2 h3 => ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h19₁, hN₁]
  · simp [gpr_write, h19₁, hnl₁]
  · simp only [gpr_write, h2, h3, ite_false]; exact B₁.gpr r (by simp [h1])
  · exact B₁.frame
  · exact B₁.val
  · exact B₁.sp
  · exact B₁.rd
  · exact B₁.wr

/-- The second block: the 1 before where the nonce goes, and the arguments of
the copy. -/
theorem nonceOne_ok {W N : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {nl : Nat}
    (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (h12 : s.gpr .x12 = N) (h13 : s.gpr .x13 = BitVec.ofNat 64 nl) :
    ∃ s₁, runBlock isa [Impl.AesGcm.AArch64.ptr .x11 .x19 (tmpO + 16), .sub .x .x11 .x11 .x13,
        .subImm .x .x14 .x11 1, Impl.AesGcm.AArch64.imm .x9 1, .strb .x9 .x14 0] s = some s₁ ∧
      s₁.gpr .x11 = W + BitVec.ofNat 64 (128 - nl) ∧ s₁.gpr .x12 = N ∧ s₁.gpr .x13 = BitVec.ofNat 64 nl ∧
      (∀ r, r ≠ .x9 → r ≠ .x11 → r ≠ .x14 → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 (127 - nl)) (1 : Byte) ∧
      s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have e1 : W + 128#64 - BitVec.ofNat 64 nl = W + BitVec.ofNat 64 (128 - nl) := Offset.add_ofNat_sub W (by omega)
  have e2 : W + BitVec.ofNat 64 (128 - nl) - 1#64 = W + BitVec.ofNat 64 (127 - nl) := by
    rw [Offset.add_ofNat_sub W (by omega)]; congr 2; omega
  have w : InRegions s.wr (W + BitVec.ofNat 64 (127 - nl)) 1 := in_off hw (by omega) (by decide)
  refine ⟨_, by orun [h19, h13, e1, e2, w, VG.Proof.AesOcb.AArch64.write1], ?_, ?_, ?_, fun r a b c => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h19, h13, e1]
  · simp [gpr_write, h12]
  · simp [gpr_write, h13]
  · simp [gpr_write, a, b, c]
  all_goals rfl

/-- The last block: `TAGLEN mod 128` into the first byte, `bottom`, and the
last byte's bits cleared. -/
theorem nonceTail_ok {W : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {t : Nat}
    (ht : t < 2 ^ 64) (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t) :
    ∃ s₁, runBlock isa [ld .x10 .x19 tlO, Impl.AesGcm.AArch64.imm .x11 15, .logic .and .x .x10 .x10 .x11,
        .lsl .x .x10 .x10 4, .ldrb .x9 .x19 tmpO, .logic .orr .x .x9 .x9 .x10, .strb .x9 .x19 tmpO,
        .ldrb .x9 .x19 (tmpO + 15), Impl.AesGcm.AArch64.imm .x11 63, .logic .and .x .x10 .x9 .x11,
        st .x19 botO .x10, Impl.AesGcm.AArch64.imm .x11 0xc0, .logic .and .x .x9 .x9 .x11,
        .strb .x9 .x19 (tmpO + 15)] s = some s₁ ∧
      s₁.mem = ((s.mem.writeW (W + BitVec.ofNat 64 112)
          (s.mem (W + BitVec.ofNat 64 112) ||| BitVec.ofNat 8 (16 * (t % 16)))).writeW (W + BitVec.ofNat 64 288)
          (BitVec.ofNat 64 ((s.mem (W + BitVec.ofNat 64 127)).toNat % 64))).writeW (W + BitVec.ofNat 64 127)
        (s.mem (W + BitVec.ofNat 64 127) &&& BitVec.ofNat 8 192) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
  have r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 tlO) 8 := in_left (in_off hw (by decide) (by decide))
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 112) 1 := in_left (in_off hw (by decide) (by decide))
  have w₁ : InRegions s.wr (W + BitVec.ofNat 64 112) 1 := in_off hw (by decide) (by decide)
  have r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 127) 1 := in_left (in_off hw (by decide) (by decide))
  have w₂ : InRegions s.wr (W + BitVec.ofNat 64 127) 1 := in_off hw (by decide) (by decide)
  have w₃ : InRegions s.wr (W + BitVec.ofNat 64 288) 8 := in_off hw (by decide) (by decide)
  have ne : (W + BitVec.ofNat 64 127 = W + BitVec.ofNat 64 112) = False := by
    simp only [eq_iff_iff, iff_false]
    intro h
    have := congrArg (· - W) h
    simp only [Offset.add_sub_cancel_left] at this
    exact absurd this (by decide)
  simp only [tlO] at r₀ htl
  refine ⟨_, by orun [h19, r₀, htl, r₁, w₁, r₂, w₂, w₃, VG.Proof.AesOcb.AArch64.write1, VG.Proof.AesGcm.AArch64.read_one, WriteBytes.writeW8_apply, ne], ?_,
    fun r a b c => ?_, ?_, ?_, ?_⟩
  · simp only [and15, toNat_ofNat_of_lt ht, lsl4_ofNat, VG.Proof.AesOcb.AArch64.or_byte, VG.Proof.AesOcb.AArch64.and_byte, VG.Proof.AesOcb.AArch64.and63]
  · simp [gpr_write, a, b, c]
  all_goals rfl

theorem nonceBlock_ok {K W : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    {N : Addr} {nl t : Nat} (hN : s.mem.readW (W + BitVec.ofNat 64 nO) 64 = N)
    (hnl : s.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15)
    (ht : t < 2 ^ 64) (hB : VG.Proof.AesOcb.AArch64.Buf W s N nl) :
    WP isa nonceBlock s (VG.Proof.AesOcb.AArch64.NoncePost W t (bytesAt s.mem N nl) s) := by
  obtain ⟨s₁, run₁, x12₁, x13₁, g₁, f₁, z₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.AArch64.nonceHead_ok h19 hw hN hnl
  have h19₁ : s₁.gpr .x19 = W := by rw [g₁ _ (by decide) (by decide) (by decide), h19]
  obtain ⟨s₂, run₂, x11₂, x12₂, x13₂, g₂, m₂, sp₂, rd₂, wr₂⟩ :=
    VG.Proof.AesOcb.AArch64.nonceOne_ok h19₁ (by rw [wr₁]; exact hw) h1 h15 x12₁ x13₁
  have hS₂ : Covers [⟨N, nl⟩] (s₂.rd ++ s₂.wr) := by rw [rd₂, wr₂, rd₁, wr₁]; exact hB.rd
  have hD₂ : Covers [⟨W + BitVec.ofNat 64 (128 - nl), nl⟩] s₂.wr := by
    rw [wr₂, wr₁]; exact Proof.AesGcm.AArch64.covers_off hw (by omega) (by decide)
  have hSD : (⟨N, nl⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (128 - nl), nl⟩ := hB.w.sub_right (Lay.wSub (by omega))
  have f₂ : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
    rw [show W + BitVec.ofNat 64 (127 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - nl) by
      rw [Offset.add_add]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  have eN : bytesAt s₂.mem N nl = bytesAt s.mem N nl := by
    rw [Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hB.w.sub_right (Lay.wSub (by decide))) (by omega),
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hB.w.sub_right (Lay.wSub (by decide))) (by omega)]
  unfold nonceBlock
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.seq (WP.mono (copyLoop_ok s₂ x12₂ x11₂ x13₂ (by omega) ⟨by omega, hS₂, hD₂, hSD⟩) fun s₃ h₃ => ?_)
  obtain ⟨m₃, _, _, g₃, sp₃, rd₃, wr₃⟩ := h₃
  rw [eN] at m₃
  have h19₃ : s₃.gpr .x19 = W := by
    rw [g₃ _ (by decide), g₂ _ (by decide) (by decide) (by decide), h19₁]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  have fr₃ : Frame [⟨W + BitVec.ofNat 64 (128 - nl), nl⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact VG.Proof.AesOcb.AArch64.contains_pre _ (by omega))
  have htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t := by
    have k : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' →
        (∀ r ∈ rs, (⟨W + BitVec.ofNat 64 tlO, 8⟩ : Region).Disjoint r) →
        m'.readW (W + BitVec.ofNat 64 tlO) 64 = m.readW (W + BitVec.ofNat 64 tlO) 64 :=
      fun h hd => h.readW (r := ⟨W + BitVec.ofNat 64 tlO, 8⟩) (Region.contains_self _ _) hd (by decide)
    rw [k fr₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by simp only [tlO]; omega)) (by decide)
          (by omega)),
      k f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
      k f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), htl]
  obtain ⟨s₄, run₄, m₄, g₄, sp₄, rd₄, wr₄⟩ := VG.Proof.AesOcb.AArch64.nonceTail_ok h19₃ (by rw [wr₃']; exact hw) ht htl₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  -- the bytes at `W + tmpO`, step by step
  have hlen : (bytesAt s.mem N nl).length = nl := length_bytesAt _ _ _
  have L₁ : bytesAt s₁.mem (W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros 16 := VG.Proof.AesOcb.AArch64.bytesAt_of_zero z₁
  have e128 : W + BitVec.ofNat 64 (128 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (16 - nl) := by
    rw [Offset.add_add, show 112 + (16 - nl) = 128 - nl by omega]
  have e127 : W + BitVec.ofNat 64 (127 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - nl) := by
    rw [Offset.add_add, show 112 + (15 - nl) = 127 - nl by omega]
  have L₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 112) 16 =
      Spec.Ocb.zeros (15 - nl) ++ [1] ++ Spec.Ocb.zeros (nl) := by
    rw [m₂, e127, bytesAt_writeW8_at _ _ _ (by omega) (by decide), L₁]
    simp only [Spec.Ocb.zeros, List.take_replicate, List.drop_replicate, show min (15 - nl) 16 = 15 - nl by omega,
      show 16 - (15 - nl + 1) = nl by omega]
  have L₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros (15 - nl) ++ [1] ++ bytesAt s.mem N nl := by
    rw [m₃, e128, bytesAt_writeBytes_at _ _ _ (by omega) (by decide), L₂, hlen]
    rw [show 16 - nl + nl = 16 by omega]
    simp only [Spec.Ocb.zeros, List.take_append, List.take_replicate, List.drop_append, List.drop_replicate,
      List.length_replicate, List.length_append, List.length_singleton, List.append_assoc]
    simp only [show min (16 - nl) (15 - nl) = 15 - nl by omega, show 16 - nl - (15 - nl) = 1 by omega,
      show 16 - (15 - nl) = nl + 1 by omega, show 15 - nl + (1 + nl) = 16 by omega]
    simp only [show 1 - 1 = 0 from rfl, Nat.zero_min, List.replicate_zero, List.nil_append,
      show 15 - nl - 16 = 0 by omega, List.take_one, List.head?_cons, Option.toList_some,
      List.drop_eq_nil_of_le (show [(1 : Byte)].length ≤ nl + 1 by simp), show nl - (nl + 1 - 1) = 0 by omega,
      List.append_nil]
  have L₃d : ∀ k < 16, (bytesAt s₃.mem (W + BitVec.ofNat 64 112) 16).getD k 0 = nbase (bytesAt s.mem N nl) k :=
    fun k hk => by
      have := Proof.Ocb.nbase_list (bytesAt s.mem N nl) (by rw [hlen]; omega) (by rw [hlen]; omega) hk
      rw [hlen] at this; rw [L₃]; exact this
  have b0 : s₃.mem (W + BitVec.ofNat 64 112) = nbase (bytesAt s.mem N nl) 0 := by
    have := VG.Proof.AesOcb.AArch64.getD_bytesAt_eq s₃.mem (W + BitVec.ofNat 64 112) (k := 0) (n := 16) (by decide)
    rw [BitVec.add_zero] at this
    rw [this, L₃d 0 (by decide)]
  have e127' : W + BitVec.ofNat 64 127 = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 15 :=
    (Offset.add_add W 112 15).symm
  have b15 : s₃.mem (W + BitVec.ofNat 64 127) = nb t (bytesAt s.mem N nl) 15 := by
    rw [e127', VG.Proof.AesOcb.AArch64.getD_bytesAt_eq s₃.mem (W + BitVec.ofNat 64 112) (k := 15) (n := 16) (by decide),
      L₃d 15 (by decide)]
    rfl
  have fr288 : ∀ (M : Mem) (v : BitVec 64), Frame [⟨W + BitVec.ofNat 64 288, 8⟩] M
      (M.writeW (W + BitVec.ofNat 64 288) v) :=
    fun M v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have L₄d : ∀ k < 16, (bytesAt s₄.mem (W + BitVec.ofNat 64 112) 16).getD k 0 =
      if k = 15 then nb t (bytesAt s.mem N nl) 15 &&& 0xc0 else nb t (bytesAt s.mem N nl) k := by
    intro k hk
    rw [m₄, b15, e127', bytesAt_writeW8_at _ _ (o := 15) (n := 16) _ (by decide) (by decide),
      Proof.Cmac.bytesAt_frame (fr288 _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := 112) (n := 16) (d := 288) (k := 8) (.inl (by decide)) (by decide) (by decide))
        (by decide),
      VG.Proof.AesOcb.AArch64.getD_set16 _ (length_bytesAt _ _ _) (by decide) _ hk]
    split
    · rfl
    · rename_i hk15
      rw [bytesAt_writeW8_base _ _ _ (by decide) (by decide), b0]
      unfold nb
      rcases k with _ | k
      · rfl
      · simp only [List.getD_cons_succ, show k + 1 ≠ 0 by omega, ↓reduceIte]
        rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
          show 1 + k = k + 1 by omega]
        exact L₃d (k + 1) hk
  have hlen16 := length_bytesAt s₄.mem (W + BitVec.ofNat 64 112) 16
  have f₃ : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 botO, 8⟩] s.mem s₃.mem :=
    ((f₁.trans f₂).mono (fun r hr => by simp at hr; simp [hr])).trans ((fr₃.sub fun r hr => ⟨_, List.mem_cons_self .., by
        simp only [List.mem_singleton] at hr; subst hr
        rw [e128]; exact Offset.sub_base _ (by omega)⟩))
  refine ⟨?_, ?_, ?_, fun r hr => ?_, by rw [sp₄, sp₃, sp₂, sp₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃']⟩
  · rw [m₄]
    refine ((f₃.writeW (List.mem_cons_self ..) _ ?_).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Region.contains_self _ _)).writeW (List.mem_cons_self ..) _ ?_
    · show (⟨W + BitVec.ofNat 64 112, 16⟩ : Region).Contains (W + BitVec.ofNat 64 112) 1
      exact VG.Proof.AesOcb.AArch64.contains_pre _ (by decide)
    · rw [e127']; exact Offset.contains_base _ (by decide) (by decide)
  · show blockAtMem s₄.mem (W + BitVec.ofNat 64 112) = _
    rw [blockAtMem]
    apply Proof.Ocb.toBytes_inj
    rw [Proof.Ocb.toBytes_ofBytes hlen16]
    refine Proof.Cmac.ext16 hlen16 (Proof.Ocb.toBytes_length _) fun k hk => ?_
    rw [L₄d k hk, Proof.Ocb.nonceN_masked_byte _ _ (by omega) (by omega) hk]
  · show s₄.mem.readW (W + BitVec.ofNat 64 288) 64 = _
    rw [m₄, Mem.readW_writeW_sep (Offset.sep W (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64, b15, Proof.Ocb.nonceN_bottom _ _ (by omega) (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₄ r hr.1 hr.2.1 hr.2.2.1, g₃ r (by simp [Proof.AesGcm.AArch64.loopRegs, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]), g₂ r hr.1 hr.2.2.1 hr.2.2.2.2.2.1, g₁ r hr.1 hr.2.2.2.1 hr.2.2.2.2.1]

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Offset0`. -/
section

/-!
# AES-OCB on AArch64: `Offset_0` (`offset0`)

Untrusted: everything here is checked by Lean. `offset0` loads `Ktop` as
two byte-reversed words, computes the third word of `Stretch`
(`Proof.Ocb.stretch_words`), shifts the three words left by `bottom` in six
masked stages (`stage_ok`, `Proof.Ocb.shl_stages`), and stores the top two,
byte-reversed, to `W + ofsO` and `W + o0O` (`offset0_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (shlIf sel_mask shl3 toNat_ofNat_of_lt)
open VG.Proof.AesGcm.AArch64 (in_left in_off)

/-- Bit `k` of `bottom` (less than 64), as 0 or 1. -/
theorem bit_v {v : Nat} (hv : v < 64) (k : Nat) :
    (BitVec.ofNat 64 v >>> k) &&& 1#64 = if v.testBit k then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  have h2 : v / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : v / 2 ^ k % 2 = 1
  · simp [h]
  · simp [h]; omega

theorem sel_mask0 (x x' : BitVec 64) (b : Bool) :
    x ^^^ ((x' ^^^ x) &&& (0#64 - (if b = true then 1 else 0))) = if b then x' else x := sel_mask x x' b

/-- One stage: the three words shifted left by `a` if bit `k` of `bottom` is set. -/
theorem stage_ok (s : State) {k a v : Nat} (hk6 : k < 64) (ha : 0 < a) (ha' : a < 64) (hv : v < 64)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa (stage k a) s = some s' ∧
      s'.gpr .x9 ++ s'.gpr .x10 ++ s'.gpr .x11 = shlIf (v.testBit k) a (s.gpr .x9 ++ s.gpr .x10 ++ s.gpr .x11) ∧
      (∀ r, r ∉ [.x9, .x10, .x11, .x13, .x14, .x15] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have c1 : 64 - a < 64 := by omega
  refine ⟨_, by orun [stage, h12, hk6, ha', c1, List.flatMap_cons, List.flatMap_nil], ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h12, VG.Proof.AesOcb.AArch64.bit_v hv, BitVec.setWidth_eq]
    rw [VG.Proof.AesOcb.AArch64.sel_mask0, VG.Proof.AesOcb.AArch64.sel_mask0, VG.Proof.AesOcb.AArch64.sel_mask0]
    unfold shlIf
    split
    · exact shl3 _ _ _ ha ha'
    · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]
  all_goals rfl

/-- The top two of three words. -/
theorem top2 (x y z : BitVec 64) : (x ++ y ++ z).extractLsb' 64 128 = x ++ y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬ 64 + i < 64 by omega, ↓reduceIte, show 64 + i - 64 = i by omega]

/-- `Stretch`. -/
def stretch (ktop : Block) : BitVec 192 := ktop ++ (ktop.extractLsb' 64 64 ^^^ ktop.extractLsb' 56 64)

/-- What `offset0` leaves. -/
structure Off0Post (W : Addr) (o : Block) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 o0O, 16⟩] s.mem s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = o
  gpr : ∀ r, r ∉ [.x9, .x10, .x11, .x12, .x13, .x14, .x15] → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem blockAtMem_eq_gcm (m : Mem) (p : Addr) : blockAtMem m p = Spec.Gcm.blockAt m p := rfl

theorem offset0_ok {K W : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    {v : Nat} (hv : v < 64) (hbot : s.mem.readW (W + BitVec.ofNat 64 botO) 64 = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa offset0 s = some s' ∧
      VG.Proof.AesOcb.AArch64.Off0Post W ((VG.Proof.AesOcb.AArch64.stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128) s s' := by
  have rr : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 :=
    fun h => in_left (in_off hw h (by decide))
  simp only [botO] at hbot
  obtain ⟨s₁, run₁, w₁, x12₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [ld .x9 .x19 tmpO, .rev .x9 .x9, ld .x10 .x19 (tmpO + 8), .rev .x10 .x10,
       .lsl .x .x11 .x9 8, .lsr .x .x13 .x10 56, .logic .orr .x .x11 .x11 .x13,
       .logic .eor .x .x11 .x11 .x9, ld .x12 .x19 botO] s = some s₁ ∧
      s₁.gpr .x9 ++ s₁.gpr .x10 ++ s₁.gpr .x11 = VG.Proof.AesOcb.AArch64.stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO)) ∧
      s₁.gpr .x12 = BitVec.ofNat 64 v ∧
      (∀ r, r ∉ [.x9, .x10, .x11, .x12, .x13] → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    have r₀ := rr (d := 112) (by decide)
    have r₁ := rr (d := 120) (by decide)
    have r₂ := rr (d := 288) (by decide)
    refine ⟨_, by orun [h19, r₀, r₁, r₂], ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
      have hb : blockAtMem s.mem (W + BitVec.ofNat 64 tmpO) =
          rev64 (s.mem.readW (W + BitVec.ofNat 64 112) 64) ++ rev64 (s.mem.readW (W + BitVec.ofNat 64 120) 64) := by
        have := Proof.Gcm.AArch64.blockAt_rev s.mem (W + BitVec.ofNat 64 112)
        rw [BitVec.add_zero, Offset.add_add] at this
        exact this.symm
      rw [VG.Proof.AesOcb.AArch64.stretch, hb, Proof.Ocb.stretch_words]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, hbot]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]
    all_goals rfl
  -- the six stages
  have keep : ∀ {t t' : State}, (∀ r, r ∉ [.x9, .x10, .x11, .x13, .x14, .x15] → t'.gpr r = t.gpr r) →
      t.gpr .x12 = BitVec.ofNat 64 v → t'.gpr .x12 = BitVec.ofNat 64 v := fun g h => by rw [g _ (by decide), h]
  obtain ⟨s₂, run₂, w₂, g₂, m₂, sp₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.AArch64.stage_ok s₁ (k := 0) (a := 1) (by decide) (by decide) (by decide) hv x12₁
  obtain ⟨s₃, run₃, w₃, g₃, m₃, sp₃, rd₃, wr₃⟩ := VG.Proof.AesOcb.AArch64.stage_ok s₂ (k := 1) (a := 2) (by decide) (by decide) (by decide) hv
    (keep g₂ x12₁)
  obtain ⟨s₄, run₄, w₄, g₄, m₄, sp₄, rd₄, wr₄⟩ := VG.Proof.AesOcb.AArch64.stage_ok s₃ (k := 2) (a := 4) (by decide) (by decide) (by decide) hv
    (keep g₃ (keep g₂ x12₁))
  obtain ⟨s₅, run₅, w₅, g₅, m₅, sp₅, rd₅, wr₅⟩ := VG.Proof.AesOcb.AArch64.stage_ok s₄ (k := 3) (a := 8) (by decide) (by decide) (by decide) hv
    (keep g₄ (keep g₃ (keep g₂ x12₁)))
  obtain ⟨s₆, run₆, w₆, g₆, m₆, sp₆, rd₆, wr₆⟩ := VG.Proof.AesOcb.AArch64.stage_ok s₅ (k := 4) (a := 16) (by decide) (by decide) (by decide) hv
    (keep g₅ (keep g₄ (keep g₃ (keep g₂ x12₁))))
  obtain ⟨s₇, run₇, w₇, g₇, m₇, sp₇, rd₇, wr₇⟩ := VG.Proof.AesOcb.AArch64.stage_ok s₆ (k := 5) (a := 32) (by decide) (by decide) (by decide) hv
    (keep g₆ (keep g₅ (keep g₄ (keep g₃ (keep g₂ x12₁)))))
  have hw7 : s₇.gpr .x9 ++ s₇.gpr .x10 ++ s₇.gpr .x11 =
      VG.Proof.AesOcb.AArch64.stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO)) <<< v := by
    rw [w₇, w₆, w₅, w₄, w₃, w₂, w₁, Proof.Ocb.shl_stages _ hv]
  have hO : s₇.gpr .x9 ++ s₇.gpr .x10 =
      (VG.Proof.AesOcb.AArch64.stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [← VG.Proof.AesOcb.AArch64.top2 _ _ (s₇.gpr .x11), hw7, Proof.Ocb.offset_shl _ (by omega)]
  have hm₇ : s₇.mem = s.mem := by rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁]
  have hsp₇ : s₇.sp = s.sp := by rw [sp₇, sp₆, sp₅, sp₄, sp₃, sp₂, sp₁]
  have hrd₇ : s₇.rd = s.rd := by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]
  have hwr₇ : s₇.wr = s.wr := by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]
  have g₁₇ : ∀ r, r ∉ [.x9, .x10, .x11, .x12, .x13, .x14, .x15] → s₇.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    have h' : r ∉ [Reg.x9, .x10, .x11, .x13, .x14, .x15] := by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]
    rw [g₇ r h', g₆ r h', g₅ r h', g₄ r h', g₃ r h', g₂ r h',
      g₁ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1])]
  have h19₇ : s₇.gpr .x19 = W := by rw [g₁₇ _ (by decide), h19]
  have ww : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions s₇.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => by rw [hwr₇]; exact in_off hw h (by decide)
  obtain ⟨s₈, run₈, m₈, g₈, sp₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa [.rev .x9 .x9, .rev .x10 .x10, st .x19 ofsO .x9,
      st .x19 (ofsO + 8) .x10, st .x19 o0O .x9, st .x19 (o0O + 8) .x10] s₇ = some s₈ ∧
      s₈.mem = (((s₇.mem.writeW (W + BitVec.ofNat 64 16) (rev64 (s₇.gpr .x9))).writeW (W + BitVec.ofNat 64 24)
        (rev64 (s₇.gpr .x10))).writeW (W + BitVec.ofNat 64 304) (rev64 (s₇.gpr .x9))).writeW
        (W + BitVec.ofNat 64 312) (rev64 (s₇.gpr .x10)) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s₈.gpr r = s₇.gpr r) ∧ s₈.sp = s₇.sp ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    have w₁₆ := ww (d := 16) (by decide)
    have w₂₄ := ww (d := 24) (by decide)
    have w₃₀₄ := ww (d := 304) (by decide)
    have w₃₁₂ := ww (d := 312) (by decide)
    refine ⟨_, by orun [h19₇, w₁₆, w₂₄, w₃₀₄, w₃₁₂], ?_, fun r h1 h2 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    · simp [gpr_write, h1, h2]
    all_goals rfl
  have val : Spec.Ocb.ofBytes (Proof.Cmac.le8 (rev64 (s₇.gpr .x9)) ++ Proof.Cmac.le8 (rev64 (s₇.gpr .x10))) =
      (VG.Proof.AesOcb.AArch64.stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [Proof.CmacAes.AArch64.le8_rev, ← Proof.Ocb.toBytes_eq, Proof.Ocb.ofBytes_toBytes, hO]
  have run : runBlock isa offset0 s = some s₈ := by
    unfold offset0
    rw [VG.Proof.AesOcb.AArch64.runBlock_append, VG.Proof.AesOcb.AArch64.runBlock_append, VG.Proof.AesOcb.AArch64.runBlock_append, VG.Proof.AesOcb.AArch64.runBlock_append, VG.Proof.AesOcb.AArch64.runBlock_append, VG.Proof.AesOcb.AArch64.runBlock_append,
      VG.Proof.AesOcb.AArch64.runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, run₄,
      Option.bind_some, run₅, Option.bind_some, run₆, Option.bind_some, run₇, Option.bind_some, run₈]
  have f304 : ∀ M : Mem, Frame [⟨W + BitVec.ofNat 64 304, 16⟩] M
      ((M.writeW (W + BitVec.ofNat 64 304) (rev64 (s₇.gpr .x9))).writeW (W + BitVec.ofNat 64 312)
        (rev64 (s₇.gpr .x10))) := fun M => by
    rw [← VG.Proof.AesOcb.AArch64.addr8 W 304]; exact Proof.Cmac.frame_store2 _ _ _
  refine ⟨s₈, run, ?_, ?_, ?_, fun r hr => ?_, by rw [sp₈, hsp₇], by rw [rd₈, hrd₇], by rw [wr₈, hwr₇]⟩
  · rw [m₈, ← hm₇]
    show Frame [⟨W + BitVec.ofNat 64 16, 16⟩, ⟨W + BitVec.ofNat 64 304, 16⟩] _ _
    exact ((((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (VG.Proof.AesOcb.AArch64.contains_pre _ (by decide))).writeW
      (List.mem_cons_self ..) _ (Offset.contains W (e := 16) (k := 16) (d := 24) (n := 8) (by decide) (by decide)
        (by decide))).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (VG.Proof.AesOcb.AArch64.contains_pre _ (by decide))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
        (Offset.contains W (e := 304) (k := 16) (d := 312) (n := 8) (by decide) (by decide) (by decide))
  · show blockAtMem s₈.mem (W + BitVec.ofNat 64 16) = _
    rw [m₈, Proof.Ocb.blockAtMem_frame (f304 _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 16) (n := 16) (d := 304) (k := 16) (.inl (by decide)) (by decide) (by decide))]
    rw [show W + BitVec.ofNat 64 24 = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 from (VG.Proof.AesOcb.AArch64.addr8 W 16).symm,
      VG.Proof.AesOcb.AArch64.blockAtMem_store2, val]
  · show blockAtMem s₈.mem (W + BitVec.ofNat 64 304) = _
    rw [m₈, show W + BitVec.ofNat 64 312 = W + BitVec.ofNat 64 304 + BitVec.ofNat 64 8 from (VG.Proof.AesOcb.AArch64.addr8 W 304).symm,
      VG.Proof.AesOcb.AArch64.blockAtMem_store2, val]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₈ r hr.1 hr.2.1, g₁₇ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2])]

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Nonce`. -/
section

/-!
# AES-OCB on AArch64: `Offset_0` from the nonce (`nonce`)

Untrusted: everything here is checked by Lean. `nonce` writes `Nonce` with
its last 6 bits cleared and `bottom` (`nonceBlock_ok`), enciphers the block
(`Ktop`, `callBlocks_ok`), and computes `Offset_0` (`offset0_ok`), to
`W + ofsO` and `W + o0O` (`nonce_ok`): §4.2's `Offset_0`
(`Proof.Ocb.offset0_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph ctxInv ctxLstar)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.Ocb (blockAtMem_frame)

/-- The key schedule, after a frame within the parts the pieces write. -/
theorem ctxCiph_mut {K W D : Addr} {n : Nat} (L : VG.Proof.AesOcb.AArch64.Lay K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    {m m' : Mem} (h : Frame (VG.Proof.AesOcb.AArch64.mutR W D n) m m') {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ctxCiph m' K R = ctxCiph m K R := by
  unfold ctxCiph
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [Proof.Cmac.bytesAt_frame h (fun r hr => (VG.Proof.AesOcb.AArch64.k_mut L hD r hr).sub_left (Region.sub_prefix hRb)) (by omega)]

theorem ctxInv_mut {K W D : Addr} {n : Nat} (L : VG.Proof.AesOcb.AArch64.Lay K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    {m m' : Mem} (h : Frame (VG.Proof.AesOcb.AArch64.mutR W D n) m m') {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ctxInv m' K R = ctxInv m K R := by
  unfold ctxInv
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [Proof.Cmac.bytesAt_frame h (fun r hr => (VG.Proof.AesOcb.AArch64.k_mut L hD r hr).sub_left (Region.sub_prefix hRb)) (by omega)]

theorem ctxLstar_mut {K W D : Addr} {n : Nat} (L : VG.Proof.AesOcb.AArch64.Lay K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    {m m' : Mem} (h : Frame (VG.Proof.AesOcb.AArch64.mutR W D n) m m') : ctxLstar m' K = ctxLstar m K := by
  show blockAtMem m' (K + BitVec.ofNat 64 240) = blockAtMem m (K + BitVec.ofNat 64 240)
  exact blockAtMem_frame h fun r hr => (VG.Proof.AesOcb.AArch64.k_mut L hD r hr).sub_left (Lay.kSub (by decide))

/-- What `nonce` writes: `[16, 160)` and `[288, 2560)` of `W`. -/
abbrev nonceR (W : Addr) : List Region := [⟨W + BitVec.ofNat 64 16, 144⟩, VG.Proof.AesOcb.AArch64.wB W]

theorem nonceR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (VG.Proof.AesOcb.AArch64.nonceR W) m m') :
    Frame (VG.Proof.AesOcb.AArch64.mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Proof.AesOcb.AArch64.in_mutA (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩

/-- What `nonce` leaves. -/
structure NonceOk (K W D : Addr) (R n : Nat) (SP : Addr) (o : Block) (s s' : State) : Prop where
  env : VG.Proof.AesOcb.AArch64.Env K W D R n SP s'
  frame : Frame (VG.Proof.AesOcb.AArch64.nonceR W) s.mem s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = o
  keep : ∀ {d : Nat}, 32 ≤ d → d + 16 ≤ 112 →
    blockAtMem s'.mem (W + BitVec.ofNat 64 d) = blockAtMem s.mem (W + BitVec.ofNat 64 d)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem nonce_ok (v : BlocksImpl) {K W D : Addr} {R n : Nat} {SP : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {s : State}
    (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {N : Addr} {nl t : Nat}
    (hN : s.mem.readW (W + BitVec.ofNat 64 nO) 64 = N)
    (hnl : s.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15)
    (ht : t < 2 ^ 64) (hB : VG.Proof.AesOcb.AArch64.Buf W s N nl) (hKD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩) :
    WP isa (nonce (VG.Proof.AesOcb.AArch64.callees v)) s
      (VG.Proof.AesOcb.AArch64.NonceOk K W D R n SP (Spec.Ocb.offset0 (ctxCiph s.mem K R) t (bytesAt s.mem N nl)) s) := by
  unfold nonce
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.nonceBlock_ok L E.x19 E.perm.w hN hnl htl h1 h15 ht hB) fun s₁ P₁ => ?_)
  have E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP s₁ := E.others P₁.gpr P₁.sp P₁.rd P₁.wr
  have F₁ : Frame (VG.Proof.AesOcb.AArch64.nonceR W) s.mem s₁.mem := P₁.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), VG.Proof.AesOcb.AArch64.sub_wB (by decide) (by decide)⟩
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNoFrames L E₁ hR
    (VG.Proof.AesOcb.AArch64.oneBlock_ok E₁.x19 tmpO (by decide)) (VG.Proof.AesOcb.AArch64.dstW L E₁.perm (d := tmpO) (n := 1) (by decide))) fun s₂ P₂ => ?_)
  have E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP s₂ := E₁.of_saved P₂.saved P₂.sp P₂.rd P₂.wr
  have F₂ : Frame (VG.Proof.AesOcb.AArch64.nonceR W) s₁.mem s₂.mem := P₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), VG.Proof.AesOcb.AArch64.sub_wB (by decide) (by decide)⟩
  have ktop : blockAtMem s₂.mem (W + BitVec.ofNat 64 tmpO) =
      ctxCiph s.mem K R (Proof.Ocb.nonceN t (bytesAt s.mem N nl) &&& ~~~(63 : Block)) := by
    rw [P₂.enc0, P₁.blk]
    exact congrFun (VG.Proof.AesOcb.AArch64.ctxCiph_mut L hKD (VG.Proof.AesOcb.AArch64.nonceR_mut F₁) hR) _
  have hbv : ((Proof.Ocb.nonceN t (bytesAt s.mem N nl)).extractLsb' 0 6).toNat < 64 :=
    (BitVec.extractLsb' 0 6 _).isLt
  have bot₂ : s₂.mem.readW (W + BitVec.ofNat 64 botO) 64 =
      BitVec.ofNat 64 ((Proof.Ocb.nonceN t (bytesAt s.mem N nl)).extractLsb' 0 6).toNat := by
    rw [P₂.frame.readW (r := ⟨W + BitVec.ofNat 64 botO, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), P₁.bot]
  obtain ⟨s₃, run₃, P₃⟩ := VG.Proof.AesOcb.AArch64.offset0_ok L E₂.x19 E₂.perm.w hbv bot₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨E₂.others P₃.gpr P₃.sp P₃.rd P₃.wr,
    F₁.trans (F₂.trans (P₃.frame.sub fun r hr => ?_)), ?_, ?_, fun {d} h₁ h₂ => ?_, by rw [P₃.rd, P₂.rd, P₁.rd],
    by rw [P₃.wr, P₂.wr, P₁.wr]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), VG.Proof.AesOcb.AArch64.sub_wB (by decide) (by decide)⟩
  · rw [P₃.ofs, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [P₃.o0, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [blockAtMem_frame P₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.w_w (by simp only [ofsO, o0O]; omega) (by omega) (by decide)),
      blockAtMem_frame P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.w_w (by simp only [tmpO]; omega) (by omega) (by decide)
        · exact L.w_w (by omega) (by omega) (by decide)),
      blockAtMem_frame P₁.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.w_w (by simp only [tmpO, botO]; omega) (by omega) (by decide))]

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.HashFill`. -/
section

/-!
# AES-OCB on AArch64: filling the buffer of `HASH` (`hashFill`)

Untrusted: everything here is checked by Lean. `hashFill` computes the next
offset of `HASH`, `Offset_{i+1} = Offset_i ⊕ L_{ntz(i+1)}` (`lNtz_ok`,
`xor16_ok`), and writes the next block of the associated data XORed with it
to the next slot of the buffer at `W + bufO` (`hashFill_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.AArch64 (in_left in_off)

/-- The registers `hashFill` writes. -/
abbrev fillRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x23, .x25, .x27]

/-- What one `hashFill` leaves. -/
structure FillPost (W A : Addr) (l : Block) (j i c : Nat) (t t' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ohO, 16⟩,
    ⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩] t.mem t'.mem
  oh : blockAtMem t'.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1)
  buf : blockAtMem t'.mem (W + BitVec.ofNat 64 (384 + 16 * i)) =
    blockAtMem t.mem (A + BitVec.ofNat 64 (16 * (j + i))) ^^^ offAt 0 l (j + i + 1)
  x23 : t'.gpr .x23 = A + BitVec.ofNat 64 (16 * (j + i + 1))
  x25 : t'.gpr .x25 = BitVec.ofNat 64 (j + i + 2)
  x27 : t'.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * (i + 1))
  x15 : t'.gpr .x15 = BitVec.ofNat 64 (c - (i + 1))
  gpr : ∀ r, r ∉ VG.Proof.AesOcb.AArch64.fillRegs → t'.gpr r = t.gpr r
  sp : t'.sp = t.sp
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem hashFill_ok {K W : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {t : State} (h19 : t.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] t.wr)
    {A : Addr} {l : Block} {j i c : Nat} (hi : i < c) (hc : c ≤ 8) (hj : j + i + 2 < 2 ^ 61)
    (h25 : t.gpr .x25 = BitVec.ofNat 64 (j + i + 1)) (h23 : t.gpr .x23 = A + BitVec.ofNat 64 (16 * (j + i)))
    (h27 : t.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * i)) (h15 : t.gpr .x15 = BitVec.ofNat 64 (c - i))
    (hl0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hoh : blockAtMem t.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i))
    (hA : Covers [⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩] (t.rd ++ t.wr))
    (hAW : (⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa hashFill t (VG.Proof.AesOcb.AArch64.FillPost W A l j i c t) := by
  unfold hashFill
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.lNtz_ok (i := j + i + 1) h19 hw (by omega) (by omega) h25 hl0) fun t₁ P₁ => ?_)
  have h19₁ : t₁.gpr .x19 = W := by rw [P₁.gpr _ (by decide), h19]
  have ww : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions t₁.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => by rw [P₁.wr]; exact in_off hw h (by decide)
  obtain ⟨t₂, run₂, B₂⟩ := VG.Proof.AesOcb.AArch64.xor16_ok (s := t₁) (b := .x19) (a := lO) (d := ohO) (by decide) (by decide) h19₁ h19₁
    (by decide) (by decide) (by decide) (in_left (ww (by decide))) (in_left (ww (by decide)))
    (ww (by decide)) (ww (by decide))
  have oh₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1) := by
    rw [B₂.val, P₁.val, blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), hoh]
    rfl
  have g₂ : ∀ r, r ∉ VG.Proof.AesOcb.AArch64.ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    rw [B₂.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h | h | h <;> simp [h])),
      P₁.gpr r hr]
  have h23₂ : t₂.gpr .x23 = A + BitVec.ofNat 64 (16 * (j + i)) := by rw [g₂ _ (by decide), h23]
  have h27₂ : t₂.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * i) := by rw [g₂ _ (by decide), h27]
  have h19₂ : t₂.gpr .x19 = W := by rw [g₂ _ (by decide), h19]
  have h25₂ : t₂.gpr .x25 = BitVec.ofNat 64 (j + i + 1) := by rw [g₂ _ (by decide), h25]
  have h15₂ : t₂.gpr .x15 = BitVec.ofNat 64 (c - i) := by rw [g₂ _ (by decide), h15]
  have rd₂ : t₂.rd = t.rd := by rw [B₂.rd, P₁.rd]
  have wr₂ : t₂.wr = t.wr := by rw [B₂.wr, P₁.wr]
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  have eA : blockAtMem t₂.mem (A + BitVec.ofNat 64 (16 * (j + i))) = blockAtMem t.mem (A + BitVec.ofNat 64 (16 * (j + i))) :=
    blockAtMem_frame fr₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hAW.sub_right (Lay.wSub (by decide))
  have rA₀ : InRegions (t₂.rd ++ t₂.wr) (A + BitVec.ofNat 64 (16 * (j + i))) 8 := by
    rw [rd₂, wr₂]; simpa using in_off (d := 0) (n := 8) hA (by decide) (by decide)
  have rA₈ : InRegions (t₂.rd ++ t₂.wr) (A + BitVec.ofNat 64 (16 * (j + i)) + BitVec.ofNat 64 8) 8 := by
    rw [rd₂, wr₂]; exact in_off (d := 8) (n := 8) hA (by decide) (by decide)
  have rO₀ : InRegions (t₂.rd ++ t₂.wr) (W + BitVec.ofNat 64 144) 8 := by
    rw [rd₂, wr₂]; exact in_left (in_off hw (by decide) (by decide))
  have rO₈ : InRegions (t₂.rd ++ t₂.wr) (W + BitVec.ofNat 64 152) 8 := by
    rw [rd₂, wr₂]; exact in_left (in_off hw (by decide) (by decide))
  have wS₀ : InRegions t₂.wr (W + BitVec.ofNat 64 (384 + 16 * i)) 8 := by rw [wr₂]; exact in_off hw (by omega) (by decide)
  have wS₈ : InRegions t₂.wr (W + BitVec.ofNat 64 (384 + 16 * i) + BitVec.ofNat 64 8) 8 := by
    rw [wr₂, Offset.add_add]; exact in_off hw (by omega) (by decide)
  refine WP.of_runBlock ⟨_, by rw [VG.Proof.AesOcb.AArch64.runBlock_append, run₂, Option.bind_some]; orun [h23₂, h27₂, h19₂, h25₂, h15₂,
    rA₀, rA₈, rO₀, rO₈, wS₀, wS₈], ?_⟩
  have fs : ∀ (M : Mem) (v₀ v₁ : BitVec 64), Frame [⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩] M
      ((M.writeW (W + BitVec.ofNat 64 (384 + 16 * i)) v₀).writeW (W + BitVec.ofNat 64 (384 + 16 * i) + 8#64) v₁) :=
    fun M v₀ v₁ => Proof.Cmac.frame_store2 _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩ <;> try dsimp only
  · simp only [mem_write]
    exact (fr₂.mono (by simp)).trans ((fs _ _ _).mono (by simp))
  · simp only [mem_write]
    rw [blockAtMem_frame (fs _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 144) (n := 16) (d := 384 + 16 * i) (k := 16) (.inl (by omega)) (by decide) (by omega)), oh₂]
  · simp only [mem_write]
    rw [VG.Proof.AesOcb.AArch64.blockAtMem_store2, show W + 152#64 = W + BitVec.ofNat 64 144 + BitVec.ofNat 64 8 from (VG.Proof.AesOcb.AArch64.addr8 W 144).symm,
      VG.Proof.AesOcb.AArch64.blockAtMem_xor_words, eA, show W + BitVec.ofNat 64 144 = W + BitVec.ofNat 64 ohO from rfl, oh₂]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h23₂, Offset.add_add]
    rw [show 16 * (j + i) + 16 = 16 * (j + i + 1) by omega]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h25₂, ← BitVec.ofNat_add]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27₂, Offset.add_add]
    rw [show 384 + 16 * i + 16 = 384 + 16 * (i + 1) by omega]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h15₂]
    rw [Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · simp only [VG.Proof.AesOcb.AArch64.fillRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2, ite_false]
    exact g₂ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1])
  · simp only [sp_write]; rw [B₂.sp, P₁.sp]
  · simp only [rd_write]; exact rd₂
  · simp only [wr_write]; exact wr₂

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.HashChunk`. -/
section

/-!
# AES-OCB on AArch64: a chunk of `HASH` (`hashChunk`)

Untrusted: everything here is checked by Lean. After `j` of the `m` whole
blocks of the associated data `a`, `HInv` holds: the sum and the offset of
`HASH` are `Sum_j` and `Offset_j` (`Proof.Ocb.hsum`, `Proof.Ocb.offAt`),
`x23` points at block `j`, `x25` is `j + 1` and `x26` is `m − j`.
`hashChunk` takes `c = min(8, m − j)` blocks (`chunkHead_ok`): fills the
buffer with each block XORed with its offset (`fill_ok`), enciphers the
buffer, adds it to the sum (`hashSum_ok`), and leaves `HInv` at `j + c`
(`hashChunk_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar)
open VG.Proof.Ocb (offAt hsum blockAtMem_frame)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (in_left in_off eval_zero eval_nonzero toNat_ofNat_of_lt)

/-- What `HASH` writes: the sum, `[96, 160)` (`L_{ntz(i)}`, the blocks of
one call and the offset), and the buffer and the working space of the
functions called. -/
abbrev hashR (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 48, 16⟩, ⟨W + BitVec.ofNat 64 96, 64⟩, ⟨W + BitVec.ofNat 64 384, 2176⟩]

theorem hashR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (VG.Proof.AesOcb.AArch64.hashR W) m m') :
    Frame (VG.Proof.AesOcb.AArch64.mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact VG.Proof.AesOcb.AArch64.in_mutA (by decide)
  · exact VG.Proof.AesOcb.AArch64.in_mutA (by decide)
  · exact VG.Proof.AesOcb.AArch64.in_mutB (by decide) (by decide)

/-- What holds of `HASH` of `a` (at `A`) after `j` of its whole blocks, from
the state `s₀` at its start. -/
structure HInv (K W D : Addr) (R n : Nat) (SP : Addr) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ s : State) (j : Nat) : Prop where
  env : VG.Proof.AesOcb.AArch64.Env K W D R n SP s
  frame : Frame (VG.Proof.AesOcb.AArch64.hashR W) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  le : j ≤ a.length / 16
  sum : blockAtMem s.mem (W + BitVec.ofNat 64 sumO) = hsum ciph l a j
  oh : blockAtMem s.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l j
  x23 : s.gpr .x23 = A + BitVec.ofNat 64 (16 * j)
  x25 : s.gpr .x25 = BitVec.ofNat 64 (j + 1)
  x26 : s.gpr .x26 = BitVec.ofNat 64 (a.length / 16 - j)
  l0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0

/-- What a chunk of `HASH` needs of its start, `s₀`: the key context's
cipher and `L_*`, the associated data (apart from `W` and the data at `D`). -/
structure HCtx (K W D : Addr) (n R : Nat) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ : State) : Prop where
  lay : VG.Proof.AesOcb.AArch64.Lay K W
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  ciph : ctxCiph s₀.mem K R = ciph
  lstar : ctxLstar s₀.mem K = l
  buf : VG.Proof.AesOcb.AArch64.Buf W s₀ A a.length
  aad : bytesAt s₀.mem A a.length = a
  ad : (⟨A, a.length⟩ : Region).Disjoint ⟨D, n⟩
  kd : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩
  dw : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩

namespace HCtx

variable {K W D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte} {s₀ : State}
  (C : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph l A a s₀)
include C

theorem short : a.length < 2 ^ 64 := C.buf.lt

/-- The associated data misses the parts the pieces write. -/
theorem a_mut : ∀ r ∈ VG.Proof.AesOcb.AArch64.mutR W D n, (⟨A, a.length⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact C.buf.w.sub_right (Region.sub_prefix (by decide))
  · exact C.buf.w.sub_right (Lay.wSub (by decide))
  · exact C.ad

/-- Block `i` of the associated data, in a state after `s₀`. -/
theorem blk {m : Mem} (h : Frame (VG.Proof.AesOcb.AArch64.mutR W D n) s₀.mem m) {i : Nat} (hi : i < a.length / 16) :
    blockAtMem m (A + BitVec.ofNat 64 (16 * i)) = blockAt a i := by
  rw [← C.aad, Proof.Ocb.blockAt_bytesAt _ _ (by omega), blockAtMem_frame h fun r hr =>
    (C.a_mut r hr).sub_left (Offset.sub_base A (by omega))]

theorem ciph' {m : Mem} (h : Frame (VG.Proof.AesOcb.AArch64.mutR W D n) s₀.mem m) : ctxCiph m K R = ciph := by
  rw [VG.Proof.AesOcb.AArch64.ctxCiph_mut C.lay C.kd h C.rounds, C.ciph]

theorem lstar' {m : Mem} (h : Frame (VG.Proof.AesOcb.AArch64.mutR W D n) s₀.mem m) : ctxLstar m K = l := by
  rw [VG.Proof.AesOcb.AArch64.ctxLstar_mut C.lay C.kd h, C.lstar]

end HCtx

/-! ## Filling the buffer -/

/-- The fill loop after `i` of the `c` blocks of a chunk from block `j`. -/
structure FillInv (K W D : Addr) (R n : Nat) (SP : Addr) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ : State) (j c : Nat) (t : State) (i : Nat) : Prop where
  env : VG.Proof.AesOcb.AArch64.Env K W D R n SP t
  frame : Frame (VG.Proof.AesOcb.AArch64.hashR W) s₀.mem t.mem
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  x23 : t.gpr .x23 = A + BitVec.ofNat 64 (16 * (j + i))
  x25 : t.gpr .x25 = BitVec.ofNat 64 (j + i + 1)
  x27 : t.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * i)
  x15 : t.gpr .x15 = BitVec.ofNat 64 (c - i)
  x24 : t.gpr .x24 = BitVec.ofNat 64 c
  x26 : t.gpr .x26 = BitVec.ofNat 64 (a.length / 16 - j)
  oh : blockAtMem t.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i)
  buf : ∀ k < i, blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k)) = blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)
  sum : blockAtMem t.mem (W + BitVec.ofNat 64 sumO) = hsum ciph l a j
  l0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0

theorem fill_step {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte}
    {s₀ : State} (C : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph l A a s₀) {j c : Nat} (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16)
    {t : State} {i : Nat} (hi : i < c) (F : VG.Proof.AesOcb.AArch64.FillInv K W D R n SP ciph l A a s₀ j c t i) :
    WP isa hashFill t fun t' => VG.Proof.AesOcb.AArch64.FillInv K W D R n SP ciph l A a s₀ j c t' (i + 1) := by
  have L := C.lay
  have hs := C.short
  have hA : Covers [⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩] (t.rd ++ t.wr) := by
    rw [F.rd, F.wr]; exact (C.buf.slice (a := 16 * (j + i)) (k := 16) (by omega)).rd
  have hAW : (⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint ⟨W, 2560⟩ :=
    (C.buf.slice (a := 16 * (j + i)) (k := 16) (by omega)).w
  refine WP.mono (VG.Proof.AesOcb.AArch64.hashFill_ok L F.env.x19 F.env.perm.w hi hc (by omega) F.x25 F.x23 F.x27 F.x15 F.l0 F.oh hA hAW)
    fun t' P => ?_
  have hfr : ∀ r ∈ [(⟨W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ohO, 16⟩,
      ⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩], ∃ r' ∈ VG.Proof.AesOcb.AArch64.hashR W, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        Offset.sub W (by omega) (by omega)⟩
  have keepB : ∀ {d : Nat}, (d + 16 ≤ 96 ∨ (112 ≤ d ∧ d + 16 ≤ 144) ∨ (160 ≤ d ∧ d + 16 ≤ 384 + 16 * i) ∨
      384 + 16 * (i + 1) ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t'.mem (W + BitVec.ofNat 64 d) = blockAtMem t.mem (W + BitVec.ofNat 64 d) := fun h₁ h₂ =>
    blockAtMem_frame P.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 144) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 384 + 16 * i) (k := 16) (by omega) h₂ (by omega)
  have hg : ∀ r ∈ VG.Proof.AesOcb.AArch64.envRegs, t'.gpr r = t.gpr r := fun r hr => P.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  refine
    { env := F.env.keep hg P.sp P.rd P.wr
      frame := F.frame.trans (P.frame.sub hfr)
      rd := by rw [P.rd, F.rd]
      wr := by rw [P.wr, F.wr]
      x23 := by rw [P.x23, show j + i + 1 = j + (i + 1) by omega]
      x25 := by rw [P.x25, show j + i + 2 = j + (i + 1) + 1 by omega]
      x27 := P.x27
      x15 := P.x15
      x24 := by rw [P.gpr _ (by decide), F.x24]
      x26 := by rw [P.gpr _ (by decide), F.x26]
      oh := by rw [P.oh]; rfl
      buf := fun k hk => ?_
      sum := by rw [keepB (by simp only [sumO]; omega) (by decide), F.sum]
      l0 := by rw [keepB (by simp only [l0O]; omega) (by decide), F.l0] }
  rcases Nat.lt_or_ge k i with hk' | hk'
  · rw [keepB (by omega) (by omega), F.buf k hk']
  · obtain rfl : k = i := by omega
    rw [P.buf, C.blk (VG.Proof.AesOcb.AArch64.hashR_mut F.frame) (by omega)]

theorem fill_ok {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte}
    {s₀ : State} (C : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph l A a s₀) {j c : Nat} (hc0 : 0 < c) (hc : c ≤ 8)
    (hjc : j + c ≤ a.length / 16) {t : State} (F : VG.Proof.AesOcb.AArch64.FillInv K W D R n SP ciph l A a s₀ j c t 0) :
    WP isa (.loop hashFill (.nonzero .x .x15)) t fun t' => VG.Proof.AesOcb.AArch64.FillInv K W D R n SP ciph l A a s₀ j c t' c := by
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧ VG.Proof.AesOcb.AArch64.FillInv K W D R n SP ciph l A a s₀ j c u i) ?_ (c - 0) _
    ⟨0, rfl, hc0, F⟩
  rintro k u ⟨i, rfl, hi, F⟩
  refine WP.mono (VG.Proof.AesOcb.AArch64.fill_step C hc hjc hi F) fun u' F' => ?_
  have ev := eval_nonzero F'.x15 (by omega)
  by_cases he : i + 1 = c
  · left; exact ⟨ev.trans (by simp; omega), he ▸ F'⟩
  · right; exact ⟨ev.trans (by simp; omega), c - (i + 1), by omega, i + 1, rfl, by omega, F'⟩

/-! ## Adding the buffer to the sum -/

theorem bufStart_ok {W : Addr} {t : State} (h19 : t.gpr .x19 = W) {c : Nat} (h24 : t.gpr .x24 = BitVec.ofNat 64 c) :
    ∃ t', runBlock isa bufStart t = some t' ∧ t'.gpr .x15 = BitVec.ofNat 64 (c - 0) ∧
      t'.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * 0) ∧
      (∀ r, r ≠ .x15 → r ≠ .x27 → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
  refine ⟨_, by orun [bufStart, h19], ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h24]
  · simp [gpr_write, h19]
  · simp [gpr_write, h1, h2]
  all_goals rfl

/-- `x` XORed with `g 0`, …, `g (k − 1)`. -/
def sumOf (x : Block) (g : Nat → Block) : Nat → Block
  | 0 => x
  | k + 1 => VG.Proof.AesOcb.AArch64.sumOf x g k ^^^ g k

theorem hsum_add (ciph : Cipher) (l : Block) (a : List Byte) (j : Nat) :
    ∀ c, hsum ciph l a (j + c) =
      VG.Proof.AesOcb.AArch64.sumOf (hsum ciph l a j) (fun k => ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1))) c
  | 0 => rfl
  | c + 1 => by rw [← Nat.add_assoc, hsum, VG.Proof.AesOcb.AArch64.hsum_add ciph l a j c]; rfl

/-- The sum loop after `k` of the `c` blocks of the buffer. -/
theorem sumStep_ok {W : Addr} {t : State} (h19 : t.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] t.wr) {k c : Nat}
    (hk : k < c) (hc : c ≤ 8) (h27 : t.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * k))
    (h15 : t.gpr .x15 = BitVec.ofNat 64 (c - k)) :
    ∃ t', runBlock isa (xor16 .x27 0 sumO ++ [Impl.AesGcm.AArch64.ptr .x27 .x27 16, .subImm .x .x15 .x15 1]) t =
        some t' ∧
      VG.Proof.AesOcb.AArch64.BlkStep W sumO (blockAtMem t.mem (W + BitVec.ofNat 64 sumO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k))) [.x9, .x10, .x11, .x12, .x15, .x27] t t' ∧
      t'.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * (k + 1)) ∧ t'.gpr .x15 = BitVec.ofNat 64 (c - (k + 1)) := by
  have e0 : W + BitVec.ofNat 64 (384 + 16 * k) + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 (384 + 16 * k) :=
    BitVec.add_zero _
  obtain ⟨t₁, run₁, B₁⟩ := VG.Proof.AesOcb.AArch64.xor16_ok (s := t) (b := .x27) (a := 0) (d := sumO) (by decide) (by decide) h19 h27
    (by decide) (by decide) (by decide) (by rw [e0]; exact in_left (in_off hw (by omega) (by decide)))
    (by rw [Offset.add_add]; exact in_left (in_off hw (by omega) (by decide)))
    (in_off hw (by decide) (by decide)) (in_off hw (by decide) (by decide))
  rw [e0] at B₁
  have h27₁ : t₁.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * k) := by rw [B₁.gpr _ (by decide), h27]
  have h15₁ : t₁.gpr .x15 = BitVec.ofNat 64 (c - k) := by rw [B₁.gpr _ (by decide), h15]
  refine ⟨_, by rw [VG.Proof.AesOcb.AArch64.runBlock_append, run₁, Option.bind_some]; orun [h27₁, h15₁], ?_, ?_, ?_⟩
  · refine ⟨B₁.frame, B₁.val, fun r hr => ?_, B₁.sp, B₁.rd, B₁.wr⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
    exact B₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1])
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27₁, Offset.add_add]
    rw [show 384 + 16 * k + 16 = 384 + 16 * (k + 1) by omega]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h15₁]
    rw [Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]

theorem hashSum_ok {K W : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {t : State} (h19 : t.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] t.wr)
    {c : Nat} (hc0 : 0 < c) (hc : c ≤ 8) (h24 : t.gpr .x24 = BitVec.ofNat 64 c) {g : Nat → Block}
    (hg : ∀ k < c, blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k)) = g k) :
    WP isa hashSum t fun t' => Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = VG.Proof.AesOcb.AArch64.sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g c ∧
      (∀ r, r ∉ [.x9, .x10, .x11, .x12, .x15, .x27] → t'.gpr r = t.gpr r) ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
  obtain ⟨t₁, run₁, x15₁, x27₁, g₁, m₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.AArch64.bufStart_ok h19 h24
  unfold hashSum
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧
      u.gpr .x27 = W + BitVec.ofNat 64 (384 + 16 * i) ∧ u.gpr .x15 = BitVec.ofNat 64 (c - i) ∧
      Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem u.mem ∧
      blockAtMem u.mem (W + BitVec.ofNat 64 sumO) = VG.Proof.AesOcb.AArch64.sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g i ∧
      (∀ r, r ∉ [.x9, .x10, .x11, .x12, .x15, .x27] → u.gpr r = t.gpr r) ∧ u.sp = t.sp ∧ u.rd = t.rd ∧
      u.wr = t.wr) ?_ (c - 0) _
    ⟨0, rfl, hc0, x27₁, x15₁, by rw [m₁]; exact Frame.refl _ _, by rw [m₁]; rfl, fun r hr => g₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.2.2.2.2.1)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.2.2.2.2.2), sp₁, rd₁,
      wr₁⟩
  rintro k u ⟨i, rfl, hi, x27, x15, fr, sum, gu, sp, rd, wr⟩
  obtain ⟨u', run', B, x27', x15'⟩ := VG.Proof.AesOcb.AArch64.sumStep_ok (by rw [gu _ (by decide), h19]) (by rw [wr]; exact hw) hi hc x27 x15
  refine WP.of_runBlock ⟨u', run', ?_⟩
  have hbuf : blockAtMem u.mem (W + BitVec.ofNat 64 (384 + 16 * i)) = g i := by
    rw [blockAtMem_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 384 + 16 * i) (n := 16) (d := 48) (k := 16) (.inr (by omega)) (by omega) (by decide),
      hg i hi]
  have fr' : Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem u'.mem := fr.trans B.frame
  have sum' : blockAtMem u'.mem (W + BitVec.ofNat 64 sumO) = VG.Proof.AesOcb.AArch64.sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g (i + 1) := by
    rw [B.val, sum, hbuf]; rfl
  have gu' : ∀ r, r ∉ [.x9, .x10, .x11, .x12, .x15, .x27] → u'.gpr r = t.gpr r := fun r hr => by
    rw [B.gpr r hr, gu r hr]
  have ev := eval_nonzero x15' (by omega)
  by_cases he : i + 1 = c
  · left
    exact ⟨ev.trans (by simp; omega), fr', he ▸ sum', gu', by rw [B.sp, sp], by rw [B.rd, rd], by rw [B.wr, wr]⟩
  · right
    exact ⟨ev.trans (by simp; omega), c - (i + 1), by omega, i + 1, rfl, by omega, x27', x15', fr',
      sum', gu', by rw [B.sp, sp], by rw [B.rd, rd], by rw [B.wr, wr]⟩

/-! ## A chunk -/

/-- `x9 ← (x26 − 8) ⋙ 63`: 1 if fewer than 8 blocks are left. -/
theorem lt8 {L : Nat} (hL : L < 2 ^ 63) :
    (BitVec.ofNat 64 L - 8#64) >>> 63 = BitVec.ofNat 64 (if L < 8 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, toNat_ofNat_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

/-- The number of blocks of a chunk: `x24 ← min(8, x26)`. -/
theorem chunkHead_ok {t : State} {L : Nat} (hL : L < 2 ^ 63) (h26 : t.gpr .x26 = BitVec.ofNat 64 L) :
    WP isa (.seq (.block [.subImm .x .x9 .x26 8, .lsr .x .x9 .x9 63, Impl.AesGcm.AArch64.mov .x24 .x26])
      (.ite (.zero .x .x9) (.block [Impl.AesGcm.AArch64.imm .x24 8]) (.block []))) t fun t' =>
      t'.gpr .x24 = BitVec.ofNat 64 (min 8 L) ∧ (∀ r, r ≠ .x9 → r ≠ .x24 → t'.gpr r = t.gpr r) ∧
      t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨t₁, run₁, x9₁, x24₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa
      [.subImm .x .x9 .x26 8, .lsr .x .x9 .x9 63, Impl.AesGcm.AArch64.mov .x24 .x26] t = some t₁ ∧
      t₁.gpr .x9 = BitVec.ofNat 64 (if L < 8 then 1 else 0) ∧ t₁.gpr .x24 = BitVec.ofNat 64 L ∧
      (∀ r, r ≠ .x9 → r ≠ .x24 → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
    refine ⟨_, by orun [h26], ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, h26, VG.Proof.AesOcb.AArch64.lt8 hL]
    · simp [gpr_write, h26]
    · simp [gpr_write, h1, h2]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  by_cases h8 : L < 8
  · simp only [h8, ↓reduceIte] at x9₁
    refine WP.ite false (by rw [eval_zero x9₁ (by decide)]; rfl) (fun h => by cases h) (fun _ => ?_)
    exact WP.block_nil ⟨by rw [x24₁, Nat.min_eq_right (by omega)], g₁, m₁, sp₁, rd₁, wr₁⟩
  · simp only [h8, ↓reduceIte] at x9₁
    refine WP.ite true (by rw [eval_zero x9₁ (by decide)]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine Proof.AesGcm.AArch64.WP.run (Q := fun t' => t' = t₁.write .x .x24 (BitVec.ofNat 64 8)) ⟨_, by orun [], rfl⟩ fun t' ht' => ?_
    subst ht'
    refine ⟨by simp [gpr_write, Nat.min_eq_left (show 8 ≤ L by omega)], fun r h1 h2 => ?_, m₁, sp₁, rd₁, wr₁⟩
    simp only [gpr_write, h2, ite_false]; exact g₁ r h1 h2

/-- The `c` blocks of the buffer. -/
theorem bufArgs_ok {W : Addr} {t : State} (h19 : t.gpr .x19 = W) {c : Nat} (h24 : t.gpr .x24 = BitVec.ofNat 64 c) :
    VG.Proof.AesOcb.AArch64.ArgsOk [Impl.AesGcm.AArch64.ptr .x2 .x19 bufO, Impl.AesGcm.AArch64.mov .x3 .x24] t (W + BitVec.ofNat 64 384) c := by
  refine ⟨_, by orun [h19, h24], ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h19]
  · simp [gpr_write, h24]
  · simp [gpr_write, h1, h2]
  all_goals rfl

/-- `bufStart`: the fill loop before its first block. -/
theorem bufStart_inv {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} {t : State} {j c : Nat}
    (H : VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ t j) (h24 : t.gpr .x24 = BitVec.ofNat 64 c) :
    ∃ t₁, runBlock isa bufStart t = some t₁ ∧ VG.Proof.AesOcb.AArch64.FillInv K W D R n SP ciph l A a s₀ j c t₁ 0 := by
  obtain ⟨t₁, run₁, x15₁, x27₁, g₁, m₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.AArch64.bufStart_ok H.env.x19 h24
  exact ⟨t₁, run₁,
    { env := H.env.others (rs := [.x15, .x27]) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact g₁ r hr.1 hr.2) sp₁ rd₁ wr₁
      frame := by rw [m₁]; exact H.frame
      rd := by rw [rd₁, H.rd]
      wr := by rw [wr₁, H.wr]
      x23 := by rw [g₁ _ (by decide) (by decide), H.x23]; rfl
      x25 := by rw [g₁ _ (by decide) (by decide), H.x25]
      x27 := x27₁
      x15 := x15₁
      x24 := by rw [g₁ _ (by decide) (by decide), h24]
      x26 := by rw [g₁ _ (by decide) (by decide), H.x26]
      oh := by rw [m₁, H.oh]; rfl
      buf := fun k hk => absurd hk (Nat.not_lt_zero _)
      sum := by rw [m₁, H.sum]
      l0 := by rw [m₁, H.l0] }⟩

/-- A chunk from `bufStart` on, with its `c` blocks in `x24`. -/
theorem chunkRest_ok (v : BlocksImpl) {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph l A a s₀) {t : State} {j c : Nat}
    (H : VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ t j) (hc0 : 0 < c) (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16)
    (h24 : t.gpr .x24 = BitVec.ofNat 64 c) :
    WP isa (.seq (.block bufStart) (.seq (.loop hashFill (.nonzero .x .x15))
        (.seq (callBlocks (VG.Proof.AesOcb.AArch64.callees v).enc [Impl.AesGcm.AArch64.ptr .x2 .x19 bufO, Impl.AesGcm.AArch64.mov .x3 .x24])
          (.seq hashSum (.block [.sub .x .x26 .x26 .x24]))))) t
      fun t' => VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ t' (j + c) := by
  have L := C.lay
  have hs := C.short
  obtain ⟨t₁, run₁, F₀⟩ := VG.Proof.AesOcb.AArch64.bufStart_inv H h24
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.fill_ok C hc0 hc hjc F₀) fun t₂ F => ?_)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNoFrames L F.env
    C.rounds (VG.Proof.AesOcb.AArch64.bufArgs_ok F.env.x19 F.x24) (VG.Proof.AesOcb.AArch64.dstW L F.env.perm (d := 384) (n := c) (by omega)))
    fun t₃ P₃ => ?_)
  have E₃ := F.env.of_saved P₃.saved P₃.sp P₃.rd P₃.wr
  have F₃ : Frame (VG.Proof.AesOcb.AArch64.hashR W) t₂.mem t₃.mem := P₃.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, Offset.sub W (e := 384) (k := 2176) (by decide) (by omega)⟩
    · exact ⟨_, by simp, Offset.sub W (e := 384) (k := 2176) (by decide) (by decide)⟩
  have k₃ : ∀ {d : Nat}, d + 16 ≤ 384 → blockAtMem t₃.mem (W + BitVec.ofNat 64 d) = blockAtMem t₂.mem (W + BitVec.ofNat 64 d) :=
    fun hd => blockAtMem_frame P₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by omega)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  have hg : ∀ k < c, blockAtMem t₃.mem (W + BitVec.ofNat 64 (384 + 16 * k)) =
      ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)) := fun k hk => by
    have := P₃.enc hk
    rw [Offset.add_add] at this
    rw [this, F.buf k hk]
    exact congrFun (C.ciph' (VG.Proof.AesOcb.AArch64.hashR_mut F.frame)) _
  have h24₃ : t₃.gpr .x24 = BitVec.ofNat 64 c := by rw [P₃.saved _ (by decide) (by decide), F.x24]
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.hashSum_ok L E₃.x19 E₃.perm.w hc0 hc h24₃ hg) fun t₄ ⟨fr₄, sum₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
  have E₄ := E₃.others g₄ sp₄ rd₄ wr₄
  have k₄ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ 64 ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t₄.mem (W + BitVec.ofNat 64 d) = blockAtMem t₃.mem (W + BitVec.ofNat 64 d) := fun h₁ h₂ =>
    blockAtMem_frame fr₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (a := _) (d := 48) (k := 16) (by omega) h₂ (by decide)
  have h24₄ : t₄.gpr .x24 = BitVec.ofNat 64 c := by rw [g₄ _ (by decide), h24₃]
  have h26₄ : t₄.gpr .x26 = BitVec.ofNat 64 (a.length / 16 - j) := by
    rw [g₄ _ (by decide), P₃.saved _ (by decide) (by decide), F.x26]
  refine Proof.AesGcm.AArch64.WP.run (Q := fun t' => t' = t₄.write .x .x26 (t₄.gpr .x26 - t₄.gpr .x24)) ⟨_, by orun [], rfl⟩ fun t' ht' => ?_
  subst ht'
  refine
    { env := E₄.others (rs := [.x26]) (fun r hr => by simp at hr; simp [gpr_write, hr]) rfl rfl rfl
      frame := F.frame.trans (F₃.trans (fr₄.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., fun _ h => h⟩))
      rd := by rw [rd_write, rd₄, P₃.rd, F.rd]
      wr := by rw [wr_write, wr₄, P₃.wr, F.wr]
      le := by omega
      sum := by rw [mem_write, sum₄, k₃ (by decide), F.sum, VG.Proof.AesOcb.AArch64.hsum_add]
      oh := by rw [mem_write, k₄ (by simp only [ohO]; omega) (by decide), k₃ (by decide), F.oh]
      x23 := by
        rw [gpr_write_of_ne _ _ _ (by decide), g₄ _ (by decide), P₃.saved _ (by decide) (by decide), F.x23]
      x25 := by
        rw [gpr_write_of_ne _ _ _ (by decide), g₄ _ (by decide), P₃.saved _ (by decide) (by decide), F.x25]
      x26 := by
        rw [gpr_write_self, h26₄, h24₄, BitVec.setWidth_eq, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
      l0 := by rw [mem_write, k₄ (by simp only [l0O]; omega) (by decide), k₃ (by decide), F.l0] }

/-- `HInv` after `chunkHead`, which writes only `x9` and `x24`. -/
theorem HInv.head {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} {t t₁ : State} {j : Nat}
    (H : VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ t j) (g₁ : ∀ r, r ≠ .x9 → r ≠ .x24 → t₁.gpr r = t.gpr r)
    (m₁ : t₁.mem = t.mem) (sp₁ : t₁.sp = t.sp) (rd₁ : t₁.rd = t.rd) (wr₁ : t₁.wr = t.wr) :
    VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ t₁ j :=
  { H with
    env := H.env.others (rs := [.x9, .x24]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact g₁ r hr.1 hr.2) sp₁ rd₁ wr₁
    frame := by rw [m₁]; exact H.frame
    rd := by rw [rd₁, H.rd]
    wr := by rw [wr₁, H.wr]
    sum := by rw [m₁, H.sum]
    oh := by rw [m₁, H.oh]
    x23 := by rw [g₁ _ (by decide) (by decide), H.x23]
    x25 := by rw [g₁ _ (by decide) (by decide), H.x25]
    x26 := by rw [g₁ _ (by decide) (by decide), H.x26]
    l0 := by rw [m₁, H.l0] }

theorem hashChunk_ok (v : BlocksImpl) {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph l A a s₀) {t : State} {j : Nat}
    (H : VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ t j) (hj : j < a.length / 16) :
    WP isa (hashChunk (VG.Proof.AesOcb.AArch64.callees v)) t fun t' =>
      VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ t' (j + min 8 (a.length / 16 - j)) := by
  have hs := C.short
  unfold hashChunk
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.chunkHead_ok (L := a.length / 16 - j) (by omega) H.x26)
    fun t₁ ⟨h24, g₁, m₁, sp₁, rd₁, wr₁⟩ => ?_))
  exact VG.Proof.AesOcb.AArch64.chunkRest_ok v C (H.head g₁ m₁ sp₁ rd₁ wr₁) (by omega) (by omega) (by omega) h24

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Hash`. -/
section

/-!
# AES-OCB on AArch64: `HASH` (`hash`)

Untrusted: everything here is checked by Lean. `hash` zeroes the sum and the
offset, loads the associated data and its length from `W`, takes the whole
blocks a chunk at a time (`hashChunk_ok`), and the rest, padded, XORed with
`Offset_m ⊕ L_*` and enciphered (`hashRest_ok`): the sum is §4.1's
`HASH(K, A)` (`hash_ok`, `Proof.Ocb.hash_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt hsum blockAtMem_frame)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (in_left in_off eval_zero eval_nonzero toNat_ofNat_of_lt lsr_ofNat and15)

/-- The padded rest of the associated data, after its `m` whole blocks. -/
theorem hashRest_ok (v : BlocksImpl) {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph l A a s₀) {t : State}
    (H : VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ t (a.length / 16)) (hr : 0 < a.length % 16)
    (h24 : t.gpr .x24 = BitVec.ofNat 64 (a.length % 16)) :
    WP isa (hashRest (VG.Proof.AesOcb.AArch64.callees v)) t fun t' => VG.Proof.AesOcb.AArch64.Env K W D R n SP t' ∧ Frame (VG.Proof.AesOcb.AArch64.hashR W) s₀.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  have L := C.lay
  have E := H.env
  have hs := C.short
  generalize hm : a.length / 16 = m at H
  have hrest : a.length - 16 * m = a.length % 16 := by omega
  -- `Offset_m ⊕ L_*`
  obtain ⟨t₁, run₁, B₁⟩ := VG.Proof.AesOcb.AArch64.xor16_ok (s := t) (b := .x20) (a := 240) (d := ohO) (by decide) (by decide) E.x19 E.x20
    (by decide) (by decide) (by decide) (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide))
    (E.perm.wW (by decide))
  have E₁ := E.others B₁.gpr B₁.sp B₁.rd B₁.wr
  have oh₁ : blockAtMem t₁.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [B₁.val, H.oh, ← C.lstar' (VG.Proof.AesOcb.AArch64.hashR_mut H.frame)]; rfl
  have fr₁ : Frame (VG.Proof.AesOcb.AArch64.hashR W) s₀.mem t₁.mem := H.frame.trans (B₁.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩)
  -- `pad(A_*)`
  have hB := C.buf.slice (a := 16 * m) (k := a.length % 16) (by omega)
  have hS : Covers [⟨A + BitVec.ofNat 64 (16 * m), a.length % 16⟩] (t₁.rd ++ t₁.wr) := by
    rw [B₁.rd, B₁.wr, H.rd, H.wr]; exact hB.rd
  have hSD : (⟨A + BitVec.ofNat 64 (16 * m), a.length % 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 bufO, 16⟩ :=
    hB.w.sub_right (Lay.wSub (by decide))
  have hrestb : bytesAt t₁.mem (A + BitVec.ofNat 64 (16 * m)) (a.length % 16) = a.drop (16 * m) := by
    have hd := Proof.Ocb.bytesAt_drop s₀.mem A (a := 16 * m) (n := a.length) (by omega)
    rw [C.aad, hrest] at hd
    rw [Proof.Cmac.bytesAt_frame (VG.Proof.AesOcb.AArch64.hashR_mut (D := D) (n := n) fr₁) (fun r hr =>
      (C.a_mut r hr).sub_left (Offset.sub_base A (by omega))) (by omega), hd]
  unfold hashRest
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.padTo_ok E₁.x19 E₁.perm.w hr (by omega) (by decide)
    (by rw [B₁.gpr _ (by decide), H.x23]) (by rw [B₁.gpr _ (by decide), h24]) hS hSD)
    fun t₂ ⟨fr₂, pad₂, g₂, sp₂, rd₂, wr₂⟩ => ?_)
  rw [hrestb] at pad₂
  have E₂ := E₁.others g₂ sp₂ rd₂ wr₂
  have oh₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [blockAtMem_frame fr₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide), oh₁]
  -- XORed with the offset
  obtain ⟨t₃, run₃, B₃⟩ := VG.Proof.AesOcb.AArch64.xor16_ok (s := t₂) (b := .x19) (a := ohO) (d := bufO) (by decide) (by decide) E₂.x19
    E₂.x19 (by decide) (by decide) (by decide) (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide))
    (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  have E₃ := E₂.others B₃.gpr B₃.sp B₃.rd B₃.wr
  have buf₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 bufO) = pad (a.drop (16 * m)) ^^^ (offAt 0 l m ^^^ l) := by
    rw [B₃.val, pad₂, oh₂]
  have fr₃ : Frame (VG.Proof.AesOcb.AArch64.hashR W) s₀.mem t₃.mem := fr₁.trans ((fr₂.trans B₃.frame).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, Offset.sub W (e := 384) (k := 2176) (by decide) (by decide)⟩)
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  -- enciphered
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNoFrames L E₃
    C.rounds (VG.Proof.AesOcb.AArch64.oneBlock_ok E₃.x19 bufO (by decide)) (VG.Proof.AesOcb.AArch64.dstW L E₃.perm (d := bufO) (n := 1) (by decide))) fun t₄ P₄ => ?_)
  have E₄ := E₃.of_saved P₄.saved P₄.sp P₄.rd P₄.wr
  have buf₄ : blockAtMem t₄.mem (W + BitVec.ofNat 64 bufO) = ciph (pad (a.drop (16 * m)) ^^^ (offAt 0 l m ^^^ l)) := by
    rw [P₄.enc0, buf₃]
    exact congrFun (C.ciph' (VG.Proof.AesOcb.AArch64.hashR_mut fr₃)) _
  have fr₄ : Frame (VG.Proof.AesOcb.AArch64.hashR W) s₀.mem t₄.mem := fr₃.trans (P₄.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, Offset.sub W (e := 384) (k := 2176) (by decide) (by decide)⟩
    · exact ⟨_, by simp, Offset.sub W (e := 384) (k := 2176) (by decide) (by decide)⟩)
  have kSum : ∀ {u u' : State}, Frame [⟨W + BitVec.ofNat 64 bufO, 16⟩] u.mem u'.mem →
      blockAtMem u'.mem (W + BitVec.ofNat 64 sumO) = blockAtMem u.mem (W + BitVec.ofNat 64 sumO) := fun h =>
    blockAtMem_frame h fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have sum₄ : blockAtMem t₄.mem (W + BitVec.ofNat 64 sumO) = hsum ciph l a m := by
    rw [blockAtMem_frame P₄.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)),
      kSum B₃.frame, kSum fr₂, blockAtMem_frame B₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), H.sum]
  -- added to the sum
  obtain ⟨t₅, run₅, B₅⟩ := VG.Proof.AesOcb.AArch64.xor16_ok (s := t₄) (b := .x19) (a := bufO) (d := sumO) (by decide) (by decide) E₄.x19
    E₄.x19 (by decide) (by decide) (by decide) (E₄.perm.wR (by decide)) (E₄.perm.wR (by decide))
    (E₄.perm.wW (by decide)) (E₄.perm.wW (by decide))
  refine WP.of_runBlock ⟨t₅, run₅, E₄.others B₅.gpr B₅.sp B₅.rd B₅.wr, fr₄.trans (B₅.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩), ?_,
    by rw [B₅.rd, P₄.rd, B₃.rd, rd₂, B₁.rd, H.rd], by rw [B₅.wr, P₄.wr, B₃.wr, wr₂, B₁.wr, H.wr]⟩
  rw [B₅.val, sum₄, buf₄, Proof.Ocb.hash_eq]
  have hlen : (a.drop (16 * m)).length = a.length % 16 := by simp; omega
  simp only [hlen, show a.length % 16 > 0 from hr, ↓reduceIte, hm]

/-- The first block of `hash`: the sum and the offset zeroed, the associated
data and its length loaded. -/
theorem hashHead1_ok {K W : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {s₀ : State} (h19 : s₀.gpr .x19 = W)
    (hw : Covers [⟨W, 2560⟩] s₀.wr) {A : Addr} {al : Nat}
    (haad : s₀.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 al) :
    ∃ s, runBlock isa (zero16 sumO ++ zero16 ohO ++ [ld .x23 .x19 aadO, ld .x26 .x19 alenO]) s₀ = some s ∧
      s.gpr .x23 = A ∧ s.gpr .x26 = BitVec.ofNat 64 al ∧ (∀ r, r ∉ [.x9, .x23, .x26] → s.gpr r = s₀.gpr r) ∧
      Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩, ⟨W + BitVec.ofNat 64 ohO, 16⟩] s₀.mem s.mem ∧
      blockAtMem s.mem (W + BitVec.ofNat 64 sumO) = 0 ∧ blockAtMem s.mem (W + BitVec.ofNat 64 ohO) = 0 ∧
      s.sp = s₀.sp ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  obtain ⟨s₁, run₁, B₁⟩ := VG.Proof.AesOcb.AArch64.zero16_ok (s := s₀) (d := sumO) (by decide) h19 (in_off hw (by decide) (by decide))
    (in_off hw (by decide) (by decide))
  have h19₁ : s₁.gpr .x19 = W := by rw [B₁.gpr _ (by decide), h19]
  obtain ⟨s₂, run₂, B₂⟩ := VG.Proof.AesOcb.AArch64.zero16_ok (s := s₁) (d := ohO) (by decide) h19₁ (by rw [B₁.wr]; exact in_off hw (by decide) (by decide))
    (by rw [B₁.wr]; exact in_off hw (by decide) (by decide))
  have h19₂ : s₂.gpr .x19 = W := by rw [B₂.gpr _ (by decide), h19₁]
  have kA : ∀ {d : Nat}, (d + 8 ≤ 48 ∨ (64 ≤ d ∧ d + 8 ≤ 144) ∨ 160 ≤ d) → d + 8 ≤ 2560 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₀.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ => by
    rw [B₂.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := _) (d := 144) (k := 16) (by omega) h₂ (by decide)) (by decide),
      B₁.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := _) (d := 48) (k := 16) (by omega) h₂ (by decide)) (by decide)]
  have haad₂ := (kA (d := aadO) (by decide) (by decide)).trans haad
  have halen₂ := (kA (d := alenO) (by decide) (by decide)).trans halen
  have r₁ : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 aadO) 8 := by
    rw [B₂.rd, B₂.wr, B₁.rd, B₁.wr]; exact in_left (in_off hw (by decide) (by decide))
  have r₂ : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 alenO) 8 := by
    rw [B₂.rd, B₂.wr, B₁.rd, B₁.wr]; exact in_left (in_off hw (by decide) (by decide))
  simp only [aadO, alenO] at haad₂ halen₂ r₁ r₂
  refine ⟨_, by rw [VG.Proof.AesOcb.AArch64.runBlock_append, VG.Proof.AesOcb.AArch64.runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some]; orun [h19₂,
    r₁, r₂], ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, haad₂]
  · simp [gpr_write, halen₂]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.2.1, hr.2.2, ite_false]
    rw [B₂.gpr r (by simp [hr.1]), B₁.gpr r (by simp [hr.1])]
  · exact (B₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  · simp only [mem_write]
    rw [blockAtMem_frame B₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), B₁.val]
  · simp only [mem_write]; exact B₂.val
  · simp only [sp_write]; rw [B₂.sp, B₁.sp]
  · simp only [rd_write]; rw [B₂.rd, B₁.rd]
  · simp only [wr_write]; rw [B₂.wr, B₁.wr]

/-- `HASH(K, A)` to `W + sumO`, with `aad` and `aad_len` in `W`: `HInv` at 0. -/
theorem hashHead_ok {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph l A a s₀) (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP s₀)
    (haad : s₀.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length)
    (hl0 : blockAtMem s₀.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (.seq (.block (zero16 sumO ++ zero16 ohO ++ [ld .x23 .x19 aadO, ld .x26 .x19 alenO]))
      (.block [.lsr .x .x26 .x26 4, Impl.AesGcm.AArch64.imm .x25 1])) s₀ fun s =>
      VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ s 0 := by
  have L := C.lay
  have hs := C.short
  obtain ⟨s₁, run₁, x23₁, x26₁, g₁, f₁, sum₁, oh₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.AArch64.hashHead1_ok L E.x19 E.perm.w haad halen
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine Proof.AesGcm.AArch64.WP.run (Q := fun s => s = (s₁.write .x .x26 (s₁.gpr .x26 >>> 4)).write .x .x25
    (BitVec.ofNat 64 1)) ⟨_, by orun [], rfl⟩ fun s hs' => ?_
  subst hs'
  refine
    { env := E.others (rs := [.x9, .x23, .x25, .x26]) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [gpr_write, hr.2.2.1, hr.2.2.2, ite_false]; exact g₁ r (by simp [hr.1, hr.2.1, hr.2.2.2]))
        (by simp only [sp_write]; exact sp₁) (by simp only [rd_write]; exact rd₁) (by simp only [wr_write]; exact wr₁)
      frame := by
        simp only [mem_write]
        exact f₁.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
          · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
      rd := by simp only [rd_write]; exact rd₁
      wr := by simp only [wr_write]; exact wr₁
      le := Nat.zero_le _
      sum := by simp only [mem_write]; rw [sum₁]; rfl
      oh := by simp only [mem_write]; rw [oh₁]; rfl
      x23 := by simp [gpr_write, x23₁]
      x25 := by simp [gpr_write]
      x26 := by simp [gpr_write, x26₁, lsr_ofNat _ _ hs]
      l0 := by
        simp only [mem_write]
        rw [blockAtMem_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact L.w_w (.inr (by decide)) (by decide) (by decide)
          · exact L.w_w (.inl (by decide)) (by decide) (by decide)), hl0] }

/-- The chunks of `HASH`, from the first. -/
theorem hashLoop_ok (v : BlocksImpl) {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph l A a s₀) {t : State}
    (H₀ : VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ t 0) (hm : 0 < a.length / 16) :
    WP isa (.loop (hashChunk (VG.Proof.AesOcb.AArch64.callees v)) (.nonzero .x .x26)) t fun u =>
      VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ u (a.length / 16) := by
  have hs := C.short
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ j, k = a.length / 16 - j ∧ j < a.length / 16 ∧
      VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ u j) ?_ (a.length / 16 - 0) _ ⟨0, rfl, hm, H₀⟩
  rintro k u ⟨j, rfl, hj, H⟩
  refine WP.mono (VG.Proof.AesOcb.AArch64.hashChunk_ok v C H hj) fun u' H' => ?_
  have ev := eval_nonzero H'.x26 (by omega)
  by_cases he : a.length / 16 - (j + min 8 (a.length / 16 - j)) = 0
  · left
    have hje : j + min 8 (a.length / 16 - j) = a.length / 16 := by omega
    exact ⟨ev.trans (by simp [he]), hje ▸ H'⟩
  · right
    exact ⟨ev.trans (by simp [he]), a.length / 16 - (j + min 8 (a.length / 16 - j)), by omega,
      j + min 8 (a.length / 16 - j), rfl, by omega, H'⟩

/-- The length of the rest of the associated data. -/
theorem tailHead_ok {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph l A a s₀)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length) {t : State}
    (H : VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ t (a.length / 16)) :
    WP isa (.block [ld .x24 .x19 alenO, Impl.AesGcm.AArch64.imm .x10 15, .logic .and .x .x24 .x24 .x10]) t
      fun t₁ => VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ t₁ (a.length / 16) ∧
        t₁.gpr .x24 = BitVec.ofNat 64 (a.length % 16) := by
  have hs := C.short
  have r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 alenO) 8 := H.env.perm.wR (by decide)
  have al : t.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length := by
    rw [VG.Proof.AesOcb.AArch64.kept_read C.lay C.dw (VG.Proof.AesOcb.AArch64.hashR_mut H.frame) (by decide), halen]
  simp only [alenO] at r₁ al
  refine Proof.AesGcm.AArch64.WP.run (Q := fun t₁ => t₁ = ((t.write .x .x24 (BitVec.ofNat 64 a.length)).write .x .x10
    (BitVec.ofNat 64 15)).write .x .x24 (BitVec.ofNat 64 a.length &&& BitVec.ofNat 64 15))
    ⟨_, by orun [H.env.x19, r₁, al], rfl⟩ fun t₁ ht₁ => ?_
  subst ht₁
  refine ⟨{ H with
      env := H.env.others (rs := [.x10, .x24]) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr.1, hr.2])
        rfl rfl rfl
      frame := H.frame
      x23 := by simp [gpr_write, H.x23]
      x25 := by simp [gpr_write, H.x25]
      x26 := by simp [gpr_write, H.x26] }, ?_⟩
  simp [gpr_write, and15, toNat_ofNat_of_lt hs]

/-- After the whole blocks: the rest, if any. -/
theorem hashTail_ok (v : BlocksImpl) {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block}
    {A : Addr} {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph l A a s₀)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length) {t : State}
    (H : VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ t (a.length / 16)) :
    WP isa (.seq (.block [ld .x24 .x19 alenO, Impl.AesGcm.AArch64.imm .x10 15, .logic .and .x .x24 .x24 .x10])
      (.ite (.zero .x .x24) (.block []) (hashRest (VG.Proof.AesOcb.AArch64.callees v)))) t fun t' => VG.Proof.AesOcb.AArch64.Env K W D R n SP t' ∧
        Frame (VG.Proof.AesOcb.AArch64.hashR W) s₀.mem t'.mem ∧
        blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  have hs := C.short
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.tailHead_ok C halen H) fun t₁ ⟨H₁, h24⟩ => ?_)
  refine WP.ite (decide (a.length % 16 = 0)) (eval_zero h24 (by omega)) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : a.length % 16 = 0 := of_decide_eq_true hb
    refine ⟨H₁.env, H₁.frame, ?_, H₁.rd, H₁.wr⟩
    rw [H₁.sum, Proof.Ocb.hash_eq]
    have hlen : (a.drop (16 * (a.length / 16))).length = 0 := by simp; omega
    simp [hlen]
  · exact VG.Proof.AesOcb.AArch64.hashRest_ok v C H₁ (by have := of_decide_eq_false hb; omega) h24

/-- The chunks, if any. -/
theorem hashBody_ok (v : BlocksImpl) {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph l A a s₀) {t : State}
    (H₀ : VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ t 0) :
    WP isa (.ite (.zero .x .x26) (.block []) (.loop (hashChunk (VG.Proof.AesOcb.AArch64.callees v)) (.nonzero .x .x26))) t fun u =>
      VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph l A a s₀ u (a.length / 16) := by
  have hs := C.short
  refine WP.ite (decide (a.length / 16 = 0)) (eval_zero H₀.x26 (by omega)) (fun hb => WP.block_nil ?_)
    (fun hb => VG.Proof.AesOcb.AArch64.hashLoop_ok v C H₀ (Nat.pos_of_ne_zero (of_decide_eq_false hb)))
  exact (of_decide_eq_true hb) ▸ H₀

/-- `HASH(K, A)` to `W + sumO`, with `aad` and `aad_len` in `W + aadO` and
`W + alenO`. -/
theorem hash_ok (v : BlocksImpl) {K W D : Addr} {n R : Nat} {SP : Addr} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph l A a s₀) (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP s₀)
    (haad : s₀.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length)
    (hl0 : blockAtMem s₀.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (Impl.AesOcb.AArch64.hash (VG.Proof.AesOcb.AArch64.callees v)) s₀ fun t' => VG.Proof.AesOcb.AArch64.Env K W D R n SP t' ∧
      Frame (VG.Proof.AesOcb.AArch64.hashR W) s₀.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  unfold Impl.AesOcb.AArch64.hash
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.hashHead_ok C E haad halen hl0) fun s₃ H₀ => ?_))
  exact WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.hashBody_ok v C H₀) fun u H => VG.Proof.AesOcb.AArch64.hashTail_ok v C halen H)

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Pass`. -/
section

/-!
# AES-OCB on AArch64: a pass over the whole blocks (`pass`)

Untrusted: everything here is checked by Lean. `pass body` goes over the
`m` whole blocks of the data at `D`: for block `i` it computes
`Offset_{i+1}` (`lNtz_ok`, `xor16_ok`), then runs `body` on the block, which
replaces it with `fB` of it and the offset, and the checksum with `fC` of
them (`BodyOk`: `xorOfs`, `addCk ++ xorOfs`, `xorOfs ++ addCk`); `pass_ok`
gives the blocks and the checksum after all `m`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.AArch64 (in_left in_off eval_nonzero toNat_ofNat_of_lt)

/-- The registers a body writes. -/
abbrev bodyRegs : List Reg := [.x9, .x10, .x11, .x12]

/-- What a body does to the block at `B` (in `x23`) and the checksum, with
the offset at `W + ofsO`. -/
def BodyOk (W : Addr) (body : List Instr) (fB : Block → Block → Block) (fC : Block → Block → Block → Block) : Prop :=
  ∀ (t : State) (B : Addr), t.gpr .x23 = B → t.gpr .x19 = W →
    InRegions (t.rd ++ t.wr) B 8 → InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 8) 8 →
    InRegions t.wr B 8 → InRegions t.wr (B + BitVec.ofNat 64 8) 8 →
    InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 16) 8 → InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 24) 8 →
    InRegions t.wr (W + BitVec.ofNat 64 32) 8 → InRegions t.wr (W + BitVec.ofNat 64 40) 8 →
    (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩ →
    ∃ t', runBlock isa body t = some t' ∧
      blockAtMem t'.mem B = fB (blockAtMem t.mem B) (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)) ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) = fC (blockAtMem t.mem (W + BitVec.ofNat 64 ckO))
        (blockAtMem t.mem B) (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)) ∧
      Frame [⟨B, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩] t.mem t'.mem ∧
      (∀ r, r ∉ VG.Proof.AesOcb.AArch64.bodyRegs → t'.gpr r = t.gpr r) ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr

theorem xorOfs_ok {W : Addr} : VG.Proof.AesOcb.AArch64.BodyOk W xorOfs (fun b o => b ^^^ o) (fun c _ _ => c) := by
  intro t B h23 h19 rB₀ rB₈ wB₀ wB₈ rO₀ rO₈ _ _ hBW
  refine ⟨_, by orun [xorOfs, h23, h19, rB₀, rB₈, wB₀, wB₈, rO₀, rO₈], ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩ <;>
    try simp only [mem_write, sp_write, rd_write, wr_write]
  · rw [VG.Proof.AesOcb.AArch64.blockAtMem_store2, show W + 24#64 = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 from (VG.Proof.AesOcb.AArch64.addr8 W 16).symm,
      VG.Proof.AesOcb.AArch64.blockAtMem_xor_words]; rfl
  · rw [blockAtMem_frame (Proof.Cmac.frame_store2 _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hBW.sub_right (Lay.wSub (W := W) (d := 32) (n := 16) (by decide))).symm]
  · exact (Proof.Cmac.frame_store2 _ _ _).mono (by simp)
  · simp only [VG.Proof.AesOcb.AArch64.bodyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]
  all_goals rfl

/-- `addCk`: the checksum XORed with the block at `B`. -/
theorem addCk_ok {W B : Addr} {t : State} (h23 : t.gpr .x23 = B) (h19 : t.gpr .x19 = W)
    (rB₀ : InRegions (t.rd ++ t.wr) B 8) (rB₈ : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 8) 8)
    (wC₀ : InRegions t.wr (W + BitVec.ofNat 64 32) 8) (wC₈ : InRegions t.wr (W + BitVec.ofNat 64 40) 8) :
    ∃ t', runBlock isa addCk t = some t' ∧
      VG.Proof.AesOcb.AArch64.BlkStep W ckO (blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem B) VG.Proof.AesOcb.AArch64.bodyRegs t t' := by
  obtain ⟨t', run, Bk⟩ := VG.Proof.AesOcb.AArch64.xor16_ok (s := t) (b := .x23) (a := 0) (d := ckO) (by decide) (by decide) h19 h23
    (by decide) (by decide) (by decide) (by rw [BitVec.add_zero]; exact rB₀) rB₈ wC₀ wC₈
  rw [BitVec.add_zero] at Bk
  exact ⟨t', run, Bk⟩

theorem blockAtMem_ck {W B : Addr} (hBW : (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩) {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 ckO, 16⟩] m m') : blockAtMem m' B = blockAtMem m B :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hBW.sub_right (Lay.wSub (by decide))

theorem blockAtMem_ofs_ck {W : Addr} {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 ckO, 16⟩] m m') :
    blockAtMem m' (W + BitVec.ofNat 64 ofsO) = blockAtMem m (W + BitVec.ofNat 64 ofsO) :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (d := 16) (n := 16) (e := 32) (k := 16) (.inl (by decide)) (by omega) (by omega)

/-- `seal`'s first pass: the checksum of the block, then the block XORed with the offset. -/
theorem sealPre_ok {W : Addr} :
    VG.Proof.AesOcb.AArch64.BodyOk W (addCk ++ xorOfs) (fun b o => b ^^^ o) (fun c b _ => c ^^^ b) := by
  intro t B h23 h19 rB₀ rB₈ wB₀ wB₈ rO₀ rO₈ wC₀ wC₈ hBW
  obtain ⟨t₁, run₁, B₁⟩ := VG.Proof.AesOcb.AArch64.addCk_ok h23 h19 rB₀ rB₈ wC₀ wC₈
  obtain ⟨t₂, run₂, b₂, c₂, f₂, g₂, sp₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.AArch64.xorOfs_ok t₁ B (by rw [B₁.gpr _ (by decide), h23])
    (by rw [B₁.gpr _ (by decide), h19]) (by rw [B₁.rd, B₁.wr]; exact rB₀) (by rw [B₁.rd, B₁.wr]; exact rB₈)
    (by rw [B₁.wr]; exact wB₀) (by rw [B₁.wr]; exact wB₈) (by rw [B₁.rd, B₁.wr]; exact rO₀)
    (by rw [B₁.rd, B₁.wr]; exact rO₈) (by rw [B₁.wr]; exact wC₀) (by rw [B₁.wr]; exact wC₈) hBW
  refine ⟨t₂, by rw [VG.Proof.AesOcb.AArch64.runBlock_append, run₁, Option.bind_some, run₂], ?_, ?_, ?_, fun r hr => ?_,
    by rw [sp₂, B₁.sp], by rw [rd₂, B₁.rd], by rw [wr₂, B₁.wr]⟩
  · rw [b₂, VG.Proof.AesOcb.AArch64.blockAtMem_ck hBW B₁.frame, VG.Proof.AesOcb.AArch64.blockAtMem_ofs_ck B₁.frame]
  · rw [c₂, B₁.val]
  · exact (B₁.frame.mono (by simp)).trans f₂
  · rw [g₂ r hr, B₁.gpr r hr]

/-- `open`'s third pass: the block XORed with the offset, then its checksum. -/
theorem openPost_ok {W : Addr} :
    VG.Proof.AesOcb.AArch64.BodyOk W (xorOfs ++ addCk) (fun b o => b ^^^ o) (fun c b o => c ^^^ (b ^^^ o)) := by
  intro t B h23 h19 rB₀ rB₈ wB₀ wB₈ rO₀ rO₈ wC₀ wC₈ hBW
  obtain ⟨t₁, run₁, b₁, c₁, f₁, g₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.AArch64.xorOfs_ok t B h23 h19 rB₀ rB₈ wB₀ wB₈ rO₀ rO₈ wC₀ wC₈ hBW
  obtain ⟨t₂, run₂, B₂⟩ := VG.Proof.AesOcb.AArch64.addCk_ok (t := t₁) (by rw [g₁ _ (by decide), h23])
    (by rw [g₁ _ (by decide), h19]) (by rw [rd₁, wr₁]; exact rB₀) (by rw [rd₁, wr₁]; exact rB₈)
    (by rw [wr₁]; exact wC₀) (by rw [wr₁]; exact wC₈)
  refine ⟨t₂, by rw [VG.Proof.AesOcb.AArch64.runBlock_append, run₁, Option.bind_some, run₂], ?_, ?_, ?_, fun r hr => ?_,
    by rw [B₂.sp, sp₁], by rw [B₂.rd, rd₁], by rw [B₂.wr, wr₁]⟩
  · rw [VG.Proof.AesOcb.AArch64.blockAtMem_ck hBW B₂.frame, b₁]
  · rw [B₂.val, c₁, b₁]
  · exact f₁.trans (B₂.frame.mono (by simp))
  · rw [B₂.gpr r hr, g₁ r hr]

/-- The registers a pass writes. -/
abbrev passRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14, .x23, .x24, .x25]

/-- A pass over the `m` whole blocks at `D` (`X k` at its start, `t₀`), after
`i` of them. -/
structure PassInv (K W D : Addr) (R n : Nat) (SP : Addr) (m : Nat) (O0 l : Block) (X : Nat → Block)
    (fB : Block → Block → Block) (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : VG.Proof.AesOcb.AArch64.Env K W D R n SP t
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩,
    ⟨D, 16 * m⟩] t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  x23 : t.gpr .x23 = D + BitVec.ofNat 64 (16 * i)
  x25 : t.gpr .x25 = BitVec.ofNat 64 (i + 1)
  x24 : t.gpr .x24 = BitVec.ofNat 64 (m - i)
  ofs : blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) = offAt O0 l i
  ck : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) =
    if k < i then fB (X k) (offAt O0 l (k + 1)) else X k
  l0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0
  gpr : ∀ r, r ∉ VG.Proof.AesOcb.AArch64.passRegs → t.gpr r = t₀.gpr r

theorem pass_step {K W D : Addr} {R n : Nat} {SP : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : VG.Proof.AesOcb.AArch64.BodyOk W body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : VG.Proof.AesOcb.AArch64.DBuf K W t₀ D (16 * m)) (hm : m < 2 ^ 60) {t : State} {i : Nat} (hi : i < m)
    (P : VG.Proof.AesOcb.AArch64.PassInv K W D R n SP m O0 l X fB ckF t₀ t i) :
    WP isa (.seq nextOffset (.block (body ++ nextBlock))) t fun t' =>
      VG.Proof.AesOcb.AArch64.PassInv K W D R n SP m O0 l X fB ckF t₀ t' (i + 1) := by
  have hDt : VG.Proof.AesOcb.AArch64.DBuf K W t D (16 * m) := hD.of_eq P.rd P.wr
  have hBi := hDt.slice (a := 16 * i) (k := 16) (by omega)
  have E := P.env
  unfold nextOffset
  refine WP.seq (WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.lNtz_ok E.x19 E.perm.w (by omega) (by omega) P.x25 P.l0) fun t₁ P₁ => ?_))
  have h19₁ : t₁.gpr .x19 = W := by rw [P₁.gpr _ (by decide), E.x19]
  obtain ⟨t₂, run₂, B₂⟩ := VG.Proof.AesOcb.AArch64.xor16_ok (s := t₁) (b := .x19) (a := lO) (d := ofsO) (by decide) (by decide) h19₁ h19₁
    (by decide) (by decide) (by decide) (by rw [P₁.rd, P₁.wr]; exact E.perm.wR (by decide))
    (by rw [P₁.rd, P₁.wr]; exact E.perm.wR (by decide))
    (by rw [P₁.wr]; exact E.perm.wW (by decide)) (by rw [P₁.wr]; exact E.perm.wW (by decide))
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  have g₂ : ∀ r, r ∉ VG.Proof.AesOcb.AArch64.ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    rw [B₂.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h | h | h <;> simp [h])),
      P₁.gpr r hr]
  have rd₂ : t₂.rd = t.rd := by rw [B₂.rd, P₁.rd]
  have wr₂ : t₂.wr = t.wr := by rw [B₂.wr, P₁.wr]
  have sp₂ : t₂.sp = t.sp := by rw [B₂.sp, P₁.sp]
  have h19₂ : t₂.gpr .x19 = W := by rw [g₂ _ (by decide), E.x19]
  have h23₂ : t₂.gpr .x23 = D + BitVec.ofNat 64 (16 * i) := by rw [g₂ _ (by decide), P.x23]
  have fW₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ofsO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  have kW₂ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨W, 2560⟩ → blockAtMem t₂.mem Q = blockAtMem t.mem Q :=
    fun hQ => blockAtMem_frame fW₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hQ.sub_right (Lay.wSub (by decide))
  have ofs₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ofsO) = offAt O0 l (i + 1) := by
    rw [B₂.val, blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), P.ofs,
      P₁.val]
    rfl
  have ck₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ckO) = ckF i := by
    rw [blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.ck]
  have Bi₂ : blockAtMem t₂.mem (D + BitVec.ofNat 64 (16 * i)) = X i := by
    rw [kW₂ hBi.w, P.blk i hi]; simp
  obtain ⟨t₃, run₃, blk₃, ck₃, fr₃, g₃, sp₃, rd₃, wr₃⟩ := hB t₂ _ h23₂ h19₂
    (by rw [rd₂, wr₂]; exact hBi.rd _ _ ⟨_, List.mem_singleton_self _,
      by simpa using Offset.contains_base (D + BitVec.ofNat 64 (16 * i)) (d := 0) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [rd₂, wr₂]; exact hBi.rd _ _ ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (d := 8) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [wr₂]; exact hBi.wr _ _ ⟨_, List.mem_singleton_self _,
      by simpa using Offset.contains_base (D + BitVec.ofNat 64 (16 * i)) (d := 0) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [wr₂]; exact hBi.wr _ _ ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (d := 8) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [rd₂, wr₂]; exact E.perm.wR (by decide)) (by rw [rd₂, wr₂]; exact E.perm.wR (by decide))
    (by rw [wr₂]; exact E.perm.wW (by decide)) (by rw [wr₂]; exact E.perm.wW (by decide)) hBi.w
  have g₃' : ∀ r, r ∉ VG.Proof.AesOcb.AArch64.ntzRegs → t₃.gpr r = t.gpr r := fun r hr => by
    rw [g₃ r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h | h | h <;> simp [h])),
      g₂ r hr]
  have x24₃ : t₃.gpr .x24 = BitVec.ofNat 64 (m - i) := by rw [g₃' _ (by decide), P.x24]
  have x25₃ : t₃.gpr .x25 = BitVec.ofNat 64 (i + 1) := by rw [g₃' _ (by decide), P.x25]
  have x23₃ : t₃.gpr .x23 = D + BitVec.ofNat 64 (16 * i) := by rw [g₃' _ (by decide), P.x23]
  have kB₃ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * i), 16⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨W, 2560⟩ → blockAtMem t₃.mem Q = blockAtMem t.mem Q := fun h₁ h₂ => by
    rw [blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂.sub_right (Lay.wSub (by decide))), kW₂ h₂]
  refine Proof.AesGcm.AArch64.WP.run (Q := fun t' => t' = ((t₃.write .x .x23 (t₃.gpr .x23 + 16#64)).write .x .x25
    (t₃.gpr .x25 + 1#64)).write .x .x24 (t₃.gpr .x24 - 1#64))
    ⟨_, by rw [VG.Proof.AesOcb.AArch64.runBlock_append, run₃, Option.bind_some]; orun [nextBlock], rfl⟩ fun t' ht' => ?_
  subst ht'
  have hw := hD.wrap
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, fun r hr => ?_⟩ <;>
    try simp only [mem_write, rd_write, wr_write]
  · exact E.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [gpr_write, reduceCtorEq, ite_false] <;>
        exact g₃' _ (by decide))
      (by simp only [sp_write]; rw [sp₃, sp₂]) (by simp only [rd_write]; rw [rd₃, rd₂])
      (by simp only [wr_write]; rw [wr₃, wr₂])
  · exact P.frame.trans ((fW₂.mono (by simp)).trans (fr₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨D, 16 * m⟩, by simp, Offset.sub_base D (by omega)⟩
      · exact ⟨⟨W + BitVec.ofNat 64 ckO, 16⟩, by simp, fun _ h => h⟩))
  · rw [rd₃, rd₂, P.rd]
  · rw [wr₃, wr₂, P.wr]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x23₃, Offset.add_add]
    rw [show 16 * i + 16 = 16 * (i + 1) by omega]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x25₃, ← BitVec.ofNat_add]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x24₃]
    rw [Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · rw [blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hBi.w.sub_right (Lay.wSub (W := W) (d := 16) (n := 16) (by decide))).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)), ofs₂]
  · rw [ck₃, ck₂, Bi₂, ofs₂, hckF i hi]
  · by_cases hki : k = i
    · subst hki
      rw [blk₃, Bi₂, ofs₂]; simp
    · have hBk := hDt.slice (a := 16 * k) (k := 16) (by omega)
      rw [kB₃ (Offset.disjoint D (by omega) (by omega) (by omega)) hBk.w, P.blk k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega]
      · simp [hk', show ¬ k < i + 1 by omega]
  · rw [blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hBi.w.sub_right (Lay.wSub (W := W) (d := 80) (n := 16) (by decide))).symm
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.l0]
  · simp only [VG.Proof.AesOcb.AArch64.passRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]
    rw [g₃' r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1]),
      P.gpr r (by simp [VG.Proof.AesOcb.AArch64.passRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]

theorem pass_ok {K W D : Addr} {R n : Nat} {SP : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : VG.Proof.AesOcb.AArch64.BodyOk W body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : VG.Proof.AesOcb.AArch64.DBuf K W t₀ D (16 * m)) (hm0 : 0 < m) (hm : m < 2 ^ 60) {t : State}
    (P : VG.Proof.AesOcb.AArch64.PassInv K W D R n SP m O0 l X fB ckF t₀ t 0) :
    WP isa (pass body) t (fun t' => VG.Proof.AesOcb.AArch64.PassInv K W D R n SP m O0 l X fB ckF t₀ t' m) := by
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = m - i ∧ i < m ∧ VG.Proof.AesOcb.AArch64.PassInv K W D R n SP m O0 l X fB ckF t₀ u i) ?_
    (m - 0) _ ⟨0, rfl, hm0, P⟩
  rintro k u ⟨i, rfl, hi, P⟩
  refine WP.mono (VG.Proof.AesOcb.AArch64.pass_step L hB hckF hD hm hi P) fun u' P' => ?_
  have ev := eval_nonzero P'.x24 (by omega)
  by_cases he : m - (i + 1) = 0
  · left
    exact ⟨ev.trans (by simp [he]), (show i + 1 = m by omega) ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp [he]), m - (i + 1), by omega, i + 1, rfl, by omega, P'⟩

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Whole`. -/
section

/-!
# AES-OCB on AArch64: the whole blocks (`whole`)

Untrusted: everything here is checked by Lean. `whole f pre post` runs the
first pass (each block XORed with its offset, `pre`), `f` on all the blocks
(`ENCIPHER` or `DECIPHER`), and the second pass from `Offset_0` again
(`post`), each pass also updating the checksum (`whole_ok`): block `k`
becomes `Offset_{k+1} ⊕ g(X_k ⊕ Offset_{k+1})`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.AArch64 (in_left in_off)

/-- What `whole` writes: the offset and the checksum, `L_{ntz(i)}`, the
working space of the functions called and the data. -/
abbrev wholeR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D, n⟩]

theorem wholeR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (VG.Proof.AesOcb.AArch64.wholeR W D n) m m') :
    Frame (VG.Proof.AesOcb.AArch64.mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesOcb.AArch64.in_mutA (by decide)
  · exact VG.Proof.AesOcb.AArch64.in_mutA (by decide)
  · exact VG.Proof.AesOcb.AArch64.in_mutB (by decide) (by decide)
  · exact VG.Proof.AesOcb.AArch64.in_mutD fun _ h => h

/-- The first `k` bytes of a buffer, as a buffer at the same place. -/
theorem DBuf.take' {K W : Addr} {s : State} {D : Addr} {n k : Nat} (h : VG.Proof.AesOcb.AArch64.DBuf K W s D n) (hk : k ≤ n) :
    VG.Proof.AesOcb.AArch64.DBuf K W s D k := by
  have := h.slice (a := 0) (k := k) (by omega)
  rwa [BitVec.add_zero] at this

/-- The `m` blocks of the data. -/
theorem dataArgs_ok {D : Addr} {t : State} (h21 : t.gpr .x21 = D) {m : Nat} (h26 : t.gpr .x26 = BitVec.ofNat 64 m) :
    VG.Proof.AesOcb.AArch64.ArgsOk [Impl.AesGcm.AArch64.mov .x2 .x21, Impl.AesGcm.AArch64.mov .x3 .x26] t D m := by
  refine ⟨_, by orun [], ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h21]
  · simp [gpr_write, h26]
  · simp [gpr_write, h1, h2]
  all_goals rfl

/-- The start of a pass: `x23 ← D`, `x24 ← m`, `x25 ← 1`. -/
theorem passStart_ok {D : Addr} {t : State} (h21 : t.gpr .x21 = D) {m : Nat} (h26 : t.gpr .x26 = BitVec.ofNat 64 m) :
    ∃ t', runBlock isa [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1] t = some t' ∧
      t'.gpr .x23 = D + BitVec.ofNat 64 (16 * 0) ∧ t'.gpr .x24 = BitVec.ofNat 64 (m - 0) ∧
      t'.gpr .x25 = BitVec.ofNat 64 (0 + 1) ∧
      (∀ r, r ∉ [.x23, .x24, .x25] → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
  refine ⟨_, by orun [], ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h21]
  · simp [gpr_write, h26]
  · simp [gpr_write]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2]
  all_goals rfl

/-- What `whole` leaves. -/
structure WholePost (K W D : Addr) (R n : Nat) (SP : Addr) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block)
    (t t' : State) : Prop where
  env : VG.Proof.AesOcb.AArch64.Env K W D R n SP t'
  frame : Frame (VG.Proof.AesOcb.AArch64.wholeR W D (16 * m)) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) = ck

theorem whole_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : b.code.noFrames = true) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, VG.Proof.AesOcb.AArch64.BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : ∀ {W}, VG.Proof.AesOcb.AArch64.BodyOk W pre (fun b o => b ^^^ o) fC1) (hB2 : ∀ {W}, VG.Proof.AesOcb.AArch64.BodyOk W post (fun b o => b ^^^ o) fC2)
    {K W D : Addr} {R n : Nat} {SP : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {t : State} (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP t)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {m : Nat} (hD : VG.Proof.AesOcb.AArch64.DBuf K W t D n) (hmn : 16 * m ≤ n) (hm0 : 0 < m)
    (hm : m < 2 ^ 60) {O0 l : Block} (h26 : t.gpr .x26 = BitVec.ofNat 64 m)
    (hofs : blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem t.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 m)
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt t.mem K (16 * (R + 1))) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (whole b pre post) t (VG.Proof.AesOcb.AArch64.WholePost K W D R n SP m O0 l
      (fun k => G (bytesAt t.mem K (16 * (R + 1))) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
      (ckF2 m) t) := by
  have hDm := hD.take' hmn
  -- the first pass
  obtain ⟨s₁, run₁, x23₁, x24₁, x25₁, g₁, m₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.AArch64.passStart_ok E.x21 h26
  have E₁ := E.others g₁ sp₁ rd₁ wr₁
  have hD₁ : VG.Proof.AesOcb.AArch64.DBuf K W s₁ D (16 * m) := hDm.of_eq rd₁ wr₁
  have P₀ : VG.Proof.AesOcb.AArch64.PassInv K W D R n SP m O0 l (fun k => blockAtMem s₁.mem (D + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF1 s₁ s₁ 0 :=
    { env := E₁, frame := Frame.refl _ _, rd := rfl, wr := rfl, x23 := x23₁, x25 := x25₁, x24 := x24₁
      ofs := by rw [m₁, hofs]; rfl
      ck := by rw [m₁, hck]
      blk := fun k _ => by simp
      l0 := by rw [m₁, hl0]
      gpr := fun _ _ => rfl }
  unfold whole
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.pass_ok L hB1 (fun i _ => by rw [hckF1, m₁]) hD₁ hm0 hm P₀) fun s₂ P₂ => ?_)
  have hw := hD.wrap
  have h26₂ : s₂.gpr .x26 = BitVec.ofNat 64 m := by rw [P₂.gpr _ (by decide), g₁ _ (by decide), h26]
  have hD₂ : VG.Proof.AesOcb.AArch64.DBuf K W s₂ D (16 * m) := hD₁.of_eq P₂.rd P₂.wr
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.callBlocks_ok (f := f) (b := b) ok nf L P₂.env hR
    (VG.Proof.AesOcb.AArch64.dataArgs_ok P₂.env.x21 h26₂) (VG.Proof.AesOcb.AArch64.dstD hD₂)) fun s₃ P₃ => ?_)
  have E₃ := P₂.env.of_saved P₃.saved P₃.sp P₃.rd P₃.wr
  have kC : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨D, 16 * m⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩ → blockAtMem s₃.mem Q = blockAtMem s₂.mem Q :=
    fun h₁ h₂ => blockAtMem_frame P₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂
  have kWP : ∀ {d : Nat}, (d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 512)) →
      blockAtMem s₃.mem (W + BitVec.ofNat 64 d) = blockAtMem s₁.mem (W + BitVec.ofNat 64 d) := fun hd => by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by omega))).symm) (L.w_w (.inl (by omega)) (by omega) (by decide)),
      blockAtMem_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega) (by omega) (by decide)
      · exact L.w_w (a := _) (d := 16) (k := 16) (by omega) (by omega) (by decide)
      · exact L.w_w (a := _) (d := 32) (k := 16) (by omega) (by omega) (by decide)
      · exact (hD₁.w.sub_right (Lay.wSub (by omega))).symm)]
  have o0₃ : blockAtMem s₃.mem (W + BitVec.ofNat 64 o0O) = O0 := by rw [kWP (by decide), m₁, ho0]
  -- `Offset_0` again
  obtain ⟨s₄a, run₄a, B₄⟩ := VG.Proof.AesOcb.AArch64.copy16_ok (s := s₃) (a := o0O) (d := ofsO) (by decide) (by decide) E₃.x19
    (E₃.perm.wR (by decide)) (E₃.perm.wR (by decide)) (E₃.perm.wW (by decide)) (E₃.perm.wW (by decide))
  have E₄a := E₃.others B₄.gpr B₄.sp B₄.rd B₄.wr
  have h26₄ : s₄a.gpr .x26 = BitVec.ofNat 64 m := by
    rw [B₄.gpr _ (by decide), P₃.saved _ (by decide) (by decide), h26₂]
  obtain ⟨s₄, run₄, x23₄, x24₄, x25₄, g₄, m₄, sp₄, rd₄, wr₄⟩ := VG.Proof.AesOcb.AArch64.passStart_ok E₄a.x21 h26₄
  have E₄ := E₄a.others g₄ sp₄ rd₄ wr₄
  have hD₄ : VG.Proof.AesOcb.AArch64.DBuf K W s₄ D (16 * m) := hD₂.of_eq (by rw [rd₄, B₄.rd, P₃.rd]) (by rw [wr₄, B₄.wr, P₃.wr])
  have kB₄ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨W, 2560⟩ → blockAtMem s₄.mem Q = blockAtMem s₃.mem Q :=
    fun hQ => by
      rw [m₄]; exact blockAtMem_frame B₄.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hQ.sub_right (Lay.wSub (by decide))
  have hK : bytesAt s₂.mem K (16 * (R + 1)) = bytesAt t.mem K (16 * (R + 1)) := by
    have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
    rw [Proof.Cmac.bytesAt_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact hD₁.k.sub_left (Region.sub_prefix hRb)) (by omega), m₁]
  have X₄ : ∀ k < m, blockAtMem s₄.mem (D + BitVec.ofNat 64 (16 * k)) =
      G (bytesAt t.mem K (16 * (R + 1))) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)) :=
    fun k hk => by
      rw [kB₄ (hD₂.slice (a := 16 * k) (k := 16) (by omega)).w, hcall P₃ k hk, hK, P₂.blk k hk]
      simp only [hk, ↓reduceIte, m₁]
  have ck₃ : blockAtMem s₃.mem (W + BitVec.ofNat 64 ckO) = ckF2 0 := by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by decide))).symm) (L.w_w (.inl (by decide)) (by decide) (by decide)),
      P₂.ck, hckF2₀]
  have P₀' : VG.Proof.AesOcb.AArch64.PassInv K W D R n SP m O0 l (fun k => blockAtMem s₄.mem (D + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF2 s₄ s₄ 0 :=
    { env := E₄, frame := Frame.refl _ _, rd := rfl, wr := rfl, x23 := x23₄, x25 := x25₄, x24 := x24₄
      ofs := by rw [m₄, B₄.val, o0₃]; rfl
      ck := by
        rw [m₄, blockAtMem_frame B₄.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), ck₃]
      blk := fun k _ => by simp
      l0 := by
        rw [m₄, blockAtMem_frame B₄.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
          kWP (by decide), m₁, hl0]
      gpr := fun _ _ => rfl }
  refine WP.seq (WP.of_runBlock ⟨s₄, by rw [VG.Proof.AesOcb.AArch64.runBlock_append, run₄a, Option.bind_some, run₄], ?_⟩)
  refine WP.mono (VG.Proof.AesOcb.AArch64.pass_ok L hB2 (fun i hi => by rw [hckF2, X₄ i hi]) hD₄ hm0 hm P₀') fun s₅ P₅ => ?_
  have subW : ∀ r ∈ [(⟨W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ofsO, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨D, 16 * m⟩], ∃ r' ∈ VG.Proof.AesOcb.AArch64.wholeR W D (16 * m), Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (d := 32) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨⟨D, 16 * m⟩, by simp, fun _ h => h⟩
  refine ⟨P₅.env, ?_, by rw [P₅.rd, rd₄, B₄.rd, P₃.rd, P₂.rd, rd₁], by rw [P₅.wr, wr₄, B₄.wr, P₃.wr, P₂.wr, wr₁],
    fun k hk => ?_, P₅.ofs, P₅.ck⟩
  · rw [← m₁]
    refine (P₂.frame.sub subW).trans ((P₃.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨D, 16 * m⟩, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · have F₅ := P₅.frame
      rw [m₄] at F₅
      exact (B₄.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Offset.sub W (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩).trans
        (F₅.sub subW)
  · rw [P₅.blk k hk]
    simp only [hk, ↓reduceIte]
    rw [X₄ k hk]

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.XorPad`. -/
section

/-!
# AES-OCB on AArch64: the rest of the data XORed with `Pad` (`xorPad`)

Untrusted: everything here is checked by Lean. `xorPad` XORs the `r` bytes
at `x23` with the first `r` bytes at `W + tmpO`, with AES-GCM's `xorLoop`
(`xorPad_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (xorLoop_ok in_left in_off covers_off)

/-- The registers `xorPad` writes. -/
abbrev xpRegs : List Reg := [.x11, .x12, .x13, .x14, .x15]

/-- `xorPad`: the `r` bytes at `P` (in `x23`), `0 < r < 16`, XORed with the
first `r` bytes at `W + tmpO`. -/
theorem xorPad_ok {K W : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {P : Addr}
    {r : Nat} (hr : 0 < r) (hr' : r < 16) (h23 : s.gpr .x23 = P) (h24 : s.gpr .x24 = BitVec.ofNat 64 r)
    (hP : VG.Proof.AesOcb.AArch64.DBuf K W s P r) :
    WP isa xorPad s fun t => t.mem = writeBytes s.mem P
        (Spec.Ocb.xor (bytesAt s.mem P r) (bytesAt s.mem (W + BitVec.ofNat 64 112) r)) ∧
      (∀ r, r ∉ VG.Proof.AesOcb.AArch64.xpRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [Impl.AesGcm.AArch64.ptr .x11 .x19 tmpO, Impl.AesGcm.AArch64.mov .x12 .x23,
        Impl.AesGcm.AArch64.mov .x13 .x24] s = some s₁ ∧
      s₁.gpr .x11 = W + BitVec.ofNat 64 112 ∧ s₁.gpr .x12 = P ∧ s₁.gpr .x13 = BitVec.ofNat 64 r ∧
      (∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [], ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, h19]
    · simp [gpr_write, h23]
    · simp [gpr_write, h24]
    · simp [gpr_write, h1, h2, h3]
    all_goals rfl
  unfold xorPad
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have pre : Proof.AesGcm.AArch64.LoopPre s₁ (W + BitVec.ofNat 64 112) P r :=
    ⟨by omega, by rw [rd₁, wr₁]; exact Proof.AesGcm.AArch64.covers_left (covers_off hw (by omega) (by decide)),
      by rw [wr₁]; exact hP.wr, (hP.w.sub_right (Lay.wSub (W := W) (d := 112) (n := r) (by omega))).symm⟩
  refine WP.mono (xorLoop_ok s₁ x11₁ x12₁ x13₁ hr pre) fun t ⟨mt, gt, spt, rdt, wrt⟩ => ?_
  refine ⟨by rw [mt, m₁]; rfl, fun q hq => ?_, by rw [spt, sp₁], by rw [rdt, rd₁], by rw [wrt, wr₁]⟩
  simp only [VG.Proof.AesOcb.AArch64.xpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  rw [gt q (by simp [Proof.AesGcm.AArch64.loopRegs, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2]),
    g₁ q hq.1 hq.2.1 hq.2.2.1]

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.RestTag`. -/
section

/-!
# AES-OCB on AArch64: the rest of the data and the tag (`rest`, `tag`)

Untrusted: everything here is checked by Lean. `rest` computes
`Offset_* = Offset_m ⊕ L_*` and `Pad = ENCIPHER(K, Offset_*)`
(`restHead_ok`), XORs the last bytes with `Pad` (`xorPad_ok`) and adds the
padded plaintext to the checksum (`padCk_ok`), in the order of `seal` or
`open` (`rest_ok`). `tag d` writes
`ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)` to `W + d` (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem pad ctxCiph)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.Ocb (length_bytesAt blockAtMem_frame)

/-- The callee-saved registers but `x30` are unchanged. -/
abbrev Saved (t t' : State) : Prop := ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r

theorem saved_of {t t' : State} {rs : List Reg} (h : ∀ r, r ∉ rs → t'.gpr r = t.gpr r)
    (hd : ∀ r ∈ rs, r ∉ preserved := by decide) : VG.Proof.AesOcb.AArch64.Saved t t' :=
  fun r hr _ => h r fun h' => hd r h' hr

theorem Saved.trans {t₁ t₂ t₃ : State} (h₁ : VG.Proof.AesOcb.AArch64.Saved t₁ t₂) (h₂ : VG.Proof.AesOcb.AArch64.Saved t₂ t₃) : VG.Proof.AesOcb.AArch64.Saved t₁ t₃ :=
  fun r hr h30 => (h₂ r hr h30).trans (h₁ r hr h30)

/-- `padCk`: `W + t2O ← pad(S)` and the checksum XORed with it, for the
`r` bytes `S` at `x23`. -/
theorem padCk_ok {K W : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    {S : Addr} {r : Nat} (hr : 0 < r) (hr' : r < 16) (h23 : s.gpr .x23 = S) (h24 : s.gpr .x24 = BitVec.ofNat 64 r)
    (hS : Covers [⟨S, r⟩] (s.rd ++ s.wr)) (hSW : (⟨S, r⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa padCk s fun t => Frame [⟨W + BitVec.ofNat 64 t2O, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = blockAtMem s.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt s.mem S r) ∧
      (∀ r, r ∉ [.x9, .x10, .x11, .x12, .x13, .x14, .x15] → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  unfold padCk
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.padTo_ok h19 hw hr hr' (by decide) h23 h24 hS (hSW.sub_right (Lay.wSub (by decide))))
    fun t₁ ⟨fr₁, pad₁, g₁, sp₁, rd₁, wr₁⟩ => ?_)
  have h19₁ : t₁.gpr .x19 = W := by rw [g₁ _ (by decide), h19]
  have ww : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions t₁.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => by rw [wr₁]; exact Proof.AesGcm.AArch64.in_off hw h (by decide)
  obtain ⟨t₂, run₂, B₂⟩ := VG.Proof.AesOcb.AArch64.xor16_ok (s := t₁) (b := .x19) (a := t2O) (d := ckO) (by decide) (by decide) h19₁ h19₁
    (by decide) (by decide) (by decide) (by rw [rd₁]; exact Proof.AesGcm.AArch64.in_left (ww (by decide)))
    (by rw [rd₁]; exact Proof.AesGcm.AArch64.in_left (ww (by decide))) (ww (by decide)) (ww (by decide))
  refine WP.of_runBlock ⟨t₂, run₂, (fr₁.mono (by simp)).trans (B₂.frame.mono (by simp)), ?_,
    fun q hq => ?_, by rw [B₂.sp, sp₁], by rw [B₂.rd, rd₁], by rw [B₂.wr, wr₁]⟩
  · rw [B₂.val, pad₁, blockAtMem_frame fr₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [B₂.gpr q (by simp [hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1]),
      g₁ q (by simp [VG.Proof.AesOcb.AArch64.padRegs, hq.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2.1, hq.2.2.2.2.2.2])]

/-- What the head of `rest` leaves: `Offset_*` and `Pad`. -/
structure RestHead (K W D : Addr) (R n : Nat) (SP : Addr) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.AArch64.Env K W D R n SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩]
    t.mem t'.mem
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K
  tmp : blockAtMem t'.mem (W + BitVec.ofNat 64 tmpO) =
    ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K)
  saved : VG.Proof.AesOcb.AArch64.Saved t t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem restHead_ok (v : BlocksImpl) {K W D : Addr} {R n : Nat} {SP : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {t : State}
    (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP t) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    WP isa (.seq (.block (xor16 .x20 240 ofsO ++ copy16 ofsO tmpO)) (callBlocks (VG.Proof.AesOcb.AArch64.callees v).enc (oneBlock tmpO))) t
      (VG.Proof.AesOcb.AArch64.RestHead K W D R n SP t) := by
  obtain ⟨t₁, run₁, B₁⟩ := VG.Proof.AesOcb.AArch64.xor16_ok (s := t) (b := .x20) (a := 240) (d := ofsO) (by decide) (by decide) E.x19 E.x20
    (by decide) (by decide) (by decide) (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide))
    (E.perm.wW (by decide))
  have E₁ := E.others B₁.gpr B₁.sp B₁.rd B₁.wr
  obtain ⟨t₂, run₂, B₂⟩ := VG.Proof.AesOcb.AArch64.copy16_ok (s := t₁) (a := ofsO) (d := tmpO) (by decide) (by decide) E₁.x19
    (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wW (by decide)) (E₁.perm.wW (by decide))
  have E₂ := E₁.others B₂.gpr B₂.sp B₂.rd B₂.wr
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₂.mem :=
    (B₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  have ofs₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ofsO) =
      blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K := by
    rw [blockAtMem_frame B₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), B₁.val]
    rfl
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  have cK : ctxCiph t₂.mem K R = ctxCiph t.mem K R := by
    unfold ctxCiph
    rw [Proof.Cmac.bytesAt_frame fr₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide)))
      (by omega)]
  refine WP.seq (WP.of_runBlock ⟨t₂, by rw [VG.Proof.AesOcb.AArch64.runBlock_append, run₁, Option.bind_some, run₂], ?_⟩)
  refine WP.mono (VG.Proof.AesOcb.AArch64.callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNoFrames L E₂ hR
    (VG.Proof.AesOcb.AArch64.oneBlock_ok E₂.x19 tmpO (by decide)) (VG.Proof.AesOcb.AArch64.dstW L E₂.perm (d := tmpO) (n := 1) (by decide))) fun t₃ P₃ => ?_
  refine ⟨E₂.of_saved P₃.saved P₃.sp P₃.rd P₃.wr, ?_, ?_, ?_, ?_, by rw [P₃.rd, B₂.rd, B₁.rd],
    by rw [P₃.wr, B₂.wr, B₁.wr]⟩
  · refine (fr₂.mono (by simp)).trans (P₃.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [blockAtMem_frame P₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)), ofs₂]
  · rw [P₃.enc0, B₂.val, B₁.val]
    show ctxCiph t₂.mem K R _ = _
    rw [cK]; rfl
  · exact (VG.Proof.AesOcb.AArch64.saved_of B₁.gpr).trans ((VG.Proof.AesOcb.AArch64.saved_of B₂.gpr).trans P₃.saved)

theorem xor_append_right (xs ys zs : List Byte) (h : xs.length = ys.length) :
    Spec.Ocb.xor xs (ys ++ zs) = Spec.Ocb.xor xs ys := by
  simpa [Spec.Ocb.xor] using List.zipWith_append (f := fun x1 x2 : Byte => x1 ^^^ x2) (l₁' := []) (l₂' := zs) h

/-- `r` bytes XORed with the first `r` bytes of a block. -/
theorem xor_bytesAt_block (xs : List Byte) (m : Mem) (Q : Addr) {r : Nat} (hl : xs.length = r) (hr : r ≤ 16) :
    Spec.Ocb.xor xs (bytesAt m Q r) = Spec.Ocb.xor xs (Spec.Ocb.toBytes (blockAtMem m Q)) := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = r + (16 - r) by omega,
    Proof.Ocb.bytesAt_append, VG.Proof.AesOcb.AArch64.xor_append_right _ _ _ (by rw [hl, length_bytesAt])]

/-- What `rest` leaves: `Offset_*`, the data XORed with `Pad`, and the
checksum with the padded plaintext (before the XOR for `seal`, after it for
`open`). -/
structure RestPost (enc : Bool) (K W D : Addr) (R n : Nat) (SP : Addr) (P : Addr) (r : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.AArch64.Env K W D R n SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
    ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨P, r⟩] t.mem t'.mem
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K
  out : bytesAt t'.mem P r = Spec.Ocb.xor (bytesAt t.mem P r)
    (Spec.Ocb.toBytes (ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K)))
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) =
    blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
  saved : VG.Proof.AesOcb.AArch64.Saved t t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem rest_ok (v : BlocksImpl) (enc : Bool) {K W D : Addr} {R n : Nat} {SP : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {t : State}
    (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP t) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : Addr} {r : Nat} (hr : 0 < r) (hr' : r < 16)
    (h23 : t.gpr .x23 = P) (h24 : t.gpr .x24 = BitVec.ofNat 64 r) (hP : VG.Proof.AesOcb.AArch64.DBuf K W t P r) :
    WP isa (rest (VG.Proof.AesOcb.AArch64.callees v) enc) t (VG.Proof.AesOcb.AArch64.RestPost enc K W D R n SP P r t) := by
  unfold rest
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.restHead_ok v L E hR) fun t₃ H => ?_))
  have h23₃ : t₃.gpr .x23 = P := by rw [H.saved _ (by decide) (by decide), h23]
  have h24₃ : t₃.gpr .x24 = BitVec.ofNat 64 r := by rw [H.saved _ (by decide) (by decide), h24]
  have hP₃ : VG.Proof.AesOcb.AArch64.DBuf K W t₃ P r := hP.of_eq H.rd H.wr
  have hS₃ : Covers [⟨P, r⟩] (t₃.rd ++ t₃.wr) := hP₃.rd
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨P, r⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
    fun h => hP.w.sub_right (Lay.wSub h)
  have dH : ∀ q ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨W + BitVec.ofNat 64 512, 2048⟩], (⟨P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact dW (by decide)
  have dT : ∀ q ∈ [(⟨W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact dW (by decide)
  have dTmp : ∀ q ∈ [(⟨W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨W + BitVec.ofNat 64 tmpO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have dOfs : ∀ q ∈ [(⟨W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have pP₃ : bytesAt t₃.mem P r = bytesAt t.mem P r := Proof.Cmac.bytesAt_frame H.frame dH (by omega)
  have hl : (bytesAt t.mem P r).length = r := length_bytesAt _ _ _
  have hlx : ∀ ys, (Spec.Ocb.xor (bytesAt t.mem P r) (Spec.Ocb.toBytes ys)).length = r := fun ys => by
    simp [Spec.Ocb.xor, length_bytesAt, Proof.Ocb.toBytes_length]; omega
  have fP : ∀ (m : Mem) (xs : List Byte), xs.length = r → Frame [⟨P, r⟩] m (writeBytes m P xs) :=
    fun m xs h => writeBytes_frame _ _ _ (by rw [h]; exact Region.contains_self _ _)
  have xP : ∀ u : State, bytesAt u.mem P r = bytesAt t.mem P r →
      blockAtMem u.mem (W + BitVec.ofNat 64 tmpO) = blockAtMem t₃.mem (W + BitVec.ofNat 64 tmpO) →
      bytesAt (writeBytes u.mem P (Spec.Ocb.xor (bytesAt u.mem P r) (bytesAt u.mem (W + BitVec.ofNat 64 112) r))) P r =
        Spec.Ocb.xor (bytesAt t.mem P r) (Spec.Ocb.toBytes
          (ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K))) := by
    intro u hu ht
    rw [hu, VG.Proof.AesOcb.AArch64.xor_bytesAt_block _ _ _ hl (by omega), show (112 : Nat) = tmpO from rfl, ht, H.tmp,
      Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [hlx]) (by omega), hlx, List.drop_of_length_le
        (by rw [length_bytesAt]), List.append_nil]
  have dCk : ∀ q ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨W + BitVec.ofNat 64 512, 2048⟩], (⟨W + BitVec.ofNat 64 ckO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have ck₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 ckO) = blockAtMem t.mem (W + BitVec.ofNat 64 ckO) :=
    blockAtMem_frame H.frame dCk
  have pW : ∀ {d : Nat}, d + 16 ≤ 2560 → ∀ q ∈ [(⟨P, r⟩ : Region)], (⟨W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q :=
    fun h q hq => by simp only [List.mem_singleton] at hq; subst hq; exact (dW h).symm
  have E₃ := H.env
  cases enc
  · -- `open`: the XOR, then the checksum.
    refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.xorPad_ok E₃.x19 E₃.perm.w hr hr' h23₃ h24₃ hP₃) fun t₄ ⟨m₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
    have E₄ := E₃.others g₄ sp₄ rd₄ wr₄
    have fr₄ : Frame [⟨P, r⟩] t₃.mem t₄.mem := by rw [m₄]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    refine WP.mono (VG.Proof.AesOcb.AArch64.padCk_ok L E₄.x19 E₄.perm.w hr hr' (by rw [g₄ _ (by decide), h23₃])
      (by rw [g₄ _ (by decide), h24₃]) (by rw [rd₄, wr₄]; exact hS₃) hP.w) fun t₅ ⟨fr₅, ck₅, g₅, sp₅, rd₅, wr₅⟩ => ?_
    have p₅ : bytesAt t₅.mem P r = bytesAt t₄.mem P r := Proof.Cmac.bytesAt_frame fr₅ dT (by omega)
    refine ⟨E₄.others g₅ sp₅ rd₅ wr₅,
      ((H.frame.mono (by simp)).trans (fr₄.mono (by simp))).trans (fr₅.mono (by simp)), ?_, ?_, ?_,
      H.saved.trans ((VG.Proof.AesOcb.AArch64.saved_of g₄).trans (VG.Proof.AesOcb.AArch64.saved_of g₅)), by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [blockAtMem_frame fr₅ dOfs, blockAtMem_frame fr₄ (pW (by decide)), H.ofs]
    · rw [p₅, m₄, xP t₃ pP₃ rfl]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ck₅, p₅, blockAtMem_frame fr₄ (pW (by decide)), ck₃]
  · -- `seal`: the checksum, then the XOR.
    refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.padCk_ok L E₃.x19 E₃.perm.w hr hr' h23₃ h24₃ hS₃ hP.w)
      fun t₄ ⟨fr₄, ck₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
    have E₄ := E₃.others g₄ sp₄ rd₄ wr₄
    have p₄ : bytesAt t₄.mem P r = bytesAt t₃.mem P r := Proof.Cmac.bytesAt_frame fr₄ dT (by omega)
    refine WP.mono (VG.Proof.AesOcb.AArch64.xorPad_ok E₄.x19 E₄.perm.w hr hr' (by rw [g₄ _ (by decide), h23₃])
      (by rw [g₄ _ (by decide), h24₃]) (hP₃.of_eq rd₄ wr₄)) fun t₅ ⟨m₅, g₅, sp₅, rd₅, wr₅⟩ => ?_
    have fr₅ : Frame [⟨P, r⟩] t₄.mem t₅.mem := by rw [m₅]; exact fP _ _ (by simp [Spec.Ocb.xor, length_bytesAt])
    refine ⟨E₄.others g₅ sp₅ rd₅ wr₅,
      ((H.frame.mono (by simp)).trans (fr₄.mono (by simp))).trans (fr₅.mono (by simp)), ?_, ?_, ?_,
      H.saved.trans ((VG.Proof.AesOcb.AArch64.saved_of g₄).trans (VG.Proof.AesOcb.AArch64.saved_of g₅)), by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [blockAtMem_frame fr₅ (pW (by decide)), blockAtMem_frame fr₄ dOfs, H.ofs]
    · rw [m₅, xP t₄ (by rw [p₄, pP₃]) (blockAtMem_frame fr₄ dTmp)]
    · simp only [↓reduceIte]
      rw [blockAtMem_frame fr₅ (pW (by decide)), ck₄, ck₃, pP₃]

/-- What `tag d` leaves. -/
structure TagPost (K W D : Addr) (R n : Nat) (SP : Addr) (d : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.AArch64.Env K W D R n SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩]
    t.mem t'.mem
  val : blockAtMem t'.mem (W + BitVec.ofNat 64 d) =
    ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^
      blockAtMem t.mem (W + BitVec.ofNat 64 ldO)) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 sumO)
  saved : VG.Proof.AesOcb.AArch64.Saved t t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem tag_ok (v : BlocksImpl) {K W D : Addr} {R n : Nat} {SP : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {t : State}
    (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP t) (hR : R = 10 ∨ R = 12 ∨ R = 14) {d : Nat} (hd : d = tagO ∨ d = t2O) :
    WP isa (tag (VG.Proof.AesOcb.AArch64.callees v) d) t (VG.Proof.AesOcb.AArch64.TagPost K W D R n SP d t) := by
  have hd' : d = 0 ∨ d = 128 := hd
  have hd8 : d % 8 = 0 ∧ d + 8 < 32768 := by omega
  obtain ⟨t₁, run₁, B₁⟩ := VG.Proof.AesOcb.AArch64.copy16_ok (s := t) (a := ckO) (d := tmpO) (by decide) (by decide) E.x19
    (E.perm.wR (by decide)) (E.perm.wR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have E₁ := E.others B₁.gpr B₁.sp B₁.rd B₁.wr
  obtain ⟨t₂, run₂, B₂⟩ := VG.Proof.AesOcb.AArch64.xor16_ok (s := t₁) (b := .x19) (a := ofsO) (d := tmpO) (by decide) (by decide) E₁.x19
    E₁.x19 (by decide) (by decide) (by decide) (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide))
    (E₁.perm.wW (by decide)) (E₁.perm.wW (by decide))
  have E₂ := E₁.others B₂.gpr B₂.sp B₂.rd B₂.wr
  obtain ⟨t₃, run₃, B₃⟩ := VG.Proof.AesOcb.AArch64.xor16_ok (s := t₂) (b := .x19) (a := ldO) (d := tmpO) (by decide) (by decide) E₂.x19
    E₂.x19 (by decide) (by decide) (by decide) (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide))
    (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  have E₃ := E₂.others B₃.gpr B₃.sp B₃.rd B₃.wr
  have tW : ∀ {a : Nat}, (a + 16 ≤ 112 ∨ 128 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w h h' (by decide)
  have fr₃ : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem :=
    (B₁.frame.trans B₂.frame).trans B₃.frame
  have tmp₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 tmpO) =
      blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 ldO) := by
    rw [B₃.val, B₂.val, B₁.val, blockAtMem_frame B₁.frame (tW (by decide) (by decide)),
      blockAtMem_frame (B₁.frame.trans B₂.frame) (tW (by decide) (by decide))]
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  have cK : ctxCiph t₃.mem K R = ctxCiph t.mem K R := by
    unfold ctxCiph
    rw [Proof.Cmac.bytesAt_frame fr₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))) (by omega)]
  unfold tag
  refine WP.seq (WP.of_runBlock ⟨t₃, by rw [VG.Proof.AesOcb.AArch64.runBlock_append, VG.Proof.AesOcb.AArch64.runBlock_append, run₁, Option.bind_some, run₂,
    Option.bind_some, run₃], ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNoFrames L E₃ hR
    (VG.Proof.AesOcb.AArch64.oneBlock_ok E₃.x19 tmpO (by decide)) (VG.Proof.AesOcb.AArch64.dstW L E₃.perm (d := tmpO) (n := 1) (by decide))) fun t₄ P₄ => ?_)
  have E₄ := E₃.of_saved P₄.saved P₄.sp P₄.rd P₄.wr
  have tmp₄ : blockAtMem t₄.mem (W + BitVec.ofNat 64 tmpO) =
      ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 ldO)) := by
    rw [P₄.enc0, tmp₃, ← cK]; rfl
  obtain ⟨t₅, run₅, B₅⟩ := VG.Proof.AesOcb.AArch64.copy16_ok (s := t₄) (a := tmpO) (d := d) (by decide) hd8 E₄.x19
    (E₄.perm.wR (by decide)) (E₄.perm.wR (by decide)) (E₄.perm.wW (by omega)) (E₄.perm.wW (by omega))
  have E₅ := E₄.others B₅.gpr B₅.sp B₅.rd B₅.wr
  obtain ⟨t₆, run₆, B₆⟩ := VG.Proof.AesOcb.AArch64.xor16_ok (s := t₅) (b := .x19) (a := sumO) (d := d) (by decide) hd8 E₅.x19 E₅.x19
    (by decide) (by decide) (by decide) (E₅.perm.wR (by decide)) (E₅.perm.wR (by decide)) (E₅.perm.wW (by omega))
    (E₅.perm.wW (by omega))
  refine WP.of_runBlock ⟨t₆, by rw [VG.Proof.AesOcb.AArch64.runBlock_append, run₅, Option.bind_some, run₆], ?_⟩
  have dD : ∀ {a : Nat}, (a + 16 ≤ d ∨ d + 16 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨W + BitVec.ofNat 64 d, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w h h' (by omega)
  have dCall : ∀ q ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16 * 1⟩ : Region), ⟨W + BitVec.ofNat 64 512, 2048⟩],
      (⟨W + BitVec.ofNat 64 sumO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  refine ⟨E₅.others B₆.gpr B₆.sp B₆.rd B₆.wr, ?_, ?_,
    (VG.Proof.AesOcb.AArch64.saved_of B₁.gpr).trans ((VG.Proof.AesOcb.AArch64.saved_of B₂.gpr).trans ((VG.Proof.AesOcb.AArch64.saved_of B₃.gpr).trans (Saved.trans P₄.saved
      ((VG.Proof.AesOcb.AArch64.saved_of B₅.gpr).trans (VG.Proof.AesOcb.AArch64.saved_of B₆.gpr))))),
    by rw [B₆.rd, B₅.rd, P₄.rd, B₃.rd, B₂.rd, B₁.rd], by rw [B₆.wr, B₅.wr, P₄.wr, B₃.wr, B₂.wr, B₁.wr]⟩
  · refine (((fr₃.mono (by simp)).trans (P₄.frame.sub fun r hr => ?_)).trans (B₅.frame.mono (by simp))).trans
      (B₆.frame.mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [B₆.val, B₅.val, tmp₄, blockAtMem_frame B₅.frame (dD (by simp only [sumO]; omega) (by decide)),
      blockAtMem_frame P₄.frame dCall, blockAtMem_frame fr₃ (tW (by decide) (by decide))]

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Body`. -/
section

/-!
# AES-OCB on AArch64: the data (`body`)

Untrusted: everything here is checked by Lean. `body` takes the whole blocks
(if any, `wholeIte_ok`) and then the rest (if any, `restIte_ok`); for `seal`
the result is `OCB-ENCRYPT`'s ciphertext, offset and checksum
(`bodySeal_ok`), for `open` `OCB-DECRYPT`'s (`bodyOpen_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (eval_zero toNat_ofNat_of_lt lsr_ofNat and15)

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : b.code.noFrames = true) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, VG.Proof.AesOcb.AArch64.BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : ∀ {W}, VG.Proof.AesOcb.AArch64.BodyOk W pre (fun b o => b ^^^ o) fC1) (hB2 : ∀ {W}, VG.Proof.AesOcb.AArch64.BodyOk W post (fun b o => b ^^^ o) fC2)
    {K W D : Addr} {R n : Nat} {SP : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {s : State} (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP s)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hD : VG.Proof.AesOcb.AArch64.DBuf K W s D n) {O0 l : Block}
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (n / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [.lsr .x .x26 .x28 4]) (.ite (.zero .x .x26) (.block []) (whole b pre post))) s
      (VG.Proof.AesOcb.AArch64.WholePost K W D R n SP (n / 16) O0 l
        (fun k => G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (n / 16)) s) := by
  have hn := hD.lt
  obtain ⟨s₁, run₁, h₁⟩ : ∃ s₁, runBlock isa [.lsr .x .x26 .x28 4] s = some s₁ ∧
      s₁ = s.write .x .x26 (s.gpr .x28 >>> 4) := ⟨_, by orun [], rfl⟩
  subst h₁
  have x26₁ : (s.write .x .x26 (s.gpr .x28 >>> 4)).gpr .x26 = BitVec.ofNat 64 (n / 16) := by
    simp [gpr_write, E.x28, lsr_ofNat _ _ hn]
  have E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP (s.write .x .x26 (s.gpr .x28 >>> 4)) :=
    E.others (rs := [.x26]) (fun r hr => by simp at hr; simp [gpr_write, hr]) rfl rfl rfl
  refine WP.seq (WP.of_runBlock ⟨_, run₁, ?_⟩)
  refine WP.ite _ (eval_zero x26₁ (by omega)) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hm : n / 16 = 0 := of_decide_eq_true h0
    exact ⟨E₁, Frame.refl _ _, rfl, rfl, fun k hk => absurd hk (by omega),
      by rw [mem_write, hofs, hm]; rfl, by rw [mem_write, hck, hm, hckF2₀, hm]⟩
  · have hm : n / 16 ≠ 0 := of_decide_eq_false h0
    refine WP.mono (VG.Proof.AesOcb.AArch64.whole_ok (O0 := O0) (l := l) ok nf hcall hB1 hB2 L E₁ hR (hD.of_eq rfl rfl)
      (Nat.mul_div_le n 16) (by omega) (by omega) x26₁ hofs ho0 hck hl0 hckF1 hckF2₀ hckF2) fun t P => ?_
    exact ⟨P.env, P.frame, P.rd, P.wr, P.blk, P.ofs, P.ck⟩

/-- Where the rest of the data is, and how long it is. -/
theorem bodyTail_ok {K W D : Addr} {R n : Nat} {SP : Addr} {t : State} (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP t) (hn : n < 2 ^ 64) :
    ∃ t₁, runBlock isa [Impl.AesGcm.AArch64.imm .x10 15, .logic .and .x .x24 .x28 .x10, .sub .x .x9 .x28 .x24,
        .add .x .x23 .x21 .x9] t = some t₁ ∧
      t₁.gpr .x23 = D + BitVec.ofNat 64 (16 * (n / 16)) ∧ t₁.gpr .x24 = BitVec.ofNat 64 (n % 16) ∧
      t₁.mem = t.mem ∧ (∀ r, r ∉ [.x9, .x10, .x23, .x24] → t₁.gpr r = t.gpr r) ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 (n % 16) = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [Proof.AesGcm.AArch64.ofNat_sub (Nat.mod_le _ _) hn, show n - n % 16 = 16 * (n / 16) by omega]
  refine ⟨_, by orun [], ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, E.x28, E.x21, and15, toNat_ofNat_of_lt hn, hsub]
  · simp [gpr_write, E.x28, and15, toNat_ofNat_of_lt hn]
  · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]
  all_goals rfl

/-- What the rest of the data leaves, if there is any: `r` bytes at `P`. -/
structure TailPost (enc : Bool) (K W D : Addr) (R n : Nat) (SP : Addr) (P : Addr) (r : Nat) (t t' : State) : Prop where
  env : VG.Proof.AesOcb.AArch64.Env K W D R n SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
    ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨P, r⟩] t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem K
    else blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem P r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem P r)
      (Spec.Ocb.toBytes (ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem K)))
    else bytesAt t.mem P r
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) =
    if 0 < r then blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
    else blockAtMem t.mem (W + BitVec.ofNat 64 ckO)

/-- The rest of the data, if there is any. -/
theorem restIte_ok (v : BlocksImpl) (enc : Bool) {K W D : Addr} {R n : Nat} {SP : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {t : State}
    (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP t) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hD : VG.Proof.AesOcb.AArch64.DBuf K W t D n) :
    WP isa (.seq (.block [Impl.AesGcm.AArch64.imm .x10 15, .logic .and .x .x24 .x28 .x10, .sub .x .x9 .x28 .x24,
        .add .x .x23 .x21 .x9]) (.ite (.zero .x .x24) (.block []) (rest (VG.Proof.AesOcb.AArch64.callees v) enc))) t
      (VG.Proof.AesOcb.AArch64.TailPost enc K W D R n SP (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) t) := by
  have hn := hD.lt
  obtain ⟨t₁, run₁, x23₁, x24₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.AArch64.bodyTail_ok E hn
  have E₁ := E.others g₁ sp₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite _ (eval_zero x24₁ (by omega)) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hr : ¬ 0 < n % 16 := by have := of_decide_eq_true h0; omega
    refine ⟨E₁, by rw [m₁]; exact Frame.refl _ _, rd₁, wr₁, ?_, ?_, ?_⟩ <;> simp only [hr, ↓reduceIte, m₁]
  · have hr : 0 < n % 16 := by have := of_decide_eq_false h0; omega
    have hP : VG.Proof.AesOcb.AArch64.DBuf K W t₁ (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)).of_eq rd₁ wr₁
    refine WP.mono (VG.Proof.AesOcb.AArch64.rest_ok v enc L E₁ hR hr (Nat.mod_lt _ (by decide)) x23₁ x24₁ hP) fun t' P => ?_
    refine ⟨P.env, by rw [← m₁]; exact P.frame, by rw [P.rd, rd₁], by rw [P.wr, wr₁], ?_, ?_, ?_⟩ <;>
      simp only [hr, ↓reduceIte]
    · rw [P.ofs, m₁]
    · rw [P.out, m₁]
    · rw [P.ck, m₁]

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}`, `Pad` and
`pad(·)`, the working space of the functions called, the stack and the data. -/
abbrev bodyR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 48⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D, n⟩]

theorem bodyR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (VG.Proof.AesOcb.AArch64.bodyR W D n) m m') :
    Frame (VG.Proof.AesOcb.AArch64.mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesOcb.AArch64.in_mutA (by decide)
  · exact VG.Proof.AesOcb.AArch64.in_mutA (by decide)
  · exact VG.Proof.AesOcb.AArch64.in_mutB (by decide) (by decide)
  · exact VG.Proof.AesOcb.AArch64.in_mutD fun _ h => h

/-- What `body` leaves: the data, the offset and the checksum. -/
structure BodyPost (K W D : Addr) (R n : Nat) (SP : Addr) (out : List Byte) (ofs ck : Block) (s t : State) : Prop where
  env : VG.Proof.AesOcb.AArch64.Env K W D R n SP t
  frame : Frame (VG.Proof.AesOcb.AArch64.bodyR W D n) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem D n = out
  ofs : blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = ck

/-- A checksum of blocks `X i`. -/
def ckOf (X : Nat → Block) : Nat → Block
  | 0 => 0
  | i + 1 => VG.Proof.AesOcb.AArch64.ckOf X i ^^^ X i

theorem ckOf_eq {X : Nat → Block} {p : List Byte} {m : Nat} (h : ∀ i < m, X i = Spec.Ocb.blockAt p i) :
    VG.Proof.AesOcb.AArch64.ckOf X m = Proof.Ocb.ckAt p m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [VG.Proof.AesOcb.AArch64.ckOf, Proof.Ocb.ckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} {m : Nat} (h : ∀ i < m, f i = g i) :
    (List.range m).flatMap f = (List.range m).flatMap g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun i hi => h i (by omega))]
    simp only [List.flatMap_cons, List.flatMap_nil, h m (by omega)]

/-- `ENCIPHER` from the key schedule, whatever its length. -/
def encG (ks : List Byte) : Cipher := Spec.Ocb.aesWith (ks.length / 16 - 1) ks

/-- `DECIPHER` from the key schedule, whatever its length. -/
def decG (ks : List Byte) : Cipher := Spec.Ocb.aesInvWith (ks.length / 16 - 1) ks

theorem encG_eq (m : Mem) (K : Addr) (R : Nat) : VG.Proof.AesOcb.AArch64.encG (bytesAt m K (16 * (R + 1))) = ctxCiph m K R := by
  rw [VG.Proof.AesOcb.AArch64.encG, length_bytesAt, show 16 * (R + 1) / 16 - 1 = R by omega]; rfl

theorem decG_eq (m : Mem) (K : Addr) (R : Nat) : VG.Proof.AesOcb.AArch64.decG (bytesAt m K (16 * (R + 1))) = Spec.Ocb.ctxInv m K R := by
  rw [VG.Proof.AesOcb.AArch64.decG, length_bytesAt, show 16 * (R + 1) / 16 - 1 = R by omega]; rfl

theorem hcall_enc {s s' : State} {K D S : Addr} {R n : Nat} (h : VG.Proof.AesOcb.AArch64.BPost Spec.Aes.cipher s K D S R n s') :
    ∀ i < n, blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      VG.Proof.AesOcb.AArch64.encG (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) := fun i hi => by
  rw [h.enc hi, VG.Proof.AesOcb.AArch64.encG_eq]; rfl

theorem hcall_dec {s s' : State} {K D S : Addr} {R n : Nat} (h : VG.Proof.AesOcb.AArch64.BPost Spec.Aes.invCipher s K D S R n s') :
    ∀ i < n, blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      VG.Proof.AesOcb.AArch64.decG (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) := fun i hi => by
  rw [h.dec hi, VG.Proof.AesOcb.AArch64.decG_eq]; rfl

/-- A buffer apart from `W` and `⟨P, r⟩` misses what `rest` writes. -/
theorem disj_tail {W Q P : Addr} {k r : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hp : (⟨Q, k⟩ : Region).Disjoint ⟨P, r⟩) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨P, r⟩], (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hp

/-- A buffer apart from `W` and `⟨D, n⟩` misses what `whole` writes. -/
theorem disj_whole {W Q D : Addr} {k n : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hp : (⟨Q, k⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ x ∈ VG.Proof.AesOcb.AArch64.wholeR W D n, (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hp

theorem wholeR_sub {W D : Addr} {k n : Nat} (hk : k ≤ n) :
    ∀ r ∈ VG.Proof.AesOcb.AArch64.wholeR W D k, ∃ r' ∈ VG.Proof.AesOcb.AArch64.bodyR W D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Region.sub_prefix hk⟩

theorem tailR_sub {W D : Addr} {n a r : Nat} (h : a + r ≤ n) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D + BitVec.ofNat 64 a, r⟩],
      ∃ r' ∈ VG.Proof.AesOcb.AArch64.bodyR W D n, Region.Sub x r' := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Offset.sub_base D h⟩

/-- `body` for `seal`. -/
theorem bodySeal_ok (v : BlocksImpl) {K W D : Addr} {R n : Nat} {SP : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {s : State}
    (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP s) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hD : VG.Proof.AesOcb.AArch64.DBuf K W s D n) {O0 : Block}
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0) :
    WP isa (body (VG.Proof.AesOcb.AArch64.callees v) true) s (VG.Proof.AesOcb.AArch64.BodyPost K W D R n SP
      (if 0 < n % 16 then
        Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K)))
      else Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K
       else offAt O0 (ctxLstar s.mem K) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) ^^^ pad ((bytesAt s.mem D n).drop (16 * (n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : VG.Proof.AesOcb.AArch64.DBuf K W s D (16 * (n / 16)) := hD.take' hmn
  have hP : VG.Proof.AesOcb.AArch64.DBuf K W s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)
  have dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega)
  have hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega)).symm
  simp only [body, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.wholeIte_ok (O0 := O0) (l := ctxLstar s.mem K)
    (ckF1 := VG.Proof.AesOcb.AArch64.ckOf fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => VG.Proof.AesOcb.AArch64.ckOf (fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (n / 16))
    v.encOk v.encNoFrames VG.Proof.AesOcb.AArch64.hcall_enc VG.Proof.AesOcb.AArch64.sealPre_ok VG.Proof.AesOcb.AArch64.xorOfs_ok L E hR hD hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (VG.Proof.AesOcb.AArch64.mutR W D (16 * (n / 16))) s.mem t.mem := VG.Proof.AesOcb.AArch64.wholeR_mut Pw.frame
  refine WP.mono (VG.Proof.AesOcb.AArch64.restIte_ok v true L Pw.env hR (hD.of_eq Pw.rd Pw.wr)) fun t' Pt => ?_
  have cT : ctxCiph t.mem K R = ctxCiph s.mem K R := VG.Proof.AesOcb.AArch64.ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem K = ctxLstar s.mem K :=
    blockAtMem_frame fW fun r hr => (VG.Proof.AesOcb.AArch64.k_mut L hDm.k r hr).sub_left (Lay.kSub (by decide))
  have pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (VG.Proof.AesOcb.AArch64.disj_whole hP.w dDP.symm) (by omega)
  have rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega]
  have ckT : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, VG.Proof.AesOcb.AArch64.ckOf_eq hl]
  have blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (VG.Proof.AesOcb.AArch64.disj_tail hDm.w dDP) (by omega), Proof.Ocb.bytesAt_blocks, Proof.Ocb.encBlocks]
    refine VG.Proof.AesOcb.AArch64.flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, VG.Proof.AesOcb.AArch64.encG_eq, hl i hi,
      BitVec.xor_comm]
  refine ⟨Pt.env, (Pw.frame.sub (VG.Proof.AesOcb.AArch64.wholeR_sub hmn)).trans (Pt.frame.sub (VG.Proof.AesOcb.AArch64.tailR_sub (by omega))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · have e := Proof.Ocb.bytesAt_append t'.mem D (16 * (n / 16)) (n % 16)
    rw [show 16 * (n / 16) + n % 16 = n by omega] at e
    rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show n % 16 = 0 by omega, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    simp only [↓reduceIte, pT, rest]

theorem ckOf_dck {X : Nat → Block} {inv : Cipher} {o0 l : Block} {c : List Byte} {m : Nat}
    (h : ∀ i < m, X i = Proof.Ocb.decBlock inv o0 l c i) : VG.Proof.AesOcb.AArch64.ckOf X m = Proof.Ocb.dckAt inv o0 l c m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [VG.Proof.AesOcb.AArch64.ckOf, Proof.Ocb.dckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

/-- `body` for `open`. -/
theorem bodyOpen_ok (v : BlocksImpl) {K W D : Addr} {R n : Nat} {SP : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {s : State}
    (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP s) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hD : VG.Proof.AesOcb.AArch64.DBuf K W s D n) {O0 : Block}
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0) :
    WP isa (body (VG.Proof.AesOcb.AArch64.callees v) false) s (VG.Proof.AesOcb.AArch64.BodyPost K W D R n SP
      (if 0 < n % 16 then
        Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K)))
      else Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K
       else offAt O0 (ctxLstar s.mem K) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K))))
      else Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : VG.Proof.AesOcb.AArch64.DBuf K W s D (16 * (n / 16)) := hD.take' hmn
  have hP : VG.Proof.AesOcb.AArch64.DBuf K W s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)
  have dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega)
  have hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega)).symm
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.wholeIte_ok (O0 := O0) (l := ctxLstar s.mem K) (ckF1 := fun _ => 0)
    (ckF2 := VG.Proof.AesOcb.AArch64.ckOf fun i => VG.Proof.AesOcb.AArch64.decG (bytesAt s.mem K (16 * (R + 1)))
      (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem K) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem K) (i + 1))
    v.decOk v.decNoFrames VG.Proof.AesOcb.AArch64.hcall_dec VG.Proof.AesOcb.AArch64.xorOfs_ok VG.Proof.AesOcb.AArch64.openPost_ok L E hR hD hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (VG.Proof.AesOcb.AArch64.mutR W D (16 * (n / 16))) s.mem t.mem := VG.Proof.AesOcb.AArch64.wholeR_mut Pw.frame
  refine WP.mono (VG.Proof.AesOcb.AArch64.restIte_ok v false L Pw.env hR (hD.of_eq Pw.rd Pw.wr)) fun t' Pt => ?_
  have cT : ctxCiph t.mem K R = ctxCiph s.mem K R := VG.Proof.AesOcb.AArch64.ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem K = ctxLstar s.mem K :=
    blockAtMem_frame fW fun r hr => (VG.Proof.AesOcb.AArch64.k_mut L hDm.k r hr).sub_left (Lay.kSub (by decide))
  have pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (VG.Proof.AesOcb.AArch64.disj_whole hP.w dDP.symm) (by omega)
  have rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega]
  have ckT : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, VG.Proof.AesOcb.AArch64.ckOf_dck fun i hi => by rw [VG.Proof.AesOcb.AArch64.decG_eq, hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  have blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (VG.Proof.AesOcb.AArch64.disj_tail hDm.w dDP) (by omega), Proof.Ocb.bytesAt_blocks, Proof.Ocb.decBlocks]
    refine VG.Proof.AesOcb.AArch64.flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, VG.Proof.AesOcb.AArch64.decG_eq, hl i hi,
      Proof.Ocb.decBlock, BitVec.xor_comm]
  have e := Proof.Ocb.bytesAt_append t'.mem D (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega] at e
  refine ⟨Pt.env, (Pw.frame.sub (VG.Proof.AesOcb.AArch64.wholeR_sub hmn)).trans (Pt.frame.sub (VG.Proof.AesOcb.AArch64.tailR_sub (by omega))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show n % 16 = 0 by omega, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < n % 16
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, Pt.out, pT, cT, lT, Pw.ofs, rest]
    · simp only [hr, ↓reduceIte]

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.CTBase`. -/
section

/-!
# AES-OCB on AArch64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs from given states (AES-GCM's `Eq2`) piece by piece, as
AES-GCM's do (`Proof/AesGcm/AArch64/Rel.lean`): the code between calls by
the taint analysis, from the registers `Env` fixes and others the
correctness proofs pin to the same values in both runs (`rel_env`); each call
of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` with the same arguments
in both runs (`callBlocks_rel`); and the next piece from the states the
correctness proofs describe (`rel_seq`). The taint analysis takes memory as
secret, so a block that loads a public value (an argument kept in `W`) and
uses it as an address or a count is split after the load.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint)

/-- Code the taint analysis checks, from the registers `rs` the two runs
agree on and those `Env` fixes. -/
theorem rel_env {K W D : Addr} {R n : Nat} {SP : Addr} {σ₁ σ₂ : State} {c : Prog isa}
    (E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₁) (E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₂) (rs : List Reg) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (taint.check (Taint.ofRegs (rs ++ ([.x19, .x20, .x21, .x22, .x28] : List Reg))) c h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT :=
  rel_taint _ (by rw [E₁.sp, E₂.sp]) (fun r hr' => by
    rcases List.mem_append.mp hr' with h | h
    · exact hr r h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · rw [E₁.x19, E₂.x19]
      · rw [E₁.x20, E₂.x20]
      · rw [E₁.x21, E₂.x21]
      · rw [E₁.x22, E₂.x22]
      · rw [E₁.x28, E₂.x28]) hc

/-- A call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on the same
`k` blocks at `D'` in both runs. -/
theorem callBlocks_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub b.code)
    {K W D : Addr} {R n : Nat} {SP : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) (hR : R = 10 ∨ R = 12 ∨ R = 14) {σ₁ σ₂ : State}
    (E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₁) (E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₂) {args : List Instr} (rs : List Reg)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (taint.check (Taint.ofRegs (rs ++ ([.x19, .x20, .x21, .x22, .x28] : List Reg)))
      (.block (args ++ ([Impl.AesGcm.AArch64.mov .x0 .x20, Impl.AesGcm.AArch64.mov .x1 .x22,
        Impl.AesGcm.AArch64.ptr .x4 .x19 scrO] : List Instr))) h).isSome = true)
    {D' : Addr} {k : Nat} (a₁ : VG.Proof.AesOcb.AArch64.ArgsOk args σ₁ D' k) (a₂ : VG.Proof.AesOcb.AArch64.ArgsOk args σ₂ D' k) (d₁ : VG.Proof.AesOcb.AArch64.Dst K W σ₁ D' k)
    (d₂ : VG.Proof.AesOcb.AArch64.Dst K W σ₂ D' k) : RelCT isa (Eq2 σ₁ σ₂) (callBlocks b args) TT := by
  unfold callBlocks
  exact rel_seq (VG.Proof.AesOcb.AArch64.rel_env E₁ E₂ rs hr hc) (VG.Proof.AesOcb.AArch64.callArgs_ok L E₁ hR a₁ d₁) (VG.Proof.AesOcb.AArch64.callArgs_ok L E₂ hR a₂ d₂)
    fun τ₁ τ₂ h₁ h₂ => VG.Proof.AesOcb.AArch64.blk_rel ok ct fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨K, D', _, R, k, h₁.1, h₂.1, by rw [h₁.2.2.1, h₂.2.2.1, E₁.sp, E₂.sp]⟩

/-- Two runs from states related by `P`, from each pair. -/
theorem rel_of_pt {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, P σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c Q) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-- Then: the next piece, from what holds of every run of the first (not
only of one, as `rel_seq` takes it). -/
theorem rel_seqE {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (hF₁ : ∀ t s', Exec isa c₁ σ₁ t s' → F₁ s')
    (hF₂ : ∀ t s', Exec isa c₁ σ₂ t s' → F₂ s')
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) : RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) (fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => ?_) (VG.Proof.AesOcb.AArch64.rel_of_pt fun τ₁ τ₂ h =>
    h₂ τ₁ τ₂ h.1 h.2)
  obtain ⟨rfl, rfl⟩ := hp
  exact ⟨(h₁ _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, hF₁ _ _ e₁, hF₂ _ _ e₂⟩

/-- Code without calls that writes none of the registers `rs` keeps them, the
stack pointer and the permissions. -/
theorem exec_keep {c : Prog isa} (rs : List Reg) (hk : c.allInstrs (keeps (RegSet.ofList rs)) = true)
    (hn : c.noCalls = true) {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    (∀ r ∈ rs, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hk' := instrs_keeps hk
  refine ⟨fun r hr => Exec.gpr (fun i hi => ?_) h (.inl hn), (Exec.rdwr h).2.2, (Exec.rdwr h).1, (Exec.rdwr h).2.1⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp hk' i hi) r hr
  simpa using this

/-- An environment, after code without calls that writes none of its registers. -/
theorem Env.exec {K W D : Addr} {R n : Nat} {SP : Addr} {s s' : State} {c : Prog isa} {t : List Leak}
    (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP s) (h : Exec isa c s t s')
    (hk : c.allInstrs (keeps (RegSet.ofList [.x19, .x20, .x21, .x22, .x28])) = true) (hn : c.noCalls = true) :
    VG.Proof.AesOcb.AArch64.Env K W D R n SP s' :=
  let ⟨g, sp, rd, wr⟩ := VG.Proof.AesOcb.AArch64.exec_keep _ hk hn h
  E.keep g sp rd wr

/-- Then: the next piece, in the environment, after code without calls
that keeps it. -/
theorem rel_seqEnv {K W D : Addr} {R n : Nat} {SP : Addr} {c₁ c₂ : Prog isa} {σ₁ σ₂ : State}
    (E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₁) (E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₂) (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT)
    (hk : c₁.allInstrs (keeps (RegSet.ofList [.x19, .x20, .x21, .x22, .x28])) = true) (hn : c₁.noCalls = true)
    (h₂ : ∀ τ₁ τ₂, VG.Proof.AesOcb.AArch64.Env K W D R n SP τ₁ → VG.Proof.AesOcb.AArch64.Env K W D R n SP τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT :=
  VG.Proof.AesOcb.AArch64.rel_seqE h₁ (fun _ _ h => E₁.exec h hk hn) (fun _ _ h => E₂.exec h hk hn) h₂

/-- Two runs of `a; (b; (c; d))` are two runs of `a; ((b; c); d)`. -/
theorem RelCT.assoc_in {a b c d : Prog isa} {P Q : State → State → Prop}
    (h : RelCT isa P (.seq a (.seq (.seq b c) d)) Q) : RelCT isa P (.seq a (.seq b (.seq c d))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ r₁ =>
    cases r₁ with
    | seq b₁ r₁ =>
      cases r₁ with
      | seq c₁ d₁ =>
        cases e₂ with
        | seq a₂ r₂ =>
          cases r₂ with
          | seq b₂ r₂ =>
            cases r₂ with
            | seq c₂ d₂ =>
              obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq (.seq b₁ c₁) d₁)) (.seq a₂ (.seq (.seq b₂ c₂) d₂))
              simp only [List.append_assoc] at ht
              exact ⟨ht, hq⟩

/-- A register `Env` fixes is not one outside them. -/
theorem envRegs_ne {r : Reg} (hr : r ∈ VG.Proof.AesOcb.AArch64.envRegs) {x : Reg} (hx : x ∉ VG.Proof.AesOcb.AArch64.envRegs := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.BodyCT`. -/
section

/-!
# AES-OCB on AArch64: the data and the tag are constant time

Untrusted: everything here is checked by Lean. Between the calls, the code
runs from the data's address and length (`x21`, `x28`), the number of whole
blocks (`x26`) and, for the rest, its address and length (`x23`, `x24`),
which are the same in both runs; what each piece keeps of them is read off
its instructions (`exec_keep`) or from its correctness proof. The calls have
the same arguments in both runs (`callBlocks_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ite eval_zero lsr_ofNat)

section
variable {K W D : Addr} {R n : Nat} {SP : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- The tag at `W + d`, in two runs. -/
theorem tag_rel (v : BlocksImpl) {σ₁ σ₂ : State} (E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₁) (E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₂) {d : Nat}
    (hd : d = tagO ∨ d = t2O) : RelCT isa (Eq2 σ₁ σ₂) (tag (VG.Proof.AesOcb.AArch64.callees v) d) TT := by
  have mid : ∀ {τ₁ τ₂ : State}, VG.Proof.AesOcb.AArch64.Env K W D R n SP τ₁ → VG.Proof.AesOcb.AArch64.Env K W D R n SP τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) (.seq (callBlocks (VG.Proof.AesOcb.AArch64.callees v).enc (oneBlock tmpO)) (.block (copy16 tmpO d ++
        xor16 .x19 sumO d))) TT := fun {τ₁ τ₂} F₁ F₂ => by
    refine rel_seq (VG.Proof.AesOcb.AArch64.callBlocks_rel v.encOk v.encCt L hR F₁ F₂ [] (by agree_tac []) ⟨_, by taint_decide⟩
        (VG.Proof.AesOcb.AArch64.oneBlock_ok F₁.x19 tmpO (by decide)) (VG.Proof.AesOcb.AArch64.oneBlock_ok F₂.x19 tmpO (by decide))
        (VG.Proof.AesOcb.AArch64.dstW L F₁.perm (d := tmpO) (n := 1) (by decide)) (VG.Proof.AesOcb.AArch64.dstW L F₂.perm (d := tmpO) (n := 1) (by decide)))
      (VG.Proof.AesOcb.AArch64.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L F₁ hR (VG.Proof.AesOcb.AArch64.oneBlock_ok F₁.x19 tmpO (by decide))
        (VG.Proof.AesOcb.AArch64.dstW L F₁.perm (d := tmpO) (n := 1) (by decide)))
      (VG.Proof.AesOcb.AArch64.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L F₂ hR (VG.Proof.AesOcb.AArch64.oneBlock_ok F₂.x19 tmpO (by decide))
        (VG.Proof.AesOcb.AArch64.dstW L F₂.perm (d := tmpO) (n := 1) (by decide))) fun u₁ u₂ P₁ P₂ => ?_
    rcases hd with rfl | rfl <;>
      exact VG.Proof.AesOcb.AArch64.rel_env (F₁.of_saved P₁.saved P₁.sp P₁.rd P₁.wr) (F₂.of_saved P₂.saved P₂.sp P₂.rd P₂.wr) []
        (by agree_tac []) ⟨_, by taint_decide⟩
  unfold tag
  exact VG.Proof.AesOcb.AArch64.rel_seqE (VG.Proof.AesOcb.AArch64.rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩)
    (fun _ _ h => E₁.exec h (by decide +kernel) (by decide +kernel))
    (fun _ _ h => E₂.exec h (by decide +kernel) (by decide +kernel)) fun _ _ F₁ F₂ => mid F₁ F₂

/-- The rest of the data (`r` bytes at `P`), in two runs. -/
theorem rest_rel (v : BlocksImpl) (enc : Bool) {σ₁ σ₂ : State} (E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₁) (E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₂)
    {P : Addr} {r : Nat} (h23₁ : σ₁.gpr .x23 = P) (h23₂ : σ₂.gpr .x23 = P)
    (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 r) (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 r) :
    RelCT isa (Eq2 σ₁ σ₂) (rest (VG.Proof.AesOcb.AArch64.callees v) enc) TT := by
  have keep : ∀ {σ : State}, VG.Proof.AesOcb.AArch64.Env K W D R n SP σ → σ.gpr .x23 = P → σ.gpr .x24 = BitVec.ofNat 64 r →
      ∀ t s', Exec isa (.block (xor16 .x20 240 ofsO ++ copy16 ofsO tmpO)) σ t s' →
        VG.Proof.AesOcb.AArch64.Env K W D R n SP s' ∧ s'.gpr .x23 = P ∧ s'.gpr .x24 = BitVec.ofNat 64 r := fun E h23 h24 _ _ h => by
    obtain ⟨g, sp, rd, wr⟩ := VG.Proof.AesOcb.AArch64.exec_keep [.x19, .x20, .x21, .x22, .x28, .x23, .x24] (by decide +kernel)
      (by decide +kernel) h
    exact ⟨E.keep (fun q hq => g q (List.mem_append_left _ hq)) sp rd wr,
      by rw [g _ (by simp), h23], by rw [g _ (by simp), h24]⟩
  unfold rest
  refine VG.Proof.AesOcb.AArch64.rel_seqE (VG.Proof.AesOcb.AArch64.rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (keep E₁ h23₁ h24₁) (keep E₂ h23₂ h24₂)
    fun τ₁ τ₂ ⟨F₁, a₁, b₁⟩ ⟨F₂, a₂, b₂⟩ => ?_
  refine rel_seq (VG.Proof.AesOcb.AArch64.callBlocks_rel v.encOk v.encCt L hR F₁ F₂ [] (by agree_tac []) ⟨_, by taint_decide⟩
      (VG.Proof.AesOcb.AArch64.oneBlock_ok F₁.x19 tmpO (by decide)) (VG.Proof.AesOcb.AArch64.oneBlock_ok F₂.x19 tmpO (by decide))
      (VG.Proof.AesOcb.AArch64.dstW L F₁.perm (d := tmpO) (n := 1) (by decide)) (VG.Proof.AesOcb.AArch64.dstW L F₂.perm (d := tmpO) (n := 1) (by decide)))
    (VG.Proof.AesOcb.AArch64.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L F₁ hR (VG.Proof.AesOcb.AArch64.oneBlock_ok F₁.x19 tmpO (by decide))
      (VG.Proof.AesOcb.AArch64.dstW L F₁.perm (d := tmpO) (n := 1) (by decide)))
    (VG.Proof.AesOcb.AArch64.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L F₂ hR (VG.Proof.AesOcb.AArch64.oneBlock_ok F₂.x19 tmpO (by decide))
      (VG.Proof.AesOcb.AArch64.dstW L F₂.perm (d := tmpO) (n := 1) (by decide))) fun u₁ u₂ P₁ P₂ => ?_
  have c23₁ : u₁.gpr .x23 = τ₁.gpr .x23 := P₁.saved _ (by decide) (by decide)
  have c23₂ : u₂.gpr .x23 = τ₂.gpr .x23 := P₂.saved _ (by decide) (by decide)
  have c24₁ : u₁.gpr .x24 = τ₁.gpr .x24 := P₁.saved _ (by decide) (by decide)
  have c24₂ : u₂.gpr .x24 = τ₂.gpr .x24 := P₂.saved _ (by decide) (by decide)
  cases enc <;>
    exact VG.Proof.AesOcb.AArch64.rel_env (F₁.of_saved P₁.saved P₁.sp P₁.rd P₁.wr) (F₂.of_saved P₂.saved P₂.sp P₂.rd P₂.wr) [.x23, .x24]
      (by agree_tac [c23₁, c23₂, c24₁, c24₂, a₁, a₂, b₁, b₂]) ⟨_, by taint_decide⟩

/-- The rest of the data, if there is any, in two runs. -/
theorem restIte_rel (v : BlocksImpl) (enc : Bool) {σ₁ σ₂ : State} (E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₁)
    (E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₂) (hn : n < 2 ^ 64) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block [Impl.AesGcm.AArch64.imm .x10 15, .logic .and .x .x24 .x28 .x10,
      .sub .x .x9 .x28 .x24, .add .x .x23 .x21 .x9]) (.ite (.zero .x .x24) (.block []) (rest (VG.Proof.AesOcb.AArch64.callees v) enc))) TT := by
  obtain ⟨t₁, run₁, x23₁, x24₁, _, g₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.AArch64.bodyTail_ok E₁ hn
  obtain ⟨t₂, run₂, x23₂, x24₂, _, g₂, sp₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.AArch64.bodyTail_ok E₂ hn
  refine rel_seq (VG.Proof.AesOcb.AArch64.rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (WP.of_runBlock ⟨t₁, run₁, rfl⟩)
    (WP.of_runBlock ⟨t₂, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_
  subst h₁ h₂
  exact rel_ite (eval_zero x24₁ (by omega)) (eval_zero x24₂ (by omega)) (fun _ => RelCT.block_nil fun _ _ _ => trivial)
    fun _ => VG.Proof.AesOcb.AArch64.rest_rel L hR v enc (E₁.others g₁ sp₁ rd₁ wr₁) (E₂.others g₂ sp₂ rd₂ wr₂) x23₁ x23₂ x24₁ x24₂

/-- The whole blocks (`m` of them, in `x26`), in two runs. -/
theorem whole_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub b.code)
    (nf : b.code.noFrames = true) {pre post : List Instr}
    (hc₁ : ∃ h, (taint.check (Taint.ofRegs (([.x26] : List Reg) ++ ([.x19, .x20, .x21, .x22, .x28] : List Reg)))
      (.seq (.block [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1]) (pass pre)) h).isSome = true)
    (hk₁ : (Code.seq (.block [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1]) (pass pre) : Prog isa).allInstrs
        (keeps (RegSet.ofList [.x19, .x20, .x21, .x22, .x28, .x26])) = true)
    (hn₁ : (Code.seq (.block [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1]) (pass pre) : Prog isa).noCalls = true)
    (hc₂ : ∃ h, (taint.check (Taint.ofRegs (([.x26] : List Reg) ++ ([.x19, .x20, .x21, .x22, .x28] : List Reg)))
      (.seq (.block (copy16 o0O ofsO ++ ([Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1] : List Instr))) (pass post)) h).isSome = true)
    {σ₁ σ₂ : State} (E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₁) (E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₂) {m : Nat}
    (h26₁ : σ₁.gpr .x26 = BitVec.ofNat 64 m) (h26₂ : σ₂.gpr .x26 = BitVec.ofNat 64 m)
    (hD₁ : VG.Proof.AesOcb.AArch64.DBuf K W σ₁ D (16 * m)) (hD₂ : VG.Proof.AesOcb.AArch64.DBuf K W σ₂ D (16 * m)) :
    RelCT isa (Eq2 σ₁ σ₂) (whole b pre post) TT := by
  have keep : ∀ {σ : State}, VG.Proof.AesOcb.AArch64.Env K W D R n SP σ → σ.gpr .x26 = BitVec.ofNat 64 m → VG.Proof.AesOcb.AArch64.DBuf K W σ D (16 * m) →
      ∀ t s', Exec isa (.seq (.block [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1]) (pass pre)) σ t s' →
        VG.Proof.AesOcb.AArch64.Env K W D R n SP s' ∧ s'.gpr .x26 = BitVec.ofNat 64 m ∧ VG.Proof.AesOcb.AArch64.DBuf K W s' D (16 * m) := fun E h26 hD _ _ h => by
    obtain ⟨g, sp, rd, wr⟩ := VG.Proof.AesOcb.AArch64.exec_keep _ hk₁ hn₁ h
    exact ⟨E.keep (fun q hq => g q (List.mem_append_left _ hq)) sp rd wr,
      by rw [g _ (by simp), h26], hD.of_eq rd wr⟩
  unfold whole
  refine RelCT.assoc (VG.Proof.AesOcb.AArch64.rel_seqE (VG.Proof.AesOcb.AArch64.rel_env E₁ E₂ [.x26] (by agree_tac [h26₁, h26₂]) hc₁) (keep E₁ h26₁ hD₁)
    (keep E₂ h26₂ hD₂) fun τ₁ τ₂ ⟨F₁, a₁, d₁⟩ ⟨F₂, a₂, d₂⟩ => ?_)
  refine rel_seq (VG.Proof.AesOcb.AArch64.callBlocks_rel ok ct L hR F₁ F₂ [.x26] (by agree_tac [a₁, a₂]) ⟨_, by taint_decide⟩
      (VG.Proof.AesOcb.AArch64.dataArgs_ok F₁.x21 a₁) (VG.Proof.AesOcb.AArch64.dataArgs_ok F₂.x21 a₂) (VG.Proof.AesOcb.AArch64.dstD d₁) (VG.Proof.AesOcb.AArch64.dstD d₂))
    (VG.Proof.AesOcb.AArch64.callBlocks_ok ok nf L F₁ hR (VG.Proof.AesOcb.AArch64.dataArgs_ok F₁.x21 a₁) (VG.Proof.AesOcb.AArch64.dstD d₁))
    (VG.Proof.AesOcb.AArch64.callBlocks_ok ok nf L F₂ hR (VG.Proof.AesOcb.AArch64.dataArgs_ok F₂.x21 a₂) (VG.Proof.AesOcb.AArch64.dstD d₂)) fun u₁ u₂ P₁ P₂ => ?_
  have c₁ : u₁.gpr .x26 = τ₁.gpr .x26 := P₁.saved _ (by decide) (by decide)
  have c₂ : u₂.gpr .x26 = τ₂.gpr .x26 := P₂.saved _ (by decide) (by decide)
  exact VG.Proof.AesOcb.AArch64.rel_env (F₁.of_saved P₁.saved P₁.sp P₁.rd P₁.wr) (F₂.of_saved P₂.saved P₂.sp P₂.rd P₂.wr) [.x26]
    (by agree_tac [c₁, c₂, a₁, a₂]) hc₂

/-- The whole blocks, if there are any, in two runs. -/
theorem wholeIte_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub b.code)
    (nf : b.code.noFrames = true) {pre post : List Instr}
    (hc₁ : ∃ h, (taint.check (Taint.ofRegs (([.x26] : List Reg) ++ ([.x19, .x20, .x21, .x22, .x28] : List Reg)))
      (.seq (.block [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1]) (pass pre)) h).isSome = true)
    (hk₁ : (Code.seq (.block [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1]) (pass pre) : Prog isa).allInstrs
        (keeps (RegSet.ofList [.x19, .x20, .x21, .x22, .x28, .x26])) = true)
    (hn₁ : (Code.seq (.block [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1]) (pass pre) : Prog isa).noCalls = true)
    (hc₂ : ∃ h, (taint.check (Taint.ofRegs (([.x26] : List Reg) ++ ([.x19, .x20, .x21, .x22, .x28] : List Reg)))
      (.seq (.block (copy16 o0O ofsO ++ ([Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1] : List Instr))) (pass post)) h).isSome = true)
    {σ₁ σ₂ : State} (E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₁) (E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₂) (hD₁ : VG.Proof.AesOcb.AArch64.DBuf K W σ₁ D n)
    (hD₂ : VG.Proof.AesOcb.AArch64.DBuf K W σ₂ D n) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block [.lsr .x .x26 .x28 4]) (.ite (.zero .x .x26) (.block [])
      (whole b pre post))) TT := by
  have hn := hD₁.lt
  have lsr : ∀ {σ : State}, VG.Proof.AesOcb.AArch64.Env K W D R n SP σ →
      WP isa (.block [.lsr .x .x26 .x28 4]) σ fun t => VG.Proof.AesOcb.AArch64.Env K W D R n SP t ∧ t.gpr .x26 = BitVec.ofNat 64 (n / 16) ∧
        t.rd = σ.rd ∧ t.wr = σ.wr := fun {σ} E =>
    WP.of_runBlock ⟨σ.write .x .x26 (σ.gpr .x28 >>> 4), by orun [], E.others (rs := [.x26]) (fun r hr => by simp at hr; simp [gpr_write, hr]) rfl rfl rfl,
      by simp [gpr_write, E.x28, lsr_ofNat _ _ hn], rfl, rfl⟩
  refine rel_seq (VG.Proof.AesOcb.AArch64.rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (lsr E₁) (lsr E₂)
    fun τ₁ τ₂ ⟨F₁, a₁, r₁, w₁⟩ ⟨F₂, a₂, r₂, w₂⟩ => ?_
  exact rel_ite (eval_zero a₁ (by omega)) (eval_zero a₂ (by omega)) (fun _ => RelCT.block_nil fun _ _ _ => trivial)
    fun _ => VG.Proof.AesOcb.AArch64.whole_rel L hR ok ct nf hc₁ hk₁ hn₁ hc₂ F₁ F₂ a₁ a₂ ((hD₁.take' (Nat.mul_div_le n 16)).of_eq r₁ w₁)
      ((hD₂.take' (Nat.mul_div_le n 16)).of_eq r₂ w₂)

/-- `body` for `seal`, in two runs. -/
theorem bodySeal_rel (v : BlocksImpl) {σ₁ σ₂ : State} (E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₁) (E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₂)
    (hD₁ : VG.Proof.AesOcb.AArch64.DBuf K W σ₁ D n) (hD₂ : VG.Proof.AesOcb.AArch64.DBuf K W σ₂ D n) {O₁ O₂ : Block}
    (hofs₁ : blockAtMem σ₁.mem (W + BitVec.ofNat 64 ofsO) = O₁) (ho0₁ : blockAtMem σ₁.mem (W + BitVec.ofNat 64 o0O) = O₁)
    (hck₁ : blockAtMem σ₁.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hl0₁ : blockAtMem σ₁.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar σ₁.mem K) 0)
    (hofs₂ : blockAtMem σ₂.mem (W + BitVec.ofNat 64 ofsO) = O₂) (ho0₂ : blockAtMem σ₂.mem (W + BitVec.ofNat 64 o0O) = O₂)
    (hck₂ : blockAtMem σ₂.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hl0₂ : blockAtMem σ₂.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar σ₂.mem K) 0) :
    RelCT isa (Eq2 σ₁ σ₂) (body (VG.Proof.AesOcb.AArch64.callees v) true) TT := by
  simp only [body, ↓reduceIte]
  refine RelCT.assoc (rel_seq (VG.Proof.AesOcb.AArch64.wholeIte_rel L hR v.encOk v.encCt v.encNoFrames ⟨_, by taint_decide⟩
      (by decide +kernel) (by decide +kernel) ⟨_, by taint_decide⟩ E₁ E₂ hD₁ hD₂)
    (VG.Proof.AesOcb.AArch64.wholeIte_ok (O0 := O₁) (l := ctxLstar σ₁.mem K)
      (ckF1 := VG.Proof.AesOcb.AArch64.ckOf fun i => blockAtMem σ₁.mem (D + BitVec.ofNat 64 (16 * i)))
      (ckF2 := fun _ => VG.Proof.AesOcb.AArch64.ckOf (fun i => blockAtMem σ₁.mem (D + BitVec.ofNat 64 (16 * i))) (n / 16))
      v.encOk v.encNoFrames VG.Proof.AesOcb.AArch64.hcall_enc VG.Proof.AesOcb.AArch64.sealPre_ok VG.Proof.AesOcb.AArch64.xorOfs_ok L E₁ hR hD₁ hofs₁ ho0₁ hck₁ hl0₁
      (fun _ => rfl) rfl (fun _ => rfl))
    (VG.Proof.AesOcb.AArch64.wholeIte_ok (O0 := O₂) (l := ctxLstar σ₂.mem K)
      (ckF1 := VG.Proof.AesOcb.AArch64.ckOf fun i => blockAtMem σ₂.mem (D + BitVec.ofNat 64 (16 * i)))
      (ckF2 := fun _ => VG.Proof.AesOcb.AArch64.ckOf (fun i => blockAtMem σ₂.mem (D + BitVec.ofNat 64 (16 * i))) (n / 16))
      v.encOk v.encNoFrames VG.Proof.AesOcb.AArch64.hcall_enc VG.Proof.AesOcb.AArch64.sealPre_ok VG.Proof.AesOcb.AArch64.xorOfs_ok L E₂ hR hD₂ hofs₂ ho0₂ hck₂ hl0₂
      (fun _ => rfl) rfl (fun _ => rfl)) fun t₁ t₂ P₁ P₂ => ?_)
  exact VG.Proof.AesOcb.AArch64.restIte_rel L hR v true P₁.env P₂.env hD₁.lt

/-- `body` for `open`, in two runs. -/
theorem bodyOpen_rel (v : BlocksImpl) {σ₁ σ₂ : State} (E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₁) (E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₂)
    (hD₁ : VG.Proof.AesOcb.AArch64.DBuf K W σ₁ D n) (hD₂ : VG.Proof.AesOcb.AArch64.DBuf K W σ₂ D n) {O₁ O₂ : Block}
    (hofs₁ : blockAtMem σ₁.mem (W + BitVec.ofNat 64 ofsO) = O₁) (ho0₁ : blockAtMem σ₁.mem (W + BitVec.ofNat 64 o0O) = O₁)
    (hck₁ : blockAtMem σ₁.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hl0₁ : blockAtMem σ₁.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar σ₁.mem K) 0)
    (hofs₂ : blockAtMem σ₂.mem (W + BitVec.ofNat 64 ofsO) = O₂) (ho0₂ : blockAtMem σ₂.mem (W + BitVec.ofNat 64 o0O) = O₂)
    (hck₂ : blockAtMem σ₂.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hl0₂ : blockAtMem σ₂.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar σ₂.mem K) 0) :
    RelCT isa (Eq2 σ₁ σ₂) (body (VG.Proof.AesOcb.AArch64.callees v) false) TT := by
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine RelCT.assoc (rel_seq (VG.Proof.AesOcb.AArch64.wholeIte_rel L hR v.decOk v.decCt v.decNoFrames ⟨_, by taint_decide⟩
      (by decide +kernel) (by decide +kernel) ⟨_, by taint_decide⟩ E₁ E₂ hD₁ hD₂)
    (VG.Proof.AesOcb.AArch64.wholeIte_ok (O0 := O₁) (l := ctxLstar σ₁.mem K) (ckF1 := fun _ => 0)
      (ckF2 := VG.Proof.AesOcb.AArch64.ckOf fun i => VG.Proof.AesOcb.AArch64.decG (bytesAt σ₁.mem K (16 * (R + 1)))
        (blockAtMem σ₁.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O₁ (ctxLstar σ₁.mem K) (i + 1)) ^^^
          offAt O₁ (ctxLstar σ₁.mem K) (i + 1))
      v.decOk v.decNoFrames VG.Proof.AesOcb.AArch64.hcall_dec VG.Proof.AesOcb.AArch64.xorOfs_ok VG.Proof.AesOcb.AArch64.openPost_ok L E₁ hR hD₁ hofs₁ ho0₁ hck₁ hl0₁
      (fun _ => rfl) rfl (fun _ => rfl))
    (VG.Proof.AesOcb.AArch64.wholeIte_ok (O0 := O₂) (l := ctxLstar σ₂.mem K) (ckF1 := fun _ => 0)
      (ckF2 := VG.Proof.AesOcb.AArch64.ckOf fun i => VG.Proof.AesOcb.AArch64.decG (bytesAt σ₂.mem K (16 * (R + 1)))
        (blockAtMem σ₂.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O₂ (ctxLstar σ₂.mem K) (i + 1)) ^^^
          offAt O₂ (ctxLstar σ₂.mem K) (i + 1))
      v.decOk v.decNoFrames VG.Proof.AesOcb.AArch64.hcall_dec VG.Proof.AesOcb.AArch64.xorOfs_ok VG.Proof.AesOcb.AArch64.openPost_ok L E₂ hR hD₂ hofs₂ ho0₂ hck₂ hl0₂
      (fun _ => rfl) rfl (fun _ => rfl)) fun t₁ t₂ P₁ P₂ => ?_)
  exact VG.Proof.AesOcb.AArch64.restIte_rel L hR v false P₁.env P₂.env hD₁.lt

end

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.CmpMask`. -/
section

/-!
# AES-OCB on AArch64: checking the tag and masking the data (`cmp`, `mask`)

Untrusted: everything here is checked by Lean. `cmp` ORs the XORs of the
first `tag_len` bytes of the received tag (at `W`) and the computed one (at
`W + t2O`) and leaves 1 at `W` if the OR is 0, else 0 (`cmp_ok`); `mask`
ANDs every byte of the data with `0 − ok`: the data stays if the tags were
equal, and is zeroed if not (`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (zeros)
open VG.Proof.Ocb (length_bytesAt)
open VG.Proof.AesGcm.AArch64 (read_one succ_ofNat bytesAt_succ in_of_covers eval_zero eval_nonzero)

/-! ## `cmp` -/

theorem zext8 (b : BitVec (8 * 1)) : BitVec.setWidth 64 (BitVec.setWidth 32 b) = BitVec.setWidth 64 (b : Byte) := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem setWidth_xor_eq_zero (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64 = 0#64) ↔ a = b := by
  rw [BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega),
      Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)] at this
  · intro h; rw [h]

theorem toNat_setWidth_xor (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).toNat < 256 := by
  simp only [BitVec.toNat_xor, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega), Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact Nat.xor_lt_two_pow (n := 8) a.isLt b.isLt

/-- `(x − 1) >> 63` is 1 if `x` is 0 and 0 if `0 < x < 256`. -/
theorem okBit {x : BitVec 64} (h : x.toNat < 256) :
    (x - BitVec.ofNat 64 1) >>> 63 = if x = 0#64 then 1#64 else 0#64 := by
  by_cases hx : x = 0#64
  · subst hx; decide
  · simp only [hx, ↓reduceIte]
    have hx' : 0 < x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hx
      · exact h0
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    rw [show 2 ^ 64 - 1 % 2 ^ 64 + x.toNat = (x.toNat - 1) + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]

/-- The registers `cmp` writes. -/
abbrev cmpRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x24]

abbrev cmpBody : List Instr :=
  [.ldrb .x9 .x11 0, .ldrb .x10 .x12 0, .logic .eor .x .x9 .x9 .x10, .logic .orr .x .x13 .x13 .x9,
    Impl.AesGcm.AArch64.ptr .x11 .x11 1, Impl.AesGcm.AArch64.ptr .x12 .x12 1, .subImm .x .x24 .x24 1]

/-- One step of `cmp`. -/
theorem cmpStep_ok (s : State) {A B : Addr} (ha : s.gpr .x11 = A) (hb : s.gpr .x12 = B)
    (ra : InRegions (s.rd ++ s.wr) A 1) (rb : InRegions (s.rd ++ s.wr) B 1) :
    ∃ s', runBlock isa VG.Proof.AesOcb.AArch64.cmpBody s = some s' ∧ s'.mem = s.mem ∧
      s'.gpr .x13 = s.gpr .x13 ||| ((s.mem A).setWidth 64 ^^^ (s.mem B).setWidth 64) ∧
      s'.gpr .x11 = A + BitVec.ofNat 64 1 ∧ s'.gpr .x12 = B + BitVec.ofNat 64 1 ∧
      s'.gpr .x24 = s.gpr .x24 - BitVec.ofNat 64 1 ∧
      (∀ r, r ∉ VG.Proof.AesOcb.AArch64.cmpRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by orun [ha, hb, ra, rb], ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [gpr_write, VG.Proof.AesGcm.AArch64.read_one, VG.Proof.AesOcb.AArch64.zext8, ha, hb]
  · simp [gpr_write, ha]
  · simp [gpr_write, hb]
  · simp [gpr_write]
  · simp only [VG.Proof.AesOcb.AArch64.cmpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hr
    simp [gpr_write, h₁, h₂, h₃, h₄, h₅, h₆]
  all_goals rfl

/-- `cmp`'s first block: the tag length, and the two tags' addresses. -/
theorem cmpHead_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP s) {tl : Nat}
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) :
    ∃ s₁, runBlock isa
        [Impl.AesGcm.AArch64.imm .x13 0, Impl.AesGcm.AArch64.mov .x11 .x19, Impl.AesGcm.AArch64.ptr .x12 .x19 t2O,
          ld .x24 .x19 tlO] s = some s₁ ∧
      s₁.gpr .x13 = 0#64 ∧ s₁.gpr .x11 = W + BitVec.ofNat 64 0 ∧ s₁.gpr .x12 = W + BitVec.ofNat 64 t2O + BitVec.ofNat 64 0 ∧
      s₁.gpr .x24 = BitVec.ofNat 64 (tl - 0) ∧ s₁.mem = s.mem ∧
      (∀ r, r ∉ VG.Proof.AesOcb.AArch64.cmpRegs → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have r₀ := E.perm.wR (show 248 + 8 ≤ 2560 by decide)
  simp only [tlO] at htl
  refine ⟨_, by orun [E.x19, r₀, htl], ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp [gpr_write]
  · simp [gpr_write, E.x19]
  · simp [gpr_write, E.x19, t2O]
  · simp [gpr_write, htl]
  · rfl
  · simp only [VG.Proof.AesOcb.AArch64.cmpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hr
    simp [gpr_write, h₁, h₂, h₃, h₄, h₅, h₆]
  all_goals rfl

/-- `cmp`: 1 at `W` if the first `tl` bytes at `W` and `W + t2O` are equal, else 0. -/
theorem cmp_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP s) {tl : Nat} (h1 : 1 ≤ tl)
    (h16 : tl ≤ 16) (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) :
    WP isa cmp s fun t => t.mem = s.mem.writeW (W + BitVec.ofNat 64 tagO)
        (if bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl then 1#64 else 0#64) ∧
      (∀ r, r ∉ VG.Proof.AesOcb.AArch64.cmpRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s₁, run₁, x13₁, x11₁, x12₁, x24₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.AArch64.cmpHead_ok E htl
  unfold cmp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hR : ∀ {d j : Nat}, d + j < 2560 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d + BitVec.ofNat 64 j) 1 :=
    fun h => by rw [Offset.add_add]; exact E.perm.wR (by omega)
  -- The loop: the OR of the XORs of the first `j` bytes in `x13`.
  refine WP.seq (WP.mono (WP.loop (M := isa) (c := .nonzero .x .x24)
    (Q := fun u => (u.gpr .x13).toNat < 256 ∧
      (u.gpr .x13 = 0#64 ↔ bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl) ∧
      u.mem = s.mem ∧ (∀ r, r ∉ VG.Proof.AesOcb.AArch64.cmpRegs → u.gpr r = s.gpr r) ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr)
    (fun (k : Nat) (u : State) => ∃ j, k = tl - j ∧ j < tl ∧ u.gpr .x11 = W + BitVec.ofNat 64 j ∧
      u.gpr .x12 = W + BitVec.ofNat 64 t2O + BitVec.ofNat 64 j ∧ u.gpr .x24 = BitVec.ofNat 64 (tl - j) ∧
      (u.gpr .x13).toNat < 256 ∧
      (u.gpr .x13 = 0#64 ↔ bytesAt s.mem W j = bytesAt s.mem (W + BitVec.ofNat 64 t2O) j) ∧
      u.mem = s.mem ∧ (∀ r, r ∉ VG.Proof.AesOcb.AArch64.cmpRegs → u.gpr r = s.gpr r) ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr) ?_ (tl - 0) _
    ⟨0, rfl, by omega, x11₁, x12₁, x24₁, by rw [x13₁]; decide, by rw [x13₁]; simp [bytesAt], m₁, g₁, sp₁, rd₁,
      wr₁⟩) fun u hu => ?_)
  · rintro k u ⟨j, rfl, hj, x11, x12, x24, lt, iff, mem, g, sp, rd, wr⟩
    obtain ⟨u', run', mem', x13', x11', x12', x24', g', sp', rd', wr'⟩ := VG.Proof.AesOcb.AArch64.cmpStep_ok u x11 x12
      (by rw [rd, wr, show W + BitVec.ofNat 64 j = W + BitVec.ofNat 64 0 + BitVec.ofNat 64 j by simp]
          exact hR (by omega))
      (by rw [rd, wr]; exact hR (by simp only [t2O]; omega))
    refine WP.of_runBlock ⟨u', run', ?_⟩
    rw [mem] at x13'
    have lt' : (u'.gpr .x13).toNat < 256 := by
      rw [x13', BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 8) lt (VG.Proof.AesOcb.AArch64.toNat_setWidth_xor _ _)
    have iff' : u'.gpr .x13 = 0#64 ↔
        bytesAt s.mem W (j + 1) = bytesAt s.mem (W + BitVec.ofNat 64 t2O) (j + 1) := by
      rw [x13', BitVec.or_eq_zero_iff, iff, VG.Proof.AesOcb.AArch64.setWidth_xor_eq_zero, bytesAt_succ, bytesAt_succ]
      constructor
      · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
      · intro h
        obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [length_bytesAt, length_bytesAt])
        exact ⟨h₁, List.head_eq_of_cons_eq h₂⟩
    have x24'' : u'.gpr .x24 = BitVec.ofNat 64 (tl - (j + 1)) := by
      rw [x24', x24, Offset.ofNat_sub_ofNat (by omega)]; rfl
    have ev := eval_nonzero (r := .x24) (a := tl - (j + 1)) x24'' (by omega)
    have gg : ∀ r, r ∉ VG.Proof.AesOcb.AArch64.cmpRegs → u'.gpr r = s.gpr r := fun r hr => by rw [g' r hr, g r hr]
    by_cases he : j + 1 = tl
    · left
      exact ⟨by rw [ev]; simp [he], lt', by rw [iff', he], by rw [mem', mem], gg, by rw [sp', sp],
        by rw [rd', rd], by rw [wr', wr]⟩
    · right
      exact ⟨by rw [ev]; simp; omega, tl - (j + 1), by omega, j + 1, rfl, by omega,
        by rw [x11', Offset.add_add], by rw [x12', Offset.add_add], x24'', lt', iff', by rw [mem', mem], gg,
        by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · obtain ⟨lt, iff, mem, g, sp, rd, wr⟩ := hu
    have h19 : u.gpr .x19 = W := by rw [g _ (by decide), E.x19]
    have w₀ : InRegions u.wr W 8 := by rw [wr]; simpa using E.perm.wW (d := 0) (n := 8) (by decide)
    refine WP.of_runBlock ⟨_, by orun [h19, w₀], ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · simp only [mem_write, gpr_write, ite_true, mem, tagO, BitVec.add_zero]
      rw [VG.Proof.AesOcb.AArch64.okBit lt]
      by_cases he : bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl
      · simp only [iff.mpr he, he, ↓reduceIte]
      · simp only [mt iff.mp he, he, ↓reduceIte]
    · simp only [VG.Proof.AesOcb.AArch64.cmpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hr
      simp only [gpr_write, h₅, ite_false]
      exact g r (by simp [VG.Proof.AesOcb.AArch64.cmpRegs, h₁, h₂, h₃, h₄, h₅, h₆])
    all_goals simp only [sp, rd, wr, sp_write, rd_write, wr_write, mem_write]

/-! ## `mask` -/

theorem mask_byte (b : BitVec (8 * 1)) (c : Bool) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 b)) &&& BitVec.setWidth 32 (0#64 - (if c then 1#64 else 0#64))))) =
      if c then (b : Byte) else 0 := by
  cases c
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [show (if true = true then 1#64 else 0#64) = 1#64 from rfl,
      show (0#64 - 1#64 : BitVec 64) = BitVec.allOnes 64 by decide]
    simp [BitVec.getLsbD_setWidth, show i < 32 by omega, show i < 64 by omega, hi]
    intro _
    rw [BitVec.getElem_eq_testBit_toNat, show (255#8).toNat = 2 ^ 8 - 1 from rfl, Nat.testBit_two_pow_sub_one]
    simp [hi]

/-- The registers `mask` writes. -/
abbrev maskRegs : List Reg := [.x9, .x10, .x23, .x24]

abbrev maskBody : List Instr :=
  [.ldrb .x9 .x23 0, .logic .and .w .x9 .x9 .x10, .strb .x9 .x23 0, Impl.AesGcm.AArch64.ptr .x23 .x23 1,
    .subImm .x .x24 .x24 1]

theorem maskStep_ok (s : State) {P : Addr} {c : Bool} (h23 : s.gpr .x23 = P)
    (h10 : s.gpr .x10 = 0#64 - (if c then 1#64 else 0#64))
    (rq : InRegions (s.rd ++ s.wr) P 1) (wq : InRegions s.wr P 1) :
    ∃ s', runBlock isa VG.Proof.AesOcb.AArch64.maskBody s = some s' ∧
      s'.mem = s.mem.writeW P ((if c then s.mem P else 0 : Byte)) ∧
      s'.gpr .x23 = P + BitVec.ofNat 64 1 ∧ s'.gpr .x24 = s.gpr .x24 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .x9 → r ≠ .x23 → r ≠ .x24 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by orun [h23, rq, wq, VG.Proof.AesOcb.AArch64.write1], ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_, ?_⟩
  · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, h10, h23, VG.Proof.AesGcm.AArch64.read_one, VG.Proof.AesOcb.AArch64.mask_byte]
  · simp [gpr_write, h23]
  · simp [gpr_write]
  · simp [gpr_write, h₁, h₂, h₃]
  all_goals rfl

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

/-- Every byte of the data ANDed with `0 − ok`. -/
theorem mask_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP s) (hD : VG.Proof.AesOcb.AArch64.DBuf K W s D n)
    {c : Bool} (hok : s.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64) :
    WP isa mask s fun t => (∀ r, r ∉ VG.Proof.AesOcb.AArch64.maskRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mem = writeBytes s.mem D (if c then bytesAt s.mem D n else zeros n) := by
  have r₃ : InRegions (s.rd ++ s.wr) W 8 := by simpa using E.perm.wR (d := 0) (n := 8) (by decide)
  simp only [tagO, BitVec.add_zero] at hok
  have hok' : s.mem.readW W 64 = if c then 1#64 else 0#64 := by simpa using hok
  have hn := hD.lt
  obtain ⟨s₁, run₁, m₁, x23₁, x24₁, x10₁, g₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x28, ld .x9 .x19 tagO,
        Impl.AesGcm.AArch64.imm .x10 0, .sub .x .x10 .x10 .x9] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .x23 = D ∧ s₁.gpr .x24 = BitVec.ofNat 64 n ∧
      s₁.gpr .x10 = 0#64 - (if c then 1#64 else 0#64) ∧
      (∀ r, r ∉ VG.Proof.AesOcb.AArch64.maskRegs → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [E.x19, r₃, hok'], ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_write, E.x21]
    · simp [gpr_write, E.x28]
    · simp [gpr_write, hok']
    · simp only [VG.Proof.AesOcb.AArch64.maskRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h₁, h₂, h₃, h₄⟩ := hr
      simp [gpr_write, h₁, h₂, h₃, h₄]
    all_goals rfl
  unfold mask
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_zero x24₁ hn) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := of_decide_eq_true hb
    subst hn0
    refine ⟨g₁, sp₁, rd₁, wr₁, ?_⟩
    rw [m₁]
    cases c <;> simp [bytesAt, zeros, writeBytes_nil]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  refine WP.loop (M := isa) (c := .nonzero .x .x24)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .x23 = D + BitVec.ofNat 64 j ∧
      t.gpr .x24 = BitVec.ofNat 64 (n - j) ∧ t.gpr .x10 = 0#64 - (if c then 1#64 else 0#64) ∧
      t.mem = writeBytes s.mem D (if c then bytesAt s.mem D j else zeros j) ∧
      (∀ r, r ∉ VG.Proof.AesOcb.AArch64.maskRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn0, by rw [x23₁]; simp, x24₁, x10₁, by rw [m₁]; cases c <;> simp [bytesAt, zeros, writeBytes_nil],
      g₁, sp₁, rd₁, wr₁⟩
  rintro k t ⟨j, rfl, hj, x23, x24, x10, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x23', x24', g', sp', rd', wr'⟩ := VG.Proof.AesOcb.AArch64.maskStep_ok t (c := c) x23 x10
    (by rw [rd, wr]; exact in_of_covers hD.rd hj hn) (by rw [wr]; exact in_of_covers hD.wr hj hn)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [VG.Proof.AesOcb.AArch64.length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (D + BitVec.ofNat 64 j) = s.mem (D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat D (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem D (if c then bytesAt s.mem D (j + 1) else zeros (j + 1)) := by
    rw [mem', hq, mem, VG.Proof.AesOcb.AArch64.mask_succ, writeBytes_snoc _ _ _ _ (by rw [VG.Proof.AesOcb.AArch64.length_mask]; omega), VG.Proof.AesOcb.AArch64.length_mask]
  have x24'' : t'.gpr .x24 = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [x24', x24, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev := eval_nonzero (r := .x24) (a := n - (j + 1)) x24'' (by omega)
  have gg : ∀ r, r ∉ VG.Proof.AesOcb.AArch64.maskRegs → t'.gpr r = s.gpr r := fun r hr => by
    simp only [VG.Proof.AesOcb.AArch64.maskRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g' r hr.1 hr.2.2.1 hr.2.2.2, g r (by simp [VG.Proof.AesOcb.AArch64.maskRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
  by_cases he : j + 1 = n
  · left
    exact ⟨by rw [ev]; simp [he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr], by rw [hmem, he]⟩
  · right
    exact ⟨by rw [ev]; simp; omega, n - (j + 1), by omega, j + 1, rfl, by omega,
      by rw [x23', Offset.add_add], x24'', by rw [g' _ (by decide) (by decide) (by decide), x10], hmem, gg,
      by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Entry`. -/
section

/-!
# AES-OCB on AArch64: the entry (`entry`)

Untrusted: everything here is checked by Lean. `entry` reads `W` from the
stack, saves our caller's registers at `W + savO` (`Spill.save_wp`), keeps
the data and its length in `x21` and `x28` and the other arguments in `W`,
computes `L_$` and `L_0` from `L_*` and zeroes the checksum (`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxLstar lDollar lAt)
open VG.Proof.AesGcm.AArch64 (in_left in_off)
open VG.Proof.Ocb (blockAtMem_frame)

theorem saved_fits : Spill.Fits saved := by decide

theorem saved_in : ∀ p ∈ saved, 160 ≤ p.2 ∧ p.2 + 8 ≤ 160 + 88 := by decide

theorem save_eq (b : Reg) : save b = Spill.saveCode b saved := rfl

theorem restore_eq : restore = Spill.restoreCode .x19 saved := rfl

/-- The parts of `W` that `entry` writes. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 32, 256⟩

/-- `ldr x, [sp, #off]` of a stack argument. -/
theorem ldrSp_ok {s : State} {t : Reg} {i : Nat} (hi : i < 4)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * i)) 8) :
    ∃ s', runBlock isa [.ldrSp t (8 * i)] s = some s' ∧ s' = s.write .x t (stackArg s i) := by
  refine ⟨_, ?_, rfl⟩
  have h₁ : (8 * i) % 8 = 0 := by omega
  have h₂ : 8 * i < 32768 := by omega
  simp only [runBlock_cons, runBlock_nil, runStep_some, VG.AArch64.exec, h₁, h₂, and_self, ite_true, State.load, hsp,
    Option.map_some, stackArg, stackArgAddr, Mem.readW, BitVec.setWidth_eq]

/-- What `entry` leaves. -/
structure EntryPost (K W D : Addr) (R n : Nat) (N A : Addr) (nl al tl : Nat) (s s₁ : State) : Prop where
  env : VG.Proof.AesOcb.AArch64.Env K W D R n s.sp s₁
  slots : VG.Proof.AesOcb.AArch64.Slots W N A nl al tl s₁.mem
  saved : Spill.Saved W s.gpr saved s₁.mem
  ld : blockAtMem s₁.mem (W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem K)
  l0 : blockAtMem s₁.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0
  ck : blockAtMem s₁.mem (W + BitVec.ofNat 64 ckO) = 0
  frame : Frame [VG.Proof.AesOcb.AArch64.entryR W] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem readW_writeW_off {m : Mem} {W : Addr} {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (W + BitVec.ofNat 64 e) v).readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep W h hd he) (by decide)

/-- `entry`. -/
theorem entry_ok {K W : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {s : State} (P : VG.Proof.AesOcb.AArch64.Perm K W s) {R n : Nat} {N A D : Addr}
    {nl al tl : Nat} (hW : stackArg s 2 = W) (htl : stackArg s 1 = BitVec.ofNat 64 tl)
    (hargs : Covers [⟨s.sp, 24⟩] (s.rd ++ s.wr)) (hargsW : (⟨s.sp, 24⟩ : Region).Disjoint ⟨W, 2560⟩)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = N)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 nl) (h4 : s.gpr .x4 = A) (h5 : s.gpr .x5 = BitVec.ofNat 64 al)
    (h6 : s.gpr .x6 = D) (h7 : s.gpr .x7 = BitVec.ofNat 64 n) :
    WP isa (.block entry) s (VG.Proof.AesOcb.AArch64.EntryPost K W D R n N A nl al tl s) := by
  have a₀ : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * 2)) 8 := in_off hargs (by decide) (by decide)
  obtain ⟨_, run₀, rfl⟩ := VG.Proof.AesOcb.AArch64.ldrSp_ok (t := .x9) (s := s) (i := 2) (by decide) a₀
  rw [hW] at run₀
  simp only [Nat.reduceMul] at run₀
  have x9₀ : (s.write .x .x9 W).gpr .x9 = W := by simp [gpr_write]
  have hin : ∀ p ∈ saved, InRegions (s.write .x .x9 W).wr ((s.write .x .x9 W).gpr .x9 + BitVec.ofNat 64 p.2) 8 :=
    fun p hp => by
      rw [x9₀, wr_write]; exact in_off P.w (by have := VG.Proof.AesOcb.AArch64.saved_in p hp; omega) (by decide)
  obtain ⟨g₀, hg₀⟩ : ∃ g, g = (s.write .x .x9 W).gpr := ⟨_, rfl⟩
  obtain ⟨M₁, hM₁⟩ : ∃ M, M = Spill.saveMem s.mem W g₀ saved := ⟨_, rfl⟩
  have hsv₁ : Spill.Saved W s.gpr saved M₁ := by
    have := Spill.saveMem_saved VG.Proof.AesOcb.AArch64.saved_fits s.mem W g₀
    rw [← hM₁] at this
    intro p hp
    rw [this p hp]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hg₀, gpr_write]
  have f₁ : Frame [⟨W + BitVec.ofNat 64 160, 88⟩] s.mem M₁ :=
    hM₁ ▸ Spill.saveMem_frame VG.Proof.AesOcb.AArch64.saved_in (by decide) _ _ _
  rw [entry]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨_, run₀, ?_⟩
  rw [VG.Proof.AesOcb.AArch64.save_eq, WP.block_append_iff]
  refine WP.mono (Spill.save_wp saved_fits.1 hin) fun s₁ St => ?_
  rw [x9₀] at St
  have g₁ : s₁.gpr = g₀ := by rw [St.gpr, hg₀]
  have m₁ : s₁.mem = M₁ := by rw [St.mem, hM₁, hg₀]; rfl
  -- the registers and the arguments kept in `W`
  have ww : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions s₁.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => by rw [St.wr, wr_write]; exact in_off P.w h (by decide)
  have w₁ := ww (d := nO) (by decide)
  have w₂ := ww (d := nlO) (by decide)
  have w₃ := ww (d := aadO) (by decide)
  have w₄ := ww (d := alenO) (by decide)
  have w₅ := ww (d := tlO) (by decide)
  simp only [nO, nlO, aadO, alenO, tlO] at w₁ w₂ w₃ w₄ w₅
  have gx : ∀ r, r ≠ .x9 → s₁.gpr r = s.gpr r := fun r hr => by rw [g₁, hg₀, gpr_write_of_ne _ _ _ hr]
  have x9₁ : s₁.gpr .x9 = W := by rw [g₁, hg₀, x9₀]
  obtain ⟨M₂, hM₂⟩ : ∃ M, M = (((M₁.writeW (W + BitVec.ofNat 64 272) N).writeW (W + BitVec.ofNat 64 280)
    (BitVec.ofNat 64 nl)).writeW (W + BitVec.ofNat 64 256) A).writeW (W + BitVec.ofNat 64 264) (BitVec.ofNat 64 al) :=
    ⟨_, rfl⟩
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x22₂, x28₂, g₂, m₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [Impl.AesGcm.AArch64.mov .x19 .x9, Impl.AesGcm.AArch64.mov .x20 .x0, Impl.AesGcm.AArch64.mov .x21 .x6,
        Impl.AesGcm.AArch64.mov .x22 .x1, Impl.AesGcm.AArch64.mov .x28 .x7, st .x19 nO .x2, st .x19 nlO .x3,
        st .x19 aadO .x4, st .x19 alenO .x5] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = K ∧ s₂.gpr .x21 = D ∧ s₂.gpr .x22 = BitVec.ofNat 64 R ∧
      s₂.gpr .x28 = BitVec.ofNat 64 n ∧ (∀ r, r ∉ [.x19, .x20, .x21, .x22, .x28] → s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = M₂ ∧ s₂.sp = s.sp ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by orun [x9₁, w₁, w₂, w₃, w₄], ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩ <;>
      try simp only [mem_write, sp_write, rd_write, wr_write]
    · simp [gpr_write, x9₁]
    · simp [gpr_write, gx .x0 (by decide), h0]
    · simp [gpr_write, gx .x6 (by decide), h6]
    · simp [gpr_write, gx .x1 (by decide), h1]
    · simp [gpr_write, gx .x7 (by decide), h7]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, gx .x2 (by decide), gx .x3 (by decide),
        gx .x4 (by decide), gx .x5 (by decide), h2, h3, h4, h5, x9₁, hM₂, m₁]
    · rw [St.sp, sp_write]
    · rw [St.rd, rd_write]
    · rw [St.wr, wr_write]
  have f₂ : Frame [⟨W, 2560⟩] s.mem s₂.mem := by
    rw [m₂, hM₂]
    have c : ∀ {d : Nat}, d + 8 ≤ 2560 → (⟨W, 2560⟩ : Region).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun h => Offset.contains_base W h (by omega)
    exact (((((f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (c (by decide))).writeW (List.mem_singleton_self _) _ (c (by decide))).writeW
      (List.mem_singleton_self _) _ (c (by decide))).writeW (List.mem_singleton_self _) _ (c (by decide)))
  have a₁ : InRegions (s₂.rd ++ s₂.wr) (s₂.sp + BitVec.ofNat 64 (8 * 1)) 8 := by
    rw [rd₂, wr₂, sp₂]; exact in_off hargs (by decide) (by decide)
  have tl₂ : stackArg s₂ 1 = BitVec.ofNat 64 tl := by
    rw [← htl]
    simp only [stackArg, stackArgAddr, sp₂]
    refine f₂.readW (r := ⟨s.sp + BitVec.ofNat 64 (8 * 1), 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact hargsW.sub_left (Offset.sub_base _ (by decide))
  obtain ⟨_, run₃, rfl⟩ := VG.Proof.AesOcb.AArch64.ldrSp_ok (t := .x10) (s := s₂) (i := 1) (by decide) a₁
  rw [tl₂] at run₃
  simp only [Nat.reduceMul] at run₃
  rw [show ([Impl.AesGcm.AArch64.mov .x19 .x9, Impl.AesGcm.AArch64.mov .x20 .x0, Impl.AesGcm.AArch64.mov .x21 .x6,
        Impl.AesGcm.AArch64.mov .x22 .x1, Impl.AesGcm.AArch64.mov .x28 .x7, st .x19 nO .x2, st .x19 nlO .x3,
        st .x19 aadO .x4, st .x19 alenO .x5, .ldrSp .x10 8, st .x19 tlO .x10] : List Instr) ++ (lsetup ++ zero16 ckO) =
      [Impl.AesGcm.AArch64.mov .x19 .x9, Impl.AesGcm.AArch64.mov .x20 .x0, Impl.AesGcm.AArch64.mov .x21 .x6,
        Impl.AesGcm.AArch64.mov .x22 .x1, Impl.AesGcm.AArch64.mov .x28 .x7, st .x19 nO .x2, st .x19 nlO .x3,
        st .x19 aadO .x4, st .x19 alenO .x5] ++ ([.ldrSp .x10 8] ++ ([st .x19 tlO .x10] ++ (lsetup ++ zero16 ckO)))
      from rfl, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨_, run₃, ?_⟩
  rw [WP.block_append_iff]
  obtain ⟨s₄, run₄, h₄⟩ : ∃ s₄, runBlock isa [st .x19 tlO .x10] (s₂.write .x .x10 (BitVec.ofNat 64 tl)) = some s₄ ∧
      s₄ = { s₂.write .x .x10 (BitVec.ofNat 64 tl) with mem := M₂.writeW (W + BitVec.ofNat 64 248) (BitVec.ofNat 64 tl) } :=
    ⟨_, by orun [x19₂, wr₂, m₂, show InRegions s.wr (W + BitVec.ofNat 64 248) 8 from in_off P.w (by decide) (by decide)],
      rfl⟩
  refine WP.of_runBlock ⟨_, run₄, ?_⟩
  have g₄ : ∀ r, r ≠ .x10 → s₄.gpr r = s₂.gpr r := fun r hr => by rw [h₄]; simp [gpr_write, hr]
  have m₄ : s₄.mem = M₂.writeW (W + BitVec.ofNat 64 248) (BitVec.ofNat 64 tl) := by rw [h₄]
  have sp₄ : s₄.sp = s.sp := by rw [h₄]; exact sp₂
  have rd₄ : s₄.rd = s.rd := by rw [h₄]; exact rd₂
  have wr₄ : s₄.wr = s.wr := by rw [h₄]; exact wr₂
  have E₄ : VG.Proof.AesOcb.AArch64.Env K W D R n s.sp s₄ := ⟨by rw [g₄ _ (by decide), x19₂], by rw [g₄ _ (by decide), x20₂],
    by rw [g₄ _ (by decide), x21₂], by rw [g₄ _ (by decide), x22₂], by rw [g₄ _ (by decide), x28₂], sp₄,
    P.of_eq rd₄ wr₄⟩
  -- `L_$`, `L_0` and the checksum
  obtain ⟨s₅, run₅, B₅⟩ := VG.Proof.AesOcb.AArch64.dbl_ok (s := s₄) (b := .x20) (a := 240) (d := ldO) (by decide) (by decide) E₄.x19 E₄.x20
    (by decide) (E₄.perm.kR (by decide)) (E₄.perm.kR (by decide)) (E₄.perm.wW (by decide)) (E₄.perm.wW (by decide))
  have E₅ := E₄.others B₅.gpr B₅.sp B₅.rd B₅.wr
  obtain ⟨s₆, run₆, B₆⟩ := VG.Proof.AesOcb.AArch64.dbl_ok (s := s₅) (b := .x19) (a := ldO) (d := l0O) (by decide) (by decide) E₅.x19 E₅.x19
    (by decide) (E₅.perm.wR (by decide)) (E₅.perm.wR (by decide)) (E₅.perm.wW (by decide)) (E₅.perm.wW (by decide))
  have E₆ := E₅.others B₆.gpr B₆.sp B₆.rd B₆.wr
  obtain ⟨s₇, run₇, B₇⟩ := VG.Proof.AesOcb.AArch64.zero16_ok (s := s₆) (d := ckO) (by decide) E₆.x19 (E₆.perm.wW (by decide))
    (E₆.perm.wW (by decide))
  refine WP.of_runBlock ⟨s₇, by rw [lsetup, VG.Proof.AesOcb.AArch64.runBlock_append, VG.Proof.AesOcb.AArch64.runBlock_append, run₅, Option.bind_some, run₆,
    Option.bind_some, run₇], ?_⟩
  have fr₇ : Frame [⟨W + BitVec.ofNat 64 32, 64⟩] s₄.mem s₇.mem :=
    ((B₅.frame.sub fun r hr => ?_).trans (B₆.frame.sub fun r hr => ?_)).trans (B₇.frame.sub fun r hr => ?_)
  rotate_left
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  have k₇ : ∀ {d : Nat}, 96 ≤ d → d + 8 ≤ 2560 →
      s₇.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ =>
    fr₇.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega)) h₂ (by decide)) (by decide)
  have k₄ : ∀ {d : Nat}, (d + 8 ≤ 248 ∨ 288 ≤ d) → d + 8 ≤ 2560 →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = M₁.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ => by
    rw [m₄, VG.Proof.AesOcb.AArch64.readW_writeW_off _ (by omega) (by omega) (by decide), hM₂,
      VG.Proof.AesOcb.AArch64.readW_writeW_off _ (by omega) (by omega) (by decide), VG.Proof.AesOcb.AArch64.readW_writeW_off _ (by omega) (by omega) (by decide),
      VG.Proof.AesOcb.AArch64.readW_writeW_off _ (by omega) (by omega) (by decide), VG.Proof.AesOcb.AArch64.readW_writeW_off _ (by omega) (by omega) (by decide)]
  have l₄ : blockAtMem s₄.mem (K + BitVec.ofNat 64 240) = ctxLstar s.mem K := by
    have f₄ : Frame [⟨W, 2560⟩] s.mem s₄.mem := by
      rw [m₄, ← m₂]; exact f₂.writeW (List.mem_singleton_self _) (BitVec.ofNat 64 tl) (Offset.contains_base W (d := 248) (n := 8) (k := 2560) (by decide) (by decide))
    rw [blockAtMem_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_left (Lay.kSub (by decide)))]
    rfl
  refine ⟨E₆.others B₇.gpr B₇.sp B₇.rd B₇.wr, ⟨?_, ?_, ?_, ?_, ?_⟩, fun p hp => ?_, ?_, ?_, B₇.val, ?_,
    by rw [B₇.rd, B₆.rd, B₅.rd, rd₄], by rw [B₇.wr, B₆.wr, B₅.wr, wr₄]⟩
  · rw [k₇ (by decide) (by decide), m₄]; exact Mem.readW_writeW_self64 ..
  · rw [k₇ (by decide) (by decide), m₄, VG.Proof.AesOcb.AArch64.readW_writeW_off _ (by decide) (by decide) (by decide), hM₂,
      VG.Proof.AesOcb.AArch64.readW_writeW_off _ (by decide) (by decide) (by decide)]; exact Mem.readW_writeW_self64 ..
  · rw [k₇ (by decide) (by decide), m₄, VG.Proof.AesOcb.AArch64.readW_writeW_off _ (by decide) (by decide) (by decide), hM₂]
    exact Mem.readW_writeW_self64 ..
  · rw [k₇ (by decide) (by decide), m₄, VG.Proof.AesOcb.AArch64.readW_writeW_off _ (by decide) (by decide) (by decide), hM₂,
      VG.Proof.AesOcb.AArch64.readW_writeW_off _ (by decide) (by decide) (by decide), VG.Proof.AesOcb.AArch64.readW_writeW_off _ (by decide) (by decide) (by decide),
      VG.Proof.AesOcb.AArch64.readW_writeW_off _ (by decide) (by decide) (by decide)]; exact Mem.readW_writeW_self64 ..
  · rw [k₇ (by decide) (by decide), m₄, VG.Proof.AesOcb.AArch64.readW_writeW_off _ (by decide) (by decide) (by decide), hM₂,
      VG.Proof.AesOcb.AArch64.readW_writeW_off _ (by decide) (by decide) (by decide), VG.Proof.AesOcb.AArch64.readW_writeW_off _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self64 ..
  · have hp' := VG.Proof.AesOcb.AArch64.saved_in p hp
    rw [← hsv₁ p hp, k₇ (by omega) (by omega), k₄ (.inl (by omega)) (by omega)]
  · rw [blockAtMem_frame B₇.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
      blockAtMem_frame B₆.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
      B₅.val, l₄]
    rfl
  · rw [blockAtMem_frame B₇.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
      B₆.val, B₅.val, l₄]
    rfl
  · have c : ∀ {d : Nat}, 32 ≤ d → d + 8 ≤ 288 → (VG.Proof.AesOcb.AArch64.entryR W).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun h₁ h₂ => Offset.contains W h₁ (by omega) (by decide)
    have f₄ : Frame [VG.Proof.AesOcb.AArch64.entryR W] s.mem s₄.mem := by
      rw [m₄, hM₂]
      exact (((((f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub W (by decide) (by decide)⟩).writeW
        (List.mem_singleton_self _) N (c (d := 272) (by decide) (by decide))).writeW (List.mem_singleton_self _)
        (BitVec.ofNat 64 nl) (c (d := 280) (by decide) (by decide))).writeW (List.mem_singleton_self _) A
        (c (d := 256) (by decide) (by decide))).writeW (List.mem_singleton_self _) (BitVec.ofNat 64 al)
        (c (d := 264) (by decide) (by decide))).writeW (List.mem_singleton_self _) (BitVec.ofNat 64 tl)
        (c (d := 248) (by decide) (by decide))
    exact f₄.trans (fr₇.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub W (by decide) (by decide)⟩)

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.NonceCT`. -/
section

/-!
# AES-OCB on AArch64: `Offset_0` is constant time

Untrusted: everything here is checked by Lean. `nonceBlock` loads the
nonce's address and length from `W`: its first block is split there, and the
rest runs from them (`nonceBlock_rel`); then the call (`callBlocks_rel`) and
`offset0`, whose shifts by `bottom` are masks, not branches (`nonce_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq)

theorem nonceBlock_rel {K W D : Addr} {R n : Nat} {SP : Addr} {σ₁ σ₂ : State} (E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₁)
    (E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₂) {N : Addr} {nl : Nat}
    (hN₁ : σ₁.mem.readW (W + BitVec.ofNat 64 nO) 64 = N) (hN₂ : σ₂.mem.readW (W + BitVec.ofNat 64 nO) 64 = N)
    (hnl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (hnl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl) :
    RelCT isa (Eq2 σ₁ σ₂) nonceBlock TT := by
  obtain ⟨s₁, run₁, x12₁, x13₁, g₁, -, -, sp₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.AArch64.nonceHead_ok E₁.x19 E₁.perm.w hN₁ hnl₁
  obtain ⟨s₂, run₂, x12₂, x13₂, g₂, -, -, sp₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.AArch64.nonceHead_ok E₂.x19 E₂.perm.w hN₂ hnl₂
  unfold nonceBlock
  refine rel_seq (VG.Proof.AesOcb.AArch64.rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (WP.of_runBlock ⟨s₁, run₁, rfl⟩)
    (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_
  subst h₁ h₂
  exact VG.Proof.AesOcb.AArch64.rel_env (E₁.keep (fun r hr => g₁ r (VG.Proof.AesOcb.AArch64.envRegs_ne hr) (VG.Proof.AesOcb.AArch64.envRegs_ne hr) (VG.Proof.AesOcb.AArch64.envRegs_ne hr)) sp₁ rd₁ wr₁)
    (E₂.keep (fun r hr => g₂ r (VG.Proof.AesOcb.AArch64.envRegs_ne hr) (VG.Proof.AesOcb.AArch64.envRegs_ne hr) (VG.Proof.AesOcb.AArch64.envRegs_ne hr)) sp₂ rd₂ wr₂) [.x12, .x13]
    (by agree_tac [x12₁, x12₂, x13₁, x13₂]) ⟨_, by taint_decide⟩

theorem nonce_rel (v : BlocksImpl) {K W D : Addr} {R n : Nat} {SP : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {σ₁ σ₂ : State}
    (E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₁) (E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₂) (hR : R = 10 ∨ R = 12 ∨ R = 14) {N : Addr} {nl t : Nat}
    (hN₁ : σ₁.mem.readW (W + BitVec.ofNat 64 nO) 64 = N) (hN₂ : σ₂.mem.readW (W + BitVec.ofNat 64 nO) 64 = N)
    (hnl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (hnl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (htl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t)
    (htl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15)
    (ht : t < 2 ^ 64) (hB₁ : VG.Proof.AesOcb.AArch64.Buf W σ₁ N nl) (hB₂ : VG.Proof.AesOcb.AArch64.Buf W σ₂ N nl) :
    RelCT isa (Eq2 σ₁ σ₂) (nonce (VG.Proof.AesOcb.AArch64.callees v)) TT := by
  unfold nonce
  refine rel_seq (VG.Proof.AesOcb.AArch64.nonceBlock_rel E₁ E₂ hN₁ hN₂ hnl₁ hnl₂)
    (VG.Proof.AesOcb.AArch64.nonceBlock_ok L E₁.x19 E₁.perm.w hN₁ hnl₁ htl₁ h1 h15 ht hB₁)
    (VG.Proof.AesOcb.AArch64.nonceBlock_ok L E₂.x19 E₂.perm.w hN₂ hnl₂ htl₂ h1 h15 ht hB₂) fun τ₁ τ₂ P₁ P₂ => ?_
  have F₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP τ₁ := E₁.others P₁.gpr P₁.sp P₁.rd P₁.wr
  have F₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP τ₂ := E₂.others P₂.gpr P₂.sp P₂.rd P₂.wr
  refine rel_seq (VG.Proof.AesOcb.AArch64.callBlocks_rel v.encOk v.encCt L hR F₁ F₂ [] (by agree_tac []) ⟨_, by taint_decide⟩
      (VG.Proof.AesOcb.AArch64.oneBlock_ok F₁.x19 tmpO (by decide)) (VG.Proof.AesOcb.AArch64.oneBlock_ok F₂.x19 tmpO (by decide))
      (VG.Proof.AesOcb.AArch64.dstW L F₁.perm (d := tmpO) (n := 1) (by decide)) (VG.Proof.AesOcb.AArch64.dstW L F₂.perm (d := tmpO) (n := 1) (by decide)))
    (VG.Proof.AesOcb.AArch64.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L F₁ hR (VG.Proof.AesOcb.AArch64.oneBlock_ok F₁.x19 tmpO (by decide))
      (VG.Proof.AesOcb.AArch64.dstW L F₁.perm (d := tmpO) (n := 1) (by decide)))
    (VG.Proof.AesOcb.AArch64.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L F₂ hR (VG.Proof.AesOcb.AArch64.oneBlock_ok F₂.x19 tmpO (by decide))
      (VG.Proof.AesOcb.AArch64.dstW L F₂.perm (d := tmpO) (n := 1) (by decide))) fun u₁ u₂ Q₁ Q₂ => ?_
  exact VG.Proof.AesOcb.AArch64.rel_env (F₁.of_saved Q₁.saved Q₁.sp Q₁.rd Q₁.wr) (F₂.of_saved Q₂.saved Q₂.sp Q₂.rd Q₂.wr) []
    (by agree_tac []) ⟨_, by taint_decide⟩

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.HashCT`. -/
section

/-!
# AES-OCB on AArch64: `HASH` is constant time

Untrusted: everything here is checked by Lean. The two runs hash associated
data of the same length at the same address `A`. The first block loads `A`
and the length from `W` (which the taint analysis takes as secret, so no
later code uses them from there); the correctness proofs pin `x23` (the
position in the data), `x25` (the block's index) and `x26` (the blocks left)
to the same values in both runs. Each chunk fills its buffer and adds it to
the sum by code the taint analysis checks from those, with the call between
on the same arguments (`chunk_rel`); both runs are at the same chunk at each
iteration (`hashLoop_rel`); the rest, if any, likewise (`hashRest_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ite eval_zero eval_nonzero)

section
variable {K W D : Addr} {n R : Nat} {SP : Addr} {A : Addr}
  {ciph₁ ciph₂ : Cipher} {l₁ l₂ : Block} {a₁ a₂ : List Byte} {s₁ s₂ : State}

/-- The blocks of the rest of the associated data, before its call. -/
theorem hashRestPre_ok (C : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph₁ l₁ A a₁ s₁) {t : State}
    (H : VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph₁ l₁ A a₁ s₁ t (a₁.length / 16)) (hr : 0 < a₁.length % 16)
    (h24 : t.gpr .x24 = BitVec.ofNat 64 (a₁.length % 16)) :
    WP isa (.seq (.seq (.block (xor16 .x20 240 ohO)) (padTo bufO)) (.block (xor16 .x19 ohO bufO))) t
      (VG.Proof.AesOcb.AArch64.Env K W D R n SP) := by
  have E := H.env
  have hs := C.short
  generalize hm : a₁.length / 16 = m at H
  obtain ⟨t₁, run₁, B₁⟩ := VG.Proof.AesOcb.AArch64.xor16_ok (s := t) (b := .x20) (a := 240) (d := ohO) (by decide) (by decide) E.x19 E.x20
    (by decide) (by decide) (by decide) (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide))
    (E.perm.wW (by decide))
  have E₁ := E.others B₁.gpr B₁.sp B₁.rd B₁.wr
  have hB := C.buf.slice (a := 16 * m) (k := a₁.length % 16) (by omega)
  have hS : Covers [⟨A + BitVec.ofNat 64 (16 * m), a₁.length % 16⟩] (t₁.rd ++ t₁.wr) := by
    rw [B₁.rd, B₁.wr, H.rd, H.wr]; exact hB.rd
  have hSD : (⟨A + BitVec.ofNat 64 (16 * m), a₁.length % 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 bufO, 16⟩ :=
    hB.w.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩))
  refine WP.mono (VG.Proof.AesOcb.AArch64.padTo_ok E₁.x19 E₁.perm.w hr (by omega) (by decide)
    (by rw [B₁.gpr _ (by decide), H.x23]) (by rw [B₁.gpr _ (by decide), h24]) hS hSD)
    fun t₂ ⟨_, _, g₂, sp₂, rd₂, wr₂⟩ => ?_
  have E₂ := E₁.others g₂ sp₂ rd₂ wr₂
  obtain ⟨t₃, run₃, B₃⟩ := VG.Proof.AesOcb.AArch64.xor16_ok (s := t₂) (b := .x19) (a := ohO) (d := bufO) (by decide) (by decide) E₂.x19
    E₂.x19 (by decide) (by decide) (by decide) (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide))
    (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  exact WP.of_runBlock ⟨t₃, run₃, E₂.others B₃.gpr B₃.sp B₃.rd B₃.wr⟩

/-- The rest of the associated data, in two runs. -/
theorem hashRest_rel (v : BlocksImpl) (C₁ : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph₁ l₁ A a₁ s₁) (C₂ : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph₂ l₂ A a₂ s₂)
    (hlen : a₂.length = a₁.length) {τ₁ τ₂ : State}
    (H₁ : VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph₁ l₁ A a₁ s₁ τ₁ (a₁.length / 16))
    (H₂ : VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph₂ l₂ A a₂ s₂ τ₂ (a₂.length / 16)) (hr : 0 < a₁.length % 16)
    (h24₁ : τ₁.gpr .x24 = BitVec.ofNat 64 (a₁.length % 16)) (h24₂ : τ₂.gpr .x24 = BitVec.ofNat 64 (a₂.length % 16)) :
    RelCT isa (Eq2 τ₁ τ₂) (hashRest (VG.Proof.AesOcb.AArch64.callees v)) TT := by
  unfold hashRest
  refine RelCT.assoc (RelCT.assoc (rel_seq (VG.Proof.AesOcb.AArch64.rel_env H₁.env H₂.env [.x23, .x24]
      (by agree_tac [H₁.x23, H₂.x23, h24₁, h24₂, hlen]) ⟨_, by taint_decide⟩)
    (VG.Proof.AesOcb.AArch64.hashRestPre_ok C₁ H₁ hr h24₁) (VG.Proof.AesOcb.AArch64.hashRestPre_ok C₂ H₂ (by rw [hlen]; exact hr) h24₂) fun u₁ u₂ E₁ E₂ => ?_))
  have L := C₁.lay
  refine rel_seq (VG.Proof.AesOcb.AArch64.callBlocks_rel v.encOk v.encCt L C₁.rounds E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩
      (VG.Proof.AesOcb.AArch64.oneBlock_ok E₁.x19 bufO (by decide)) (VG.Proof.AesOcb.AArch64.oneBlock_ok E₂.x19 bufO (by decide))
      (VG.Proof.AesOcb.AArch64.dstW L E₁.perm (d := bufO) (n := 1) (by decide)) (VG.Proof.AesOcb.AArch64.dstW L E₂.perm (d := bufO) (n := 1) (by decide)))
    (VG.Proof.AesOcb.AArch64.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L E₁ C₁.rounds (VG.Proof.AesOcb.AArch64.oneBlock_ok E₁.x19 bufO (by decide))
      (VG.Proof.AesOcb.AArch64.dstW L E₁.perm (d := bufO) (n := 1) (by decide)))
    (VG.Proof.AesOcb.AArch64.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L E₂ C₁.rounds (VG.Proof.AesOcb.AArch64.oneBlock_ok E₂.x19 bufO (by decide))
      (VG.Proof.AesOcb.AArch64.dstW L E₂.perm (d := bufO) (n := 1) (by decide))) fun w₁ w₂ P₁ P₂ => ?_
  exact VG.Proof.AesOcb.AArch64.rel_env (E₁.of_saved P₁.saved P₁.sp P₁.rd P₁.wr) (E₂.of_saved P₂.saved P₂.sp P₂.rd P₂.wr) []
    (by agree_tac []) ⟨_, by taint_decide⟩

/-- A chunk, in two runs at the same block `j`. -/
theorem chunk_rel (v : BlocksImpl) (C₁ : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph₁ l₁ A a₁ s₁) (C₂ : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph₂ l₂ A a₂ s₂)
    (hlen : a₂.length = a₁.length) {τ₁ τ₂ : State} {j : Nat}
    (H₁ : VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph₁ l₁ A a₁ s₁ τ₁ j) (H₂ : VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph₂ l₂ A a₂ s₂ τ₂ j)
    (hj : j < a₁.length / 16) : RelCT isa (Eq2 τ₁ τ₂) (hashChunk (VG.Proof.AesOcb.AArch64.callees v)) TT := by
  have hs := C₁.short
  have L := C₁.lay
  have x26₂ := H₂.x26
  rw [hlen] at x26₂
  unfold hashChunk
  refine RelCT.assoc (rel_seq (VG.Proof.AesOcb.AArch64.rel_env H₁.env H₂.env [.x26] (by agree_tac [H₁.x26, x26₂]) ⟨_, by taint_decide⟩)
    (VG.Proof.AesOcb.AArch64.chunkHead_ok (L := a₁.length / 16 - j) (by omega) H₁.x26)
    (VG.Proof.AesOcb.AArch64.chunkHead_ok (L := a₁.length / 16 - j) (by omega) x26₂)
    fun t₁ t₂ ⟨h24₁, g₁, m₁, sp₁, rd₁, wr₁⟩ ⟨h24₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_)
  have H₁' := H₁.head g₁ m₁ sp₁ rd₁ wr₁
  have H₂' := H₂.head g₂ m₂ sp₂ rd₂ wr₂
  obtain ⟨u₁, run₁, F₁⟩ := VG.Proof.AesOcb.AArch64.bufStart_inv H₁' h24₁
  obtain ⟨u₂, run₂, F₂⟩ := VG.Proof.AesOcb.AArch64.bufStart_inv H₂' h24₂
  refine rel_seq (F₁ := fun t => VG.Proof.AesOcb.AArch64.FillInv K W D R n SP ciph₁ l₁ A a₁ s₁ j (min 8 (a₁.length / 16 - j)) t 0)
    (F₂ := fun t => VG.Proof.AesOcb.AArch64.FillInv K W D R n SP ciph₂ l₂ A a₂ s₂ j (min 8 (a₁.length / 16 - j)) t 0)
    (VG.Proof.AesOcb.AArch64.rel_env H₁'.env H₂'.env [.x24] (by agree_tac [h24₁, h24₂]) ⟨_, by taint_decide⟩)
    (WP.of_runBlock ⟨u₁, run₁, F₁⟩) (WP.of_runBlock ⟨u₂, run₂, F₂⟩) fun u₁ u₂ F₁ F₂ => ?_
  have x26f := F₂.x26
  rw [hlen] at x26f
  refine rel_seq (VG.Proof.AesOcb.AArch64.rel_env F₁.env F₂.env [.x15, .x23, .x24, .x25, .x26, .x27]
      (by agree_tac [F₁.x15, F₂.x15, F₁.x23, F₂.x23, F₁.x24, F₂.x24, F₁.x25, F₂.x25, F₁.x26, x26f, F₁.x27, F₂.x27])
      ⟨_, by taint_decide⟩)
    (VG.Proof.AesOcb.AArch64.fill_ok C₁ (by omega) (by omega) (by omega) F₁) (VG.Proof.AesOcb.AArch64.fill_ok C₂ (by omega) (by omega) (by omega) F₂)
    fun w₁ w₂ G₁ G₂ => ?_
  have x26g := G₂.x26
  rw [hlen] at x26g
  refine rel_seq (VG.Proof.AesOcb.AArch64.callBlocks_rel v.encOk v.encCt L C₁.rounds G₁.env G₂.env [.x24] (by agree_tac [G₁.x24, G₂.x24])
      ⟨_, by taint_decide⟩ (VG.Proof.AesOcb.AArch64.bufArgs_ok G₁.env.x19 G₁.x24) (VG.Proof.AesOcb.AArch64.bufArgs_ok G₂.env.x19 G₂.x24)
      (VG.Proof.AesOcb.AArch64.dstW L G₁.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega))
      (VG.Proof.AesOcb.AArch64.dstW L G₂.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega)))
    (VG.Proof.AesOcb.AArch64.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L G₁.env C₁.rounds (VG.Proof.AesOcb.AArch64.bufArgs_ok G₁.env.x19 G₁.x24)
      (VG.Proof.AesOcb.AArch64.dstW L G₁.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega)))
    (VG.Proof.AesOcb.AArch64.callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNoFrames L G₂.env C₁.rounds (VG.Proof.AesOcb.AArch64.bufArgs_ok G₂.env.x19 G₂.x24)
      (VG.Proof.AesOcb.AArch64.dstW L G₂.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega))) fun y₁ y₂ P₁ P₂ => ?_
  have a₁ : y₁.gpr .x24 = w₁.gpr .x24 := P₁.saved _ (by decide) (by decide)
  have a₂ : y₂.gpr .x24 = w₂.gpr .x24 := P₂.saved _ (by decide) (by decide)
  have b₁ : y₁.gpr .x26 = w₁.gpr .x26 := P₁.saved _ (by decide) (by decide)
  have b₂ : y₂.gpr .x26 = w₂.gpr .x26 := P₂.saved _ (by decide) (by decide)
  exact VG.Proof.AesOcb.AArch64.rel_env (G₁.env.of_saved P₁.saved P₁.sp P₁.rd P₁.wr) (G₂.env.of_saved P₂.saved P₂.sp P₂.rd P₂.wr)
    [.x24, .x26] (by agree_tac [a₁, a₂, b₁, b₂, G₁.x24, G₂.x24, G₁.x26, x26g]) ⟨_, by taint_decide⟩

/-- The chunks, in two runs. -/
theorem hashLoop_rel (v : BlocksImpl) (C₁ : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph₁ l₁ A a₁ s₁)
    (C₂ : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph₂ l₂ A a₂ s₂) (hlen : a₂.length = a₁.length) {τ₁ τ₂ : State}
    (H₁ : VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph₁ l₁ A a₁ s₁ τ₁ 0) (H₂ : VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph₂ l₂ A a₂ s₂ τ₂ 0)
    (hm : 0 < a₁.length / 16) :
    RelCT isa (Eq2 τ₁ τ₂) (.loop (hashChunk (VG.Proof.AesOcb.AArch64.callees v)) (.nonzero .x .x26)) TT := by
  have hs := C₁.short
  refine (RelCT.loop (Q := TT)
    (fun (k : Nat) (u₁ u₂ : State) => ∃ j, k = a₁.length / 16 - j ∧ j < a₁.length / 16 ∧
      VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph₁ l₁ A a₁ s₁ u₁ j ∧ VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph₂ l₂ A a₂ s₂ u₂ j) (fun k => ?_)
    (a₁.length / 16 - 0)).mono (fun x y hxy => by obtain ⟨rfl, rfl⟩ := hxy; exact ⟨0, rfl, hm, H₁, H₂⟩)
    fun _ _ h => h
  refine VG.Proof.AesOcb.AArch64.rel_of_pt fun σ₁ σ₂ ⟨j, hk, hj, G₁, G₂⟩ => ?_
  refine ((VG.Proof.AesOcb.AArch64.chunk_rel v C₁ C₂ hlen G₁ G₂ hj).wp
    (F₁ := fun u => VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph₁ l₁ A a₁ s₁ u (j + min 8 (a₁.length / 16 - j)))
    (F₂ := fun u => VG.Proof.AesOcb.AArch64.HInv K W D R n SP ciph₂ l₂ A a₂ s₂ u (j + min 8 (a₂.length / 16 - j))) fun x y hxy => by
      obtain ⟨rfl, rfl⟩ := hxy
      exact ⟨VG.Proof.AesOcb.AArch64.hashChunk_ok v C₁ G₁ hj, VG.Proof.AesOcb.AArch64.hashChunk_ok v C₂ G₂ (by rw [hlen]; exact hj)⟩).mono (fun _ _ h => h)
    fun u₁ u₂ ⟨_, F₁, F₂⟩ => ?_
  rw [hlen] at F₂
  have ev₁ := eval_nonzero F₁.x26 (by omega)
  have ev₂ := eval_nonzero F₂.x26 (by rw [hlen]; omega)
  rw [hlen] at ev₂
  refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun h => ?_⟩
  rw [ev₁] at h
  have he : ¬ a₁.length / 16 - (j + min 8 (a₁.length / 16 - j)) = 0 := by simpa using h
  exact ⟨a₁.length / 16 - (j + min 8 (a₁.length / 16 - j)), by omega, j + min 8 (a₁.length / 16 - j), rfl,
    by omega, F₁, F₂⟩

/-- `HASH`, in two runs. -/
theorem hash_rel (v : BlocksImpl) (C₁ : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph₁ l₁ A a₁ s₁) (C₂ : VG.Proof.AesOcb.AArch64.HCtx K W D n R ciph₂ l₂ A a₂ s₂)
    (hlen : a₂.length = a₁.length) (E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP s₁) (E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP s₂)
    (haad₁ : s₁.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (haad₂ : s₂.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen₁ : s₁.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a₁.length)
    (halen₂ : s₂.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a₂.length)
    (hl0₁ : blockAtMem s₁.mem (W + BitVec.ofNat 64 l0O) = lAt l₁ 0)
    (hl0₂ : blockAtMem s₂.mem (W + BitVec.ofNat 64 l0O) = lAt l₂ 0) :
    RelCT isa (Eq2 s₁ s₂) (Impl.AesOcb.AArch64.hash (VG.Proof.AesOcb.AArch64.callees v)) TT := by
  have hs := C₁.short
  unfold Impl.AesOcb.AArch64.hash
  refine RelCT.assoc (rel_seq (VG.Proof.AesOcb.AArch64.rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩)
    (VG.Proof.AesOcb.AArch64.hashHead_ok C₁ E₁ haad₁ halen₁ hl0₁) (VG.Proof.AesOcb.AArch64.hashHead_ok C₂ E₂ haad₂ halen₂ hl0₂) fun t₁ t₂ H₁ H₂ => ?_)
  have x26₂ := H₂.x26
  rw [hlen] at x26₂
  refine rel_seq (rel_ite (eval_zero H₁.x26 (by omega)) (eval_zero x26₂ (by omega))
      (fun _ => RelCT.block_nil fun _ _ _ => trivial)
      (fun hb => VG.Proof.AesOcb.AArch64.hashLoop_rel v C₁ C₂ hlen H₁ H₂ (Nat.pos_of_ne_zero (of_decide_eq_false hb))))
    (VG.Proof.AesOcb.AArch64.hashBody_ok v C₁ H₁) (VG.Proof.AesOcb.AArch64.hashBody_ok v C₂ H₂) fun u₁ u₂ G₁ G₂ => ?_
  refine rel_seq (VG.Proof.AesOcb.AArch64.rel_env G₁.env G₂.env [] (by agree_tac []) ⟨_, by taint_decide⟩)
    (VG.Proof.AesOcb.AArch64.tailHead_ok C₁ halen₁ G₁) (VG.Proof.AesOcb.AArch64.tailHead_ok C₂ halen₂ G₂) fun w₁ w₂ ⟨T₁, h24₁⟩ ⟨T₂, h24₂⟩ => ?_
  have h24₂' := h24₂
  rw [hlen] at h24₂'
  exact rel_ite (eval_zero h24₁ (by omega)) (eval_zero h24₂' (by omega))
    (fun _ => RelCT.block_nil fun _ _ _ => trivial)
    (fun hb => VG.Proof.AesOcb.AArch64.hashRest_rel v C₁ C₂ hlen T₁ T₂ (by have := of_decide_eq_false hb; omega) h24₁ h24₂)

end

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Seal`. -/
section

/-!
# AES-OCB on AArch64: `vg_aes_ocb_seal`

Untrusted: everything here is checked by Lean. The preconditions `sealPreA`
and `openPreA` give the facts the proofs use about the arguments (`Args`,
`sealArgs_of`, `openArgs_of`). `seal` is `front`: `entry`, `Offset_0`
(`nonce`), `HASH` (`hash`), the data (`body`) and the tag at `W` (`tag`);
then the copy of the tag to `tag`, whose address is on the stack
(`tagOut`), and `restore` (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (covers_of_mem covers_left)

/-- What `seal` and `open` are given: the key context at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`) and the
working space at `W`. -/
structure Args (s : State) (K W N A D : Addr) (R nl al n tl : Nat) (T : Addr) : Prop where
  lay : VG.Proof.AesOcb.AArch64.Lay K W
  perm : VG.Proof.AesOcb.AArch64.Perm K W s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : VG.Proof.AesOcb.AArch64.Buf W s N nl
  aad : VG.Proof.AesOcb.AArch64.Buf W s A al
  data : VG.Proof.AesOcb.AArch64.DBuf K W s D n
  tag : VG.Proof.AesOcb.AArch64.Buf W s T tl
  nd : (⟨N, nl⟩ : Region).Disjoint ⟨D, n⟩
  td : (⟨T, tl⟩ : Region).Disjoint ⟨D, n⟩
  ad : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩
  n1 : 1 ≤ nl
  n15 : nl ≤ 15
  t1 : 1 ≤ tl
  t16 : tl ≤ 16
  args : Covers [⟨s.sp, 24⟩] (s.rd ++ s.wr)
  argsW : (⟨s.sp, 24⟩ : Region).Disjoint ⟨W, 2560⟩
  argsD : (⟨s.sp, 24⟩ : Region).Disjoint ⟨D, n⟩

/-- `Args` from the facts both preconditions give, for a state that may
read the key context, the nonce, the associated data, the arguments on the
stack and the tag, and write the data and `W`. -/
theorem args_of {s : State} (h : VG.Proof.AesOcb.AArch64.oneFacts s)
    (mrd : ∀ r ∈ [VG.Proof.AesOcb.AArch64.aCtx s, VG.Proof.AesOcb.AArch64.aNonce s, VG.Proof.AesOcb.AArch64.aAad s, VG.Proof.AesOcb.AArch64.args s 3, VG.Proof.AesOcb.AArch64.aTag s], Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [VG.Proof.AesOcb.AArch64.aData s, VG.Proof.AesOcb.AArch64.aWork s], Covers [r] s.wr) :
    VG.Proof.AesOcb.AArch64.Args s (s.gpr .x0) (stackArg s 2) (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (s.gpr .x1).toNat (s.gpr .x3).toNat
      (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨d3, d4, d5, d6, d7, d8, t1, t2, d9, d10, d11, b12, b13, b14, b15, bt, b16, _, hR, hv⟩ := h
  simp only [Spec.Ocb.lengthsOk, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨ht1, ht16⟩, hn1⟩, hn15⟩ := hv
  have sp0 : stackArgAddr s 0 = s.sp := by simp [stackArgAddr]
  have ha := mrd (VG.Proof.AesOcb.AArch64.args s 3) (by simp)
  simp only [VG.Proof.AesOcb.AArch64.args, sp0] at ha d10 d11
  exact {
    lay := ⟨b12, b16, d4⟩
    perm := ⟨mrd _ (by simp), mwr _ (by simp)⟩
    rounds := hR
    nonce := ⟨mrd _ (by simp), BitVec.isLt _, b13, d6⟩
    aad := ⟨mrd _ (by simp), BitVec.isLt _, b14, d8⟩
    data := ⟨⟨covers_left (mwr _ (by simp)), BitVec.isLt _, b15, d9⟩, mwr _ (by simp), d3⟩
    tag := ⟨mrd _ (by simp), BitVec.isLt _, bt, t2⟩
    nd := d5
    ad := d7
    td := t1
    n1 := hn1
    n15 := hn15
    t1 := ht1
    t16 := ht16
    args := ha
    argsW := d11.symm
    argsD := d10.symm }

theorem sealArgs_of {s : State} (h : VG.Proof.AesOcb.AArch64.sealPreA s) :
    VG.Proof.AesOcb.AArch64.Args s (s.gpr .x0) (stackArg s 2) (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (s.gpr .x1).toNat (s.gpr .x3).toNat
      (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨hrd, hwr, -, -, -, -, hf⟩ := h
  refine VG.Proof.AesOcb.AArch64.args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_of_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_of_mem (by simp))

theorem openArgs_of {s : State} (h : VG.Proof.AesOcb.AArch64.openPreA s) :
    VG.Proof.AesOcb.AArch64.Args s (s.gpr .x0) (stackArg s 2) (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (s.gpr .x1).toNat (s.gpr .x3).toNat
      (s.gpr .x5).toNat (s.gpr .x7).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨hrd, hwr, hf⟩ := h
  refine VG.Proof.AesOcb.AArch64.args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_of_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_of_mem (by simp))

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-! ## Frames -/

/-- A frame within `W`. -/
theorem frameW {W : Addr} {rs : List Region} {m m' : Mem} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r ⟨W, 2560⟩) : Frame [⟨W, 2560⟩] m m' :=
  h.sub fun r hr => ⟨_, List.mem_singleton_self _, hs r hr⟩

theorem entryR_W (W : Addr) : ∀ r ∈ [VG.Proof.AesOcb.AArch64.entryR W], Region.Sub r ⟨W, 2560⟩ := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)

theorem nonceR_W (W : Addr) : ∀ r ∈ VG.Proof.AesOcb.AArch64.nonceR W, Region.Sub r ⟨W, 2560⟩ := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Lay.wSub (by decide)

theorem hashR_W (W : Addr) : ∀ r ∈ VG.Proof.AesOcb.AArch64.hashR W, Region.Sub r ⟨W, 2560⟩ := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact Lay.wSub (by decide)

/-- A buffer apart from `W`, after a frame within `W`. -/
theorem bytesAt_W {W P : Addr} {k : Nat} (hP : (⟨P, k⟩ : Region).Disjoint ⟨W, 2560⟩) (hk : k < 2 ^ 64) {m m' : Mem}
    (h : Frame [⟨W, 2560⟩] m m') : bytesAt m' P k = bytesAt m P k :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hP) (by omega)

theorem ctxCiph_W {K W : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {m m' : Mem} (h : Frame [⟨W, 2560⟩] m m') {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) : ctxCiph m' K R = ctxCiph m K R := by
  unfold ctxCiph
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [VG.Proof.AesOcb.AArch64.bytesAt_W (L.k_w.sub_left (Region.sub_prefix hRb)) (by omega) h]

theorem ctxInv_W {K W : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {m m' : Mem} (h : Frame [⟨W, 2560⟩] m m') {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) : Spec.Ocb.ctxInv m' K R = Spec.Ocb.ctxInv m K R := by
  unfold Spec.Ocb.ctxInv
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [VG.Proof.AesOcb.AArch64.bytesAt_W (L.k_w.sub_left (Region.sub_prefix hRb)) (by omega) h]

theorem ctxLstar_W {K W : Addr} (L : VG.Proof.AesOcb.AArch64.Lay K W) {m m' : Mem} (h : Frame [⟨W, 2560⟩] m m') :
    ctxLstar m' K = ctxLstar m K := by
  show blockAtMem m' (K + BitVec.ofNat 64 240) = blockAtMem m (K + BitVec.ofNat 64 240)
  exact blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_left (Lay.kSub (by decide))

/-- What `tag d` writes, within the parts the pieces write. -/
theorem tagR_mut {W D : Addr} {n d : Nat} (hd : d + 16 ≤ 160) {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩] m m') :
    Frame (VG.Proof.AesOcb.AArch64.mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact VG.Proof.AesOcb.AArch64.in_mutA (by decide)
  · exact VG.Proof.AesOcb.AArch64.in_mutA hd
  · exact VG.Proof.AesOcb.AArch64.in_mutB (by decide) (by decide)

/-- The saved registers, after a frame within the parts the pieces write. -/
theorem saved_mut {K W D : Addr} {n : Nat} (L : VG.Proof.AesOcb.AArch64.Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {g : Reg → BitVec 64} {m m' : Mem} (h : Spill.Saved W g saved m) (hf : Frame (VG.Proof.AesOcb.AArch64.mutR W D n) m m') :
    Spill.Saved W g saved m' :=
  Spill.Saved.frame_in h VG.Proof.AesOcb.AArch64.saved_in hf (VG.Proof.AesOcb.AArch64.kept_mut L hD (by decide))

/-- The first `t ≤ 16` bytes of a block. -/
theorem bytesAt_take_block (m : Mem) (p : Addr) {t : Nat} (h : t ≤ 16) :
    bytesAt m p t = (Spec.Ocb.toBytes (blockAtMem m p)).take t := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = t + (16 - t) by omega,
    Proof.Ocb.bytesAt_append, List.take_left' (length_bytesAt _ _ _)]

/-! ## Before the data -/

/-- What the pieces before the data leave: the offset, the checksum, `L_$`,
`L_0` and `HASH`. -/
structure Pre (K W D : Addr) (R n : Nat) (N A : Addr) (nl al tl : Nat) (s s' : State) : Prop where
  env : VG.Proof.AesOcb.AArch64.Env K W D R n s.sp s'
  frame : Frame [⟨W, 2560⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  slots : VG.Proof.AesOcb.AArch64.Slots W N A nl al tl s'.mem
  saved : Spill.Saved W s.gpr saved s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) =
    Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) =
    Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
  ck : blockAtMem s'.mem (W + BitVec.ofNat 64 ckO) = 0
  ld : blockAtMem s'.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K)
  l0 : blockAtMem s'.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0
  sum : blockAtMem s'.mem (W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al)

/-- What `HASH` needs, after `entry` and `nonce`. -/
theorem hctx_of {s : State} {K W N A D : Addr} {R nl al n tl : Nat} {T : Addr} (Ar : VG.Proof.AesOcb.AArch64.Args s K W N A D R nl al n tl T)
    {s₁ s₂ : State} (P₁ : VG.Proof.AesOcb.AArch64.EntryPost K W D R n N A nl al tl s s₁) {SP : Addr} {o : Block}
    (P₂ : VG.Proof.AesOcb.AArch64.NonceOk K W D R n SP o s₁ s₂) :
    VG.Proof.AesOcb.AArch64.HCtx K W D n R (ctxCiph s.mem K R) (ctxLstar s.mem K) A (bytesAt s.mem A al) s₂ :=
  have L := Ar.lay
  have F₁ : Frame [⟨W, 2560⟩] s.mem s₁.mem := VG.Proof.AesOcb.AArch64.frameW P₁.frame (VG.Proof.AesOcb.AArch64.entryR_W W)
  have F₂ : Frame [⟨W, 2560⟩] s₁.mem s₂.mem := VG.Proof.AesOcb.AArch64.frameW P₂.frame (VG.Proof.AesOcb.AArch64.nonceR_W W)
  { lay := L, rounds := Ar.rounds
    ciph := by rw [VG.Proof.AesOcb.AArch64.ctxCiph_W L F₂ Ar.rounds, VG.Proof.AesOcb.AArch64.ctxCiph_W L F₁ Ar.rounds]
    lstar := by rw [VG.Proof.AesOcb.AArch64.ctxLstar_W L F₂, VG.Proof.AesOcb.AArch64.ctxLstar_W L F₁]
    buf := by rw [length_bytesAt]; exact Ar.aad.of_eq (P₂.rd.trans P₁.rd) (P₂.wr.trans P₁.wr)
    aad := by rw [length_bytesAt, VG.Proof.AesOcb.AArch64.bytesAt_W Ar.aad.w Ar.aad.lt F₂, VG.Proof.AesOcb.AArch64.bytesAt_W Ar.aad.w Ar.aad.lt F₁]
    ad := by rw [length_bytesAt]; exact Ar.ad
    kd := Ar.data.k, dw := Ar.data.w }

/-- `entry`, `nonce` and `hash`. -/
theorem pre_wp' (v : BlocksImpl) {s : State} {K W N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : VG.Proof.AesOcb.AArch64.Args s K W N A D R nl al n tl T) (hW : stackArg s 2 = W)
    (htl : stackArg s 1 = BitVec.ofNat 64 tl)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = N)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 nl) (h4 : s.gpr .x4 = A) (h5 : s.gpr .x5 = BitVec.ofNat 64 al)
    (h6 : s.gpr .x6 = D) (h7 : s.gpr .x7 = BitVec.ofNat 64 n) :
    WP isa (.seq (.block entry) (.seq (nonce (VG.Proof.AesOcb.AArch64.callees v)) (hash (VG.Proof.AesOcb.AArch64.callees v)))) s
      (VG.Proof.AesOcb.AArch64.Pre K W D R n N A nl al tl s) := by
  have L := Ar.lay
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.entry_ok L Ar.perm hW htl Ar.args Ar.argsW h0 h1 h2 h3 h4 h5 h6 h7) fun s₁ P₁ => ?_)
  have F₁ : Frame [⟨W, 2560⟩] s.mem s₁.mem := VG.Proof.AesOcb.AArch64.frameW P₁.frame (VG.Proof.AesOcb.AArch64.entryR_W W)
  -- `Offset_0`.
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.nonce_ok v L P₁.env Ar.rounds P₁.slots.nonce P₁.slots.nlen P₁.slots.tl
    Ar.n1 Ar.n15 (by have := Ar.t16; omega) (Ar.nonce.of_eq P₁.rd P₁.wr) Ar.data.k) fun s₂ P₂ => ?_)
  have F₂ : Frame [⟨W, 2560⟩] s₁.mem s₂.mem := VG.Proof.AesOcb.AArch64.frameW P₂.frame (VG.Proof.AesOcb.AArch64.nonceR_W W)
  have S₂ := Slots.of_mut L Ar.data.w (VG.Proof.AesOcb.AArch64.nonceR_mut (D := D) (n := n) P₂.frame) P₁.slots
  -- `HASH`.
  have C := VG.Proof.AesOcb.AArch64.hctx_of Ar P₁ P₂
  refine WP.mono (VG.Proof.AesOcb.AArch64.hash_ok v C P₂.env S₂.aad (by rw [length_bytesAt]; exact S₂.alen)
    (by rw [P₂.keep (by decide) (by decide), P₁.l0])) fun s₃ ⟨E₃, F₃, sum₃, rd₃, wr₃⟩ => ?_
  have F₃' : Frame [⟨W, 2560⟩] s₂.mem s₃.mem := VG.Proof.AesOcb.AArch64.frameW F₃ (VG.Proof.AesOcb.AArch64.hashR_W W)
  have k₃ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (160 ≤ d ∧ d + 16 ≤ 384)) →
      blockAtMem s₃.mem (W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (W + BitVec.ofNat 64 d) := fun {d} hd =>
    blockAtMem_frame F₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact L.w_w (by omega) (by omega) (by decide)
  refine ⟨E₃, F₁.trans (F₂.trans F₃'), by rw [rd₃, P₂.rd, P₁.rd], by rw [wr₃, P₂.wr, P₁.wr],
    Slots.of_mut L Ar.data.w (VG.Proof.AesOcb.AArch64.hashR_mut F₃) S₂,
    VG.Proof.AesOcb.AArch64.saved_mut L Ar.data.w (VG.Proof.AesOcb.AArch64.saved_mut L Ar.data.w P₁.saved (VG.Proof.AesOcb.AArch64.nonceR_mut P₂.frame)) (VG.Proof.AesOcb.AArch64.hashR_mut F₃), ?_, ?_, ?_, ?_,
    ?_, by rw [sum₃]⟩
  · rw [k₃ (d := ofsO) (by decide), P₂.ofs, VG.Proof.AesOcb.AArch64.ctxCiph_W L F₁ Ar.rounds, VG.Proof.AesOcb.AArch64.bytesAt_W Ar.nonce.w Ar.nonce.lt F₁]
  · rw [k₃ (d := o0O) (by decide), P₂.o0, VG.Proof.AesOcb.AArch64.ctxCiph_W L F₁ Ar.rounds, VG.Proof.AesOcb.AArch64.bytesAt_W Ar.nonce.w Ar.nonce.lt F₁]
  · rw [k₃ (d := ckO) (by decide), P₂.keep (by decide) (by decide), P₁.ck]
  · rw [k₃ (d := ldO) (by decide), P₂.keep (by decide) (by decide), P₁.ld]
  · rw [k₃ (d := l0O) (by decide), P₂.keep (by decide) (by decide), P₁.l0]

/-- `entry`, `nonce` and `hash`, then `k`. -/
theorem pre_wp (v : BlocksImpl) {s : State} {K W N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : VG.Proof.AesOcb.AArch64.Args s K W N A D R nl al n tl T) (hW : stackArg s 2 = W)
    (htl : stackArg s 1 = BitVec.ofNat 64 tl)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = N)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 nl) (h4 : s.gpr .x4 = A) (h5 : s.gpr .x5 = BitVec.ofNat 64 al)
    (h6 : s.gpr .x6 = D) (h7 : s.gpr .x7 = BitVec.ofNat 64 n)
    {k : Prog isa} {Q : State → Prop} (hk : ∀ s', VG.Proof.AesOcb.AArch64.Pre K W D R n N A nl al tl s s' → WP isa k s' Q) :
    WP isa (.seq (.block entry) (.seq (nonce (VG.Proof.AesOcb.AArch64.callees v)) (.seq (hash (VG.Proof.AesOcb.AArch64.callees v)) k))) s Q := by
  exact WP.seq (WP.mono (WP.seq_iff.mp (VG.Proof.AesOcb.AArch64.pre_wp' v Ar hW htl h0 h1 h2 h3 h4 h5 h6 h7)) fun _ h₁ =>
    WP.assoc (WP.seq (WP.mono h₁ hk)))

/-- `body`'s frame misses a block of `W` outside the offset, the checksum and
`[96, 144)`. -/
theorem body_keep {K W D : Addr} {n : Nat} (L : VG.Proof.AesOcb.AArch64.Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {m m' : Mem}
    (h : Frame (VG.Proof.AesOcb.AArch64.bodyR W D n) m m') {d : Nat} (hd : d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (144 ≤ d ∧ d + 16 ≤ 512)) :
    blockAtMem m' (W + BitVec.ofNat 64 d) = blockAtMem m (W + BitVec.ofNat 64 d) :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (by omega) (by omega) (by decide)
    · exact L.w_w (by omega) (by omega) (by decide)
    · exact L.w_w (by omega) (by omega) (by decide)
    · exact (hD.sub_right (Lay.wSub (by omega))).symm

/-- `tag d`'s frame misses the data. -/
theorem tag_data {W D : Addr} {n d : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hd : d + 16 ≤ 512) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 d, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩],
      (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact hD.sub_right (Lay.wSub (by first | omega | (simp only [tmpO]; omega)))

/-- The registers `restore` restores are our caller's. -/
theorem restore_abi {s t t' : State} (h : Spill.Restored s.gpr saved t t') (hsp : t.sp = s.sp) : GprAbi s t' := by
  refine ⟨fun r hr => ?_, by rw [h.sp, hsp]⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ((by decide : ∀ r ∈ preserved, r ∈ saved.map Prod.fst) r hr)
  exact h.gpr p hp

/-- `restore`. -/
theorem restore_wp' {K W D : Addr} {R n : Nat} {SP : Addr} {t : State} (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP t)
    {g : Reg → BitVec 64} (hsv : Spill.Saved W g saved t.mem) :
    WP isa (.block restore) t (Spill.Restored g saved t) := by
  rw [VG.Proof.AesOcb.AArch64.restore_eq]
  exact Spill.restore_wp E.x19 saved_fits.1 (by decide) (fun p hp => E.perm.wR (by have := VG.Proof.AesOcb.AArch64.saved_in p hp; omega))
    hsv

/-- The arguments on the stack, apart from `W` and the data, are kept by a
frame within them. -/
theorem args_kept {W D : Addr} {n : Nat} {SP : Addr} (hW : (⟨SP, 24⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : (⟨SP, 24⟩ : Region).Disjoint ⟨D, n⟩) {m m' : Mem} (h : Frame [⟨W, 2560⟩, ⟨D, n⟩] m m') {i : Nat}
    (hi : i < 3) : m'.readW (SP + BitVec.ofNat 64 (8 * i)) 64 = m.readW (SP + BitVec.ofNat 64 (8 * i)) 64 :=
  h.readW (r := ⟨SP + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hW.sub_left (Offset.sub_base _ (by omega))
    · exact hD.sub_left (Offset.sub_base _ (by omega))) (by decide)

/-- The frame of `front`, from those of its pieces. -/
theorem front_frame {W D : Addr} {n : Nat} {m₀ m₃ m₄ m₅ : Mem} {d : Nat} (hd : d + 16 ≤ 160)
    (P : Frame [⟨W, 2560⟩] m₀ m₃) (B : Frame (VG.Proof.AesOcb.AArch64.bodyR W D n) m₃ m₄)
    (T : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩] m₄ m₅) :
    Frame [⟨W, 2560⟩, ⟨D, n⟩] m₀ m₅ :=
  have M : Frame (VG.Proof.AesOcb.AArch64.mutR W D n) m₃ m₅ := (VG.Proof.AesOcb.AArch64.bodyR_mut B).trans (VG.Proof.AesOcb.AArch64.tagR_mut hd T)
  (P.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans (M.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩)

/-- The first block of `tagOut`: the tag's address from the stack, `W` and
the tag length. -/
theorem tagOutHead_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP s) {T : Addr}
    {tl : Nat} (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) (hT : stackArg s 0 = T)
    (ha : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * 0)) 8) :
    ∃ s₁, runBlock isa [.ldrSp .x11 0, Impl.AesGcm.AArch64.mov .x12 .x19, ld .x13 .x19 tlO] s = some s₁ ∧
      s₁.gpr .x11 = T ∧ s₁.gpr .x12 = W ∧ s₁.gpr .x13 = BitVec.ofNat 64 tl ∧ s₁.mem = s.mem ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
  obtain ⟨_, run₀, rfl⟩ := VG.Proof.AesOcb.AArch64.ldrSp_ok (t := .x11) (s := s) (i := 0) (by decide) ha
  simp only [Nat.reduceMul] at run₀
  have r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 248) 8 := E.perm.wR (by decide)
  have h19 : (s.write .x .x11 (stackArg s 0)).gpr .x19 = W := by simp [gpr_write, E.x19]
  have htl' : s.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl := htl
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [Impl.AesGcm.AArch64.mov .x12 .x19, ld .x13 .x19 tlO] (s.write .x .x11 (stackArg s 0)) = some s₁ ∧
      s₁.gpr .x11 = stackArg s 0 ∧ s₁.gpr .x12 = W ∧ s₁.gpr .x13 = BitVec.ofNat 64 tl ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [E.x19, r₀, htl'], ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write]
    · simp [gpr_write, E.x19]
    · simp [gpr_write, htl']
    · simp only [Proof.AesGcm.AArch64.loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hr.2.1, hr.2.2.1]
    all_goals rfl
  exact ⟨s₁, by rw [show ([.ldrSp .x11 0, Impl.AesGcm.AArch64.mov .x12 .x19, ld .x13 .x19 tlO] : List Instr) =
    [.ldrSp .x11 0] ++ [Impl.AesGcm.AArch64.mov .x12 .x19, ld .x13 .x19 tlO] from rfl, VG.Proof.AesOcb.AArch64.runBlock_append, run₀,
    Option.bind_some, run₁], by rw [x11₁, hT], x12₁, x13₁, m₁, g₁, sp₁, rd₁, wr₁⟩

/-- The first block of `recv`: `W`, the tag's address from the stack and the
tag length. -/
theorem recvHead_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP s) {T : Addr}
    {tl : Nat} (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) (hT : stackArg s 0 = T)
    (ha : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * 0)) 8) :
    ∃ s₁, runBlock isa [Impl.AesGcm.AArch64.mov .x11 .x19, .ldrSp .x12 0, ld .x13 .x19 tlO] s = some s₁ ∧
      s₁.gpr .x11 = W ∧ s₁.gpr .x12 = T ∧ s₁.gpr .x13 = BitVec.ofNat 64 tl ∧ s₁.mem = s.mem ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
  obtain ⟨s₀, run₀, x11₀, g₀, m₀, sp₀, rd₀, wr₀⟩ : ∃ s₀, runBlock isa [Impl.AesGcm.AArch64.mov .x11 .x19] s = some s₀ ∧
      s₀.gpr .x11 = W ∧ (∀ r, r ≠ .x11 → s₀.gpr r = s.gpr r) ∧ s₀.mem = s.mem ∧ s₀.sp = s.sp ∧ s₀.rd = s.rd ∧
      s₀.wr = s.wr := by
    refine ⟨_, by orun [E.x19], ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, E.x19]
    · simp [gpr_write, hr]
    all_goals rfl
  have ha₀ : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 (8 * 0)) 8 := by rw [rd₀, wr₀, sp₀]; exact ha
  obtain ⟨_, run₁, rfl⟩ := VG.Proof.AesOcb.AArch64.ldrSp_ok (t := .x12) (s := s₀) (i := 0) (by decide) ha₀
  simp only [Nat.reduceMul] at run₁
  have hT₀ : stackArg s₀ 0 = T := by rw [← hT]; simp only [stackArg, stackArgAddr, m₀, sp₀]
  have r₀ : InRegions (s₀.rd ++ s₀.wr) (W + BitVec.ofNat 64 248) 8 := by
    rw [rd₀, wr₀]; exact E.perm.wR (by decide)
  have h19 : s₀.gpr .x19 = W := by rw [g₀ .x19 (by decide), E.x19]
  have htl' : s₀.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 tl := by rw [m₀]; exact htl
  obtain ⟨s₁, run₂, x11₁, x12₁, x13₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [ld .x13 .x19 tlO]
      (s₀.write .x .x12 (stackArg s₀ 0)) = some s₁ ∧
      s₁.gpr .x11 = W ∧ s₁.gpr .x12 = T ∧ s₁.gpr .x13 = BitVec.ofNat 64 tl ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [h19, r₀, htl'], ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, x11₀]
    · simp [gpr_write, hT₀]
    · simp [gpr_write, h19, htl']
    · simp only [Proof.AesGcm.AArch64.loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, g₀ r hr.1]
    · simp [mem_write, m₀]
    · simp [sp_write, sp₀]
    · simp [rd_write, rd₀]
    · simp [wr_write, wr₀]
  exact ⟨s₁, by rw [show ([Impl.AesGcm.AArch64.mov .x11 .x19, .ldrSp .x12 0, ld .x13 .x19 tlO] : List Instr) =
    [Impl.AesGcm.AArch64.mov .x11 .x19] ++ ([.ldrSp .x12 0] ++ [ld .x13 .x19 tlO]) from rfl, VG.Proof.AesOcb.AArch64.runBlock_append,
    run₀, Option.bind_some, VG.Proof.AesOcb.AArch64.runBlock_append, run₁, Option.bind_some, run₂], x11₁, x12₁, x13₁, m₁, g₁, sp₁, rd₁,
    wr₁⟩

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag at `T`, which the
state may write. -/
theorem tagOut_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP s) {T : Addr}
    {tl : Nat} (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (hT : stackArg s 0 = T) (ha : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * 0)) 8)
    (hTw : Covers [⟨T, tl⟩] s.wr) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa tagOut s fun t => t.mem = writeBytes s.mem T (bytesAt s.mem W tl) ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.AArch64.tagOutHead_ok E htl hT ha
  unfold tagOut
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (Proof.AesGcm.AArch64.copyLoop_ok s₁ x12₁ x11₁ x13₁ (by omega)
    ⟨by omega, by
      rw [rd₁, wr₁]
      exact covers_left fun a m ⟨r, hr, hc⟩ => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.perm.w a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩,
      by rw [wr₁]; exact hTw,
      (hTW.sub_right (Region.sub_prefix (by omega))).symm⟩)
    fun t ⟨m, _, _, g, sp, rd, wr⟩ => ⟨by rw [m, m₁], fun r hr => by rw [g r hr, g₁ r hr], by rw [sp, sp₁],
      by rw [rd, rd₁], by rw [wr, wr₁]⟩

/-- `vg_aes_ocb_seal`, for its arguments. -/
theorem seal_wp' (v : BlocksImpl) {s : State} {K W N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : VG.Proof.AesOcb.AArch64.Args s K W N A D R nl al n tl T) (hTw : Covers [⟨T, tl⟩] s.wr) (hW : stackArg s 2 = W)
    (hT : stackArg s 0 = T) (htl : stackArg s 1 = BitVec.ofNat 64 tl)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = N)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 nl) (h4 : s.gpr .x4 = A) (h5 : s.gpr .x5 = BitVec.ofNat 64 al)
    (h6 : s.gpr .x6 = D) (h7 : s.gpr .x7 = BitVec.ofNat 64 n) :
    WP isa («seal» (VG.Proof.AesOcb.AArch64.callees v)) s fun s' => GprAbi s s' ∧
      Spec.Ocb.encryptWith (ctxCiph s.mem K R) (ctxLstar s.mem K) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
        (bytesAt s.mem D n) = (bytesAt s'.mem D n, bytesAt s'.mem T tl) := by
  have L := Ar.lay
  unfold «seal» front
  refine WP.seq (VG.Proof.AesOcb.AArch64.pre_wp v Ar hW htl h0 h1 h2 h3 h4 h5 h6 h7 fun s₃ P₃ => ?_)
  have hD₃ : VG.Proof.AesOcb.AArch64.DBuf K W s₃ D n := Ar.data.of_eq P₃.rd P₃.wr
  have c₃ : ctxCiph s₃.mem K R = ctxCiph s.mem K R := VG.Proof.AesOcb.AArch64.ctxCiph_W L P₃.frame Ar.rounds
  have l₃ : ctxLstar s₃.mem K = ctxLstar s.mem K := VG.Proof.AesOcb.AArch64.ctxLstar_W L P₃.frame
  have d₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := VG.Proof.AesOcb.AArch64.bytesAt_W Ar.data.w Ar.data.lt P₃.frame
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.bodySeal_ok v L P₃.env Ar.rounds hD₃ P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, l₃]))
    fun s₄ B => ?_)
  have F₄ : Frame (VG.Proof.AesOcb.AArch64.mutR W D n) s₃.mem s₄.mem := VG.Proof.AesOcb.AArch64.bodyR_mut B.frame
  have cK₄ : ctxCiph s₄.mem K R = ctxCiph s.mem K R := (VG.Proof.AesOcb.AArch64.ctxCiph_mut L Ar.data.k F₄ Ar.rounds).trans c₃
  have ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K) := by
    rw [VG.Proof.AesOcb.AArch64.body_keep L Ar.data.w B.frame (d := ldO) (by decide), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al) := by
    rw [VG.Proof.AesOcb.AArch64.body_keep L Ar.data.w B.frame (d := sumO) (by decide), P₃.sum]
  -- The tag.
  refine WP.mono (VG.Proof.AesOcb.AArch64.tag_ok v L B.env Ar.rounds (.inl rfl)) fun s₅ T₅ => ?_
  have F₅ : Frame (VG.Proof.AesOcb.AArch64.mutR W D n) s₄.mem s₅.mem := VG.Proof.AesOcb.AArch64.tagR_mut (by decide) T₅.frame
  have S₅ := Slots.of_mut L Ar.data.w (F₄.trans F₅) P₃.slots
  have sv₅ := VG.Proof.AesOcb.AArch64.saved_mut L Ar.data.w (VG.Proof.AesOcb.AArch64.saved_mut L Ar.data.w P₃.saved F₄) F₅
  have Ff := VG.Proof.AesOcb.AArch64.front_frame (by decide) P₃.frame B.frame T₅.frame
  have sp₅ : s₅.sp = s.sp := T₅.env.sp
  -- The copy of the tag.
  have hT₅ : stackArg s₅ 0 = T := by
    rw [← hT]; simp only [stackArg, stackArgAddr, sp₅]
    exact VG.Proof.AesOcb.AArch64.args_kept Ar.argsW Ar.argsD Ff (i := 0) (by decide)
  have ha₅ : InRegions (s₅.rd ++ s₅.wr) (s₅.sp + BitVec.ofNat 64 (8 * 0)) 8 := by
    rw [T₅.rd, B.rd, P₃.rd, T₅.wr, B.wr, P₃.wr, sp₅]
    exact Proof.AesGcm.AArch64.in_off Ar.args (by decide) (by decide)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.tagOut_ok T₅.env Ar.t1 Ar.t16 S₅.tl hT₅ ha₅
    (by rw [T₅.wr, B.wr, P₃.wr]; exact hTw) Ar.tag.w) fun s₆ ⟨m₆, g₆, sp₆, rd₆, wr₆⟩ => ?_)
  have E₆ := T₅.env.others g₆ sp₆ rd₆ wr₆
  have F₆ : Frame [⟨T, tl⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  have sv₆ : Spill.Saved W s.gpr saved s₆.mem :=
    Spill.Saved.frame_in sv₅ VG.Proof.AesOcb.AArch64.saved_in F₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Ar.tag.w.sub_right (Lay.wSub (by decide))).symm
  -- `restore`.
  refine WP.mono (VG.Proof.AesOcb.AArch64.restore_wp' E₆ sv₆) fun s₇ Rs => ⟨VG.Proof.AesOcb.AArch64.restore_abi Rs E₆.sp, ?_⟩
  have hout := B.out
  rw [c₃, l₃, d₃] at hout
  have hofs := B.ofs
  rw [l₃] at hofs
  have hck := B.ck
  rw [d₃] at hck
  have hn := Ar.data.lt
  have ht := Ar.tag.lt
  have d₇ : bytesAt s₇.mem D n = bytesAt s₄.mem D n := by
    rw [Rs.mem, Proof.Cmac.bytesAt_frame F₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.td.symm) (by omega)]
    exact Proof.Cmac.bytesAt_frame T₅.frame (VG.Proof.AesOcb.AArch64.tag_data Ar.data.w (by decide)) (by omega)
  have tv := T₅.val
  rw [show W + BitVec.ofNat 64 tagO = W from BitVec.add_zero W] at tv
  have t₇ : bytesAt s₇.mem T tl = (Spec.Ocb.toBytes (blockAtMem s₅.mem W)).take tl := by
    rw [Rs.mem, m₆, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]) ht, length_bytesAt,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, VG.Proof.AesOcb.AArch64.bytesAt_take_block _ _ Ar.t16]
  rw [Proof.Ocb.encryptWith_eq, d₇, hout, t₇, tv, hck, hofs, ld₄, sum₄, cK₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < n % 16
  · have h' : n - 16 * (n / 16) > 0 := by omega
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega
    simp only [h', hr, ↓reduceIte]

/-- `vg_aes_ocb_seal`. -/
theorem seal_wp (v : BlocksImpl) {s : State} (h : sealAArch64.pre s) :
    WP isa («seal» (VG.Proof.AesOcb.AArch64.callees v)) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' :=
  VG.Proof.AesOcb.AArch64.seal_wp' v (VG.Proof.AesOcb.AArch64.sealArgs_of h) (covers_of_mem (by rw [h.2.1]; simp)) rfl rfl (VG.Proof.AesOcb.AArch64.ofNat_toNat64 _).symm rfl
    (VG.Proof.AesOcb.AArch64.ofNat_toNat64 _).symm rfl (VG.Proof.AesOcb.AArch64.ofNat_toNat64 _).symm rfl (VG.Proof.AesOcb.AArch64.ofNat_toNat64 _).symm rfl (VG.Proof.AesOcb.AArch64.ofNat_toNat64 _).symm

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.SealCT`. -/
section

/-!
# AES-OCB on AArch64: `vg_aes_ocb_seal` is constant time

Untrusted: everything here is checked by Lean. The entry loads `work` from
the stack, which the taint analysis takes as secret (it reads memory): the
block is split after the load, and the rest runs from `x9`, which holds
`work` (public) in both runs (`entry_rel`). Then `nonce_rel`, `hash_rel`
(`pre_rel`), `bodySeal_rel`, `tag_rel`, the copy of the tag, whose first
block loads the tag's address from the stack and is split there
(`tagOut_rel`), and `restore`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph ctxLstar)
open VG.Proof.Ocb (length_bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint ct_of in_off RelCT.block_split)

/-- The entry of `seal` and `open`, in two runs. -/
theorem entry_rel {σ₁ σ₂ : State} {W : Addr} (hW₁ : stackArg σ₁ 2 = W) (hW₂ : stackArg σ₂ 2 = W)
    (hargs₁ : Covers [⟨σ₁.sp, 24⟩] (σ₁.rd ++ σ₁.wr)) (hargs₂ : Covers [⟨σ₂.sp, 24⟩] (σ₂.rd ++ σ₂.wr))
    (qsp : σ₁.sp = σ₂.sp) (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  obtain ⟨_, run₁, rfl⟩ := VG.Proof.AesOcb.AArch64.ldrSp_ok (t := .x9) (s := σ₁) (i := 2) (by decide) (in_off hargs₁ (by decide) (by decide))
  obtain ⟨_, run₂, rfl⟩ := VG.Proof.AesOcb.AArch64.ldrSp_ok (t := .x9) (s := σ₂) (i := 2) (by decide) (in_off hargs₂ (by decide) (by decide))
  simp only [Nat.reduceMul] at run₁ run₂
  rw [entry]
  simp only [List.append_assoc]
  refine RelCT.block_split (rel_seq (rel_taint [] qsp (by agree_tac []) ⟨_, by taint_decide⟩)
    (WP.of_runBlock ⟨_, run₁, rfl⟩) (WP.of_runBlock ⟨_, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_)
  subst h₁ h₂
  refine rel_taint [.x9, .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] (by simp only [sp_write]; exact qsp) ?_
    ⟨_, by taint_decide⟩
  intro r hr
  by_cases h9 : r = .x9
  · subst h9; simp [gpr_write, hW₁, hW₂]
  · simp only [gpr_write, h9, ite_false]
    exact hq r (by simp only [List.mem_cons, List.not_mem_nil, or_false, h9, false_or] at hr ⊢; exact hr)

/-- `entry`, `nonce` and `hash`, in two runs with the same public arguments. -/
theorem pre_rel (v : BlocksImpl) {σ₁ σ₂ : State} {K W N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (A₁ : VG.Proof.AesOcb.AArch64.Args σ₁ K W N A D R nl al n tl T) (A₂ : VG.Proof.AesOcb.AArch64.Args σ₂ K W N A D R nl al n tl T)
    (hW₁ : stackArg σ₁ 2 = W) (htl₁ : stackArg σ₁ 1 = BitVec.ofNat 64 tl)
    (h0₁ : σ₁.gpr .x0 = K) (h1₁ : σ₁.gpr .x1 = BitVec.ofNat 64 R) (h2₁ : σ₁.gpr .x2 = N)
    (h3₁ : σ₁.gpr .x3 = BitVec.ofNat 64 nl) (h4₁ : σ₁.gpr .x4 = A) (h5₁ : σ₁.gpr .x5 = BitVec.ofNat 64 al)
    (h6₁ : σ₁.gpr .x6 = D) (h7₁ : σ₁.gpr .x7 = BitVec.ofNat 64 n)
    (hW₂ : stackArg σ₂ 2 = W) (htl₂ : stackArg σ₂ 1 = BitVec.ofNat 64 tl)
    (h0₂ : σ₂.gpr .x0 = K) (h1₂ : σ₂.gpr .x1 = BitVec.ofNat 64 R) (h2₂ : σ₂.gpr .x2 = N)
    (h3₂ : σ₂.gpr .x3 = BitVec.ofNat 64 nl) (h4₂ : σ₂.gpr .x4 = A) (h5₂ : σ₂.gpr .x5 = BitVec.ofNat 64 al)
    (h6₂ : σ₂.gpr .x6 = D) (h7₂ : σ₂.gpr .x7 = BitVec.ofNat 64 n) (qsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block entry) (.seq (nonce (VG.Proof.AesOcb.AArch64.callees v)) (hash (VG.Proof.AesOcb.AArch64.callees v)))) TT := by
  have L := A₁.lay
  refine rel_seq (VG.Proof.AesOcb.AArch64.entry_rel hW₁ hW₂ A₁.args A₂.args qsp
      (by agree_tac [h0₁, h0₂, h1₁, h1₂, h2₁, h2₂, h3₁, h3₂, h4₁, h4₂, h5₁, h5₂, h6₁, h6₂, h7₁, h7₂]))
    (VG.Proof.AesOcb.AArch64.entry_ok L A₁.perm hW₁ htl₁ A₁.args A₁.argsW h0₁ h1₁ h2₁ h3₁ h4₁ h5₁ h6₁ h7₁)
    (VG.Proof.AesOcb.AArch64.entry_ok L A₂.perm hW₂ htl₂ A₂.args A₂.argsW h0₂ h1₂ h2₂ h3₂ h4₂ h5₂ h6₂ h7₂) fun s₁ s₂ P₁ P₂ => ?_
  have E₂ := P₂.env
  rw [← qsp] at E₂
  have ht : tl < 2 ^ 64 := by have := A₁.t16; omega
  refine rel_seq (VG.Proof.AesOcb.AArch64.nonce_rel v L P₁.env E₂ A₁.rounds P₁.slots.nonce P₂.slots.nonce P₁.slots.nlen P₂.slots.nlen
      P₁.slots.tl P₂.slots.tl A₁.n1 A₁.n15 ht (A₁.nonce.of_eq P₁.rd P₁.wr) (A₂.nonce.of_eq P₂.rd P₂.wr))
    (VG.Proof.AesOcb.AArch64.nonce_ok v L P₁.env A₁.rounds P₁.slots.nonce P₁.slots.nlen P₁.slots.tl A₁.n1 A₁.n15 ht
      (A₁.nonce.of_eq P₁.rd P₁.wr) A₁.data.k)
    (VG.Proof.AesOcb.AArch64.nonce_ok v L E₂ A₁.rounds P₂.slots.nonce P₂.slots.nlen P₂.slots.tl A₁.n1 A₁.n15 ht
      (A₂.nonce.of_eq P₂.rd P₂.wr) A₁.data.k) fun t₁ t₂ Q₁ Q₂ => ?_
  have S₁ := Slots.of_mut L A₁.data.w (VG.Proof.AesOcb.AArch64.nonceR_mut Q₁.frame) P₁.slots
  have S₂ := Slots.of_mut L A₁.data.w (VG.Proof.AesOcb.AArch64.nonceR_mut Q₂.frame) P₂.slots
  exact VG.Proof.AesOcb.AArch64.hash_rel v (VG.Proof.AesOcb.AArch64.hctx_of A₁ P₁ Q₁) (VG.Proof.AesOcb.AArch64.hctx_of A₂ P₂ Q₂) (by rw [length_bytesAt, length_bytesAt]) Q₁.env Q₂.env
    S₁.aad S₂.aad (by rw [length_bytesAt]; exact S₁.alen) (by rw [length_bytesAt]; exact S₂.alen)
    (by rw [Q₁.keep (by decide) (by decide), P₁.l0]) (by rw [Q₂.keep (by decide) (by decide), P₂.l0])

/-- `Args` in two runs with the same public arguments, with the values of the
first. -/
theorem args₂_of {σ₁ σ₂ : State} (hq : VG.Proof.AesOcb.AArch64.onePub σ₁ σ₂)
    (A₂ : VG.Proof.AesOcb.AArch64.Args σ₂ (σ₂.gpr .x0) (stackArg σ₂ 2) (σ₂.gpr .x2) (σ₂.gpr .x4) (σ₂.gpr .x6) (σ₂.gpr .x1).toNat
      (σ₂.gpr .x3).toNat (σ₂.gpr .x5).toNat (σ₂.gpr .x7).toNat (stackArg σ₂ 1).toNat (stackArg σ₂ 0)) :
    VG.Proof.AesOcb.AArch64.Args σ₂ (σ₁.gpr .x0) (stackArg σ₁ 2) (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat
      (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0) := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, -, qa⟩ := hq
  rw [← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qa 0 (by decide), ← qa 1 (by decide),
    ← qa 2 (by decide)] at A₂
  exact A₂

/-- `pre_rel` and `pre_wp'` in two runs with the same public arguments, then
`k`. -/
theorem pre_relk (v : BlocksImpl) {σ₁ σ₂ : State}
    (A₁ : VG.Proof.AesOcb.AArch64.Args σ₁ (σ₁.gpr .x0) (stackArg σ₁ 2) (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat
      (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0))
    (A₂ : VG.Proof.AesOcb.AArch64.Args σ₂ (σ₁.gpr .x0) (stackArg σ₁ 2) (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat
      (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0))
    (hq : VG.Proof.AesOcb.AArch64.onePub σ₁ σ₂) {k : Prog isa}
    (hk : ∀ τ₁ τ₂, VG.Proof.AesOcb.AArch64.Pre (σ₁.gpr .x0) (stackArg σ₁ 2) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat (σ₁.gpr .x7).toNat (σ₁.gpr .x2)
      (σ₁.gpr .x4) (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (stackArg σ₁ 1).toNat σ₁ τ₁ →
      VG.Proof.AesOcb.AArch64.Pre (σ₁.gpr .x0) (stackArg σ₁ 2) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat (σ₁.gpr .x7).toNat (σ₁.gpr .x2)
      (σ₁.gpr .x4) (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (stackArg σ₁ 1).toNat σ₂ τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) k TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block entry) (.seq (nonce (VG.Proof.AesOcb.AArch64.callees v)) (.seq (hash (VG.Proof.AesOcb.AArch64.callees v)) k))) TT := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have o : ∀ x : BitVec 64, x = BitVec.ofNat 64 x.toNat := fun x => (VG.Proof.AesOcb.AArch64.ofNat_toNat64 x).symm
  have o' : ∀ {x y : BitVec 64}, x = y → y = BitVec.ofNat 64 x.toNat := fun h => by rw [h]; exact o _
  refine RelCT.assoc_in (RelCT.assoc (rel_seq (VG.Proof.AesOcb.AArch64.pre_rel v A₁ A₂ rfl (o _) rfl (o _) rfl (o _) rfl (o _) rfl (o _)
      (qa 2 (by decide)).symm (o' (qa 1 (by decide))) q0.symm (o' q1) q2.symm (o' q3) q4.symm (o' q5) q6.symm
      (o' q7) qsp)
    (VG.Proof.AesOcb.AArch64.pre_wp' v A₁ rfl (o _) rfl (o _) rfl (o _) rfl (o _) rfl (o _))
    (VG.Proof.AesOcb.AArch64.pre_wp' v A₂ (qa 2 (by decide)).symm (o' (qa 1 (by decide))) q0.symm (o' q1) q2.symm (o' q3) q4.symm (o' q5)
      q6.symm (o' q7)) hk))

/-- Two runs of `front; tail` are two runs of `front`'s pieces, then `tail`. -/
theorem rel_front {P Q : State → State → Prop} {e n h b t tail : Prog isa}
    (hr : RelCT isa P (.seq e (.seq n (.seq h (.seq b (.seq t tail))))) Q) :
    RelCT isa P (.seq (.seq e (.seq n (.seq h (.seq b t)))) tail) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq f₁ r₁ => cases f₁ with | seq a₁ f₁ => cases f₁ with | seq b₁ f₁ =>
  cases f₁ with | seq c₁ f₁ => cases f₁ with | seq d₁ g₁ =>
  cases e₂ with | seq f₂ r₂ => cases f₂ with | seq a₂ f₂ => cases f₂ with | seq b₂ f₂ =>
  cases f₂ with | seq c₂ f₂ => cases f₂ with | seq d₂ g₂ =>
  obtain ⟨ht, hq⟩ := hr _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ (.seq g₁ r₁)))))
    (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ (.seq g₂ r₂)))))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- `tagOut` in two runs: its first block loads the tag's address from the
stack, and the copy runs from it. -/
theorem tagOut_rel {K W D : Addr} {R n : Nat} {SP : Addr} {σ₁ σ₂ : State} (E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₁)
    (E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₂) {T : Addr} {tl : Nat}
    (htl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (htl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) (hT₁ : stackArg σ₁ 0 = T)
    (hT₂ : stackArg σ₂ 0 = T) (ha₁ : InRegions (σ₁.rd ++ σ₁.wr) (σ₁.sp + BitVec.ofNat 64 (8 * 0)) 8)
    (ha₂ : InRegions (σ₂.rd ++ σ₂.wr) (σ₂.sp + BitVec.ofNat 64 (8 * 0)) 8) : RelCT isa (Eq2 σ₁ σ₂) tagOut TT := by
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, -, g₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.AArch64.tagOutHead_ok E₁ htl₁ hT₁ ha₁
  obtain ⟨s₂, run₂, x11₂, x12₂, x13₂, -, g₂, sp₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.AArch64.tagOutHead_ok E₂ htl₂ hT₂ ha₂
  unfold tagOut
  refine rel_seq (VG.Proof.AesOcb.AArch64.rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (WP.of_runBlock ⟨s₁, run₁, rfl⟩)
    (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_
  subst h₁ h₂
  exact VG.Proof.AesOcb.AArch64.rel_env (E₁.others g₁ sp₁ rd₁ wr₁) (E₂.others g₂ sp₂ rd₂ wr₂) [.x11, .x12, .x13]
    (by agree_tac [x11₁, x11₂, x12₁, x12₂, x13₁, x13₂]) ⟨_, by taint_decide⟩

/-- The state after `front`, in a run with the arguments: the address of the
tag on the stack, where the state may read it. -/
theorem front_tag {s : State} {K W N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : VG.Proof.AesOcb.AArch64.Args s K W N A D R nl al n tl T) (hT : stackArg s 0 = T) {s₃ s₄ s₅ : State} {d : Nat} (hd : d + 16 ≤ 160)
    (P : VG.Proof.AesOcb.AArch64.Pre K W D R n N A nl al tl s s₃) {out : List Byte} {ofs ck : Spec.Ocb.Block}
    {SP SP' : Addr} (B : VG.Proof.AesOcb.AArch64.BodyPost K W D R n SP' out ofs ck s₃ s₄) (T₅ : VG.Proof.AesOcb.AArch64.TagPost K W D R n SP d s₄ s₅)
    (hsp : SP = s.sp) :
    stackArg s₅ 0 = T ∧ InRegions (s₅.rd ++ s₅.wr) (s₅.sp + BitVec.ofNat 64 (8 * 0)) 8 := by
  have sp₅ : s₅.sp = s.sp := T₅.env.sp.trans hsp
  refine ⟨?_, ?_⟩
  · rw [← hT]; simp only [stackArg, stackArgAddr, sp₅]
    exact VG.Proof.AesOcb.AArch64.args_kept Ar.argsW Ar.argsD (VG.Proof.AesOcb.AArch64.front_frame hd P.frame B.frame T₅.frame) (i := 0) (by decide)
  · rw [T₅.rd, B.rd, P.rd, T₅.wr, B.wr, P.wr, sp₅]
    exact in_off Ar.args (by decide) (by decide)

theorem seal_ct (v : BlocksImpl) : ConstantTime isa sealAArch64.pre sealAArch64.pub («seal» (VG.Proof.AesOcb.AArch64.callees v)) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have A₁ := VG.Proof.AesOcb.AArch64.sealArgs_of h₁
  have A₂ := VG.Proof.AesOcb.AArch64.args₂_of hq (VG.Proof.AesOcb.AArch64.sealArgs_of h₂)
  have qsp := hq.2.2.2.2.2.2.2.2.1
  have qT : stackArg σ₂ 0 = stackArg σ₁ 0 := (hq.2.2.2.2.2.2.2.2.2 0 (by decide)).symm
  have L := A₁.lay
  unfold «seal» front
  refine VG.Proof.AesOcb.AArch64.rel_front (VG.Proof.AesOcb.AArch64.pre_relk v A₁ A₂ hq fun τ₁ τ₂ P₁ P₂ => ?_)
  have E₂ := P₂.env
  rw [← qsp] at E₂
  refine rel_seq (VG.Proof.AesOcb.AArch64.bodySeal_rel L A₁.rounds v P₁.env E₂ (A₁.data.of_eq P₁.rd P₁.wr) (A₂.data.of_eq P₂.rd P₂.wr)
      P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, VG.Proof.AesOcb.AArch64.ctxLstar_W L P₁.frame]) P₂.ofs P₂.o0 P₂.ck
      (by rw [P₂.l0, VG.Proof.AesOcb.AArch64.ctxLstar_W L P₂.frame]))
    (VG.Proof.AesOcb.AArch64.bodySeal_ok v L P₁.env A₁.rounds (A₁.data.of_eq P₁.rd P₁.wr) P₁.ofs P₁.o0 P₁.ck
      (by rw [P₁.l0, VG.Proof.AesOcb.AArch64.ctxLstar_W L P₁.frame]))
    (VG.Proof.AesOcb.AArch64.bodySeal_ok v L E₂ A₁.rounds (A₂.data.of_eq P₂.rd P₂.wr) P₂.ofs P₂.o0 P₂.ck
      (by rw [P₂.l0, VG.Proof.AesOcb.AArch64.ctxLstar_W L P₂.frame])) fun u₁ u₂ B₁ B₂ => ?_
  refine rel_seq (VG.Proof.AesOcb.AArch64.tag_rel L A₁.rounds v B₁.env B₂.env (.inl rfl)) (VG.Proof.AesOcb.AArch64.tag_ok v L B₁.env A₁.rounds (.inl rfl))
    (VG.Proof.AesOcb.AArch64.tag_ok v L B₂.env A₁.rounds (.inl rfl)) fun w₁ w₂ T₁ T₂ => ?_
  have S₁ := Slots.of_mut L A₁.data.w ((VG.Proof.AesOcb.AArch64.bodyR_mut B₁.frame).trans (VG.Proof.AesOcb.AArch64.tagR_mut (by decide) T₁.frame)) P₁.slots
  have S₂ := Slots.of_mut L A₁.data.w ((VG.Proof.AesOcb.AArch64.bodyR_mut B₂.frame).trans (VG.Proof.AesOcb.AArch64.tagR_mut (by decide) T₂.frame)) P₂.slots
  obtain ⟨t₁, a₁⟩ := VG.Proof.AesOcb.AArch64.front_tag A₁ rfl (by decide) P₁ B₁ T₁ rfl
  obtain ⟨t₂, a₂⟩ := VG.Proof.AesOcb.AArch64.front_tag A₂ qT (by decide) P₂ B₂ T₂ qsp
  refine rel_seq (VG.Proof.AesOcb.AArch64.tagOut_rel T₁.env T₂.env S₁.tl S₂.tl t₁ t₂ a₁ a₂)
    (VG.Proof.AesOcb.AArch64.tagOut_ok T₁.env A₁.t1 A₁.t16 S₁.tl t₁ a₁ (by
      rw [T₁.wr, B₁.wr, P₁.wr, h₁.2.1]; exact Proof.AesGcm.AArch64.covers_of_mem (by simp)) A₁.tag.w)
    (VG.Proof.AesOcb.AArch64.tagOut_ok T₂.env A₁.t1 A₁.t16 S₂.tl t₂ a₂ (by
      rw [T₂.wr, B₂.wr, P₂.wr, h₂.2.1, ← qT, hq.2.2.2.2.2.2.2.2.2 1 (by decide)]
      exact Proof.AesGcm.AArch64.covers_of_mem (by simp)) A₂.tag.w)
    fun y₁ y₂ ⟨_, g₁, sp₁, rd₁, wr₁⟩ ⟨_, g₂, sp₂, rd₂, wr₂⟩ => ?_
  exact VG.Proof.AesOcb.AArch64.rel_env (T₁.env.others g₁ sp₁ rd₁ wr₁) (T₂.env.others g₂ sp₂ rd₂ wr₂) [] (by agree_tac [])
    ⟨_, by taint_decide⟩

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Open`. -/
section

/-!
# AES-OCB on AArch64: `vg_aes_ocb_open`

Untrusted: everything here is checked by Lean. `open` is `front`: `entry`,
`Offset_0` (`nonce`), `HASH` (`hash`), the data (`body`) and the tag at
`W + t2O` (`tag`); then the copy of the received tag from `tag`, whose
address is on the stack, to `W` (`recv`), its comparison with the computed
tag (`cmp`), the mask of the data (`mask`), the result and `restore`
(`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar pad zeros)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- `recv`: the `tl` bytes of the tag at `T` copied to `W`. -/
theorem recv_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : VG.Proof.AesOcb.AArch64.Env K W D R n SP s) {T : Addr}
    {tl : Nat} (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (hT : stackArg s 0 = T) (ha : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * 0)) 8)
    (hTr : Covers [⟨T, tl⟩] (s.rd ++ s.wr)) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa recv s fun t => t.mem = writeBytes s.mem W (bytesAt s.mem T tl) ∧
      (∀ r, r ∉ Proof.AesGcm.AArch64.loopRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.AArch64.recvHead_ok E htl hT ha
  unfold recv
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (Proof.AesGcm.AArch64.copyLoop_ok s₁ x12₁ x11₁ x13₁ (by omega)
    ⟨by omega, by rw [rd₁, wr₁]; exact hTr, by
      rw [wr₁]
      exact fun a m ⟨r, hr, hc⟩ => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.perm.w a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩,
      hTW.sub_right (Region.sub_prefix (by omega))⟩)
    fun t ⟨m, _, _, g, sp, rd, wr⟩ => ⟨by rw [m, m₁], fun r hr => by rw [g r hr, g₁ r hr], by rw [sp, sp₁],
      by rw [rd, rd₁], by rw [wr, wr₁]⟩

/-- `vg_aes_ocb_open`, for its arguments. -/
theorem open_wp' (v : BlocksImpl) {s : State} {K W N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : VG.Proof.AesOcb.AArch64.Args s K W N A D R nl al n tl T) (hW : stackArg s 2 = W) (hT : stackArg s 0 = T)
    (htl : stackArg s 1 = BitVec.ofNat 64 tl)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = N)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 nl) (h4 : s.gpr .x4 = A) (h5 : s.gpr .x5 = BitVec.ofNat 64 al)
    (h6 : s.gpr .x6 = D) (h7 : s.gpr .x7 = BitVec.ofNat 64 n) :
    WP isa («open» (VG.Proof.AesOcb.AArch64.callees v)) s fun s' => GprAbi s s' ∧
      match Spec.Ocb.decryptWith (ctxCiph s.mem K R) (Spec.Ocb.ctxInv s.mem K R) (ctxLstar s.mem K) tl
          (bytesAt s.mem N nl) (bytesAt s.mem A al) (bytesAt s.mem D n) (bytesAt s.mem T tl) with
      | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
      | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n := by
  have L := Ar.lay
  have hn := Ar.data.lt
  unfold «open» front
  refine WP.seq (VG.Proof.AesOcb.AArch64.pre_wp v Ar hW htl h0 h1 h2 h3 h4 h5 h6 h7 fun s₃ P₃ => ?_)
  have hD₃ : VG.Proof.AesOcb.AArch64.DBuf K W s₃ D n := Ar.data.of_eq P₃.rd P₃.wr
  have c₃ : ctxCiph s₃.mem K R = ctxCiph s.mem K R := VG.Proof.AesOcb.AArch64.ctxCiph_W L P₃.frame Ar.rounds
  have i₃ : Spec.Ocb.ctxInv s₃.mem K R = Spec.Ocb.ctxInv s.mem K R := VG.Proof.AesOcb.AArch64.ctxInv_W L P₃.frame Ar.rounds
  have l₃ : ctxLstar s₃.mem K = ctxLstar s.mem K := VG.Proof.AesOcb.AArch64.ctxLstar_W L P₃.frame
  have d₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := VG.Proof.AesOcb.AArch64.bytesAt_W Ar.data.w hn P₃.frame
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.bodyOpen_ok v L P₃.env Ar.rounds hD₃ P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, l₃]))
    fun s₄ B => ?_)
  have F₄ : Frame (VG.Proof.AesOcb.AArch64.mutR W D n) s₃.mem s₄.mem := VG.Proof.AesOcb.AArch64.bodyR_mut B.frame
  have cK₄ : ctxCiph s₄.mem K R = ctxCiph s.mem K R := (VG.Proof.AesOcb.AArch64.ctxCiph_mut L Ar.data.k F₄ Ar.rounds).trans c₃
  have ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K) := by
    rw [VG.Proof.AesOcb.AArch64.body_keep L Ar.data.w B.frame (d := ldO) (by decide), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al) := by
    rw [VG.Proof.AesOcb.AArch64.body_keep L Ar.data.w B.frame (d := sumO) (by decide), P₃.sum]
  -- The tag, at `W + t2O`.
  refine WP.mono (VG.Proof.AesOcb.AArch64.tag_ok v L B.env Ar.rounds (.inr rfl)) fun s₅ T₅ => ?_
  have F₅ : Frame (VG.Proof.AesOcb.AArch64.mutR W D n) s₄.mem s₅.mem := VG.Proof.AesOcb.AArch64.tagR_mut (by decide) T₅.frame
  have S₅ := Slots.of_mut L Ar.data.w (F₄.trans F₅) P₃.slots
  have Ff := VG.Proof.AesOcb.AArch64.front_frame (by decide) P₃.frame B.frame T₅.frame
  have sp₅ : s₅.sp = s.sp := T₅.env.sp
  -- The received tag, to `W`.
  have hT₅ : stackArg s₅ 0 = T := by
    rw [← hT]; simp only [stackArg, stackArgAddr, sp₅]
    exact VG.Proof.AesOcb.AArch64.args_kept Ar.argsW Ar.argsD Ff (i := 0) (by decide)
  have ha₅ : InRegions (s₅.rd ++ s₅.wr) (s₅.sp + BitVec.ofNat 64 (8 * 0)) 8 := by
    rw [T₅.rd, B.rd, P₃.rd, T₅.wr, B.wr, P₃.wr, sp₅]
    exact Proof.AesGcm.AArch64.in_off Ar.args (by decide) (by decide)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.recv_ok T₅.env Ar.t1 Ar.t16 S₅.tl hT₅ ha₅
    (by rw [T₅.rd, B.rd, P₃.rd, T₅.wr, B.wr, P₃.wr]; exact Ar.tag.rd) Ar.tag.w)
    fun s₅' ⟨mr, gr, spr, rdr, wrr⟩ => ?_)
  have E₅' := T₅.env.others gr spr rdr wrr
  have Fr : Frame [⟨W, tl⟩] s₅.mem s₅'.mem := by
    rw [mr]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  have Fr' : Frame (VG.Proof.AesOcb.AArch64.mutR W D n) s₅.mem s₅'.mem := Fr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by have := Ar.t16; omega)⟩
  have S₅' := Slots.of_mut L Ar.data.w Fr' S₅
  -- The comparison.
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.cmp_ok E₅' Ar.t1 Ar.t16 S₅'.tl) fun s₆ ⟨m₆, g₆, sp₆, rd₆, wr₆⟩ => ?_)
  have E₆ := E₅'.others g₆ sp₆ rd₆ wr₆
  have F₆ : Frame [⟨W + BitVec.ofNat 64 tagO, 8⟩] s₅'.mem s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hD₆ : VG.Proof.AesOcb.AArch64.DBuf K W s₆ D n :=
    hD₃.of_eq (rd₆.trans (rdr.trans (T₅.rd.trans B.rd))) (wr₆.trans (wrr.trans (T₅.wr.trans B.wr)))
  let c : Bool := decide (bytesAt s₅'.mem W tl = bytesAt s₅'.mem (W + BitVec.ofNat 64 t2O) tl)
  -- The mask.
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.mask_ok E₆ hD₆ (c := c)
    (by rw [m₆, Mem.readW_writeW_self64]; simp only [c, decide_eq_true_eq])) fun s₇ ⟨g₇, sp₇, rd₇, wr₇, m₇⟩ => ?_)
  have E₇ := E₆.others g₇ sp₇ rd₇ wr₇
  have F₇ : Frame [⟨D, n⟩] s₆.mem s₇.mem := by
    rw [m₇]; exact writeBytes_frame _ _ _ (by rw [VG.Proof.AesOcb.AArch64.length_mask]; exact Region.contains_self _ _)
  have F₃₇ : Frame (VG.Proof.AesOcb.AArch64.mutR W D n) s₃.mem s₇.mem :=
    (((F₄.trans F₅).trans Fr').trans (F₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.AArch64.in_mutA (by decide))).trans
    (F₇.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesOcb.AArch64.in_mutD fun _ h => h)
  -- The result, and `restore`.
  have ok₇ : s₇.mem.readW W 64 = if c then 1#64 else 0#64 := by
    have e : s₆.mem.readW W 64 = if c then 1#64 else 0#64 := by
      have := Mem.readW_writeW_self64 s₅'.mem (W + BitVec.ofNat 64 tagO)
        (if bytesAt s₅'.mem W tl = bytesAt s₅'.mem (W + BitVec.ofNat 64 t2O) tl then 1#64 else 0#64)
      rw [← m₆] at this
      simp only [tagO, BitVec.add_zero] at this
      rw [this]; simp only [c, decide_eq_true_eq]
    rw [F₇.readW (r := ⟨W, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Ar.data.w.sub_right (Region.sub_prefix (by decide))).symm) (by decide), e]
  have r₀ : InRegions (s₇.rd ++ s₇.wr) W 8 := by simpa using E₇.perm.wR (d := 0) (n := 8) (by decide)
  obtain ⟨s₈, run₈, x0₈, m₈, g₈, sp₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa [ld .x0 .x19 tagO] s₇ = some s₈ ∧
      s₈.gpr .x0 = (if c then 1#64 else 0#64) ∧ s₈.mem = s₇.mem ∧ (∀ r, r ∉ [Reg.x0] → s₈.gpr r = s₇.gpr r) ∧
      s₈.sp = s₇.sp ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by orun [E₇.x19, r₀, ok₇], ?_, ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp [gpr_write]
    · rfl
    · simp only [List.mem_singleton] at h
      simp [gpr_write, h]
    all_goals rfl
  have E₈ := E₇.others g₈ sp₈ rd₈ wr₈
  have sv₈ : Spill.Saved W s.gpr saved s₈.mem := by
    rw [m₈]; exact VG.Proof.AesOcb.AArch64.saved_mut L Ar.data.w P₃.saved F₃₇
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
  refine WP.mono (VG.Proof.AesOcb.AArch64.restore_wp' E₈ sv₈) fun s₉ Rs => ⟨VG.Proof.AesOcb.AArch64.restore_abi Rs E₈.sp, ?_⟩
  -- The plaintext and the comparison.
  have x0₉ : s₉.gpr .x0 = if c then 1#64 else 0#64 := by rw [Rs.other _ (by decide), x0₈]
  have hout := B.out
  rw [c₃, i₃, l₃, d₃] at hout
  have hofs := B.ofs
  rw [l₃] at hofs
  have hck := B.ck
  rw [c₃, i₃, l₃, d₃] at hck
  have hTn := Ar.tag.lt
  have recv : bytesAt s₅'.mem W tl = bytesAt s.mem T tl := by
    rw [mr, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]) (by omega), length_bytesAt,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil]
    exact Proof.Cmac.bytesAt_frame Ff (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Ar.tag.w
      · exact Ar.td) (by omega)
  have t2₅ : bytesAt s₅'.mem (W + BitVec.ofNat 64 t2O) tl = bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl :=
    Proof.Cmac.bytesAt_frame Fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Offset.base_disjoint W (e := t2O) (n := tl) (k := tl) (by have := Ar.t16; unfold t2O; omega)
        (by have := Ar.t16; unfold t2O; omega)).symm) (by omega)
  have tagv := T₅.val
  rw [hck, hofs, ld₄, sum₄, cK₄] at tagv
  have d₉ : bytesAt s₉.mem D n = if c then bytesAt s₄.mem D n else zeros n := by
    have d₆ : bytesAt s₆.mem D n = bytesAt s₄.mem D n := by
      rw [Proof.Cmac.bytesAt_frame F₆ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
          (by omega),
        Proof.Cmac.bytesAt_frame Fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Ar.data.w.sub_right (Region.sub_prefix (by have := Ar.t16; omega))) (by omega),
        Proof.Cmac.bytesAt_frame T₅.frame (VG.Proof.AesOcb.AArch64.tag_data Ar.data.w (by decide)) (by omega)]
    rw [Rs.mem, m₈, m₇, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [VG.Proof.AesOcb.AArch64.length_mask]) hn, VG.Proof.AesOcb.AArch64.length_mask,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, d₆]
  rw [x0₉, d₉, hout, Proof.Ocb.decryptWith_eq]
  simp only [length_bytesAt, List.length_drop]
  have hc : ∀ x : Block, bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl = (Spec.Ocb.toBytes x).take tl →
      (c = true ↔ (Spec.Ocb.toBytes x).take tl = bytesAt s.mem T tl) := fun x hx => by
    show decide (_ = _) = true ↔ _
    rw [recv, t2₅, hx, decide_eq_true_iff, eq_comm]
  by_cases hr : 0 < n % 16
  · have h' : n - 16 * (n / 16) > 0 := by omega
    simp only [h', hr, ↓reduceIte] at tagv ⊢
    rw [VG.Proof.AesOcb.AArch64.bytesAt_take_block _ _ Ar.t16, tagv] at hc
    have hc := hc _ rfl
    by_cases hk : c = true
    · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
    · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩
  · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega
    simp only [h', hr, ↓reduceIte] at tagv ⊢
    rw [VG.Proof.AesOcb.AArch64.bytesAt_take_block _ _ Ar.t16, tagv] at hc
    have hc := hc _ rfl
    by_cases hk : c = true
    · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
    · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩

/-- `vg_aes_ocb_open`. -/
theorem open_wp (v : BlocksImpl) {s : State} (h : openAArch64.pre s) :
    WP isa («open» (VG.Proof.AesOcb.AArch64.callees v)) s fun s' => GprAbi s s' ∧ openAArch64.post s s' :=
  VG.Proof.AesOcb.AArch64.open_wp' v (VG.Proof.AesOcb.AArch64.openArgs_of h) rfl rfl (VG.Proof.AesOcb.AArch64.ofNat_toNat64 _).symm rfl (VG.Proof.AesOcb.AArch64.ofNat_toNat64 _).symm rfl (VG.Proof.AesOcb.AArch64.ofNat_toNat64 _).symm
    rfl (VG.Proof.AesOcb.AArch64.ofNat_toNat64 _).symm rfl (VG.Proof.AesOcb.AArch64.ofNat_toNat64 _).symm

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.OpenCT`. -/
section

/-!
# AES-OCB on AArch64: `vg_aes_ocb_open` is constant time

Untrusted: everything here is checked by Lean. As `seal_ct`, with the tag at
`W + t2O`; then the copy of the received tag to `W`, whose first block loads
the tag's address from the stack and is split there (`recv_rel`); then
`cmp`, which loads the tag length from `W`: its first block is split there,
and the comparison runs from it (`cmp_rel`); `mask` and the result read the
comparison's result only as data.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Ocb (Block blockAtMem ctxCiph ctxLstar)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq ct_of)

/-- `cmp`, in two runs. -/
theorem cmp_rel {K W D : Addr} {R n : Nat} {SP : Addr} {σ₁ σ₂ : State} (E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₁)
    (E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₂) {tl : Nat} (htl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (htl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) : RelCT isa (Eq2 σ₁ σ₂) cmp TT := by
  obtain ⟨s₁, run₁, -, x11₁, x12₁, x24₁, -, g₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.AArch64.cmpHead_ok E₁ htl₁
  obtain ⟨s₂, run₂, -, x11₂, x12₂, x24₂, -, g₂, sp₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.AArch64.cmpHead_ok E₂ htl₂
  have ne : ∀ r ∈ VG.Proof.AesOcb.AArch64.envRegs, r ∉ VG.Proof.AesOcb.AArch64.cmpRegs := by decide
  unfold cmp
  refine rel_seq (VG.Proof.AesOcb.AArch64.rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (WP.of_runBlock ⟨s₁, run₁, rfl⟩)
    (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_
  subst h₁ h₂
  exact VG.Proof.AesOcb.AArch64.rel_env (E₁.keep (fun r hr => g₁ r (ne r hr)) sp₁ rd₁ wr₁) (E₂.keep (fun r hr => g₂ r (ne r hr)) sp₂ rd₂ wr₂)
    [.x11, .x12, .x24] (by agree_tac [x11₁, x11₂, x12₁, x12₂, x24₁, x24₂]) ⟨_, by taint_decide⟩

/-- `recv` in two runs: its first block loads the tag's address from the
stack, and the copy runs from it. -/
theorem recv_rel {K W D : Addr} {R n : Nat} {SP : Addr} {σ₁ σ₂ : State} (E₁ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₁)
    (E₂ : VG.Proof.AesOcb.AArch64.Env K W D R n SP σ₂) {T : Addr} {tl : Nat}
    (htl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (htl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) (hT₁ : stackArg σ₁ 0 = T)
    (hT₂ : stackArg σ₂ 0 = T) (ha₁ : InRegions (σ₁.rd ++ σ₁.wr) (σ₁.sp + BitVec.ofNat 64 (8 * 0)) 8)
    (ha₂ : InRegions (σ₂.rd ++ σ₂.wr) (σ₂.sp + BitVec.ofNat 64 (8 * 0)) 8) : RelCT isa (Eq2 σ₁ σ₂) recv TT := by
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, -, g₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.AArch64.recvHead_ok E₁ htl₁ hT₁ ha₁
  obtain ⟨s₂, run₂, x11₂, x12₂, x13₂, -, g₂, sp₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.AArch64.recvHead_ok E₂ htl₂ hT₂ ha₂
  unfold recv
  refine rel_seq (VG.Proof.AesOcb.AArch64.rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (WP.of_runBlock ⟨s₁, run₁, rfl⟩)
    (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_
  subst h₁ h₂
  exact VG.Proof.AesOcb.AArch64.rel_env (E₁.others g₁ sp₁ rd₁ wr₁) (E₂.others g₂ sp₂ rd₂ wr₂) [.x11, .x12, .x13]
    (by agree_tac [x11₁, x11₂, x12₁, x12₂, x13₁, x13₂]) ⟨_, by taint_decide⟩

/-- The received tag's copy to `W` keeps the slots. -/
theorem recv_slots {K W D : Addr} {n : Nat} (L : VG.Proof.AesOcb.AArch64.Lay K W) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {tl : Nat}
    (h16 : tl ≤ 16) {m : Mem} {xs : List Byte} (hx : xs.length = tl) {N A : Addr} {nl al : Nat}
    (S : VG.Proof.AesOcb.AArch64.Slots W N A nl al tl m) : VG.Proof.AesOcb.AArch64.Slots W N A nl al tl (writeBytes m W xs) :=
  Slots.of_mut L hDW ((writeBytes_frame _ _ _ (by rw [hx]; exact Region.contains_self _ _)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by omega)⟩) S

theorem open_ct (v : BlocksImpl) : ConstantTime isa openAArch64.pre openAArch64.pub («open» (VG.Proof.AesOcb.AArch64.callees v)) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have A₁ := VG.Proof.AesOcb.AArch64.openArgs_of h₁
  have A₂ := VG.Proof.AesOcb.AArch64.args₂_of hq.1 (VG.Proof.AesOcb.AArch64.openArgs_of h₂)
  have qsp := hq.1.2.2.2.2.2.2.2.2.1
  have qT : stackArg σ₂ 0 = stackArg σ₁ 0 := (hq.1.2.2.2.2.2.2.2.2.2 0 (by decide)).symm
  have L := A₁.lay
  unfold «open» front
  refine VG.Proof.AesOcb.AArch64.rel_front (VG.Proof.AesOcb.AArch64.pre_relk v A₁ A₂ hq.1 fun τ₁ τ₂ P₁ P₂ => ?_)
  have E₂ := P₂.env
  rw [← qsp] at E₂
  refine rel_seq (VG.Proof.AesOcb.AArch64.bodyOpen_rel L A₁.rounds v P₁.env E₂ (A₁.data.of_eq P₁.rd P₁.wr) (A₂.data.of_eq P₂.rd P₂.wr)
      P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, VG.Proof.AesOcb.AArch64.ctxLstar_W L P₁.frame]) P₂.ofs P₂.o0 P₂.ck
      (by rw [P₂.l0, VG.Proof.AesOcb.AArch64.ctxLstar_W L P₂.frame]))
    (VG.Proof.AesOcb.AArch64.bodyOpen_ok v L P₁.env A₁.rounds (A₁.data.of_eq P₁.rd P₁.wr) P₁.ofs P₁.o0 P₁.ck
      (by rw [P₁.l0, VG.Proof.AesOcb.AArch64.ctxLstar_W L P₁.frame]))
    (VG.Proof.AesOcb.AArch64.bodyOpen_ok v L E₂ A₁.rounds (A₂.data.of_eq P₂.rd P₂.wr) P₂.ofs P₂.o0 P₂.ck
      (by rw [P₂.l0, VG.Proof.AesOcb.AArch64.ctxLstar_W L P₂.frame])) fun u₁ u₂ B₁ B₂ => ?_
  refine rel_seq (VG.Proof.AesOcb.AArch64.tag_rel L A₁.rounds v B₁.env B₂.env (.inr rfl)) (VG.Proof.AesOcb.AArch64.tag_ok v L B₁.env A₁.rounds (.inr rfl))
    (VG.Proof.AesOcb.AArch64.tag_ok v L B₂.env A₁.rounds (.inr rfl)) fun w₁ w₂ T₁ T₂ => ?_
  have S₁ := Slots.of_mut L A₁.data.w ((VG.Proof.AesOcb.AArch64.bodyR_mut B₁.frame).trans (VG.Proof.AesOcb.AArch64.tagR_mut (by decide) T₁.frame)) P₁.slots
  have S₂ := Slots.of_mut L A₁.data.w ((VG.Proof.AesOcb.AArch64.bodyR_mut B₂.frame).trans (VG.Proof.AesOcb.AArch64.tagR_mut (by decide) T₂.frame)) P₂.slots
  obtain ⟨t₁, a₁⟩ := VG.Proof.AesOcb.AArch64.front_tag A₁ rfl (by decide) P₁ B₁ T₁ rfl
  obtain ⟨t₂, a₂⟩ := VG.Proof.AesOcb.AArch64.front_tag A₂ qT (by decide) P₂ B₂ T₂ qsp
  refine rel_seq (VG.Proof.AesOcb.AArch64.recv_rel T₁.env T₂.env S₁.tl S₂.tl t₁ t₂ a₁ a₂)
    (VG.Proof.AesOcb.AArch64.recv_ok T₁.env A₁.t1 A₁.t16 S₁.tl t₁ a₁ (by rw [T₁.rd, B₁.rd, P₁.rd, T₁.wr, B₁.wr, P₁.wr]; exact A₁.tag.rd)
      A₁.tag.w)
    (VG.Proof.AesOcb.AArch64.recv_ok T₂.env A₁.t1 A₁.t16 S₂.tl t₂ a₂ (by rw [T₂.rd, B₂.rd, P₂.rd, T₂.wr, B₂.wr, P₂.wr]; exact A₂.tag.rd)
      A₂.tag.w)
    fun y₁ y₂ ⟨m₁, g₁, sp₁, rd₁, wr₁⟩ ⟨m₂, g₂, sp₂, rd₂, wr₂⟩ => ?_
  have Y₁ := T₁.env.others g₁ sp₁ rd₁ wr₁
  have Y₂ := T₂.env.others g₂ sp₂ rd₂ wr₂
  have Sy₁ := VG.Proof.AesOcb.AArch64.recv_slots L A₁.data.w A₁.t16 (Proof.Ocb.length_bytesAt w₁.mem (stackArg σ₁ 0) _) S₁
  have Sy₂ := VG.Proof.AesOcb.AArch64.recv_slots L A₁.data.w A₁.t16 (Proof.Ocb.length_bytesAt w₂.mem (stackArg σ₁ 0) _) S₂
  rw [← m₁] at Sy₁
  rw [← m₂] at Sy₂
  refine rel_seq (VG.Proof.AesOcb.AArch64.cmp_rel Y₁ Y₂ Sy₁.tl Sy₂.tl) (VG.Proof.AesOcb.AArch64.cmp_ok Y₁ A₁.t1 A₁.t16 Sy₁.tl)
    (VG.Proof.AesOcb.AArch64.cmp_ok Y₂ A₁.t1 A₁.t16 Sy₂.tl) fun z₁ z₂ ⟨_, g₁, sp₁, rd₁, wr₁⟩ ⟨_, g₂, sp₂, rd₂, wr₂⟩ => ?_
  have F₁ := Y₁.others g₁ sp₁ rd₁ wr₁
  have F₂ := Y₂.others g₂ sp₂ rd₂ wr₂
  refine VG.Proof.AesOcb.AArch64.rel_seqEnv F₁ F₂ (VG.Proof.AesOcb.AArch64.rel_env F₁ F₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · intro z₁ z₂ G₁ G₂
    exact VG.Proof.AesOcb.AArch64.rel_env G₁ G₂ [] (by agree_tac []) ⟨_, by taint_decide⟩

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Init`. -/
section

/-!
# AES-OCB on AArch64: `vg_aes_ocb_init`

Untrusted: everything here is checked by Lean. `init` saves our caller's
registers in the scratch buffer, expands the key into the key context
(`vg_aes_expand_key_scratch`), enciphers a zero block at byte 240 of it in place,
for `L_*` (`vg_aes_encrypt_blocks`), and restores the registers
(`init_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (length_bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (covers_of_mem covers_cons covers_prefix covers_off covers_left in_off KeyCall key_call)

/-- The rounds, as `lsr 2; add 6` computes them from the key length. -/
theorem rounds_of_len {L : Nat} (hL : L = 16 ∨ L = 24 ∨ L = 32) :
    BitVec.ofNat 64 L >>> 2 + BitVec.ofNat 64 6 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) := by
  rcases hL with rfl | rfl | rfl <;> decide

/-- What `vg_aes_ocb_init` is given: the key (`L` bytes at `K`), the key
context at `Ctx` and the scratch buffer at `W`. -/
structure IArgs (s : State) (K Ctx W : Addr) (L : Nat) : Prop where
  rd : s.rd = [⟨K, L⟩]
  wr : s.wr = [⟨Ctx, 256⟩, ⟨W, 2560⟩]
  kc : (⟨K, L⟩ : Region).Disjoint ⟨Ctx, 256⟩
  ks : (⟨K, L⟩ : Region).Disjoint ⟨W, 2560⟩
  cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩
  wc : Ctx.toNat + 256 ≤ 2 ^ 64
  ws : W.toNat + 2560 ≤ 2 ^ 64
  len : L = 16 ∨ L = 24 ∨ L = 32

theorem IArgs.of {s : State} (hp : initAArch64.pre s) :
    VG.Proof.AesOcb.AArch64.IArgs s (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x1).toNat :=
  let ⟨a, b, c, d, e, f, g, h⟩ := hp
  ⟨a, b, c, d, e, f, g, h⟩

namespace IArgs

variable {s : State} {K Ctx W : Addr} {L : Nat} (Ar : VG.Proof.AesOcb.AArch64.IArgs s K Ctx W L)
include Ar

theorem pW : Covers [⟨W, 2560⟩] s.wr := by rw [Ar.wr]; exact covers_of_mem (by simp)
theorem pC : Covers [⟨Ctx, 256⟩] s.wr := by rw [Ar.wr]; exact covers_of_mem (by simp)
theorem pK : Covers [⟨K, L⟩] (s.rd ++ s.wr) := by rw [Ar.rd]; exact covers_of_mem (by simp)

end IArgs

/-- The registers saved and the arguments of `vg_aes_expand_key_scratch`. -/
theorem init1_ok {s : State} {K Ctx W : Addr} {L : Nat} (Ar : IArgs s K Ctx W L) (h0 : s.gpr .x0 = K)
    (h1 : s.gpr .x1 = BitVec.ofNat 64 L) (h2 : s.gpr .x2 = Ctx) (h3 : s.gpr .x3 = W) :
    WP isa (.block (save .x3 ++ [Impl.AesGcm.AArch64.mov .x19 .x3, Impl.AesGcm.AArch64.mov .x20 .x2,
        .lsr .x .x22 .x1 2, Impl.AesGcm.AArch64.ptr .x22 .x22 6, Impl.AesGcm.AArch64.ptr .x3 .x19 scrO])) s
      fun s₂ => s₂.gpr .x19 = W ∧ s₂.gpr .x20 = Ctx ∧
        s₂.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧
        KeyCall s₂ K Ctx (W + BitVec.ofNat 64 512) L ∧ s₂.sp = s.sp ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr ∧
        Spill.Saved W s.gpr saved s₂.mem ∧ Frame [⟨W + BitVec.ofNat 64 160, 88⟩] s.mem s₂.mem := by
  have pW := Ar.pW
  have pC := Ar.pC
  have hin : ∀ p ∈ saved, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 p.2) 8 := fun p hp => by
    rw [h3]; exact in_off pW (by have := VG.Proof.AesOcb.AArch64.saved_in p hp; omega) (by decide)
  rw [VG.Proof.AesOcb.AArch64.save_eq]
  refine WP.block_append_iff.mpr (WP.mono (Spill.save_wp saved_fits.1 hin) fun s₁ St => ?_)
  rw [h3] at St
  obtain ⟨s₂, run₂, x19₂, x20₂, x22₂, x3₂, x0₂, x1₂, x2₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [Impl.AesGcm.AArch64.mov .x19 .x3, Impl.AesGcm.AArch64.mov .x20 .x2, .lsr .x .x22 .x1 2,
        Impl.AesGcm.AArch64.ptr .x22 .x22 6, Impl.AesGcm.AArch64.ptr .x3 .x19 scrO] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = Ctx ∧ s₂.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds (L / 4)) ∧
      s₂.gpr .x3 = W + BitVec.ofNat 64 512 ∧ s₂.gpr .x0 = K ∧ s₂.gpr .x1 = BitVec.ofNat 64 L ∧
      s₂.gpr .x2 = Ctx ∧ s₂.sp = s.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by orun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, St.gpr, h3]
    · simp [gpr_write, St.gpr, h2]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, St.gpr, h1, BitVec.setWidth_eq]
      exact VG.Proof.AesOcb.AArch64.rounds_of_len Ar.len
    · simp [gpr_write, St.gpr, h3]
    · simp [gpr_write, St.gpr, h0]
    · simp [gpr_write, St.gpr, h1]
    · simp [gpr_write, St.gpr, h2]
    · simp only [sp_write]; exact St.sp
    · rfl
    · simp only [rd_write]; exact St.rd
    · simp only [wr_write]; exact St.wr
  refine WP.of_runBlock ⟨s₂, run₂, x19₂, x20₂, x22₂, ?_, sp₂, rd₂, wr₂, ?_, ?_⟩
  · refine ⟨x0₂, x1₂, x2₂, x3₂, Ar.len, Ar.kc.sub_right (Region.sub_prefix (by decide)),
      Ar.ks.sub_right (Lay.wSub (by decide)), (Ar.cs.sub_left (Region.sub_prefix (by decide))).sub_right
        (Lay.wSub (by decide)), ?_, ?_⟩
    · rw [rd₂, wr₂]
      exact covers_cons Ar.pK (covers_left (covers_cons (covers_prefix pC (by decide))
        (covers_off pW (by decide) (by decide))))
    · rw [wr₂]; exact covers_cons (covers_prefix pC (by decide)) (covers_off pW (by decide) (by decide))
  · rw [m₂, St.mem]; exact Spill.saveMem_saved VG.Proof.AesOcb.AArch64.saved_fits _ _ _
  · rw [m₂, St.mem]; exact Spill.saveMem_frame VG.Proof.AesOcb.AArch64.saved_in (by decide) _ _ _

/-- A zero block at byte 240 of the key context, and the arguments of its encipherment. -/
theorem init2_ok {s : State} {K Ctx W : Addr} {L : Nat} (Ar : VG.Proof.AesOcb.AArch64.IArgs s K Ctx W L) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {t : State} (h19 : t.gpr .x19 = W) (h20 : t.gpr .x20 = Ctx)
    (h22 : t.gpr .x22 = BitVec.ofNat 64 R) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    WP isa (.block [Impl.AesGcm.AArch64.imm .x9 0, st .x20 240 .x9, st .x20 248 .x9,
        Impl.AesGcm.AArch64.ptr .x2 .x20 240, Impl.AesGcm.AArch64.imm .x3 1, Impl.AesGcm.AArch64.mov .x0 .x20,
        Impl.AesGcm.AArch64.mov .x1 .x22, Impl.AesGcm.AArch64.ptr .x4 .x19 scrO]) t fun t₄ =>
      VG.Proof.AesOcb.AArch64.BCall t₄ Ctx (Ctx + BitVec.ofNat 64 240) (W + BitVec.ofNat 64 512) R 1 ∧
      (∀ r ∈ preserved, t₄.gpr r = t.gpr r) ∧ t₄.sp = t.sp ∧ t₄.rd = t.rd ∧ t₄.wr = t.wr ∧
      t₄.mem = (t.mem.writeW (Ctx + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
  have pW := Ar.pW
  have pC := Ar.pC
  have w₁ := in_off pC (show 240 + 8 ≤ 256 by decide) (by decide)
  have w₂ := in_off pC (show 248 + 8 ≤ 256 by decide) (by decide)
  rw [← hwr] at w₁ w₂
  obtain ⟨s₄, run₄, m₄, x0₄, x1₄, x2₄, x3₄, x4₄, g₄, sp₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa
      [Impl.AesGcm.AArch64.imm .x9 0, st .x20 240 .x9, st .x20 248 .x9, Impl.AesGcm.AArch64.ptr .x2 .x20 240,
        Impl.AesGcm.AArch64.imm .x3 1, Impl.AesGcm.AArch64.mov .x0 .x20, Impl.AesGcm.AArch64.mov .x1 .x22,
        Impl.AesGcm.AArch64.ptr .x4 .x19 scrO] t = some s₄ ∧
      s₄.mem = (t.mem.writeW (Ctx + BitVec.ofNat 64 240) (0 : BitVec 64)).writeW
        (Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₄.gpr .x0 = Ctx ∧ s₄.gpr .x1 = BitVec.ofNat 64 R ∧ s₄.gpr .x2 = Ctx + BitVec.ofNat 64 240 ∧
      s₄.gpr .x3 = BitVec.ofNat 64 1 ∧ s₄.gpr .x4 = W + BitVec.ofNat 64 512 ∧
      (∀ r ∈ preserved, s₄.gpr r = t.gpr r) ∧ s₄.sp = t.sp ∧ s₄.rd = t.rd ∧ s₄.wr = t.wr := by
    refine ⟨_, by orun [h19, h20, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · simp only [mem_write, VG.Proof.AesOcb.AArch64.addr8]; rfl
    · simp [gpr_write, h20]
    · simp [gpr_write, h22]
    · simp [gpr_write, h20]
    · simp [gpr_write]
    · simp [gpr_write, h19]
    · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
    all_goals rfl
  have rd₄' : s₄.rd = s.rd := rd₄.trans hrd
  have wr₄' : s₄.wr = s.wr := wr₄.trans hwr
  refine WP.of_runBlock ⟨s₄, run₄,
    { x0 := x0₄, x1 := x1₄, x2 := x2₄, x3 := x3₄, x4 := x4₄, rounds := hR
      wrap := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Nat.mod_le (Ctx.toNat + 240 % 2 ^ 64) (2 ^ 64); have := Ar.wc; omega
      kd := Offset.base_disjoint Ctx (by decide) (by have := Ar.wc; omega)
      ks := (Ar.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
      ds := (Ar.cs.sub_left (Lay.kSub (by decide))).sub_right (Lay.wSub (by decide))
      reads := by
        rw [rd₄', wr₄']
        exact covers_cons (covers_left (covers_prefix pC (by decide))) (covers_cons
          (covers_left (covers_off pC (by decide) (by decide))) (covers_left (covers_off pW (by decide) (by decide))))
      writes := by
        rw [wr₄']
        exact covers_cons (covers_off pC (by decide) (by decide)) (covers_off pW (by decide) (by decide)) },
    g₄, sp₄, rd₄, wr₄, m₄⟩

/-- `vg_aes_ocb_init`, for its arguments. -/
theorem init_wp' (v : BlocksImpl) {s : State} {K Ctx W : Addr} {L : Nat} (Ar : VG.Proof.AesOcb.AArch64.IArgs s K Ctx W L)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 L) (h2 : s.gpr .x2 = Ctx) (h3 : s.gpr .x3 = W) :
    WP isa (init (VG.Proof.AesOcb.AArch64.callees v)) s fun s' => GprAbi s s' ∧ Spec.Ocb.KeyRepr s'.mem Ctx (bytesAt s.mem K L) := by
  have pW := Ar.pW
  have hKL : L < 2 ^ 64 := by rcases Ar.len with h | h | h <;> omega
  unfold init
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.init1_ok Ar h0 h1 h2 h3) fun s₂ ⟨x19₂, x20₂, x22₂, kc, sp₂, rd₂, wr₂, sv₂, f₂⟩ => ?_)
  generalize hRd : Spec.Aes.rounds (L / 4) = R at x22₂
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := by rw [← hRd]; rcases Ar.len with rfl | rfl | rfl <;> decide
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR' with rfl | rfl | rfl <;> decide
  -- The key schedule.
  refine WP.seq (WP.mono (key_call (VG.Proof.AesOcb.AArch64.keyImpl v) kc) fun s₃ g => ?_)
  have g19 : s₃.gpr .x19 = W := by rw [g.saved .x19 (by decide) (by decide), x19₂]
  have g20 : s₃.gpr .x20 = Ctx := by rw [g.saved .x20 (by decide) (by decide), x20₂]
  have g22 : s₃.gpr .x22 = BitVec.ofNat 64 R := by rw [g.saved .x22 (by decide) (by decide), x22₂]
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.init2_ok Ar hR' g19 g20 g22 (g.rd.trans rd₂) (g.wr.trans wr₂))
    fun s₄ ⟨bc, g₄, sp₄, rd₄, wr₄, m₄⟩ => ?_)
  have rd₄' : s₄.rd = s.rd := rd₄.trans (g.rd.trans rd₂)
  have wr₄' : s₄.wr = s.wr := wr₄.trans (g.wr.trans wr₂)
  have dK0 : (⟨Ctx, 240⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 240, 16 * 1⟩ := bc.kd
  refine WP.seq (WP.mono (VG.Proof.AesOcb.AArch64.blk_call v.encOk v.encNoFrames bc) fun s₅ P₅ => ?_)
  -- The saved registers, and `restore`.
  have dSv : ∀ {d k : Nat}, d + k ≤ 256 → (⟨W + BitVec.ofNat 64 160, 88⟩ : Region).Disjoint ⟨Ctx + BitVec.ofNat 64 d, k⟩ :=
    fun h => (Ar.cs.sub_left (Offset.sub_base _ h)).sub_right (Lay.wSub (by decide)) |>.symm
  have dSv' : ∀ {d k : Nat}, 512 ≤ d → d + k ≤ 2560 →
      (⟨W + BitVec.ofNat 64 160, 88⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Offset.disjoint W (.inl (by omega)) (by omega) (by have := Ar.ws; omega)
  have f₄ : Frame [⟨Ctx + BitVec.ofNat 64 240, 16⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact Proof.Cmac.frame_store2 _ _ _
  have sv₅ : Spill.Saved W s.gpr saved s₅.mem := by
    have a := Spill.Saved.frame_in sv₂ VG.Proof.AesOcb.AArch64.saved_in (rs := [⟨Ctx, 240⟩, ⟨W + BitVec.ofNat 64 512, 512⟩]) g.frame
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simpa using dSv (d := 0) (k := 240) (by decide)
        · exact dSv' (by decide) (by decide))
    have b := Spill.Saved.frame_in a VG.Proof.AesOcb.AArch64.saved_in f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dSv (by decide))
    exact Spill.Saved.frame_in b VG.Proof.AesOcb.AArch64.saved_in P₅.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dSv (by decide)
      · exact dSv' (by decide) (by decide))
  have c19 : s₅.gpr .x19 = W := by rw [P₅.saved .x19 (by decide) (by decide), g₄ _ (by decide), g19]
  have sp₅ : s₅.sp = s.sp := by rw [P₅.sp, sp₄, g.sp, sp₂]
  rw [VG.Proof.AesOcb.AArch64.restore_eq]
  refine WP.mono (Spill.restore_wp c19 saved_fits.1 (by decide) (fun p hp => by
    rw [P₅.rd, P₅.wr, rd₄', wr₄']; exact covers_left pW _ _ ⟨_, List.mem_singleton_self _,
      Offset.contains_base W (by have := VG.Proof.AesOcb.AArch64.saved_in p hp; omega) (by have := VG.Proof.AesOcb.AArch64.saved_in p hp; have := Ar.ws; omega)⟩)
      sv₅) fun s₆ Rs => ⟨VG.Proof.AesOcb.AArch64.restore_abi Rs sp₅, ?_⟩
  -- The key context.
  have k₃ : bytesAt s₃.mem Ctx (16 * (R + 1)) = Spec.Aes.expandKey (bytesAt s.mem K L) := by
    rw [← hRd, g.out, Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.ks.sub_right (Lay.wSub (by decide)))
        (by omega)]
  have k₅ : bytesAt s₅.mem Ctx (16 * (R + 1)) = Spec.Aes.expandKey (bytesAt s.mem K L) := by
    rw [Proof.Cmac.bytesAt_frame P₅.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dK0.sub_left (Region.sub_prefix hRb)
        · exact (Ar.cs.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))) (by omega),
      Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dK0.sub_left (Region.sub_prefix hRb)) (by omega), k₃]
  refine ⟨?_, ?_⟩
  · rw [length_bytesAt, hRd, Rs.mem]; exact k₅
  · show blockAtMem s₆.mem (Ctx + BitVec.ofNat 64 240) = _
    have hz : blockAtMem s₄.mem (Ctx + BitVec.ofNat 64 240) = 0 := by
      rw [m₄, VG.Proof.AesOcb.AArch64.blockAtMem_store2, Proof.Cmac.le8_zero]; rfl
    rw [Rs.mem, P₅.enc0, hz, Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dK0.sub_left (Region.sub_prefix hRb)) (by omega), k₃,
      Spec.Ocb.aes, length_bytesAt, hRd]

/-- `vg_aes_ocb_init`. -/
theorem init_wp (v : BlocksImpl) {s : State} (hp : initAArch64.pre s) :
    WP isa (init (VG.Proof.AesOcb.AArch64.callees v)) s fun s' => GprAbi s s' ∧ initAArch64.post s s' :=
  VG.Proof.AesOcb.AArch64.init_wp' v (IArgs.of hp) rfl (VG.Proof.AesOcb.AArch64.ofNat_toNat64 _).symm rfl rfl

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.InitCT`. -/
section

/-!
# AES-OCB on AArch64: `vg_aes_ocb_init` is constant time

Untrusted: everything here is checked by Lean. The blocks between the calls
run from public registers (the arguments, then the scratch buffer, the key
context and the rounds), and the calls have the same arguments in both runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint rel_key ct_of KeyCall key_call)

theorem init_ct (v : BlocksImpl) : ConstantTime isa initAArch64.pre initAArch64.pub (init (VG.Proof.AesOcb.AArch64.callees v)) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, qsp⟩ := hq
  have A₁ := IArgs.of h₁
  have A₂ := IArgs.of h₂
  rw [← q0, ← q1, ← q2, ← q3] at A₂
  have o : ∀ x : BitVec 64, x = BitVec.ofNat 64 x.toNat := fun x => (VG.Proof.AesOcb.AArch64.ofNat_toNat64 x).symm
  have hR' : Spec.Aes.rounds ((σ₁.gpr .x1).toNat / 4) = 10 ∨ Spec.Aes.rounds ((σ₁.gpr .x1).toNat / 4) = 12 ∨
      Spec.Aes.rounds ((σ₁.gpr .x1).toNat / 4) = 14 := by rcases A₁.len with h | h | h <;> rw [h] <;> decide
  unfold init
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3] qsp (by agree_tac [q0, q1, q2, q3]) ⟨_, by taint_decide⟩)
    (VG.Proof.AesOcb.AArch64.init1_ok A₁ rfl (o _) rfl rfl) (VG.Proof.AesOcb.AArch64.init1_ok A₂ q0.symm (by rw [← q1]; exact o _) q2.symm q3.symm)
    fun s₁ s₂ ⟨a19, a20, a22, kc₁, asp, ard, awr, _, _⟩ ⟨b19, b20, b22, kc₂, bsp, brd, bwr, _, _⟩ => ?_
  refine rel_seq (rel_key (VG.Proof.AesOcb.AArch64.keyImpl v) kc₁ kc₂ (by rw [asp, bsp, qsp])) (key_call (VG.Proof.AesOcb.AArch64.keyImpl v) kc₁)
    (key_call (VG.Proof.AesOcb.AArch64.keyImpl v) kc₂) fun t₁ t₂ g₁ g₂ => ?_
  have c19 : t₁.gpr .x19 = σ₁.gpr .x3 := by rw [g₁.saved .x19 (by decide) (by decide), a19]
  have c20 : t₁.gpr .x20 = σ₁.gpr .x2 := by rw [g₁.saved .x20 (by decide) (by decide), a20]
  have c22 : t₁.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds ((σ₁.gpr .x1).toNat / 4)) := by rw [g₁.saved .x22 (by decide) (by decide), a22]
  have d19 : t₂.gpr .x19 = σ₁.gpr .x3 := by rw [g₂.saved .x19 (by decide) (by decide), b19]
  have d20 : t₂.gpr .x20 = σ₁.gpr .x2 := by rw [g₂.saved .x20 (by decide) (by decide), b20]
  have d22 : t₂.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds ((σ₁.gpr .x1).toNat / 4)) := by rw [g₂.saved .x22 (by decide) (by decide), b22]
  refine rel_seq (rel_taint [.x19, .x20, .x22] (by rw [g₁.sp, g₂.sp, asp, bsp, qsp])
      (by agree_tac [c19, c20, c22, d19, d20, d22]) ⟨_, by taint_decide⟩)
    (VG.Proof.AesOcb.AArch64.init2_ok A₁ hR' c19 c20 c22 (by rw [g₁.rd, ard]) (by rw [g₁.wr, awr]))
    (VG.Proof.AesOcb.AArch64.init2_ok A₂ hR' d19 d20 d22 (by rw [g₂.rd, brd]) (by rw [g₂.wr, bwr]))
    fun u₁ u₂ ⟨bc₁, e₁, esp₁, _, _, _⟩ ⟨bc₂, e₂, esp₂, _, _, _⟩ => ?_
  refine rel_seq (VG.Proof.AesOcb.AArch64.blk_rel v.encOk v.encCt fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨_, _, _, _, _, bc₁, bc₂, by rw [esp₁, esp₂, g₁.sp, g₂.sp, asp, bsp, qsp]⟩)
    (VG.Proof.AesOcb.AArch64.blk_call v.encOk v.encNoFrames bc₁) (VG.Proof.AesOcb.AArch64.blk_call v.encOk v.encNoFrames bc₂) fun w₁ w₂ P₁ P₂ => ?_
  exact rel_taint [.x19] (by rw [P₁.sp, P₂.sp, esp₁, esp₂, g₁.sp, g₂.sp, asp, bsp, qsp])
    (by agree_tac [P₁.saved .x19 (by decide) (by decide), P₂.saved .x19 (by decide) (by decide),
      e₁ .x19 (by decide), e₂ .x19 (by decide), c19, d19]) ⟨_, by taint_decide⟩

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Verified`. -/
section

/-!
# AES-OCB on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_encrypt_blocks`,
`vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch`), a state satisfying each
precondition, and the shared contracts of `Spec/Ocb/Contract.lean` with the
working space as a last argument (`Proof/AesOcb/Scratch.lean`), with no
stack: the calls keep the return address in `x30`, which each function saves
in its working space. `Frame.lean` allocates the working space.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.Impl.AesOcb.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-! ## v8–v15 -/

theorem seal_keepsV (v : BlocksImpl) : («seal» (VG.Proof.AesOcb.AArch64.callees v)).allInstrs keepsV = true := by
  simp only [«seal», front, tagOut, nonce, Impl.AesOcb.AArch64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, lNtz, body,
    whole, pass, nextOffset, rest, padCk, xorPad, tag, callBlocks, VG.Proof.AesOcb.AArch64.callees, Code.allInstrs, v.encKeepsV,
    v.decKeepsV, Bool.true_and, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem open_keepsV (v : BlocksImpl) : («open» (VG.Proof.AesOcb.AArch64.callees v)).allInstrs keepsV = true := by
  simp only [«open», front, recv, nonce, Impl.AesOcb.AArch64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, lNtz, body,
    whole, pass, nextOffset, rest, padCk, xorPad, tag, cmp, mask, callBlocks, VG.Proof.AesOcb.AArch64.callees, Code.allInstrs, v.encKeepsV,
    v.decKeepsV, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_keepsV (v : BlocksImpl) : (init (VG.Proof.AesOcb.AArch64.callees v)).allInstrs keepsV = true := by
  simp only [init, VG.Proof.AesOcb.AArch64.callees, Code.allInstrs, v.encKeepsV, v.expandKeepsV, Bool.true_and, Bool.and_true]
  decide +kernel

/-! ## Correctness -/

theorem seal_correct (v : BlocksImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa («seal» (VG.Proof.AesOcb.AArch64.callees v)) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesOcb.AArch64.seal_wp v hs) (VG.Proof.AesOcb.AArch64.seal_keepsV v)

theorem open_correct (v : BlocksImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa («open» (VG.Proof.AesOcb.AArch64.callees v)) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesOcb.AArch64.open_wp v hs) (VG.Proof.AesOcb.AArch64.open_keepsV v)

theorem init_correct (v : BlocksImpl) (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa (init (VG.Proof.AesOcb.AArch64.callees v)) s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesOcb.AArch64.init_wp v hs) (VG.Proof.AesOcb.AArch64.init_keepsV v)

/-! ## States satisfying the preconditions -/

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: a 1-byte nonce,
no associated data, no data, a 4-byte tag at `0x5000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 1 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8008 then 4 else if a = 0x8001 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x8000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ocb_open`: as `sealSat`,
with the tag read only. -/
def openSat : State := { VG.Proof.AesOcb.AArch64.sealSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0, 2560⟩] }

/-- A state satisfying the precondition of `vg_aes_ocb_init`: a 16-byte key. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

/-! ## The shared contracts -/

theorem seal_verified (v : BlocksImpl) :
    Verified AArch64.target («seal» (VG.Proof.AesOcb.AArch64.callees v)) (Proof.AesOcb.sealScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.AesOcb.AArch64.seal_correct v) (VG.Proof.AesOcb.AArch64.seal_ct v) (by
    sig_implies [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Spec.Ocb.sealPost, VG.Proof.AesOcb.AArch64.sealAArch64, VG.Proof.AesOcb.AArch64.sealPreA, VG.Proof.AesOcb.AArch64.oneFacts, VG.Proof.AesOcb.AArch64.aCtx, VG.Proof.AesOcb.AArch64.aNonce, VG.Proof.AesOcb.AArch64.aAad, VG.Proof.AesOcb.AArch64.aData, VG.Proof.AesOcb.AArch64.aTag, VG.Proof.AesOcb.AArch64.aWork, VG.Proof.AesOcb.AArch64.onePub, VG.Proof.AesOcb.AArch64.args,
      VG.Proof.AesOcb.AArch64.rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
      List.range.loop] [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesOcb.AArch64.sealSat)

theorem init_verified (v : BlocksImpl) :
    Verified AArch64.target (init (VG.Proof.AesOcb.AArch64.callees v)) (Proof.AesOcb.initScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.AesOcb.AArch64.init_correct v) (VG.Proof.AesOcb.AArch64.init_ct v) (by
    sig_implies [Proof.AesOcb.initScratchContract, Proof.AesOcb.initScratchSig, Spec.Ocb.initPre,
      Spec.Ocb.initPost, VG.Proof.AesOcb.AArch64.initAArch64, AArch64.abi, AArch64.argRegs] [initSat] using VG.Proof.AesOcb.AArch64.initSat)

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (v : BlocksImpl) :
    Verified AArch64.target («open» (VG.Proof.AesOcb.AArch64.callees v)) (Proof.AesOcb.openScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.AesOcb.AArch64.open_correct v) (VG.Proof.AesOcb.AArch64.open_ct v)
    { pre := by sig_implies_pre [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, VG.Proof.AesOcb.AArch64.openAArch64, VG.Proof.AesOcb.AArch64.openLeak, VG.Proof.AesOcb.AArch64.openPreA, VG.Proof.AesOcb.AArch64.oneFacts, VG.Proof.AesOcb.AArch64.aCtx, VG.Proof.AesOcb.AArch64.aNonce, VG.Proof.AesOcb.AArch64.aAad, VG.Proof.AesOcb.AArch64.aData,
        VG.Proof.AesOcb.AArch64.aTag, VG.Proof.AesOcb.AArch64.aWork, VG.Proof.AesOcb.AArch64.onePub, VG.Proof.AesOcb.AArch64.openOut, VG.Proof.AesOcb.AArch64.args, VG.Proof.AesOcb.AArch64.rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      post := by sig_implies_post [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, VG.Proof.AesOcb.AArch64.openAArch64, VG.Proof.AesOcb.AArch64.openLeak, VG.Proof.AesOcb.AArch64.openPreA, VG.Proof.AesOcb.AArch64.oneFacts, VG.Proof.AesOcb.AArch64.aCtx, VG.Proof.AesOcb.AArch64.aNonce, VG.Proof.AesOcb.AArch64.aAad, VG.Proof.AesOcb.AArch64.aData,
        VG.Proof.AesOcb.AArch64.aTag, VG.Proof.AesOcb.AArch64.aWork, VG.Proof.AesOcb.AArch64.onePub, VG.Proof.AesOcb.AArch64.openOut, VG.Proof.AesOcb.AArch64.args, VG.Proof.AesOcb.AArch64.rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, VG.Proof.AesOcb.AArch64.openAArch64, VG.Proof.AesOcb.AArch64.openLeak, VG.Proof.AesOcb.AArch64.openPreA, VG.Proof.AesOcb.AArch64.oneFacts, VG.Proof.AesOcb.AArch64.aCtx, VG.Proof.AesOcb.AArch64.aNonce, VG.Proof.AesOcb.AArch64.aAad, VG.Proof.AesOcb.AArch64.aData,
        VG.Proof.AesOcb.AArch64.aTag, VG.Proof.AesOcb.AArch64.aWork, VG.Proof.AesOcb.AArch64.onePub, VG.Proof.AesOcb.AArch64.openOut, VG.Proof.AesOcb.AArch64.args, VG.Proof.AesOcb.AArch64.rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop] at h
        sig_split h
        sig_reduce [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, VG.Proof.AesOcb.AArch64.openAArch64, VG.Proof.AesOcb.AArch64.openLeak, VG.Proof.AesOcb.AArch64.openPreA, VG.Proof.AesOcb.AArch64.oneFacts, VG.Proof.AesOcb.AArch64.aCtx, VG.Proof.AesOcb.AArch64.aNonce, VG.Proof.AesOcb.AArch64.aAad, VG.Proof.AesOcb.AArch64.aData,
        VG.Proof.AesOcb.AArch64.aTag, VG.Proof.AesOcb.AArch64.aWork, VG.Proof.AesOcb.AArch64.onePub, VG.Proof.AesOcb.AArch64.openOut, VG.Proof.AesOcb.AArch64.args, VG.Proof.AesOcb.AArch64.rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
        sig_simp [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, VG.Proof.AesOcb.AArch64.openAArch64, VG.Proof.AesOcb.AArch64.openLeak, VG.Proof.AesOcb.AArch64.openPreA, VG.Proof.AesOcb.AArch64.oneFacts, VG.Proof.AesOcb.AArch64.aCtx, VG.Proof.AesOcb.AArch64.aNonce, VG.Proof.AesOcb.AArch64.aAad, VG.Proof.AesOcb.AArch64.aData,
        VG.Proof.AesOcb.AArch64.aTag, VG.Proof.AesOcb.AArch64.aWork, VG.Proof.AesOcb.AArch64.onePub, VG.Proof.AesOcb.AArch64.openOut, VG.Proof.AesOcb.AArch64.args, VG.Proof.AesOcb.AArch64.rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, VG.Proof.AesOcb.AArch64.openAArch64, VG.Proof.AesOcb.AArch64.openLeak, VG.Proof.AesOcb.AArch64.openPreA, VG.Proof.AesOcb.AArch64.oneFacts, VG.Proof.AesOcb.AArch64.aCtx, VG.Proof.AesOcb.AArch64.aNonce, VG.Proof.AesOcb.AArch64.aAad, VG.Proof.AesOcb.AArch64.aData,
        VG.Proof.AesOcb.AArch64.aTag, VG.Proof.AesOcb.AArch64.aWork, VG.Proof.AesOcb.AArch64.onePub, VG.Proof.AesOcb.AArch64.openOut, VG.Proof.AesOcb.AArch64.args, VG.Proof.AesOcb.AArch64.rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
        AArch64.stackArgAddr, List.getD, List.range, List.range.loop] [openSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesOcb.AArch64.openSat }

end VG.Proof.AesOcb.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.AArch64.Frame`. -/
section

/-!
# AES-OCB on AArch64, with its working space on the stack

Every function runs its code, proved with the working space as its last
argument (`Verified.lean`), in a frame that allocates it. `init`'s working
space is in a register (`x3`): its frame holds the 2560 bytes
(`Verified.stackScratch`). The working space of `seal` and `open` is their
third stack argument, after `tag` and `tag_len`, so their frame of 2592
bytes holds a copy of those two, the address of the working space and the
working space, at the next 16-byte boundary (`Verified.stackArgScratch`).
The code itself uses no stack: its calls keep the return address in `x30`.
`open`'s leak, whether it succeeds, reads only its buffers
(`openLeak_local`).
-/

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.Impl.AesOcb.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- A state satisfying `vg_aes_ocb_init`'s precondition, without the working
space. -/
def initFrameSat : State := { VG.Proof.AesOcb.AArch64.initSat with
                                           wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Ocb.initContract AArch64.abi 2560).pre s := by
  implies_sat [Spec.Ocb.initContract, Spec.Ocb.initSig, Spec.Ocb.initPre, Spec.Ocb.initPost,
    AArch64.abi, AArch64.argRegs] [initFrameSat, initSat] using VG.Proof.AesOcb.AArch64.initFrameSat

theorem init_framed (v : BlocksImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 2560 .x3 (init (VG.Proof.AesOcb.AArch64.callees v)))
      (Spec.Ocb.initContract AArch64.abi 2560) :=
  AArch64.Verified.stackScratch (sig := Spec.Ocb.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Ocb.initPre AArch64.abi.ptrBits) (post := Spec.Ocb.initPost AArch64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2560) (VG.Proof.AesOcb.AArch64.init_verified v) (by decide) (by decide)
    VG.Proof.AesOcb.AArch64.initFrameSat_pre

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def sealFrameSat : State :=
  { VG.Proof.AesOcb.AArch64.sealSat with
                 rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ocb.sealContract AArch64.abi 2592).pre s := by
  implies_sat [Spec.Ocb.sealContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Spec.Ocb.sealPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesOcb.AArch64.sealFrameSat

theorem seal_framed (v : BlocksImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («seal» (VG.Proof.AesOcb.AArch64.callees v)))
      (Spec.Ocb.sealContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ocb.sealPre AArch64.abi.ptrBits)
    (post := Spec.Ocb.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (VG.Proof.AesOcb.AArch64.seal_verified v) (by decide) (by decide) (Proof.AesOcb.sealPre_local _) (Proof.AesOcb.sealPost_local _)
    VG.Proof.AesOcb.AArch64.sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def openFrameSat : State :=
  { VG.Proof.AesOcb.AArch64.sealSat with
                 rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ocb.openContract AArch64.abi 2592).pre s := by
  implies_sat [Spec.Ocb.openContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Spec.Ocb.openPost,
    Spec.Ocb.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
    List.getD, List.range, List.range.loop] [openFrameSat, sealSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using VG.Proof.AesOcb.AArch64.openFrameSat

theorem open_framed (v : BlocksImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («open» (VG.Proof.AesOcb.AArch64.callees v)))
      (Spec.Ocb.openContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ocb.openPre AArch64.abi.ptrBits)
    (post := Spec.Ocb.openPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (leak := some (Spec.Ocb.openLeak AArch64.abi.ptrBits))
    (VG.Proof.AesOcb.AArch64.open_verified v) (by decide) (by decide) (Proof.AesOcb.openPre_local _)
    (Proof.AesOcb.openPost_local _) VG.Proof.AesOcb.AArch64.openFrameSat_pre (hleak := Proof.AesOcb.openLeak_local _)

end VG.Proof.AesOcb.AArch64

end
