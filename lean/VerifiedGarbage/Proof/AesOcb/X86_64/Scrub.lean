module

public import VerifiedGarbage.Spec.Ocb.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant
public import VerifiedGarbage.Proof.AesOcb.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Aes.X86_64.Scrub
import VerifiedGarbage.Proof.Aes.X86_64.ModesScrub

/-!
# AES-OCB on x86-64, without secret residue

`vg_aes_ocb_init` over an implementation of the AES block functions
(`Aes.X86_64.BlocksImpl`) whose encryption and key expansion need no working
space (`BlocksImpl.free`), in a frame of only the 24 bytes it writes itself
(`initF_framed`), followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`) where the implementation gives its residue
analysis (`BlocksImpl.ocbInitRes`). Over the others, in a frame of 2.5 KB
(below). Its postcondition reads the memory on return only within the key context, for a
key of the lengths the precondition allows (`X86_64.Scrub.PostOut`).

`vg_aes_ocb_init`, `vg_aes_ocb_seal` and `vg_aes_ocb_open` over an
implementation whose encryption needs working space (`BlocksImpl.encWritten`
is not 0): their frames of 2.5 and 3.6 KB, mostly that working space, wiped
whole on return (`X86_64.Scrub.withScrubAll`). Over the others, `seal` and
`open` as before: their table of `L_j` alone is 1 KB.
-/

@[expose] public section

namespace VG.Proof.AesOcb.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Proof.Aes.X86_64
open VG.Proof.AesOcb.X86_64 (callees seal_framed open_framed seal_spSafe open_spSafe)

theorem ocbInitOut (stack : Nat) :
    PostOut (Spec.Ocb.initContract X86_64.abi stack) (Spec.Ocb.initSig.retBits 64) :=
  Proof.Aes.X86_64.Scrub.postOut_of_local_pre fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [k, ln, ctx], _ =>
      simp only [Spec.Ocb.initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      change Spec.Ocb.KeyRepr m₁ ctx _ at h
      change Spec.Ocb.KeyRepr m₂ ctx _
      change _ ∨ _ at hpre
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ?_⟩
      · rw [ModesScrub.bytesAt_of0 hb.2 ?_]
        · exact h1
        · simp only [Spec.Aes.bytesAt, List.length_map, List.length_range, Spec.Aes.rounds, Elem.size]
          rcases hpre with h | h | h <;> rw [h] <;> decide
      · simp only [Spec.Ocb.ctxLstar, Spec.Ocb.blockAtMem] at h2 ⊢
        rw [show (240 : BitVec 64) = BitVec.ofNat 64 240 from rfl] at h2 ⊢
        rw [ModesScrub.bytesAt_of hb.2 (by decide)]
        exact h2

open VG.X86_64.RScrub in
/-- `vg_aes_ocb_init` over `v`: with no working space for an implementation
whose encryption and key expansion need none (`BlocksImpl.free`), and then
without secret residue where the analysis handles it. -/
def ocbInitReg (v : BlocksImpl) : Registration Spec.Ocb.initApi X86_64.target :=
  match v.free with
  | some f =>
    withScrub {
      suffix := v.suffix
      code := Proof.Aes.X86_64.ocbInitCodeF v.enc v.dec v.expand
      stack := 40
      verified := Proof.AesOcb.X86_64.initF_framed v f
      spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.AesOcb.X86_64.init_spSafe v) }
      (ocbInitOut _) [] (pubOk_nil _) v.ocbInitRes
  | none =>
    withScrubAll {
      suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesOcb.X86_64.init ⟨v.enc, v.dec, v.expand⟩)
      stack := 2576
      verified := Proof.AesOcb.X86_64.init_framed v
      spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.AesOcb.X86_64.init_spSafe v) }
      (ocbInitOut _)

theorem sealOut (stack : Nat) :
    PostOut (Spec.Ocb.sealContract X86_64.abi stack) (Spec.Ocb.sealSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ocb.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ocb.sealPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ocb.sealPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ocb.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, ModesScrub.bytesAt_of0 hb.2.2.2.1 (by simp), ModesScrub.bytesAt_of0 hb.2.2.2.2 (by simp)]

theorem openOut (stack : Nat) :
    PostOut (Spec.Ocb.openContract X86_64.abi stack) (Spec.Ocb.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ocb.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ocb.openPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ocb.openPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ocb.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [ModesScrub.bytesAt_of0 hb.2.2.2.1 (by simp)]
      exact h key hk

/-- `vg_aes_ocb_seal` over `v`: over an implementation whose encryption needs
working space, wiped whole on return (`withScrubAll`); over the others, as
before. -/
def sealReg (v : BlocksImpl) : Registration Spec.Ocb.sealApi X86_64.target :=
  let r : Registration Spec.Ocb.sealApi X86_64.target := {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 3632 4 (Impl.AesOcb.X86_64.seal (callees v))
    stack := 3640
    verified := Proof.AesOcb.seal_keyed (seal_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (seal_spSafe v) }
  if v.encWritten = 0 then r else withScrubAll r (sealOut _)

/-- `vg_aes_ocb_open` over `v`, as `sealReg`. -/
def openReg (v : BlocksImpl) : Registration Spec.Ocb.openApi X86_64.target :=
  let r : Registration Spec.Ocb.openApi X86_64.target := {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 3632 4 (Impl.AesOcb.X86_64.open (callees v))
    stack := 3640
    verified := Proof.AesOcb.open_keyed (open_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (open_spSafe v) }
  if v.encWritten = 0 then r else withScrubAll r (openOut _)

end VG.Proof.AesOcb.X86_64.Scrub
