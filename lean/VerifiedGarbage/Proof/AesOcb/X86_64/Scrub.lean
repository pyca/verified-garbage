module

public import VerifiedGarbage.Spec.Ocb.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant
public import VerifiedGarbage.Proof.AesOcb.X86_64.Frame
public import VerifiedGarbage.Proof.AesOcb.Scratch
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Aes.X86_64.Scrub
import VerifiedGarbage.Proof.Aes.X86_64.ModesScrub
import VerifiedGarbage.Proof.Aes.ScrubLocal

/-!
# AES-OCB's key setup on x86-64, without secret residue

`vg_aes_ocb_init` over an implementation of the AES block functions
(`Aes.X86_64.BlocksImpl`) whose encryption and key expansion need no working
space (`BlocksImpl.free`), in a frame of only the 24 bytes it writes itself
(`initF_framed`), followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`) where the implementation gives its residue
analysis (`BlocksImpl.ocbInitRes`). Over the others, as before, in a frame of
2.5 KB, of which the analysis cannot tell what may hold secrets. Over the others, that frame is mostly the
working space of the functions called, wiped whole on return
(`X86_64.Scrub.withScrubAll`). Its postcondition reads the memory on return
only within the key context, for a key of the lengths the precondition
allows (`X86_64.Scrub.PostOut`).

`vg_aes_ocb_seal` and `vg_aes_ocb_open` over an implementation that needs
working space: their frame of 3632 bytes is that working space, the offsets,
the checksum, the table of `L_j` and blocks of the data XORed with offsets,
so it is wiped whole on return (`RScrub.withScrubAllC`, `sealReg`,
`openReg`). Their postconditions read the
memory on return only within the data and the tag (`sealOut`, `openOut`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Proof.Aes.X86_64

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
      · rw [Proof.Aes.ScrubLocal.bytesAt_of0 hb.2 ?_]
        · exact h1
        · simp only [Spec.Aes.bytesAt, List.length_map, List.length_range, Spec.Aes.rounds, Elem.size]
          rcases hpre with h | h | h <;> rw [h] <;> decide
      · simp only [Spec.Ocb.ctxLstar, Spec.Ocb.blockAtMem] at h2 ⊢
        rw [show (240 : BitVec 64) = BitVec.ofNat 64 240 from rfl] at h2 ⊢
        rw [Proof.Aes.ScrubLocal.bytesAt_of hb.2 (by decide)]
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
    | [cp, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
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
      rw [h key hk, Proof.Aes.ScrubLocal.bytesAt_of0 hb.2.2.2.1 (by simp),
        Proof.Aes.ScrubLocal.bytesAt_of0 hb.2.2.2.2 (by simp)]

theorem openOut (stack : Nat) :
    PostOut (Spec.Ocb.openContract X86_64.abi stack) (Spec.Ocb.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [cp, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
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
      rw [Proof.Aes.ScrubLocal.bytesAt_of0 hb.2.2.2.1 (by simp)]
      exact h key hk

/-- `vg_aes_ocb_seal` over `v`: over an implementation of AES that needs
working space (`BlocksImpl.free` is `none`), its frame wiped whole on return,
in 16-byte stores that are all aligned (the chunks `[8, 3632]`); over the
others, as before. -/
def sealReg (v : BlocksImpl) : Registration Spec.Ocb.sealApi X86_64.target :=
  let r : Registration Spec.Ocb.sealApi X86_64.target := {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 3632 4
      (Impl.AesOcb.X86_64.seal (Proof.AesOcb.X86_64.callees v))
    verified := Proof.AesOcb.seal_keyed (Proof.AesOcb.X86_64.seal_framed v)
    spSafe := VG.X86_64.withStackArgScratch_spSafe (Proof.AesOcb.X86_64.seal_spSafe v) }
  match v.free with
  | some _ => r
  | none => RScrub.withScrubAllC r (sealOut _) [8, 3632]

/-- `vg_aes_ocb_open` over `v`: over an implementation of AES that needs
working space (`BlocksImpl.free` is `none`), its frame wiped whole on return,
in 16-byte stores that are all aligned (the chunks `[8, 3632]`); over the
others, as before. -/
def openReg (v : BlocksImpl) : Registration Spec.Ocb.openApi X86_64.target :=
  let r : Registration Spec.Ocb.openApi X86_64.target := {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 3632 4
      (Impl.AesOcb.X86_64.open (Proof.AesOcb.X86_64.callees v))
    verified := Proof.AesOcb.open_keyed (Proof.AesOcb.X86_64.open_framed v)
    spSafe := VG.X86_64.withStackArgScratch_spSafe (Proof.AesOcb.X86_64.open_spSafe v) }
  match v.free with
  | some _ => r
  | none => RScrub.withScrubAllC r (openOut _) [8, 3632]

end VG.Proof.AesOcb.X86_64.Scrub
