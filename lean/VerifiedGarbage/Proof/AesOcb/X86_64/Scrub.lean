module

public import VerifiedGarbage.Impl.AesOcb.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
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

/-- `vg_aes_ocb_init` over `v`, as emitted (`Impl.AesOcb.X86_64.Fn.init`), in a frame of only
the bytes it writes itself over an implementation whose encryption and key
expansion need no working space (`BlocksImpl.free`), meets its contract in
constant time and returns without secret residue: its code is its code over
a stub, with `v`'s where it calls it (`Fill`). -/
theorem ocbInit_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed target (Impl.AesOcb.X86_64.Fn.init v.level v.free.isSome (Proof.AesOcb.X86_64.callees v))
      (Spec.Ocb.initApi.contract X86_64.abi (if v.free.isSome then 40 else 2576)) 0 := by
  have := v.encSide
  have := v.decSide
  have := v.expandSide
  unfold Impl.AesOcb.X86_64.Fn.init
  rcases hf : v.free with _ | f
  · simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte]
    exact verifiedScrubbedAllFill (api := Spec.Ocb.initApi) (ks := 0) (n := fun _ => 0)
      (a := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesOcb.X86_64.init ⟨⟨"", .block []⟩, ⟨"", .block []⟩, ⟨"", .block []⟩⟩))
      { suffix := v.suffix
        code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesOcb.X86_64.init ⟨v.enc, v.dec, v.expand⟩)
        stack := 2576
        verified := Proof.AesOcb.X86_64.init_framed v
        spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.AesOcb.X86_64.init_spSafe v) }
      v.level (ocbInitOut _) (by fill_calls) (Nat.zero_le _) (Nat.le_refl _)
  · simp only [Option.isSome, ↓reduceIte]
    exact verifiedScrubbedAllFill (api := Spec.Ocb.initApi) (ks := 0) (n := fun _ => 0)
      (a := Impl.StackScratch.X86_64.withStackScratch 32 .rcx (Impl.AesOcb.X86_64.init ⟨⟨"", .block []⟩, ⟨"", .block []⟩, ⟨"", .block []⟩⟩))
      { suffix := v.suffix
        code := Proof.Aes.X86_64.ocbInitCodeF v.enc v.dec v.expand
        stack := 40
        verified := Proof.AesOcb.X86_64.initF_framed v f
        spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.AesOcb.X86_64.init_spSafe v) }
      v.level (ocbInitOut _) (by unfold Proof.Aes.X86_64.ocbInitCodeF; fill_calls) (Nat.zero_le _) (Nat.le_refl _)

theorem ocbInit_spSafeFn (v : BlocksImpl) :
    (Impl.AesOcb.X86_64.Fn.init v.level v.free.isSome (Proof.AesOcb.X86_64.callees v)).all
      (fun i => !VG.X86_64.isa.writesSp i) = true := by
  unfold Impl.AesOcb.X86_64.Fn.init
  split
  · exact scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (Proof.AesOcb.X86_64.init_spSafe v))
  · exact scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (Proof.AesOcb.X86_64.init_spSafe v))

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

/-- `Spec.Ocb.sealApi`'s function over `v`, as emitted (`Impl.AesOcb.X86_64.Fn.«seal»`), its frame wiped
whole on return. -/
theorem seal_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed target (Impl.AesOcb.X86_64.Fn.«seal» v.level (Proof.AesOcb.X86_64.callees v))
      (Spec.Ocb.sealApi.contract X86_64.abi 3640) 0 := by
  have := v.encSide
  have := v.decSide
  have := v.expandSide
  exact verifiedScrubbedAllFill (api := Spec.Ocb.sealApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackArgScratch 3632 4 (Impl.AesOcb.X86_64.«seal» ⟨⟨"", .block []⟩, ⟨"", .block []⟩, ⟨"", .block []⟩⟩))
    { suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 3632 4 (Impl.AesOcb.X86_64.«seal» (Proof.AesOcb.X86_64.callees v))
      verified := Proof.AesOcb.seal_keyed (Proof.AesOcb.X86_64.seal_framed v)
      spSafe := VG.X86_64.withStackArgScratch_spSafe (Proof.AesOcb.X86_64.seal_spSafe v) }
    v.level (sealOut _) (by unfold Proof.AesOcb.X86_64.callees; fill_calls) (Nat.zero_le _) (Nat.le_refl _)

theorem seal_spSafeFn (v : BlocksImpl) :
    (Impl.AesOcb.X86_64.Fn.«seal» v.level (Proof.AesOcb.X86_64.callees v)).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (VG.X86_64.withStackArgScratch_spSafe (Proof.AesOcb.X86_64.seal_spSafe v))

/-- `Spec.Ocb.openApi`'s function over `v`, as emitted (`Impl.AesOcb.X86_64.Fn.«open»`), its frame wiped
whole on return. -/
theorem open_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed target (Impl.AesOcb.X86_64.Fn.«open» v.level (Proof.AesOcb.X86_64.callees v))
      (Spec.Ocb.openApi.contract X86_64.abi 3640) 32 := by
  have := v.encSide
  have := v.decSide
  have := v.expandSide
  exact verifiedScrubbedAllFill (api := Spec.Ocb.openApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackArgScratch 3632 4 (Impl.AesOcb.X86_64.«open» ⟨⟨"", .block []⟩, ⟨"", .block []⟩, ⟨"", .block []⟩⟩))
    { suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 3632 4 (Impl.AesOcb.X86_64.«open» (Proof.AesOcb.X86_64.callees v))
      verified := Proof.AesOcb.open_keyed (Proof.AesOcb.X86_64.open_framed v)
      spSafe := VG.X86_64.withStackArgScratch_spSafe (Proof.AesOcb.X86_64.open_spSafe v) }
    v.level (openOut _) (by unfold Proof.AesOcb.X86_64.callees; fill_calls) (Nat.zero_le _) (Nat.le_refl _)

theorem open_spSafeFn (v : BlocksImpl) :
    (Impl.AesOcb.X86_64.Fn.«open» v.level (Proof.AesOcb.X86_64.callees v)).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (VG.X86_64.withStackArgScratch_spSafe (Proof.AesOcb.X86_64.open_spSafe v))

end VG.Proof.AesOcb.X86_64.Scrub
