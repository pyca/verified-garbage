module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesOcb.X86.Frame
public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
public import VerifiedGarbage.Spec.Ocb.Contract
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.AesOcb.X86
import VerifiedGarbage.Proof.AesOcb.Scratch
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesOcb.X86.Frame
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
meta import VerifiedGarbage.Spec.Ocb.Contract
meta import VerifiedGarbage.Proof.AesOcb.Scratch
meta import VerifiedGarbage.Proof.Aes.ScrubLocal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.AesOcb.X86

/-!
# AES-OCB on x86 (32-bit), without secret residue

`vg_aes_ocb_init`, `vg_aes_ocb_seal` and `vg_aes_ocb_open` read the memory
on return only within the key context, the data and the tag (`initOut`,
`sealOut`, `openOut`), as on PPC64LE (`Proof/AesOcb/PPC64LE/Scrub.lean`):
what the scrub of their frames and calls needs (`X86.Scrub.PostOut`).
`init`'s does for a key of a length its precondition allows
(`postOut_of_local_pre`).

Each as emitted (`Impl.AesOcb.X86.Fn`) zeroes the stack of its contract
below `esp` (its frame of working space, `withStackScratch`, and its
callees') and clears the registers, and returns without secret residue
(`X86.Scrub.verifiedScrubbedF`: `init_scrubbed`, `seal_scrubbed`,
`open_scrubbed`). What that needs of the code (`scrubFSide`) holds whatever the
implementation of the block functions (`init_scrub`, …): from OCB's code
with stub block functions, whose code is `.block []`, which the kernel
evaluates once (`init_side`, …), the implementation's own facts
(`BlocksImpl.encScrub`, …), and `Fill`, which `fill_calls` proves by walking
only OCB's code.
-/

@[expose] public section

namespace VG.Proof.AesOcb.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Aes.ScrubLocal

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers when the precondition holds. -/
theorem postOut_of_local_pre {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      Curry.apply (sig.words A.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -, -, -, hpre⟩ := hs
    have hpre' : Curry.apply (sig.words A.ptrBits) pre (vals s) (A.mem s) := by
      cases hal : A.alignsBufs
      · rw [hal] at hpre; exact hpre
      · rw [hal] at hpre; exact hpre.1
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hA.mem] at hpre'
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) hpre' (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

/-- A length argument, which the contract reads as its low 32 bits, is at
most the bytes of the buffer `Sig.bufs` gives it. -/
private theorem len_le1 (x : BitVec 64) : (x.setWidth abi.ptrBits).toNat ≤ x.toNat * Elem.u8.size := by
  rw [BitVec.toNat_setWidth, show Elem.u8.size = 1 from rfl, Nat.mul_one]
  exact Nat.mod_le _ _

theorem initOut (stack : Nat) :
    PostOut (Spec.Ocb.initContract abi stack) (Spec.Ocb.initSig.retBits 32) :=
  postOut_of_local_pre (leak := none) ScrubAbi.plain (Proof.AesOcb.initPostOut_local _)

theorem sealOut (stack : Nat) :
    PostOut (Spec.Ocb.sealContract abi stack) (Spec.Ocb.sealSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [cp, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ocb.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr,
        ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits]
        (Spec.Ocb.sealPost abi.ptrBits) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr,
        ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits]
        (Spec.Ocb.sealPost abi.ptrBits) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ocb.sealPost, ArgWord.ofRaw] at h ⊢
      intro key hk
      rw [h key hk, bytesAt_of0 hb.2.2.2.1 (len_le1 dl), bytesAt_of0 hb.2.2.2.2 (len_le1 tl)]

theorem openOut (stack : Nat) :
    PostOut (Spec.Ocb.openContract abi stack) (Spec.Ocb.openSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [cp, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ocb.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr,
        ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits]
        (Spec.Ocb.openPost abi.ptrBits) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr,
        ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits]
        (Spec.Ocb.openPost abi.ptrBits) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ocb.openPost, ArgWord.ofRaw] at h ⊢
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (len_le1 dl)]
      exact h key hk

/-! ## What the scrub needs of the code -/

open Impl.StackScratch.X86 (withStackScratch)
open Proof.Aes.X86 (BlocksImpl)

/-- Block functions and key expansion with no code. -/
def stubCallees : Impl.AesOcb.X86.Callees := ⟨⟨"", .block []⟩, ⟨"", .block []⟩, ⟨"", .block []⟩⟩

-- OCB's own code, with the stubs, as literals for the kernel's evaluation.
materialize_code initStub := withStackScratch 2580 3 (Impl.AesOcb.X86.init stubCallees)
materialize_code sealStub := withStackScratch 2608 10 (Impl.AesOcb.X86.seal stubCallees)
materialize_code openStub := withStackScratch 2608 10 (Impl.AesOcb.X86.open stubCallees)

theorem init_side : scrubFSide (withStackScratch 2580 3 (Impl.AesOcb.X86.init stubCallees)) [] 2604 = true := by
  lit_decide

theorem seal_side : scrubFSide (withStackScratch 2608 10 (Impl.AesOcb.X86.seal stubCallees)) [] 2632 = true := by
  lit_decide

theorem open_side : scrubFSide (withStackScratch 2608 10 (Impl.AesOcb.X86.open stubCallees)) [] 2632 = true := by
  lit_decide

theorem init_fill (e d k : Impl.AesGcm.X86.Fn) (he : calleeSide e.code 0 = true)
    (hk : calleeSide k.code 0 = true) :
    Fill 0 (withStackScratch 2580 3 (Impl.AesOcb.X86.init stubCallees))
      (withStackScratch 2580 3 (Impl.AesOcb.X86.init ⟨e, d, k⟩)) := by
  fill_calls

theorem seal_fill (e d k : Impl.AesGcm.X86.Fn) (he : calleeSide e.code 0 = true) :
    Fill 0 (withStackScratch 2608 10 (Impl.AesOcb.X86.seal stubCallees))
      (withStackScratch 2608 10 (Impl.AesOcb.X86.seal ⟨e, d, k⟩)) := by
  fill_calls

theorem open_fill (e d k : Impl.AesGcm.X86.Fn) (he : calleeSide e.code 0 = true)
    (hd : calleeSide d.code 0 = true) :
    Fill 0 (withStackScratch 2608 10 (Impl.AesOcb.X86.open stubCallees))
      (withStackScratch 2608 10 (Impl.AesOcb.X86.open ⟨e, d, k⟩)) := by
  fill_calls

/-- `scrubFSide` of `vg_aes_ocb_init`, whatever the implementation. -/
theorem init_scrub (v : BlocksImpl) :
    scrubFSide (withStackScratch 2580 3 (Impl.AesOcb.X86.init (callees v))) [] 2604 = true :=
  scrubFSide_of_fill (init_fill _ _ _ (calleeSide_of_eq v.encStack v.encScrub)
    (calleeSide_of_eq v.expandStack v.expandScrub)) init_side

/-- `scrubFSide` of `vg_aes_ocb_seal`, whatever the implementation. -/
theorem seal_scrub (v : BlocksImpl) :
    scrubFSide (withStackScratch 2608 10 (Impl.AesOcb.X86.seal (callees v))) [] 2632 = true :=
  scrubFSide_of_fill (seal_fill _ _ _ (calleeSide_of_eq v.encStack v.encScrub)) seal_side

/-- `scrubFSide` of `vg_aes_ocb_open`, whatever the implementation. -/
theorem open_scrub (v : BlocksImpl) :
    scrubFSide (withStackScratch 2608 10 (Impl.AesOcb.X86.open (callees v))) [] 2632 = true :=
  scrubFSide_of_fill (open_fill _ _ _ (calleeSide_of_eq v.encStack v.encScrub)
    (calleeSide_of_eq v.decStack v.decScrub)) open_side

/-! ## The functions as emitted -/

/-- `vg_aes_ocb_init` over `v` as emitted (`Impl.AesOcb.X86.Fn.init`)
meets its contract in constant time and returns without secret residue. -/
theorem init_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed X86.target (Impl.AesOcb.X86.Fn.init (Proof.AesOcb.X86.callees v))
      (Spec.Ocb.initContract X86.abi 2604) 0 :=
  verifiedScrubbedF (api := Spec.Ocb.initApi) {
      suffix := v.suffix
      code := withStackScratch 2580 3 (Impl.AesOcb.X86.init (callees v))
      verified := init_framed v
      spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (init_spSafe v) }
    (initOut _) (W := 2604) (hs := init_scrub v)

/-- `vg_aes_ocb_seal` over `v` as emitted (`Impl.AesOcb.X86.Fn.«seal»`)
meets its contract in constant time and returns without secret residue. -/
theorem seal_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed X86.target (Impl.AesOcb.X86.Fn.«seal» (Proof.AesOcb.X86.callees v))
      (Spec.Ocb.sealContract X86.abi 2632) 0 :=
  verifiedScrubbedF (api := Spec.Ocb.sealApi) {
      suffix := v.suffix
      code := withStackScratch 2608 10 (Impl.AesOcb.X86.seal (callees v))
      verified := Proof.AesOcb.seal_keyed (seal_framed v)
      spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (seal_spSafe v) }
    (sealOut _) (W := 2632) (hs := seal_scrub v)

/-- `vg_aes_ocb_open` over `v` as emitted (`Impl.AesOcb.X86.Fn.«open»`)
meets its contract in constant time and returns without secret residue. -/
theorem open_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed X86.target (Impl.AesOcb.X86.Fn.«open» (Proof.AesOcb.X86.callees v))
      (Spec.Ocb.openContract X86.abi 2632) 32 :=
  verifiedScrubbedF (api := Spec.Ocb.openApi) {
      suffix := v.suffix
      code := withStackScratch 2608 10 (Impl.AesOcb.X86.open (callees v))
      verified := Proof.AesOcb.open_keyed (open_framed v)
      spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (open_spSafe v) }
    (openOut _) (W := 2632) (hs := open_scrub v)

/-- The code as emitted, `c` and then its cleanup, writes `esp` only in its
frames and calls, as `c` does. -/
theorem scrubF_spSafe {rb W : Nat} {c : Prog X86.isa} (h : c.all (fun i => !X86.isa.writesSp i) = true) :
    (Impl.Scrub.X86.scrubF rb W c).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [Impl.Scrub.X86.scrubF, Impl.Scrub.X86.wipeBelow, Code.all, h, zeroRegs_all, tail_all,
    Bool.true_and, Bool.and_true]
  exact wipe_all _

/-- `Impl.AesOcb.X86.Fn.init` writes `esp` only in its frames and calls. -/
theorem init_fnSpSafe (v : BlocksImpl) :
    (Impl.AesOcb.X86.Fn.init (Proof.AesOcb.X86.callees v)).all (fun i => !X86.isa.writesSp i) = true :=
  scrubF_spSafe (Proof.CmacAes.Stream.X86.withStackScratch_spSafe (init_spSafe v))

/-- `Impl.AesOcb.X86.Fn.«seal»` writes `esp` only in its frames and calls. -/
theorem seal_fnSpSafe (v : BlocksImpl) :
    (Impl.AesOcb.X86.Fn.«seal» (Proof.AesOcb.X86.callees v)).all (fun i => !X86.isa.writesSp i) = true :=
  scrubF_spSafe (Proof.CmacAes.Stream.X86.withStackScratch_spSafe (seal_spSafe v))

/-- `Impl.AesOcb.X86.Fn.«open»` writes `esp` only in its frames and calls. -/
theorem open_fnSpSafe (v : BlocksImpl) :
    (Impl.AesOcb.X86.Fn.«open» (Proof.AesOcb.X86.callees v)).all (fun i => !X86.isa.writesSp i) = true :=
  scrubF_spSafe (Proof.CmacAes.Stream.X86.withStackScratch_spSafe (open_spSafe v))

end VG.Proof.AesOcb.X86.Scrub
