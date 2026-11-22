module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Spec.HmacTable
public import VerifiedGarbage.Proof.HashTable.Basic
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE
public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.InitAny
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Instance
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.InitLong

/-!
# Tables of the interface `Hmac` on PPC64LE

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Reduce.lean`), for the hash functions with
HMAC on PPC64LE, MD5, SHA-1 and the SHA-2 family, one implementation of each
(`vars`, `PPC64LE/Vars.lean`): the table of a hash function (`tableOf`, `VG_HMAC_<HASH>`) holds
the addresses of HMAC's `init` for a key of any length
(`vg_hmac_<hash>_init_any_scratch`, `Hash.initAny`) and `finalize` and of
the streaming `update`, in the forms that take their working space as an
argument (`_scratch`, in `r7`), then its data (`Spec.HmacTable.dataOf`: the
hash function's index in `Mgf1.hashes`, its digest length and HMAC's block
size); the tables of a list of them (`tables`); and the functions an
indirect call of each of a table's functions may reach (`fnsOf`).

Word 0 (`HVar.anyV`) meets `anyScratchContract`: `initAnyKeyContract` with
the working space of the instance's functions (`Instance.scratch`
doublewords, which `initLong`'s, `Hash.lbytes`, fits in) and 144 bytes of
stack, from the proofs of `init` and `initLong` (`initAnyScratch`, by
`Verified.entryBranch`). For a key of at most a block it runs `init` alone,
inline, and so meets `init`'s contract, with 96 bytes of stack
(`HVar.shortV`), and changes only what `init` may (`HVar.shortFr`): a caller
whose key is that short (deterministic ECDSA's `K`) calls it as it would
`init`.

A function's proof runs the code of whichever of these the table holds
(`TabOK`): the first function of `fnsOf vs` at the address called, which is
the table's function of that name (`tabOK_of`), when the functions of
distinct names are at distinct addresses (as `Abi.withTables` says) and the
functions of the same name have the same code (`Coh`, which the registration
checks). `held_tableOf` reads a table's words, and `hashAt_tableOf` the hash
function it names.
-/

@[expose] public section

namespace VG.Proof.HmacTable.PPC64LE

open VG VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Impl.RsaOaep.PPC64LE (Fns)
open VG.Proof.HashTable (pw_ne find_name)

/-! ## HMAC's `init` for a key of any length, with its working space as an argument -/

/-- `VG.Spec.Hmac.initAnyKeyContract` with its working space passed in
`scratch` (`n` doublewords), as `Proof.Hmac.initScratchContract` is
`initContract`'s: the contract of word 0 of a table (`Hash.initAny`), with
the 144 bytes of stack a long key's path uses (`initLong`'s frame, `init`'s
and the streaming functions'). -/
def anyScratchContract (S : Spec.Hmac.StreamingHash) (n : Nat) : Contract isa :=
  (Proof.Hmac.initScratchSig S n).contract PPC64LE.abi
    (post := fun inner outer key keyLen _scratch => Spec.Hmac.initPost S PPC64LE.abi.ptrBits inner outer key keyLen)
    (writeArgs := true) (stack := 144)

open VG.Proof.Hmac.Stream.PPC64LE (longG)
open VG.Proof.Hmac.Stream.PPC64LE.Shared (longScratchContract longPre longImp Ran entry_run)

/-- `initLong` with its working space in `scratch` (`n` doublewords, of
which it uses `lbytes` bytes), given its constant time. -/
theorem longScratchAt {H : Hash} (hH : HashOK H) {n : Nat} (hfit : H.lbytes ≤ 8 * n)
    (ct : ConstantTime isa (longG hH.SH H.lbytes 144).pre (longG hH.SH H.lbytes 144).pub H.initLong)
    (hs : ∃ s, (longScratchContract hH.SH n).pre s) :
    Verified PPC64LE.target H.initLong (longScratchContract hH.SH n) := by
  have imp := longImp hH.SH n hs
  have wide : ∀ s, (longG hH.SH (8 * n) 144).pre s →
      (longG hH.SH H.lbytes 144).pre (s.withRegions s.rd [⟨s.gpr .r3, hH.SH.stateBytes⟩,
        ⟨s.gpr .r4, hH.SH.stateBytes⟩, ⟨s.gpr .r7, H.lbytes⟩]) := by
    intro s ⟨h0, h1, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
    exact ⟨h0, h1, rfl, h3, h4.sub_right (Region.sub_prefix hfit), h5.sub_right (Region.sub_prefix hfit),
      h6, h7, h8.sub_right (Region.sub_prefix hfit), h9, h10, h11, h12, h13.sub_right (Region.sub_prefix hfit)⟩
  have v : Verified PPC64LE.target H.initLong (longG hH.SH H.lbytes 144) :=
    ⟨fun s hs => by
      obtain ⟨t, s', he, h₁, h₂⟩ := Proof.Hmac.Stream.PPC64LE.InitLong.correct hH hs
      exact ⟨t, s', he, h₁, h₂⟩, ct, imp.sat_left.elim fun s h => ⟨_, wide s h⟩⟩
  refine (Verified.widen v (fun s => [⟨s.gpr .r3, hH.SH.stateBytes⟩, ⟨s.gpr .r4, hH.SH.stateBytes⟩,
      ⟨s.gpr .r7, H.lbytes⟩]) wide (fun _ h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h)
      imp.sat_left).of_implies imp
  obtain ⟨_, _, h2, _⟩ := h
  rw [h2]
  exact .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, hfit⟩ .nil))

/-- The stack below the stack pointer that `init`'s contract keeps apart
from the buffers, within the 144 bytes `anyScratchContract`'s does. -/
theorem stack96 {sp : Addr} {r : Region} (h : Region.Disjoint ⟨sp - BitVec.ofNat 64 144, 144⟩ r) :
    Region.Disjoint ⟨sp - BitVec.ofNat 64 96, 96⟩ r :=
  h.sub_left (below_sub (by decide) (by decide))

/-- `Hash.initAny`, against the contract of a table's word 0: `initLong`
for a key longer than a block, `init` otherwise, with the same working
space. -/
theorem initAnyScratch {H : Hash} {I : Spec.Hmac.Instance} {b : Nat} (hb : b = 6 ∨ b = 7)
    (hbB : I.S.H.blockSize = 2 ^ b)
    (hshort : Verified PPC64LE.target H.init (Proof.Hmac.Instance.initScratchContract I PPC64LE.abi 96))
    (hlong : Verified PPC64LE.target H.initLong (longScratchContract I.S I.scratch)) :
    Verified PPC64LE.target (H.initAny b) (anyScratchContract I.S I.scratch) := by
  have hp : ∀ r ∈ preserved, r ≠ .r11 ∧ r ≠ .r12 := by decide
  have hsat : ∃ s, (anyScratchContract I.S I.scratch).pre s := by
    obtain ⟨s, h⟩ := hlong.2.2
    refine ⟨s, ?_⟩
    sig_pre [longScratchContract, longPre, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, PPC64LE.abi,
      PPC64LE.argRegs] at h
    sig_pre [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs]
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, -⟩ := h
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩
  refine Verified.entryBranch (p := fun s => decide (2 ^ b < (s.gpr .r6).toNat))
    (fun _ => []) hlong hshort (fun s hs => ?_) ?_ hsat
  · obtain ⟨u, e, r, ev⟩ := entry_run hb s
    have g3 := r.g .r3 (by decide) (by decide)
    have g4 := r.g .r4 (by decide) (by decide)
    have g5 := r.g .r5 (by decide) (by decide)
    have g6 := r.g .r6 (by decide) (by decide)
    have g7 := r.g .r7 (by decide) (by decide)
    have abi : ∀ s', PPC64LE.target.abiPreserved u s' → PPC64LE.target.abiPreserved s s' := fun s' a =>
      ⟨fun x hx => by
        obtain ⟨h11, h12⟩ := hp x hx
        rw [a.1 x hx, r.g x h11 h12], by rw [a.2.1, r.sp], by rw [a.2.2, r.lr]⟩
    refine ⟨u, e, ev, fun hl => ⟨?_, fun s' a q => ⟨abi s' a, ?_⟩⟩, fun hl => ⟨?_, fun s' a q => ⟨abi s' a, ?_⟩⟩⟩
    · have hk : 2 ^ b < (s.gpr .r6).toNat := of_decide_eq_true hl
      sig_pre [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, PPC64LE.abi,
        PPC64LE.argRegs] at hs
      sig_pre [longScratchContract, longPre, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, PPC64LE.abi,
        PPC64LE.argRegs]
      rw [g3, g4, g5, g6, g7, r.sp, r.rd, r.wr, hbB]
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hs
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, hk⟩
    · sig_post [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs]
      sig_post [longScratchContract, longPre, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, PPC64LE.abi,
        PPC64LE.argRegs] at q
      rw [g3, g4, g5, g6, r.mem] at q; exact q
    · have hk : (s.gpr .r6).toNat ≤ 2 ^ b := by have := of_decide_eq_false hl; omega_using [this]
      sig_pre [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, PPC64LE.abi,
        PPC64LE.argRegs] at hs
      sig_pre [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig,
        Spec.Hmac.initPre, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs]
      rw [g3, g4, g5, g6, g7, r.sp, r.rd, r.wr, hbB]
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hs
      exact ⟨by omega_using [a1], a2, a3, a4, a5, a6, a7, a8, a9, stack96 a10, stack96 a11, stack96 a12,
        stack96 a13, a14, a15, a16, a17, hk⟩
    · sig_post [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs]
      sig_post [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig,
        Spec.Hmac.initPre, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs] at q
      rw [g3, g4, g5, g6, r.mem] at q; exact q
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨u₀, e₀, r, -⟩ := entry_run hb s
    obtain ⟨u₀', e₀', r', -⟩ := entry_run hb s'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    have hq' := hq
    sig_pub [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs] at hq'
    obtain ⟨qsp, q3, q4, q5, q6, q7⟩ := hq'
    have e3 := r.g .r3 (by decide) (by decide)
    have e4 := r.g .r4 (by decide) (by decide)
    have e5 := r.g .r5 (by decide) (by decide)
    have e6 := r.g .r6 (by decide) (by decide)
    have e7 := r.g .r7 (by decide) (by decide)
    have e3' := r'.g .r3 (by decide) (by decide)
    have e4' := r'.g .r4 (by decide) (by decide)
    have e5' := r'.g .r5 (by decide) (by decide)
    have e6' := r'.g .r6 (by decide) (by decide)
    have e7' := r'.g .r7 (by decide) (by decide)
    refine ⟨rfl, by rw [q6], fun _ => ?_, fun _ => ?_⟩
    · sig_pub [longScratchContract, longPre, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, PPC64LE.abi,
        PPC64LE.argRegs]
      rw [r.sp, r'.sp, e3, e3', e4, e4', e5, e5', e6, e6', e7, e7']
      exact ⟨qsp, q3, q4, q5, q6, q7⟩
    · sig_pub [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig,
        Spec.Hmac.initPre, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs]
      rw [r.sp, r'.sp, e3, e3', e4, e4', e5, e5', e6, e6', e7, e7']
      exact ⟨qsp, q3, q4, q5, q6, q7⟩

/-- A run of `Hash.initAny` for a key of at most a block runs `init` alone:
it changes memory only in the regions it may write and the 96 bytes of
stack below the stack pointer that `init` and its callees use. -/
theorem initAny_frame {H : Hash} (hH : HashOK H) {b : Nat} (hb : b = 6 ∨ b = 7) {s s' : State}
    {t : List Leak} (hk : (s.gpr .r6).toNat ≤ 2 ^ b) (he : Exec isa (H.initAny b) s t s') :
    Frame (s.wr ++ [below s.sp 96]) s.mem s'.mem := by
  obtain ⟨u, e, r, ev⟩ := entry_run hb s
  have hsd : sdepth H.init ≤ 96 := by
    have h₁ := sdepth_le_fdepth _ (Proof.Hmac.Stream.PPC64LE.InitLong.init_pf hH)
    have h₂ := Proof.Hmac.Stream.PPC64LE.InitLong.init_fdepth hH
    omega_using [h₁, h₂]
  unfold Hash.initAny Hash.initEntry at he
  cases he with
  | seq a i =>
    have x := Exec.block_eq (T := PPC64LE.target) a
    rw [e] at x
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj x)
    cases Exec.iteCold_iff.mp i with
    | iteT hc _ =>
      have hc' : eval (.nonzero .d .r12) u = some true := hc
      rw [ev, decide_eq_false (by omega_using [hk])] at hc'
      cases hc'
    | iteF _ r₁ =>
      have f := Exec.frameAny r₁ (by omega_using [hsd])
      rw [r.wr, r.sp, r.mem] at f
      exact Frame.below_mono f hsd (by decide)

/-- `Hash.initAny` against `init`'s contract, for a key of at most a block,
which it gives `init` alone, inline (`initAny_frame`): as `init_scratch`, so
that a caller with a key of at most a block (deterministic ECDSA's `K`) calls
a table's word 0 as it would `init`. -/
theorem initAnyShort {H : Hash} {I : Spec.Hmac.Instance} {b : Nat} (hb : b = 6 ∨ b = 7)
    (hbB : I.S.H.blockSize = 2 ^ b)
    (hshort : Verified PPC64LE.target H.init (Proof.Hmac.Instance.initScratchContract I PPC64LE.abi 96))
    (hlong : Verified PPC64LE.target H.initLong (longScratchContract I.S I.scratch)) :
    Verified PPC64LE.target (H.initAny b) (Proof.Hmac.Instance.initScratchContract I PPC64LE.abi 96) := by
  have hp : ∀ r ∈ preserved, r ≠ .r11 ∧ r ≠ .r12 := by decide
  refine Verified.entryBranch (p := fun s => decide (2 ^ b < (s.gpr .r6).toNat))
    (fun _ => []) hlong hshort (fun s hs => ?_) ?_ hshort.2.2
  · obtain ⟨u, e, r, ev⟩ := entry_run hb s
    have g3 := r.g .r3 (by decide) (by decide)
    have g4 := r.g .r4 (by decide) (by decide)
    have g5 := r.g .r5 (by decide) (by decide)
    have g6 := r.g .r6 (by decide) (by decide)
    have g7 := r.g .r7 (by decide) (by decide)
    have abi : ∀ s', PPC64LE.target.abiPreserved u s' → PPC64LE.target.abiPreserved s s' := fun s' a =>
      ⟨fun x hx => by
        obtain ⟨h11, h12⟩ := hp x hx
        rw [a.1 x hx, r.g x h11 h12], by rw [a.2.1, r.sp], by rw [a.2.2, r.lr]⟩
    sig_pre [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs] at hs
    have hk : (s.gpr .r6).toNat ≤ 2 ^ b := hbB ▸ hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    refine ⟨u, e, ev, fun hl => absurd hk (by have := of_decide_eq_true hl; omega_using [this]),
      fun _ => ⟨?_, fun s' a q => ⟨abi s' a, ?_⟩⟩⟩
    · sig_pre [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig,
        Spec.Hmac.initPre, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs]
      rw [g3, g4, g5, g6, g7, r.sp, r.rd, r.wr]
      exact hs
    · sig_post [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig,
        Spec.Hmac.initPre, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs]
      sig_post [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig,
        Spec.Hmac.initPre, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs] at q
      rw [g3, g4, g5, g6, r.mem] at q; exact q
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨u₀, e₀, r, -⟩ := entry_run hb s
    obtain ⟨u₀', e₀', r', -⟩ := entry_run hb s'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    have hq' := hq
    sig_pub [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs] at hq'
    obtain ⟨qsp, q3, q4, q5, q6, q7⟩ := hq'
    have e3 := r.g .r3 (by decide) (by decide)
    have e4 := r.g .r4 (by decide) (by decide)
    have e5 := r.g .r5 (by decide) (by decide)
    have e6 := r.g .r6 (by decide) (by decide)
    have e7 := r.g .r7 (by decide) (by decide)
    have e3' := r'.g .r3 (by decide) (by decide)
    have e4' := r'.g .r4 (by decide) (by decide)
    have e5' := r'.g .r5 (by decide) (by decide)
    have e6' := r'.g .r6 (by decide) (by decide)
    have e7' := r'.g .r7 (by decide) (by decide)
    refine ⟨rfl, by rw [q6], fun _ => ?_, fun _ => ?_⟩
    · sig_pub [longScratchContract, longPre, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, PPC64LE.abi,
        PPC64LE.argRegs]
      rw [r.sp, r'.sp, e3, e3', e4, e4', e5, e5', e6, e6', e7, e7']
      exact ⟨qsp, q3, q4, q5, q6, q7⟩
    · sig_pub [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig,
        Spec.Hmac.initPre, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs]
      rw [r.sp, r'.sp, e3, e3', e4, e4', e5, e5', e6, e6', e7, e7']
      exact ⟨qsp, q3, q4, q5, q6, q7⟩

/-- `initAny_frame`, from `init`'s precondition. -/
theorem initAnyShort_frame {H : Hash} (hH : HashOK H) {I : Spec.Hmac.Instance} {b : Nat} (hb : b = 6 ∨ b = 7)
    (hbB : I.S.H.blockSize = 2 ^ b) {s s' : State} {t : List Leak}
    (hs : (Proof.Hmac.Instance.initScratchContract I PPC64LE.abi 96).pre s) (he : Exec isa (H.initAny b) s t s') :
    Frame (s.wr ++ [below s.sp 96]) s.mem s'.mem := by
  sig_pre [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPre, Spec.Hmac.initPost, PPC64LE.abi, PPC64LE.argRegs] at hs
  exact initAny_frame hH hb (hbB ▸ hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) he

/-- A hash function's streaming functions (`H`, with what HMAC's proofs need
of them, `ok`, and their constant time, `ct`), the hash function of
`Spec.Mgf1` they compute (`G`) and its place in `Spec.Mgf1.hashes`, and its
HMAC `init` and `finalize` with their working space as an argument, verified
against the shared contracts of HMAC's instance `I` with 96 bytes of stack,
and `initLong` with the same working space (with 144: `init` calls the
streaming functions in a frame of its own, `initLong` calls `init` in
another), from which `Hash.initAny`, a table's word 0, is verified
(`HVar.anyV`); `B = 2 ^ b`. -/
structure HVar where
  H : Hash
  ok : HashOK H
  ct : Proof.RsaOaep.PPC64LE.HashCT ok
  G : Spec.Mgf1.Hash
  hash : ∀ x, G.hash x = ok.SH.H.hash x
  len : G.len = H.D
  idx : Spec.Mgf1.hashes[Spec.HashTable.index G]? = some G
  I : Spec.Hmac.Instance
  hIS : I.S = ok.SH
  initV : Verified PPC64LE.target H.init (Proof.Hmac.Instance.initScratchContract I PPC64LE.abi 96)
  finV : Verified PPC64LE.target H.finalize (Proof.Hmac.Instance.finalizeScratchContract I PPC64LE.abi 96)
  b : Nat
  hb : b = 6 ∨ b = 7
  hbB : I.S.H.blockSize = 2 ^ b
  longV : Verified PPC64LE.target H.initLong (longScratchContract I.S I.scratch)

namespace HVar

variable (w : HVar)

/-- HMAC's `init` for a key of any length with its working space as an
argument, word 0 of the table. -/
def initN : String := s!"vg_hmac_{w.I.rust}_init_any_scratch"

/-- Its code. -/
def initC : Prog isa := w.H.initAny w.b

/-- HMAC's `finalize` with its working space as an argument. -/
def finN : String := s!"vg_hmac_{w.I.rust}_finalize_scratch"

/-- A table's word 0 meets the contract of `init` for a key of any length,
with the working space of `I`'s functions. -/
theorem anyV : Verified PPC64LE.target w.initC (anyScratchContract w.I.S w.I.scratch) :=
  initAnyScratch w.hb w.hbB w.initV w.longV

/-- For a key of at most a block, it meets `init`'s contract, with 96 bytes
of stack. -/
theorem shortV : Verified PPC64LE.target w.initC (Proof.Hmac.Instance.initScratchContract w.I PPC64LE.abi 96) :=
  initAnyShort w.hb w.hbB w.initV w.longV

/-- What a run of it with such a key changes. -/
theorem shortFr {s s' : State} {t : List Leak}
    (hs : (Proof.Hmac.Instance.initScratchContract w.I PPC64LE.abi 96).pre s) (he : Exec isa w.initC s t s') :
    Frame (s.wr ++ [below s.sp 96]) s.mem s'.mem :=
  initAnyShort_frame w.ok w.hb w.hbB hs he

end HVar

/-- The table of `w`'s HMAC, `VG_HMAC_<HASH>`. -/
def tableOf (w : HVar) : FnTable where
  name := s!"VG_HMAC_{w.G.rust.toUpper}"
  iface := Spec.HmacTable.iface
  fns := [w.initN, w.H.updN, w.finN]
  data := Spec.HmacTable.dataOf w.G

/-- The tables of `vs`. -/
def tables (vs : List HVar) : List FnTable := vs.map tableOf

/-- For each of a table's functions, that function of each of `vs`. -/
def fnsOf (vs : List HVar) : Fns :=
  ⟨vs.map fun w => (w.initN, w.initC), vs.map fun w => (w.H.updN, w.H.updC),
    vs.map fun w => (w.finN, w.H.finalize)⟩

/-- The functions of `tables vs`. -/
def names (vs : List HVar) : List String := ((tables vs).map (·.fns)).flatten

/-- The functions of the same name have the same code. -/
def Coh (vs : List HVar) : Prop :=
  ∀ w ∈ vs, ∀ w' ∈ vs, (w.initN = w'.initN → w.initC = w'.initC) ∧
    (w.H.updN = w'.H.updN → w.H.updC = w'.H.updC) ∧ (w.finN = w'.finN → w.H.finalize = w'.H.finalize)

instance (vs : List HVar) : Decidable (Coh vs) := by unfold Coh; infer_instance

/-- An indirect call of `f`'s functions, at the addresses `sy` gives, to the
address of one of `w`'s HMAC functions reaches it. -/
structure TabOK (w : HVar) (f : Fns) (sy : String → Addr) : Prop where
  i : f.init.find? (fun q => sy q.1 == sy w.initN) = some (w.initN, w.initC)
  u : f.upd.find? (fun q => sy q.1 == sy w.H.updN) = some (w.H.updN, w.H.updC)
  f : f.fin.find? (fun q => sy q.1 == sy w.finN) = some (w.finN, w.H.finalize)

/-- At `p` in `m`, the addresses `sy` gives `w`'s HMAC `init`, the streaming
`update` and HMAC's `finalize`. -/
def TabMem (w : HVar) (sy : String → Addr) (p : Addr) (m : Mem) : Prop :=
  m.readW (p + BitVec.ofNat 64 0) 64 = sy w.initN ∧ m.readW (p + BitVec.ofNat 64 8) 64 = sy w.H.updN ∧
    m.readW (p + BitVec.ofNat 64 16) 64 = sy w.finN

theorem mem_names {vs : List HVar} {w : HVar} (hw : w ∈ vs) :
    w.initN ∈ names vs ∧ w.H.updN ∈ names vs ∧ w.finN ∈ names vs := by
  have : (tableOf w).fns ∈ (tables vs).map (·.fns) := List.mem_map_of_mem (List.mem_map_of_mem hw)
  refine ⟨?_, ?_, ?_⟩ <;> exact List.mem_flatten.mpr ⟨_, this, by simp [tableOf]⟩

/-- An indirect call of `fnsOf vs`'s functions reaches `w`'s. -/
theorem tabOK_of {vs : List HVar} (hc : Coh vs) {sy : String → Addr}
    (hd : (names vs).Pairwise fun f g => f ≠ g → sy f ≠ sy g) {w : HVar} (hw : w ∈ vs) :
    TabOK w (fnsOf vs) sy := by
  have hn := mem_names hw
  refine ⟨find_name (List.mem_map_of_mem hw) ?_ ?_, find_name (List.mem_map_of_mem hw) ?_ ?_,
    find_name (List.mem_map_of_mem hw) ?_ ?_⟩
  all_goals intro q hq
  all_goals obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hq
  · exact pw_ne hd _ (mem_names hw').1 _ hn.1
  · exact (hc w' hw' w hw).1
  · exact pw_ne hd _ (mem_names hw').2.1 _ hn.2.1
  · exact (hc w' hw' w hw).2.1
  · exact pw_ne hd _ (mem_names hw').2.2 _ hn.2.2
  · exact (hc w' hw' w hw).2.2

/-- The words of the table of `w`. -/
theorem words_tableOf (s : State) (w : HVar) :
    FnTable.words isa s (tableOf w) = [s.syms w.initN, s.syms w.H.updN, s.syms w.finN,
      BitVec.ofNat 64 (Spec.HashTable.index w.G), BitVec.ofNat 64 w.G.len,
      BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G)] := rfl

/-- What the table of `w` at `p` holds: its functions' addresses, its index,
its digest length and HMAC's block size. -/
theorem held_tableOf {m : Mem} {p : Addr} {s : State} {w : HVar}
    (h : Abi.tableHeld 64 m p (FnTable.words isa s (tableOf w))) :
    TabMem w s.syms p m ∧
      m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.G) ∧
      m.readW (p + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D ∧
      m.readW (p + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G) := by
  rw [words_tableOf] at h
  refine ⟨⟨h 0 (by simp), h 1 (by simp), h 2 (by simp)⟩, h 3 (by simp), ?_, h 5 (by simp)⟩
  exact (h 4 (by simp)).trans (by rw [w.len]; rfl)

/-- The hash function a table of `w` names. -/
theorem hashAt_tableOf {m : Mem} {p : Addr} {w : HVar}
    (h : m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.G)) :
    Spec.HmacTable.hashAt 64 m p = some w.G := by
  simp only [Spec.HmacTable.hashAt, Spec.HmacTable.fns]
  rw [show p + BitVec.ofNat 64 (64 / 8 * 3) = p + BitVec.ofNat 64 24 from rfl, h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := List.findIdx_le_length (p := fun G => G.rust == w.G.rust) (xs := Spec.Mgf1.hashes)
      simp only [Spec.HashTable.index, Spec.Mgf1.hashes, List.length_cons, List.length_nil] at this ⊢
      omega_using [this])]
  exact w.idx

end VG.Proof.HmacTable.PPC64LE
