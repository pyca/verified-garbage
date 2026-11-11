module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyCT
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyEntry
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Hmac.AnyKey
public import VerifiedGarbage.Proof.Sha512.X86_64.Variant
public import VerifiedGarbage.Proof.Sha256.X86_64.Variant
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Pbkdf2.Scratch
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueTaint
public import VerifiedGarbage.Proof.Hmac.Scratch
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-!
# Merkle–Damgård hash functions on x86-64, as variants

An `MdHash` is one Merkle–Damgård hash function with one implementation of
its compression function: each is a variant of the interface `MdHash` on
x86-64 (`Variants/MdHash/X86_64/`), and each function built on the hash
function (in `Generic/MdHash/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`): its streaming `update` and `finalize` (when they are not
shared by several variants, `stream`), HMAC's `init` and `finalize`, and
PBKDF2's `iterate` and `pbkdf2`, all named with the variant's `suffix`.

`MdHash.of` builds one from what the proofs need of the hash function's
code (`HashOK`), what the kernel checks of the code HMAC and PBKDF2 add to
it (`CoreOK`, once for each hash function) and of the functions they call
(`Callees`, once for each implementation), and the satisfiability of the
shared contracts, which the kernel checks for each instance.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- `Code.allInstrs p` from `Code.all p`. -/
theorem allInstrs_of_all {I C : Type} {p : I → Bool} {c : Code I C} (h : c.all p = true) :
    c.allInstrs p = true := by
  induction c with
  | block is => induction is <;> simp_all [Code.all, Code.allInstrs]
  | _ => simp_all [Code.all, Code.allInstrs]

/-- One of the streaming functions made with an implementation of a hash
function's compression function, which `Generic/MdHash/X86_64/Stream.lean`
emits, naming it with the variant's suffix: its `Api` (in `Spec/`), and its
code, verified against the contract the `Api` gives it (`ofApi`, as
`Artifact.ofApi`) with `stack` bytes of stack. -/
structure StreamFn where
  api : Api
  code : Prog X86_64.target.isa
  contract : Contract X86_64.target.isa
  stack : Nat := 0
  verified : Verified X86_64.target code contract
  ofSig : ∃ pre post leak,
      contract = api.sig.contract (X86_64.target.abi.withMode api.pubMode) pre post api.writeArgs stack leak := by
    exact ⟨_, _, _, rfl⟩
  ofApi : contract = api.contract X86_64.target.abi stack := by exact rfl
  spSafe : code.all (fun i => !X86_64.target.isa.writesSp i) = true
  /-- `Artifact.residue`. -/
  residue : Option (PLift (X86_64.NoResidue code contract (api.sig.retBits 64))) := none

/-- `f` as a registration of its `Api` (`Api.artifact`). -/
def StreamFn.reg (f : StreamFn) : Registration f.api X86_64.target where
  consts := []
  tables := []
  code := f.code
  contract := f.contract
  stack := f.stack
  verified := f.verified
  ofApi := f.ofApi
  ofSig := f.ofSig
  spSafe := f.spSafe
  residue := f.residue

/-- The bytes of the frame in which HMAC's `init` and `finalize` (of
instance `I`) keep their working space, for their `_scratch` forms. -/
def hmacFrame (I : Spec.Hmac.Instance) : Nat := 8 + 8 * I.scratch

/-- The bytes of the frame in which HMAC's `init` for a key of any length (of
instance `I`) keeps its working space, which it wipes before returning: a
quadword standing for the return address, then the buffer
(`VG.Spec.Hmac.Instance.initAnyKeyScratch` words). -/
def anyFrame (I : Spec.Hmac.Instance) : Nat := 8 + 8 * I.initAnyKeyScratch

/-- HMAC's `init` for a key of any length, `vg_hmac_<hash>_init`: for a key
of at most a block, `init_scratch` (`Hash.hmacInit`) in a frame holding its
working space; for a longer key (cold), `Hash.hmacInitAny`, in a frame
holding its larger working space, which it wipes. -/
def initCode (H : Hash) (I : Spec.Hmac.Instance) : Prog isa :=
  Impl.Pbkdf2.Md.X86_64.initEntry I.S.H.blockSize
    (Impl.StackScratch.X86_64.withStackScratch (hmacFrame I) .r8 H.hmacInit)
    (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame I) .r8 I.initAnyKeyScratch H.hmacInitAny)

/-- The taints of the hint of the residue analysis of `initCode` (of instance
`I`), for `taint_decide_weak`: without the public slots of 16 bytes of the
frame of its branch for long keys (`anyFrame I` bytes, the outermost frame)
that the clearing of that frame (`withStackScratchWiped`, from its byte 8)
covers. That branch clears its frame before freeing it, which makes those
bytes public again, so the analysis never needs the slots that the frame
starts with, but scans them at every access to memory: the kernel checks
the analysis about four times faster without them. -/
def initHintWeak (I : Spec.Hmac.Instance) (τ : RTaint.FT) : RTaint.FT :=
  if 1 ≤ τ.nfr && τ.t.lens.getD (τ.nfr - 1) 0 == anyFrame I then
    { τ with t := { τ.t with slots := τ.t.slots.filter fun sl =>
        !(sl.1 == τ.nfr - 1 && sl.2.2 == 16 && 8 ≤ sl.2.1 && sl.2.1 + 16 ≤ anyFrame I) } }
  else τ

/-! ### The residue analysis of `initCode`, a branch at a time

`initRes_ok` puts together the residue analysis of `initCode` from those of its
two branches (`InitLongOk`, `InitShortOk`), each from the comparison of the
key's length (`initMid`) to the end (`initEndOk`). Each is a theorem of its
own, which the kernel checks with about two thirds of the memory of the
whole. -/

/-- The comparison of the key's length with which `initCode` starts. -/
def initCmp (I : Spec.Hmac.Instance) : Instr :=
  .alu .cmp .rcx (.imm (BitVec.ofNat 32 (I.S.H.blockSize + 1)))

/-- The residue analysis of `initCode` (of instance `I`) after `initCmp`. -/
def initMid (I : Spec.Hmac.Instance) : RTaint.rtaint.T :=
  (RTaint.rtaint.step (RScrub.init I.initAnyKeyApi.sig (24 + anyFrame I) []) (initCmp I)).getD RTaint.none'

/-- The analysis of `initCmp` succeeds (`initMid`), and the branch on its
flags is public. -/
def initMidOk (I : Spec.Hmac.Instance) : Bool :=
  (RTaint.rtaint.step (RScrub.init I.initAnyKeyApi.sig (24 + anyFrame I) []) (initCmp I)).isSome &&
    RTaint.rtaint.le (initMid I) (initMid I) && RTaint.rtaint.condPub (initMid I) .ae

/-- What the residue analysis of each branch of `initCode` ends with: the
bytes of its window that may hold secrets are within the granules `ks`, and
no frame or call is in progress, as at the end of the other branch. -/
def initEndOk (I : Spec.Hmac.Instance) (ks : List Nat) (τ : RTaint.FT) : Bool :=
  RScrub.resOkB τ (24 + anyFrame I) ks (Impl.Scrub.X86_64.chunks (24 + anyFrame I)) && τ.nfr == 0 &&
    τ.ras == [] && τ.fw == [] && τ.t.lens == (RScrub.init I.initAnyKeyApi.sig (24 + anyFrame I) []).t.lens

/-- The residue analysis of `initCode`'s branch for keys longer than a block,
from `initMid`. -/
def InitLongOk (H : Hash) (I : Spec.Hmac.Instance) (ks : List Nat) : Prop :=
  ∃ h : VG.Taint.Hint RTaint.FT, (VG.Taint.check RTaint.rtaint (initMid I)
    (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame I) .r8 I.initAnyKeyScratch H.hmacInitAny) h).any
    (initEndOk I ks) = true

/-- The residue analysis of `initCmp` (`initMidOk`), and of `initCode`'s
branch for keys of at most a block from `initMid`. -/
def InitShortOk (H : Hash) (I : Spec.Hmac.Instance) (ks : List Nat) : Prop :=
  initMidOk I = true ∧ ∃ h : VG.Taint.Hint RTaint.FT, (VG.Taint.check RTaint.rtaint (initMid I)
    (Impl.StackScratch.X86_64.withStackScratch (hmacFrame I) .r8 H.hmacInit) h).any
    (initEndOk I ks) = true

theorem exists_of_any {α : Type} {p : α → Bool} {o : Option α} (h : o.any p = true) :
    ∃ a, o = some a ∧ p a = true := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

theorem resOkB_meet {stack : Nat} {ks cs : List Nat} {τ₁ τ₂ : RTaint.FT}
    (h₁ : RScrub.resOkB τ₁ stack ks cs = true) (h₂ : RScrub.resOkB τ₂ stack ks cs = true)
    (hn : τ₁.nfr = τ₂.nfr) (hr : τ₁.ras = τ₂.ras) (hf : τ₁.fw = τ₂.fw) (hl : τ₁.t.lens = τ₂.t.lens) :
    RScrub.resOkB (RTaint.meet τ₁ τ₂) stack ks cs = true := by
  simp only [RScrub.resOkB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', List.any_eq_false] at h₁ h₂ ⊢
  obtain ⟨⟨⟨o₁, r₁⟩, d₁⟩, a₁⟩ := h₁
  obtain ⟨⟨⟨o₂, r₂⟩, d₂⟩, a₂⟩ := h₂
  have hc : (τ₁.ok && τ₂.ok && τ₁.nfr == τ₂.nfr && τ₁.depth == τ₂.depth && τ₁.room == τ₂.room &&
      τ₁.ras == τ₂.ras && τ₁.t.lens == τ₂.t.lens && τ₁.fw == τ₂.fw) = true := by
    simp [o₁, o₂, hn, hr, hf, hl, r₁, r₂, d₁, d₂]
  simp only [RTaint.meet, hc, ↓reduceIte]
  refine ⟨⟨⟨o₁, r₁⟩, d₁⟩, fun j hj => ?_⟩
  rcases a₁ j hj with h | h
  · exact .inl h
  rcases a₂ j hj with h' | h'
  · exact .inl h'
  · exact .inr fun p hp => by
      rcases List.mem_append.mp hp with hp | hp
      · exact h p hp
      · exact h' p hp

theorem initRes_ok {H : Hash} {I : Spec.Hmac.Instance} {ks : List Nat}
    (hl : InitLongOk H I ks) (hs : InitShortOk H I ks) :
    ∃ h : VG.Taint.Hint RTaint.FT,
      (VG.Taint.check RTaint.rtaint (RScrub.init I.initAnyKeyApi.sig (24 + anyFrame I) []) (initCode H I) h).any
        (RScrub.resOkB · (24 + anyFrame I) ks (Impl.Scrub.X86_64.chunks (24 + anyFrame I))) = true := by
  obtain ⟨hL, hl⟩ := hl
  obtain ⟨hm, hS, hs⟩ := hs
  simp only [initMidOk, Bool.and_eq_true] at hm
  obtain ⟨⟨hm, hle⟩, hc⟩ := hm
  refine ⟨.seq (initMid I) (.block [] VG.Taint.chunk) (.ite (.seq (initMid I)
    (.seq (initMid I) (.block [] VG.Taint.chunk) (.block [] VG.Taint.chunk)) hL) hS), ?_⟩
  obtain ⟨τL, eL, oL⟩ := exists_of_any hl
  obtain ⟨τS, eS, oS⟩ := exists_of_any hs
  have e : VG.Taint.check RTaint.rtaint (RScrub.init I.initAnyKeyApi.sig (24 + anyFrame I) []) (initCode H I)
      (.seq (initMid I) (.block [] VG.Taint.chunk) (.ite (.seq (initMid I)
        (.seq (initMid I) (.block [] VG.Taint.chunk) (.block [] VG.Taint.chunk)) hL) hS)) =
      some (RTaint.rtaint.meet τL τS) := by
    have hb : ∀ τ, VG.Taint.checkChunks RTaint.rtaint VG.Taint.chunk τ [] [] = some τ := fun _ => rfl
    have h0 : VG.Taint.checkChunks RTaint.rtaint VG.Taint.chunk (RScrub.init I.initAnyKeyApi.sig (24 + anyFrame I) [])
        [.alu .cmp .rcx (.imm (BitVec.ofNat 32 (I.S.H.blockSize + 1)))] [] = some (initMid I) := by
      show (RTaint.rtaint.step _ (initCmp I)).bind some = some ((RTaint.rtaint.step _ (initCmp I)).getD _)
      revert hm
      cases RTaint.rtaint.step (RScrub.init I.initAnyKeyApi.sig (24 + anyFrame I) []) (initCmp I) with
      | none => intro hm; cases hm
      | some τ => intro _; rfl
    simp only [initCode, Impl.Pbkdf2.Md.X86_64.initEntry, Code.iteCold, VG.Taint.check]
    rw [h0]
    simp only [Option.bind_some, hle, ↓reduceIte, hc, hb, eL, eS]
    rfl
  refine (congrArg (Option.any _) e).trans ?_
  simp only [initEndOk, Bool.and_eq_true, beq_iff_eq] at oL oS
  exact resOkB_meet oL.1.1.1.1 oS.1.1.1.1 (oL.1.1.1.2.trans oS.1.1.1.2.symm) (oL.1.1.2.trans oS.1.1.2.symm)
    (oL.1.2.trans oS.1.2.symm) (oL.2.trans oS.2.symm)

/-! ### The branch for long keys, in two parts

The kernel's check of the analysis of `initCode`'s branch for long keys,
which hashes the key and then calls HMAC's `init`, takes the most memory of
the two: `initLong_of` puts it together from the analysis of its start, up
to the call (`initLongPre`), and of the rest (`initLongPost`), from a taint
`M` between them (`init_long_mid%`). -/

/-- The start of `initCode`'s branch for long keys, in its frame: the
frame's set-up, the entry, the key and the arguments of HMAC's `init`. -/
def initLongPre (H : Hash) : Prog isa :=
  .seq (.block [.mov .r8 (.reg .rsp), .alu .add .r8 (.imm 8)])
    (.seq (.block H.anyEntry) (.seq H.key (.block Impl.Pbkdf2.Md.X86_64.Hash.anyArgs)))

/-- The rest, in its frame: the call of HMAC's `init`, the exit and the
clearing of the frame. -/
def initLongPost (H : Hash) (I : Spec.Hmac.Instance) : Prog isa :=
  .seq (.seq (.call H.hmacInitN H.hmacInit) (.block H.exit))
    (.block (Impl.StackScratch.X86_64.wipe I.initAnyKeyScratch))

/-- The residue analysis on entry to the frame of the branch for long keys. -/
def initLongStart (I : Spec.Hmac.Instance) : RTaint.rtaint.T :=
  (RTaint.rtaint.push (initMid I) (.alloc (anyFrame I))).getD RTaint.none'

/-- The residue analysis of `initLongPre`, ending with at least `M` public. -/
def InitLongPre (H : Hash) (I : Spec.Hmac.Instance) (M : RTaint.rtaint.T) : Prop :=
  ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (initLongStart I) (initLongPre H) h).any (RTaint.rtaint.le M) = true

/-- The residue analysis of `initLongPost` from `M` and of the frame's
release, ending as `initEndOk` says. -/
def InitLongPost (H : Hash) (I : Spec.Hmac.Instance) (ks : List Nat) (M : RTaint.rtaint.T) : Prop :=
  ∃ h : VG.Taint.Hint RTaint.FT, (VG.Taint.check RTaint.rtaint M (initLongPost H I) h).any
    (fun τ => (RTaint.rtaint.pop τ (.free (anyFrame I))).any (initEndOk I ks)) = true

/-- The taint between `initLongPre` and `initLongPost`: what the analysis of
`initLongPre` ends with, weakened as `initHintWeak` weakens a hint (for
`init_long_mid%`, which computes it in compiled code). -/
def initLongMidOf (H : Hash) (I : Spec.Hmac.Instance) : RTaint.FT :=
  initHintWeak I (((VG.Taint.hint RTaint.rtaint 1024 (initLongStart I) (initLongPre H)).map (·.1)).getD RTaint.none')

theorem check_seq_some {τ τ'' : RTaint.rtaint.T} {c₁ c₂ : Prog isa} {h : VG.Taint.Hint RTaint.rtaint.T}
    (e : VG.Taint.check RTaint.rtaint τ (.seq c₁ c₂) h = some τ'') :
    ∃ m h₁ h₂ τ', h = .seq m h₁ h₂ ∧ VG.Taint.check RTaint.rtaint τ c₁ h₁ = some τ' ∧
      RTaint.rtaint.le m τ' = true ∧ VG.Taint.check RTaint.rtaint m c₂ h₂ = some τ'' := by
  cases h with
  | seq m h₁ h₂ =>
    simp only [VG.Taint.check, Option.bind_eq_some_iff] at e
    obtain ⟨τ', e₁, e₂⟩ := e
    split at e₂
    · exact ⟨m, h₁, h₂, τ', rfl, e₁, by assumption, e₂⟩
    · cases e₂
  | _ => simp [VG.Taint.check] at e

theorem check_seq_of {τ τ' τ'' m : RTaint.rtaint.T} {c₁ c₂ : Prog isa} {h₁ h₂ : VG.Taint.Hint RTaint.rtaint.T}
    (e₁ : VG.Taint.check RTaint.rtaint τ c₁ h₁ = some τ') (hl : RTaint.rtaint.le m τ' = true)
    (e₂ : VG.Taint.check RTaint.rtaint m c₂ h₂ = some τ'') :
    VG.Taint.check RTaint.rtaint τ (.seq c₁ c₂) (.seq m h₁ h₂) = some τ'' := by
  simp only [VG.Taint.check, e₁, Option.bind_some, hl, ↓reduceIte, e₂]

theorem initLong_of {H : Hash} {I : Spec.Hmac.Instance} {ks : List Nat} {M : RTaint.rtaint.T}
    (hp : (RTaint.rtaint.push (initMid I) (.alloc (anyFrame I))).isSome = true)
    (ha : InitLongPre H I M) (hb : InitLongPost H I ks M) : InitLongOk H I ks := by
  obtain ⟨hA, ha⟩ := ha
  obtain ⟨hB, hb⟩ := hb
  obtain ⟨τA, eA, lA⟩ := exists_of_any ha
  obtain ⟨τW, eW, oW⟩ := exists_of_any hb
  obtain ⟨τE, eE, oE⟩ := exists_of_any oW
  obtain ⟨m₁, h₀, _, τ₀, rfl, e₀, l₀, er⟩ := check_seq_some eA
  obtain ⟨m₃, hE, _, τe, rfl, eE', lE, er'⟩ := check_seq_some er
  obtain ⟨m₄, hK, hAa, τk, rfl, eK, lK, eAa⟩ := check_seq_some er'
  obtain ⟨m₂, hCX, hW, τx, rfl, eCX, l₂, eWp⟩ := check_seq_some eW
  have e₅ := check_seq_of e₀ l₀ (check_seq_of (check_seq_of eE' lE (check_seq_of eK lK
    (check_seq_of eAa lA eCX))) l₂ eWp)
  have hs : RTaint.rtaint.push (initMid I) (.alloc (anyFrame I)) = some (initLongStart I) := by
    unfold initLongStart
    revert hp
    cases RTaint.rtaint.push (initMid I) (.alloc (anyFrame I)) with
    | none => intro hp; cases hp
    | some τ => intro _; rfl
  have e : VG.Taint.check RTaint.rtaint (initMid I)
      (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame I) .r8 I.initAnyKeyScratch H.hmacInitAny)
      (.frame (.seq m₁ h₀ (.seq m₂ (.seq m₃ hE (.seq m₄ hK (.seq M hAa hCX))) hW))) = some τE := by
    simp only [Impl.StackScratch.X86_64.withStackScratchWiped, Impl.StackScratch.X86_64.withStackScratch,
      VG.Taint.check, hs, Option.bind_some]
    refine (congrArg (fun o => Option.bind o (fun τ => RTaint.rtaint.pop τ (.free (anyFrame I)))) e₅).trans ?_
    exact eE
  exact ⟨_, (congrArg (Option.any (initEndOk I ks)) e).trans oE⟩

open Lean Elab Term Meta in
/-- `init_long_mid% H I`: `initLongMidOf H I`, computed in compiled code, as
a literal. -/
elab "init_long_mid% " H:term:max I:term:max : term => do
  let e ← elabTerm (← `(VG.Proof.Pbkdf2.Md.X86_64.initLongMidOf $H $I)) none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let v ← unsafe evalExpr RTaint.FT (mkConst ``RTaint.FT) e
  return toExpr v

/-- The bytes of the frame in which PBKDF2's `pbkdf2` (of instance `I`) keeps
its working space, for its `_scratch` form: a quadword standing for the
return address, a copy of `out_len` and the buffer's address (its stack
arguments), then the buffer. -/
def pbkdf2Frame (I : Spec.Hmac.Instance) : Nat := 24 + 8 * I.pbkdf2Scratch

/-- A Merkle–Damgård hash function on x86-64, with one implementation of its
compression function: its functions, verified against the contracts of its
instance `I` (`Spec/Hmac/Generic.lean`, `Spec/Pbkdf2/Generic.lean`). -/
structure MdHash where
  /-- The hash function's code and the names of its functions. -/
  H : Hash
  /-- The instance of the shared contracts. -/
  I : Spec.Hmac.Instance
  /-- What the proofs know of the hash function's code, and of the functions
  it calls (for the callers that work at the level of its compression
  function: RSASSA-PSS's, `Generic/MdHash/RsaPrivateCrt/X86_64/RsaPss.lean`). -/
  ok : HashOK H
  K : Callees H
  /-- The hash function as RSA's padding takes it. -/
  mgf : MgfLink H ok
  hmacInit : Verified X86_64.target H.hmacInit (Proof.Hmac.Instance.initScratchContract I X86_64.abi 16)
  hmacFin : Verified X86_64.target H.hmacFin (Proof.Hmac.Instance.finalizeScratchContract I X86_64.abi 16)
  iterate : Verified X86_64.target H.iterate (Proof.Pbkdf2.Instance.iterateContract I X86_64.abi 8)
  pbkdf2 : Verified X86_64.target H.pbkdf2 (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I X86_64.abi 24)
  hmacInitSp : H.hmacInit.all (fun i => !isa.writesSp i) = true
  hmacFinSp : H.hmacFin.all (fun i => !isa.writesSp i) = true
  iterateSp : H.iterate.all (fun i => !isa.writesSp i) = true
  pbkdf2Sp : H.pbkdf2.all (fun i => !isa.writesSp i) = true
  /-- HMAC's `init` for a key of any length (`initEntry`): for a key of at
  most a block, `init_scratch` with its working space in a frame of its own;
  for a longer key, `hmacInitAny` with its working space in a frame of its
  own, wiped before returning; and `finalize` with its working space in a
  frame of its own (`hmacFin` is its `_scratch` form). -/
  hmacInitF : Verified X86_64.target (initCode H I) (I.initAnyKeyContract X86_64.abi (24 + anyFrame I))
  hmacInitFSp : (initCode H I).all (fun i => !isa.writesSp i) = true
  /-- The two branches of `initCode`, each verified against its contract:
  what `hmacInitF` is made of, for `MdHash.initScrubbed`, which clears after
  each. -/
  hmacShortF : Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch (hmacFrame I) .r8 H.hmacInit)
    (I.initContract X86_64.abi (16 + hmacFrame I))
  hmacShortFSp : (Impl.StackScratch.X86_64.withStackScratch (hmacFrame I) .r8 H.hmacInit).all
    (fun i => !isa.writesSp i) = true
  hmacAnyF : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame I) .r8 I.initAnyKeyScratch H.hmacInitAny)
    (I.initAnyKeyContract X86_64.abi (24 + anyFrame I))
  hmacAnyFSp : (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame I) .r8 I.initAnyKeyScratch
    H.hmacInitAny).all (fun i => !isa.writesSp i) = true
  /-- The streaming states represent a message by their bytes alone, and a
  block's size is small. -/
  reprLocal : Proof.Hmac.ReprLocal I.S
  hBlock : I.S.H.blockSize + 1 < 2 ^ 31
  hmacFinF : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch (hmacFrame I) .r8 H.hmacFin)
    (I.finalizeContract X86_64.abi (16 + hmacFrame I))
  /-- PBKDF2's `pbkdf2` with its working space in a frame of its own
  (`pbkdf2` is its `_scratch` form). -/
  pbkdf2F : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackArgScratch (pbkdf2Frame I) 1 H.pbkdf2)
    (I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame I))
  /-- What the kernel checked of the code HMAC and PBKDF2 add to the hash
  function's (`CoreOK`), and that the instance's streaming hash function is
  the code's (its state's representation and its working space): what a
  function generic over the variant that calls HMAC's `_scratch` functions
  needs (deterministic ECDSA's, through a table of `Hmac`,
  `Proof/HmacTable/X86_64.lean`). -/
  C : CoreOK (core H)
  hSH : ok.SH = I.S
  hW : H.W = I.scratch
  /-- What the names of the functions emitted for it end with (e.g.
  `_shani`; nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its compression function requires, which the
  functions built on it require too. -/
  features : List String
  /-- The streaming `update` and `finalize` made with this implementation of
  the compression function, when no other variant shares them (otherwise
  they are in the hash function's registration file). -/
  stream : List StreamFn
  /-- The residue analysis of HMAC's `finalize` (`hmacFinF`), if the analysis
  handles it: that function then returns without secret residue
  (`MdHash.hmacFinReg`). -/
  hmacFinRes : Option (RScrub.Analysed I.finalizeApi.sig (16 + hmacFrame I) []
    (Impl.StackScratch.X86_64.withStackScratch (hmacFrame I) .r8 H.hmacFin)) := none
  /-- The residue analysis of HMAC's `init` (`hmacInitF`), if the analysis
  handles it: that function then returns without secret residue
  (`MdHash.hmacInitReg`). -/
  hmacInitRes : Option (RScrub.Analysed I.initAnyKeyApi.sig (24 + anyFrame I) [] (initCode H I)) := none

namespace MdHash

variable {H : Hash} {I : Spec.Hmac.Instance} (hH : HashOK H) (C : CoreOK (core H)) (K : Callees H)
  (hSH : hH.SH = I.S) (hW : H.W = I.scratch)
include hH C K hSH hW

theorem hmacInit_of (hs : ∃ s, (Proof.Hmac.Instance.initScratchContract I X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacInit (Proof.Hmac.Instance.initScratchContract I X86_64.abi 16) := by
  simp only [Proof.Hmac.Instance.initScratchContract, ← hSH, ← hW] at hs ⊢
  exact hmacInit_verified hH C K hs

theorem hmacFin_of (hs : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacFin (Proof.Hmac.Instance.finalizeScratchContract I X86_64.abi 16) := by
  simp only [Proof.Hmac.Instance.finalizeScratchContract, ← hSH, ← hW] at hs ⊢
  exact hmacFin_verified hH C K hs

theorem iterate_of (hs : ∃ s, (Proof.Pbkdf2.Instance.iterateContract I X86_64.abi 8).pre s) :
    Verified X86_64.target H.iterate (Proof.Pbkdf2.Instance.iterateContract I X86_64.abi 8) := by
  simp only [Proof.Pbkdf2.Instance.iterateContract, ← hSH, ← hW] at hs ⊢
  exact iterate_verified hH C K hs

theorem pbkdf2_of (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I X86_64.abi 16).pre s)
    (hsF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I X86_64.abi 16).pre s)
    (hsT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract I X86_64.abi 8).pre s)
    (hs : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I X86_64.abi 24).pre s) :
    Verified X86_64.target H.pbkdf2 (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I X86_64.abi 24) := by
  simp only [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.Instance.finalizeScratchContract,
    Proof.Pbkdf2.Instance.iterateContract, Proof.Pbkdf2.Instance.pbkdf2ScratchContract,
    Spec.Hmac.Instance.pbkdf2Scratch, ← hSH, ← hW, hH.hS] at hsI hsF hsT hs ⊢
  exact pbkdf2_verified hH C K hsI hsF hsT hs

theorem hmacInitAny_of (A : Any.AnyOK (core H)) (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I X86_64.abi 16).pre s)
    (hs : ∃ s, (Any.anyScratchContract I.S I.initAnyKeyScratch).pre s) :
    Verified X86_64.target H.hmacInitAny (Any.anyScratchContract I.S I.initAnyKeyScratch) := by
  simp only [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, ← hSH, ← hW,
    hH.hS] at hsI hs ⊢
  exact Any.hmacInitAny_verified hH C A K hsI hs

omit hH C hSH hW in
theorem hmacInitAnySp_of (A : Any.AnyOK (core H)) :
    (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame I) .r8 I.initAnyKeyScratch
      H.hmacInitAny).all (fun i => !isa.writesSp i) = true :=
  X86_64.withStackScratch_spSafe (by decide)
    (by simp only [Code.all, Any.hmacInitAny_sp A K, X86_64.wipe_spSafe, Bool.and_self])

theorem hmacInitAnyF_of (A : Any.AnyOK (core H)) (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I X86_64.abi 16).pre s)
    (hs : ∃ s, (Any.anyScratchContract I.S I.initAnyKeyScratch).pre s) (ha : I.initAnyKeyScratch < 511)
    (hR : Proof.Hmac.ReprLocal I.S)
    (hsat : ∃ s, (I.initAnyKeyContract X86_64.abi (24 + anyFrame I)).pre s) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratchWiped (anyFrame I) .r8 I.initAnyKeyScratch H.hmacInitAny)
      (I.initAnyKeyContract X86_64.abi (24 + anyFrame I)) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := I.initAnyKeyScratch) (post := Spec.Hmac.initPost I.S X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := anyFrame I) (words := I.initAnyKeyScratch) (hmacInitAny_of hH C K hSH hW A hsI hs)
    (by exact (by decide : 4 < 6)) (by simp only [anyFrame, Elem.size]; omega_arith) (by simp only [anyFrame]; omega_arith)
    (Any.hmacInitAny_sp A K) (Any.hmacInitAny_xd A K)
    (by simp only [Elem.size]; omega_arith)
    (Proof.Hmac.initPostOut_local I.S _ hR (by
      rw [← hSH, hH.hS]; have := hH.N_le; have := hH.B_le
      show H.P.N + H.P.B < 2 ^ 64; omega_arith)) hsat rfl

theorem hmacShortF_of (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I X86_64.abi 16).pre s) (hs : I.scratch < 511)
    (hsat : ∃ s, (I.initContract X86_64.abi (16 + hmacFrame I)).pre s) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch (hmacFrame I) .r8 H.hmacInit)
      (I.initContract X86_64.abi (16 + hmacFrame I)) :=
  X86_64.Verified.stackScratch (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := I.scratch) (pre := Spec.Hmac.initPre I.S X86_64.abi.ptrBits)
    (post := Spec.Hmac.initPost I.S X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := hmacFrame I) (hmacInit_of hH C K hSH hW hsI) (by exact (by decide : 4 < 6))
    (by simp only [hmacFrame, Elem.size]; omega_arith) (by simp only [hmacFrame]; omega_arith) (hmacInit_sp C K)
    (Callees.hmacInitXD K C) hsat rfl

theorem hmacInitF_of (A : Any.AnyOK (core H)) (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I X86_64.abi 16).pre s)
    (hs : I.scratch < 511) (hsIF : ∃ s, (I.initContract X86_64.abi (16 + hmacFrame I)).pre s)
    (hsA : ∃ s, (Any.anyScratchContract I.S I.initAnyKeyScratch).pre s) (ha : I.initAnyKeyScratch < 511)
    (hR : Proof.Hmac.ReprLocal I.S) (hB : I.S.H.blockSize + 1 < 2 ^ 31)
    (hsat : ∃ s, (I.initAnyKeyContract X86_64.abi (24 + anyFrame I)).pre s) :
    Verified X86_64.target (initCode H I) (I.initAnyKeyContract X86_64.abi (24 + anyFrame I)) :=
  initEntry_verified (hmacShortF_of hH C K hSH hW hsI hs hsIF)
    (hmacInitAnyF_of hH C K hSH hW A hsI hsA ha hR hsat) (by omega_arith)
    (by simp only [hmacFrame, anyFrame, Spec.Hmac.Instance.initAnyKeyScratch]; omega_arith) hB hsat

omit hH hSH hW in
theorem hmacShortFSp_of :
    (Impl.StackScratch.X86_64.withStackScratch (hmacFrame I) .r8 H.hmacInit).all
      (fun i => !isa.writesSp i) = true :=
  X86_64.withStackScratch_spSafe_of (r := .r8) (hmacInit_sp C K)

omit hH hSH hW in
theorem hmacInitFSp_of (A : Any.AnyOK (core H)) :
    (initCode H I).all (fun i => !isa.writesSp i) = true := by
  have hs : (Impl.StackScratch.X86_64.withStackScratch (hmacFrame I) .r8 H.hmacInit).all
      (fun i => !isa.writesSp i) = true := X86_64.withStackScratch_spSafe_of (r := .r8) (hmacInit_sp C K)
  simp only [initCode, Impl.Pbkdf2.Md.X86_64.initEntry, Code.iteCold, Code.all, hmacInitAnySp_of K A, hs,
    Bool.and_true]
  rfl

theorem hmacFinF_of (hsF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I X86_64.abi 16).pre s) (hs : I.scratch < 511)
    (hsat : ∃ s, (I.finalizeContract X86_64.abi (16 + hmacFrame I)).pre s) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch (hmacFrame I) .r8 H.hmacFin)
      (I.finalizeContract X86_64.abi (16 + hmacFrame I)) :=
  X86_64.Verified.stackScratch (sig := Spec.Hmac.finalizeSig I.S) (nm := "scratch") (e := .u64)
    (n := I.scratch) (post := Spec.Hmac.finalizePost I.S X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := hmacFrame I) (hmacFin_of hH C K hSH hW hsF) (by exact (by decide : 4 < 6))
    (by simp only [hmacFrame, Elem.size]; omega_arith) (by simp only [hmacFrame]; omega_arith) (hmacFin_sp C K)
    (Callees.hmacFinXD K C) hsat rfl

theorem pbkdf2F_of (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I X86_64.abi 16).pre s)
    (hsF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I X86_64.abi 16).pre s)
    (hsT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract I X86_64.abi 8).pre s)
    (hsP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I X86_64.abi 24).pre s) (hp : I.pbkdf2Scratch < 509)
    (hsat : ∃ s, (I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame I)).pre s) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch (pbkdf2Frame I) 1 H.pbkdf2)
      (I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame I)) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Pbkdf2.pbkdf2Sig) (nm := "scratch") (e := .u64)
    (n := I.pbkdf2Scratch) (pre := Spec.Pbkdf2.pbkdf2Pre I.S X86_64.abi.ptrBits)
    (post := Spec.Pbkdf2.pbkdf2Post I.S X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := pbkdf2Frame I) (pbkdf2_of hH C K hSH hW hsI hsF hsT hsP) (by decide)
    (by
      have : X86_64.nStack Spec.Pbkdf2.pbkdf2Sig = 1 := rfl
      simp only [pbkdf2Frame, Elem.size]; omega_arith)
    (by simp only [pbkdf2Frame]; omega_arith) (pbkdf2_sp C K) (Callees.pbkdf2XD K C)
    (pbkdf2Pre_local I.S _) (pbkdf2Post_local I.S _) hsat

end MdHash

/-- The variant of hash function `H`, of instance `I`, from what the proofs
need of it and the satisfiability of the shared contracts. -/
def MdHash.of {H : Hash} {I : Spec.Hmac.Instance} (hH : HashOK H) (C : CoreOK (core H)) (K : Callees H)
    (mgf : MgfLink H hH) (hSH : hH.SH = I.S) (hW : H.W = I.scratch)
    (hsI : ∃ s, (Proof.Hmac.Instance.initScratchContract I X86_64.abi 16).pre s)
    (hsF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract I X86_64.abi 16).pre s)
    (hsT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract I X86_64.abi 8).pre s)
    (hsP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I X86_64.abi 24).pre s)
    (hs : I.scratch < 511)
    (A : Any.AnyOK (core H)) (hsA : ∃ s, (Any.anyScratchContract I.S I.initAnyKeyScratch).pre s)
    (ha : I.initAnyKeyScratch < 511) (hR : Proof.Hmac.ReprLocal I.S)
    (hsAF : ∃ s, (I.initAnyKeyContract X86_64.abi (24 + anyFrame I)).pre s)
    (hsIF : ∃ s, (I.initContract X86_64.abi (16 + hmacFrame I)).pre s) (hB : I.S.H.blockSize + 1 < 2 ^ 31)
    (hsFF : ∃ s, (I.finalizeContract X86_64.abi (16 + hmacFrame I)).pre s)
    (hp : I.pbkdf2Scratch < 509)
    (hsPF : ∃ s, (I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame I)).pre s)
    (suffix : String) (features : List String) (stream : List StreamFn) : MdHash where
  H := H
  I := I
  ok := hH
  K := K
  mgf := mgf
  hmacInit := MdHash.hmacInit_of hH C K hSH hW hsI
  hmacFin := MdHash.hmacFin_of hH C K hSH hW hsF
  iterate := MdHash.iterate_of hH C K hSH hW hsT
  pbkdf2 := MdHash.pbkdf2_of hH C K hSH hW hsI hsF hsT hsP
  hmacInitSp := hmacInit_sp C K
  hmacFinSp := hmacFin_sp C K
  iterateSp := iterate_sp C K
  pbkdf2Sp := pbkdf2_sp C K
  hmacInitF := MdHash.hmacInitF_of hH C K hSH hW A hsI hs hsIF hsA ha hR hB hsAF
  hmacInitFSp := MdHash.hmacInitFSp_of C K A
  hmacShortF := MdHash.hmacShortF_of hH C K hSH hW hsI hs hsIF
  hmacShortFSp := MdHash.hmacShortFSp_of C K
  hmacAnyF := MdHash.hmacInitAnyF_of hH C K hSH hW A hsI hsA ha hR hsAF
  hmacAnyFSp := MdHash.hmacInitAnySp_of K A
  reprLocal := hR
  hBlock := hB
  hmacFinF := MdHash.hmacFinF_of hH C K hSH hW hsF hs hsFF
  pbkdf2F := MdHash.pbkdf2F_of hH C K hSH hW hsI hsF hsT hsP hp hsPF
  C := C
  hSH := hSH
  hW := hW
  suffix := suffix
  features := features
  stream := stream

end VG.Proof.Pbkdf2.Md.X86_64
