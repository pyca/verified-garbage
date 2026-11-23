module

public import VerifiedGarbage.Proof.Framework.X86_64.ForwardSlots
public import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.ValidatePrivateVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.DeriveCheckedVerified
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubPaths
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.Dsa.X86_64.Fn
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
import VerifiedGarbage.Proof.Ffdh.X86_64.Scrub
public import VerifiedGarbage.Proof.Dsa.X86_64.Scrub

/-!
# DSA's functions over its arithmetic on x86-64, calling it through slots

Four of DSA's functions are emitted once, over every implementation of
the arithmetic (`SlotBackend`): each is an internal function that calls the
multiplication and the squaring through slots above its stack arguments
(`Impl.Dsa.X86_64.Fn.slotBody`), which meets its contract with the slots
(`Contract.withSlots`, `prevalidated_slot_verified` and the others), and each
implementation's function stores the addresses of its own there and calls it
(`Fn.slotted`, `Verified.forwardS`), its contract making them public
(`Abi.withFns`). It returns with its whole stack wiped (`scrubbedFns`).

The kernel evaluates what these need of the code, for an implementation, in
one declaration (`entriesOk`).
-/

@[expose] public section

/-! ## The functions as emitted -/

namespace VG.Proof.Dsa.X86_64.Slots

open VG VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.Dsa.X86_64

/-- What the cleanup needs of the instructions of code: vector instructions of
at most the level `k`, and no load of MXCSR. -/
abbrev Ins (k : Nat) : Instr → Bool := fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i

/-- The calling convention with the functions `x :: xs` of public address
is one the cleanup takes: `Abi.withFns` changes only what is public. -/
theorem scrubAbi_fns (x : String) (xs : List String) : ScrubAbi (abi.withFns (x :: xs)) :=
  ⟨rfl, rfl, fun _ => rfl, ScrubAbi.plain.wf, fun _ _ h => ScrubAbi.plain.pub _ _ h.1, fun _ => rfl,
    fun _ => rfl, ScrubAbi.plain.rdSub, abi_args_len, fun _ => rfl, abi_argRo, fun _ _ => rfl,
    ScrubAbi.plain.wfAbi⟩

/-- `scrubAll` of code verified against a contract that makes public the
addresses of the functions it calls indirectly (`Abi.withFns`), with its
whole stack wiped: no secret residue, as two runs agree on where every
function it calls indirectly is (`Verified.scrubM`). -/
theorem scrubbedFns {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
    {wa : Bool} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa} {x : String}
    {xs : List String} (v : VecLevel) (stack : Nat)
    (h : Verified target c (sig.contract (abi.withFns (x :: xs)) pre post wa stack leak))
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hins : c.allInstrs (Ins v.level) = true) (hin : ∀ n ∈ UpperLock.inames c, n ∈ x :: xs)
    (hl : litSide stack 32 = true) (hrb : sig.retBits 64 = 32)
    (hpost : PostOut (sig.contract (abi.withFns (x :: xs)) pre post wa stack leak) 32) :
    VerifiedScrubbed target (scrubAll v 32 stack c) (sig.contract (abi.withFns (x :: xs)) pre post wa stack leak)
      32 := by
  have hl' := hl
  simp only [litSide, Bool.and_eq_true, beq_iff_eq] at hl'
  simp only [litSide, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hl
  obtain ⟨⟨⟨hst, hcs⟩, hcv⟩, -⟩ := hl
  have hcv' : ∀ b ∈ chunksA stack, 0 < b ∧ b < 4096 ∧ b % 8 = 0 :=
    fun b hb => of_decide_eq_true (List.all_eq_true.mp hcv b hb)
  obtain ⟨hlv, hmx⟩ := allInstrs_level (Nat.le_refl _) hins
  have hlv' : ∀ i ∈ instrs c, i.vecLevelR ≤ v.level := fun i hi => by
    simpa using List.all_eq_true.mp ((Code.allInstrs_eq _ c).symm.trans hlv) i hi
  let ks := wipeKs (chunksA stack)
  have hres : ResOk c (sig.contract (abi.withFns (x :: xs)) pre post wa stack leak) stack ks (chunksA stack) := by
    show ResOk c _ stack (wipeKs (chunksA stack)) (chunksA stack)
    rw [wipeKs_eq]
    exact RScrub.resOk_allC _ _ (fun b hb => (of_decide_eq_true (List.all_eq_true.mp hl'.1.2 b hb)).2.2)
      hl'.1.1.2
  have ht : TailOk 32 xregs (psOf ks) (gsAll ks) ks :=
    { x0 := fun _ => mem_xregs _
      r11 := fun hk => by simp [psOf, hk]
      psOk := fun q hq => by unfold psOf at hq; split at hq <;> simp_all [scratchRegs]
      gsOk := fun q hq => by
        unfold gsAll at hq; split at hq
        · exact hq
        · exact List.mem_of_mem_erase hq
      gne := by unfold gsAll; split <;> simp [scratchRegs] }
  have hgk : ∀ q ∈ scratchRegs, q ∉ gsAll ks → q ∉ psOf ks → ∀ i ∈ instrs c,
      Taint.clobbers i q = false := fun q hq hg hp =>
    ((gsAll_cover ks q hq).elim (fun h => absurd h hg) (fun h => absurd h hp))
  have hrb' : sig.retBits (abi.withFns (x :: xs)).ptrBits = 32 := hrb
  rw [← hrb'] at ht hpost ⊢
  have key := Verified.scrubM (f := .avx) (scrubAbi_fns x xs) h (SpSafe.of_all hsp) hd
    hcs hst hcv' hlv' (fun _ => mxSame_of_noLoad hmx) (.inl (by rw [hrb'])) hpost hres ht (.inl mem_xregs)
    (fun _ => mem_xregs) (fun _ _ e => absurd e (by decide)) hgk
  exact ⟨key.1, key.2 fun s₁ s₂ hp n hn => (pub_withFns.mp hp).2 n (hin n hn)⟩

/-! ## What the contracts read of memory

Their preconditions, postconditions and leaks read memory only within their
buffers, as forwarding them asks (`Verified.forwardS`). -/

section
open VG.Proof.Ffdh.X86_64.Scrub (bytesAt_of toNat_sw)

theorem bytes_of {m₁ m₂ : Mem} {o : Addr} {len : BitVec 64}
    (h : ∀ a, Region.Contains ⟨o, len.toNat * 1⟩ a 1 → m₁ a = m₂ a) :
    Spec.Rsa.bytesAt m₂ o (len.setWidth abi.ptrBits).toNat = Spec.Rsa.bytesAt m₁ o (len.setWidth abi.ptrBits).toNat := by
  rw [show (len.setWidth abi.ptrBits).toNat = len.toNat from toNat_sw [] len]
  exact bytesAt_of h

end

/-! ## An implementation of the arithmetic, called through slots -/

/-- What the kernel evaluates of a function over the arithmetic with `m`
stack arguments, called through slots: of its body (`Fn.slotBody`), that its
calls can be inlined, that it writes `rsp` only by its calls and uses 8 bytes
of stack below it; of the call with its frame (`Fn.slotted`), the level of
its instructions, that it calls only `nm` and `ns` indirectly, and its stack. -/
noncomputable def entryOk (k bytes m stack : Nat) (name : String)
    (entry : Prog isa → (Nat → Nat → Nat → Prog isa) → Prog isa) (nm ns : String) (bm bs : Prog isa) : Bool :=
  (Fn.slotBody m entry nm ns bm bs).InlineOkNS (slotsOf m [nm, ns]) 1 &&
  (Fn.slotBody m entry nm ns bm bs).all (fun i => !isa.writesSp i) &&
  Nat.ble (Fn.slotBody m entry nm ns bm bs).x86_64Depth 8 &&
  (Fn.slotted bytes m name entry nm ns bm bs).allInstrs (Ins k) &&
  (UpperLock.inames (Fn.slotted bytes m name entry nm ns bm bs)).all (fun n => n == nm || n == ns) &&
  Nat.ble (Fn.slotted bytes m name entry nm ns bm bs).x86_64Depth stack

/-- What `entryOk` shows. -/
structure EntryOk (k bytes m stack : Nat) (name : String)
    (entry : Prog isa → (Nat → Nat → Nat → Prog isa) → Prog isa) (nm ns : String) (bm bs : Prog isa) : Prop where
  inl : (Fn.slotBody m entry nm ns bm bs).InlineOkNS (slotsOf m [nm, ns]) 1 = true
  sp : (Fn.slotBody m entry nm ns bm bs).all (fun i => !isa.writesSp i) = true
  depth : (Fn.slotBody m entry nm ns bm bs).x86_64Depth ≤ 8
  ins : (Fn.slotted bytes m name entry nm ns bm bs).allInstrs (Ins k) = true
  inames : ∀ n ∈ UpperLock.inames (Fn.slotted bytes m name entry nm ns bm bs), n ∈ [nm, ns]
  wdepth : (Fn.slotted bytes m name entry nm ns bm bs).x86_64Depth ≤ stack

theorem EntryOk.of_eval {k bytes m stack : Nat} {name : String}
    {entry : Prog isa → (Nat → Nat → Nat → Prog isa) → Prog isa} {nm ns : String} {bm bs : Prog isa}
    (h : entryOk k bytes m stack name entry nm ns bm bs = true) : EntryOk k bytes m stack name entry nm ns bm bs := by
  simp only [entryOk, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩ := h
  refine ⟨h₁, h₂, h₃, h₄, fun n hn => ?_, h₆⟩
  have := List.all_eq_true.mp h₅ n hn
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with rfl | rfl <;> simp

/-- The tests of the four functions over the arithmetic that it is called
through slots by, for the kernel: one evaluation. -/
noncomputable def entriesOk (k : Nat) (nm ns : String) (bm bs : Prog isa) : Bool :=
  entryOk k 24 0 40 "vg_dsa_validate_public_key_shared" Prevalidated.validate nm ns bm bs &&
  entryOk k 56 4 72 "vg_dsa_verify_prevalidated_shared" Prevalidated.verify nm ns bm bs &&
  entryOk k 24 0 40 "vg_dsa_validate_private_key_shared" PrevalidatedSign.validate nm ns bm bs &&
  entryOk k 40 3 56 "vg_dsa_derive_key_shared" Generate.deriveKey nm ns bm bs

/-- An implementation of the arithmetic (`backend`) that the functions over it
call through slots: its multiplication `nm` (code `bm`) and squaring `ns`
(code `bs`), which run as `M` and `Sq` inlined. -/
structure SlotBackend where
  backend : Backend
  nm : String
  ns : String
  bm : Prog isa
  bs : Prog isa
  M : Mont
  Sq : MontS
  checks : entriesOk backend.level.level nm ns bm bs = true
  validateIn : (Fn.slotBody 0 Prevalidated.validate nm ns bm bs).inlineAll = Prevalidated.validate Sq.mm M.mm
  verifyIn : (Fn.slotBody 4 Prevalidated.verify nm ns bm bs).inlineAll = Prevalidated.verify Sq.mm M.mm
  validatePrivateIn :
    (Fn.slotBody 0 PrevalidatedSign.validate nm ns bm bs).inlineAll = PrevalidatedSign.validate Sq.mm M.mm
  deriveIn : (Fn.slotBody 3 Generate.deriveKey nm ns bm bs).inlineAll = Generate.deriveKey Sq.mm M.mm
  validateMx : (Prevalidated.validate Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true
  verifyMx : (Prevalidated.verify Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true
  validatePrivateMx : (PrevalidatedSign.validate Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true
  deriveMx : (Generate.deriveKey Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true

theorem SlotBackend.ok (A : SlotBackend) :
    EntryOk A.backend.level.level 24 0 40 "vg_dsa_validate_public_key_shared" Prevalidated.validate A.nm A.ns A.bm A.bs ∧
    EntryOk A.backend.level.level 56 4 72 "vg_dsa_verify_prevalidated_shared" Prevalidated.verify A.nm A.ns A.bm A.bs ∧
    EntryOk A.backend.level.level 24 0 40 "vg_dsa_validate_private_key_shared" PrevalidatedSign.validate A.nm A.ns
      A.bm A.bs ∧
    EntryOk A.backend.level.level 40 3 56 "vg_dsa_derive_key_shared" Generate.deriveKey A.nm A.ns A.bm A.bs := by
  have h := A.checks
  simp only [entriesOk, Bool.and_eq_true] at h
  exact ⟨.of_eval h.1.1.1, .of_eval h.1.1.2, .of_eval h.1.2, .of_eval h.2⟩

theorem verify_sat : ∃ s, (Spec.Dsa.verifyPrevalidatedContract abi 72).pre s := by
  have ho : ∃ s, (Spec.Dsa.verifyContract abi 72).pre s ∧ s = prevalidatedSatState := by
    sig_implies_sat [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four, List.range,
      List.range.loop]
      [prevalidatedSatState, verifyingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using prevalidatedSatState
  obtain ⟨s, h, rfl⟩ := ho
  exact ⟨_, prevalidatedPre_of h prevalidatedSat_valid⟩

/-- `Spec.Dsa.verifyPrevalidatedApi`'s function as emitted over `A` meets its
contract in constant time and returns without secret residue. -/
theorem verify_scrubbed (A : SlotBackend) :
    VerifiedScrubbed target (Fn.verifyPrevalidatedS A.backend.level A.nm A.ns A.bm A.bs)
      (Spec.Dsa.verifyPrevalidatedApi.contract (X86_64.abi.withFns [A.nm, A.ns]) 72) 32 := by
  obtain ⟨-, e, -, -⟩ := A.ok
  have hb := prevalidated_slot_verified (fns := [A.nm, A.ns]) A.M A.Sq e.inl
    (by simp only [List.length_cons, List.length_nil]; decide) A.verifyIn A.verifyMx
  have hw : Verified target (Fn.slotted 56 4 "vg_dsa_verify_prevalidated_shared" Prevalidated.verify A.nm A.ns A.bm A.bs)
      (Spec.Dsa.verifyPrevalidatedContract (abi.withFns [A.nm, A.ns]) 72) :=
    Verified.forwardS (sig := Spec.Dsa.verifySig) (bytes := 56) hb (by decide)
      (by simp only [List.length_cons, List.length_nil]; decide) (by decide) e.sp e.depth
      (fun
        | [_, _, _, _, _, _, _, _, _, _], m₁, m₂, _, hb, _, h => by
          simp only [Spec.Dsa.verifySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, Elem.size] at hb
          change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ m₁ at h
          change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ m₂
          dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
          erw [bytes_of hb.1]
          exact h)
      (fun
        | [_, _, _, _, _, _, _, _, _, _], m₁, m₂, m', r, _, hb, _, h => by
          simp only [Spec.Dsa.verifySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, Elem.size] at hb
          change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ m₁ m' r at h
          change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ m₂ m' r
          dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
          erw [bytes_of hb.1, bytes_of hb.2.1, bytes_of hb.2.2.1]
          exact h)
      (fun | [_, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, _, _, h => h)
      verify_sat
      (fun
        | [_, _, _, _, _, _, _, _, _, _], m₁, m₂, _, hb, _ => by
          simp only [Spec.Dsa.verifySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, Elem.size] at hb
          change @Curry.apply (Mem → List Nat) [_, _, _, _, _, _, _, _, _, _] _ _ m₁ = @Curry.apply (Mem → List Nat) [_, _, _, _, _, _, _, _, _, _] _ _ m₂
          dsimp only [Curry.apply, ArgWord.ofRaw]
          erw [bytes_of hb.1, bytes_of hb.2.1, bytes_of hb.2.2.1]
          rfl)
  exact scrubbedFns A.backend.level 72 hw (forwardS_spSafe e.sp) e.wdepth e.ins e.inames (by decide) rfl
    (Proof.Dsa.X86_64.Scrub.verifyPrevalidatedOut 72)

theorem validatePublic_sat40 : ∃ s, (Spec.Dsa.validatePublicKeyContract abi 40).pre s := by
  sig_implies_sat [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argRegs,
    stackArgs_zero, List.range, List.range.loop]
    [validatingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using validatingSatState

/-- `Spec.Dsa.validatePublicKeyApi`'s function as emitted over `A` meets its contract in
constant time and returns without secret residue. -/
theorem validatePublic_scrubbed (A : SlotBackend) :
    VerifiedScrubbed target (Fn.validatePublicKeyS A.backend.level A.nm A.ns A.bm A.bs)
      (Spec.Dsa.validatePublicKeyApi.contract (X86_64.abi.withFns [A.nm, A.ns]) 40) 32 := by
  obtain ⟨e, -, -, -⟩ := A.ok
  have hb := validating_slot_verified (fns := [A.nm, A.ns]) A.M A.Sq e.inl
    (by simp only [List.length_cons, List.length_nil]; decide) A.validateIn A.validateMx
  have hw : Verified target (Fn.slotted 24 0 "vg_dsa_validate_public_key_shared" Prevalidated.validate A.nm A.ns A.bm A.bs)
      (Spec.Dsa.validatePublicKeyContract (abi.withFns [A.nm, A.ns]) 40) :=
    Verified.forwardS (sig := Spec.Dsa.validatePublicKeySig) (bytes := 24) hb (by decide)
      (by simp only [List.length_cons, List.length_nil]; decide) (by decide) e.sp e.depth
      (fun | [_, _, _, _, _, _], _, _, _, _, _, h => h)
      (fun
        | [_, _, _, _, _, _], m₁, m₂, m', r, _, hb, _, h => by
          simp only [Spec.Dsa.validatePublicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, Elem.size] at hb
          change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _] _ _ m₁ m' r at h
          change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _] _ _ m₂ m' r
          dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
          erw [bytes_of hb.1]
          exact h)
      (fun | [_, _, _, _, _, _], _, _, _, _, _, _, _, _, h => h)
      validatePublic_sat40
      (fun
        | [_, _, _, _, _, _], m₁, m₂, _, hb, _ => by
          simp only [Spec.Dsa.validatePublicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, Elem.size] at hb
          change @Curry.apply (Mem → List Nat) [_, _, _, _, _, _] _ _ m₁ = @Curry.apply (Mem → List Nat) [_, _, _, _, _, _] _ _ m₂
          dsimp only [Curry.apply, ArgWord.ofRaw]
          erw [bytes_of hb.1]
          rfl)
  exact scrubbedFns A.backend.level 40 hw (forwardS_spSafe e.sp) e.wdepth e.ins e.inames (by decide) rfl
    (Proof.Dsa.X86_64.Scrub.validatePublicKeyOut 40)

theorem validatePrivate_sat40 : ∃ s, (Spec.Dsa.validatePrivateKeyContract abi 40).pre s := by
  sig_implies_sat [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs,
    stackArgs_zero, List.range, List.range.loop]
    [privateSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using privateSatState

/-- `Spec.Dsa.validatePrivateKeyApi`'s function as emitted over `A` meets its contract in
constant time and returns without secret residue. -/
theorem validatePrivate_scrubbed (A : SlotBackend) :
    VerifiedScrubbed target (Fn.validatePrivateKeyS A.backend.level A.nm A.ns A.bm A.bs)
      (Spec.Dsa.validatePrivateKeyApi.contract (X86_64.abi.withFns [A.nm, A.ns]) 40) 32 := by
  obtain ⟨-, -, e, -⟩ := A.ok
  have hb := validating_private_slot_verified (fns := [A.nm, A.ns]) A.M A.Sq e.inl
    (by simp only [List.length_cons, List.length_nil]; decide) A.validatePrivateIn A.validatePrivateMx
  have hw : Verified target (Fn.slotted 24 0 "vg_dsa_validate_private_key_shared" PrevalidatedSign.validate A.nm A.ns A.bm A.bs)
      (Spec.Dsa.validatePrivateKeyContract (abi.withFns [A.nm, A.ns]) 40) :=
    Verified.forwardS (sig := Spec.Dsa.validatePrivateKeySig) (bytes := 24) hb (by decide)
      (by simp only [List.length_cons, List.length_nil]; decide) (by decide) e.sp e.depth
      (fun | [_, _, _, _, _, _], _, _, _, _, _, h => h)
      (fun
        | [_, _, _, _, _, _], m₁, m₂, m', r, _, hb, _, h => by
          simp only [Spec.Dsa.validatePrivateKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, Elem.size] at hb
          change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _] _ _ m₁ m' r at h
          change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _] _ _ m₂ m' r
          dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
          erw [bytes_of hb.1]
          exact h)
      (fun | [_, _, _, _, _, _], _, _, _, _, _, _, _, _, h => h)
      validatePrivate_sat40
      (fun
        | [_, _, _, _, _, _], m₁, m₂, _, hb, _ => by
          simp only [Spec.Dsa.validatePrivateKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, Elem.size] at hb
          change @Curry.apply (Mem → List Nat) [_, _, _, _, _, _] _ _ m₁ = @Curry.apply (Mem → List Nat) [_, _, _, _, _, _] _ _ m₂
          dsimp only [Curry.apply, ArgWord.ofRaw]
          erw [bytes_of hb.1]
          rfl)
  exact scrubbedFns A.backend.level 40 hw (forwardS_spSafe e.sp) e.wdepth e.ins e.inames (by decide) rfl
    (Proof.Dsa.X86_64.Scrub.validatePrivateKeyOut 40)

theorem deriveKey_sat56 : ∃ s, (Spec.Dsa.deriveKeyContract abi 56).pre s := by
  sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range,
    List.range.loop]
    [deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using deriveSatState

/-- `Spec.Dsa.deriveKeyApi`'s function as emitted over `A` meets its contract in
constant time and returns without secret residue. -/
theorem deriveKey_scrubbed (A : SlotBackend) :
    VerifiedScrubbed target (Fn.deriveKeyS A.backend.level A.nm A.ns A.bm A.bs)
      (Spec.Dsa.deriveKeyApi.contract (X86_64.abi.withFns [A.nm, A.ns]) 56) 32 := by
  obtain ⟨-, -, -, e⟩ := A.ok
  have hb := derive_slot_verified (fns := [A.nm, A.ns]) A.M A.Sq e.inl
    (by simp only [List.length_cons, List.length_nil]; decide) A.deriveIn A.deriveMx
  have hw : Verified target (Fn.slotted 40 3 "vg_dsa_derive_key_shared" Generate.deriveKey A.nm A.ns A.bm A.bs)
      (Spec.Dsa.deriveKeyContract (abi.withFns [A.nm, A.ns]) 56) :=
    Verified.forwardS (sig := Spec.Dsa.deriveKeySig) (bytes := 40) hb (by decide)
      (by simp only [List.length_cons, List.length_nil]; decide) (by decide) e.sp e.depth
      (fun | [_, _, _, _, _, _, _, _, _], _, _, _, _, _, h => h)
      (fun
        | [_, _, _, _, _, _, _, _, _], m₁, m₂, m', r, _, hb, _, h => by
          simp only [Spec.Dsa.deriveKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, Elem.size] at hb
          change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _] _ _ m₁ m' r at h
          change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _] _ _ m₂ m' r
          dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
          erw [bytes_of hb.2.1, bytes_of hb.2.2.1]
          exact h)
      (fun
        | [_, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, _, hb, _, h => by
          simp only [Spec.Dsa.deriveKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, Elem.size] at hb
          change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _] _ _ m m₁ r at h
          change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _] _ _ m m₂ r
          dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
          erw [bytes_of hb.1]
          exact h)
      deriveKey_sat56
      (fun
        | [_, _, _, _, _, _, _, _, _], m₁, m₂, _, hb, _ => by
          simp only [Spec.Dsa.deriveKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, Elem.size] at hb
          change @Curry.apply (Mem → List Nat) [_, _, _, _, _, _, _, _, _] _ _ m₁ = @Curry.apply (Mem → List Nat) [_, _, _, _, _, _, _, _, _] _ _ m₂
          dsimp only [Curry.apply, ArgWord.ofRaw]
          erw [bytes_of hb.2.1, bytes_of hb.2.2.1]
          rfl)
  exact scrubbedFns A.backend.level 56 hw (forwardS_spSafe e.sp) e.wdepth e.ins e.inames (by decide) rfl
    (Proof.Dsa.X86_64.Scrub.deriveKeyOut 56)

theorem validatePublic_spSafe (A : SlotBackend) :
    (Fn.validatePublicKeyS A.backend.level A.nm A.ns A.bm A.bs).all (fun i => !isa.writesSp i) = true := by
  obtain ⟨e, -, -, -⟩ := A.ok
  exact scrubKs_spSafe (forwardS_spSafe e.sp)

theorem verify_spSafe (A : SlotBackend) :
    (Fn.verifyPrevalidatedS A.backend.level A.nm A.ns A.bm A.bs).all (fun i => !isa.writesSp i) = true := by
  obtain ⟨-, e, -, -⟩ := A.ok
  exact scrubKs_spSafe (forwardS_spSafe e.sp)

theorem validatePrivate_spSafe (A : SlotBackend) :
    (Fn.validatePrivateKeyS A.backend.level A.nm A.ns A.bm A.bs).all (fun i => !isa.writesSp i) = true := by
  obtain ⟨-, -, e, -⟩ := A.ok
  exact scrubKs_spSafe (forwardS_spSafe e.sp)

theorem deriveKey_spSafe (A : SlotBackend) :
    (Fn.deriveKeyS A.backend.level A.nm A.ns A.bm A.bs).all (fun i => !isa.writesSp i) = true := by
  obtain ⟨-, -, -, e⟩ := A.ok
  exact scrubKs_spSafe (forwardS_spSafe e.sp)

end VG.Proof.Dsa.X86_64.Slots
