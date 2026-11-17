module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Init
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.InitCT
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTCryptFn
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamFinish
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTFin
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamVerify
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTVerify
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Seal
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTSeal
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Open
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTOpen
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sm4Gcm.Scratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs

/-! ### `Sm4Gcm.PPC64LE.Verified`, which only this module used -/

section

/-!
# SM4-GCM on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time,
a state satisfying each precondition, and the shared contracts of
`Spec/Sm4/Gcm/Contract.lean` with AES-GCM's working space (320 doublewords)
and SM4's (`sm4`, 408) as the last two arguments (`scratch2`; with no
stack: the code calls nothing, and each function saves the link register in
`W`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE

/-- The shared contract of `sig`, with AES-GCM's working space `nm` and
SM4's `sm4` as two more arguments, whatever they hold. -/
abbrev scratch2 (sig : Sig) (nm : String) (pre : Curry (sig.words PPC64LE.abi.ptrBits) (Mem → Prop))
    (post : sig.Post PPC64LE.abi.ptrBits)
    (leak : Option (Curry (sig.words PPC64LE.abi.ptrBits) (Mem → List Nat)) := none) : Contract isa :=
  Sig.scratchContract PPC64LE.abi (sig.withScratch nm .u64 320) "sm4" .u64 408
    (Curry.withScratch PPC64LE.abi.ptrBits nm .u64 320 sig.params pre)
    (Curry.withScratch PPC64LE.abi.ptrBits nm .u64 320 sig.params post) true 0
    (leak.map (Curry.withScratch PPC64LE.abi.ptrBits nm .u64 320 sig.params))

theorem init_correct (s : State) (hs : initPPC64LE.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initPPC64LE.post s s' :=
  init_wp hs

theorem streamEncrypt_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : streamEncryptPPC64LE.pre s) :
    ∃ t s', Exec isa streamEncrypt s t s' ∧ abiPreserved s s' ∧ streamEncryptPPC64LE.post s s' :=
  streamEncrypt_wp hs

theorem streamDecrypt_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : streamDecryptPPC64LE.pre s) :
    ∃ t s', Exec isa streamDecrypt s t s' ∧ abiPreserved s s' ∧ streamDecryptPPC64LE.post s s' :=
  streamDecrypt_wp hs

theorem streamFinish_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : streamFinishPPC64LE.pre s) :
    ∃ t s', Exec isa streamFinish s t s' ∧ abiPreserved s s' ∧ streamFinishPPC64LE.post s s' :=
  streamFinish_wp hs

theorem streamVerify_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : streamVerifyPPC64LE.pre s) :
    ∃ t s', Exec isa streamVerify s t s' ∧ abiPreserved s s' ∧ streamVerifyPPC64LE.post s s' :=
  streamVerify_wp hs

theorem seal_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : sealPPC64LE.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealPPC64LE.post s s' :=
  seal_wp hs

theorem open_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : openPPC64LE.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openPPC64LE.post s s' :=
  open_wp hs

/-! ## States satisfying the preconditions (with empty buffers) -/

def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x4000 | .r6 => 0x6000 | _ => 0
  lr := 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩, ⟨0x6000, 3264⟩]

def streamCryptSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r7 => 0x2000 | .r9 => 0x4000 | .r10 => 0x6000 | _ => 0
  lr := 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩, ⟨0x6000, 3264⟩]

def finSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r7 => 0x5000 | .r8 => 0x4000 | .r9 => 0x6000 | _ => 0
  lr := 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩, ⟨0x6000, 3264⟩]

def verSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r7 => 0x5000 | .r9 => 0x4000 | .r10 => 0x6000 | _ => 0
  lr := 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩, ⟨0x6000, 3264⟩]

/-! ## The shared contracts -/

theorem init_verified :
    Verified PPC64LE.target init (scratch2 Spec.Sm4.Gcm.initSig "scratch" (Curry.const (fun _ => True) _)
      (Spec.Sm4.Gcm.initPost PPC64LE.abi.ptrBits)) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.initSig,
      Spec.Sm4.Gcm.initPost, initPPC64LE, PPC64LE.abi, PPC64LE.argRegs] [initSat] using initSat)

theorem streamEncrypt_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target streamEncrypt (scratch2 Spec.Sm4.Gcm.streamCryptSig "scratch"
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamEncryptPost PPC64LE.abi.ptrBits)) :=
  Verified.of_correct streamEncrypt_correct streamEncrypt_ct (by
    sig_implies [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.streamCryptSig,
      Spec.Sm4.Gcm.streamEncryptPost, streamEncryptPPC64LE, streamCryptPre, streamCryptPub, PPC64LE.abi,
      PPC64LE.argRegs] [streamCryptSat] using streamCryptSat)

theorem streamDecrypt_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target streamDecrypt (scratch2 Spec.Sm4.Gcm.streamCryptSig "scratch"
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamDecryptPost PPC64LE.abi.ptrBits)) :=
  Verified.of_correct streamDecrypt_correct streamDecrypt_ct (by
    sig_implies [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.streamCryptSig,
      Spec.Sm4.Gcm.streamDecryptPost, streamDecryptPPC64LE, streamCryptPre, streamCryptPub, PPC64LE.abi,
      PPC64LE.argRegs] [streamCryptSat] using streamCryptSat)

theorem streamFinish_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target streamFinish (scratch2 Spec.Sm4.Gcm.streamFinishSig "work"
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamFinishPost PPC64LE.abi.ptrBits)) :=
  Verified.of_correct streamFinish_correct streamFinish_ct (by
    sig_implies [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.streamFinishSig,
      Spec.Sm4.Gcm.streamFinishPost, streamFinishPPC64LE, finPre, PPC64LE.abi, PPC64LE.argRegs]
      [finSat] using finSat)

theorem streamVerify_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target streamVerify (scratch2 Spec.Sm4.Gcm.streamVerifySig "work"
      (Curry.const (fun _ => True) _) (Spec.Sm4.Gcm.streamVerifyPost PPC64LE.abi.ptrBits)) :=
  Verified.of_correct streamVerify_correct streamVerify_ct (by
    sig_implies [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.streamVerifySig,
      Spec.Sm4.Gcm.streamVerifyPost, streamVerifyPPC64LE, verPre, PPC64LE.abi, PPC64LE.argRegs]
      [verSat] using verSat)

/-- The working space at `0x6000` and SM4's at `0x7000`, the stack arguments. -/
def sealSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | .r8 => 0x2800 | .r10 => 0x5000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9061 then 0x60 else bif Nat.beq a.toNat 0x9069 then 0x70 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9060, 16⟩]
  wr := [⟨0x2800, 0⟩, ⟨0x5000, 16⟩, ⟨0x6000, 2560⟩, ⟨0x7000, 3264⟩]

theorem seal_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target «seal» (scratch2 Spec.Sm4.Gcm.sealSig "work" (Curry.const (fun _ => True) _)
      (Spec.Sm4.Gcm.sealPost PPC64LE.abi.ptrBits)) :=
  Verified.of_correct seal_correct seal_ct (by
    sig_implies [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.sealSig,
      Spec.Sm4.Gcm.sealPost, sealPPC64LE, sealPre, onePub, args, PPC64LE.abi, PPC64LE.argRegs,
      stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

/-- `tag_len` 0, the working space at `0x6000` and SM4's at `0x7000`, the stack arguments. -/
def openSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | .r8 => 0x2800 | .r10 => 0x5000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9069 then 0x60 else bif Nat.beq a.toNat 0x9071 then 0x70 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9060, 24⟩]
  wr := [⟨0x2800, 0⟩, ⟨0x6000, 2560⟩, ⟨0x7000, 3264⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The postconditions match on `openResult`; the result is the low 32 bits
of `r3`; and `open`'s public data include its leak, whether it succeeds. -/
theorem open_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target «open» (scratch2 Spec.Sm4.Gcm.openSig "work" (Curry.const (fun _ => True) _)
      (Spec.Sm4.Gcm.openPost PPC64LE.abi.ptrBits) (some (Spec.Sm4.Gcm.openLeak PPC64LE.abi.ptrBits))) :=
  Verified.of_correct open_correct open_ct
    { pre := by
        sig_implies_pre [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.openSig,
          openPPC64LE, openPre, onePub, args, PPC64LE.abi, PPC64LE.argRegs,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        intro s s' _ h
        sig_eval [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Sm4.Gcm.openSig,
          Spec.Sm4.Gcm.openPost, PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range,
          List.range.loop]
        simp only [openPPC64LE] at h
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.openSig,
          Spec.Sm4.Gcm.openLeak, openPPC64LE, openPre, onePub, args, PPC64LE.abi, PPC64LE.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2⟩ := h
        refine ⟨⟨h3, h4, h5, h6, h7, h8, h9, h10, hsp, fun i hi => ?_⟩, leak_bool hl⟩
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_using [hi]) with rfl | rfl | rfl
        · exact a0
        · exact a1
        · exact a2
      sat := by
        sig_implies_sat [scratch2, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sm4.Gcm.openSig,
          openPPC64LE, openPre, onePub, args, PPC64LE.abi, PPC64LE.argRegs,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
          [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

end VG.Proof.Sm4Gcm.PPC64LE

end

end

/-! ### `Sm4Gcm.PPC64LE.Scratch`, which only this module used -/

section

/-!
# SM4-GCM on PPC64LE: two working spaces

Untrusted: everything here is checked by Lean. The functions keep AES-GCM's
working space and SM4's each in a frame of their own (a frame is less than
a page, too small for both): around the code, proved with both as its last
two arguments, a frame allocates SM4's, and around that frame another
allocates AES-GCM's. Each frame needs the contract of the code inside it to
read the memory on entry only within the function's buffers; the inner
frame's contract has AES-GCM's working space as one more argument, which
it ignores (`Curry.withScratch`), and stays local (`local_withScratch`,
`leakLocal_withScratch`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG

/-- A function of the arguments and the memory on entry that reads the
memory only within the buffers does so too taking one more array argument,
last, which it ignores. -/
theorem local_withScratch {α : Type} {pb : Nat} {sig : Sig} (nm : String) (e : Elem) (n : Nat)
    {f : Curry (sig.words pb) (Mem → α)} {R : α → α → Prop}
    (h : ∀ vs m₁ m₂, vs.length = (sig.words pb).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      R (Curry.apply (sig.words pb) f vs m₁) (Curry.apply (sig.words pb) f vs m₂)) :
    ∀ vs m₁ m₂, vs.length = ((sig.withScratch nm e n).words pb).length →
      (∀ b ∈ Sig.bufs (sig.withScratch nm e n).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      R (Curry.apply _ (Curry.withScratch pb nm e n sig.params f) vs m₁)
        (Curry.apply _ (Curry.withScratch pb nm e n sig.params f) vs m₂) := by
  intro vs m₁ m₂ hl hb
  rw [Sig.words_withScratch, List.length_append, List.length_singleton] at hl
  obtain ⟨vs', x, rfl⟩ : ∃ vs' x, vs = vs' ++ [x] := by
    rcases List.eq_nil_or_concat vs with h0 | ⟨L, b, rfl⟩
    · subst h0; simp at hl
    · exact ⟨L, b, List.concat_eq_append ..⟩
  have hl' : vs'.length = (sig.words pb).length := by
    rw [List.length_append, List.length_singleton] at hl; omega_using [hl]
  show R (Curry.apply _ (Curry.withScratch pb nm e n sig.params f) (vs' ++ [x]) m₁)
    (Curry.apply _ (Curry.withScratch pb nm e n sig.params f) (vs' ++ [x]) m₂)
  rw [Curry.apply_withScratch pb nm e n sig.params f vs' x hl']
  refine h vs' m₁ m₂ hl' fun b hb' => hb b ?_
  show b ∈ Sig.bufs (sig.params ++ [((nm, .array true e n) : String × Param)]) (vs' ++ [x])
  rw [Sig.bufs_append_array pb nm e n x sig.params vs' hl']
  exact List.mem_append_left _ hb'

/-- `local_withScratch`, for a precondition. -/
theorem pre_withScratch {pb : Nat} {sig : Sig} (nm : String) (e : Elem) (n : Nat)
    {pre : Curry (sig.words pb) (Mem → Prop)}
    (h : ∀ vs m₁ m₂, vs.length = (sig.words pb).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words pb) pre vs m₁ → Curry.apply (sig.words pb) pre vs m₂) :
    ∀ vs m₁ m₂, vs.length = ((sig.withScratch nm e n).words pb).length →
      (∀ b ∈ Sig.bufs (sig.withScratch nm e n).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply _ (Curry.withScratch pb nm e n sig.params pre) vs m₁ →
        Curry.apply _ (Curry.withScratch pb nm e n sig.params pre) vs m₂ :=
  local_withScratch nm e n (R := fun P Q => P → Q) h

/-- `local_withScratch`, for a postcondition. -/
theorem post_withScratch {pb : Nat} {sig : Sig} (nm : String) (e : Elem) (n : Nat) {post : sig.Post pb}
    (h : ∀ vs m₁ m₂ m' r, vs.length = (sig.words pb).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words pb) post vs m₁ m' r → Curry.apply (sig.words pb) post vs m₂ m' r) :
    ∀ vs m₁ m₂ m' r, vs.length = ((sig.withScratch nm e n).words pb).length →
      (∀ b ∈ Sig.bufs (sig.withScratch nm e n).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply _ (Curry.withScratch pb nm e n sig.params post) vs m₁ m' r →
        Curry.apply _ (Curry.withScratch pb nm e n sig.params post) vs m₂ m' r :=
  fun vs m₁ m₂ m' r hl hb => local_withScratch nm e n
    (R := fun (P Q : Mem → BitVec (sig.retBits pb) → Prop) => ∀ m' r, P m' r → Q m' r)
    (fun vs m₁ m₂ hl hb m' r => h vs m₁ m₂ m' r hl hb) vs m₁ m₂ hl hb m' r

/-- A postcondition that reads the memory on return only within the buffers
still does, taking one more array argument. -/
theorem postOut_withScratch {pb : Nat} {sig : Sig} (nm : String) (e : Elem) (n : Nat) {post : sig.Post pb}
    (h : ∀ vs m m₁ m₂ r, vs.length = (sig.words pb).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words pb) post vs m m₁ r → Curry.apply (sig.words pb) post vs m m₂ r) :
    ∀ vs m m₁ m₂ r, vs.length = ((sig.withScratch nm e n).words pb).length →
      (∀ b ∈ Sig.bufs (sig.withScratch nm e n).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply _ (Curry.withScratch pb nm e n sig.params post) vs m m₁ r →
        Curry.apply _ (Curry.withScratch pb nm e n sig.params post) vs m m₂ r := by
  intro vs m m₁ m₂ r hl hb
  rw [Sig.words_withScratch, List.length_append, List.length_singleton] at hl
  obtain ⟨vs', x, rfl⟩ : ∃ vs' x, vs = vs' ++ [x] := by
    rcases List.eq_nil_or_concat vs with h0 | ⟨L, b, rfl⟩
    · subst h0; simp at hl
    · exact ⟨L, b, List.concat_eq_append ..⟩
  have hl' : vs'.length = (sig.words pb).length := by
    rw [List.length_append, List.length_singleton] at hl; omega_using [hl]
  show Curry.apply _ (Curry.withScratch pb nm e n sig.params post) (vs' ++ [x]) m m₁ r →
    Curry.apply _ (Curry.withScratch pb nm e n sig.params post) (vs' ++ [x]) m m₂ r
  rw [Curry.apply_withScratch pb nm e n sig.params post vs' x hl']
  refine h vs' m m₁ m₂ r hl' fun b hb' => hb b ?_
  show b ∈ Sig.bufs (sig.params ++ [((nm, .array true e n) : String × Param)]) (vs' ++ [x])
  rw [Sig.bufs_append_array pb nm e n x sig.params vs' hl']
  exact List.mem_append_left _ hb'

/-- A leak local within the buffers stays local taking one more array argument. -/
theorem leakLocal_withScratch {pb : Nat} {sig : Sig} (nm : String) (e : Elem) (n : Nat)
    {leak : Option (Curry (sig.words pb) (Mem → List Nat))} (h : Sig.LeakLocal pb sig leak) :
    Sig.LeakLocal pb (sig.withScratch nm e n) (leak.map (Curry.withScratch pb nm e n sig.params)) := by
  cases leak with
  | none => trivial
  | some f => exact local_withScratch nm e n (R := Eq) h

end VG.Proof.Sm4Gcm.PPC64LE

end

end


/-!
# SM4-GCM on PPC64LE, with its working spaces on the stack

Each function runs its code, proved with AES-GCM's working space and SM4's
as its last two arguments (`Verified.lean`), in two frames: the inner one
allocates SM4's (3296 bytes), the outer one AES-GCM's (2592 bytes), each
less than a page (`Verified.stackScratch`). The inner frame's contract is
the function's with AES-GCM's working space as one more argument, which the
pre- and postcondition ignore (`Scratch.lean`). For `seal` and `open`, whose
working spaces arrive on the stack, each frame also copies the stack
arguments before them (`Verified.stackScratchArgs`): 2672 and 3376 bytes for
`seal`, 2672 and 3392 for `open`.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE

/-! ## `init` -/

def initInnerSat : State := { initSat with wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩] }

theorem initInnerSat_pre : ∃ s, ((Spec.Sm4.Gcm.initSig.withScratch "scratch" .u64 320).contract PPC64LE.abi
    (Curry.withScratch PPC64LE.abi.ptrBits "scratch" .u64 320 Spec.Sm4.Gcm.initSig.params
      (Curry.const (fun _ => True) _))
    (Curry.withScratch PPC64LE.abi.ptrBits "scratch" .u64 320 Spec.Sm4.Gcm.initSig.params
      (Spec.Sm4.Gcm.initPost PPC64LE.abi.ptrBits)) true (0 + 3296)).pre s := by
  implies_sat [Sig.withScratch, Curry.withScratch, Curry.app, Spec.Sm4.Gcm.initSig, Spec.Sm4.Gcm.initPost,
    PPC64LE.abi, PPC64LE.argRegs] [initInnerSat, initSat] using initInnerSat

def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.initContract PPC64LE.abi 5888).pre s := by
  implies_sat [Spec.Sm4.Gcm.initContract, Spec.Sm4.Gcm.initSig, Spec.Sm4.Gcm.initPost, PPC64LE.abi,
    PPC64LE.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r5
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r6 init))
      (Spec.Sm4.Gcm.initContract PPC64LE.abi 5888) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.initPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 3296) (bytes := 2592)
    (PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.initSig.withScratch "scratch" .u64 320) (nm := "sm4")
      (e := .u64) (n := 408) (wa := true) (stack := 0) (bytes := 3296) init_verified (by decide) (by decide)
      (pre_withScratch "scratch" .u64 320 (Proof.Sm4Gcm.pre_local _ _))
      (post_withScratch "scratch" .u64 320 (Proof.Sm4Gcm.initPost_local _))
      (fun vs m m₁ m₂ r hl _ => postOut_withScratch "scratch" .u64 320 (Proof.Sm4Gcm.initPostOut_local _) vs m m₁ m₂ r hl) initInnerSat_pre)
    (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.initPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.initPostOut_local _ vs m m₁ m₂ r hl) initFrameSat_pre

/-! ## `stream_encrypt` -/

def streamEncryptInnerSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩] }

theorem streamEncryptInnerSat_pre : ∃ s, ((Spec.Sm4.Gcm.streamCryptSig.withScratch "scratch" .u64 320).contract PPC64LE.abi
    (Curry.withScratch PPC64LE.abi.ptrBits "scratch" .u64 320 Spec.Sm4.Gcm.streamCryptSig.params (Curry.const (fun _ => True) _))
    (Curry.withScratch PPC64LE.abi.ptrBits "scratch" .u64 320 Spec.Sm4.Gcm.streamCryptSig.params (Spec.Sm4.Gcm.streamEncryptPost PPC64LE.abi.ptrBits)) true
    (0 + 3296)).pre s := by
  implies_sat [Sig.withScratch, Curry.withScratch, Curry.app, Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamEncryptPost, PPC64LE.abi, PPC64LE.argRegs]
    [streamEncryptInnerSat, streamCryptSat] using streamEncryptInnerSat

def streamEncryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamCryptSig.contract PPC64LE.abi (post := Spec.Sm4.Gcm.streamEncryptPost PPC64LE.abi.ptrBits)
    (writeArgs := true) (stack := 5888)).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamEncryptPost, PPC64LE.abi, PPC64LE.argRegs] [streamEncryptFrameSat, streamCryptSat] using streamEncryptFrameSat

theorem streamEncrypt_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 streamEncrypt))
      (Spec.Sm4.Gcm.streamCryptSig.contract PPC64LE.abi (post := Spec.Sm4.Gcm.streamEncryptPost PPC64LE.abi.ptrBits) (writeArgs := true) (stack := 5888)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.streamEncryptPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 3296) (bytes := 2592)
    (PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig.withScratch "scratch" .u64 320) (nm := "sm4")
      (e := .u64) (n := 408) (wa := true) (stack := 0) (bytes := 3296) streamEncrypt_verified (by decide) (by decide)
      (pre_withScratch "scratch" .u64 320 (Proof.Sm4Gcm.pre_local _ _))
      (post_withScratch "scratch" .u64 320 (Proof.Sm4Gcm.streamEncryptPost_local _))
      (fun vs m m₁ m₂ r hl _ => postOut_withScratch "scratch" .u64 320 (Proof.Sm4Gcm.streamEncryptPostOut_local _) vs m m₁ m₂ r hl) streamEncryptInnerSat_pre)
    (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.streamEncryptPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.streamEncryptPostOut_local _ vs m m₁ m₂ r hl) streamEncryptFrameSat_pre

/-! ## `stream_decrypt` -/

def streamDecryptInnerSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩] }

theorem streamDecryptInnerSat_pre : ∃ s, ((Spec.Sm4.Gcm.streamCryptSig.withScratch "scratch" .u64 320).contract PPC64LE.abi
    (Curry.withScratch PPC64LE.abi.ptrBits "scratch" .u64 320 Spec.Sm4.Gcm.streamCryptSig.params (Curry.const (fun _ => True) _))
    (Curry.withScratch PPC64LE.abi.ptrBits "scratch" .u64 320 Spec.Sm4.Gcm.streamCryptSig.params (Spec.Sm4.Gcm.streamDecryptPost PPC64LE.abi.ptrBits)) true
    (0 + 3296)).pre s := by
  implies_sat [Sig.withScratch, Curry.withScratch, Curry.app, Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamDecryptPost, PPC64LE.abi, PPC64LE.argRegs]
    [streamDecryptInnerSat, streamCryptSat] using streamDecryptInnerSat

def streamDecryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamCryptSig.contract PPC64LE.abi (post := Spec.Sm4.Gcm.streamDecryptPost PPC64LE.abi.ptrBits)
    (writeArgs := true) (stack := 5888)).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamDecryptPost, PPC64LE.abi, PPC64LE.argRegs] [streamDecryptFrameSat, streamCryptSat] using streamDecryptFrameSat

theorem streamDecrypt_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 streamDecrypt))
      (Spec.Sm4.Gcm.streamCryptSig.contract PPC64LE.abi (post := Spec.Sm4.Gcm.streamDecryptPost PPC64LE.abi.ptrBits) (writeArgs := true) (stack := 5888)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.streamDecryptPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 3296) (bytes := 2592)
    (PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig.withScratch "scratch" .u64 320) (nm := "sm4")
      (e := .u64) (n := 408) (wa := true) (stack := 0) (bytes := 3296) streamDecrypt_verified (by decide) (by decide)
      (pre_withScratch "scratch" .u64 320 (Proof.Sm4Gcm.pre_local _ _))
      (post_withScratch "scratch" .u64 320 (Proof.Sm4Gcm.streamDecryptPost_local _))
      (fun vs m m₁ m₂ r hl _ => postOut_withScratch "scratch" .u64 320 (Proof.Sm4Gcm.streamDecryptPostOut_local _) vs m m₁ m₂ r hl) streamDecryptInnerSat_pre)
    (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.streamDecryptPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.streamDecryptPostOut_local _ vs m m₁ m₂ r hl) streamDecryptFrameSat_pre

/-! ## `stream_finish` -/

def streamFinishInnerSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩] }

theorem streamFinishInnerSat_pre : ∃ s, ((Spec.Sm4.Gcm.streamFinishSig.withScratch "work" .u64 320).contract PPC64LE.abi
    (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.streamFinishSig.params (Curry.const (fun _ => True) _))
    (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.streamFinishSig.params (Spec.Sm4.Gcm.streamFinishPost PPC64LE.abi.ptrBits)) true
    (0 + 3296)).pre s := by
  implies_sat [Sig.withScratch, Curry.withScratch, Curry.app, Spec.Sm4.Gcm.streamFinishSig, Spec.Sm4.Gcm.streamFinishPost, PPC64LE.abi, PPC64LE.argRegs]
    [streamFinishInnerSat, finSat] using streamFinishInnerSat

def streamFinishFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem streamFinishFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamFinishSig.contract PPC64LE.abi (post := Spec.Sm4.Gcm.streamFinishPost PPC64LE.abi.ptrBits)
    (writeArgs := true) (stack := 5888)).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamFinishSig, Spec.Sm4.Gcm.streamFinishPost, PPC64LE.abi, PPC64LE.argRegs] [streamFinishFrameSat, finSat] using streamFinishFrameSat

theorem streamFinish_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r8
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r9 streamFinish))
      (Spec.Sm4.Gcm.streamFinishSig.contract PPC64LE.abi (post := Spec.Sm4.Gcm.streamFinishPost PPC64LE.abi.ptrBits) (writeArgs := true) (stack := 5888)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamFinishSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.streamFinishPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 3296) (bytes := 2592)
    (PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamFinishSig.withScratch "work" .u64 320) (nm := "sm4")
      (e := .u64) (n := 408) (wa := true) (stack := 0) (bytes := 3296) streamFinish_verified (by decide) (by decide)
      (pre_withScratch "work" .u64 320 (Proof.Sm4Gcm.pre_local _ _))
      (post_withScratch "work" .u64 320 (Proof.Sm4Gcm.streamFinishPost_local _))
      (fun vs m m₁ m₂ r hl _ => postOut_withScratch "work" .u64 320 (Proof.Sm4Gcm.streamFinishPostOut_local _) vs m m₁ m₂ r hl) streamFinishInnerSat_pre)
    (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.streamFinishPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.streamFinishPostOut_local _ vs m m₁ m₂ r hl) streamFinishFrameSat_pre

/-! ## `stream_verify` -/

def streamVerifyInnerSat : State := { verSat with wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩] }

theorem streamVerifyInnerSat_pre : ∃ s, ((Spec.Sm4.Gcm.streamVerifySig.withScratch "work" .u64 320).contract PPC64LE.abi
    (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.streamVerifySig.params (Curry.const (fun _ => True) _))
    (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.streamVerifySig.params (Spec.Sm4.Gcm.streamVerifyPost PPC64LE.abi.ptrBits)) true
    (0 + 3296)).pre s := by
  implies_sat [Sig.withScratch, Curry.withScratch, Curry.app, Spec.Sm4.Gcm.streamVerifySig, Spec.Sm4.Gcm.streamVerifyPost, PPC64LE.abi, PPC64LE.argRegs]
    [streamVerifyInnerSat, verSat] using streamVerifyInnerSat

def streamVerifyFrameSat : State := { verSat with wr := [⟨0x3000, 80⟩] }

theorem streamVerifyFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamVerifySig.contract PPC64LE.abi (post := Spec.Sm4.Gcm.streamVerifyPost PPC64LE.abi.ptrBits)
    (writeArgs := true) (stack := 5888)).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamVerifySig, Spec.Sm4.Gcm.streamVerifyPost, PPC64LE.abi, PPC64LE.argRegs] [streamVerifyFrameSat, verSat] using streamVerifyFrameSat

theorem streamVerify_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9
      (Impl.StackScratch.PPC64LE.withStackScratch 3296 .r10 streamVerify))
      (Spec.Sm4.Gcm.streamVerifySig.contract PPC64LE.abi (post := Spec.Sm4.Gcm.streamVerifyPost PPC64LE.abi.ptrBits) (writeArgs := true) (stack := 5888)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamVerifySig) (nm := "work") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.streamVerifyPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 3296) (bytes := 2592)
    (PPC64LE.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamVerifySig.withScratch "work" .u64 320) (nm := "sm4")
      (e := .u64) (n := 408) (wa := true) (stack := 0) (bytes := 3296) streamVerify_verified (by decide) (by decide)
      (pre_withScratch "work" .u64 320 (Proof.Sm4Gcm.pre_local _ _))
      (post_withScratch "work" .u64 320 (Proof.Sm4Gcm.streamVerifyPost_local _))
      (fun vs m m₁ m₂ r hl _ => postOut_withScratch "work" .u64 320 (Proof.Sm4Gcm.streamVerifyPostOut_local _) vs m m₁ m₂ r hl) streamVerifyInnerSat_pre)
    (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.streamVerifyPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.streamVerifyPostOut_local _ vs m m₁ m₂ r hl) streamVerifyFrameSat_pre

/-! ## `seal` -/

/-- `sealSat` with the working space alone on the stack. -/
def sealInnerSat : State := { sealSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9060, 8⟩]
  wr := [⟨0x2800, 0⟩, ⟨0x5000, 16⟩, ⟨0x6000, 2560⟩] }

theorem sealInnerSat_pre : ∃ s, ((Spec.Sm4.Gcm.sealSig.withScratch "work" .u64 320).contract PPC64LE.abi
    (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.sealSig.params
      (Curry.const (fun _ => True) _))
    (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.sealSig.params
      (Spec.Sm4.Gcm.sealPost PPC64LE.abi.ptrBits)) true (0 + 3376)).pre s := by
  implies_sat [Sig.withScratch, Curry.withScratch, Curry.app, Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost,
    PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealInnerSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealInnerSat

/-- `sealSat` without the stack arguments. -/
def sealFrameSat : State := { sealSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2800, 0⟩, ⟨0x5000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.sealContract PPC64LE.abi 6048).pre s := by
  implies_sat [Spec.Sm4.Gcm.sealContract, Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost, PPC64LE.abi,
    PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealFrameSat

/-- `seal`: the outer frame passes the working space's address as the first
stack argument, and the inner frame copies it, then SM4's working space's
address, above its stack pointer (`Verified.stackScratchArgs`). -/
theorem seal_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 0
      (Impl.StackScratch.PPC64LE.withStackScratchArgs 3376 1 «seal»))
      (Spec.Sm4.Gcm.sealContract PPC64LE.abi 6048) :=
  PPC64LE.Verified.stackScratchArgs (sig := Spec.Sm4.Gcm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.sealPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 3376) (bytes := 2672) (m := 0)
    (PPC64LE.Verified.stackScratchArgs (sig := Spec.Sm4.Gcm.sealSig.withScratch "work" .u64 320) (nm := "sm4")
      (e := .u64) (n := 408) (wa := true) (stack := 0) (bytes := 3376) (m := 1) seal_verified (by decide)
      (by decide) (pre_withScratch "work" .u64 320 (Proof.Sm4Gcm.pre_local _ _))
      (post_withScratch "work" .u64 320 (Proof.Sm4Gcm.sealPost_local _))
      (fun vs m m₁ m₂ r hl _ => postOut_withScratch "work" .u64 320 (Proof.Sm4Gcm.sealPostOut_local _) vs m m₁ m₂ r hl) sealInnerSat_pre)
    (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.sealPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.sealPostOut_local _ vs m m₁ m₂ r hl) sealFrameSat_pre

/-! ## `open` -/

/-- `openSat` with `tag_len` and the working space on the stack. -/
def openInnerSat : State := { openSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9060, 16⟩]
  wr := [⟨0x2800, 0⟩, ⟨0x6000, 2560⟩] }

theorem openInnerSat_pre : ∃ s, ((Spec.Sm4.Gcm.openSig.withScratch "work" .u64 320).contract PPC64LE.abi
    (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.openSig.params
      (Curry.const (fun _ => True) _))
    (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.openSig.params
      (Spec.Sm4.Gcm.openPost PPC64LE.abi.ptrBits)) true (0 + 3392)
    ((some (Spec.Sm4.Gcm.openLeak PPC64LE.abi.ptrBits)).map
      (Curry.withScratch PPC64LE.abi.ptrBits "work" .u64 320 Spec.Sm4.Gcm.openSig.params))).pre s := by
  implies_sat [Sig.withScratch, Curry.withScratch, Curry.app, Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost,
    Spec.Sm4.Gcm.openLeak, PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range,
    List.range.loop] [openInnerSat, openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openInnerSat

/-- `openSat` with `tag_len` alone on the stack. -/
def openFrameSat : State := { openSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9060, 8⟩]
  wr := [⟨0x2800, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.openContract PPC64LE.abi 6064).pre s := by
  implies_sat [Spec.Sm4.Gcm.openContract, Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak,
    PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [openFrameSat, openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openFrameSat

/-- `open`, whose `tag_len` arrives on the stack before the working spaces. -/
theorem open_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 1
      (Impl.StackScratch.PPC64LE.withStackScratchArgs 3392 2 «open»))
      (Spec.Sm4.Gcm.openContract PPC64LE.abi 6064) :=
  PPC64LE.Verified.stackScratchArgs (sig := Spec.Sm4.Gcm.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Curry.const (fun _ => True) _) (post := Spec.Sm4.Gcm.openPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 3392) (bytes := 2672) (m := 1)
    (leak := some (Spec.Sm4.Gcm.openLeak PPC64LE.abi.ptrBits))
    (PPC64LE.Verified.stackScratchArgs (sig := Spec.Sm4.Gcm.openSig.withScratch "work" .u64 320) (nm := "sm4")
      (e := .u64) (n := 408) (wa := true) (stack := 0) (bytes := 3392) (m := 2) open_verified (by decide)
      (by decide) (pre_withScratch "work" .u64 320 (Proof.Sm4Gcm.pre_local _ _))
      (post_withScratch "work" .u64 320 (Proof.Sm4Gcm.openPost_local _))
      (fun vs m m₁ m₂ r hl _ => postOut_withScratch "work" .u64 320 (Proof.Sm4Gcm.openPostOut_local _) vs m m₁ m₂ r hl) openInnerSat_pre
      (hleak := leakLocal_withScratch "work" .u64 320 (Proof.Sm4Gcm.openLeak_local _)))
    (by decide) (by decide) (Proof.Sm4Gcm.pre_local _ _) (Proof.Sm4Gcm.openPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm4Gcm.openPostOut_local _ vs m m₁ m₂ r hl) openFrameSat_pre
    (hleak := Proof.Sm4Gcm.openLeak_local _)

end VG.Proof.Sm4Gcm.PPC64LE
