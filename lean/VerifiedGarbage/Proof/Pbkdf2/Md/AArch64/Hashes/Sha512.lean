module

public import VerifiedGarbage.Proof.Sha512.AArch64.OneShot
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.Sha1.PostOut
public import VerifiedGarbage.Proof.Sha256.PostOut
public import VerifiedGarbage.Proof.Sha512.PostOut
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Sha512.AArch64.OneShot
meta import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
meta import VerifiedGarbage.Proof.Sha512.AArch64.Shared
meta import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Sha512.AArch64.Shared
public import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Digest
public import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
meta import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Digest
public import VerifiedGarbage.Proof.Sha1.AArch64.Sha2.Compress
import VerifiedGarbage.Proof.Sha1.AArch64.Sha2.Lit
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha1.AArch64.Sha2.Compress
meta import VerifiedGarbage.Proof.Sha1.AArch64.Sha2.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha1.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Sha1.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Sha256.AArch64.Shared
public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
meta import VerifiedGarbage.Proof.Sha256.AArch64.Shared
meta import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
meta import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Digest
public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Digest
public import VerifiedGarbage.Proof.Sha1.AArch64.Stream.Init
public import VerifiedGarbage.Spec.Sha1.Contract
meta import VerifiedGarbage.Proof.Sha1.AArch64.Shared
meta import VerifiedGarbage.Proof.Sha1.AArch64.Stream.Init
meta import VerifiedGarbage.Spec.Sha1.Contract
public import VerifiedGarbage.Proof.Sha1.AArch64.Shared
public import VerifiedGarbage.Proof.Md5.AArch64.Stream.Md
public import VerifiedGarbage.Proof.Md5.AArch64.Stream.Init
public import VerifiedGarbage.Spec.Md5.Contract
meta import VerifiedGarbage.Proof.Md5.AArch64.Stream.Md
meta import VerifiedGarbage.Proof.Md5.AArch64.Stream.Init
meta import VerifiedGarbage.Spec.Md5.Contract
public import VerifiedGarbage.Impl.Sha1.AArch64.Stream
public import VerifiedGarbage.Proof.MdStream.AArch64.OneShot
public import VerifiedGarbage.Proof.Sha1.Md
meta import VerifiedGarbage.Impl.Sha1.AArch64.Stream
meta import VerifiedGarbage.Proof.MdStream.AArch64.OneShot
meta import VerifiedGarbage.Proof.Sha1.Md
public import VerifiedGarbage.Proof.Sha1.AArch64.Stream.Md
meta import VerifiedGarbage.Proof.Sha1.AArch64.Stream.Md

/-! ### `Sha1.AArch64.Variant`, which only this module used -/

section

/-!
# SHA-1 compression backends on AArch64

Each backend supplies its verified compression code and the mechanically
checked constant-time, register and frame facts for the generic streaming
wrappers. The functional streaming proofs are shared by every backend.
HMAC and PBKDF2 consume the resulting streaming functions through `MdHash`.
-/

@[expose] public section

namespace VG.Proof.Sha1.AArch64

open VG.AArch64 VG.Proof.MdStream.AArch64
open VG.Impl.MdStream.AArch64

/-- The one-shot digest, calling the compression function `code` named
`name`. -/
def oneShotWith (name : String) (code : Prog isa) : Prog isa :=
  Impl.MdStream.AArch64.OneShot.digest Stream.params Impl.Sha1.AArch64.Stream.init name code

/-- The one-shot digest is constant time. -/
abbrev OneShotCT (name : String) (code : Prog isa) : Prop :=
  ConstantTime isa (MdStream.AArch64.OneShot.oneK (P := Stream.params) md Spec.Sha1.H0 20).pre
    (MdStream.AArch64.OneShot.oneK (P := Stream.params) md Spec.Sha1.H0 20).pub (oneShotWith name code)

structure Compress where
  name : String
  code : Prog isa
  verified : Verified AArch64.target code Proof.Sha1.compressAArch64
  noFrames : code.noFrames = true
  /-- Current streaming wrappers require untouched callee-saved SIMD registers. -/
  keepsV : code.allInstrs keepsV = true
  /-- No instruction of it writes PSTATE.DIT, and it calls nothing indirectly:
  what the cleanup of the functions that call it needs of its code
  (`ScrubAll.verifiedScrubbedOf`). -/
  side : ScrubAll.sideAll (fun i => !i.writesDit) code = true
  suffix : String
  features : List String
  updateCT : ConstantTime isa (updK (P := Stream.params) md).pre
    (updK (P := Stream.params) md).pub (update Stream.params name code)
  finalizeCT : ConstantTime isa (finK (P := Stream.params) md).pre
    (finK (P := Stream.params) md).pub (finalize Stream.params name code)
  updateDepth : (updateMain Stream.params name code).aarch64Depth = 0
  finalizeDepth : (finalizeMain Stream.params name code).aarch64Depth = 0
  /-- The one-shot digest. -/
  oneShot : OneShotCT name code

/-! ## The one-shot digest's common facts -/

namespace OneShot

open MdStream.AArch64.OneShot (initK Fits)

theorem fits : Fits Stream.params := ⟨by decide⟩

theorem init_ok :
    ∀ s, (initK (P := Stream.params) md Spec.Sha1.H0).pre s → ∃ t s',
      Exec isa Impl.Sha1.AArch64.Stream.init s t s' ∧ abiPreserved s s' ∧
        (initK (P := Stream.params) md Spec.Sha1.H0).post s s' := fun s h => by
  obtain ⟨t, s', he, h⟩ := Stream.init_correct h
  exact ⟨t, s', he, h⟩

theorem init_writes :
    ∀ r, r ≠ .x9 → r ≠ .x10 → ∀ i ∈ instrs Impl.Sha1.AArch64.Stream.init, clobbers i r = false := by
  intro r h9 _ i hi
  simp only [Impl.Sha1.AArch64.Stream.init, instrs, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  obtain ⟨_, _, rfl | rfl | rfl⟩ := hi <;> simp [clobbers, dstOf, Ne.symm h9]

theorem init_keepsV : Impl.Sha1.AArch64.Stream.init.allInstrs VG.AArch64.keepsV = true := by
  rw [Code.allInstrs_eq]
  simp only [Impl.Sha1.AArch64.Stream.init, instrs, List.all_eq_true, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false]
  rintro _ ⟨_, _, rfl | rfl | rfl⟩ <;> rfl

/-- A state satisfying the precondition: an empty message at `0x1000`, the
digest at `0x2000` and the stack pointer at `0x10000`. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 0⟩]
  wr := [⟨0x2000, 20⟩]

theorem sat_pre : MdStream.AArch64.OneShot.Pre Stream.params 20 sat where
  rd := rfl
  wr := rfl
  d_o := show Region.Disjoint ⟨0x1000, 0⟩ ⟨0x2000, 20⟩ from
    Offset.disjoint_of_le (show 4096 + 0 ≤ 8192 by decide) (by decide)
  sp := show Impl.MdStream.AArch64.OneShot.frameBytes Stream.params ≤ (0x10000 : BitVec 64).toNat by decide
  f_d := show Region.Disjoint ⟨0x10000 - BitVec.ofNat 64 (Impl.MdStream.AArch64.OneShot.frameBytes Stream.params),
      Impl.MdStream.AArch64.OneShot.frameBytes Stream.params⟩ ⟨0x1000, 0⟩ from
    (Offset.disjoint_of_le (by decide) (by decide)).symm
  f_o := show Region.Disjoint ⟨0x10000 - BitVec.ofNat 64 (Impl.MdStream.AArch64.OneShot.frameBytes Stream.params),
      Impl.MdStream.AArch64.OneShot.frameBytes Stream.params⟩ ⟨0x2000, 20⟩ from
    (Offset.disjoint_of_le (by decide) (by decide)).symm

end OneShot

namespace Compress

variable (v : Compress)

def update : Prog isa := Impl.MdStream.AArch64.update Stream.params v.name v.code
def finalize : Prog isa := Impl.MdStream.AArch64.finalize Stream.params v.name v.code

theorem callee : CalleeOk (P := Stream.params) md v.code := ⟨v.verified.1, v.noFrames, v.keepsV⟩

theorem update_verified : Verified AArch64.target v.update Proof.Sha1.updateAArch64 := by
  have h := MdStream.AArch64.Update.verified Stream.dims v.callee v.updateCT
    (by rw [v.updateDepth]; decide)
  exact h.of_implies ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha1.H0 m hr hc,
    fun _ _ _ _ h => h, h.2.2⟩

theorem finalize_verified : Verified AArch64.target v.finalize Proof.Sha1.finalizeAArch64 := by
  have h := MdStream.AArch64.Finalize.verified Stream.dims Stream.shape v.callee v.finalizeCT
    (by rw [v.finalizeDepth]; decide)
  exact h.of_implies ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha1.H0 m hr trivial hc,
    fun _ _ _ _ h => h, h.2.2⟩

/-- The one-shot digest. -/
theorem oneShot_verified :
    Verified AArch64.target (oneShotWith v.name v.code)
      (MdStream.AArch64.OneShot.oneK (P := Stream.params) md Spec.Sha1.H0 20) :=
  MdStream.AArch64.OneShot.verified OneShot.fits Stream.dims Stream.shape.toD v.callee OneShot.init_ok
    OneShot.init_writes rfl OneShot.init_keepsV v.oneShot ⟨_, OneShot.sat_pre⟩

end Compress
end VG.Proof.Sha1.AArch64

end

end

/-! ### `Pbkdf2.Md.AArch64.Hashes.Sha224`, which the modules that import this one used -/

section

/-! ### `Pbkdf2.Md.AArch64.Hashes.Sha1`, which the modules that import this one used -/

section

/-! ### `Sha1.AArch64.OneShot`, which only this module used -/

section

/-!
# The one-shot SHA-1 digest on AArch64, against its shared contract

`Compress.oneShot_verified` proves the one-shot digest against
`OneShot.oneK`; `implies` moves it to `Spec.Sha1.digestContract`, whose
`stack` is the digest's frame.
-/

@[expose] public section

namespace VG.Proof.Sha1.AArch64.OneShot

open VG.AArch64 VG.Proof.MdStream.AArch64

/-- The stack the one-shot digest uses: its frame. -/
abbrev stack : Nat := Impl.MdStream.AArch64.OneShot.frameBytes Impl.Sha1.AArch64.Stream.params

/-- SHA-1's digest is all of the final hash value. -/
theorem hash_take (m : List Byte) : (md.hash Spec.Sha1.H0 m).take 20 = Spec.Sha1.hash m := by
  rw [Proof.Sha1.hash_eq]
  exact List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))

theorem implies :
    (OneShot.oneK (P := Impl.Sha1.AArch64.Stream.params) md Spec.Sha1.H0 20).Implies
      (Spec.Sha1.digestContract AArch64.abi stack) := by
  refine
    { pre := fun s h => ?_
      post := fun s s' _ h => ?_
      pub := by implies_pub [Spec.Sha1.digestContract, Spec.Sha1.digestSig, Spec.Sha1.digestPost,
        OneShot.oneK, AArch64.abi, AArch64.argRegs]
      sat := ⟨sat, ?_⟩ }
  · sig_pre [Spec.Sha1.digestContract, Spec.Sha1.digestSig, Spec.Sha1.digestPost, AArch64.abi,
      AArch64.argRegs] at h
    obtain ⟨hsp, hrd, hwr, hdo, hfd, hfo, -, -⟩ := h
    exact ⟨hrd, hwr, hdo, hsp, hfd, hfo⟩
  · sig_post [Spec.Sha1.digestContract, Spec.Sha1.digestSig, Spec.Sha1.digestPost, AArch64.abi,
      AArch64.argRegs]
    rw [← hash_take]
    exact h trivial
  · have hp := sat_pre
    sig_pre [Spec.Sha1.digestContract, Spec.Sha1.digestSig, Spec.Sha1.digestPost, AArch64.abi,
      AArch64.argRegs]
    sig_and_intros
    all_goals first
      | exact hp.sp | rfl | exact hp.d_o | exact hp.f_d | exact hp.f_o | decide

end VG.Proof.Sha1.AArch64.OneShot

end

end

/-! ### `Pbkdf2.Md.AArch64.Hashes.Md5`, which the modules that import this one used -/

section

/-!
# MD5 on AArch64, as a Merkle–Damgård hash function

MD5 with its compression function, as a variant of `MdHash` (`variant`), from
which HMAC and PBKDF2 are emitted (`Generic/MdHash/AArch64/`): its streaming
code is the generic Merkle–Damgård code (`Stream.params`), its specification
`Spec.Hmac.md5S`. The facts about the code HMAC and PBKDF2 add, which do not
depend on the functions they call, are checked once (`coreOK`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64.Md5

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- MD5's functions. -/
def hash : Hash where
  P := Impl.Pbkdf2.AArch64.ofMd Impl.Md5.AArch64.Stream.params
  D := 16
  W := Spec.Hmac.md5I.scratch
  compN := "vg_md5_compress"
  compC := Impl.Md5.AArch64.compress
  initN := Spec.Md5.initApi.name
  initC := Impl.Md5.AArch64.Stream.init
  updN := "vg_md5_update_scratch"
  updC := Impl.Md5.AArch64.Stream.update
  finN := "vg_md5_finalize_scratch"
  finC := Impl.Md5.AArch64.Stream.finalize
  hmacInitN := "vg_hmac_md5_init_scratch"
  hmacFinN := "vg_hmac_md5_finalize_scratch"
  iterN := "vg_pbkdf2_hmac_md5_iterate"

/-- `hash` without the functions it calls. -/
def coreH : Hash := ⟨Impl.Pbkdf2.AArch64.ofMd Impl.Md5.AArch64.Stream.params, 16, 48, "", .block [], "",
  .block [], "", .block [], "", .block [], "", "", ""⟩

theorem coreOK : CoreOK coreH := by
  refine {
    pbk := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    iter := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    hinit := {
      pro := ⟨?_, ?_⟩
      argI := List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_nil _⟩⟩
      keys := ⟨?_, ?_⟩
      mid := ⟨?_, ?_⟩
      restore := ⟨?_, ?_⟩ }
    hfin := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    fitI := ?_
    fitF := ?_ }
  taint_decide_all

theorem anyOK : Any.AnyOK coreH := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

/-- The streaming functions, verified against the contracts HMAC's proofs
call them with. -/
def streamOK : Calls.StreamOK hash.stream where
  SH := Spec.Hmac.md5S
  Wb := 112
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := by decide
  hF := by decide
  hD0 := by decide
  hS0 := by decide
  hSB := by decide
  hB0 := by decide
  hBB := by decide
  hWb := by decide
  hW := by decide
  repr := Hmac.Generic.Common.md5_repr
  init := Proof.Md5.AArch64.Stream.init_verified
  upd := Proof.Md5.AArch64.Stream.Update.update_verified
  fin := Proof.Md5.AArch64.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 16 (Spec.Md5.bytesAt s'.mem _ 16) = _
        rw [List.take_of_length_le (by simp [Spec.Md5.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Md5.AArch64.Stream.Finalize.finalize_verified.2.2 }
  initDepth := by decide +kernel
  updDepth := by decide +kernel
  finDepth := by decide +kernel

def ok : HashOK hash where
  initKeepsV := by decide +kernel
  updKeepsV := by lit_decide
  finKeepsV := by lit_decide
  md := Proof.Md5.md
  shape := Pbkdf2.AArch64.Shape.ofMd Proof.Md5.AArch64.Stream.shape
  comp := ⟨Proof.Md5.AArch64.Stream.callee.verified, Proof.Md5.AArch64.compress_verified.2.1,
    Proof.Md5.AArch64.Stream.callee.noFrames, Proof.Md5.AArch64.Stream.callee.keepsV⟩
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 16) h (by omega_using [hj])
  lenOk _ _ := trivial
  stream := streamOK
  iv := Spec.Md5.H0
  repr _ _ _ := Iff.rfl
  hash m := by
    show Spec.Md5.hash m = _
    rw [Proof.Md5.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm
  sizes := ⟨⟨by decide, by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  L := by decide
  W := by decide
  hPad := by decide
  L816 := by decide

theorem satI : ∃ s, (Proof.Hmac.Instance.initScratchContract Spec.Hmac.md5I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.md5I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi, AArch64.argRegs] using initSat 80 48

theorem satF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.md5I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Spec.Hmac.md5I, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi, AArch64.argRegs] using finSat 80 16 48

theorem satT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.md5I AArch64.abi).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.iterateContract, Spec.Hmac.md5I, Proof.Pbkdf2.iterateContract,
    Proof.Pbkdf2.iterateSig, Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi, AArch64.argRegs]
    using Pbkdf2.AArch64.iterSat 80 16 48

theorem satA : ∃ s, (Any.anyScratchContract Spec.Hmac.md5I.S Spec.Hmac.md5I.initAnyKeyScratch).pre s := by
  inst_sat [Any.anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.md5I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi, AArch64.argRegs] using initSat 80 128

theorem satP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.md5I AArch64.abi 16).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.md5I,
    Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi,
    AArch64.argRegs] using pbkSat 128

theorem satPF :
    ∃ s, (Spec.Hmac.md5I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame Spec.Hmac.md5I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.md5I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi,
    AArch64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

/-- HMAC's buffers fit in the right-sized working space (`MdHash.initW`, `MdHash.finW`). -/
theorem fitI : (hash).stream.buf ≤ 8 * 22 := by
  simp only [hash, Hash.stream, Impl.Pbkdf2.Md.AArch64.Stream.buf, Impl.Pbkdf2.AArch64.ofMd,
    Impl.Md5.AArch64.Stream.params]
  decide

theorem fitF : (hash).stream.buf + (hash).stream.F ≤ 8 * 24 := by
  simp only [hash, Hash.stream, Impl.Pbkdf2.Md.AArch64.Stream.buf, Impl.Pbkdf2.AArch64.ofMd,
    Impl.Md5.AArch64.Stream.params]
  decide

theorem coreSide : CoreSide coreH := ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

/-- MD5's code that HMAC and PBKDF2 call writes no PSTATE.DIT and calls
nothing indirectly. -/
theorem calleeSide : CalleeSide hash := ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

/-- MD5 with its compression function. -/
def variant : MdHash := MdHash.of ok coreOK ⟨Spec.Mgf1.md5, by simp [mdHashes], fun _ => rfl, rfl⟩ rfl rfl satI satF satT satP (by decide)
    anyOK satA (by decide) Proof.Hmac.md5_local
    (by
      unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by decide)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) satPF
    22 24 ⟨fitI, by decide, by decide, by decide⟩ ⟨fitF, by decide, by decide, by decide⟩
    (by inst_sat [Proof.Hmac.initScratchContract, Spec.Hmac.md5I, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi, AArch64.argRegs] using initSat 80 22)
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by inst_sat [Proof.Hmac.finalizeScratchContract, Spec.Hmac.md5I, Proof.Hmac.finalizeScratchSig,
      Spec.Hmac.finalizePost, Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi, AArch64.argRegs] using finSat 80 16 24)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by kernel_rfl) (by kernel_rfl) (by decide) (by decide) calleeSide coreSide
    "" []

end VG.Proof.Pbkdf2.Md.AArch64.Md5

end

end

/-!
# SHA-1 on AArch64, as a Merkle–Damgård hash function

SHA-1 with its compression function, as a variant of `MdHash` (`variant`),
from which HMAC and PBKDF2 are emitted (`Generic/MdHash/AArch64/`): its
streaming code is the generic Merkle–Damgård code (`Stream.params`), its
specification `Spec.Hmac.sha1S`. The facts about the code HMAC and PBKDF2 add,
which do not depend on the functions they call, are checked once (`coreOK`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64.Sha1

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Sha1.AArch64 (Compress)

/-- SHA-1's functions. -/
def hash (v : Compress) : Hash where
  P := Impl.Pbkdf2.AArch64.ofMd Impl.Sha1.AArch64.Stream.params
  D := 20
  W := Spec.Hmac.sha1I.scratch
  compN := v.name
  compC := v.code
  initN := Spec.Sha1.initApi.name
  initC := Impl.Sha1.AArch64.Stream.init
  updN := "vg_sha1_update_scratch" ++ v.suffix
  updC := v.update
  finN := "vg_sha1_finalize_scratch" ++ v.suffix
  finC := v.finalize
  hmacInitN := "vg_hmac_sha1_init_scratch" ++ v.suffix
  hmacFinN := "vg_hmac_sha1_finalize_scratch" ++ v.suffix
  iterN := "vg_pbkdf2_hmac_sha1_iterate" ++ v.suffix

/-- `hash` without the functions it calls. -/
def coreH : Hash := ⟨Impl.Pbkdf2.AArch64.ofMd Impl.Sha1.AArch64.Stream.params, 20, 56, "", .block [], "",
  .block [], "", .block [], "", .block [], "", "", ""⟩

theorem coreOK : CoreOK coreH := by
  refine {
    pbk := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    iter := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    hinit := {
      pro := ⟨?_, ?_⟩
      argI := List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_nil _⟩⟩
      keys := ⟨?_, ?_⟩
      mid := ⟨?_, ?_⟩
      restore := ⟨?_, ?_⟩ }
    hfin := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    fitI := ?_
    fitF := ?_ }
  taint_decide_all

theorem anyOK : Any.AnyOK coreH := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

variable (v : Compress)

/-- The streaming functions, verified against the contracts HMAC's proofs
call them with. -/
def streamOK : Calls.StreamOK (hash v).stream where
  SH := Spec.Hmac.sha1S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := by simp only [hash, Hash.stream] <;> decide
  hF := by simp only [hash, Hash.stream] <;> decide
  hD0 := by simp only [hash, Hash.stream] <;> decide
  hS0 := by simp only [hash, Hash.stream, Hash.S] <;> decide
  hSB := by simp only [hash, Hash.stream, Hash.S] <;> decide
  hB0 := by simp only [hash, Hash.stream] <;> decide
  hBB := by simp only [hash, Hash.stream] <;> decide
  hWb := by simp only [hash, Hash.stream] <;> decide
  hW := by simp only [hash, Hash.stream] <;> decide
  repr := Hmac.Generic.Common.sha1_repr
  init := Proof.Sha1.AArch64.Stream.init_verified
  upd := v.update_verified
  fin := v.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 20 (Spec.Sha1.bytesAt s'.mem _ 20) = _
        rw [List.take_of_length_le (by simp [Spec.Sha1.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.finalize_verified.2.2 }
  initDepth := by simp only [hash, Hash.stream] <;> decide +kernel
  updDepth := by
    show (Impl.MdStream.AArch64.update _ v.name v.code).aarch64Depth ≤ 1
    simp only [Impl.MdStream.AArch64.update, Code.aarch64Depth, v.updateDepth]; decide
  finDepth := by
    show (Impl.MdStream.AArch64.finalize _ v.name v.code).aarch64Depth ≤ 1
    simp only [Impl.MdStream.AArch64.finalize, Code.aarch64Depth, v.finalizeDepth]; decide

def ok : HashOK (hash v) where
  initKeepsV := by rfl
  updKeepsV := MdStream.AArch64.update_keepsV v.keepsV
  finKeepsV := MdStream.AArch64.finalize_keepsV Proof.Sha1.AArch64.Stream.shape v.keepsV
  md := Proof.Sha1.md
  shape := Pbkdf2.AArch64.Shape.ofMd Proof.Sha1.AArch64.Stream.shape
  comp := ⟨v.callee.verified, v.verified.2.1, v.noFrames, v.keepsV⟩
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega_using [hj])
  lenOk _ _ := trivial
  stream := streamOK v
  iv := Spec.Sha1.H0
  repr _ _ _ := Iff.rfl
  hash m := by
    show Spec.Sha1.hash m = _
    rw [Proof.Sha1.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm
  sizes := ⟨⟨by simp only [hash] <;> decide, by simp only [hash] <;> decide, by simp only [hash] <;> decide,
      by simp only [hash] <;> decide⟩,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide⟩
  L := by simp only [hash] <;> decide
  W := by simp only [hash] <;> decide
  hPad := by simp only [hash] <;> decide
  L816 := by simp only [hash] <;> decide

theorem satI : ∃ s, (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha1I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.sha1I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi, AArch64.argRegs] using initSat 84 56

theorem satF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha1I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha1I, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi, AArch64.argRegs] using finSat 84 20 56

theorem satT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha1I AArch64.abi).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.iterateContract, Spec.Hmac.sha1I, Proof.Pbkdf2.iterateContract,
    Proof.Pbkdf2.iterateSig, Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi, AArch64.argRegs]
    using Pbkdf2.AArch64.iterSat 84 20 56

theorem satA : ∃ s, (Any.anyScratchContract Spec.Hmac.sha1I.S Spec.Hmac.sha1I.initAnyKeyScratch).pre s := by
  inst_sat [Any.anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha1I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi, AArch64.argRegs] using initSat 84 140

theorem satP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha1I AArch64.abi 16).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha1I,
    Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi,
    AArch64.argRegs] using pbkSat 140

theorem satPF :
    ∃ s, (Spec.Hmac.sha1I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame Spec.Hmac.sha1I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha1I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi,
    AArch64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

/-- `Impl.Sha1.AArch64.Stream.Fn.update`, the function as emitted, cleanup included: it meets its
contract in constant time and returns without secret residue. -/
theorem update_scrubbed (v : Compress) :
    VerifiedScrubbed AArch64.target (Impl.Sha1.AArch64.Stream.Fn.update v.name v.code)
      (Spec.Sha1.updateContract AArch64.abi (16 + 160)) 0 :=
  AArch64.ScrubAll.verifiedScrubbedOf
    (Proof.Sha1.AArch64.Shared.update_of v.update_verified)
    (AArch64.ScrubAll.scrubAllOk_regs (sig := Spec.Sha1.updateSig) (by decide) (by decide) (Nat.le_refl _) (Proof.Sha1.updatePost_out _))
    (by decide) (depth_frame_le (mdUpdate_depth _ _ _ v.updateDepth))
    (AArch64.ScrubAll.sideAll_withStackScratch rfl rfl rfl (mdUpdate_side _ _ (by kernel_rfl) v.side)) (Or.inl rfl)

/-- `Impl.Sha1.AArch64.Stream.Fn.finalize`, the function as emitted, cleanup included: it meets its
contract in constant time and returns without secret residue. -/
theorem finalize_scrubbed (v : Compress) :
    VerifiedScrubbed AArch64.target (Impl.Sha1.AArch64.Stream.Fn.finalize v.name v.code)
      (Spec.Sha1.finalizeContract AArch64.abi (16 + 160)) 0 :=
  AArch64.ScrubAll.verifiedScrubbedOf
    (Proof.Sha1.AArch64.Shared.finalize_of v.finalize_verified)
    (AArch64.ScrubAll.scrubAllOk_regs (sig := Spec.Sha1.finalizeSig) (by decide) (by decide) (Nat.le_refl _) (Proof.Sha1.finalizePost_out _))
    (by decide) (depth_frame_le (mdFinalize_depth _ _ _ v.finalizeDepth))
    (AArch64.ScrubAll.sideAll_withStackScratch rfl rfl rfl (mdFinalize_side _ _ (by kernel_rfl) v.side)) (Or.inl rfl)

/-- `Impl.Sha1.AArch64.Stream.Fn.digest`, the function as emitted, cleanup included: it meets its
contract in constant time and returns without secret residue. -/
theorem digest_scrubbed (v : Compress) :
    VerifiedScrubbed AArch64.target (Impl.Sha1.AArch64.Stream.Fn.digest v.name v.code)
      (Spec.Sha1.digestContract AArch64.abi Proof.Sha1.AArch64.OneShot.stack) 0 :=
  AArch64.ScrubAll.verifiedScrubbedOf
    (v.oneShot_verified.of_implies Proof.Sha1.AArch64.OneShot.implies)
    (AArch64.ScrubAll.scrubAllOk_regs (sig := Spec.Sha1.digestSig) (by decide) (by decide) (Nat.le_refl _) (Proof.Sha1.digestPost_out _))
    (by decide) (mdDigest_depth _ _ _ _ (by decide) v.noFrames)
    (mdDigest_side _ _ _ (by kernel_rfl) v.side) (Or.inl rfl)

/-- HMAC's buffers fit in the right-sized working space (`MdHash.initW`, `MdHash.finW`). -/
theorem fitI (v : Compress) : (hash v).stream.buf ≤ 8 * 28 := by
  simp only [hash, Hash.stream, Impl.Pbkdf2.Md.AArch64.Stream.buf, Impl.Pbkdf2.AArch64.ofMd,
    Impl.Sha1.AArch64.Stream.params]
  decide

theorem fitF (v : Compress) : (hash v).stream.buf + (hash v).stream.F ≤ 8 * 30 := by
  simp only [hash, Hash.stream, Impl.Pbkdf2.Md.AArch64.Stream.buf, Impl.Pbkdf2.AArch64.ofMd,
    Impl.Sha1.AArch64.Stream.params]
  decide

theorem coreSide : CoreSide coreH := ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

/-- The hash function's code that HMAC and PBKDF2 call writes no PSTATE.DIT
and calls nothing indirectly: the compression function's (`Compress.side`),
and the streaming functions' own instructions. -/
theorem calleeSide (v : Compress) : CalleeSide (hash v) :=
  ⟨v.side, by kernel_rfl, mdUpdate_side _ _ (by kernel_rfl) v.side, mdFinalize_side _ _ (by kernel_rfl) v.side⟩

/-- Every construction follows the registered compression backend. -/
def variant : MdHash :=
  MdHash.of (ok v) coreOK ⟨Spec.Mgf1.sha1, by simp [mdHashes], fun _ => rfl, rfl⟩ rfl rfl satI satF satT satP (by decide)
    anyOK satA (by decide) Proof.Hmac.sha1_local
    (by
      unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by decide)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) satPF
    28 30 ⟨(fitI v), by decide, by decide, by decide⟩ ⟨(fitF v), by decide, by decide, by decide⟩
    (by inst_sat [Proof.Hmac.initScratchContract, Spec.Hmac.sha1I, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi, AArch64.argRegs] using initSat 84 28)
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by inst_sat [Proof.Hmac.finalizeScratchContract, Spec.Hmac.sha1I, Proof.Hmac.finalizeScratchSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi, AArch64.argRegs] using finSat 84 20 30)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by kernel_rfl) (by kernel_rfl) (by decide) (by decide) (calleeSide v) coreSide
    v.suffix v.features

end VG.Proof.Pbkdf2.Md.AArch64.Sha1

end

end

/-!
# SHA-224 on AArch64, as a Merkle–Damgård hash function

SHA-224 with an implementation of SHA-256's compression function, as a variant
of `MdHash` (`variant`), from which HMAC and PBKDF2 are emitted
(`Generic/MdHash/AArch64/`): its streaming code is SHA-256's, the generic
Merkle–Damgård code (`Stream.params`) from SHA-224's initial hash value
(`vg_sha224_init`), its specification `Spec.Hmac.sha224S`, with the digest the
first 28 bytes of the final hash value. The facts about the code HMAC and
PBKDF2 add, which do not depend on the functions they call, are checked once
(`coreOK`).

Its streaming `update` is SHA-256's, which SHA-256's variants carry
(`Proof/Pbkdf2/Md/AArch64/Hashes/Sha256.lean`); SHA-224's carry its own
`finalize`, which writes its digest (`stream v`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64.Sha224

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Sha256.AArch64 (Compress)
open VG.Impl.MdStream.AArch64 (out32)

/-- SHA-224's functions, calling the implementation `v` of SHA-256's
compression function and SHA-256's streaming functions made with it, named
with its suffix. -/
def hash (v : Compress) : Hash where
  P := Impl.Pbkdf2.AArch64.ofMd Impl.Sha256.AArch64.Stream.params
  D := 28
  W := Spec.Hmac.sha224I.scratch
  compN := v.name
  compC := v.code
  initN := Spec.Sha256.init224Api.name
  initC := Impl.Sha256.AArch64.Stream.init224
  updN := "vg_sha256_update_scratch" ++ v.suffix
  updC := v.update
  finN := "vg_sha256_finalize_scratch" ++ v.suffix
  finC := v.finalize
  hmacInitN := "vg_hmac_sha224_init_scratch" ++ v.suffix
  hmacFinN := "vg_hmac_sha224_finalize_scratch" ++ v.suffix
  iterN := "vg_pbkdf2_hmac_sha224_iterate" ++ v.suffix

/-- `hash` without the functions it calls. -/
def coreH : Hash := ⟨Impl.Pbkdf2.AArch64.ofMd Impl.Sha256.AArch64.Stream.params, 28, 104, "", .block [], "",
  .block [], "", .block [], "", .block [], "", "", ""⟩

theorem coreOK : CoreOK coreH := by
  refine {
    pbk := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    iter := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    hinit := {
      pro := ⟨?_, ?_⟩
      argI := List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_nil _⟩⟩
      keys := ⟨?_, ?_⟩
      mid := ⟨?_, ?_⟩
      restore := ⟨?_, ?_⟩ }
    hfin := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    fitI := ?_
    fitF := ?_ }
  taint_decide_all

theorem anyOK : Any.AnyOK coreH := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

/-- The representation moves with the state's bytes. -/
theorem sha224_repr (m m' : Mem) (p q : Addr) (msg : List Byte)
    (h : ∀ i < 96, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha256.ReprFrom Spec.Sha256.H0_224 m p msg) :
    Spec.Sha256.ReprFrom Spec.Sha256.H0_224 m' q msg := by
  refine ⟨?_, ?_⟩
  · rw [← hr.1]
    apply Vector.ext
    intro j hj
    simp only [Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc h (by omega_using [hj])
  · rw [← hr.2]
    exact Hmac.Generic.Common.bytesAt_reloc h (o := 32) (k := msg.length % 64) (by omega_using [])

variable (v : Compress)

/-- The streaming functions, verified against the contracts HMAC's proofs
call them with. -/
def streamOK : Calls.StreamOK (hash v).stream where
  SH := Spec.Hmac.sha224S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := by simp only [hash, Hash.stream] <;> decide
  hF := by simp only [hash, Hash.stream] <;> decide
  hD0 := by simp only [hash, Hash.stream] <;> decide
  hS0 := by simp only [hash, Hash.stream, Hash.S] <;> decide
  hSB := by simp only [hash, Hash.stream, Hash.S] <;> decide
  hB0 := by simp only [hash, Hash.stream] <;> decide
  hBB := by simp only [hash, Hash.stream] <;> decide
  hWb := by simp only [hash, Hash.stream] <;> decide
  hW := by simp only [hash, Hash.stream] <;> decide
  repr := sha224_repr
  init := Proof.Sha256.AArch64.Stream.init224_verified
  upd := v.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0_224 m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.update_verified.2.2 }
  fin := v.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 28 (Spec.Sha256.bytesAt s'.mem _ 32) = Spec.Sha256.sha224 m
        rw [h Spec.Sha256.H0_224 m hr hc]
        rfl
      pub := fun _ _ _ _ h => h
      sat := v.finalize_verified.2.2 }
  initDepth := by simp only [hash, Hash.stream] <;> decide +kernel
  updDepth := by
    show (Impl.MdStream.AArch64.update _ v.name v.code).aarch64Depth ≤ 1
    simp only [Impl.MdStream.AArch64.update, Code.aarch64Depth, v.updateDepth]; decide
  finDepth := by
    show (Impl.MdStream.AArch64.finalize _ v.name v.code).aarch64Depth ≤ 1
    simp only [Impl.MdStream.AArch64.finalize, Code.aarch64Depth, v.finalizeDepth]; decide

def ok : HashOK (hash v) where
  initKeepsV := by rfl
  updKeepsV := MdStream.AArch64.update_keepsV v.keepsV
  finKeepsV := MdStream.AArch64.finalize_keepsV Proof.Sha256.AArch64.Stream.shape v.keepsV
  md := Proof.Sha256.md
  shape := Pbkdf2.AArch64.Shape.ofMd Proof.Sha256.AArch64.Stream.shape
  comp := ⟨v.callee.verified, v.verified.2.1, v.noFrames, v.keepsV⟩
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega_using [hj])
  lenOk _ _ := trivial
  stream := streamOK v
  iv := Spec.Sha256.H0_224
  repr _ _ _ := Iff.rfl
  hash _ := rfl
  sizes := ⟨⟨by simp only [hash] <;> decide, by simp only [hash] <;> decide, by simp only [hash] <;> decide,
      by simp only [hash] <;> decide⟩,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide⟩
  L := by simp only [hash] <;> decide
  W := by simp only [hash] <;> decide
  hPad := by simp only [hash] <;> decide
  L816 := by simp only [hash] <;> decide

theorem satI : ∃ s, (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha224I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.sha224I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha224S, Spec.Hmac.sha224, AArch64.abi, AArch64.argRegs] using initSat 96 104

theorem satF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha224I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha224I, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha224S, Spec.Hmac.sha224, AArch64.abi, AArch64.argRegs] using finSat 96 28 104

theorem satT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha224I AArch64.abi).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.iterateContract, Spec.Hmac.sha224I, Proof.Pbkdf2.iterateContract,
    Proof.Pbkdf2.iterateSig, Spec.Hmac.sha224S, Spec.Hmac.sha224, AArch64.abi, AArch64.argRegs]
    using Pbkdf2.AArch64.iterSat 96 28 104

theorem satA : ∃ s, (Any.anyScratchContract Spec.Hmac.sha224I.S Spec.Hmac.sha224I.initAnyKeyScratch).pre s := by
  inst_sat [Any.anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha224I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha224S, Spec.Hmac.sha224, AArch64.abi, AArch64.argRegs] using initSat 96 200

theorem satP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha224I AArch64.abi 16).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha224I,
    Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha224S, Spec.Hmac.sha224, AArch64.abi,
    AArch64.argRegs] using pbkSat 200

theorem satPF :
    ∃ s, (Spec.Hmac.sha224I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame Spec.Hmac.sha224I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha224I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha224S, Spec.Hmac.sha224, AArch64.abi,
    AArch64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

/-- `Impl.Sha256.AArch64.Stream.Fn.finalize224`, the function as emitted, cleanup included: it meets its
contract in constant time and returns without secret residue. -/
theorem finalize224_scrubbed (v : Compress) :
    VerifiedScrubbed AArch64.target (Impl.Sha256.AArch64.Stream.Fn.finalize224 v.name v.code)
      (Spec.Sha256.finalize224Contract AArch64.abi (16 + 160)) 0 :=
  AArch64.ScrubAll.verifiedScrubbedOf
    (Proof.Sha256.AArch64.Shared.finalize224_of v.finalize224_verified)
    (AArch64.ScrubAll.scrubAllOk_regs (sig := Spec.Sha256.finalize224Sig) (by decide) (by decide) (Nat.le_refl _) (Proof.Sha256.finalize224Post_out _))
    (by decide) (depth_frame_le (mdFinalize_depth _ _ _ v.finalize224Depth))
    (AArch64.ScrubAll.sideAll_withStackScratch rfl rfl rfl (mdFinalize_side _ _ (by kernel_rfl) v.side)) (Or.inl rfl)

/-- `Impl.Sha256.AArch64.Stream.Fn.digest224`, the function as emitted, cleanup included: it meets its
contract in constant time and returns without secret residue. -/
theorem digest224_scrubbed (v : Compress) :
    VerifiedScrubbed AArch64.target (Impl.Sha256.AArch64.Stream.Fn.digest224 v.name v.code)
      (Spec.Sha256.digestContract AArch64.abi 28 Spec.Sha256.sha224 Proof.Sha256.AArch64.OneShot.stack) 0 :=
  AArch64.ScrubAll.verifiedScrubbedOf
    ((v.oneShot_verified (by decide) Proof.Sha256.AArch64.Stream.shape224 v.oneShot224).of_implies (Proof.Sha256.AArch64.OneShot.implies (by decide) Proof.Sha256.AArch64.OneShot.sha224_take))
    (AArch64.ScrubAll.scrubAllOk_regs (sig := (Spec.Sha256.digestSig 28)) (by decide) (by decide) (Nat.le_refl _) (Proof.Sha256.digestPost_out _ _ _ (by decide)))
    (by decide) (mdDigest_depth _ _ _ _ (by decide) v.noFrames)
    (mdDigest_side _ _ _ (by kernel_rfl) v.side) (Or.inl rfl)

/-- HMAC's buffers fit in the right-sized working space (`MdHash.initW`, `MdHash.finW`). -/
theorem fitI (v : Compress) : (hash v).stream.buf ≤ 8 * 28 := by
  simp only [hash, Hash.stream, Impl.Pbkdf2.Md.AArch64.Stream.buf, Impl.Pbkdf2.AArch64.ofMd,
    Impl.Sha256.AArch64.Stream.params]
  decide

theorem fitF (v : Compress) : (hash v).stream.buf + (hash v).stream.F ≤ 8 * 32 := by
  simp only [hash, Hash.stream, Impl.Pbkdf2.Md.AArch64.Stream.buf, Impl.Pbkdf2.AArch64.ofMd,
    Impl.Sha256.AArch64.Stream.params]
  decide

theorem coreSide : CoreSide coreH := ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

/-- The hash function's code that HMAC and PBKDF2 call writes no PSTATE.DIT
and calls nothing indirectly: the compression function's (`Compress.side`),
and the streaming functions' own instructions. -/
theorem calleeSide (v : Compress) : CalleeSide (hash v) :=
  ⟨v.side, by kernel_rfl, mdUpdate_side _ _ (by kernel_rfl) v.side, mdFinalize_side _ _ (by kernel_rfl) v.side⟩

/-- SHA-224 with the implementation `v` of SHA-256's compression function.
Its streaming `update` is SHA-256's, which SHA-256's variant with `v`
carries, and its `finalize` its own (`stream v`). -/
def variant : MdHash :=
  MdHash.of (ok v) coreOK ⟨Spec.Mgf1.sha224, by simp [mdHashes], fun _ => rfl, rfl⟩ rfl rfl satI satF satT satP (by decide)
    anyOK satA (by decide) Proof.Hmac.sha224_local
    (by
      unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by decide)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) satPF
    28 32 ⟨(fitI v), by decide, by decide, by decide⟩ ⟨(fitF v), by decide, by decide, by decide⟩
    (by inst_sat [Proof.Hmac.initScratchContract, Spec.Hmac.sha224I, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha224S, Spec.Hmac.sha224, AArch64.abi, AArch64.argRegs] using initSat 96 28)
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by inst_sat [Proof.Hmac.finalizeScratchContract, Spec.Hmac.sha224I, Proof.Hmac.finalizeScratchSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha224S, Spec.Hmac.sha224, AArch64.abi, AArch64.argRegs] using finSat 96 28 32)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by kernel_rfl) (by kernel_rfl) (by decide) (by decide) (calleeSide v) coreSide
    v.suffix v.features

end VG.Proof.Pbkdf2.Md.AArch64.Sha224

end

end

/-! ### `Sha1.AArch64.Sha2Backend`, which the modules that import this one used -/

section

/-! ### `Sha1.AArch64.ScalarBackend`, which the modules that import this one used -/

section

@[expose] public section

namespace VG.Proof.Sha1.AArch64.Scalar

open VG.AArch64

/-- The scalar compression backend and the checked facts its streaming callers
need. Its code keeps the callee-saved registers in lanes of vector
registers, so the analyses are those that follow the lanes (`LaneTaint`). -/
def backend : Compress where
  name := "vg_sha1_compress"
  code := Impl.Sha1.AArch64.compress
  verified := Proof.Sha1.AArch64.compress_verified
  noFrames := by lit_decide
  keepsV := by lit_decide
  side := by lit_decide
  suffix := ""
  features := []
  updateCT := by exact (LaneTaint.constantTime (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ hp => MdStream.AArch64.Update.agree₀ hp) (by taint_decide))
  finalizeCT := by exact (LaneTaint.constantTime (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀ hp) (by taint_decide))
  updateDepth := by lit_decide
  finalizeDepth := by lit_decide
  oneShot := by exact (LaneTaint.constantTime (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ hp => MdStream.AArch64.OneShot.agree₀ hp) (by taint_decide))

end VG.Proof.Sha1.AArch64.Scalar

end

end

@[expose] public section

namespace VG.Proof.Sha1.AArch64.Sha2

open VG.AArch64

/-- The sha2 compression backend and the checked facts its streaming callers need. -/
def backend : Compress where
  name := "vg_sha1_compress_sha2"
  code := Impl.Sha1.AArch64.Sha2.compress
  verified := Proof.Sha1.AArch64.Sha2.compress_verified
  noFrames := by lit_decide
  keepsV := by lit_decide
  side := by lit_decide
  suffix := "_sha2"
  features := ["sha2"]
  updateCT := by exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ hp => MdStream.AArch64.Update.agree₀ hp) (by taint_decide))
  finalizeCT := by exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀ hp) (by taint_decide))
  updateDepth := by lit_decide
  finalizeDepth := by lit_decide
  oneShot := by exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ hp => MdStream.AArch64.OneShot.agree₀ hp) (by taint_decide))

end VG.Proof.Sha1.AArch64.Sha2

end

end

/-!
# The SHA-512 family on AArch64, as Merkle–Damgård hash functions

SHA-384, SHA-512, SHA-512/224 and SHA-512/256, with their compression
function, as variants of `MdHash` (`sha384`, …), from which HMAC and PBKDF2
are emitted (`Generic/MdHash/AArch64/`). Their streaming code is the generic
Merkle–Damgård code (`Stream.params`), shared by the four, which differ in
their initial hash value `iv` and the size `D` of their digest, the first `D`
bytes of the final hash value. The facts about the code HMAC and PBKDF2 add,
which do not depend on the functions they call, are checked once for each
member (`coreOK`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64.Sha512

open VG.AArch64
open VG.Proof.Sha512.AArch64 (Compress)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open Spec.Sha512 (H0_384 H0_512 H0_512_224 H0_512_256)
open VG.Impl.MdStream.AArch64 (out64)

/-- The member of the SHA-512 family of instance `I`, with a `D`-byte digest,
initial hash value `iv` and streaming `init` named `initN`. -/
def hash (v : Compress) (I : Spec.Hmac.Instance) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Hash where
  P := Impl.Pbkdf2.AArch64.ofMd Impl.Sha512.AArch64.Stream.params
  D := D
  W := I.scratch
  compN := v.name
  compC := v.code
  initN := initN
  initC := Impl.Sha512.AArch64.Stream.init iv
  updN := "vg_sha512_update_scratch" ++ v.suffix
  updC := v.update
  finN := "vg_sha512_finalize_scratch" ++ v.suffix
  finC := v.finalize
  hmacInitN := s!"vg_hmac_{I.rust}_init_scratch" ++ v.suffix
  hmacFinN := s!"vg_hmac_{I.rust}_finalize_scratch" ++ v.suffix
  iterN := s!"vg_pbkdf2_hmac_{I.rust}_iterate" ++ v.suffix

/-- A member of the family without the functions it calls. -/
def coreH (D : Nat) : Hash :=
  ⟨Impl.Pbkdf2.AArch64.ofMd Impl.Sha512.AArch64.Stream.params, D, 234, "", .block [], "", .block [], "", .block [], "", .block [], "", "", ""⟩

theorem coreOK (D : Nat) (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) : CoreOK (coreH D) := by
  rcases hD with rfl | rfl | rfl | rfl <;> refine {
      pbk := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      iter := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      hinit := {
        pro := ⟨?_, ?_⟩
        argI := List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_nil _⟩⟩
        keys := ⟨?_, ?_⟩
        mid := ⟨?_, ?_⟩
        restore := ⟨?_, ?_⟩ }
      hfin := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      fitI := ?_
      fitF := ?_
  }
  taint_decide_all

theorem anyOK (D : Nat) (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) : Any.AnyOK (coreH D) := by
  rcases hD with rfl | rfl | rfl | rfl <;> refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem coreSide (D : Nat) (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) : CoreSide (coreH D) := by
  rcases hD with rfl | rfl | rfl | rfl <;> exact ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

/-- The initial hash values of the family. -/
abbrev IVs (iv : Spec.Sha512.HashValue) : Prop := iv = H0_384 ∨ iv = H0_512 ∨ iv = H0_512_224 ∨ iv = H0_512_256

section
variable (v : Compress)
variable {I : Spec.Hmac.Instance} {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue}

/-- The streaming functions of the member of instance `I`, verified against
the contracts HMAC's proofs call them with. -/
def streamOK (hR : I.S.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, I.S.H.hash m = (Spec.Sha512.finalHash iv m).take D)
    (hB : I.S.H.blockSize = 128) (hS : I.S.stateBytes = 192) (hDs : I.S.digestBytes = D)
    (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) (hiv : IVs iv) :
    Calls.StreamOK (hash v I D initN iv).stream where
  SH := I.S
  Wb := Impl.Sha512.AArch64.scratchBytes + 48
  hS := hS
  hD := hDs
  hB := hB
  hDF := by show D ≤ 64; omega_using [hD]
  hF := Nat.le_refl 64
  hD0 := by show 0 < D; omega_using [hD]
  hS0 := show 0 < 192 by decide
  hSB := show 192 ≤ 256 by decide
  hB0 := show 0 < 128 by decide
  hBB := Nat.le_refl 128
  hWb := by show Impl.Sha512.AArch64.scratchBytes + 48 ≤ 8 * ((Impl.Sha512.AArch64.Stream.params.so + 48) / 8); decide
  hW := by show (Impl.Sha512.AArch64.Stream.params.so + 48) / 8 ≤ 134; decide
  repr := hR ▸ Hmac.Generic.Common.sha512_repr iv
  init := hR ▸ Proof.Sha512.AArch64.Stream.init_verified iv
  upd := hR ▸ v.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h iv m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.update_verified.2.2 }
  fin := v.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr hl hc => by
        show List.take D (Spec.Sha512.bytesAt s'.mem _ 64) = _
        rw [hh, h iv m (hR ▸ hr) hl hc]
      pub := fun _ _ _ _ h => h
      sat := v.finalize_verified.2.2 }
  initDepth := by
    show (Impl.Sha512.AArch64.Stream.init iv).aarch64Depth ≤ 1
    rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  updDepth := by show v.update.aarch64Depth ≤ 1; rw [v.update_depth]
  finDepth := by show v.finalize.aarch64Depth ≤ 1; rw [v.finalize_depth]

/-- `HashOK` for the member of instance `I`, whose specification is the
family's from `iv`, with its digest the first `D` bytes. -/
def ok (hR : I.S.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, I.S.H.hash m = (Spec.Sha512.finalHash iv m).take D)
    (hB : I.S.H.blockSize = 128) (hS : I.S.stateBytes = 192) (hDs : I.S.digestBytes = D)
    (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) (hW : I.scratch = 234) (hiv : IVs iv) :
    HashOK (hash v I D initN iv) where
  initKeepsV := by rfl
  updKeepsV := v.update_keepsV
  finKeepsV := v.finalize_keepsV
  md := Proof.Sha512.md
  shape := Pbkdf2.AArch64.Shape.ofMd Proof.Sha512.AArch64.Stream.shape
  comp := ⟨v.verified.1, v.verified.2.1, v.noFrames, v.keepsV⟩
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega_using [hj])
  lenOk _ h := h
  stream := streamOK v hR hh hB hS hDs hD hiv
  iv := iv
  repr _ _ _ := by show I.S.Repr _ _ _ ↔ _; rw [hR]; exact Proof.Sha512.repr_iff
  hash := hh
  sizes := by
    show Pbkdf2.AArch64.Sizes (Impl.Pbkdf2.AArch64.ofMd Impl.Sha512.AArch64.Stream.params) D I.scratch
    rw [hW]
    rcases hD with rfl | rfl | rfl | rfl <;>
    exact ⟨⟨by decide, by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide⟩
  L := by show 0 < Impl.Sha512.AArch64.Stream.params.L ∧ Impl.Sha512.AArch64.Stream.params.L ≤ 16; decide
  W := by show I.scratch ≤ 256; omega_using [hW]
  hPad := by show 16 * (D / 16 + 1) + 16 ≤ 128; omega_using [hD]
  L816 := by show Impl.Sha512.AArch64.Stream.params.L = 8 ∨ Impl.Sha512.AArch64.Stream.params.L = 16; decide

end

/-- The hash function's code that HMAC and PBKDF2 call writes no PSTATE.DIT
and calls nothing indirectly: the compression function's (`Compress.side`),
the streaming functions' own instructions, and `init`'s for the member's
initial hash value. -/
theorem calleeSide (v : Compress) (I : Spec.Hmac.Instance) (D : Nat) (initN : String)
    (iv : Spec.Sha512.HashValue) (hi : ScrubAll.sideAll noDit (Impl.Sha512.AArch64.Stream.init iv) = true) :
    CalleeSide (hash v I D initN iv) :=
  ⟨v.side, hi, mdUpdate_side _ _ (by kernel_rfl) v.side, mdFinalize_side _ _ (by kernel_rfl) v.side⟩

/-- `Impl.Sha512.AArch64.Stream.Fn.update`, the function as emitted, cleanup included: it meets its
contract in constant time and returns without secret residue. -/
theorem update_scrubbed (v : Compress) :
    VerifiedScrubbed AArch64.target (Impl.Sha512.AArch64.Stream.Fn.update v.suffix v.code)
      (Spec.Sha512.updateContract AArch64.abi (16 + 688)) 0 :=
  AArch64.ScrubAll.verifiedScrubbedOf
    (Proof.Sha512.AArch64.Shared.update_of v.update_verified)
    (AArch64.ScrubAll.scrubAllOk_regs (sig := Spec.Sha512.updateSig) (by decide) (by decide) (Nat.le_refl _) (Proof.Sha512.updatePost_out _))
    (by decide) (depth_frame_le (mdUpdate_depth _ _ _ v.updateDepth))
    (AArch64.ScrubAll.sideAll_withStackScratch rfl rfl rfl (mdUpdate_side _ _ (by kernel_rfl) v.side)) (Or.inl rfl)

/-- `Impl.Sha512.AArch64.Stream.Fn.finalize`, the function as emitted, cleanup included: it meets its
contract in constant time and returns without secret residue. -/
theorem finalize_scrubbed (v : Compress) :
    VerifiedScrubbed AArch64.target (Impl.Sha512.AArch64.Stream.Fn.finalize v.suffix v.code)
      (Spec.Sha512.finalizeContract AArch64.abi (16 + 688)) 0 :=
  AArch64.ScrubAll.verifiedScrubbedOf
    (Proof.Sha512.AArch64.Shared.finalize_of v.finalize_verified)
    (AArch64.ScrubAll.scrubAllOk_regs (sig := Spec.Sha512.finalizeSig) (by decide) (by decide) (Nat.le_refl _) (Proof.Sha512.finalizePost_out _))
    (by decide) (depth_frame_le (mdFinalize_depth _ _ _ v.finalizeDepth))
    (AArch64.ScrubAll.sideAll_withStackScratch rfl rfl rfl (mdFinalize_side _ _ (by kernel_rfl) v.side)) (Or.inl rfl)

/-- `Impl.Sha512.AArch64.Stream.Fn.digest512`, the function as emitted, cleanup included: it meets its
contract in constant time and returns without secret residue. -/
theorem digest512_scrubbed (v : Compress) :
    VerifiedScrubbed AArch64.target (Impl.Sha512.AArch64.Stream.Fn.digest512 v.suffix v.code)
      (Spec.Sha512.digestContract AArch64.abi 64 Spec.Sha512.sha512 Proof.Sha512.AArch64.OneShot.stack) 0 :=
  AArch64.ScrubAll.verifiedScrubbedOf
    ((v.oneShot_verified (by decide) Proof.Sha512.AArch64.Stream.shape.toD v.oneShot512).of_implies (Proof.Sha512.AArch64.OneShot.implies (by decide) fun m => List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))))
    (AArch64.ScrubAll.scrubAllOk_regs (sig := (Spec.Sha512.digestSig 64)) (by decide) (by decide) (Nat.le_refl _) (Proof.Sha512.digestPost_out _ _ _ (by decide)))
    (by decide) (mdDigest_depth _ _ _ _ (by decide) v.noFrames)
    (mdDigest_side _ _ _ (by kernel_rfl) v.side) (Or.inl rfl)

/-- `Impl.Sha512.AArch64.Stream.Fn.finalize384`, the function as emitted, cleanup included: it meets its
contract in constant time and returns without secret residue. -/
theorem finalize384_scrubbed (v : Compress) :
    VerifiedScrubbed AArch64.target (Impl.Sha512.AArch64.Stream.Fn.finalize384 v.suffix v.code)
      (Spec.Sha512.finalizeDigestContract AArch64.abi H0_384 48 Spec.Sha512.sha384 (16 + 688)) 0 :=
  AArch64.ScrubAll.verifiedScrubbedOf
    (Proof.Sha512.AArch64.Shared.finalizeDigest_of (.inl rfl) (v.finalizeDigest_verified Proof.Sha512.AArch64.Stream.shape384 v.digest384) (fun _ => rfl))
    (AArch64.ScrubAll.scrubAllOk_regs (sig := (Spec.Sha512.finalizeDigestSig 48)) (by decide) (by decide) (Nat.le_refl _) (Proof.Sha512.finalizeDigestPost_out _ _ _ _ (by decide)))
    (by decide) (depth_frame_le (mdFinalize_depth _ _ _ v.digest384.depth))
    (AArch64.ScrubAll.sideAll_withStackScratch rfl rfl rfl (mdFinalize_side _ _ (by kernel_rfl) v.side)) (Or.inl rfl)

/-- `Impl.Sha512.AArch64.Stream.Fn.digest384`, the function as emitted, cleanup included: it meets its
contract in constant time and returns without secret residue. -/
theorem digest384_scrubbed (v : Compress) :
    VerifiedScrubbed AArch64.target (Impl.Sha512.AArch64.Stream.Fn.digest384 v.suffix v.code)
      (Spec.Sha512.digestContract AArch64.abi 48 Spec.Sha512.sha384 Proof.Sha512.AArch64.OneShot.stack) 0 :=
  AArch64.ScrubAll.verifiedScrubbedOf
    ((v.oneShot_verified (by decide) Proof.Sha512.AArch64.Stream.shape384 v.oneShot384).of_implies (Proof.Sha512.AArch64.OneShot.implies (by decide) fun _ => rfl))
    (AArch64.ScrubAll.scrubAllOk_regs (sig := (Spec.Sha512.digestSig 48)) (by decide) (by decide) (Nat.le_refl _) (Proof.Sha512.digestPost_out _ _ _ (by decide)))
    (by decide) (mdDigest_depth _ _ _ _ (by decide) v.noFrames)
    (mdDigest_side _ _ _ (by kernel_rfl) v.side) (Or.inl rfl)

/-- `Impl.Sha512.AArch64.Stream.Fn.finalize512_256`, the function as emitted, cleanup included: it meets its
contract in constant time and returns without secret residue. -/
theorem finalize512_256_scrubbed (v : Compress) :
    VerifiedScrubbed AArch64.target (Impl.Sha512.AArch64.Stream.Fn.finalize512_256 v.suffix v.code)
      (Spec.Sha512.finalizeDigestContract AArch64.abi H0_512_256 32 Spec.Sha512.sha512_256 (16 + 688)) 0 :=
  AArch64.ScrubAll.verifiedScrubbedOf
    (Proof.Sha512.AArch64.Shared.finalizeDigest_of (.inr (.inl rfl)) (v.finalizeDigest_verified Proof.Sha512.AArch64.Stream.shape512_256 v.digest512_256) (fun _ => rfl))
    (AArch64.ScrubAll.scrubAllOk_regs (sig := (Spec.Sha512.finalizeDigestSig 32)) (by decide) (by decide) (Nat.le_refl _) (Proof.Sha512.finalizeDigestPost_out _ _ _ _ (by decide)))
    (by decide) (depth_frame_le (mdFinalize_depth _ _ _ v.digest512_256.depth))
    (AArch64.ScrubAll.sideAll_withStackScratch rfl rfl rfl (mdFinalize_side _ _ (by kernel_rfl) v.side)) (Or.inl rfl)

/-- `Impl.Sha512.AArch64.Stream.Fn.digest512_256`, the function as emitted, cleanup included: it meets its
contract in constant time and returns without secret residue. -/
theorem digest512_256_scrubbed (v : Compress) :
    VerifiedScrubbed AArch64.target (Impl.Sha512.AArch64.Stream.Fn.digest512_256 v.suffix v.code)
      (Spec.Sha512.digestContract AArch64.abi 32 Spec.Sha512.sha512_256 Proof.Sha512.AArch64.OneShot.stack) 0 :=
  AArch64.ScrubAll.verifiedScrubbedOf
    ((v.oneShot_verified (by decide) Proof.Sha512.AArch64.Stream.shape512_256 v.oneShot512_256).of_implies (Proof.Sha512.AArch64.OneShot.implies (by decide) fun _ => rfl))
    (AArch64.ScrubAll.scrubAllOk_regs (sig := (Spec.Sha512.digestSig 32)) (by decide) (by decide) (Nat.le_refl _) (Proof.Sha512.digestPost_out _ _ _ (by decide)))
    (by decide) (mdDigest_depth _ _ _ _ (by decide) v.noFrames)
    (mdDigest_side _ _ _ (by kernel_rfl) v.side) (Or.inl rfl)

/-- `Impl.Sha512.AArch64.Stream.Fn.finalize512_224`, the function as emitted, cleanup included: it meets its
contract in constant time and returns without secret residue. -/
theorem finalize512_224_scrubbed (v : Compress) :
    VerifiedScrubbed AArch64.target (Impl.Sha512.AArch64.Stream.Fn.finalize512_224 v.suffix v.code)
      (Spec.Sha512.finalizeDigestContract AArch64.abi H0_512_224 28 Spec.Sha512.sha512_224 (16 + 688)) 0 :=
  AArch64.ScrubAll.verifiedScrubbedOf
    (Proof.Sha512.AArch64.Shared.finalizeDigest_of (.inr (.inr rfl)) (v.finalizeDigest_verified Proof.Sha512.AArch64.Stream.shape512_224 v.digest512_224) (fun _ => rfl))
    (AArch64.ScrubAll.scrubAllOk_regs (sig := (Spec.Sha512.finalizeDigestSig 28)) (by decide) (by decide) (Nat.le_refl _) (Proof.Sha512.finalizeDigestPost_out _ _ _ _ (by decide)))
    (by decide) (depth_frame_le (mdFinalize_depth _ _ _ v.digest512_224.depth))
    (AArch64.ScrubAll.sideAll_withStackScratch rfl rfl rfl (mdFinalize_side _ _ (by kernel_rfl) v.side)) (Or.inl rfl)

/-- `Impl.Sha512.AArch64.Stream.Fn.digest512_224`, the function as emitted, cleanup included: it meets its
contract in constant time and returns without secret residue. -/
theorem digest512_224_scrubbed (v : Compress) :
    VerifiedScrubbed AArch64.target (Impl.Sha512.AArch64.Stream.Fn.digest512_224 v.suffix v.code)
      (Spec.Sha512.digestContract AArch64.abi 28 Spec.Sha512.sha512_224 Proof.Sha512.AArch64.OneShot.stack) 0 :=
  AArch64.ScrubAll.verifiedScrubbedOf
    ((v.oneShot_verified (by decide) Proof.Sha512.AArch64.Stream.shape512_224 v.oneShot512_224).of_implies (Proof.Sha512.AArch64.OneShot.implies (by decide) fun _ => rfl))
    (AArch64.ScrubAll.scrubAllOk_regs (sig := (Spec.Sha512.digestSig 28)) (by decide) (by decide) (Nat.le_refl _) (Proof.Sha512.digestPost_out _ _ _ (by decide)))
    (by decide) (mdDigest_depth _ _ _ _ (by decide) v.noFrames)
    (mdDigest_side _ _ _ (by kernel_rfl) v.side) (Or.inl rfl)

/-! ## SHA-384 -/

theorem sha384_satI : ∃ s, (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha384I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.sha384I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi, AArch64.argRegs] using initSat 192 234

theorem sha384_satF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha384I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha384I, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi, AArch64.argRegs] using finSat 192 48 234

theorem sha384_satT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha384I AArch64.abi).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.iterateContract, Spec.Hmac.sha384I, Proof.Pbkdf2.iterateContract,
    Proof.Pbkdf2.iterateSig, Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi, AArch64.argRegs] using
    Pbkdf2.AArch64.iterSat 192 48 234

theorem sha384_satA : ∃ s, (Any.anyScratchContract Spec.Hmac.sha384I.S Spec.Hmac.sha384I.initAnyKeyScratch).pre s := by
  inst_sat [Any.anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha384I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi, AArch64.argRegs] using initSat 192 426

theorem sha384_satP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha384I AArch64.abi 16).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I,
    Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi,
    AArch64.argRegs] using pbkSat 426

theorem sha384_satPF :
    ∃ s, (Spec.Hmac.sha384I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame Spec.Hmac.sha384I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi,
    AArch64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

/-- HMAC's buffers fit in the right-sized working space (`MdHash.initW`, `MdHash.finW`). -/
theorem fitI (v : Compress) (I : Spec.Hmac.Instance) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : (hash v I D initN iv).stream.buf ≤ 8 * 94 := by
  simp only [hash, Hash.stream, Impl.Pbkdf2.Md.AArch64.Stream.buf, Impl.Pbkdf2.AArch64.ofMd,
    Impl.Sha512.AArch64.Stream.params, Impl.Sha512.AArch64.scratchBytes]
  decide

theorem fitF (v : Compress) (I : Spec.Hmac.Instance) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : (hash v I D initN iv).stream.buf + (hash v I D initN iv).stream.F ≤ 8 * 102 := by
  simp only [hash, Hash.stream, Impl.Pbkdf2.Md.AArch64.Stream.buf, Impl.Pbkdf2.AArch64.ofMd,
    Impl.Sha512.AArch64.Stream.params, Impl.Sha512.AArch64.scratchBytes]
  decide

theorem sha384_coreOK : CoreOK (coreH 48) := coreOK 48 (Or.inr (Or.inr (Or.inl rfl)))

theorem sha384_anyOK : Any.AnyOK (coreH 48) := anyOK 48 (Or.inr (Or.inr (Or.inl rfl)))

/-- SHA-384 with its compression function `v`. -/
def sha384 (v : Compress) : MdHash :=
  MdHash.of (H := hash v Spec.Hmac.sha384I 48 Spec.Sha512.init384Api.name H0_384)
    (ok v rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inr (Or.inl rfl))) rfl (Or.inl rfl)) sha384_coreOK ⟨Spec.Mgf1.sha384, by simp [mdHashes], fun _ => rfl, rfl⟩ rfl rfl
    sha384_satI sha384_satF sha384_satT sha384_satP (by decide)
    sha384_anyOK sha384_satA (by decide) Proof.Hmac.sha384_local
    (by
      unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by decide)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) sha384_satPF
    94 102 ⟨fitI .., by decide, by decide, by decide⟩ ⟨fitF .., by decide, by decide, by decide⟩
    (by inst_sat [Proof.Hmac.initScratchContract, Spec.Hmac.sha384I, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi, AArch64.argRegs] using initSat 192 94)
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by inst_sat [Proof.Hmac.finalizeScratchContract, Spec.Hmac.sha384I, Proof.Hmac.finalizeScratchSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi, AArch64.argRegs] using finSat 192 48 102)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by kernel_rfl) (by kernel_rfl) (by decide) (by decide) (calleeSide v _ _ _ _ (by kernel_rfl)) (coreSide 48 (Or.inr (Or.inr (Or.inl rfl))))
    v.suffix v.features

/-! ## SHA-512 -/

theorem sha512_satI : ∃ s, (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha512I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.sha512I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi, AArch64.argRegs] using initSat 192 234

theorem sha512_satF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha512I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha512I, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi, AArch64.argRegs] using finSat 192 64 234

theorem sha512_satT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha512I AArch64.abi).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.iterateContract, Spec.Hmac.sha512I, Proof.Pbkdf2.iterateContract,
    Proof.Pbkdf2.iterateSig, Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi, AArch64.argRegs] using
    Pbkdf2.AArch64.iterSat 192 64 234

theorem sha512_satA : ∃ s, (Any.anyScratchContract Spec.Hmac.sha512I.S Spec.Hmac.sha512I.initAnyKeyScratch).pre s := by
  inst_sat [Any.anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha512I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi, AArch64.argRegs] using initSat 192 426

theorem sha512_satP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha512I AArch64.abi 16).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I,
    Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi,
    AArch64.argRegs] using pbkSat 426

theorem sha512_satPF :
    ∃ s, (Spec.Hmac.sha512I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame Spec.Hmac.sha512I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi,
    AArch64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

theorem sha512_coreOK : CoreOK (coreH 64) := coreOK 64 (Or.inr (Or.inr (Or.inr rfl)))

theorem sha512_anyOK : Any.AnyOK (coreH 64) := anyOK 64 (Or.inr (Or.inr (Or.inr rfl)))

/-- SHA-512 with its compression function. -/
def sha512 (v : Compress) : MdHash :=
  MdHash.of (H := hash v Spec.Hmac.sha512I 64 Spec.Sha512.init512Api.name H0_512)
    (ok v rfl (fun m => (List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))).symm) rfl rfl rfl (Or.inr (Or.inr (Or.inr rfl))) rfl (Or.inr (Or.inl rfl))) sha512_coreOK ⟨Spec.Mgf1.sha512, by simp [mdHashes], fun _ => rfl, rfl⟩ rfl rfl
    sha512_satI sha512_satF sha512_satT sha512_satP (by decide)
    sha512_anyOK sha512_satA (by decide) Proof.Hmac.sha512_local
    (by
      unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by decide)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) sha512_satPF
    94 102 ⟨fitI .., by decide, by decide, by decide⟩ ⟨fitF .., by decide, by decide, by decide⟩
    (by inst_sat [Proof.Hmac.initScratchContract, Spec.Hmac.sha512I, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi, AArch64.argRegs] using initSat 192 94)
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by inst_sat [Proof.Hmac.finalizeScratchContract, Spec.Hmac.sha512I, Proof.Hmac.finalizeScratchSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi, AArch64.argRegs] using finSat 192 64 102)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by kernel_rfl) (by kernel_rfl) (by decide) (by decide) (calleeSide v _ _ _ _ (by kernel_rfl)) (coreSide 64 (Or.inr (Or.inr (Or.inr rfl))))
    v.suffix v.features

/-! ## SHA-512/224 -/

theorem sha512_224_satI : ∃ s, (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha512_224I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.sha512_224I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi, AArch64.argRegs] using initSat 192 234

theorem sha512_224_satF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha512_224I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha512_224I, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi, AArch64.argRegs] using finSat 192 28 234

theorem sha512_224_satT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha512_224I AArch64.abi).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.iterateContract, Spec.Hmac.sha512_224I, Proof.Pbkdf2.iterateContract,
    Proof.Pbkdf2.iterateSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi, AArch64.argRegs] using
    Pbkdf2.AArch64.iterSat 192 28 234

theorem sha512_224_satA : ∃ s, (Any.anyScratchContract Spec.Hmac.sha512_224I.S Spec.Hmac.sha512_224I.initAnyKeyScratch).pre s := by
  inst_sat [Any.anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha512_224I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi, AArch64.argRegs] using initSat 192 426

theorem sha512_224_satP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha512_224I AArch64.abi 16).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I,
    Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi,
    AArch64.argRegs] using pbkSat 426

theorem sha512_224_satPF :
    ∃ s, (Spec.Hmac.sha512_224I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame Spec.Hmac.sha512_224I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi,
    AArch64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

theorem sha512_224_coreOK : CoreOK (coreH 28) := coreOK 28 (Or.inl rfl)

theorem sha512_224_anyOK : Any.AnyOK (coreH 28) := anyOK 28 (Or.inl rfl)

/-- SHA-512/224 with its compression function. -/
def sha512_224 (v : Compress) : MdHash :=
  MdHash.of (H := hash v Spec.Hmac.sha512_224I 28 Spec.Sha512.init512_224Api.name H0_512_224)
    (ok v rfl (fun _ => rfl) rfl rfl rfl (Or.inl rfl) rfl (Or.inr (Or.inr (Or.inl rfl)))) sha512_224_coreOK ⟨Spec.Mgf1.sha512_224, by simp [mdHashes], fun _ => rfl, rfl⟩ rfl rfl
    sha512_224_satI sha512_224_satF sha512_224_satT sha512_224_satP (by decide)
    sha512_224_anyOK sha512_224_satA (by decide) Proof.Hmac.sha512_224_local
    (by
      unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by decide)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) sha512_224_satPF
    94 102 ⟨fitI .., by decide, by decide, by decide⟩ ⟨fitF .., by decide, by decide, by decide⟩
    (by inst_sat [Proof.Hmac.initScratchContract, Spec.Hmac.sha512_224I, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi, AArch64.argRegs] using initSat 192 94)
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by inst_sat [Proof.Hmac.finalizeScratchContract, Spec.Hmac.sha512_224I, Proof.Hmac.finalizeScratchSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi, AArch64.argRegs] using finSat 192 28 102)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by kernel_rfl) (by kernel_rfl) (by decide) (by decide) (calleeSide v _ _ _ _ (by kernel_rfl)) (coreSide 28 (Or.inl rfl))
    v.suffix v.features

/-! ## SHA-512/256 -/

theorem sha512_256_satI : ∃ s, (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha512_256I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.initScratchContract, Spec.Hmac.sha512_256I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi, AArch64.argRegs] using initSat 192 234

theorem sha512_256_satF : ∃ s, (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha512_256I AArch64.abi 16).pre s := by
  inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha512_256I, Proof.Hmac.finalizeScratchContract,
    Proof.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi, AArch64.argRegs] using finSat 192 32 234

theorem sha512_256_satT : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha512_256I AArch64.abi).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.iterateContract, Spec.Hmac.sha512_256I, Proof.Pbkdf2.iterateContract,
    Proof.Pbkdf2.iterateSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi, AArch64.argRegs] using
    Pbkdf2.AArch64.iterSat 192 32 234

theorem sha512_256_satA : ∃ s, (Any.anyScratchContract Spec.Hmac.sha512_256I.S Spec.Hmac.sha512_256I.initAnyKeyScratch).pre s := by
  inst_sat [Any.anyScratchContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha512_256I, Proof.Hmac.initScratchSig,
    Spec.Hmac.initPost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi, AArch64.argRegs] using initSat 192 426

theorem sha512_256_satP : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha512_256I AArch64.abi 16).pre s := by
  inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I,
    Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi,
    AArch64.argRegs] using pbkSat 426

theorem sha512_256_satPF :
    ∃ s, (Spec.Hmac.sha512_256I.pbkdf2Contract AArch64.abi (16 + pbkdf2Frame Spec.Hmac.sha512_256I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi,
    AArch64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

theorem sha512_256_coreOK : CoreOK (coreH 32) := coreOK 32 (Or.inr (Or.inl rfl))

theorem sha512_256_anyOK : Any.AnyOK (coreH 32) := anyOK 32 (Or.inr (Or.inl rfl))

/-- SHA-512/256 with its compression function. -/
def sha512_256 (v : Compress) : MdHash :=
  MdHash.of (H := hash v Spec.Hmac.sha512_256I 32 Spec.Sha512.init512_256Api.name H0_512_256)
    (ok v rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inl rfl)) rfl (Or.inr (Or.inr (Or.inr rfl)))) sha512_256_coreOK ⟨Spec.Mgf1.sha512_256, by simp [mdHashes], fun _ => rfl, rfl⟩ rfl rfl
    sha512_256_satI sha512_256_satF sha512_256_satT sha512_256_satP (by decide)
    sha512_256_anyOK sha512_256_satA (by decide) Proof.Hmac.sha512_256_local
    (by
      unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by decide)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) sha512_256_satPF
    94 102 ⟨fitI .., by decide, by decide, by decide⟩ ⟨fitF .., by decide, by decide, by decide⟩
    (by inst_sat [Proof.Hmac.initScratchContract, Spec.Hmac.sha512_256I, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi, AArch64.argRegs] using initSat 192 94)
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by inst_sat [Proof.Hmac.finalizeScratchContract, Spec.Hmac.sha512_256I, Proof.Hmac.finalizeScratchSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi, AArch64.argRegs] using finSat 192 32 102)
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by kernel_rfl) (by kernel_rfl) (by decide) (by decide) (calleeSide v _ _ _ _ (by kernel_rfl)) (coreSide 32 (Or.inr (Or.inl rfl)))
    v.suffix v.features

end VG.Proof.Pbkdf2.Md.AArch64.Sha512
