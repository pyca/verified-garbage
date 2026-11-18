module

public import VerifiedGarbage.Proof.Sha512.AArch64.OneShot
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
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
public import VerifiedGarbage.Proof.Sha1.AArch64.Variant
public import VerifiedGarbage.Proof.Sha1.AArch64.Sha2.Compress
import VerifiedGarbage.Proof.Sha1.AArch64.Sha2.Lit
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha1.AArch64.Variant
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

/-- The streaming `update` and `finalize` made with `v`, which keep their
working space in a frame of their own, and the one-shot `digest` (`Proof/Pbkdf2/Md/AArch64/Hashes/Sha512.lean`), which
`Generic/MdHash/AArch64/Stream.lean` emits. -/
def stream : List StreamFn := [
  { api := Spec.Sha1.updateApi
    code := Impl.StackScratch.AArch64.withStackScratch 160 .x4 v.update
    contract := Spec.Sha1.updateContract AArch64.abi (16 + 160)
    stack := 16 + 160
    verified := Proof.Sha1.AArch64.Shared.update_of v.update_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha1.finalizeApi
    code := Impl.StackScratch.AArch64.withStackScratch 160 .x3 v.finalize
    contract := Spec.Sha1.finalizeContract AArch64.abi (16 + 160)
    stack := 16 + 160
    verified := Proof.Sha1.AArch64.Shared.finalize_of v.finalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha1.digestApi
    code := Proof.Sha1.AArch64.oneShotWith v.name v.code
    contract := Spec.Sha1.digestContract AArch64.abi Proof.Sha1.AArch64.OneShot.stack
    stack := Proof.Sha1.AArch64.OneShot.stack
    verified := v.oneShot_verified.of_implies Proof.Sha1.AArch64.OneShot.implies
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

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
    v.suffix v.features (stream v)

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

/-- SHA-224's `finalize` made with `v`, which writes its digest
(`Compress.finalize224`). -/
def stream : List StreamFn := [
  { api := Spec.Sha256.finalize224Api
    code := Impl.StackScratch.AArch64.withStackScratch 608 .x3 v.finalize224
    contract := Spec.Sha256.finalize224Contract AArch64.abi (16 + 608)
    stack := 16 + 608
    verified := Proof.Sha256.AArch64.Shared.finalize224_of v.finalize224_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha256.digest224Api
    code := Proof.Sha256.AArch64.oneShotWith (out32 7 true) Spec.Sha256.H0_224 v.name
      v.code
    contract := Spec.Sha256.digestContract AArch64.abi 28 Spec.Sha256.sha224 Proof.Sha256.AArch64.OneShot.stack
    stack := Proof.Sha256.AArch64.OneShot.stack
    verified := (v.oneShot_verified (by decide) Proof.Sha256.AArch64.Stream.shape224 v.oneShot224).of_implies
        (Proof.Sha256.AArch64.OneShot.implies (by decide) Proof.Sha256.AArch64.OneShot.sha224_take)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

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
    v.suffix v.features (stream v)

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

/-- Streaming wrappers shared by all four digest sizes. The SHA-512 member
emits them once per backend through `MdHash`; the other members call them:
`update` and `finalize`, which keep their working space in a frame of their
own. -/
def stream (v : Compress) : List StreamFn := [
  { api := Spec.Sha512.updateApi
    code := Impl.StackScratch.AArch64.withStackScratch 688 .x4 v.update
    contract := Spec.Sha512.updateContract AArch64.abi (16 + 688)
    stack := 16 + 688
    verified := Proof.Sha512.AArch64.Shared.update_of v.update_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha512.finalizeApi
    code := Impl.StackScratch.AArch64.withStackScratch 688 .x3 v.finalize
    contract := Spec.Sha512.finalizeContract AArch64.abi (16 + 688)
    stack := 16 + 688
    verified := Proof.Sha512.AArch64.Shared.finalize_of v.finalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha512.digest512Api
    code := Proof.Sha512.AArch64.oneShotWith (out64 8) H0_512 v.suffix v.code
    contract := Spec.Sha512.digestContract AArch64.abi 64 Spec.Sha512.sha512 Proof.Sha512.AArch64.OneShot.stack
    stack := Proof.Sha512.AArch64.OneShot.stack
    verified := (v.oneShot_verified (by decide) Proof.Sha512.AArch64.Stream.shape.toD v.oneShot512).of_implies (Proof.Sha512.AArch64.OneShot.implies (by decide) fun m =>
        List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m)))
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

/-- SHA-384's `finalize` made with `v`, which writes its digest (`finalizeDigestWith`). -/
def stream384 (v : Compress) : List StreamFn := [
  { api := Spec.Sha512.finalize384Api
    code := Impl.StackScratch.AArch64.withStackScratch 688 .x3
      (Impl.Sha512.AArch64.Stream.finalizeDigestWith Impl.Sha512.AArch64.Stream.params384 v.suffix v.code)
    contract := Spec.Sha512.finalizeDigestContract AArch64.abi H0_384 48 Spec.Sha512.sha384 (16 + 688)
    stack := 16 + 688
    verified := Proof.Sha512.AArch64.Shared.finalizeDigest_of (.inl rfl)
      (v.finalizeDigest_verified Proof.Sha512.AArch64.Stream.shape384 v.digest384) (fun _ => rfl)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha512.digest384Api
    code := Proof.Sha512.AArch64.oneShotWith (out64 6) H0_384 v.suffix v.code
    contract := Spec.Sha512.digestContract AArch64.abi 48 Spec.Sha512.sha384 Proof.Sha512.AArch64.OneShot.stack
    stack := Proof.Sha512.AArch64.OneShot.stack
    verified := (v.oneShot_verified (by decide) Proof.Sha512.AArch64.Stream.shape384 v.oneShot384).of_implies (Proof.Sha512.AArch64.OneShot.implies (by decide) fun _ => rfl)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

/-- SHA-512/256's `finalize` made with `v`, which writes its digest (`finalizeDigestWith`). -/
def stream512_256 (v : Compress) : List StreamFn := [
  { api := Spec.Sha512.finalize512_256Api
    code := Impl.StackScratch.AArch64.withStackScratch 688 .x3
      (Impl.Sha512.AArch64.Stream.finalizeDigestWith Impl.Sha512.AArch64.Stream.params512_256 v.suffix v.code)
    contract := Spec.Sha512.finalizeDigestContract AArch64.abi H0_512_256 32 Spec.Sha512.sha512_256 (16 + 688)
    stack := 16 + 688
    verified := Proof.Sha512.AArch64.Shared.finalizeDigest_of (.inr (.inl rfl))
      (v.finalizeDigest_verified Proof.Sha512.AArch64.Stream.shape512_256 v.digest512_256) (fun _ => rfl)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha512.digest512_256Api
    code := Proof.Sha512.AArch64.oneShotWith (out64 4) H0_512_256 v.suffix v.code
    contract := Spec.Sha512.digestContract AArch64.abi 32 Spec.Sha512.sha512_256
      Proof.Sha512.AArch64.OneShot.stack
    stack := Proof.Sha512.AArch64.OneShot.stack
    verified := (v.oneShot_verified (by decide) Proof.Sha512.AArch64.Stream.shape512_256 v.oneShot512_256).of_implies (Proof.Sha512.AArch64.OneShot.implies (by decide) fun _ => rfl)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

/-- SHA-512/224's `finalize` made with `v`, which writes its digest (`finalizeDigestWith`). -/
def stream512_224 (v : Compress) : List StreamFn := [
  { api := Spec.Sha512.finalize512_224Api
    code := Impl.StackScratch.AArch64.withStackScratch 688 .x3
      (Impl.Sha512.AArch64.Stream.finalizeDigestWith Impl.Sha512.AArch64.Stream.params512_224 v.suffix v.code)
    contract := Spec.Sha512.finalizeDigestContract AArch64.abi H0_512_224 28 Spec.Sha512.sha512_224 (16 + 688)
    stack := 16 + 688
    verified := Proof.Sha512.AArch64.Shared.finalizeDigest_of (.inr (.inr rfl))
      (v.finalizeDigest_verified Proof.Sha512.AArch64.Stream.shape512_224 v.digest512_224) (fun _ => rfl)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha512.digest512_224Api
    code := Proof.Sha512.AArch64.oneShotWith (out64 3 ++ Impl.Sha512.AArch64.Stream.outHi 3) H0_512_224
      v.suffix v.code
    contract := Spec.Sha512.digestContract AArch64.abi 28 Spec.Sha512.sha512_224
      Proof.Sha512.AArch64.OneShot.stack
    stack := Proof.Sha512.AArch64.OneShot.stack
    verified := (v.oneShot_verified (by decide) Proof.Sha512.AArch64.Stream.shape512_224 v.oneShot512_224).of_implies (Proof.Sha512.AArch64.OneShot.implies (by decide) fun _ => rfl)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

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
    v.suffix v.features (stream384 v)

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
    v.suffix v.features (stream v)

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
    v.suffix v.features (stream512_224 v)

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
    v.suffix v.features (stream512_256 v)

end VG.Proof.Pbkdf2.Md.AArch64.Sha512
