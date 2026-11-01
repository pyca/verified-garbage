module

public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Instance
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Md
public import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Init
public import VerifiedGarbage.Spec.Sha1.Contract
public import VerifiedGarbage.Proof.Hmac.Stream.Reloc
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Instance
meta import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Md
meta import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Init
meta import VerifiedGarbage.Spec.Sha1.Contract
meta import VerifiedGarbage.Proof.Hmac.Stream.Reloc
meta import VerifiedGarbage.Proof.Hmac.Scratch
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Shared
public import VerifiedGarbage.Proof.Hmac.Scratch
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Shared

/-!
# HMAC-SHA-1 on PPC64LE

SHA-1's streaming functions (`Impl/Sha1/PPC64LE/Stream.lean`), as HMAC's code
over any streaming hash function calls them (`hash`), and what the proofs
need of them (`ok`); the constant time of HMAC's code for them, which the
kernel checks; and the functions against the shared contracts of
`Spec.Hmac.sha1I`.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE.Sha1

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)

/-- SHA-1's streaming functions. -/
def hash : Hash where
  B := 64
  N := 20
  D := 20
  FD := 20
  W := 160
  initN := Spec.Sha1.initApi.name
  initC := Impl.Sha1.PPC64LE.Stream.init
  updN := "vg_sha1_update_scratch"
  updC := Impl.Sha1.PPC64LE.Stream.update
  finN := "vg_sha1_finalize_scratch"
  finC := Impl.Sha1.PPC64LE.Stream.finalize
  hmacInitN := "vg_hmac_sha1_init_scratch"

/-- What the proofs need of them. -/
def ok : HashOK hash where
  SH := Spec.Hmac.sha1S
  hS := rfl
  hD := rfl
  hB := rfl
  dims := ⟨by decide, by decide, by decide, by decide⟩
  hN4 := by decide
  hD0 := by decide
  hDB := by decide
  hD4 := by decide
  hDF := by decide
  hFD64 := by decide
  fh := Spec.Hmac.sha1S.H.hash
  init s hs := Proof.Sha1.PPC64LE.Stream.init_verified.1 s ⟨hs.1, hs.2.1⟩
  upd s hs := Proof.Sha1.PPC64LE.Stream.Update.update_verified.1 s hs
  fin s hs := by
    obtain ⟨t, s', he, ha, h⟩ := Proof.Sha1.PPC64LE.Stream.Finalize.finalize_verified.1 s hs
    exact ⟨t, s', he, ha, fun m hr _ hc => h m hr hc⟩
  initFd := by decide +kernel
  updFd := by decide +kernel
  finFd := by decide +kernel
  initPf := by decide +kernel
  updPf := by decide +kernel
  finPf := by decide +kernel
  reloc m m' p q x hx h hr := Proof.Hmac.Stream.sha1_reloc m m' p q x hx h hr
  congr _ _ _ _ h hr := Proof.Hmac.sha1_local (fun i hi => h i hi) hr
  fhLen x := by simp [hash, Spec.Hmac.sha1S, Spec.Hmac.sha1, Spec.Sha1.hash, Spec.Sha1.wordBytes,
    List.length_flatMap, List.map_const']
  hashTake x := by
    refine (List.take_of_length_le (Nat.le_of_eq ?_)).symm
    simp [hash, Spec.Hmac.sha1S, Spec.Hmac.sha1, Spec.Sha1.hash, Spec.Sha1.wordBytes, List.length_flatMap,
      List.map_const']

/-! ## Constant time -/

theorem init_ct : ConstantTime isa (initG ok.SH (hash.W + 48) 96).pre (initG ok.SH (hash.W + 48) 96).pub
    hash.init :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

theorem fin_ct : ConstantTime isa (finG ok.SH (hash.W + 48 + hash.FD) 96).pre
    (finG ok.SH (hash.W + 48 + hash.FD) 96).pub hash.finalize :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

theorem long_ct : ConstantTime isa (longG ok.SH hash.lbytes 144).pre (longG ok.SH hash.lbytes 144).pub
    hash.initLong :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

/-! ## The shared contracts -/

theorem initScratch : Verified PPC64LE.target hash.init (Proof.Hmac.Instance.initScratchContract Spec.Hmac.sha1I PPC64LE.abi 96) :=
  Shared.initScratch ok rfl (by decide) init_ct (by
    inst_sat [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig,
      Spec.Hmac.initPre, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, PPC64LE.abi, PPC64LE.argRegs]
      using initSat 84 448)

theorem finalizeScratch :
    Verified PPC64LE.target hash.finalize (Proof.Hmac.Instance.finalizeScratchContract Spec.Hmac.sha1I PPC64LE.abi 96) :=
  Shared.finalizeScratch ok rfl (by decide) fin_ct (by
    inst_sat [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract,
      Proof.Hmac.finalizeScratchSig, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, PPC64LE.abi,
      PPC64LE.argRegs]
      using finSat 84 20 448)

theorem longScratch : Verified PPC64LE.target hash.initLong (Shared.longScratchContract ok.SH (hash.lbytes / 8)) :=
  Shared.longScratch ok (by decide) long_ct (by
    inst_sat [Shared.longScratchContract, Shared.longPre, Proof.Hmac.initScratchSig, Spec.Hmac.sha1S, Spec.Hmac.sha1,
      PPC64LE.abi, PPC64LE.argRegs]
      using longSat 84 360)

theorem initAny : Verified PPC64LE.target (initCode hash Spec.Hmac.sha1I 6)
    (Spec.Hmac.sha1I.initAnyKeyContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha1I)) :=
  Shared.initAny (b := 6) (.inl rfl) rfl (by decide)
    (Shared.initFrame initScratch (by decide) (by
      inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
        using initSat 84 0))
    (Shared.longFrame longScratch (by decide) Proof.Hmac.sha1_local (by decide) (by
      inst_sat [Shared.longContract, Shared.longPre, Spec.Hmac.initSig, Spec.Hmac.sha1I, Spec.Hmac.sha1S,
        Spec.Hmac.sha1, longFrame, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
        using longSat 84 0))
    (by
      inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
        using initSat 84 0)

theorem finalize : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame Spec.Hmac.sha1I) .r7 hash.finalize)
    (Spec.Hmac.sha1I.finalizeContract PPC64LE.abi (96 + hmacFrame Spec.Hmac.sha1I)) :=
  Shared.finalizeFrame finalizeScratch (by decide) Proof.Hmac.sha1_local (by decide) (by
    inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
      using finSat 84 20 0)

end VG.Proof.Hmac.Stream.PPC64LE.Sha1
