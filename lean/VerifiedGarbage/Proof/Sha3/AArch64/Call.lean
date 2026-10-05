import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.KeyGen
import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Verify
import VerifiedGarbage.Impl.MlKem1024.AArch64.Encaps
import VerifiedGarbage.Impl.MlKem1024.AArch64.Decaps
import VerifiedGarbage.Impl.MlKem.AArch64.Encaps
import VerifiedGarbage.Impl.MlKem.AArch64.Decaps
import VerifiedGarbage.Impl.MlKem.AArch64.KeyGen
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.ExpandMask
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Impl.MlKem.AArch64.Sample
import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
import VerifiedGarbage.Proof.Framework.AArch64.Spill

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sums`. -/
section

/-!
# Summaries for the constant-time checks of the sponge's callers

The constant-time check of each caller of the sponge (ML-KEM, ML-DSA) with
each Keccak backend (`Permutation`) analyses, at every call, the permutation
and the sponge's functions, and the ML-KEM functions it calls. Here those
calls are summarized once (`taint_summary`), and the checks use the summaries
(`taint_decide_sum`).

Each summary applies to a call from its arguments public, and keeps public
the callee-saved registers the function does not write (`keeping`).
-/

namespace VG.Proof.Sha3.AArch64.MlKemSums

open VG VG.AArch64

/-- The callee-saved registers. -/
def callee : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

/-! ## ML-KEM's functions -/

taint_summary ntt : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1])
  (.call "vg_mlkem_ntt" Impl.MlKem.AArch64.ntt)
  keeping (VectorTaint.ofRegs callee)

taint_summary nttInv : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1])
  (.call "vg_mlkem_inv_ntt" Impl.MlKem.AArch64.nttInv)
  keeping (VectorTaint.ofRegs callee)

taint_summary mul : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
  (.call "vg_mlkem_multiply_ntts" Impl.MlKem.AArch64.multiplyNTTs)
  keeping (VectorTaint.ofRegs callee)

taint_summary add : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1])
  (.call "vg_mlkem_add" Impl.MlKem.AArch64.add)
  keeping (VectorTaint.ofRegs callee)

taint_summary sub : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1])
  (.call "vg_mlkem_sub" Impl.MlKem.AArch64.sub)
  keeping (VectorTaint.ofRegs callee)

taint_summary cbd2 : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1])
  (.call "vg_mlkem_cbd2" Impl.MlKem.AArch64.cbd2)
  keeping (VectorTaint.ofRegs callee)

taint_summary encode12 : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1])
  (.call "vg_mlkem_encode12" Impl.MlKem.AArch64.encode12)
  keeping (VectorTaint.ofRegs callee)

taint_summary decode12 : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1])
  (.call "vg_mlkem_decode12" Impl.MlKem.AArch64.decode12)
  keeping (VectorTaint.ofRegs callee)

taint_summary ce : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x2, .x3])
  (.call "vg_mlkem_compress_encode" Impl.MlKem.AArch64.compressEncode)
  keeping (VectorTaint.ofRegs callee)

taint_summary dd : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1, .x3])
  (.call "vg_mlkem_decode_decompress" Impl.MlKem.AArch64.decodeDecompress)
  keeping (VectorTaint.ofRegs callee)

taint_summary ce1024 : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x2, .x3])
  (.call "vg_mlkem1024_compress_encode" Impl.MlKem1024.AArch64.compressEncode)
  keeping (VectorTaint.ofRegs callee)

taint_summary dd1024 : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1, .x3])
  (.call "vg_mlkem1024_decode_decompress" Impl.MlKem1024.AArch64.decodeDecompress)
  keeping (VectorTaint.ofRegs callee)

end VG.Proof.Sha3.AArch64.MlKemSums

namespace VG.Proof.Sha3.AArch64

open Lean Elab Command

/-- The sets of callee-saved registers, besides `x19`–`x24` (which the
sponge's functions use), public at the calls of the sponge's functions. -/
private def spongeSaved : List (String × String) :=
  [("28", ".x25, .x26, .x27, .x28"), ("27", ".x25, .x26, .x27"), ("26", ".x25, .x26")]

/-- The summaries `sponge_taint_summaries` may define in `ns`, in the order
`taint_decide_sum` tries them. -/
def spongeSumNames : List String :=
  ["absorb23", "absorb24", "absorb28", "absorb27", "absorb24_26"] ++
  (spongeSaved.map fun (n, _) => s!"pad{n}") ++ (spongeSaved.map fun (n, _) => s!"squeeze{n}") ++
  (spongeSaved.map fun (n, _) => s!"perm{n}s") ++ ["permS"] ++
  (spongeSaved.map fun (n, _) => s!"perm{n}") ++ ["absorb", "pad", "squeeze", "perm"]

/-- The ML-KEM functions' summaries (`MlKemSums`). -/
def mlkemSumNames : List String :=
  ["ntt", "nttInv", "mul", "add", "sub", "cbd2", "encode12", "decode12", "ce", "dd", "ce1024",
    "dd1024"].map ("VG.Proof.Sha3.AArch64.MlKemSums." ++ ·)

/-- The commands of `sponge_taint_summaries ns callee`, with the summaries of
the permutation and of `pad` and `squeeze` those of `base`, if given (for a
callee that differs only in its absorb). The permutation and `pad` keep the
callee-saved registers; `absorb` and `squeeze` restore `x19`–`x24` from
memory, and keep `x25`–`x28`. -/
def spongeSumCmds (ns c : String) (base : Option String) :
    List String × List (String × String) := Id.run do
  let fn (f n : String) :=
    s!"(.call (\"vg_keccak_{f}_scratch\" ++ {c}.suffix) (Impl.Sha3.AArch64.Stream.{n}With {c}))"
  let ofRegs (rs : String) := s!"(VectorTaint.ofRegs [{rs}])"
  let all := "(VectorTaint.ofRegs VG.Proof.Sha3.AArch64.MlKemSums.callee)"
  let high := ofRegs ".x25, .x26, .x27, .x28"
  let pns := base.getD ns
  let args := ".x0, .x1, .x2, .x3, .x4, .x5"
  let absorb := s!"taint_summary {ns}.absorb : VectorTaint.taint {ofRegs args} " ++
    s!"{fn "absorb" "absorb"} keeping {high} using {pns}.perm"
  if let some b := base then
    return ([absorb], ["pad", "squeeze", "perm"].map fun n => (s!"{ns}.{n}", s!"{b}.{n}"))
  return ([s!"taint_summary {ns}.perm : VectorTaint.taint {ofRegs ".x0, .x1"} " ++
      s!"(.call {c}.name {c}.code) keeping {all}", absorb,
    s!"taint_summary {ns}.pad : VectorTaint.taint {ofRegs ".x0, .x1, .x2, .x4"} " ++
      s!"{fn "pad" "pad"} keeping {all} using {ns}.perm",
    s!"taint_summary {ns}.squeeze : VectorTaint.taint {ofRegs args} " ++
      s!"{fn "squeeze" "squeeze"} keeping {high} using {ns}.perm"], [])

/-- The commands of `sponge_taint_summaries ns callee saving`, for a
permutation that writes the callee-saved registers (restoring them): no
summary keeps anything, so each function has a summary for each set of
callee-saved registers public at some call (the larger first). The
summaries `permUsing` (e.g. of the permutation's rounds) are used in those of
the permutation. -/
def spongeSumSavingCmds (ns c : String) (permUsing : List String := []) : List String := Id.run do
  let perm := s!"(.call {c}.name {c}.code)"
  let fn (f n : String) :=
    s!"(.call (\"vg_keccak_{f}_scratch\" ++ {c}.suffix) (Impl.Sha3.AArch64.Stream.{n}With {c}))"
  let ofRegs (rs : String) := s!"(VectorTaint.ofRegs [{rs}])"
  let s := ".x19, .x20, .x21, .x22, .x23, .x24"
  let perms := (spongeSaved.map fun (n, rs) => (s!"perm{n}s", s!".x0, .x1, {s}, {rs}")) ++
    [("permS", s!".x0, .x1, {s}")] ++
    (spongeSaved.map fun (n, rs) => (s!"perm{n}", s!".x0, .x1, {rs}")) ++ [("perm", ".x0, .x1")]
  let usingS := " ".intercalate (perms.map fun (n, _) => s!"{ns}.{n}")
  let args := ".x0, .x1, .x2, .x3, .x4, .x5"
  let absorbs := [("absorb23", ".x23, .x25, .x26, .x27, .x28"),
    ("absorb24", ".x24, .x25, .x26, .x27, .x28"), ("absorb28", ".x25, .x26, .x27, .x28"),
    ("absorb27", ".x25, .x26, .x27"), ("absorb24_26", ".x24, .x25, .x26")]
  let permUsingS := if permUsing.isEmpty then "" else " using " ++ " ".intercalate permUsing
  return (perms.map fun (n, rs) =>
      s!"taint_summary {ns}.{n} : VectorTaint.taint {ofRegs rs} {perm}{permUsingS}") ++
    (absorbs.map fun (n, rs) =>
      s!"taint_summary {ns}.{n} : VectorTaint.taint {ofRegs (args ++ ", " ++ rs)} " ++
        s!"{fn "absorb" "absorb"} using {usingS}") ++
    (spongeSaved.map fun (n, rs) =>
      s!"taint_summary {ns}.pad{n} : VectorTaint.taint {ofRegs (".x0, .x1, .x2, .x4, " ++ rs)} " ++
        s!"{fn "pad" "pad"} using {usingS}") ++
    (spongeSaved.map fun (n, rs) =>
      s!"taint_summary {ns}.squeeze{n} : VectorTaint.taint {ofRegs (args ++ ", " ++ rs)} " ++
        s!"{fn "squeeze" "squeeze"} using {usingS}")

/-- `sponge_taint_summaries ns callee` defines, in the namespace `ns`, the
summaries of the permutation `callee` and of the sponge's functions over it
(the absorb, pad and squeeze calls of `Impl.Sha3.AArch64.Stream`), for
`sponge_taint_decide ns`; `sponge_taint_summaries ns callee from base` only
that of absorb, and takes the others from `base` (for a callee that differs
from `base`'s only in its absorb); `sponge_taint_summaries ns callee saving`
those of a permutation that writes (and restores) the callee-saved
registers (`spongeSumSavingCmds`), and `… saving using l₁ …` proves those
of the permutation with the summaries `lᵢ` (e.g. of its rounds, so that the
summaries of the permutation for each set of callee-saved registers do not
each analyse them again). -/
syntax "sponge_taint_summaries " ident ident (" from " ident)? (&" saving")?
  (" using " ident+)? : command

elab_rules : command
  | `(sponge_taint_summaries $ns $callee $[from $base]? $[saving%$sv]? $[using $ls*]?) => do
    let permUsing := (ls.getD #[]).toList.map (·.getId.toString)
    unless permUsing.isEmpty || sv.isSome do
      throwError "sponge_taint_summaries: `using` needs `saving`"
    let (cmds, aliases) := if sv.isSome then
        (spongeSumSavingCmds ns.getId.toString callee.getId.toString permUsing, [])
      else spongeSumCmds ns.getId.toString callee.getId.toString (base.map (·.getId.toString))
    for cmd in cmds do
      match Parser.runParserCategory (← getEnv) `command cmd with
      | .ok stx => elabCommand stx
      | .error e => throwError "sponge_taint_summaries: {e}"
    -- The summaries of `base`, under the names of `ns`.
    liftTermElabM do
      for (a, b) in aliases do
        let b ← realizeGlobalConstNoOverload (mkIdent b.toName)
        let name := (← getCurrNamespace) ++ a.toName
        let type := (← getConstInfo b).type
        addDecl <| .thmDecl { name, levelParams := [], type, value := mkConst b }

/-- `taint_decide_sum` with the summaries of `sponge_taint_summaries ns` and
of ML-KEM's functions. -/
elab "sponge_taint_decide " ns:ident : tactic => do
  let ns := ns.getId.toString
  let mut names := #[]
  for n in (spongeSumNames.map fun n => s!"{ns}.{n}") ++ mlkemSumNames do
    if !(← resolveGlobalName n.toName).isEmpty then names := names.push n
  let tac := s!"taint_decide_sum [{", ".intercalate names.toList}]"
  match Parser.runParserCategory (← getEnv) `tactic tac with
  | .ok stx => Tactic.evalTactic stx
  | .error e => throwError "sponge_taint_decide: {e}"

end VG.Proof.Sha3.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Call`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Variant`. -/
section

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64

/-- The permutation contract and mechanical facts needed by generic sponge callers. -/
structure Permutation where
  callee : Impl.Sha3.AArch64.Callee
  features : List String
  ok : ∀ s, Proof.Sha3.permuteAArch64.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.permuteAArch64.post s s'
  noFrames : callee.code.noFrames = true
  /-- An absorb override must prove the same functional and SIMD ABI contract
  as the general loop; it need not obey that loop's syntactic register shape. -/
  absorbOverrideOk : ∀ code, callee.absorbOverride = some code →
    ∀ s, Proof.Sha3.absorbAArch64.pre s →
      ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧
        Proof.Sha3.absorbAArch64.post s s'
  absorbOverrideDepth : ∀ code, callee.absorbOverride = some code → code.aarch64Depth = 1
  absorbTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.absorbWith callee) h).isSome = true
  padTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x4])
    (Impl.Sha3.AArch64.Stream.padWith callee) h).isSome = true
  squeezeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.squeezeWith callee) h).isSome = true

  sampleFullTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2])
    (Impl.MlKem.AArch64.sampleSqueezeWith callee) h).isSome = true
  sampleFastTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2])
    (Impl.MlKem.AArch64.sampleSqueezeNWith callee 504 (Impl.MlKem.AArch64.sampleRegs 168)) h).isSome = true

  mldsaNttTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 168 1008) h).isSome = true
  mldsaBoundedTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 544) h).isSome = true
  mldsaBallTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 272) h).isSome = true
  mldsaMaskTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.expandMaskTailWith callee) h).isSome = true

  mlkemKgATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem.AArch64.kgAWith callee) h).isSome = true
  mlkemKgCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.kgCWith callee) h).isSome = true

  mlkemEnATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.MlKem.AArch64.enAWith callee) h).isSome = true

  mlkemEnCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.enCWith callee) h).isSome = true

  mlkemDeATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem.AArch64.deAWith callee) h).isSome = true

  mlkemDeCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.deCWith callee) h).isSome = true

  mlkem1024KgATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem1024.AArch64.kgAWith callee) h).isSome = true

  mlkem1024KgCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.kgCWith callee) h).isSome = true

  mlkem1024EnATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.MlKem1024.AArch64.enAWith callee) h).isSome = true

  mlkem1024EnCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.enCWith callee) h).isSome = true

  mlkem1024DeATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem1024.AArch64.deAWith callee) h).isSome = true

  mlkem1024DeCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.deCWith callee) h).isSome = true

  mldsaSeedsTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With callee [⟨.x25, 0, 32⟩, ⟨.x28, 896, 2⟩] [⟨.x28, 1024, 128⟩]) h).isSome = true
  mldsaTrHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.trHashWith callee p) h).isSome = true
  mldsaVerifyHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With callee [⟨.x26, 0, 64⟩,
      ⟨.x28, (Impl.MlDsa.AArch64.Verify.bP p).2, p.k * Impl.MlDsa.AArch64.Verify.w1Len p⟩]
      [⟨.x28, 1024, p.ctildeLen⟩]) h).isSome = true

  mldsaSignDecodeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith callee [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, 960, 64⟩) h).isSome = true
  mldsaSignCommitTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith callee [⟨.x26, 0, 64⟩,
      ⟨.x28, 2048, p.k * Impl.MlDsa.AArch64.Sign.w1Len p⟩]
      ⟨.x28, 1040, Impl.MlDsa.AArch64.Sign.cLen p⟩) h).isSome = true

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

theorem Permutation.absorbMain_depth (v : VG.Proof.Sha3.AArch64.Permutation) :
    (Impl.Sha3.AArch64.Stream.absorbMainWith v.callee).aarch64Depth = 0 := by
  simp only [Impl.Sha3.AArch64.Stream.absorbMainWith, Impl.Sha3.AArch64.Stream.absorbBodyWith, Impl.Sha3.AArch64.Stream.permuteAtWith, Code.aarch64Depth,
    VG.Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames, Nat.max_self]

theorem Permutation.absorb_depth (v : VG.Proof.Sha3.AArch64.Permutation) :
    (Impl.Sha3.AArch64.Stream.absorbWith v.callee).aarch64Depth = 1 := by
  cases h : v.callee.absorbOverride with
  | none =>
    simp only [Impl.Sha3.AArch64.Stream.absorbWith, h,
      Impl.Sha3.AArch64.Stream.absorbGenericWith, Code.aarch64Depth, Instr.frameUnits, v.absorbMain_depth]
  | some code =>
    simpa only [Impl.Sha3.AArch64.Stream.absorbWith, h] using v.absorbOverrideDepth code h

theorem Permutation.padMain_depth (v : VG.Proof.Sha3.AArch64.Permutation) :
    (Impl.Sha3.AArch64.Stream.padMainWith v.callee).aarch64Depth = 0 := by
  simp only [Impl.Sha3.AArch64.Stream.padMainWith, Code.aarch64Depth,
    VG.Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames, Nat.max_self]

theorem Permutation.pad_depth (v : VG.Proof.Sha3.AArch64.Permutation) :
    (Impl.Sha3.AArch64.Stream.padWith v.callee).aarch64Depth = 1 := by
  simp only [Impl.Sha3.AArch64.Stream.padWith, Code.aarch64Depth, Instr.frameUnits, v.padMain_depth]

theorem Permutation.squeezeMain_depth (v : VG.Proof.Sha3.AArch64.Permutation) :
    (Impl.Sha3.AArch64.Stream.squeezeMainWith v.callee).aarch64Depth = 0 := by
  simp only [Impl.Sha3.AArch64.Stream.squeezeMainWith, Impl.Sha3.AArch64.Stream.squeezeBodyWith, Impl.Sha3.AArch64.Stream.permuteAtWith, Code.aarch64Depth,
    VG.Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames, Nat.max_self]

theorem Permutation.squeeze_depth (v : VG.Proof.Sha3.AArch64.Permutation) :
    (Impl.Sha3.AArch64.Stream.squeezeWith v.callee).aarch64Depth = 1 := by
  simp only [Impl.Sha3.AArch64.Stream.squeezeWith, Code.aarch64Depth, Instr.frameUnits, v.squeezeMain_depth]

theorem keeps_of_check {c : Prog isa} {rs : List Reg}
    (h : (c.allInstrs fun i => rs.all fun r => dstOf i != some r) = true) :
    ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r := by
  rw [Code.allInstrs_eq] at h
  intro r hr i hi
  have h' := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using h'

sponge_taint_summaries ScalarSums Impl.Sha3.AArch64.Callee.scalar

def Permutation.scalar : VG.Proof.Sha3.AArch64.Permutation where
  callee := .scalar
  features := []
  ok := permute_correct
  noFrames := permute_noFrames
  absorbOverrideOk := by intro code h; cases h
  absorbOverrideDepth := by intro code h; cases h
  absorbTaint := Taint.exists_check_of_sumOk_call ScalarSums.absorb (VG.AArch64.VectorTaint.le_refl _) rfl
  padTaint := Taint.exists_check_of_sumOk_call ScalarSums.pad (VG.AArch64.VectorTaint.le_refl _) rfl
  squeezeTaint := Taint.exists_check_of_sumOk_call ScalarSums.squeeze (VG.AArch64.VectorTaint.le_refl _) rfl
  sampleFullTaint := by sponge_taint_decide ScalarSums
  sampleFastTaint := by sponge_taint_decide ScalarSums
  mldsaNttTaint := by sponge_taint_decide ScalarSums
  mldsaBoundedTaint := by sponge_taint_decide ScalarSums
  mldsaBallTaint := by sponge_taint_decide ScalarSums
  mldsaMaskTaint := by sponge_taint_decide ScalarSums
  mlkemKgATaint := by sponge_taint_decide ScalarSums
  mlkemKgCTaint := by sponge_taint_decide ScalarSums
  mlkemEnATaint := by sponge_taint_decide ScalarSums
  mlkemEnCTaint := by sponge_taint_decide ScalarSums
  mlkemDeATaint := by sponge_taint_decide ScalarSums
  mlkemDeCTaint := by sponge_taint_decide ScalarSums
  mlkem1024KgATaint := by sponge_taint_decide ScalarSums
  mlkem1024KgCTaint := by sponge_taint_decide ScalarSums
  mlkem1024EnATaint := by sponge_taint_decide ScalarSums
  mlkem1024EnCTaint := by sponge_taint_decide ScalarSums
  mlkem1024DeATaint := by sponge_taint_decide ScalarSums
  mlkem1024DeCTaint := by sponge_taint_decide ScalarSums

  mldsaSeedsTaint := by sponge_taint_decide ScalarSums
  mldsaTrHashTaint := by
    intro p hp
    rcases hp with rfl | rfl | rfl <;> exact by sponge_taint_decide ScalarSums
  mldsaVerifyHashTaint := by
    intro p hp
    rcases hp with rfl | rfl | rfl <;> exact by sponge_taint_decide ScalarSums

  mldsaSignDecodeTaint := by sponge_taint_decide ScalarSums
  mldsaSignCommitTaint := by
    intro p hp
    rcases hp with rfl | rfl | rfl <;> exact by sponge_taint_decide ScalarSums

end VG.Proof.Sha3.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Call`. -/
section

section

/-!
# SHA-3 on AArch64: calling the permutation, and saving registers
-/

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64 VG.Impl.Sha3.AArch64
open VG.Spec.Sha3 (stateAt keccakF)

theorem preserved_x0_x1 : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 := by decide

/-- Calling `vg_keccak_f1600` on the state at `x0`, with scratch space at
`x1`: the callee-saved registers other than `x30` are kept. -/
theorem call_ok (v : VG.Proof.Sha3.AArch64.Permutation) {s : State} {st scr : Addr} (h0 : s.gpr .x0 = st) (h1 : s.gpr .x1 = scr)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩)
    (hw : Covers [⟨st, 200⟩, ⟨scr, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) →
      Frame [⟨st, 200⟩, ⟨scr, 512⟩] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa (.call v.callee.name v.callee.code) s Q := by
  have c0 : s.callEntry.gpr .x0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .x1 = scr := (State.callEntry_gpr _ (by decide)).trans h1
  refine WP.callV (k := Proof.Sha3.permuteAArch64) v.ok
    (rd := []) (wr := [⟨st, 200⟩, ⟨scr, 512⟩]) ?_ ?_ hw ?_ v.noFrames
  · simp only [Proof.Sha3.permuteAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, d₁⟩
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hw a n (by simpa using h)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro s' hrd hwr hsp hf hcs _ hv hpost
    simp only [Proof.Sha3.permuteAArch64, State.withRegions_gpr, State.withRegions_mem, c0] at hpost
    exact hQ s' hrd hwr hsp hcs hv hf (by rw [hpost]; rfl)

/-- `permuteAt`: calling `vg_keccak_f1600` on the state at `x19`, with
scratch space at `x20`. -/
theorem permuteAt_ok (v : VG.Proof.Sha3.AArch64.Permutation) {s : State} {st scr : Addr} (h19 : s.gpr .x19 = st) (h20 : s.gpr .x20 = scr)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩)
    (hw : Covers [⟨st, 200⟩, ⟨scr, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) →
      Frame [⟨st, 200⟩, ⟨scr, 512⟩] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa (Impl.Sha3.AArch64.Stream.permuteAtWith v.callee) s Q := by
  unfold Impl.Sha3.AArch64.Stream.permuteAtWith
  refine WP.seq (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_nil ?_)
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine VG.Proof.Sha3.AArch64.call_ok v (st := st) (scr := scr) (by rw [u₂.other _ (by decide), u₁.gpr, h19])
    (by rw [u₂.gpr, u₁.other _ (by decide), h20]) d₁ (by rw [u₂.wr, u₁.wr]; exact hw)
    fun s' rd' wr' sp' cs' vc' f' e' => ?_
  refine hQ s' (by rw [rd', u₂.rd, u₁.rd]) (by rw [wr', u₂.wr, u₁.wr]) (by rw [sp', u₂.sp, u₁.sp])
    (fun r hr h30 => ?_) (fun r hr => by rw [vc' r hr, u₂.vec, u₁.vec]) (m₂ ▸ f') (by rw [e', m₂])
  rw [cs' r hr h30, u₂.other _ (VG.Proof.Sha3.AArch64.preserved_x0_x1 r hr).2, u₁.other _ (VG.Proof.Sha3.AArch64.preserved_x0_x1 r hr).1]

/-! ## Saving the caller's registers -/


/-- The `k`th callee-saved register saved in the scratch space. -/
def sv (k : Nat) : Reg := (VG.Impl.Sha3.AArch64.Stream.saved.getD k (.x0, 0)).1

/-- Where it is saved. -/
abbrev slot (scr : Addr) (k : Nat) : Addr := scr + BitVec.ofNat 64 (512 + 8 * k)

/-- The registers `m` saves at `scr` are those of `g`. -/
def Saved (scr : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ k < 6, m.readW (VG.Proof.Sha3.AArch64.slot scr k) 64 = g (VG.Proof.Sha3.AArch64.sv k)

/-- The saved registers lie in the scratch space, past the permutation's. -/
theorem slot_sub (scr : Addr) {k : Nat} (hk : k < 6) : Region.Sub ⟨VG.Proof.Sha3.AArch64.slot scr k, 8⟩ ⟨scr, 640⟩ :=
  sub_offset (by omega) (by omega)

theorem slot_scr (scr : Addr) {k : Nat} (hk : k < 6) :
    Region.Disjoint ⟨VG.Proof.Sha3.AArch64.slot scr k, 8⟩ ⟨scr, 512⟩ := Offset.disjoint_base scr (by omega) (by omega)

theorem Saved.frame {scr : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : VG.Proof.Sha3.AArch64.Saved scr g m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ k < 6, ∀ r ∈ rs, Region.Disjoint ⟨VG.Proof.Sha3.AArch64.slot scr k, 8⟩ r) : VG.Proof.Sha3.AArch64.Saved scr g m' :=
  fun k hk => by
    rw [hf.readW (Region.contains_self _ _) (hd k hk) (by decide)]
    exact h k hk

/-- Writes to the state and to the permutation's scratch space keep the
saved registers. -/
theorem Saved.permute {st scr : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : VG.Proof.Sha3.AArch64.Saved scr g m)
    (hd : Region.Disjoint ⟨st, 200⟩ ⟨scr, 640⟩) (hf : Frame [⟨st, 200⟩, ⟨scr, 512⟩] m m') :
    VG.Proof.Sha3.AArch64.Saved scr g m' :=
  h.frame hf fun k hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd.symm.sub_left (VG.Proof.Sha3.AArch64.slot_sub scr hk)
    · exact VG.Proof.Sha3.AArch64.slot_scr scr hk

theorem saved_mem : ∀ k < 6, (VG.Proof.Sha3.AArch64.sv k, 512 + 8 * k) ∈ VG.Impl.Sha3.AArch64.Stream.saved := by decide

theorem saved_idx : ∀ p ∈ VG.Impl.Sha3.AArch64.Stream.saved, ∃ k < 6, p = (VG.Proof.Sha3.AArch64.sv k, 512 + 8 * k) := by
  decide

theorem Saved.of_spill {scr : Addr} {g : Reg → BitVec 64} {m : Mem}
    (h : Spill.Saved scr g VG.Impl.Sha3.AArch64.Stream.saved m) : VG.Proof.Sha3.AArch64.Saved scr g m :=
  fun k hk => h (VG.Proof.Sha3.AArch64.sv k, 512 + 8 * k) (VG.Proof.Sha3.AArch64.saved_mem k hk)

theorem Saved.spill {scr : Addr} {g : Reg → BitVec 64} {m : Mem} (h : VG.Proof.Sha3.AArch64.Saved scr g m) :
    Spill.Saved scr g VG.Impl.Sha3.AArch64.Stream.saved m := fun p hp => by
  obtain ⟨k, hk, rfl⟩ := VG.Proof.Sha3.AArch64.saved_idx p hp
  exact h k hk

/-- Saving `x19`–`x24` in the scratch space at `x5`. -/
theorem saves_ok {s₀ : State} (hin : ∀ k < 6, InRegions s₀.wr (VG.Proof.Sha3.AArch64.slot (s₀.gpr .x5) k) 8) :
    WP isa (.block (VG.Impl.Sha3.AArch64.Stream.save .x5)) s₀ fun s =>
      s.gpr = s₀.gpr ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      Frame [⟨s₀.gpr .x5, 640⟩] s₀.mem s.mem ∧ s.v = s₀.v ∧ VG.Proof.Sha3.AArch64.Saved (s₀.gpr .x5) s₀.gpr s.mem := by
  rw [← List.append_nil (VG.Impl.Sha3.AArch64.Stream.save .x5)]
  exact Spill.save_ok (b := .x5) (by decide) (fun p hp => by
      obtain ⟨k, hk, rfl⟩ := VG.Proof.Sha3.AArch64.saved_idx p hp; exact hin k hk)
    (WP.block_nil ⟨rfl, rfl, rfl, rfl, Spill.saveMem_frame_base (by decide) (by decide) _ _ _, rfl,
      .of_spill (Spill.saveMem_saved (by decide) _ _ _)⟩)

/-- The order of the restores: `x20`, the base, last. -/
abbrev restored : List (Reg × Nat) :=
  [(.x19, 512), (.x21, 528), (.x22, 536), (.x23, 544), (.x24, 552), (.x20, 520)]

/-- Restoring `x19`–`x24` from the scratch space at `x20`. -/
theorem restores_ok {s₁ : State} {scr : Addr} (h20 : s₁.gpr .x20 = scr)
    (hin : ∀ k < 6, InRegions (s₁.rd ++ s₁.wr) (VG.Proof.Sha3.AArch64.slot scr k) 8) {g : Reg → BitVec 64}
    (hsv : VG.Proof.Sha3.AArch64.Saved scr g s₁.mem) :
    WP isa (.block VG.Impl.Sha3.AArch64.Stream.restore) s₁ fun s =>
      s.gpr .x0 = s₁.gpr .x0 ∧ s.sp = s₁.sp ∧ s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.v = s₁.v ∧
      (∀ r, (∀ k < 6, r ≠ VG.Proof.Sha3.AArch64.sv k) → s.gpr r = s₁.gpr r) ∧ ∀ k < 6, s.gpr (VG.Proof.Sha3.AArch64.sv k) = g (VG.Proof.Sha3.AArch64.sv k) := by
  have e : VG.Impl.Sha3.AArch64.Stream.restore = Spill.restoreCode .x20 VG.Proof.Sha3.AArch64.restored := by decide
  rw [e]
  refine WP.mono (Spill.restore_wp h20 (by decide) (by decide) (fun p hp => by
      obtain ⟨k, hk, rfl⟩ := VG.Proof.Sha3.AArch64.saved_idx p (by revert p; decide); exact hin k hk)
    (hsv.spill.sub (by decide))) fun s h => ?_
  have h := h.perm (l' := VG.Impl.Sha3.AArch64.Stream.saved) (by decide) (by decide)
  refine ⟨h.other _ (by decide), h.sp, h.mem, h.rd, h.wr, h.v, fun r hr => h.other r fun hm => ?_,
    fun k hk => h.gpr (VG.Proof.Sha3.AArch64.sv k, 512 + 8 * k) (VG.Proof.Sha3.AArch64.saved_mem k hk)⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  obtain ⟨k, hk, rfl⟩ := VG.Proof.Sha3.AArch64.saved_idx p hp
  exact hr k hk rfl

/-! ## The frame saving `x30` -/

/-- Registers that no instruction writes keep their values, as a postcondition. -/
theorem WP.gprs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r)
    (hn : c.noCalls = true ∨ ∀ r ∈ rs, r ∉ linkRegs :=
      by first | exact .inr (by decide) | exact .inl (by decide +kernel)) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => Exec.gpr (hc r hr) he (hn.imp id fun h => h r hr)⟩

/-- The callee-saved registers our code never touches (but for `x30`, which
our calls change and the frame restores). -/
def untouched : List Reg := [.x25, .x26, .x27, .x28]

theorem untouched_ne_sv : ∀ r ∈ VG.Proof.Sha3.AArch64.untouched, ∀ k < 6, r ≠ VG.Proof.Sha3.AArch64.sv k := by decide

/-- A register of `untouched` is not `d`, for any `d` not in it (decided). -/
theorem ne_of_untouched {r : Reg} (h : r ∈ VG.Proof.Sha3.AArch64.untouched) {d : Reg}
    (hd : d ∉ VG.Proof.Sha3.AArch64.untouched := by decide) : r ≠ d :=
  fun e => hd (e ▸ h)

/-- A register of `untouched` is in any list that has them all (decided). -/
theorem mem_of_untouched {r : Reg} (h : r ∈ VG.Proof.Sha3.AArch64.untouched) {l : List Reg}
    (hl : ∀ r ∈ VG.Proof.Sha3.AArch64.untouched, r ∈ l := by decide) : r ∈ l :=
  hl r h

/-- The callee-saved registers but `x30` are saved or untouched. -/
theorem preserved_cases : ∀ r ∈ preserved, r ≠ .x30 → (∃ k < 6, VG.Proof.Sha3.AArch64.sv k = r) ∨ r ∈ VG.Proof.Sha3.AArch64.untouched := by
  decide

/-- A byte of a region disjoint from a frame is unchanged by the push. -/
theorem write_frame_apply {m : Mem} {sp : Addr} {v : BitVec (8 * 8)} {R : Region}
    (hd : Region.Disjoint ⟨sp - 16, 16⟩ R) {x : Addr} (hx : R.Contains x 1) :
    m.write (sp - 16) 8 v x = m x :=
  Mem.write_apply fun h => hd x (by simp only [Region.Contains]; omega) hx

/-- The bytes of a region disjoint from a frame are unchanged by the push. -/
theorem write_frame_bytes {m : Mem} {sp : Addr} {v : BitVec (8 * 8)} {R : Region}
    (hd : Region.Disjoint ⟨sp - 16, 16⟩ R) (hR : R.len < 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m.write (sp - 16) 8 v (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) :=
  VG.Proof.Sha3.AArch64.write_frame_apply hd (by
    simp only [Region.Contains]
    rw [show R.base + BitVec.ofNat 64 i - R.base = BitVec.ofNat 64 i by bv_omega,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega)

/-- The state is unchanged by the push. -/
theorem write_frame_state {m : Mem} {sp : Addr} {v : BitVec (8 * 8)} {st : Addr}
    (hd : Region.Disjoint ⟨sp - 16, 16⟩ ⟨st, 200⟩) :
    stateAt (m.write (sp - 16) 8 v) st = stateAt m st :=
  stateAt_congr fun _ hi => VG.Proof.Sha3.AArch64.write_frame_bytes (R := ⟨st, 200⟩) hd (by simp) hi

theorem bytesAt_congr {mem mem' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
    Spec.Sha3.bytesAt mem' p n = Spec.Sha3.bytesAt mem p n := by
  simp only [Spec.Sha3.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

end VG.Proof.Sha3.AArch64

end

end

end
