-- UNPROVED prepared-key experiment. New key layouts require reviewed contracts
-- before production. Instructions, control flow and Rust templates use Lean's printer.
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedLoop
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedRest
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecks
import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.OptimizedTop
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst
import VerifiedGarbage.Variants.Keccak.AArch64.Scalar
import VerifiedGarbage.Variants.Keccak.AArch64.Sha3
import VerifiedGarbage.TCB.Rust
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call
namespace KeyCachePrototype
namespace S
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Sign.Optimized

def refs (p : Params) : List (Nat × Nat) :=
  (List.range p.ℓ).map (fun i => ((s1P p i).2,p.skLen+1024*i)) ++
  (List.range p.k).map (fun i => ((s2P p i).2,p.skLen+1024*(p.ℓ+i))) ++
  (List.range p.k).map (fun i => ((t0P p i).2,p.skLen+1024*(p.ℓ+p.k+i)))

def rewritePtrs (rs : List (Nat × Nat)) : Nat → List Instr → List Instr
  | 0,is => is
  | _+1,[] => []
  | fuel+1,is@(i :: tail) =>
    match rs.findSome? (fun (old,new) => [Reg.x1,.x2].findSome? fun r =>
      if (lea r .x28 old).isPrefixOf is then some (r,new,(lea r .x28 old).length) else none) with
    | some (r,new,n) => lea r .x25 new ++ rewritePtrs rs fuel (is.drop n)
    | none => i :: rewritePtrs rs fuel tail

-- Only the caller's argument setup is rewritten; callee implementations are unchanged.
def redirect (rs : List (Nat × Nat)) : Prog isa → Prog isa
 | .block is => .block (rewritePtrs rs is.length is)
 | .seq a b => .seq (redirect rs a) (redirect rs b)
 | .ite c a b => .ite c (redirect rs a) (redirect rs b)
 | .loop a c => .loop (redirect rs a) c
 | .call n a => .call n a
 | .frame i a j => .frame i (redirect rs a) j

def decode (c : Impl.Sha3.AArch64.Callee) (_P : Prims) (p : Params) (ntt : Bool) : Prog isa :=
  let fromCache := (refs p).foldr (fun (dst,src) tail =>
    .seq (callAt "vg_mldsa_ntt_positive_from" Impl.MlDsa.AArch64.Optimized.Ntt.outNtt
      [(.x0,.ptr (.x28,dst)),(.x1,.ptr (.x25,src))]) tail) (.block [])
  .seq (if ntt then .block [] else fromCache)
    (shakeAtWith c [⟨.x25,32,32⟩,⟨.x27,0,32⟩,⟨.x26,0,64⟩] ⟨.x28,oMS,64⟩)

def program (c : Impl.Sha3.AArch64.Callee) (p : Params) (ntt prepared : Bool) : Prog isa :=
  let P := Proof.MlDsa.AArch64.Sign.primsWith c
  let checks := if prepared && ntt then redirect (refs p) (pairedChecks p) else pairedChecks p
  if !prepared then
    if c.pairedSha3 && p.k != 4 then Cached.signWith c P p checks else Optimized.signWith c P p checks
  else
    let cached := c.pairedSha3 && p.k != 4
    let rest := .seq (decode c P p ntt)
      (.seq (if cached then Cached.signLoop P p checks else signLoopWith c P p checks) (ifOk (Optimized.output P p)))
    .seq (.block pro) (.seq (if cached then CachedMatrix.expandA P p else expandA P p)
      (.seq (ifOk rest) (.block epi)))
end S

namespace V
open VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.KeyGen

def copyPoly (src dst : Ptr) : Prog isa :=
  .seq (.block (lea .x0 src.1 src.2 ++ lea .x1 dst.1 dst.2 ++ movV .x2 8))
    (.loop (.block ((List.range 8).flatMap (fun i =>
      ([.ldrq .v0 .x0 (16*i),.strq .v0 .x1 (16*i)] : List Instr)) ++
      ([.addImm .x .x0 .x0 128,.addImm .x .x1 .x1 128,.subImm .x .x2 .x2 1] : List Instr))) (.nonzero .x .x2))

def cachedT1 (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) (r : Nat) (ntt : Bool) : Prog isa :=
  if ntt then .block [] else
    if c.pairedSha3 then
      callAt "vg_mldsa_ntt_positive_from" Impl.MlDsa.AArch64.Optimized.Ntt.outNtt
        [(.x0,.ptr (tmP p)),(.x1,.ptr (.x25,p.pkLen+1024*r))]
    else .seq (copyPoly (.x25,p.pkLen+1024*r) (tmP p)) (nttAt P (sc oSS) (tmP p))

def row (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) (r : Nat) (ntt : Bool) : Prog isa :=
  let rhs := if ntt then (.x25,p.pkLen+1024*r) else tmP p
  if c.pairedSha3 then
    .seq (Optimized.dot p r) (.seq (cachedT1 c P p r ntt)
      (.seq (callAt "vg_mldsa_montgomery_product" Impl.MlDsa.AArch64.Optimized.MontProduct.code
        [(.x0,.ptr (tm2P p)),(.x1,.ptr (cP p)),(.x2,.ptr rhs)])
        (.seq (Optimized.subtract p) (.seq (Optimized.inverse (wP p)) (Optimized.hintPack p r)))))
  else
    .seq (VG.Impl.MlDsa.AArch64.Verify.dot P p r) (.seq (cachedT1 c P p r ntt)
      (.seq (mulAt P (tm2P p) (cP p) rhs) (.seq (subAt P (wP p) (tm2P p))
        (.seq (invNttAt P (sc oSS) (wP p))
          (.seq (useHintAt P (hP p r) (wP p) p.γ₂ (w1P p))
            (simpleBitPackAt P (w1P p) (w1Max p) ((bP p).1,(bP p).2+w1Len p*r) (w1Len p)))))))

def program (c : Impl.Sha3.AArch64.Callee) (p : Params) (ntt prepared : Bool) : Prog isa :=
  let P := VG.Impl.MlDsa.AArch64.KeyGen.primsWith c
  if !prepared then
    if c.pairedSha3 then Optimized.verifyWith c P p else verifyWith c P p
  else
    let compute :=
      .seq (seqR (fun i => if c.pairedSha3 then Optimized.forward (zP p i) else nttAt P (sc oSS) (zP p i)) 0 p.ℓ)
      (.seq (if c.pairedSha3 then Optimized.forward (cP p) else nttAt P (sc oSS) (cP p))
        (.seq (seqR (row c P p · ntt) 0 p.k)
          (.seq (shake256With c [⟨.x26,0,64⟩,⟨.x28,(bP p).2,p.k*w1Len p⟩] [⟨.x28,oCT,p.ctildeLen⟩])
            (cmpAnd (sc oCT) (.x27,0) p.ctildeLen))))
    let body := .seq (hint P p) (ifOk (.seq (seqR (zOne P p) 0 p.ℓ)
      (ifOk (.seq (if c.pairedSha3 then OptimizedSamples.samples P p else samples P p) compute))))
    .seq (.block pro) (.seq body (.block epi))
end V

-- Source glue only: the modeled program and trusted printer generate every instruction.
def function (old : String) (c : Impl.Sha3.AArch64.Callee) (code : Prog isa) : IO String := do
  let P := target.printer
  let fs := if c.pairedSha3 then ["sha3"] else []
  let ls := (fs.flatMap P.enableFeature).map Line.text ++ P.function code ++
    (fs.flatMap P.disableFeature).map Line.text ++ P.funcAlign.map Line.text
  let calls := Rust.dedup (ls.filterMap fun | .call n => some n | _ => none)
  let syms := Rust.dedup (ls.filterMap fun | .sym _ _ n => some n | _ => none)
  let mut bindings := ""
  for n in calls ++ syms do
    let some l := (old.splitOn "\n").find? (fun l => (l.splitOn (n ++ " = sym ")).length == 2)
      | if n == "vg_mldsa_ntt_positive_from" then
          bindings := bindings ++ s!"        {n} = sym super::mldsa::{n},\n"
          continue
        else throw <| IO.userError s!"Unknown binding {n}"
    bindings := bindings ++ l ++ "\n"
  return (old.splitOn "    core::arch::naked_asm!(").head! ++ "    core::arch::naked_asm!(\n" ++
    Rust.template P.call ls ++ bindings ++ "    )\n}\n"

def main (args : List String) : IO Unit := do
  let mode := args.headD "ntt"
  for (tag,p) in [("44",mlDsa44),("65",mlDsa65),("87",mlDsa87)] do
    let mut src ← IO.FS.readFile s!"../src/asm/aarch64/mldsa{tag}.rs"
    for c in [Variants.Keccak.AArch64.Scalar.variant.callee, Variants.Keccak.AArch64.Sha3.variant.callee] do
      for (op,mk) in [("sign",S.program),("verify",V.program)] do
        let name := s!"vg_mldsa{tag}_{op}{c.suffix}"
        let marker := s!"pub(crate) unsafe extern \"C\" fn {name}("
        let [pre,rest] := src.splitOn marker | throw <| IO.userError s!"Missing {name}"
        let old := marker ++ ((rest.splitOn "\n}\n").head!) ++ "\n}\n"
        let unchanged ← function old c (mk c p false false)
        unless old == unchanged do
          IO.FS.writeFile s!"../../mldsa-key-cache-experiments/expected-{name}.rs" unchanged
          IO.FS.writeFile s!"../../mldsa-key-cache-experiments/actual-{name}.rs" old
          throw <| IO.userError s!"Baseline emission mismatch for {name}"
        let new ← function old c (mk c p (mode == "ntt") (mode != "baseline"))
        src := pre ++ new ++ "\n}\n".intercalate ((rest.splitOn "\n}\n").drop 1)
    IO.FS.writeFile s!"../../mldsa-key-cache-experiments/{mode}-mldsa{tag}.rs"
      ("// UNPROVED PROTOTYPE: appended key-polynomial cache required; baseline contracts below do not apply.\n" ++ src)
end KeyCachePrototype

def main := KeyCachePrototype.main
