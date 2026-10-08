import VerifiedGarbage.Impl.MlDsa.AArch64.Message
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
import VerifiedGarbage.Variants.Keccak.AArch64.Sha3
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
namespace SquareCachedTr
open VG.Impl.MlDsa.AArch64.Message
-- Private experimental entry: old seven verify_message arguments plus x7=tr[64].
-- Required invariant: tr=SHAKE256(pk,64); raw public entry is unchanged.
def code (c : Impl.Sha3.AArch64.Callee) (name : String) (verify : Prog isa) (p : Spec.MlDsa.Params) : Prog isa :=
 top (enter .x6 p (verifySaves.map fun (r,o) => (if o==fRnd then .x7 else r,o)))
  (.seq (muHash c (.slot fRnd))
   (callA name verify [(.x0,.slot fKey),(.x1,.off oMU),(.x2,.slot fSig),(.x3,.slot fScr)]))
end SquareCachedTr

def main : IO Unit := do
 let c := VG.Variants.Keccak.AArch64.Sha3.variant.callee
 for (nm,p,f) in [("44",Spec.MlDsa.mlDsa44,Impl.MlDsa.AArch64.KeyGen.verify44With c),
  ("65",Spec.MlDsa.mlDsa65,Impl.MlDsa.AArch64.KeyGen.verify65With c),
  ("87",Spec.MlDsa.mlDsa87,Impl.MlDsa.AArch64.KeyGen.verify87With c)] do
  let name := "vg_mldsa"++nm++"_verify_sha3"
  let xs := printer.function (SquareCachedTr.code c name f p)
  IO.FS.writeFile ("/tmp/square-cached-tr-verify"++nm++"-sha3.body") (String.join (xs.map (Rust.line printer.call)))
  IO.FS.writeFile ("/tmp/square-cached-tr-verify"++nm++"-sha3.bindings")
   ("        vg_keccak_absorb_scratch_sha3 = sym super::sha3::vg_keccak_absorb_scratch_sha3,\n"++
    "        vg_keccak_pad_scratch_sha3 = sym super::sha3::vg_keccak_pad_scratch_sha3,\n"++
    "        vg_keccak_squeeze_scratch_sha3 = sym super::sha3::vg_keccak_squeeze_scratch_sha3,\n"++
    "        "++name++" = sym super::mldsa"++nm++"::"++name++",\n")
  IO.println s!"cached-tr {nm}: {xs.length}"
