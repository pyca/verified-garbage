module

public import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-OFB artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.AArch64

/-- How the functions compute Camellia, and the mode. -/
def note : String :=
  "Baseline AArch64: a single-block scalar Feistel core with the S-box resident in NEON registers. \
  Table loads use fixed public addresses; secret indices select bytes only within registers. \
  The raw expanded keys and constant table are prepared once per call, by a call of \
  `vg_camellia_prepare_encrypt_keys`, and each block is a call of `vg_camellia_encrypt_prepared`. \
  Generic OFB retains the IV pointer in x19, which neither function writes."

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact AArch64.target {
    notes := [note]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.ofb
    stack := 3344
    verified := Proof.Camellia.AArch64.ofb_framed }]

end VG.Artifacts.CamelliaOfb.AArch64
