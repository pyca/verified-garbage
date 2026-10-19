module

public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
import VerifiedGarbage.Proof.MlKem1024.AArch64.Args
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.Args
public import VerifiedGarbage.Spec.MlKem.Contract1024
meta import VerifiedGarbage.Spec.MlKem.Contract1024
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Input
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Out
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Prepare
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Stores
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd2
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Bytes
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecInput
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLoop
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecSpec
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Decode
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncLoop
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncMath
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Encode
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce1Step
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4Step
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem.AArch64.Decode12
import VerifiedGarbage.Proof.MlKem.AArch64.Encode12
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.Mem16Bytes
import VerifiedGarbage.Proof.MlKem1024.AArch64.Stream
import VerifiedGarbage.Proof.Rc4.AArch64.Group
import VerifiedGarbage.Proof.Rc4.AArch64.Rotate
import VerifiedGarbage.Proof.Rc4.AArch64.Rows
import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Rc4.Table
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
meta import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Input
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Out
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Prepare
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Stores
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd2
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Bytes
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecInput
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLoop
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecSpec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Decode
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncLoop
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncMath
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Encode
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce1Step
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4Step
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
meta import VerifiedGarbage.Proof.MlKem.AArch64.Decode12
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encode12
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.Mem16Bytes
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.Stream
meta import VerifiedGarbage.Proof.Rc4.AArch64.Group
meta import VerifiedGarbage.Proof.Rc4.AArch64.Rotate
meta import VerifiedGarbage.Proof.Rc4.AArch64.Rows
meta import VerifiedGarbage.Proof.Rc4.Stream
meta import VerifiedGarbage.Proof.Rc4.Table
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.Arith

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_encaps`

ML-KEM-768's proof (`Proof/MlKem/AArch64/Kem*.lean`, `Encaps.lean`), which is
stated for any well-formed parameter set, for ML-KEM-1024's (`lay1024`),
whose compression functions at the widths 11 and 5 are ML-KEM-1024's own
(`calls1024`); the taint analyses of its code are decided on its literals.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.Encaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem VG.Proof.MlKem.AArch64.Encaps
open VG.Proof.MlKem1024.AArch64 (compressEncode1024_call decodeDecompress1024_call)
open VG.Impl.MlKem.AArch64 (KemLay)

theorem calls1024 : Calls lay1024 :=
  ⟨fun h0 h1 h2 h3 hd => compressEncode1024_call h0 h1 h2 h3 (by rcases hd with rfl | rfl <;> decide),
    fun h0 h1 h2 h3 hd => decodeDecompress1024_call h0 h1 h2 h3 (by rcases hd with rfl | rfl <;> decide)⟩

theorem setupTaint1024 : SetupTaint lay1024 := by
  intro i hi j hj
  change i < 4 at hi
  change j < 4 at hj
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  exact ⟨_, by taint_decide⟩

theorem taints1024 : EnTaints lay1024 keccak :=
  ⟨keccak.mlkem1024EnATaint, keccak.mlkem1024EnCTaint, setupTaint1024⟩

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x4 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 1568⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1568⟩, ⟨0x10000, 49152⟩]

theorem encaps_correctWith (s : State) (hs : (encapsAArch64 lay1024).pre s) :
    ∃ t s', Exec isa (encapsWith keccak.callee) s t s' ∧ abiPreserved s s' ∧
      (encapsAArch64 lay1024).post s s' :=
  encaps_correct KeyGen.wf1024 calls1024 hs

theorem encaps_verifiedWith :
    Verified AArch64.target (encapsWith keccak.callee) (Spec.MlKem1024.encapsContract AArch64.abi 16) :=
  Verified.of_correct (encaps_correctWith (keccak := keccak)) (ct KeyGen.wf1024 taints1024) (by
    mlkem_implies [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, encapsAArch64, lay1024,
      KemLay.params, Spec.MlKem.mlKem1024, KemLay.ekLen, KemLay.ctLen, AArch64.abi, AArch64.argRegs] [sat]
      using sat)

theorem encaps_verified :
    Verified AArch64.target encaps (Spec.MlKem1024.encapsContract AArch64.abi 16) :=
  encaps_verifiedWith (keccak := .scalar)

end VG.Proof.MlKem1024.AArch64.Encaps
