module

public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedPrims
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsEntry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedVerified
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Compute
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFields
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
public import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Layers
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Ntt
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.NttInv
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedLayer
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedSpec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedStep
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Scale
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Step
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Ntt
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Inline
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Round
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Blocks
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Call4
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallSample
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Main
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Mask4
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedDepth
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedEntry
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedPrims
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSat
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCall
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCopy
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretMath
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecrets
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestRow
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp4
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallCorrect
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFirst
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFrame
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSelected
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallTry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskMemory
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourOuterTaint
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParse
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSpec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezePast
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourStore
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveInit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveTraversal
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCall
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCoefficients
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackDigits
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackEncode
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Indexed
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseCall
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableConstants
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourBytes
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourContracts
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWritten
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Layout
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemorySchedule
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryTraversal
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorbWord
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskBytes
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskCall
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentParse
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAccept
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdaptive
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdvance
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBodyTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBytes
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEnvTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEpi
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourLoopTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejGuard
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPhase
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPro
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRowStep
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarStep
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSelected
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueeze
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueezeSetup
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStart
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTail
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailReadyTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoopTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRestoreG
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentStream
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.SliceFrame
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.StaticCore
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Table
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableDecode
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TailBank
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalChecked
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintPack
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintUnpack
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.SimpleBitPack
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Bits
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.MakeHint
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.NormLt
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.UseHint
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Depth
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.ExpandMask
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbArgs
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Advance
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTTop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Depth
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Epi
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadMem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pro
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.ProArgs
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.RestoreG
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.RestoreV
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SaveG
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqAdvance
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqFrame
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqPair
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Squeeze
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Tail
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Verified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Zero
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBoundedCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4CT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseOCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Cmp
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Final
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp4
public import VerifiedGarbage.Proof.MlDsa.DecideAt
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlDsa.Sample.LeNat
public import VerifiedGarbage.Proof.MlDsa.Sample.LeWord
public import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
public import VerifiedGarbage.Proof.MlDsa.Sign.Mem
public import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
public import VerifiedGarbage.Proof.MlDsa.Verify.Final
public import VerifiedGarbage.Proof.MlDsa.Verify.Mem
public import VerifiedGarbage.Proof.MlKem.AArch64.Shared
public import VerifiedGarbage.Proof.MlKem.Compress
public import VerifiedGarbage.Proof.MlKem.Encode
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Load
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Resident
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentBulk
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentControl
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentMath
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentSelect
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Restore
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Rounds
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Save
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Store
public import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
public import VerifiedGarbage.Proof.Sha3.Arith
public import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Layers
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.NttInv
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedLayer
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedSpec
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Scale
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Step
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Inline
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Round
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Blocks
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Call4
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallSample
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Main
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Mask4
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedDepth
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedEntry
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedPrims
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSat
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCall
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCopy
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretMath
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecrets
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestRow
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp4
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFirst
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSelected
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallTry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourOuterTaint
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSpec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezePast
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveTraversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCoefficients
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackDigits
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackEncode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Indexed
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableConstants
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourContracts
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWritten
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Layout
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemorySchedule
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryTraversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorbWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentParse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAccept
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdaptive
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdvance
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBodyTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEnvTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEpi
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejGuard
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPhase
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPro
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRowStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSelected
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueeze
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueezeSetup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStart
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTail
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailReadyTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRestoreG
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentStream
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.SliceFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.StaticCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Table
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableDecode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TailBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalChecked
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintUnpack
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Bits
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.UseHint
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Depth
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbArgs
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Advance
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTTop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Depth
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Epi
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pro
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.ProArgs
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.RestoreG
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.RestoreV
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SaveG
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqAdvance
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqPair
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Squeeze
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Tail
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Verified
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Zero
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBoundedCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4CT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Cmp
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Final
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp4
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Sample.LeNat
import VerifiedGarbage.Proof.MlDsa.Sample.LeWord
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.MlDsa.Verify.Final
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Load
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Resident
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentBulk
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentControl
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentMath
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentSelect
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Restore
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Rounds
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Save
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.TCB.Axioms

/-! # ML-DSA (FIPS 204) key generation on AArch64 -/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlDsaKeyGen

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's `x24`–`x28` and `x30` in `scratch`, and uses no stack of its \
    own; the functions it calls use the 16 bytes of stack below the stack pointer.",
   "It samples every polynomial of `A` and of `s1` and `s2` whatever the samplers return, and \
    zeroes the polynomial of a sampler that fails rather than branching on it: its timing does not \
    depend on whether key generation fails."]

def legacyArtifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := notes
    code := Impl.MlDsa.AArch64.KeyGen.keyGen44With v.callee
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.keyGen44_verifiedWith (keccak := v) },
  Spec.MlDsa.keyGen65Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := notes
    code := Impl.MlDsa.AArch64.KeyGen.keyGen65With v.callee
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.keyGen65_verifiedWith (keccak := v) },
  Spec.MlDsa.keyGen87Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := notes
    code := Impl.MlDsa.AArch64.KeyGen.keyGen87With v.callee
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.keyGen87_verifiedWith (keccak := v) }]

/-- SHA3 key generation uses hoisted matrix seeds, grouped secret sampling, and
positive transform arithmetic. The scalar fallback shares its grouped secret
sampling (`Optimized.secretsWith`), with the four-way samplers of its own
permutation. -/
def optimizedArtifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := notes
    consts := Proof.MlDsa.AArch64.Sign.signRootConsts
    code := Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith v.callee Spec.MlDsa.mlDsa44
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.Optimized.keyGen_verified v (.inl rfl) },
  Spec.MlDsa.keyGen65Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := notes
    consts := Proof.MlDsa.AArch64.Sign.signRootConsts
    code := Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith v.callee Spec.MlDsa.mlDsa65
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.Optimized.keyGen_verified v (.inr (.inl rfl)) },
  Spec.MlDsa.keyGen87Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := notes
    consts := Proof.MlDsa.AArch64.Sign.signRootConsts
    code := Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith v.callee Spec.MlDsa.mlDsa87
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.Optimized.keyGen_verified v (.inr (.inr rfl)) }]

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact :=
  if v.callee.pairedSha3 then optimizedArtifacts v else legacyArtifacts v

end VG.Generic.Keccak.AArch64.MlDsaKeyGen
