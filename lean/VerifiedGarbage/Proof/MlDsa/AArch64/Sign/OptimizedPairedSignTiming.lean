module

import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedRestCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedRestCorrect
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopTiming
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedRest
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Correct
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsForget
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsForget
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedInitializationTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedInitializationTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSignTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSignTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedExpansion
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTrace
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedExpansion
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTrace
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedHints
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.WriteBytes
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
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Main
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Mask4
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCall
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCopy
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretMath
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecrets
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestRow
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp4
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
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
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemoryValues
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVerified
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
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableConstants
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeccakMix
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
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckSource
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLoad
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPassOutput
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedShape
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableDecode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductRepresentation
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVerified
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
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZMemory
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
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintEnd
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4CT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Verified
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
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwLanes
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRounds
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Load
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Resident
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentBulk
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentControl
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentMath
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentSelect
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Restore
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Rounds
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Save
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Spec.MlDsa.ResponseLow
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedHints
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Layers
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Ntt
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.NttInv
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedLayer
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedSpec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedStep
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Scale
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Step
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Ntt
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Inline
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Round
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Blocks
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Call4
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallSample
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Main
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Mask4
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCall
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCopy
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretMath
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecrets
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestRow
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp4
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFirst
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFrame
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSelected
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallTry
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskMemory
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourOuterTaint
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParse
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSpec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezePast
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourStore
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotBank
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemoryValues
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveTraversal
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCall
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCoefficients
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackDigits
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackEncode
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Indexed
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableConstants
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeccakMix
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourContracts
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWritten
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Layout
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemorySchedule
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryTraversal
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckSource
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstRoots
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLoad
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPassOutput
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedShape
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableDecode
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZCallTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductRepresentation
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorbWord
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskCall
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentParse
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAccept
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdaptive
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdvance
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBodyTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEnvTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEpi
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourLoopTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejGuard
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPhase
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPro
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRowStep
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarStep
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSelected
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueeze
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueezeSetup
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStart
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTail
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailReadyTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoopTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRestoreG
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentStream
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintMemory
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMath
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMemory
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowWord
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZ
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZMemory
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.SliceFrame
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.StaticCore
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Table
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableDecode
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TailBank
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalChecked
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintPack
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintUnpack
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.SimpleBitPack
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Unpack
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Bits
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Round.MakeHint
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Round.NormLt
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Round.UseHint
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Depth
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.ExpandMask
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbArgs
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Advance
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTTop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Depth
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Epi
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadMem
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pro
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.ProArgs
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.RestoreG
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.RestoreV
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SaveG
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqAdvance
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqFrame
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqPair
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Squeeze
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Tail
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Verified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Zero
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBoundedCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintEnd
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4CT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsFrame
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Verified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Cmp
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Final
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Inst
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp4
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
meta import VerifiedGarbage.Proof.MlDsa.Pack.Arith
meta import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
meta import VerifiedGarbage.Proof.MlDsa.Pack.Stream
meta import VerifiedGarbage.Proof.MlDsa.Sample.LeNat
meta import VerifiedGarbage.Proof.MlDsa.Sample.LeWord
meta import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Sign.Mem
meta import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Verify.Final
meta import VerifiedGarbage.Proof.MlDsa.Verify.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.AArch64.Shared
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwLanes
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRounds
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Load
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Resident
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentBulk
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentControl
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentMath
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentSelect
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Restore
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Rounds
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Save
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Store
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Spec.MlDsa.ResponseLow
meta import VerifiedGarbage.TCB.Axioms

/-! ## From `OptimizedPairedRestTiming.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

/-- Initialization, bounded rejection, and accepted-output packing retain the
same observable leakage as the signing contract. -/
theorem pairedRest_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
    (hp : Ok3 p) {checks : Prog isa}
    (hinit : 16*(positiveDecodeWith keccak.callee P p).aarch64Depth≤D)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p).aarch64Depth≤D)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤D)
    (hchecks : ∀σ s t,PositiveIB p D σ t s → PairedRoots D s → (s.gpr .x0).setWidth 32=1 →
      WP isa checks s fun u=>(PositiveEP p D σ t u ∨ PositiveEF p D σ t u) ∧ PairedRoots D u)
    (hct : PairedChecksCT p D checks) :
    RelCT isa (PairedRS p D (LeakEq p 0) fun σ s=>IM p D σ s ∧ StaticRoots D s)
      (Impl.MlDsa.AArch64.Sign.Optimized.restWith keccak.callee P p checks)
      (RootRS p D (LeakEq p 0) (FS p D)) := by
  refine liftPairedForgetR (fun _ _ _ h rp=>pairedRest_ok hP hp hinit hcommit hball hchecks h.1 h.2 rp) ?_
  unfold Impl.MlDsa.AArch64.Sign.Optimized.restWith
  have hi := RelCT.mono (paired_trace_frame hinit hP.s64 (positiveInitialization_tr (E:=LeakEq p 0) hP hp))
    (fun _ _ h=>h) (fun _ _ h=>PairedRS.of_root h.1 h.2.1 h.2.2.1 h.2.2.2)
  refine RelCT.seq hi (RelCT.seq (pairedSignLoop_tr hP hp hct hcommit hball) ?_)
  unfold ifOk
  refine ifOkElse_tr (fun x y h=>by rw [h.2.1])
    (RelCT.mono (optimizedOutput_tr hP hp (lo := -(q:Int)+1) (hi := (q:Int)-1) (by omega) (by omega)
      (E := fun _ _=>True)) ?_ (fun _ _ h=>h))
    (RelCT.mono nil_tr (fun _ _ h=>h) (fun _ _ _=>trivial))
  rintro x y ⟨⟨⟨⟨σ,τ,ps,pt,pub,_,hx,hy⟩,_⟩,eq,hj⟩,hne⟩
  have ex := x24_one hx.r01 hne
  have ey : y.gpr .x24=1 := eq ▸ ex
  obtain ⟨_,f,fx,fy⟩ := hj ex
  exact ⟨⟨σ,τ,ps,pt,pub,trivial,hx.conversion ex,hy.conversion ey⟩,f,fx,fy⟩

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedPairedSignTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : Proof.Sha3.AArch64.Permutation}

def WithPaired (S : Nat) (R : State → State → Prop) (x y : State) : Prop :=
  R x y ∧ PairedRoots S x ∧ PairedRoots S y ∧
    x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR"

theorem withPaired_tr {S : Nat} {R Q : State → State → Prop} {code : Prog isa}
    (hd : 16*code.aarch64Depth≤S) (hS : S<2^64) (ht : RelCT isa R code Q) :
    RelCT isa (WithPaired S R) code (WithPaired S Q) := by
  intro x y tx ty x' y' h ex ey
  have res := ht _ _ _ _ _ _ h.1 ex ey
  exact ⟨res.1,res.2,h.2.1.exec ex hd hS,h.2.2.1.exec ey hd hS,by
    simpa only [VG.AArch64.Exec.syms ex,VG.AArch64.Exec.syms ey] using h.2.2.2⟩

theorem pairedSign_ct {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hp : Ok3 p)
    {checks : Prog isa}
    (hinit : 16*(positiveDecodeWith keccak.callee P p).aarch64Depth≤D)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p).aarch64Depth≤D)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤D)
    (hchecks : ∀σ s t,PositiveIB p D σ t s → PairedRoots D s → (s.gpr .x0).setWidth 32=1 →
      WP isa checks s fun u=>(PositiveEP p D σ t u ∨ PositiveEF p D σ t u) ∧ PairedRoots D u)
    (hct : PairedChecksCT p D checks) :
    ConstantTime isa (fun s=>(signK p D).pre s ∧ StaticRoots D s ∧ PairedRoots D s)
      (fun x y=>(signK p D).pub x y ∧ RootSymbolsEq x y ∧
        x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR")
      (Impl.MlDsa.AArch64.Sign.Optimized.signWith keccak.callee P p checks) := by
  have trace : RelCT isa (WithPaired D (PositiveEntry p D))
      (Impl.MlDsa.AArch64.Sign.Optimized.signWith keccak.callee P p checks) fun _ _=>True := by
    unfold Impl.MlDsa.AArch64.Sign.Optimized.signWith
    refine RelCT.seq (withPaired_tr (Nat.zero_le _) hP.s64 (positivePro_tr hp))
      (RelCT.seq (withPaired_tr (expandA_depth hP p) hP.s64 (positiveExpand_tr hP hp)) ?_)
    refine RelCT.seq (R:=LRel D (sgR p) (sgW p)) ?_
      (lrel_tr (fun _ _ h=>h) (by taint_decide))
    unfold ifOk
    refine ifOkElse_tr (P:=WithPaired D (PositiveRA p D)) (fun _ _ h=>by rw [h.1.1.2])
      (RelCT.mono (pairedRest_tr hP hp hinit hcommit hball hchecks hct) ?_
        (fun _ _ h=>h.1.lrel (fun _ _ h=>h.st)))
      (RelCT.mono nil_tr (fun _ _ h=>h) (fun _ _ h=>h.1.1.1.lrel (fun _ _ h=>h.st)))
    rintro x y ⟨⟨⟨⟨⟨σ,τ,ps,pt,pub,hx,hy⟩,eq⟩,rx,ry,re⟩,px,py,pe⟩,hne⟩
    have ex := x24_one hx.r01 hne
    have ey : y.gpr .x24=1 := eq ▸ ex
    obtain ⟨ox,fx⟩ := hx.ok ex
    obtain ⟨oy,fy⟩ := hy.ok ey
    exact ⟨⟨⟨σ,τ,ps,pt,pub,pub_leq pub (expandA_max ox) (expandA_max oy),
      ⟨⟨⟨hx.st,ox,fx⟩,rx⟩,px⟩,⟨⟨⟨hy.st,oy,fy⟩,ry⟩,py⟩⟩,re⟩,pe⟩
  intro x y tx ty x' y' hx hy pub ex ey
  exact (trace _ _ _ _ _ _ ⟨⟨hx.1,hy.1,pub.1,hx.2.1,hy.2.1,pub.2.1⟩,
    hx.2.2,hy.2.2,pub.2.2⟩ ex ey).1

end VG.Proof.MlDsa.AArch64.Sign

end
