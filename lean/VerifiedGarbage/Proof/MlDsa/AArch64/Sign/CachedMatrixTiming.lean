module

import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixCall
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4CT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4CT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixBatch
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixBatch
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixRoots
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixRoots
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSignTiming
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedMatrix
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSignTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.Bits
meta import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlKem.Mem
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
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRestoreG
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentStream
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
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
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedExpansion
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT
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
import VerifiedGarbage.TCB.Axioms
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
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoopTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRestoreG
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentStream
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
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
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedExpansion
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT
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
meta import VerifiedGarbage.TCB.Axioms

/-! ## From `CachedMatrixCallTiming.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG.Spec.Sha3 (bytesAt)

theorem two_ret {S : Nat} (hS : S<2^64) : RetPub (rejNTT2Contract abi S) Two.code := by
  intro x y tx ty x' y' ⟨hx,hy,hpub⟩ ex ey
  have px := pre_two (pre_stack (Nat.zero_le S) hS hx)
  have py := pre_two (pre_stack (Nat.zero_le S) hS hy)
  have pub : Pub 2 x y := by
    sig_pub [rejNTT2Contract,rejNTT2Sig,abi,argRegs] at hpub
    obtain ⟨hsp,hb,h0,h1,h2⟩ := hpub
    exact ⟨h0,h1,h2,hsp,VG.Proof.MlKem.map_toNat_inj hb⟩
  refine ⟨two_ct _ _ _ _ _ _ px py pub ex ey,?_⟩
  obtain ⟨_,u,eu,hu⟩ := two_ok px
  obtain ⟨_,v,ev,hv⟩ := two_ok py
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  have he : (∀k<2,(prefixRow x k 1008).length=256) ↔ ∀k<2,(prefixRow y k 1008).length=256 := by
    constructor
    · intro h k hk; rw [←pub.prefix hk]; exact h k hk
    · intro h k hk; rw [pub.prefix hk]; exact h k hk
  rw [hu.status,hv.status]
  by_cases h : ∀k<2,(prefixRow x k 1008).length=256
  · simp only [ite_eq_left h,ite_eq_left (he.mp h)]
  · simp only [ite_eq_right h,ite_eq_right (fun hy=>h (he.mpr hy))]

theorem rej2At_trRet {S : Nat} (hS : S<2^64)
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : rej2Chk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x seed) 68 = bytesAt y.mem (pa y seed) 68 ∧ SameB x y) :
    RelCT isa Q (callAt "vg_mldsa_rej_ntt_poly2_sha3" Two.code (rej2Args seed a ss))
      fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 := by
  have hc' := hc
  simp only [rej2Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_trRet (callee hS) (two_ret hS) (rej2_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, rej2_pre Lx hc h1, ?_, ?_, (rej2_cov Lx hc).1, (rej2_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact rej2_pre Ly hc h2
  · sig_pub [rejNTT2Contract, rejNTT2Sig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (rej2_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (rej2_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix

end

/-! ## From `CachedMatrixBatchTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Sign

theorem seeds2 {p : Params} {D : Nat} {σ s : State} {e : Nat} (h : AS p D σ e 2 s) :
    bytesAt s.mem (pa s (sc oRS4)) 68=seedE p σ (e+0)++seedE p σ (e+1) := by
  have h0 := aseeds2_eq h (show 0<2 by decide)
  have h1 := aseeds2_eq h (show 1<2 by decide)
  unfold seed4 at h0 h1
  rw [show 68=34+34 from rfl,VG.Proof.MlKem.bytesAt_add]
  simp only [Nat.mul_zero,Nat.mul_one,VG.Proof.MlKem.AArch64.ptr_zero] at h0 h1
  rw [h0,h1]

theorem twoBatch_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {e : Nat} (hc : twoChk p e = true) :
    RelCT isa (RR p D (AS p D · e 2) fun x y => x.gpr .x24 = y.gpr .x24)
      (.seq (callAt "vg_mldsa_rej_ntt_poly2_sha3" Two.code (rej2Args (sc oRS4) (pS (aBase p+e)) (sc (oR4 p)))) (.block and24))
      (RA p D (e+2)) := by
  have hc' := hc
  simp only [twoChk,Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨cr,_⟩,_⟩,_⟩,_⟩ := hc'
  refine stepRR (F := fun _ _ => True) (fun _ _ _ h => WP.mono (twoBatch_ok hP hc h) fun _ ht => ⟨ht,trivial⟩) ?_
    (fun _ _ _ _ _ _ _ h => h)
  have calltr : RelCT isa (RR p D (AS p D · e 2) fun x y => x.gpr .x24 = y.gpr .x24)
      (callAt "vg_mldsa_rej_ntt_poly2_sha3" Two.code (rej2Args (sc oRS4) (pS (aBase p+e)) (sc (oR4 p))))
      (fun x y => LRel D (sgR p) (sgW p) x y ∧ x.gpr .x24 = y.gpr .x24 ∧ (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32) := by
    refine postDepQ (fun x y t1 t2 x' y' h e1 e2 =>
      rej2At_trRet hP.s64 (h.lrel fun _ _ h => h.ia.st).ok cr ?_ x y t1 t2 x' y' h e1 e2)
      (F := fun s t => PPostB D s t [(pS (aBase p+e),2048),(sc (oR4 p),8192)] ∧ t.gpr .x24 = s.gpr .x24)
      ?_ ?_
    · intro x y h
      have L := h.lrel fun _ _ h => h.ia.st
      refine ⟨L.lx,L.ly,?_,L.same⟩
      obtain ⟨⟨σ1,σ2,_,_,pub,h1,h2⟩,_⟩ := h
      rw [seeds2 h1,seeds2 h2]
      simp only [seedE,pub_rho pub]
    · intro x y h
      obtain ⟨⟨σ1,σ2,_,_,_,h1,h2⟩,_⟩ := h
      exact ⟨WP.mono (rej2Call_ok hP.s64 h1.ia.st.lay cr) (fun _ ht => ⟨ht.1,ht.2.1⟩),
        WP.mono (rej2Call_ok hP.s64 h2.ia.st.lay cr) (fun _ ht => ⟨ht.1,ht.2.1⟩)⟩
    · intro x y x' y' h hx hy hr
      have L := h.lrel fun _ _ h => h.ia.st
      refine ⟨⟨L.lx.post hx.1,L.ly.post hy.1,fun r hr => ?_,?_,L.ok⟩,by rw [hx.2,hy.2,h.2],hr⟩
      · rw [hx.1.bs r (bases_kept r hr),hy.1.bs r (bases_kept r hr)]; exact L.regs r hr
      · rw [hx.1.sp,hy.1.sp]; exact L.sp
  refine RelCT.seq calltr (RelCT.postDep (lrel_tr (fun _ _ h => h.1) (by taint_decide))
    (F := fun s t => t.gpr .x24 = BitVec.setWidth 64 ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32))
    (fun x y _ => ⟨WP.mono (and24_ok x) (fun _ h => h.2),WP.mono (and24_ok y) (fun _ h => h.2)⟩)
    fun x y x' y' h hx hy => by rw [hx,hy,h.2.1,h.2.2])


end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix

end

/-! ## From `CachedMatrixTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.Sign

theorem tail_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) :
    RelCT isa (RA mlDsa65 D 28) (Impl.MlDsa.AArch64.Sign.CachedMatrix.tail mlDsa65)
      (RA mlDsa65 D 30) := by
  unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.tail
  rw [show 4*(mlDsa65.k*mlDsa65.ℓ/4)=28 by decide]
  refine RelCT.seq (RelCT.mono (seqR_tr
    (Q:=fun j=>RR mlDsa65 D (AS mlDsa65 D · 28 j) fun x y=>x.gpr .x24=y.gpr .x24) 2 0
    (fun j _ hj=>slot4_tr (by omega)
      (slotChk_ok mlDsa65 (by simp) 28 (by decide) j (by omega)))) ?_ (fun _ _ h=>by simpa using h))
    (twoBatch_tr hP (show twoChk mlDsa65 28=true by decide))
  exact fun x y h=>h.mono (fun _ _ h=>⟨h,fun _ h=>False.elim (Nat.not_lt_zero _ h)⟩) (fun h=>h)

theorem expandA65_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) (hc : aChk mlDsa65 = true) :
    RelCT isa (RR mlDsa65 D (fun σ s => St mlDsa65 D σ s ∧ s.gpr .x24 = 1) fun _ _ => True)
      (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P mlDsa65) (RA mlDsa65 D (mlDsa65.k * mlDsa65.ℓ)) := by
  have hp : mlDsa65 ∈ [mlDsa44,mlDsa65,mlDsa87] := by simp
  simp only [aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩ := hc
  unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA
  rw [ite_eq_left (by decide)]
  refine RelCT.seq (R := RA mlDsa65 D 0) (stepRR (F := fun s s' => s'.gpr .x24 = s.gpr .x24) (J := fun σ s => IA mlDsa65 D σ 0 s)
    (E' := fun x y => x.gpr .x24 = y.gpr .x24)
    (fun σ s _ h => ?_) (lrel_tr (fun x y h => h.lrel fun _ _ h => h.1) (by taint_decide))
    fun x y x' y' h fx fy _ => ?_) ?_
  · refine WP.mono (copyP_ok h.1.lay hcp) fun s1 ⟨hP1, hcs1, hb⟩ => ⟨?_, hcs1.get .x24⟩
    have S1 := h.1.step hP1 hst
    have e15 : s1.gpr .x24 = 1 := by rw [hcs1.get .x24, h.2]
    exact ⟨S1, by rw [hP1.pa (by decide), hb, rhoOf, ← h.1.sk, VG.Proof.MlKem.bytesAt_take _ _ hsk],
      .inr e15, fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      fun h0 => absurd (h0.symm.trans e15) (by decide)⟩
  · obtain ⟨⟨σ₁, σ₂, _, _, _, ⟨_, h₁⟩, ⟨_, h₂⟩⟩, _⟩ := h
    rw [fx, fy, h₁, h₂]
  · have hB : RelCT isa (RA mlDsa65 D 0) (seqR (sample4 P mlDsa65) 0 7) (RA mlDsa65 D 28) := by
      simpa only [Nat.zero_add,Nat.mul_zero] using
        (seqR_tr (Q:=fun g=>RA mlDsa65 D (4*g)) 7 0 (fun g _ hg=>
          sample4_tr hP (batchChk_ok mlDsa65 hp g (by change g<7; omega))
            (fun j hj=>slotChk_ok mlDsa65 hp (4*g) (by change 4*g<30; omega) j hj)))
    exact RelCT.seq hB (tail_tr hP)

theorem expandA_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
    (hp : Ok3 p) (hc : aChk p=true) :
    RelCT isa (RR p D (fun σ s=>St p D σ s ∧ s.gpr .x24=1) fun _ _=>True)
      (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p) (RA p D (p.k*p.ℓ)) := by
  rcases hp with rfl|rfl|rfl
  · exact Sign.expandA_tr hP (.inl rfl) hc
  · exact expandA65_tr hP hc
  · exact Sign.expandA_tr hP (.inr (.inr rfl)) hc

theorem positiveExpand_tr {P : Prims} {p : Params} {D : Nat} (hP : PrimsOk P D) (hp : Ok3 p) :
    RelCT isa (RR p D (fun σ s=>RootedSt p D σ s ∧ s.gpr .x24=1) RootSymbolsEq)
      (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p) (PositiveRA p D) := by
  have ha := aChk_ok hp
  intro x y tx ty x' y' h ex ey
  have old : RR p D (fun σ s=>St p D σ s ∧ s.gpr .x24=1) (fun _ _=>True) x y := h.mono (fun _ _ h=>⟨h.1.1,h.2⟩) (fun _=>trivial)
  obtain ⟨tr,out⟩ := expandA_tr hP hp ha _ _ _ _ _ _ old ex ey
  obtain ⟨⟨σ,τ,_,_,_,hx,hy⟩,re⟩ := h
  obtain ⟨_,u,eu,_,ru⟩ := rooted_expandA_ok hP hp ha hx.1 hx.2
  obtain ⟨_,v,ev,_,rv⟩ := rooted_expandA_ok hP hp ha hy.1 hy.2
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨tr,out,ru,rv,by
    simpa only [RootSymbolsEq,VG.AArch64.Exec.syms ex,VG.AArch64.Exec.syms ey] using re⟩


end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix

end
