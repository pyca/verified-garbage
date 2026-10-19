module
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashDecaps
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
meta import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashDecaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
import VerifiedGarbage.Proof.Framework.AArch64.DepthFill
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Input
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Out
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Prepare
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Stores
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16W
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
import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
import VerifiedGarbage.Proof.MlKem.AArch64.DecapsCmp
import VerifiedGarbage.Proof.MlKem.AArch64.Decode12
import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Core
import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Loop
import VerifiedGarbage.Proof.MlKem.AArch64.Dot.LoopInput
import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Pointer
import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Reduce
import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Setup
import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
import VerifiedGarbage.Proof.MlKem.AArch64.Encode12
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.AbsorbLoop
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.AbsorbStep
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.CompiledShapes
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Correct
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsTiming
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Finish
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Init
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenPrefix
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenTiming
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.PadState
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Permute
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Schedules
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Squeeze
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.SqueezePiece
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.SqueezeTransport
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.SqueezeWords
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Transport
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Word
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.WordSemantic
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.All
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.AllWith
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cbd16Call
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitCall
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitCore
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.LayoutPair
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Offsets
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.OutCall
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Output
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutAll
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutPair
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutTables
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyOut
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyPair
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyPairTail
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Tail
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Word
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Words
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Zero
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Fwd
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Gs
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Inv
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.At
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Fwd
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Inv
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Words
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Call
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Inv
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.InvPass1
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.InvPass2
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Pass2
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptM
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptReadonlyTail
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptReadonlyU
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptSeed
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptStart
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Depth
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DotSpec
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemDot
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrix
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixPost
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemReadonlyTransform
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemReady
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemTransformFrames
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemUContext
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemURow
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemVDecode
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenFinish
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrix
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixLast
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixPair
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixPost
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenNoise
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Lists
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Taints
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTablesExec
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraPair
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraPairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraStep
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraStepTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FastFinish
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FinishTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitCore
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastPrepare
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastStartTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Pair
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reinit
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Result
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Single
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Store
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Trace
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Zero
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ZeroBoth
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ZeroBothTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Accept
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8BatchCT
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8BodyCT
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8CT
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Decode
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Invariant
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Keep
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Loop
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8LoopCT
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Public
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8ScalarCT
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Steps
import VerifiedGarbage.Proof.Rc4.AArch64.Group
import VerifiedGarbage.Proof.Rc4.AArch64.Rotate
import VerifiedGarbage.Proof.Rc4.AArch64.Rows
import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Rc4.Table
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
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
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Rounds
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
meta import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
meta import VerifiedGarbage.Proof.Framework.AArch64.DepthFill
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Input
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Out
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Prepare
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Stores
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16W
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
meta import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Core
meta import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Loop
meta import VerifiedGarbage.Proof.MlKem.AArch64.Dot.LoopInput
meta import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Pointer
meta import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Reduce
meta import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Setup
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encode12
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.AbsorbLoop
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.AbsorbStep
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.CompiledShapes
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Correct
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Finish
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Init
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenPrefix
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.PadState
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Permute
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Schedules
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Squeeze
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.SqueezePiece
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.SqueezeTransport
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.SqueezeWords
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Transport
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Word
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.WordSemantic
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.All
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.AllWith
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cbd16Call
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitCall
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitCore
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.LayoutPair
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Offsets
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.OutCall
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Output
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutAll
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutPair
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutTables
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyOut
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyPair
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyPairTail
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Tail
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Word
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Words
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Zero
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Fwd
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Gs
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Inv
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.At
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Fwd
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Inv
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Words
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Call
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Inv
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.InvPass1
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.InvPass2
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Pass2
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Depth
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DotSpec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemDot
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrix
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixPost
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemNoise
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemReady
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemURow
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenFinish
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrix
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixLast
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixPair
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixPost
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenNoise
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Taints
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTablesExec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraPair
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraPairTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraStep
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraStepTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FastFinish
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FinishTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitCore
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastPrepare
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastStartTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Pair
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reinit
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Result
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Single
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Store
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Trace
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Zero
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ZeroBoth
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ZeroBothTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Accept
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8BatchCT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8BodyCT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8CT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Decode
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Invariant
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Keep
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Loop
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8LoopCT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Memory
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Public
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8ScalarCT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Steps
meta import VerifiedGarbage.Proof.Rc4.AArch64.Group
meta import VerifiedGarbage.Proof.Rc4.AArch64.Rotate
meta import VerifiedGarbage.Proof.Rc4.AArch64.Rows
meta import VerifiedGarbage.Proof.Rc4.Stream
meta import VerifiedGarbage.Proof.Rc4.Table
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
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
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Rounds
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.TCB.Axioms

/-! # The checks of the hashing decapsulation, for any permutation (as `KeyGenChecks`) -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64.Optimized

theorem deStart768_depth (v : Proof.Sha3.AArch64.Permutation) :
    (FixedHashDecaps.deStartUsing (fixedHash v.callee) lay768).aarch64Depth≤1 :=
  Code.aarch64Depth_le_of_fillHoles (n := v.callee.name) (e := FixedHashDecaps.deStartUsing (fixedHash hole) lay768)
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel)
theorem deStart768_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃h,((VectorSymbols.analysis restSymbols).check
      (VectorTaint.ofRegs [.x0,.x1,.x2,.x3]) (FixedHashDecaps.deStartUsing (fixedHash c) lay768) h).isSome=true := by
  taint_decide_generic c := hole using hS
theorem deStart1024_depth (v : Proof.Sha3.AArch64.Permutation) :
    (FixedHashDecaps.deStartUsing (fixedHash v.callee) Impl.MlKem1024.AArch64.lay1024).aarch64Depth≤1 :=
  Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
    (e := FixedHashDecaps.deStartUsing (fixedHash hole) Impl.MlKem1024.AArch64.lay1024)
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel)
theorem deStart1024_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
      (FixedHashDecaps.deStartUsing (fixedHash c) Impl.MlKem1024.AArch64.lay1024) h).isSome=true := by
  taint_decide_generic c := hole using hS
end VG.Proof.MlKem.AArch64.FixedHash
