module

public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.CT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed25519.X86_64.BaseHeld
import VerifiedGarbage.Proof.Sha512.X86_64.Shared
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarVerified
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLit
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Decode
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Ed25519.X86_64.BaseCallee
import VerifiedGarbage.Proof.Ed25519.X86_64.Bits
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.CombNeg
import VerifiedGarbage.Proof.Ed25519.X86_64.CombSelectY
import VerifiedGarbage.Proof.Ed25519.X86_64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.X86_64.DecodePowers
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldLazy
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombSelect
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.ScalarBase
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Keeps
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEncode
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEqual
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowersLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseAdx
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowCT
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowDigits
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry
import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Half
import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Keep
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Hmac.AnyKey
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.MdStream.OneShot
import VerifiedGarbage.Proof.MdStream.Prefix
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyEntry
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Pbkdf2.Scratch
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Copy
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Compress
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Compress
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Compress
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.X25519.X86_64.AddSub
import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.X25519.X86_64.Bits
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Main
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Step
import VerifiedGarbage.Proof.X25519.X86_64.Finish
import VerifiedGarbage.Proof.X25519.X86_64.Freeze
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Block
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Bound
import VerifiedGarbage.Proof.X25519.X86_64.Inv
import VerifiedGarbage.Proof.X25519.X86_64.Invert
import VerifiedGarbage.Proof.X25519.X86_64.Iter
import VerifiedGarbage.Proof.X25519.X86_64.Sqr

/-! The complete verifier satisfies the reviewed message-level contract. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.VerifyMessage

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
variable {win : VG.Prog VG.X86_64.isa}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (scalarReduce verifyEquation callWith)
open VG.Impl.Ed25519.X86_64.VerifyMessage
open VG.Proof.Sha512.X86_64 (Compress)

/-- The memory of the contract's witness: the static at `0x100000`. -/
@[irreducible] def satMem : Mem := constMem 0x100000 Impl.Ed25519.X86_64.baseOddWords

theorem satMem_held : ∀ i < 2048,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = Impl.Ed25519.X86_64.baseOddWords.getD i 0 := by
  unfold satMem
  intro i hi
  exact constMem_held _ _ (by rw [baseOddWords_length]; omega) i (by rw [baseOddWords_length]; exact hi)

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0 | .rcx => 0x3000
    | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 0⟩, ⟨0x3000, 64⟩, ⟨0x100000, 16384⟩]
  wr := [⟨0x4000, 8192⟩]
  syms _ := 0x100000

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

theorem baseOddConsts_eq' :
    Impl.Ed25519.X86_64.baseOddConsts =
      [(Impl.Ed25519.X86_64.baseOddSym, Impl.Ed25519.X86_64.baseOddWords)] := rfl

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State} (h184 : 184 ≤ (s.gpr .rsp).toNat)
    (hrd : s.rd = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 64⟩,
      ⟨s.syms Impl.Ed25519.X86_64.baseOddSym, 16384⟩])
    (hw : s.wr = [⟨s.gpr .r8, 8192⟩])
    (pc : Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .r8, 8192⟩)
    (mc : Region.Disjoint ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩ ⟨s.gpr .r8, 8192⟩)
    (sc : Region.Disjoint ⟨s.gpr .rcx, 64⟩ ⟨s.gpr .r8, 8192⟩)
    (rp : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 32⟩)
    (rm : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩)
    (rs : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 64⟩)
    (rc : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .r8, 8192⟩)
    (kp : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 184, 184⟩ ⟨s.gpr .rdi, 32⟩)
    (km : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 184, 184⟩ ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩)
    (ks : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 184, 184⟩ ⟨s.gpr .rcx, 64⟩)
    (kc : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 184, 184⟩ ⟨s.gpr .r8, 8192⟩)
    (np : (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64) (nm : (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64)
    (ns : (s.gpr .rcx).toNat + 64 ≤ 2 ^ 64) (nc : (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64)
    (held : ∀ i < 2048, s.mem.readW (s.syms Impl.Ed25519.X86_64.baseOddSym + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.Ed25519.X86_64.baseOddWords.getD i 0)
    (fit : (s.syms Impl.Ed25519.X86_64.baseOddSym).toNat + 16384 ≤ 2 ^ 64)
    (td : Region.Disjoint ⟨s.syms Impl.Ed25519.X86_64.baseOddSym, 16384⟩ ⟨s.gpr .r8, 8192⟩)
    (tr : Region.Disjoint ⟨s.syms Impl.Ed25519.X86_64.baseOddSym, 16384⟩ ⟨s.gpr .rsp, 8⟩)
    (tk : Region.Disjoint ⟨s.syms Impl.Ed25519.X86_64.baseOddSym, 16384⟩
      ⟨s.gpr .rsp - BitVec.ofNat 64 184, 184⟩) :
    (Spec.Ed25519.verifyContract (X86_64.abi.withConsts Impl.Ed25519.X86_64.baseOddConsts) 184).pre s := by
  sig_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
    Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, baseOddConsts_eq', Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow, baseOddWords_length]
  exact ⟨h184, by rw [hrd]; rfl, held, fit, by rw [hw]; simp only [List.mem_singleton, forall_eq]; exact td,
    tr, tk, by rw [hrd]; rfl, hw, pc, mc, sc, rp, rm, rs, rc, kp, km, ks, kc, np, nm, ns, nc⟩

theorem sat_spec :
    (Spec.Ed25519.verifyContract (X86_64.abi.withConsts Impl.Ed25519.X86_64.baseOddConsts) 184).pre
      satState :=
  spec_pre (by decide) rfl rfl (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (by decide) (by decide) (by decide) (by decide)
    satMem_held (by decide) (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide))

theorem implies : verifyMessageLocal.Implies
    (Spec.Ed25519.verifyContract (X86_64.abi.withConsts Impl.Ed25519.X86_64.baseOddConsts) 184) where
  pre s h := by
    sig_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, baseOddConsts_eq', Abi.withConsts,
      Abi.constRegions, Abi.constsHeld, stackBelow, baseOddWords_length] at h
    obtain ⟨h184, hd, hheld, -, hdw, -, hstk, ht, hw, pc, mc, sc, rp, rm, rs, rc, kp, km, ks, kc, np, nm, ns,
      nc⟩ := h
    refine ⟨h184, ?_, hw, pc, mc, sc, rp, rm, rs, rc, kp, km, ks, kc, np, nm, ns, nc,
      hdw _ (by rw [hw]; simp), hstk, hheld⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, baseOddConsts_eq', Abi.withConsts]
    change t.gpr .rax = if _ then 1 else 0 at h
    rw [h]
    generalize Spec.Ed25519.verify (Spec.Ed25519.bytesAt s.mem (s.gpr .rdi) 32)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .rcx) 64) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, baseOddConsts_eq', Abi.withConsts] at h
    obtain ⟨sp, sy, bytes, pk, msg, len, sig, scr⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb
      (by simp only [PublicKey.bytesAt_length])
    obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [PublicKey.bytesAt_length, len])
    exact ⟨sp, pk, msg, len, sig, scr, first, middle, last, sy⟩
  sat := ⟨satState, sat_spec⟩

theorem verified (hq : EqCode fld win) (v : Compress) :
    Verified X86_64.target (code fld win fs v.callee v.suffix)
      (Spec.Ed25519.verifyContract (X86_64.abi.withConsts Impl.Ed25519.X86_64.baseOddConsts) 184) :=
  Verified.of_correct (fun _ h => verifyMessage_ok hq v h) (verifyMessage_ct hq v) implies

omit [VG.Proof.Ed25519.X86_64.EdArith fld] in
theorem spSafe (hq : EqCode fld win) (v : Compress) :
    (code fld win fs v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  have hu := Proof.Sha512.X86_64.Shared.update_spSafe v.spSafe
  have hf := Proof.Sha512.X86_64.Shared.finalize_spSafe v.spSafe
  have hr : scalarReduce.all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs (by lit_decide)
  have he := hq.spSafe
  have hi : (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512).all (fun i => !isa.writesSp i) = true := by
    decide +kernel
  simp only [code, body, Impl.Ed25519.X86_64.VerifyMessage.hash, callWith, Code.all, hu, hf, hr, he, hi, Bool.and_true]
  decide

end VG.Proof.Ed25519.X86_64.VerifyMessage
