module

public import VerifiedGarbage.Proof.EcKey.X86_64.Main
meta import VerifiedGarbage.Proof.EcKey.X86_64.Main
public import VerifiedGarbage.Proof.EcKey.X86_64.Secp256k1.Contract
meta import VerifiedGarbage.Proof.EcKey.X86_64.Secp256k1.Contract
public import VerifiedGarbage.Proof.EcKey.X86_64.Secp256k1.Lit
meta import VerifiedGarbage.Proof.EcKey.X86_64.Secp256k1.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.CodeErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CodeErase
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Mont.X86_64.Blocks
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Mont.X86_64.Friendly
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Mont.X86_64.Round
import VerifiedGarbage.Proof.Mont.X86_64.Sparse
import VerifiedGarbage.Proof.Mont.X86_64.SparseX
import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.Secp256k1.Point
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.Weierstrass.X86_64.Words
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.EcKey.PublicKey
meta import VerifiedGarbage.Proof.Ecdsa.Sign
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Bswap
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Mont.Words128
meta import VerifiedGarbage.Proof.Mont.X86_64.Blocks
meta import VerifiedGarbage.Proof.Mont.X86_64.CsubS
meta import VerifiedGarbage.Proof.Mont.X86_64.Friendly
meta import VerifiedGarbage.Proof.Mont.X86_64.Ops
meta import VerifiedGarbage.Proof.Mont.X86_64.Round
meta import VerifiedGarbage.Proof.Mont.X86_64.Sparse
meta import VerifiedGarbage.Proof.Mont.X86_64.SparseX
meta import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Proof.Mont.X86_64.WideOps
meta import VerifiedGarbage.Proof.Secp256k1.Point
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.Words
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd

/-!
# secp256k1 public keys on x86-64: `Verified`

secp256k1 is a curve the proof supports (`secp256k1_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.Secp256k1.law`), so `publicKey_ok`
gives the contract's postcondition; the callee-saved registers are restored,
`rsp` is never written, and every store is to `out` or `scratch`, which the
return address is apart from (`abiPreserved`). Constant time by taint
tracking: the only branches are on loop counters, and every address is an
argument plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86_64.Secp256k1

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.EcKey.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.Secp256k1

theorem pre_of {s : State} (h : pkX86_64.pre s) : PkPre secp256k1 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h8, h9, by simp [TblsHeld, Cfg.combConsts, secp256k1, Abi.constsHeld, Abi.constRegions]⟩

theorem post_of {s s' : State} (h : PkPost secp256k1 s s') : pkX86_64.post s s' := by
  unfold PkPost at h
  show match pk s.mem (s.gpr .rsi) with
    | some (.affine x y) => (s'.gpr .rax).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 65 = Spec.EcKey.encodePoint (.affine x y)
    | _ => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 65 = List.replicate 65 0
  revert h
  generalize hq : pk s.mem (s.gpr .rsi) = q
  rw [show Spec.EcKey.publicKey secp256k1.C (dk secp256k1 s) = pk s.mem (s.gpr .rsi) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

/-- `publicKeySecp256k1` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def publicKeySecp256k1Erased : Prog isa := Code.erase publicKeySecp256k1

materialize_shared publicKeySecp256k1Erased

theorem pk_inlineOk : publicKeySecp256k1.InlineOk = true := by
  rw [← Code.InlineOk_erase]
  show publicKeySecp256k1Erased.InlineOk = true
  lit_decide

theorem pk_x86 (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.X86_64.InvSounds) (s : State) (hs : pkX86_64.pre s) :
    ∃ t s', Exec isa publicKeySecp256k1.inline s t s' ∧ abiPreserved s s' ∧ pkX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := publicKey_ok (secp256k1_ok hI) hL secp256k1_tbls (pre_of hs) secp256k1_mulBase
  have hsp := Code.clobbers_rsp_of_inlineOk pk_inlineOk
  have F := (Exec.regions he (Code.noCalls_inline pk_inlineOk)).2.2
  obtain ⟨-, hwr, -, -, -, hro, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by
    rw [Code.allInstrs_inline, ← Code.allInstrs_mapBlocks (f := Instr.erase) fun i => by rw [loadsMxcsr_erase]]
    show publicKeySecp256k1Erased.allInstrs _ = true
    lit_decide) he
    ⟨fun r hr => ?_, ?_⟩, post_of hpost⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact Exec.gpr hsp he
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
  · rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hro
      · exact hrs) (by decide)


theorem pk_ct : ConstantTime isa pkX86_64.pre pkX86_64.pub publicKeySecp256k1 := by
  refine VG.Taint.constantTime_mapBlocks (c' := publicKeySecp256k1Erased) taintS_eraseInv
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) rfl ?_ rfl (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h0

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 : pkX86_64.Implies (Spec.EcKey.Secp256k1.inst.publicKeyContract X86_64.abi 8) :=
  implies.stack8_abi (by
    sig_implies_sat [Spec.EcKey.Secp256k1.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.Secp256k1.curve, Spec.EcKey.scratchWords, X86_64.abi,
      X86_64.argRegs, satState] [satState] using satState)

/-- The output is apart from the calls' return address. -/
theorem pk_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.EcKey.Secp256k1.inst.publicKeyContract X86_64.abi 8).pre s)
    (hp : pkX86_64.post s b) : pkX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -⟩ := implies8.pre s hs
  have hb := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := 65)
    (by rw [hwr]; simp) (by decide)
  simpa only [pkX86_64, State.patch_gpr, EcKey.bytesAt_patch hb] using hp

theorem pk_verified (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target publicKeySecp256k1 (Spec.EcKey.Secp256k1.inst.publicKeyContract X86_64.abi 8) :=
  Verified.of_inline_ct pk_inlineOk (pk_x86 hL hI) pk_ct implies8
    (fun _ h => Sig.clear_of_pre h) pk_patch

end VG.Proof.EcKey.X86_64.Secp256k1
