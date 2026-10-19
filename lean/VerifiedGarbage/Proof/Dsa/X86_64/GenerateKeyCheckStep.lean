module

public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyState
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyCheck
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.Random
public import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Proof.Dsa.RandomSign
public import VerifiedGarbage.Proof.Dsa.RandomSignResult
public import VerifiedGarbage.Proof.Dsa.X86_64.DeriveMainCT
public import VerifiedGarbage.Proof.Dsa.X86_64.DeriveVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyDerive
public import VerifiedGarbage.Proof.Dsa.X86_64.ParametersVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomBorrow
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopy
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyCandidate
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyInit
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyWhole
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomDraw
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCopy
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawRange
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomFunctional
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomInRange
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomNonceEncoding
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepare
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepareFinish
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepareState
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomRange
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSample
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignArgs
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallPre
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInit
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSaved
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPost
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPre
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPost
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPre
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingVerified
public import VerifiedGarbage.Proof.Framework.X86_64.CallSp
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCounter
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedLoop
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedStep
import VerifiedGarbage.Proof.Bignum.X86_64.PdExp
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.X86_64.DeriveMainCT
import VerifiedGarbage.Proof.Dsa.X86_64.DeriveVerified
import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyDerive
import VerifiedGarbage.Proof.Dsa.X86_64.ParametersVerified
import VerifiedGarbage.Proof.Dsa.X86_64.RandomBorrow
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopy
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyCandidate
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyInit
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyWhole
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDraw
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCopy
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawRange
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFunctional
import VerifiedGarbage.Proof.Dsa.X86_64.RandomInRange
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Dsa.X86_64.RandomNonceEncoding
import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepare
import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepareFinish
import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepareState
import VerifiedGarbage.Proof.Dsa.X86_64.RandomRange
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSample
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoop
import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignArgs
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallPre
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInit
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSaved
import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPost
import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPre
import VerifiedGarbage.Proof.Dsa.X86_64.SigningVerified
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPost
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPre
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.X86_64.Frame

/-! # Key generation's domain check, on its frame state -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Whether the domain is one key generation accepts. -/
abbrev keygenChecked (s : State) : Bool :=
  Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params

/-- After a call: the frame's bytes kept, the inputs kept, the callee-saved
registers kept. -/
theorem KeygenState.after_call {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    {wr : List Region} (ht : KeygenState h used t)
    (hwrF : ∀ r ∈ wr, r.Disjoint ⟨randomBase s, Random.frameBytes⟩)
    (hwrP : ∀ r ∈ wr, r.Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩)
    (hwrR : ∀ r ∈ wr, r.Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩)
    (hf : Frame (wr ++ [below (randomBase s) (extra + 8)]) t.mem u.mem)
    (hur : u.rd = t.rd) (huw : u.wr = t.wr) (huc : ∀ r ∈ calleeSaved, u.gpr r = t.gpr r)
    (hmx : u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10) :
    KeygenState h used u ∧
      ∀ d, d + 8 ≤ Random.frameBytes → word u.mem (randomBase s) d = word t.mem (randomBase s) d := by
  have hb := keygen_call_frameBytes h hwrF hf
  have hw (d : Nat) (hd : d + 8 ≤ Random.frameBytes) := random_frame_words hb hd
  have hpl : (keygenInput s).params.length = (s.gpr .r8).toNat := bytesAt_length _ _ _
  have hrl : (keygenInput s).rand.length = (stackArg s 2).toNat := bytesAt_length _ _ _
  refine ⟨⟨ht.scr.congr huw, (huc .rsp (by decide)).trans ht.sp,
    ht.saved.congr (fun d _ hd => hw d (by unfold Random.frameBytes; omega)),
    (hw _ (by decide)).trans ht.usedWord, hur.trans ht.rd, huw.trans ht.wr,
    keygen_call_source ht.params hf hur huw (by rw [hpl]; exact hwrP) (by rw [hpl]; exact h.stackParams)
      (by rw [hpl]; exact Nat.le_of_lt (s.gpr .r8).isLt),
    keygen_call_source ht.rand hf hur huw (by rw [hrl]; exact hwrR) (by rw [hrl]; exact h.stackRand)
      (by rw [hrl]; exact Nat.le_of_lt (stackArg s 2).isLt),
    fun r hc hn => (huc r hc).trans (ht.callee r hc hn), hmx.trans ht.mxcsr⟩, hw⟩

theorem keygen_check_step (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s}
    (ht : KeygenState h 0 t)
    (hdi : t.gpr .rdi = s.gpr .rcx) (hsi : t.gpr .rsi = s.gpr .r8) (hdx : t.gpr .rdx = s.gpr .r9)
    (hcx : t.gpr .rcx = stackArg s 0) (h8 : t.gpr .r8 = stackArg s 3) (h9 : t.gpr .r9 = stackArg s 4) :
    WP isa (.call (keygenCheckName v) (Generate.checkParameters v.sq v.mul)) t fun u =>
      KeygenState h 0 u ∧
      (∀ d, d + 8 ≤ Random.frameBytes → word u.mem (randomBase s) d = word t.mem (randomBase s) d) ∧
      ((u.gpr .rax).setWidth 32).toNat = if keygenChecked s then 1 else 0 := by
  refine WP.mono (keygen_check_call v h ht.sp hdi hsi hdx hcx h8 h9 ht.rd ht.wr)
    fun u ⟨hur, huw, huc, hf, hres, hmx⟩ => ?_
  have hscratch : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨randomBase s, Random.frameBytes⟩ :=
    (h.stackScratch.sub_left (keygen_frame_sub h)).symm
  obtain ⟨hu, hw⟩ := ht.after_call (wr := keygenCheckWr s)
    (fun r hr => by simp only [keygenCheckWr, List.mem_singleton] at hr; subst hr; exact hscratch)
    (fun r hr => by simp only [keygenCheckWr, List.mem_singleton] at hr; subst hr; exact h.paramsScratch.symm)
    (fun r hr => by simp only [keygenCheckWr, List.mem_singleton] at hr; subst hr; exact h.randScratch.symm)
    hf hur huw huc hmx
  refine ⟨hu, hw, ?_⟩
  rw [hres]
  have hp : Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (keygenInput s).params := by
    simpa only [keygenInput, bytesAt_length] using FoldedPublic.src_bytesAt ht.params
  rw [hp]

end VG.Proof.Dsa.X86_64
