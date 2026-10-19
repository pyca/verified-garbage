module
public import Mathlib.Tactic.Conv
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context

meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceSlice
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common
import VerifiedGarbage.Spec.Pbkdf2.Generic
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.RsaOaep.Scan
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
meta import VerifiedGarbage.Proof.Sha256.X86_64.Compress
meta import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common
meta import VerifiedGarbage.Spec.Pbkdf2.Generic

/-! # Phase gates branch only on the public generation status -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64

def PhaseDecided {α : Type} (Φ : α → State → Prop) (status : α → BitVec 64)
    (p : α) (s : State) : Prop := Φ p s ∧ isa.eval .e s = some (status p == 1)

theorem onSuccess_ct {α : Type} {Φ : α → State → Prop}
    (context : α → GenerationContext) (status : α → BitVec 64)
    (view : ∀ p s, Φ p s → ∃ W, GenerationMemory (context p) W s ∧ W 19 = status p)
    (stable : ∀ p s t, Φ p s → t.mem = s.mem → Keep [.rax] s t → Φ p t)
    {next : Prog isa}
    (body : RelCT isa (Two fun p s => Φ p s ∧ status p = 1) next (fun _ _ => True)) :
    RelCT isa (Two Φ) (Impl.Dsa.X86_64.Generation.onSuccess next) (fun _ _ => True) := by
  have check : RelCT isa (Two Φ) (.block Impl.Dsa.X86_64.Generation.successStatus)
      (Two (PhaseDecided Φ status)) := by
    refine two_piece [.rsp] ?_ (by taint_decide) ?_
    · intro p s t hs ht r hr
      obtain rfl := List.mem_singleton.mp hr
      obtain ⟨Ws, hms, _⟩ := view p s hs
      obtain ⟨Wt, hmt, _⟩ := view p t ht
      exact hms.layout.rsp.trans hmt.layout.rsp.symm
    · intro p s hs
      obtain ⟨W, hm, hw⟩ := view p s hs
      obtain ⟨V, R⟩ := hm.rep
      refine WP.mono (successStatus_ok hm.layout R) fun t ⟨hz, he, hk⟩ => ?_
      exact ⟨stable p s t hs he hk, by simp only [eval, hz, hw]⟩
  refine RelCT.seq check (two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_)
  · exact two_map (fun p : α => p) (fun _ _ h => ⟨h.1.1, by
      have he := h.1.2.symm.trans h.2
      exact beq_iff_eq.mp (Option.some.inj he)⟩) body
  · exact two_taint [] (by intro _ _ _ _ _ r hr; simp at hr) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
