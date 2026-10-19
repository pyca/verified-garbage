module

import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
public meta import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
public import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Front
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # FFDH on x86-64: the domain front in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- A public workspace pointer. -/
theorem pins_rdiB {α : Type} {Φ : α → State → Prop} (f : α → Addr)
    (h : ∀ a s, Φ a s → s.gpr .rdi = f a) : Pins Φ [.rdi] :=
  pins_of (fun a _ => f a) fun a s ha r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact h a s ha

private abbrev domPtrs : List Instr :=
  [.mov .rdx (.mem (hdr sDom)), .mov .rcx (.mem (hdr sK)), .mov .rax (.reg .rdx),
    .alu .add .rax (.reg .rcx), .store (hdr sG) .rax, .alu .add .rax (.reg .rcx), .store (hdr sQ) .rax]

private theorem domPtrs_ok (a : DPub) (s : State) (h : DHP a s) :
    WP isa (.block domPtrs) s fun t => t.gpr .rdx = a.dp ∧ t.gpr .rcx = BitVec.ofNat 64 a.k := by
  obtain ⟨hs, hdi, hZ, hD, hK⟩ := h
  exact WP.mono (WP.keep [.rax, .rdx, .rcx]
    (Q := fun t => t.gpr .rdx = a.dp ∧ t.gpr .rcx = BitVec.ofNat 64 a.k)
    (by unfold domPtrs; xrun [State.ea, hdr, hdi, hdrOff,
      hs.ld (d := 8 * sDom) (by change 136 ≤ a.Z; omega), hs.ld (d := 8 * sK) (by change 152 ≤ a.Z; omega),
      hs.st (d := 8 * sG) (by change 224 ≤ a.Z; omega), hs.st (d := 8 * sQ) (by change 232 ≤ a.Z; omega), hD, hK]) rfl)
    fun _ h => h.1

theorem domHead_ct : RelCT isa (Two DHP) (.block domHead) fun _ _ => True := by
  change RelCT isa (Two DHP) (.block (domPtrs ++ invalid)) _
  refine RelCT.block_append (RelCT.seq
    (two_piece [.rdi] (pins_rdiB DPub.B fun _ _ h => h.2.1) (by taint_decide) domPtrs_ok)
    (two_taint [.rdx, .rcx] (pins_of (fun (a : DPub) r => if r = .rdx then a.dp else BitVec.ofNat 64 a.k)
      fun a s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) (by taint_decide)))

theorem setup_ct :
    RelCT isa (Two SetupP) (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup))
      fun _ _ => True := by
  refine RelCT.seq (R := Two SP1)
    (two_piece [.rdi] (pins_rdiB DPub.B fun _ _ ⟨_, _, hdi, _⟩ => hdi) (by taint_decide) sp0_sp1) ?_
  exact two_map DPub.m sp1_m1 (wsMod_ct (by decide) (by decide) (by decide) (by decide)
    (by taint_decide) (by taint_decide) (by taint_decide))

end VG.Proof.Ffdh.X86_64
