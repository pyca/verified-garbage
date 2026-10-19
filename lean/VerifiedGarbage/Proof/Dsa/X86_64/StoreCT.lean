module

import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
public import VerifiedGarbage.Impl.Dsa.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Impl.Dsa.Layout
import Mathlib.Tactic.Set
meta import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86_64.Store
meta import VerifiedGarbage.Proof.Dsa.X86_64.Store
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
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
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
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
import VerifiedGarbage.Spec.Dsa.SignVerify
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
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
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Operands
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Spec.Dsa.SignVerify

/-! # Constant-time encoding of an arithmetic result -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def StorePre (p : BPub) (s : State) : Prop := ∃ minv,
  SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx minv ∧
  word s.mem p.x.B (8 * result) = p.ptr ∧ word s.mem p.x.B (8 * resultLen) = BitVec.ofNat 64 p.len

def StoreRegs (p : BPub) (s : State) : Prop :=
  s.gpr .rbx = off (off p.x.B p.x.o) (slot p.x.wx aY) ∧
  s.gpr .rsi = p.ptr ∧ s.gpr .rcx = BitVec.ofNat 64 p.len

theorem store_ct : RelCT isa (Two StorePre) (Arithmetic.store aY result resultLen) (fun _ _ => True) := by
  unfold Arithmetic.store seqs
  refine RelCT.seq (RelCT.block_append (l₁ := ([.mov .rax (.mem (hdr Crt.sLink))] : List Instr))
    (RelCT.seq (two_piece (Ψ := fun p s => StorePre p s ∧ s.gpr .rax = p.x.B) [.rdi]
      (pins_of (fun p _ => off p.x.B p.x.o) (by
        intro p s ⟨_, hc, _⟩ r hr
        obtain rfl := List.mem_singleton.mp hr
        exact hc.rdi)) (by taint_decide) ?_)
      (two_piece (Ψ := StoreRegs) [.rdi, .rax]
        (pins_of (fun p r => if r = .rdi then off p.x.B p.x.o else p.x.B) (by
          intro p s ⟨⟨_, hc, _⟩, ha⟩ r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hc.rdi
          · exact ha)) (by taint_decide) ?_))) ?_
  · intro p s ⟨minv, hc, hp, hl⟩
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.x.B ∧ t.mem = s.mem)
      ?_ rfl) fun t ⟨⟨ha, hm⟩, hk⟩ =>
      ⟨⟨minv, hc.mem hm hk (by decide), hm ▸ hp, hm ▸ hl⟩, ha⟩
    xrun [State.ea, hdr, hc.rdi, hdrOff, hc.link,
      hc.good.scr.ld (show 8 * Crt.sLink + 8 ≤ slot p.x.wx 8 by
        have := hdr_lt_slot p.x.wx 8 (show Crt.sLink < 32 by decide); omega)]
  · intro p s ⟨⟨minv, hc, hp, hl⟩, ha⟩
    have hsmall : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off p.x.B p.x.o) (8 * i)) 8 :=
      fun i hi => hc.good.scr.ld (by have := hdr_lt_slot p.x.wx 8 hi; omega)
    have hlarge : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.x.B (8 * i)) 8 :=
      fun i hi => hc.scr.ld (by
        have := hc.lo; have := hc.hi
        have : 256 ≤ slot p.x.w 8 := by unfold slot hdrBytes; omega
        omega)
    xrun [StoreRegs, State.ea, hdr, Crt.ws, hc.rdi, ha, hdrOff,
      hlarge result (by decide), hlarge resultLen (by decide), hp, hl,
      hsmall (sArr aY) (by decide), hc.hdr.harr aY (by decide)]
  exact two_taint [.rbx, .rsi, .rcx]
    (pins_of (fun p r => if r = .rbx then off (off p.x.B p.x.o) (slot p.x.wx aY)
      else if r = .rsi then p.ptr else BitVec.ofNat 64 p.len) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2)) (by taint_decide)

end VG.Proof.Dsa.X86_64
