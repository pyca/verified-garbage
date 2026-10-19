module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
public import VerifiedGarbage.Impl.Dsa.Layout
public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Impl.Dsa.Layout
meta import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Dsa.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant-time encoding of an arithmetic result -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def StorePre (p : BPub) (s : State) : Prop := ∃ minv,
  SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx minv ∧
  word s.mem p.x.B (8 * result) = p.ptr ∧ word s.mem p.x.B (8 * resultLen) = BitVec.ofNat 64 p.len

def StoreRegs (p : BPub) (s : State) : Prop :=
  s.gpr .x8 = off (off p.x.B p.x.o) (slot p.x.wx aY) ∧
  s.gpr .x1 = p.ptr + BitVec.ofNat 64 p.len ∧ s.gpr .x9 = BitVec.ofNat 64 p.len

theorem store_ct : RelCT isa (Two StorePre) (Arithmetic.store aY result resultLen) (fun _ _ => True) := by
  unfold Arithmetic.store seqs
  refine RelCT.seq (RelCT.block_append (l₁ := ([ldh .x5 Crt.sLink] : List Instr))
    (RelCT.seq (two_piece (Ψ := fun p s => StorePre p s ∧ s.gpr .x5 = p.x.B) [.x0]
      (pins_of (fun p _ => off p.x.B p.x.o) (by
        intro p s ⟨_, hc, _⟩ r hr
        obtain rfl := List.mem_singleton.mp hr
        exact hc.x0)) (by taint_decide) ?_)
      (two_piece (Ψ := StoreRegs) [.x0, .x5]
        (pins_of (fun p r => if r = .x0 then off p.x.B p.x.o else p.x.B) (by
          intro p s ⟨⟨_, hc, _⟩, ha⟩ r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hc.x0
          · exact ha)) (by taint_decide) ?_))) ?_
  · intro p s ⟨minv, hc, hp, hl⟩
    refine WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = p.x.B ∧ t.mem = s.mem)
      ?_ rfl rfl rfl) fun t ⟨⟨ha, hm⟩, hk⟩ =>
      ⟨⟨minv, hc.mem hm hk (by decide), hm ▸ hp, hm ▸ hl⟩, ha⟩
    drun [hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hc.link,
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
    drun [StoreRegs, Crt.ldw, hc.x0, ha, hdr_enc (show result < 32 by decide),
      hdr_enc (show resultLen < 32 by decide), hdr_enc (show sArr aY < 32 by decide),
      hlarge result (by decide), hlarge resultLen (by decide), hp, hl,
      hsmall (sArr aY) (by decide), hc.hdr.harr aY (by decide)]
  exact two_taint [.x8, .x1, .x9]
    (pins_of (fun p r => if r = .x8 then off (off p.x.B p.x.o) (slot p.x.wx aY)
      else if r = .x1 then p.ptr + BitVec.ofNat 64 p.len else BitVec.ofNat 64 p.len) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2)) (by taint_decide)

end VG.Proof.Dsa.AArch64
