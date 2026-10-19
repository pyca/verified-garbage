module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Load
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Load
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdStep
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.ModE
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Exp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Load
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
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdStep
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.ModE

/-! # Padded primality loads leak only their public workspace and source dimensions -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

structure PaddedPublic where
  B : Addr
  Z : Nat
  w : Nat
  source : Addr
  length : Nat

def PaddedPublic.workspace (p : PaddedPublic) : VG.Proof.Bignum.X86_64.Ws := ⟨p.B, p.Z, p.w⟩

structure PaddedState (ptr len : Nat) (p : PaddedPublic) (s : State) : Prop where
  good : ∃ mi, Good s p.B p.Z p.w mi
  room : slot p.w 8 ≤ p.Z
  positive : 1 ≤ p.w
  bound : p.w < 2 ^ 31
  pointer : word s.mem p.B (8 * ptr) = p.source
  length : word s.mem p.B (8 * len) = BitVec.ofNat 64 p.length

theorem paddedZero_state {a ptr len : Nat} (ha : a < 8) (hp : ptr < 32) (hl : len < 32)
    {p : PaddedPublic} {s : State} (h : PaddedState ptr len p s) :
    WP isa (Impl.Rsa.X86_64.Crt.zeroArr a) s (PaddedState ptr len p) := by
  obtain ⟨mi, hg⟩ := h.good
  have hn := hg.scr.nowrap
  have hhdr : 256 ≤ slot p.w a := by simp only [slot, hdrBytes]; omega
  refine WP.mono (zeroArr_ok hg h.room h.positive h.bound ha) fun t ⟨_, ho, hk⟩ => ?_
  have ht : Good t p.B p.Z p.w mi :=
    ⟨hg.scr.congr hk.2.2, (hk.gpr (by decide)).trans hg.rdi, hg.hdr.outside ho hhdr⟩
  have header (i : Nat) (hi : i < 32) : word t.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    ho.word (Or.inl (by omega)) (by omega)
  exact ⟨⟨mi, ht⟩, h.room, h.positive, h.bound,
    (header ptr hp).trans h.pointer, (header len hl).trans h.length⟩

def PaddedRegs (a : Nat) (p : PaddedPublic) (s : State) : Prop :=
  s.gpr .rsi = p.source ∧ s.gpr .rcx = BitVec.ofNat 64 p.length ∧
    s.gpr .rbx = off p.B (slot p.w a)

theorem paddedArgs_state {a ptr len : Nat} (ha : a < 8) (hp : ptr < 32) (hl : len < 32)
    {p : PaddedPublic} {s : State} (h : PaddedState ptr len p s) :
    WP isa (.block [.mov .rsi (.mem (hdr ptr)), .mov .rcx (.mem (hdr len)),
      .mov .rbx (.mem (hdr (sArr a)))]) s (PaddedRegs a p) := by
  obtain ⟨mi, hg⟩ := h.good
  have hld : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot p.w 8 hi; omega_using [h.room, this])
  xrun [PaddedRegs, State.ea, hdr, hg.rdi, hdrOff, hld ptr hp, hld len hl,
    hld (sArr a) (by unfold sArr; omega), h.pointer, h.length, hg.hdr.harr a ha]

theorem loadPadded_ct {a ptr len : Nat} (ha : a < 8) (hp : ptr < 32) (hl : len < 32)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi])
      (.block [.mov .r8 (.mem (hdr (sArr a))), .mov .r12 (.mem (hdr sW))]) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi])
      (.block [.mov .rsi (.mem (hdr ptr)), .mov .rcx (.mem (hdr len)),
        .mov .rbx (.mem (hdr (sArr a)))]) hc₂).isSome = true) :
    RelCT isa (Two (PaddedState ptr len)) (Impl.Dsa.X86_64.Generation.loadPadded a ptr len)
      (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.loadPadded
  simp only [seqs]
  refine RelCT.seq (two_post
    (two_map PaddedPublic.workspace (fun _ _ h => by
      obtain ⟨mi, hg⟩ := h.good
      exact ⟨mi, hg, h.room⟩) (zeroArr_ct ha ht₁))
    (fun _ _ h => paddedZero_state ha hp hl h)) ?_
  refine RelCT.seq (two_post (Ψ := PaddedRegs a) (two_taint [.rdi] ?_ ht₂)
    (fun _ _ h => paddedArgs_state ha hp hl h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs.good
    obtain ⟨mi', ht⟩ := ht.good
    exact hs.rdi.trans ht.rdi.symm
  · exact two_taint [.rsi, .rcx, .rbx] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.trans ht.2.2.symm) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
