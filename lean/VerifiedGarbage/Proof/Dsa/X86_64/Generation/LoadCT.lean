module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces

import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCT
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Rsa.Ranges
meta import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReduction
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Division
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Double
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Increment
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Reduce
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionExponent
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Subtract
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Rsa.X86_64.CvCode
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.BitLengthBounds
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Generation.PReduction
meta import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReduction
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Division
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Double
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Increment
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Reduce
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionExponent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Subtract
meta import VerifiedGarbage.Proof.Ffdh.KeyScalar
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCode
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops

/-! # Constant time of padded candidate loads from public pointers and lengths -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Keys VG.Impl.Bignum.X86_64

structure LoadPublic where
  B : Addr
  Z : Nat
  w : Nat
  ptr : Addr
  bytes : List Byte

structure LoadState (ptr len : Nat) (p : LoadPublic) (s : State) : Prop where
  ws : Ws s p.B p.Z p.w
  pointer : word s.mem p.B (8 * ptr) = p.ptr
  length : word s.mem p.B (8 * len) = BitVec.ofNat 64 p.bytes.length
  source : Src s p.B p.Z p.ptr p.bytes
  positive : 1 ≤ p.bytes.length
  fits : p.bytes.length ≤ 8 * p.w

theorem loadZero_state {a ptr len : Nat} (ha : a < 16) (hp : ptr < 32) (hl : len < 32)
    {p : LoadPublic} {s : State} (h : LoadState ptr len p s) :
    WP isa (zeroA a) s (LoadState ptr len p) := by
  refine WP.mono (zeroA_ok h.ws ha) fun t ⟨_, ho, hk⟩ => ?_
  have f : Frm p.B [ar p.w a] s.mem t.mem := Frm.of_outside ho (by simp [ar])
  have ht := h.ws.congr f (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) hk (by decide)
  have hdr (i : Nat) (hi : i < 32) : word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := by
    apply f.word_eq
    · simp only [List.mem_singleton]; rintro r rfl
      left; simp only [slot, hdrBytes]; omega
    · have := h.ws.h256; have := h.ws.scr.nowrap; omega
  refine ⟨ht, (hdr ptr hp).trans h.pointer, (hdr len hl).trans h.length,
    h.source.congrK ?_ hk, h.positive, h.fits⟩
  intro x hx
  apply f x
  simp only [List.mem_singleton]; rintro r rfl
  right
  have := h.ws.sl ha
  exact Nat.le_trans this hx

theorem loadZero_ct {a ptr len : Nat} (ha : a < 16) (hp : ptr < 32) (hl : len < 32)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.seq (.block (base a .r8)) zeroAccLoop) hc).isSome = true) :
    RelCT isa (Two (LoadState ptr len)) (zeroA a) (Two (LoadState ptr len)) :=
  ws_ct LoadPublic.B LoadPublic.Z LoadPublic.w (fun _ _ h => h.ws) ht
    (fun _ _ h => loadZero_state ha hp hl h)

def loadPublicRegs (a : Nat) (p : LoadPublic) : Reg → BitVec 64
  | .rdi => p.B
  | .rbx => off p.B (slot p.w a)
  | .rsi => p.ptr
  | .rcx => BitVec.ofNat 64 p.bytes.length
  | _ => 0

theorem loadTail_ct {a ptr len : Nat} (ha : a < 16) (hp : ptr < 32) (hl : len < 32)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base a .rbx ++
      ([.mov .rsi (.mem (hdr ptr)), .mov .rcx (.mem (hdr len))] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (LoadState ptr len))
      (.seq (.block (ws ++ base a .rbx ++ ([.mov .rsi (.mem (hdr ptr)), .mov .rcx (.mem (hdr len))] : List Instr)))
        loadBE) (fun _ _ => True) := by
  have ct := pin_ct (c₂ := loadBE) (Φ := LoadState ptr len) (Ψ := fun _ _ => True)
    [.rdi] [.rdi, .rbx, .rsi, .rcx] (loadPublicRegs a) (by
      intro p s t hs ht r hr
      simp only [List.mem_singleton] at hr
      subst r; exact hs.ws.rdi.trans ht.ws.rdi.symm) ht
    (fun p s h => WP.mono (loadBlk_ok h.ws hp hl h.pointer h.length)
      fun t ⟨hbx, hsi, hcx, hdi, _, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact hbx
        · exact hsi
        · exact hcx)
    (by taint_decide) (fun p s h => ?_)
  · exact ct.mono (fun _ _ h => h) (fun _ _ _ => True.intro)
  · refine WP.seq (WP.mono (loadBlk_ok h.ws hp hl h.pointer h.length)
      fun t ⟨hbx, hsi, hcx, _, hm, hk⟩ => ?_)
    have src := h.source.congrK (fun x _ => by rw [hm]) hk
    have nw := h.ws.scr.nowrap
    have room := h.ws.sl ha
    have words := h.ws.w2
    have fits := h.fits
    exact WP.mono (loadBE_ok (w := (p.bytes.length + 7) / 8) (h.ws.scr.congr hk.2.2)
      hsi hcx hbx rfl h.positive (by omega) rfl (by omega)
      (fun i hi => src.rd i (by omega)) (fun i hi => src.val i (by omega))
      (fun i hi => Or.inr (by have := src.out i (by omega); omega))) (fun _ _ => True.intro)

theorem loadCandidate_ct {a ptr len : Nat} (ha : a < 16) (hp : ptr < 32) (hl : len < 32)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.seq (.block (base a .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base a .rbx ++
      ([.mov .rsi (.mem (hdr ptr)), .mov .rcx (.mem (hdr len))] : List Instr))) hc₂).isSome = true) :
    RelCT isa (Two (LoadState ptr len)) (seqs (loadA a ptr len)) (fun _ _ => True) :=
  RelCT.seq (loadZero_ct ha hp hl ht₁) (loadTail_ct ha hp hl ht₂)

end VG.Proof.Dsa.X86_64.Generation
