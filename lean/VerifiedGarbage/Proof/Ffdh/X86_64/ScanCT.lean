module
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Ffdh.Lead
public import VerifiedGarbage.Proof.Ffdh.X86_64.Ws

import VerifiedGarbage.Proof.Ffdh.X86_64.Scan
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
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
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
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
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
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
meta import VerifiedGarbage.Proof.Bignum.X86_64.Exp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
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

/-! # FFDH on x86-64: the public scan is constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh VG.Proof.MlKem.X86_64

/-- The public data of `scan sp`: the workspace, the pointer and the octets. -/
structure ScanPub where
  B : Addr
  Z : Nat
  w : Nat
  p : Addr
  bs : List Byte

/-- `scan_ok`'s hypotheses. -/
def ScanPre (sp : Nat) (a : ScanPub) (s : State) : Prop :=
  Outer s a.B a.Z a.w ∧ word s.mem a.B (8 * sp) = a.p ∧ word s.mem a.B (8 * sK) = BitVec.ofNat 64 a.bs.length ∧
    a.bs ≠ [] ∧ a.bs.length < 2 ^ 32 ∧ Src s a.B a.Z a.p a.bs ∧ sp < 32

/-- Before iteration `j` of the loop. -/
def ScanJ (a : ScanPub) (j : Nat) (t : State) : Prop :=
  t.gpr .rsi = off a.p j ∧ t.gpr .rcx = BitVec.ofNat 64 (a.bs.length - j) ∧ a.bs ≠ [] ∧
    a.bs.length < 2 ^ 32 ∧ Src t a.B a.Z a.p a.bs ∧ t.gpr .rdi = a.B

theorem scanJ_step (a : ScanPub) (j : Nat) (t : State) (hj : j < lead a.bs + 1) (h : ScanJ a j t) :
    WP isa (.block scanBody) t fun t' => isa.eval .ne t' = some (decide (j + 1 < lead a.bs + 1)) ∧
      (j + 1 < lead a.bs + 1 → ScanJ a (j + 1) t') ∧ (j + 1 = lead a.bs + 1 → ScanJ a (lead a.bs) t') := by
  obtain ⟨h1, h2, hne, hl, hsrc, h0⟩ := h
  refine WP.mono (scanStep_ok (s₀ := t) hl hne hsrc.rd hsrc.val (j := j) (by omega)
    ⟨h1, h2, rfl, Keep.refl _ _⟩) fun t' ⟨⟨h1', h2', hm', k'⟩, hz⟩ => ?_
  have hs' : Src t' a.B a.Z a.p a.bs := hsrc.congr (by rw [hm']; exact InScr.refl _ _ _) k'.2.1 k'.2.2
  have h0' : t'.gpr .rdi = a.B := (k'.gpr (by decide)).trans h0
  refine ⟨?_, fun hlt => ?_, fun he => ?_⟩
  · simp only [eval, hz]
    change some (!decide (j + 1 = lead a.bs + 1)) = some (decide (j + 1 < lead a.bs + 1))
    congr 1
    rw [Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_iff]
    omega
  · rw [Nat.min_eq_left (by omega)] at h1' h2'
    exact ⟨h1', h2', hne, hl, hs', h0'⟩
  · rw [Nat.min_eq_right (by omega)] at h1' h2'
    exact ⟨h1', h2', hne, hl, hs', h0'⟩

/-- `scan sp` leaks the same in runs on the same octets. -/
theorem scan_ct {sp : Nat} {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rsi (.mem (hdr sp)), .mov .rcx (.mem (hdr sK))]) hc₁).isSome = true)
    (hT₂ : (taint.check (Taint.ofRegs [.rdi, .rsi]) (.block [.store (hdr sEp) .rsi, .store (hdr sEl) .rcx, .movzx8 .rax (at0 .rsi)]) hc₂).isSome =
      true) :
    RelCT isa (Two (ScanPre sp)) (seqs (scan sp)) fun _ _ => True := by
  unfold scan
  simp only [seqs]
  refine RelCT.seq (R := Two fun a t => 0 < lead a.bs + 1 ∧ ScanJ a 0 t)
    (two_piece [.rdi] (pins_of (fun a _ => a.B) fun a s h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.1.rdi) hT₁ fun a s h => ?_)
    (RelCT.seq (R := Two fun a t => ScanJ a (lead a.bs) t)
      (two_loop (fun a => lead a.bs + 1)
        (two_taint [.rsi, .rcx] (pins_of (fun (p : ScanPub × Nat) r => if r = .rsi then off p.1.p p.2 else
            BitVec.ofNat 64 (p.1.bs.length - p.2)) fun p t h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.2.1
          · exact h.2.2.1) (by taint_decide))
        fun a j t hj h => scanJ_step a j t hj h)
      (two_taint [.rdi, .rsi] (pins_of (fun a r => if r = .rdi then a.B else off a.p (lead a.bs)) fun a t h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.2.2.2.2.2
        · exact h.1) hT₂))
  obtain ⟨hO, hp, hk, hne, hl, hsrc, hsp⟩ := h
  have l1 := hO.ld hsp
  have l2 := hO.ld (show sK < 32 by decide)
  exact WP.mono (WP.keep [.rsi, .rcx] (Q := fun t => t.gpr .rsi = a.p ∧ t.gpr .rcx = BitVec.ofNat 64 a.bs.length ∧
      t.mem = s.mem)
    (by xrun [State.ea, hdr, hO.rdi, hdrOff, l1, l2, hp, hk])
    rfl)
    fun t ⟨⟨h1, h2, hm⟩, k⟩ => ⟨by omega, by rw [h1]; simp, by rw [h2]; simp, hne, hl,
      hsrc.congr (by rw [hm]; exact InScr.refl _ _ _) k.2.1 k.2.2, (k.gpr (by decide)).trans hO.rdi⟩

end VG.Proof.Ffdh.X86_64
