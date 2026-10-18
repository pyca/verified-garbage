module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionExponentCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # Public values and workspace preservation through the two candidate loads -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

structure CandidatePublic where
  B : Addr
  Z : Nat
  w : Nat
  xp : Addr
  qp : Addr
  xb : List Byte
  qb : List Byte

def CandidatePublic.xLoad (p : CandidatePublic) : LoadPublic := ⟨p.B, p.Z, p.w, p.xp, p.xb⟩
def CandidatePublic.qLoad (p : CandidatePublic) : LoadPublic := ⟨p.B, p.Z, p.w, p.qp, p.qb⟩
def CandidatePublic.reduction (p : CandidatePublic) : ReductionPublic :=
  ⟨p.B, p.Z, p.w, Spec.Rsa.os2ip p.xb, Spec.Rsa.os2ip p.qb⟩

structure CandidateInput (p : CandidatePublic) (s : State) : Prop where
  x : LoadState 16 17 p.xLoad s
  q : LoadState 18 19 p.qLoad s
  qPositive : 0 < Spec.Rsa.os2ip p.qb
  qFits : 2 * Spec.Rsa.os2ip p.qb < 2 ^ (64 * p.w)

structure CandidateFirst (p : CandidatePublic) (s : State) : Prop where
  q : LoadState 18 19 p.qLoad s
  x : wv s.mem p.B (slot p.w 0) p.w = Spec.Rsa.os2ip p.xb
  qPositive : 0 < Spec.Rsa.os2ip p.qb
  qFits : 2 * Spec.Rsa.os2ip p.qb < 2 ^ (64 * p.w)

structure CandidateLoaded (p : CandidatePublic) (s : State) : Prop where
  ws : Ws s p.B p.Z p.w
  x : wv s.mem p.B (slot p.w 0) p.w = Spec.Rsa.os2ip p.xb
  q : wv s.mem p.B (slot p.w 2) p.w = Spec.Rsa.os2ip p.qb
  qPositive : 0 < Spec.Rsa.os2ip p.qb
  qFits : 2 * Spec.Rsa.os2ip p.qb < 2 ^ (64 * p.w)

theorem candidateFirst_state {p : CandidatePublic} {s : State} (h : CandidateInput p s) :
    WP isa (seqs (loadA 0 16 17)) s (CandidateFirst p) := by
  refine WP.mono (loadCandidateArray_ok h.x.ws (by decide : 0 < 16) (by decide : 16 < 32)
    (by decide : 17 < 32) h.x.pointer h.x.length h.x.source h.x.positive h.x.fits)
    fun t ⟨ht, hx, f, hk⟩ => ?_
  have hdr (d : Nat) (hd : d + 8 ≤ 256) : word t.mem p.B d = word s.mem p.B d := by
    apply f.word_eq
    · simp only [List.mem_singleton]; rintro r rfl
      left; simp only [slot, hdrBytes]; omega
    · have := h.x.ws.h256; have := h.x.ws.scr.nowrap; omega
  refine ⟨⟨ht, (hdr 144 (by decide)).trans h.q.pointer, (hdr 152 (by decide)).trans h.q.length,
    h.q.source.congrK ?_ hk, h.q.positive, h.q.fits⟩, hx, h.qPositive, h.qFits⟩
  intro a ha
  apply f a
  simp only [List.mem_singleton]; rintro r rfl
  right
  exact Nat.le_trans (h.x.ws.sl (by decide : 0 < 16)) ha

theorem candidateSecond_state {p : CandidatePublic} {s : State} (h : CandidateFirst p s) :
    WP isa (seqs (loadA 2 18 19)) s (CandidateLoaded p) := by
  have hw : Ws s p.B p.Z p.w := h.q.ws
  refine WP.mono (loadCandidateArray_ok h.q.ws (by decide : 2 < 16) (by decide : 18 < 32)
    (by decide : 19 < 32) h.q.pointer h.q.length h.q.source h.q.positive h.q.fits)
    fun t ⟨ht, hq, f, _⟩ => ?_
  change Frm p.B [ar p.w 2] s.mem t.mem at f
  refine ⟨ht, ?_, hq, h.qPositive, h.qFits⟩
  rw [f.wv_eq (by
    simp only [List.mem_singleton]; rintro r rfl
    left; simp only [slot, hdrBytes]; omega)
    (by have := hw.sl (by decide : 0 < 16); have := hw.scr.nowrap; omega)]
  exact h.x

theorem candidateDouble_state {p : CandidatePublic} {s : State} (h : CandidateLoaded p s) :
    WP isa (Impl.Dsa.X86_64.Generation.doubleArray 2) s (ReductionStart p.reduction) := by
  refine WP.mono (doubleArray_ok h.ws (by decide : 2 < 16) (by rw [h.q]; exact h.qFits))
    fun t ⟨hq, ho, hk⟩ => ?_
  have f : Frm p.B [ar p.w 2] s.mem t.mem :=
    Frm.of_outside (ho.mono (n' := 8 * (p.w + 2)) (Nat.le_refl _) (by omega)) (by simp [ar])
  have ht := h.ws.congr f (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) hk (by decide)
  refine ⟨ht, ?_, ?_, h.qPositive⟩
  · change wv t.mem p.B (slot p.w 0) p.w = Spec.Rsa.os2ip p.xb
    rw [f.wv_eq (by
      simp only [List.mem_singleton]; rintro r rfl
      left; simp only [slot, hdrBytes]; omega)
      (by have := h.ws.sl (by decide : 0 < 16); have := h.ws.scr.nowrap; omega)]
    exact h.x
  · change wv t.mem p.B (slot p.w 2) p.w = 2 * Spec.Rsa.os2ip p.qb
    rw [hq, h.q]

end VG.Proof.Dsa.X86_64.Generation
