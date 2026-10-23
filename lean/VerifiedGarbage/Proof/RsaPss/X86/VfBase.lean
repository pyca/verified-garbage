module

public import VerifiedGarbage.Impl.RsaPss.X86
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Entry
public import VerifiedGarbage.Spec.RsaPss.Precomputed
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaPss.X86.Base
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS verification with a precomputed public key on x86: where everything is

As on ARMv7 (`Proof/RsaPss/Arm/VfBase.lean`): `EP`, what two runs share
(the frame's base `B`, the pointers, the lengths, `salt_len`,
`any_salt_len`, and the public key's bytes and precomputed words), and its
layout (`EP.lay`), with the 100 bytes below the frame that the call of
`vg_rsa_public_precomputed_checked` (100) and the hash function's calls (48)
use. `In D P σ`: the state `σ` the body starts from (`in_of_pre`); the
working space's bound is used in one place, `In.pubScr`.

`VQ F c G`: a piece correct (`wp`) and constant time with nothing after it
(`ct`), as the end of a body; the pieces after the call are proven over the
state the call leaves (`VQ.reidx`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

/-- What two runs share. -/
structure EP where
  B : BitVec 32
  n : BitVec 32
  e : BitVec 32
  dig : BitVec 32
  sig : BitVec 32
  scr : BitVec 32
  pre : BitVec 32
  K : Nat
  el : Nat
  gl : Nat
  slt : Nat
  any : BitVec 32
  scl : Nat
  rl : Nat
  nB : List Byte
  eB : List Byte
  pw : List (BitVec 64)

namespace EP

variable (D : Nat) (P : EP)

abbrev N : Region := ⟨P.n.setWidth 64, P.K⟩
abbrev E : Region := ⟨P.e.setWidth 64, P.el⟩
abbrev DIG : Region := ⟨P.dig.setWidth 64, D⟩
abbrev SIG : Region := ⟨P.sig.setWidth 64, P.gl⟩
abbrev SCR : Region := ⟨P.scr.setWidth 64, P.scl * 8⟩
abbrev PRE : Region := ⟨P.pre.setWidth 64, P.rl * 8⟩

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.dig, P.sig, BitVec.ofNat 32 P.gl,
    BitVec.ofNat 32 P.slt, P.any, P.scr, BitVec.ofNat 32 P.scl, P.pre, BitVec.ofNat 32 P.rl]

abbrev ro : List Region := [P.N, P.E, P.DIG D, P.SIG, P.PRE]
abbrev rw : List Region := [P.SCR]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  argv := P.argv
  ro := P.ro D
  rw := P.rw
  C := 100

end EP

/-- The state the body starts from. -/
structure In (D : Nat) (P : EP) (σ : State) : Prop where
  ok : (P.lay D).Ok σ
  kv : Spec.Rsa.lenValid P.K
  el1 : 1 ≤ P.el
  elK : P.el ≤ P.K
  glK : P.gl = P.K
  scrK : Spec.RsaPss.publicScratchWords P.K ≤ P.scl
  rlK : P.rl = Spec.Rsa.precomputedWords P.K
  slt32 : P.slt < 2 ^ 32
  scl32 : P.scl < 2 ^ 32
  nB : Spec.Rsa.bytesAt σ.mem (P.n.setWidth 64) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (P.e.setWidth 64) P.el = P.eB
  pw : Spec.Rsa.wordsAt σ.mem (P.pre.setWidth 64) P.rl = P.pw

namespace In

variable {D : Nat} {P : EP} {σ : State} (h : In D P σ)
include h

theorem k64 : 64 ≤ P.K := h.kv.1
theorem k1024 : P.K ≤ 1024 := h.kv.2

/-- The working space: ours, and the public operation's after it. This is
the one place the contract's bound on `scratch_len` is used. -/
theorem pubScr : Spec.Rsa.publicScratchWords P.K ≤ P.scl - 1024 ∧ 1025 ≤ P.scl := by
  have := h.scrK
  unfold Spec.RsaPss.publicScratchWords Spec.Rsa.publicScratchWords at this
  unfold Spec.Rsa.publicScratchWords
  omega

/-- Our part of `scratch`. -/
theorem geo : Geo (P.lay D) P.scr := by
  have hs := h.pubScr.2
  have hf := h.ok.fits (P.SCR) (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.scr.isLt; omega)] at hf
  exact ⟨rfl, by unfold oRsa; omega, ⟨P.scl * 8, by unfold oRsa; omega, by simp⟩, ⟨σ, h.ok⟩,
    by show 48 ≤ 100; decide⟩

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the calls'. -/
abbrev stackBytes : Nat := 16 + frameBytes + 100

/-- The shared contract, with that stack. -/
abbrev spec (G : Spec.Mgf1.Hash) : Contract isa := Spec.RsaPss.verifyPrecomputedContract G G abi stackBytes

/-- The public parameters of an entry state. -/
def ep (s : State) : EP where
  B := s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 frameBytes
  n := arg s 0
  e := arg s 2
  dig := arg s 4
  sig := arg s 5
  scr := arg s 9
  pre := arg s 11
  K := (arg s 1).toNat
  el := (arg s 3).toNat
  gl := (arg s 6).toNat
  slt := (arg s 7).toNat
  any := arg s 8
  scl := (arg s 10).toNat
  rl := (arg s 12).toNat
  nB := Spec.Rsa.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat
  eB := Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat
  pw := Spec.Rsa.wordsAt s.mem ((arg s 11).setWidth 64) (arg s 12).toNat

theorem ep_lay (D : Nat) (s : State) :
    (ep s).lay D = layOf frameBytes (ep s).argv ((ep s).ro D) (ep s).rw s 100 := rfl

theorem in_of_pre {G : Spec.Mgf1.Hash} {s : State} (h : (spec G).pre s) : In G.len (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argSlots, argVal,
    argBytes, stackBelow] at h
  obtain ⟨hsp, hsa, hrd, hwr, nS, nA, eS, eA, dS, dA, gS, gA, sR, sA, rA, rN, rE, rD, rG, rS, rR, rAr,
    kN, kE, kD, kG, kS, kR, kA, fN, fE, fD, fG, fS, fR, kv, el1, elK, glK, scrK, rlK⟩ := h
  simp only [stackBytes, frameBytes, Nat.reduceAdd] at hsp kN kE kD kG kS kR kA
  have h16 : 4 * Impl.RsaPkcs1Sig.X86.savedRegs.length ≤ (s.gpr .esp).toNat := by
    simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega
  have hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
      (entered frameBytes s).mem :=
    pushed_frame (by decide) h16
  have below16 : Region.Sub (below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length))
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 260, 260⟩ := by
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega)]
    exact Offset.sub_below _ (by omega) (by omega)
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, glK := glK, scrK := scrK, rlK := rlK
      slt32 := (arg s 7).isLt
      scl32 := (arg s 10).isLt
      nB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below16).symm)
        (by show (arg s 1).toNat ≤ 2 ^ 64; omega)
      eB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below16).symm)
        (by show (arg s 3).toNat ≤ 2 ^ 64; omega)
      pw := Proof.RsaPkcs1Sig.wordsAt_frame' hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kR.sub_left below16).symm)
        (by show (arg s 12).toNat * 8 ≤ 2 ^ 64; have := (arg s 12).isLt; omega) }
  rw [ep_lay]
  refine ok_entered (S := 260) rfl (by decide) hsp (by simp) (by simp; omega) hrd
    (by rw [hwr]; rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kD, kG, kR, kS]
  · intro r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact rS
  · intro w hw r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [EP.ro, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hw
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [nS.symm, eS.symm, dS.symm, gS.symm, sR, sA]
  · exact List.pairwise_singleton _ _
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [ep, BitVec.toNat_setWidth]
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 4).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 5).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 11).isLt; omega)]; omega)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 9).isLt; omega)]; omega)
  · intro j hj
    have : j < 13 := hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
        j = 10 ∨ j = 11 ∨ j = 12) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep]

/-! ## Pieces at the end of the body -/

/-- Correct, and constant time with nothing after it. -/
def VQ (F : State → State → Prop) (c : Prog isa) (G : State → State → Prop) : Prop :=
  (∀ σ s, F σ s → WP isa c s (G σ)) ∧ RelCT isa (Two F) c fun _ _ => True

theorem VQ.of_vp {F G : State → State → Prop} {c : Prog isa} (h : VP F c G) : VQ F c G :=
  ⟨h.wp, h.ct.mono (fun _ _ h => h) fun _ _ _ => trivial⟩

theorem VQ.seq {F G H : State → State → Prop} {c₁ c₂ : Prog isa} (h₁ : VP F c₁ G) (h₂ : VQ G c₂ H) :
    VQ F (.seq c₁ c₂) H :=
  ⟨fun σ s hs => WP.seq (WP.mono (h₁.wp σ s hs) fun t ht => h₂.1 σ t ht), RelCT.seq h₁.ct h₂.2⟩

theorem VQ.ite {F G : State → State → Prop} {c : Cond} {t e : Prog isa}
    (hd : ∀ σ s, F σ s → ∃ b, isa.eval c s = some b)
    (hc : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : VQ (fun σ s => F σ s ∧ isa.eval c s = some true) t G)
    (he : VQ (fun σ s => F σ s ∧ isa.eval c s = some false) e G) : VQ F (.ite c t e) G := by
  refine ⟨fun σ s hs => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hd σ s hs
    exact WP.ite b hb (fun h => ht.1 σ s ⟨hs, by rw [hb, h]⟩) (fun h => he.1 σ s ⟨hs, by rw [hb, h]⟩)
  · refine RelCT.ite (fun s₁ s₂ ⟨σ₁, σ₂, h₁, h₂⟩ => hc _ _ _ _ h₁ h₂) ?_ ?_
    · exact ht.2.mono (fun s₁ s₂ ⟨⟨σ₁, σ₂, h₁, h₂⟩, e⟩ =>
        ⟨σ₁, σ₂, ⟨h₁, e⟩, h₂, (hc _ _ _ _ h₁ h₂).symm.trans e⟩) fun _ _ h => h
    · exact he.2.mono (fun s₁ s₂ ⟨⟨σ₁, σ₂, h₁, h₂⟩, e⟩ =>
        ⟨σ₁, σ₂, ⟨h₁, e⟩, h₂, (hc _ _ _ _ h₁ h₂).symm.trans e⟩) fun _ _ h => h

/-- A piece proven over the state it starts from, as a piece of a run from `σ`. -/
theorem VQ.reidx {F F' G G' : State → State → Prop} {c : Prog isa} (h : VP F' c G')
    (hF : ∀ σ s, F σ s → F' s s) (hG : ∀ σ s t, F σ s → G' s t → G σ t) : VQ F c G :=
  ⟨fun σ s hs => WP.mono (h.wp s s (hF σ s hs)) fun t ht => hG σ s t hs ht,
    h.ct.mono (fun s₁ s₂ ⟨_, _, h₁, h₂⟩ => ⟨s₁, s₂, hF _ _ h₁, hF _ _ h₂⟩) fun _ _ _ => trivial⟩

end VG.Proof.RsaPss.X86.Vf
