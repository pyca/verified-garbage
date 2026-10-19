module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.InnerCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LinkCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TapeHead

/-! # FFDH parameter generation on x86-64: public witness-sampling state -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen.X86_64

structure DrawPublic where
  p : WitnessParams
  rp : Addr
  used : Nat
  bs : List Byte
  wr : List Region

def DrawBefore (d : DrawPublic) (s : State) : Prop :=
  DrawState d.p d.rp d.used d.bs s ∧ s.wr = d.wr ∧ InnerKW d.p.O d.wr

theorem DrawBefore.link {d : DrawPublic} {s : State} (h : DrawBefore d s) :
    LinkHeader ⟨d.p.O, d.wr⟩ s :=
  ⟨h.2.2, h.1.ready.good.rdi, h.2.1, fun e he => by
    simp only [List.mem_singleton] at he; subst e; exact h.1.link⟩

def DrawPublic.inner (d : DrawPublic) : InnerPublic :=
  ⟨d.p.O, d.p.w, d.wr, d.p.op, d.p.len, 0⟩

theorem DrawBefore.header {d : DrawPublic} {s : State} (h : DrawBefore d s) : InnerHeader d.inner s :=
  ⟨h.2.2, good_hp h.1.ready.good h.2.1⟩

/-- A byte cut temporarily uses RDI for the output buffer; the saved
modulus words still belong to the inner frame. -/
structure CutBefore (d : DrawPublic) (s : State) : Prop where
  retained : ∃ s₀ : State, ModulusReady s₀ d.p.I d.p.IZ d.p.w d.p.mi d.p.N ∧ s.wr = s₀.wr ∧
    ∀ off, off + 8 ≤ d.p.IZ → word s.mem d.p.I off = word s₀.mem d.p.I off
  scr : Scr s d.p.O d.p.Z
  link : word s.mem d.p.I (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = d.p.O
  outPtr : word s.mem d.p.O (8 * oOut) = d.p.op
  len : word s.mem d.p.O (8 * oWitnessLen) = BitVec.ofNat 64 d.p.len
  rdi : s.gpr .rdi = d.p.op
  rsi : s.gpr .rsi = d.rp
  rbp : s.gpr .rbp = d.p.I
  rcx : s.gpr .rcx = BitVec.ofNat 64 d.p.len
  rdx : s.gpr .rdx = BitVec.ofNat 64 d.p.bits
  src : Src s d.p.O d.p.Z d.rp (d.bs.take d.p.len)
  out : OutOk s d.p.O d.p.Z d.p.op d.p.len
  apart : Apart d.p.op d.p.len d.rp (d.bs.take d.p.len).length
  available : d.p.len ≤ d.bs.length
  wr : s.wr = d.wr
  kw : InnerKW d.p.O d.wr

theorem drawSetup_cut (d : DrawPublic) (s : State) (h : DrawBefore d s) (ha : d.p.len ≤ d.bs.length) :
    WP isa (.block drawSetup) s (CutBefore d) := by
  have houter : Scr s d.p.O 256 := by
    simpa [off] using h.1.scr.sub (o := 0) (n := 256) d.p.space_bounds.1 (by decide)
  refine WP.mono (drawSetup_ok h.1.ready.good.scr d.p.space_bounds.2.1 houter h.1.ready.good.rdi
    h.1.link h.1.outPtr h.1.ptr h.1.left h.1.usedWord h.1.len h.1.bits
    (by omega_using [d.p.width_bounds.2.2.2.1]) ha)
    fun t ⟨hm, hsi, hdi, hbp, hcx, hdx, k⟩ => ?_
  have hf : Frm d.p.O [(8 * oRandPtr, 24)] s.mem t.mem := by rw [hm]; exact advanceMem_frame _ _ _ _ _ _
  have hi : InScr d.p.O d.p.Z s.mem t.mem := InScr.of_frm hf (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    change 120 ≤ d.p.Z; omega_using [d.p.space_bounds.1])
  have hw : ∀ off, off + 8 ≤ d.p.IZ → word t.mem d.p.I off = word s.mem d.p.I off :=
    outer_words (Z := d.p.IZ) hf (by simp [oRandPtr]) (by
      have hz64 := Nat.le_trans (Nat.le_add_left _ _) h.1.scr.nowrap
      omega_using [hz64, d.p.space_bounds.2.2])
  have hh : ∀ j < 32, j ≠ 12 → j ≠ 13 → j ≠ 14 → word t.mem d.p.O (8 * j) = word s.mem d.p.O (8 * j) := by
    intro j hj h12 h13 h14
    apply hf.word_eq
    · intro r hr; simp only [List.mem_singleton] at hr; subst r
      change 8 * j + 8 ≤ 96 ∨ 120 ≤ 8 * j; omega
    · omega
  exact ⟨⟨s, h.1.ready, k.2.2, hw⟩, h.1.scr.congr k.2.2,
    (hw _ d.p.space_bounds.2.1).trans h.1.link,
    (hh _ (by decide) (by decide) (by decide) (by decide)).trans h.1.outPtr,
    (hh _ (by decide) (by decide) (by decide) (by decide)).trans h.1.len,
    hdi, hsi, hbp, hcx, hdx, source_take (h.1.rand.congrK hi k) d.p.len,
    ⟨fun i hi => by rw [k.2.2]; exact h.1.out.wr i hi, h.1.out.sep⟩,
    fun i hi j hj => h.1.apart i hi j (by rw [List.length_take] at hj; omega), ha,
    k.2.2.trans h.2.1, h.2.2⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
