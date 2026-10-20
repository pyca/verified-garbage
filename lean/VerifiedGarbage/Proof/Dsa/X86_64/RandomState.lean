module
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawControl
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomMask

import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual

/-! The sampler state retained across rejected draws. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomContext where
  B : Addr
  initialMem : Mem
  R : Addr
  Q : Addr
  qBytes : List Byte
  rand : List Byte
  qlen : qBytes.length ≤ 32
  randBound : rand.length < 2 ^ 64
  positive : 0 < (VG.Proof.Dsa.significant qBytes).1

def randomWriteRanges : List (Nat × Nat) := [(144, 8), (160, 72)]

structure RandomReady (C : RandomContext) (used draws : Nat) (s : State) : Prop where
  scr : Scr s C.B Random.frameBytes
  sp : s.gpr .rsp = C.B
  rand : word s.mem C.B Random.oRand = C.R
  randLen : word s.mem C.B Random.oRandLen = BitVec.ofNat 64 C.rand.length
  usedWord : word s.mem C.B Random.oUsed = BitVec.ofNat 64 used
  width : word s.mem C.B Random.oWidth = BitVec.ofNat 64 (VG.Proof.Dsa.significant C.qBytes).1
  qLen : word s.mem C.B Random.oQLen = BitVec.ofNat 64 C.qBytes.length
  mask : word s.mem C.B Random.oMask = randomMaskValue (VG.Proof.Dsa.significant C.qBytes).2.toNat
  q : word s.mem C.B Random.oQ = C.Q + BitVec.ofNat 64
    (C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1)
  draws : word s.mem C.B Random.oDraws = BitVec.ofNat 64 draws
  randSrc : Src s C.B Random.frameBytes C.R C.rand
  qSrc : Src s C.B Random.frameBytes C.Q C.qBytes
  usedBound : used ≤ C.rand.length
  frame : Frm C.B randomWriteRanges C.initialMem s.mem
  padding : ∀ i < C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1,
    s.mem (off C.B (200 + i)) = 0

theorem RandomReady.congr {C : RandomContext} {used draws : Nat} {s t : State}
    (h : RandomReady C used draws s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) :
    RandomReady C used draws t := by
  have hf : InScr C.B Random.frameBytes s.mem t.mem := by rw [hm]; exact InScr.refl _ _ _
  exact ⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.sp,
    by rw [hm]; exact h.rand, by rw [hm]; exact h.randLen,
    by rw [hm]; exact h.usedWord, by rw [hm]; exact h.width,
    by rw [hm]; exact h.qLen, by rw [hm]; exact h.mask,
    by rw [hm]; exact h.q, by rw [hm]; exact h.draws,
    h.randSrc.congrK hf hk, h.qSrc.congrK hf hk, h.usedBound, by rw [hm]; exact h.frame, by rw [hm]; exact h.padding⟩

/-- Reconstruct the persistent state from the exact memory effects of a draw. -/
theorem RandomReady.after_draw {C : RandomContext} {used draws : Nat} {s t : State} {m : Mem}
    (h : RandomReady C used draws s) (accept : Bool)
    (hfull : used + (VG.Proof.Dsa.significant C.qBytes).1 ≤ C.rand.length)
    (hcopy : Outside C.B (200 + C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1)
      (VG.Proof.Dsa.significant C.qBytes).1 s.mem m)
    (hm : t.mem = randomDrawFinishMem
      (m.writeW (off C.B Random.oUsed) (BitVec.ofNat 64 (used + (VG.Proof.Dsa.significant C.qBytes).1)))
      C.B accept draws)
    (hk : Keep [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11] s t) :
    RandomReady C (used + (VG.Proof.Dsa.significant C.qBytes).1)
      (if accept then draws else draws - 1) t := by
  have hnfit := VG.Proof.Dsa.significant_fits C.qBytes
  have hcopyCoarse : Outside C.B 200 32 s.mem m := hcopy.mono (by omega) (by have := C.qlen; omega)
  let m' := m.writeW (off C.B Random.oUsed) (BitVec.ofNat 64 (used + (VG.Proof.Dsa.significant C.qBytes).1))
  have hused : Outside C.B Random.oUsed 8 m m' := writeW_outside _ _ _ (by decide)
  have hfinish := random_drawFinish_outside m' C.B accept draws
  have hf : InScr C.B Random.frameBytes s.mem t.mem := by
    rw [hm]
    exact ((InScr.of_outside hcopyCoarse (by decide)).trans
      (InScr.of_outside hused (by decide))).trans (InScr.of_outside hfinish (by decide))
  have hw (d : Nat) (hd : d + 8 ≤ 200)
      (hu : d + 8 ≤ 144 ∨ 152 ≤ d) (hdraw : d + 8 ≤ 160 ∨ 168 ≤ d)
      (hstatus : d + 8 ≤ 192 ∨ 200 ≤ d) : word t.mem C.B d = word s.mem C.B d := by
    rw [hm, random_drawFinish_word _ _ _ _ d (by omega) hdraw hstatus,
      hused.word hu (by omega), hcopyCoarse.word (Or.inl hd) (by omega)]
  refine ⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.sp,
    (hw _ (by decide) (by decide) (by decide) (by decide)).trans h.rand,
    (hw _ (by decide) (by decide) (by decide) (by decide)).trans h.randLen, ?_,
    (hw _ (by decide) (by decide) (by decide) (by decide)).trans h.width,
    (hw _ (by decide) (by decide) (by decide) (by decide)).trans h.qLen,
    (hw _ (by decide) (by decide) (by decide) (by decide)).trans h.mask,
    (hw _ (by decide) (by decide) (by decide) (by decide)).trans h.q, ?_,
    h.randSrc.congrK hf hk, h.qSrc.congrK hf hk, hfull, ?_, ?_⟩
  · rw [hm, random_drawFinish_word _ _ _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm, random_drawFinish_draws]
    cases accept with
    | false => rfl
    | true =>
      simp only [ite_true]
      rw [hused.word (by decide) (by decide), hcopyCoarse.word (by decide) (by decide)]
      exact h.draws
  · rw [hm]
    exact ((h.frame.trans (Frm.of_outside (hcopyCoarse.mono (by decide) (by decide))
      (show (160, 72) ∈ randomWriteRanges by decide))).trans
      (Frm.of_outside hused (show (144, 8) ∈ randomWriteRanges by decide))).trans
      (Frm.of_outside (hfinish.mono (by decide) (by decide)) (show (160, 72) ∈ randomWriteRanges by decide))
  · intro i hi
    have ho : ofs C.B (off C.B (200 + i)) = 200 + i := by
      have he : off C.B (200 + i) + BitVec.ofNat 64 0 = off C.B (200 + i) := BitVec.add_zero _
      simpa only [he, Nat.add_zero] using ofs_off C.B (d := 200 + i) (i := 0) (by have := C.qlen; omega)
    rw [hm, hfinish _ (by rw [ho]; right; omega),
      hused _ (by rw [ho]; right; unfold Random.oUsed; omega),
      hcopy _ (by rw [ho]; left; omega)]
    exact h.padding i hi

theorem RandomReady.after_status {C : RandomContext} {used draws : Nat} {s t : State} {status : BitVec 64}
    (h : RandomReady C used draws s)
    (hm : t.mem = s.mem.writeW (off C.B Random.oStatus) status) (hk : Keep [.rax] s t) :
    RandomReady C used draws t := by
  have hf : Outside C.B Random.oStatus 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by decide)
  have hi := InScr.of_outside hf (show Random.oStatus + 8 ≤ Random.frameBytes by decide)
  have hw (d : Nat) (hd : d + 8 ≤ 192) : word t.mem C.B d = word s.mem C.B d :=
    hf.word (Or.inl hd) (by omega)
  refine ⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.sp,
    (hw _ (by decide)).trans h.rand, (hw _ (by decide)).trans h.randLen,
    (hw _ (by decide)).trans h.usedWord, (hw _ (by decide)).trans h.width,
    (hw _ (by decide)).trans h.qLen, (hw _ (by decide)).trans h.mask,
    (hw _ (by decide)).trans h.q, (hw _ (by decide)).trans h.draws,
    h.randSrc.congrK hi hk, h.qSrc.congrK hi hk, h.usedBound,
    h.frame.trans (Frm.of_outside (hf.mono (by decide) (by decide))
      (show (160, 72) ∈ randomWriteRanges by decide)), ?_⟩
  intro i hi'
  have ho : ofs C.B (off C.B (200 + i)) = 200 + i := by
    have he : off C.B (200 + i) + BitVec.ofNat 64 0 = off C.B (200 + i) := BitVec.add_zero _
    simpa only [he, Nat.add_zero] using ofs_off C.B (d := 200 + i) (i := 0) (by have := C.qlen; omega)
  rw [hf _ (by rw [ho]; right; unfold Random.oStatus; omega)]
  exact h.padding i hi'

end VG.Proof.Dsa.X86_64
