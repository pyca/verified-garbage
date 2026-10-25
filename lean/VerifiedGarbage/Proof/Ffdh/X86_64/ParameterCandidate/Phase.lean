module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: per-modulus witness policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

def phaseMem (m : Mem) (O : Addr) (bits : Nat) : Mem :=
  ((m.writeW (off O (8 * oWitnessBits)) (BitVec.ofNat 64 bits)).writeW
    (off O (8 * oWitnessLen)) (BitVec.ofNat 64 ((bits + 7) / 8))).writeW
    (off O (8 * oChecks)) (BitVec.ofNat 64 (Spec.Ffdh.primeChecks bits))

/-- The threshold is checked against this modulus, including q's smaller width. -/
theorem phaseWidth_ok {s : State} {O : Addr} {bits : Nat}
    (hs : Scr s O 256) (hdi : s.gpr .rdi = O)
    (hb : bits < 2 ^ 32) (hbits : s.gpr .rdx = BitVec.ofNat 64 bits) :
    WP isa (.block phaseWidth) s fun t =>
      t.mem = phaseMem s.mem O bits ∧ t.gpr .rax = off O 256 ∧ Keep [.rax, .rcx, .rdx] s t := by
  have hwr : ∀ j < 32, InRegions s.wr (off O (8 * j)) 8 := fun j hj => hs.st (by omega_arith)
  have hcf : decide ((BitVec.ofNat 64 bits).toNat <
      (BitVec.signExtend 64 (2049 : BitVec 32)).toNat) = decide (bits ≤ 2048) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    change decide (bits < 2049) = decide (bits ≤ 2048)
    exact decide_eq_decide.mpr (by omega_arith)
  have hchecks : (if !decide (bits ≤ 2048) then (128#32).setWidth 64 else (64#32).setWidth 64) =
      BitVec.ofNat 64 (Spec.Ffdh.primeChecks bits) := by
    by_cases h : bits ≤ 2048 <;> simp [Spec.Ffdh.primeChecks, h]
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t =>
    t.mem = phaseMem s.mem O bits ∧ t.gpr .rax = off O 256) ?_ rfl)
    fun t ⟨⟨hm, ha⟩, k⟩ => ⟨hm, ha, k⟩
  xrun [phaseWidth, phaseMem, State.ea, hdr, hdi, hdrOff, hbits,
    hwr oWitnessBits (by decide), hwr oWitnessLen (by decide), hwr oChecks (by decide),
    shr3_w bits hb, hcf, cmov_reg_value, eval]
  constructor
  · congr 1
  · rfl

theorem phaseMem_frame (m : Mem) (O : Addr) (bits : Nat) :
    Frm O [(8 * oWitnessBits, 24)] m (phaseMem m O bits) := by
  have hf (m : Mem) (d : Nat) (v : BitVec 64) (h1 : 8 * oWitnessBits ≤ d)
      (h2 : d + 8 ≤ 8 * oWitnessBits + 24) : Frm O [(8 * oWitnessBits, 24)] m (m.writeW (off O d) v) :=
    by
      have hd : d + 8 ≤ 2 ^ 64 := by
        have hh : 8 * oWitnessBits + 24 ≤ 2 ^ 64 := by decide
        omega_arith
      exact Frm.of_outside ((writeW_outside m O (d := d) v hd).mono h1 h2) (by simp)
  unfold phaseMem
  exact (hf m (8 * oWitnessBits) (BitVec.ofNat 64 bits) (by decide) (by decide)).trans
    ((hf _ (8 * oWitnessLen) (BitVec.ofNat 64 ((bits + 7) / 8)) (by decide) (by decide)).trans
      (hf _ (8 * oChecks) (BitVec.ofNat 64 (Spec.Ffdh.primeChecks bits)) (by decide) (by decide)))

theorem phaseSelect_ok {s : State} {O : Addr} {bits : Nat}
    (hs : Scr s O 256) (hdi : s.gpr .rdi = O)
    (hb1 : 1 ≤ bits)
    (hb : word s.mem O (8 * oBits) = BitVec.ofNat 64 bits) (q : Bool) :
    WP isa (.block (([.mov .rdx (.mem (hdr oBits))] : List Instr) ++
      (if q then [.alu .sub .rdx (.imm 1)] else []))) s fun t =>
      t.gpr .rdx = BitVec.ofNat 64 (if q then bits - 1 else bits) ∧
      t.mem = s.mem ∧ Keep [.rdx] s t := by
  refine WP.mono (WP.keep [.rdx] (Q := fun t =>
    t.gpr .rdx = BitVec.ofNat 64 (if q then bits - 1 else bits) ∧ t.mem = s.mem) ?_
    (by cases q <;> rfl)) fun t ⟨⟨hd, hm⟩, k⟩ => ⟨hd, hm, k⟩
  have hl := hs.ld (d := 8 * oBits) (by decide)
  cases q
  · simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
    xrun [State.ea, hdr, hdi, hdrOff, hl, hb]
  · simp only [↓reduceIte, List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi, hdrOff, hl, hb]
    exact BitVec.ofNat_sub_ofNat_of_le (w := 64) bits 1 (by decide) hb1

theorem phaseHead_ok {s : State} {O : Addr} {bits : Nat}
    (hs : Scr s O 256) (hdi : s.gpr .rdi = O)
    (hb1 : 1 ≤ bits) (hb2 : bits < 2 ^ 32)
    (hb : word s.mem O (8 * oBits) = BitVec.ofNat 64 bits) (q : Bool) :
    WP isa (.block (phaseHead q)) s fun t =>
      t.mem = phaseMem s.mem O (if q then bits - 1 else bits) ∧
      t.gpr .rax = off O 256 ∧ Keep [.rax, .rcx, .rdx] s t := by
  unfold phaseHead
  rw [WP.block_append_iff]
  refine WP.mono (phaseSelect_ok hs hdi hb1 hb q) fun u ⟨hd, hm, k⟩ => ?_
  have hbu : (if q then bits - 1 else bits) < 2 ^ 32 := by cases q <;> simp_all <;> omega_arith
  refine WP.mono (phaseWidth_ok (hs.congr k.2.2) ((k.gpr (by decide)).trans hdi) hbu hd)
    fun t ⟨hmem, ha, k'⟩ => ?_
  exact ⟨by rw [hmem, hm], ha, (k.trans k').mono (by decide)⟩

theorem phaseMem_len (m : Mem) (O : Addr) (bits : Nat) :
    word (phaseMem m O bits) O (8 * oWitnessLen) = BitVec.ofNat 64 ((bits + 7) / 8) := by
  unfold phaseMem
  rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]

theorem phaseMem_bits (m : Mem) (O : Addr) (bits : Nat) :
    word (phaseMem m O bits) O (8 * oWitnessBits) = BitVec.ofNat 64 bits := by
  unfold phaseMem
  rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
    hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]

theorem phaseMem_checks (m : Mem) (O : Addr) (bits : Nat) :
    word (phaseMem m O bits) O (8 * oChecks) = BitVec.ofNat 64 (Spec.Ffdh.primeChecks bits) := by
  unfold phaseMem
  exact word_writeW_self _ _ _ _

def phaseRanges : List (Nat × Nat) :=
  [(8 * oWitnessBits, 24)] ++ [(8 * oInner, 8), (256, 8 * 17)]

theorem phaseSetup_ok {s : State} {O : Addr} {Z bits : Nat}
    (hs : Scr s O Z) (hdi : s.gpr .rdi = O)
    (hb1 : 1 ≤ bits) (hb2 : bits < 2 ^ 32)
    (hb : word s.mem O (8 * oBits) = BitVec.ofNat 64 bits) (q : Bool)
    (hz : 256 + slot (wsWords (((if q then bits - 1 else bits) + 7) / 8)) 8 ≤ Z) :
    WP isa (phaseSetup q) s fun t => ∃ mi,
      Good t (off O 256) (Z - 256) (wsWords (((if q then bits - 1 else bits) + 7) / 8)) mi ∧
      word t.mem (off O 256) (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = O ∧
      word t.mem O (8 * oInner) = off O 256 ∧
      word t.mem O (8 * oWitnessBits) = BitVec.ofNat 64 (if q then bits - 1 else bits) ∧
      word t.mem O (8 * oWitnessLen) = BitVec.ofNat 64 (((if q then bits - 1 else bits) + 7) / 8) ∧
      word t.mem O (8 * oChecks) = BitVec.ofNat 64 (Spec.Ffdh.primeChecks (if q then bits - 1 else bits)) ∧
      Frm O phaseRanges s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  let b := if q then bits - 1 else bits
  let len := (b + 7) / 8
  let w := wsWords len
  have hz256 : 256 ≤ Z := by omega_arith
  have hs256 : Scr s O 256 := by
    simpa [off] using hs.sub (o := 0) (n := 256) (by omega_arith) (by decide)
  unfold phaseSetup
  refine WP.seq (WP.mono (phaseHead_ok hs256 hdi hb1 hb2 hb q) fun u ⟨hm, ha, k⟩ => ?_)
  have hf : Frm O [(8 * oWitnessBits, 24)] s.mem u.mem := by rw [hm]; exact phaseMem_frame _ _ _
  have hu : Scr u O Z := hs.congr k.2.2
  have hlen : word u.mem O (8 * oWitnessLen) = BitVec.ofNat 64 len := by
    rw [hm]; exact phaseMem_len _ _ _
  have hlen32 : len < 2 ^ 32 := by
    have hl : b ≤ bits := by dsimp [b]; cases q <;> simp
    dsimp only [len]
    omega_arith
  refine WP.seq (WP.mono (wsNew_ok hu ((k.gpr (by decide)).trans hdi) ha
    (by decide : oInner < 32) (by decide : oWitnessLen < 32) (by decide) hlen hlen32 (by decide) hz)
    fun v ⟨hinner, hlink, hw, harr, hd, hf', k'⟩ => ?_)
  have hv : Scr v O Z := hu.congr k'.2.2
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off O 256 ∧ t.mem = v.mem)
    (by xrun [State.ea, hdr, hd, hdrOff, hv.ld (d := 8 * oInner) (by unfold oInner; omega_arith), hinner]) rfl)
    fun t ⟨⟨hdt, hmt⟩, kt⟩ => ?_
  have hst : Scr t (off O 256) (Z - 256) :=
    (hv.congr kt.2.2).sub (by omega_arith) (by unfold slot VG.Impl.Bignum.hdrBytes at hz; omega_arith)
  have hhead : ∀ j < 18, word v.mem O (8 * j) = word u.mem O (8 * j) := by
    intro j hj
    apply hf'.word_eq
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · left; change 8 * j + 8 ≤ 160; omega_arith
      · left; omega_arith
    · omega_arith
  refine ⟨word t.mem (off O 256) (8 * sMinv), ⟨hst, hdt, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    ((k.trans k').trans kt).mono (by decide)⟩
  · apply hdr_any
    · rw [hmt]; exact hw
    · intro j hj; rw [hmt]; exact harr j hj
  · rw [hmt]; exact hlink
  · rw [hmt]; exact hinner
  · rw [hmt, hhead _ (by decide), hm]; exact phaseMem_bits _ _ _
  · rw [hmt, hhead _ (by decide), hm]; exact phaseMem_len _ _ _
  · rw [hmt, hhead _ (by decide), hm]; exact phaseMem_checks _ _ _
  · rw [hmt]
    exact hf.append hf'

end VG.Proof.Ffdh.X86_64.ParameterCandidate
