module
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Ffdh.X86_64.Checks
public import VerifiedGarbage.Proof.Ffdh.X86_64.Ws

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup

/-! # FFDH on x86-64: workspace switches and Boolean branches -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (leave)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem enter_ok {s : State} {B : Addr} {Z w : Nat} (h : Outer s B Z w)
    (hWs : word s.mem B (8 * sWs) = off B (inner w)) :
    WP isa (.block [enter]) s fun t => t.gpr .rdi = off B (inner w) ∧ t.mem = s.mem ∧ Keep [.rdi] s t := by
  exact WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B (inner w) ∧ t.mem = s.mem)
    (by unfold enter; xrun [State.ea, hdr, h.rdi, hdrOff, h.ld (show sWs < 32 by decide), hWs]) rfl)
    fun _ ⟨h, k⟩ => ⟨h.1, h.2, k⟩

theorem leave_ok {s : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64}
    (hc : SubCtx s B Z o w wx mi) :
    WP isa (.block [leave]) s fun t => t.gpr .rdi = B ∧ t.mem = s.mem ∧ Keep [.rdi] s t := by
  have hL := hdr_lt_slot wx 8 (show VG.Impl.Rsa.X86_64.Crt.sLink < 32 by decide)
  exact WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s.mem)
    (by unfold leave; xrun [State.ea, hdr, hc.rdi, hdrOff, hc.good.scr.ld hL, hc.link]) rfl)
    fun _ ⟨h, k⟩ => ⟨h.1, h.2, k⟩

theorem ret_ok (s : State) {r : Nat} (hr : r < 2 ^ 32) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.ret r) s fun t => t.gpr .rax = BitVec.ofNat 64 r ∧
      t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 r ∧ t.mem = s.mem)
    (by unfold VG.Impl.Ffdh.X86_64.Domain.ret; xrun
        [show (BitVec.ofNat 32 r).setWidth 64 = BitVec.ofNat 64 r from by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
          omega]) rfl) fun _ ⟨h, k⟩ => ⟨h.1, h.2, k⟩

/-- Testing a Boolean preserves every register, memory and permissions. -/
theorem test_bit_ok {s : State} {P : Prop} [Decidable P] (hp : s.gpr .rax = bit P) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s fun t =>
      t.zf = some (!decide P) ∧ t.mem = s.mem ∧ Keep [] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (!decide P) ∧
      t.mem = s.mem ∧ t.gpr .rax = s.gpr .rax)
    (by xrun [hp]; by_cases h : P <;> simp [bit, h]) rfl) fun t ⟨⟨hz, hm, hax⟩, k⟩ => ?_
  exact ⟨hz, hm, ⟨fun r _ => by
    by_cases h : r = .rax
    · subst h; exact hax
    · exact k.gpr (by simpa using h), k.2⟩⟩

/-- Branch on a Boolean, exposing the unchanged data to either continuation. -/
theorem branchZero_ok {s : State} {P : Prop} [Decidable P] {th el : Prog isa} {Q : State → Prop}
    (hp : s.gpr .rax = bit P)
    (ht : ∀ t, t.mem = s.mem → Keep [] s t → ¬P → WP isa th t Q)
    (he : ∀ t, t.mem = s.mem → Keep [] s t → P → WP isa el t Q) :
    WP isa (branchZero th el) s Q := by
  refine WP.seq (WP.mono (test_bit_ok hp) fun t ⟨hz, hm, k⟩ => ?_)
  refine WP.ite (!decide P) (by simp [eval, hz]) (fun h => ht t hm k (by simpa using h))
    (fun h => he t hm k (by simpa using h))

/-- Test whether the packed domain contains a subgroup order. -/
theorem qTest_ok {s : State} {B : Addr} {Z dl k : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : 256 ≤ Z)
    (hdl : word s.mem B (8 * sDomLen) = BitVec.ofNat 64 dl)
    (hk : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hdk : 2 * k ≤ dl) (hdl32 : dl < 2 ^ 32) :
    WP isa (.block qTest) s fun t => t.gpr .rax = BitVec.ofNat 64 (dl - 2 * k) ∧
      t.zf = some (decide (dl = 2 * k)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have e : BitVec.ofNat 64 dl - BitVec.ofNat 64 k - BitVec.ofNat 64 k = BitVec.ofNat 64 (dl - 2 * k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hz : (BitVec.ofNat 64 (dl - 2 * k) == 0) = decide (dl = 2 * k) := by
    rw [ofNat_beq_zero (by omega)]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    omega
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (dl - 2 * k) ∧
      t.zf = some (decide (dl = 2 * k)) ∧ t.mem = s.mem)
    (by unfold qTest; xrun [State.ea, hdr, hdi, hdrOff,
      hs.ld (d := 8 * sDomLen) (by change 144 ≤ Z; omega),
      hs.ld (d := 8 * sK) (by change 152 ≤ Z; omega), hdl, hk, e, hz]) rfl)
    fun _ ⟨h, K⟩ => ⟨h.1, h.2.1, h.2.2, K⟩

/-- Leave the inner workspace before testing q's presence. -/
theorem leaveQ_ok {s : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} {dl k : Nat}
    (hc : SubCtx s B Z o w wx mi)
    (hdl : word s.mem B (8 * sDomLen) = BitVec.ofNat 64 dl)
    (hk : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hdk : 2 * k ≤ dl) (hdl32 : dl < 2 ^ 32) :
    WP isa (.block (leave :: qTest)) s fun t => t.gpr .rdi = B ∧
      t.gpr .rax = BitVec.ofNat 64 (dl - 2 * k) ∧ t.zf = some (decide (dl = 2 * k)) ∧
      t.mem = s.mem ∧ Keep [.rdi, .rax] s t := by
  rw [show leave :: qTest = ([leave] : List Instr) ++ qTest from rfl, WP.block_append_iff]
  refine WP.mono (leave_ok hc) fun s₁ ⟨hdi, hm, k₁⟩ => ?_
  have hlo := hc.lo
  have hi := hc.hi
  refine WP.mono (qTest_ok (hc.scr.congr k₁.2.2) hdi
    (by unfold slot hdrBytes at hlo; omega) (by rw [hm]; exact hdl) (by rw [hm]; exact hk) hdk hdl32)
    fun t ⟨hax, hz, hm', k₂⟩ =>
      ⟨(k₂.gpr (by decide)).trans hdi, hax, hz, hm'.trans hm, (k₁.trans k₂).mono (by decide)⟩

/-- The range comparison with its branch condition in ZF. -/
theorem rangeTest_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    {a : Nat} (ha : a < 8) (haT : a ≠ aTmp) (hone : wv s.mem B (slot w aOne) w = 1) :
    let P := 1 < wv s.mem B (slot w a) w ∧
      2 * (wv s.mem B (slot w a) w / 2) + 1 < wv s.mem B (slot w aN) w
    WP isa (seqs (rangeTest a)) s fun t =>
      t.gpr .rax = bit P ∧ t.zf = some (!decide P) ∧ word t.mem B (8 * sF) = t.gpr .rax ∧
      Frm B [(slot w aTmp, 8 * w), (8 * sF, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  intro P
  unfold rangeTest
  refine wp_seqs_append (by simp [range, gt1, ltArr, cmpArr]) (by simp) ?_
  refine WP.mono (range_ok hg hZ hw hw' ha haT hone) fun s₁ ⟨hax, hF, f, k₁⟩ => ?_
  simp only [seqs]
  refine WP.mono (test_bit_ok hax) fun t ⟨hz, hm, k₂⟩ => ?_
  have hax' : t.gpr .rax = s₁.gpr .rax := k₂.gpr (by decide)
  exact ⟨hax'.trans hax, hz, by rw [hm, hax']; exact hF, by rw [hm]; exact f,
    (k₁.trans k₂).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64
