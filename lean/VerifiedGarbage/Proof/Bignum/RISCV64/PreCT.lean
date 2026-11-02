module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PreDefs
public import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreDefs
meta import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreSave
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Bignum.RISCV64.PreWrite
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreSave
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreWrite
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# The precomputed values of an RSA modulus on RISC-V: constant time

As on PPC64LE (`Proof/Bignum/PPC64LE/PreCT.lean`): `n` is public, but the
taint analysis treats memory as secret, so the bytes of `n` that `check`
loads, and its result, are secret to it. Two runs are related by `Two` at
each step, both satisfying the same predicate for the same public data `PD`
(which holds `n`'s bytes): after `check1` it fixes the first byte, which
`check2` branches on, and after `check2` whether `n` is valid, which the
final branch tests (`RelCT.ite`). Each piece is checked by the taint
analysis from the registers the predicate fixes.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pre

open VG VG.RISCV64 VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Precompute
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64 (Scr r2_ok r2Regs loadN_ok check1_ok check2_ok write_ok zeroPre_ok)

/-! ## Relating two runs -/

/-- Both runs satisfy `Φ a`, for the same `a`, with the same stack pointer. -/
def Two {α : Type} (Φ : α → State → Prop) (s₁ s₂ : State) : Prop := ∃ a, Φ a s₁ ∧ Φ a s₂ ∧ s₁.sp = s₂.sp

theorem two_post {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨a, h₁, h₂, hsp⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw a s₁ h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw a s₂ h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, a, y₁, y₂, by rw [(Exec.rdwr e₁).2.2, (Exec.rdwr e₂).2.2, hsp]⟩

/-- `Φ a` fixes the registers `rs`. -/
def Pins {α : Type} (Φ : α → State → Prop) (rs : List Reg) : Prop :=
  ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem two_taint {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨hsp, fun r hr => hpin a _ _ h₁ h₂ r (Taint.mem_ofRegs.mp hr)⟩) h

/-! ## The states of a run -/

/-- The data of a state on entry. -/
def dataOf (s : State) : PD :=
  ⟨s.gpr .a0, s.gpr .a2, s.gpr .a4, (s.gpr .a3).toNat, (s.gpr .a5).toNat * 8,
    Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat⟩

theorem getD_of_lt {l : List Byte} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- On entry. -/
def C0 (d : PD) (s : State) : Prop := fnContract.pre s ∧ dataOf s = d

/-- After `loadN`. -/
def C2 (d : PD) (s : State) : Prop :=
  Base d s ∧ wordsVal s.mem d.S (slot d.w 0) d.w = Spec.Rsa.os2ip d.nb ∧
    (∀ i < d.k, InRegions (s.rd ++ s.wr) (off d.N i) 1) ∧
    ∀ i (h : i < d.nb.length), s.mem (off d.N i) = d.nb[i]

/-- After `check1`. -/
def C3 (d : PD) (s : State) : Prop :=
  Base d s ∧ wordsVal s.mem d.S (slot d.w 0) d.w = Spec.Rsa.os2ip d.nb ∧
    s.gpr .t4 = BitVec.ofNat 64 (d.nb.getD 0 0).toNat ∧
    (s.gpr .s0 = 0 ↔ (d.nb.getD (d.k - 1) 0).toNat % 2 = 1)

/-- After `check2`. -/
def C4 (d : PD) (s : State) : Prop :=
  Base d s ∧ wordsVal s.mem d.S (slot d.w 0) d.w = Spec.Rsa.os2ip d.nb ∧
    (s.gpr .s0 = 0 ↔ Spec.Rsa.modulusValid (Spec.Rsa.os2ip d.nb) d.k = true)

/-- After the branch. -/
def C5 (d : PD) (s : State) : Prop := s.gpr .s6 = d.S

theorem base_pins {d : PD} {s₁ s₂ : State} (h₁ : Base d s₁) (h₂ : Base d s₂) :
    ∀ r ∈ baseRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.s5, h₂.s5]
  · rw [h₁.a7, h₂.a7]
  · rw [h₁.a2, h₂.a2]
  · rw [h₁.a5, h₂.a5]
  · rw [h₁.a6, h₂.a6]
  · rw [h₁.t0, h₂.t0]
  · rw [h₁.s6, h₂.s6]
  · rw [h₁.s8, h₂.s8]
  · rw [h₁.s7, h₂.s7]

theorem pins_C0 : Pins C0 [.a0, .a2, .a3, .a4] := by
  rintro d s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [show s₁.gpr .a0 = d.P from congrArg PD.P h₁, show s₂.gpr .a0 = d.P from congrArg PD.P h₂]
  · rw [show s₁.gpr .a2 = d.N from congrArg PD.N h₁, show s₂.gpr .a2 = d.N from congrArg PD.N h₂]
  · exact BitVec.eq_of_toNat_eq ((congrArg PD.k h₁).trans (congrArg PD.k h₂).symm)
  · rw [show s₁.gpr .a4 = d.S from congrArg PD.S h₁, show s₂.gpr .a4 = d.S from congrArg PD.S h₂]

theorem pins_C1 : Pins C1 baseRegs := fun _ _ _ h₁ h₂ => base_pins h₁.base h₂.base

theorem pins_C2 : Pins C2 baseRegs := fun _ _ _ h₁ h₂ => base_pins h₁.1 h₂.1

theorem pins_C3 : Pins C3 (baseRegs ++ ([.t4] : List Reg)) := by
  intro d s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact base_pins h₁.1 h₂.1 r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    rw [h₁.2.2.1, h₂.2.2.1]

theorem pins_C4 {Φ : PD → State → Prop} (h : ∀ d s, Φ d s → C4 d s) : Pins Φ baseRegs :=
  fun _ _ _ h₁ h₂ => base_pins (h _ _ h₁).1 (h _ _ h₂).1

theorem pins_C5 : Pins C5 [.s6] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [h₁, h₂]

/-! ## The steps, by correctness -/

/-- The saved words are in the working space. -/
theorem ct_sav_in {S : Addr} {Z : Nat} (hZ : 200 ≤ Z) {i : Nat} (hi : i < 9) :
    (⟨S, Z⟩ : Region).Contains (off (savW S) (8 * i)) 8 := by
  rw [off, Offset.add_add]
  exact Offset.contains_base S (by omega_arith) (by omega_arith)

theorem T01 {d : PD} {s : State} (h : C0 d s) : WP isa (.block (Precompute.save ++ setup)) s (C1 d) := by
  obtain ⟨⟨hrd, hwr, dPN, dPS, dNS, nwP, nwN, nwS, ⟨hk, hk'⟩, hpl, hsl, alP, alS⟩, rfl⟩ := h
  simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, Spec.Rsa.publicScratchWords] at hpl hsl
  have hs : Scr s (s.gpr .a4) ((s.gpr .a5).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) nwS alS
  have hin : ∀ i < 9, InRegions s.wr (off (savW (s.gpr .a4)) (8 * i)) 8 := fun i hi =>
    ⟨scrR s, by rw [hwr]; simp, ct_sav_in (by omega_arith) hi⟩
  have hal : ∀ i < 9, (off (savW (s.gpr .a4)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [show off (savW (s.gpr .a4)) (8 * i) = off (s.gpr .a4) (128 + 8 * i) by
      rw [off, off, Offset.add_add]]
    exact hs.al8 (by omega_arith) (by omega_arith)
  refine WP.block_append (WP.mono (save_ok s hin hal) fun s₁ hS => ?_)
  have hk1 := hS.keep
  have e3 : s.gpr .a3 = BitVec.ofNat 64 (s.gpr .a3).toNat := BitVec.eq_of_toNat_eq (by simp)
  refine WP.mono (setup_ok (P := s.gpr .a0) (N := s.gpr .a2) (k := (s.gpr .a3).toNat) (hs.congr hk1.2.2)
    (hk1.gpr (by decide)) (hk1.gpr (by decide)) ((hk1.gpr (by decide)).trans e3) hS.s6 (by omega_arith)
    hk' (by omega_arith)) fun s₂ ⟨⟨j5, j7, j8, j0, ja7, ja2, ja5, ja6, jm⟩, k₂⟩ => ?_
  have k12 := hk1.trans k₂
  have hlen : 16 * (((s.gpr .a3).toNat + 7) / 8) = (s.gpr .a1).toNat * 8 := by omega_arith
  have hmem : (⟨s.gpr .a0, 16 * (((s.gpr .a3).toNat + 7) / 8)⟩ : Region) ∈ s₂.wr := by
    rw [k12.2.2, hwr, hlen]; simp
  -- Only the working space changed.
  have fr₂ : Frame [scrR s] s.mem s₂.mem := by
    rw [jm]
    refine (hS.frame.sub fun r hr => ⟨scrR s, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by simp; omega_arith) (by decide))
    simp only [List.mem_singleton] at hr
    subst hr
    exact Offset.sub_base _ (by omega_arith)
  simp only [dataOf]
  refine ⟨⟨hs.congr k12.2.2, Scr.of_mem hmem (by dsimp only [PD.w]; omega_arith) alP, hk, hk',
    by dsimp only [PD.w]; unfold slot hdrBytes; omega_arith,
    fun x hx => ?_, VG.Proof.Bignum.bytesAt_length _ _ _, j5, ja7, ja2, ja5, ja6, j0,
    (k₂.gpr (by decide)).trans hS.s6, j8, j7⟩,
    fun i hi => by
      dsimp only at hi ⊢
      exact ⟨nR s, by rw [k12.2.1, hrd]; simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun i hi x hx e => ?_, fun i hi => ?_⟩
  · dsimp only [PD.w] at hx ⊢
    by_contra hc
    exact dPS x (by simp only [Region.Contains]; simp only [ofs] at hc; omega_arith)
      (by simp only [Region.Contains]; simp only [ofs] at hx; omega_arith)
  · dsimp only at hi hx
    subst e
    exact dNS _ (Offset.contains_base (d := i) _ (by omega_arith) (by omega_arith))
      (by simp only [Region.Contains]; simp only [ofs, off] at hx; omega_arith)
  · dsimp only at hi ⊢
    simp only [VG.Proof.Bignum.bytesAt_length] at hi
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact fr₂.bytes (R := nR s) (by simpa using dNS) (by show (s.gpr .a3).toNat ≤ 2 ^ 64; omega_arith) hi

theorem T12 {d : PD} {s : State} (h : C1 d s) : WP isa loadN s (C2 d) := by
  have hb := h.base
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hw1 : 8 ≤ d.w := by have := hb.k64; omega
  have e0 : slot d.w 0 = hdrBytes := by simp [slot]
  have e8 : slot d.w 8 = hdrBytes + 8 * (8 * (d.w + 2)) := rfl
  have hh : hdrBytes = 256 := rfl
  have hZ := hb.hZ
  refine WP.mono (loadN_ok (dA := slot d.w 0) hb.scr hb.a7 (by rw [hb.s7]; simp) hb.s8 hb.t0
    (by have := hb.k64; omega) (by omega) (by have := hb.k1024; omega) (by omega) (by omega) (by omega)
    h.rd h.sep)
    fun t ⟨hv, out, k⟩ => ⟨hb.keep k, by rw [hv, h.bytesAt], by rw [k.2.1, k.2.2]; exact h.rd, fun i hi => ?_⟩
  rw [← h.bytes i hi]
  refine out _ (Or.inr ?_)
  have := h.sep i (by rw [← hb.len]; exact hi) (off d.N i)
  simp only [Mont.ofs, VG.Proof.Bignum.ofs] at this ⊢
  by_contra hc; exact this (by omega) rfl

theorem T23 {d : PD} {s : State} (h : C2 d s) : WP isa (.block check1) s (C3 d) := by
  obtain ⟨hb, hv, hrd, hby⟩ := h
  have hl := hb.len
  have hk := hb.k64
  refine WP.mono (check1_ok (N := d.N) (nb := d.nb) (by rw [hb.s7]; simp) hb.s8 hk hl hrd
    fun i hi => hby i (by omega)) fun t ⟨⟨i0, i4, im⟩, k⟩ =>
    ⟨hb.keep k, by rw [im]; exact hv, by rw [i4, getD_of_lt (by omega)],
      by rw [i0, getD_of_lt (by omega)]⟩

theorem T34 {d : PD} {s : State} (h : C3 d s) : WP isa check2 s (C4 d) := by
  obtain ⟨hb, hv, h4, h0⟩ := h
  have hl := hb.len
  have hk := hb.k64
  refine WP.mono (check2_ok (nb := d.nb) hb.s8 hk hb.k1024 hl (by rw [h0, getD_of_lt (by omega)])
    (by rw [h4, getD_of_lt (by omega)])) fun t ⟨a, m, k⟩ =>
    ⟨hb.keep k, by rw [m]; exact hv, a⟩

theorem TA {d : PD} {s : State} (h : C4 d s ∧ s.gpr .s0 = 0) :
    WP isa (.seq r2 (.seq write (.block [.li .a0 1]))) s (C5 d) := by
  obtain ⟨⟨hb, hv, h0⟩, hz⟩ := h
  have hval := h0.mp hz
  have hf := VG.Proof.Bignum.valid_facts hval hb.k64
  have hnw := hb.scr.nowrap
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hw1 : 8 ≤ d.w := by have := hb.k64; omega
  have hw' : d.w < 2 ^ 31 := by have := hb.k1024; omega
  have e : ∀ j, slot d.w j = hdrBytes + j * (8 * (d.w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hZ := hb.hZ
  rw [← hwd] at hf
  refine WP.seq (WP.mono (r2_ok hb.scr hb.a2 hb.a5 hb.a6 hb.a7 hb.t0 (by omega) hw' hZ
    (by rw [hv]; exact hf.2.2) (by rw [hv]; exact hf.1)) fun s₃ ⟨_, _, k₃⟩ => ?_)
  have g : ∀ r ∈ [Reg.s5, .a7, .a2, .t0, .s6], s₃.gpr r = s.gpr r := fun r hr =>
    k₃.gpr (by revert r hr; decide)
  refine WP.seq (WP.mono (write_ok (P := d.P) (dN := slot d.w 0) (dX := slot d.w 1) (hb.scr.congr k₃.2.2)
    (hb.pre.congr k₃.2.2) (by rw [g .s5 (by decide), hb.s5]; simp) (by rw [g .a7 (by decide), hb.a7])
    (by rw [g .a2 (by decide), hb.a2]) (by rw [g .t0 (by decide), hb.t0]) (by omega) hw'
    (by simp [slot, hdrBytes]) (by simp only [slot, hdrBytes]; omega) (by omega) (by omega)
    (Nat.le_refl _) hb.hPS) fun s₄ ⟨_, k₄⟩ => ?_)
  refine WP.mono (WP.keep [.a0] (Q := fun _ => True) (by brun [exec_li]; exact ⟨_, rfl⟩) (by rfl) (by rfl))
    fun t ⟨_, k₅⟩ => ?_
  show t.gpr .s6 = d.S
  rw [k₅.gpr (by decide), k₄.gpr (by decide), g .s6 (by decide), hb.s6]

theorem TB {d : PD} {s : State} (h : C4 d s ∧ s.gpr .s0 ≠ 0) :
    WP isa (.seq zeroPre (.block [.li .a0 0])) s (C5 d) := by
  obtain ⟨⟨hb, -, -⟩, -⟩ := h
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hw1 : 8 ≤ d.w := by have := hb.k64; omega
  have hw' : d.w < 2 ^ 31 := by have := hb.k1024; omega
  refine WP.seq (WP.mono (zeroPre_ok hb.pre (by rw [hb.s5]; simp) hb.t0 (by omega) hw' (Nat.le_refl _))
    fun s₃ ⟨_, k₃⟩ => ?_)
  refine WP.mono (WP.keep [.a0] (Q := fun _ => True) (by brun [exec_li]; exact ⟨_, rfl⟩) (by rfl) (by rfl))
    fun t ⟨_, k₄⟩ => ?_
  show t.gpr .s6 = d.S
  rw [k₄.gpr (by decide), k₃.gpr (by decide), hb.s6]

/-! ## Constant time -/

theorem fn_rel : RelCT isa (Two C0) precompute fun _ _ => True := by
  unfold precompute
  refine RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => T01 h)
    (RelCT.seq ?_ (two_taint _ pins_C5 (by taint_decide)))
  unfold core
  refine RelCT.seq (two_post (two_taint _ pins_C1 (by taint_decide)) fun _ _ h => T12 h)
    (RelCT.seq (R := Two C4) ?_ ?_)
  · unfold check
    exact RelCT.seq (two_post (two_taint _ pins_C2 (by taint_decide)) fun _ _ h => T23 h)
      (two_post (two_taint _ pins_C3 (by taint_decide)) fun _ _ h => T34 h)
  · refine RelCT.ite (fun s₁ s₂ ⟨d, h₁, h₂, _⟩ => ?_)
      (RelCT.mono (two_post (Φ := fun d s => C4 d s ∧ s.gpr .s0 = 0)
        (two_taint _ (pins_C4 fun _ _ h => h.1) (by taint_decide)) fun _ _ h => TA h)
        (fun s₁ s₂ ⟨⟨d, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
      (RelCT.mono (two_post (Φ := fun d s => C4 d s ∧ s.gpr .s0 ≠ 0)
        (two_taint _ (pins_C4 fun _ _ h => h.1) (by taint_decide)) fun _ _ h => TB h)
        (fun s₁ s₂ ⟨⟨d, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
    · rw [Steps.eval_zero, Steps.eval_zero]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h₁.2.2, h₂.2.2]
    · rw [Steps.eval_zero] at hc
      have h0 : s₁.gpr .s0 = 0 := by simpa using hc
      exact ⟨d, ⟨h₁, h0⟩, ⟨h₂, h₂.2.2.mpr (h₁.2.2.mp h0)⟩, hsp⟩
    · rw [Steps.eval_zero] at hc
      have h0 : s₁.gpr .s0 ≠ 0 := by simpa using hc
      exact ⟨d, ⟨h₁, h0⟩, ⟨h₂, fun e => h0 (h₁.2.2.mpr (h₂.2.2.mp e))⟩, hsp⟩

theorem fn_ct : ConstantTime isa fnContract.pre fnContract.pub precompute :=
  RelCT.constantTime (fn_rel.mono (fun s t ⟨hs, ht, hsp, hb, h0, h1, h2, h3, h4, h5⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [dataOf]
      rw [(List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp hb, h0, h2, h3, h4, h5]⟩,
      hsp⟩) fun _ _ h => h)

end VG.Proof.Bignum.RISCV64.Pre
