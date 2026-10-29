module
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Core
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.RsaKeyGen.Gcd

/-!
# A candidate on x86-64: Miller–Rabin's table entry

The selection of `T_d` into `aXm` (`d` in `kG`) by two passes of the CRT's
gathering (`Proof/Bignum/X86_64/CrtSel.lean`), over the entries `0` to `7`
and `8` to `15` (the arrays `8` to `23`): `mrSel_ok`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen

theorem scr_mono {s : State} {B : Addr} {Z Z' : Nat} (h : Scr s B Z) (hz : Z' ≤ Z) : Scr s B Z' :=
  let ⟨B₀, o, L, h1, h2, h3, h4⟩ := h.wr
  ⟨⟨B₀, o, L, h1, h2, by omega_using [hz, h3], h4⟩, by have := h.nowrap; omega_using [hz, this]⟩

theorem aT_eq : Crt.aT = aXm := rfl

/-- The first pass's registers. -/
theorem selRegs_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hw' : w < 2 ^ 30) :
    WP isa (.block selRegs) s fun t =>
      t.gpr .r15 = BitVec.ofNat 64 (8 * 0) ∧ t.gpr .rcx = off B (slot w (8 + 8 * 0)) ∧
      t.gpr .r11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r13 = BitVec.ofNat 64 (2 * ((w + 1) / 2)) ∧
      t.gpr .rbx = off B (slot w aXm) ∧ t.mem = s.mem ∧
      Keep [.rax, .r15, .rcx, .r12, .r11, .r13, .rbx] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  have h11 : BitVec.ofNat 64 w + 2 + (BitVec.ofNat 64 w + 2) + (BitVec.ofNat 64 w + 2 + (BitVec.ofNat 64 w + 2)) +
      (BitVec.ofNat 64 w + 2 + (BitVec.ofNat 64 w + 2) + (BitVec.ofNat 64 w + 2 + (BitVec.ofNat 64 w + 2))) =
      BitVec.ofNat 64 (8 * (w + 2)) := by
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl]
    simp only [BitVec.ofNat_add_ofNat]
    congr 1
    omega_using []
  have h13 : (BitVec.ofNat 64 w + 1) >>> 1 + (BitVec.ofNat 64 w + 1) >>> 1 = BitVec.ofNat 64 (2 * ((w + 1) / 2)) := by
    rw [ofNat_add_one]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    omega_using []
  unfold selRegs
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r15, .r12, .r11, .r13, .rbx] (Q := fun t =>
      t.gpr .r15 = BitVec.ofNat 64 (8 * 0) ∧ t.gpr .r11 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      t.gpr .r13 = BitVec.ofNat 64 (2 * ((w + 1) / 2)) ∧ t.gpr .rbx = off B (slot w aXm) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aXm) (by decide), hg.hdr.hw,
      hg.hdr.harr aXm (by decide), h11, h13]) rfl) fun s₁ ⟨⟨h15₁, h11₁, h13₁, hbx₁, hm₁⟩, k₁⟩ => ?_
  have hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine WP.mono (extBase_ok hg₁ hZ (by omega_using [hw']) (j := aT0) (by decide) (r := .rcx) (by decide)
    rfl rfl) fun t ⟨hcx, hm, k⟩ => ⟨?_, hcx, ?_, ?_, ?_, by rw [hm, hm₁], (k₁.trans k).mono (by decide)⟩
  · exact (k.gpr (by decide)).trans h15₁
  · exact (k.gpr (by decide)).trans h11₁
  · exact (k.gpr (by decide)).trans h13₁
  · exact (k.gpr (by decide)).trans hbx₁

/-- The second pass's registers, from the first's. -/
theorem selNext_ok {s : State} {B : Addr} {w : Nat} (h11 : s.gpr .r11 = BitVec.ofNat 64 (8 * (w + 2)))
    (hcx : s.gpr .rcx = off B (slot w (8 + 8 * 0))) :
    WP isa (.block selNext) s fun t =>
      t.gpr .r15 = BitVec.ofNat 64 (8 * 1) ∧ t.gpr .rcx = off B (slot w (8 + 8 * 1)) ∧ t.mem = s.mem ∧
      Keep [.rax, .r15, .rcx] s t := by
  have e : off B (slot w (8 + 8 * 0)) + (BitVec.ofNat 64 (8 * (w + 2)) + BitVec.ofNat 64 (8 * (w + 2)) +
      (BitVec.ofNat 64 (8 * (w + 2)) + BitVec.ofNat 64 (8 * (w + 2))) + (BitVec.ofNat 64 (8 * (w + 2)) +
      BitVec.ofNat 64 (8 * (w + 2)) + (BitVec.ofNat 64 (8 * (w + 2)) + BitVec.ofNat 64 (8 * (w + 2))))) =
      off B (slot w (8 + 8 * 1)) := by
    simp only [BitVec.ofNat_add_ofNat, off, BitVec.add_assoc]
    congr 2
    rw [show (8 : Nat) + 8 * 1 = 8 + 8 from rfl, slot_add_mul w 8 8, slot_add_mul w 8 (8 * 0)]; omega_using []
  refine WP.mono (WP.keep [.rax, .r15, .rcx] (Q := fun t => t.gpr .r15 = BitVec.ofNat 64 (8 * 1) ∧
      t.gpr .rcx = off B (slot w (8 + 8 * 1)) ∧ t.mem = s.mem) (by
    unfold selNext
    xrun [h11, hcx, e]) rfl) fun t ⟨⟨h15, hcx', hm⟩, k⟩ => ⟨h15, hcx', hm, k⟩

/-- The mask of `k + j = d` in both quadwords of `x`, `d` in `kG` and `k` in
`r15`. -/
theorem selMask_ok {t : State} {B : Addr} {k j v : Nat} (hdi : t.gpr .rdi = B)
    (hld : InRegions (t.rd ++ t.wr) (off B (8 * kG)) 8) (hN : word t.mem B (8 * kG) = BitVec.ofNat 64 v)
    (h15 : t.gpr .r15 = BitVec.ofNat 64 k) (hk : k < 16) (hj : j < 8) (hv : v < 16) (x : XReg) :
    WP isa (.block (Crt.selMask (BitVec.ofNat 32 j) (.mem (hdr kG)) x)) t fun t' =>
      (∀ q < 2, q128 (t'.xmm x) q = mask (decide (k + j = v))) ∧ (∀ y, y ≠ x → t'.xmm y = t.xmm y) ∧
      t'.mem = t.mem ∧ Keep [.r14] t t' := by
  rw [show Crt.selMask (BitVec.ofNat 32 j) (.mem (hdr kG)) x =
    ([.mov .r14 (.reg .r15), .alu .add .r14 (.imm (BitVec.ofNat 32 j)), .alu .xor .r14 (.mem (hdr kG)),
      .alu .cmp .r14 (.imm 1), .alu .sbb .r14 (.reg .r14)] : List Instr) ++
    ([.xop (.movq x .r14), .xop (.bin .punpcklqdq x x)] : List Instr) from rfl]
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r14] (Q := fun t' =>
      (∃ b : Bool, b = decide (BitVec.ofNat 64 k + BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 v = 0) ∧
        t'.gpr .r14 = mask b) ∧ t'.mem = t.mem ∧ t'.xmm = t.xmm) (by
    xrun [State.ea, hdr, hdi, hdrOff, hld, hN, h15, sx_ofNat (show j < 2 ^ 31 by omega_using [hj])]
    exact ⟨⟨_, decide_lt_one _, rfl⟩, rfl⟩) rfl) fun t₁ ⟨⟨⟨b, hb, h14⟩, hm, hx⟩, k₁⟩ => ?_)
  refine WP.mono (dupX_ok x) fun t' ⟨hd, hy, hg, hm', hrd, hwr⟩ => ⟨fun q hq => ?_,
    fun y hy' => by rw [hy y hy', hx], by rw [hm', hm], ?_⟩
  · rw [hd q hq, h14, hb, BitVec.ofNat_add_ofNat]
    congr 1
    exact decide_eq_decide.mpr (xor_eq_zero_iff.trans (ofNat64_inj (by omega_using [hk, hj]) (by omega_using [hv])))
  · exact ⟨fun r hr => by rw [hg]; exact k₁.1 r hr, hrd.trans k₁.2.1, hwr.trans k₁.2.2⟩

/-- A pass's masks and bases, from its registers. -/
theorem selMasks_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    {p v : Nat} (hp : p < 2) (hv : v < 16) (hN : word s.mem B (8 * kG) = BitVec.ofNat 64 v)
    (h15 : s.gpr .r15 = BitVec.ofNat 64 (8 * p)) (hcx : s.gpr .rcx = off B (slot w (8 + 8 * p)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (8 * (w + 2))) (h13 : s.gpr .r13 = BitVec.ofNat 64 (2 * ((w + 1) / 2)))
    (hbx : s.gpr .rbx = off B (slot w aXm)) :
    WP isa (seqs selMasks) s fun t => GRegs B w p v t ∧ t.gpr .r14 = BitVec.ofNat 64 (2 * 0) ∧
      t.gpr .r11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem ∧ Keep mmRegs s t := by
  simp only [selMasks, seqs]
  have hld : ∀ s' : State, s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      InRegions (s'.rd ++ s'.wr) (off B (8 * kG)) 8 := fun s' _ hrd hwr => by
    rw [hrd, hwr]; exact hg.scr.ld (by have := hdr_lt_slot w 8 (show kG < 32 by decide); omega_using [hZ, this])
  have mstep : ∀ (s' : State) (j : Nat) (x : XReg), j < 8 → s'.gpr .rdi = B → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.gpr .r15 = BitVec.ofNat 64 (8 * p) →
      WP isa (.block (Crt.selMask (BitVec.ofNat 32 j) (.mem (hdr kG)) x)) s' fun s'' =>
        (∀ q < 2, q128 (s''.xmm x) q = mask (decide (8 * p + j = v))) ∧ (∀ y, y ≠ x → s''.xmm y = s'.xmm y) ∧
        s''.mem = s.mem ∧ s''.gpr .rdi = B ∧ s''.rd = s.rd ∧ s''.wr = s.wr ∧ s''.gpr .r15 = BitVec.ofNat 64 (8 * p) ∧
        Keep [.r14] s' s'' :=
    fun s' j x hj hdi hm hrd hwr h15' => WP.mono (selMask_ok hdi (hld s' hm hrd hwr) (by rw [hm]; exact hN) h15'
      (by omega_using [hp]) hj hv x) fun s'' ⟨hq, hy, hm', k⟩ =>
        ⟨hq, hy, hm'.trans hm, (k.gpr (by decide)).trans hdi, k.2.1.trans hrd, k.2.2.trans hwr,
          (k.gpr (by decide)).trans h15', k⟩
  refine WP.seq (WP.mono (mstep s 0 .xmm8 (by decide) hg.rdi rfl rfl rfl h15)
    fun s₀ ⟨q₀, y₀, m₀, d₀, r₀, w₀, f₀, k₀⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₀ 1 .xmm9 (by decide) d₀ m₀ r₀ w₀ f₀)
    fun s₁ ⟨q₁, y₁, m₁, d₁, r₁, w₁, f₁, k₁'⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₁ 2 .xmm10 (by decide) d₁ m₁ r₁ w₁ f₁)
    fun s₂ ⟨q₂, y₂, m₂, d₂, r₂, w₂, f₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₂ 3 .xmm11 (by decide) d₂ m₂ r₂ w₂ f₂)
    fun s₃ ⟨q₃, y₃, m₃, d₃, r₃, w₃, f₃, k₃⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₃ 4 .xmm12 (by decide) d₃ m₃ r₃ w₃ f₃)
    fun s₄ ⟨q₄, y₄, m₄, d₄, r₄, w₄, f₄, k₄⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₄ 5 .xmm13 (by decide) d₄ m₄ r₄ w₄ f₄)
    fun s₅ ⟨q₅, y₅, m₅, d₅, r₅, w₅, f₅, k₅⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₅ 6 .xmm14 (by decide) d₅ m₅ r₅ w₅ f₅)
    fun s₆ ⟨q₆, y₆, m₆, d₆, r₆, w₆, f₆, k₆⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₆ 7 .xmm15 (by decide) d₆ m₆ r₆ w₆ f₆)
    fun s₇ ⟨q₇, y₇, m₇, d₇, r₇, w₇, f₇, k₇⟩ => ?_)
  refine WP.seq (WP.mono (gKeep_ok f₇ hp) fun s₈ ⟨q₈, y₈, m₈, k₈⟩ => ?_)
  have kM := ((((((((k₀.trans k₁').trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k₈)
  have hcx₈ : s₈.gpr .rcx = off B (slot w (8 + 8 * p)) := (kM.gpr (by decide)).trans hcx
  have h11₈ : s₈.gpr .r11 = BitVec.ofNat 64 (8 * (w + 2)) := (kM.gpr (by decide)).trans h11
  refine WP.mono (gBases_ok hcx₈ h11₈) fun s₉ ⟨hb, h14, m₉, x₉, k₉⟩ => ?_
  have kA := kM.trans k₉
  have hG : GRegs B w p v s₉ := by
    refine ⟨hb, by rw [kA.gpr (by decide), aT_eq]; exact hbx, by rw [kA.gpr (by decide)]; exact h13,
      fun k hk q hq => ?_, fun q hq => by rw [x₉]; exact q₈ q hq⟩
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega_using [hk]
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show gX 0 = .xmm8 from rfl, x₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide), y₅ _ (by decide),
        y₄ _ (by decide), y₃ _ (by decide), y₂ _ (by decide), y₁ _ (by decide)]; exact q₀ q hq
    · rw [show gX 1 = .xmm9 from rfl, x₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide), y₅ _ (by decide),
        y₄ _ (by decide), y₃ _ (by decide), y₂ _ (by decide)]; exact q₁ q hq
    · rw [show gX 2 = .xmm10 from rfl, x₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide), y₅ _ (by decide),
        y₄ _ (by decide), y₃ _ (by decide)]; exact q₂ q hq
    · rw [show gX 3 = .xmm11 from rfl, x₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide), y₅ _ (by decide),
        y₄ _ (by decide)]; exact q₃ q hq
    · rw [show gX 4 = .xmm12 from rfl, x₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide), y₅ _ (by decide)]
      exact q₄ q hq
    · rw [show gX 5 = .xmm13 from rfl, x₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide)]; exact q₅ q hq
    · rw [show gX 6 = .xmm14 from rfl, x₉, y₈ _ (by decide), y₇ _ (by decide)]; exact q₆ q hq
    · rw [show gX 7 = .xmm15 from rfl, x₉, y₈ _ (by decide)]; exact q₇ q hq
  exact ⟨hG, h14, by rw [kA.gpr (by decide)]; exact h11, by rw [m₉, m₈, m₇], kA.mono (by decide)⟩

/-- A pass's loop, from its masks and bases: each pair of words of `aXm`
below `2 ⌈w / 2⌉` becomes `gval`; `rcx`, `r11`, `r13` and `rbx` kept. -/
theorem selLoop_ok' {s : State} {B : Addr} {Z w : Nat} {p v : Nat} (hs : Scr s B Z)
    (hZ : slot w 8 + tabBytes w ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 30) (hp : p < 2) (hG : GRegs B w p v s)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 (2 * 0)) :
    WP isa (.loop (seqs Crt.gatherBody) .ne) s fun t =>
      (∀ k < 2 * ((w + 1) / 2), word t.mem B (slot w aXm + 8 * k) = gval s.mem B w p v k) ∧
      Outside B (slot w aXm) (16 * ((w + 1) / 2)) s.mem t.mem ∧ (∀ r, r ≠ .r14 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr :=
  WP.mono (gLoop_ok (scr_mono hs hZ) hG hp h14 hw hw') fun t hI => ⟨fun k hk => by
    have := hI.val k hk
    rw [aT_eq] at this
    rw [this]
    simp only [show k < 2 * ((w + 1) / 2) from hk, ↓reduceIte], by rw [← aT_eq]; exact hI.out, hI.gpr, hI.rd, hI.wr⟩

theorem mrSel_eq : mrSel = ([seqs (.block selRegs :: selMasks)] : List (Prog isa)) ++
    (([.loop (seqs Crt.gatherBody) .ne] : List (Prog isa)) ++ (([seqs (.block selNext :: selMasks)] : List (Prog isa)) ++
      ([.loop (seqs Crt.gatherBody) .ne] : List (Prog isa)))) := rfl

/-- The selection of `T_v`, `v < 16` in `kG`, into `aXm`. -/
theorem mrSel_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi)
    (hZ : slot w 8 + tabBytes w ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 30) {v : Nat} (hv : v < 16)
    (hN : word s.mem B (8 * kG) = BitVec.ofNat 64 v) :
    WP isa (seqs mrSel) s fun t =>
      wv t.mem B (slot w aXm) w = wv s.mem B (slot w (8 + v)) w ∧
      Outside B (slot w aXm) (8 * (w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hZ8 : slot w 8 ≤ Z := by unfold tabBytes at hZ; omega_using [hZ]
  have hX8 := slot_le (w := w) (show aXm < 8 by decide)
  have hXs := slot_succ w aXm
  have hXe := slot_mono w (show aXm + 1 ≤ 8 by decide)
  rw [mrSel_eq]
  -- The first pass.
  refine wp_seqs_append (by simp) (by simp) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (selRegs_ok hg hZ8 hw') fun s₁ ⟨h15, hcx, h11, h13, hbx, hm₁, k₁⟩ => ?_)
  have hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine WP.mono (selMasks_ok hg₁ hZ8 (p := 0) (by decide) hv (by rw [hm₁]; exact hN) h15 hcx h11 h13 hbx)
    fun s₂ ⟨hG₂, h14₂, h11₂, hm₂, k₂⟩ => ?_
  refine wp_seqs_append (by simp) (by simp) ?_
  simp only [seqs]
  refine WP.mono (selLoop_ok' (hg₁.scr.congr k₂.2.2) hZ hw hw' (by decide) hG₂ h14₂)
    fun s₃ ⟨hv₃, ho₃, hgp₃, hrd₃, hwr₃⟩ => ?_
  have hg₃ : Good s₃ B Z w mi := ⟨(hg₁.scr.congr k₂.2.2).congr hwr₃, (hgp₃ .rdi (by decide)).trans
    ((k₂.gpr (by decide)).trans hg₁.rdi), Hdr.outside (by rw [hm₂, hm₁]; exact hg.hdr) ho₃ (by unfold slot; omega_using [])⟩
  have hN₃ : word s₃.mem B (8 * kG) = BitVec.ofNat 64 v := by
    rw [ho₃.word (Or.inl (hdr_lt_slot w aXm (show kG < 32 by decide))) (by unfold kG sFn; omega_using []), hm₂, hm₁]; exact hN
  -- The second pass.
  have h11₃ : s₃.gpr .r11 = BitVec.ofNat 64 (8 * (w + 2)) := (hgp₃ .r11 (by decide)).trans h11₂
  have hcx₃ : s₃.gpr .rcx = off B (slot w (8 + 8 * 0)) := (hgp₃ .rcx (by decide)).trans (hG₂.base 0 (by decide))
  have h13₃ : s₃.gpr .r13 = BitVec.ofNat 64 (2 * ((w + 1) / 2)) := (hgp₃ .r13 (by decide)).trans hG₂.r13
  have hbx₃ : s₃.gpr .rbx = off B (slot w aXm) := (hgp₃ .rbx (by decide)).trans (by rw [← aT_eq]; exact hG₂.bx)
  refine wp_seqs_append (by simp) (by simp) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (selNext_ok h11₃ hcx₃) fun s₄ ⟨h15₄, hcx₄, hm₄, k₄⟩ => ?_)
  have hg₄ : Good s₄ B Z w mi := ⟨hg₃.scr.congr k₄.2.2, (k₄.gpr (by decide)).trans hg₃.rdi, by rw [hm₄]; exact hg₃.hdr⟩
  refine WP.mono (selMasks_ok hg₄ hZ8 (p := 1) (by decide) hv (by rw [hm₄]; exact hN₃) h15₄ hcx₄
    ((k₄.gpr (by decide)).trans h11₃) ((k₄.gpr (by decide)).trans h13₃) ((k₄.gpr (by decide)).trans hbx₃))
    fun s₅ ⟨hG₅, h14₅, _, hm₅, k₅⟩ => ?_
  refine WP.mono (selLoop_ok' (hg₄.scr.congr k₅.2.2) hZ hw hw' (by decide) hG₅ h14₅)
    fun t ⟨hv₂, ho₂, hgpt, hrdt, hwrt⟩ => ?_
  have kt : Keep mmRegs s₅ t := ⟨fun r hr => hgpt r (fun h => hr (by rw [h]; decide)), hrdt, hwrt⟩
  have kst : Keep mmRegs s₂ s₃ := ⟨fun r hr => hgp₃ r (fun h => hr (by rw [h]; decide)), hrd₃, hwr₃⟩
  have hE : ∀ j < 16, ∀ k < 2 * ((w + 1) / 2), word s₃.mem B (slot w (8 + j) + 8 * k) =
      word s.mem B (slot w (8 + j) + 8 * k) := fun j hj k hk => by
    have := ent_le w (n := 16) hj
    have := slot_mono w (show 8 ≤ 8 + j by omega_using [])
    rw [ho₃.word (Or.inr (by omega_arith)) (by omega_arith), hm₂, hm₁]
  rw [hm₅, hm₄] at hv₂ ho₂
  refine ⟨wv_congr2 fun i hi => ?_, ?_, (((((k₁.trans k₂).trans kst).trans k₄).trans k₅).trans kt).mono (by decide)⟩
  · have hk : i < 2 * ((w + 1) / 2) := by omega_using [hi]
    rw [hv₂ i hk]
    unfold gval
    rw [aT_eq, hv₃ i hk]
    unfold gval
    rw [aT_eq, hm₂, hm₁]
    simp only [gacc_eq, gath_and_mask]
    by_cases h8 : v < 8
    · simp [show ¬ 8 * 1 ≤ v by omega_using [h8], show v ≤ 8 * 0 + 7 by omega_using [h8]]
    · simp [show 8 * 1 ≤ v by omega_using [h8], show v ≤ 8 * 1 + 7 by omega_using [hv], show ¬ v ≤ 8 * 0 + 7 by omega_using [h8],
        show (8 : Nat) + 8 * 1 + (v - 8 * 1) = 8 + v by omega_using [h8], ← hm₂, ← hm₁, hE v hv i hk]
  · rw [hm₂, hm₁] at ho₃
    exact (ho₃.trans ho₂).mono (by omega_using []) (by omega_using [])

end VG.Proof.RsaKeyGen.X86_64
