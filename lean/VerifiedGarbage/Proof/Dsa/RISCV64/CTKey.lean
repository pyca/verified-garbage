module

public import VerifiedGarbage.Proof.Dsa.RISCV64.CTBase
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA verification on RISC-V: constant time, the cuts of the sizes' checks

The levels `verify` (`FT`), `X1` and `X2` (`CTBase.lean`): the registers at
their cuts (`pins*`), and what correctness says at their branches (`mid*`),
from which the next level's states satisfy its phase (`sem*`): p's scan, q's
scan, and the pair of sizes.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Pins)
open VG.Proof.Dsa (significant)

/-! ## Steps -/

theorem ptrP_P0 {v : VD} {s : State} (h : P0 v s) :
    WP isa (.block ptrP) s fun t => P0 v t ∧ t.gpr .s7 = v.key ∧ t.gpr .s8 = BitVec.ofNat 64 v.L.pl :=
  WP.mono (ptrP_ok h.1.scr h.1.ok h.1.regs) fun _ ⟨⟨a7, a8, m⟩, k⟩ =>
    ⟨⟨h.1.keepM k m, by rw [Lens, m]; exact h.2⟩, a7, a8⟩

theorem ptrQ_P0 {v : VD} {s : State} (h : P0 v s) :
    WP isa (.block ptrQ) s fun t => (P0 v t ∧ t.gpr .s7 = off v.key v.L.pl ∧
      t.gpr .s8 = BitVec.ofNat 64 v.L.ql) ∧ Keep ptrRegs s t :=
  WP.mono (ptrQ_ok h.1.scr h.1.ok h.1.regs) fun _ ⟨⟨a7, a8, m⟩, k⟩ =>
    ⟨⟨⟨h.1.keepM k m, by rw [Lens, m]; exact h.2⟩, a7, a8⟩, k⟩

/-- p's or q's `sigLen`. -/
theorem sigLen_P0 {v : VD} {s : State} {o k : Nat} (h : P0 v s) (hk : 1 ≤ k ∧ k ≤ 1024)
    (hok : o + k ≤ 3 * v.L.pl + v.L.ql) (h7 : s.gpr .s7 = off v.key o) (h8 : s.gpr .s8 = BitVec.ofNat 64 k) :
    WP isa sigLen s fun t => (P0 v t ∧ t.gpr .a1 = BitVec.ofNat 64 (significant (v.sl o k)).1) ∧
      Keep sigRegs s t :=
  WP.mono (sigLen_ok h7 h8 hk.1 hk.2 (h.1.hk.sub hok).rd) fun _ ⟨⟨a1, m⟩, kt⟩ =>
    ⟨⟨⟨h.1.keepM kt m, by rw [Lens, m]; exact h.2⟩, by rw [a1, h.1.bytes hok]⟩, kt⟩

/-- p's or q's `bytesBits`. -/
theorem bytesBits_P0 {v : VD} {s : State} {o k : Nat} (h : P0 v s) (hk : 1 ≤ k ∧ k ≤ 1024)
    (hok : o + k ≤ 3 * v.L.pl + v.L.ql) (h7 : s.gpr .s7 = off v.key o) (h8 : s.gpr .s8 = BitVec.ofNat 64 k) :
    WP isa bytesBits s fun t => (P0 v t ∧ t.gpr .a1 = BitVec.ofNat 64 (significant (v.sl o k)).1 ∧
      (t.gpr .a0 = 0 ↔ 128 ≤ (significant (v.sl o k)).2.toNat)) ∧ Keep sigRegs s t :=
  WP.mono (bytesBits_ok h7 h8 hk.1 hk.2 (h.1.hk.sub hok).rd) fun _ ⟨⟨a1, a0, m⟩, kt⟩ =>
    ⟨⟨⟨h.1.keepM kt m, by rw [Lens, m]; exact h.2⟩, by rw [a1, h.1.bytes hok], by rw [a0, h.1.bytes hok]⟩, kt⟩

theorem off_zero (p : Addr) : off p 0 = p := BitVec.add_zero p

/-! ## `verify` -/

theorem semT1 {v : VD} {s : State} (h : C0 v s) : WP isa (Code.seqL (FT.take 1)) s (P0 v) :=
  WP.of_flat (c := .block Verify.entry) rfl (front_P0 h)

theorem pinsT1 : Pins (At C0 FT 1) [.s6, .s11, .ra] :=
  pins_at_fix fixB (fun _ => rfl) fun _ _ h => (semT1 h).mono fun _ h => h.1.fixB

theorem pinsT2 : Pins (At C0 FT 2) [.s6, .s11, .ra, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ [(.s7, v.key), (.s8, BitVec.ofNat 64 v.L.pl)]) (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq (.block Verify.entry) (.block ptrP)) rfl (WP.seq (WP.mono (front_P0 h) fun _ h =>
      (ptrP_P0 h).mono fun _ ⟨h, a7, a8⟩ => h.1.fixB.app ⟨a7, a8, trivial⟩))

theorem pinsT4 : Pins (At C0 FT 4) [.s6, .s11, .ra, .s7, .s8, .a1] :=
  pins_at_fix (fun v => fixB v ++ [(.s7, v.key), (.s8, BitVec.ofNat 64 v.L.pl), (.a1, BitVec.ofNat 64 v.sP)])
    (fun _ => rfl) fun v _ h =>
    WP.of_flat (c := .seq (.block Verify.entry) (.seq (.block ptrP) sigLen)) rfl (WP.seq (WP.mono (front_P0 h)
      fun _ h => WP.seq ((ptrP_P0 h).mono fun _ ⟨h, a7, a8⟩ =>
        (sigLen_P0 (o := 0) (k := v.L.pl) h (by have := h.1.pl; omega) (by omega) (by rw [off_zero]; exact a7) a8).mono
          fun _ ⟨⟨h', a1⟩, k⟩ => h'.1.fixB.app ⟨(k.gpr (r := .s7) (by decide)).trans a7, (k.gpr (r := .s8) (by decide)).trans a8,
            a1, trivial⟩)))

/-- At the branch on p's top bit. -/
abbrev MT (v : VD) (u : State) : Prop :=
  P0 v u ∧ u.gpr .a1 = BitVec.ofNat 64 v.sP ∧ (u.gpr .a0 = 0 ↔ 128 ≤ v.tP)

theorem midT {v : VD} {s : State} (h : C0 v s) : WP isa (Code.seqL (FT.take 5)) s (MT v) :=
  WP.of_flat (c := .seq (.block Verify.entry) (.seq (.block ptrP) bytesBits)) rfl (WP.seq (WP.mono (front_P0 h)
    fun _ h => WP.seq ((ptrP_P0 h).mono fun _ ⟨h, a7, a8⟩ =>
      (bytesBits_P0 (o := 0) (k := v.L.pl) h (by have := h.1.pl; omega) (by omega) (by rw [off_zero]; exact a7) a8).mono
        fun _ ⟨h', _⟩ => h')))

theorem zeroT : ∀ v s₁ s₂, At C0 FT 5 v s₁ → At C0 FT 5 v s₂ → (s₁.gpr .a0 == 0) = (s₂.gpr .a0 == 0) :=
  zero_at (fun v => 128 ≤ v.tP) fun _ _ h => (midT h).mono fun _ h => h.2.2

/-- `X1`'s phase: p's scan passed. -/
abbrev SX1 (v : VD) (u : State) : Prop := P0 v u ∧ u.gpr .a1 = BitVec.ofNat 64 v.sP ∧ 128 ≤ v.tP

theorem semX1 {v : VD} {u : State} (h : ΦX1 v u) : SX1 v u :=
  let m := at_sem (fun _ _ h => midT h) h.1
  ⟨m.1, m.2.1, m.2.2.mp h.2⟩

/-! ## `restore` -/

theorem s6_kept : ∀ i ∈ instrs (seg FT 1 6), dstOf i ≠ some .s6 := by
  have h : (instrs (seg FT 1 6)).all (fun i => dstOf i != some .s6) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem pinsT6 : Pins (At C0 FT 6) [.s6] :=
  pins_fix (fun v => [(.s6, v.L.S)]) (fun _ => rfl) fun v u ⟨s₀, t, h₀, e⟩ => by
    rw [take_split FT (n := 1) (m := 6) (by decide)] at e
    obtain ⟨_, _, u₁, -, e₁, e₂⟩ := exec_seqL_append.mp e
    have h₁ : u₁.gpr .s6 = v.L.S := (at_sem (Φ := C0) (F := FT) (n := 1) (M := P0) (fun _ _ h => semT1 h) ⟨s₀, _, h₀, e₁⟩).1.regs.s6
    exact ⟨(Exec.gpr_callFree s6_kept e₂ rfl).trans h₁, trivial⟩

/-! ## `X1`: q's scan -/

theorem a2_P0 {v : VD} {s : State} (h : P0 v s) :
    WP isa (.block [.addi .a2 .a1 0]) s fun t => (P0 v t ∧ t.gpr .a2 = s.gpr .a1) ∧ Keep [.a2] s t :=
  WP.mono (WP.keep [.a2] (Q := fun t => t.gpr .a2 = s.gpr .a1 ∧ t.mem = s.mem) (by brun [BitVec.add_zero])
    (by decide) (by rfl)) fun _ ⟨⟨a2, m⟩, k⟩ => ⟨⟨⟨h.1.keepM k m, by rw [Lens, m]; exact h.2⟩, a2⟩, k⟩

theorem pinsX1_0 : Pins (At ΦX1 FX1 0) [.s6, .s11, .ra, .a1] :=
  pins_at_fix (fun v => fixB v ++ [(.a1, BitVec.ofNat 64 v.sP)]) (fun _ => rfl) fun _ _ h =>
    ⟨[], _, .block rfl, (semX1 h).1.1.fixB.app ⟨(semX1 h).2.1, trivial⟩⟩

theorem pinsX1_2 : Pins (At ΦX1 FX1 2) [.s6, .s11, .ra, .a2, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ [(.a2, BitVec.ofNat 64 v.sP), (.s7, off v.key v.L.pl),
      (.s8, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl) fun v _ h =>
    WP.of_flat (c := (.seq (.block [.addi .a2 .a1 0]) (.block ptrQ) : Prog isa)) rfl (WP.seq (WP.mono (a2_P0 (semX1 h).1)
      fun _ ⟨⟨h', a2⟩, _⟩ => (ptrQ_P0 h').mono fun _ ⟨⟨h'', a7, a8⟩, k⟩ =>
        h''.1.fixB.app ⟨(k.gpr (r := .a2) (by decide)).trans (a2.trans (semX1 h).2.1), a7, a8, trivial⟩))

theorem pinsX1_4 : Pins (At ΦX1 FX1 4) [.s6, .s11, .ra, .a1, .a2, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ [(.a1, BitVec.ofNat 64 v.sQ), (.a2, BitVec.ofNat 64 v.sP),
      (.s7, off v.key v.L.pl), (.s8, BitVec.ofNat 64 v.L.ql)]) (fun _ => rfl) fun v _ h =>
    WP.of_flat (c := (.seq (.block [.addi .a2 .a1 0]) (.seq (.block ptrQ) sigLen) : Prog isa)) rfl
      (WP.seq (WP.mono (a2_P0 (semX1 h).1) fun _ ⟨⟨h', a2⟩, _⟩ => WP.seq ((ptrQ_P0 h').mono
        fun _ ⟨⟨h'', a7, a8⟩, k⟩ =>
          (sigLen_P0 (o := v.L.pl) (k := v.L.ql) h'' (by have := h''.1.ql; omega) (by omega) a7 a8).mono fun _ ⟨⟨h₃, a1⟩, k'⟩ =>
            h₃.1.fixB.app ⟨a1, (k'.gpr (r := .a2) (by decide)).trans ((k.gpr (r := .a2) (by decide)).trans
              (a2.trans (semX1 h).2.1)), (k'.gpr (r := .s7) (by decide)).trans a7,
              (k'.gpr (r := .s8) (by decide)).trans a8, trivial⟩)))

/-- At the branch on q's top bit. -/
abbrev MX1 (v : VD) (u : State) : Prop :=
  P0 v u ∧ u.gpr .a1 = BitVec.ofNat 64 v.sQ ∧ u.gpr .a2 = BitVec.ofNat 64 v.sP ∧ 128 ≤ v.tP ∧
    (u.gpr .a0 = 0 ↔ 128 ≤ v.tQ)

theorem midX1 {v : VD} {s : State} (h : ΦX1 v s) : WP isa (Code.seqL (FX1.take 5)) s (MX1 v) :=
  WP.of_flat (c := (.seq (.block [.addi .a2 .a1 0]) (.seq (.block ptrQ) bytesBits) : Prog isa)) rfl
    (WP.seq (WP.mono (a2_P0 (semX1 h).1) fun _ ⟨⟨h', a2⟩, _⟩ => WP.seq ((ptrQ_P0 h').mono
      fun _ ⟨⟨h'', a7, a8⟩, k⟩ =>
        (bytesBits_P0 (o := v.L.pl) (k := v.L.ql) h'' (by have := h''.1.ql; omega) (by omega) a7 a8).mono fun _ ⟨⟨h₃, a1, a0⟩, k'⟩ =>
          ⟨h₃, a1, (k'.gpr (r := .a2) (by decide)).trans ((k.gpr (r := .a2) (by decide)).trans (a2.trans (semX1 h).2.1)),
            (semX1 h).2.2, a0⟩)))

theorem zeroX1 : ∀ v s₁ s₂, At ΦX1 FX1 5 v s₁ → At ΦX1 FX1 5 v s₂ → (s₁.gpr .a0 == 0) = (s₂.gpr .a0 == 0) :=
  zero_at (fun v => 128 ≤ v.tQ) fun _ _ h => (midX1 h).mono fun _ h => h.2.2.2.2

/-- `X2`'s phase: both scans passed. -/
abbrev SX2 (v : VD) (u : State) : Prop :=
  P0 v u ∧ u.gpr .a1 = BitVec.ofNat 64 v.sQ ∧ u.gpr .a2 = BitVec.ofNat 64 v.sP ∧ 128 ≤ v.tP ∧ 128 ≤ v.tQ

theorem semX2 {v : VD} {u : State} (h : ΦX2 v u) : SX2 v u :=
  let m := at_sem (fun _ _ h => midX1 h) h.1
  ⟨m.1, m.2.1, m.2.2.1, m.2.2.2.1, m.2.2.2.2.mp h.2⟩

/-! ## `X2`: the pair of sizes -/

theorem pinsX2_0 : Pins (At ΦX2 FX2 0) [.s6, .s11, .ra, .a1, .a2] :=
  pins_at_fix (fun v => fixB v ++ [(.a1, BitVec.ofNat 64 v.sQ), (.a2, BitVec.ofNat 64 v.sP)]) (fun _ => rfl)
    fun _ _ h => ⟨[], _, .block rfl, (semX2 h).1.1.fixB.app ⟨(semX2 h).2.1, (semX2 h).2.2.1, trivial⟩⟩

theorem sP_le (v : VD) : v.sP ≤ v.L.pl := by
  have := VG.Proof.Dsa.significant_fits v.pB
  have : v.pB.length ≤ v.L.pl := by simp only [VD.pB, VD.sl, List.length_take]; omega
  unfold VD.sP; omega

theorem sQ_le (v : VD) : v.sQ ≤ v.L.ql := by
  have := VG.Proof.Dsa.significant_fits v.qB
  have : v.qB.length ≤ v.L.ql := by simp only [VD.qB, VD.sl, List.length_take]; omega
  unfold VD.sQ; omega

/-- At the branch on the pair of sizes. -/
abbrev MX2 (v : VD) (u : State) : Prop :=
  Base v u ∧ Lens v v.sQ u ∧ 128 ≤ v.tP ∧ 128 ≤ v.tQ ∧
    (u.gpr .a0 = 0 ↔ Spec.Dsa.supportedSizes (8 * v.sP) (8 * v.sQ))

theorem midX2 {v : VD} {s : State} (h : ΦX2 v s) : WP isa (Code.seqL (FX2.take 12)) s (MX2 v) := by
  obtain ⟨⟨B, l0⟩, a1, a2, hp, hq⟩ := semX2 h
  have hL := B.ok
  have hpl := B.pl; have hql := B.ql
  have hsp := sP_le v; have hsq := sQ_le v
  have hqb : v.sQ < 2 ^ 16 := by simp only [Nat.reducePow]; omega
  have hd : v.d < 2 ^ 16 := by show min v.dl 64 < 2 ^ 16; simp only [Nat.reducePow]; omega
  obtain ⟨hin, hal⟩ := ScrL.hdr B.scr hL (d := 16) (by decide) (by decide)
  have hst : InRegions s.wr (off v.L.S 16) 8 := B.scr.st (by have := hL.z256; omega)
  have l0' : word s.mem v.L.S 16 = pack v.L.pl v.L.ql 0 v.d := l0
  refine WP.of_flat (c := (.seq (.block [.addi .a3 .a1 0, .shift .sll .d .t3 .a1 32, .load .d .t4 .s6 hLens,
    .add .t4 .t4 .t3, .store .d .t4 .s6 hLens]) pairs : Prog isa)) rfl (WP.seq (WP.mono (WP.keep [.a3, .t3, .t4] (Q := fun t =>
    t.gpr .a3 = BitVec.ofNat 64 v.sQ ∧ t.mem = s.mem.writeW (off v.L.S 16) (pack v.L.pl v.L.ql v.sQ v.d))
    (by brun [hLens, a1, B.regs.s6, hin, hal, hst, BitVec.add_zero, exec_shift_d (show 32 < 64 by decide), l0',
      pack_add hqb]) (by decide) (by rfl)) fun t₁ ⟨⟨f3, fm⟩, k1⟩ => ?_))
  have hw := writeW_outside s.mem v.L.S (d := 16) (pack v.L.pl v.L.ql v.sQ v.d) (by have := hL.nowrap; omega_arith)
  have g2 : t₁.gpr .a2 = BitVec.ofNat 64 v.sP := (k1.gpr (by decide)).trans a2
  refine WP.mono (pairs_ok g2 f3 (by omega) (by omega)) fun t ⟨⟨g0, gm⟩, k2⟩ => ?_
  have m : t.mem = s.mem.writeW (off v.L.S 16) (pack v.L.pl v.L.ql v.sQ v.d) := by rw [gm, fm]
  have w : Lens v v.sQ t := by rw [Lens, m]; exact word_writeW_self _ _ _ _
  have k := k1.trans k2
  refine ⟨B.kept k (Kept.ofHdr hL (by rw [m]; exact hw))
    (Regs.of_pack hL B.regs (k.gpr (by decide)) (k.gpr (by decide)) (k.gpr (by decide)) w hqb hd), w, hp, hq, g0⟩

theorem zeroX2 : ∀ v s₁ s₂, At ΦX2 FX2 12 v s₁ → At ΦX2 FX2 12 v s₂ → (s₁.gpr .a0 == 0) = (s₂.gpr .a0 == 0) :=
  zero_at (fun v => Spec.Dsa.supportedSizes (8 * v.sP) (8 * v.sQ)) fun _ _ h => (midX2 h).mono fun _ h => h.2.2.2.2

/-- The sizes are supported. -/
abbrev SzOk (v : VD) : Prop := Spec.Dsa.supportedSizes (Spec.Dsa.bitLength v.p) (Spec.Dsa.bitLength v.q)

/-- After the sizes: the header's lengths with q's significant octets. -/
abbrev P1 (v : VD) (u : State) : Prop := Base v u ∧ Lens v v.qb u ∧ SzOk v

theorem semR0 {v : VD} {u : State} (h : ΦR0 v u) : P1 v u := by
  obtain ⟨B, l, hp, hq, h0⟩ := at_sem (fun _ _ h => midX2 h) h.1
  have hok : SzOk v := (VG.Proof.Dsa.supported_scans v.pB v.qB).mpr ⟨hp, hq, h0.mp h.2⟩
  have hb : v.qb = v.sQ := by
    have := VG.Proof.Dsa.subgroup_scan_width (p := v.pB) hok
    show Spec.Dsa.bitLength v.q / 8 = _
    rw [show v.q = Spec.Dsa.decodeBE v.qB from rfl, this]; unfold VD.sQ; omega
  exact ⟨B, by rw [hb]; exact l, hok⟩

end VG.Proof.Dsa.RISCV64.CT
