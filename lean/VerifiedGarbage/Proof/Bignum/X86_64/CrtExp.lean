import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.CrtExp

/-!
# RSA with the CRT on x86-64: the exponentiation in a prime's workspace

In a prime's workspace (`X`, `w_X` words, `R = 2^(64 w_X)`), with
`Y ≡ R` and `[aXc] ≡ x R`: `tabBuild` writes the table `T_j ≡ x^j R` after
the arrays (`tabBuild_ok`); a window `v` is four squarings, `[aT] := T_v` by
a masked selection from every entry (`tabSel_ok`) and `Y := Y T_v R⁻¹`
(`crtWin_ok`); `expLoop` does two windows for every byte of the exponent,
read from the modulus' header (`crtExpLoop_ok`): `Y ≡ x^d R`.

The values hold if `Y ≡ R` and `[aXc] ≡ x R`, which a proposition `Q` (in
the phases, that `X` divides `n`) gives; the bounds hold whatever.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-! ## What the exponentiation changes -/

/-! ## The prime's workspace -/

/-- What the exponentiation keeps in the workspace at `P` (`w_X` words) and
its table: the prime `X` (and its low word, for `-X⁻¹`), and `Xc`. -/
structure CExpCtx (t : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) : Prop where
  good : Good t P (slot wx 8) wx minv
  scrT : Scr t P (slot wx 8 + tabBytes wx)
  n : wv t.mem P (slot wx aN) wx = X
  inv : ((word t.mem P (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  x : wv t.mem P (slot wx Crt.aXc) wx = Xc

theorem CExpCtx.ld {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) {i : Nat} (hi : i < 32) : InRegions (t.rd ++ t.wr) (off P (8 * i)) 8 :=
  hc.good.scr.ld (by have := hdr_lt_slot wx 8 hi; omega_arith)

theorem CExpCtx.st {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) {i : Nat} (hi : i < 32) : InRegions t.wr (off P (8 * i)) 8 :=
  hc.good.scr.st (by have := hdr_lt_slot wx 8 hi; omega_arith)

/-- What changes only within the exponentiation's ranges keeps the context. -/
theorem CExpCtx.of_frm {t t' : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hf : Frm P (crtExpRanges wx) t.mem t'.mem) (hwr : t'.wr = t.wr)
    (hdi : t'.gpr .rdi = t.gpr .rdi) : CExpCtx t' P wx minv X Xc := by
  have hn := hc.scrT.nowrap
  have rN := crtExpRanges_arr wx (j := aN) (by decide) (by decide) (by decide) (by decide) (by decide)
  have rX := crtExpRanges_arr wx (j := Crt.aXc) (by decide) (by decide) (by decide) (by decide) (by decide)
  have lN := slot_le (w := wx) (show aN < 8 by decide)
  have lX := slot_le (w := wx) (show Crt.aXc < 8 by decide)
  have hh : ∀ i < 17, word t'.mem P (8 * i) = word t.mem P (8 * i) := fun i hi =>
    hf.word_eq (fun r hr => Or.inl (by have := crtExpRanges_ok wx r hr; omega_arith))
      (by have := hdr_lt_slot wx 8 (show i < 32 by omega_arith); omega_arith)
  exact ⟨⟨hc.good.scr.congr hwr, hdi.trans hc.good.rdi,
    ⟨(hh _ (by decide)).trans hc.good.hdr.hw, (hh _ (by decide)).trans hc.good.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega_arith)).trans (hc.good.hdr.harr j hj)⟩⟩, hc.scrT.congr hwr,
    by rw [hf.wv_eq (fun r hr => by have := rN r hr; omega_arith) (by omega_arith)]; exact hc.n,
    by rw [hf.word_eq (fun r hr => by have := rN r hr; omega_arith) (by omega_arith)]; exact hc.inv,
    by rw [hf.wv_eq (fun r hr => by have := rX r hr; omega_arith) (by omega_arith)]; exact hc.x⟩

theorem CExpCtx.of_win {t t' : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hf : Frm P (crtWinRanges wx) t.mem t'.mem) (hwr : t'.wr = t.wr)
    (hdi : t'.gpr .rdi = t.gpr .rdi) : CExpCtx t' P wx minv X Xc :=
  hc.of_frm (hf.mono (crtWinRanges_sub wx)) hwr hdi

/-! ## The table's entries -/

/-- `off P e` moved up an entry, as `nextEnt` computes it. -/
theorem entStep (P : Addr) (e wx : Nat) :
    off P e + (BitVec.ofNat 64 wx + 2 + (BitVec.ofNat 64 wx + 2) + (BitVec.ofNat 64 wx + 2 + (BitVec.ofNat 64 wx + 2)) +
      (BitVec.ofNat 64 wx + 2 + (BitVec.ofNat 64 wx + 2) + (BitVec.ofNat 64 wx + 2 + (BitVec.ofNat 64 wx + 2)))) =
      off P (e + 8 * (wx + 2)) := by
  rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl]
  simp only [BitVec.ofNat_add_ofNat, off, BitVec.add_assoc]
  congr 2
  omega_arith

/-- `sEnt` moves up an entry. -/
theorem nextEnt_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) {e : Nat} (he : word t.mem P (8 * Crt.sEnt) = off P e) :
    WP isa Crt.nextEnt t fun t' => t'.mem = t.mem.writeW (off P (8 * Crt.sEnt)) (off P (e + 8 * (wx + 2))) ∧
      Keep [.rax, .rdx] t t' := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t' => t'.mem = t.mem.writeW (off P (8 * Crt.sEnt))
    (off P (e + 8 * (wx + 2)))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩
  unfold Crt.nextEnt
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sEnt) (by decide), hc.ld (i := sW) (by decide),
    hc.st (i := Crt.sEnt) (by decide), he, hc.good.hdr.hw]
  rw [entStep]

/-- `toEnt a`: entry `j`, at `sEnt`, `:= [a]`. -/
theorem toEnt_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) {a j : Nat} (ha : a < 8) (hj : j < 16)
    (he : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + j))) :
    WP isa (seqs (Crt.toEnt a)) t fun t' => wv t'.mem P (slot wx (8 + j)) wx = wv t.mem P (slot wx a) wx ∧
      Outside P (slot wx (8 + j)) (8 * wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  have hT := ent_le wx hj
  have sa := slot_le (w := wx) ha
  have sp := slot_sep (w := wx) (show a ≠ 8 + j by omega_arith)
  unfold Crt.toEnt
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t₁ => t₁.gpr .r12 = BitVec.ofNat 64 wx ∧
      t₁.gpr .rsi = off P (slot wx a) ∧ t₁.gpr .rbx = off P (slot wx (8 + j)) ∧ t₁.mem = t.mem)
    (by xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := sArr a) (by unfold sArr; omega_arith),
      hc.ld (i := Crt.sEnt) (by decide), hc.ld (i := sW) (by decide), hc.good.hdr.harr a ha, he,
      hc.good.hdr.hw]) rfl) fun t₁ ⟨⟨h12, hsi, hbx, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hc.scrT.congr k₁.2.2
  refine WP.mono (copyWords_ok hsi hbx h12 (by omega_arith) (by omega_arith) (by omega_arith) (fun i hi => hs₁.ld (by omega_arith))
    (fun i hi => hs₁.st (by omega_arith)) (fun i hi b hb => by rw [ofs_off P (by omega_arith)]; omega_arith))
    fun t' ⟨hv, _, ho', k⟩ => ⟨by rw [hv, hm₁], by rw [hm₁] at ho'; exact ho', (k₁.trans k).mono (by decide)⟩

/-! ## Reading an entry -/

/-- The selection's start: `sEnt := sTab`, `sJ := 0`. -/
theorem selInit_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) (ht : word t.mem P (8 * Crt.sTab) = off P (slot wx 8)) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sTab)), .store (hdr Crt.sEnt) .rax, .mov32 .rax (.imm 0),
      .store (hdr Crt.sJ) .rax]) t fun t' =>
      t'.mem = (t.mem.writeW (off P (8 * Crt.sEnt)) (off P (slot wx 8))).writeW (off P (8 * Crt.sJ))
        (BitVec.setWidth 64 (0 : BitVec 32)) ∧ Keep [.rax] t t' := by
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = (t.mem.writeW (off P (8 * Crt.sEnt))
      (off P (slot wx 8))).writeW (off P (8 * Crt.sJ)) (BitVec.setWidth 64 (0 : BitVec 32))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sTab) (by decide), ht,
      hc.st (i := Crt.sEnt) (by decide), hc.st (i := Crt.sJ) (by decide)]) rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩

theorem slot_add_mul (w j k : Nat) : slot w (j + k) = slot w j + k * (8 * (w + 2)) := by
  induction k with
  | zero => simp
  | succ k ih => rw [← Nat.add_assoc, slot_succ, ih, Nat.add_mul, Nat.one_mul, Nat.add_assoc]

/-- A pass's registers: `r15 = 8 p`, its first entry in `rcx`, an entry's
size in `r11`, `r13 = 2 ⌈w / 2⌉` and `rbx = aT`. -/
theorem gRegs_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc p : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hw' : wx < 2 ^ 30)
    (hJ : word t.mem P (8 * Crt.sJ) = BitVec.ofNat 64 (8 * p))
    (hE : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + 8 * p))) :
    WP isa (.block Crt.gatherRegs) t fun t' =>
      t'.gpr .r15 = BitVec.ofNat 64 (8 * p) ∧ t'.gpr .rcx = off P (slot wx (8 + 8 * p)) ∧
      t'.gpr .r11 = BitVec.ofNat 64 (8 * (wx + 2)) ∧ t'.gpr .r13 = BitVec.ofNat 64 (2 * ((wx + 1) / 2)) ∧
      t'.gpr .rbx = off P (slot wx Crt.aT) ∧ t'.mem = t.mem ∧ t'.xmm = t.xmm ∧
      Keep [.r15, .rcx, .r12, .r11, .r13, .rbx] t t' := by
  have h11 : BitVec.ofNat 64 wx + 2 + (BitVec.ofNat 64 wx + 2) + (BitVec.ofNat 64 wx + 2 + (BitVec.ofNat 64 wx + 2)) +
      (BitVec.ofNat 64 wx + 2 + (BitVec.ofNat 64 wx + 2) + (BitVec.ofNat 64 wx + 2 + (BitVec.ofNat 64 wx + 2))) =
      BitVec.ofNat 64 (8 * (wx + 2)) := by
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl]
    simp only [BitVec.ofNat_add_ofNat]
    congr 1
    omega
  have h13 : (BitVec.ofNat 64 wx + 1) >>> 1 + (BitVec.ofNat 64 wx + 1) >>> 1 = BitVec.ofNat 64 (2 * ((wx + 1) / 2)) := by
    rw [ofNat_add_one]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    omega
  refine WP.mono (WP.keep [.r15, .rcx, .r12, .r11, .r13, .rbx] (Q := fun t' =>
      t'.gpr .r15 = BitVec.ofNat 64 (8 * p) ∧ t'.gpr .rcx = off P (slot wx (8 + 8 * p)) ∧
      t'.gpr .r11 = BitVec.ofNat 64 (8 * (wx + 2)) ∧ t'.gpr .r13 = BitVec.ofNat 64 (2 * ((wx + 1) / 2)) ∧
      t'.gpr .rbx = off P (slot wx Crt.aT) ∧ t'.mem = t.mem ∧ t'.xmm = t.xmm) (by
    unfold Crt.gatherRegs
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sJ) (by decide), hc.ld (i := Crt.sEnt) (by decide),
      hc.ld (i := sW) (by decide), hc.ld (i := sArr Crt.aT) (by decide), hJ, hE, hc.good.hdr.hw,
      hc.good.hdr.harr Crt.aT (by decide), h11, h13]
    rfl) rfl) fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, k⟩

/-- The mask of `k + j = v` in both quadwords of `x`, `v` in `sNib` and `k` in `r15`. -/
theorem gMask_ok {t : State} {P : Addr} {k j v : Nat} (hdi : t.gpr .rdi = P)
    (hld : InRegions (t.rd ++ t.wr) (off P (8 * Crt.sNib)) 8) (hN : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v)
    (h15 : t.gpr .r15 = BitVec.ofNat 64 k) (hk : k < 16) (hj : j < 8) (hv : v < 16) (x : XReg) :
    WP isa (.block (Crt.selMask (BitVec.ofNat 32 j) (.mem (hdr Crt.sNib)) x)) t fun t' =>
      (∀ q < 2, q128 (t'.xmm x) q = mask (decide (k + j = v))) ∧ (∀ y, y ≠ x → t'.xmm y = t.xmm y) ∧
      t'.mem = t.mem ∧ Keep [.r14] t t' := by
  rw [show Crt.selMask (BitVec.ofNat 32 j) (.mem (hdr Crt.sNib)) x =
    ([.mov .r14 (.reg .r15), .alu .add .r14 (.imm (BitVec.ofNat 32 j)), .alu .xor .r14 (.mem (hdr Crt.sNib)),
      .alu .cmp .r14 (.imm 1), .alu .sbb .r14 (.reg .r14)] : List Instr) ++
    ([.xop (.movq x .r14), .xop (.bin .punpcklqdq x x)] : List Instr) from rfl]
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r14] (Q := fun t' =>
      (∃ b : Bool, b = decide (BitVec.ofNat 64 k + BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 v = 0) ∧
        t'.gpr .r14 = mask b) ∧ t'.mem = t.mem ∧ t'.xmm = t.xmm) (by
    xrun [State.ea, hdr, hdi, hdrOff, hld, hN, h15, sx_ofNat (show j < 2 ^ 31 by omega)]
    exact ⟨⟨_, decide_lt_one _, rfl⟩, rfl⟩) rfl) fun t₁ ⟨⟨⟨b, hb, h14⟩, hm, hx⟩, k₁⟩ => ?_)
  refine WP.mono (dupX_ok x) fun t' ⟨hd, hy, hg, hm', hrd, hwr⟩ => ⟨fun q hq => ?_,
    fun y hy' => by rw [hy y hy', hx], by rw [hm', hm], ?_⟩
  · rw [hd q hq, h14, hb, BitVec.ofNat_add_ofNat]
    congr 1
    exact decide_eq_decide.mpr (xor_eq_zero_iff.trans (ofNat64_inj (by omega) (by omega)))
  · exact ⟨fun r hr => by rw [hg]; exact k₁.1 r hr, hrd.trans k₁.2.1, hwr.trans k₁.2.2⟩

/-- The mask of `p = 1` in both quadwords of `xmm7`, `8 p` in `r15`. -/
theorem gKeep_ok {t : State} {p : Nat} (h15 : t.gpr .r15 = BitVec.ofNat 64 (8 * p)) (hp : p < 2) :
    WP isa (.block (Crt.selMask 0 (.imm 8) .xmm7)) t fun t' =>
      (∀ q < 2, q128 (t'.xmm .xmm7) q = mask (decide (p = 1))) ∧ (∀ y, y ≠ .xmm7 → t'.xmm y = t.xmm y) ∧
      t'.mem = t.mem ∧ Keep [.r14] t t' := by
  rw [show Crt.selMask 0 (.imm 8) .xmm7 =
    ([.mov .r14 (.reg .r15), .alu .add .r14 (.imm 0), .alu .xor .r14 (.imm 8),
      .alu .cmp .r14 (.imm 1), .alu .sbb .r14 (.reg .r14)] : List Instr) ++
    ([.xop (.movq .xmm7 .r14), .xop (.bin .punpcklqdq .xmm7 .xmm7)] : List Instr) from rfl]
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r14] (Q := fun t' =>
      (∃ b : Bool, b = decide (BitVec.ofNat 64 (8 * p) + 0 ^^^ 8 = 0) ∧
        t'.gpr .r14 = mask b) ∧ t'.mem = t.mem ∧ t'.xmm = t.xmm) (by
    xrun [h15, show BitVec.signExtend 64 (0 : BitVec 32) = 0 by decide, BitVec.add_zero]
    exact ⟨⟨_, decide_lt_one _, rfl⟩, rfl⟩) rfl) fun t₁ ⟨⟨⟨b, hb, h14⟩, hm, hx⟩, k₁⟩ => ?_)
  refine WP.mono (dupX_ok .xmm7) fun t' ⟨hd, hy, hg, hm', hrd, hwr⟩ => ⟨fun q hq => ?_,
    fun y hy' => by rw [hy y hy', hx], by rw [hm', hm], ?_⟩
  · rw [hd q hq, h14, hb]
    congr 1
    apply decide_eq_decide.mpr
    rw [xor_eq_zero_iff, show BitVec.ofNat 64 (8 * p) + (0 : BitVec 64) = BitVec.ofNat 64 (8 * p) from BitVec.add_zero _,
      show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ofNat64_inj (by omega) (by omega)]
    omega
  · exact ⟨fun r hr => by rw [hg]; exact k₁.1 r hr, hrd.trans k₁.2.1, hwr.trans k₁.2.2⟩

/-- The pass's entries: entry `8 p + k` in `gReg k`, from `rcx`, and `r14 = 0`. -/
theorem gBases_ok {t : State} {P : Addr} {wx p : Nat} (hcx : t.gpr .rcx = off P (slot wx (8 + 8 * p)))
    (h11 : t.gpr .r11 = BitVec.ofNat 64 (8 * (wx + 2))) :
    WP isa (.block Crt.gatherBases) t fun t' =>
      (∀ k < 8, t'.gpr (gReg k) = off P (slot wx (8 + 8 * p + k))) ∧ t'.gpr .r14 = BitVec.ofNat 64 (2 * 0) ∧
      t'.mem = t.mem ∧ t'.xmm = t.xmm ∧ Keep [.rdx, .rsi, .rbp, .r8, .r9, .r10, .rax, .r14] t t' := by
  refine WP.mono (WP.keep [.rdx, .rsi, .rbp, .r8, .r9, .r10, .rax, .r14] (Q := fun t' =>
      t'.gpr .rcx = off P (slot wx (8 + 8 * p + 0)) ∧ t'.gpr .rdx = off P (slot wx (8 + 8 * p + 1)) ∧
      t'.gpr .rsi = off P (slot wx (8 + 8 * p + 2)) ∧ t'.gpr .rbp = off P (slot wx (8 + 8 * p + 3)) ∧
      t'.gpr .r8 = off P (slot wx (8 + 8 * p + 4)) ∧ t'.gpr .r9 = off P (slot wx (8 + 8 * p + 5)) ∧
      t'.gpr .r10 = off P (slot wx (8 + 8 * p + 6)) ∧ t'.gpr .rax = off P (slot wx (8 + 8 * p + 7)) ∧
      t'.gpr .r14 = BitVec.ofNat 64 (2 * 0) ∧ t'.mem = t.mem ∧ t'.xmm = t.xmm) (by
    unfold Crt.gatherBases
    xrun [hcx, h11, off_add_eq, Nat.add_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> exact congrArg (off P) (by rw [slot_add_mul wx (8 + 8 * p)]; omega)) rfl)
    fun t' ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h14, hm, hx⟩, k⟩ => ⟨fun k hk => ?_, h14, hm, hx, k⟩
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- The pass's end: `sEnt` past its entries, `sJ := 8 (p + 1)`, `ZF` after the second. -/
theorem gEnd_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc p : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hp : p < 2) (h7 : t.gpr .rax = off P (slot wx (8 + 8 * p + 7)))
    (h11 : t.gpr .r11 = BitVec.ofNat 64 (8 * (wx + 2))) (h15 : t.gpr .r15 = BitVec.ofNat 64 (8 * p)) :
    WP isa (.block Crt.gatherEnd) t fun t' =>
      t'.mem = (t.mem.writeW (off P (8 * Crt.sEnt)) (off P (slot wx (8 + 8 * (p + 1))))).writeW (off P (8 * Crt.sJ))
        (BitVec.ofNat 64 (8 * (p + 1))) ∧ t'.zf = some (decide (p + 1 = 2)) ∧ Keep [.rax] t t' := by
  have hs : slot wx (8 + 8 * p + 7) + 8 * (wx + 2) = slot wx (8 + 8 * (p + 1)) := by
    rw [← slot_succ, show 8 + 8 * p + 7 + 1 = 8 + 8 * (p + 1) by omega]
  have h8 : BitVec.ofNat 64 (8 * p) + 8 = BitVec.ofNat 64 (8 * (p + 1)) := by
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]; congr 1
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = (t.mem.writeW (off P (8 * Crt.sEnt))
      (off P (slot wx (8 + 8 * (p + 1))))).writeW (off P (8 * Crt.sJ)) (BitVec.ofNat 64 (8 * (p + 1))) ∧
      t'.zf = some (decide (p + 1 = 2))) (by
    unfold Crt.gatherEnd
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.st (i := Crt.sEnt) (by decide), hc.st (i := Crt.sJ) (by decide),
      h7, h11, h15, off_add_eq, hs, sx_ofNat (show 8 < 2 ^ 31 by omega), h8]
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_beq (show 8 * (p + 1) < 2 ^ 64 by omega) (show 16 < 2 ^ 64 by decide)]
    exact decide_eq_decide.mpr (by omega)) rfl) fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩

/-- After `p` passes of the selection of entry `v` from `t₀`. -/
structure GathPassInv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc v : Nat) (p : Nat) (t : State) :
    Prop where
  ctx : CExpCtx t P wx minv X Xc
  nib : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v
  ent : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + 8 * p))
  idx : word t.mem P (8 * Crt.sJ) = BitVec.ofNat 64 (8 * p)
  val : p = 0 ∨ ∀ k < 2 * ((wx + 1) / 2), word t.mem P (slot wx Crt.aT + 8 * k) =
    if v < 8 * p then word t₀.mem P (slot wx (8 + v) + 8 * k) else 0
  frm : Frm P (selRanges wx) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

theorem tabSelect_eq : Crt.tabSelect = [.block [.mov .rax (.mem (hdr Crt.sTab)), .store (hdr Crt.sEnt) .rax,
    .mov32 .rax (.imm 0), .store (hdr Crt.sJ) .rax], .loop (seqs Crt.gatherPass) .ne] := rfl

/-- A pass's head: its registers, masks and bases. -/
theorem gathHead_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v p : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hw' : wx < 2 ^ 30) (hv : v < 16) (hp : p < 2)
    (hN : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) (hJ : word t.mem P (8 * Crt.sJ) = BitVec.ofNat 64 (8 * p))
    (hE : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + 8 * p))) :
    WP isa (seqs Crt.gatherHead) t fun s => GRegs P wx p v s ∧ s.gpr .r14 = BitVec.ofNat 64 (2 * 0) ∧
      s.gpr .r11 = BitVec.ofNat 64 (8 * (wx + 2)) ∧ s.gpr .r15 = BitVec.ofNat 64 (8 * p) ∧ s.mem = t.mem ∧
      Keep mmRegs t s := by
  simp only [Crt.gatherHead, seqs]
  refine WP.seq (WP.mono (gRegs_ok hc hw' hJ hE) fun t₁ ⟨h15, hcx, h11, h13, hbx, hm₁, hx₁, k₁⟩ => ?_)
  have hdi₁ : t₁.gpr .rdi = P := (k₁.gpr (by decide)).trans hc.good.rdi
  have hld : ∀ s : State, s.mem = t.mem → s.rd = t.rd → s.wr = t.wr →
      InRegions (s.rd ++ s.wr) (off P (8 * Crt.sNib)) 8 := fun s _ hrd hwr => by
    rw [hrd, hwr]; exact hc.ld (by decide)
  -- The masks.
  have mstep : ∀ (s : State) (j : Nat) (x : XReg), j < 8 → s.gpr .rdi = P → s.mem = t.mem → s.rd = t.rd →
      s.wr = t.wr → s.gpr .r15 = BitVec.ofNat 64 (8 * p) →
      WP isa (.block (Crt.selMask (BitVec.ofNat 32 j) (.mem (hdr Crt.sNib)) x)) s fun s' =>
        (∀ q < 2, q128 (s'.xmm x) q = mask (decide (8 * p + j = v))) ∧ (∀ y, y ≠ x → s'.xmm y = s.xmm y) ∧
        s'.mem = t.mem ∧ s'.gpr .rdi = P ∧ s'.rd = t.rd ∧ s'.wr = t.wr ∧ s'.gpr .r15 = BitVec.ofNat 64 (8 * p) ∧
        Keep [.r14] s s' :=
    fun s j x hj hdi hm hrd hwr h15 => WP.mono (gMask_ok hdi (hld s hm hrd hwr) (by rw [hm]; exact hN) h15
      (by omega) hj hv x) fun s' ⟨hq, hy, hm', k⟩ =>
        ⟨hq, hy, hm'.trans hm, (k.gpr (by decide)).trans hdi, k.2.1.trans hrd, k.2.2.trans hwr,
          (k.gpr (by decide)).trans h15, k⟩
  refine WP.seq (WP.mono (mstep t₁ 0 .xmm8 (by decide) hdi₁ hm₁ k₁.2.1 k₁.2.2 h15)
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
  -- The bases.
  have hcx₈ : s₈.gpr .rcx = off P (slot wx (8 + 8 * p)) := (kM.gpr (by decide)).trans hcx
  have h11₈ : s₈.gpr .r11 = BitVec.ofNat 64 (8 * (wx + 2)) := (kM.gpr (by decide)).trans h11
  refine WP.mono (gBases_ok hcx₈ h11₈) fun s₉ ⟨hb, h14, m₉, x₉, k₉⟩ => ?_
  have kA := kM.trans k₉
  have hG : GRegs P wx p v s₉ := by
    refine ⟨hb, by rw [kA.gpr (by decide)]; exact hbx, by rw [kA.gpr (by decide)]; exact h13, fun k hk q hq => ?_,
      fun q hq => by rw [x₉]; exact q₈ q hq⟩
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
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
  exact ⟨hG, h14, by rw [kA.gpr (by decide)]; exact h11, by rw [kA.gpr (by decide)]; exact h15,
    by rw [m₉, m₈, m₇], (k₁.trans kA).mono (by decide)⟩

/-- Pass `p` of the selection. -/
theorem gPass_ok {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v p : Nat}
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 16) (hp : p < 2) (hI : GathPassInv t₀ P wx minv X Xc v p t) :
    WP isa (seqs Crt.gatherPass) t fun t' => t'.zf = some (decide (p + 1 = 2)) ∧
      GathPassInv t₀ P wx minv X Xc v (p + 1) t' := by
  have hc := hI.ctx
  have hn := hc.scrT.nowrap
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have hTa := slot_succ wx Crt.aT
  have hT8 := slot_mono wx (show Crt.aT + 1 ≤ 8 by decide)
  rw [show seqs Crt.gatherPass = .seq (seqs Crt.gatherHead) (.seq (.loop (seqs Crt.gatherBody) .ne)
    (.block Crt.gatherEnd)) from rfl]
  refine WP.seq (WP.mono (gathHead_ok hc hw' hv hp hI.nib hI.idx hI.ent) fun s₉ ⟨hG, h14, h11, h15, hm₉, kA⟩ => ?_)
  have hs₉ : Scr s₉ P (slot wx 8 + tabBytes wx) := hc.scrT.congr kA.2.2
  -- The pairs.
  refine WP.seq (WP.mono (gLoop_ok hs₉ hG hp h14 (by omega) hw') fun s₁₀ hL => ?_)
  have kL : Keep [.r14] s₉ s₁₀ := ⟨fun r hr => hL.gpr r (by simpa using hr), hL.rd, hL.wr⟩
  have hc₁₀ : CExpCtx s₁₀ P wx minv X Xc := by
    refine hc.of_win (Frm.of_outside (o := slot wx Crt.aT) (n := 8 * (wx + 2)) ?_ (by simp [crtWinRanges]))
      (by rw [hL.wr, kA.2.2]) ((kA.trans kL).gpr (by decide))
    rw [← hm₉]; exact hL.out.mono (Nat.le_refl _) (by omega)
  refine WP.mono (gEnd_ok hc₁₀ hp (by rw [hL.gpr _ (by decide)]; exact hG.base 7 (by decide))
    (by rw [hL.gpr _ (by decide)]; exact h11) (by rw [hL.gpr _ (by decide)]; exact h15)) fun t' ⟨hm', hz, k'⟩ => ⟨hz, ?_⟩
  -- What changed.
  have o₁ := writeW_outside s₁₀.mem P (d := 8 * Crt.sEnt) (off P (slot wx (8 + 8 * (p + 1)))) (by decide)
  have o₂ := writeW_outside (s₁₀.mem.writeW (off P (8 * Crt.sEnt)) (off P (slot wx (8 + 8 * (p + 1))))) P
    (d := 8 * Crt.sJ) (BitVec.ofNat 64 (8 * (p + 1))) (by decide)
  rw [← hm'] at o₂
  have oL : Outside P (slot wx Crt.aT) (8 * (wx + 2)) t.mem s₁₀.mem := by
    rw [← hm₉]; exact hL.out.mono (Nat.le_refl _) (by omega)
  have fL : Frm P (selRanges wx) t.mem s₁₀.mem := Frm.of_outside oL (by simp [selRanges])
  have fE : Frm P (selRanges wx) s₁₀.mem t'.mem :=
    (Frm.of_outside o₁ (by simp [selRanges])).trans (Frm.of_outside o₂ (by simp [selRanges]))
  have hT : ∀ k < 2 * ((wx + 1) / 2), word t'.mem P (slot wx Crt.aT + 8 * k) = word s₁₀.mem P (slot wx Crt.aT + 8 * k) :=
    fun k hk => by
      have := hdr_lt_slot wx Crt.aT (show Crt.sJ < 32 by decide)
      have := hdr_lt_slot wx Crt.aT (show Crt.sEnt < 32 by decide)
      rw [o₂.word (by omega) (by omega), o₁.word (by omega) (by omega)]
  have hE : ∀ j < 16, ∀ k < 2 * ((wx + 1) / 2), word t.mem P (slot wx (8 + j) + 8 * k) =
      word t₀.mem P (slot wx (8 + j) + 8 * k) := fun j hj k hk =>
    hI.frm.word_eq (fun r hr => by
      have := hdr_lt_slot wx 8 (show 31 < 32 by decide)
      have := slot_mono wx (show 8 ≤ 8 + j by omega)
      simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega
      · simp only [Crt.sEnt, sFn]; omega
      · simp only [Crt.sJ, sFn]; omega) (by have := ent_le wx hj; omega)
  refine ⟨hc₁₀.of_win (fE.mono (selRanges_sub wx)) k'.2.2 (k'.gpr (by decide)), ?_, ?_, ?_, Or.inr fun k hk => ?_,
    hI.frm.trans (fL.trans fE), ((hI.keep.trans ((kA.trans kL).trans k')).mono (by decide))⟩
  · have := hdr_lt_slot wx Crt.aT (show Crt.sNib < 32 by decide)
    rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hL.out.word (by omega) (by omega), hm₉]
    exact hI.nib
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm', word_writeW_self]
  · rw [hT k hk, hL.val k hk]
    simp only [hk, ↓reduceIte, gval, gacc_eq, gath_and_mask, hm₉]
    have hold := hI.val
    have hv' : v < 16 := hv
    rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl
    · by_cases h8 : v < 8
      · simp [h8, show v ≤ 8 * 0 + 7 by omega, hE v (by omega) k hk]
      · simp [h8, show ¬ v ≤ 8 * 0 + 7 by omega]
    · rcases hold with h | hold
      · omega
      rw [hold k hk]
      by_cases h8 : v < 8
      · simp [h8, show ¬ 8 * 1 ≤ v by omega, show v < 8 * (1 + 1) by omega]
      · simp [h8, show 8 * 1 ≤ v by omega, show v ≤ 8 * 1 + 7 by omega, show v < 8 * (1 + 1) by omega,
          show 8 + 8 * 1 + (v - 8 * 1) = 8 + v by omega, hE v (by omega) k hk]

/-- The selection: `[aT] := T_v`. -/
theorem tabSel_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 16)
    (ht : word t.mem P (8 * Crt.sTab) = off P (slot wx 8)) (hN : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (seqs Crt.tabSelect) t fun t' => CExpCtx t' P wx minv X Xc ∧
      wv t'.mem P (slot wx Crt.aT) wx = wv t.mem P (slot wx (8 + v)) wx ∧
      Frm P (selRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  rw [tabSelect_eq]
  simp only [seqs]
  refine WP.seq (WP.mono (selInit_ok hc ht) fun t₁ ⟨hm₁, k₁⟩ => ?_)
  have o1 := writeW_outside t.mem P (d := 8 * Crt.sEnt) (off P (slot wx 8)) (by decide)
  have o2 := writeW_outside (t.mem.writeW (off P (8 * Crt.sEnt)) (off P (slot wx 8))) P (d := 8 * Crt.sJ)
    (BitVec.setWidth 64 (0 : BitVec 32)) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm P (selRanges wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [selRanges])).trans (Frm.of_outside o2 (by simp [selRanges]))
  have h₁ : GathPassInv t₁ P wx minv X Xc v 0 t₁ := by
    refine ⟨hc.of_win (f₁.mono (selRanges_sub wx)) k₁.2.2 (k₁.gpr (by decide)), ?_, ?_, ?_, .inl rfl,
      Frm.refl _ _ _, Keep.refl _ _⟩
    · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hN
    · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hm₁, word_writeW_self]; rfl
  refine WP.mono (wp_upto (a := 0) (N := 2) (by decide) (GathPassInv t₁ P wx minv X Xc v)
    (fun p _ hp s hI => gPass_ok hw hw' hv hp hI) (fun s h => h) h₁) fun t' hI => ?_
  have hEv : ∀ i < wx, word t₁.mem P (slot wx (8 + v) + 8 * i) = word t.mem P (slot wx (8 + v) + 8 * i) :=
    fun i hi => f₁.word_eq (fun r hr => by
      have := slot_mono wx (show 8 ≤ 8 + v by omega)
      have := hdr_lt_slot wx 8 (show 31 < 32 by decide)
      simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · have := slot_le (w := wx) (show Crt.aT < 8 by decide); simp only; omega
      · simp only [Crt.sEnt, sFn]; omega
      · simp only [Crt.sJ, sFn]; omega) (by have := ent_le wx hv; omega)
  refine ⟨hI.ctx, wv_congr2 fun i hi => ?_, f₁.trans hI.frm, (k₁.trans hI.keep).mono (by decide)⟩
  rcases hI.val with h | h
  · omega
  rw [h i (by omega), ite_eq_left (by omega), hEv i hi]

/-! ## A window -/

/-- The window count decremented, `ZF` when it reaches 0. -/
theorem crtBitEnd_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc b : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hb : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b)
    (hb' : b < 2 ^ 31) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sBit)), .alu .sub .rax (.imm 1), .store (hdr Crt.sBit) .rax]) t
      fun t' => t'.mem = t.mem.writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b - 1)) ∧
        t'.zf = some (decide (b - 1 = 0)) ∧ Keep [.rax] t t' := by
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off P (8 * i)) 8 := fun i hi =>
    hc.good.scr.ld (by have := hdr_lt_slot wx 8 hi; omega_arith)
  have hs : ∀ i < 32, InRegions t.wr (off P (8 * i)) 8 := fun i hi =>
    hc.good.scr.st (by have := hdr_lt_slot wx 8 hi; omega_arith)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem.writeW (off P (8 * Crt.sBit))
      (BitVec.ofNat 64 (b - 1)) ∧ t'.zf = some (decide (b - 1 = 0))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hl Crt.sBit (by decide), hs Crt.sBit (by decide), hb,
      ofNat64_pred hb1 (by omega_arith), ofNat64_beq_zero (show b - 1 < 2 ^ 64 by omega_arith)]) rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩

/-- `Y := Y² R⁻¹`: `x^E R` becomes `x^(2E) R`. -/
theorem crtSq_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E : Nat} (hc : CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hY : wv t.mem P (slot wx aY) wx < X)
    (hYv : Q → wv t.mem P (slot wx aY) wx % X = x ^ E * 2 ^ (64 * wx) % X) :
    WP isa (M.mm aY aY aY) t fun t' => CExpCtx t' P wx minv X Xc ∧ wv t'.mem P (slot wx aY) wx < X ∧
      (Q → wv t'.mem P (slot wx aY) wx % X = x ^ (2 * E) * 2 ^ (64 * wx) % X) ∧
      (∀ k < 32, word t'.mem P (8 * k) = word t.mem P (8 * k)) ∧
      Frm P (crtWinRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  refine WP.mono (M.mm_ok (o := aY) (a := aY) (b := aY) hc.good (Nat.le_refl _) hw (by omega_arith)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hc.n]; exact hY)) fun t₁ ⟨_, hlt₁, hm₁, ha₁, k₁⟩ => ?_
  rw [hc.n] at hlt₁ hm₁
  have f₁ : Frm P (crtWinRanges wx) t.mem t₁.mem := Frm.of_arrays ha₁ (by simp [crtWinRanges])
  exact ⟨hc.of_win f₁ k₁.2.2 (k₁.gpr (by decide)), hlt₁, fun hq => VG.Proof.Bignum.mont_sq hR (hYv hq) hm₁,
    fun k hk => ha₁.hslot hk, f₁, k₁⟩

/-- `Y := Y T R⁻¹`: `x^E R` and `T ≡ x^v R` give `x^(E+v) R`. -/
theorem crtMulT_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E v : Nat} (hc : CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hT : wv t.mem P (slot wx Crt.aT) wx < X)
    (hYv : Q → wv t.mem P (slot wx aY) wx % X = x ^ E * 2 ^ (64 * wx) % X)
    (hTv : Q → wv t.mem P (slot wx Crt.aT) wx % X = x ^ v * 2 ^ (64 * wx) % X) :
    WP isa (M.mm aY aY Crt.aT) t fun t' => CExpCtx t' P wx minv X Xc ∧ wv t'.mem P (slot wx aY) wx < X ∧
      (Q → wv t'.mem P (slot wx aY) wx % X = x ^ (E + v) * 2 ^ (64 * wx) % X) ∧
      (∀ k < 32, word t'.mem P (8 * k) = word t.mem P (8 * k)) ∧
      Frm P (crtWinRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  refine WP.mono (M.mm_ok (o := aY) (a := aY) (b := Crt.aT) hc.good (Nat.le_refl _) hw (by omega_arith)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hc.n]; exact hT)) fun t₁ ⟨_, hlt₁, hm₁, ha₁, k₁⟩ => ?_
  rw [hc.n] at hlt₁ hm₁
  have f₁ : Frm P (crtWinRanges wx) t.mem t₁.mem := Frm.of_arrays ha₁ (by simp [crtWinRanges])
  exact ⟨hc.of_win f₁ k₁.2.2 (k₁.gpr (by decide)), hlt₁, fun hq => mont_mulT hR (hYv hq) (hTv hq) hm₁,
    fun k hk => ha₁.hslot hk, f₁, k₁⟩

/-- The window's value: `(V >> 4) & 15`. -/
theorem nibMask (V : Nat) (hV : V < 2 ^ 64) :
    (BitVec.ofNat 64 V >>> 4 &&& BitVec.signExtend 64 (15 : BitVec 32)) = BitVec.ofNat 64 (V / 16 % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hV,
    Nat.shiftRight_eq_div_pow, show (BitVec.signExtend 64 (15 : BitVec 32)).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega_arith

/-- The block after the squarings: the window into `sNib`, and `sV` up 4 bits. -/
theorem winMid_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc V : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hV : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 60) :
    WP isa (.block [.mov .rdx (.mem (hdr Crt.sV)), .mov .rax (.reg .rdx), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .store (hdr Crt.sV) .rax,
      .shift .shr .rdx 4, .alu .and .rdx (.imm 15), .store (hdr Crt.sNib) .rdx]) t fun t' =>
      t'.mem = (t.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (16 * V))).writeW (off P (8 * Crt.sNib))
        (BitVec.ofNat 64 (V / 16 % 16)) ∧ Keep [.rdx, .rax] t t' := by
  refine WP.mono (WP.keep [.rdx, .rax] (Q := fun t' => t'.mem = (t.mem.writeW (off P (8 * Crt.sV))
      (BitVec.ofNat 64 (16 * V))).writeW (off P (8 * Crt.sNib)) (BitVec.ofNat 64 (V / 16 % 16))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sV) (by decide), hc.st (i := Crt.sV) (by decide),
      hc.st (i := Crt.sNib) (by decide), hV, nibMask V (by omega_arith), ← BitVec.ofNat_add]
    rw [show V + V + (V + V) + (V + V + (V + V)) + (V + V + (V + V) + (V + V + (V + V))) = 16 * V by omega_arith])
    rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩

theorem expWin_eq (mul : Nat → Nat → Nat → Prog isa) : Crt.expWin mul =
    [mul aY aY aY, mul aY aY aY, mul aY aY aY, mul aY aY aY,
      .block [.mov .rdx (.mem (hdr Crt.sV)), .mov .rax (.reg .rdx), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .store (hdr Crt.sV) .rax,
        .shift .shr .rdx 4, .alu .and .rdx (.imm 15), .store (hdr Crt.sNib) .rdx]] ++
    (Crt.tabSelect ++ [mul aY aY Crt.aT,
      .block [.mov .rax (.mem (hdr Crt.sBit)), .alu .sub .rax (.imm 1), .store (hdr Crt.sBit) .rax]]) := rfl

/-- One window: `Y ≡ x^E R` becomes `x^(16 E + v) R` for the window
`v = ⌊V / 16⌋ mod 16` of the value `V` in `sV`, which moves up 4 bits; the
window count `b` drops. -/
theorem crtWin_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E V b : Nat} (hc : CExpCtx t P wx minv X Xc) (htab : CTab t.mem P wx X Q x) (hw : 2 ≤ wx)
    (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hY : wv t.mem P (slot wx aY) wx < X)
    (hYv : Q → wv t.mem P (slot wx aY) wx % X = x ^ E * 2 ^ (64 * wx) % X)
    (hV : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 56)
    (hb : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) (hb' : b < 2 ^ 31) :
    WP isa (seqs (Crt.expWin M.mm)) t fun t' => CExpCtx t' P wx minv X Xc ∧ CTab t'.mem P wx X Q x ∧
      wv t'.mem P (slot wx aY) wx < X ∧
      (Q → wv t'.mem P (slot wx aY) wx % X = x ^ (16 * E + V / 16 % 16) * 2 ^ (64 * wx) % X) ∧
      word t'.mem P (8 * Crt.sV) = BitVec.ofNat 64 (16 * V) ∧
      word t'.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (b - 1) ∧
      t'.zf = some (decide (b - 1 = 0)) ∧ Frm P (crtWinRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  rw [expWin_eq]
  refine wp_seqs_append (by simp) (by simp [tabSelect_eq]) ?_
  simp only [seqs]
  -- Four squarings.
  refine WP.seq (WP.mono (crtSq_ok M hc hw hw' hR hY hYv) fun t₁ ⟨hc₁, hY₁, hYv₁, hh₁, f₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (crtSq_ok M hc₁ hw hw' hR hY₁ hYv₁) fun t₂ ⟨hc₂, hY₂, hYv₂, hh₂, f₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (crtSq_ok M hc₂ hw hw' hR hY₂ hYv₂) fun t₃ ⟨hc₃, hY₃, hYv₃, hh₃, f₃, k₃⟩ => ?_)
  refine WP.seq (WP.mono (crtSq_ok M hc₃ hw hw' hR hY₃ hYv₃) fun t₄ ⟨hc₄, hY₄, hYv₄, hh₄, f₄, k₄⟩ => ?_)
  have hh04 : ∀ k < 32, word t₄.mem P (8 * k) = word t.mem P (8 * k) := fun k hk =>
    (hh₄ k hk).trans ((hh₃ k hk).trans ((hh₂ k hk).trans (hh₁ k hk)))
  have f04 : Frm P (crtWinRanges wx) t.mem t₄.mem := ((f₁.trans f₂).trans f₃).trans f₄
  have k04 : Keep mmRegs t t₄ := (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)
  -- The window, and `sV` up.
  refine WP.mono (winMid_ok (V := V) hc₄ (by rw [hh04 _ (by decide)]; exact hV) (by omega_arith)) fun t₅ ⟨hm₅, k₅⟩ => ?_
  have o1 := writeW_outside t₄.mem P (d := 8 * Crt.sV) (BitVec.ofNat 64 (16 * V)) (by decide)
  have o2 := writeW_outside (t₄.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (16 * V))) P (d := 8 * Crt.sNib)
    (BitVec.ofNat 64 (V / 16 % 16)) (by decide)
  rw [← hm₅] at o2
  have f₅ : Frm P (crtWinRanges wx) t₄.mem t₅.mem :=
    (Frm.of_outside o1 (by simp [crtWinRanges])).trans (Frm.of_outside o2 (by simp [crtWinRanges]))
  have hc₅ := hc₄.of_win f₅ k₅.2.2 (k₅.gpr (by decide))
  have htab₅ : CTab t₅.mem P wx X Q x := htab.of_win (f04.trans f₅) hn
  have hY₅ : wv t₅.mem P (slot wx aY) wx = wv t₄.mem P (slot wx aY) wx := by
    rw [o2.wv (by have := hdr_lt_slot wx aY (show Crt.sNib < 32 by decide); omega_arith) (by omega_arith),
      o1.wv (by have := hdr_lt_slot wx aY (show Crt.sV < 32 by decide); omega_arith) (by omega_arith)]
  have hh₅ : ∀ k < 32, k ≠ Crt.sV → k ≠ Crt.sNib → word t₅.mem P (8 * k) = word t.mem P (8 * k) :=
    fun k hk h1 h2 => by
      rw [hm₅, hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h1),
        hh04 k hk]
  have hv16 : V / 16 % 16 < 16 := Nat.mod_lt _ (by decide)
  -- `T := T_v`.
  refine wp_seqs_append (by simp [tabSelect_eq]) (by simp) ?_
  refine WP.mono (tabSel_ok hc₅ hw hw' hv16 (by rw [hh₅ _ (by decide) (by decide) (by decide)]; exact htab.tab)
    (by rw [hm₅, word_writeW_self])) fun t₆ ⟨hc₆, hT₆, f₆, k₆⟩ => ?_
  have f₆' : Frm P (crtWinRanges wx) t₅.mem t₆.mem := f₆.mono (selRanges_sub wx)
  have hY₆ : wv t₆.mem P (slot wx aY) wx = wv t₅.mem P (slot wx aY) wx :=
    f₆.wv_eq (fun r hr => by
      have := slot_sep (w := wx) (show aY ≠ Crt.aT by decide)
      simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega_arith
      · simp only [Crt.sEnt, sFn]; have := hdr_lt_slot wx aY (show 31 < 32 by decide); omega_arith
      · simp only [Crt.sJ, sFn]; have := hdr_lt_slot wx aY (show 31 < 32 by decide); omega_arith) (by omega_arith)
  have hh₆ : ∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → word t₆.mem P (8 * k) = word t₅.mem P (8 * k) :=
    fun k hk h1 h2 => f₆.word_eq (fun r hr => by
      have := hdr_lt_slot wx Crt.aT hk
      simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega_arith
      · simp only [Crt.sEnt, sFn] at h1 ⊢; omega_arith
      · simp only [Crt.sJ, sFn] at h2 ⊢; omega_arith) (by omega_arith)
  have htab₆ : CTab t₆.mem P wx X Q x := htab₅.of_win f₆' hn
  simp only [seqs]
  -- `Y := Y T`.
  refine WP.seq (WP.mono (crtMulT_ok M (Q := Q) (x := x) (E := 16 * E) (v := V / 16 % 16) hc₆ hw hw' hR
    (by rw [hT₆]; exact htab₅.lt _ hv16)
    (fun hq => by rw [hY₆, hY₅, hYv₄ hq, show 2 * (2 * (2 * (2 * E))) = 16 * E by omega_arith])
    (fun hq => by rw [hT₆]; exact htab₅.val hq _ hv16)) fun t₇ ⟨hc₇, hY₇, hYv₇, hh₇, f₇, k₇⟩ => ?_)
  -- The count.
  refine WP.mono (crtBitEnd_ok hc₇ (by
    rw [hh₇ _ (by decide), hh₆ _ (by decide) (by decide) (by decide), hh₅ _ (by decide) (by decide) (by decide)]
    exact hb) hb1 hb') fun t' ⟨hm', hz', k'⟩ => ?_
  have o₈ := writeW_outside t₇.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 (b - 1)) (by decide)
  rw [← hm'] at o₈
  have f₈ : Frm P (crtWinRanges wx) t₇.mem t'.mem := Frm.of_outside o₈ (by simp [crtWinRanges])
  have fall : Frm P (crtWinRanges wx) t.mem t'.mem := (((f04.trans f₅).trans f₆').trans f₇).trans f₈
  refine ⟨hc₇.of_win f₈ k'.2.2 (k'.gpr (by decide)), htab.of_win fall hn, ?_, ?_, ?_, ?_, hz', fall,
    ((((k04.trans k₅).trans k₆).trans k₇).trans k').mono (by decide)⟩
  · rw [o₈.wv (by have := hdr_lt_slot wx aY (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith)]; exact hY₇
  · intro hq
    rw [o₈.wv (by have := hdr_lt_slot wx aY (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith)]
    exact hYv₇ hq
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₇ _ (by decide),
      hh₆ _ (by decide) (by decide) (by decide), hm₅, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self]
  · rw [hm', word_writeW_self]

/-! ## The windows of a byte -/

/-- After `j` windows of the byte `v` from `t₀`, where `Y ≡ x^E R`. -/
structure CWinInv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) (Q : Prop) (x E v : Nat)
    (j : Nat) (t : State) : Prop where
  ctx : CExpCtx t P wx minv X Xc
  tab : CTab t.mem P wx X Q x
  ylt : wv t.mem P (slot wx aY) wx < X
  y : Q → wv t.mem P (slot wx aY) wx % X = x ^ (E * 16 ^ j + v / 16 ^ (2 - j)) * 2 ^ (64 * wx) % X
  v : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 (v * 16 ^ j)
  b : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (2 - j)
  frm : Frm P (crtWinRanges wx) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

/-- Window `j` of the byte `v`. -/
theorem crtWinStep_ok (M : Mont) {t s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E v : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hv : v < 256) {j : Nat}
    (hj : j < 2) (hI : CWinInv t P wx minv X Xc Q x E v j s) :
    WP isa (seqs (Crt.expWin M.mm)) s fun s' => s'.zf = some (decide (j + 1 = 2)) ∧
      CWinInv t P wx minv X Xc Q x E v (j + 1) s' := by
  have hp : 16 ^ j ≤ 16 := by rcases (show j = 0 ∨ j = 1 by omega_arith) with rfl | rfl <;> decide
  refine WP.mono (crtWin_ok M (E := E * 16 ^ j + v / 16 ^ (2 - j)) hI.ctx hI.tab hw hw' hR hI.ylt hI.y hI.v
    (by have := Nat.mul_le_mul_left v hp; omega_arith) hI.b (by omega_arith) (by omega_arith))
    fun s' ⟨hc', htab', hY', hYv', hV', hb', hz', hfr', k'⟩ => ⟨?_, hc', htab', hY', ?_, ?_, ?_,
      hI.frm.trans hfr', (hI.keep.trans k').mono (by decide)⟩
  · rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega_arith)
  · intro hq; rw [hYv' hq, win_step hv hj]
  · rw [hV', Nat.pow_succ]; congr 1; rw [Nat.mul_comm 16, Nat.mul_assoc]
  · rw [hb']; congr 1

/-- The two windows of the byte `v`: `Y ≡ x^E R` becomes `x^(256 E + v) R`. -/
theorem crtWins_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E v : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hv : v < 256)
    (h0 : CWinInv t P wx minv X Xc Q x E v 0 t) :
    WP isa (.loop (seqs (Crt.expWin M.mm)) .ne) t (CWinInv t P wx minv X Xc Q x E v 2) :=
  wp_upto (a := 0) (N := 2) (by decide) (CWinInv t P wx minv X Xc Q x E v)
    (fun _ _ hj _ hI => crtWinStep_ok M hw hw' hR hv hj hI) (fun _ h => h) h0

/-! ## The bytes of the exponent -/

/-- After `i` bytes of the exponent (`L` bytes `eb` at `ep`) from `t₀`. -/
structure CByteInv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) (Q : Prop) (x : Nat)
    (ep : Addr) (L : Nat) (eb : List Byte) (i : Nat) (t : State) : Prop where
  ctx : CExpCtx t P wx minv X Xc
  tab : CTab t.mem P wx X Q x
  ylt : wv t.mem P (slot wx aY) wx < X
  y : Q → wv t.mem P (slot wx aY) wx % X = x ^ pre eb i * 2 ^ (64 * wx) % X
  idx : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i
  e : word t.mem P (8 * Crt.sExp) = ep
  len : word t.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L
  frm : Frm P (crtExpRanges wx) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

/-- The loads of the byte's address. -/
theorem crtByteHead1_ok {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop} {x : Nat}
    {ep : Addr} {L : Nat} {eb : List Byte} {i : Nat} (hI : CByteInv t₀ P wx minv X Xc Q x ep L eb i t) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI))]) t fun t₁ =>
      t₁.gpr .rax = ep ∧ t₁.gpr .rcx = BitVec.ofNat 64 i ∧ CByteInv t₀ P wx minv X Xc Q x ep L eb i t₁ := by
  have hc := hI.ctx
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t₁ => t₁.gpr .rax = ep ∧ t₁.gpr .rcx = BitVec.ofNat 64 i ∧
      t₁.mem = t.mem) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sExp) (by decide), hc.ld (i := Crt.sI) (by decide),
      hI.e, hI.idx]) rfl)
    fun t₁ ⟨⟨h1, h2, hm⟩, k⟩ => ⟨h1, h2, ?_⟩
  have hf : Frm P (crtExpRanges wx) t.mem t₁.mem := by rw [hm]; exact Frm.refl _ _ _
  exact ⟨hc.of_frm hf k.2.2 (k.gpr (by decide)), hm ▸ hI.tab, hm ▸ hI.ylt, hm ▸ hI.y, hm ▸ hI.idx, hm ▸ hI.e,
    hm ▸ hI.len, hI.frm.trans hf, (hI.keep.trans k).mono (by decide)⟩

/-- The byte into `sV`, and the window count 2: the start of the windows. -/
theorem crtByteHead2_ok {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop} {x : Nat}
    {ep : Addr} {L : Nat} {eb : List Byte} {i : Nat} (hL : eb.length = L) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hout : ∀ i < L, slot wx 8 + tabBytes wx ≤ ofs P (ep + BitVec.ofNat 64 i))
    (hI : CByteInv t₀ P wx minv X Xc Q x ep L eb i t) (hax : t.gpr .rax = ep)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 i) :
    WP isa (.block [.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax,
      .mov32 .rax (.imm 2), .store (hdr Crt.sBit) .rax]) t fun t₁ =>
      t₁.mem = (t.mem.writeW (off P (8 * Crt.sV)) ((eb[i]'(by omega_arith)).setWidth 64)).writeW
        (off P (8 * Crt.sBit)) (BitVec.setWidth 64 (2 : BitVec 32)) ∧ Keep [.rax] t t₁ ∧
      CWinInv t₁ P wx minv X Xc Q x (pre eb i) (eb[i]'(by omega_arith)).toNat 0 t₁ := by
  have hc := hI.ctx
  have hn := hc.scrT.nowrap
  have hrdi : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd i hi
  have hbi : t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith) := by
    rw [hI.frm _ fun r hr => Or.inr (by have := (crtExpRanges_ok wx r hr).2; have := hout i hi; omega_arith)]
    exact hbytes i hi
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ => t₁.mem = (t.mem.writeW (off P (8 * Crt.sV))
      ((eb[i]'(by omega_arith)).setWidth 64)).writeW (off P (8 * Crt.sBit)) (BitVec.setWidth 64 (2 : BitVec 32))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hax, hcx, byteRead, hrdi, hbi, hc.st (i := Crt.sV) (by decide),
      hc.st (i := Crt.sBit) (by decide)]) rfl)
    fun t₁ ⟨hm₁, k₁⟩ => ⟨hm₁, k₁, ?_⟩
  have o1 := writeW_outside t.mem P (d := 8 * Crt.sV) ((eb[i]'(by omega_arith)).setWidth 64) (by decide)
  have o2 := writeW_outside (t.mem.writeW (off P (8 * Crt.sV)) ((eb[i]'(by omega_arith)).setWidth 64)) P
    (d := 8 * Crt.sBit) (BitVec.setWidth 64 (2 : BitVec 32)) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm P (crtWinRanges wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [crtWinRanges])).trans (Frm.of_outside o2 (by simp [crtWinRanges]))
  have hc₁ := hc.of_win f₁ k₁.2.2 (k₁.gpr (by decide))
  have hv : (eb[i]'(by omega_arith)).toNat < 256 := (eb[i]'(by omega_arith)).isLt
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hYe : wv t₁.mem P (slot wx aY) wx = wv t.mem P (slot wx aY) wx := by
    rw [o2.wv (by have := hdr_lt_slot wx aY (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith),
      o1.wv (by have := hdr_lt_slot wx aY (show Crt.sV < 32 by decide); omega_arith) (by omega_arith)]
  refine ⟨hc₁, hI.tab.of_win f₁ hn, hYe ▸ hI.ylt, fun hq => ?_, ?_, ?_, Frm.refl _ _ _, Keep.refl _ _⟩
  · rw [hYe, hI.y hq, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, Nat.div_eq_of_lt (show _ < 16 ^ 2 from hv),
      Nat.add_zero]
  · rw [o2.word (by decide) (by decide), word_writeW_self, setWidth_byte, Nat.pow_zero]
  · rw [hm₁, word_writeW_self]; rfl

theorem crtByteHead_eq : ([.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI)),
      .movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 2),
      .store (hdr Crt.sBit) .rax] : List Instr) =
    ([.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI))] : List Instr) ++
    ([.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 2),
      .store (hdr Crt.sBit) .rax] : List Instr) := rfl

/-- One byte of the exponent: its two windows, then the next byte. -/
theorem crtByte_ok (M : Mont) {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} {ep : Addr} {L : Nat} {eb : List Byte} {i : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hL : eb.length = L) (hL' : L < 2 ^ 31) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hout : ∀ i < L, slot wx 8 + tabBytes wx ≤ ofs P (ep + BitVec.ofNat 64 i))
    (hI : CByteInv t₀ P wx minv X Xc Q x ep L eb i t) :
    WP isa (seqs [.block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI)),
        .movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 2),
        .store (hdr Crt.sBit) .rax],
      .loop (seqs (Crt.expWin M.mm)) .ne,
      .block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
        .alu .cmp .rax (.mem (hdr Crt.sExpLen))]]) t fun t' =>
      t'.zf = some (decide (i + 1 = L)) ∧ CByteInv t₀ P wx minv X Xc Q x ep L eb (i + 1) t' := by
  have hn := hI.ctx.scrT.nowrap
  simp only [seqs]
  rw [crtByteHead_eq]
  refine WP.seq ((WP.block_append_iff).mpr (WP.mono (crtByteHead1_ok hI) fun tₐ ⟨hax, hcx, hIₐ⟩ =>
    WP.mono (crtByteHead2_ok hL hi hrd hbytes hout hIₐ hax hcx) fun t₁ ⟨hm₁, k₁, hB0⟩ => ?_))
  have hv : (eb[i]'(by omega_arith)).toNat < 256 := (eb[i]'(by omega_arith)).isLt
  refine WP.seq (WP.mono (crtWins_ok M hw hw' hR hv hB0) fun t₂ h₂ => ?_)
  -- The next byte.
  have hc₂ := h₂.ctx
  have hh₂ : ∀ k < 32, k ≠ Crt.sV → k ≠ Crt.sBit → k ≠ Crt.sNib → k ≠ Crt.sEnt → k ≠ Crt.sJ →
      word t₂.mem P (8 * k) = word tₐ.mem P (8 * k) := fun k hk h1 h2 h3 h4 h5 => by
    rw [h₂.frm.word_eq (crtWinRanges_hdr wx hk h1 h2 h3 h4 h5) (by omega_arith), hm₁,
      hdrStore_hdr (i := Crt.sBit) _ _ _ (by decide) hk (Ne.symm h2),
      hdrStore_hdr (i := Crt.sV) _ _ _ (by decide) hk (Ne.symm h1)]
  have hidx₂ := (hh₂ Crt.sI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hIₐ.idx
  have he₂ := (hh₂ Crt.sExp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hIₐ.e
  have hlen₂ := (hh₂ Crt.sExpLen (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    hIₐ.len
  have hlen₂' : (t₂.mem.writeW (off P (8 * Crt.sI)) (BitVec.ofNat 64 (i + 1))).readW (off P (8 * Crt.sExpLen)) 64 =
      BitVec.ofNat 64 L := by
    rw [← hlen₂]; exact hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t₂.mem.writeW (off P (8 * Crt.sI))
      (BitVec.ofNat 64 (i + 1)) ∧ t'.zf = some (decide (i + 1 = L))) (by
    xrun [State.ea, hdr, hc₂.good.rdi, hdrOff, hc₂.ld (i := Crt.sI) (by decide), hc₂.st (i := Crt.sI) (by decide),
      hidx₂, ofNat_add_one, hc₂.ld (i := Crt.sExpLen) (by decide), hlen₂',
      ofNat_sub_beq (show i + 1 < 2 ^ 64 by omega_arith) (show L < 2 ^ 64 by omega_arith)]) rfl)
    fun t' ⟨⟨hm', hz'⟩, k'⟩ => ⟨hz', ?_⟩
  have o' := writeW_outside t₂.mem P (d := 8 * Crt.sI) (BitVec.ofNat 64 (i + 1)) (by decide)
  rw [← hm'] at o'
  have f' : Frm P (crtExpRanges wx) t₂.mem t'.mem := Frm.of_outside o' (by simp [crtExpRanges])
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hYe : wv t'.mem P (slot wx aY) wx = wv t₂.mem P (slot wx aY) wx :=
    o'.wv (by have := hdr_lt_slot wx aY (show Crt.sI < 32 by decide); omega_arith) (by omega_arith)
  refine ⟨hc₂.of_frm f' k'.2.2 (k'.gpr (by decide)), ?_, hYe ▸ h₂.ylt, fun hq => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [o'.word (by decide) (by decide)]; exact h₂.tab.tab,
      fun j hj => by rw [o'.wv (by have := hdr_lt_slot wx (8 + j) (show Crt.sI < 32 by decide); omega_arith)
        (by have := ent_le wx hj; omega_arith)]; exact h₂.tab.lt j hj,
      fun hq j hj => by rw [o'.wv (by have := hdr_lt_slot wx (8 + j) (show Crt.sI < 32 by decide); omega_arith)
        (by have := ent_le wx hj; omega_arith)]; exact h₂.tab.val hq j hj⟩
  · rw [hYe, h₂.y hq, pre_succ eb (by omega_arith)]
    congr 3
    simp only [Nat.reducePow, Nat.reduceSub, Nat.pow_zero, Nat.div_one]
    omega_arith
  · rw [hm', word_writeW_self]
  · rw [hm', hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)]; exact he₂
  · rw [hm', hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen₂
  · have f₁ : Frm P (crtExpRanges wx) tₐ.mem t₁.mem := by
      rw [hm₁]
      exact (Frm.of_outside (writeW_outside tₐ.mem P _ (d := 8 * Crt.sV) (by decide))
        (by simp [crtExpRanges, crtWinRanges])).trans
        (Frm.of_outside (writeW_outside _ P _ (d := 8 * Crt.sBit) (by decide))
          (by simp [crtExpRanges, crtWinRanges]))
    exact ((hIₐ.frm.trans f₁).trans (h₂.frm.mono (crtWinRanges_sub wx))).trans f'
  · exact (((hIₐ.keep.trans k₁).trans h₂.keep).trans k').mono (by decide)

/-! ## The table -/

/-- The table's base, past the last array, into `sTab` and `sEnt`. -/
theorem tabInit_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) :
    WP isa (.block [.mov .rax (.mem (hdr (sArr aOne))), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2),
      .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx),
      .store (hdr Crt.sTab) .rax, .store (hdr Crt.sEnt) .rax]) t fun t' =>
      t'.mem = (t.mem.writeW (off P (8 * Crt.sTab)) (off P (slot wx 8))).writeW (off P (8 * Crt.sEnt))
        (off P (slot wx 8)) ∧ Keep [.rax, .rdx] t t' := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t' => t'.mem = (t.mem.writeW (off P (8 * Crt.sTab))
      (off P (slot wx 8))).writeW (off P (8 * Crt.sEnt)) (off P (slot wx 8))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := sArr aOne) (by decide), hc.ld (i := sW) (by decide),
    hc.st (i := Crt.sTab) (by decide), hc.st (i := Crt.sEnt) (by decide), hc.good.hdr.harr aOne (by decide),
    hc.good.hdr.hw]
  rw [entStep, ← slot_succ]
  rfl

/-- `sBit := 14`, the count of the table's products. -/
theorem cnt14_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) :
    WP isa (.block [.mov32 .rax (.imm 14), .store (hdr Crt.sBit) .rax]) t fun t' =>
      t'.mem = t.mem.writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 14) ∧ Keep [.rax] t t' := by
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem.writeW (off P (8 * Crt.sBit))
      (BitVec.ofNat 64 14)) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.st (i := Crt.sBit) (by decide)]
  rfl

/-- After `i` of the table's products from `t₀`: entries `0 … i + 1`
written, `T ≡ x^(i+1) R` the last. -/
structure BuildInv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) (Q : Prop) (x : Nat)
    (i : Nat) (t : State) : Prop where
  ctx : CExpCtx t P wx minv X Xc
  tab : word t.mem P (8 * Crt.sTab) = off P (slot wx 8)
  ent : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + (i + 1)))
  cnt : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (14 - i)
  tlt : wv t.mem P (slot wx Crt.aT) wx < X
  tval : Q → wv t.mem P (slot wx Crt.aT) wx % X = x ^ (i + 1) * 2 ^ (64 * wx) % X
  elt : ∀ j < i + 2, wv t.mem P (slot wx (8 + j)) wx < X
  eval : Q → ∀ j < i + 2, wv t.mem P (slot wx (8 + j)) wx % X = x ^ j * 2 ^ (64 * wx) % X
  frm : Frm P (buildRanges wx) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

/-- A product of the table's build. -/
def tabBody (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [mul Crt.aT Crt.aT Crt.aXc, Crt.nextEnt] ++ (Crt.toEnt Crt.aT ++
    [.block [.mov .rax (.mem (hdr Crt.sBit)), .alu .sub .rax (.imm 1), .store (hdr Crt.sBit) .rax]])

/-- The table's product `i`. -/
theorem buildStep_ok (M : Mont) {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hXN : Xc < X)
    (hXc : Q → Xc % X = x * 2 ^ (64 * wx) % X) {i : Nat} (hi : i < 14)
    (hI : BuildInv t₀ P wx minv X Xc Q x i t) :
    WP isa (seqs (tabBody M.mm)) t
      fun t' => t'.zf = some (decide (i + 1 = 14)) ∧ BuildInv t₀ P wx minv X Xc Q x (i + 1) t' := by
  have hc := hI.ctx
  have hn := hc.scrT.nowrap
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  unfold tabBody
  refine wp_seqs_append (by simp) (by simp [Crt.toEnt]) ?_
  simp only [seqs]
  -- `T := T Xc`.
  refine WP.seq (WP.mono (M.mm_ok (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) hc.good (Nat.le_refl _) hw (by omega_arith)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hc.x, hc.n]; exact hXN)) fun t₁ ⟨_, hlt₁, hm₁, ha₁, k₁⟩ => ?_)
  rw [hc.n] at hlt₁
  rw [hc.n, hc.x] at hm₁
  have f₁ : Frm P (buildRanges wx) t.mem t₁.mem := Frm.of_arrays ha₁ (by simp [buildRanges])
  have hc₁ := hc.of_frm (f₁.mono (buildRanges_sub wx)) k₁.2.2 (k₁.gpr (by decide))
  have he₁ : ∀ j < 16, wv t₁.mem P (slot wx (8 + j)) wx = wv t.mem P (slot wx (8 + j)) wx := fun j hj =>
    ha₁.wv_eq (fun k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      have := slot_mono wx (show 8 ≤ 8 + j by omega_arith)
      rcases hk with rfl | rfl | rfl
      · exact Or.inr (by have := slot_le (w := wx) (show aAcc < 8 by decide); omega_arith)
      · exact Or.inr (by have := slot_le (w := wx) (show aTmp < 8 by decide); omega_arith)
      · exact Or.inr (by omega_arith)) (by have := ent_le wx hj; omega_arith)
  -- `sEnt` up.
  refine WP.mono (nextEnt_ok (e := slot wx (8 + (i + 1))) hc₁ (by rw [ha₁.hslot (by decide)]; exact hI.ent))
    fun t₂ ⟨hm₂, k₂⟩ => ?_
  have o₂ := writeW_outside t₁.mem P (d := 8 * Crt.sEnt) (off P (slot wx (8 + (i + 1)) + 8 * (wx + 2))) (by decide)
  rw [← hm₂] at o₂
  have f₂ : Frm P (buildRanges wx) t₁.mem t₂.mem := Frm.of_outside o₂ (by simp [buildRanges])
  have hc₂ := hc₁.of_frm (f₂.mono (buildRanges_sub wx)) k₂.2.2 (k₂.gpr (by decide))
  have hT₂ : wv t₂.mem P (slot wx Crt.aT) wx = wv t₁.mem P (slot wx Crt.aT) wx :=
    o₂.wv (by have := hdr_lt_slot wx Crt.aT (show Crt.sEnt < 32 by decide); omega_arith) (by omega_arith)
  have he₂ : ∀ j < 16, wv t₂.mem P (slot wx (8 + j)) wx = wv t₁.mem P (slot wx (8 + j)) wx := fun j hj =>
    o₂.wv (by have := hdr_lt_slot wx (8 + j) (show Crt.sEnt < 32 by decide); omega_arith) (by have := ent_le wx hj; omega_arith)
  -- Entry `i + 2 := T`.
  refine wp_seqs_append (by simp [Crt.toEnt]) (by simp) ?_
  refine WP.mono (toEnt_ok hc₂ hw hw' (a := Crt.aT) (j := i + 2) (by decide) (by omega_arith) (by
    rw [hm₂, word_writeW_self, ← slot_succ]; rfl)) fun t₃ ⟨hv₃, o₃, k₃⟩ => ?_
  have hE := ent_le wx (show i + 2 < 16 by omega_arith)
  have hE8 := slot_mono wx (show 8 ≤ 8 + (i + 2) by omega_arith)
  have f₃ : Frm P (buildRanges wx) t₂.mem t₃.mem :=
    Frm.of_outside (o₃.mono (o' := slot wx 8) (n' := tabBytes wx) hE8 (by omega_arith)) (by simp [buildRanges])
  have hc₃ := hc₂.of_frm (f₃.mono (buildRanges_sub wx)) k₃.2.2 (k₃.gpr (by decide))
  have hh₃ : ∀ k < 32, word t₃.mem P (8 * k) = word t₂.mem P (8 * k) := fun k hk =>
    o₃.word (by have := hdr_lt_slot wx (8 + (i + 2)) hk; omega_arith) (by omega_arith)
  have hT8 : slot wx Crt.aT + 8 * (wx + 2) ≤ slot wx (8 + (i + 2)) := by
    have := slot_mono wx (show Crt.aT + 1 ≤ 8 + (i + 2) by unfold Crt.aT; omega_arith)
    rw [slot_succ] at this; omega_arith
  have hT₃ : wv t₃.mem P (slot wx Crt.aT) wx = wv t₂.mem P (slot wx Crt.aT) wx :=
    o₃.wv (by omega_arith) (by omega_arith)
  simp only [seqs]
  -- The count.
  refine WP.mono (crtBitEnd_ok hc₃ (b := 14 - i) (by rw [hh₃ _ (by decide), hm₂,
    hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), ha₁.hslot (by decide)]; exact hI.cnt) (by omega_arith)
    (by omega_arith)) fun t' ⟨hm', hz', k'⟩ => ⟨by rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega_arith), ?_⟩
  have o₄ := writeW_outside t₃.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 (14 - i - 1)) (by decide)
  rw [← hm'] at o₄
  have f₄ : Frm P (buildRanges wx) t₃.mem t'.mem := Frm.of_outside o₄ (by simp [buildRanges])
  have hT' : wv t'.mem P (slot wx Crt.aT) wx = wv t₁.mem P (slot wx Crt.aT) wx := by
    rw [o₄.wv (by have := hdr_lt_slot wx Crt.aT (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith), hT₃, hT₂]
  have hE' : ∀ j < 16, wv t'.mem P (slot wx (8 + j)) wx = wv t₃.mem P (slot wx (8 + j)) wx := fun j hj =>
    o₄.wv (by have := hdr_lt_slot wx (8 + j) (show Crt.sBit < 32 by decide); omega_arith) (by have := ent_le wx hj; omega_arith)
  -- Entries other than `i + 2` are kept by `toEnt`.
  have hEo : ∀ j < 16, j ≠ i + 2 → wv t₃.mem P (slot wx (8 + j)) wx = wv t.mem P (slot wx (8 + j)) wx :=
    fun j hj hne => by
      have := slot_sep (w := wx) (show 8 + j ≠ 8 + (i + 2) by omega_arith)
      rw [o₃.wv (by omega_arith) (by have := ent_le wx hj; omega_arith), he₂ j hj, he₁ j hj]
  have hTv : Q → wv t₁.mem P (slot wx Crt.aT) wx % X = x ^ (i + 1 + 1) * 2 ^ (64 * wx) % X := fun hq =>
    mont_mulT (E := i + 1) (v := 1) hR (hI.tval hq) (by rw [Nat.pow_one]; exact hXc hq) hm₁
  refine ⟨hc₃.of_frm (f₄.mono (buildRanges_sub wx)) k'.2.2 (k'.gpr (by decide)), ?_, ?_, ?_, by rw [hT']; exact hlt₁,
    fun hq => by rw [hT']; exact hTv hq, fun j hj => ?_, fun hq j hj => ?_,
    (((hI.frm.trans f₁).trans f₂).trans f₃).trans f₄, ((((hI.keep.trans k₁).trans k₂).trans k₃).trans k').mono
      (by decide)⟩
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₃ _ (by decide), hm₂,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), ha₁.hslot (by decide)]; exact hI.tab
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₃ _ (by decide), hm₂, word_writeW_self,
      ← slot_succ]
    rfl
  · rw [hm', word_writeW_self]; congr 1
  · rw [hE' j (by omega_arith)]
    by_cases hj2 : j = i + 2
    · subst hj2; rw [hv₃, hT₂]; exact hlt₁
    · rw [hEo j (by omega_arith) hj2]; exact hI.elt j (by omega_arith)
  · rw [hE' j (by omega_arith)]
    by_cases hj2 : j = i + 2
    · subst hj2; rw [hv₃, hT₂]; exact hTv hq
    · rw [hEo j (by omega_arith) hj2]; exact hI.eval hq j (by omega_arith)

/-- The table's first two entries, `T` and the count. -/
def tabPre : List (Prog isa) :=
  [.block [.mov .rax (.mem (hdr (sArr aOne))), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2),
    .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx),
    .store (hdr Crt.sTab) .rax, .store (hdr Crt.sEnt) .rax]] ++ (Crt.toEnt aY ++ ([Crt.nextEnt] ++
    (Crt.toEnt Crt.aXc ++ (Crt.copyArr Crt.aT Crt.aXc ++ [.block [.mov32 .rax (.imm 14), .store (hdr Crt.sBit) .rax]]))))

/-- The table's products. -/
def tabLoop (mul : Nat → Nat → Nat → Prog isa) : Prog isa := .loop (seqs (tabBody mul)) .ne

theorem tabBuild_eq (mul : Nat → Nat → Nat → Prog isa) : Crt.tabBuild mul = tabPre ++ [tabLoop mul] := by
  simp [Crt.tabBuild, tabPre, tabLoop, tabBody]

/-- The table's first two entries: `T_0 := Y ≡ R`, `T_1 := [aXc] ≡ x R`. -/
theorem tabPre_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} (hc : CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hXN : Xc < X) (hXc : Q → Xc % X = x * 2 ^ (64 * wx) % X) (hY : wv t.mem P (slot wx aY) wx < X)
    (hYv : Q → wv t.mem P (slot wx aY) wx % X = 2 ^ (64 * wx) % X) :
    WP isa (seqs tabPre) t (BuildInv t P wx minv X Xc Q x 0) := by
  have hn := hc.scrT.nowrap
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have hX0 := slot_le (w := wx) (show Crt.aXc < 8 by decide)
  have hE0 := ent_le wx (show 0 < 16 by decide)
  have hE1 := ent_le wx (show 1 < 16 by decide)
  have h8 := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  unfold tabPre
  refine wp_seqs_append (by simp) (by simp [Crt.toEnt]) ?_
  simp only [seqs]
  -- The base.
  refine WP.mono (tabInit_ok hc) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have o1 := writeW_outside t.mem P (d := 8 * Crt.sTab) (off P (slot wx 8)) (by decide)
  have o2 := writeW_outside (t.mem.writeW (off P (8 * Crt.sTab)) (off P (slot wx 8))) P (d := 8 * Crt.sEnt)
    (off P (slot wx 8)) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm P (buildRanges wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [buildRanges])).trans (Frm.of_outside o2 (by simp [buildRanges]))
  have hc₁ := hc.of_frm (f₁.mono (buildRanges_sub wx)) k₁.2.2 (k₁.gpr (by decide))
  -- `T_0 := Y`.
  refine wp_seqs_append (by simp [Crt.toEnt]) (by simp) ?_
  refine WP.mono (toEnt_ok hc₁ hw hw' (a := aY) (j := 0) (by decide) (by decide) (by
    rw [hm₁, word_writeW_self])) fun t₂ ⟨hv₂, o₃, k₂⟩ => ?_
  have f₂ : Frm P (buildRanges wx) t₁.mem t₂.mem :=
    Frm.of_outside (o₃.mono (o' := slot wx 8) (n' := tabBytes wx) (Nat.le_refl _) (by omega_arith)) (by simp [buildRanges])
  have hc₂ := hc₁.of_frm (f₂.mono (buildRanges_sub wx)) k₂.2.2 (k₂.gpr (by decide))
  have hh₂ : ∀ k < 32, word t₂.mem P (8 * k) = word t₁.mem P (8 * k) := fun k hk =>
    o₃.word (by have := hdr_lt_slot wx (8 + 0) hk; omega_arith) (by omega_arith)
  -- `sEnt` up.
  refine wp_seqs_append (by simp) (by simp [Crt.toEnt]) ?_
  simp only [seqs]
  refine WP.mono (nextEnt_ok (e := slot wx 8) hc₂ (by rw [hh₂ _ (by decide), hm₁, word_writeW_self]))
    fun t₃ ⟨hm₃, k₃⟩ => ?_
  have o₄ := writeW_outside t₂.mem P (d := 8 * Crt.sEnt) (off P (slot wx 8 + 8 * (wx + 2))) (by decide)
  rw [← hm₃] at o₄
  have f₃ : Frm P (buildRanges wx) t₂.mem t₃.mem := Frm.of_outside o₄ (by simp [buildRanges])
  have hc₃ := hc₂.of_frm (f₃.mono (buildRanges_sub wx)) k₃.2.2 (k₃.gpr (by decide))
  -- `T_1 := Xc`.
  refine wp_seqs_append (by simp [Crt.toEnt]) (by simp [Crt.copyArr]) ?_
  refine WP.mono (toEnt_ok hc₃ hw hw' (a := Crt.aXc) (j := 1) (by decide) (by decide) (by
    rw [hm₃, word_writeW_self, ← slot_succ])) fun t₄ ⟨hv₄, o₅, k₄⟩ => ?_
  have hE01 := slot_sep (w := wx) (show 8 + 0 ≠ 8 + 1 by decide)
  have f₄ : Frm P (buildRanges wx) t₃.mem t₄.mem :=
    Frm.of_outside (o₅.mono (o' := slot wx 8) (n' := tabBytes wx) (slot_mono wx (by decide)) (by omega_arith))
      (by simp [buildRanges])
  have hc₄ := hc₃.of_frm (f₄.mono (buildRanges_sub wx)) k₄.2.2 (k₄.gpr (by decide))
  have hh₄ : ∀ k < 32, word t₄.mem P (8 * k) = word t₃.mem P (8 * k) := fun k hk =>
    o₅.word (by have := hdr_lt_slot wx (8 + 1) hk; omega_arith) (by omega_arith)
  -- `T := Xc`.
  refine wp_seqs_append (by simp [Crt.copyArr]) (by simp) ?_
  refine WP.mono (copyArr_ok hc₄.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := Crt.aT) (a := Crt.aXc)
    (by decide) (by decide) (by decide)) fun t₅ ⟨hv₅, o₆, k₅⟩ => ?_
  have f₅ : Frm P (buildRanges wx) t₄.mem t₅.mem :=
    Frm.of_outside (o₆.mono (o' := slot wx Crt.aT) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_arith))
      (by simp [buildRanges])
  have hc₅ := hc₄.of_frm (f₅.mono (buildRanges_sub wx)) k₅.2.2 (k₅.gpr (by decide))
  have hh₅ : ∀ k < 32, word t₅.mem P (8 * k) = word t₄.mem P (8 * k) := fun k hk =>
    o₆.word (by have := hdr_lt_slot wx Crt.aT hk; omega_arith) (by omega_arith)
  have hT8 : ∀ j, slot wx Crt.aT + 8 * (wx + 2) ≤ slot wx (8 + j) := fun j => by
    have := slot_mono wx (show 8 ≤ 8 + j by omega_arith); omega_arith
  simp only [seqs]
  -- The count.
  refine WP.mono (cnt14_ok hc₅) fun t₆ ⟨hm₆, k₆⟩ => ?_
  have o₇ := writeW_outside t₅.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 14) (by decide)
  rw [← hm₆] at o₇
  have f₆ : Frm P (buildRanges wx) t₅.mem t₆.mem := Frm.of_outside o₇ (by simp [buildRanges])
  have hc₆ := hc₅.of_frm (f₆.mono (buildRanges_sub wx)) k₆.2.2 (k₆.gpr (by decide))
  have f06 : Frm P (buildRanges wx) t.mem t₆.mem := ((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).trans f₆
  have k06 : Keep mmRegs t t₆ := (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).mono (by decide)
  -- Entries 0 and 1, and `T`, at `t₆`.
  have hX₄ : wv t₄.mem P (slot wx Crt.aXc) wx = Xc := hc₄.x
  have e0 : wv t₆.mem P (slot wx (8 + 0)) wx = wv t.mem P (slot wx aY) wx := by
    rw [o₇.wv (by have := hdr_lt_slot wx (8 + 0) (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith),
      o₆.wv (by have := hT8 0; omega_arith) (by omega_arith),
      o₅.wv (by omega_arith) (by omega_arith), o₄.wv (by have := hdr_lt_slot wx (8 + 0) (show Crt.sEnt < 32 by decide); omega_arith)
        (by omega_arith), hv₂]
    exact f₁.wv_eq (buildRanges_y wx) (by omega_arith)
  have e1 : wv t₆.mem P (slot wx (8 + 1)) wx = Xc := by
    rw [o₇.wv (by have := hdr_lt_slot wx (8 + 1) (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith),
      o₆.wv (by have := hT8 1; omega_arith) (by omega_arith), hv₄]
    exact hc₃.x
  have eT : wv t₆.mem P (slot wx Crt.aT) wx = Xc := by
    rw [o₇.wv (by have := hdr_lt_slot wx Crt.aT (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith), hv₅, hX₄]
  refine ⟨hc₆, ?_, ?_, ?_, by rw [eT]; exact hXN, fun hq => by rw [eT, Nat.zero_add, Nat.pow_one]; exact hXc hq,
    fun j hj => ?_, fun hq j hj => ?_, f06, k06⟩
  · rw [hm₆, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₅ _ (by decide), hh₄ _ (by decide), hm₃,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₂ _ (by decide), hm₁,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm₆, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₅ _ (by decide), hh₄ _ (by decide), hm₃,
      word_writeW_self, ← slot_succ]
  · rw [hm₆, word_writeW_self]
  · rcases (show j = 0 ∨ j = 1 by omega_arith) with rfl | rfl
    · rw [e0]; exact hY
    · rw [e1]; exact hXN
  · rcases (show j = 0 ∨ j = 1 by omega_arith) with rfl | rfl
    · rw [e0, hYv hq, Nat.pow_zero, Nat.one_mul]
    · rw [e1, Nat.pow_one]; exact hXc hq

/-- The table: `T_0 := Y ≡ R`, `T_1 := [aXc] ≡ x R` and `T_i := T_(i-1) [aXc] R⁻¹`. -/
theorem tabBuild_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} (hc : CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X)
    (hXN : Xc < X) (hXc : Q → Xc % X = x * 2 ^ (64 * wx) % X) (hY : wv t.mem P (slot wx aY) wx < X)
    (hYv : Q → wv t.mem P (slot wx aY) wx % X = 2 ^ (64 * wx) % X) :
    WP isa (seqs (Crt.tabBuild M.mm)) t fun t' => CExpCtx t' P wx minv X Xc ∧ CTab t'.mem P wx X Q x ∧
      wv t'.mem P (slot wx aY) wx = wv t.mem P (slot wx aY) wx ∧
      (∀ k < 32, k ≠ Crt.sTab → k ≠ Crt.sEnt → k ≠ Crt.sBit → word t'.mem P (8 * k) = word t.mem P (8 * k)) ∧
      Frm P (crtExpRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  rw [tabBuild_eq]
  refine wp_seqs_append (by simp [tabPre]) (by simp) (WP.mono (tabPre_ok hc hw hw' hXN hXc hY hYv) fun t₆ h₀ => ?_)
  simp only [seqs, tabLoop]
  refine WP.mono (wp_upto (a := 0) (N := 14) (by decide) (BuildInv t P wx minv X Xc Q x)
    (fun i _ hi s hI => buildStep_ok M hw hw' hR hXN hXc hi hI) (fun s h => h) h₀) fun t' hI => ?_
  refine ⟨hI.ctx, ⟨hI.tab, fun j hj => hI.elt j (by omega_arith), fun hq j hj => hI.eval hq j (by omega_arith)⟩,
    hI.frm.wv_eq (buildRanges_y wx) (by omega_arith),
    fun k hk h1 h2 h3 => hI.frm.word_eq (fun r hr => by
      simp only [buildRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      have := hdr_lt_slot wx 0 hk
      have := slot_le (w := wx) (show aAcc < 8 by decide)
      have := slot_mono wx (show 0 ≤ aAcc by decide)
      have := slot_mono wx (show aAcc ≤ aTmp by decide)
      have := slot_mono wx (show aTmp ≤ Crt.aT by decide)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Crt.sTab, Crt.sEnt, Crt.sBit, sFn] at * <;> omega_arith) (by omega_arith),
    hI.frm.mono (buildRanges_sub wx), hI.keep⟩

/-! ## The exponentiation -/

/-- `expLoop`'s start: the exponent's pointer and length from the modulus'
header slots `sp` and `sl`, and byte index 0. -/
theorem crtExpInit_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {L : Nat}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 L) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sLink)), .mov .rdx (.mem (Crt.ws .rax sp)),
      .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
      .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]) s fun t =>
      t.mem = ((s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep).writeW (off (off B o) (8 * Crt.sExpLen))
        (BitVec.ofNat 64 L)).writeW (off (off B o) (8 * Crt.sI)) (BitVec.setWidth 64 (0 : BitVec 32)) ∧
      Keep [.rax, .rdx] s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.ld (by have := hdr_lt_slot wx 8 hi'; omega_arith)
  have hln : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi' =>
    hc.scr.ld (by have := hdr_lt_slot w 8 hi'; omega_arith)
  have hst : ∀ i < 32, InRegions s.wr (off (off B o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.st (by have := hdr_lt_slot wx 8 hi'; omega_arith)
  have o1 := writeW_outside s.mem (off B o) (d := 8 * Crt.sExp) ep (by decide)
  have hW : (s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep).readW (off B (8 * sl)) 64 = BitVec.ofNat 64 L :=
    ((Frm.of_outside (rs := [(8 * Crt.sExp, 8)]) o1 (by simp)).word_below (L := slot wx 8)
      (fun r hr => by rw [List.mem_singleton.mp hr]; unfold Crt.sExp sFn slot hdrBytes; omega_arith) (by omega_arith)
      (by unfold slot hdrBytes at hi; omega_arith) (by have := hdr_lt_slot w 8 hsl; omega_arith)).trans hel
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = ((s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep).writeW
      (off (off B o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 L)).writeW (off (off B o) (8 * Crt.sI))
      (BitVec.setWidth 64 (0 : BitVec 32)))
    (by xrun [State.ea, hdr, Crt.ws, hc.rdi, hdrOff, hl Crt.sLink (by decide), hc.link, hln sp hsp, hep,
      hst Crt.sExp (by decide), hln sl hsl, hW, hst Crt.sExpLen (by decide), hst Crt.sI (by decide)]) rfl)
    fun t ⟨hm, k⟩ => ⟨hm, k⟩

/-- `expLoop`'s start: the exponent's pointer and length, and byte index 0. -/
def expInit (sp sl : Nat) : Prog isa :=
  .block [.mov .rax (.mem (hdr Crt.sLink)), .mov .rdx (.mem (Crt.ws .rax sp)), .store (hdr Crt.sExp) .rdx,
    .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx, .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]

/-- `expLoop`'s bytes. -/
def expBytes (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .loop (seqs [
    .block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI)),
      .movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 2),
      .store (hdr Crt.sBit) .rax],
    .loop (seqs (Crt.expWin mul)) .ne,
    .block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
      .alu .cmp .rax (.mem (hdr Crt.sExpLen))]]) .ne

theorem expLoop_eq (mul : Nat → Nat → Nat → Prog isa) (sp sl : Nat) :
    Crt.expLoop mul sp sl = expInit sp sl :: (Crt.tabBuild mul ++ [expBytes mul]) := by
  simp [Crt.expLoop, expInit, expBytes]

/-- `expLoop`'s start and table: the bytes' invariant. -/
theorem crtExpHead_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat}
    {Q : Prop} (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = X)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X)
    (hxc : Q → wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < X)
    (hyc : Q → wv s.mem (off B o) (slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (he : Src s B Z ep eb) :
    WP isa (seqs (expInit sp sl :: Crt.tabBuild M.mm)) s
      (CByteInv s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) Q x ep eb.length eb 0) := by
  have hPn := hc.scrT.nowrap
  have hBn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hodd _
  have hout : ∀ i < eb.length, slot wx 8 + tabBytes wx ≤ ofs (off B o) (ep + BitVec.ofNat 64 i) := fun i hi' => by
    have := he.out i hi'
    rcases ofs_rebase B (ep + BitVec.ofNat 64 i) (o := o) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩
    · omega_arith
    · omega_arith
  have hc₀ : CExpCtx s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) :=
    ⟨hc.good, hc.scrT, hn, hinv, rfl⟩
  rw [← List.singleton_append]
  refine wp_seqs_append (by simp) (by simp [tabBuild_eq, tabPre]) ?_
  simp only [seqs, expInit]
  refine WP.mono (crtExpInit_ok hc hsp hsl hep hel) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have o1 := writeW_outside s.mem (off B o) (d := 8 * Crt.sExp) ep (by decide)
  have o2 := writeW_outside (s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep) (off B o) (d := 8 * Crt.sExpLen)
    (BitVec.ofNat 64 eb.length) (by decide)
  have o3 := writeW_outside ((s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep).writeW
    (off (off B o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 eb.length)) (off B o) (d := 8 * Crt.sI)
    (BitVec.setWidth 64 (0 : BitVec 32)) (by decide)
  rw [← hm₁] at o3
  have f₁ : Frm (off B o) (crtExpRanges wx) s.mem t₁.mem :=
    ((Frm.of_outside o1 (by simp [crtExpRanges])).trans (Frm.of_outside o2 (by simp [crtExpRanges]))).trans
      (Frm.of_outside o3 (by simp [crtExpRanges]))
  have hc₁ := hc₀.of_frm f₁ k₁.2.2 (k₁.gpr (by decide))
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hY1 := hdr_lt_slot wx aY (show 31 < 32 by decide)
  have hYe₁ : wv t₁.mem (off B o) (slot wx aY) wx = wv s.mem (off B o) (slot wx aY) wx := by
    rw [o3.wv (by unfold Crt.sI sFn at *; omega_arith) (by omega_arith), o2.wv (by unfold Crt.sExpLen sFn at *; omega_arith)
      (by omega_arith), o1.wv (by unfold Crt.sExp sFn at *; omega_arith) (by omega_arith)]
  -- The table.
  refine WP.mono (tabBuild_ok M (Q := Q) (x := x) hc₁ hw2 (by omega_arith) hR hxl hxc (by rw [hYe₁]; exact hyl)
    (fun hq => by rw [hYe₁]; exact hyc hq)) fun t₂ ⟨hc₂, htab₂, hYe₂, hh₂, f₂, k₂⟩ => ?_
  refine ⟨hc₂, htab₂, by rw [hYe₂, hYe₁]; exact hyl, fun hq => ?_, ?_, ?_, ?_, f₁.trans f₂,
    (k₁.trans k₂).mono (by decide)⟩
  · rw [hYe₂, hYe₁, hyc hq, pre_zero, Nat.pow_zero, Nat.one_mul]
  · rw [hh₂ _ (by decide) (by decide) (by decide) (by decide), hm₁, word_writeW_self]; rfl
  · rw [hh₂ _ (by decide) (by decide) (by decide) (by decide), hm₁,
      hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr (i := Crt.sExpLen) _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hh₂ _ (by decide) (by decide) (by decide) (by decide), hm₁,
      hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide), word_writeW_self]

/-- The exponentiation in a prime's workspace: `Y < X` and `[aXc] < X`
stay so, and if `Q` gives `Y ≡ R` and `[aXc] ≡ x R` modulo `X`, then
`Y ≡ x^d R`, for the exponent `d` whose `L` bytes `eb` (most significant
first) are at `ep`, outside the working space, the pointer and length in
the modulus' header slots `sp` and `sl`. -/
theorem crtExpLoop_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat}
    {Q : Prop} (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = X)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X)
    (hxc : Q → wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < X)
    (hyc : Q → wv s.mem (off B o) (slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (seqs (Crt.expLoop M.mm sp sl)) s fun t => SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx < X ∧
      (Q → wv t.mem (off B o) (slot wx aY) wx % X = x ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X) ∧
      Frm (off B o) (crtExpRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hi := hc.hi
  have hlo := hc.lo
  have hBn := hc.scr.nowrap
  have hPn := hc.scrT.nowrap
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hodd _
  have hout : ∀ i < eb.length, slot wx 8 + tabBytes wx ≤ ofs (off B o) (ep + BitVec.ofNat 64 i) := fun i hi' => by
    have := he.out i hi'
    rcases ofs_rebase B (ep + BitVec.ofNat 64 i) (o := o) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩
    · omega_arith
    · omega_arith
  rw [expLoop_eq, ← List.cons_append]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (crtExpHead_ok M hc hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc
    hsp hsl hep hel he) fun t₂ h₂ => ?_)
  simp only [seqs, expBytes]
  refine wp_upto (a := 0) (N := eb.length) (by omega_arith)
    (CByteInv s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) Q x ep eb.length eb)
    (fun i _ hi' t hI => crtByte_ok M hw2 (by omega_arith) hR rfl (by omega_arith) hi' he.rd he.val hout hI)
    (fun t hI => ?_) h₂
  exact ⟨hc.of_frmT hI.frm (crtExpRanges_ok wx) hI.keep.2.2 (hI.keep.gpr (by decide)), hI.ylt,
    fun hq => by rw [hI.y hq, pre_len], hI.frm, hI.keep⟩

end VG.Proof.Bignum.X86_64
