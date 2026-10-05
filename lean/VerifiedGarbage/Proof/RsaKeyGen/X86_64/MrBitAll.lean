import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrBit

/-!
# A candidate on x86-64: `mrExpBit`

`mrExpBit_ok`: from `y R mod c` in `aY` and the top bit `bt` of `kV`,
`y' = y² b^bt mod c` (as `y' R mod c`), the flag updated with `y' = 1` and
`y' = c − 1`, `kV` doubled and `kBits` decremented.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- What `mrExpBit` changes. -/
def bitRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)), (slot w aXm, 8 * (w + 2)),
    (8 * kG, 8), (8 * kFlag, 8), (8 * kV, 8), (8 * kBits, 8)]

theorem mrExpBit_eq (mul : Nat → Nat → Nat → Prog isa) : mrExpBit mul =
    [mul aY aY aY,
      .block (([.mov .rax (.mem (hdr kV)), .shift .shr .rax 63, .mov32 .r15 (.imm 0), .alu .sub .r15 (.reg .rax),
        .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aXm)))] : List Instr) ++ extBase aB .r8 ++
        extBase aR1 .rsi),
      wordLoop 0 [.mov .rax (.mem (ix .r8 .r14)), .mov .rdx (.mem (ix .rsi .r14)), .alu .xor .rax (.reg .rdx),
        .alu .and .rax (.reg .r15), .alu .xor .rax (.reg .rdx), .store (ix .rbx .r14) .rax],
      mul aY aY aXm] ++ (eqMask aRm1 ++ (([.block [.store (hdr kG) .rbp]] : List (Prog isa)) ++ (eqMask aR1 ++ ([
      .block [.mov .rax (.mem (hdr kV)), .shift .shr .rax 63, .mov32 .r15 (.imm 0), .alu .sub .r15 (.reg .rax),
        .mov .rdx (.mem (hdr kG)), .alu .or .rbp (.reg .rdx), .alu .and .rbp (.reg .r15),
        .mov .rax (.mem (hdr kFlag)), .alu .or .rax (.reg .rdx), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1))),
        .alu .and .rax (.reg .r15), .alu .or .rax (.reg .rbp), .store (hdr kFlag) .rax,
        .mov .rax (.mem (hdr kV)), .alu .add .rax (.reg .rax), .store (hdr kV) .rax,
        .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]] : List (Prog isa))))) := rfl

/-- The selection's bases and mask. -/
theorem bitSel_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hw' : w < 2 ^ 31) {V : BitVec 64} {bt : Bool} (hV : word s.mem B (8 * kV) = V)
    (hbt : V >>> 63 = BitVec.ofNat 64 bt.toNat) :
    WP isa (.block (([.mov .rax (.mem (hdr kV)), .shift .shr .rax 63, .mov32 .r15 (.imm 0), .alu .sub .r15 (.reg .rax),
        .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aXm)))] : List Instr) ++ extBase aB .r8 ++
        extBase aR1 .rsi)) s fun t =>
      t.gpr .r15 = mask bt ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = off B (slot w aXm) ∧
      t.gpr .r8 = off B (slot w aB) ∧ t.gpr .rsi = off B (slot w aR1) ∧ t.mem = s.mem ∧
      Keep [.rax, .rbx, .rsi, .r8, .r12, .r15] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r15, .r12, .rbx] (Q := fun t => t.gpr .r15 = mask bt ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = off B (slot w aXm) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl kV (by decide), hl (sArr aXm) (by decide),
      hg.hdr.hw, hg.hdr.harr aXm (by decide), hV, hbt, neg_bit]) rfl) fun s₁ ⟨⟨h15, h12, hbx, hm₁⟩, k₁⟩ => ?_
  have hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine WP.mono (extBase_ok hg₁ hZ hw' (j := aB) (by decide) (r := .r8) (by decide) rfl rfl)
    fun s₂ ⟨h8, hm₂, k₂⟩ => ?_
  have hg₂ : Good s₂ B Z w mi := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, by rw [hm₂]; exact hg₁.hdr⟩
  refine WP.mono (extBase_ok hg₂ hZ hw' (j := aR1) (by decide) (r := .rsi) (by decide) rfl rfl)
    fun t ⟨hsi, hm, k⟩ => ⟨?_, ?_, ?_, ?_, hsi, by rw [hm, hm₂, hm₁], ((k₁.trans k₂).trans k).mono (by decide)⟩
  · exact (k.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h15)
  · exact (k.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12)
  · exact (k.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hbx)
  · exact (k.gpr (by decide)).trans h8

/-- `mrExpBit`. -/
theorem mrExpBit_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c b y : Nat}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c (b * 2 ^ (64 * w) % c)) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % c)
    {V : BitVec 64} {bt P : Bool} {n : Nat} (hV : word s.mem B (8 * kV) = V)
    (hbt : V >>> 63 = BitVec.ofNat 64 bt.toNat) (hP : word s.mem B (8 * kFlag) = mask P)
    (hnb : word s.mem B (8 * kBits) = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hn' : n < 2 ^ 64) :
    WP isa (seqs (mrExpBit M.mm)) s fun t =>
      MrCtx t B Z w mi c (b * 2 ^ (64 * w) % c) ∧
      wv t.mem B (slot w aY) w = (y * y % c * (if bt then b else 1) % c) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (if bt then
          decide (y * y % c * (if bt then b else 1) % c = 1) || decide (y * y % c * (if bt then b else 1) % c = c - 1)
        else P || decide (y * y % c * (if bt then b else 1) % c = c - 1)) ∧
      word t.mem B (8 * kV) = V + V ∧ word t.mem B (8 * kBits) = BitVec.ofNat 64 (n - 1) ∧
      t.zf = some (decide (n - 1 = 0)) ∧ Frm B (bitRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hg := hc.good
  have hZ := hd.z
  have hXZ := hd.x
  have hw := hd.w4
  have hw' : w < 2 ^ 31 := by have := hd.w64; omega
  have hn := hg.scr.nowrap
  have hR : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega
  rw [mrExpBit_eq]
  refine wp_seqs_append (by simp) (by simp [eqMask]) ?_
  simp only [seqs]
  -- `y := y²`.
  refine WP.seq (WP.mono (M.mm_ok hg hZ (by omega) hw' (o := aY) (a := aY) (b := aY) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hY, hc.n]; exact Nat.mod_lt _ hc0)) fun s₁ ⟨hg₁, hlt₁, hy₁, ha₁, k₁⟩ => ?_)
  rw [hc.n] at hlt₁ hy₁
  rw [hY] at hy₁
  have hY₁ : wv s₁.mem B (slot w aY) w = y * y % c * 2 ^ (64 * w) % c := mont_val hR hlt₁ hy₁ rfl rfl
  have hc₁ : MrCtx s₁ B Z w mi c (b * 2 ^ (64 * w) % c) := hc.of_frm hd (Frm.of_arrays ha₁ (by simp [bitRanges]) (rs := bitRanges w))
    hg₁.scr hg₁.rdi (by simp only [bitRanges]; rng_disj) (by simp only [bitRanges]; rng_disj)
    (by simp only [bitRanges]; rng_disj) (by simp only [bitRanges]; rng_disj) (by simp only [bitRanges]; rng_disj)
  have hV₁ : word s₁.mem B (8 * kV) = V := by rw [ha₁.hslot (by decide)]; exact hV
  -- The selection.
  refine WP.seq (WP.mono (bitSel_ok hg₁ hZ hw' hV₁ hbt) fun s₂ ⟨h15, h12, hbx, h8, hsi, hm₂, k₂⟩ => ?_)
  have hs₂ := hg₁.scr.congr k₂.2.2
  refine WP.seq (WP.mono (selLoop_ok hs₂ h8 hsi hbx h15 h12 (by omega) hw' (by unfold slot aB aRm1 at *; omega)
    (by unfold slot aR1 aRm1 at *; omega) (by have := slot_le (w := w) (show aXm < 8 by decide); omega)
    (Or.inl (by unfold slot aXm aB; omega)) (Or.inl (by unfold slot aXm aR1; omega)))
    fun s₃ ⟨hv₃, hs₃, ho₃, k₃⟩ => ?_)
  rw [hm₂, hc₁.b, hc₁.r1] at hv₃
  have hg₃ : Good s₃ B Z w mi := ⟨hs₃, (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hg₁.rdi),
    Hdr.outside (by rw [hm₂]; exact hg₁.hdr) ho₃ (by unfold slot; omega)⟩
  have hf₃ : Frm B (bitRanges w) s₁.mem s₃.mem := by
    rw [← hm₂]; exact Frm.of_outside (ho₃.mono (o' := slot w aXm) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega))
      (by simp [bitRanges])
  have hc₃ : MrCtx s₃ B Z w mi c (b * 2 ^ (64 * w) % c) := hc₁.of_frm hd hf₃ hs₃ hg₃.rdi
    (by simp only [bitRanges]; rng_disj) (by simp only [bitRanges]; rng_disj)
    (by simp only [bitRanges]; rng_disj) (by simp only [bitRanges]; rng_disj) (by simp only [bitRanges]; rng_disj)
  have hY₃ : wv s₃.mem B (slot w aY) w = y * y % c * 2 ^ (64 * w) % c := by
    rw [ho₃.wv (Or.inr (by unfold slot aXm aY; omega)) (by have := slot_le (w := w) (show aY < 8 by decide); omega),
      hm₂, hY₁]
  have hX₃ : wv s₃.mem B (slot w aXm) w = (if bt then b else 1) * 2 ^ (64 * w) % c := by
    rw [hv₃]; cases bt <;> simp
  -- `y := y b^bt`.
  refine WP.mono (M.mm_ok hg₃ hZ (by omega) hw' (o := aY) (a := aY) (b := aXm) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc₃.inv
    (by rw [hX₃, hc₃.n]; exact Nat.mod_lt _ hc0)) fun s₄ ⟨hg₄, hlt₄, hy₄, ha₄, k₄⟩ => ?_
  rw [hc₃.n] at hlt₄ hy₄
  rw [hY₃, hX₃] at hy₄
  have hY₄ : wv s₄.mem B (slot w aY) w = y * y % c * (if bt then b else 1) % c * 2 ^ (64 * w) % c := mont_val hR hlt₄ hy₄ rfl rfl
  have hc₄ : MrCtx s₄ B Z w mi c (b * 2 ^ (64 * w) % c) := hc₃.of_frm hd (Frm.of_arrays ha₄ (by simp [bitRanges]) (rs := bitRanges w))
    hg₄.scr hg₄.rdi (by simp only [bitRanges]; rng_disj) (by simp only [bitRanges]; rng_disj)
    (by simp only [bitRanges]; rng_disj) (by simp only [bitRanges]; rng_disj) (by simp only [bitRanges]; rng_disj)
  have hlt2 : y * y % c * (if bt then b else 1) % c < c := Nat.mod_lt _ hc0
  have hhd₄ : ∀ i < 32, word s₄.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [ha₄.hslot hi, ho₃.word (Or.inl (by have := hdr_lt_slot w aXm hi; omega)) (by omega), hm₂, ha₁.hslot hi]
  -- `y = c − 1` into `kG`.
  refine wp_seqs_append (by simp [eqMask]) (by simp) ?_
  refine WP.mono (eqMask_ok hg₄ hZ (by omega) hw' (j := aRm1) (by decide) hXZ) fun s₅ ⟨hbp₅, hm₅, k₅⟩ => ?_
  have em1 : decide (y * y % c * (if bt then b else 1) % c * 2 ^ (64 * w) % c = c - 2 ^ (64 * w) % c) =
      decide (y * y % c * (if bt then b else 1) % c = c - 1) := decide_eq_decide.mpr (mont_eq_m1 hR hc1 hlt2)
  rw [hY₄, hc₄.rm1, em1] at hbp₅
  have hdi₅ : s₅.gpr .rdi = B := (k₅.gpr (by decide)).trans hg₄.rdi
  have hs₅ := hg₄.scr.congr k₅.2.2
  refine wp_seqs_append (by simp) (by simp [eqMask]) ?_
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₅.mem.writeW (off B (8 * kG)) (s₅.gpr .rbp)) (by
    xrun [State.ea, hdr, hdi₅, hdrOff, hs₅.st (d := 8 * kG) (by have := hdr_lt_slot w 8 (show kG < 32 by decide); omega)])
    rfl) fun s₆ ⟨hm₆, k₆⟩ => ?_
  have hg₆ : Good s₆ B Z w mi := ⟨hs₅.congr k₆.2.2, (k₆.gpr (by decide)).trans hdi₅,
    by rw [hm₆, hm₅]; exact hg₄.hdr.store (by decide) (by decide) _⟩
  have hY₆ : wv s₆.mem B (slot w aY) w = wv s₄.mem B (slot w aY) w := by
    rw [hm₆, hdrStore_wv _ _ _ (by decide) (by decide) (by omega), hm₅]
  have hR1₆ : wv s₆.mem B (slot w aR1) w = wv s₄.mem B (slot w aR1) w := by
    rw [hm₆, (writeW_outside _ B _ (d := 8 * kG) (by unfold kG sFn; omega)).wv
      (Or.inr (by unfold slot kG sFn aR1 hdrBytes; omega)) (by unfold slot aR1 aRm1 at *; omega), hm₅]
  -- `y = 1`, then the flag.
  refine wp_seqs_append (by simp [eqMask]) (by simp) ?_
  refine WP.mono (eqMask_ok hg₆ hZ (by omega) hw' (j := aR1) (by decide)
    (by unfold slot aR1 aRm1 at *; omega)) fun s₇ ⟨hbp₇, hm₇, k₇⟩ => ?_
  have e1 : decide (y * y % c * (if bt then b else 1) % c * 2 ^ (64 * w) % c = 2 ^ (64 * w) % c) =
      decide (y * y % c * (if bt then b else 1) % c = 1) := decide_eq_decide.mpr (mont_eq_one hR hc1 hlt2)
  rw [hY₆, hR1₆, hY₄, hc₄.r1, e1] at hbp₇
  have hg₇ : Good s₇ B Z w mi := ⟨hg₆.scr.congr k₇.2.2, (k₇.gpr (by decide)).trans hg₆.rdi, by rw [hm₇]; exact hg₆.hdr⟩
  have hhd₇ : ∀ i < 32, i ≠ kG → word s₇.mem B (8 * i) = word s.mem B (8 * i) := fun i hi hne => by
    rw [hm₇, hm₆, hdrStore_hdr _ _ _ (by decide) hi (Ne.symm hne), hm₅, hhd₄ i hi]
  have hG₇ : word s₇.mem B (8 * kG) = mask (decide (y * y % c * (if bt then b else 1) % c = c - 1)) := by
    rw [hm₇, hm₆, word_writeW_self, ← hbp₅]
  refine WP.mono (bitTail_ok (V := V) (P := P) (n := n) hg₇ hZ (by rw [hhd₇ kV (by decide) (by decide)]; exact hV) hbt hG₇ hbp₇
    (by rw [hhd₇ kFlag (by decide) (by decide)]; exact hP) (by rw [hhd₇ kBits (by decide) (by decide)]; exact hnb)
    hn1 hn') fun t ⟨hm, hz, k⟩ => ?_
  have hm' : t.mem = (((s₄.mem.writeW (off B (8 * kG)) (s₅.gpr .rbp)).writeW (off B (8 * kFlag))
      (mask (if bt then decide (y * y % c * (if bt then b else 1) % c = 1) ||
        decide (y * y % c * (if bt then b else 1) % c = c - 1)
        else P || decide (y * y % c * (if bt then b else 1) % c = c - 1)))).writeW (off B (8 * kV))
      (V + V)).writeW (off B (8 * kBits)) (BitVec.ofNat 64 (n - 1)) := by rw [hm, hm₇, hm₆, hm₅]
  have hft : Frm B (bitRanges w) s₄.mem t.mem := by
    rw [hm']
    refine (((Frm.of_outside (writeW_outside _ B _ (d := 8 * kG) (by unfold kG sFn; omega)) (by simp [bitRanges])).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * kFlag) (by unfold kFlag kPlen sFn; omega)) (by simp [bitRanges]))).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * kV) (by unfold kV kT0 sFn; omega)) (by simp [bitRanges]))).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * kBits) (by unfold kBits kT2 sFn; omega)) (by simp [bitRanges]))
  have hgt : Good t B Z w mi := ⟨hg₇.scr.congr k.2.2, (k.gpr (by decide)).trans hg₇.rdi,
    Hdr.of_frm hg₄.hdr hft (by simp only [bitRanges]; rng_disj)⟩
  refine ⟨hc₄.of_frm hd hft hgt.scr hgt.rdi (by simp only [bitRanges]; rng_disj) (by simp only [bitRanges]; rng_disj)
      (by simp only [bitRanges]; rng_disj) (by simp only [bitRanges]; rng_disj) (by simp only [bitRanges]; rng_disj),
    ?_, ?_, ?_, ?_, hz, ?_, ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k |>.mono (by decide)⟩
  · rw [hm', hdrStore_wv _ _ _ (by decide) (by decide) (by omega), hdrStore_wv _ _ _ (by decide) (by decide) (by omega),
      hdrStore_wv _ _ _ (by decide) (by decide) (by omega), hdrStore_wv _ _ _ (by decide) (by decide) (by omega)]
    exact hY₄
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm, word_writeW_self]
  · have f₁ : Frm B (bitRanges w) s.mem s₁.mem := Frm.of_arrays ha₁ (by simp [bitRanges])
    have f₄ : Frm B (bitRanges w) s₃.mem s₄.mem := Frm.of_arrays ha₄ (by simp [bitRanges])
    exact ((f₁.trans hf₃).trans f₄).trans hft

end VG.Proof.RsaKeyGen.X86_64
