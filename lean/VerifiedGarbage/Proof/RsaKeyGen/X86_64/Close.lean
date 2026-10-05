import VerifiedGarbage.Proof.RsaKeyGen.X86_64.LoadC
import VerifiedGarbage.Spec.RsaKeyGen.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.Cmp
import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# A candidate on x86-64: too close to `p`

`closeCheck` loads `p` into `aX`, puts `c − p` (with its borrow) in `aAcc`
(`diff_ok`), negates it under the mask of the borrow (`neg_ok`): `|c − p|`;
then compares the bound `2^(64 w − 100)` (`aTmp`, by `setWord`) with it
(`cmpLoop_ok`), and leaves the mask of `|c − p| ≤ 2^(64 w − 100)`, or 0
without `p`, in `rbp` (`closeCheck_ok`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- After `j` words of the negation: the low `j` words negated if `b`, with
the carry in `rbp`. -/
structure NegInv (s₀ : State) (B : Addr) (Z e : Nat) (b : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B e (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = mask c ∧
    wv t.mem B e j + 2 ^ (64 * j) * c.toNat =
      if b then 2 ^ (64 * j) - wv s₀.mem B e j else wv s₀.mem B e j

theorem xor_mask_toNat (x : BitVec 64) (b : Bool) :
    (x ^^^ mask b).toNat = if b then 2 ^ 64 - 1 - x.toNat else x.toNat := by
  cases b
  · simp [mask_false]
  · simp only [mask_true, BitVec.xor_allOnes, BitVec.toNat_not, ite_true]

theorem negStep_ok {s₀ : State} {B : Addr} {Z w e : Nat} {b : Bool}
    (hsi : s₀.gpr .rsi = off B e) (h15 : s₀.gpr .r15 = mask b) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (he : e + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State} (hI : NegInv s₀ B Z e b j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rsi .r14)), .alu .xor .rax (.reg .r15), cfFromRbp, .alu .adc .rax (.imm 0),
        .store (ix .rsi .r14) .rax, cfToRbp] : List Instr) ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ NegInv s₀ B Z e b (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tsi : t.gpr .rsi = off B e := (hI.keep.gpr (by decide)).trans hsi
  have t15 : t.gpr .r15 = mask b := (hI.keep.gpr (by decide)).trans h15
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (off B (e + 8 * j)) r ∧
        r.toNat + 2 ^ 64 * c'.toNat = (word t.mem B (e + 8 * j) ^^^ mask b).toNat + c.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tsi hI.r14, t15, hbp, cf_mask, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show e + 8 * j + 8 ≤ Z by omega)]
    refine ⟨_, rfl, _, rfl, ?_⟩
    have := adc_toNat (word t.mem B (e + 8 * j) ^^^ mask b) (BitVec.signExtend 64 (0 : BitVec 32)) c
    rw [show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl, Nat.add_zero] at this
    exact this
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : word t.mem B (e + 8 * j) = word s₀.mem B (e + 8 * j) := hI.out.word (by omega) (by omega)
  rw [hx, xor_mask_toNat] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega)]
    simp only [wv]
    have hD := wv_lt s₀.mem B e j
    have hxl := (word s₀.mem B (e + 8 * j)).isLt
    have hc1 := Bool.toNat_le c
    have hc1' := Bool.toNat_le c'
    rw [pow64_succ]
    generalize 2 ^ (64 * j) = P at hD hval ⊢
    generalize wv s₀.mem B e j = D at hD hval ⊢
    generalize (word s₀.mem B (e + 8 * j)).toNat = x at hxl hr ⊢
    generalize wv t.mem B e j = V at hval ⊢
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hr hval ⊢
      grind
    · simp only [↓reduceIte] at hr hval ⊢
      have hPx : P * x + P ≤ P * 2 ^ 64 := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hxl
      have e1 : P * r.toNat + P * 2 ^ 64 * c'.toNat = P * (2 ^ 64 - 1 - x + c.toNat) := by
        rw [Nat.mul_assoc, ← Nat.mul_add, hr]
      have e2 : P * (2 ^ 64 - 1 - x + c.toNat) + P * x + P = P * 2 ^ 64 + P * c.toNat := by
        rw [← Nat.mul_add, ← Nat.mul_succ, ← Nat.mul_add]; congr 1; omega
      omega

/-- `|c − p|` from the difference `D` and its borrow `b`. -/
theorem absDiff_of {D p c P : Nat} {b : Bool} (h : D + p = c + P * b.toNat) (hD : D < P) :
    (if b then P - D else D) = Spec.RsaKeyGen.absDiff c p := by
  unfold Spec.RsaKeyGen.absDiff
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero,
    Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> split <;> omega

/-- `diffLoop`: `[aAcc] := c − p` (`aN` minus `aX`), its borrow's mask in `rbp`. -/
theorem diff_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa (seqs diffLoop) s fun t => ∃ b : Bool, t.gpr .rbp = mask b ∧
      wv t.mem B (slot w aAcc) w + wv s.mem B (slot w aX) w = wv s.mem B (slot w aN) w + 2 ^ (64 * w) * b.toNat ∧
      Outside B (slot w aAcc) (8 * w) s.mem t.mem ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      Keep [.rax, .rbp, .rsi, .r8, .r10, .r12, .r14] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have sX := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  have sA := Nat.le_trans (slot_le (w := w) (show aAcc < 8 by decide)) hZ
  have p1 := slot_sep (w := w) (show aAcc ≠ aN by decide)
  have p2 := slot_sep (w := w) (show aAcc ≠ aX by decide)
  unfold diffLoop
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .r8, .r10, .rsi, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aN) ∧ t.gpr .r10 = off B (slot w aX) ∧ t.gpr .rsi = off B (slot w aAcc) ∧
      t.gpr .rbp = mask false ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hl (sArr aX) (by decide),
      hl (sArr aAcc) (by decide), hg.hdr.hw, hg.hdr.harr aN (by decide), hg.hdr.harr aX (by decide),
      hg.hdr.harr aAcc (by decide)]) rfl) fun s₁ ⟨⟨h12, h8, h10, hsi, hbp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' (SubInv s₁ B Z (slot w aN) (slot w aX) (slot w aAcc))
    (fun t h14 hm k _ => ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, by rw [k.gpr (by decide)]; exact hbp, by simp [wv]⟩⟩)
    (fun j _ hj t hI => subStep_ok h8 h10 hsi h12 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hj hI))
    fun t hI => ?_
  obtain ⟨b, hb, hv⟩ := hI.val
  rw [hm₁] at hv
  refine ⟨b, hb, hv, by rw [← hm₁]; exact hI.out, (hI.keep.gpr (by decide)).trans h12, (k₁.trans hI.keep).mono (by decide)⟩

/-- `negLoop`: `[aAcc]` negated modulo `2^(64 w)` if `rbp` is the mask of
`true`. -/
theorem neg_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {b : Bool} (hbp : s.gpr .rbp = mask b) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) :
    WP isa (seqs negLoop) s fun t =>
      wv t.mem B (slot w aAcc) w = (if b then 2 ^ (64 * w) - wv s.mem B (slot w aAcc) w else wv s.mem B (slot w aAcc) w)
        % 2 ^ (64 * w) ∧
      Outside B (slot w aAcc) (8 * w) s.mem t.mem ∧ Keep [.rax, .rbp, .rsi, .r14, .r15] s t := by
  have hn := hg.scr.nowrap
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sArr aAcc)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show sArr aAcc < 32 by decide); omega)
  have sA := Nat.le_trans (slot_le (w := w) (show aAcc < 8 by decide)) hZ
  unfold negLoop
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r15, .rsi] (Q := fun t => t.gpr .r15 = mask b ∧ t.gpr .rsi = off B (slot w aAcc) ∧
      t.mem = s.mem) (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hbp, hg.hdr.harr aAcc (by decide)]) rfl)
    fun s₁ ⟨⟨h15, hsi, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' (NegInv s₁ B Z (slot w aAcc) b)
    (fun t h14 hm k _ => ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨b, by rw [k.gpr (by decide), k₁.gpr (by decide)]; exact hbp, by cases b <;> simp [wv]⟩⟩)
    (fun j _ hj t hI => negStep_ok hsi h15 ((k₁.gpr (by decide)).trans h12) (by omega) (by omega) hj hI))
    fun t hI => ?_
  obtain ⟨c, _, hv⟩ := hI.val
  rw [hm₁] at hv
  refine ⟨?_, by rw [← hm₁]; exact hI.out, (k₁.trans hI.keep).mono (by decide)⟩
  have hlt := wv_lt t.mem B (slot w aAcc) w
  rw [← hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- What `closeCheck` changes: `aX`, `aAcc` and `aTmp`. -/
def closeRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aX, 8 * (w + 2)), (slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2))]

theorem sxm1 : BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = BitVec.allOnes 64 := by decide

theorem mask_not (b : Bool) : mask b ^^^ BitVec.allOnes 64 = mask (!b) := by cases b <;> decide

/-- The bound: `[aTmp] := 2^(64 w − 100)`, `aTmp`'s word `w − 2` set to `2^28`. -/
theorem bound_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 4 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa (.seq (.block [.mov .r12 (.mem (hdr sW)), .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 2),
        .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ 28)))]) (setWord aTmp .rcx)) s fun t =>
      wv t.mem B (slot w aTmp) w = 2 ^ (64 * w - 100) ∧ Outside B (slot w aTmp) (8 * (w + 2)) s.mem t.mem ∧
      Keep [.rax, .rcx, .rdx, .r8, .r12, .r14] s t := by
  have hn := hg.scr.nowrap
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sW)) 8 := hg.scr.ld (by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)
  refine WP.seq (WP.mono (WP.keep [.r12, .rcx, .rdx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rcx = BitVec.ofNat 64 (w - 2) ∧ (t.gpr .rdx).toNat = 2 ^ 28 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hg.hdr.hw, sx2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (2 : BitVec 64).toNat = 2 from rfl]
    omega) rfl)
    fun s₁ ⟨⟨h12, hcx, hdx, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (setWord_ok (hg.scr.congr k₁.2.2) ((k₁.gpr (by decide)).trans hg.rdi) (by rw [hm₁]; exact hg.hdr) hZ h12
    (by omega) hw' (o := aTmp) (by decide) (ri := .rcx) (by decide) (i := w - 2) (by omega) hcx)
    fun t ⟨hv, ho, k⟩ => ⟨?_, by rw [hm₁] at ho; exact ho, (k₁.trans k).mono (by decide)⟩
  rw [hv, hdx, ← Nat.pow_add]; congr 1; omega

/-- `closeCheck` with `p` (`8 w` octets `pB`): `rbp` the mask of
`|c − p| ≤ 2^(64 w − 100)`. -/
theorem closeInner_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 4 ≤ w) (hw' : w ≤ 64) {pP : Addr} {pB : List Byte} (hP : word s.mem B (8 * kP) = pP)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)) (hpl : pB.length = 8 * w) (hsrc : Src s B Z pP pB) :
    WP isa (seqs (([.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr kP)), .mov .rcx (.mem (hdr kLen)),
        .mov .rbx (.mem (hdr (sArr aX)))], loadBE] : List (Prog isa)) ++ diffLoop ++ negLoop ++ ([
      .block [.mov .r12 (.mem (hdr sW)), .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 2),
        .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ 28)))],
      setWord aTmp .rcx,
      .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aTmp))), .mov .r10 (.mem (hdr (sArr aAcc))),
        .mov32 .rbp (.imm 0)],
      wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp],
      .block [.alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]] : List (Prog isa)))) s fun t =>
      t.gpr .rbp = mask (decide (Spec.RsaKeyGen.absDiff (wv s.mem B (slot w aN) w) (Spec.Rsa.os2ip pB) ≤
        2 ^ (64 * w - 100))) ∧
      Good t B Z w minv ∧ Frm B (closeRanges w) s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r10, .r12, .r14, .r15] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hw8 : (8 * w + 7) / 8 = w := by omega
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have sX := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  have sA := Nat.le_trans (slot_le (w := w) (show aAcc < 8 by decide)) hZ
  have sT := Nat.le_trans (slot_le (w := w) (show aTmp < 8 by decide)) hZ
  have hsl : ∀ r ∈ closeRanges w, r.1 + r.2 ≤ Z := by
    simp only [closeRanges, List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl | rfl) <;> omega
  have hdisj : ∀ j < 8, j ≠ aX → j ≠ aAcc → j ≠ aTmp → ∀ r ∈ closeRanges w,
      slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
    intro j hj h1 h2 h3 r hr
    simp only [closeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact slot_sep h1
    · exact slot_sep h2
    · exact slot_sep h3
  have hhd : ∀ i < 32, ∀ r ∈ closeRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
    intro i hi r hr
    simp only [closeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Or.inl (hdr_lt_slot w _ hi)
  refine wp_seqs_append (by simp) (by simp) ?_
  refine wp_seqs_append (by simp) (by simp [negLoop]) ?_
  refine wp_seqs_append (by simp) (by simp [diffLoop]) ?_
  simp only [seqs]
  -- `p` into `aX`.
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rcx, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rsi = pP ∧ t.gpr .rcx = BitVec.ofNat 64 (8 * w) ∧ t.gpr .rbx = off B (slot w aX) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl kP (by decide), hl kLen (by decide),
      hl (sArr aX) (by decide), hg.hdr.hw, hP, hK, hg.hdr.harr aX (by decide)]) rfl)
    fun s₁ ⟨⟨h12₁, hsi₁, hcx₁, hbx₁, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  refine WP.mono (loadArr_ok (j := aX) hs₁ (by decide) (by rw [hw8]; exact hZ)
    (hsrc.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁) hpl (by omega) (by omega) hsi₁ hcx₁
    (by rw [hw8]; exact hbx₁)) fun s₂ ⟨hp₂, ha₂, k₂⟩ => ?_
  rw [hw8] at hp₂ ha₂
  have hf₂ : Frm B (closeRanges w) s.mem s₂.mem := by
    rw [← hm₁]; exact Frm.of_arrays ha₂ fun _ hj => (List.mem_singleton.mp hj) ▸ by simp [closeRanges]
  have hg₂ : Good s₂ B Z w minv := ⟨hs₁.congr k₂.2.2, (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi),
    ha₂.hdr (by rw [hm₁]; exact hg.hdr)⟩
  have hc₂ : wv s₂.mem B (slot w aN) w = wv s.mem B (slot w aN) w :=
    hf₂.wv_eq (fun r hr => by have := hdisj aN (by decide) (by decide) (by decide) (by decide) r hr; omega) (by omega)
  -- `c − p`.
  refine WP.mono (diff_ok hg₂ hZ (by omega) (by omega)) fun s₃ ⟨b, hb₃, hv₃, ho₃, h12₃, k₃⟩ => ?_
  rw [hc₂, hp₂] at hv₃
  have hf₃ : Frm B (closeRanges w) s.mem s₃.mem :=
    hf₂.trans (Frm.of_outside (ho₃.mono (o' := slot w aAcc) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp [closeRanges]))
  have hg₃ : Good s₃ B Z w minv := ⟨hg₂.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hg₂.rdi,
    Hdr.outside hg₂.hdr ho₃ (by unfold slot; omega)⟩
  -- `|c − p|`.
  refine WP.mono (neg_ok hg₃ hZ (by omega) (by omega) hb₃ h12₃) fun s₄ ⟨hv₄, ho₄, k₄⟩ => ?_
  have hD := wv_lt s₃.mem B (slot w aAcc) w
  have habs : wv s₄.mem B (slot w aAcc) w = Spec.RsaKeyGen.absDiff (wv s.mem B (slot w aN) w) (Spec.Rsa.os2ip pB) := by
    rw [hv₄, absDiff_of hv₃ hD]
    exact Nat.mod_eq_of_lt (by
      unfold Spec.RsaKeyGen.absDiff
      have := wv_lt s.mem B (slot w aN) w
      have : Spec.Rsa.os2ip pB < 2 ^ (64 * w) := by
        have := os2ip_lt pB; rw [hpl, pow256_eq] at this; rwa [show 8 * (8 * w) = 64 * w by omega] at this
      split <;> omega)
  have hf₄ : Frm B (closeRanges w) s.mem s₄.mem :=
    hf₃.trans (Frm.of_outside (ho₄.mono (o' := slot w aAcc) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp [closeRanges]))
  have hg₄ : Good s₄ B Z w minv := ⟨hg₃.scr.congr k₄.2.2, (k₄.gpr (by decide)).trans hg₃.rdi,
    Hdr.outside hg₃.hdr ho₄ (by unfold slot; omega)⟩
  -- The bound.
  refine WP.assoc (WP.seq (WP.mono (bound_ok hg₄ hZ hw (by omega)) fun s₅ ⟨hT₅, ho₅, k₅⟩ => ?_))
  have hf₅ : Frm B (closeRanges w) s.mem s₅.mem := hf₄.trans (Frm.of_outside ho₅ (by simp [closeRanges]))
  have hg₅ : Good s₅ B Z w minv := ⟨hg₄.scr.congr k₅.2.2, (k₅.gpr (by decide)).trans hg₄.rdi,
    Hdr.outside hg₄.hdr ho₅ (by unfold slot; omega)⟩
  have hA₅ : wv s₅.mem B (slot w aAcc) w = Spec.RsaKeyGen.absDiff (wv s.mem B (slot w aN) w) (Spec.Rsa.os2ip pB) := by
    rw [ho₅.wv (k := w) (by have := slot_sep (w := w) (show aTmp ≠ aAcc by decide); omega) (by omega)]; exact habs
  have hl₅ : ∀ i < 32, InRegions (s₅.rd ++ s₅.wr) (off B (8 * i)) 8 := fun i hi =>
    hg₅.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.seq (WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = off B (slot w aTmp) ∧ t.gpr .r10 = off B (slot w aAcc) ∧ t.gpr .rbp = mask false ∧ t.mem = s₅.mem) (by
    xrun [State.ea, hdr, hg₅.rdi, hdrOff, hl₅ sW (by decide), hl₅ (sArr aTmp) (by decide), hl₅ (sArr aAcc) (by decide),
      hg₅.hdr.hw, hg₅.hdr.harr aTmp (by decide), hg₅.hdr.harr aAcc (by decide)]) rfl)
    fun s₆ ⟨⟨h12₆, hbx₆, h10₆, hbp₆, hm₆⟩, k₆⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (hg₅.scr.congr k₆.2.2) hbx₆ h10₆ h12₆ hbp₆ (by omega) (by omega) (by omega)
    (by omega)) fun s₇ ⟨hbp₇, hm₇, k₇⟩ => ?_)
  rw [hm₆, hT₅, hA₅] at hbp₇
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask (!decide (2 ^ (64 * w - 100) <
      Spec.RsaKeyGen.absDiff (wv s.mem B (slot w aN) w) (Spec.Rsa.os2ip pB))) ∧ t.mem = s₇.mem) (by
    xrun [sxm1, hbp₇, mask_not]) rfl) fun t ⟨⟨hbp, hm⟩, k⟩ => ⟨?_, ⟨hg₅.scr.congr (k.2.2.trans (k₇.2.2.trans k₆.2.2)),
      (k.gpr (by decide)).trans ((k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans hg₅.rdi)),
      by rw [hm, hm₇, hm₆]; exact hg₅.hdr⟩, by rw [hm, hm₇, hm₆]; exact hf₅,
      (((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k).mono (by decide)⟩
  rw [hbp, ← decide_not]; simp only [Nat.not_lt]

theorem mask_beq_zero (b : Bool) : (mask b &&& mask b == (0 : BitVec 64)) = !b := by cases b <;> decide

/-- `closeCheck`: ZF set unless the candidate is too close to `p` (none if
`p_len = 0`). -/
theorem closeCheck_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 4 ≤ w) (hw' : w ≤ 64) {pP : Addr} {pB : List Byte} (hP : word s.mem B (8 * kP) = pP)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hPl : word s.mem B (8 * kPlen) = BitVec.ofNat 64 pB.length) (hpl : pB.length = 0 ∨ pB.length = 8 * w)
    (hsrc : Src s B Z pP pB) :
    WP isa (seqs closeCheck) s fun t =>
      t.zf = some (!Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime pB) (wv s.mem B (slot w aN) w)) ∧
      Good t B Z w minv ∧ Frm B (closeRanges w) s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r10, .r12, .r14, .r15] s t := by
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kPlen)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show kPlen < 32 by decide); omega)
  have hlen : pB.length < 2 ^ 64 := by omega
  unfold closeCheck
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.zf = some (decide (pB = [])) ∧ t.gpr .rbp = mask false ∧
      t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hPl]
    cases pB with
    | nil => rfl
    | cons a l =>
      refine beq_false_of_ne fun h => ?_
      have := congrArg BitVec.toNat h
      rw [BitVec.and_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen] at this
      exact absurd this (by simp)) rfl)
    fun s₁ ⟨⟨hz₁, hbp₁, hm₁⟩, k₁⟩ => ?_)
  have hg₁ : Good s₁ B Z w minv := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  have fin : ∀ (t : State) (b : Bool), t.gpr .rbp = mask b →
      b = Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime pB) (wv s.mem B (slot w aN) w) →
      Good t B Z w minv → Frm B (closeRanges w) s.mem t.mem →
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r10, .r12, .r14, .r15] s t →
      WP isa (.block [.alu .test .rbp (.reg .rbp)]) t fun t' =>
        t'.zf = some (!Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime pB) (wv s.mem B (slot w aN) w)) ∧
        Good t' B Z w minv ∧ Frm B (closeRanges w) s.mem t'.mem ∧
        Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r10, .r12, .r14, .r15] s t' := by
    intro t b hb hbv hgt hf kt
    refine WP.mono (WP.keep [.rbp] (Q := fun t' => t'.zf = some (!b) ∧ t'.mem = t.mem) (by
      xrun [hb, mask_beq_zero]) rfl)
      fun t' ⟨⟨hz, hm⟩, k⟩ => ⟨hbv ▸ hz, ⟨hgt.scr.congr k.2.2, (k.gpr (by decide)).trans hgt.rdi, by rw [hm]; exact hgt.hdr⟩,
        by rw [hm]; exact hf, (kt.trans k).mono (by decide)⟩
  refine WP.seq (WP.ite (!decide (pB = [])) (by simp [eval, hz₁]) (fun he => ?_) (fun he => ?_))
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at he
    have hpl8 : pB.length = 8 * w := hpl.resolve_left (by rw [List.length_eq_zero_iff]; exact he)
    refine WP.mono (closeInner_ok hg₁ hZ hw hw' (by rw [hm₁]; exact hP) (by rw [hm₁]; exact hK) hpl8
      (hsrc.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁)) fun t ⟨hbp, hgt, hf, kt⟩ =>
      fin t _ hbp ?_ hgt (by rw [hm₁] at hf; exact hf) ((k₁.trans kt).mono (by decide))
    simp only [Spec.RsaKeyGen.otherPrime, he, ↓reduceIte, Spec.RsaKeyGen.tooClose, hm₁]
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at he
    refine WP.block_nil (fin s₁ false hbp₁ ?_ hg₁ (by rw [hm₁]; exact Frm.refl _ _ _) (k₁.mono (by decide)))
    simp only [Spec.RsaKeyGen.otherPrime, he, ↓reduceIte, Spec.RsaKeyGen.tooClose]

end VG.Proof.RsaKeyGen.X86_64
