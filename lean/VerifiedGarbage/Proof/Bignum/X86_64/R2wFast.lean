import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.PubR2

/-!
# `R² mod m` by word steps on x86-64

`steps`: `c` word steps, `x := x 2^(64 c) mod m` (`steps_ok`); `fast`:
`R - m`, the reciprocal `v` of `m`'s top word, `w / 4` steps and two
squarings, `R² mod m` (`fast_ok`); and
`choice`, which takes `fast` for `m`'s top bit set and `w` a multiple of 4,
`vg_rsa_public`'s computation otherwise (`choice_ok`, with `r2_ok`'s
result).
-/

namespace VG.Proof.Bignum.X86_64.R2w

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Words VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.WordStep

/-! ## The steps -/

/-- After `j` of `c` steps from `s`, from `x = X`, modulo `m = M` whose top
word is `T`, with `v = ⌊(2^128 - 1) / T⌋ - 2^64` the temporary's first word. -/
structure StepsInv (s : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (c X M T j : Nat) (t : State) :
    Prop where
  scr : Scr t B Z
  rdi : t.gpr .rdi = B
  hdr : Hdr t.mem B w minv
  cnt : word t.mem B (8 * sCnt) = BitVec.ofNat 64 (c - j)
  xv : wv t.mem B (slot w aR2) w = X * 2 ^ (64 * j) % M
  nv : wv t.mem B (slot w aN) w = M
  top : (word t.mem B (slot w aN + 8 * (w - 1))).toNat = T
  rcp : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / T - 2 ^ 64
  frm : Frm B (r2Ranges w) s.mem t.mem
  keep : Keep mmRegs s t

theorem stepIter_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {c X M T j : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hc : c < 2 ^ 31) (hM : 0 < M) (hT : 2 ^ 63 ≤ T)
    (hj : j < c) {t : State} (hI : StepsInv s B Z w minv c X M T j t) :
    WP isa (.seq step (.block (dblCount sCnt))) t fun t' =>
      t'.zf = some (decide (j + 1 = c)) ∧ StepsInv s B Z w minv c X M T (j + 1) t' := by
  have hn := hI.scr.nowrap
  have hsl8 := slot_le (w := w) (show aN < 8 by decide)
  have hhs : ∀ j, 8 * sCnt + 8 ≤ slot w j := fun j => hdr_lt_slot w j (show sCnt < 32 by decide)
  have hZ0 := slot_le (w := w) (show 0 < 8 by decide)
  have hc0 : 8 * sCnt + 8 ≤ Z := by have := hhs 0; omega_using [hZ, hZ0, this]
  have hlt : wv t.mem B (slot w aR2) w < wv t.mem B (slot w aN) w := by rw [hI.xv, hI.nv]; exact Nat.mod_lt _ hM
  have hst := step_ok (L := ⟨B, Z, w, minv⟩) ⟨⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩ hw hw' (by rw [hI.top]; exact hT)
    (by rw [hI.rcp, hI.top]) hlt
  refine WP.seq (WP.mono hst fun t₁ ⟨hg₁, hv₁, ha₁, k₁⟩ => ?_)
  dsimp only at hg₁ hv₁ ha₁
  have hst₁ : Scr t₁ B Z := hg₁.1.scr
  have hdi₁ : t₁.gpr .rdi = B := hg₁.1.rdi
  have hH₁ : Hdr t₁.mem B w minv := hg₁.1.hdr
  have hcnt₁ : word t₁.mem B (8 * sCnt) = BitVec.ofNat 64 (c - j) := by
    rw [ha₁.word_eq (fun j' hj' => Or.inl (by simp at hj'; rcases hj' with rfl | rfl <;> exact hhs _))
      (by omega_using [hn, hc0]), hI.cnt]
  have hld : InRegions (t₁.rd ++ t₁.wr) (off B (8 * sCnt)) 8 := hst₁.ld hc0
  have hsto : InRegions t₁.wr (off B (8 * sCnt)) 8 := hst₁.st hc0
  refine WP.mono (WP.keep [.rcx] (Q := fun t' => t'.mem = t₁.mem.writeW (off B (8 * sCnt))
      (BitVec.ofNat 64 (c - (j + 1))) ∧ t'.zf = some (decide (c - (j + 1) = 0))) (by
    xrun [State.ea, hdr, hdi₁, hdrOff, hld, hsto, hcnt₁,
      ofNat64_pred (show 1 ≤ c - j by omega_using [hj]) (by omega_using [hc]),
          ofNat64_beq_zero (show c - j - 1 < 2 ^ 64 by omega_using [hc])]
    exact ⟨by congr 2, by congr 1⟩) rfl) fun t' ⟨⟨hm', hz'⟩, k'⟩ => ⟨?_, ?_⟩
  · rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega_using [hj])
  have o' : Outside B (8 * sCnt) 8 t₁.mem t'.mem := by rw [hm']; exact writeW_outside _ _ _ (by omega_using [hn, hc0])
  have hN₁ : wv t₁.mem B (slot w aN) w = M := by
    rw [ha₁.wv_eq (fun j' hj' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl | rfl
      · have := Rsa.slot_lt (w := w) (show aN < aAcc by decide); omega_using [this]
      · have := Rsa.slot_lt (w := w) (show aN < aR2 by decide); omega_using [this]) (by omega_using [hZ, hn, hsl8]), hI.nv]
  have hT₁ : (word t₁.mem B (slot w aN + 8 * (w - 1))).toNat = T := by
    rw [ha₁.word_eq (fun j' hj' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl | rfl
      · have := Rsa.slot_lt (w := w) (show aN < aAcc by decide); omega_using [this]
      · have := Rsa.slot_lt (w := w) (show aN < aR2 by decide); omega_using [this]) (by omega_using [hZ, hn, hsl8]), hI.top]
  have hsv := slot_le (w := w) (show aTmp < 8 by decide)
  have hV₁ : (word t₁.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / T - 2 ^ 64 := by
    rw [ha₁.word_eq (fun j' hj' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl | rfl
      · have := Rsa.slot_lt (w := w) (show aAcc < aTmp by decide); omega_using [this]
      · have := Rsa.slot_lt (w := w) (show aTmp < aR2 by decide); omega_using [this]) (by omega_using [hZ, hn, hsv]), hI.rcp]
  have hH' : Hdr t'.mem B w minv := by rw [hm']; exact Hdr.store hH₁ (by decide) (by decide) _
  refine ⟨hst₁.congr k'.2.2, (k'.gpr (by decide)).trans hdi₁, hH', by rw [hm', word_writeW_self], ?_, ?_, ?_, ?_,
    ?_, ((hI.keep.trans k₁).trans k').mono (by decide)⟩
  · rw [o'.wv (by have := hhs aR2; omega_using [this])
      (by have := slot_le (w := w) (show aR2 < 8 by decide); omega_using [hZ, hn, this]), hv₁,
      hI.xv, hI.nv, Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add, show 64 * j + 64 = 64 * (j + 1) by omega_using []]
  · rw [o'.wv (by have := hhs aN; omega_using [this]) (by omega_using [hZ, hn, hsl8]), hN₁]
  · rw [o'.word (by have := hhs aN; omega_using [this]) (by omega_using [hZ, hn, hsl8]), hT₁]
  · rw [o'.word (by have := hhs aTmp; omega_using [this]) (by omega_using [hZ, hn, hsv]), hV₁]
  · exact (hI.frm.trans (Frm.of_arrays ha₁ (by simp [r2Ranges]))).trans (Frm.of_outside o' (by simp [r2Ranges]))

theorem steps_eq : steps =
    .seq (.block [.store (hdr sCnt) .rcx]) (.loop (.seq step (.block (dblCount sCnt))) .ne) := rfl

/-- `steps`' start: the count `c` into `sCnt`. -/
theorem stepsStart_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {c : Nat}
    (hcx : s.gpr .rcx = BitVec.ofNat 64 c) (hO : wv s.mem B (slot w aR2) w < wv s.mem B (slot w aN) w)
    (hv : (word s.mem B (slot w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem B (slot w aN + 8 * (w - 1))).toNat - 2 ^ 64) :
    WP isa (.block [.store (hdr sCnt) .rcx]) s (StepsInv s B Z w minv c (wv s.mem B (slot w aR2) w)
      (wv s.mem B (slot w aN) w) (word s.mem B (slot w aN + 8 * (w - 1))).toNat 0) := by
  have hn := hs.nowrap
  have hsl8 := slot_le (w := w) (show aN < 8 by decide)
  have hsr8 := slot_le (w := w) (show aR2 < 8 by decide)
  have hsv := slot_le (w := w) (show aTmp < 8 by decide)
  have hhs : ∀ j, 8 * sCnt + 8 ≤ slot w j := fun j => hdr_lt_slot w j (show sCnt < 32 by decide)
  have hZ0 := slot_le (w := w) (show 0 < 8 by decide)
  have hc0 : 8 * sCnt + 8 ≤ Z := by have := hhs 0; omega_using [hZ, hZ0, this]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sCnt)) (s.gpr .rcx))
    (by xrun [State.ea, hdr, hdi, hdrOff, hs.st hc0]) rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have o₁ : Outside B (8 * sCnt) 8 s.mem s₁.mem := by rw [hm₁]; exact writeW_outside _ _ _ (by omega_using [hn, hc0])
  exact ⟨hs.congr k₁.2.2, (k₁.gpr (by decide)).trans hdi, by rw [hm₁]; exact Hdr.store hH (by decide) (by decide) _,
      by rw [hm₁, word_writeW_self, hcx, Nat.sub_zero],
      by rw [o₁.wv (by have := hhs aR2; omega_using [this]) (by omega_using [hZ, hn, hsr8]), Nat.mul_zero, Nat.pow_zero, Nat.mul_one,
        Nat.mod_eq_of_lt hO],
      o₁.wv (by have := hhs aN; omega_using [this]) (by omega_using [hZ, hn, hsl8]),
      by rw [o₁.word (by have := hhs aN; omega_using [this]) (by omega_using [hZ, hn, hsl8])],
      by rw [o₁.word (by have := hhs aTmp; omega_using [this]) (by omega_using [hZ, hn, hsv])]; exact hv,
      Frm.of_outside o₁ (by simp [r2Ranges]), k₁.mono (by decide)⟩

/-- What `steps` leaves, from `StepsInv`. -/
theorem StepsInv.post {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {c X M T : Nat} {t : State}
    (hZ : slot w 8 ≤ Z) (hI : StepsInv s B Z w minv c X M T c t) :
    wv t.mem B (slot w aR2) w = X * 2 ^ (64 * c) % M ∧ wv t.mem B (slot w aN) w = M ∧
      (word t.mem B (slot w aN) = word s.mem B (slot w aN)) ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Good t B Z w minv ∧ Keep mmRegs s t := by
  have hn := hI.scr.nowrap
  have hsl8 := slot_le (w := w) (show aN < 8 by decide)
  exact ⟨hI.xv, hI.nv, by
      rw [hI.frm.word_eq (fun r hr => by
        have := r2Ranges_arr w (j := aN) (by decide) (by decide) (by decide) r hr; omega_using [this]) (by omega_using [hZ, hn, hsl8])],
    hI.frm, ⟨hI.scr, hI.rdi, hI.hdr⟩, hI.keep⟩

/-- `steps`: `c ≥ 1` word steps (the count in `rcx`), `x := x 2^(64 c) mod m`. -/
theorem steps_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 30)
    {c : Nat} (hc : 1 ≤ c) (hc' : c < 2 ^ 31) (hcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (hT : 2 ^ 63 ≤ (word s.mem B (slot w aN + 8 * (w - 1))).toNat)
    (hv : (word s.mem B (slot w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem B (slot w aN + 8 * (w - 1))).toNat - 2 ^ 64)
    (hO : wv s.mem B (slot w aR2) w < wv s.mem B (slot w aN) w) :
    WP isa steps s fun t =>
      wv t.mem B (slot w aR2) w = wv s.mem B (slot w aR2) w * 2 ^ (64 * c) % wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w aN) w = wv s.mem B (slot w aN) w ∧
      (word t.mem B (slot w aN) = word s.mem B (slot w aN)) ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Good t B Z w minv ∧ Keep mmRegs s t := by
  have hM : 0 < wv s.mem B (slot w aN) w := Nat.lt_of_le_of_lt (Nat.zero_le _) hO
  rw [steps_eq]
  refine WP.seq (WP.mono (stepsStart_ok hs hdi hH hZ hcx hO hv) fun s₁ h0 => ?_)
  exact wp_upto (a := 0) (N := c) (by omega_using [hc]) _ (fun j _ hj t hI => stepIter_ok hZ hw hw' hc' hM hT hj hI)
    (fun t hI => hI.post hZ) h0

/-! ## `R - m` -/

/-- After `j` words of `x := 0 - m` from `s₀`: `X_j + M_j = 2^(64 j) b`. -/
structure NegInv (s₀ : State) (B : Addr) (Z ex em : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B ex (8 * j) s₀.mem t.mem
  val : ∃ b : Bool, t.gpr .rbp = mask b ∧ wv t.mem B ex j + wv s₀.mem B em j = 2 ^ (64 * j) * b.toNat

theorem negStep_ok {s₀ : State} {B : Addr} {Z w ex em : Nat}
    (hbx : s₀.gpr .rbx = off B ex) (h10 : s₀.gpr .r10 = off B em) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (_hw : w < 2 ^ 31) (hX : ex + 8 * w ≤ Z) (hM : em + 8 * w ≤ Z) (sM : ex + 8 * w ≤ em ∨ em + 8 * w ≤ ex)
    {j : Nat} (hj : j < w) {t : State} (hI : NegInv s₀ B Z ex em j t) :
    WP isa (.block (negBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t fun t' =>
      t'.zf = some (decide (j + 1 = w)) ∧ NegInv s₀ B Z ex em (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B ex := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = off B em := (hI.keep.gpr (by decide)).trans h10
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨b, hbp, hval⟩ := hI.val
  have hld : InRegions (t.rd ++ t.wr) (off B (em + 8 * j)) 8 := hI.scr.ld (by omega_using [hM, hj])
  have hst : InRegions t.wr (off B (ex + 8 * j)) 8 := hI.scr.st (by omega_using [hX, hj])
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ => ∃ (v : BitVec 64) (b' : Bool),
      t₁.mem = t.mem.writeW (off B (ex + 8 * j)) v ∧ t₁.gpr .rbp = mask b' ∧
      v.toNat + (t.mem.readW (off B (em + 8 * j)) 64).toNat + b.toNat = 2 ^ 64 * b'.toNat) ?_ rfl)
    fun t₁ ⟨⟨v, b', hm₁, hbp₁, hv₁⟩, k₁⟩ => ?_
  · unfold negBody cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tbx hI.r14, addr0 t10 hI.r14, hld, hst, hbp, cf_mask]
    have := sbb_toNat (BitVec.setWidth 64 (0 : BitVec 32)) (t.mem.readW (off B (em + 8 * j)) 64) b
    rw [show (BitVec.setWidth 64 (0 : BitVec 32)).toNat = 0 from rfl, Nat.zero_add] at this
    exact ⟨_, _, rfl, rfl, this⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_using [hM, hj, hn]) (by omega_using [hM, hn])) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hy : t.mem.readW (off B (em + 8 * j)) 64 = word s₀.mem B (em + 8 * j) := hI.out.word (by omega_using [sM, hj])
      (by omega_using [hM, hj, hn])
  rw [hy] at hv₁
  have hmem : t'.mem = t.mem.writeW (off B (ex + 8 * j)) v := by rw [hm', hm₁]
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨b', (k'.gpr (by decide)).trans hbp₁, ?_⟩⟩
  · rw [hmem]
    intro x hx'
    rw [writeW_outside t.mem B v (by omega_using [hX, hj, hn]) x (by omega_using [hx'])]
    exact hI.out x (by omega_using [hx'])
  · rw [hmem, wv_writeW_top _ _ _ _ _ (by omega_using [hX, hj, hn])]
    simp only [wv]
    rw [pow64_succ]
    grind

/-- `x := 0 - m` over `w` words, for `x` at `rbx` and `m` at `r10`: `R - m`,
for `0 < m < R`. -/
theorem neg_ok {s : State} {B : Addr} {Z w ex em : Nat} (hs : Scr s B Z)
    (hbx : s.gpr .rbx = off B ex) (h10 : s.gpr .r10 = off B em) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hbp : s.gpr .rbp = mask false) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hX : ex + 8 * w ≤ Z)
    (hM : em + 8 * w ≤ Z) (sM : ex + 8 * w ≤ em ∨ em + 8 * w ≤ ex) (hM0 : 0 < wv s.mem B em w) :
    WP isa (wordLoop 0 negBody) s fun t =>
      wv t.mem B ex w = 2 ^ (64 * w) - wv s.mem B em w ∧ Outside B ex (8 * w) s.mem t.mem ∧
      Keep [.rax, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      NegInv s B Z ex em 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by simp [wv]⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega_using [hw]) hw' (NegInv s B Z ex em) h0
    (fun j _ hj t hI => negStep_ok hbx h10 h12 hw' hX hM sM hj hI)) fun t hI => ?_
  obtain ⟨b, -, hval⟩ := hI.val
  refine ⟨?_, hI.out, hI.keep⟩
  have h1 := wv_lt t.mem B ex w
  have h2 := wv_lt s.mem B em w
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one] at hval <;> omega_using [hM0, hval]

/-! ## `R² mod m` by word steps -/

theorem shr2_ofNat {w : Nat} (hw : w < 2 ^ 64) : BitVec.ofNat 64 w >>> 2 = BitVec.ofNat 64 (w / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_using [hw])]

/-- `R - m ≡ R (mod m)`, and so for its multiples. -/
theorem sub_mul_mod {R N k : Nat} (h : N ≤ R) : (R - N) * k % N = R * k % N := by
  obtain ⟨D, rfl⟩ : ∃ D, R = D + N := ⟨R - N, by omega_using [h]⟩
  rw [Nat.add_sub_cancel, Nat.add_mul, Nat.add_mul_mod_self_left]

theorem fast_eq (mul : Nat → Nat → Nat → Prog isa) : fast mul = .seq (.block [.mov .rbx (.mem (hdr (sArr aR2))),
      .mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aTmp))),
      .mov32 .rbp (.imm 0)])
    (.seq (wordLoop 0 negBody) (.seq recip (.seq (.block [.mov .rcx (.mem (hdr sW)), .shift .shr .rcx 2])
      (.seq steps (.seq (mul aR2 aR2 aR2) (mul aR2 aR2 aR2)))))) := rfl

/-- `fast`: `R² mod m`, for the odd `m` of `w` words (a multiple of 4), its
top word at least `2^63`; with `r2_ok`'s result. -/
theorem fast_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem B (slot w aN) w = N) (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : N % 2 = 1) (hT : 2 ^ 63 ≤ (word s.mem B (slot w aN + 8 * (w - 1))).toNat) (h4 : w % 4 = 0) :
    WP isa (fast M.mm) s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aR2) w < N ∧ wv t.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw' : w < 2 ^ 31 := by omega_using [hw30]
  have hs := hg.scr
  have hnw := hs.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hZ, hnw]
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hN0 : 0 < N := by omega_using [hodd]
  have hNR : N < 2 ^ (64 * w) := hn ▸ wv_lt _ _ _ _
  have hsx := slot_le (w := w) (show aR2 < 8 by decide)
  have hsm := slot_le (w := w) (show aN < 8 by decide)
  have hsv := slot_le (w := w) (show aTmp < 8 by decide)
  have sXM := Rsa.slot_lt (w := w) (show aN < aR2 by decide)
  have sXV := Rsa.slot_lt (w := w) (show aTmp < aR2 by decide)
  have sMV := Rsa.slot_lt (w := w) (show aN < aTmp by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  -- `m > R / 2`: its top bit is set, and it is odd.
  have hhalf : 2 ^ (64 * w) < 2 * N := by
    have e : N = wv s.mem B (slot w aN) (w - 1) +
        2 ^ (64 * (w - 1)) * (word s.mem B (slot w aN + 8 * (w - 1))).toNat := by
      rw [← hn, show w = (w - 1) + 1 by omega_using [hw], wv_succ, show w - 1 + 1 - 1 = w - 1 by omega_using []]
    have hp : 2 ^ (64 * w) = 2 * (2 ^ (64 * (w - 1)) * 2 ^ 63) := by
      rw [← Nat.pow_add, show 64 * w = 1 + (64 * (w - 1) + 63) by omega_using [hw], Nat.pow_add, Nat.pow_one]
    have hle := Nat.mul_le_mul_left (2 ^ (64 * (w - 1))) hT
    have hev : 2 ^ (64 * (w - 1)) * 2 ^ 63 % 2 = 0 := by
      rw [Nat.mul_mod, show 2 ^ 63 % 2 = 0 by decide, Nat.mul_zero, Nat.zero_mod]
    omega_using [hodd, e, hp, hle]
  rw [fast_eq M.mm]
  refine WP.seq (WP.mono (WP.keep [.rbx, .r10, .r12, .r8, .rbp] (Q := fun t =>
      t.gpr .rbx = off B (slot w aR2) ∧ t.gpr .r10 = off B (slot w aN) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aTmp) ∧ t.gpr .rbp = mask false ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr aR2) (by decide), hl (sArr aN) (by decide), hl sW (by decide),
      hl (sArr aTmp) (by decide), hg.hdr.harr aR2 (by decide), hg.hdr.harr aN (by decide), hg.hdr.hw,
      hg.hdr.harr aTmp (by decide)]) rfl)
    fun t₁ ⟨⟨h1bx, h110, h112, h18, h1bp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hM0 : 0 < wv t₁.mem B (slot w aN) w := by rw [hm₁, hn]; exact hN0
  have e1 : slot w aR2 + 8 * w ≤ Z := by omega_using [hZ, hsx]
  have e2 : slot w aN + 8 * w ≤ Z := by omega_using [sXV, sMV, e1]
  have sM : slot w aR2 + 8 * w ≤ slot w aN ∨ slot w aN + 8 * w ≤ slot w aR2 := by omega_using [sXV, sMV]
  have hng := neg_ok hs₁ h1bx h110 h112 h1bp (by omega_using [hw]) hw' e1 e2 sM hM0
  refine WP.seq (WP.mono hng fun t₂ ⟨hx₂, ho₂, k₂⟩ => ?_)
  rw [hm₁, hn] at hx₂
  have hs₂ := hs₁.congr k₂.2.2
  -- `v`.
  have h210 : t₂.gpr .r10 = off B (slot w aN) := (k₂.gpr (by decide)).trans h110
  have h212 : t₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans h112
  have h28 : t₂.gpr .r8 = off B (slot w aTmp) := (k₂.gpr (by decide)).trans h18
  have eV : slot w aTmp + 8 ≤ Z := by omega_using [sXV, e1]
  have hT₂ : 2 ^ 63 ≤ (word t₂.mem B (slot w aN + 8 * (w - 1))).toNat := by
    rw [ho₂.word (by omega_using [sXV, sMV]) (by omega_using [hn', hsv, sMV]), hm₁]; exact hT
  refine WP.seq (WP.mono (recip_ok hs₂ h210 h212 h28 (by omega_using [hw]) e2 eV hT₂) fun t₂' ⟨hm₂', k₂'⟩ => ?_)
  have hvlt : (2 ^ 128 - 1) / (word t₂.mem B (slot w aN + 8 * (w - 1))).toNat - 2 ^ 64 < 2 ^ 64 := by
    have : (2 ^ 128 - 1) / (word t₂.mem B (slot w aN + 8 * (w - 1))).toNat < 2 ^ 65 := by
      rw [Nat.div_lt_iff_lt_mul (by omega_using [hT₂])]; omega_using [hT₂]
    omega_using [this]
  have o₂' : Outside B (slot w aTmp) 8 t₂.mem t₂'.mem := by rw [hm₂']; exact writeW_outside _ _ _ (by omega_using [hn', hsv])
  have hs₂' := hs₂.congr k₂'.2.2
  have hdi₂ : t₂'.gpr .rdi = B :=
    (k₂'.gpr (by decide)).trans ((k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi))
  have hH₂ : Hdr t₂'.mem B w minv :=
    (Arrays.of_outside (j := aTmp) (List.mem_singleton_self _) o₂' (Nat.le_refl _) (by omega_using [])).hdr
      ((Arrays.of_outside (j := aR2) (List.mem_singleton_self _) ho₂ (Nat.le_refl _) (by omega_using [])).hdr
        (hm₁ ▸ hg.hdr))
  have hl₂ : ∀ i < 32, InRegions (t₂'.rd ++ t₂'.wr) (off B (8 * i)) 8 := fun i hi =>
    hs₂'.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 (w / 4) ∧ t.mem = t₂'.mem)
    (by xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ sW (by decide), hH₂.hw, shr2_ofNat (show w < 2 ^ 64 by omega_using [hn', hsv])])
    rfl) fun t₃ ⟨⟨h3cx, hm₃⟩, k₃⟩ => ?_)
  have hN₃ : wv t₃.mem B (slot w aN) w = N := by
    rw [hm₃, o₂'.wv (by omega_using [sMV]) (by omega_using [hn', hsv, sMV]),
        ho₂.wv (by omega_using [sM]) (by omega_using [hn', hsv, sMV]), hm₁, hn]
  have hT₃ : 2 ^ 63 ≤ (word t₃.mem B (slot w aN + 8 * (w - 1))).toNat := by
    rw [hm₃, o₂'.word (by omega_using [sMV]) (by omega_using [hn', hsv, sMV])]; exact hT₂
  have hV₃ : (word t₃.mem B (slot w aTmp)).toNat =
      (2 ^ 128 - 1) / (word t₃.mem B (slot w aN + 8 * (w - 1))).toNat - 2 ^ 64 := by
    rw [hm₃, o₂'.word (d := slot w aN + 8 * (w - 1)) (by omega_using [sMV]) (by omega_using [hn', hsv, sMV]), hm₂', word_writeW_self,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
  have hO₃ : wv t₃.mem B (slot w aR2) w < wv t₃.mem B (slot w aN) w := by
    rw [hN₃, hm₃, o₂'.wv (by omega_using [sXV]) (by omega_using [hn', hsx]), hx₂]; omega_using [hNR, hhalf]
  have hsp := steps_ok (hs₂'.congr k₃.2.2) ((k₃.gpr (by decide)).trans hdi₂) (hm₃ ▸ hH₂) hZ hw hw30
    (c := w / 4) (by omega_using [hw, h4]) (by omega_using [hw']) h3cx hT₃ hV₃ hO₃
  refine WP.seq (WP.mono hsp fun t₄ ⟨hx₄, hn₄, hw₄, hf₄, hg₄, k₄⟩ => ?_)
  rw [hN₃, hm₃, o₂'.wv (by omega_using [sXV]) (by omega_using [hn', hsx]), hx₂, sub_mul_mod (Nat.le_of_lt hNR),
    show 64 * (w / 4) = 16 * w by omega_using [h4]] at hx₄
  rw [hN₃] at hn₄
  have hinv₄ : ((word t₄.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hw₄, hm₃, o₂'.word (by omega_using [sMV]) (by omega_using [hn', hsv, sMV]),
        ho₂.word (by omega_using [sXV, sMV]) (by omega_using [hn', hsv, sMV]), hm₁]; exact hinv
  have hsq := sqs_ok M 1 hg₄ hZ hw hw' hR (E := 16 * w) hn₄ hinv₄ (by rw [hx₄]; exact Nat.mod_lt _ hN0)
    (by rw [hx₄, Nat.mod_mod, Nat.mul_comm])
  refine WP.mono hsq fun t ⟨h1, h2, h3, h4', h5⟩ => ⟨h1, h2, ?_, ?_, ?_⟩
  · rw [h3, show 2 ^ (1 + 1) * (16 * w) = 64 * w by omega_using []]
  · have f₂ : Frm B (r2Ranges w) s.mem t₂.mem := by
      rw [← hm₁]; exact Frm.of_arrays (Arrays.of_outside (j := aR2) (List.mem_singleton_self _) ho₂
        (Nat.le_refl _) (by omega_using [])) (by simp [r2Ranges])
    have f₂' : Frm B (r2Ranges w) t₂.mem t₂'.mem :=
      Frm.of_arrays1 (Arrays.of_outside (j := aTmp) (List.mem_singleton_self _) o₂' (Nat.le_refl _) (by omega_using []))
        (by simp [r2Ranges])
    exact (((f₂.trans f₂').trans (by rw [hm₃]; exact Frm.refl _ _ _)).trans hf₄).trans
      (Frm.of_arrays h4' (by simp [r2Ranges]))
  · exact (((((k₁.trans k₂).trans k₂').trans k₃).trans k₄).trans h5).mono (by decide)

/-! ## The choice -/

/-- `fastTest`'s flag: whether the top bit of `T` is set and `w` is a multiple
of 4. -/
theorem fastFlag (T : BitVec 64) {w : Nat} (hw : w < 2 ^ 64) :
    ((T >>> 63 ^^^ BitVec.signExtend 64 (1 : BitVec 32)) ||| (BitVec.ofNat 64 w &&& BitVec.signExtend 64 (3 : BitVec 32))
      == 0) = decide (2 ^ 63 ≤ T.toNat ∧ w % 4 = 0) := by
  have h1 : (T >>> 63).toNat = T.toNat / 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h3 : (BitVec.ofNat 64 w &&& BitVec.signExtend 64 (3 : BitVec 32)).toNat = w % 4 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw, show (BitVec.signExtend 64 (3 : BitVec 32)).toNat
      = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hT := T.isLt
  generalize hx : (T >>> 63 ^^^ BitVec.signExtend 64 (1 : BitVec 32)) = x
  generalize hy : (BitVec.ofNat 64 w &&& BitVec.signExtend 64 (3 : BitVec 32)) = y at h3
  have hx' : x.toNat = if 2 ^ 63 ≤ T.toNat then 0 else 1 := by
    rw [← hx, BitVec.toNat_xor, h1, show (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 from rfl]
    by_cases h : 2 ^ 63 ≤ T.toNat
    · simp only [h, ite_true, show T.toNat / 2 ^ 63 = 1 by omega_using [h]]; rfl
    · simp only [h, ite_false, show T.toNat / 2 ^ 63 = 0 by omega_using [h]]; rfl
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have e := congrArg BitVec.toNat h
    rw [BitVec.toNat_or, show (0 : BitVec 64).toNat = 0 from rfl, Nat.or_eq_zero_iff] at e
    rw [hx'] at e
    refine ⟨?_, by omega_using [h3, e]⟩
    by_contra hc; simp only [hc, ite_false] at e; omega_using [e]
  · rintro ⟨hP, hQ⟩
    have ex : x = 0 := BitVec.eq_of_toNat_eq (by rw [hx']; simp [hP])
    have ey : y = 0 := BitVec.eq_of_toNat_eq (by rw [h3, hQ]; rfl)
    rw [ex, ey]; rfl

theorem old_eq (M : Mont) : seqs (old M.mm) = seqs (r2Steps M) := rfl

/-- `choice`: `R² mod m` for the odd `m` of `w ≥ 2` words, its top word not
zero, by word steps when `m`'s top bit is set and `w` is a multiple of 4 and
by `vg_rsa_public`'s computation otherwise: `r2_ok`'s result. -/
theorem choice_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem B (slot w aN) w = N) (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h10 : s.gpr .r10 = off B (slot w aN)) (hodd : N % 2 = 1)
    (hlo : 2 ^ (64 * (w - 1)) ≤ N) :
    WP isa (choice M.mm) s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aR2) w < N ∧ wv t.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hnw := hs.nowrap
  have hsm := slot_le (w := w) (show aN < 8 by decide)
  have hd8 : slot w aN + 8 * (w - 1) + 8 ≤ Z := by omega_using [hZ, hsm]
  have hld : InRegions (s.rd ++ s.wr) (off B (slot w aN + 8 * (w - 1))) 8 := hs.ld hd8
  unfold choice
  refine WP.seq (WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.zf = some (decide (2 ^ 63 ≤
      (word s.mem B (slot w aN + 8 * (w - 1))).toNat ∧ w % 4 = 0)) ∧ t.mem = s.mem) (by
    unfold fastTest
    xrun [State.ea, ix, addrm8 h10 h12 (by omega_using [hw]), hld]
    rw [h12]
    exact fastFlag _ (by omega_using [hnw, hd8])) rfl) fun t₁ ⟨⟨hz₁, hm₁⟩, k₁⟩ => ?_)
  have hg₁ : Good t₁ B Z w minv := ⟨hs.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, hm₁ ▸ hg.hdr⟩
  have hn₁ : wv t₁.mem B (slot w aN) w = N := by rw [hm₁, hn]
  have hinv₁ : ((word t₁.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by rw [hm₁]; exact hinv
  generalize hP : decide (2 ^ 63 ≤ (word s.mem B (slot w aN + 8 * (w - 1))).toNat ∧ w % 4 = 0) = P at hz₁
  refine WP.ite P (by simp only [eval, hz₁]) (fun hc => ?_) (fun hc => ?_)
  · obtain ⟨hT, h4⟩ := of_decide_eq_true (hP.trans hc)
    refine WP.mono (fast_ok M hg₁ hZ hw hw30 hn₁ hinv₁ hodd (by rw [hm₁]; exact hT) h4)
      fun t ⟨h1, h2, h3, h4', h5⟩ => ⟨h1, h2, h3, by rw [← hm₁]; exact h4', (k₁.trans h5).mono (by decide)⟩
  · rw [old_eq]
    refine WP.mono (r2_ok M hg₁ hZ hw hw30 hn₁ hinv₁ ((k₁.gpr (by decide)).trans h12)
      ((k₁.gpr (by decide)).trans h10) hodd hlo)
      fun t ⟨h1, h2, h3, h4', h5⟩ => ⟨h1, h2, h3, by rw [← hm₁]; exact h4', (k₁.trans h5).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.R2w
