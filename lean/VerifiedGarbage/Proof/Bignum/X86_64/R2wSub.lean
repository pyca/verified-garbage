import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.Csub

/-!
# `R² mod m` by word steps on x86-64: `x 2^64 - q̂ m`

`mulSub` computes `t = x 2^64 - q̂ m` over `w + 1` words, modulo
`2^(64 (w + 1))`, with the products' carry in `r9` and the borrow in `rbp`
(`mulSub_ok`): `t + q̂ m = x 2^64 + 2^(64 (w + 1)) b` for the borrow `b`.
-/

namespace VG.Proof.Bignum.X86_64.R2w

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Words
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.WordStep

/-- `mov rax, [r10 + 8 r14]; mul rcx; add rax, r9; adc rdx, 0; mov r9, rdx`:
`rax + 2^64 r9 = q̂ mᵢ + r9`. -/
theorem mulc_ok (s : State) {aS : Addr}
    (eS : s.gpr .r10 + s.gpr .r14 * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = aS)
    (hS : InRegions (s.rd ++ s.wr) aS 8) :
    WP isa (.block [.mov .rax (.mem (ix .r10 .r14)), .mul .rcx, .alu .add .rax (.reg .r9), .alu .adc .rdx (.imm 0),
        .mov .r9 (.reg .rdx)]) s fun t =>
      (t.gpr .rax).toNat + 2 ^ 64 * (t.gpr .r9).toNat =
        (s.gpr .rcx).toNat * (s.mem.readW aS 64).toNat + (s.gpr .r9).toNat ∧ t.mem = s.mem ∧
      Keep [.rax, .rdx, .r9] s t := by
  refine WP.mono (WP.keep [.rax, .rdx, .r9] (Q := fun t =>
      (t.gpr .rax).toNat + 2 ^ 64 * (t.gpr .r9).toNat =
        (s.gpr .rcx).toNat * (s.mem.readW aS 64).toNat + (s.gpr .r9).toNat ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  xrun [State.ea, ix, eS, hS, sx0]
  have hm := mul_toNat (s.mem.readW aS 64) (s.gpr .rcx)
  have hl := mul_le (s.mem.readW aS 64) (s.gpr .rcx)
  have hc := (s.gpr .r9).isLt
  have e1 := addc_toNat (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .rcx).toNat))
    (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .rcx).toNat / 2 ^ 64)) (s.gpr .r9) (by omega_arith)
  rw [e1, Nat.mul_comm (s.gpr .rcx).toNat]
  omega_arith

/-- `mov rdx, [rbx + 8 r14 - 8]; add rbp, rbp; sbb rdx, rax; sbb rbp, rbp;
mov [r8 + 8 r14], rdx`: `v + rax + c = x[i - 1] + 2^64 c'` stored, for the
borrow `c` in `rbp`, and the next borrow `c'` into `rbp`. -/
theorem sbbSt_ok (s : State) {aX aD : Addr} {c : Bool}
    (eX : s.gpr .rbx + s.gpr .r14 * BitVec.ofNat 64 8 + BitVec.ofInt 64 (-8) = aX)
    (eD : s.gpr .r8 + s.gpr .r14 * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = aD)
    (hX : InRegions (s.rd ++ s.wr) aX 8) (hD : InRegions s.wr aD 8) (hbp : s.gpr .rbp = mask c) :
    WP isa (.block [.mov .rdx (.mem (ix .rbx .r14 (-8))), cfFromRbp, .alu .sbb .rdx (.reg .rax), cfToRbp,
        .store (ix .r8 .r14) .rdx]) s fun t =>
      ∃ (v : BitVec 64) (c' : Bool), t.mem = s.mem.writeW aD v ∧ t.gpr .rbp = mask c' ∧
        v.toNat + (s.gpr .rax).toNat + c.toNat = (s.mem.readW aX 64).toNat + 2 ^ 64 * c'.toNat ∧
      Keep [.rdx, .rbp] s t := by
  refine WP.mono (WP.keep [.rdx, .rbp] (Q := fun t =>
      ∃ (v : BitVec 64) (c' : Bool), t.mem = s.mem.writeW aD v ∧ t.gpr .rbp = mask c' ∧
        v.toNat + (s.gpr .rax).toNat + c.toNat = (s.mem.readW aX 64).toNat + 2 ^ 64 * c'.toNat) ?_ rfl)
    fun t ⟨h, k⟩ => let ⟨v, c', h1, h2, h3⟩ := h; ⟨v, c', h1, h2, h3, k⟩
  unfold cfFromRbp cfToRbp
  xrun [State.ea, ix, eX, eD, hX, hD, hbp, cf_mask]
  exact ⟨_, _, rfl, rfl, sbb_toNat _ _ _⟩

/-- After words `0, …, j - 1` of `mulSub` from `s₀`, for `q̂` in `rcx`: the
words `T_j` of `t`, the carry `r9` and the borrow `b`:
`T_j + q̂ M_j = X_(j-1) 2^64 + 2^(64 j) (r9 + b)`. -/
structure MsInv (s₀ : State) (B : Addr) (Z ex em et q : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .rbp, .r9, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B et (8 * j) s₀.mem t.mem
  val : ∃ b : Bool, t.gpr .rbp = mask b ∧
    wv t.mem B et j + q * wv s₀.mem B em j = wv s₀.mem B ex (j - 1) * 2 ^ 64 + 2 ^ (64 * j) * ((t.gpr .r9).toNat + b.toNat)

theorem msStep_ok {s₀ : State} {B : Addr} {Z w ex em et : Nat}
    (hbx : s₀.gpr .rbx = off B ex) (h10 : s₀.gpr .r10 = off B em) (h8 : s₀.gpr .r8 = off B et)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 31) (hX : ex + 8 * w ≤ Z) (hM : em + 8 * w ≤ Z)
    (hT : et + 8 * (w + 1) ≤ Z)
    (sX : et + 8 * (w + 1) ≤ ex ∨ ex + 8 * w ≤ et) (sM : et + 8 * (w + 1) ≤ em ∨ em + 8 * w ≤ et)
    {j : Nat} (hj1 : 1 ≤ j) (hj : j < w) {t : State} (hI : MsInv s₀ B Z ex em et (s₀.gpr .rcx).toNat j t) :
    WP isa (.block (subBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t fun t' =>
      t'.zf = some (decide (j + 1 = w)) ∧ MsInv s₀ B Z ex em et (s₀.gpr .rcx).toNat (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B ex := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = off B em := (hI.keep.gpr (by decide)).trans h10
  have t8 : t.gpr .r8 = off B et := (hI.keep.gpr (by decide)).trans h8
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have tcx : t.gpr .rcx = s₀.gpr .rcx := hI.keep.gpr (by decide)
  obtain ⟨b, hbp, hval⟩ := hI.val
  rw [show subBody = [.mov .rax (.mem (ix .r10 .r14)), .mul .rcx, .alu .add .rax (.reg .r9),
      .alu .adc .rdx (.imm 0), .mov .r9 (.reg .rdx)] ++ [.mov .rdx (.mem (ix .rbx .r14 (-8))), cfFromRbp,
      .alu .sbb .rdx (.reg .rax), cfToRbp, .store (ix .r8 .r14) .rdx] from rfl, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (mulc_ok t (addr0 t10 hI.r14) (hI.scr.ld (by omega_arith))) fun t₁ ⟨hv₁, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁bx : t₁.gpr .rbx = off B ex := (k₁.gpr (by decide)).trans tbx
  have t₁8 : t₁.gpr .r8 = off B et := (k₁.gpr (by decide)).trans t8
  have t₁bp : t₁.gpr .rbp = mask b := (k₁.gpr (by decide)).trans hbp
  have hs₁ := hI.scr.congr k₁.2.2
  refine WP.mono (sbbSt_ok t₁ (addrm8 t₁bx t₁14 hj1) (addr0 t₁8 t₁14) (hs₁.ld (by omega_arith)) (hs₁.st (by omega_arith))
    t₁bp) fun t₂ ⟨v, b', hm₂, hbp₂, hv₂, k₂⟩ => ?_
  have t₂14 : t₂.gpr .r14 = BitVec.ofNat 64 j := (k₂.gpr (by decide)).trans t₁14
  have t₂12 : t₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans t12)
  refine WP.mono (count_ok t₂ t₂14 t₂12 (by omega_arith) (by omega_arith)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  -- The words read, as on entry.
  have hx : t₁.mem.readW (off B (ex + 8 * (j - 1))) 64 = word s₀.mem B (ex + 8 * (j - 1)) := by
    rw [hm₁]; exact hI.out.word (by omega_arith) (by omega_arith)
  have hy : t.mem.readW (off B (em + 8 * j)) 64 = word s₀.mem B (em + 8 * j) :=
    hI.out.word (by omega_arith) (by omega_arith)
  have hmem : t'.mem = t.mem.writeW (off B (et + 8 * j)) v := by rw [hm', hm₂, hm₁]
  have h9 : t'.gpr .r9 = t₁.gpr .r9 := (k'.gpr (by decide)).trans (k₂.gpr (by decide))
  rw [hx] at hv₂
  rw [hy, tcx] at hv₁
  refine ⟨hI.scr.congr (k'.2.2.trans (k₂.2.2.trans k₁.2.2)),
    ((hI.keep.trans k₁).trans (k₂.trans k')).mono (by decide), h14, ?_, ⟨b', (k'.gpr (by decide)).trans hbp₂, ?_⟩⟩
  · rw [hmem]
    intro x hx'
    rw [writeW_outside t.mem B v (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [hmem, wv_writeW_top _ _ _ _ _ (by omega_arith), h9]
    rw [show j + 1 - 1 = (j - 1) + 1 by omega_arith]
    simp only [wv]
    have e1 : 2 ^ (64 * j) = 2 ^ (64 * (j - 1)) * 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega_arith
    have e2 : 2 ^ (64 * (j + 1)) = 2 ^ (64 * (j - 1)) * 2 ^ 64 * 2 ^ 64 := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_arith
    rw [e1] at hval ⊢
    rw [e2]
    grind

/-- Word 0: `0 - lo(q̂ m₀)` stored, its borrow into `rbp` and `hi(q̂ m₀)` into
`r9`. -/
theorem subHead_ok (s : State) {aM aD : Addr}
    (eM : s.gpr .r10 + BitVec.ofInt 64 0 = aM) (eD : s.gpr .r8 + BitVec.ofInt 64 0 = aD)
    (hMr : InRegions (s.rd ++ s.wr) aM 8) (hD : InRegions s.wr aD 8) :
    WP isa (.block subHead) s fun t =>
      ∃ (v : BitVec 64) (b : Bool), t.mem = s.mem.writeW aD v ∧ t.gpr .rbp = mask b ∧
        v.toNat + (s.gpr .rcx).toNat * (s.mem.readW aM 64).toNat = 2 ^ 64 * ((t.gpr .r9).toNat + b.toNat) ∧
      Keep [.rax, .rdx, .rbp, .r9] s t := by
  refine WP.mono (WP.keep [.rax, .rdx, .rbp, .r9] (Q := fun t =>
      ∃ (v : BitVec 64) (b : Bool), t.mem = s.mem.writeW aD v ∧ t.gpr .rbp = mask b ∧
        v.toNat + (s.gpr .rcx).toNat * (s.mem.readW aM 64).toNat = 2 ^ 64 * ((t.gpr .r9).toNat + b.toNat)) ?_ rfl)
    fun t ⟨h, k⟩ => let ⟨v, b, h1, h2, h3⟩ := h; ⟨v, b, h1, h2, h3, k⟩
  unfold subHead cfToRbp
  xrun [State.ea, at0, eM, eD, hMr, hD]
  refine ⟨_, _, rfl, rfl, ?_⟩
  have hm := mul_toNat (s.mem.readW aM 64) (s.gpr .rcx)
  have hsb := sbb_toNat (0#64 : BitVec 64) (BitVec.ofNat 64 ((s.mem.readW aM 64).toNat * (s.gpr .rcx).toNat)) false
  simp only [Bool.toNat_false, Nat.add_zero, show (0#64 : BitVec 64).toNat = 0 from rfl,
    show (BitVec.ofBool false).setWidth 64 = (0#64 : BitVec 64) from rfl, BitVec.sub_zero] at hsb
  rw [show BitVec.setWidth 64 (0 : BitVec 32) = 0#64 from rfl, show (0#64 : BitVec 64).toNat = 0 from rfl,
    Nat.mul_comm (s.gpr .rcx).toNat]
  omega_arith

/-- Word `w`: `v + r9 + c = x[w - 1] + 2^64 c'` stored. -/
theorem subTop_ok (s : State) {aX aD : Addr} {c : Bool}
    (eX : s.gpr .rbx + s.gpr .r12 * BitVec.ofNat 64 8 + BitVec.ofInt 64 (-8) = aX)
    (eD : s.gpr .r8 + s.gpr .r12 * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = aD)
    (hX : InRegions (s.rd ++ s.wr) aX 8) (hD : InRegions s.wr aD 8) (hbp : s.gpr .rbp = mask c) :
    WP isa (.block subTop) s fun t =>
      ∃ (v : BitVec 64) (c' : Bool), t.mem = s.mem.writeW aD v ∧
        v.toNat + (s.gpr .r9).toNat + c.toNat = (s.mem.readW aX 64).toNat + 2 ^ 64 * c'.toNat ∧
      Keep [.rdx, .rbp] s t := by
  refine WP.mono (WP.keep [.rdx, .rbp] (Q := fun t =>
      ∃ (v : BitVec 64) (c' : Bool), t.mem = s.mem.writeW aD v ∧
        v.toNat + (s.gpr .r9).toNat + c.toNat = (s.mem.readW aX 64).toNat + 2 ^ 64 * c'.toNat) ?_ rfl)
    fun t ⟨h, k⟩ => let ⟨v, c', h1, h2⟩ := h; ⟨v, c', h1, h2, k⟩
  unfold subTop cfFromRbp
  xrun [State.ea, ix, eX, eD, hX, hD, hbp, cf_mask]
  exact ⟨_, _, rfl, sbb_toNat _ _ _⟩

/-- `t = x 2^64 - q̂ m` over `w + 1` words at `r8`, for `x` at `rbx` and `m` at
`r10` of `w` words and `q̂` in `rcx`: `t + q̂ m = x 2^64 + 2^(64 (w + 1)) b`. -/
theorem mulSub_ok {s : State} {B : Addr} {Z w ex em et : Nat} (hs : Scr s B Z)
    (hbx : s.gpr .rbx = off B ex) (h10 : s.gpr .r10 = off B em) (h8 : s.gpr .r8 = off B et)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hX : ex + 8 * w ≤ Z)
    (hM : em + 8 * w ≤ Z) (hT : et + 8 * (w + 1) ≤ Z)
    (sX : et + 8 * (w + 1) ≤ ex ∨ ex + 8 * w ≤ et) (sM : et + 8 * (w + 1) ≤ em ∨ em + 8 * w ≤ et) :
    WP isa mulSub s fun t => ∃ b : Bool,
      wv t.mem B et (w + 1) + (s.gpr .rcx).toNat * wv s.mem B em w =
        wv s.mem B ex w * 2 ^ 64 + 2 ^ (64 * (w + 1)) * b.toNat ∧
      Outside B et (8 * (w + 1)) s.mem t.mem ∧ Keep [.rax, .rdx, .rbp, .r9, .r14] s t := by
  have hn := hs.nowrap
  unfold mulSub
  refine WP.seq (WP.mono (subHead_ok s (by rw [h10]; simp [off]) (by rw [h8]; simp [off])
    (hs.ld (d := em) (by omega_arith)) (hs.st (d := et) (by omega_arith))) fun t₁ ⟨v, b, hm₁, hbp₁, hv₁, k₁⟩ => ?_)
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 1 → t.mem = t₁.mem → Keep [.r14] t₁ t → t.cf = t₁.cf →
      MsInv s B Z ex em et (s.gpr .rcx).toNat 1 t := fun t h14 hm k _ => by
    refine ⟨hs.congr (k.2.2.trans k₁.2.2), (k₁.trans k).mono (by decide), h14, ?_, ⟨b, ?_, ?_⟩⟩
    · rw [hm, hm₁]
      intro x hx
      rw [writeW_outside s.mem B v (by omega_arith) x (by omega_arith)]
    · rw [k.gpr (by decide), hbp₁]
    · rw [hm, hm₁, k.gpr (by decide)]
      simp only [wv, Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.add_zero, Nat.pow_zero,
        word_writeW_self, Nat.one_mul, Nat.sub_self, Nat.zero_mul]
      exact hv₁
  refine WP.seq (WP.mono (wordLoop_ok (start := 1) (N := w) (by omega_arith) hw' (MsInv s B Z ex em et (s.gpr .rcx).toNat)
    h0 (fun j hj1 hj t hI => msStep_ok hbx h10 h8 h12 hw' hX hM hT sX sM hj1 hj hI)) fun t₂ hI => ?_)
  obtain ⟨c, hbp₂, hval⟩ := hI.val
  have t₂bx : t₂.gpr .rbx = off B ex := (hI.keep.gpr (by decide)).trans hbx
  have t₂8 : t₂.gpr .r8 = off B et := (hI.keep.gpr (by decide)).trans h8
  have t₂12 : t₂.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  refine WP.mono (subTop_ok t₂ (addrm8 t₂bx t₂12 (by omega_arith)) (addr0 t₂8 t₂12) (hI.scr.ld (by omega_arith))
    (hI.scr.st (by omega_arith)) hbp₂) fun t ⟨v', c', hm, hv, k⟩ => ⟨c', ?_, ?_, (hI.keep.trans k).mono (by decide)⟩
  · have hx : t₂.mem.readW (off B (ex + 8 * (w - 1))) 64 = word s.mem B (ex + 8 * (w - 1)) :=
      hI.out.word (by omega_arith) (by omega_arith)
    rw [hx] at hv
    rw [hm, show w + 1 = w + 1 from rfl, wv_writeW_top _ _ _ _ _ (by omega_arith)]
    have ew : wv s.mem B ex w = wv s.mem B ex (w - 1) + 2 ^ (64 * (w - 1)) * (word s.mem B (ex + 8 * (w - 1))).toNat := by
      conv => lhs; rw [show w = (w - 1) + 1 by omega_arith]
      simp only [wv]
    have e1 : 2 ^ (64 * w) = 2 ^ (64 * (w - 1)) * 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega_arith
    have e2 : 2 ^ (64 * (w + 1)) = 2 ^ (64 * (w - 1)) * 2 ^ 64 * 2 ^ 64 := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_arith
    rw [ew, e2]
    rw [e1] at hval ⊢
    grind
  · rw [hm]
    intro x hx
    rw [writeW_outside t₂.mem B v' (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)

end VG.Proof.Bignum.X86_64.R2w
