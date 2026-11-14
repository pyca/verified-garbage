module

public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverDet
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.R2wSub
import VerifiedGarbage.Proof.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.RecoverDetWords
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the square root's loops, apart from its stages

/-!
# `vg_rsa_recover_primes_det` on x86-64: the square root's loops

`R - q̂ D` in place over a window of words (`msub_ok`), and the first
digit's 64 steps on registers (`isq_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Bignum.X86_64.R2w

/-! ## `R - q̂ D` in place -/

/-- `mov rdx, [rbx + 8 r14]; add rbp, rbp; sbb rdx, rax; sbb rbp, rbp;
mov [rbx + 8 r14], rdx`: `v + rax + c = x[i] + 2^64 c'` stored in place. -/
theorem sbbIn_ok (s : State) {aX : Addr} {c : Bool}
    (eX : s.gpr .rbx + s.gpr .r14 * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = aX)
    (hX : InRegions s.wr aX 8) (hXr : InRegions (s.rd ++ s.wr) aX 8) (hbp : s.gpr .rbp = mask c) :
    WP isa (.block [.mov .rdx (.mem (ix .rbx .r14)), cfFromRbp, .alu .sbb .rdx (.reg .rax), cfToRbp,
        .store (ix .rbx .r14) .rdx]) s fun t =>
      ∃ (v : BitVec 64) (c' : Bool), t.mem = s.mem.writeW aX v ∧ t.gpr .rbp = mask c' ∧
        v.toNat + (s.gpr .rax).toNat + c.toNat = (s.mem.readW aX 64).toNat + 2 ^ 64 * c'.toNat ∧
      Keep [.rdx, .rbp] s t := by
  refine WP.mono (WP.keep [.rdx, .rbp] (Q := fun t =>
      ∃ (v : BitVec 64) (c' : Bool), t.mem = s.mem.writeW aX v ∧ t.gpr .rbp = mask c' ∧
        v.toNat + (s.gpr .rax).toNat + c.toNat = (s.mem.readW aX 64).toNat + 2 ^ 64 * c'.toNat) ?_ rfl)
    fun t ⟨h, k⟩ => let ⟨v, c', h1, h2, h3⟩ := h; ⟨v, c', h1, h2, h3, k⟩
  unfold cfFromRbp cfToRbp
  xrun [State.ea, ix, eX, hX, hXr, hbp, cf_mask]
  exact ⟨_, _, rfl, rfl, sbb_toNat _ _ _⟩

/-- After words `0, …, j - 1` of `R - q D` in place from `s₀`: the words
`T_j`, the carry `r9` and the borrow `b`, `T_j + q D_j = R_j + 2^(64 j) (r9 + b)`. -/
structure MsIInv (s₀ : State) (B : Addr) (Z e eD q : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .rbp, .r9, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B e (8 * j) s₀.mem t.mem
  val : ∃ b : Bool, t.gpr .rbp = mask b ∧
    wv t.mem B e j + q * wv s₀.mem B eD j = wv s₀.mem B e j + 2 ^ (64 * j) * ((t.gpr .r9).toNat + b.toNat)

theorem msIStep_ok {s₀ : State} {B : Addr} {Z w e eD : Nat}
    (hbx : s₀.gpr .rbx = off B e) (h10 : s₀.gpr .r10 = off B eD)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 31) (hX : e + 8 * w ≤ Z) (hM : eD + 8 * w ≤ Z)
    (sM : e + 8 * w ≤ eD ∨ eD + 8 * w ≤ e)
    {j : Nat} (hj : j < w) {t : State} (hI : MsIInv s₀ B Z e eD (s₀.gpr .rcx).toNat j t) :
    WP isa (.block (msBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t fun t' =>
      t'.zf = some (decide (j + 1 = w)) ∧ MsIInv s₀ B Z e eD (s₀.gpr .rcx).toNat (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B e := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = off B eD := (hI.keep.gpr (by decide)).trans h10
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have tcx : t.gpr .rcx = s₀.gpr .rcx := hI.keep.gpr (by decide)
  obtain ⟨b, hbp, hval⟩ := hI.val
  rw [show msBody = [.mov .rax (.mem (ix .r10 .r14)), .mul .rcx, .alu .add .rax (.reg .r9),
      .alu .adc .rdx (.imm 0), .mov .r9 (.reg .rdx)] ++ [.mov .rdx (.mem (ix .rbx .r14)), cfFromRbp,
      .alu .sbb .rdx (.reg .rax), cfToRbp, .store (ix .rbx .r14) .rdx] from rfl, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (mulc_ok t (addr0 t10 hI.r14) (hI.scr.ld (by omega_arith))) fun t₁ ⟨hv₁, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁bx : t₁.gpr .rbx = off B e := (k₁.gpr (by decide)).trans tbx
  have t₁bp : t₁.gpr .rbp = mask b := (k₁.gpr (by decide)).trans hbp
  have hs₁ := hI.scr.congr k₁.2.2
  refine WP.mono (sbbIn_ok t₁ (addr0 t₁bx t₁14) (hs₁.st (by omega_arith)) (hs₁.ld (by omega_arith)) t₁bp)
    fun t₂ ⟨v, b', hm₂, hbp₂, hv₂, k₂⟩ => ?_
  have t₂14 : t₂.gpr .r14 = BitVec.ofNat 64 j := (k₂.gpr (by decide)).trans t₁14
  have t₂12 : t₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans t12)
  refine WP.mono (count_ok t₂ t₂14 t₂12 (by omega_arith) (by omega_arith)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  -- The words read, as on entry.
  have hx : t₁.mem.readW (off B (e + 8 * j)) 64 = word s₀.mem B (e + 8 * j) := by
    rw [hm₁]; exact hI.out.word (by omega_arith) (by omega_arith)
  have hy : t.mem.readW (off B (eD + 8 * j)) 64 = word s₀.mem B (eD + 8 * j) :=
    hI.out.word (by omega_arith) (by omega_arith)
  have hmem : t'.mem = t.mem.writeW (off B (e + 8 * j)) v := by rw [hm', hm₂, hm₁]
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
    simp only [wv]
    have e1 : 2 ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64 := by rw [← Nat.pow_add, Nat.mul_succ]
    rw [e1]
    grind

/-- `wordLoop 0 msBody` over `N` words: `[rbx] := [rbx] - rcx [r10]` in place,
`r9 = 0` and no borrow on entry: `T + q D = R + 2^(64 N) k`. -/
theorem msub_ok {s : State} {B : Addr} {Z N e eD : Nat} (hs : Scr s B Z)
    (hbx : s.gpr .rbx = off B e) (h10 : s.gpr .r10 = off B eD) (h12 : s.gpr .r12 = BitVec.ofNat 64 N)
    (h9 : s.gpr .r9 = 0) (hbp : s.gpr .rbp = mask false) (hN : 1 ≤ N) (hN' : N < 2 ^ 31)
    (hX : e + 8 * N ≤ Z) (hM : eD + 8 * N ≤ Z) (sM : e + 8 * N ≤ eD ∨ eD + 8 * N ≤ e) :
    WP isa (wordLoop 0 msBody) s fun t => ∃ k,
      wv t.mem B e N + (s.gpr .rcx).toNat * wv s.mem B eD N = wv s.mem B e N + 2 ^ (64 * N) * k ∧
      Outside B e (8 * N) s.mem t.mem ∧ Keep [.rax, .rdx, .rbp, .r9, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      MsIInv s B Z e eD (s.gpr .rcx).toNat 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by
        rw [k.gpr (by decide), h9]; simp [wv]⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega_arith) hN' (MsIInv s B Z e eD (s.gpr .rcx).toNat) h0
    (fun j _ hj t hI => msIStep_ok hbx h10 h12 hN' hX hM sM hj hI)) fun t hI => ?_
  obtain ⟨b, _, hv⟩ := hI.val
  exact ⟨_, hv, hI.out, hI.keep⟩

/-! ## The first digit -/

/-- Disjoint bits: `or` adds. -/
theorem or_disj (a b : BitVec 64) {k : Nat} (ha : a.toNat % 2 ^ k = 0) (hb : b.toNat < 2 ^ k) :
    (a ||| b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_or]
  have : a.toNat = 2 ^ k * (a.toNat / 2 ^ k) := by
    have := Nat.div_add_mod a.toNat (2 ^ k); omega_using [ha, this]
  rw [this, ← Nat.two_pow_add_eq_or_of_lt hb]

/-- `shld d, r, n`: `d 2ⁿ mod 2⁶⁴` and `r`'s top `n` bits. -/
theorem shld_ok (s : State) (d r : Reg) {n : Nat} (hn : 1 ≤ n ∧ n ≤ 63) :
    WP isa (.block [.shld d r n]) s fun s' =>
      (s'.gpr d).toNat = (s.gpr d).toNat * 2 ^ n % 2 ^ 64 + (s.gpr r).toNat / 2 ^ (64 - n) ∧
        s'.mem = s.mem ∧ Keep [d] s s' := by
  refine WP.mono (WP.keep [d] (Q := fun s' => s'.gpr d =
      ((s.gpr d) <<< n) ||| (s.gpr r >>> (64 - n)) ∧ s'.mem = s.mem) (by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShld, hn, and_self, ite_true,
      RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, rfl⟩) (by cases d <;> rfl)) fun s' ⟨⟨e, m⟩, k⟩ => ⟨?_, m, k⟩
  rw [e]
  have h1 : ((s.gpr d) <<< n).toNat % 2 ^ n = 0 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega_using [hn]))]
    exact Nat.mul_mod_left _ _
  have h2 : ((s.gpr r) >>> (64 - n)).toNat < 2 ^ n := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := (s.gpr r).isLt
    exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add, show 64 - n + n = 64 by omega_using [hn]]; exact this)
  rw [or_disj _ _ h1 h2, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

/-- `cmovae d, r`: `d := r` iff CF is clear. -/
theorem cmovae_ok {t : State} {d r : Reg} {c : Bool} (hc : t.cf = some c) :
    WP isa (.block [.cmov .ae d (.reg r)]) t fun t' =>
      t'.gpr d = (if c then t.gpr d else t.gpr r) ∧ t'.cf = t.cf ∧ t'.mem = t.mem ∧ Keep [d] t t' := by
  refine WP.mono (WP.keep [d] (Q := fun t' => t'.gpr d = (if c then t.gpr d else t.gpr r) ∧ t'.cf = t.cf ∧
    t'.mem = t.mem) ?_ (by cases d <;> rfl)) fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  apply WP.of_runBlock
  cases c <;> simp [runBlock_cons, runStep_some, runBlock_nil, exec, execCmov, readSrc, eval, hc,
    setReg_gpr, setReg_mem]

/-- The pair's shift: `(r11, r13)` and `(r8, r9)` by two bits, `r13`'s top two
into `r11`, `r8`'s into `r13`, `r9`'s into `r8`. -/
theorem isqA_ok (t : State) :
    WP isa (.block [.shld .r11 .r13 2, .shld .r13 .r8 2, .shld .r8 .r9 2, .shift .shl .r9 2]) t fun t' =>
      (t'.gpr .r11).toNat = (t.gpr .r11).toNat * 4 % 2 ^ 64 + (t.gpr .r13).toNat / 2 ^ 62 ∧
      (t'.gpr .r13).toNat = (t.gpr .r13).toNat * 4 % 2 ^ 64 + (t.gpr .r8).toNat / 2 ^ 62 ∧
      (t'.gpr .r8).toNat = (t.gpr .r8).toNat * 4 % 2 ^ 64 + (t.gpr .r9).toNat / 2 ^ 62 ∧
      (t'.gpr .r9).toNat = (t.gpr .r9).toNat * 4 % 2 ^ 64 ∧ t'.mem = t.mem ∧ Keep [.r11, .r13, .r8, .r9] t t' := by
  rw [show ([.shld .r11 .r13 2, .shld .r13 .r8 2, .shld .r8 .r9 2, .shift .shl .r9 2] : List Instr) =
    [.shld .r11 .r13 2] ++ ([.shld .r13 .r8 2] ++ ([.shld .r8 .r9 2] ++ [.shift .shl .r9 2])) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (shld_ok t .r11 .r13 (n := 2) (by decide)) fun t₁ ⟨v1, m1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (shld_ok t₁ .r13 .r8 (n := 2) (by decide)) fun t₂ ⟨v2, m2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (shld_ok t₂ .r8 .r9 (n := 2) (by decide)) fun t₃ ⟨v3, m3, k3⟩ => ?_
  refine WP.mono (WP.keep [.r9] (Q := fun t' => t'.gpr .r9 = t₃.gpr .r9 <<< 2 ∧ t'.mem = t₃.mem) (by xrun) rfl)
    fun t' ⟨⟨v4, m4⟩, k4⟩ => ?_
  have g1 : t₁.gpr .r13 = t.gpr .r13 := k1.gpr (by decide)
  have g1' : t₁.gpr .r8 = t.gpr .r8 := k1.gpr (by decide)
  have g2 : t₂.gpr .r8 = t.gpr .r8 := (k2.gpr (by decide)).trans g1'
  have g9 : t₃.gpr .r9 = t.gpr .r9 := (k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans (k1.gpr (by decide)))
  refine ⟨?_, ?_, ?_, ?_, by rw [m4, m3, m2, m1], ((k1.trans k2).trans (k3.trans k4)).mono (by decide)⟩
  · rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), v1]
  · rw [k4.gpr (by decide), k3.gpr (by decide), v2, g1, g1']
  · rw [k4.gpr (by decide), v3, g2, (k2.gpr (by decide) : t₂.gpr .r9 = _), (k1.gpr (by decide) : t₁.gpr .r9 = _)]
  · rw [v4, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, g9]

/-- `4 s + 1`: `r14 := s / 2^62`, `r15 := 4 s mod 2^64 + 1`. -/
theorem isqB_ok (t : State) :
    WP isa (.block [.mov .r14 (.reg .r10), .shift .shr .r14 62, .mov .r15 (.reg .r10), .shift .shl .r15 2,
        .alu .or .r15 (.imm 1)]) t fun t' =>
      (t'.gpr .r14).toNat = (t.gpr .r10).toNat / 2 ^ 62 ∧
      (t'.gpr .r15).toNat = (t.gpr .r10).toNat * 4 % 2 ^ 64 + 1 ∧ t'.mem = t.mem ∧ Keep [.r14, .r15] t t' := by
  refine WP.mono (WP.keep [.r14, .r15] (Q := fun t' => t'.gpr .r14 = t.gpr .r10 >>> 62 ∧
      t'.gpr .r15 = (t.gpr .r10 <<< 2) ||| 1#64 ∧ t'.mem = t.mem) (by xrun; rfl) rfl) fun t' ⟨⟨a, b, m⟩, k⟩ => ?_
  refine ⟨by rw [a, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow], ?_, m, k⟩
  have h1 : ((t.gpr .r10) <<< 2).toNat % 2 ^ 1 = 0 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have : (t.gpr .r10).toNat * 2 ^ 2 % 2 ^ 64 % 2 = 0 := by
      rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 64)]; omega_using []
    exact this
  rw [b, or_disj _ _ h1 (by decide), BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rfl

/-- The comparison: `(rdx, rax) := (r11, r13) - (r14, r15)` and CF the borrow,
`r11 2^64 + r13 < r14 2^64 + r15`. -/
theorem isqC_ok {t : State} {x1 x0 y1 y0 : Nat} (h11 : t.gpr .r11 = BitVec.ofNat 64 x1)
    (h13 : t.gpr .r13 = BitVec.ofNat 64 x0) (h14 : t.gpr .r14 = BitVec.ofNat 64 y1)
    (h15 : t.gpr .r15 = BitVec.ofNat 64 y0) (hx1 : x1 < 2 ^ 64) (hx0 : x0 < 2 ^ 64) (hy1 : y1 < 2 ^ 64)
    (hy0 : y0 < 2 ^ 64) :
    WP isa (.block [.mov .rax (.reg .r13), .alu .sub .rax (.reg .r15), .mov .rdx (.reg .r11),
        .alu .sbb .rdx (.reg .r14)]) t fun t' =>
      t'.cf = some (decide (x1 * 2 ^ 64 + x0 < y1 * 2 ^ 64 + y0)) ∧
      (decide (x1 * 2 ^ 64 + x0 < y1 * 2 ^ 64 + y0) = false →
        (t'.gpr .rdx).toNat * 2 ^ 64 + (t'.gpr .rax).toNat = x1 * 2 ^ 64 + x0 - (y1 * 2 ^ 64 + y0)) ∧
      t'.mem = t.mem ∧ Keep [.rax, .rdx] t t' := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t' =>
      t'.gpr .rax = BitVec.ofNat 64 x0 - BitVec.ofNat 64 y0 ∧
      t'.gpr .rdx = BitVec.ofNat 64 x1 - BitVec.ofNat 64 y1 -
        (BitVec.ofBool (decide (x0 < y0))).setWidth 64 ∧
      t'.cf = some (decide (x1 < y1 + (decide (x0 < y0)).toNat)) ∧ t'.mem = t.mem) (by
    xrun [h11, h13, h14, h15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx1, Nat.mod_eq_of_lt hx0,
      Nat.mod_eq_of_lt hy1, Nat.mod_eq_of_lt hy0]) rfl) fun t' ⟨⟨a, b, c, m⟩, k⟩ => ?_
  have hcmp : decide (x1 < y1 + (decide (x0 < y0)).toNat) = decide (x1 * 2 ^ 64 + x0 < y1 * 2 ^ 64 + y0) := by
    by_cases h : x0 < y0 <;> simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
      (apply decide_eq_decide.mpr; omega_arith)
  refine ⟨by rw [c, hcmp], fun hn => ?_, m, k⟩
  rw [← hcmp] at hn
  have s1 := sbb_toNat (BitVec.ofNat 64 x1) (BitVec.ofNat 64 y1) (decide (x0 < y0))
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx1, Nat.mod_eq_of_lt hy1, hn] at s1
  have s0 := sbb_toNat (BitVec.ofNat 64 x0) (BitVec.ofNat 64 y0) false
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx0, Nat.mod_eq_of_lt hy0] at s0
  simp only [Bool.toNat_false, Nat.add_zero, show (BitVec.ofBool false).setWidth 64 = (0#64 : BitVec 64) from rfl,
    BitVec.sub_zero] at s0
  rw [a, b]
  simp only [decide_eq_false_iff_not, Nat.not_lt] at hn
  by_cases h : x0 < y0 <;> simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] at s0 s1 hn ⊢ <;>
    omega_using [s0, s1]

/-- `sbb rbx, rbx`: the carry as a mask. -/
theorem sbbBx_ok {t : State} {c : Bool} (hcf : t.cf = some c) :
    WP isa (.block [.alu .sbb .rbx (.reg .rbx)]) t fun t' =>
      t'.gpr .rbx = mask c ∧ t'.mem = t.mem ∧ Keep [.rbx] t t' := by
  refine WP.mono (WP.keep [.rbx] (Q := fun t' => t'.gpr .rbx = mask c ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  xrun [hcf]
  rfl

theorem ofNat_beq_zero' {j : Nat} (hj : j < 2 ^ 64) : (BitVec.ofNat 64 j == 0) = decide (j = 0) := by
  by_cases h : j = 0
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj] at this

/-- `s := 2 s + 1 - c` for the mask of `c` in `rbx`, and the count down. -/
theorem isqE_ok {t : State} {s n : Nat} {c : Bool} (h10 : t.gpr .r10 = BitVec.ofNat 64 s)
    (hbx : t.gpr .rbx = mask c) (hcx : t.gpr .rcx = BitVec.ofNat 64 n) (hs : 2 * s + 1 < 2 ^ 64) (hn : 1 ≤ n)
    (hn' : n < 2 ^ 64) :
    WP isa (.block [.alu .add .r10 (.reg .r10), .alu .add .r10 (.imm 1), .alu .add .r10 (.reg .rbx),
        .alu .sub .rcx (.imm 1)]) t fun t' =>
      t'.gpr .r10 = BitVec.ofNat 64 (2 * s + 1 - c.toNat) ∧ t'.gpr .rcx = BitVec.ofNat 64 (n - 1) ∧
      t'.zf = some (decide (n - 1 = 0)) ∧ t'.mem = t.mem ∧ Keep [.r10, .rcx] t t' := by
  refine WP.mono (WP.keep [.r10, .rcx] (Q := fun t' => t'.gpr .r10 = BitVec.ofNat 64 (2 * s + 1 - c.toNat) ∧
      t'.gpr .rcx = BitVec.ofNat 64 (n - 1) ∧ t'.zf = some (decide (n - 1 = 0)) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  xrun [h10, hbx, hcx]
  refine ⟨?_, ofNat64_pred hn hn', ?_⟩
  · apply BitVec.eq_of_toNat_eq
    have hs64 : s < 2 ^ 64 := by omega_using [hs]
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hs64, show (1 : BitVec 64).toNat = 1 from rfl]
    cases c
    · rw [mask_false, show (0 : BitVec 64).toNat = 0 from rfl]
      simp only [Bool.toNat_false, Nat.sub_zero]
      omega_using []
    · rw [mask_true, BitVec.toNat_allOnes]
      simp only [Bool.toNat_true]
      omega_using []
  · rw [ofNat64_pred hn hn']
    exact ofNat_beq_zero' (by omega_using [hn'])

/-- After `i` steps of the first digit from `T = r8 2^64 + r9` (`< 2^128`): the
root `s` of `T`'s top `2 i` bits in `r10`, its remainder in `(r11, r13)`, the
pair shifted left by `2 i` bits, and the count `64 - i` in `rcx`. -/
def IsqInv (t₀ : State) (T i : Nat) (t : State) : Prop :=
  t.gpr .r10 = BitVec.ofNat 64 (VG.Spec.Rsa.isqrt (T / 4 ^ (64 - i))) ∧
  t.gpr .r11 = BitVec.ofNat 64 ((T / 4 ^ (64 - i) - VG.Spec.Rsa.isqrt (T / 4 ^ (64 - i)) *
    VG.Spec.Rsa.isqrt (T / 4 ^ (64 - i))) / 2 ^ 64) ∧
  t.gpr .r13 = BitVec.ofNat 64 ((T / 4 ^ (64 - i) - VG.Spec.Rsa.isqrt (T / 4 ^ (64 - i)) *
    VG.Spec.Rsa.isqrt (T / 4 ^ (64 - i))) % 2 ^ 64) ∧
  t.gpr .r8 = BitVec.ofNat 64 (T * 4 ^ i % 2 ^ 128 / 2 ^ 64) ∧ t.gpr .r9 = BitVec.ofNat 64 (T * 4 ^ i % 2 ^ 64) ∧
  t.gpr .rcx = BitVec.ofNat 64 (64 - i) ∧ t.mem = t₀.mem ∧
  Keep [.r8, .r9, .r10, .r11, .r13, .r14, .r15, .rax, .rdx, .rbx, .rcx] t₀ t

theorem pow4 (k : Nat) : 4 ^ k = 2 ^ (2 * k) := by rw [Nat.pow_mul]

/-- Pair `63 - i` of `T < 2^128` from `T 4^i`'s top word: its top two bits. -/
theorem pair_top {T i : Nat} (hi : i < 64) :
    T * 4 ^ i % 2 ^ 128 / 2 ^ 64 / 2 ^ 62 = T / 4 ^ (63 - i) % 4 := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add,
    show (2 : Nat) ^ 128 = 2 ^ (64 + 62) * 4 by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add],
    Nat.mod_mul_right_div_self, pow4, pow4]
  congr 1
  have e : 2 ^ (64 + 62) = 2 ^ (2 * i) * 2 ^ (2 * (63 - i)) := by rw [← Nat.pow_add]; congr 1; omega_using [hi]
  rw [e, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- `T 4^(i + 1)`'s words from `T 4^i`'s. -/
theorem pair_shift {T i : Nat} :
    T * 4 ^ (i + 1) % 2 ^ 128 / 2 ^ 64 =
      T * 4 ^ i % 2 ^ 128 / 2 ^ 64 * 4 % 2 ^ 64 + T * 4 ^ i % 2 ^ 64 / 2 ^ 62 ∧
    T * 4 ^ (i + 1) % 2 ^ 64 = T * 4 ^ i % 2 ^ 64 * 4 % 2 ^ 64 := by
  generalize hP : T * 4 ^ i = P
  have e : T * 4 ^ (i + 1) = P * 4 := by rw [Nat.pow_succ, ← Nat.mul_assoc, hP]
  rw [e]
  constructor
  · -- `(4 P mod 2^128) / 2^64 = 4 (P mod 2^128 / 2^64) mod 2^64 + (P mod 2^64) / 2^62`.
    have h1 : P % 2 ^ 128 = P % 2 ^ 128 / 2 ^ 64 * 2 ^ 64 + P % 2 ^ 64 := by
      have := Nat.div_add_mod (P % 2 ^ 128) (2 ^ 64)
      rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 64 ∣ 2 ^ 128)] at this; omega_using []
    have h2 : P * 4 % 2 ^ 128 = P % 2 ^ 128 * 4 % 2 ^ 128 := by
      rw [Nat.mul_mod, Nat.mod_eq_of_lt (show (4 : Nat) < 2 ^ 128 by decide)]
    rw [h2]
    generalize P % 2 ^ 128 / 2 ^ 64 = a1 at h1
    generalize hb : P % 2 ^ 64 = a0 at h1
    have ha0 : a0 < 2 ^ 64 := by rw [← hb]; exact Nat.mod_lt _ (by decide)
    have ha1 : a1 < 2 ^ 64 := by
      have := Nat.mod_lt P (show 0 < 2 ^ 128 by decide); omega_using [h1]
    rw [h1]
    omega_using [hb]
  · rw [Nat.mul_mod, Nat.mod_eq_of_lt (show (4 : Nat) < 2 ^ 64 by decide)]

theorem of_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem mul4_mod (a : Nat) : a * 4 % 2 ^ 64 = a % 2 ^ 62 * 4 := by
  rw [show (2 : Nat) ^ 64 = 2 ^ 62 * 4 by decide, Nat.mul_mod_mul_right]

theorem split4 (a c : Nat) : a / 2 ^ 62 * 2 ^ 64 + (a % 2 ^ 62 * 4 + c) = 4 * a + c := by
  have := Nat.div_add_mod a (2 ^ 62)
  generalize a / 2 ^ 62 = u at this ⊢
  generalize a % 2 ^ 62 = v at this ⊢
  rw [show (2 : Nat) ^ 64 = 2 ^ 62 * 4 by decide]
  generalize (2 : Nat) ^ 62 = P at this ⊢
  subst this
  grind

/-- A two-word value from its words. -/
theorem words_eq {x hi lo : Nat} (h : hi * 2 ^ 64 + lo = x) (hlo : lo < 2 ^ 64) : hi = x / 2 ^ 64 ∧ lo = x % 2 ^ 64 := by
  subst h
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos 64), Nat.div_eq_of_lt hlo, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hlo]

/-- A step of the first digit. -/
theorem isqStep_ok {t₀ : State} {T i : Nat} (hT : T < 2 ^ 128) (hi : i < 64) {t : State}
    (hI : IsqInv t₀ T i t) :
    WP isa (.block isqBody) t fun t' => t'.zf = some (decide (i + 1 = 64)) ∧ IsqInv t₀ T (i + 1) t' := by
  obtain ⟨h10, h11, h13, h8, h9, hcx, hm, k⟩ := hI
  -- The root and remainder so far.
  have hN : T / 4 ^ (64 - i) < 4 ^ i := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (show 0 < 4 by decide)), ← Nat.pow_add,
      show i + (64 - i) = 64 by omega_using [hi]]
    exact Nat.lt_of_lt_of_le hT (by decide)
  generalize hNd : T / 4 ^ (64 - i) = N at hN h10 h11 h13
  obtain ⟨lo, hi'⟩ := VG.Proof.Rsa.RecoverDet.isqrt_spec N
  generalize hs : VG.Spec.Rsa.isqrt N = s at lo hi' h10 h11 h13
  have hsi : s < 2 ^ i := by
    refine Nat.lt_of_not_le fun c => ?_
    have := Nat.mul_le_mul c c
    rw [← Nat.pow_add, show i + i = 2 * i by omega_using [], ← pow4] at this
    omega_using [hT, hi, h8, h9, hcx, hNd, hN, hs, lo, hi', h10, h11, h13, c, this]
  have hs63 : s < 2 ^ 63 := Nat.lt_of_lt_of_le hsi (Nat.pow_le_pow_right (by decide) (by omega_using [hi]))
  have e1 : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by grind
  generalize hr : N - s * s = r at h11 h13
  have hr2 : r ≤ 2 * s := by omega_using [hi', e1, hr]
  have hr64 : r < 2 ^ 64 := by omega_using [hi', hs63, e1, hr]
  rw [Nat.div_eq_of_lt hr64] at h11
  rw [Nat.mod_eq_of_lt hr64] at h13
  -- The pair.
  have hP1 : T * 4 ^ i % 2 ^ 128 / 2 ^ 64 < 2 ^ 64 :=
    Nat.div_lt_of_lt_mul (by have := Nat.mod_lt (T * 4 ^ i) (show 0 < 2 ^ 128 by decide); omega_using [])
  have hδ := pair_top (T := T) hi
  generalize hδd : T / 4 ^ (63 - i) % 4 = δ at hδ
  have hδ4 : δ < 4 := by rw [← hδd]; exact Nat.mod_lt _ (by decide)
  rw [show isqBody = [.shld .r11 .r13 2, .shld .r13 .r8 2, .shld .r8 .r9 2, .shift .shl .r9 2] ++
    ([.mov .r14 (.reg .r10), .shift .shr .r14 62, .mov .r15 (.reg .r10), .shift .shl .r15 2,
      .alu .or .r15 (.imm 1)] ++ ([.mov .rax (.reg .r13), .alu .sub .rax (.reg .r15), .mov .rdx (.reg .r11),
      .alu .sbb .rdx (.reg .r14)] ++ ([.cmov .ae .r13 (.reg .rax)] ++ ([.cmov .ae .r11 (.reg .rdx)] ++
      ([.alu .sbb .rbx (.reg .rbx)] ++ [.alu .add .r10 (.reg .r10), .alu .add .r10 (.imm 1),
      .alu .add .r10 (.reg .rbx), .alu .sub .rcx (.imm 1)]))))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (isqA_ok t) fun t₁ ⟨a11, a13, a8, a9, m₁, k₁⟩ => ?_
  simp only [h11, h13, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hr64] at a11
  rw [h13, h8, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr64, Nat.mod_eq_of_lt hP1, hδ] at a13
  rw [h8, h9, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hP1, Nat.mod_mod] at a8
  rw [h9, BitVec.toNat_ofNat, Nat.mod_mod] at a9
  rw [WP.block_append_iff]
  refine WP.mono (isqB_ok t₁) fun t₂ ⟨b14, b15, m₂, k₂⟩ => ?_
  have t₁10 : t₁.gpr .r10 = BitVec.ofNat 64 s := (k₁.gpr (by decide)).trans h10
  rw [t₁10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hs63] : s < 2 ^ 64)] at b14 b15
  rw [mul4_mod] at a13 b15
  have hx1 : r / 2 ^ 62 < 2 ^ 64 := by omega_using [hr64]
  have hx0 : r % 2 ^ 62 * 4 + δ < 2 ^ 64 := by omega_arith
  have hy1 : s / 2 ^ 62 < 2 ^ 64 := by omega_using [hs63]
  have hy0 : s % 2 ^ 62 * 4 + 1 < 2 ^ 64 := by omega_using []
  have ex : r / 2 ^ 62 * 2 ^ 64 + (r % 2 ^ 62 * 4 + δ) = 4 * r + δ := split4 r δ
  have ey : s / 2 ^ 62 * 2 ^ 64 + (s % 2 ^ 62 * 4 + 1) = 4 * s + 1 := split4 s 1
  rw [WP.block_append_iff]
  refine WP.mono (isqC_ok (x1 := r / 2 ^ 62) (x0 := r % 2 ^ 62 * 4 + δ) (y1 := s / 2 ^ 62) (y0 := s % 2 ^ 62 * 4 + 1)
    (of_toNat (by rw [k₂.gpr (by decide), a11])) (of_toNat (by rw [k₂.gpr (by decide), a13]))
    (of_toNat b14) (of_toNat b15) hx1 hx0 hy1 hy0) fun t₃ ⟨hcf, hdif, m₃, k₃⟩ => ?_
  rw [ex, ey] at hcf hdif
  generalize hc : decide (4 * r + δ < 4 * s + 1) = c at hcf hdif
  rw [WP.block_append_iff]
  refine WP.mono (cmovae_ok (d := .r13) (r := .rax) hcf) fun t₄ ⟨d13, cf₄, m₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cmovae_ok (d := .r11) (r := .rdx) (cf₄.trans hcf)) fun t₅ ⟨d11, cf₅, m₅, k₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sbbBx_ok (cf₅.trans (cf₄.trans hcf))) fun t₆ ⟨hbx, m₆, k₆⟩ => ?_
  have t₆10 : t₆.gpr .r10 = BitVec.ofNat 64 s := by
    rw [k₆.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), t₁10]
  have t₆cx : t₆.gpr .rcx = BitVec.ofNat 64 (64 - i) := by
    rw [k₆.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide),
      k₁.gpr (by decide), hcx]
  refine WP.mono (isqE_ok t₆10 hbx t₆cx (by omega_using [hs63]) (by omega_using [hi]) (by omega_using [])) fun t' ⟨e10, ecx, ez, m', k'⟩ => ?_
  -- The new root and remainder.
  have hN' : T / 4 ^ (64 - (i + 1)) = 4 * N + δ := by
    have e := VG.Proof.Rsa.RecoverDet.pair_succ T (63 - i)
    rw [show 63 - i + 1 = 64 - i by omega_using [hi], hNd, hδd] at e
    rw [show 64 - (i + 1) = 63 - i by omega_using [], e]
  obtain ⟨sq, sr, -⟩ := VG.Proof.Rsa.RecoverDet.sqrt_step (t := N) (y := s) (r := r) (δ := δ) hs.symm (by omega_using [hNd, hN, lo, hi', hsi, hs63, e1, hr, hr2, hr64, a13, a11, b14, b15, hx1, hx0, hy1, hy0, ex, ey, hN']) hδ4
  obtain ⟨p8, p9⟩ := pair_shift (T := T) (i := i)
  refine ⟨by rw [ez]; simp only [Option.some.injEq, decide_eq_decide]; omega_using [hi], ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [m', m₆, m₅, m₄, m₃, m₂, m₁, hm], (k.trans ((((k₁.trans k₂).trans (k₃.trans k₄)).trans (k₅.trans k₆)).trans k')).mono
      (by decide)⟩
  · rw [hN', sq, e10]; congr 1
    rw [← hc]
    by_cases h : 4 * s + 1 ≤ 4 * r + δ
    · simp only [h, ↓reduceIte, decide_eq_false (show ¬ 4 * r + δ < 4 * s + 1 by omega_arith), Bool.toNat_false, Nat.sub_zero]
    · simp only [h, ↓reduceIte, decide_eq_true (show 4 * r + δ < 4 * s + 1 by omega_arith), Bool.toNat_true, Nat.add_sub_cancel]
  · -- The remainder's words.
    have hrem : 4 * N + δ - VG.Spec.Rsa.isqrt (4 * N + δ) * VG.Spec.Rsa.isqrt (4 * N + δ) =
        if 4 * s + 1 ≤ 4 * r + δ then 4 * r + δ - (4 * s + 1) else 4 * r + δ := by omega_arith
    rw [hN', hrem, k'.gpr (by decide), k₆.gpr (by decide), d11]
    have t₄11 : t₄.gpr .r11 = BitVec.ofNat 64 (r / 2 ^ 62) := by
      rw [k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide)]; exact of_toNat a11
    cases c
    · have h : 4 * s + 1 ≤ 4 * r + δ := by simp only [decide_eq_false_iff_not] at hc; omega_arith
      simp only [h, ↓reduceIte, Bool.false_eq_true]
      rw [k₄.gpr (by decide)]
      have := words_eq (hdif rfl) (BitVec.isLt _)
      rw [of_toNat this.1]
    · have h : ¬ 4 * s + 1 ≤ 4 * r + δ := by simp only [decide_eq_true_eq] at hc; omega_arith
      simp only [h, ↓reduceIte]
      rw [t₄11, (words_eq ex hx0).1]
  · have hrem : 4 * N + δ - VG.Spec.Rsa.isqrt (4 * N + δ) * VG.Spec.Rsa.isqrt (4 * N + δ) =
        if 4 * s + 1 ≤ 4 * r + δ then 4 * r + δ - (4 * s + 1) else 4 * r + δ := by omega_arith
    rw [hN', hrem, k'.gpr (by decide), k₆.gpr (by decide), k₅.gpr (by decide), d13]
    have t₃13 : t₃.gpr .r13 = BitVec.ofNat 64 (r % 2 ^ 62 * 4 + δ) := by
      rw [k₃.gpr (by decide), k₂.gpr (by decide)]; exact of_toNat a13
    cases c
    · have h : 4 * s + 1 ≤ 4 * r + δ := by simp only [decide_eq_false_iff_not] at hc; omega_arith
      simp only [h, ↓reduceIte, Bool.false_eq_true]
      have := words_eq (hdif rfl) (BitVec.isLt _)
      rw [of_toNat this.2]
    · have h : ¬ 4 * s + 1 ≤ 4 * r + δ := by simp only [decide_eq_true_eq] at hc; omega_arith
      simp only [h, ↓reduceIte]
      rw [t₃13, (words_eq ex hx0).2]
  · rw [k'.gpr (by decide), k₆.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide),
      k₂.gpr (by decide), of_toNat a8, p8]
  · rw [k'.gpr (by decide), k₆.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide),
      k₂.gpr (by decide), of_toNat a9, p9]
  · rw [ecx]; congr 1

/-- The first digit's 64 steps: the root of `T` and its remainder. -/
theorem isq_ok {t₀ t : State} {T : Nat} (hT : T < 2 ^ 128) (h0 : IsqInv t₀ T 0 t) :
    WP isa (.loop (.block isqBody) .ne) t fun t' => IsqInv t₀ T 64 t' :=
  wp_upto (a := 0) (N := 64) (by decide) (IsqInv t₀ T)
    (fun j _ hj s hI => isqStep_ok hT hj hI) (fun _ h => h) h0

/-- The first digit's entry state: `r10`, `r11`, `r13` zero, the pair `(r8, r9)`, `rcx = 64`. -/
theorem isqInv0 {t₀ t : State} {T : Nat} (hT : T < 2 ^ 128) (h10 : t.gpr .r10 = 0) (h11 : t.gpr .r11 = 0)
    (h13 : t.gpr .r13 = 0) (h8 : t.gpr .r8 = BitVec.ofNat 64 (T / 2 ^ 64))
    (h9 : t.gpr .r9 = BitVec.ofNat 64 (T % 2 ^ 64)) (hcx : t.gpr .rcx = BitVec.ofNat 64 64)
    (hm : t.mem = t₀.mem) (k : Keep [.r8, .r9, .r10, .r11, .r13, .r14, .r15, .rax, .rdx, .rbx, .rcx] t₀ t) :
    IsqInv t₀ T 0 t := by
  have e0 : T / 4 ^ (64 - 0) = 0 := Nat.div_eq_of_lt (by rw [Nat.sub_zero, pow4]; exact hT)
  have z : VG.Spec.Rsa.isqrt 0 = 0 := by rw [VG.Spec.Rsa.isqrt]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_, hcx, hm, k⟩
  · rw [e0, z, h10]; rfl
  · rw [e0, z, h11]; rfl
  · rw [e0, z, h13]; rfl
  · rw [h8, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hT]
  · rw [h9, Nat.pow_zero, Nat.mul_one]
