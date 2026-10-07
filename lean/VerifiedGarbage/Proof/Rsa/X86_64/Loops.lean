import VerifiedGarbage.Impl.Rsa.X86_64.Keys
import VerifiedGarbage.Proof.Bignum.X86_64.CrtArith
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.Cmp
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Double

/-!
# RSA private keys on x86-64: bases and loops over the words

The bases of the arrays, computed from `rdi` and the stride in `r9`
(`base_ok`), and the loops of the routines of `Impl/Rsa/X86_64/Keys.lean`
that `vg_rsa_public`'s proofs do not already cover: a shift left by a bit
in place (`shl_ok`), a selection in place (`sel_ok`), a masked subtraction
(`subM_ok`), a shift right by a bit (`shr_ok`), a masked swap (`cswap_ok`),
and the masked addition (`addM_ok`) and subtraction (`sub_ok`) of
`subModArr` and `subMod`, as loops.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## Bases -/

theorem add_r9 (x : Addr) (B : Addr) (w j : Nat) (hx : x = off B (slot w j)) :
    x + BitVec.ofNat 64 (8 * (w + 2)) = off B (slot w (j + 1)) := by
  subst hx
  have : slot w (j + 1) = slot w j + 8 * (w + 2) := by unfold slot; rw [Nat.add_mul, Nat.one_mul]; omega
  rw [this]
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

theorem only_of {r : Reg} {s s' : State} (h : ∀ r', r' ≠ r → s'.gpr r' = s.gpr r') (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Keep [r] s s' :=
  ⟨fun r' hr' => h r' (by simpa using hr'), hrd, hwr⟩

/-- `base j r`: `r := rdi + 256 + j · r9`, the base of array `j`. -/
theorem base_ok {s : State} {B : Addr} {w : Nat} (j : Nat) {r : Reg} (hr' : r ≠ .r9)
    (hdi : s.gpr .rdi = B) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block (base j r)) s fun t =>
      t.gpr r = off B (slot w j) ∧ t.mem = s.mem ∧ Keep [r] s t := by
  unfold base
  rw [WP.block_append_iff]
  have e₀ : WP isa (.block [.mov r (.reg .rdi), .alu .add r (.imm (BitVec.ofNat 32 hdrBytes))]) s
      fun (t₁ : State) => t₁.gpr r = off B (slot w 0) ∧ t₁.mem = s.mem ∧ Keep [r] s t₁ := by
    xrun [hdi, sx_ofNat (show hdrBytes < 2 ^ 31 by decide)]
    refine ⟨by simp [off, slot], only_of (fun r' h => by simp [setReg_gpr, setFlags_gpr, h]) rfl rfl⟩
  refine WP.mono e₀ fun t₁ ⟨h₁, m₁, k₁⟩ => ?_
  have h9₁ : t₁.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) := (k₁.gpr (by simp [hr'.symm])).trans h9
  suffices ∀ n, ∀ t, t.gpr r = off B (slot w (j - n)) → t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) → n ≤ j →
      WP isa (.block (List.replicate n (.alu .add r (.reg .r9)))) t fun t' =>
        t'.gpr r = off B (slot w j) ∧ t'.mem = t.mem ∧ Keep [r] t t' by
    refine WP.mono (this j t₁ (by rw [Nat.sub_self]; exact h₁) h9₁ (Nat.le_refl _))
      fun t ⟨h, m, k⟩ => ⟨h, m.trans m₁, (k₁.trans k).mono (by simp)⟩
  intro n
  induction n with
  | zero => intro t h _ _; exact WP.block_nil ⟨by rwa [Nat.sub_zero] at h, rfl, Keep.refl _ _⟩
  | succ n ih =>
    intro t h h9t hn
    rw [List.replicate_succ, show (Instr.alu .add r (.reg .r9) :: List.replicate n (.alu .add r (.reg .r9))) =
      [.alu .add r (.reg .r9)] ++ List.replicate n (.alu .add r (.reg .r9)) from rfl, WP.block_append_iff]
    have e₁ : WP isa (.block [.alu .add r (.reg .r9)]) t
        fun (t₁ : State) => t₁.gpr r = off B (slot w (j - n)) ∧ t₁.mem = t.mem ∧ Keep [r] t t₁ := by
      xrun [h, h9t]
      refine ⟨?_, only_of (fun r' h => by simp [setReg_gpr, setFlags_gpr, h]) rfl rfl⟩
      rw [add_r9 _ B w (j - (n + 1)) rfl, show j - (n + 1) + 1 = j - n by omega]
    refine WP.mono e₁ fun t₁ ⟨h₁, m₁, k₁⟩ => ?_
    refine WP.mono (ih t₁ h₁ ((k₁.gpr (by simp [hr'.symm])).trans h9t) (by omega))
      fun t' ⟨h', m', k'⟩ => ⟨h', m'.trans m₁, (k₁.trans k').mono (by simp)⟩

/-- `ws`: `w` and the stride from the header. -/
theorem ws_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z)
    (hW : word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hS : word s.mem B (8 * sStride) = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block ws) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem ∧
        Keep [.r12, .r9] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  refine WP.mono (WP.keep [.r12, .r9] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
    t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold ws
  xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl sStride (by decide), hW, hS]

/-! ## Loops -/

/-- After `j` words of `shlBody` in place at `e`: `X_j' + 2^(64 j) c = 2 X_j + c₀`. -/
structure ShlInv (s₀ : State) (B : Addr) (Z e : Nat) (c₀ : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B e (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = mask c ∧
    wv t.mem B e j + 2 ^ (64 * j) * c.toNat = 2 * wv s₀.mem B e j + c₀.toNat

theorem shlStep_ok {s₀ : State} {B : Addr} {Z w e : Nat} {c₀ : Bool}
    (hbx : s₀.gpr .rbx = off B e) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 32) (he : e + 8 * w ≤ Z)
    {j : Nat} (hj : j < w) {t : State} (hI : ShlInv s₀ B Z e c₀ j t) :
    WP isa (.block (shlBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ ShlInv s₀ B Z e c₀ (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B e := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (off B (e + 8 * j)) r ∧
        r.toNat + 2 ^ 64 * c'.toNat = 2 * (word t.mem B (e + 8 * j)).toNat + c.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold shlBody cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tbx hI.r14, hbp, cf_mask, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show e + 8 * j + 8 ≤ Z by omega)]
    refine ⟨_, rfl, _, rfl, ?_⟩
    rw [adc_toNat]
    simp only [Bignum.word]
    omega
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : word t.mem B (e + 8 * j) = word s₀.mem B (e + 8 * j) := hI.out.word (by omega) (by omega)
  rw [hx] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega)]
    simp only [wv]
    rw [pow64_succ]
    grind

/-- `wordLoop 0 shlBody` over `N` words at `e`: `X' + 2^(64 N) c = 2 X + c₀`
for the carry `c₀` in `rbp` on entry and `c` on exit. -/
theorem shl_ok {s : State} {B : Addr} {Z N e : Nat} {c₀ : Bool} (hs : Scr s B Z)
    (hbx : s.gpr .rbx = off B e) (h12 : s.gpr .r12 = BitVec.ofNat 64 N) (hbp : s.gpr .rbp = mask c₀)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (he : e + 8 * N ≤ Z) :
    WP isa (wordLoop 0 shlBody) s fun t => ∃ c : Bool, t.gpr .rbp = mask c ∧
      wv t.mem B e N + 2 ^ (64 * N) * c.toNat = 2 * wv s.mem B e N + c₀.toNat ∧
      Outside B e (8 * N) s.mem t.mem ∧ Keep [.rax, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      ShlInv s B Z e c₀ 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨c₀, (k.gpr (by decide)).trans hbp, by simp [wv]⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN' (ShlInv s B Z e c₀) h0
    (fun j _ hj t hI => shlStep_ok hbx h12 (by omega) he hj hI)) fun t hI => ?_
  obtain ⟨c, hc, hv⟩ := hI.val
  exact ⟨c, hc, hv, hI.out, hI.keep⟩

/-! ## Selection in place -/

structure SelInv (s₀ : State) (B : Addr) (Z eA eT : Nat) (lt : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eA (8 * j) s₀.mem t.mem
  val : wv t.mem B eA j = if lt then wv s₀.mem B eA j else wv s₀.mem B eT j

theorem selStep_ok {s₀ : State} {B : Addr} {Z w eA eT : Nat} {lt : Bool}
    (h8 : s₀.gpr .r8 = off B eA) (hsi : s₀.gpr .rsi = off B eT) (hbp : s₀.gpr .rbp = mask lt)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 32) (hA : eA + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z)
    (sT : eA + 8 * w ≤ eT ∨ eT + 8 * w ≤ eA) {j : Nat} (hj : j < w) {t : State} (hI : SelInv s₀ B Z eA eT lt j t) :
    WP isa (.block (selBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ SelInv s₀ B Z eA eT lt (j + 1) t' := by
  have hn := hI.scr.nowrap
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have tsi : t.gpr .rsi = off B eT := (hI.keep.gpr (by decide)).trans hsi
  have tbp : t.gpr .rbp = mask lt := (hI.keep.gpr (by decide)).trans hbp
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hx : word t.mem B (eA + 8 * j) = word s₀.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eT + 8 * j) = word s₀.mem B (eT + 8 * j) := hI.out.word (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eA + 8 * j))
      (if lt then word s₀.mem B (eA + 8 * j) else word s₀.mem B (eT + 8 * j))) (by
      unfold selBody
      xrun [State.ea, ix, addr0 t8 hI.r14, addr0 tsi hI.r14, tbp,
        hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eT + 8 * j + 8 ≤ Z by omega),
        hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega), hx, hy, select_mask]) rfl) fun t₁ ⟨hm, k₁⟩ => ?_
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hI.val]
    cases lt <;> simp [wv]

/-- `wordLoop 0 selBody` over `N` words: `[r8] := lt ? [r8] : [rsi]`. -/
theorem sel_ok {s : State} {B : Addr} {Z N eA eT : Nat} {lt : Bool} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B eA) (hsi : s.gpr .rsi = off B eT) (hbp : s.gpr .rbp = mask lt)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 N) (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (hA : eA + 8 * N ≤ Z)
    (hT : eT + 8 * N ≤ Z) (sT : eA + 8 * N ≤ eT ∨ eT + 8 * N ≤ eA) :
    WP isa (wordLoop 0 selBody) s fun t =>
      wv t.mem B eA N = (if lt then wv s.mem B eA N else wv s.mem B eT N) ∧
      Outside B eA (8 * N) s.mem t.mem ∧ Keep [.rax, .rdx, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      SelInv s B Z eA eT lt 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _, by cases lt <;> rfl⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN' (SelInv s B Z eA eT lt) h0
    (fun j _ hj t hI => selStep_ok h8 hsi hbp h12 (by omega) hA hT sT hj hI)) fun t hI => ⟨hI.val, hI.out, hI.keep⟩

/-! ## Masked subtraction -/

structure SubMInv (s₀ : State) (B : Addr) (Z eo eA eB : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eo (8 * j) s₀.mem t.mem
  val : ∃ b : Bool, t.gpr .rbp = mask b ∧
    wv t.mem B eo j + (if c then wv s₀.mem B eB j else 0) = wv s₀.mem B eA j + 2 ^ (64 * j) * b.toNat

theorem subMStep_ok {s₀ : State} {B : Addr} {Z w eo eA eB : Nat} {c : Bool}
    (hsi : s₀.gpr .rsi = off B eo) (h8 : s₀.gpr .r8 = off B eA) (h10 : s₀.gpr .r10 = off B eB)
    (h15 : s₀.gpr .r15 = mask c) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 32)
    (ho : eo + 8 * w ≤ Z) (hA : eA + 8 * w ≤ Z) (hB : eB + 8 * w ≤ Z)
    (sA : eo ≤ eA ∨ eA + 8 * w ≤ eo) (sB : eo + 8 * w ≤ eB ∨ eB + 8 * w ≤ eo)
    {j : Nat} (hj : j < w) {t : State} (hI : SubMInv s₀ B Z eo eA eB c j t) :
    WP isa (.block (subMBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ SubMInv s₀ B Z eo eA eB c (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tsi : t.gpr .rsi = off B eo := (hI.keep.gpr (by decide)).trans hsi
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have t10 : t.gpr .r10 = off B eB := (hI.keep.gpr (by decide)).trans h10
  have t15 : t.gpr .r15 = mask c := (hI.keep.gpr (by decide)).trans h15
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨b, hbp, hval⟩ := hI.val
  have hx : word t.mem B (eA + 8 * j) = word s₀.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eB + 8 * j) = word s₀.mem B (eB + 8 * j) := hI.out.word (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx, .rbp] (Q := fun t₁ =>
      ∃ b' : Bool, t₁.gpr .rbp = mask b' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (off B (eo + 8 * j)) r ∧
        r.toNat + (word s₀.mem B (eB + 8 * j) &&& mask c).toNat + b.toNat =
          (word s₀.mem B (eA + 8 * j)).toNat + 2 ^ 64 * b'.toNat) ?_ rfl)
    fun t₁ ⟨⟨b', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold subMBody cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tsi hI.r14, addr0 t8 hI.r14, addr0 t10 hI.r14, hbp, t15, cf_mask,
      hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eB + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega), hx, hy]
    exact ⟨_, rfl, _, rfl, sbb_toNat _ _ _⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  rw [and_mask] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨b', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega)]
    simp only [wv]
    rw [pow64_succ]
    cases c
    · simp only [ite_false, Bool.false_eq_true] at hr hval ⊢
      grind
    · simp only [ite_true] at hr hval ⊢
      grind

/-- `wordLoop 0 subMBody` over `N` words: `[rsi] := [r8] - ([r10] & mask c)`,
its borrow `b` in `rbp`. -/
theorem subM_ok {s : State} {B : Addr} {Z N eo eA eB : Nat} {c : Bool} (hs : Scr s B Z)
    (hsi : s.gpr .rsi = off B eo) (h8 : s.gpr .r8 = off B eA) (h10 : s.gpr .r10 = off B eB)
    (h15 : s.gpr .r15 = mask c) (h12 : s.gpr .r12 = BitVec.ofNat 64 N) (hbp : s.gpr .rbp = mask false)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (ho : eo + 8 * N ≤ Z) (hA : eA + 8 * N ≤ Z) (hB : eB + 8 * N ≤ Z)
    (sA : eo ≤ eA ∨ eA + 8 * N ≤ eo) (sB : eo + 8 * N ≤ eB ∨ eB + 8 * N ≤ eo) :
    WP isa (wordLoop 0 subMBody) s fun t => ∃ b : Bool, t.gpr .rbp = mask b ∧
      wv t.mem B eo N + (if c then wv s.mem B eB N else 0) = wv s.mem B eA N + 2 ^ (64 * N) * b.toNat ∧
      Outside B eo (8 * N) s.mem t.mem ∧ Keep [.rax, .rdx, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      SubMInv s B Z eo eA eB c 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by cases c <;> simp [wv]⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN' (SubMInv s B Z eo eA eB c) h0
    (fun j _ hj t hI => subMStep_ok hsi h8 h10 h15 h12 (by omega) ho hA hB sA sB hj hI)) fun t hI => ?_
  obtain ⟨b, hb, hv⟩ := hI.val
  exact ⟨b, hb, hv, hI.out, hI.keep⟩

/-! ## Shift right -/

theorem shr_word (x y : BitVec 64) :
    ((x >>> 1) + (y &&& 1).rotateRight 1).toNat = x.toNat / 2 + 2 ^ 63 * (y.toNat % 2) := by
  have h1 : (x >>> 1).toNat = x.toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : y &&& 1 = BitVec.ofNat 64 (y.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
    omega
  have h3 : ((y &&& 1).rotateRight 1).toNat = 2 ^ 63 * (y.toNat % 2) := by
    rw [h2]; rcases Nat.mod_two_eq_zero_or_one y.toNat with h | h <;> rw [h] <;> decide
  have hx := x.isLt
  have hy : y.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  have hlt : x.toNat / 2 + 2 ^ 63 * (y.toNat % 2) < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, h1, h3]
  exact Nat.mod_eq_of_lt hlt

structure ShrInv (s₀ : State) (B : Addr) (Z eo eA : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eo (8 * j) s₀.mem t.mem
  val : wv t.mem B eo j * 2 + (word s₀.mem B eA).toNat % 2 =
    wv s₀.mem B eA j + 2 ^ (64 * j) * ((word s₀.mem B (eA + 8 * j)).toNat % 2)

theorem shrStep_ok {s₀ : State} {B : Addr} {Z w eo eA : Nat}
    (hsi : s₀.gpr .rsi = off B eo) (h8 : s₀.gpr .r8 = off B eA) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (ho : eo + 8 * w ≤ Z) (hA : eA + 8 * (w + 1) ≤ Z) (sA : eo ≤ eA ∨ eA + 8 * (w + 1) ≤ eo)
    {j : Nat} (hj : j < w) {t : State} (hI : ShrInv s₀ B Z eo eA j t) :
    WP isa (.block (shrBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ ShrInv s₀ B Z eo eA (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tsi : t.gpr .rsi = off B eo := (hI.keep.gpr (by decide)).trans hsi
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hx : word t.mem B (eA + 8 * j) = word s₀.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eA + 8 * j + 8) = word s₀.mem B (eA + 8 * j + 8) :=
    hI.out.word (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t₁ => ∃ r : BitVec 64,
      t₁.mem = t.mem.writeW (off B (eo + 8 * j)) r ∧
      r.toNat = (word s₀.mem B (eA + 8 * j)).toNat / 2 + 2 ^ 63 * ((word s₀.mem B (eA + 8 * j + 8)).toNat % 2))
      ?_ rfl) fun t₁ ⟨⟨r, hm, hr⟩, k₁⟩ => ?_
  · unfold shrBody
    xrun [State.ea, ix, addr0 tsi hI.r14, addr0 t8 hI.r14, addr8 t8 hI.r14,
      hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eA + 8 * j + 8 + 8 ≤ Z by omega),
      hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega), hx, hy]
    exact ⟨_, rfl, shr_word _ _⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hr]
    have hv := hI.val
    simp only [wv]
    rw [pow64_succ, show eA + 8 * (j + 1) = eA + 8 * j + 8 by omega]
    have h2 := Nat.div_add_mod (word s₀.mem B (eA + 8 * j)).toNat 2
    generalize (word s₀.mem B (eA + 8 * j)).toNat = x at h2 hv ⊢
    generalize (word s₀.mem B (eA + 8 * j + 8)).toNat % 2 = y
    generalize 2 ^ (64 * j) = P at hv ⊢
    have : (2 : Nat) ^ 64 = 2 * 2 ^ 63 := by decide
    rw [this]
    grind

/-- `wordLoop 0 shrBody` over `N` words: `2 [rsi] + a₀ = A + 2^(64 N) a_N`
for the `N + 1` words `A` at `r8`, the low bit `a₀` of `A` and the low bit
`a_N` of its word `N`. -/
theorem shr_ok {s : State} {B : Addr} {Z N eo eA : Nat} (hs : Scr s B Z)
    (hsi : s.gpr .rsi = off B eo) (h8 : s.gpr .r8 = off B eA) (h12 : s.gpr .r12 = BitVec.ofNat 64 N)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (ho : eo + 8 * N ≤ Z) (hA : eA + 8 * (N + 1) ≤ Z)
    (sA : eo ≤ eA ∨ eA + 8 * (N + 1) ≤ eo) :
    WP isa (wordLoop 0 shrBody) s fun t =>
      wv t.mem B eo N * 2 + (word s.mem B eA).toNat % 2 =
        wv s.mem B eA N + 2 ^ (64 * N) * ((word s.mem B (eA + 8 * N)).toNat % 2) ∧
      Outside B eo (8 * N) s.mem t.mem ∧ Keep [.rax, .rdx, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      ShrInv s B Z eo eA 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _, by simp [wv]⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN' (ShrInv s B Z eo eA) h0
    (fun j _ hj t hI => shrStep_ok hsi h8 h12 (by omega) ho hA sA hj hI)) fun t hI => ⟨hI.val, hI.out, hI.keep⟩

/-! ## Masked swap -/

theorem cswap_x (a b : BitVec 64) (c : Bool) : a ^^^ ((a ^^^ b) &&& mask c) = if c then b else a := by
  cases c
  · simp [mask_false]
  · simp only [mask_true, BitVec.and_allOnes, ite_true, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem cswap_y (a b : BitVec 64) (c : Bool) : b ^^^ ((a ^^^ b) &&& mask c) = if c then a else b := by
  cases c
  · simp [mask_false]
  · simp only [mask_true, BitVec.and_allOnes, ite_true]
    rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- After `j` words of `cswapBody` on `X` at `eX` and `Y` at `eY`. -/
structure CsInv (s₀ : State) (B : Addr) (Z eX eY : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : ∀ x, (ofs B x < eX ∨ eX + 8 * j ≤ ofs B x) → (ofs B x < eY ∨ eY + 8 * j ≤ ofs B x) → t.mem x = s₀.mem x
  vx : ∀ i < j, word t.mem B (eX + 8 * i) =
    if c then word s₀.mem B (eY + 8 * i) else word s₀.mem B (eX + 8 * i)
  vy : ∀ i < j, word t.mem B (eY + 8 * i) =
    if c then word s₀.mem B (eX + 8 * i) else word s₀.mem B (eY + 8 * i)

theorem csStep_ok {s₀ : State} {B : Addr} {Z w eX eY : Nat} {c : Bool}
    (hbx : s₀.gpr .rbx = off B eX) (h10 : s₀.gpr .r10 = off B eY) (h15 : s₀.gpr .r15 = mask c)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 32) (hX : eX + 8 * w ≤ Z) (hY : eY + 8 * w ≤ Z)
    (sXY : eX + 8 * w ≤ eY ∨ eY + 8 * w ≤ eX) {j : Nat} (hj : j < w) {t : State} (hI : CsInv s₀ B Z eX eY c j t) :
    WP isa (.block (cswapBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ CsInv s₀ B Z eX eY c (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B eX := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = off B eY := (hI.keep.gpr (by decide)).trans h10
  have t15 : t.gpr .r15 = mask c := (hI.keep.gpr (by decide)).trans h15
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hx : word t.mem B (eX + 8 * j) = word s₀.mem B (eX + 8 * j) :=
    Mem.readW_congr fun b hb => hI.out _ (by rw [ofs_off B (by omega)]; omega)
      (by rw [ofs_off B (by omega)]; omega)
  have hy : word t.mem B (eY + 8 * j) = word s₀.mem B (eY + 8 * j) :=
    Mem.readW_congr fun b hb => hI.out _ (by rw [ofs_off B (by omega)]; omega)
      (by rw [ofs_off B (by omega)]; omega)
  have hy' : ∀ v : BitVec 64, (t.mem.writeW (off B (eX + 8 * j)) v).readW (off B (eY + 8 * j)) 64 =
      word s₀.mem B (eY + 8 * j) := fun v =>
    ((writeW_outside t.mem B v (by omega)).word (by omega) (by omega)).trans hy
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t₁ => t₁.mem =
      (t.mem.writeW (off B (eX + 8 * j)) (if c then word s₀.mem B (eY + 8 * j) else word s₀.mem B (eX + 8 * j))).writeW
        (off B (eY + 8 * j)) (if c then word s₀.mem B (eX + 8 * j) else word s₀.mem B (eY + 8 * j))) (by
      unfold cswapBody
      xrun [State.ea, ix, addr0 tbx hI.r14, addr0 t10 hI.r14, t15,
        hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eY + 8 * j + 8 ≤ Z by omega),
        hI.scr.st (show eX + 8 * j + 8 ≤ Z by omega), hI.scr.st (show eY + 8 * j + 8 ≤ Z by omega), hx, hy, hy',
        cswap_x, cswap_y]) rfl) fun t₁ ⟨hm, k₁⟩ => ?_
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have o1 := writeW_outside t.mem B (if c then word s₀.mem B (eY + 8 * j) else word s₀.mem B (eX + 8 * j))
    (d := eX + 8 * j) (by omega)
  have o2 := writeW_outside (t.mem.writeW (off B (eX + 8 * j))
    (if c then word s₀.mem B (eY + 8 * j) else word s₀.mem B (eX + 8 * j))) B
    (if c then word s₀.mem B (eX + 8 * j) else word s₀.mem B (eY + 8 * j)) (d := eY + 8 * j) (by omega)
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_, ?_, ?_⟩
  · intro x h1 h2
    rw [hm', hm, o2 x (by omega), o1 x (by omega)]
    exact hI.out x (by omega) (by omega)
  · intro i hi
    rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [o2.word (by omega) (by omega), o1.word (by omega) (by omega)]; exact hI.vx i hi
    · rw [o2.word (by omega) (by omega), word_writeW_self]
  · intro i hi
    rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [o2.word (by omega) (by omega), o1.word (by omega) (by omega)]; exact hI.vy i hi
    · rw [word_writeW_self]

/-- `wordLoop 0 cswapBody` over `N` words: `[rbx]` and `[r10]` swapped if `c`. -/
theorem cswap_ok {s : State} {B : Addr} {Z N eX eY : Nat} {c : Bool} (hs : Scr s B Z)
    (hbx : s.gpr .rbx = off B eX) (h10 : s.gpr .r10 = off B eY) (h15 : s.gpr .r15 = mask c)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 N) (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (hX : eX + 8 * N ≤ Z)
    (hY : eY + 8 * N ≤ Z) (sXY : eX + 8 * N ≤ eY ∨ eY + 8 * N ≤ eX) :
    WP isa (wordLoop 0 cswapBody) s fun t =>
      wv t.mem B eX N = (if c then wv s.mem B eY N else wv s.mem B eX N) ∧
      wv t.mem B eY N = (if c then wv s.mem B eX N else wv s.mem B eY N) ∧
      Frm B [(eX, 8 * N), (eY, 8 * N)] s.mem t.mem ∧ Keep [.rax, .rdx, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      CsInv s B Z eX eY c 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, fun x _ _ => by rw [hm], fun i hi => absurd hi (by omega),
      fun i hi => absurd hi (by omega)⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN' (CsInv s B Z eX eY c) h0
    (fun j _ hj t hI => csStep_ok hbx h10 h15 h12 (by omega) hX hY sXY hj hI)) fun t hI => ?_
  refine ⟨?_, ?_, fun x hx => hI.out x (hx (eX, 8 * N) (by simp)) (hx (eY, 8 * N) (by simp)), hI.keep⟩
  · cases c
    · exact wv_congr2 fun i hi => by simpa using hI.vx i hi
    · exact wv_congr2 fun i hi => by simpa using hI.vx i hi
  · cases c
    · exact wv_congr2 fun i hi => by simpa using hI.vy i hi
    · exact wv_congr2 fun i hi => by simpa using hI.vy i hi

/-! ## The loops of `subMod` and `subModArr` -/

/-- `wordLoop 0 subBody` over `N` words: `[rsi] := [r8] - [r10]`, its borrow
in `rbp`. -/
theorem sub_ok {s : State} {B : Addr} {Z N eA eN eT : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B eA) (h10 : s.gpr .r10 = off B eN) (hsi : s.gpr .rsi = off B eT)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 N) (hbp : s.gpr .rbp = mask false) (hN : 1 ≤ N) (hN' : N < 2 ^ 31)
    (hA : eA + 8 * N ≤ Z) (hNz : eN + 8 * N ≤ Z) (hT : eT + 8 * N ≤ Z)
    (sA : eT + 8 * N ≤ eA ∨ eA + 8 * N ≤ eT) (sN : eT + 8 * N ≤ eN ∨ eN + 8 * N ≤ eT) :
    WP isa (wordLoop 0 subBody) s fun t => ∃ c : Bool, t.gpr .rbp = mask c ∧
      wv t.mem B eT N + wv s.mem B eN N = wv s.mem B eA N + 2 ^ (64 * N) * c.toNat ∧
      Outside B eT (8 * N) s.mem t.mem ∧ Keep [.rax, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      SubInv s B Z eA eN eT 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by simp [wv]⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN' (SubInv s B Z eA eN eT) h0
    (fun j _ hj t hI => subStep_ok h8 h10 hsi h12 (by omega) hA hNz hT sA sN hj hI)) fun t hI => ?_
  obtain ⟨c, hc, hv⟩ := hI.val
  exact ⟨c, hc, hv, hI.out, hI.keep⟩

/-- `wordLoop 0 addMBody` over `N` words: `[rbx] := ([r10] & mask c) + [r8]`,
its carry in `rbp`. -/
theorem addM_ok {s : State} {B : Addr} {Z N eo eN eA : Nat} {c : Bool} (hs : Scr s B Z)
    (hbx : s.gpr .rbx = off B eo) (h10 : s.gpr .r10 = off B eN) (h8 : s.gpr .r8 = off B eA)
    (h15 : s.gpr .r15 = mask c) (h12 : s.gpr .r12 = BitVec.ofNat 64 N) (hbp : s.gpr .rbp = mask false)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (ho : eo + 8 * N ≤ Z) (hNz : eN + 8 * N ≤ Z) (hA : eA + 8 * N ≤ Z)
    (sN : eN + 8 * N ≤ eo ∨ eo + 8 * N ≤ eN) (sA : eA + 8 * N ≤ eo ∨ eo + 8 * N ≤ eA) :
    WP isa (wordLoop 0 addMBody) s fun t => ∃ c' : Bool, t.gpr .rbp = mask c' ∧
      wv t.mem B eo N + 2 ^ (64 * N) * c'.toNat = (if c then wv s.mem B eN N else 0) + wv s.mem B eA N ∧
      Outside B eo (8 * N) s.mem t.mem ∧ Keep [.rax, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      MaInv s B Z eo eN eA c 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by cases c <;> simp [wv]⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN' (MaInv s B Z eo eN eA c) h0
    (fun j _ hj t hI => maStep_ok hbx h10 h8 h15 h12 (by omega) ho hNz hA sN sA hj hI)) fun t hI => ?_
  obtain ⟨c', hc, hv⟩ := hI.val
  exact ⟨c', hc, hv, hI.out, hI.keep⟩

end VG.Proof.Rsa.X86_64
