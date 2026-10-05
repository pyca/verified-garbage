import VerifiedGarbage.Impl.Rsa.X86_64.Keys
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.Rsa.X86_64.Recover

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.Loops`. -/
section

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
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-! ## Bases -/

theorem add_r9 (x : Addr) (B : Addr) (w j : Nat) (hx : x = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j)) :
    x + BitVec.ofNat 64 (8 * (w + 2)) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w (j + 1)) := by
  subst hx
  have : VG.Proof.Bignum.X86_64.slot w (j + 1) = VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) := by unfold VG.Proof.Bignum.X86_64.slot; rw [Nat.add_mul, Nat.one_mul]; omega
  rw [this]
  simp only [VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, BitVec.ofNat_add]

theorem only_of {r : Reg} {s s' : State} (h : ∀ r', r' ≠ r → s'.gpr r' = s.gpr r') (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.MlKem.X86_64.Keep [r] s s' :=
  ⟨fun r' hr' => h r' (by simpa using hr'), hrd, hwr⟩

/-- `base j r`: `r := rdi + 256 + j · r9`, the base of array `j`. -/
theorem base_ok {s : State} {B : Addr} {w : Nat} (j : Nat) {r : Reg} (hr' : r ≠ .r9)
    (hdi : s.gpr .rdi = B) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block (base j r)) s fun t =>
      t.gpr r = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j) ∧ t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [r] s t := by
  unfold base
  rw [WP.block_append_iff]
  have e₀ : WP isa (.block [.mov r (.reg .rdi), .alu .add r (.imm (BitVec.ofNat 32 hdrBytes))]) s
      fun (t₁ : State) => t₁.gpr r = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w 0) ∧ t₁.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [r] s t₁ := by
    xrun [hdi, sx_ofNat (show hdrBytes < 2 ^ 31 by decide)]
    refine ⟨by simp [VG.Proof.Bignum.X86_64.off, VG.Proof.Bignum.X86_64.slot], VG.Proof.Rsa.X86_64.only_of (fun r' h => by simp [setReg_gpr, setFlags_gpr, h]) rfl rfl⟩
  refine WP.mono e₀ fun t₁ ⟨h₁, m₁, k₁⟩ => ?_
  have h9₁ : t₁.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) := (k₁.gpr (by simp [hr'.symm])).trans h9
  suffices ∀ n, ∀ t, t.gpr r = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w (j - n)) → t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) → n ≤ j →
      WP isa (.block (List.replicate n (.alu .add r (.reg .r9)))) t fun t' =>
        t'.gpr r = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j) ∧ t'.mem = t.mem ∧ VG.Proof.MlKem.X86_64.Keep [r] t t' by
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
        fun (t₁ : State) => t₁.gpr r = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w (j - n)) ∧ t₁.mem = t.mem ∧ VG.Proof.MlKem.X86_64.Keep [r] t t₁ := by
      xrun [h, h9t]
      refine ⟨?_, VG.Proof.Rsa.X86_64.only_of (fun r' h => by simp [setReg_gpr, setFlags_gpr, h]) rfl rfl⟩
      rw [VG.Proof.Rsa.X86_64.add_r9 _ B w (j - (n + 1)) rfl, show j - (n + 1) + 1 = j - n by omega]
    refine WP.mono e₁ fun t₁ ⟨h₁, m₁, k₁⟩ => ?_
    refine WP.mono (ih t₁ h₁ ((k₁.gpr (by simp [hr'.symm])).trans h9t) (by omega))
      fun t' ⟨h', m', k'⟩ => ⟨h', m'.trans m₁, (k₁.trans k').mono (by simp)⟩

/-- `ws`: `w` and the stride from the header. -/
theorem ws_ok {s : State} {B : Addr} {Z w : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z)
    (hW : VG.Proof.Bignum.X86_64.word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hS : VG.Proof.Bignum.X86_64.word s.mem B (8 * sStride) = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block VG.Impl.Rsa.X86_64.Keys.ws) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem ∧
        VG.Proof.MlKem.X86_64.Keep [.r12, .r9] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  refine WP.mono (WP.keep [.r12, .r9] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
    t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold VG.Impl.Rsa.X86_64.Keys.ws
  xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, hdrOff, hl sW (by decide), hl sStride (by decide), hW, hS]

/-! ## Loops -/

/-- After `j` words of `shlBody` in place at `e`: `X_j' + 2^(64 j) c = 2 X_j + c₀`. -/
structure ShlInv (s₀ : State) (B : Addr) (Z e : Nat) (c₀ : Bool) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : VG.Proof.Bignum.X86_64.Outside B e (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = VG.Proof.Bignum.X86_64.mask c ∧
    wv t.mem B e j + 2 ^ (64 * j) * c.toNat = 2 * wv s₀.mem B e j + c₀.toNat

theorem shlStep_ok {s₀ : State} {B : Addr} {Z w e : Nat} {c₀ : Bool}
    (hbx : s₀.gpr .rbx = VG.Proof.Bignum.X86_64.off B e) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 32) (he : e + 8 * w ≤ Z)
    {j : Nat} (hj : j < w) {t : State} (hI : VG.Proof.Rsa.X86_64.ShlInv s₀ B Z e c₀ j t) :
    WP isa (.block (shlBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ VG.Proof.Rsa.X86_64.ShlInv s₀ B Z e c₀ (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off B e := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = VG.Proof.Bignum.X86_64.mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (e + 8 * j)) r ∧
        r.toNat + 2 ^ 64 * c'.toNat = 2 * (VG.Proof.Bignum.X86_64.word t.mem B (e + 8 * j)).toNat + c.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold shlBody cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tbx hI.r14, hbp, cf_mask, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show e + 8 * j + 8 ≤ Z by omega)]
    refine ⟨_, rfl, _, rfl, ?_⟩
    rw [adc_toNat]
    simp only [Bignum.X86_64.word]
    omega
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : VG.Proof.Bignum.X86_64.word t.mem B (e + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem B (e + 8 * j) := hI.out.word (by omega) (by omega)
  rw [hx] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [VG.Proof.Bignum.X86_64.writeW_outside t.mem B r (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega)]
    simp only [wv]
    rw [pow64_succ]
    grind

/-- `wordLoop 0 shlBody` over `N` words at `e`: `X' + 2^(64 N) c = 2 X + c₀`
for the carry `c₀` in `rbp` on entry and `c` on exit. -/
theorem shl_ok {s : State} {B : Addr} {Z N e : Nat} {c₀ : Bool} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hbx : s.gpr .rbx = VG.Proof.Bignum.X86_64.off B e) (h12 : s.gpr .r12 = BitVec.ofNat 64 N) (hbp : s.gpr .rbp = VG.Proof.Bignum.X86_64.mask c₀)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (he : e + 8 * N ≤ Z) :
    WP isa (wordLoop 0 shlBody) s fun t => ∃ c : Bool, t.gpr .rbp = VG.Proof.Bignum.X86_64.mask c ∧
      wv t.mem B e N + 2 ^ (64 * N) * c.toNat = 2 * wv s.mem B e N + c₀.toNat ∧
      VG.Proof.Bignum.X86_64.Outside B e (8 * N) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s t → t.cf = s.cf →
      VG.Proof.Rsa.X86_64.ShlInv s B Z e c₀ 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨c₀, (k.gpr (by decide)).trans hbp, by simp [wv]⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN' (VG.Proof.Rsa.X86_64.ShlInv s B Z e c₀) h0
    (fun j _ hj t hI => VG.Proof.Rsa.X86_64.shlStep_ok hbx h12 (by omega) he hj hI)) fun t hI => ?_
  obtain ⟨c, hc, hv⟩ := hI.val
  exact ⟨c, hc, hv, hI.out, hI.keep⟩

/-! ## Selection in place -/

structure SelInv (s₀ : State) (B : Addr) (Z eA eT : Nat) (lt : Bool) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : VG.Proof.Bignum.X86_64.Outside B eA (8 * j) s₀.mem t.mem
  val : wv t.mem B eA j = if lt then wv s₀.mem B eA j else wv s₀.mem B eT j

theorem selStep_ok {s₀ : State} {B : Addr} {Z w eA eT : Nat} {lt : Bool}
    (h8 : s₀.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (hsi : s₀.gpr .rsi = VG.Proof.Bignum.X86_64.off B eT) (hbp : s₀.gpr .rbp = VG.Proof.Bignum.X86_64.mask lt)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 32) (hA : eA + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z)
    (sT : eA + 8 * w ≤ eT ∨ eT + 8 * w ≤ eA) {j : Nat} (hj : j < w) {t : State} (hI : VG.Proof.Rsa.X86_64.SelInv s₀ B Z eA eT lt j t) :
    WP isa (.block (VG.Impl.Rsa.X86_64.Keys.selBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ VG.Proof.Rsa.X86_64.SelInv s₀ B Z eA eT lt (j + 1) t' := by
  have hn := hI.scr.nowrap
  have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans h8
  have tsi : t.gpr .rsi = VG.Proof.Bignum.X86_64.off B eT := (hI.keep.gpr (by decide)).trans hsi
  have tbp : t.gpr .rbp = VG.Proof.Bignum.X86_64.mask lt := (hI.keep.gpr (by decide)).trans hbp
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hx : VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : VG.Proof.Bignum.X86_64.word t.mem B (eT + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem B (eT + 8 * j) := hI.out.word (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t₁ => t₁.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * j))
      (if lt then VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * j) else VG.Proof.Bignum.X86_64.word s₀.mem B (eT + 8 * j))) (by
      unfold VG.Impl.Rsa.X86_64.Keys.selBody
      xrun [State.ea, ix, addr0 t8 hI.r14, addr0 tsi hI.r14, tbp,
        hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eT + 8 * j + 8 ≤ Z by omega),
        hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega), hx, hy, select_mask]) rfl) fun t₁ ⟨hm, k₁⟩ => ?_
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [VG.Proof.Bignum.X86_64.writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hI.val]
    cases lt <;> simp [wv]

/-- `wordLoop 0 selBody` over `N` words: `[r8] := lt ? [r8] : [rsi]`. -/
theorem sel_ok {s : State} {B : Addr} {Z N eA eT : Nat} {lt : Bool} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (hsi : s.gpr .rsi = VG.Proof.Bignum.X86_64.off B eT) (hbp : s.gpr .rbp = VG.Proof.Bignum.X86_64.mask lt)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 N) (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (hA : eA + 8 * N ≤ Z)
    (hT : eT + 8 * N ≤ Z) (sT : eA + 8 * N ≤ eT ∨ eT + 8 * N ≤ eA) :
    WP isa (wordLoop 0 VG.Impl.Rsa.X86_64.Keys.selBody) s fun t =>
      wv t.mem B eA N = (if lt then wv s.mem B eA N else wv s.mem B eT N) ∧
      VG.Proof.Bignum.X86_64.Outside B eA (8 * N) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s t → t.cf = s.cf →
      VG.Proof.Rsa.X86_64.SelInv s B Z eA eT lt 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _, by cases lt <;> rfl⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN' (VG.Proof.Rsa.X86_64.SelInv s B Z eA eT lt) h0
    (fun j _ hj t hI => VG.Proof.Rsa.X86_64.selStep_ok h8 hsi hbp h12 (by omega) hA hT sT hj hI)) fun t hI => ⟨hI.val, hI.out, hI.keep⟩

/-! ## Masked subtraction -/

structure SubMInv (s₀ : State) (B : Addr) (Z eo eA eB : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : VG.Proof.Bignum.X86_64.Outside B eo (8 * j) s₀.mem t.mem
  val : ∃ b : Bool, t.gpr .rbp = VG.Proof.Bignum.X86_64.mask b ∧
    wv t.mem B eo j + (if c then wv s₀.mem B eB j else 0) = wv s₀.mem B eA j + 2 ^ (64 * j) * b.toNat

theorem subMStep_ok {s₀ : State} {B : Addr} {Z w eo eA eB : Nat} {c : Bool}
    (hsi : s₀.gpr .rsi = VG.Proof.Bignum.X86_64.off B eo) (h8 : s₀.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h10 : s₀.gpr .r10 = VG.Proof.Bignum.X86_64.off B eB)
    (h15 : s₀.gpr .r15 = VG.Proof.Bignum.X86_64.mask c) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 32)
    (ho : eo + 8 * w ≤ Z) (hA : eA + 8 * w ≤ Z) (hB : eB + 8 * w ≤ Z)
    (sA : eo ≤ eA ∨ eA + 8 * w ≤ eo) (sB : eo + 8 * w ≤ eB ∨ eB + 8 * w ≤ eo)
    {j : Nat} (hj : j < w) {t : State} (hI : VG.Proof.Rsa.X86_64.SubMInv s₀ B Z eo eA eB c j t) :
    WP isa (.block (subMBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ VG.Proof.Rsa.X86_64.SubMInv s₀ B Z eo eA eB c (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tsi : t.gpr .rsi = VG.Proof.Bignum.X86_64.off B eo := (hI.keep.gpr (by decide)).trans hsi
  have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans h8
  have t10 : t.gpr .r10 = VG.Proof.Bignum.X86_64.off B eB := (hI.keep.gpr (by decide)).trans h10
  have t15 : t.gpr .r15 = VG.Proof.Bignum.X86_64.mask c := (hI.keep.gpr (by decide)).trans h15
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨b, hbp, hval⟩ := hI.val
  have hx : VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : VG.Proof.Bignum.X86_64.word t.mem B (eB + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem B (eB + 8 * j) := hI.out.word (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx, .rbp] (Q := fun t₁ =>
      ∃ b' : Bool, t₁.gpr .rbp = VG.Proof.Bignum.X86_64.mask b' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eo + 8 * j)) r ∧
        r.toNat + (VG.Proof.Bignum.X86_64.word s₀.mem B (eB + 8 * j) &&& VG.Proof.Bignum.X86_64.mask c).toNat + b.toNat =
          (VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * j)).toNat + 2 ^ 64 * b'.toNat) ?_ rfl)
    fun t₁ ⟨⟨b', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold subMBody cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tsi hI.r14, addr0 t8 hI.r14, addr0 t10 hI.r14, hbp, t15, cf_mask,
      hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eB + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega), hx, hy]
    exact ⟨_, rfl, _, rfl, sbb_toNat _ _ _⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  rw [VG.Proof.Bignum.X86_64.and_mask] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨b', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [VG.Proof.Bignum.X86_64.writeW_outside t.mem B r (by omega) x (by omega)]
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
theorem subM_ok {s : State} {B : Addr} {Z N eo eA eB : Nat} {c : Bool} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hsi : s.gpr .rsi = VG.Proof.Bignum.X86_64.off B eo) (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h10 : s.gpr .r10 = VG.Proof.Bignum.X86_64.off B eB)
    (h15 : s.gpr .r15 = VG.Proof.Bignum.X86_64.mask c) (h12 : s.gpr .r12 = BitVec.ofNat 64 N) (hbp : s.gpr .rbp = VG.Proof.Bignum.X86_64.mask false)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (ho : eo + 8 * N ≤ Z) (hA : eA + 8 * N ≤ Z) (hB : eB + 8 * N ≤ Z)
    (sA : eo ≤ eA ∨ eA + 8 * N ≤ eo) (sB : eo + 8 * N ≤ eB ∨ eB + 8 * N ≤ eo) :
    WP isa (wordLoop 0 subMBody) s fun t => ∃ b : Bool, t.gpr .rbp = VG.Proof.Bignum.X86_64.mask b ∧
      wv t.mem B eo N + (if c then wv s.mem B eB N else 0) = wv s.mem B eA N + 2 ^ (64 * N) * b.toNat ∧
      VG.Proof.Bignum.X86_64.Outside B eo (8 * N) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s t → t.cf = s.cf →
      VG.Proof.Rsa.X86_64.SubMInv s B Z eo eA eB c 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by cases c <;> simp [wv]⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN' (VG.Proof.Rsa.X86_64.SubMInv s B Z eo eA eB c) h0
    (fun j _ hj t hI => VG.Proof.Rsa.X86_64.subMStep_ok hsi h8 h10 h15 h12 (by omega) ho hA hB sA sB hj hI)) fun t hI => ?_
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
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : VG.Proof.Bignum.X86_64.Outside B eo (8 * j) s₀.mem t.mem
  val : wv t.mem B eo j * 2 + (VG.Proof.Bignum.X86_64.word s₀.mem B eA).toNat % 2 =
    wv s₀.mem B eA j + 2 ^ (64 * j) * ((VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * j)).toNat % 2)

theorem shrStep_ok {s₀ : State} {B : Addr} {Z w eo eA : Nat}
    (hsi : s₀.gpr .rsi = VG.Proof.Bignum.X86_64.off B eo) (h8 : s₀.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (ho : eo + 8 * w ≤ Z) (hA : eA + 8 * (w + 1) ≤ Z) (sA : eo ≤ eA ∨ eA + 8 * (w + 1) ≤ eo)
    {j : Nat} (hj : j < w) {t : State} (hI : VG.Proof.Rsa.X86_64.ShrInv s₀ B Z eo eA j t) :
    WP isa (.block (shrBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ VG.Proof.Rsa.X86_64.ShrInv s₀ B Z eo eA (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tsi : t.gpr .rsi = VG.Proof.Bignum.X86_64.off B eo := (hI.keep.gpr (by decide)).trans hsi
  have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans h8
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hx : VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * j + 8) = VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * j + 8) :=
    hI.out.word (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t₁ => ∃ r : BitVec 64,
      t₁.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eo + 8 * j)) r ∧
      r.toNat = (VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * j)).toNat / 2 + 2 ^ 63 * ((VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * j + 8)).toNat % 2))
      ?_ rfl) fun t₁ ⟨⟨r, hm, hr⟩, k₁⟩ => ?_
  · unfold shrBody
    xrun [State.ea, ix, addr0 tsi hI.r14, addr0 t8 hI.r14, addr8 t8 hI.r14,
      hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eA + 8 * j + 8 + 8 ≤ Z by omega),
      hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega), hx, hy]
    exact ⟨_, rfl, VG.Proof.Rsa.X86_64.shr_word _ _⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [VG.Proof.Bignum.X86_64.writeW_outside t.mem B r (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hr]
    have hv := hI.val
    simp only [wv]
    rw [pow64_succ, show eA + 8 * (j + 1) = eA + 8 * j + 8 by omega]
    have h2 := Nat.div_add_mod (VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * j)).toNat 2
    generalize (VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * j)).toNat = x at h2 hv ⊢
    generalize (VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * j + 8)).toNat % 2 = y
    generalize 2 ^ (64 * j) = P at hv ⊢
    have : (2 : Nat) ^ 64 = 2 * 2 ^ 63 := by decide
    rw [this]
    grind

/-- `wordLoop 0 shrBody` over `N` words: `2 [rsi] + a₀ = A + 2^(64 N) a_N`
for the `N + 1` words `A` at `r8`, the low bit `a₀` of `A` and the low bit
`a_N` of its word `N`. -/
theorem shr_ok {s : State} {B : Addr} {Z N eo eA : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hsi : s.gpr .rsi = VG.Proof.Bignum.X86_64.off B eo) (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h12 : s.gpr .r12 = BitVec.ofNat 64 N)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (ho : eo + 8 * N ≤ Z) (hA : eA + 8 * (N + 1) ≤ Z)
    (sA : eo ≤ eA ∨ eA + 8 * (N + 1) ≤ eo) :
    WP isa (wordLoop 0 shrBody) s fun t =>
      wv t.mem B eo N * 2 + (VG.Proof.Bignum.X86_64.word s.mem B eA).toNat % 2 =
        wv s.mem B eA N + 2 ^ (64 * N) * ((VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * N)).toNat % 2) ∧
      VG.Proof.Bignum.X86_64.Outside B eo (8 * N) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s t → t.cf = s.cf →
      VG.Proof.Rsa.X86_64.ShrInv s B Z eo eA 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _, by simp [wv]⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN' (VG.Proof.Rsa.X86_64.ShrInv s B Z eo eA) h0
    (fun j _ hj t hI => VG.Proof.Rsa.X86_64.shrStep_ok hsi h8 h12 (by omega) ho hA sA hj hI)) fun t hI => ⟨hI.val, hI.out, hI.keep⟩

/-! ## Masked swap -/

theorem cswap_x (a b : BitVec 64) (c : Bool) : a ^^^ ((a ^^^ b) &&& VG.Proof.Bignum.X86_64.mask c) = if c then b else a := by
  cases c
  · simp [mask_false]
  · simp only [mask_true, BitVec.and_allOnes, ite_true, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem cswap_y (a b : BitVec 64) (c : Bool) : b ^^^ ((a ^^^ b) &&& VG.Proof.Bignum.X86_64.mask c) = if c then a else b := by
  cases c
  · simp [mask_false]
  · simp only [mask_true, BitVec.and_allOnes, ite_true]
    rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- After `j` words of `cswapBody` on `X` at `eX` and `Y` at `eY`. -/
structure CsInv (s₀ : State) (B : Addr) (Z eX eY : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : ∀ x, (VG.Proof.Bignum.X86_64.ofs B x < eX ∨ eX + 8 * j ≤ VG.Proof.Bignum.X86_64.ofs B x) → (VG.Proof.Bignum.X86_64.ofs B x < eY ∨ eY + 8 * j ≤ VG.Proof.Bignum.X86_64.ofs B x) → t.mem x = s₀.mem x
  vx : ∀ i < j, VG.Proof.Bignum.X86_64.word t.mem B (eX + 8 * i) =
    if c then VG.Proof.Bignum.X86_64.word s₀.mem B (eY + 8 * i) else VG.Proof.Bignum.X86_64.word s₀.mem B (eX + 8 * i)
  vy : ∀ i < j, VG.Proof.Bignum.X86_64.word t.mem B (eY + 8 * i) =
    if c then VG.Proof.Bignum.X86_64.word s₀.mem B (eX + 8 * i) else VG.Proof.Bignum.X86_64.word s₀.mem B (eY + 8 * i)

theorem csStep_ok {s₀ : State} {B : Addr} {Z w eX eY : Nat} {c : Bool}
    (hbx : s₀.gpr .rbx = VG.Proof.Bignum.X86_64.off B eX) (h10 : s₀.gpr .r10 = VG.Proof.Bignum.X86_64.off B eY) (h15 : s₀.gpr .r15 = VG.Proof.Bignum.X86_64.mask c)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 32) (hX : eX + 8 * w ≤ Z) (hY : eY + 8 * w ≤ Z)
    (sXY : eX + 8 * w ≤ eY ∨ eY + 8 * w ≤ eX) {j : Nat} (hj : j < w) {t : State} (hI : VG.Proof.Rsa.X86_64.CsInv s₀ B Z eX eY c j t) :
    WP isa (.block (cswapBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ VG.Proof.Rsa.X86_64.CsInv s₀ B Z eX eY c (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off B eX := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = VG.Proof.Bignum.X86_64.off B eY := (hI.keep.gpr (by decide)).trans h10
  have t15 : t.gpr .r15 = VG.Proof.Bignum.X86_64.mask c := (hI.keep.gpr (by decide)).trans h15
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hx : VG.Proof.Bignum.X86_64.word t.mem B (eX + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem B (eX + 8 * j) :=
    Mem.readW_congr fun b hb => hI.out _ (by rw [VG.Proof.Bignum.X86_64.ofs_off B (by omega)]; omega)
      (by rw [VG.Proof.Bignum.X86_64.ofs_off B (by omega)]; omega)
  have hy : VG.Proof.Bignum.X86_64.word t.mem B (eY + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem B (eY + 8 * j) :=
    Mem.readW_congr fun b hb => hI.out _ (by rw [VG.Proof.Bignum.X86_64.ofs_off B (by omega)]; omega)
      (by rw [VG.Proof.Bignum.X86_64.ofs_off B (by omega)]; omega)
  have hy' : ∀ v : BitVec 64, (t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eX + 8 * j)) v).readW (VG.Proof.Bignum.X86_64.off B (eY + 8 * j)) 64 =
      VG.Proof.Bignum.X86_64.word s₀.mem B (eY + 8 * j) := fun v =>
    ((VG.Proof.Bignum.X86_64.writeW_outside t.mem B v (by omega)).word (by omega) (by omega)).trans hy
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t₁ => t₁.mem =
      (t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eX + 8 * j)) (if c then VG.Proof.Bignum.X86_64.word s₀.mem B (eY + 8 * j) else VG.Proof.Bignum.X86_64.word s₀.mem B (eX + 8 * j))).writeW
        (VG.Proof.Bignum.X86_64.off B (eY + 8 * j)) (if c then VG.Proof.Bignum.X86_64.word s₀.mem B (eX + 8 * j) else VG.Proof.Bignum.X86_64.word s₀.mem B (eY + 8 * j))) (by
      unfold cswapBody
      xrun [State.ea, ix, addr0 tbx hI.r14, addr0 t10 hI.r14, t15,
        hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eY + 8 * j + 8 ≤ Z by omega),
        hI.scr.st (show eX + 8 * j + 8 ≤ Z by omega), hI.scr.st (show eY + 8 * j + 8 ≤ Z by omega), hx, hy, hy',
        VG.Proof.Rsa.X86_64.cswap_x, VG.Proof.Rsa.X86_64.cswap_y]) rfl) fun t₁ ⟨hm, k₁⟩ => ?_
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside t.mem B (if c then VG.Proof.Bignum.X86_64.word s₀.mem B (eY + 8 * j) else VG.Proof.Bignum.X86_64.word s₀.mem B (eX + 8 * j))
    (d := eX + 8 * j) (by omega)
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside (t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eX + 8 * j))
    (if c then VG.Proof.Bignum.X86_64.word s₀.mem B (eY + 8 * j) else VG.Proof.Bignum.X86_64.word s₀.mem B (eX + 8 * j))) B
    (if c then VG.Proof.Bignum.X86_64.word s₀.mem B (eX + 8 * j) else VG.Proof.Bignum.X86_64.word s₀.mem B (eY + 8 * j)) (d := eY + 8 * j) (by omega)
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_, ?_, ?_⟩
  · intro x h1 h2
    rw [hm', hm, o2 x (by omega), o1 x (by omega)]
    exact hI.out x (by omega) (by omega)
  · intro i hi
    rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [o2.word (by omega) (by omega), o1.word (by omega) (by omega)]; exact hI.vx i hi
    · rw [o2.word (by omega) (by omega), VG.Proof.Bignum.X86_64.word_writeW_self]
  · intro i hi
    rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [o2.word (by omega) (by omega), o1.word (by omega) (by omega)]; exact hI.vy i hi
    · rw [VG.Proof.Bignum.X86_64.word_writeW_self]

/-- `wordLoop 0 cswapBody` over `N` words: `[rbx]` and `[r10]` swapped if `c`. -/
theorem cswap_ok {s : State} {B : Addr} {Z N eX eY : Nat} {c : Bool} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hbx : s.gpr .rbx = VG.Proof.Bignum.X86_64.off B eX) (h10 : s.gpr .r10 = VG.Proof.Bignum.X86_64.off B eY) (h15 : s.gpr .r15 = VG.Proof.Bignum.X86_64.mask c)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 N) (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (hX : eX + 8 * N ≤ Z)
    (hY : eY + 8 * N ≤ Z) (sXY : eX + 8 * N ≤ eY ∨ eY + 8 * N ≤ eX) :
    WP isa (wordLoop 0 cswapBody) s fun t =>
      wv t.mem B eX N = (if c then wv s.mem B eY N else wv s.mem B eX N) ∧
      wv t.mem B eY N = (if c then wv s.mem B eX N else wv s.mem B eY N) ∧
      Frm B [(eX, 8 * N), (eY, 8 * N)] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s t → t.cf = s.cf →
      VG.Proof.Rsa.X86_64.CsInv s B Z eX eY c 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, fun x _ _ => by rw [hm], fun i hi => absurd hi (by omega),
      fun i hi => absurd hi (by omega)⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN' (VG.Proof.Rsa.X86_64.CsInv s B Z eX eY c) h0
    (fun j _ hj t hI => VG.Proof.Rsa.X86_64.csStep_ok hbx h10 h15 h12 (by omega) hX hY sXY hj hI)) fun t hI => ?_
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
theorem sub_ok {s : State} {B : Addr} {Z N eA eN eT : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h10 : s.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN) (hsi : s.gpr .rsi = VG.Proof.Bignum.X86_64.off B eT)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 N) (hbp : s.gpr .rbp = VG.Proof.Bignum.X86_64.mask false) (hN : 1 ≤ N) (hN' : N < 2 ^ 31)
    (hA : eA + 8 * N ≤ Z) (hNz : eN + 8 * N ≤ Z) (hT : eT + 8 * N ≤ Z)
    (sA : eT + 8 * N ≤ eA ∨ eA + 8 * N ≤ eT) (sN : eT + 8 * N ≤ eN ∨ eN + 8 * N ≤ eT) :
    WP isa (wordLoop 0 subBody) s fun t => ∃ c : Bool, t.gpr .rbp = VG.Proof.Bignum.X86_64.mask c ∧
      wv t.mem B eT N + wv s.mem B eN N = wv s.mem B eA N + 2 ^ (64 * N) * c.toNat ∧
      VG.Proof.Bignum.X86_64.Outside B eT (8 * N) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s t → t.cf = s.cf →
      SubInv s B Z eA eN eT 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by simp [wv]⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN' (SubInv s B Z eA eN eT) h0
    (fun j _ hj t hI => subStep_ok h8 h10 hsi h12 (by omega) hA hNz hT sA sN hj hI)) fun t hI => ?_
  obtain ⟨c, hc, hv⟩ := hI.val
  exact ⟨c, hc, hv, hI.out, hI.keep⟩

/-- `wordLoop 0 addMBody` over `N` words: `[rbx] := ([r10] & mask c) + [r8]`,
its carry in `rbp`. -/
theorem addM_ok {s : State} {B : Addr} {Z N eo eN eA : Nat} {c : Bool} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hbx : s.gpr .rbx = VG.Proof.Bignum.X86_64.off B eo) (h10 : s.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN) (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA)
    (h15 : s.gpr .r15 = VG.Proof.Bignum.X86_64.mask c) (h12 : s.gpr .r12 = BitVec.ofNat 64 N) (hbp : s.gpr .rbp = VG.Proof.Bignum.X86_64.mask false)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (ho : eo + 8 * N ≤ Z) (hNz : eN + 8 * N ≤ Z) (hA : eA + 8 * N ≤ Z)
    (sN : eN + 8 * N ≤ eo ∨ eo + 8 * N ≤ eN) (sA : eA + 8 * N ≤ eo ∨ eo + 8 * N ≤ eA) :
    WP isa (wordLoop 0 addMBody) s fun t => ∃ c' : Bool, t.gpr .rbp = VG.Proof.Bignum.X86_64.mask c' ∧
      wv t.mem B eo N + 2 ^ (64 * N) * c'.toNat = (if c then wv s.mem B eN N else 0) + wv s.mem B eA N ∧
      VG.Proof.Bignum.X86_64.Outside B eo (8 * N) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s t → t.cf = s.cf →
      MaInv s B Z eo eN eA c 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by cases c <;> simp [wv]⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN' (MaInv s B Z eo eN eA c) h0
    (fun j _ hj t hI => maStep_ok hbx h10 h8 h15 h12 (by omega) ho hNz hA sN sA hj hI)) fun t hI => ?_
  obtain ⟨c', hc, hv⟩ := hI.val
  exact ⟨c', hc, hv, hI.out, hI.keep⟩

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.Div`. -/
section

/-!
# RSA private keys on x86-64: the division

`divStep`, one step of `divmod`, is `VG.Proof.Rsa.divStep` on the arrays
(`divStepCode_ok`): the remainder `R` (`w + 1` words) and the register `Q`
(`w` words), while `R` is below the divisor; `divmod` is `KeyMath.divIter`
for `64 w` steps from `(0, Q)` (`divmod_ok`): the remainder and the
quotient (`divIter_done`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

theorem slot_lt {w j K : Nat} (h : j < K) : VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w K := by
  unfold VG.Proof.Bignum.X86_64.slot
  have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ K by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

/-- The byte range of array `j`. -/
abbrev ar (w j : Nat) : Nat × Nat := (VG.Proof.Bignum.X86_64.slot w j, 8 * (w + 2))

theorem mask_add_one (c : Bool) : (VG.Proof.Bignum.X86_64.mask c + 1).toNat = if c then 0 else 1 := by cases c <;> decide

/-- An even word plus a bit does not carry. -/
theorem add_bit {x r : BitVec 64} (hx : x.toNat % 2 = 0) (hr : r.toNat ≤ 1) : (x + r).toNat = x.toNat + r.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

/-- `2 Q`'s carry out of `K` bits is `Q`'s top bit. -/
theorem two_mul_div {Q K : Nat} (hK : 1 ≤ K) : 2 * Q / 2 ^ K = Q / 2 ^ (K - 1) := by
  rw [show 2 ^ K = 2 * 2 ^ (K - 1) by rw [← Nat.pow_succ']; congr 1; omega, Nat.mul_div_mul_left _ _ (by decide)]

/-- A shift left of `[q]` (`w` words) into `[r]` (`w + 1` words). -/
theorem divShift_ok {s : State} {B : Addr} {Z w : Nat} {iQ iR : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z) (hQ : iQ < 16) (hR : iR < 16) (hQR : iQ ≠ iR) :
    WP isa (seqs (divShiftP iQ iR)) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 (w + 1) ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w = 2 * wv s.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w % 2 ^ (64 * w) ∧
      (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) < 2 ^ (64 * w) →
        wv t.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) =
          2 * wv s.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) + wv s.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w / 2 ^ (64 * w - 1)) ∧
      Frm B [VG.Proof.Rsa.X86_64.ar w iQ, VG.Proof.Rsa.X86_64.ar w iR] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rbx, .rbp, .r12, .r14] s t := by
  have hn := hs.nowrap
  have sQ := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hQ) hZ
  have sR := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hR) hZ
  have sp := VG.Proof.Bignum.X86_64.slot_sep (w := w) hQR
  simp only [divShiftP, seqs]
  -- `rbp := 0` and `rbx := Q`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧
    t.mem = s.mem) (by xrun) rfl)
    fun s₀ ⟨⟨hbp₀, m₀⟩, k₀⟩ => WP.mono (VG.Proof.Rsa.X86_64.base_ok iQ (r := .rbx) (by decide) ((k₀.gpr (by decide)).trans hdi)
      ((k₀.gpr (by decide)).trans h9)) fun s₁ ⟨hbx₁, m₁, k₁⟩ => ?_))
  have k01 := k₀.trans k₁
  -- `Q := 2 Q`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.shl_ok (hs.congr k01.2.2) hbx₁ ((k01.gpr (by decide)).trans h12)
    ((k₁.gpr (by decide)).trans hbp₀) hw1 (by omega) (by omega)) fun s₂ ⟨c₁, hc₁, hv₂, ho₂, k₂⟩ => ?_)
  have k02 := k01.trans k₂
  rw [m₁, m₀] at hv₂ ho₂
  simp only [Bool.toNat_false, Nat.add_zero] at hv₂
  -- `rbx := R`, `r12 := w + 1`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (VG.Proof.Rsa.X86_64.base_ok iR (r := .rbx) (by decide) ((k02.gpr (by decide)).trans hdi)
      ((k02.gpr (by decide)).trans h9)) fun s₃ ⟨hbx₃, m₃, k₃⟩ => WP.mono (WP.keep [.r12]
      (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (w + 1) ∧ t.mem = s₃.mem ∧
        t.gpr .rbp = s₃.gpr .rbp) (by
        xrun [(k₃.gpr (by decide) : s₃.gpr .r12 = _), (k02.gpr (by decide) : s₂.gpr .r12 = _), h12]
        exact ofNat_add_one w) rfl)
    fun s₄ ⟨⟨h12₄, m₄, hbp₄⟩, k₄⟩ => ?_))
  have k04 := (k02.trans k₃).trans k₄
  -- `R := 2 R + c₁`.
  refine WP.mono (VG.Proof.Rsa.X86_64.shl_ok (c₀ := c₁) (hs.congr k04.2.2) ((k₄.gpr (by decide)).trans hbx₃) h12₄
    (by rw [hbp₄, (k₃.gpr (by decide) : s₃.gpr .rbp = _)]; exact hc₁) (by omega) (by omega) (by omega))
    fun t ⟨c₂, _, hv, ho, k₅⟩ => ?_
  rw [m₄, m₃] at hv ho
  have hQ' : wv t.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w = wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w :=
    ho.wv (by omega) (by omega)
  have hR' : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) :=
    ho₂.wv (by omega) (by omega)
  have hQlt := wv_lt s₂.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w
  have hQs := wv_lt s.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w
  have hc1 : c₁.toNat = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w / 2 ^ (64 * w - 1) := by
    rw [← VG.Proof.Rsa.X86_64.two_mul_div (by omega), ← hv₂, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hQlt]
    simp
  refine ⟨(k₅.gpr (by decide)).trans h12₄, ?_, fun hRlt => ?_, ?_, ((k04.trans k₅).mono (by simp))⟩
  · rw [hQ', ← hv₂, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hQlt]
  · rw [hR'] at hv
    have hc1' : c₁.toNat ≤ 1 := Bool.toNat_le _
    have : 2 * wv s.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) + c₁.toNat < 2 ^ (64 * (w + 1)) := by
      rw [show 64 * (w + 1) = 64 * w + 64 by omega, Nat.pow_add]
      have : 2 ^ (64 * w) * 2 ≤ 2 ^ (64 * w) * 2 ^ 64 := Nat.mul_le_mul_left _ (by decide)
      omega
    have hc2 : c₂.toNat = 0 := by
      rcases Bool.toNat_le c₂ |> Nat.le_one_iff_eq_zero_or_eq_one.mp with h | h
      · exact h
      · rw [h] at hv; omega
    rw [hc2] at hv
    omega
  · intro x hx
    have a := hx (VG.Proof.Rsa.X86_64.ar w iQ) (by simp)
    have b := hx (VG.Proof.Rsa.X86_64.ar w iR) (by simp)
    rw [ho x (by dsimp only at b; omega), ho₂ x (by dsimp only at a; omega)]

theorem sx0 : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide

theorem ofNat_succ_sub_one (w : Nat) : BitVec.ofNat 64 (w + 1) - 1 = BitVec.ofNat 64 w := by
  rw [← ofNat_add_one, BitVec.add_sub_cancel]

/-- Three bases. -/
theorem base3_ok {s : State} {B : Addr} {w : Nat} (i j k : Nat) {r₁ r₂ r₃ : Reg} (h₁ : r₁ ≠ .r9) (h₂ : r₂ ≠ .r9)
    (h₃ : r₃ ≠ .r9) (h₁₂ : r₂ ≠ r₁) (h₁₃ : r₃ ≠ r₁) (h₂₃ : r₃ ≠ r₂) (hdi : s.gpr .rdi = B)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) (hr1 : r₁ ≠ .rdi) (hr2 : r₂ ≠ .rdi) :
    WP isa (.block (base i r₁ ++ (base j r₂ ++ base k r₃))) s fun t =>
      t.gpr r₁ = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w i) ∧ t.gpr r₂ = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j) ∧ t.gpr r₃ = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w k) ∧ t.mem = s.mem ∧
        VG.Proof.MlKem.X86_64.Keep [r₁, r₂, r₃] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok i h₁ hdi h9) fun t₁ ⟨e₁, m₁, k₁⟩ => ?_
  have g1 : ∀ r, r ≠ r₁ → t₁.gpr r = s.gpr r := fun r h => k₁.gpr (by simp [h])
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok j h₂ ((g1 _ (Ne.symm hr1)).trans hdi) ((g1 _ (Ne.symm h₁)).trans h9))
    fun t₂ ⟨e₂, m₂, k₂⟩ => ?_
  have g2 : ∀ r, r ≠ r₂ → t₂.gpr r = t₁.gpr r := fun r h => k₂.gpr (by simp [h])
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok k h₃ ((g2 _ (Ne.symm hr2)).trans ((g1 _ (Ne.symm hr1)).trans hdi))
    ((g2 _ (Ne.symm h₂)).trans ((g1 _ (Ne.symm h₁)).trans h9))) fun t ⟨e₃, m₃, k₃⟩ => ?_
  have g3 : ∀ r, r ≠ r₃ → t.gpr r = t₂.gpr r := fun r h => k₃.gpr (by simp [h])
  refine ⟨(g3 _ (Ne.symm h₁₃)).trans ((g2 _ (Ne.symm h₁₂)).trans e₁), (g3 _ (Ne.symm h₂₃)).trans e₂, e₃,
    m₃.trans (m₂.trans m₁), ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- The subtraction of the divisor and the selection: `[r] := [r] - [d]` if
it does not borrow (`b`), over `w + 1` words. -/
theorem divSub_ok {s : State} {B : Addr} {Z w : Nat} {iR iD iT : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 (w + 1)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16)
    (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT) :
    WP isa (seqs (divSubP iR iD iT)) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 (w + 1) ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.mask (decide (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) < wv s.mem B (VG.Proof.Bignum.X86_64.slot w iD) w)) ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) = (if wv s.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) < wv s.mem B (VG.Proof.Bignum.X86_64.slot w iD) w then
        wv s.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) else wv s.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) - wv s.mem B (VG.Proof.Bignum.X86_64.slot w iD) w) ∧
      Frm B [VG.Proof.Rsa.X86_64.ar w iR, VG.Proof.Rsa.X86_64.ar w iT] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rbp, .r8, .r10, .rsi, .r12, .r14] s t := by
  have hn := hs.nowrap
  have sR := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hR) hZ
  have sD := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hD) hZ
  have sT := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hT) hZ
  have pRD := VG.Proof.Bignum.X86_64.slot_sep (w := w) dRD
  have pRT := VG.Proof.Bignum.X86_64.slot_sep (w := w) dRT
  have pDT := VG.Proof.Bignum.X86_64.slot_sep (w := w) dDT
  simp only [divSubP, seqs, List.append_assoc]
  -- `r12 := w`, `rbp := 0`, the bases.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.r12, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t.mem = s.mem) (by xrun [h12, VG.Proof.Rsa.X86_64.ofNat_succ_sub_one]) rfl)
    fun s₀ ⟨⟨h12₀, hbp₀, m₀⟩, k₀⟩ => ?_))
  refine WP.mono (VG.Proof.Rsa.X86_64.base3_ok iR iD iT (r₁ := .r8) (r₂ := .r10) (r₃ := .rsi) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ((k₀.gpr (by decide)).trans hdi) ((k₀.gpr (by decide)).trans h9)
    (by decide) (by decide)) fun s₁ ⟨h8, h10, hsi, m₁, k₁⟩ => ?_
  have k01 := k₀.trans k₁
  -- `T := R - D` over `w` words.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.sub_ok (hs.congr k01.2.2) h8 h10 hsi ((k₁.gpr (by decide)).trans h12₀)
    ((k₁.gpr (by decide)).trans hbp₀) hw1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun s₂ ⟨b₁, hb₁, hv₂, ho₂, k₂⟩ => ?_)
  rw [m₁, m₀] at hv₂ ho₂
  have k02 := k01.trans k₂
  have hs₂ := hs.congr k02.2.2
  have hR₂ : VG.Proof.Bignum.X86_64.word s₂.mem B (VG.Proof.Bignum.X86_64.slot w iR + 8 * w) = VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w iR + 8 * w) := ho₂.word (by omega) (by omega)
  -- The top word: `T_w := R_w - b₁`, and `rbp` its borrow.
  refine WP.seq (WP.mono (WP.keep [.rax, .rbp, .r12] (Q := fun t =>
      ∃ b₂ : Bool, t.gpr .rbp = VG.Proof.Bignum.X86_64.mask b₂ ∧ t.gpr .r12 = BitVec.ofNat 64 (w + 1) ∧ ∃ r : BitVec 64,
        t.mem = s₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w iT + 8 * w)) r ∧
        r.toNat + 0 + b₁.toNat = (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w iR + 8 * w)).toNat + 2 ^ 64 * b₂.toNat) (by
      unfold cfFromRbp cfToRbp
      have e8 : s₂.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w iR) := (k₂.gpr (by decide)).trans h8
      have esi : s₂.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w iT) := (k₂.gpr (by decide)).trans hsi
      have e12 : s₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h12₀)
      xrun [State.ea, ix, e8, esi, e12, addr0 (b := VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w iR)) rfl rfl,
        addr0 (b := VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w iT)) rfl rfl, hb₁, cf_mask, hs₂.ld (show VG.Proof.Bignum.X86_64.slot w iR + 8 * w + 8 ≤ Z by omega),
        hs₂.st (show VG.Proof.Bignum.X86_64.slot w iT + 8 * w + 8 ≤ Z by omega), hR₂, ofNat_add_one, e12, VG.Proof.Rsa.X86_64.sx0]
      refine ⟨_, rfl, _, rfl, ?_⟩
      have := sbb_toNat (Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w iR + 8 * w)) 0 b₁
      simpa using this) rfl) fun s₃ ⟨⟨b₂, hb₂, h12₃, r, m₃, hr⟩, k₃⟩ => ?_)
  have k03 := k02.trans k₃
  -- The value of `T` over `w + 1` words.
  have hT : wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w iT) (w + 1) + wv s.mem B (VG.Proof.Bignum.X86_64.slot w iD) w =
      wv s.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) + 2 ^ (64 * (w + 1)) * b₂.toNat := by
    rw [m₃, wv_writeW_top _ _ _ _ _ (by omega), wv, pow64_succ]
    simp only [Bignum.X86_64.word] at hr ⊢
    grind
  have hb : b₂ = decide (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) < wv s.mem B (VG.Proof.Bignum.X86_64.slot w iD) w) :=
    lt_of_borrow (wv_lt _ _ _ _) hT
  -- The selection.
  have k13 := k₂.trans k₃
  refine WP.mono (VG.Proof.Rsa.X86_64.sel_ok (hs.congr k03.2.2) ((k13.gpr (by decide)).trans h8) ((k13.gpr (by decide)).trans hsi)
    hb₂ h12₃ (by omega) (by omega) (by omega) (by omega) (by omega)) fun t ⟨hv, ho, k₄⟩ => ?_
  have hR₃ : wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) := by
    rw [m₃, (VG.Proof.Bignum.X86_64.writeW_outside s₂.mem B r (by omega)).wv (by omega) (by omega)]
    exact ho₂.wv (by omega) (by omega)
  refine ⟨(k₄.gpr (by decide)).trans h12₃, (k₄.gpr (by decide)).trans (hb ▸ hb₂), ?_, ?_,
    (k03.trans k₄).mono (by simp)⟩
  · rw [hv, hR₃]
    cases b₂
    · simp only [Bool.false_eq_true, ite_false]
      have : ¬ wv s.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) < wv s.mem B (VG.Proof.Bignum.X86_64.slot w iD) w := by simpa using hb
      simp only [this, ite_false]
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hT
      omega
    · have : wv s.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) < wv s.mem B (VG.Proof.Bignum.X86_64.slot w iD) w := by simpa using hb
      simp [this]
  · intro x hx
    have a := hx (VG.Proof.Rsa.X86_64.ar w iR) (by simp)
    have b := hx (VG.Proof.Rsa.X86_64.ar w iT) (by simp)
    dsimp only at a b
    rw [ho x (by omega), m₃, VG.Proof.Bignum.X86_64.writeW_outside s₂.mem B r (by omega) x (by omega), ho₂ x (by omega)]

/-- A number of `w ≥ 1` words is its low word and the `w - 1` above. -/
theorem wv_low {m : Mem} {B : Addr} {e w : Nat} (hw : 1 ≤ w) :
    wv m B e w = (VG.Proof.Bignum.X86_64.word m B e).toNat + 2 ^ 64 * wv m B (e + 8) (w - 1) := by
  rw [show w = 1 + (w - 1) by omega, wv_add, show 1 + (w - 1) - 1 = w - 1 by omega]
  simp [wv]

/-- The quotient's new bit (`rbp` the mask of the borrow `b`) into word 0 of
`[q]`, `r12 := w`, and the step counter. -/
theorem divBit_ok {s : State} {B : Addr} {Z w k : Nat} {iQ : Nat} {b : Bool} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 (w + 1))
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) (hbp : s.gpr .rbp = VG.Proof.Bignum.X86_64.mask b)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 k) (h11 : s.gpr .r11 = BitVec.ofNat 64 (64 * w))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hk : k < 64 * w) (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z) (hQ : iQ < 16)
    (hev : (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w iQ)).toNat % 2 = 0) :
    WP isa (.block (divBitP iQ)) s fun t =>
      t.zf = some (decide (k + 1 = 64 * w)) ∧ t.gpr .r13 = BitVec.ofNat 64 (k + 1) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w + (if b then 0 else 1) ∧
      Frm B [VG.Proof.Rsa.X86_64.ar w iQ] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rbx, .rdx, .r12, .r13] s t := by
  have hn := hs.nowrap
  have sQ := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hQ) hZ
  rw [divBitP, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12, .rax] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      (t.gpr .rax).toNat = (if b then 0 else 1) ∧ t.mem = s.mem) (by
      xrun [h12, hbp, VG.Proof.Rsa.X86_64.ofNat_succ_sub_one]
      exact VG.Proof.Rsa.X86_64.mask_add_one b) rfl) fun s₁ ⟨⟨h12₁, hax₁, m₁⟩, k₁⟩ => ?_
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok iQ (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans hdi)
    ((k₁.gpr (by decide)).trans h9)) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  have e13 : s₂.gpr .r13 = BitVec.ofNat 64 k := (k12.gpr (by decide)).trans h13
  have e11 : s₂.gpr .r11 = BitVec.ofNat 64 (64 * w) := (k12.gpr (by decide)).trans h11
  have eax : (s₂.gpr .rax).toNat = if b then 0 else 1 := by rw [(k₂.gpr (by decide) : s₂.gpr .rax = _)]; exact hax₁
  have hw0 : VG.Proof.Bignum.X86_64.word s₂.mem B (VG.Proof.Bignum.X86_64.slot w iQ) = VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w iQ) := by rw [m₂, m₁]
  refine WP.mono (WP.keep [.rdx, .r13] (Q := fun t => t.zf = some (decide (k + 1 = 64 * w)) ∧
      t.gpr .r13 = BitVec.ofNat 64 (k + 1) ∧
      t.mem = s₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w iQ)) (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w iQ) + s₂.gpr .rax)) (by
      xrun [State.ea, at0, hbx, e13, e11, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        hs₂.ld (d := VG.Proof.Bignum.X86_64.slot w iQ) (by omega), hs₂.st (d := VG.Proof.Bignum.X86_64.slot w iQ) (by omega), hw0, ofNat_add_one,
        ofNat_sub_beq (show k + 1 < 2 ^ 64 by omega) (show 64 * w < 2 ^ 64 by omega)]) rfl)
    fun t ⟨⟨hz, h13t, mt⟩, k₃⟩ => ?_
  have hax : (s₂.gpr .rax).toNat ≤ 1 := by rw [eax]; split <;> omega
  refine ⟨hz, h13t, (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12₁), ?_, ?_,
    (k12.trans k₃).mono (by simp)⟩
  · rw [mt, VG.Proof.Rsa.X86_64.wv_low hw1, VG.Proof.Rsa.X86_64.wv_low (m := s.mem) hw1, VG.Proof.Bignum.X86_64.word_writeW_self, VG.Proof.Rsa.X86_64.add_bit hev hax, eax,
      (VG.Proof.Bignum.X86_64.writeW_outside s₂.mem B _ (by omega)).wv (Or.inr (by omega)) (by omega), m₂, m₁]
    omega
  · intro x hx
    have a := hx (VG.Proof.Rsa.X86_64.ar w iQ) (by simp)
    dsimp only at a
    rw [mt, VG.Proof.Bignum.X86_64.writeW_outside s₂.mem B _ (by omega) x (by omega), m₂, m₁]

/-- The registers `divStep` and `inverse`'s step may change. -/
def stepRegs : List Reg := [.rax, .rbx, .rdx, .rsi, .rbp, .r8, .r10, .r12, .r13, .r14, .r15]

/-- One step of `divmod`: `VG.Proof.Rsa.divStep` while the remainder is below the
divisor. -/
theorem divStepCode_ok {s : State} {B : Addr} {Z w k : Nat} {iQ iR iD iT : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h13 : s.gpr .r13 = BitVec.ofNat 64 k) (h11 : s.gpr .r11 = BitVec.ofNat 64 (64 * w))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hk : k < 64 * w) (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z)
    (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16) (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT)
    (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.divStep iQ iR iD iT) s fun t =>
      t.zf = some (decide (k + 1 = 64 * w)) ∧ t.gpr .r13 = BitVec.ofNat 64 (k + 1) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ Frm B [VG.Proof.Rsa.X86_64.ar w iQ, VG.Proof.Rsa.X86_64.ar w iR, VG.Proof.Rsa.X86_64.ar w iT] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep VG.Proof.Rsa.X86_64.stepRegs s t ∧
      (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) < wv s.mem B (VG.Proof.Bignum.X86_64.slot w iD) w →
        (wv t.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1), wv t.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w) =
          VG.Proof.Rsa.divStep (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iD) w) (64 * w)
            (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1), wv s.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w)) := by
  have hn := hs.nowrap
  have sQ := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hQ) hZ
  have sR := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hR) hZ
  have sD := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hD) hZ
  have sT := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hT) hZ
  have pQR := VG.Proof.Bignum.X86_64.slot_sep (w := w) dQR
  have pQD := VG.Proof.Bignum.X86_64.slot_sep (w := w) dQD
  have pQT := VG.Proof.Bignum.X86_64.slot_sep (w := w) dQT
  have pRD := VG.Proof.Bignum.X86_64.slot_sep (w := w) dRD
  have pRT := VG.Proof.Bignum.X86_64.slot_sep (w := w) dRT
  rw [VG.Impl.Rsa.X86_64.Keys.divStep]
  refine wp_seqs_append (by simp [divShiftP]) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.divShift_ok hs hdi h12 h9 hw1 hw hZ hQ hR dQR)
    fun s₁ ⟨h12₁, hQ₁, hR₁, f₁, k₁⟩ => ?_)
  refine wp_seqs_append (by simp [divSubP]) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.divSub_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi)
    h12₁ ((k₁.gpr (by decide)).trans h9) hw1 hw hZ hR hD hT dRD dRT (by omega)) fun s₂ ⟨h12₂, hbp₂, hR₂, f₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have hD₁ : wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w iD) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iD) w :=
    f₁.wv_eq (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega)
  have hQ₂ : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w = wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w :=
    f₂.wv_eq (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega)
  have hQ2' : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w = 2 * wv s.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w % 2 ^ (64 * w) := hQ₂.trans hQ₁
  have hev : (VG.Proof.Bignum.X86_64.word s₂.mem B (VG.Proof.Bignum.X86_64.slot w iQ)).toNat % 2 = 0 := by
    have d1 : 2 ∣ 2 ^ (64 * w) := ⟨2 ^ (64 * w - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩
    rw [← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide), hQ2', Nat.mod_mod_of_dvd _ d1]
    omega
  simp only [seqs]
  refine WP.mono (VG.Proof.Rsa.X86_64.divBit_ok (hs.congr k12.2.2) ((k12.gpr (by decide)).trans hdi) h12₂ ((k12.gpr (by decide)).trans h9)
    hbp₂ ((k12.gpr (by decide)).trans h13) ((k12.gpr (by decide)).trans h11) hw1 hw hk hZ hQ hev)
    fun t ⟨hz, h13t, h12t, hQt, f₃, k₃⟩ => ⟨hz, h13t, h12t, ?_, (k12.trans k₃).mono (by simp [VG.Proof.Rsa.X86_64.stepRegs]), fun hlt => ?_⟩
  · intro x hx
    have a := hx (VG.Proof.Rsa.X86_64.ar w iQ) (by simp)
    have b := hx (VG.Proof.Rsa.X86_64.ar w iR) (by simp)
    have c := hx (VG.Proof.Rsa.X86_64.ar w iT) (by simp)
    rw [f₃ x (by simpa using a), f₂ x (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl)
      <;> with_reducible assumption), f₁ x (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl)
      <;> with_reducible assumption)]
  · have hRlt : wv s.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) < 2 ^ (64 * w) := Nat.lt_trans hlt (wv_lt _ _ _ _)
    have hR₁' := hR₁ hRlt
    have hRt : wv t.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) = wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) :=
      f₃.wv_eq (fun r hr => by simp at hr; subst hr; dsimp only; omega) (by omega)
    simp only [VG.Proof.Rsa.divStep]
    rw [hQt, hQ2', hRt, hR₂, hD₁, hR₁']
    split
    · rename_i h; simp [h]
    · rename_i h; simp [h]

theorem ofNat_dbl (a : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 a = BitVec.ofNat 64 (2 * a) := by
  rw [← BitVec.ofNat_add, Nat.two_mul]

/-- The invariant of `divmod`'s loop after `j` steps from `s`, for the
dividend `N` and the divisor `D`. -/
structure DivInv (s : State) (B : Addr) (Z w iQ iR iD iT N D : Nat) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  rdi : t.gpr .rdi = B
  r12 : t.gpr .r12 = BitVec.ofNat 64 w
  r9 : t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))
  r13 : t.gpr .r13 = BitVec.ofNat 64 j
  r11 : t.gpr .r11 = BitVec.ofNat 64 (64 * w)
  frm : Frm B [VG.Proof.Rsa.X86_64.ar w iQ, VG.Proof.Rsa.X86_64.ar w iR, VG.Proof.Rsa.X86_64.ar w iT] s.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep (.r9 :: .r11 :: VG.Proof.Rsa.X86_64.stepRegs) s t
  val : 0 < D → (wv t.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1), wv t.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w) = divIter D (64 * w) j (0, N)

/-- `divmod`: the remainder of `[q]` by `[d]` into `[r]` (`w + 1` words) and
the quotient into `[q]`, if `[d]` is not zero. -/
theorem divmod_ok {s : State} {B : Addr} {Z w : Nat} {iQ iR iD iT : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (hW : VG.Proof.Bignum.X86_64.word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hS : VG.Proof.Bignum.X86_64.word s.mem B (8 * sStride) = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z)
    (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16) (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT)
    (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT) :
    WP isa (divmod iQ iR iD iT) s fun t =>
      t.gpr .rdi = B ∧ Frm B [VG.Proof.Rsa.X86_64.ar w iQ, VG.Proof.Rsa.X86_64.ar w iR, VG.Proof.Rsa.X86_64.ar w iT] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep (.r9 :: .r11 :: VG.Proof.Rsa.X86_64.stepRegs) s t ∧
      (0 < wv s.mem B (VG.Proof.Bignum.X86_64.slot w iD) w →
        wv t.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w % wv s.mem B (VG.Proof.Bignum.X86_64.slot w iD) w ∧
        wv t.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w / wv s.mem B (VG.Proof.Bignum.X86_64.slot w iD) w) := by
  have hn := hs.nowrap
  have sQ := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hQ) hZ
  have sR := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hR) hZ
  have sD := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hD) hZ
  have sT := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hT) hZ
  have pQR := VG.Proof.Bignum.X86_64.slot_sep (w := w) dQR
  have pRD := VG.Proof.Bignum.X86_64.slot_sep (w := w) dRD
  have pRT := VG.Proof.Bignum.X86_64.slot_sep (w := w) dRT
  have pQD := VG.Proof.Bignum.X86_64.slot_sep (w := w) dQD
  have pDT := VG.Proof.Bignum.X86_64.slot_sep (w := w) dDT
  have h256 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 16 (show 31 < 32 by decide); omega
  unfold divmod
  simp only [seqs]
  -- The registers.
  have e₁ : WP isa (.block (divInit iR)) s fun (t : State) =>
      t.gpr .rdi = B ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w iR) ∧
      t.gpr .r11 = BitVec.ofNat 64 (64 * w) ∧ t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .r8, .r11, .r13] s t := by
    rw [divInit, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (VG.Proof.Rsa.X86_64.ws_ok hs hdi h256 hW hS) fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
    refine WP.mono (VG.Proof.Rsa.X86_64.base_ok iR (r := .r8) (by decide) ((k₁.gpr (by decide)).trans hdi) h9) fun s₂ ⟨h8, m₂, k₂⟩ => ?_
    have k12 := k₁.trans k₂
    have e12 : s₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans h12
    refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 w ∧ t.mem = s₂.mem)
      (by xrun [e12]) rfl) fun s₃ ⟨⟨h11, m₃⟩, k₃⟩ => ?_
    refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (64 * w) ∧ t.mem = s₃.mem)
      (by
        xrun [h11, VG.Proof.Rsa.X86_64.ofNat_dbl, List.replicate]
        congr 1; omega) rfl) fun s₄ ⟨⟨h11', m₄⟩, k₄⟩ => ?_
    refine WP.mono (WP.keep [.r13] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s₄.mem)
      (by xrun) rfl) fun t ⟨⟨h13, m₅⟩, k₅⟩ => ?_
    have kk := (((k12.trans k₃).trans k₄).trans k₅)
    refine ⟨(kk.gpr (by decide)).trans hdi, (((k₂.trans k₃).trans k₄).trans k₅ |>.gpr (by decide)).trans h12,
      (((k₂.trans k₃).trans k₄).trans k₅ |>.gpr (by decide)).trans h9, ((k₃.trans k₄).trans k₅ |>.gpr (by decide)).trans h8,
      (k₅.gpr (by decide)).trans h11', h13, by rw [m₅, m₄, m₃, m₂, m₁], kk.mono (by simp)⟩
  refine WP.seq (WP.mono e₁ fun s₁ ⟨hdi₁, h12₁, h9₁, h8₁, h11₁, h13₁, m₁, k₁⟩ => ?_)
  -- `[r] := 0`.
  refine WP.seq (WP.mono (zeroAccLoop_ok (hs.congr k₁.2.2) h8₁ h12₁ hw1 (by omega) (by omega)) fun s₂ ⟨hz, ho, k₂⟩ => ?_)
  rw [m₁] at ho
  have k12 := k₁.trans k₂
  have hN₂ : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w := ho.wv (by omega) (by omega)
  have hD₂ : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iD) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iD) w := ho.wv (by omega) (by omega)
  have hR₂ : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) = 0 := by
    have := wv_add s₂.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) 1
    rw [show w + 1 + 1 = w + 2 by omega, hz] at this
    omega
  -- The loop.
  refine wp_upto (a := 0) (N := 64 * w) (by omega)
    (VG.Proof.Rsa.X86_64.DivInv s B Z w iQ iR iD iT (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w) (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iD) w))
    (fun j _ hj t hI => ?_) (fun t hI => ⟨hI.rdi, hI.frm, hI.keep, fun hD0 => ?_⟩)
    ⟨hs.congr k12.2.2, (k₂.gpr (by decide)).trans hdi₁, (k₂.gpr (by decide)).trans h12₁,
      (k₂.gpr (by decide)).trans h9₁, (k₂.gpr (by decide)).trans h13₁, (k₂.gpr (by decide)).trans h11₁,
      Frm.of_outside (ho.mono (Nat.le_refl _) (Nat.le_refl _)) (by simp), k12.mono (by simp [VG.Proof.Rsa.X86_64.stepRegs]),
      fun _ => by rw [hR₂, hN₂]; rfl⟩
  · have hDt : wv t.mem B (VG.Proof.Bignum.X86_64.slot w iD) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iD) w :=
      hI.frm.wv_eq (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega) (by omega)
    refine WP.mono (VG.Proof.Rsa.X86_64.divStepCode_ok hI.scr hI.rdi hI.r12 hI.r9 hI.r13 hI.r11 hw1 hw hj hZ hQ hR hD hT dQR dQD dQT dRD
      dRT dDT) fun t' ⟨hz', h13', h12', f', k', hv'⟩ => ⟨hz', ?_⟩
    refine ⟨hI.scr.congr k'.2.2, (k'.gpr (by decide)).trans hI.rdi, h12', (k'.gpr (by decide)).trans hI.r9, h13',
      (k'.gpr (by decide)).trans hI.r11, hI.frm.trans f', (hI.keep.trans k').mono (by simp [VG.Proof.Rsa.X86_64.stepRegs]), fun hD0 => ?_⟩
    obtain ⟨q, hlt, -, -, -⟩ := divIter_inv hD0 (wv_lt s.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w) j (by omega)
    have hv := hI.val hD0
    have hRt : wv t.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) < wv t.mem B (VG.Proof.Bignum.X86_64.slot w iD) w := by
      rw [hDt, show wv t.mem B (VG.Proof.Bignum.X86_64.slot w iR) (w + 1) = _ from congrArg Prod.fst hv]; exact hlt
    rw [hv' hRt, hDt, hv]
    rfl
  · have := hI.val hD0
    rw [divIter_done hD0 (wv_lt s.mem B (VG.Proof.Bignum.X86_64.slot w iQ) w), Prod.ext_iff] at this
    exact this

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.Inv`. -/
section

/-!
# RSA private keys on x86-64: the binary extended Euclidean algorithm

`invStep`, one step of `inverse`, is `KeyMath.invStep` on the arrays
(`invStepCode_ok`): `u`, `v`, `x₁` and `x₂` (`w` words each), while
`x₁, x₂ < m` and the word `w` of `u` is zero. Its parts: the masks and the
swaps (`invSwap_ok`), the subtractions (`invSub_ok`) and the halvings
(`invHalf_ok`). `inverse` is `KeyMath.invIter` for `128 w` steps from
`(a, m, 1, 0)` (`inverse_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

theorem mask_and' (a b : Bool) : VG.Proof.Bignum.X86_64.mask a &&& VG.Proof.Bignum.X86_64.mask b = VG.Proof.Bignum.X86_64.mask (a && b) := by
  cases a <;> cases b <;> rfl

/-- The mask of a word's low bit. -/
theorem mask_low (x : BitVec 64) : BitVec.setWidth 64 (0 : BitVec 32) - (x &&& 1) =
    VG.Proof.Bignum.X86_64.mask (decide (x.toNat % 2 = 1)) := by
  have h2 : x &&& 1 = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega
  rw [h2]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- The masks and the swaps: `(u, v, x₁, x₂)` swapped to `(v, u, x₂, x₁)`
if `u` is odd and below `v`, and the mask of `u` odd in `sMo`. -/
theorem invSwap_ok {s : State} {B : Addr} {Z w : Nat} {iU iV iX₁ iX₂ : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (dUV : iU ≠ iV) (dX : iX₁ ≠ iX₂)
    (d₁ : iU ≠ iX₁) (d₂ : iU ≠ iX₂) (d₃ : iV ≠ iX₁) (d₄ : iV ≠ iX₂) {u v x₁ x₂ : Nat} {sw : Bool}
    (hu : wv s.mem B (VG.Proof.Bignum.X86_64.slot w iU) w = u) (hv : wv s.mem B (VG.Proof.Bignum.X86_64.slot w iV) w = v)
    (hx₁ : wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w = x₁) (hx₂ : wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w = x₂)
    (hsw : sw = (decide (u % 2 = 1) && decide (u < v))) :
    WP isa (seqs (invSwapP iU iV iX₁ iX₂)) s fun t =>
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sMo) = VG.Proof.Bignum.X86_64.mask (decide (u % 2 = 1)) ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w iU) w = (if sw then v else u) ∧ wv t.mem B (VG.Proof.Bignum.X86_64.slot w iV) w = (if sw then u else v) ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w = (if sw then x₂ else x₁) ∧ wv t.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w = (if sw then x₁ else x₂) ∧
      Frm B [(VG.Proof.Bignum.X86_64.slot w iU, 8 * w), (VG.Proof.Bignum.X86_64.slot w iV, 8 * w), (VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w), (VG.Proof.Bignum.X86_64.slot w iX₂, 8 * w), (8 * sMo, 8)]
        s.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rbx, .rdx, .rbp, .r10, .r14, .r15] s t := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hU) hZ
  have sV := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hV) hZ
  have sX₁ := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hX₁) hZ
  have sX₂ := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hX₂) hZ
  have pUV := VG.Proof.Bignum.X86_64.slot_sep (w := w) dUV
  have pX := VG.Proof.Bignum.X86_64.slot_sep (w := w) dX
  have p₁ := VG.Proof.Bignum.X86_64.slot_sep (w := w) d₁
  have p₂ := VG.Proof.Bignum.X86_64.slot_sep (w := w) d₂
  have p₃ := VG.Proof.Bignum.X86_64.slot_sep (w := w) d₃
  have p₄ := VG.Proof.Bignum.X86_64.slot_sep (w := w) d₄
  have hU0 := hdr_lt_slot w iU (show sMo < 32 by decide)
  have hX0 := hdr_lt_slot w iX₁ (show sMo < 32 by decide)
  have hX0' := hdr_lt_slot w iX₂ (show sMo < 32 by decide)
  have hV0 := hdr_lt_slot w iV (show sMo < 32 by decide)
  have eMo : sMo = 29 := rfl
  simp only [invSwapP, seqs, List.append_assoc]
  -- `rbx := U`, the mask of `u` odd into `sMo`, `r10 := V`, `rbp := 0`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (VG.Proof.Rsa.X86_64.base_ok iU (r := .rbx) (by decide) hdi h9)
    fun s₁ ⟨hbx, m₁, k₁⟩ => WP.block_append_iff.mpr (WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
      t.mem = s₁.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sMo)) (VG.Proof.Bignum.X86_64.mask (decide (u % 2 = 1)))) (by
        have hs₁ := hs.congr k₁.2.2
        have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
        have e0 : (s₁.mem.readW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w iU)) 64).toNat % 2 = u % 2 := by
          rw [m₁, ← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide), hu]
        xrun [State.ea, at0, VG.Impl.Bignum.X86_64.hdr, hbx, hdi₁, hdrOff, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
          hs₁.ld (d := VG.Proof.Bignum.X86_64.slot w iU) (by omega), hs₁.st (d := 8 * sMo) (by omega), VG.Proof.Rsa.X86_64.mask_low, e0]) rfl)
      fun s₂ ⟨m₂, k₂⟩ => WP.block_append_iff.mpr (WP.mono (VG.Proof.Rsa.X86_64.base_ok iV (r := .r10) (by decide)
        (((k₁.trans k₂).gpr (by decide)).trans hdi) (((k₁.trans k₂).gpr (by decide)).trans h9))
        fun s₃ ⟨h10, m₃, k₃⟩ => WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t.mem = s₃.mem)
          (by xrun) rfl) fun s₄ ⟨⟨hbp, m₄⟩, k₄⟩ => ?_))))
  have k04 := ((k₁.trans k₂).trans k₃).trans k₄
  have hm₄ : s₄.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sMo)) (VG.Proof.Bignum.X86_64.mask (decide (u % 2 = 1))) := by rw [m₄, m₃, m₂, m₁]
  have o₄ := VG.Proof.Bignum.X86_64.writeW_outside s.mem B (VG.Proof.Bignum.X86_64.mask (decide (u % 2 = 1))) (d := 8 * sMo) (by omega)
  have eU : wv s₄.mem B (VG.Proof.Bignum.X86_64.slot w iU) w = u := by
    rw [hm₄]
    exact (o₄.wv (Or.inr hU0) (by omega)).trans hu
  have eV : wv s₄.mem B (VG.Proof.Bignum.X86_64.slot w iV) w = v := by
    rw [hm₄]
    exact (o₄.wv (Or.inr hV0) (by omega)).trans hv
  have hs₄ := hs.congr k04.2.2
  -- `rbp := ` the mask of `u < v`.
  refine WP.seq (WP.mono (cmpLoop_ok hs₄ ((k₂.trans k₃).trans k₄ |>.gpr (by decide) |>.trans hbx)
    ((k₄.gpr (by decide)).trans h10) ((k04.gpr (by decide)).trans h12) hbp hw1 (by omega) (by omega) (by omega))
    fun s₅ ⟨hbp₅, m₅, k₅⟩ => ?_)
  rw [eU, eV] at hbp₅
  -- `r15 := ` the swap's mask.
  have hl : InRegions (s₅.rd ++ s₅.wr) (VG.Proof.Bignum.X86_64.off B (8 * sMo)) 8 := (hs.congr (k04.trans k₅).2.2).ld (by omega)
  have hdi₅ : s₅.gpr .rdi = B := ((k04.trans k₅).gpr (by decide)).trans hdi
  have hmo₅ : VG.Proof.Bignum.X86_64.word s₅.mem B (8 * sMo) = VG.Proof.Bignum.X86_64.mask (decide (u % 2 = 1)) := by rw [m₅, hm₄, VG.Proof.Bignum.X86_64.word_writeW_self]
  refine WP.seq (WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = VG.Proof.Bignum.X86_64.mask sw ∧ t.mem = s₅.mem) (by
    xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi₅, hdrOff, hl, hbp₅, hmo₅, VG.Proof.Rsa.X86_64.mask_and']
    rw [hsw, Bool.and_comm]) rfl) fun s₆ ⟨⟨h15, m₆⟩, k₆⟩ => ?_)
  have k06 := (k04.trans k₅).trans k₆
  -- The swap of `U` and `V`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.cswap_ok (hs.congr k06.2.2) ((k₂.trans k₃ |>.trans k₄ |>.trans k₅ |>.trans k₆).gpr
    (by decide) |>.trans hbx) ((k₄.trans k₅ |>.trans k₆).gpr (by decide) |>.trans h10) h15
    ((k06.gpr (by decide)).trans h12) hw1 (by omega) (by omega) (by omega) (by omega))
    fun s₇ ⟨hU₇, hV₇, f₇, k₇⟩ => ?_)
  have k07 := k06.trans k₇
  rw [m₆, m₅, eU, eV] at hU₇ hV₇
  -- The bases of `X₁` and `X₂`.
  refine WP.seq (WP.mono (Q := fun (t : State) => t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w iX₁) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w iX₂) ∧
      t.mem = s₇.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rbx, .r10] s₇ t) ?_ fun t h => ?_)
  · rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Rsa.X86_64.base_ok iX₁ (r := .rbx) (by decide) ((k07.gpr (by decide)).trans hdi)
      ((k07.gpr (by decide)).trans h9)) fun t₁ ⟨e₁, n₁, j₁⟩ => WP.mono (VG.Proof.Rsa.X86_64.base_ok iX₂ (r := .r10) (by decide)
        (((k07.trans j₁).gpr (by decide)).trans hdi) (((k07.trans j₁).gpr (by decide)).trans h9))
        fun t₂ ⟨e₂, n₂, j₂⟩ => ⟨(j₂.gpr (by decide)).trans e₁, e₂, n₂.trans n₁, (j₁.trans j₂).mono (by simp)⟩
  obtain ⟨hbx₈, h10₈, m₈, k₈⟩ := h
  -- The swap of `X₁` and `X₂`.
  refine WP.mono (VG.Proof.Rsa.X86_64.cswap_ok (hs.congr (k07.trans k₈).2.2) hbx₈ h10₈ ((k₇.trans k₈).gpr (by decide) |>.trans h15)
    (((k07.trans k₈).gpr (by decide)).trans h12) hw1 (by omega) (by omega) (by omega) (by omega))
    fun t ⟨hX₁t, hX₂t, f₉, k₉⟩ => ?_
  rw [m₈] at hX₁t hX₂t f₉
  -- What the swap of `U` and `V` left of `X₁` and `X₂`.
  have fx : ∀ i, i = iX₁ ∨ i = iX₂ → wv s₇.mem B (VG.Proof.Bignum.X86_64.slot w i) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w i) w := by
    intro i hi
    have hi' : i < 16 := by rcases hi with rfl | rfl <;> with_reducible assumption
    have hsep : ∀ r ∈ [(VG.Proof.Bignum.X86_64.slot w iU, 8 * w), (VG.Proof.Bignum.X86_64.slot w iV, 8 * w)], VG.Proof.Bignum.X86_64.slot w i + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot w i := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> rcases hi with rfl | rfl <;> omega
    rw [f₇.wv_eq hsep (by have := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hi') hZ; omega), m₆, m₅, hm₄]
    exact o₄.wv (by have := hdr_lt_slot w i (show sMo < 32 by decide); omega)
      (by have := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hi') hZ; omega)
  have hUt : ∀ i, i = iU ∨ i = iV → wv t.mem B (VG.Proof.Bignum.X86_64.slot w i) w = wv s₇.mem B (VG.Proof.Bignum.X86_64.slot w i) w := by
    intro i hi
    have hi' : i < 16 := by rcases hi with rfl | rfl <;> with_reducible assumption
    exact f₉.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> rcases hi with rfl | rfl <;> omega)
      (by have := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hi') hZ; omega)
  refine ⟨?_, by rw [hUt iU (.inl rfl)]; exact hU₇, by rw [hUt iV (.inr rfl)]; exact hV₇,
    by rw [hX₁t, fx iX₁ (.inl rfl), fx iX₂ (.inr rfl), hx₁, hx₂],
    by rw [hX₂t, fx iX₁ (.inl rfl), fx iX₂ (.inr rfl), hx₁, hx₂], ?_, ((k07.trans k₈).trans k₉).mono (by simp)⟩
  · have e₁ : VG.Proof.Bignum.X86_64.word t.mem B (8 * sMo) = VG.Proof.Bignum.X86_64.word s₇.mem B (8 * sMo) :=
      f₉.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega)
    have e₂ : VG.Proof.Bignum.X86_64.word s₇.mem B (8 * sMo) = VG.Proof.Bignum.X86_64.word s₆.mem B (8 * sMo) :=
      f₇.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega)
    rw [e₁, e₂, m₆, hmo₅]
  · intro x hx
    have a := hx (VG.Proof.Bignum.X86_64.slot w iU, 8 * w) (by simp)
    have b := hx (VG.Proof.Bignum.X86_64.slot w iV, 8 * w) (by simp)
    have c := hx (VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w) (by simp)
    have d := hx (VG.Proof.Bignum.X86_64.slot w iX₂, 8 * w) (by simp)
    have e := hx (8 * sMo, 8) (by simp)
    dsimp only at a b c d e
    rw [f₉ x (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> with_reducible assumption),
      f₇ x (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> with_reducible assumption),
      m₆, m₅, hm₄, VG.Proof.Bignum.X86_64.writeW_outside s.mem B _ (by omega) x (by omega)]

/-- Three distinct arrays among sixteen are apart. -/
theorem slot_far {w i j : Nat} (h : i ≠ j) : VG.Proof.Bignum.X86_64.slot w i + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w j ∨ VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w i :=
  VG.Proof.Bignum.X86_64.slot_sep h

/-- `u -= v` if `u` is odd (the mask in `sMo`), leaving the mask in `r15`. -/
theorem invSubU_ok {s : State} {B : Addr} {Z w : Nat} {iU iV : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z) (hU : iU < 16) (hV : iV < 16) (dUV : iU ≠ iV)
    {odd : Bool} (hmo : VG.Proof.Bignum.X86_64.word s.mem B (8 * sMo) = VG.Proof.Bignum.X86_64.mask odd) :
    WP isa (seqs (invSubUP iU iV)) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w iU) w + (if odd then wv s.mem B (VG.Proof.Bignum.X86_64.slot w iV) w else 0) =
        wv s.mem B (VG.Proof.Bignum.X86_64.slot w iU) w + 2 ^ (64 * w) * (if odd ∧ wv s.mem B (VG.Proof.Bignum.X86_64.slot w iU) w < wv s.mem B (VG.Proof.Bignum.X86_64.slot w iV) w
          then 1 else 0) ∧
      t.gpr .r15 = VG.Proof.Bignum.X86_64.mask odd ∧ VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w iU) (8 * w) s.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rsi, .rbp, .r8, .r10, .r14, .r15] s t := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hU) hZ
  have sV := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hV) hZ
  have p1 := VG.Proof.Rsa.X86_64.slot_far (w := w) dUV
  have hmo0 := hdr_lt_slot w 0 (show sMo < 32 by decide)
  have hmo1 := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) (show 0 < 16 by decide)) hZ
  have hl : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * sMo)) 8 := hs.ld (by omega)
  simp only [invSubUP, seqs, List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.r15, .rbp] (Q := fun t => t.gpr .r15 = VG.Proof.Bignum.X86_64.mask odd ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t.mem = s.mem) (by xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, hdrOff, hl, hmo]) rfl)
    fun s₀ ⟨⟨h15₀, hbp₀, m₀⟩, k₀⟩ => WP.mono (VG.Proof.Rsa.X86_64.base3_ok iU iV iU (r₁ := .r8) (r₂ := .r10) (r₃ := .rsi) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) ((k₀.gpr (by decide)).trans hdi)
      ((k₀.gpr (by decide)).trans h9) (by decide) (by decide)) fun s₁ ⟨h8, h10, hsi, m₁, k₁⟩ => ?_))
  have k01 := k₀.trans k₁
  refine WP.mono (VG.Proof.Rsa.X86_64.subM_ok (hs.congr k01.2.2) hsi h8 h10 ((k₁.gpr (by decide)).trans h15₀)
    ((k01.gpr (by decide)).trans h12) ((k₁.gpr (by decide)).trans hbp₀) hw1 (by omega) (by omega) (by omega)
    (by omega) (Or.inl (Nat.le_refl _)) (by omega)) fun t ⟨b₁, _, hv, o, k₂⟩ => ?_
  rw [m₁, m₀] at hv o
  have u2 := wv_lt t.mem B (VG.Proof.Bignum.X86_64.slot w iU) w
  have v0 := wv_lt s.mem B (VG.Proof.Bignum.X86_64.slot w iV) w
  have u0 := wv_lt s.mem B (VG.Proof.Bignum.X86_64.slot w iU) w
  have hb1 := Bool.toNat_le b₁
  refine ⟨?_, (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h15₀), o, (k01.trans k₂).mono (by simp)⟩
  cases odd <;> simp only [Bool.false_eq_true, ite_false, ite_true, false_and, true_and] at hv ⊢
  · cases b₁ <;> simp only [Bool.toNat_false, Bool.toNat_true] at hv <;> omega
  · split <;> rename_i h <;> cases b₁ <;> simp only [Bool.toNat_false, Bool.toNat_true] at hv <;> omega

/-- `x₁ := x₁ - x₂ mod m` if `u` is odd (the mask in `r15`). -/
theorem invSubX_ok {s : State} {B : Addr} {Z w : Nat} {iX₁ iX₂ iM iT : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z)
    (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT)
    {odd : Bool} (h15 : s.gpr .r15 = VG.Proof.Bignum.X86_64.mask odd) :
    WP isa (seqs (invSubXP iX₁ iX₂ iM iT)) s fun t =>
      (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w < wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w → wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w < wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w →
        wv t.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w = if odd then
          subMod (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w) (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w) (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w)
          else wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w) ∧
      Frm B [(VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w), (VG.Proof.Bignum.X86_64.slot w iT, 8 * w)] s.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rbx, .rdx, .rsi, .rbp, .r8, .r10, .r14, .r15] s t := by
  have hn := hs.nowrap
  have sX₁ := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hX₁) hZ
  have sX₂ := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hX₂) hZ
  have sM := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hM) hZ
  have sT := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hT) hZ
  have p9 := VG.Proof.Rsa.X86_64.slot_far (w := w) dX
  have p10 := VG.Proof.Rsa.X86_64.slot_far (w := w) dX₁M
  have p11 := VG.Proof.Rsa.X86_64.slot_far (w := w) dX₁T
  have p12 := VG.Proof.Rsa.X86_64.slot_far (w := w) dX₂T
  have p13 := VG.Proof.Rsa.X86_64.slot_far (w := w) dMT
  simp only [invSubXP, seqs, List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧
      t.mem = s.mem) (by xrun) rfl)
    fun s₃ ⟨⟨hbp₃, m₃⟩, k₃⟩ => WP.mono (VG.Proof.Rsa.X86_64.base3_ok iX₁ iX₂ iT (r₁ := .r8) (r₂ := .r10) (r₃ := .rsi) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) ((k₃.gpr (by decide)).trans hdi)
      ((k₃.gpr (by decide)).trans h9) (by decide) (by decide)) fun s₄ ⟨h8₄, h10₄, hsi₄, m₄, k₄⟩ => ?_))
  have k04 := k₃.trans k₄
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.subM_ok (hs.congr k04.2.2) hsi₄ h8₄ h10₄ ((k04.gpr (by decide)).trans h15)
    ((k04.gpr (by decide)).trans h12) ((k₄.gpr (by decide)).trans hbp₃) hw1 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)) fun s₅ ⟨b₂, hb₂, hv₅, o₅, k₅⟩ => ?_)
  rw [m₄, m₃] at hv₅ o₅
  have k05 := k04.trans k₅
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.r15, .rbp] (Q := fun t => t.gpr .r15 = VG.Proof.Bignum.X86_64.mask b₂ ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t.mem = s₅.mem) (by xrun [hb₂]) rfl)
    fun s₆ ⟨⟨h15₆, hbp₆, m₆⟩, k₆⟩ => WP.mono (VG.Proof.Rsa.X86_64.base3_ok iT iM iX₁ (r₁ := .r8) (r₂ := .r10) (r₃ := .rbx) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (((k05.trans k₆).gpr (by decide)).trans hdi)
      (((k05.trans k₆).gpr (by decide)).trans h9) (by decide) (by decide)) fun s₇ ⟨h8₇, h10₇, hbx₇, m₇, k₇⟩ => ?_))
  have k07 := (k05.trans k₆).trans k₇
  have hT₇ : wv s₇.mem B (VG.Proof.Bignum.X86_64.slot w iT) w = wv s₅.mem B (VG.Proof.Bignum.X86_64.slot w iT) w := by rw [m₇, m₆]
  have hM₇ : wv s₇.mem B (VG.Proof.Bignum.X86_64.slot w iM) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w := by
    have e2 := o₅.wv (d := VG.Proof.Bignum.X86_64.slot w iM) (k := w) (by omega) (by omega)
    rw [m₇, m₆, e2]
  refine WP.mono (VG.Proof.Rsa.X86_64.addM_ok (hs.congr k07.2.2) hbx₇ h10₇ h8₇ ((k₇.gpr (by decide)).trans h15₆)
    ((k07.gpr (by decide)).trans h12) ((k₇.gpr (by decide)).trans hbp₆) hw1 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)) fun t ⟨c, _, hvt, ot, kt⟩ => ?_
  rw [hT₇, hM₇] at hvt
  have x1 := wv_lt t.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w
  have t5 := wv_lt s₅.mem B (VG.Proof.Bignum.X86_64.slot w iT) w
  have x10 := wv_lt s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w
  have hb2 := Bool.toNat_le b₂
  have hc := Bool.toNat_le c
  refine ⟨fun h1 h2 => ?_, ?_, (k07.trans kt).mono (by simp)⟩
  · clear hn sX₁ sX₂ sM sT p9 p10 p11 p12 p13
    unfold subMod
    cases odd <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hv₅ ⊢
    · cases b₂ <;> cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, ite_false,
        ite_true, Bool.false_eq_true, Nat.zero_add, Nat.add_zero] at hv₅ hvt <;> omega
    · split <;> cases b₂ <;> cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one,
        ite_false, ite_true, Bool.false_eq_true, Nat.zero_add, Nat.add_zero] at hv₅ hvt <;> omega
  · intro x hx
    have b := hx (VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w) (by simp)
    have d := hx (VG.Proof.Bignum.X86_64.slot w iT, 8 * w) (by simp)
    dsimp only at b d
    rw [ot x (by omega), m₇, m₆, o₅ x (by omega)]

/-- Two bases. -/
theorem base2_ok {s : State} {B : Addr} {w : Nat} (i j : Nat) {r₁ r₂ : Reg} (h₁ : r₁ ≠ .r9) (h₂ : r₂ ≠ .r9)
    (h₁₂ : r₂ ≠ r₁) (hdi : s.gpr .rdi = B) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) (hr1 : r₁ ≠ .rdi) :
    WP isa (.block (base i r₁ ++ base j r₂)) s fun t =>
      t.gpr r₁ = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w i) ∧ t.gpr r₂ = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j) ∧ t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [r₁, r₂] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok i h₁ hdi h9) fun t₁ ⟨e₁, m₁, k₁⟩ => ?_
  have g1 : ∀ r, r ≠ r₁ → t₁.gpr r = s.gpr r := fun r h => k₁.gpr (by simp [h])
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok j h₂ ((g1 _ (Ne.symm hr1)).trans hdi) ((g1 _ (Ne.symm h₁)).trans h9))
    fun t ⟨e₂, m₂, k₂⟩ => ?_
  have g2 : ∀ r, r ≠ r₂ → t.gpr r = t₁.gpr r := fun r h => k₂.gpr (by simp [h])
  exact ⟨(g2 _ (Ne.symm h₁₂)).trans e₁, e₂, m₂.trans m₁, (k₁.trans k₂).mono (by simp)⟩

/-- `u /= 2`, if the word `w` of `u` is zero. -/
theorem invHalfU_ok {s : State} {B : Addr} {Z w : Nat} {iU : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z) (hU : iU < 16)
    (h0 : VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w iU + 8 * w) = 0) :
    WP isa (seqs (invHalfUP iU)) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w iU) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iU) w / 2 ∧ VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w iU) (8 * w) s.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rsi, .r8, .r14] s t := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hU) hZ
  simp only [invHalfUP, seqs]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.base2_ok iU iU (r₁ := .r8) (r₂ := .rsi) (by decide) (by decide) (by decide) hdi h9
    (by decide)) fun s₁ ⟨h8, hsi, m₁, k₁⟩ => ?_)
  refine WP.mono (VG.Proof.Rsa.X86_64.shr_ok (hs.congr k₁.2.2) hsi h8 ((k₁.gpr (by decide)).trans h12) hw1 (by omega) (by omega)
    (by omega) (Or.inl (Nat.le_refl _))) fun t ⟨hv, o, k₂⟩ => ?_
  rw [m₁, h0, ← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)] at hv
  rw [m₁] at o
  refine ⟨?_, o, (k₁.trans k₂).mono (by simp)⟩
  simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_mod, Nat.mul_zero, Nat.add_zero] at hv
  omega

theorem adc0 (c : Bool) : (BitVec.setWidth 64 (0 : BitVec 32) + 0 +
    BitVec.setWidth 64 (BitVec.ofBool c)).toNat = c.toNat := by cases c <;> decide

/-- `x₁ := x₁ / 2 (mod m)`. -/
theorem invHalfX_ok {s : State} {B : Addr} {Z w : Nat} {iX₁ iM iT : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z) (hX₁ : iX₁ < 16) (hM : iM < 16) (hT : iT < 16)
    (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT) (dMT : iM ≠ iT) :
    WP isa (seqs (invHalfXP iX₁ iM iT)) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w = halfMod (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w) (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w) ∧
      Frm B [(VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w), VG.Proof.Rsa.X86_64.ar w iT] s.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rbx, .rdx, .rsi, .rbp, .r8, .r10, .r14, .r15] s t := by
  have hn := hs.nowrap
  have sX₁ := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hX₁) hZ
  have sM := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hM) hZ
  have sT := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hT) hZ
  have p10 := VG.Proof.Rsa.X86_64.slot_far (w := w) dX₁M
  have p11 := VG.Proof.Rsa.X86_64.slot_far (w := w) dX₁T
  have p13 := VG.Proof.Rsa.X86_64.slot_far (w := w) dMT
  simp only [invHalfXP, seqs, List.append_assoc]
  -- `r8 := X₁`, `r15 := ` the mask of `x₁` odd, `rbp := 0`, `r10 := M`, `rbx := T`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (VG.Proof.Rsa.X86_64.base_ok iX₁ (r := .r8) (by decide) hdi h9)
    fun s₁ ⟨h8, m₁, k₁⟩ => WP.block_append_iff.mpr (WP.mono (WP.keep [.rax, .r15, .rbp] (Q := fun t =>
      t.gpr .r15 = VG.Proof.Bignum.X86_64.mask (decide (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w % 2 = 1)) ∧ t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t.mem = s₁.mem)
      (by
        have e0 : (s₁.mem.readW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w iX₁)) 64).toNat % 2 = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w % 2 := by
          rw [m₁, ← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)]
        xrun [State.ea, at0, h8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
          (hs.congr k₁.2.2).ld (d := VG.Proof.Bignum.X86_64.slot w iX₁) (by omega), VG.Proof.Rsa.X86_64.mask_low, e0]) rfl)
      fun s₂ ⟨⟨h15, hbp, m₂⟩, k₂⟩ => WP.mono (VG.Proof.Rsa.X86_64.base2_ok iM iT (r₁ := .r10) (r₂ := .rbx) (by decide) (by decide)
        (by decide) (((k₁.trans k₂).gpr (by decide)).trans hdi) (((k₁.trans k₂).gpr (by decide)).trans h9)
        (by decide)) fun s₃ ⟨h10, hbx, m₃, k₃⟩ => ?_)))
  have k03 := (k₁.trans k₂).trans k₃
  -- `T := (M & mask) + X₁`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.addM_ok (hs.congr k03.2.2) hbx h10 ((k₂.trans k₃).gpr (by decide) |>.trans h8)
    ((k₃.gpr (by decide)).trans h15) ((k03.gpr (by decide)).trans h12) ((k₃.gpr (by decide)).trans hbp) hw1
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) fun s₄ ⟨c, hc, hv₄, o₄, k₄⟩ => ?_)
  rw [m₃, m₂, m₁] at hv₄ o₄
  have k04 := k03.trans k₄
  have hs₄ := hs.congr k04.2.2
  -- `T_w := c`, `r8 := T`, `rsi := X₁`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.rax, .rbp] (Q := fun t =>
      t.mem = s₄.mem.writeW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w iT + 8 * w)) (BitVec.ofNat 64 c.toNat)) (by
      have ebx : s₄.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w iT) := (k₄.gpr (by decide)).trans hbx
      have e12 : s₄.gpr .r12 = BitVec.ofNat 64 w := (k04.gpr (by decide)).trans h12
      unfold cfFromRbp
      xrun [State.ea, ix, ebx, e12, addr0 (b := VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w iT)) rfl rfl, hc, cf_mask,
        hs₄.st (d := VG.Proof.Bignum.X86_64.slot w iT + 8 * w) (by omega), VG.Proof.Rsa.X86_64.sx0]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [VG.Proof.Rsa.X86_64.adc0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Bool.toNat_le c; omega)]) rfl)
    fun s₅ ⟨m₅, k₅⟩ => WP.mono (VG.Proof.Rsa.X86_64.base2_ok iT iX₁ (r₁ := .r8) (r₂ := .rsi) (by decide) (by decide) (by decide)
      (((k04.trans k₅).gpr (by decide)).trans hdi) (((k04.trans k₅).gpr (by decide)).trans h9) (by decide))
      fun s₆ ⟨h8₆, hsi₆, m₆, k₆⟩ => ?_))
  have k06 := (k04.trans k₅).trans k₆
  -- `X₁ := T / 2`.
  refine WP.mono (VG.Proof.Rsa.X86_64.shr_ok (hs.congr k06.2.2) hsi₆ h8₆ ((k06.gpr (by decide)).trans h12) hw1 (by omega) (by omega)
    (by omega) (by omega)) fun t ⟨hv, o, k₇⟩ => ?_
  have hT₆ : wv s₆.mem B (VG.Proof.Bignum.X86_64.slot w iT) w = wv s₄.mem B (VG.Proof.Bignum.X86_64.slot w iT) w := by
    rw [m₆, m₅]
    exact (VG.Proof.Bignum.X86_64.writeW_outside s₄.mem B (d := VG.Proof.Bignum.X86_64.slot w iT + 8 * w) _ (by omega)).wv (Or.inl (Nat.le_refl _)) (by omega)
  have hTw : VG.Proof.Bignum.X86_64.word s₆.mem B (VG.Proof.Bignum.X86_64.slot w iT + 8 * w) = BitVec.ofNat 64 c.toNat := by rw [m₆, m₅, VG.Proof.Bignum.X86_64.word_writeW_self]
  have hT0 : (VG.Proof.Bignum.X86_64.word s₆.mem B (VG.Proof.Bignum.X86_64.slot w iT)).toNat % 2 = wv s₄.mem B (VG.Proof.Bignum.X86_64.slot w iT) w % 2 := by
    rw [← hT₆, ← wv_mod64 _ _ _ hw1, Nat.mod_mod_of_dvd _ (by decide)]
  have hcl := Bool.toNat_le c
  rw [hT₆, hTw, hT0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show c.toNat < 2 by omega)] at hv
  refine ⟨?_, ?_, (k06.trans k₇).mono (by simp)⟩
  · unfold halfMod
    rcases Nat.mod_two_eq_zero_or_one (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w) with h | h
    · rw [show decide (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w % 2 = 1) = false by simp [h]] at hv₄
      simp only [Bool.false_eq_true, ite_false] at hv₄
      simp only [h, ite_true]; omega
    · rw [show decide (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w % 2 = 1) = true by simp [h]] at hv₄
      simp only [ite_true] at hv₄
      simp only [show ¬ (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w % 2 = 0) by omega, ite_false]; omega
  · intro x hx
    have a := hx (VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w) (by simp)
    have b := hx (VG.Proof.Rsa.X86_64.ar w iT) (by simp)
    dsimp only at a b
    rw [o x (by omega), m₆, m₅, VG.Proof.Bignum.X86_64.writeW_outside s₄.mem B _ (by omega) x (by omega), o₄ x (by omega)]

/-- What the swaps and the subtractions leave: `(u', v', x₁', x₂')`. -/
def subState (m : Nat) (st : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  let (u, v, x₁, x₂) := st
  if u % 2 = 1 then
    if u < v then (v - u, u, subMod m x₂ x₁, x₁) else (u - v, v, subMod m x₁ x₂, x₂)
  else (u, v, x₁, x₂)

/-- The swaps and the subtractions of a step of `inverse`. -/
theorem invFirst_ok {s : State} {B : Addr} {Z w : Nat} {iU iV iX₁ iX₂ iM iT : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT) :
    WP isa (seqs (invSwapP iU iV iX₁ iX₂ ++ invSubP iU iV iX₁ iX₂ iM iT)) s fun t =>
      (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w < wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w → wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w < wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w →
        (wv t.mem B (VG.Proof.Bignum.X86_64.slot w iU) w, wv t.mem B (VG.Proof.Bignum.X86_64.slot w iV) w, wv t.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w, wv t.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w) =
          VG.Proof.Rsa.X86_64.subState (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w) (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iU) w, wv s.mem B (VG.Proof.Bignum.X86_64.slot w iV) w,
            wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w, wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w)) ∧
      Frm B [(VG.Proof.Bignum.X86_64.slot w iU, 8 * w), (VG.Proof.Bignum.X86_64.slot w iV, 8 * w), (VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w), (VG.Proof.Bignum.X86_64.slot w iX₂, 8 * w), (VG.Proof.Bignum.X86_64.slot w iT, 8 * w),
        (8 * sMo, 8)] s.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rbx, .rdx, .rsi, .rbp, .r8, .r10, .r14, .r15] s t := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hU) hZ
  have sV := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hV) hZ
  have sX₁ := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hX₁) hZ
  have sX₂ := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hX₂) hZ
  have sM := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hM) hZ
  have sT := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hT) hZ
  have hU0 := hdr_lt_slot w iU (show sMo < 32 by decide)
  have hV0 := hdr_lt_slot w iV (show sMo < 32 by decide)
  have hX10 := hdr_lt_slot w iX₁ (show sMo < 32 by decide)
  have hX20 := hdr_lt_slot w iX₂ (show sMo < 32 by decide)
  have hM0 := hdr_lt_slot w iM (show sMo < 32 by decide)
  have hT0 := hdr_lt_slot w iT (show sMo < 32 by decide)
  rw [invSubP]
  refine wp_seqs_append (by simp [invSwapP]) (by simp [invSubUP]) (WP.mono (VG.Proof.Rsa.X86_64.invSwap_ok hs hdi h12 h9 hw1 hw hZ hU hV
    hX₁ hX₂ dUV dX dUX₁ dUX₂ dVX₁ dVX₂ rfl rfl rfl rfl rfl) fun s₁ ⟨hmo, hU₁, hV₁, hX₁₁, hX₂₁, f₁, k₁⟩ => ?_)
  refine wp_seqs_append (by simp [invSubUP]) (by simp [invSubXP]) (WP.mono (VG.Proof.Rsa.X86_64.invSubU_ok (hs.congr k₁.2.2)
    ((k₁.gpr (by decide)).trans hdi) ((k₁.gpr (by decide)).trans h12) ((k₁.gpr (by decide)).trans h9) hw1 hw hZ
    hU hV dUV hmo) fun s₂ ⟨hU₂, h15₂, o₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.mono (VG.Proof.Rsa.X86_64.invSubX_ok (hs.congr k12.2.2) ((k12.gpr (by decide)).trans hdi)
    ((k12.gpr (by decide)).trans h12) ((k12.gpr (by decide)).trans h9) hw1 hw hZ hX₁ hX₂ hM hT dX dX₁M dX₁T dX₂T dMT
    h15₂) fun t ⟨hX₁t, f₃, k₃⟩ => ?_
  -- What each part leaves of the others.
  have eM₁ : wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w iM) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w := f₁.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUM; omega
    · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dVM; omega
    · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dX₁M; omega
    · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dX₂M; omega
    · omega) (by omega)
  have eV₂ : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iV) w = wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w iV) w :=
    o₂.wv (by have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUV; omega) (by omega)
  have eX₁₂ : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w = wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w :=
    o₂.wv (by have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUX₁; omega) (by omega)
  have eX₂₂ : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w = wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w :=
    o₂.wv (by have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUX₂; omega) (by omega)
  have eM₂ : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iM) w = wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w iM) w :=
    o₂.wv (by have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUM; omega) (by omega)
  have eU₃ : wv t.mem B (VG.Proof.Bignum.X86_64.slot w iU) w = wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iU) w := f₃.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only
    · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUX₁; omega
    · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUT; omega) (by omega)
  have eV₃ : wv t.mem B (VG.Proof.Bignum.X86_64.slot w iV) w = wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iV) w := f₃.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only
    · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dVX₁; omega
    · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dVT; omega) (by omega)
  have eX₂₃ : wv t.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w = wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w := f₃.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only
    · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dX; omega
    · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dX₂T; omega) (by omega)
  rw [eX₁₂, eX₂₂, eM₂, eM₁, hX₁₁, hX₂₁] at hX₁t
  rw [hV₁, hU₁] at hU₂
  refine ⟨fun hx₁ hx₂ => ?_, ?_, ((k12.trans k₃)).mono (by simp)⟩
  · rw [eU₃, eV₃, eX₂₃, eV₂, eX₂₂, hV₁, hX₂₁]
    have := hX₁t (by split <;> omega) (by split <;> omega)
    rw [this]
    have hu := wv_lt s₂.mem B (VG.Proof.Bignum.X86_64.slot w iU) w
    unfold VG.Proof.Rsa.X86_64.subState
    dsimp only
    generalize wv s.mem B (VG.Proof.Bignum.X86_64.slot w iU) w = u at hU₂ ⊢
    generalize wv s.mem B (VG.Proof.Bignum.X86_64.slot w iV) w = v at hU₂ ⊢
    generalize wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iU) w = u' at hU₂ hu ⊢
    rcases Nat.mod_two_eq_zero_or_one u with ho | ho
    · simp only [ho, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, false_and, Nat.mul_zero,
        Nat.add_zero, show (0 : Nat) ≠ 1 by decide] at hU₂ ⊢
      rw [hU₂]
    · by_cases hlt : u < v
      · simp only [ho, hlt, decide_true, Bool.and_self, ite_true, show ¬ v < u by omega, and_false, ite_false,
          Nat.mul_zero, Nat.add_zero] at hU₂ ⊢
        refine Prod.ext (by dsimp only; omega) rfl
      · simp only [ho, hlt, decide_true, decide_false, Bool.and_false, Bool.false_eq_true, ite_true, ite_false,
          and_false, Nat.mul_zero, Nat.add_zero] at hU₂ ⊢
        refine Prod.ext (by dsimp only; omega) rfl
  · intro x hx
    have a := hx (VG.Proof.Bignum.X86_64.slot w iU, 8 * w) (by simp)
    have b := hx (VG.Proof.Bignum.X86_64.slot w iV, 8 * w) (by simp)
    have c := hx (VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w) (by simp)
    have d := hx (VG.Proof.Bignum.X86_64.slot w iX₂, 8 * w) (by simp)
    have e := hx (VG.Proof.Bignum.X86_64.slot w iT, 8 * w) (by simp)
    have g := hx (8 * sMo, 8) (by simp)
    dsimp only at a b c d e g
    have h3 : ∀ r ∈ [(VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w), (VG.Proof.Bignum.X86_64.slot w iT, 8 * w)], VG.Proof.Bignum.X86_64.ofs B x < r.1 ∨ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.ofs B x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> with_reducible assumption
    have h1 : ∀ r ∈ [(VG.Proof.Bignum.X86_64.slot w iU, 8 * w), (VG.Proof.Bignum.X86_64.slot w iV, 8 * w), (VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w), (VG.Proof.Bignum.X86_64.slot w iX₂, 8 * w), (8 * sMo, 8)],
        VG.Proof.Bignum.X86_64.ofs B x < r.1 ∨ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.ofs B x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl) <;> with_reducible assumption
    rw [f₃ x h3, o₂ x a, f₁ x h1]

/-- `KeyMath.invStep` is the subtraction, then the halvings. -/
theorem invStep_eq (m : Nat) (st : Nat × Nat × Nat × Nat) :
    VG.Proof.Rsa.invStep m st = ((VG.Proof.Rsa.X86_64.subState m st).1 / 2, (VG.Proof.Rsa.X86_64.subState m st).2.1, halfMod m (VG.Proof.Rsa.X86_64.subState m st).2.2.1,
      (VG.Proof.Rsa.X86_64.subState m st).2.2.2) := by
  obtain ⟨u, v, x₁, x₂⟩ := st
  unfold VG.Proof.Rsa.invStep VG.Proof.Rsa.X86_64.subState
  dsimp only
  split
  · split <;> rfl
  · rfl

/-- One step of `inverse`: `KeyMath.invStep`, while `x₁, x₂ < m` and the
word `w` of `u` is zero. -/
theorem invStepCode_ok {s : State} {B : Addr} {Z w k : Nat} {iU iV iX₁ iX₂ iM iT : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h13 : s.gpr .r13 = BitVec.ofNat 64 k) (h11 : s.gpr .r11 = BitVec.ofNat 64 (128 * w))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hk : k < 128 * w) (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT) (hU0 : VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w iU + 8 * w) = 0) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.invStep iU iV iX₁ iX₂ iM iT) s fun t =>
      t.zf = some (decide (k + 1 = 128 * w)) ∧ t.gpr .r13 = BitVec.ofNat 64 (k + 1) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧
      Frm B [(VG.Proof.Bignum.X86_64.slot w iU, 8 * w), (VG.Proof.Bignum.X86_64.slot w iV, 8 * w), (VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w), (VG.Proof.Bignum.X86_64.slot w iX₂, 8 * w), VG.Proof.Rsa.X86_64.ar w iT,
        (8 * sMo, 8)] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep VG.Proof.Rsa.X86_64.stepRegs s t ∧
      (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w < wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w → wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w < wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w →
        (wv t.mem B (VG.Proof.Bignum.X86_64.slot w iU) w, wv t.mem B (VG.Proof.Bignum.X86_64.slot w iV) w, wv t.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w, wv t.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w) =
          VG.Proof.Rsa.invStep (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w) (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iU) w, wv s.mem B (VG.Proof.Bignum.X86_64.slot w iV) w,
            wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w, wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w)) := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hU) hZ
  have sV := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hV) hZ
  have sX₁ := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hX₁) hZ
  have sX₂ := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hX₂) hZ
  have sM := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hM) hZ
  have sT := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hT) hZ
  have hU0' := hdr_lt_slot w iU (show sMo < 32 by decide)
  have hX10 := hdr_lt_slot w iX₁ (show sMo < 32 by decide)
  have hM0 := hdr_lt_slot w iM (show sMo < 32 by decide)
  have hT0 := hdr_lt_slot w iT (show sMo < 32 by decide)
  unfold VG.Impl.Rsa.X86_64.Keys.invStep
  rw [show invSwapP iU iV iX₁ iX₂ ++ (invSubP iU iV iX₁ iX₂ iM iT ++ (invHalfP iU iX₁ iM iT ++ [.block countP])) =
    (invSwapP iU iV iX₁ iX₂ ++ invSubP iU iV iX₁ iX₂ iM iT) ++ (invHalfUP iU ++ (invHalfXP iX₁ iM iT ++
      [.block countP])) by simp [invHalfP]]
  refine wp_seqs_append (by simp [invSwapP]) (by simp [invHalfUP]) (WP.mono (VG.Proof.Rsa.X86_64.invFirst_ok hs hdi h12 h9 hw1 hw hZ hU hV
    hX₁ hX₂ hM hT dUV dUX₁ dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T dX₂M dX₂T dMT) fun s₁ ⟨hv₁, f₁, k₁⟩ => ?_)
  have hU0₁ : VG.Proof.Bignum.X86_64.word s₁.mem B (VG.Proof.Bignum.X86_64.slot w iU + 8 * w) = 0 := by
    rw [f₁.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
      · omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUV; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUX₁; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUX₂; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUT; omega
      · omega) (by omega)]
    exact hU0
  refine wp_seqs_append (by simp [invHalfUP]) (by simp [invHalfXP]) (WP.mono (VG.Proof.Rsa.X86_64.invHalfU_ok (hs.congr k₁.2.2)
    ((k₁.gpr (by decide)).trans hdi) ((k₁.gpr (by decide)).trans h12) ((k₁.gpr (by decide)).trans h9) hw1 hw hZ
    hU hU0₁) fun s₂ ⟨hU₂, o₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine wp_seqs_append (by simp [invHalfXP]) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.invHalfX_ok (hs.congr k12.2.2)
    ((k12.gpr (by decide)).trans hdi) ((k12.gpr (by decide)).trans h12) ((k12.gpr (by decide)).trans h9) hw1 hw hZ
    hX₁ hM hT dX₁M dX₁T dMT) fun s₃ ⟨hX₃, f₃, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  simp only [seqs]
  refine WP.mono (WP.keep [.r13] (Q := fun t => t.zf = some (decide (k + 1 = 128 * w)) ∧
      t.gpr .r13 = BitVec.ofNat 64 (k + 1) ∧ t.mem = s₃.mem) (by
    unfold countP
    xrun [(k13.gpr (by decide) : s₃.gpr .r13 = _), h13, (k13.gpr (by decide) : s₃.gpr .r11 = _), h11, ofNat_add_one,
      ofNat_sub_beq (show k + 1 < 2 ^ 64 by omega) (show 128 * w < 2 ^ 64 by omega)]) rfl)
    fun t ⟨⟨hz, h13t, mt⟩, k₄⟩ => ⟨hz, h13t, (k₄.gpr (by decide)).trans ((k13.gpr (by decide)).trans h12), ?_,
      (k13.trans k₄).mono (by simp [VG.Proof.Rsa.X86_64.stepRegs]), fun hx₁ hx₂ => ?_⟩
  · intro x hx
    have a := hx (VG.Proof.Bignum.X86_64.slot w iU, 8 * w) (by simp)
    have b := hx (VG.Proof.Bignum.X86_64.slot w iV, 8 * w) (by simp)
    have c := hx (VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w) (by simp)
    have d := hx (VG.Proof.Bignum.X86_64.slot w iX₂, 8 * w) (by simp)
    have e := hx (VG.Proof.Rsa.X86_64.ar w iT) (by simp)
    have g := hx (8 * sMo, 8) (by simp)
    dsimp only at a b c d e g
    have h3 : ∀ r ∈ [(VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w), VG.Proof.Rsa.X86_64.ar w iT], VG.Proof.Bignum.X86_64.ofs B x < r.1 ∨ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.ofs B x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> with_reducible assumption
    have h1 : ∀ r ∈ [(VG.Proof.Bignum.X86_64.slot w iU, 8 * w), (VG.Proof.Bignum.X86_64.slot w iV, 8 * w), (VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w), (VG.Proof.Bignum.X86_64.slot w iX₂, 8 * w),
        (VG.Proof.Bignum.X86_64.slot w iT, 8 * w), (8 * sMo, 8)], VG.Proof.Bignum.X86_64.ofs B x < r.1 ∨ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.ofs B x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;> first | with_reducible assumption | (dsimp only; omega)
    rw [mt, f₃ x h3, o₂ x a, f₁ x h1]
  · have e := hv₁ hx₁ hx₂
    rw [VG.Proof.Rsa.X86_64.invStep_eq, ← e]
    have eM₁ : wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w iM) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w := f₁.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
      · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUM; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dVM; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dX₁M; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dX₂M; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dMT; omega
      · omega) (by omega)
    have eM₂ : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iM) w = wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w iM) w :=
      o₂.wv (by have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUM; omega) (by omega)
    have eX₂ : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w = wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w :=
      o₂.wv (by have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUX₁; omega) (by omega)
    have f3 : ∀ i, i ≠ iX₁ → i ≠ iT → i < 16 → wv t.mem B (VG.Proof.Bignum.X86_64.slot w i) w = wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w i) w := by
      intro i h1 h2 hi
      rw [mt]
      exact f₃.wv_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only
        · have := VG.Proof.Rsa.X86_64.slot_far (w := w) h1; omega
        · have := VG.Proof.Rsa.X86_64.slot_far (w := w) h2; omega) (by have := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hi) hZ; omega)
    have o2 : ∀ i, i ≠ iU → i < 16 → wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w i) w = wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w i) w := by
      intro i h1 hi
      exact o₂.wv (by have := VG.Proof.Rsa.X86_64.slot_far (w := w) h1; omega) (by have := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hi) hZ; omega)
    rw [f3 iU dUX₁ dUT hU, hU₂, f3 iV dVX₁ dVT hV, o2 iV (Ne.symm dUV) hV, f3 iX₂ (Ne.symm dX) dX₂T hX₂,
      o2 iX₂ (Ne.symm dUX₂) hX₂, mt, hX₃, eM₂, eM₁, eX₂]

/-- The invariant of `inverse`'s loop after `j` steps from `s`. -/
structure InvInv (s : State) (B : Addr) (Z w iU iV iX₁ iX₂ iT a m : Nat) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  rdi : t.gpr .rdi = B
  r12 : t.gpr .r12 = BitVec.ofNat 64 w
  r9 : t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))
  r13 : t.gpr .r13 = BitVec.ofNat 64 j
  r11 : t.gpr .r11 = BitVec.ofNat 64 (128 * w)
  frm : Frm B [(VG.Proof.Bignum.X86_64.slot w iU, 8 * w), (VG.Proof.Bignum.X86_64.slot w iV, 8 * w), (VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w), (VG.Proof.Bignum.X86_64.slot w iX₂, 8 * w), VG.Proof.Rsa.X86_64.ar w iT,
    (8 * sMo, 8)] s.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep (.r9 :: .r11 :: VG.Proof.Rsa.X86_64.stepRegs) s t
  u0 : VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w iU + 8 * w) = 0
  val : m % 2 = 1 → 1 < m → (wv t.mem B (VG.Proof.Bignum.X86_64.slot w iU) w, wv t.mem B (VG.Proof.Bignum.X86_64.slot w iV) w, wv t.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w,
    wv t.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w) = invIter m j (a, m, 1, 0)

/-- `inverse`: from `(a, m, 1, 0)` in `[u], [v], [x₁], [x₂]` (the word `w`
of `[u]` zero), `[m]` odd and above 1: `[v] = gcd(a, m)` and
`[x₂] a ≡ [v] (mod m)`, `[x₂] < m`. -/
theorem inverse_ok {s : State} {B : Addr} {Z w : Nat} {iU iV iX₁ iX₂ iM iT : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hW : VG.Proof.Bignum.X86_64.word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hS : VG.Proof.Bignum.X86_64.word s.mem B (8 * sStride) = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 1 ≤ w) (hw : w < 2 ^ 24) (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT) (hU0 : VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w iU + 8 * w) = 0)
    (hVM : wv s.mem B (VG.Proof.Bignum.X86_64.slot w iV) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w) (hX1 : wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₁) w = 1)
    (hX2 : wv s.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w = 0) :
    WP isa (inverse iU iV iX₁ iX₂ iM iT) s fun t =>
      t.gpr .rdi = B ∧
      Frm B [(VG.Proof.Bignum.X86_64.slot w iU, 8 * w), (VG.Proof.Bignum.X86_64.slot w iV, 8 * w), (VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w), (VG.Proof.Bignum.X86_64.slot w iX₂, 8 * w), VG.Proof.Rsa.X86_64.ar w iT,
        (8 * sMo, 8)] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep (.r9 :: .r11 :: VG.Proof.Rsa.X86_64.stepRegs) s t ∧
      (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w % 2 = 1 → 1 < wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w →
        wv t.mem B (VG.Proof.Bignum.X86_64.slot w iV) w = Nat.gcd (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iU) w) (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w) ∧
        ((wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w : Nat) : Int) ∣
          (wv t.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w : Int) * wv s.mem B (VG.Proof.Bignum.X86_64.slot w iU) w - wv t.mem B (VG.Proof.Bignum.X86_64.slot w iV) w ∧
        wv t.mem B (VG.Proof.Bignum.X86_64.slot w iX₂) w < wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w) := by
  have hn := hs.nowrap
  have sU := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hU) hZ
  have sM := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hM) hZ
  have hM0 := hdr_lt_slot w iM (show sMo < 32 by decide)
  have h256 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 16 (show 31 < 32 by decide); omega
  unfold inverse
  -- The registers.
  have e₁ : WP isa (.block invInit) s fun (t : State) =>
      t.gpr .rdi = B ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      t.gpr .r11 = BitVec.ofNat 64 (128 * w) ∧ t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .r11, .r13] s t := by
    rw [invInit, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (VG.Proof.Rsa.X86_64.ws_ok hs hdi h256 hW hS) fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
    refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 w ∧ t.mem = s₁.mem)
      (by xrun [h12]) rfl) fun s₃ ⟨⟨h11, m₃⟩, k₃⟩ => ?_
    refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (128 * w) ∧ t.mem = s₃.mem)
      (by
        xrun [h11, VG.Proof.Rsa.X86_64.ofNat_dbl, List.replicate]
        congr 1; omega) rfl) fun s₄ ⟨⟨h11', m₄⟩, k₄⟩ => ?_
    refine WP.mono (WP.keep [.r13] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s₄.mem)
      (by xrun) rfl) fun t ⟨⟨h13, m₅⟩, k₅⟩ => ?_
    have kk := ((k₁.trans k₃).trans k₄).trans k₅
    exact ⟨(kk.gpr (by decide)).trans hdi, ((k₃.trans k₄).trans k₅ |>.gpr (by decide)).trans h12,
      ((k₃.trans k₄).trans k₅ |>.gpr (by decide)).trans h9, (k₅.gpr (by decide)).trans h11', h13,
      by rw [m₅, m₄, m₃, m₁], kk.mono (by simp)⟩
  refine WP.seq (WP.mono e₁ fun s₁ ⟨hdi₁, h12₁, h9₁, h11₁, h13₁, m₁, k₁⟩ => ?_)
  have fM : ∀ {t : State}, Frm B [(VG.Proof.Bignum.X86_64.slot w iU, 8 * w), (VG.Proof.Bignum.X86_64.slot w iV, 8 * w), (VG.Proof.Bignum.X86_64.slot w iX₁, 8 * w), (VG.Proof.Bignum.X86_64.slot w iX₂, 8 * w),
      VG.Proof.Rsa.X86_64.ar w iT, (8 * sMo, 8)] s.mem t.mem → wv t.mem B (VG.Proof.Bignum.X86_64.slot w iM) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w := fun f =>
    f.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
      · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUM; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dVM; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dX₁M; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dX₂M; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dMT; omega
      · omega) (by omega)
  refine wp_upto (a := 0) (N := 128 * w) (by omega)
    (VG.Proof.Rsa.X86_64.InvInv s B Z w iU iV iX₁ iX₂ iT (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iU) w) (wv s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w))
    (fun j _ hj t hI => ?_) (fun t hI => ⟨hI.rdi, hI.frm, hI.keep, fun hodd h1 => ?_⟩)
    ⟨hs.congr k₁.2.2, hdi₁, h12₁, h9₁, h13₁, h11₁, by rw [m₁]; exact Frm.refl _ _ _, k₁.mono (by simp [VG.Proof.Rsa.X86_64.stepRegs]),
      by rw [m₁]; exact hU0, fun _ _ => by rw [m₁, hVM, hX1, hX2]; rfl⟩
  · refine WP.mono (VG.Proof.Rsa.X86_64.invStepCode_ok hI.scr hI.rdi hI.r12 hI.r9 hI.r13 hI.r11 hw1 hw hj hZ hU hV hX₁ hX₂ hM hT dUV dUX₁
      dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T dX₂M dX₂T dMT hI.u0) fun t' ⟨hz, h13', h12', f', k', hv'⟩ =>
      ⟨hz, hI.scr.congr k'.2.2, (k'.gpr (by decide)).trans hI.rdi, h12', (k'.gpr (by decide)).trans hI.r9, h13',
        (k'.gpr (by decide)).trans hI.r11, hI.frm.trans f', (hI.keep.trans k').mono (by simp [VG.Proof.Rsa.X86_64.stepRegs]), ?_,
        fun hodd h1 => ?_⟩
    · rw [f'.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
        · omega
        · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUV; omega
        · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUX₁; omega
        · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUX₂; omega
        · have := VG.Proof.Rsa.X86_64.slot_far (w := w) dUT; omega
        · have := hdr_lt_slot w iU (show sMo < 32 by decide); omega) (by omega)]
      exact hI.u0
    · have hv := hI.val hodd h1
      have hinv := invIter_inv hodd (invI_start (a := wv s.mem B (VG.Proof.Bignum.X86_64.slot w iU) w) hodd h1) j
      rw [← hv] at hinv
      rw [fM hI.frm] at hv'
      rw [hv' hinv.x₁_lt hinv.x₂_lt, hv]
      rfl
  · have hv := hI.val hodd h1
    have hd := invIter_done (a := wv s.mem B (VG.Proof.Bignum.X86_64.slot w iU) w) (K := 128 * w) hodd (by
      have := wv_lt s.mem B (VG.Proof.Bignum.X86_64.slot w iU) w
      have := wv_lt s.mem B (VG.Proof.Bignum.X86_64.slot w iM) w
      rw [show 128 * w = 64 * w + 64 * w by omega, Nat.pow_add]
      exact Nat.mul_lt_mul'' (by omega) (by omega))
    rw [Nat.mod_eq_of_lt h1, ← hv] at hd
    exact ⟨hd.2.1, hd.2.2.1, hd.2.2.2⟩

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.Pieces`. -/
section

/-!
# RSA private keys on x86-64: the working space and its pieces

`Ws`: the working space `vg_rsa_crt_values` and `vg_rsa_recover_primes` set
up, the header giving `w`, the stride and the bases of arrays 0 to 7, and 16
arrays fitting in it; kept by code that changes only arrays and the header
slots `sMask` and `sMo` (`Ws.congr`). The pieces of the functions that load,
clear, copy and store arrays (`zeroA_ok`, `copyA_ok`, `loadA_ok`,
`storeA_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- The working space at `B` of `Z` bytes, for `w`-word numbers. -/
structure Ws (s : State) (B : Addr) (Z w : Nat) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr s B Z
  rdi : s.gpr .rdi = B
  hw : VG.Proof.Bignum.X86_64.word s.mem B (8 * sW) = BitVec.ofNat 64 w
  hS : VG.Proof.Bignum.X86_64.word s.mem B (8 * sStride) = BitVec.ofNat 64 (8 * (w + 2))
  harr : ∀ j < 8, VG.Proof.Bignum.X86_64.word s.mem B (8 * sArr j) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j)
  hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z
  w1 : 2 ≤ w
  w2 : w < 2 ^ 24

theorem wv_zero {m : Mem} {B : Addr} {d n : Nat} (h : ∀ k < n, VG.Proof.Bignum.X86_64.word m B (d + 8 * k) = 0) : wv m B d n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wv, ih fun k hk => h k (by omega), h n (by omega)]; rfl

/-- The ranges the pieces may change: arrays, `sMask` and `sMo`. -/
def Mut (r : Nat × Nat) : Prop := 8 * 32 ≤ r.1 ∨ r = (8 * Impl.Bignum.X86_64.Public.sMask, 8) ∨ r = (8 * sMo, 8)

theorem Mut.ofSlot (w j : Nat) (n : Nat) : VG.Proof.Rsa.X86_64.Mut (Bignum.X86_64.slot w j, n) :=
  Or.inl (by unfold Bignum.X86_64.slot hdrBytes; omega)

theorem Ws.congr {s t : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {rs : List (Nat × Nat)}
    (hf : Frm B rs s.mem t.mem) (hm : ∀ r ∈ rs, VG.Proof.Rsa.X86_64.Mut r) {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t)
    (hr : .rdi ∉ regs) : VG.Proof.Rsa.X86_64.Ws t B Z w := by
  have hh : ∀ i, i ∈ [sW, sStride] ∨ (8 ≤ i ∧ i < 16) → VG.Proof.Bignum.X86_64.word t.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := by
    intro i hi
    have hi' : i < 16 ∨ i = 28 := by simp only [List.mem_cons, List.not_mem_nil, or_false, sW, sStride, sFn] at hi; omega
    exact hf.word_eq (fun r hr => by
      rcases hm r hr with h | rfl | rfl
      · omega
      · simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega
      · simp only [sMo, sFn]; omega) (by have := h.scr.nowrap; have := hdr_lt_slot w 16 (show 31 < 32 by decide)
                                         have := h.hZ; omega)
  exact ⟨h.scr.congr k.2.2, (k.gpr hr).trans h.rdi, (hh sW (.inl (by simp))).trans h.hw,
    (hh sStride (.inl (by simp))).trans h.hS, fun j hj => (hh (sArr j) (.inr (by unfold sArr; omega))).trans (h.harr j hj),
    h.hZ, h.w1, h.w2⟩

theorem Ws.good {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) :
    VG.Proof.Bignum.X86_64.Good s B Z w (VG.Proof.Bignum.X86_64.word s.mem B (8 * sMinv)) ∧ VG.Proof.Bignum.X86_64.slot w 8 ≤ Z :=
  ⟨⟨h.scr, h.rdi, ⟨h.hw, rfl, h.harr⟩⟩, Nat.le_trans (by unfold VG.Proof.Bignum.X86_64.slot; omega) h.hZ⟩

theorem Ws.h256 {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) : 8 * 32 ≤ Z := by
  have := hdr_lt_slot w 16 (show 31 < 32 by decide); have := h.hZ; omega

theorem Ws.sl {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {j : Nat} (hj : j < 16) :
    VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ Z := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt hj) h.hZ

/-- `ws`, from the working space. -/
theorem Ws.ws_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) :
    WP isa (.block VG.Impl.Rsa.X86_64.Keys.ws) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem ∧
        VG.Proof.MlKem.X86_64.Keep [.r12, .r9] s t :=
  VG.Proof.Rsa.X86_64.ws_ok h.scr h.rdi h.h256 h.hw h.hS

/-! ## Clearing and copying -/

/-- `zeroA j`: `[j] := 0` (`w + 2` words). -/
theorem zeroA_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {j : Nat} (hj : j < 16) :
    WP isa (zeroA j) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w j) (w + 2) = 0 ∧ VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w j) (8 * (w + 2)) s.mem t.mem ∧
        VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .r8, .rax, .r14] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  unfold zeroA
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (VG.Proof.Rsa.X86_64.base_ok j (r := .r8) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨h8, m₂, k₂⟩ => ?_))
  refine WP.mono (zeroAccLoop_ok (h.scr.congr (k₁.trans k₂).2.2) h8 ((k₂.gpr (by decide)).trans h12)
    (by have := h.w1; omega) (by have := h.w2; omega) (by omega)) fun t ⟨hz, o, k₃⟩ => ?_
  rw [m₂, m₁] at o
  exact ⟨hz, o, ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `copyA o a`: `[o] := [a]` over `w` words. -/
theorem copyA_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {o a : Nat} (ho : o < 16) (ha : a < 16)
    (hoa : o ≠ a) :
    WP isa (copyA o a) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w a) w ∧ VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w o) (8 * w) s.mem t.mem ∧
        VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .rsi, .rbx, .rax, .r14] s t := by
  have hn := h.scr.nowrap
  have so := h.sl ho
  have sa := h.sl ha
  have sp := VG.Proof.Rsa.X86_64.slot_far (w := w) hoa
  unfold copyA
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (VG.Proof.Rsa.X86_64.base2_ok a o (r₁ := .rsi) (r₂ := .rbx) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide)) fun s₂ ⟨hsi, hbx, m₂, k₂⟩ => ?_))
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (copyWords_ok hsi hbx ((k₂.gpr (by decide)).trans h12) (by have := h.w1; omega)
    (by have := h.w2; omega) (by omega) (fun i hi => hs₂.ld (by omega)) (fun i hi => hs₂.st (by omega))
    (fun i hi b hb => by rw [VG.Proof.Bignum.X86_64.ofs_off B (by omega)]; omega)) fun t ⟨hv, _, o', k₃⟩ => ?_
  rw [m₂, m₁] at hv o'
  exact ⟨hv, o', ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-! ## Bytes -/

/-- `loadA j sPtr sLen`: `[j] := ` the `len` bytes at `p`, most significant
first, over `w` words. -/
theorem loadA_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {j sPtr sLen len : Nat} {p : Addr}
    {bs : List Byte} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (hp : VG.Proof.Bignum.X86_64.word s.mem B (8 * sPtr) = p) (hl : VG.Proof.Bignum.X86_64.word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hsrc : Src s B Z p bs) (hlen : bs.length = len) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * w) :
    WP isa (seqs (loadA j sPtr sLen)) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w j) w = Spec.Rsa.os2ip bs ∧ VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w j) (8 * (w + 2)) s.mem t.mem ∧
        VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .r8, .rax, .r14, .rbx, .rsi, .rcx, .rdx, .rbp] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have hw2 := h.w2
  simp only [loadA, seqs]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.zeroA_ok h hj) fun s₁ ⟨hz, o₁, k₁⟩ => ?_)
  have h₁ : VG.Proof.Rsa.X86_64.Ws s₁ B Z w := h.congr (Frm.of_outside o₁ (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Mut.ofSlot w j _) k₁ (by decide)
  have hh : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₁.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi =>
    o₁.word (Or.inl (by have := hdr_lt_slot w j hi; omega)) (by omega)
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h₁.ws_ok fun s₂ ⟨h12, h9, m₂, k₂⟩ =>
    WP.mono (VG.Proof.Rsa.X86_64.base_ok j (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h₁.rdi) h9) fun s₃ ⟨hbx, m₃, k₃⟩ =>
      WP.mono (WP.keep [.rsi, .rcx] (Q := fun t => t.gpr .rsi = p ∧ t.gpr .rcx = BitVec.ofNat 64 len ∧
        t.mem = s₃.mem) (by
          have hdi₃ : s₃.gpr .rdi = B := ((k₂.trans k₃).gpr (by decide)).trans h₁.rdi
          have hs₃ := h₁.scr.congr (k₂.trans k₃).2.2
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi₃, hdrOff, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL, hh sPtr hP, hh sLen hL, hp, hl]) rfl)
      fun s₄ ⟨⟨hsi, hcx, m₄⟩, k₄⟩ => ?_)))
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hs₄ := h.scr.congr k14.2.2
  have hsrc₄ : Src s₄ B Z p bs := hsrc.congrK (fun x hx => by
    rw [m₄, m₃, m₂]; exact o₁ x (Or.inr (by omega))) k14
  refine WP.mono (loadBE_ok (w := (len + 7) / 8) hs₄ hsi hcx ((k₄.gpr (by decide)).trans hbx) hlen hl1 (by omega) rfl
    (by omega) (fun i hi => hsrc₄.rd i (by omega)) (fun i hi => hsrc₄.val i (by omega))
    (fun i hi => Or.inr (by have := hsrc₄.out i (by omega); omega))) fun t ⟨hv, o, k₅⟩ => ?_
  rw [m₄, m₃, m₂] at o
  refine ⟨?_, fun x hx => by rw [o x (by omega), o₁ x hx], (k14.trans k₅).mono (by simp)⟩
  -- The words above the loaded ones are still zero.
  have hz' : ∀ q < w + 2, VG.Proof.Bignum.X86_64.word s₁.mem B (VG.Proof.Bignum.X86_64.slot w j + 8 * q) = 0 := (wv_eq_zero_iff _ _ _ _).mp hz
  have e := wv_add t.mem B (VG.Proof.Bignum.X86_64.slot w j) ((len + 7) / 8) (w - (len + 7) / 8)
  rw [show (len + 7) / 8 + (w - (len + 7) / 8) = w by omega] at e
  rw [e, hv, VG.Proof.Rsa.X86_64.wv_zero (n := w - (len + 7) / 8) fun q hq => by
      rw [o.word (by omega) (by omega), Nat.add_assoc, ← Nat.mul_add]; exact hz' _ (by omega)]
  simp

/-- `storeA j sPtr sLen sMsk`: the low `⌈len / 8⌉` words of `[j]`, masked by
the slot `sMsk`, as `len` bytes at `out`. -/
theorem storeA_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {j sPtr sLen sMsk len : Nat} {out : Addr}
    {c : Bool} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (hM : sMsk < 32)
    (hp : VG.Proof.Bignum.X86_64.word s.mem B (8 * sPtr) = out) (hl : VG.Proof.Bignum.X86_64.word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hm : VG.Proof.Bignum.X86_64.word s.mem B (8 * sMsk) = VG.Proof.Bignum.X86_64.mask c) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * w)
    (hout : ∀ i < len, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < len, Z ≤ VG.Proof.Bignum.X86_64.ofs B (out + BitVec.ofNat 64 i)) :
    WP isa (seqs (storeA j sPtr sLen sMsk)) s fun t =>
      (List.range len).map (fun i => t.mem (out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (VG.Proof.Bignum.X86_64.slot w j) ((len + 7) / 8) else 0) len ∧
      (∀ x, (∀ i < len, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ t.wr = s.wr ∧ t.rd = s.rd ∧
      VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .rbx, .rsi, .rcx, .r15, .rax, .rdx, .rbp, .r14] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have hw2 := h.w2
  simp only [storeA, seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨h12, h9, m₂, k₂⟩ =>
    WP.mono (VG.Proof.Rsa.X86_64.base_ok j (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h.rdi) h9) fun s₃ ⟨hbx, m₃, k₃⟩ =>
      WP.mono (WP.keep [.rsi, .rcx, .r15] (Q := fun t => t.gpr .rsi = out ∧ t.gpr .rcx = BitVec.ofNat 64 len ∧
        t.gpr .r15 = VG.Proof.Bignum.X86_64.mask c ∧ t.mem = s₃.mem) (by
          have hdi₃ : s₃.gpr .rdi = B := ((k₂.trans k₃).gpr (by decide)).trans h.rdi
          have hs₃ := h.scr.congr (k₂.trans k₃).2.2
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi₃, hdrOff, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL, hl₃ sMsk hM, hp, hl, hm]) rfl)
      fun s₄ ⟨⟨hsi, hcx, h15, m₄⟩, k₄⟩ => ?_)))
  have k24 := (k₂.trans k₃).trans k₄
  refine WP.mono (storeBE_ok (w := (len + 7) / 8) (h.scr.congr k24.2.2) ((k₄.gpr (by decide)).trans hbx) hsi hcx h15
    hl1 (by omega) rfl (by omega) (fun i hi => by rw [k24.2.2]; exact hout i hi) hsep)
    fun t ⟨hb, hx, hwr, hrd, k₅⟩ => ?_
  rw [m₄, m₃, m₂] at hb hx
  exact ⟨hb, hx, hwr.trans k24.2.2, hrd.trans k24.2.1, (k24.trans k₅).mono (by simp)⟩

/-- A number below `2^(64 v)` is its low `v` words. -/
theorem wv_low_of_lt {m : Mem} {B : Addr} {e v w : Nat} (hv : v ≤ w) (h : wv m B e w < 2 ^ (64 * v)) :
    wv m B e v = wv m B e w := by
  have e1 := wv_add m B e v (w - v)
  rw [show v + (w - v) = w by omega] at e1
  have : wv m B (e + 8 * v) (w - v) = 0 := by
    rcases Nat.eq_zero_or_pos (wv m B (e + 8 * v) (w - v)) with h0 | h0
    · exact h0
    · exfalso
      have : 2 ^ (64 * v) ≤ 2 ^ (64 * v) * wv m B (e + 8 * v) (w - v) := Nat.le_mul_of_pos_right _ h0
      omega
  rw [e1, this]; simp

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.CTBase`. -/
section

/-!
# RSA key routines on x86-64: relational constant time, piece by piece

The routines reload `w` and the stride from the header (`ws`) and compute
every array's base from them, so the taint analysis, to which the header's
words are secret once a secret is stored through such a base, cannot see
that their addresses are public. Each piece is checked from a state where
the registers it needs are pinned, by correctness, to values of the public
data (`pin_ct`): `ws_ct` pins `rdi`, `r12` and `r9` after `ws`, and checks
the rest of the piece with the taint analysis.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- A block followed by code, as its two parts in sequence: it runs the same
and leaks the same trace. -/
theorem RelCT.block_seq {P Q : State → State → Prop} {l₁ l₂ : List Instr} {c : Prog isa}
    (h : RelCT isa P (.seq (.block l₁) (.seq (.block l₂) c)) Q) : RelCT isa P (.seq (.block (l₁ ++ l₂)) c) Q := by
  have split : ∀ {s t s'}, Exec isa (.seq (.block (l₁ ++ l₂)) c) s t s' →
      Exec isa (.seq (.block l₁) (.seq (.block l₂) c)) s t s' := by
    intro s t s' e
    cases e with
    | seq eb ec =>
      rw [Exec.block_iff, execBlock_append] at eb
      obtain ⟨⟨a, u⟩, ha, hb⟩ := Option.bind_eq_some_iff.mp eb
      obtain ⟨⟨b, v⟩, hc, he⟩ := Option.map_eq_some_iff.mp hb
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [List.append_assoc]
      exact .seq (.block ha) (.seq (.block hc) ec)
  exact fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (split e₁) (split e₂)

theorem WP.block_seq_iff {l₁ l₂ : List Instr} {c : Prog isa} {s : State} {Q : State → Prop} :
    WP isa (.seq (.block (l₁ ++ l₂)) c) s Q ↔ WP isa (.seq (.block l₁) (.seq (.block l₂) c)) s Q := by
  rw [WP.seq_iff, WP.block_append_iff, WP.seq_iff]
  exact ⟨fun h => WP.mono h fun t h' => WP.seq_iff.mpr h', fun h => WP.mono h fun t h' => WP.seq_iff.mp h'⟩

/-- Code checked by the taint analysis from the registers `rs₁`, which `Φ a`
pins, and which leaves the registers `rs₂` with values of `a`; then code
checked from `rs₂`. -/
theorem pin_ct {α : Type} {Φ Ψ : α → State → Prop} {c₁ c₂ : Prog isa} (rs₁ rs₂ : List Reg)
    (f : α → Reg → BitVec 64) (hpin : Pins Φ rs₁) {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs rs₁) c₁ hc₁).isSome = true)
    (hp : ∀ a s, Φ a s → WP isa c₁ s fun t => ∀ r ∈ rs₂, t.gpr r = f a r)
    {hc₂ : VG.Taint.Hint VG.X86_64.Taint.T} (ht₂ : (taint.check (Taint.ofRegs rs₂) c₂ hc₂).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.seq c₁ c₂) s (Ψ a)) :
    RelCT isa (Two Φ) (.seq c₁ c₂) (Two Ψ) :=
  RelCT.seq (two_piece (Ψ := fun a t => (∀ r ∈ rs₂, t.gpr r = f a r) ∧ WP isa c₂ t (Ψ a)) rs₁ hpin ht₁
      fun a s h => WP.and (hp a s h) (WP.seq_iff.mp (hw a s h)))
    (two_post (two_taint rs₂ (fun _ _ _ h₁ h₂ r hr => (h₁.1 r hr).trans (h₂.1 r hr).symm) ht₂)
      fun _ _ h => h.2)

/-- The registers `ws` pins: `rdi`, `w` in `r12` and the stride in `r9`. -/
def wsVal (B : Addr) (w : Nat) : Reg → BitVec 64
  | .rdi => B
  | .r12 => BitVec.ofNat 64 w
  | .r9 => BitVec.ofNat 64 (8 * (w + 2))
  | _ => 0

/-- `ws` and then code checked by the taint analysis from `rdi`, `r12` and
`r9`, from states with the working space of the public data `a`. -/
theorem ws_ct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat) {rest : List Instr}
    {body : Prog isa} (hws : ∀ a s, Φ a s → VG.Proof.Rsa.X86_64.Ws s (B a) (Z a) (w a)) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block rest) body) hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ rest)) body) s (Ψ a)) :
    RelCT isa (Two Φ) (.seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ rest)) body) (Two Ψ) :=
  RelCT.block_seq (VG.Proof.Rsa.X86_64.pin_ct [.rdi] [.rdi, .r12, .r9] (fun a => VG.Proof.Rsa.X86_64.wsVal (B a) (w a))
    (fun a s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(hws a s₁ h₁).rdi, (hws a s₂ h₂).rdi])
    (by taint_decide)
    (fun a s h => WP.mono (hws a s h).ws_ok fun t ⟨h12, h9, _, k⟩ => fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (k.gpr (by decide)).trans (hws a s h).rdi
      · exact h12
      · exact h9)
    ht fun a s h => WP.block_seq_iff.mp (hw a s h))

/-- `ws_ct` for a block. -/
theorem ws_block_ct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat) {rest : List Instr}
    (hws : ∀ a s, Φ a s → VG.Proof.Rsa.X86_64.Ws s (B a) (Z a) (w a)) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block rest) hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ rest)) s (Ψ a)) :
    RelCT isa (Two Φ) (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ rest)) (Two Ψ) :=
  RelCT.block_append (VG.Proof.Rsa.X86_64.pin_ct [.rdi] [.rdi, .r12, .r9] (fun a => VG.Proof.Rsa.X86_64.wsVal (B a) (w a))
    (fun a s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(hws a s₁ h₁).rdi, (hws a s₂ h₂).rdi])
    (by taint_decide)
    (fun a s h => WP.mono (hws a s h).ws_ok fun t ⟨h12, h9, _, k⟩ => fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (k.gpr (by decide)).trans (hws a s h).rdi
      · exact h12
      · exact h9)
    ht fun a s h => WP.seq_iff.mpr (WP.block_append_iff.mp (hw a s h)))

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.CvHead`. -/
section

/-!
# `vg_rsa_crt_values` on x86-64: the arguments and the head

`CvArgs`: the arguments `entry` leaves in the header, kept by the pieces
(`CvArgs.congr`). `cvHead_ok`: `head` sets up the working space (`Ws`) for
`w = ⌈k / 8⌉` and the mask all ones.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- The arguments in the header: the outputs' pointers, `n`'s pointer and
length, `p`'s, `q`'s and `d`'s pointers and lengths, and the saved
registers `sv`. -/
structure CvArgs (m : Mem) (B : Addr) (k pl ql dl : Nat) (pDp pDq pQi pN pP pQ pD : Addr)
    (sv : Nat → BitVec 64) : Prop where
  dp : VG.Proof.Bignum.X86_64.word m B (8 * sDp) = pDp
  dq : VG.Proof.Bignum.X86_64.word m B (8 * sDq) = pDq
  qi : VG.Proof.Bignum.X86_64.word m B (8 * sQi) = pQi
  n : VG.Proof.Bignum.X86_64.word m B (8 * Impl.Bignum.X86_64.Public.sN) = pN
  k : VG.Proof.Bignum.X86_64.word m B (8 * Impl.Bignum.X86_64.Public.sK) = BitVec.ofNat 64 k
  p : VG.Proof.Bignum.X86_64.word m B (8 * VG.Impl.Rsa.X86_64.Keys.CrtValues.sP) = pP
  pl : VG.Proof.Bignum.X86_64.word m B (8 * sPl) = BitVec.ofNat 64 pl
  q : VG.Proof.Bignum.X86_64.word m B (8 * VG.Impl.Rsa.X86_64.Keys.CrtValues.sQ) = pQ
  ql : VG.Proof.Bignum.X86_64.word m B (8 * sQl) = BitVec.ofNat 64 ql
  d : VG.Proof.Bignum.X86_64.word m B (8 * VG.Impl.Rsa.X86_64.Keys.CrtValues.sD) = pD
  dl : VG.Proof.Bignum.X86_64.word m B (8 * VG.Impl.Rsa.X86_64.Keys.CrtValues.sDl) = BitVec.ofNat 64 dl
  saved : ∀ i < 6, VG.Proof.Bignum.X86_64.word m B (8 * i) = sv i

/-- The header slots of `CvArgs`. -/
def argSlot (i : Nat) : Prop := i < 6 ∨ (16 ≤ i ∧ i < 22) ∨ (23 ≤ i ∧ i < 28)

theorem CvArgs.congr {m m' : Mem} {B : Addr} {k pl ql dl : Nat} {pDp pDq pQi pN pP pQ pD : Addr}
    {sv : Nat → BitVec 64} (h : VG.Proof.Rsa.X86_64.CvArgs m B k pl ql dl pDp pDq pQi pN pP pQ pD sv)
    (hm : ∀ i, VG.Proof.Rsa.X86_64.argSlot i → VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i)) :
    VG.Proof.Rsa.X86_64.CvArgs m' B k pl ql dl pDp pDq pQi pN pP pQ pD sv :=
  ⟨(hm _ (by simp [VG.Proof.Rsa.X86_64.argSlot, sDp, sFn])).trans h.dp, (hm _ (by simp [VG.Proof.Rsa.X86_64.argSlot, sDq, sFn])).trans h.dq,
    (hm _ (by simp [VG.Proof.Rsa.X86_64.argSlot, sQi, sFn])).trans h.qi,
    (hm _ (by simp [VG.Proof.Rsa.X86_64.argSlot, Impl.Bignum.X86_64.Public.sN, sFn])).trans h.n,
    (hm _ (by simp [VG.Proof.Rsa.X86_64.argSlot, Impl.Bignum.X86_64.Public.sK, sFn])).trans h.k,
    (hm _ (by simp [VG.Proof.Rsa.X86_64.argSlot, VG.Impl.Rsa.X86_64.Keys.CrtValues.sP, sFn])).trans h.p, (hm _ (by simp [VG.Proof.Rsa.X86_64.argSlot, sPl, sFn])).trans h.pl,
    (hm _ (by simp [VG.Proof.Rsa.X86_64.argSlot, VG.Impl.Rsa.X86_64.Keys.CrtValues.sQ, sFn])).trans h.q, (hm _ (by simp [VG.Proof.Rsa.X86_64.argSlot, sQl, sFn])).trans h.ql,
    (hm _ (by simp [VG.Proof.Rsa.X86_64.argSlot, VG.Impl.Rsa.X86_64.Keys.CrtValues.sD, sFn])).trans h.d, (hm _ (by simp [VG.Proof.Rsa.X86_64.argSlot, VG.Impl.Rsa.X86_64.Keys.CrtValues.sDl, sFn])).trans h.dl,
    fun i hi => (hm i (Or.inl hi)).trans (h.saved i hi)⟩

/-- The argument slots, after code that changes only ranges that `Mut`
allows. -/
theorem argSlot_frm {m m' : Mem} {B : Addr} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hr : ∀ r ∈ rs, VG.Proof.Rsa.X86_64.Mut r) :
    ∀ i, VG.Proof.Rsa.X86_64.argSlot i → VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i) := fun i hi => by
  unfold VG.Proof.Rsa.X86_64.argSlot at hi
  exact hf.word_eq (fun r hr' => by
    rcases hr r hr' with h | rfl | rfl
    · omega
    · simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega
    · simp only [sMo, sFn]; omega) (by omega)

/-- The words of `w = ⌈k / 8⌉` for `64 ≤ k ≤ 1024`. -/
abbrev wk (k : Nat) : Nat := (k + 7) / 8

/-- `head`: `w`, the arrays' bases, the stride, and the mask all ones. -/
theorem cvHead_ok {s : State} {B : Addr} {Z k : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B) (hk1 : 64 ≤ k)
    (hk2 : k ≤ 1024) (hZ : 128 * k ≤ Z) (hK : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sK) = BitVec.ofNat 64 k) :
    WP isa (.block head) s fun t =>
      VG.Proof.Rsa.X86_64.Ws t B Z (VG.Proof.Rsa.X86_64.wk k) ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = VG.Proof.Bignum.X86_64.mask true ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64), (8 * sStride, 8), (8 * Impl.Bignum.X86_64.Public.sMask, 8)]
        s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .r12] s t := by
  have hn := hs.nowrap
  have hZ16 : VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk k) 16 ≤ Z := by simp only [VG.Proof.Bignum.X86_64.slot, hdrBytes, VG.Proof.Rsa.X86_64.wk]; omega
  have h8 := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk k) 8 (show 31 < 32 by decide)
  have eK : Impl.Bignum.X86_64.Public.sK = 18 := rfl
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have hl8 : VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk k) 8 ≤ VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk k) 16 := by unfold VG.Proof.Bignum.X86_64.slot; omega
  unfold head
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx, .r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (VG.Proof.Rsa.X86_64.wk k) ∧
      t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sW)) (BitVec.ofNat 64 (VG.Proof.Rsa.X86_64.wk k))) ?_ rfl)
    fun t₁ ⟨⟨h12, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, hdrOff, hs.ld (d := 8 * Impl.Bignum.X86_64.Public.sK) (by omega),
      hs.st (d := 8 * sW) (by omega), hK, shr3_w k (by omega)]
  have hs₁ := hs.congr k₁.2.2
  refine WP.mono (setBases_ok hs₁ ((k₁.gpr (by decide)).trans hdi) h12 (by unfold sArr; omega))
    fun t₂ ⟨hb₂, ho₂, k₂⟩ => ?_
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi)
  have h12₂ : t₂.gpr .r12 = BitVec.ofNat 64 (VG.Proof.Rsa.X86_64.wk k) := (k₂.gpr (by decide)).trans h12
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = (t₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sStride))
      (BitVec.ofNat 64 (8 * (VG.Proof.Rsa.X86_64.wk k + 2)))).writeW (VG.Proof.Bignum.X86_64.off B (8 * Impl.Bignum.X86_64.Public.sMask)) (VG.Proof.Bignum.X86_64.mask true)) (by
    xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi₂, hdrOff, h12₂, hs₂.st (d := 8 * sStride) (by omega),
      hs₂.st (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by omega), VG.Proof.Rsa.X86_64.ofNat_dbl]
    congr 2
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, VG.Proof.Rsa.X86_64.ofNat_dbl, VG.Proof.Rsa.X86_64.ofNat_dbl, VG.Proof.Rsa.X86_64.ofNat_dbl]
    congr 1; omega) rfl) fun t ⟨hm, k₃⟩ => ?_
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside t₂.mem B (BitVec.ofNat 64 (8 * (VG.Proof.Rsa.X86_64.wk k + 2))) (d := 8 * sStride) (by omega)
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside (t₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sStride)) (BitVec.ofNat 64 (8 * (VG.Proof.Rsa.X86_64.wk k + 2)))) B (VG.Proof.Bignum.X86_64.mask true)
    (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by omega)
  have hw : ∀ i < 32, i ≠ sStride → i ≠ Impl.Bignum.X86_64.Public.sMask → VG.Proof.Bignum.X86_64.word t.mem B (8 * i) = VG.Proof.Bignum.X86_64.word t₂.mem B (8 * i) :=
    fun i hi h1 h2 => by rw [hm, o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
  have kk := ((k₁.trans k₂).trans k₃)
  refine ⟨⟨hs₂.congr k₃.2.2, (k₃.gpr (by decide)).trans hdi₂, ?_, ?_, fun j hj => ?_, hZ16, by unfold VG.Proof.Rsa.X86_64.wk; omega,
    by unfold VG.Proof.Rsa.X86_64.wk; omega⟩, by rw [hm, VG.Proof.Bignum.X86_64.word_writeW_self], ?_, kk.mono (by simp)⟩
  · rw [hw sW (by decide) (by decide) (by decide), ho₂.word (by omega) (by omega), hm₁, VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hm, o2.word (by omega) (by omega), VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hw (sArr j) (by unfold sArr; omega) (by unfold sArr sStride sFn; omega)
      (by unfold sArr Impl.Bignum.X86_64.Public.sMask sFn; omega)]
    exact hb₂ j hj
  · intro x hx
    have a := hx (8 * sW, 8) (by simp)
    have b := hx (8 * sArr 0, 64) (by simp)
    have c := hx (8 * sStride, 8) (by simp)
    have d := hx (8 * Impl.Bignum.X86_64.Public.sMask, 8) (by simp)
    dsimp only at a b c d
    rw [hm, o2 x d, o1 x c, ho₂ x b, hm₁, VG.Proof.Bignum.X86_64.writeW_outside s.mem B _ (by omega) x a]

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.CvLoad`. -/
section

/-!
# `vg_rsa_crt_values` on x86-64: the loads and the check of `p q = n`

`CvS`: what every piece of `main` keeps (the working space, the arguments,
the inputs' bytes, and memory outside the working space), from a frame of
ranges `Mut` allows (`CvS.step`). The loads of `n`, `p`, `q` and `d` and
the mask of `p q = n` (`cvLoad_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- The inputs of `vg_rsa_crt_values` and where they are. -/
structure CvIn where
  B : Addr
  Z : Nat
  k : Nat
  pl : Nat
  ql : Nat
  dl : Nat
  pDp : Addr
  pDq : Addr
  pQi : Addr
  pN : Addr
  pP : Addr
  pQ : Addr
  pD : Addr
  sv : Nat → BitVec 64
  nb : List Byte
  pb : List Byte
  qb : List Byte
  db : List Byte
  W : List Region
  sp : BitVec 64

/-- What every piece of `main` keeps, from the memory `m₀` on entry to
`main`. -/
structure CvS (I : VG.Proof.Rsa.X86_64.CvIn) (m₀ : Mem) (s : State) : Prop where
  ws : VG.Proof.Rsa.X86_64.Ws s I.B I.Z (VG.Proof.Rsa.X86_64.wk I.k)
  args : VG.Proof.Rsa.X86_64.CvArgs s.mem I.B I.k I.pl I.ql I.dl I.pDp I.pDq I.pQi I.pN I.pP I.pQ I.pD I.sv
  n : Src s I.B I.Z I.pN I.nb
  p : Src s I.B I.Z I.pP I.pb
  q : Src s I.B I.Z I.pQ I.qb
  d : Src s I.B I.Z I.pD I.db
  inScr : InScr I.B I.Z m₀ s.mem
  wr : s.wr = I.W
  rsp : s.gpr .rsp = I.sp

theorem CvS.step {I : VG.Proof.Rsa.X86_64.CvIn} {m₀ : Mem} {s t : State} (h : VG.Proof.Rsa.X86_64.CvS I m₀ s) {rs : List (Nat × Nat)}
    (hf : Frm I.B rs s.mem t.mem) (hm : ∀ r ∈ rs, VG.Proof.Rsa.X86_64.Mut r) (hz : ∀ r ∈ rs, r.1 + r.2 ≤ I.Z) {regs : List Reg}
    (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : VG.Proof.Rsa.X86_64.CvS I m₀ t :=
  have hi : InScr I.B I.Z s.mem t.mem := InScr.of_frm hf hz
  ⟨h.ws.congr hf hm k hr.1, h.args.congr (VG.Proof.Rsa.X86_64.argSlot_frm hf hm), h.n.congrK hi k, h.p.congrK hi k, h.q.congrK hi k,
    h.d.congrK hi k, h.inScr.trans hi, k.2.2.trans h.wr, (k.gpr hr.2).trans h.rsp⟩

/-- `CvS` after a piece that changes only array `j`'s first `n` bytes. -/
theorem CvS.arr {I : VG.Proof.Rsa.X86_64.CvIn} {m₀ : Mem} {s t : State} (h : VG.Proof.Rsa.X86_64.CvS I m₀ s) {j n : Nat} (hj : j < 16)
    (hn : n ≤ 8 * (VG.Proof.Rsa.X86_64.wk I.k + 2)) (ho : VG.Proof.Bignum.X86_64.Outside I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) n s.mem t.mem) {regs : List Reg}
    (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : VG.Proof.Rsa.X86_64.CvS I m₀ t :=
  h.step (Frm.of_outside ho (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]; have := h.ws.sl hj; dsimp only; omega) k hr

/-! ## Masks -/

/-- `eqA a b`: `rbp = 0` iff `[a] = [b]` over `w` words. -/
theorem eqA_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {a b : Nat} (ha : a < 16) (hb : b < 16) :
    WP isa (seqs (eqA a b)) s fun t =>
      (t.gpr .rbp = 0 ↔ wv s.mem B (VG.Proof.Bignum.X86_64.slot w a) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w) ∧ t.mem = s.mem ∧
        VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .rbx, .r10, .rbp, .rax, .r14] s t := by
  have hn := h.scr.nowrap
  have sa := h.sl ha
  have sb := h.sl hb
  simp only [eqA, seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (Q := fun (t : State) => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w a) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w b) ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .rbx, .r10] s t) ?_ fun s₁ ⟨h12, hbx, h10, m₁, k₁⟩ =>
    WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = 0 ∧ t.mem = s₁.mem) (by xrun) rfl)
      fun s₂ ⟨⟨hbp, m₂⟩, k₂⟩ => ?_))
  · rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono h.ws_ok fun t₁ ⟨e12, e9, n₁, j₁⟩ => ?_
    refine WP.mono (VG.Proof.Rsa.X86_64.base2_ok a b (r₁ := .rbx) (r₂ := .r10) (by decide) (by decide) (by decide)
      ((j₁.gpr (by decide)).trans h.rdi) e9 (by decide)) fun t ⟨e1, e2, n₂, j₂⟩ => ?_
    exact ⟨(j₂.gpr (by decide)).trans e12, e1, e2, n₂.trans n₁, (j₁.trans j₂).mono (by simp)⟩
  have k12 := k₁.trans k₂
  have hs₂ := h.scr.congr k12.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₂.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s₂ t → t.cf = s₂.cf →
      OrInv s₂ B Z (fun j => ∀ i < j, VG.Proof.Bignum.X86_64.word s₂.mem B (VG.Proof.Bignum.X86_64.slot w a + 8 * i) = VG.Proof.Bignum.X86_64.word s₂.mem B (VG.Proof.Bignum.X86_64.slot w b + 8 * i))
        0 t := fun t h14 hm k _ =>
    ⟨hs₂.congr k.2.2, k.mono (by decide), hm, h14, by
      rw [(k.gpr (by decide) : t.gpr .rbp = s₂.gpr .rbp), hbp]
      exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by have := h.w1; omega) (by have := h.w2; omega) _ h0
    (fun j _ hj t hI => xorStep_ok ((k₂.gpr (by decide)).trans hbx) ((k₂.gpr (by decide)).trans h10)
      ((k₂.gpr (by decide)).trans h12) (by have := h.w2; omega) (by omega) (by omega) hj hI)) fun t hI => ?_
  rw [m₂, m₁] at hI
  refine ⟨?_, by rw [hI.mem, m₂, m₁], (k12.trans hI.keep).mono (by simp)⟩
  rw [hI.val]
  exact ⟨fun hw => wv_congr2 fun i hi => hw i hi, fun hw => wv_inj (d := VG.Proof.Bignum.X86_64.slot w a) (e := VG.Proof.Bignum.X86_64.slot w b) w hw⟩

theorem decide_lt_one' (x : BitVec 64) : decide (x.toNat < (1 : BitVec 64).toNat) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ← BitVec.toNat_inj,
    show (1 : BitVec 64).toNat = 1 from rfl, show (0 : BitVec 64).toNat = 0 from rfl]
  constructor <;> intro h <;> omega

/-- `andZero`: the mask of `rbp = 0` and'ed into `sMask`. -/
theorem andZero_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {c : Bool}
    (hm : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = VG.Proof.Bignum.X86_64.mask c) {z : Prop} [Decidable z]
    (hz : s.gpr .rbp = 0 ↔ z) :
    WP isa (.block andZero) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * Impl.Bignum.X86_64.Public.sMask)) (VG.Proof.Bignum.X86_64.mask (c && decide z)) ∧ VG.Proof.MlKem.X86_64.Keep [.rbp] s t := by
  have hl := h.scr.ld (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by have := h.h256; unfold Impl.Bignum.X86_64.Public.sMask sFn; omega)
  have hst := h.scr.st (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by have := h.h256; unfold Impl.Bignum.X86_64.Public.sMask sFn; omega)
  have e : decide (s.gpr .rbp = 0) = decide z := by
    by_cases hz' : z
    · rw [decide_eq_true hz', decide_eq_true (hz.mpr hz')]
    · rw [decide_eq_false hz', decide_eq_false (fun h => hz' (hz.mp h))]
  refine WP.keep [.rbp] (Q := fun t => t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * Impl.Bignum.X86_64.Public.sMask))
    (VG.Proof.Bignum.X86_64.mask (c && decide z))) ?_ rfl
  unfold andZero
  xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, h.rdi, hdrOff, hl, hst, hm, VG.Proof.Rsa.X86_64.decide_lt_one', e]
  congr 1
  rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide z))) = VG.Proof.Bignum.X86_64.mask (decide z) from rfl, BitVec.and_comm,
    VG.Proof.Rsa.X86_64.mask_and']

/-- `andOdd j`: the mask of `[j]` odd and'ed into `sMask`. -/
theorem andOdd_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {j : Nat} (hj : j < 16) {c : Bool}
    (hm : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = VG.Proof.Bignum.X86_64.mask c) :
    WP isa (.block (andOdd j)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * Impl.Bignum.X86_64.Public.sMask))
        (VG.Proof.Bignum.X86_64.mask (decide (wv s.mem B (VG.Proof.Bignum.X86_64.slot w j) w % 2 = 1) && c)) ∧
        VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .rbx, .rax, .rdx] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have hst := h.scr.st (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by have := h.h256; unfold Impl.Bignum.X86_64.Public.sMask sFn; omega)
  unfold andOdd
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok j (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  have hdi₂ : s₂.gpr .rdi = B := ((k₁.trans k₂).gpr (by decide)).trans h.rdi
  have e0 : (s.mem.readW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j)) 64).toNat % 2 = wv s.mem B (VG.Proof.Bignum.X86_64.slot w j) w % 2 := by
    rw [← wv_mod64 s.mem B (VG.Proof.Bignum.X86_64.slot w j) (n := w) (by have := h.w1; omega), Nat.mod_mod_of_dvd _ (by decide)]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * Impl.Bignum.X86_64.Public.sMask))
      (VG.Proof.Bignum.X86_64.mask (decide (wv s.mem B (VG.Proof.Bignum.X86_64.slot w j) w % 2 = 1) && c))) (by
    xrun [State.ea, at0, VG.Impl.Bignum.X86_64.hdr, hdi₂, hdrOff, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.ld (d := VG.Proof.Bignum.X86_64.slot w j) (by omega), hs₂.ld (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by
        have := h.h256; unfold Impl.Bignum.X86_64.Public.sMask sFn; omega), hs₂.st (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by
        have := h.h256; unfold Impl.Bignum.X86_64.Public.sMask sFn; omega), m₂, m₁, hm, VG.Proof.Rsa.X86_64.mask_low, e0]
    rw [VG.Proof.Rsa.X86_64.mask_and']) rfl) fun t ⟨mt, k₃⟩ => ⟨mt, ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `setOneA j`: word 0 of `[j]` := 1. -/
theorem setOneA_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {j : Nat} (hj : j < 16) :
    WP isa (.block (setOneA j)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j)) (1 : BitVec 64) ∧ VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .rbx, .rax] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  unfold setOneA
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok j (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j)) (1 : BitVec 64)) (by
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.st (d := VG.Proof.Bignum.X86_64.slot w j) (by omega), m₂, m₁]
    rfl) rfl) fun t ⟨mt, k₃⟩ => ⟨mt, ((k₁.trans k₂).trans k₃).mono (by simp)⟩

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.CvCheck`. -/
section

/-!
# `vg_rsa_crt_values` on x86-64: the loads and the check of `p q = n`

The loads of `n`, `p`, `q` and `d` (`cvLoads_ok`), and the mask of
`p q = n` (`cvCheck_ok`), as `n mod p = 0`, `n / p = q` and `p` odd
(`pq_iff`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-- `p q = n` for an odd `n`, as `pqCheck` checks it. -/
theorem pq_iff {N P Q : Nat} (hN : N % 2 = 1) :
    (P % 2 = 1 ∧ N / P = Q ∧ N % P = 0) ↔ P * Q = N := by
  constructor
  · rintro ⟨hp, hq, hr⟩
    have := Nat.div_add_mod N P
    rw [hq, hr, Nat.add_zero] at this
    exact this
  · intro h
    have hp : P % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one P with hP | hP
      · rw [← h, Nat.mul_mod, hP, Nat.zero_mul] at hN; exact absurd hN (by decide)
      · exact hP
    have hP0 : 0 < P := by omega
    refine ⟨hp, ?_, ?_⟩
    · rw [← h, Nat.mul_div_cancel_left _ hP0]
    · rw [← h, Nat.mul_mod_right]

/-- The memory word of the mask. -/
abbrev mword (m : Mem) (B : Addr) : BitVec 64 := VG.Proof.Bignum.X86_64.word m B (8 * Impl.Bignum.X86_64.Public.sMask)

/-- `CvS` and the mask, after a store to the mask's slot. -/
theorem CvS.mask {I : VG.Proof.Rsa.X86_64.CvIn} {m₀ : Mem} {s t : State} (h : VG.Proof.Rsa.X86_64.CvS I m₀ s) {v : BitVec 64}
    (hm : t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off I.B (8 * Impl.Bignum.X86_64.Public.sMask)) v) {regs : List Reg}
    (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : VG.Proof.Rsa.X86_64.CvS I m₀ t ∧ VG.Proof.Rsa.X86_64.mword t.mem I.B = v ∧
      ∀ j < 16, wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k + 2) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k + 2) := by
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have ho := VG.Proof.Bignum.X86_64.writeW_outside s.mem I.B v (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by omega)
  rw [← hm] at ho
  refine ⟨h.step (Frm.of_outside ho (List.mem_singleton_self _)) (fun r hr => ?_) (fun r hr => ?_) k hr,
    by rw [hm]; exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _, fun j hj => ho.wv (Or.inr ?_) (by have := h.ws.sl hj; omega)⟩
  · rw [List.mem_singleton.mp hr]; exact Or.inr (Or.inl rfl)
  · rw [List.mem_singleton.mp hr]; simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega
  · have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega

/-- The bounds on the lengths. -/
structure CvLens (I : VG.Proof.Rsa.X86_64.CvIn) : Prop where
  k1 : 64 ≤ I.k
  k2 : I.k ≤ 1024
  pl1 : 1 ≤ I.pl
  pl2 : I.pl < I.k
  ql1 : 1 ≤ I.ql
  ql2 : I.ql < I.k
  dl1 : 1 ≤ I.dl
  dl2 : I.dl ≤ I.k
  nl : I.nb.length = I.k
  pbl : I.pb.length = I.pl
  qbl : I.qb.length = I.ql
  dbl : I.db.length = I.dl
  z : 128 * I.k ≤ I.Z

/-- An array other than the one that changed. -/
theorem outside_arr {m m' : Mem} {B : Addr} {Z w j i n L : Nat} (ho : VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w j) L m m')
    (hL : L ≤ 8 * (w + 2)) (hij : i ≠ j) (hn : n ≤ w + 2) (hi : i < 16) (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z)
    (hB : B.toNat + Z ≤ 2 ^ 64) : wv m' B (VG.Proof.Bignum.X86_64.slot w i) n = wv m B (VG.Proof.Bignum.X86_64.slot w i) n :=
  ho.wv (by have := VG.Proof.Rsa.X86_64.slot_far (w := w) hij; omega) (by have := Nat.le_trans (VG.Proof.Rsa.X86_64.slot_lt (w := w) hi) hZ; omega)

/-- The loads of `n`, `p`, `q` and `d` into their arrays. -/
theorem cvLoads_ok {I : VG.Proof.Rsa.X86_64.CvIn} {m₀ : Mem} {s : State} (h : VG.Proof.Rsa.X86_64.CvS I m₀ s) (L : VG.Proof.Rsa.X86_64.CvLens I) :
    WP isa (seqs (loadA aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
      (loadA aP VG.Impl.Rsa.X86_64.Keys.CrtValues.sP sPl ++ (loadA aQ VG.Impl.Rsa.X86_64.Keys.CrtValues.sQ sQl ++ loadA VG.Impl.Rsa.X86_64.Keys.CrtValues.aD VG.Impl.Rsa.X86_64.Keys.CrtValues.sD VG.Impl.Rsa.X86_64.Keys.CrtValues.sDl)))) s fun t =>
      VG.Proof.Rsa.X86_64.CvS I m₀ t ∧ VG.Proof.Rsa.X86_64.mword t.mem I.B = VG.Proof.Rsa.X86_64.mword s.mem I.B ∧
      wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aN) (VG.Proof.Rsa.X86_64.wk I.k) = Spec.Rsa.os2ip I.nb ∧
      wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k) = Spec.Rsa.os2ip I.pb ∧
      wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aQ) (VG.Proof.Rsa.X86_64.wk I.k) = Spec.Rsa.os2ip I.qb ∧
      wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) VG.Impl.Rsa.X86_64.Keys.CrtValues.aD) (VG.Proof.Rsa.X86_64.wk I.k) = Spec.Rsa.os2ip I.db := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have k1 := L.k1
  have k2 := L.k2
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have hm : ∀ {m m' : Mem} {j : Nat}, VG.Proof.Bignum.X86_64.Outside I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (8 * (VG.Proof.Rsa.X86_64.wk I.k + 2)) m m' →
      VG.Proof.Rsa.X86_64.mword m' I.B = VG.Proof.Rsa.X86_64.mword m I.B := fun {_ _ j} o =>
    o.word (Or.inl (by have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega))
      (by have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (VG.Proof.Rsa.X86_64.loadA_ok h.ws (by decide) (by decide)
    (by decide) h.args.n h.args.k h.n L.nl (by omega) (by unfold VG.Proof.Rsa.X86_64.wk; omega)) fun s₁ ⟨hv₁, o₁, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (VG.Proof.Rsa.X86_64.loadA_ok h₁.ws (by decide) (by decide)
    (by decide) h₁.args.p h₁.args.pl h₁.p L.pbl L.pl1 (by have := L.pl2; unfold VG.Proof.Rsa.X86_64.wk; omega)) fun s₂ ⟨hv₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.arr (by decide) (Nat.le_refl _) o₂ k₂ (by decide)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (VG.Proof.Rsa.X86_64.loadA_ok h₂.ws (by decide) (by decide)
    (by decide) h₂.args.q h₂.args.ql h₂.q L.qbl L.ql1 (by have := L.ql2; unfold VG.Proof.Rsa.X86_64.wk; omega)) fun s₃ ⟨hv₃, o₃, k₃⟩ => ?_)
  have h₃ := h₂.arr (by decide) (Nat.le_refl _) o₃ k₃ (by decide)
  refine WP.mono (VG.Proof.Rsa.X86_64.loadA_ok h₃.ws (by decide) (by decide) (by decide) h₃.args.d h₃.args.dl h₃.d L.dbl L.dl1
    (by have := L.dl2; unfold VG.Proof.Rsa.X86_64.wk; omega)) fun t ⟨hv₄, o₄, k₄⟩ => ?_
  have h₄ := h₃.arr (by decide) (Nat.le_refl _) o₄ k₄ (by decide)
  refine ⟨h₄, ?_, ?_, ?_, ?_, hv₄⟩
  · rw [hm o₄, hm o₃, hm o₂, hm o₁]
  · rw [VG.Proof.Rsa.X86_64.outside_arr o₄ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn,
      VG.Proof.Rsa.X86_64.outside_arr o₃ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn,
      VG.Proof.Rsa.X86_64.outside_arr o₂ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn]; exact hv₁
  · rw [VG.Proof.Rsa.X86_64.outside_arr o₄ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn,
      VG.Proof.Rsa.X86_64.outside_arr o₃ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn]; exact hv₂
  · rw [VG.Proof.Rsa.X86_64.outside_arr o₄ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn]; exact hv₃

theorem mask_check {c : Bool} {A B1 B2 PQ : Prop} [Decidable A] [Decidable B1] [Decidable B2] [Decidable PQ]
    (h : A → ((A ∧ B1 ∧ B2) ↔ PQ)) (hA : ¬ A → ¬ PQ) :
    (decide A && (c && decide B1 && decide B2)) = (c && decide PQ) := by
  by_cases a : A
  · have := h a
    by_cases b1 : B1 <;> by_cases b2 : B2 <;> by_cases pq : PQ <;> simp_all
  · have := hA a
    simp_all

/-- `pqCheck`: the mask of `p q = n` and'ed into `sMask`, for an odd `n`. -/
theorem cvCheck_ok {I : VG.Proof.Rsa.X86_64.CvIn} {m₀ : Mem} {s : State} (h : VG.Proof.Rsa.X86_64.CvS I m₀ s) (L : VG.Proof.Rsa.X86_64.CvLens I) {c : Bool}
    (hc : VG.Proof.Rsa.X86_64.mword s.mem I.B = VG.Proof.Bignum.X86_64.mask c) (hN : wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aN) (VG.Proof.Rsa.X86_64.wk I.k) % 2 = 1) :
    WP isa (seqs pqCheck) s fun t =>
      VG.Proof.Rsa.X86_64.CvS I m₀ t ∧ VG.Proof.Rsa.X86_64.mword t.mem I.B = VG.Proof.Bignum.X86_64.mask (c && decide (wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k) *
        wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aQ) (VG.Proof.Rsa.X86_64.wk I.k) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aN) (VG.Proof.Rsa.X86_64.wk I.k))) ∧
      ∀ j, j = aP ∨ j = aQ ∨ j = VG.Impl.Rsa.X86_64.Keys.CrtValues.aD → wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have k1 := L.k1
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have hmw : ∀ {m m' : Mem} {j L' : Nat}, VG.Proof.Bignum.X86_64.Outside I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) L' m m' → L' ≤ 8 * (VG.Proof.Rsa.X86_64.wk I.k + 2) →
      VG.Proof.Rsa.X86_64.mword m' I.B = VG.Proof.Rsa.X86_64.mword m I.B := fun {_ _ j _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega))
      (by omega)
  simp only [pqCheck, List.cons_append, List.nil_append, List.append_assoc]
  -- `[u] := n`, then `divmod`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.zeroA_ok h.ws (by decide)) fun s₁ ⟨_, o₁, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.copyA_ok h₁.ws (by decide) (by decide) (by decide)) fun s₂ ⟨hU₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.arr (by decide) (by omega) o₂ k₂ (by decide)
  have g₂ : ∀ j, j < 16 → j ≠ aU → wv s₂.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) :=
    fun j hj hne => by
      rw [VG.Proof.Rsa.X86_64.outside_arr o₂ (by omega) hne (by omega) hj hZ hn, VG.Proof.Rsa.X86_64.outside_arr o₁ (Nat.le_refl _) hne (by omega) hj hZ hn]
  rw [VG.Proof.Rsa.X86_64.outside_arr o₁ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn] at hU₂
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.divmod_ok h₂.ws.scr h₂.ws.rdi h₂.ws.hw h₂.ws.hS (by have := h₂.ws.w1; omega) h₂.ws.w2 hZ
    (iQ := aU) (iR := aV) (iD := aP) (iT := aT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨_, f₃, k₃, hv₃⟩ => ?_)
  have h₃ := h₂.step f₃ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> exact h₂.ws.sl (by decide)) k₃ (by decide)
  have g₃ : ∀ j, j < 16 → j ≠ aU → j ≠ aV → j ≠ aT →
      wv s₃.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) = wv s₂.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) := fun j hj h1 h2 h3 =>
    f₃.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · have := VG.Proof.Rsa.X86_64.slot_far (w := VG.Proof.Rsa.X86_64.wk I.k) h1; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := VG.Proof.Rsa.X86_64.wk I.k) h2; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := VG.Proof.Rsa.X86_64.wk I.k) h3; omega) (by have := h.ws.sl hj; omega)
  have hm₃ : VG.Proof.Rsa.X86_64.mword s₃.mem I.B = VG.Proof.Bignum.X86_64.mask c := by
    have e : VG.Proof.Rsa.X86_64.mword s₃.mem I.B = VG.Proof.Rsa.X86_64.mword s₂.mem I.B := f₃.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) aU (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) aV (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) aT (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega) (by omega)
    exact e.trans ((hmw o₂ (by omega)).trans ((hmw o₁ (Nat.le_refl _)).trans hc))
  rw [hU₂] at hv₃
  rw [g₂ aP (by decide) (by decide)] at hv₃
  -- `rbp = 0` iff `n / p = q`.
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.eqA_ok h₃.ws (a := aU) (b := aQ) (by decide) (by decide))
    fun s₄ ⟨hz₄, m₄, k₄⟩ => ?_)
  have h₄ := h₃.step (rs := []) (by rw [m₄]; exact Frm.refl _ _ _) (by simp) (by simp) k₄ (by decide)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.andZero_ok (c := c) h₄.ws (by rw [m₄]; exact hm₃) hz₄) fun s₅ ⟨m₅, k₅⟩ => ?_)
  obtain ⟨h₅, hm₅, a₅⟩ := h₄.mask m₅ k₅ (by decide)
  -- `[c] := 0`, and `rbp = 0` iff `n mod p = 0`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.zeroA_ok h₅.ws (j := aC) (by decide)) fun s₆ ⟨hz₆, o₆, k₆⟩ => ?_)
  have h₆ := h₅.arr (by decide) (Nat.le_refl _) o₆ k₆ (by decide)
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.eqA_ok h₆.ws (a := aV) (b := aC) (by decide) (by decide))
    fun s₇ ⟨hz₇, m₇, k₇⟩ => ?_)
  have h₇ := h₆.step (rs := []) (by rw [m₇]; exact Frm.refl _ _ _) (by simp) (by simp) k₇ (by decide)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.andZero_ok (c := c && decide (wv s₃.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aU) (VG.Proof.Rsa.X86_64.wk I.k) =
    wv s₃.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aQ) (VG.Proof.Rsa.X86_64.wk I.k))) h₇.ws (by rw [m₇]; exact (hmw o₆ (Nat.le_refl _)).trans hm₅) hz₇)
    fun s₈ ⟨m₈, k₈⟩ => ?_)
  obtain ⟨h₈, hm₈, a₈⟩ := h₇.mask m₈ k₈ (by decide)
  -- `p` odd.
  simp only [seqs]
  refine WP.mono (VG.Proof.Rsa.X86_64.andOdd_ok h₈.ws (j := aP) (by decide) hm₈) fun t ⟨mt, kt⟩ => ?_
  obtain ⟨ht, hmt, at'⟩ := h₈.mask mt kt (by decide)
  -- What the arrays hold.
  have wvw : ∀ {m m' : Mem} {j : Nat}, j < 16 →
      wv m' I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k + 2) = wv m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k + 2) →
      wv m' I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) = wv m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) := fun {m m' j} _ e => by
    have e1 := wv_add m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) 2
    have e2 := wv_add m' I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) 2
    have l1 := wv_lt m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k)
    have l2 := wv_lt m' I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k)
    rw [e] at e2
    have := congrArg (· % 2 ^ (64 * VG.Proof.Rsa.X86_64.wk I.k)) (e1.symm.trans e2)
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at this
    exact this.symm
  have eP₈ : wv s₈.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k) := by
    rw [wvw (by decide) (a₈ aP (by decide)), m₇, VG.Proof.Rsa.X86_64.outside_arr o₆ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn,
      wvw (by decide) (a₅ aP (by decide)), m₄, g₃ aP (by decide) (by decide) (by decide) (by decide),
      g₂ aP (by decide) (by decide)]
  have eC : wv s₆.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) (VG.Proof.Rsa.X86_64.wk I.k) = 0 := by
    have := wv_add s₆.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) (VG.Proof.Rsa.X86_64.wk I.k) 2; omega
  have eV₆ : wv s₆.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aV) (VG.Proof.Rsa.X86_64.wk I.k) = wv s₃.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aV) (VG.Proof.Rsa.X86_64.wk I.k) := by
    rw [VG.Proof.Rsa.X86_64.outside_arr o₆ (Nat.le_refl _) (by decide) (by omega) (by decide) hZ hn, wvw (by decide) (a₅ aV (by decide)), m₄]
  rw [g₃ aQ (by decide) (by decide) (by decide) (by decide), g₂ aQ (by decide) (by decide)] at hz₄
  refine ⟨ht, ?_, fun j hj => ?_⟩
  · rw [hmt, eP₈]
    congr 1
    rw [eV₆, eC, g₃ aQ (by decide) (by decide) (by decide) (by decide), g₂ aQ (by decide) (by decide)]
    apply VG.Proof.Rsa.X86_64.mask_check
    · intro hp
      have hP0 : 0 < wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k) := by omega
      obtain ⟨e1, e2⟩ := hv₃ hP0
      have hlt : wv s₃.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aV) (VG.Proof.Rsa.X86_64.wk I.k + 1) < 2 ^ (64 * VG.Proof.Rsa.X86_64.wk I.k) := by
        rw [e1]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hP0) (Nat.le_of_lt (wv_lt _ _ _ _))
      rw [VG.Proof.Rsa.X86_64.wv_low_of_lt (Nat.le_succ _) hlt, e1, e2]
      exact VG.Proof.Rsa.X86_64.pq_iff hN
    · intro hp hpq
      exact hp ((VG.Proof.Rsa.X86_64.pq_iff hN).mpr hpq).1
  · have hj' : j < 16 := by rcases hj with rfl | rfl | rfl <;> decide
    have e1 : j ≠ aU := by rcases hj with rfl | rfl | rfl <;> decide
    have e2 : j ≠ aV := by rcases hj with rfl | rfl | rfl <;> decide
    have e3 : j ≠ aT := by rcases hj with rfl | rfl | rfl <;> decide
    have e4 : j ≠ aC := by rcases hj with rfl | rfl | rfl <;> decide
    rw [wvw hj' (at' j hj'), wvw hj' (a₈ j hj'), m₇, VG.Proof.Rsa.X86_64.outside_arr o₆ (Nat.le_refl _) e4 (by omega) hj' hZ hn,
      wvw hj' (a₅ j hj'), m₄, g₃ j hj' e1 e2 e3, g₂ j hj' e1]

/-- `invSetup`: `inverse`'s start, `(u, v, x₁, x₂) := (q, p, 1, 0)`, with
the word of `u` above its `w` zero. -/
theorem invSetup_ok {I : VG.Proof.Rsa.X86_64.CvIn} {m₀ : Mem} {s : State} (h : VG.Proof.Rsa.X86_64.CvS I m₀ s) (L : VG.Proof.Rsa.X86_64.CvLens I) :
    WP isa (seqs invSetup) s fun t =>
      VG.Proof.Rsa.X86_64.CvS I m₀ t ∧ VG.Proof.Rsa.X86_64.mword t.mem I.B = VG.Proof.Rsa.X86_64.mword s.mem I.B ∧
      Bignum.X86_64.word t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aU + 8 * VG.Proof.Rsa.X86_64.wk I.k) = 0 ∧
      wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aU) (VG.Proof.Rsa.X86_64.wk I.k) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aQ) (VG.Proof.Rsa.X86_64.wk I.k) ∧
      wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aV) (VG.Proof.Rsa.X86_64.wk I.k) = wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k) ∧
      wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₁) (VG.Proof.Rsa.X86_64.wk I.k) = 1 ∧ wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₂) (VG.Proof.Rsa.X86_64.wk I.k) = 0 ∧
      ∀ j, j = aP ∨ j = aQ ∨ j = VG.Impl.Rsa.X86_64.Keys.CrtValues.aD → wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have k1 := L.k1
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have hmw : ∀ {m m' : Mem} {j L' : Nat}, VG.Proof.Bignum.X86_64.Outside I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) L' m m' → L' ≤ 8 * (VG.Proof.Rsa.X86_64.wk I.k + 2) →
      VG.Proof.Rsa.X86_64.mword m' I.B = VG.Proof.Rsa.X86_64.mword m I.B := fun {_ _ j _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega))
      (by omega)
  have wvw : ∀ {m m' : Mem} {j : Nat}, j < 16 →
      wv m' I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k + 2) = wv m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k + 2) →
      wv m' I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) = wv m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) := fun {m m' j} _ e => by
    have e1 := wv_add m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) 2
    have e2 := wv_add m' I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) 2
    have l1 := wv_lt m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k)
    have l2 := wv_lt m' I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k)
    rw [e] at e2
    have := congrArg (· % 2 ^ (64 * VG.Proof.Rsa.X86_64.wk I.k)) (e1.symm.trans e2)
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at this
    exact this.symm
  -- The arrays a piece leaves: `ot j` from an `Outside` of another.
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, VG.Proof.Bignum.X86_64.Outside I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) Ln m m' → Ln ≤ 8 * (VG.Proof.Rsa.X86_64.wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) (VG.Proof.Rsa.X86_64.wk I.k) = wv m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) (VG.Proof.Rsa.X86_64.wk I.k) :=
    fun o hL hij hi => VG.Proof.Rsa.X86_64.outside_arr o hL hij (by omega) hi hZ hn
  simp only [invSetup, seqs]
  -- `[u] := q`, `[v] := p`, `[x₁] := 1`, `[x₂] := 0`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.zeroA_ok h.ws (j := aU) (by decide)) fun s₁ ⟨z₁, o₁, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.copyA_ok h₁.ws (o := aU) (a := aQ) (by decide) (by decide) (by decide)) fun s₂ ⟨c₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.arr (by decide) (by omega) o₂ k₂ (by decide)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.zeroA_ok h₂.ws (j := aV) (by decide)) fun s₃ ⟨z₃, o₃, k₃⟩ => ?_)
  have h₃ := h₂.arr (by decide) (Nat.le_refl _) o₃ k₃ (by decide)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.copyA_ok h₃.ws (o := aV) (a := aP) (by decide) (by decide) (by decide)) fun s₄ ⟨c₄, o₄, k₄⟩ => ?_)
  have h₄ := h₃.arr (by decide) (by omega) o₄ k₄ (by decide)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.zeroA_ok h₄.ws (j := aX₁) (by decide)) fun s₅ ⟨z₅, o₅, k₅⟩ => ?_)
  have h₅ := h₄.arr (by decide) (Nat.le_refl _) o₅ k₅ (by decide)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.setOneA_ok h₅.ws (j := aX₁) (by decide)) fun s₆ ⟨m₆, k₆⟩ => ?_)
  have o₆ := VG.Proof.Bignum.X86_64.writeW_outside s₅.mem I.B (1 : BitVec 64) (d := VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₁) (by have := h.ws.sl (j := aX₁) (by decide); omega)
  rw [← m₆] at o₆
  have h₆ := h₅.arr (by decide) (by omega) o₆ k₆ (by decide)
  refine WP.mono (VG.Proof.Rsa.X86_64.zeroA_ok h₆.ws (j := aX₂) (by decide)) fun s₇ ⟨z₇, o₇, k₇⟩ => ?_
  have h₇ := h₆.arr (by decide) (Nat.le_refl _) o₇ k₇ (by decide)
  -- The values the inverse starts from.
  have eP : ∀ {m : Mem}, m = s.mem → wv m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k) :=
    fun e => by rw [e]
  have vP₇ : wv s₇.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k) := by
    rw [ot o₇ (Nat.le_refl _) (by decide) (by decide), ot o₆ (by omega) (by decide) (by decide),
      ot o₅ (Nat.le_refl _) (by decide) (by decide), ot o₄ (by omega) (by decide) (by decide),
      ot o₃ (Nat.le_refl _) (by decide) (by decide), ot o₂ (by omega) (by decide) (by decide),
      ot o₁ (Nat.le_refl _) (by decide) (by decide)]
  have vQ₇ : wv s₇.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aQ) (VG.Proof.Rsa.X86_64.wk I.k) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aQ) (VG.Proof.Rsa.X86_64.wk I.k) := by
    rw [ot o₇ (Nat.le_refl _) (by decide) (by decide), ot o₆ (by omega) (by decide) (by decide),
      ot o₅ (Nat.le_refl _) (by decide) (by decide), ot o₄ (by omega) (by decide) (by decide),
      ot o₃ (Nat.le_refl _) (by decide) (by decide), ot o₂ (by omega) (by decide) (by decide),
      ot o₁ (Nat.le_refl _) (by decide) (by decide)]
  have vU₇ : wv s₇.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aU) (VG.Proof.Rsa.X86_64.wk I.k) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aQ) (VG.Proof.Rsa.X86_64.wk I.k) := by
    rw [ot o₇ (Nat.le_refl _) (by decide) (by decide), ot o₆ (by omega) (by decide) (by decide),
      ot o₅ (Nat.le_refl _) (by decide) (by decide), ot o₄ (by omega) (by decide) (by decide),
      ot o₃ (Nat.le_refl _) (by decide) (by decide), c₂, ot o₁ (Nat.le_refl _) (by decide) (by decide)]
  have vV₇ : wv s₇.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aV) (VG.Proof.Rsa.X86_64.wk I.k) = wv s₇.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k) := by
    rw [vP₇, ot o₇ (Nat.le_refl _) (by decide) (by decide), ot o₆ (by omega) (by decide) (by decide),
      ot o₅ (Nat.le_refl _) (by decide) (by decide), c₄, ot o₃ (Nat.le_refl _) (by decide) (by decide),
      ot o₂ (by omega) (by decide) (by decide), ot o₁ (Nat.le_refl _) (by decide) (by decide)]
  have vX₂ : wv s₇.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₂) (VG.Proof.Rsa.X86_64.wk I.k) = 0 := by
    have := wv_add s₇.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₂) (VG.Proof.Rsa.X86_64.wk I.k) 2; omega
  have vX₁ : wv s₇.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₁) (VG.Proof.Rsa.X86_64.wk I.k) = 1 := by
    rw [ot o₇ (Nat.le_refl _) (by decide) (by decide), m₆, VG.Proof.Rsa.X86_64.wv_low (by have := h.ws.w1; omega), VG.Proof.Bignum.X86_64.word_writeW_self,
      (VG.Proof.Bignum.X86_64.writeW_outside s₅.mem I.B (1 : BitVec 64) (d := VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₁) (by
        have := h.ws.sl (j := aX₁) (by decide); omega)).wv (Or.inr (by omega)) (by have := h.ws.sl (j := aX₁) (by decide); omega)]
    have hz : ∀ q < VG.Proof.Rsa.X86_64.wk I.k + 2, Bignum.X86_64.word s₅.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₁ + 8 * q) = 0 :=
      (wv_eq_zero_iff _ _ _ _).mp z₅
    rw [VG.Proof.Rsa.X86_64.wv_zero (n := VG.Proof.Rsa.X86_64.wk I.k - 1) fun q hq => by
      have := hz (1 + q) (by omega)
      rwa [show VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₁ + 8 * (1 + q) = VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₁ + 8 + 8 * q by omega] at this]
    rfl
  have vU0 : Bignum.X86_64.word s₇.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aU + 8 * VG.Proof.Rsa.X86_64.wk I.k) = 0 := by
    have e1 : Bignum.X86_64.word s₂.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aU + 8 * VG.Proof.Rsa.X86_64.wk I.k) = 0 := by
      rw [o₂.word (Or.inr (by omega)) (by have := h.ws.sl (j := aU) (by decide); omega)]
      exact (wv_eq_zero_iff _ _ _ _).mp z₁ (VG.Proof.Rsa.X86_64.wk I.k) (by omega)
    have r := fun {j Ln : Nat} {m m' : Mem} (o : VG.Proof.Bignum.X86_64.Outside I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) Ln m m') (hL : Ln ≤ 8 * (VG.Proof.Rsa.X86_64.wk I.k + 2))
        (hj : j ≠ aU) (hj' : j < 16) =>
      o.word (d := VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aU + 8 * VG.Proof.Rsa.X86_64.wk I.k) (by have := VG.Proof.Rsa.X86_64.slot_far (w := VG.Proof.Rsa.X86_64.wk I.k) hj; omega)
        (by have := h.ws.sl (j := aU) (by decide); omega)
    rw [r o₇ (Nat.le_refl _) (by decide) (by decide), r o₆ (by omega) (by decide) (by decide),
      r o₅ (Nat.le_refl _) (by decide) (by decide), r o₄ (by omega) (by decide) (by decide),
      r o₃ (Nat.le_refl _) (by decide) (by decide)]
    exact e1
  refine ⟨h₇, (hmw o₇ (Nat.le_refl _)).trans ((hmw o₆ (by omega)).trans ((hmw o₅ (Nat.le_refl _)).trans
    ((hmw o₄ (by omega)).trans ((hmw o₃ (Nat.le_refl _)).trans ((hmw o₂ (by omega)).trans
      (hmw o₁ (Nat.le_refl _))))))), vU0, vU₇, vV₇, vX₁, vX₂, fun j hj => ?_⟩
  rcases hj with rfl | rfl | rfl
  · exact vP₇
  · exact vQ₇
  · rw [ot o₇ (Nat.le_refl _) (by decide) (by decide), ot o₆ (by omega) (by decide) (by decide),
      ot o₅ (Nat.le_refl _) (by decide) (by decide), ot o₄ (by omega) (by decide) (by decide),
      ot o₃ (Nat.le_refl _) (by decide) (by decide), ot o₂ (by omega) (by decide) (by decide),
      ot o₁ (Nat.le_refl _) (by decide) (by decide)]

/-- `invPart`: `qInv` into `aX₂` and `gcd(q, p) = 1` and'ed into `sMask`,
for a mask that is set only if `p` is odd and above 1. -/
theorem cvInv_ok {I : VG.Proof.Rsa.X86_64.CvIn} {m₀ : Mem} {s : State} (h : VG.Proof.Rsa.X86_64.CvS I m₀ s) (L : VG.Proof.Rsa.X86_64.CvLens I) {c : Bool}
    (hc : VG.Proof.Rsa.X86_64.mword s.mem I.B = VG.Proof.Bignum.X86_64.mask c)
    (hcP : c = true → wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k) % 2 = 1 ∧ 1 < wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k)) :
    WP isa (seqs invPart) s fun t =>
      VG.Proof.Rsa.X86_64.CvS I m₀ t ∧ VG.Proof.Rsa.X86_64.mword t.mem I.B = VG.Proof.Bignum.X86_64.mask (c && decide (Nat.gcd (wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aQ) (VG.Proof.Rsa.X86_64.wk I.k))
        (wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k)) = 1)) ∧
      (c = true → ((wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k) : Nat) : Int) ∣
          (wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₂) (VG.Proof.Rsa.X86_64.wk I.k) : Int) * wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aQ) (VG.Proof.Rsa.X86_64.wk I.k) -
            Nat.gcd (wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aQ) (VG.Proof.Rsa.X86_64.wk I.k)) (wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k)) ∧
        wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₂) (VG.Proof.Rsa.X86_64.wk I.k) < wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k)) ∧
      ∀ j, j = aP ∨ j = aQ ∨ j = VG.Impl.Rsa.X86_64.Keys.CrtValues.aD → wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have k1 := L.k1
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have hmw : ∀ {m m' : Mem} {j L' : Nat}, VG.Proof.Bignum.X86_64.Outside I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) L' m m' → L' ≤ 8 * (VG.Proof.Rsa.X86_64.wk I.k + 2) →
      VG.Proof.Rsa.X86_64.mword m' I.B = VG.Proof.Rsa.X86_64.mword m I.B := fun {_ _ j _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega))
      (by omega)
  have wvw : ∀ {m m' : Mem} {j : Nat}, j < 16 →
      wv m' I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k + 2) = wv m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k + 2) →
      wv m' I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) = wv m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) := fun {m m' j} _ e => by
    have e1 := wv_add m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) 2
    have e2 := wv_add m' I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) 2
    have l1 := wv_lt m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k)
    have l2 := wv_lt m' I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k)
    rw [e] at e2
    have := congrArg (· % 2 ^ (64 * VG.Proof.Rsa.X86_64.wk I.k)) (e1.symm.trans e2)
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at this
    exact this.symm
  -- The arrays a piece leaves: `ot j` from an `Outside` of another.
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, VG.Proof.Bignum.X86_64.Outside I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) Ln m m' → Ln ≤ 8 * (VG.Proof.Rsa.X86_64.wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) (VG.Proof.Rsa.X86_64.wk I.k) = wv m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) (VG.Proof.Rsa.X86_64.wk I.k) :=
    fun o hL hij hi => VG.Proof.Rsa.X86_64.outside_arr o hL hij (by omega) hi hZ hn
  simp only [invPart]
  refine wp_seqs_append (by simp [invSetup]) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.invSetup_ok h L)
    fun s₇ ⟨h₇, m₇, vU0, vU₇, vV₇, vX₁, vX₂, p₇⟩ => ?_)
  have vP₇ := p₇ aP (.inl rfl)
  have vQ₇ := p₇ aQ (.inr (.inl rfl))
  have vD₇ := p₇ VG.Impl.Rsa.X86_64.Keys.CrtValues.aD (.inr (.inr rfl))
  simp only [List.cons_append, List.nil_append]
  -- The inverse.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.inverse_ok h₇.ws.scr h₇.ws.rdi h₇.ws.hw h₇.ws.hS (by have := h₇.ws.w1; omega) h₇.ws.w2 hZ
    (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aP) (iT := aT) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) vU0 vV₇ vX₁ vX₂)
    fun s₈ ⟨_, f₈, k₈, hv₈⟩ => ?_)
  have h₈ := h₇.step f₈ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Mut.ofSlot _ _ _
    · exact Mut.ofSlot _ _ _
    · exact Mut.ofSlot _ _ _
    · exact Mut.ofSlot _ _ _
    · exact Mut.ofSlot _ _ _
    · exact Or.inr (Or.inr rfl)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have := h.ws.sl (j := aT) (by decide)
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · have := h.ws.sl (j := aU) (by decide); omega
    · have := h.ws.sl (j := aV) (by decide); omega
    · have := h.ws.sl (j := aX₁) (by decide); omega
    · have := h.ws.sl (j := aX₂) (by decide); omega
    · omega
    · have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) 0 (show sMo < 32 by decide); have := h.ws.sl (j := 0) (by decide)
      unfold sMo sFn at *; omega) k₈ (by decide)
  rw [vU₇, vP₇] at hv₈
  have f8 : ∀ j, j < 16 → j ≠ aU → j ≠ aV → j ≠ aX₁ → j ≠ aX₂ → j ≠ aT →
      wv s₈.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) = wv s₇.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) := fun j hj h1 h2 h3 h4 h5 =>
    f₈.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
      · have := VG.Proof.Rsa.X86_64.slot_far (w := VG.Proof.Rsa.X86_64.wk I.k) h1; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := VG.Proof.Rsa.X86_64.wk I.k) h2; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := VG.Proof.Rsa.X86_64.wk I.k) h3; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := VG.Proof.Rsa.X86_64.wk I.k) h4; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := VG.Proof.Rsa.X86_64.wk I.k) h5; omega
      · have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) j (show sMo < 32 by decide); omega) (by have := h.ws.sl hj; omega)
  have hm₈ : VG.Proof.Rsa.X86_64.mword s₈.mem I.B = VG.Proof.Bignum.X86_64.mask c := by
    have e8 : VG.Proof.Rsa.X86_64.mword s₈.mem I.B = VG.Proof.Rsa.X86_64.mword s₇.mem I.B := f₈.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
      · have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) aU (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) aV (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) aX₁ (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) aX₂ (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) aT (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · simp only [sMo, sFn]; omega) (by omega)
    exact e8.trans (m₇.trans hc)
  -- `[c] := 1`, and the mask of `[v] = 1`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.zeroA_ok h₈.ws (j := aC) (by decide)) fun s₉ ⟨z₉, o₉, k₉⟩ => ?_)
  have h₉ := h₈.arr (by decide) (Nat.le_refl _) o₉ k₉ (by decide)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.setOneA_ok h₉.ws (j := aC) (by decide)) fun s₁₀ ⟨m₁₀, k₁₀⟩ => ?_)
  have o₁₀ := VG.Proof.Bignum.X86_64.writeW_outside s₉.mem I.B (1 : BitVec 64) (d := VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) (by have := h.ws.sl (j := aC) (by decide); omega)
  rw [← m₁₀] at o₁₀
  have h₁₀ := h₉.arr (by decide) (by omega) o₁₀ k₁₀ (by decide)
  have vC : wv s₁₀.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) (VG.Proof.Rsa.X86_64.wk I.k) = 1 := by
    rw [m₁₀, VG.Proof.Rsa.X86_64.wv_low (by have := h.ws.w1; omega), VG.Proof.Bignum.X86_64.word_writeW_self,
      (VG.Proof.Bignum.X86_64.writeW_outside s₉.mem I.B (1 : BitVec 64) (d := VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) (by
        have := h.ws.sl (j := aC) (by decide); omega)).wv (Or.inr (by omega)) (by have := h.ws.sl (j := aC) (by decide); omega)]
    have hz : ∀ q < VG.Proof.Rsa.X86_64.wk I.k + 2, Bignum.X86_64.word s₉.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC + 8 * q) = 0 :=
      (wv_eq_zero_iff _ _ _ _).mp z₉
    rw [VG.Proof.Rsa.X86_64.wv_zero (n := VG.Proof.Rsa.X86_64.wk I.k - 1) fun q hq => by
      have := hz (1 + q) (by omega)
      rwa [show VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC + 8 * (1 + q) = VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC + 8 + 8 * q by omega] at this]
    rfl
  have vV₁₀ : wv s₁₀.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aV) (VG.Proof.Rsa.X86_64.wk I.k) = wv s₈.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aV) (VG.Proof.Rsa.X86_64.wk I.k) := by
    rw [ot o₁₀ (by omega) (by decide) (by decide), ot o₉ (Nat.le_refl _) (by decide) (by decide)]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.eqA_ok h₁₀.ws (a := aV) (b := aC) (by decide) (by decide))
    fun s₁₁ ⟨hz₁₁, m₁₁, k₁₁⟩ => ?_)
  have h₁₁ := h₁₀.step (rs := []) (by rw [m₁₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁₁ (by decide)
  rw [vC, vV₁₀] at hz₁₁
  simp only [seqs]
  refine WP.mono (VG.Proof.Rsa.X86_64.andZero_ok (c := c) h₁₁.ws (by rw [m₁₁]; exact (hmw o₁₀ (by omega)).trans ((hmw o₉ (Nat.le_refl _)).trans hm₈)) hz₁₁)
    fun t ⟨mt, kt⟩ => ?_
  obtain ⟨ht, hmt, at'⟩ := h₁₁.mask mt kt (by decide)
  have tX : ∀ j, j < 16 → j ≠ aC → wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) = wv s₈.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) :=
    fun j hj hne => by
      rw [wvw hj (at' j hj), m₁₁, ot o₁₀ (by omega) hne hj, ot o₉ (Nat.le_refl _) hne hj]
  refine ⟨ht, ?_, fun hcT => ?_, fun j hj => ?_⟩
  · rw [hmt]
    congr 1
    cases c
    · rfl
    · obtain ⟨hp, hp1⟩ := hcP rfl
      rw [(hv₈ hp hp1).1]
  · obtain ⟨hp, hp1⟩ := hcP hcT
    obtain ⟨e1, e2, e3⟩ := hv₈ hp hp1
    rw [tX aX₂ (by decide) (by decide)]
    exact ⟨e1 ▸ e2, e3⟩
  · have hj' : j < 16 := by rcases hj with rfl | rfl | rfl <;> decide
    rw [tX j hj' (by rcases hj with rfl | rfl | rfl <;> decide)]
    rcases hj with rfl | rfl | rfl
    · rw [f8 aP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), vP₇]
    · rw [f8 aQ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), vQ₇]
    · rw [f8 VG.Impl.Rsa.X86_64.Keys.CrtValues.aD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), vD₇]

/-- `decA j`: the low word of `[j]` minus one. -/
theorem decA_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {j : Nat} (hj : j < 16) :
    WP isa (.block (decA j)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j)) (Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w j) - 1) ∧
        VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .rbx, .rax] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  unfold decA
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨_, e9, n₁, j₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok j (r := .rbx) (by decide) ((j₁.gpr (by decide)).trans h.rdi) e9)
    fun t₂ ⟨hbx, n₂, j₂⟩ => ?_
  have hs₂ := h.scr.congr (j₁.trans j₂).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j))
    (Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w j) - 1)) (by
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.ld (d := VG.Proof.Bignum.X86_64.slot w j) (by omega), hs₂.st (d := VG.Proof.Bignum.X86_64.slot w j) (by omega), n₂, n₁]) rfl)
    fun t ⟨mt, j₃⟩ => ⟨mt, ((j₁.trans j₂).trans j₃).mono (by simp)⟩

/-- `divisor j ++ [divmod]`: `[aV] := d mod ([j] - 1)`, for an odd `[j]`. -/
theorem cvDivPart_ok {I : VG.Proof.Rsa.X86_64.CvIn} {m₀ : Mem} {s : State} (h : VG.Proof.Rsa.X86_64.CvS I m₀ s) (L : VG.Proof.Rsa.X86_64.CvLens I) {j : Nat} (hj : j = aP ∨ j = aQ) :
    WP isa (seqs (divisor j ++ [divmod aU aV aC aT])) s fun t =>
      VG.Proof.Rsa.X86_64.CvS I m₀ t ∧ VG.Proof.Rsa.X86_64.mword t.mem I.B = VG.Proof.Rsa.X86_64.mword s.mem I.B ∧
      (wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) % 2 = 1 → 1 < wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) →
        wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aV) (VG.Proof.Rsa.X86_64.wk I.k + 1) =
          wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) VG.Impl.Rsa.X86_64.Keys.CrtValues.aD) (VG.Proof.Rsa.X86_64.wk I.k) % (wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) - 1)) ∧
      ∀ i, i = aP ∨ i = aQ ∨ i = VG.Impl.Rsa.X86_64.Keys.CrtValues.aD ∨ i = aX₁ ∨ i = aX₂ →
        wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) (VG.Proof.Rsa.X86_64.wk I.k) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) (VG.Proof.Rsa.X86_64.wk I.k) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have k1 := L.k1
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have hj16 : j < 16 := by rcases hj with rfl | rfl <;> decide
  have hjC : j ≠ aC := by rcases hj with rfl | rfl <;> decide
  have hjU : j ≠ aU := by rcases hj with rfl | rfl <;> decide
  have hmw : ∀ {m m' : Mem} {i L' : Nat}, VG.Proof.Bignum.X86_64.Outside I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) L' m m' → L' ≤ 8 * (VG.Proof.Rsa.X86_64.wk I.k + 2) →
      VG.Proof.Rsa.X86_64.mword m' I.B = VG.Proof.Rsa.X86_64.mword m I.B := fun {_ _ i _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) i (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega))
      (by omega)
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, VG.Proof.Bignum.X86_64.Outside I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) Ln m m' → Ln ≤ 8 * (VG.Proof.Rsa.X86_64.wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) (VG.Proof.Rsa.X86_64.wk I.k) = wv m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) (VG.Proof.Rsa.X86_64.wk I.k) :=
    fun o hL hij hi => VG.Proof.Rsa.X86_64.outside_arr o hL hij (by omega) hi hZ hn
  simp only [divisor, List.cons_append, List.nil_append]
  -- `[c] := [j]`, minus one.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.zeroA_ok h.ws (j := aC) (by decide)) fun s₁ ⟨_, o₁, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.copyA_ok h₁.ws (o := aC) (a := j) (by decide) hj16 (Ne.symm hjC)) fun s₂ ⟨c₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.arr (by decide) (by omega) o₂ k₂ (by decide)
  rw [ot o₁ (Nat.le_refl _) hjC hj16] at c₂
  -- The low word.
  have sC := h.ws.sl (j := aC) (by decide)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.decA_ok h₂.ws (j := aC) (by decide)) fun s₃ ⟨m₃, k₃⟩ => ?_)
  have o₃ := VG.Proof.Bignum.X86_64.writeW_outside s₂.mem I.B (Bignum.X86_64.word s₂.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) - 1)
    (d := VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) (by omega)
  rw [← m₃] at o₃
  have h₃ := h₂.arr (by decide) (by omega) o₃ k₃ (by decide)
  -- `[c] = [j] - 1` for an odd `[j]`.
  have vC₃ : wv s₂.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) (VG.Proof.Rsa.X86_64.wk I.k) % 2 = 1 →
      wv s₃.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) (VG.Proof.Rsa.X86_64.wk I.k) = wv s₂.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) (VG.Proof.Rsa.X86_64.wk I.k) - 1 := by
    have w1 := h.ws.w1
    have e3 := VG.Proof.Rsa.X86_64.wv_low (m := s₃.mem) (B := I.B) (e := VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) (w := VG.Proof.Rsa.X86_64.wk I.k) (by omega)
    have e2 := VG.Proof.Rsa.X86_64.wv_low (m := s₂.mem) (B := I.B) (e := VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) (w := VG.Proof.Rsa.X86_64.wk I.k) (by omega)
    have hw3 : Bignum.X86_64.word s₃.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) =
        Bignum.X86_64.word s₂.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) - 1 := by
      rw [m₃, VG.Proof.Bignum.X86_64.word_writeW_self]
    have hup : wv s₃.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC + 8) (VG.Proof.Rsa.X86_64.wk I.k - 1) = wv s₂.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC + 8) (VG.Proof.Rsa.X86_64.wk I.k - 1) := by
      rw [m₃]; exact (VG.Proof.Bignum.X86_64.writeW_outside s₂.mem I.B _ (by omega)).wv (Or.inr (by omega)) (by omega)
    intro ho
    rw [e2] at ho ⊢
    have hodd : (Bignum.X86_64.word s₂.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC)).toNat % 2 = 1 := by omega
    have hsub : (Bignum.X86_64.word s₂.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) - 1).toNat =
        (Bignum.X86_64.word s₂.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC)).toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; rfl
    rw [e3, hup, hw3, hsub]
    omega
  rw [c₂] at vC₃
  -- `[u] := d`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.zeroA_ok h₃.ws (j := aU) (by decide)) fun s₄ ⟨_, o₄, k₄⟩ => ?_)
  have h₄ := h₃.arr (by decide) (Nat.le_refl _) o₄ k₄ (by decide)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.copyA_ok h₄.ws (o := aU) (a := VG.Impl.Rsa.X86_64.Keys.CrtValues.aD) (by decide) (by decide) (by decide)) fun s₅ ⟨c₅, o₅, k₅⟩ => ?_)
  have h₅ := h₄.arr (by decide) (by omega) o₅ k₅ (by decide)
  -- `divmod`.
  simp only [seqs]
  refine WP.mono (VG.Proof.Rsa.X86_64.divmod_ok h₅.ws.scr h₅.ws.rdi h₅.ws.hw h₅.ws.hS (by have := h₅.ws.w1; omega) h₅.ws.w2 hZ
    (iQ := aU) (iR := aV) (iD := aC) (iT := aT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨_, f₆, k₆, hv₆⟩ => ?_
  have ht := h₅.step f₆ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> exact h.ws.sl (by decide)) k₆ (by decide)
  have f6 : ∀ i, i < 16 → i ≠ aU → i ≠ aV → i ≠ aT →
      wv t.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) (VG.Proof.Rsa.X86_64.wk I.k) = wv s₅.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) (VG.Proof.Rsa.X86_64.wk I.k) := fun i hi h1 h2 h3 =>
    f₆.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · have := VG.Proof.Rsa.X86_64.slot_far (w := VG.Proof.Rsa.X86_64.wk I.k) h1; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := VG.Proof.Rsa.X86_64.wk I.k) h2; omega
      · have := VG.Proof.Rsa.X86_64.slot_far (w := VG.Proof.Rsa.X86_64.wk I.k) h3; omega) (by have := h.ws.sl hi; omega)
  have back : ∀ i, i < 16 → i ≠ aC → i ≠ aU → wv s₅.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) (VG.Proof.Rsa.X86_64.wk I.k) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) (VG.Proof.Rsa.X86_64.wk I.k) :=
    fun i hi h1 h2 => by
      rw [ot o₅ (by omega) h2 hi, ot o₄ (Nat.le_refl _) h2 hi, ot o₃ (by omega) h1 hi, ot o₂ (by omega) h1 hi,
        ot o₁ (Nat.le_refl _) h1 hi]
  refine ⟨ht, ?_, fun ho h1 => ?_, fun i hi => ?_⟩
  · have e6 : VG.Proof.Rsa.X86_64.mword t.mem I.B = VG.Proof.Rsa.X86_64.mword s₅.mem I.B := f₆.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) aU (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) aV (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega
      · have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) aT (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega) (by omega)
    exact e6.trans ((hmw o₅ (by omega)).trans ((hmw o₄ (Nat.le_refl _)).trans ((hmw o₃ (by omega)).trans
      ((hmw o₂ (by omega)).trans (hmw o₁ (Nat.le_refl _))))))
  · have hC : wv s₅.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) (VG.Proof.Rsa.X86_64.wk I.k) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) (VG.Proof.Rsa.X86_64.wk I.k) - 1 := by
      rw [ot o₅ (by omega) (by decide) (by decide), ot o₄ (Nat.le_refl _) (by decide) (by decide)]
      exact vC₃ ho
    have hU : wv s₅.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aU) (VG.Proof.Rsa.X86_64.wk I.k) = wv s.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) VG.Impl.Rsa.X86_64.Keys.CrtValues.aD) (VG.Proof.Rsa.X86_64.wk I.k) := by
      rw [c₅, ot o₄ (Nat.le_refl _) (by decide) (by decide), ot o₃ (by omega) (by decide) (by decide),
        ot o₂ (by omega) (by decide) (by decide), ot o₁ (Nat.le_refl _) (by decide) (by decide)]
    have hpos : 0 < wv s₅.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aC) (VG.Proof.Rsa.X86_64.wk I.k) := by
      rw [hC]; omega
    rw [(hv₆ hpos).1, hU, hC]
  · have hi16 : i < 16 := by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [f6 i hi16 (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide),
      back i hi16 (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)]

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.CvStore`. -/
section

/-!
# `vg_rsa_crt_values` on x86-64: the results

`dP`, `dQ` and `qInv`, masked, to their outputs (`storeA_ws`, which keeps
the working space), the mask's low bit returned and the saved registers
restored (`cvStores_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- Memory below `Z`, after a store outside the working space. -/
theorem frm_scr {m m' : Mem} {B out : Addr} {Z len : Nat} (hsep : ∀ i < len, Z ≤ VG.Proof.Bignum.X86_64.ofs B (out + BitVec.ofNat 64 i))
    (hx : ∀ x, (∀ i < len, x ≠ out + BitVec.ofNat 64 i) → m' x = m x) : Frm B [(Z, 2 ^ 64)] m m' :=
  fun x hx' => hx x fun i hi he => by
    have := hsep i hi
    rw [← he] at this
    have := hx' _ List.mem_cons_self
    have : VG.Proof.Bignum.X86_64.ofs B x < 2 ^ 64 := (x - B).isLt
    omega

/-- `storeA`, which keeps the working space and the header. -/
theorem storeA_ws {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {j sPtr sLen len : Nat} {out : Addr}
    {c : Bool} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (hp : VG.Proof.Bignum.X86_64.word s.mem B (8 * sPtr) = out) (hl : VG.Proof.Bignum.X86_64.word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hm : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = VG.Proof.Bignum.X86_64.mask c) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * w)
    (hout : ∀ i < len, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < len, Z ≤ VG.Proof.Bignum.X86_64.ofs B (out + BitVec.ofNat 64 i)) :
    WP isa (seqs (storeA j sPtr sLen Impl.Bignum.X86_64.Public.sMask)) s fun t =>
      (List.range len).map (fun i => t.mem (out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (VG.Proof.Bignum.X86_64.slot w j) ((len + 7) / 8) else 0) len ∧
      (∀ x, (∀ i < len, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ VG.Proof.Rsa.X86_64.Ws t B Z w ∧
      Frm B [(Z, 2 ^ 64)] s.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .rbx, .rsi, .rcx, .r15, .rax, .rdx, .rbp, .r14] s t :=
  WP.mono (VG.Proof.Rsa.X86_64.storeA_ok h hj hP hL (by decide) hp hl hm hl1 hlw hout hsep) fun t ⟨hb, hx, hwr, hrd, k⟩ =>
    have hf := VG.Proof.Rsa.X86_64.frm_scr hsep hx
    ⟨hb, hx, h.congr hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (by have := h.h256; omega)) k (by decide), hf, k⟩

/-- The mask's low bit returned and the saved registers restored. -/
theorem cvExit_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {c : Bool}
    (hm : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = VG.Proof.Bignum.X86_64.mask c) :
    WP isa (.block retMask) s
      fun t => t.gpr .rax = BitVec.ofNat 64 c.toNat ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i)) ∧
        t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  rw [retMask, exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.word s.mem B (8 * 0) ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.word s.mem B (8 * 1) ∧ t.gpr .r12 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 2) ∧
      t.gpr .r13 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 3) ∧ t.gpr .r14 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 4) ∧
      t.gpr .r15 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 5) ∧ t.mem = s.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, h.rdi, hdrOff, hl Impl.Bignum.X86_64.Public.sMask (by decide), hm, mask_and1,
      hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide), hl 4 (by decide),
      hl 5 (by decide)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm'⟩, k⟩ => ⟨hax, ?_, hm', k⟩
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-- The output bytes `out + i`, `i < len`: writable, outside the working
space. -/
structure OutOk (s : State) (B : Addr) (Z : Nat) (out : Addr) (len : Nat) : Prop where
  wr : ∀ i < len, InRegions s.wr (out + BitVec.ofNat 64 i) 1
  sep : ∀ i < len, Z ≤ VG.Proof.Bignum.X86_64.ofs B (out + BitVec.ofNat 64 i)

/-- Two outputs with no byte in common. -/
def Apart (o₁ : Addr) (l₁ : Nat) (o₂ : Addr) (l₂ : Nat) : Prop :=
  ∀ i < l₁, ∀ j < l₂, o₁ + BitVec.ofNat 64 i ≠ o₂ + BitVec.ofNat 64 j

/-- The stores of `qInv` (`aX₂`), `dP` (`aX₁`) and `dQ` (`aV`), and the
exit. -/
theorem cvStores_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {k pl ql dl : Nat}
    {pDp pDq pQi pN pP pQ pD : Addr} {sv : Nat → BitVec 64}
    (ha : VG.Proof.Rsa.X86_64.CvArgs s.mem B k pl ql dl pDp pDq pQi pN pP pQ pD sv) {c : Bool}
    (hm : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = VG.Proof.Bignum.X86_64.mask c)
    (hpl1 : 1 ≤ pl) (hpl2 : pl ≤ 8 * w) (hql1 : 1 ≤ ql) (hql2 : ql ≤ 8 * w)
    (oQi : VG.Proof.Rsa.X86_64.OutOk s B Z pQi pl) (oDp : VG.Proof.Rsa.X86_64.OutOk s B Z pDp pl) (oDq : VG.Proof.Rsa.X86_64.OutOk s B Z pDq ql)
    (a1 : VG.Proof.Rsa.X86_64.Apart pQi pl pDp pl) (a2 : VG.Proof.Rsa.X86_64.Apart pQi pl pDq ql) (a3 : VG.Proof.Rsa.X86_64.Apart pDp pl pDq ql) :
    WP isa (seqs (storeA aX₂ sQi sPl Impl.Bignum.X86_64.Public.sMask ++
      (storeA aX₁ sDp sPl Impl.Bignum.X86_64.Public.sMask ++ (storeA aV sDq sQl Impl.Bignum.X86_64.Public.sMask ++
        ([.block retMask] : List (Prog isa)))))) s
      fun t =>
        (List.range pl).map (fun i => t.mem (pQi + BitVec.ofNat 64 i)) =
          Spec.Rsa.i2osp (if c then wv s.mem B (VG.Proof.Bignum.X86_64.slot w aX₂) ((pl + 7) / 8) else 0) pl ∧
        (List.range pl).map (fun i => t.mem (pDp + BitVec.ofNat 64 i)) =
          Spec.Rsa.i2osp (if c then wv s.mem B (VG.Proof.Bignum.X86_64.slot w aX₁) ((pl + 7) / 8) else 0) pl ∧
        (List.range ql).map (fun i => t.mem (pDq + BitVec.ofNat 64 i)) =
          Spec.Rsa.i2osp (if c then wv s.mem B (VG.Proof.Bignum.X86_64.slot w aV) ((ql + 7) / 8) else 0) ql ∧
        t.gpr .rax = BitVec.ofNat 64 c.toNat ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = sv i) ∧
        (∀ x, (∀ i < pl, x ≠ pQi + BitVec.ofNat 64 i) → (∀ i < pl, x ≠ pDp + BitVec.ofNat 64 i) →
          (∀ i < ql, x ≠ pDq + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
        VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have sl : ∀ j < 16, VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ Z := fun j hj => h.sl hj
  -- Header words and arrays below `Z` are kept by each store.
  have fw : ∀ {m m' : Mem}, Frm B [(Z, 2 ^ 64)] m m' → ∀ i < 32, VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i) :=
    fun hf i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
  have fv : ∀ {m m' : Mem}, Frm B [(Z, 2 ^ 64)] m m' → ∀ j < 16, ∀ n ≤ w + 2,
      wv m' B (VG.Proof.Bignum.X86_64.slot w j) n = wv m B (VG.Proof.Bignum.X86_64.slot w j) n := fun hf j hj n hn' =>
    hf.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; have := sl j hj; exact Or.inl (by omega))
      (by have := sl j hj; omega)
  refine wp_seqs_append (by simp [storeA]) (by simp [storeA]) (WP.mono (VG.Proof.Rsa.X86_64.storeA_ws h (by decide) (by decide)
    (by decide) ha.qi ha.pl hm hpl1 hpl2 oQi.wr oQi.sep) fun s₁ ⟨b₁, x₁, h₁, f₁, k₁⟩ => ?_)
  have hm₁ : VG.Proof.Bignum.X86_64.word s₁.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = VG.Proof.Bignum.X86_64.mask c := by rw [fw f₁ _ (by decide)]; exact hm
  refine wp_seqs_append (by simp [storeA]) (by simp [storeA]) (WP.mono (VG.Proof.Rsa.X86_64.storeA_ws h₁ (by decide) (by decide)
    (by decide) (by rw [fw f₁ _ (by decide)]; exact ha.dp) (by rw [fw f₁ _ (by decide)]; exact ha.pl) hm₁ hpl1 hpl2
    (fun i hi => by rw [k₁.2.2]; exact oDp.wr i hi) oDp.sep) fun s₂ ⟨b₂, x₂, h₂, f₂, k₂⟩ => ?_)
  have hm₂ : VG.Proof.Bignum.X86_64.word s₂.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = VG.Proof.Bignum.X86_64.mask c := by rw [fw f₂ _ (by decide)]; exact hm₁
  refine wp_seqs_append (by simp [storeA]) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.storeA_ws h₂ (by decide) (by decide)
    (by decide) (by rw [fw f₂ _ (by decide), fw f₁ _ (by decide)]; exact ha.dq)
    (by rw [fw f₂ _ (by decide), fw f₁ _ (by decide)]; exact ha.ql) hm₂ hql1 hql2
    (fun i hi => by rw [k₂.2.2, k₁.2.2]; exact oDq.wr i hi) oDq.sep) fun s₃ ⟨b₃, x₃, h₃, f₃, k₃⟩ => ?_)
  have hm₃ : VG.Proof.Bignum.X86_64.word s₃.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = VG.Proof.Bignum.X86_64.mask c := by rw [fw f₃ _ (by decide)]; exact hm₂
  simp only [seqs]
  refine WP.mono (VG.Proof.Rsa.X86_64.cvExit_ok h₃ hm₃) fun t ⟨hax, hsv, hmt, k₄⟩ => ?_
  rw [hmt]
  refine ⟨?_, ?_, ?_, hax, fun i hi => ?_, fun x n1 n2 n3 => by rw [x₃ x n3, x₂ x n2, x₁ x n1],
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  · rw [← b₁]
    exact List.map_congr_left fun i hi => by
      have hi' := List.mem_range.mp hi
      rw [x₃ _ (fun j hj => a2 i hi' j hj), x₂ _ (fun j hj => a1 i hi' j hj)]
  · rw [fv f₁ _ (by decide) _ (by omega)] at b₂
    rw [← b₂]
    exact List.map_congr_left fun i hi => by
      have hi' := List.mem_range.mp hi
      rw [x₃ _ (fun j hj => a3 i hi' j hj)]
  · rw [fv f₂ _ (by decide) _ (by omega), fv f₁ _ (by decide) _ (by omega)] at b₃
    exact b₃
  · rw [hsv i hi, fw f₃ _ (by omega), fw f₂ _ (by omega), fw f₁ _ (by omega)]
    exact ha.saved i hi

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.CvMain`. -/
section

/-!
# `vg_rsa_crt_values` on x86-64: `main`

From a valid modulus, `main` writes `dP`, `dQ` and `qInv` if `p q = n`
and `gcd(q, p) = 1`, and zeros otherwise (`cvMain_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-- The inputs as numbers. -/
abbrev CvIn.N (I : VG.Proof.Rsa.X86_64.CvIn) : Nat := Spec.Rsa.os2ip I.nb
abbrev CvIn.P (I : VG.Proof.Rsa.X86_64.CvIn) : Nat := Spec.Rsa.os2ip I.pb
abbrev CvIn.Q (I : VG.Proof.Rsa.X86_64.CvIn) : Nat := Spec.Rsa.os2ip I.qb
abbrev CvIn.D (I : VG.Proof.Rsa.X86_64.CvIn) : Nat := Spec.Rsa.os2ip I.db

/-- Whether `main` writes the values: `p q = n` and `gcd(q, p) = 1`. -/
abbrev CvIn.ok (I : VG.Proof.Rsa.X86_64.CvIn) : Bool := decide (I.P * I.Q = I.N ∧ Nat.gcd I.Q I.P = 1)

/-- What `main` needs on entry. -/
structure CvPre (I : VG.Proof.Rsa.X86_64.CvIn) (s : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr s I.B I.Z
  rdi : s.gpr .rdi = I.B
  args : VG.Proof.Rsa.X86_64.CvArgs s.mem I.B I.k I.pl I.ql I.dl I.pDp I.pDq I.pQi I.pN I.pP I.pQ I.pD I.sv
  n : Src s I.B I.Z I.pN I.nb
  p : Src s I.B I.Z I.pP I.pb
  q : Src s I.B I.Z I.pQ I.qb
  d : Src s I.B I.Z I.pD I.db
  L : VG.Proof.Rsa.X86_64.CvLens I
  oQi : VG.Proof.Rsa.X86_64.OutOk s I.B I.Z I.pQi I.pl
  oDp : VG.Proof.Rsa.X86_64.OutOk s I.B I.Z I.pDp I.pl
  oDq : VG.Proof.Rsa.X86_64.OutOk s I.B I.Z I.pDq I.ql
  a1 : VG.Proof.Rsa.X86_64.Apart I.pQi I.pl I.pDp I.pl
  a2 : VG.Proof.Rsa.X86_64.Apart I.pQi I.pl I.pDq I.ql
  a3 : VG.Proof.Rsa.X86_64.Apart I.pDp I.pl I.pDq I.ql
  wr : s.wr = I.W
  rsp : s.gpr .rsp = I.sp

theorem main_eq : VG.Impl.Rsa.X86_64.Keys.CrtValues.main = seqs (([.block head] : List (Prog isa)) ++
    ((loadA aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
      (loadA aP VG.Impl.Rsa.X86_64.Keys.CrtValues.sP sPl ++ (loadA aQ VG.Impl.Rsa.X86_64.Keys.CrtValues.sQ sQl ++ loadA VG.Impl.Rsa.X86_64.Keys.CrtValues.aD VG.Impl.Rsa.X86_64.Keys.CrtValues.sD VG.Impl.Rsa.X86_64.Keys.CrtValues.sDl))) ++
    (pqCheck ++ (invPart ++ ((divisor aP ++ ([divmod aU aV aC aT] : List (Prog isa))) ++
    (([zeroA aX₁, copyA aX₁ aV] : List (Prog isa)) ++
    ((divisor aQ ++ ([divmod aU aV aC aT] : List (Prog isa))) ++
    (storeA aX₂ sQi sPl Impl.Bignum.X86_64.Public.sMask ++
      (storeA aX₁ sDp sPl Impl.Bignum.X86_64.Public.sMask ++
        (storeA aV sDq sQl Impl.Bignum.X86_64.Public.sMask ++ ([.block retMask] : List (Prog isa)))))))))))) := by
  simp only [VG.Impl.Rsa.X86_64.Keys.CrtValues.main, List.append_assoc, List.cons_append, List.nil_append]

/-- A valid modulus is odd and at least `256^(k - 1)`. -/
theorem valid_lo {N k : Nat} (hv : Spec.Rsa.modulusValid N k = true) : N % 2 = 1 ∧ 256 ^ (k - 1) ≤ N := by
  rw [Spec.Rsa.modulusValid, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hv
  obtain ⟨⟨⟨h1, -⟩, -⟩, h4⟩ := hv
  exact ⟨by simpa using h1, of_decide_eq_true h4⟩

/-- Factors of a valid modulus, each shorter than it: odd and above 1. -/
theorem factors_of {N P Q k pl ql : Nat} (hN : N % 2 = 1) (hlo : 256 ^ (k - 1) ≤ N) (hP : P < 256 ^ pl)
    (hQ : Q < 256 ^ ql) (hpl : pl < k) (hql : ql < k) (h : P * Q = N) :
    P % 2 = 1 ∧ 1 < P ∧ Q % 2 = 1 ∧ 1 < Q := by
  have hp1 : 256 ^ pl ≤ 256 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hq1 : 256 ^ ql ≤ 256 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpo := (VG.Proof.Rsa.X86_64.pq_iff hN).mpr h
  have hqo := (VG.Proof.Rsa.X86_64.pq_iff (P := Q) (Q := P) hN).mpr (by rw [Nat.mul_comm]; exact h)
  refine ⟨hpo.1, ?_, hqo.1, ?_⟩
  · rcases Nat.lt_or_ge 1 P with h1 | h1
    · exact h1
    · exfalso
      have : P * Q ≤ 1 * Q := Nat.mul_le_mul_right _ h1
      omega
  · rcases Nat.lt_or_ge 1 Q with h1 | h1
    · exact h1
    · exfalso
      have : P * Q ≤ P * 1 := Nat.mul_le_mul_left _ h1
      omega

theorem pow256_le_wk (len : Nat) : 256 ^ len ≤ 2 ^ (64 * ((len + 7) / 8)) := by
  rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by omega)

theorem pow256_le_w {len k : Nat} (h : len < k) : 256 ^ len ≤ 2 ^ (64 * VG.Proof.Rsa.X86_64.wk k) := by
  rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by unfold VG.Proof.Rsa.X86_64.wk; omega)

/-- `head`: the working space, the mask all ones, and `CvS` from the
memory on entry to `main`. -/
theorem cvHeadS_ok {I : VG.Proof.Rsa.X86_64.CvIn} {s : State} (h : VG.Proof.Rsa.X86_64.CvPre I s) :
    WP isa (.block head) s fun t => VG.Proof.Rsa.X86_64.CvS I s.mem t ∧ VG.Proof.Rsa.X86_64.mword t.mem I.B = VG.Proof.Bignum.X86_64.mask true := by
  have L := h.L
  have hZ := L.z
  refine WP.mono (VG.Proof.Rsa.X86_64.cvHead_ok h.scr h.rdi L.k1 L.k2 hZ h.args.k) fun s₁ ⟨hw₁, hm₁, f₁, k₁⟩ => ⟨?_, hm₁⟩
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have k1 := L.k1
  have hi₁ : InScr I.B I.Z s.mem s₁.mem := InScr.of_frm f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega)
  exact ⟨hw₁, h.args.congr fun i hi => f₁.word_eq (fun r hr => by
      unfold VG.Proof.Rsa.X86_64.argSlot at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega) (by unfold VG.Proof.Rsa.X86_64.argSlot at hi; omega),
    h.n.congrK hi₁ k₁, h.p.congrK hi₁ k₁, h.q.congrK hi₁ k₁, h.d.congrK hi₁ k₁, hi₁, k₁.2.2.trans h.wr,
    (k₁.gpr (by decide)).trans h.rsp⟩

/-- `main`, from a valid modulus. -/
theorem cvMain_ok {I : VG.Proof.Rsa.X86_64.CvIn} {s : State} (h : VG.Proof.Rsa.X86_64.CvPre I s) (hv : Spec.Rsa.modulusValid I.N I.k = true) :
    WP isa VG.Impl.Rsa.X86_64.Keys.CrtValues.main s fun t => ∃ X : Nat, (I.ok = true → Spec.Rsa.inverse I.Q I.P = some X) ∧
      (List.range I.pl).map (fun i => t.mem (I.pQi + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if I.ok then X else 0) I.pl ∧
      (List.range I.pl).map (fun i => t.mem (I.pDp + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if I.ok then I.D % (I.P - 1) else 0) I.pl ∧
      (List.range I.ql).map (fun i => t.mem (I.pDq + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if I.ok then I.D % (I.Q - 1) else 0) I.ql ∧
      t.gpr .rax = BitVec.ofNat 64 I.ok.toNat ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = I.sv i) ∧
      (∀ x, I.Z ≤ VG.Proof.Bignum.X86_64.ofs I.B x → (∀ i < I.pl, x ≠ I.pQi + BitVec.ofNat 64 i) →
        (∀ i < I.pl, x ≠ I.pDp + BitVec.ofNat 64 i) → (∀ i < I.ql, x ≠ I.pDq + BitVec.ofNat 64 i) →
        t.mem x = s.mem x) ∧
      t.gpr .rsp = s.gpr .rsp := by
  have L := h.L
  have k1 := L.k1
  have k2 := L.k2
  have hn := h.scr.nowrap
  have hZ := L.z
  obtain ⟨hNo, hlo⟩ := VG.Proof.Rsa.X86_64.valid_lo hv
  have hPl : I.P < 256 ^ I.pl := by have := os2ip_lt I.pb; rw [L.pbl] at this; exact this
  have hQl : I.Q < 256 ^ I.ql := by have := os2ip_lt I.qb; rw [L.qbl] at this; exact this
  have hPw := VG.Proof.Rsa.X86_64.pow256_le_w (k := I.k) L.pl2
  have hQw := VG.Proof.Rsa.X86_64.pow256_le_w (k := I.k) L.ql2
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  rw [VG.Proof.Rsa.X86_64.main_eq]
  -- The head.
  refine wp_seqs_append (by simp) (by simp [loadA]) (WP.mono (VG.Proof.Rsa.X86_64.cvHeadS_ok h) fun s₁ ⟨h₁, hm₁⟩ => ?_)
  -- The loads.
  refine wp_seqs_append (by simp [loadA]) (by simp [pqCheck]) (WP.mono (VG.Proof.Rsa.X86_64.cvLoads_ok h₁ L)
    fun s₂ ⟨h₂, m₂, vN, vP, vQ, vD⟩ => ?_)
  -- `p q = n`.
  refine wp_seqs_append (by simp [pqCheck]) (by simp [invPart]) (WP.mono (VG.Proof.Rsa.X86_64.cvCheck_ok h₂ L (c := true)
    (by rw [m₂]; exact hm₁) (by rw [vN]; exact hNo)) fun s₃ ⟨h₃, m₃, p₃⟩ => ?_)
  rw [vP, vQ, vN, Bool.true_and] at m₃
  have vP₃ : wv s₃.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k) = I.P := by rw [p₃ aP (.inl rfl), vP]
  have vQ₃ : wv s₃.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aQ) (VG.Proof.Rsa.X86_64.wk I.k) = I.Q := by rw [p₃ aQ (.inr (.inl rfl)), vQ]
  have vD₃ : wv s₃.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) VG.Impl.Rsa.X86_64.Keys.CrtValues.aD) (VG.Proof.Rsa.X86_64.wk I.k) = I.D := by rw [p₃ VG.Impl.Rsa.X86_64.Keys.CrtValues.aD (.inr (.inr rfl)), vD]
  have hf : I.P * I.Q = I.N → I.P % 2 = 1 ∧ 1 < I.P ∧ I.Q % 2 = 1 ∧ 1 < I.Q :=
    VG.Proof.Rsa.X86_64.factors_of hNo hlo hPl hQl L.pl2 L.ql2
  -- `qInv` and `gcd(q, p) = 1`.
  refine wp_seqs_append (by simp [invPart]) (by simp [divisor]) (WP.mono (VG.Proof.Rsa.X86_64.cvInv_ok h₃ L m₃ (fun hc => by
    rw [vP₃]; have := hf (of_decide_eq_true hc); exact ⟨this.1, this.2.1⟩)) fun s₄ ⟨h₄, m₄, i₄, p₄⟩ => ?_)
  rw [vP₃, vQ₃] at m₄ i₄
  have vP₄ : wv s₄.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aP) (VG.Proof.Rsa.X86_64.wk I.k) = I.P := by rw [p₄ aP (.inl rfl), vP₃]
  have vQ₄ : wv s₄.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aQ) (VG.Proof.Rsa.X86_64.wk I.k) = I.Q := by rw [p₄ aQ (.inr (.inl rfl)), vQ₃]
  have vD₄ : wv s₄.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) VG.Impl.Rsa.X86_64.Keys.CrtValues.aD) (VG.Proof.Rsa.X86_64.wk I.k) = I.D := by rw [p₄ VG.Impl.Rsa.X86_64.Keys.CrtValues.aD (.inr (.inr rfl)), vD₃]
  have hok : (decide (I.P * I.Q = I.N) && decide (Nat.gcd I.Q I.P = 1)) = I.ok := by
    simp only [CvIn.ok, Bool.decide_and]
  rw [hok] at m₄
  have hokP : I.ok = true → I.P * I.Q = I.N ∧ Nat.gcd I.Q I.P = 1 := fun hc => of_decide_eq_true hc
  -- `dP` into `aV`.
  refine wp_seqs_append (by simp [divisor]) (by simp) (WP.mono (VG.Proof.Rsa.X86_64.cvDivPart_ok h₄ L (j := aP) (.inl rfl))
    fun s₅ ⟨h₅, m₅, d₅, p₅⟩ => ?_)
  rw [vP₄, vD₄] at d₅
  -- `dP` into `aX₁`.
  have hZ' := h₅.ws.hZ
  have hn' := h₅.ws.scr.nowrap
  refine wp_seqs_append (by simp) (by simp [divisor]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.zeroA_ok h₅.ws (j := aX₁) (by decide)) fun s₆ ⟨_, o₆, k₆⟩ => ?_)
  have h₆ := h₅.arr (by decide) (Nat.le_refl _) o₆ k₆ (by decide)
  refine WP.mono (VG.Proof.Rsa.X86_64.copyA_ok h₆.ws (o := aX₁) (a := aV) (by decide) (by decide) (by decide)) fun s₇ ⟨c₇, o₇, k₇⟩ => ?_
  have h₇ := h₆.arr (by decide) (by omega) o₇ k₇ (by decide)
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, VG.Proof.Bignum.X86_64.Outside I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) j) Ln m m' → Ln ≤ 8 * (VG.Proof.Rsa.X86_64.wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) (VG.Proof.Rsa.X86_64.wk I.k) = wv m I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) (VG.Proof.Rsa.X86_64.wk I.k) :=
    fun o hL hij hi => VG.Proof.Rsa.X86_64.outside_arr o hL hij (by omega) hi hZ' hn'
  have hmw : ∀ {m m' : Mem} {i L' : Nat}, VG.Proof.Bignum.X86_64.Outside I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) L' m m' → L' ≤ 8 * (VG.Proof.Rsa.X86_64.wk I.k + 2) →
      VG.Proof.Rsa.X86_64.mword m' I.B = VG.Proof.Rsa.X86_64.mword m I.B := fun {_ _ i _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) i (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega))
      (by omega)
  have m₇ : VG.Proof.Rsa.X86_64.mword s₇.mem I.B = VG.Proof.Bignum.X86_64.mask I.ok := by rw [hmw o₇ (by omega), hmw o₆ (Nat.le_refl _), m₅, m₄]
  have pr₇ : ∀ i, i = aP ∨ i = aQ ∨ i = VG.Impl.Rsa.X86_64.Keys.CrtValues.aD ∨ i = aX₂ →
      wv s₇.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) (VG.Proof.Rsa.X86_64.wk I.k) = wv s₄.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) i) (VG.Proof.Rsa.X86_64.wk I.k) := fun i hi => by
    have h1 : i ≠ aX₁ := by rcases hi with rfl | rfl | rfl | rfl <;> decide
    have h2 : i < 16 := by rcases hi with rfl | rfl | rfl | rfl <;> decide
    rw [ot o₇ (by omega) h1 h2, ot o₆ (Nat.le_refl _) h1 h2,
      p₅ i (by rcases hi with rfl | rfl | rfl | rfl <;> simp)]
  have dP₇ : I.ok = true → wv s₇.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₁) (VG.Proof.Rsa.X86_64.wk I.k) = I.D % (I.P - 1) := fun hc => by
    obtain ⟨hpq, -⟩ := hokP hc
    have hfp := hf hpq
    have e := d₅ hfp.1 hfp.2.1
    rw [c₇, ot o₆ (Nat.le_refl _) (by decide) (by decide)]
    rw [← e]
    refine VG.Proof.Rsa.X86_64.wv_low_of_lt (by omega) ?_
    rw [e]
    have : I.D % (I.P - 1) < I.P - 1 := Nat.mod_lt _ (by omega)
    omega
  -- `dQ` into `aV`.
  have vQ₇ : wv s₇.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aQ) (VG.Proof.Rsa.X86_64.wk I.k) = I.Q := by rw [pr₇ aQ (by simp), vQ₄]
  have vD₇ : wv s₇.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) VG.Impl.Rsa.X86_64.Keys.CrtValues.aD) (VG.Proof.Rsa.X86_64.wk I.k) = I.D := by rw [pr₇ VG.Impl.Rsa.X86_64.Keys.CrtValues.aD (by simp), vD₄]
  refine wp_seqs_append (by simp [divisor]) (by simp [storeA]) (WP.mono (VG.Proof.Rsa.X86_64.cvDivPart_ok h₇ L (j := aQ) (.inr rfl))
    fun s₈ ⟨h₈, m₈, d₈, p₈⟩ => ?_)
  rw [vQ₇, vD₇] at d₈
  rw [m₇] at m₈
  -- The stores.
  have hw := h₈.ws.w1
  have := L.pl2
  have := L.ql2
  refine WP.mono (VG.Proof.Rsa.X86_64.cvStores_ok h₈.ws h₈.args m₈ L.pl1 (by unfold VG.Proof.Rsa.X86_64.wk; omega) L.ql1 (by unfold VG.Proof.Rsa.X86_64.wk; omega)
    ⟨fun i hi => by rw [h₈.wr, ← h.wr]; exact h.oQi.wr i hi, h.oQi.sep⟩
    ⟨fun i hi => by rw [h₈.wr, ← h.wr]; exact h.oDp.wr i hi, h.oDp.sep⟩
    ⟨fun i hi => by rw [h₈.wr, ← h.wr]; exact h.oDq.wr i hi, h.oDq.sep⟩ h.a1 h.a2 h.a3)
    fun t ⟨bQi, bDp, bDq, hax, hsv, hfr, kt⟩ => ?_
  have vX₈ : wv s₈.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₂) (VG.Proof.Rsa.X86_64.wk I.k) = wv s₄.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₂) (VG.Proof.Rsa.X86_64.wk I.k) := by
    rw [p₈ aX₂ (by simp), pr₇ aX₂ (by simp)]
  have vX₁₈ : wv s₈.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₁) (VG.Proof.Rsa.X86_64.wk I.k) = wv s₇.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₁) (VG.Proof.Rsa.X86_64.wk I.k) :=
    p₈ aX₁ (by simp)
  refine ⟨wv s₄.mem I.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk I.k) aX₂) (VG.Proof.Rsa.X86_64.wk I.k), fun hc => ?_, ?_, ?_, ?_, hax, hsv,
    fun x hx n1 n2 n3 => by rw [hfr x n1 n2 n3, h₈.inScr x hx],
    (kt.gpr (by decide)).trans (h₈.rsp.trans h.rsp.symm)⟩
  · obtain ⟨hpq, hg⟩ := hokP hc
    obtain ⟨hdvd, hlt⟩ := i₄ (decide_eq_true hpq)
    rw [hg] at hdvd
    exact VG.Proof.Rsa.inverse_eq (hf hpq).2.1 hlt (by exact_mod_cast hdvd)
  · rw [bQi]
    cases hc : I.ok
    · rfl
    · obtain ⟨hpq, -⟩ := hokP hc
      obtain ⟨-, hlt⟩ := i₄ (decide_eq_true hpq)
      have := VG.Proof.Rsa.X86_64.pow256_le_wk I.pl
      simp only [ite_true]
      rw [← vX₈]
      exact congrArg (Spec.Rsa.i2osp · I.pl) (VG.Proof.Rsa.X86_64.wv_low_of_lt (by unfold VG.Proof.Rsa.X86_64.wk; omega) (by omega))
  · rw [bDp]
    cases hc : I.ok
    · rfl
    · obtain ⟨hpq, -⟩ := hokP hc
      have hfp := hf hpq
      have e := dP₇ hc
      have := VG.Proof.Rsa.X86_64.pow256_le_wk I.pl
      have : I.D % (I.P - 1) < I.P - 1 := Nat.mod_lt _ (by omega)
      simp only [ite_true]
      rw [← e, ← vX₁₈]
      exact congrArg (Spec.Rsa.i2osp · I.pl) (VG.Proof.Rsa.X86_64.wv_low_of_lt (by unfold VG.Proof.Rsa.X86_64.wk; omega) (by rw [vX₁₈, e]; omega))
  · rw [bDq]
    cases hc : I.ok
    · rfl
    · obtain ⟨hpq, -⟩ := hokP hc
      have hfp := hf hpq
      have e := d₈ hfp.2.2.1 hfp.2.2.2
      have := VG.Proof.Rsa.X86_64.pow256_le_wk I.ql
      have : I.D % (I.Q - 1) < I.Q - 1 := Nat.mod_lt _ (by omega)
      simp only [ite_true]
      rw [← e]
      exact congrArg (Spec.Rsa.i2osp · I.ql) (VG.Proof.Rsa.X86_64.wv_low_of_lt (by unfold VG.Proof.Rsa.X86_64.wk; omega) (by rw [e]; omega))

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.CvFail`. -/
section

/-!
# `vg_rsa_crt_values` on x86-64: an invalid modulus

`zeroOut` writes zeros to an output (`zeroOut_ok`); `fail` to all three,
returns 0 and restores the saved registers (`cvFail_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.WriteBytes (writeW8_apply)

/-- `zeroOut sPtr sLen`: `len` zeros at `op`. -/
theorem zeroOut_ok {s : State} {B : Addr} {Z : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z)
    {sPtr sLen len : Nat} {op : Addr} (hP : sPtr < 32) (hL : sLen < 32)
    (hO : VG.Proof.Bignum.X86_64.word s.mem B (8 * sPtr) = op) (hK : VG.Proof.Bignum.X86_64.word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hk1 : 1 ≤ len) (hk' : len < 2 ^ 31) (o : VG.Proof.Rsa.X86_64.OutOk s B Z op len) :
    WP isa (zeroOut sPtr sLen) s fun t =>
      (∀ i < len, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      (∀ x, (∀ j < len, x ≠ op + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧ VG.Proof.MlKem.X86_64.Keep [.rsi, .rcx, .rax] s t := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = op ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rax = 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, hdrOff, hl sPtr hP, hl sLen hL, hO, hK]) rfl) fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_upto (a := 0) (N := len) (by omega) (FailInv s₁ op len) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩) fun t hI => ?_
  · intro j _ hj t hI
    have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
      rw [hI.keep.2.2, k₁.2.2]; exact o.wr j hj
    have hax' : (t.gpr .rax).setWidth 8 = 0 := by rw [hI.keep.gpr (by decide), hax]; rfl
    refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t' =>
        t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
        t'.gpr .rsi = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .rcx = BitVec.ofNat 64 (len - (j + 1)) ∧
        t'.zf = some (decide (j + 1 = len))) (by
      xrun [State.ea, at0, hI.rsi, hI.rcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst, hax',
        ofNat64_pred (show 1 ≤ len - j by omega) (by omega), BitVec.add_assoc, ofNat_add_one,
        ofNat64_beq_zero (show len - j - 1 < 2 ^ 64 by omega)]
      exact ⟨by rw [show len - j - 1 = len - (j + 1) by omega], decide_eq_decide.mpr (by omega)⟩) rfl)
      fun t' ⟨⟨hm, hsi', hcx', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩
    · intro i hi
      rw [hm, VG.WriteBytes.writeW8_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
        exact hI.bytes i (by omega)
    · intro x hx
      rw [hm, VG.WriteBytes.writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
      exact hI.frame x fun i hi => hx i (by omega)
  exact ⟨hI.bytes, fun x hx => by rw [hI.frame x hx, hm₁], (k₁.trans hI.keep).mono (by decide)⟩

/-- `fail`: zeros to `qInv`, `dP` and `dQ`, 0 returned, and the saved
registers restored. -/
theorem cvFail_ok {s : State} {B : Addr} {Z : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z)
    {k pl ql dl : Nat} {pDp pDq pQi pN pP pQ pD : Addr} {sv : Nat → BitVec 64}
    (ha : VG.Proof.Rsa.X86_64.CvArgs s.mem B k pl ql dl pDp pDq pQi pN pP pQ pD sv)
    (hpl1 : 1 ≤ pl) (hpl2 : pl < 2 ^ 31) (hql1 : 1 ≤ ql) (hql2 : ql < 2 ^ 31)
    (oQi : VG.Proof.Rsa.X86_64.OutOk s B Z pQi pl) (oDp : VG.Proof.Rsa.X86_64.OutOk s B Z pDp pl) (oDq : VG.Proof.Rsa.X86_64.OutOk s B Z pDq ql)
    (a1 : VG.Proof.Rsa.X86_64.Apart pQi pl pDp pl) (a2 : VG.Proof.Rsa.X86_64.Apart pQi pl pDq ql) (a3 : VG.Proof.Rsa.X86_64.Apart pDp pl pDq ql) :
    WP isa VG.Impl.Rsa.X86_64.Keys.CrtValues.fail s fun t =>
      (∀ i < pl, t.mem (pQi + BitVec.ofNat 64 i) = 0) ∧ (∀ i < pl, t.mem (pDp + BitVec.ofNat 64 i) = 0) ∧
      (∀ i < ql, t.mem (pDq + BitVec.ofNat 64 i) = 0) ∧
      t.gpr .rax = 0 ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = sv i) ∧
      (∀ x, (∀ i < pl, x ≠ pQi + BitVec.ofNat 64 i) → (∀ i < pl, x ≠ pDp + BitVec.ofNat 64 i) →
        (∀ i < ql, x ≠ pDq + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      t.gpr .rsp = s.gpr .rsp := by
  have hn := hs.nowrap
  -- Words of the header, after stores outside the working space.
  have fw : ∀ {m m' : Mem} {op : Addr} {len : Nat}, (∀ j < len, Z ≤ VG.Proof.Bignum.X86_64.ofs B (op + BitVec.ofNat 64 j)) →
      (∀ x, (∀ j < len, x ≠ op + BitVec.ofNat 64 j) → m' x = m x) → ∀ i < 32, VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i) :=
    fun hsep hx i hi => (VG.Proof.Rsa.X86_64.frm_scr hsep hx).word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
  unfold VG.Impl.Rsa.X86_64.Keys.CrtValues.fail
  simp only [seqs]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.zeroOut_ok hs hdi hZ (by decide) (by decide) ha.dp ha.pl hpl1 hpl2 oDp)
    fun s₁ ⟨z₁, x₁, k₁⟩ => ?_)
  have w₁ := fw oDp.sep x₁
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.zeroOut_ok hs₁ hdi₁ hZ (by decide) (by decide) (by rw [w₁ _ (by decide)]; exact ha.dq)
    (by rw [w₁ _ (by decide)]; exact ha.ql) hql1 hql2 ⟨fun i hi => by rw [k₁.2.2]; exact oDq.wr i hi, oDq.sep⟩)
    fun s₂ ⟨z₂, x₂, k₂⟩ => ?_)
  have w₂ := fw oDq.sep x₂
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.zeroOut_ok hs₂ hdi₂ hZ (by decide) (by decide)
    (by rw [w₂ _ (by decide), w₁ _ (by decide)]; exact ha.qi) (by rw [w₂ _ (by decide), w₁ _ (by decide)]; exact ha.pl)
    hpl1 hpl2 ⟨fun i hi => by rw [k₂.2.2, k₁.2.2]; exact oQi.wr i hi, oQi.sep⟩) fun s₃ ⟨z₃, x₃, k₃⟩ => ?_)
  have w₃ := fw oQi.sep x₃
  have hs₃ := hs₂.congr k₃.2.2
  have hdi₃ : s₃.gpr .rdi = B := (k₃.gpr (by decide)).trans hdi₂
  have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs₃.ld (by omega)
  have hw : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₃.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi => by
    rw [w₃ i hi, w₂ i hi, w₁ i hi]
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = 0 ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.word s.mem B (8 * 0) ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.word s.mem B (8 * 1) ∧ t.gpr .r12 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 2) ∧
      t.gpr .r13 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 3) ∧ t.gpr .r14 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 4) ∧
      t.gpr .r15 = VG.Proof.Bignum.X86_64.word s.mem B (8 * 5) ∧ t.mem = s₃.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi₃, hdrOff, hl₃ 0 (by decide), hl₃ 1 (by decide), hl₃ 2 (by decide),
      hl₃ 3 (by decide), hl₃ 4 (by decide), hl₃ 5 (by decide), hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm⟩, k₄⟩ => ?_
  have kk := ((k₁.trans k₂).trans k₃).trans k₄
  rw [hm]
  refine ⟨z₃, fun i hi => ?_, fun i hi => ?_, hax, fun i hi => ?_, fun x n1 n2 n3 => by rw [x₃ x n1, x₂ x n3, x₁ x n2],
    kk.gpr (by decide)⟩
  · rw [x₃ _ (fun j hj => (a1 j hj i hi).symm), x₂ _ (fun j hj => a3 i hi j hj)]
    exact z₁ i hi
  · rw [x₃ _ (fun j hj => (a2 j hj i hi).symm)]
    exact z₂ i hi
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0.trans (ha.saved 0 (by decide))
    · exact h1.trans (ha.saved 1 (by decide))
    · exact h2.trans (ha.saved 2 (by decide))
    · exact h3.trans (ha.saved 3 (by decide))
    · exact h4.trans (ha.saved 4 (by decide))
    · exact h5.trans (ha.saved 5 (by decide))

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.CvCode`. -/
section

/-!
# `vg_rsa_crt_values` on x86-64: correctness

`CrtValues.code`, from a state its contract allows, writes `crtKey` of its
inputs (`cvCode_correct`), against `cvContract`, which states the shared
contract's precondition on the registers and the stack.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-! ## The contract on the registers and the stack -/

/-- `vg_rsa_crt_values(dp = rdi, dp_len = rsi, dq = rdx, dq_len = rcx,
qinv = r8, qinv_len = r9, n = [rsp + 8], n_len = [rsp + 16],
p = [rsp + 24], p_len = [rsp + 32], q = [rsp + 40], q_len = [rsp + 48],
d = [rsp + 56], d_len = [rsp + 64], scratch = [rsp + 72],
scratch_len = [rsp + 80])`. -/
def cvContract : Contract isa where
  pre s :=
    let dp : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let dq : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let qi : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let n : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let p : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let q : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let d : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let scr : Region := ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 80⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    (s.gpr .rsp).toNat + 88 ≤ 2 ^ 64 ∧
      s.rd = [n, p, q, d, args] ∧ s.wr = [dp, dq, qi, scr] ∧
      dp.Disjoint dq ∧ dp.Disjoint qi ∧ dp.Disjoint n ∧ dp.Disjoint p ∧ dp.Disjoint q ∧ dp.Disjoint d ∧
      dp.Disjoint scr ∧ dp.Disjoint args ∧
      dq.Disjoint qi ∧ dq.Disjoint n ∧ dq.Disjoint p ∧ dq.Disjoint q ∧ dq.Disjoint d ∧ dq.Disjoint scr ∧
      dq.Disjoint args ∧
      qi.Disjoint n ∧ qi.Disjoint p ∧ qi.Disjoint q ∧ qi.Disjoint d ∧ qi.Disjoint scr ∧ qi.Disjoint args ∧
      n.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ d.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint dp ∧ ret.Disjoint dq ∧ ret.Disjoint qi ∧ ret.Disjoint n ∧ ret.Disjoint p ∧
      ret.Disjoint q ∧ ret.Disjoint d ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧ (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 8).toNat + (stackArg s 9).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (stackArg s 1).toNat ∧ 1 ≤ (stackArg s 3).toNat ∧
      (stackArg s 3).toNat < (stackArg s 1).toNat ∧ 1 ≤ (stackArg s 5).toNat ∧
      (stackArg s 5).toNat < (stackArg s 1).toNat ∧ (s.gpr .rsi).toNat = (stackArg s 3).toNat ∧
      (s.gpr .r9).toNat = (stackArg s 3).toNat ∧ (s.gpr .rcx).toNat = (stackArg s 5).toNat ∧
      1 ≤ (stackArg s 7).toNat ∧ (stackArg s 7).toNat ≤ (stackArg s 1).toNat ∧
      Spec.Rsa.scratchWords (stackArg s 1).toNat ≤ (stackArg s 9).toNat
  post s s' :=
    Spec.Rsa.writtenAll s'.mem [(s.gpr .rdi, (stackArg s 3).toNat), (s.gpr .rdx, (stackArg s 5).toNat),
        (s.gpr .r8, (stackArg s 3).toNat)] ((s'.gpr .rax).setWidth 32)
      ((Spec.Rsa.crtKey (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 5).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 7).toNat)).map fun v => [v.1, v.2.1, v.2.2])
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      stackArg s₁ 3 = stackArg s₂ 3 ∧ stackArg s₁ 4 = stackArg s₂ 4 ∧ stackArg s₁ 5 = stackArg s₂ 5 ∧
      stackArg s₁ 6 = stackArg s₂ 6 ∧ stackArg s₁ 7 = stackArg s₂ 7 ∧ stackArg s₁ 8 = stackArg s₂ 8 ∧
      stackArg s₁ 9 = stackArg s₂ 9 ∧
      Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 0) (stackArg s₁ 1).toNat =
        Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 0) (stackArg s₂ 1).toNat

/-! ## The entry -/

theorem cvEntry_eq : VG.Impl.Rsa.X86_64.Keys.CrtValues.entry = ([.mov .r11 (.mem { base := .rsp, disp := 72 }),
    .store (hdr11 0) .rbx, .store (hdr11 1) .rbp, .store (hdr11 2) .r12, .store (hdr11 3) .r13,
    .store (hdr11 4) .r14, .store (hdr11 5) .r15,
    .store (hdr11 sDp) .rdi, .store (hdr11 sPl) .rsi, .store (hdr11 sDq) .rdx, .store (hdr11 sQl) .rcx,
    .store (hdr11 sQi) .r8] : List Instr) ++
    (crtPairs [(0, Impl.Bignum.X86_64.Public.sN), (1, Impl.Bignum.X86_64.Public.sK), (2, VG.Impl.Rsa.X86_64.Keys.CrtValues.sP), (4, VG.Impl.Rsa.X86_64.Keys.CrtValues.sQ), (6, VG.Impl.Rsa.X86_64.Keys.CrtValues.sD),
      (7, VG.Impl.Rsa.X86_64.Keys.CrtValues.sDl)] ++ ([.mov .rdi (.reg .r11)] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def cvEntryMemA (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vdp vpl vdq vql vqi : BitVec 64) : Mem :=
  ((((((((((m.writeW (VG.Proof.Bignum.X86_64.off B (8 * 0)) v0).writeW (VG.Proof.Bignum.X86_64.off B (8 * 1)) v1).writeW (VG.Proof.Bignum.X86_64.off B (8 * 2)) v2).writeW
    (VG.Proof.Bignum.X86_64.off B (8 * 3)) v3).writeW (VG.Proof.Bignum.X86_64.off B (8 * 4)) v4).writeW (VG.Proof.Bignum.X86_64.off B (8 * 5)) v5).writeW (VG.Proof.Bignum.X86_64.off B (8 * sDp)) vdp).writeW
    (VG.Proof.Bignum.X86_64.off B (8 * sPl)) vpl).writeW (VG.Proof.Bignum.X86_64.off B (8 * sDq)) vdq).writeW (VG.Proof.Bignum.X86_64.off B (8 * sQl)) vql).writeW (VG.Proof.Bignum.X86_64.off B (8 * sQi)) vqi

/-- The header after the entry's stores. -/
def cvEntryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vdp vpl vdq vql vqi vn vk vp vq vd vdl : BitVec 64) : Mem :=
  ((((((VG.Proof.Rsa.X86_64.cvEntryMemA m B v0 v1 v2 v3 v4 v5 vdp vpl vdq vql vqi).writeW (VG.Proof.Bignum.X86_64.off B (8 * Impl.Bignum.X86_64.Public.sN))
    vn).writeW (VG.Proof.Bignum.X86_64.off B (8 * Impl.Bignum.X86_64.Public.sK)) vk).writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Rsa.X86_64.Keys.CrtValues.sP)) vp).writeW
    (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Rsa.X86_64.Keys.CrtValues.sQ)) vq).writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Rsa.X86_64.Keys.CrtValues.sD)) vd).writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Rsa.X86_64.Keys.CrtValues.sDl)) vdl

theorem cvEntryMemA_outside (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vdp vpl vdq vql vqi : BitVec 64) :
    VG.Proof.Bignum.X86_64.Outside B 0 (8 * 32) m (VG.Proof.Rsa.X86_64.cvEntryMemA m B v0 v1 v2 v3 v4 v5 vdp vpl vdq vql vqi) := by
  unfold VG.Proof.Rsa.X86_64.cvEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem cvEntryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vdp vpl vdq vql vqi vn vk vp vq vd vdl : BitVec 64) :
    let m' := VG.Proof.Rsa.X86_64.cvEntryMem m B v0 v1 v2 v3 v4 v5 vdp vpl vdq vql vqi vn vk vp vq vd vdl
    VG.Proof.Bignum.X86_64.word m' B (8 * 0) = v0 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 1) = v1 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 2) = v2 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 3) = v3 ∧
    VG.Proof.Bignum.X86_64.word m' B (8 * 4) = v4 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * 5) = v5 ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sDp) = vdp ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sPl) = vpl ∧
    VG.Proof.Bignum.X86_64.word m' B (8 * sDq) = vdq ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sQl) = vql ∧ VG.Proof.Bignum.X86_64.word m' B (8 * sQi) = vqi ∧
    VG.Proof.Bignum.X86_64.word m' B (8 * Impl.Bignum.X86_64.Public.sN) = vn ∧ VG.Proof.Bignum.X86_64.word m' B (8 * Impl.Bignum.X86_64.Public.sK) = vk ∧
    VG.Proof.Bignum.X86_64.word m' B (8 * VG.Impl.Rsa.X86_64.Keys.CrtValues.sP) = vp ∧ VG.Proof.Bignum.X86_64.word m' B (8 * VG.Impl.Rsa.X86_64.Keys.CrtValues.sQ) = vq ∧ VG.Proof.Bignum.X86_64.word m' B (8 * VG.Impl.Rsa.X86_64.Keys.CrtValues.sD) = vd ∧ VG.Proof.Bignum.X86_64.word m' B (8 * VG.Impl.Rsa.X86_64.Keys.CrtValues.sDl) = vdl ∧
    VG.Proof.Bignum.X86_64.Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' VG.Proof.Rsa.X86_64.cvEntryMem VG.Proof.Rsa.X86_64.cvEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments, and the working space's base
(stack argument 8) in `rdi`. -/
theorem cvEntry_ok {s : State} {B : Addr} (hB : stackArg s 8 = B)
    (hw : ∀ i < 32, InRegions s.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8)
    (ha : ∀ j < 9, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 9, ∀ m', VG.Proof.Bignum.X86_64.Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block VG.Impl.Rsa.X86_64.Keys.CrtValues.entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, VG.Proof.Bignum.X86_64.word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sDp) = s.gpr .rdi ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sPl) = s.gpr .rsi ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sDq) = s.gpr .rdx ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * sQl) = s.gpr .rcx ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * sQi) = s.gpr .r8 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * Impl.Bignum.X86_64.Public.sN) = stackArg s 0 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * Impl.Bignum.X86_64.Public.sK) = stackArg s 1 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * VG.Impl.Rsa.X86_64.Keys.CrtValues.sP) = stackArg s 2 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * VG.Impl.Rsa.X86_64.Keys.CrtValues.sQ) = stackArg s 4 ∧
      VG.Proof.Bignum.X86_64.word t.mem B (8 * VG.Impl.Rsa.X86_64.Keys.CrtValues.sD) = stackArg s 6 ∧ VG.Proof.Bignum.X86_64.word t.mem B (8 * VG.Impl.Rsa.X86_64.Keys.CrtValues.sDl) = stackArg s 7 ∧
      VG.Proof.Bignum.X86_64.Outside B 0 (8 * 32) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r11, .rax, .rdi] s t := by
  have e8 : s.gpr .rsp + BitVec.ofInt 64 72 = stackArgAddr s 8 := rfl
  have hB' : s.mem.readW (stackArgAddr s 8) 64 = B := hB
  have ha8 := ha 8 (by decide)
  rw [VG.Proof.Rsa.X86_64.cvEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧
      t.mem = VG.Proof.Rsa.X86_64.cvEntryMemA s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
        (s.gpr .r15) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8)) ?_ rfl)
    fun t₁ ⟨⟨h11, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr11, e8, ha8, hB', hdrOff, hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sDp (by decide),
      hw sPl (by decide), hw sDq (by decide), hw sQl (by decide), hw sQi (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (crtPairs_ok _ t₁ ?_ h11 (k₁.gpr (by decide)) k₁.2.1 k₁.2.2
    (by rw [hm₁]; exact VG.Proof.Rsa.X86_64.cvEntryMemA_outside _ _ _ _ _ _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h11₂ : t₂.gpr .r11 = B := (k₂.gpr (by decide)).trans h11
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = t₂.mem) (by xrun [h11₂]) rfl)
    fun t ⟨⟨hdi, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = VG.Proof.Rsa.X86_64.cvEntryMem s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (stackArg s 0) (stackArg s 1)
      (stackArg s 2) (stackArg s 4) (stackArg s 6) (stackArg s 7) := by
    rw [hm, hm₂, hm₁]; rfl
  rw [hmem]
  obtain ⟨h0, h1, h2, h3, h4, h5, hDp, hPl, hDq, hQl, hQi, hN, hK, hP, hQ, hD, hDl, ho⟩ :=
    VG.Proof.Rsa.X86_64.cvEntryMem_facts s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (stackArg s 0) (stackArg s 1)
      (stackArg s 2) (stackArg s 4) (stackArg s 6) (stackArg s 7)
  refine ⟨hdi, fun i hi => ?_, hDp, hPl, hDq, hQl, hQi, hN, hK, hP, hQ, hD, hDl, ho,
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-! ## The result -/

/-- What `CrtValues.code` leaves, from a valid modulus. -/
theorem cvWritten_of {m : Mem} {dp dq qi : Addr} {rax : BitVec 64} {nb pb qb db : List Byte} {X : Nat} {c : Bool}
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) nb.length = true)
    (hc : c = decide (Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb ∧
      Nat.gcd (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip pb) = 1))
    (hX : c = true → Spec.Rsa.inverse (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip pb) = some X)
    (b1 : Spec.Rsa.bytesAt m qi pb.length = Spec.Rsa.i2osp (if c then X else 0) pb.length)
    (b2 : Spec.Rsa.bytesAt m dp pb.length =
      Spec.Rsa.i2osp (if c then Spec.Rsa.os2ip db % (Spec.Rsa.os2ip pb - 1) else 0) pb.length)
    (b3 : Spec.Rsa.bytesAt m dq qb.length =
      Spec.Rsa.i2osp (if c then Spec.Rsa.os2ip db % (Spec.Rsa.os2ip qb - 1) else 0) qb.length)
    (hr : rax = BitVec.ofNat 64 c.toNat) :
    Spec.Rsa.writtenAll m [(dp, pb.length), (dq, qb.length), (qi, pb.length)] (rax.setWidth 32)
      ((Spec.Rsa.crtKey nb pb qb db).map fun v => [v.1, v.2.1, v.2.2]) := by
  simp only [Spec.Rsa.crtKey, hv, true_and]
  rw [hr, setWidth_flag]
  cases c
  · simp only [Bool.false_eq_true, ite_false] at b1 b2 b3
    have hnone : (if Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb then
        (Spec.Rsa.crtValues (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip db)).map
          (fun x => (Spec.Rsa.i2osp x.1 pb.length, Spec.Rsa.i2osp x.2.1 qb.length,
            Spec.Rsa.i2osp x.2.2 pb.length)) else none) = none := by
      split
      · rename_i hpq
        have hg : Nat.gcd (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip pb) ≠ 1 := fun hg =>
          absurd hc (by simp [hpq, hg])
        simp [Spec.Rsa.crtValues, VG.Proof.Rsa.inverse_none hg]
      · rfl
    rw [hnone]
    simp only [Option.map_none, Spec.Rsa.writtenAll, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    exact ⟨rfl, by rw [b2, i2osp_zero'], by rw [b3, i2osp_zero'], by rw [b1, i2osp_zero']⟩
  · simp only [ite_true] at b1 b2 b3
    have hpq := (of_decide_eq_true hc.symm).1
    simp only [hpq, ite_true]
    simp only [Spec.Rsa.crtValues, hX rfl, Option.map_some, Spec.Rsa.writtenAll, List.map_cons, List.map_nil]
    exact ⟨trivial, by rw [b2, b3, b1]⟩

theorem bytesAt_zero {m : Mem} {p : Addr} {n : Nat} (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.bytesAt m p n = List.replicate n 0 := by
  refine List.eq_replicate_iff.mpr ⟨by simp [Spec.Rsa.bytesAt], fun b hb => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact h i (List.mem_range.mp hi)

/-! ## The precondition, as the code uses it -/

theorem stkAddr_eq (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show 8 * (0 + 1) + 8 * j = 8 * (j + 1) by omega]

theorem stkAddr_add (s : State) (j b : Nat) :
    stackArgAddr s j + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j + b) := by
  rw [VG.Proof.Rsa.X86_64.stkAddr_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem apart_of {o₁ o₂ : Addr} {l₁ l₂ : Nat} (hd : (⟨o₁, l₁⟩ : Region).Disjoint ⟨o₂, l₂⟩) (h₁ : l₁ ≤ 2 ^ 64)
    (h₂ : l₂ ≤ 2 ^ 64) : VG.Proof.Rsa.X86_64.Apart o₁ l₁ o₂ l₂ := fun i hi j hj he =>
  hd _ (contains_byte o₁ hi h₁) (by rw [he]; exact contains_byte o₂ hj h₂)

/-- The inputs of `main`, from the entry state. -/
def cvIn (s : State) : VG.Proof.Rsa.X86_64.CvIn where
  B := stackArg s 8
  Z := (stackArg s 9).toNat * 8
  k := (stackArg s 1).toNat
  pl := (stackArg s 3).toNat
  ql := (stackArg s 5).toNat
  dl := (stackArg s 7).toNat
  pDp := s.gpr .rdi
  pDq := s.gpr .rdx
  pQi := s.gpr .r8
  pN := stackArg s 0
  pP := stackArg s 2
  pQ := stackArg s 4
  pD := stackArg s 6
  sv i := s.gpr (saved.getD i .rax)
  nb := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
  pb := Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat
  qb := Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 5).toNat
  db := Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 7).toNat
  W := s.wr
  sp := s.gpr .rsp

/-- What `CrtValues.code` uses of its contract's precondition. -/
structure CvCtx (s : State) : Prop where
  L : VG.Proof.Rsa.X86_64.CvLens (VG.Proof.Rsa.X86_64.cvIn s)
  rsi : (s.gpr .rsi).toNat = (stackArg s 3).toNat
  rcx : (s.gpr .rcx).toNat = (stackArg s 5).toNat
  hs : VG.Proof.Bignum.X86_64.Scr s (stackArg s 8) ((stackArg s 9).toNat * 8)
  ha : ∀ j < 9, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 9, ∀ m', VG.Proof.Bignum.X86_64.Outside (stackArg s 8) 0 (8 * 32) s.mem m' →
    m'.readW (stackArgAddr s j) 64 = stackArg s j
  n : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 0) (VG.Proof.Rsa.X86_64.cvIn s).nb
  p : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 2) (VG.Proof.Rsa.X86_64.cvIn s).pb
  q : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 4) (VG.Proof.Rsa.X86_64.cvIn s).qb
  d : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 6) (VG.Proof.Rsa.X86_64.cvIn s).db
  oQi : VG.Proof.Rsa.X86_64.OutOk s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .r8) (stackArg s 3).toNat
  oDp : VG.Proof.Rsa.X86_64.OutOk s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .rdi) (stackArg s 3).toNat
  oDq : VG.Proof.Rsa.X86_64.OutOk s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .rdx) (stackArg s 5).toNat
  a1 : VG.Proof.Rsa.X86_64.Apart (s.gpr .r8) (stackArg s 3).toNat (s.gpr .rdi) (stackArg s 3).toNat
  a2 : VG.Proof.Rsa.X86_64.Apart (s.gpr .r8) (stackArg s 3).toNat (s.gpr .rdx) (stackArg s 5).toNat
  a3 : VG.Proof.Rsa.X86_64.Apart (s.gpr .rdi) (stackArg s 3).toNat (s.gpr .rdx) (stackArg s 5).toNat
  hret : ∀ b < 8, (stackArg s 9).toNat * 8 ≤ VG.Proof.Bignum.X86_64.ofs (stackArg s 8) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    (∀ j < (stackArg s 3).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .r8 + BitVec.ofNat 64 j) ∧
    (∀ j < (stackArg s 3).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdi + BitVec.ofNat 64 j) ∧
    (∀ j < (stackArg s 5).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdx + BitVec.ofNat 64 j)

theorem cvCtx_of {s : State} (h : cvContract.pre s) : VG.Proof.Rsa.X86_64.CvCtx s := by
  simp only [VG.Proof.Rsa.X86_64.cvContract] at h
  obtain ⟨hsp, hrd, hwr, d12, d13, d1n, d1p, d1q, d1d, d1s, d1a, d23, d2n, d2p, d2q, d2d, d2s, d2a,
    d3n, d3p, d3q, d3d, d3s, d3a, dns, dps, dqs, dds, dsa, dR1, dR2, dR3, dRn, dRp, dRq, dRd, dRs, dRa,
    w1, w2, w3, wN, wP, wQ, wD, wS, hk, hpl1, hpl2, hql1, hql2, hsi, hr9, hcx, hdl1, hdl2, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : VG.Proof.Bignum.X86_64.Scr s (stackArg s 8) ((stackArg s 9).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 80⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  rw [hsi] at d12 d13 d1n d1p d1q d1d d1s d1a dR1 w1
  rw [hcx] at d12 d23 d2n d2p d2q d2d d2s d2a dR2 w2
  rw [hr9] at d13 d23 d3n d3p d3q d3d d3s d3a dR3 w3
  refine ⟨⟨hk1, hk2, hpl1, hpl2, hql1, hql2, hdl1, hdl2, VG.Proof.Bignum.X86_64.bytesAt_length _ _ _, VG.Proof.Bignum.X86_64.bytesAt_length _ _ _,
      VG.Proof.Bignum.X86_64.bytesAt_length _ _ _, VG.Proof.Bignum.X86_64.bytesAt_length _ _ _, by simp only [VG.Proof.Rsa.X86_64.cvIn]; omega⟩, hsi, hcx, hs,
    fun j hj => ⟨_, hargs, by rw [VG.Proof.Rsa.X86_64.stkAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 80) (by omega) (by omega))
      rw [← VG.Proof.Rsa.X86_64.stkAddr_add s j b] at this; omega)),
    src_of_region (by rw [hrd]; simp) (by omega) dns,
    src_of_region (by rw [hrd]; simp) (by omega) dps,
    src_of_region (by rw [hrd]; simp) (by omega) dqs,
    src_of_region (by rw [hrd]; simp) (by omega) dds,
    ⟨fun j hj => ⟨_, by rw [hwr, hsi, hcx, hr9]; simp, contains_byte _ hj (by omega)⟩,
      fun j hj => out_scr d3s (contains_byte _ hj (by omega))⟩,
    ⟨fun j hj => ⟨_, by rw [hwr, hsi, hcx, hr9]; simp, contains_byte _ hj (by omega)⟩,
      fun j hj => out_scr d1s (contains_byte _ hj (by omega))⟩,
    ⟨fun j hj => ⟨_, by rw [hwr, hsi, hcx, hr9]; simp, contains_byte _ hj (by omega)⟩,
      fun j hj => out_scr d2s (contains_byte _ hj (by omega))⟩,
    VG.Proof.Rsa.X86_64.apart_of (fun a h₁ h₂ => d13 a h₂ h₁) (by omega) (by omega), VG.Proof.Rsa.X86_64.apart_of (fun a h₁ h₂ => d23 a h₂ h₁) (by omega) (by omega),
    VG.Proof.Rsa.X86_64.apart_of d12 (by omega) (by omega), fun b hb => ?_⟩
  have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega)
  exact ⟨out_scr dRs hc, fun j hj he => dR3 _ hc (by rw [he]; exact contains_byte _ hj (by omega)),
    fun j hj he => dR1 _ hc (by rw [he]; exact contains_byte _ hj (by omega)),
    fun j hj he => dR2 _ hc (by rw [he]; exact contains_byte _ hj (by omega))⟩

/-- After `entry` and the reloads of `n` and `k`, from `s`. -/
structure CvHeadPost (s t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t (stackArg s 8) ((stackArg s 9).toNat * 8)
  rdi : t.gpr .rdi = stackArg s 8
  rdx : t.gpr .rdx = stackArg s 0
  rcx : t.gpr .rcx = BitVec.ofNat 64 (stackArg s 1).toNat
  args : VG.Proof.Rsa.X86_64.CvArgs t.mem (VG.Proof.Rsa.X86_64.cvIn s).B (VG.Proof.Rsa.X86_64.cvIn s).k (VG.Proof.Rsa.X86_64.cvIn s).pl (VG.Proof.Rsa.X86_64.cvIn s).ql (VG.Proof.Rsa.X86_64.cvIn s).dl (VG.Proof.Rsa.X86_64.cvIn s).pDp (VG.Proof.Rsa.X86_64.cvIn s).pDq
    (VG.Proof.Rsa.X86_64.cvIn s).pQi (VG.Proof.Rsa.X86_64.cvIn s).pN (VG.Proof.Rsa.X86_64.cvIn s).pP (VG.Proof.Rsa.X86_64.cvIn s).pQ (VG.Proof.Rsa.X86_64.cvIn s).pD (VG.Proof.Rsa.X86_64.cvIn s).sv
  inScr : InScr (stackArg s 8) ((stackArg s 9).toNat * 8) s.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep [.r11, .rax, .rdi, .rdx, .rcx] s t

/-- `entry`, and `n` and `k` into `rdx` and `rcx`. -/
theorem cvHead_ok' {s : State} (c : VG.Proof.Rsa.X86_64.CvCtx s) :
    WP isa (.block (VG.Impl.Rsa.X86_64.Keys.CrtValues.entry ++ ([.mov .rdx (.mem (VG.Impl.Bignum.X86_64.hdr Impl.Bignum.X86_64.Public.sN)),
      .mov .rcx (.mem (VG.Impl.Bignum.X86_64.hdr Impl.Bignum.X86_64.Public.sK))] : List Instr))) s (VG.Proof.Rsa.X86_64.CvHeadPost s) := by
  have hn := c.hs.nowrap
  have hZ : 128 * (stackArg s 1).toNat ≤ (stackArg s 9).toNat * 8 := c.L.z
  have hk1 : 64 ≤ (stackArg s 1).toNat := c.L.k1
  have hw : ∀ i < 32, InRegions s.wr (VG.Proof.Bignum.X86_64.off (stackArg s 8) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rsa.X86_64.cvEntry_ok rfl hw c.ha c.hsep) fun t₀ ⟨hdi, hsv, hDp, hPl, hDq, hQl, hQi, hN, hK, hP, hQ, hD,
    hDl, ho₀, k₀⟩ => ?_
  have hs₀ := c.hs.congr k₀.2.2
  have eN : Impl.Bignum.X86_64.Public.sN = 17 := rfl
  have eK : Impl.Bignum.X86_64.Public.sK = 18 := rfl
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = stackArg s 0 ∧
      t.gpr .rcx = stackArg s 1 ∧ t.mem = t₀.mem) (by
    xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, hdrOff, hs₀.ld (d := 8 * Impl.Bignum.X86_64.Public.sN) (by omega),
      hs₀.ld (d := 8 * Impl.Bignum.X86_64.Public.sK) (by omega), hN, hK]) rfl)
    fun t₁ ⟨⟨hdx, hcx, hm⟩, k₁⟩ => ?_
  rw [← hm] at hsv hDp hPl hDq hQl hQi hN hK hP hQ hD hDl
  refine ⟨hs₀.congr k₁.2.2, (k₁.gpr (by decide)).trans hdi, hdx, by rw [hcx, VG.Proof.Bignum.X86_64.ofNat_toNat64],
    ⟨hDp, hDq, hQi, hN,
      show Bignum.X86_64.word _ (stackArg s 8) _ = BitVec.ofNat 64 (stackArg s 1).toNat by rw [hK, VG.Proof.Bignum.X86_64.ofNat_toNat64], hP,
      show Bignum.X86_64.word _ (stackArg s 8) _ = BitVec.ofNat 64 (stackArg s 3).toNat by
        rw [hPl, ← c.rsi, VG.Proof.Bignum.X86_64.ofNat_toNat64], hQ,
      show Bignum.X86_64.word _ (stackArg s 8) _ = BitVec.ofNat 64 (stackArg s 5).toNat by
        rw [hQl, ← c.rcx, VG.Proof.Bignum.X86_64.ofNat_toNat64], hD,
      show Bignum.X86_64.word _ (stackArg s 8) _ = BitVec.ofNat 64 (stackArg s 7).toNat by rw [hDl, VG.Proof.Bignum.X86_64.ofNat_toNat64],
      hsv⟩,
    by rw [hm]; exact InScr.of_outside ho₀ (by omega), (k₀.trans k₁).mono (by decide)⟩

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem cvPre_of {s t₁ t : State} (c : VG.Proof.Rsa.X86_64.CvCtx s) (h : VG.Proof.Rsa.X86_64.CvHeadPost s t₁) (hm : t.mem = t₁.mem)
    (k : VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .rsi] t₁ t) : VG.Proof.Rsa.X86_64.CvPre (VG.Proof.Rsa.X86_64.cvIn s) t := by
  have kk := h.keep.trans k
  have hi : InScr (stackArg s 8) ((stackArg s 9).toNat * 8) s.mem t.mem := by rw [hm]; exact h.inScr
  exact
    { scr := h.scr.congr k.2.2, rdi := (k.gpr (by decide)).trans h.rdi, args := by rw [hm]; exact h.args,
      n := c.n.congrK hi kk, p := c.p.congrK hi kk, q := c.q.congrK hi kk, d := c.d.congrK hi kk, L := c.L,
      oQi := ⟨fun i hi => by rw [kk.2.2]; exact c.oQi.wr i hi, c.oQi.sep⟩,
      oDp := ⟨fun i hi => by rw [kk.2.2]; exact c.oDp.wr i hi, c.oDp.sep⟩,
      oDq := ⟨fun i hi => by rw [kk.2.2]; exact c.oDq.wr i hi, c.oDq.sep⟩,
      a1 := c.a1, a2 := c.a2, a3 := c.a3, wr := kk.2.2, rsp := kk.gpr (by decide) }

/-- The saved registers and the return address, from what `fail` or `main`
leaves. -/
theorem cvGpr_of {s t₂ t : State} (c : VG.Proof.Rsa.X86_64.CvCtx s) (hsv : ∀ i < 6, t.gpr (saved.getD i .rax) = (VG.Proof.Rsa.X86_64.cvIn s).sv i)
    (hsp : t.gpr .rsp = t₂.gpr .rsp) (hsp₂ : t₂.gpr .rsp = s.gpr .rsp)
    (hfr : ∀ x, (stackArg s 9).toNat * 8 ≤ VG.Proof.Bignum.X86_64.ofs (stackArg s 8) x →
      (∀ i < (stackArg s 3).toNat, x ≠ s.gpr .r8 + BitVec.ofNat 64 i) →
      (∀ i < (stackArg s 3).toNat, x ≠ s.gpr .rdi + BitVec.ofNat 64 i) →
      (∀ i < (stackArg s 5).toNat, x ≠ s.gpr .rdx + BitVec.ofNat 64 i) → t.mem x = s.mem x) :
    gprPreserved s t := by
  refine ⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv 0 (by decide)
    · exact hsv 1 (by decide)
    · exact hsp.trans hsp₂
    · exact hsv 2 (by decide)
    · exact hsv 3 (by decide)
    · exact hsv 4 (by decide)
    · exact hsv 5 (by decide)
  · obtain ⟨hZx, n1, n2, n3⟩ := c.hret b hb
    exact hfr _ hZx n1 n2 n3

/-- `vg_rsa_crt_values`, given that its code never loads MXCSR (which the
registration file evaluates). -/
theorem cvCode_correct (hmx : CrtValues.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : cvContract.pre s) :
    ∃ t s', Exec isa CrtValues.code s t s' ∧ abiPreserved s s' ∧ cvContract.post s s' := by
  have c := VG.Proof.Rsa.X86_64.cvCtx_of h
  clear h
  have hk1 := c.L.k1
  have hk2 := c.L.k2
  suffices hwp : WP isa CrtValues.code s fun s' => gprPreserved s s' ∧ cvContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold CrtValues.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rsa.X86_64.cvHead_ok' c) fun t₁ h₁ => ?_
  have hnb₁ := c.n.congrK h₁.inScr h₁.keep
  have hnl : (VG.Proof.Rsa.X86_64.cvIn s).nb.length = (stackArg s 1).toNat := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _
  refine WP.mono (invalid_ok h₁.rdx h₁.rcx hk1 hk2 hnl (fun i hi => hnb₁.rd i (by rw [hnl]; exact hi))
    (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
  have hpre := VG.Proof.Rsa.X86_64.cvPre_of c h₁ hm₂ k₂
  have hsp₂ : t₂.gpr .rsp = s.gpr .rsp := hpre.rsp
  have hpl : (VG.Proof.Rsa.X86_64.cvIn s).pb.length = (stackArg s 3).toNat := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _
  have hql : (VG.Proof.Rsa.X86_64.cvIn s).qb.length = (stackArg s 5).toNat := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _
  refine WP.ite (!Spec.Rsa.modulusValid (VG.Proof.Rsa.X86_64.cvIn s).N (stackArg s 1).toNat) (by simp [VG.X86_64.eval, hz₂]) (fun hb => ?_)
    (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (VG.Proof.Rsa.X86_64.cvIn s).N (stackArg s 1).toNat = false := by simpa using hb
    have z : 128 * (stackArg s 1).toNat ≤ (stackArg s 9).toNat * 8 := c.L.z
    have pl2 : (stackArg s 3).toNat < (stackArg s 1).toNat := c.L.pl2
    have ql2 : (stackArg s 5).toNat < (stackArg s 1).toNat := c.L.ql2
    have k2 : (stackArg s 1).toNat ≤ 1024 := c.L.k2
    have k1 : 64 ≤ (stackArg s 1).toNat := c.L.k1
    exact WP.mono (VG.Proof.Rsa.X86_64.cvFail_ok hpre.scr hpre.rdi (show 8 * 32 ≤ (stackArg s 9).toNat * 8 by omega) hpre.args c.L.pl1
      (show (stackArg s 3).toNat < 2 ^ 31 by omega) c.L.ql1 (show (stackArg s 5).toNat < 2 ^ 31 by omega)
      hpre.oQi hpre.oDp hpre.oDq hpre.a1 hpre.a2 hpre.a3)
      fun t ⟨z1, z2, z3, hax, hsv, hfr, hsp⟩ => ⟨VG.Proof.Rsa.X86_64.cvGpr_of c hsv hsp hsp₂ fun x hx n1 n2 n3 => by
        rw [hfr x n1 n2 n3, hm₂]; exact h₁.inScr x hx, by
        show Spec.Rsa.writtenAll _ _ _ _
        have hnone : Spec.Rsa.crtKey (VG.Proof.Rsa.X86_64.cvIn s).nb (VG.Proof.Rsa.X86_64.cvIn s).pb (VG.Proof.Rsa.X86_64.cvIn s).qb (VG.Proof.Rsa.X86_64.cvIn s).db = none := by
          simp only [Spec.Rsa.crtKey]
          rw [hnl, hv]; simp
        simp only [VG.Proof.Rsa.X86_64.cvIn] at hnone
        rw [hnone, hax]
        simp only [Option.map_none, Spec.Rsa.writtenAll, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        exact ⟨rfl, VG.Proof.Rsa.X86_64.bytesAt_zero z2, VG.Proof.Rsa.X86_64.bytesAt_zero z3, VG.Proof.Rsa.X86_64.bytesAt_zero z1⟩⟩
  · have hv : Spec.Rsa.modulusValid (VG.Proof.Rsa.X86_64.cvIn s).N (stackArg s 1).toNat = true := by simpa using hb
    exact WP.mono (VG.Proof.Rsa.X86_64.cvMain_ok hpre hv) fun t ⟨X, hX, b1, b2, b3, hax, hsv, hfr, hsp⟩ =>
      ⟨VG.Proof.Rsa.X86_64.cvGpr_of c hsv hsp hsp₂ fun x hx n1 n2 n3 => by
        rw [hfr x hx n1 n2 n3, hm₂]; exact h₁.inScr x hx, by
        have := VG.Proof.Rsa.X86_64.cvWritten_of (m := t.mem) (dp := s.gpr .rdi) (dq := s.gpr .rdx) (qi := s.gpr .r8)
          (by rw [hnl]; exact hv) rfl hX (by rw [hpl]; exact b1) (by rw [hpl]; exact b2) (by rw [hql]; exact b3) hax
        rw [hpl, hql] at this
        exact this⟩

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.CvCT`. -/
section

/-!
# `vg_rsa_crt_values` on x86-64: constant time, the pieces of `main`

`GA p`: what holds between the pieces of `main`'s arithmetic, for the
public data `p` (the working space, the pointers and lengths, `n`); each
piece leaks the same in two runs from `GA p` and leaves `GA p` (`zeroA_ct`,
…), its registers pinned after `ws` (`ws_ct`) or, for the loads, after the
block that loads the pointer and the length (`loadTail_ct`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)
open VG.Impl.Rsa.X86_64 (copyWords)

/-- The public data of `vg_rsa_crt_values`: the working space, the
pointers and lengths, `n`, the writable regions and the stack pointer. -/
structure CvP where
  B : Addr
  Z : Nat
  k : Nat
  pl : Nat
  ql : Nat
  dl : Nat
  pDp : Addr
  pDq : Addr
  pQi : Addr
  pN : Addr
  pP : Addr
  pQ : Addr
  pD : Addr
  nb : List Byte
  W : List Region
  sp : Addr
  deriving Inhabited

/-- The public part of the inputs. -/
def CvIn.pub (I : VG.Proof.Rsa.X86_64.CvIn) : VG.Proof.Rsa.X86_64.CvP :=
  ⟨I.B, I.Z, I.k, I.pl, I.ql, I.dl, I.pDp, I.pDq, I.pQi, I.pN, I.pP, I.pQ, I.pD, I.nb, I.W, I.sp⟩

/-- The outputs: writable, outside the working space, and apart. -/
structure CvOuts (I : VG.Proof.Rsa.X86_64.CvIn) : Prop where
  qi : ∀ i < I.pl, InRegions I.W (I.pQi + BitVec.ofNat 64 i) 1
  dp : ∀ i < I.pl, InRegions I.W (I.pDp + BitVec.ofNat 64 i) 1
  dq : ∀ i < I.ql, InRegions I.W (I.pDq + BitVec.ofNat 64 i) 1
  sqi : ∀ i < I.pl, I.Z ≤ VG.Proof.Bignum.X86_64.ofs I.B (I.pQi + BitVec.ofNat 64 i)
  sdp : ∀ i < I.pl, I.Z ≤ VG.Proof.Bignum.X86_64.ofs I.B (I.pDp + BitVec.ofNat 64 i)
  sdq : ∀ i < I.ql, I.Z ≤ VG.Proof.Bignum.X86_64.ofs I.B (I.pDq + BitVec.ofNat 64 i)
  a1 : VG.Proof.Rsa.X86_64.Apart I.pQi I.pl I.pDp I.pl
  a2 : VG.Proof.Rsa.X86_64.Apart I.pQi I.pl I.pDq I.ql
  a3 : VG.Proof.Rsa.X86_64.Apart I.pDp I.pl I.pDq I.ql

/-- Between the pieces of `main`'s arithmetic. -/
def GA (p : VG.Proof.Rsa.X86_64.CvP) (s : State) : Prop :=
  ∃ (I : VG.Proof.Rsa.X86_64.CvIn) (m₀ : Mem) (c : Bool), I.pub = p ∧ VG.Proof.Rsa.X86_64.CvS I m₀ s ∧ VG.Proof.Rsa.X86_64.CvLens I ∧ VG.Proof.Rsa.X86_64.CvOuts I ∧ VG.Proof.Rsa.X86_64.mword s.mem I.B = VG.Proof.Bignum.X86_64.mask c

theorem GA.ws {p : VG.Proof.Rsa.X86_64.CvP} {s : State} (h : VG.Proof.Rsa.X86_64.GA p s) : VG.Proof.Rsa.X86_64.Ws s p.B p.Z (VG.Proof.Rsa.X86_64.wk p.k) := by
  obtain ⟨I, m₀, c, rfl, h, -⟩ := h
  exact h.ws

/-- The mask, after a piece that changes only an array. -/
theorem mword_out {m m' : Mem} {B : Addr} {w j L : Nat} (o : VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w j) L m m') :
    VG.Proof.Rsa.X86_64.mword m' B = VG.Proof.Rsa.X86_64.mword m B :=
  o.word (Or.inl (by have := hdr_lt_slot w j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega))
    (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega)

/-- `GA` after a piece that changes only array `j`'s first `n` bytes. -/
theorem GA.arr {p : VG.Proof.Rsa.X86_64.CvP} {s t : State} (h : VG.Proof.Rsa.X86_64.GA p s) {j n : Nat} (hj : j < 16) (hn : n ≤ 8 * (VG.Proof.Rsa.X86_64.wk p.k + 2))
    (o : VG.Proof.Bignum.X86_64.Outside p.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk p.k) j) n s.mem t.mem) {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : VG.Proof.Rsa.X86_64.GA p t := by
  obtain ⟨I, m₀, c, rfl, h, L, O, hm⟩ := h
  exact ⟨I, m₀, c, rfl, h.arr hj hn o k hr, L, O, (VG.Proof.Rsa.X86_64.mword_out o).trans hm⟩

/-- `GA` after a piece that changes only the arrays of `rs`, and `sMo`. -/
theorem GA.frm {p : VG.Proof.Rsa.X86_64.CvP} {s t : State} (h : VG.Proof.Rsa.X86_64.GA p s) {rs : List (Nat × Nat)}
    (hf : Frm p.B rs s.mem t.mem) (hm : ∀ r ∈ rs, (∃ j < 16, r = (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk p.k) j, 8 * (VG.Proof.Rsa.X86_64.wk p.k + 2)) ∨
      r = (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk p.k) j, 8 * VG.Proof.Rsa.X86_64.wk p.k)) ∨ r = (8 * sMo, 8))
    {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : VG.Proof.Rsa.X86_64.GA p t := by
  obtain ⟨I, m₀, c, rfl, h, L, O, hmw⟩ := h
  dsimp only [CvIn.pub] at hf hm ⊢
  have hZ := h.ws.hZ
  have hn := h.ws.scr.nowrap
  refine ⟨I, m₀, c, rfl, h.step hf (fun r hr => ?_) (fun r hr => ?_) k hr, L, O, ?_⟩
  · rcases hm r hr with ⟨j, hj, rfl | rfl⟩ | rfl
    · exact Mut.ofSlot _ _ _
    · exact Mut.ofSlot _ _ _
    · exact Or.inr (Or.inr rfl)
  · rcases hm r hr with ⟨j, hj, rfl | rfl⟩ | rfl
    · have := h.ws.sl hj; dsimp only; omega
    · have := h.ws.sl hj; dsimp only; omega
    · have := h.ws.h256; simp only [sMo, sFn]; omega
  · refine (hf.word_eq (fun r hr => ?_) (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega)).trans hmw
    rcases hm r hr with ⟨j, hj, rfl | rfl⟩ | rfl
    · have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); dsimp only; omega
    · have := hdr_lt_slot (VG.Proof.Rsa.X86_64.wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); dsimp only; omega
    · simp only [Impl.Bignum.X86_64.Public.sMask, sMo, sFn]; omega

/-! ## The pieces -/

theorem zeroA_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc).isSome = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.GA) (zeroA j) (Two VG.Proof.Rsa.X86_64.GA) :=
  VG.Proof.Rsa.X86_64.ws_ct CvP.B CvP.Z (fun p => VG.Proof.Rsa.X86_64.wk p.k) (fun _ _ h => h.ws) ht fun _ _ h =>
    WP.mono (VG.Proof.Rsa.X86_64.zeroA_ok h.ws hj) fun _ ⟨_, o, k⟩ => h.arr hj (Nat.le_refl _) o k (by decide)

theorem copyA_ct {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rsi ++ base o .rbx)) copyWords)
      hc).isSome = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.GA) (copyA o a) (Two VG.Proof.Rsa.X86_64.GA) := by
  have e : copyA o a = .seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ (base a .rsi ++ base o .rbx))) copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  exact VG.Proof.Rsa.X86_64.ws_ct CvP.B CvP.Z (fun p => VG.Proof.Rsa.X86_64.wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    exact WP.mono (VG.Proof.Rsa.X86_64.copyA_ok h.ws ho ha hoa) fun _ ⟨_, o', k⟩ => h.arr ho (by omega) o' k (by decide)

theorem divmod_ct {iQ iR iD iT : Nat} (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16)
    (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT) (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base iR .r8 ++ (([.mov .r11 (.reg .r12)] : List Instr) ++
      (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++ ([.mov32 .r13 (.imm 0)] : List Instr)))))
      (.seq zeroAccLoop (.loop (VG.Impl.Rsa.X86_64.Keys.divStep iQ iR iD iT) .ne))) hc).isSome = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.GA) (divmod iQ iR iD iT) (Two VG.Proof.Rsa.X86_64.GA) := by
  have e : divmod iQ iR iD iT = .seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ (base iR .r8 ++ ([.mov .r11 (.reg .r12)] ++
      (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++ [.mov32 .r13 (.imm 0)])))))
      (.seq zeroAccLoop (.loop (VG.Impl.Rsa.X86_64.Keys.divStep iQ iR iD iT) .ne)) := by
    simp only [divmod, divInit, seqs, List.append_assoc]
  rw [e]
  exact VG.Proof.Rsa.X86_64.ws_ct CvP.B CvP.Z (fun p => VG.Proof.Rsa.X86_64.wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    have hw := h.ws
    exact WP.mono (VG.Proof.Rsa.X86_64.divmod_ok hw.scr hw.rdi hw.hw hw.hS (by have := hw.w1; omega) hw.w2 hw.hZ hQ hR hD hT dQR dQD
      dQT dRD dRT dDT) fun _ ⟨_, f, k, _⟩ => h.frm f (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact .inl ⟨iQ, hQ, .inl rfl⟩
        · exact .inl ⟨iR, hR, .inl rfl⟩
        · exact .inl ⟨iT, hT, .inl rfl⟩) k (by decide)

/-- `GA` after a piece that changes no memory. -/
theorem GA.same {p : VG.Proof.Rsa.X86_64.CvP} {s t : State} (h : VG.Proof.Rsa.X86_64.GA p s) (hm : t.mem = s.mem) {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : VG.Proof.Rsa.X86_64.GA p t := by
  obtain ⟨I, m₀, c, rfl, h, L, O, hmw⟩ := h
  exact ⟨I, m₀, c, rfl, h.step (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (by simp) k hr, L, O,
    by rw [hm]; exact hmw⟩

/-- `GA` after a store to the mask. -/
theorem GA.mask {p : VG.Proof.Rsa.X86_64.CvP} {s t : State} (h : VG.Proof.Rsa.X86_64.GA p s) {v : BitVec 64} {c : Bool} (hv : v = VG.Proof.Bignum.X86_64.mask c)
    (hm : t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off p.B (8 * Impl.Bignum.X86_64.Public.sMask)) v) {regs : List Reg}
    (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : VG.Proof.Rsa.X86_64.GA p t := by
  obtain ⟨I, m₀, c', rfl, h, L, O, -⟩ := h
  obtain ⟨ht, hmt, -⟩ := h.mask hm k hr
  exact ⟨I, m₀, c, rfl, ht, L, O, hmt.trans hv⟩

theorem pins_GA : Pins VG.Proof.Rsa.X86_64.GA [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]

theorem eqA_ct {a b : Nat} (ha : a < 16) (hb : b < 16) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rbx ++ (base b .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr)))) (wordLoop 0 xorBody)) hc).isSome = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.GA) (seqs (eqA a b)) (Two VG.Proof.Rsa.X86_64.GA) := by
  have e : seqs (eqA a b) = .seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ (base a .rbx ++ (base b .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr))))) (wordLoop 0 xorBody) := by
    simp only [eqA, seqs, List.append_assoc]
  rw [e]
  exact VG.Proof.Rsa.X86_64.ws_ct CvP.B CvP.Z (fun p => VG.Proof.Rsa.X86_64.wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    exact WP.mono (VG.Proof.Rsa.X86_64.eqA_ok h.ws ha hb) fun _ ⟨_, hm, k⟩ => h.same hm k (by decide)

theorem andZero_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.GA) (.block andZero) (Two VG.Proof.Rsa.X86_64.GA) :=
  two_piece [.rdi] VG.Proof.Rsa.X86_64.pins_GA (by taint_decide) fun _ s h => by
    obtain ⟨I, m₀, c, rfl, h', L, O, hmw⟩ := id h
    exact WP.mono (VG.Proof.Rsa.X86_64.andZero_ok (z := s.gpr .rbp = 0) h'.ws hmw Iff.rfl) fun _ ⟨hm, k⟩ =>
      h.mask rfl hm k (by decide)

theorem andOdd_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base j .rbx ++ ([.mov .rax (.mem (at0 .rbx)),
      .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
      .alu .and .rdx (.mem (VG.Impl.Bignum.X86_64.hdr Impl.Bignum.X86_64.Public.sMask)),
      .store (VG.Impl.Bignum.X86_64.hdr Impl.Bignum.X86_64.Public.sMask) .rdx] : List Instr))) hc).isSome = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.GA) (.block (andOdd j)) (Two VG.Proof.Rsa.X86_64.GA) := by
  have e : andOdd j = VG.Impl.Rsa.X86_64.Keys.ws ++ (base j .rbx ++ ([.mov .rax (.mem (at0 .rbx)),
      .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
      .alu .and .rdx (.mem (VG.Impl.Bignum.X86_64.hdr Impl.Bignum.X86_64.Public.sMask)),
      .store (VG.Impl.Bignum.X86_64.hdr Impl.Bignum.X86_64.Public.sMask) .rdx] : List Instr)) := by
    simp only [andOdd, List.append_assoc]
  rw [e]
  exact VG.Proof.Rsa.X86_64.ws_block_ct CvP.B CvP.Z (fun p => VG.Proof.Rsa.X86_64.wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    obtain ⟨I, m₀, c, rfl, h', L, O, hmw⟩ := id h
    exact WP.mono (VG.Proof.Rsa.X86_64.andOdd_ok h'.ws hj hmw) fun _ ⟨hm, k⟩ => h.mask rfl hm k (by decide)

/-- `GA` after a store of a word to array `j`. -/
theorem GA.word {p : VG.Proof.Rsa.X86_64.CvP} {s t : State} (h : VG.Proof.Rsa.X86_64.GA p s) {j : Nat} (hj : j < 16) {v : BitVec 64}
    (hm : t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk p.k) j)) v) {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : VG.Proof.Rsa.X86_64.GA p t := by
  have hw := h.ws
  have o := VG.Proof.Bignum.X86_64.writeW_outside s.mem p.B v (d := VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk p.k) j) (by have := hw.sl hj; have := hw.scr.nowrap; omega)
  rw [← hm] at o
  exact h.arr hj (by omega) o k hr

theorem setOneA_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base j .rbx ++ ([.mov32 .rax (.imm 1),
      .store (at0 .rbx) .rax] : List Instr))) hc).isSome = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.GA) (.block (setOneA j)) (Two VG.Proof.Rsa.X86_64.GA) := by
  have e : setOneA j = VG.Impl.Rsa.X86_64.Keys.ws ++ (base j .rbx ++ ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr)) := by
    simp only [setOneA, List.append_assoc]
  rw [e]
  exact VG.Proof.Rsa.X86_64.ws_block_ct CvP.B CvP.Z (fun p => VG.Proof.Rsa.X86_64.wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    exact WP.mono (VG.Proof.Rsa.X86_64.setOneA_ok h.ws hj) fun _ ⟨hm, k⟩ => h.word hj hm k (by decide)

theorem decA_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base j .rbx ++ ([.mov .rax (.mem (at0 .rbx)),
      .alu .sub .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr))) hc).isSome = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.GA) (.block (decA j)) (Two VG.Proof.Rsa.X86_64.GA) := by
  have e : decA j = VG.Impl.Rsa.X86_64.Keys.ws ++ (base j .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .sub .rax (.imm 1),
      .store (at0 .rbx) .rax] : List Instr)) := by
    simp only [decA, List.append_assoc]
  rw [e]
  exact VG.Proof.Rsa.X86_64.ws_block_ct CvP.B CvP.Z (fun p => VG.Proof.Rsa.X86_64.wk p.k) (fun _ _ h => h.ws) ht fun _ _ h => by
    rw [← e]
    exact WP.mono (VG.Proof.Rsa.X86_64.decA_ok h.ws hj) fun _ ⟨hm, k⟩ => h.word hj hm k (by decide)

/-- `GA` with `inverse`'s start. -/
def GI (p : VG.Proof.Rsa.X86_64.CvP) (s : State) : Prop :=
  VG.Proof.Rsa.X86_64.GA p s ∧ Bignum.X86_64.word s.mem p.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk p.k) aU + 8 * VG.Proof.Rsa.X86_64.wk p.k) = 0 ∧
    wv s.mem p.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk p.k) aV) (VG.Proof.Rsa.X86_64.wk p.k) = wv s.mem p.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk p.k) aP) (VG.Proof.Rsa.X86_64.wk p.k) ∧
    wv s.mem p.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk p.k) aX₁) (VG.Proof.Rsa.X86_64.wk p.k) = 1 ∧ wv s.mem p.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk p.k) aX₂) (VG.Proof.Rsa.X86_64.wk p.k) = 0

theorem inverse_ct {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (([.mov .r11 (.reg .r12)] : List Instr) ++
      (List.replicate 7 (.alu .add .r11 (.reg .r11)) ++ ([.mov32 .r13 (.imm 0)] : List Instr))))
      (.loop (VG.Impl.Rsa.X86_64.Keys.invStep aU aV aX₁ aX₂ aP aT) .ne)) hc).isSome = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.GI) (inverse aU aV aX₁ aX₂ aP aT) (Two VG.Proof.Rsa.X86_64.GA) := by
  have e : inverse aU aV aX₁ aX₂ aP aT = .seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ ([.mov .r11 (.reg .r12)] ++
      (List.replicate 7 (.alu .add .r11 (.reg .r11)) ++ [.mov32 .r13 (.imm 0)]))))
      (.loop (VG.Impl.Rsa.X86_64.Keys.invStep aU aV aX₁ aX₂ aP aT) .ne) := by
    simp only [inverse, invInit, List.append_assoc]
  rw [e]
  exact VG.Proof.Rsa.X86_64.ws_ct CvP.B CvP.Z (fun p => VG.Proof.Rsa.X86_64.wk p.k) (fun _ _ h => h.1.ws) ht fun _ _ ⟨h, u0, vm, x1, x2⟩ => by
    rw [← e]
    have hw := h.ws
    exact WP.mono (VG.Proof.Rsa.X86_64.inverse_ok hw.scr hw.rdi hw.hw hw.hS (by have := hw.w1; omega) hw.w2 hw.hZ
      (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aP) (iT := aT) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      u0 vm x1 x2) fun _ ⟨_, f, k, _⟩ => h.frm f (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact .inl ⟨aU, by decide, .inr rfl⟩
        · exact .inl ⟨aV, by decide, .inr rfl⟩
        · exact .inl ⟨aX₁, by decide, .inr rfl⟩
        · exact .inl ⟨aX₂, by decide, .inr rfl⟩
        · exact .inl ⟨aT, by decide, .inl rfl⟩
        · exact .inr rfl) k (by decide)

/-! ## The loads -/

/-- The block before `loadBE`: the base of `[j]`, the pointer and the length. -/
theorem loadBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {j sPtr sLen len : Nat} {ptr : Addr}
    (hP : sPtr < 32) (hL : sLen < 32) (hp : Bignum.X86_64.word s.mem B (8 * sPtr) = ptr)
    (hl : Bignum.X86_64.word s.mem B (8 * sLen) = BitVec.ofNat 64 len) :
    WP isa (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base j .rbx ++ ([.mov .rsi (.mem (VG.Impl.Bignum.X86_64.hdr sPtr)), .mov .rcx (.mem (VG.Impl.Bignum.X86_64.hdr sLen))] : List Instr)))
      s fun t => t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j) ∧ t.gpr .rsi = ptr ∧ t.gpr .rcx = BitVec.ofNat 64 len ∧
        t.gpr .rdi = B ∧ t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .rbx, .rsi, .rcx] s t := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨_, h9, m₂, k₂⟩ =>
    WP.mono (VG.Proof.Rsa.X86_64.base_ok j (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h.rdi) h9) fun s₃ ⟨hbx, m₃, k₃⟩ =>
      WP.mono (WP.keep [.rsi, .rcx] (Q := fun t => t.gpr .rsi = ptr ∧ t.gpr .rcx = BitVec.ofNat 64 len ∧
        t.mem = s₃.mem) (by
          have hdi₃ : s₃.gpr .rdi = B := ((k₂.trans k₃).gpr (by decide)).trans h.rdi
          have hs₃ := h.scr.congr (k₂.trans k₃).2.2
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi₃, hdrOff, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL, hp, hl]) rfl)
      fun t ⟨⟨hsi, hcx, m₄⟩, k₄⟩ => ⟨(k₄.gpr (by decide)).trans hbx, hsi, hcx,
        ((k₂.trans k₃).trans k₄ |>.gpr (by decide)).trans h.rdi, by rw [m₄, m₃, m₂],
        ((k₂.trans k₃).trans k₄).mono (by simp)⟩))

/-- The registers `loadBE` and `storeBE` need pinned. -/
def ioVal (B base ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .rdi => B
  | .rbx => base
  | .rsi => ptr
  | .rcx => BitVec.ofNat 64 len
  | _ => 0

/-- `loadA`'s block and `loadBE`, from a `GA` with the pointer and the
length in the header slots `sPtr` and `sLen`. -/
theorem loadTail_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : VG.Proof.Rsa.X86_64.CvP → Addr)
    (len : VG.Proof.Rsa.X86_64.CvP → Nat)
    (hA : ∀ p s, VG.Proof.Rsa.X86_64.GA p s → Bignum.X86_64.word s.mem p.B (8 * sPtr) = ptr p ∧
      Bignum.X86_64.word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∃ bs, Src s p.B p.Z (ptr p) bs ∧ bs.length = len p) ∧ 1 ≤ len p ∧ len p ≤ 8 * VG.Proof.Rsa.X86_64.wk p.k)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base j .rbx ++ ([.mov .rsi (.mem (VG.Impl.Bignum.X86_64.hdr sPtr)),
      .mov .rcx (.mem (VG.Impl.Bignum.X86_64.hdr sLen))] : List Instr))) hc).isSome = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.GA) (.seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base j .rbx ++ ([.mov .rsi (.mem (VG.Impl.Bignum.X86_64.hdr sPtr)),
      .mov .rcx (.mem (VG.Impl.Bignum.X86_64.hdr sLen))] : List Instr))) loadBE) (Two VG.Proof.Rsa.X86_64.GA) :=
  VG.Proof.Rsa.X86_64.pin_ct [.rdi] [.rdi, .rbx, .rsi, .rcx] (fun p => VG.Proof.Rsa.X86_64.ioVal p.B (VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk p.k) j)) (ptr p) (len p)) VG.Proof.Rsa.X86_64.pins_GA ht
    (fun p s h => by
      obtain ⟨hp, hl, -⟩ := hA p s h
      exact WP.mono (VG.Proof.Rsa.X86_64.loadBlk_ok h.ws hP hL hp hl) fun t ⟨hbx, hsi, hcx, hdi, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact hbx
        · exact hsi
        · exact hcx)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hl, ⟨bs, hsrc, hbl⟩, hl1, hlw⟩ := hA p s h
      have hw := h.ws
      have hn := hw.scr.nowrap
      have sj := hw.sl hj
      have hw2 := hw.w2
      refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.loadBlk_ok hw hP hL hp hl) fun t ⟨hbx, hsi, hcx, _, hm, k⟩ => ?_)
      have ht := h.same hm k (by decide)
      have hsrc' := hsrc.congrK (fun x _ => by rw [hm]) k
      exact WP.mono (loadBE_ok (w := (len p + 7) / 8) ht.ws.scr hsi hcx hbx hbl hl1 (by omega) rfl (by omega)
        (fun i hi => hsrc'.rd i (by omega)) (fun i hi => hsrc'.val i (by omega))
        (fun i hi => Or.inr (by have := hsrc'.out i (by omega); omega))) fun t' ⟨_, o, k'⟩ =>
          ht.arr hj (by omega) o k' (by decide)

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain`. -/
section

/-!
# `vg_rsa_crt_values` on x86-64: constant time, `main`

The pieces of `CvCT.lean` in sequence (`loads_ct`, `pqCheck_ct`,
`invPart_ct`, `divs_ct`), the stores (`stores_ct`, from `GS`), and `main`
(`cvMain_ct`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)
open VG.Impl.Rsa.X86_64 (copyWords)

/-! ## Sequences -/

theorem ct_cons {α : Type} {Φ Ψ Ξ : α → State → Prop} {e : Prog isa} {l : List (Prog isa)} (hl : l ≠ [])
    (he : RelCT isa (Two Φ) e (Two Ψ)) (hr : RelCT isa (Two Ψ) (seqs l) (Two Ξ)) :
    RelCT isa (Two Φ) (seqs (e :: l)) (Two Ξ) := by
  obtain ⟨d, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  exact RelCT.seq he hr

theorem ct_one {α : Type} {Φ Ψ : α → State → Prop} {e : Prog isa} (he : RelCT isa (Two Φ) e (Two Ψ)) :
    RelCT isa (Two Φ) (seqs [e]) (Two Ψ) := he

theorem ct_app {α : Type} {Φ Ψ Ξ : α → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (hA : RelCT isa (Two Φ) (seqs a) (Two Ψ)) (hB : RelCT isa (Two Ψ) (seqs b) (Two Ξ)) :
    RelCT isa (Two Φ) (seqs (a ++ b)) (Two Ξ) :=
  RelCT.seqs_append ha hb (RelCT.seq hA hB)

/-! ## The loads -/

theorem loadA_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : VG.Proof.Rsa.X86_64.CvP → Addr)
    (len : VG.Proof.Rsa.X86_64.CvP → Nat)
    (hA : ∀ p s, VG.Proof.Rsa.X86_64.GA p s → Bignum.X86_64.word s.mem p.B (8 * sPtr) = ptr p ∧
      Bignum.X86_64.word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∃ bs, Src s p.B p.Z (ptr p) bs ∧ bs.length = len p) ∧ 1 ≤ len p ∧ len p ≤ 8 * VG.Proof.Rsa.X86_64.wk p.k)
    {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.rdi]) (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base j .rbx ++ ([.mov .rsi (.mem (VG.Impl.Bignum.X86_64.hdr sPtr)),
      .mov .rcx (.mem (VG.Impl.Bignum.X86_64.hdr sLen))] : List Instr))) hc₂).isSome = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.GA) (seqs (loadA j sPtr sLen)) (Two VG.Proof.Rsa.X86_64.GA) :=
  RelCT.seq (VG.Proof.Rsa.X86_64.zeroA_ct hj ht₁) (VG.Proof.Rsa.X86_64.loadTail_ct hj hP hL ptr len hA ht₂)

/-- The four loads. -/
theorem loads_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.GA) (seqs (loadA aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
    (loadA aP VG.Impl.Rsa.X86_64.Keys.CrtValues.sP sPl ++ (loadA aQ VG.Impl.Rsa.X86_64.Keys.CrtValues.sQ sQl ++ loadA VG.Impl.Rsa.X86_64.Keys.CrtValues.aD VG.Impl.Rsa.X86_64.Keys.CrtValues.sD VG.Impl.Rsa.X86_64.Keys.CrtValues.sDl)))) (Two VG.Proof.Rsa.X86_64.GA) := by
  have k8 : ∀ {k : Nat}, k ≤ 8 * VG.Proof.Rsa.X86_64.wk k := fun {k} => by unfold VG.Proof.Rsa.X86_64.wk; omega
  refine VG.Proof.Rsa.X86_64.ct_app (by simp [loadA]) (by simp [loadA]) (VG.Proof.Rsa.X86_64.loadA_ct (by decide) (by decide) (by decide) CvP.pN CvP.k
    (fun p s h => ?_) (by taint_decide) (by taint_decide)) (VG.Proof.Rsa.X86_64.ct_app (by simp [loadA]) (by simp [loadA])
    (VG.Proof.Rsa.X86_64.loadA_ct (by decide) (by decide) (by decide) CvP.pP CvP.pl (fun p s h => ?_) (by taint_decide) (by taint_decide))
    (VG.Proof.Rsa.X86_64.ct_app (by simp [loadA]) (by simp [loadA])
    (VG.Proof.Rsa.X86_64.loadA_ct (by decide) (by decide) (by decide) CvP.pQ CvP.ql (fun p s h => ?_) (by taint_decide) (by taint_decide))
    (VG.Proof.Rsa.X86_64.loadA_ct (by decide) (by decide) (by decide) CvP.pD CvP.dl (fun p s h => ?_) (by taint_decide)
      (by taint_decide))))
  all_goals
    obtain ⟨I, m₀, c, rfl, h, L, -⟩ := h
    dsimp only [CvIn.pub]
    have := L.k1
  · exact ⟨h.args.n, h.args.k, ⟨_, h.n, L.nl⟩, by omega, k8⟩
  · exact ⟨h.args.p, h.args.pl, ⟨_, h.p, L.pbl⟩, L.pl1, by have := L.pl2; have := @k8 I.k; omega⟩
  · exact ⟨h.args.q, h.args.ql, ⟨_, h.q, L.qbl⟩, L.ql1, by have := L.ql2; have := @k8 I.k; omega⟩
  · exact ⟨h.args.d, h.args.dl, ⟨_, h.d, L.dbl⟩, L.dl1, by have := L.dl2; have := @k8 I.k; omega⟩

/-! ## The arithmetic -/

theorem pqCheck_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.GA) (seqs pqCheck) (Two VG.Proof.Rsa.X86_64.GA) := by
  unfold pqCheck
  exact VG.Proof.Rsa.X86_64.ct_app (by simp) (by simp)
    (VG.Proof.Rsa.X86_64.ct_app (by simp) (by simp [eqA])
      (VG.Proof.Rsa.X86_64.ct_app (by simp) (by simp)
        (VG.Proof.Rsa.X86_64.ct_app (by simp) (by simp [eqA])
          (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.zeroA_ct (by decide) (by taint_decide))
            (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.copyA_ct (by decide) (by decide) (by decide) (by taint_decide))
              (VG.Proof.Rsa.X86_64.ct_one (VG.Proof.Rsa.X86_64.divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by taint_decide)))))
          (VG.Proof.Rsa.X86_64.eqA_ct (by decide) (by decide) (by taint_decide)))
        (VG.Proof.Rsa.X86_64.ct_cons (by simp) VG.Proof.Rsa.X86_64.andZero_ct (VG.Proof.Rsa.X86_64.ct_one (VG.Proof.Rsa.X86_64.zeroA_ct (by decide) (by taint_decide)))))
      (VG.Proof.Rsa.X86_64.eqA_ct (by decide) (by decide) (by taint_decide)))
    (VG.Proof.Rsa.X86_64.ct_cons (by simp) VG.Proof.Rsa.X86_64.andZero_ct (VG.Proof.Rsa.X86_64.ct_one (VG.Proof.Rsa.X86_64.andOdd_ct (by decide) (by taint_decide))))

theorem invSetup_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.GA) (seqs invSetup) (Two VG.Proof.Rsa.X86_64.GI) := by
  refine two_post ((?_ : RelCT isa (Two VG.Proof.Rsa.X86_64.GA) (seqs invSetup) (Two VG.Proof.Rsa.X86_64.GA)).mono (fun _ _ h => h) fun _ _ _ => trivial)
    fun p s h => ?_
  · unfold invSetup
    exact VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.zeroA_ct (by decide) (by taint_decide))
      (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.copyA_ct (by decide) (by decide) (by decide) (by taint_decide))
      (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.zeroA_ct (by decide) (by taint_decide))
      (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.copyA_ct (by decide) (by decide) (by decide) (by taint_decide))
      (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.zeroA_ct (by decide) (by taint_decide))
      (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.setOneA_ct (by decide) (by taint_decide))
      (VG.Proof.Rsa.X86_64.ct_one (VG.Proof.Rsa.X86_64.zeroA_ct (by decide) (by taint_decide))))))))
  · obtain ⟨I, m₀, c, rfl, h', L, O, hm⟩ := h
    exact WP.mono (VG.Proof.Rsa.X86_64.invSetup_ok h' L) fun t ⟨ht, mt, u0, _, vm, x1, x2, _⟩ =>
      ⟨⟨I, m₀, c, rfl, ht, L, O, mt.trans hm⟩, u0, vm, x1, x2⟩

theorem invPart_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.GA) (seqs invPart) (Two VG.Proof.Rsa.X86_64.GA) := by
  unfold invPart
  exact VG.Proof.Rsa.X86_64.ct_app (by simp [invSetup]) (by simp) VG.Proof.Rsa.X86_64.invSetup_ct
    (VG.Proof.Rsa.X86_64.ct_app (by simp) (by simp [eqA])
      (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.inverse_ct (by taint_decide))
        (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.zeroA_ct (by decide) (by taint_decide))
          (VG.Proof.Rsa.X86_64.ct_one (VG.Proof.Rsa.X86_64.setOneA_ct (by decide) (by taint_decide)))))
      (VG.Proof.Rsa.X86_64.ct_app (by simp [eqA]) (by simp) (VG.Proof.Rsa.X86_64.eqA_ct (by decide) (by decide) (by taint_decide)) (VG.Proof.Rsa.X86_64.ct_one VG.Proof.Rsa.X86_64.andZero_ct)))

theorem divisor_ct {j : Nat} (hj : j < 16) (hjC : aC ≠ j) {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rsi ++ base aC .rbx)) copyWords)
      hc₁).isSome = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.GA) (seqs (divisor j)) (Two VG.Proof.Rsa.X86_64.GA) := by
  unfold divisor
  exact VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.zeroA_ct (by decide) (by taint_decide))
    (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.copyA_ct (by decide) hj hjC ht)
    (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.decA_ct (by decide) (by taint_decide))
    (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.zeroA_ct (by decide) (by taint_decide))
    (VG.Proof.Rsa.X86_64.ct_one (VG.Proof.Rsa.X86_64.copyA_ct (by decide) (by decide) (by decide) (by taint_decide))))))

/-! ## The stores -/

/-- Between the stores: the working space, the header, the mask, and the
outputs, but not memory outside the working space. -/
def GS (p : VG.Proof.Rsa.X86_64.CvP) (s : State) : Prop :=
  ∃ (I : VG.Proof.Rsa.X86_64.CvIn) (c : Bool), I.pub = p ∧ VG.Proof.Rsa.X86_64.Ws s I.B I.Z (VG.Proof.Rsa.X86_64.wk I.k) ∧
    VG.Proof.Rsa.X86_64.CvArgs s.mem I.B I.k I.pl I.ql I.dl I.pDp I.pDq I.pQi I.pN I.pP I.pQ I.pD I.sv ∧ s.wr = I.W ∧ VG.Proof.Rsa.X86_64.CvLens I ∧
    VG.Proof.Rsa.X86_64.CvOuts I ∧ VG.Proof.Rsa.X86_64.mword s.mem I.B = VG.Proof.Bignum.X86_64.mask c

theorem GS.ws {p : VG.Proof.Rsa.X86_64.CvP} {s : State} (h : VG.Proof.Rsa.X86_64.GS p s) : VG.Proof.Rsa.X86_64.Ws s p.B p.Z (VG.Proof.Rsa.X86_64.wk p.k) := by
  obtain ⟨I, c, rfl, h, -⟩ := h
  exact h

theorem GA.gs {p : VG.Proof.Rsa.X86_64.CvP} {s : State} (h : VG.Proof.Rsa.X86_64.GA p s) : VG.Proof.Rsa.X86_64.GS p s := by
  obtain ⟨I, m₀, c, rfl, h, L, O, hm⟩ := h
  exact ⟨I, c, rfl, h.ws, h.args, h.wr, L, O, hm⟩

theorem pins_GS : Pins VG.Proof.Rsa.X86_64.GS [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]

/-- The block before `storeBE`: the base of `[j]`, the pointer, the length
and the mask. -/
theorem storeBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {j sPtr sLen len : Nat} {ptr : Addr}
    (hP : sPtr < 32) (hL : sLen < 32) (hp : Bignum.X86_64.word s.mem B (8 * sPtr) = ptr)
    (hl : Bignum.X86_64.word s.mem B (8 * sLen) = BitVec.ofNat 64 len) :
    WP isa (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base j .rbx ++ ([.mov .rsi (.mem (VG.Impl.Bignum.X86_64.hdr sPtr)), .mov .rcx (.mem (VG.Impl.Bignum.X86_64.hdr sLen)),
      .mov .r15 (.mem (VG.Impl.Bignum.X86_64.hdr Impl.Bignum.X86_64.Public.sMask))] : List Instr)))
      s fun t => t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j) ∧ t.gpr .rsi = ptr ∧ t.gpr .rcx = BitVec.ofNat 64 len ∧
        t.gpr .rdi = B := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨_, h9, m₂, k₂⟩ =>
    WP.mono (VG.Proof.Rsa.X86_64.base_ok j (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h.rdi) h9) fun s₃ ⟨hbx, m₃, k₃⟩ =>
      WP.mono (WP.keep [.rsi, .rcx, .r15] (Q := fun t => t.gpr .rsi = ptr ∧ t.gpr .rcx = BitVec.ofNat 64 len) (by
          have hdi₃ : s₃.gpr .rdi = B := ((k₂.trans k₃).gpr (by decide)).trans h.rdi
          have hs₃ := h.scr.congr (k₂.trans k₃).2.2
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi₃, hdrOff, m₃, m₂, hl₃ sPtr hP, hl₃ sLen hL,
            hl₃ Impl.Bignum.X86_64.Public.sMask (by decide), hp, hl]) rfl)
      fun _ ⟨⟨hsi, hcx⟩, k₄⟩ => ⟨(k₄.gpr (by decide)).trans hbx, hsi, hcx,
        ((k₂.trans k₃).trans k₄ |>.gpr (by decide)).trans h.rdi⟩))

theorem storeA_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : VG.Proof.Rsa.X86_64.CvP → Addr)
    (len : VG.Proof.Rsa.X86_64.CvP → Nat)
    (hA : ∀ p s, VG.Proof.Rsa.X86_64.GS p s → Bignum.X86_64.word s.mem p.B (8 * sPtr) = ptr p ∧
      Bignum.X86_64.word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∀ i < len p, InRegions p.W (ptr p + BitVec.ofNat 64 i) 1) ∧
      (∀ i < len p, p.Z ≤ VG.Proof.Bignum.X86_64.ofs p.B (ptr p + BitVec.ofNat 64 i)) ∧ 1 ≤ len p ∧ len p ≤ 8 * VG.Proof.Rsa.X86_64.wk p.k)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ base j .rbx ++ ([.mov .rsi (.mem (VG.Impl.Bignum.X86_64.hdr sPtr)),
      .mov .rcx (.mem (VG.Impl.Bignum.X86_64.hdr sLen)), .mov .r15 (.mem (VG.Impl.Bignum.X86_64.hdr Impl.Bignum.X86_64.Public.sMask))] : List Instr))) hc).isSome
      = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.GS) (seqs (storeA j sPtr sLen Impl.Bignum.X86_64.Public.sMask)) (Two VG.Proof.Rsa.X86_64.GS) :=
  VG.Proof.Rsa.X86_64.pin_ct [.rdi] [.rdi, .rbx, .rsi, .rcx] (fun p => VG.Proof.Rsa.X86_64.ioVal p.B (VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot (VG.Proof.Rsa.X86_64.wk p.k) j)) (ptr p) (len p)) VG.Proof.Rsa.X86_64.pins_GS ht
    (fun p s h => by
      obtain ⟨hp, hl, -⟩ := hA p s h
      exact WP.mono (VG.Proof.Rsa.X86_64.storeBlk_ok h.ws hP hL hp hl) fun t ⟨hbx, hsi, hcx, hdi⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact hbx
        · exact hsi
        · exact hcx)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hl, hwr, hsep, hl1, hlw⟩ := hA p s h
      obtain ⟨I, c, rfl, hw, ha, hW, L, O, hm⟩ := h
      dsimp only [CvIn.pub] at hp hl hwr hsep hl1 hlw ⊢
      have hn := hw.scr.nowrap
      have h256 := hw.h256
      refine WP.mono (VG.Proof.Rsa.X86_64.storeA_ws hw hj hP hL hp hl hm hl1 hlw (fun i hi => by rw [hW]; exact hwr i hi) hsep)
        fun t ⟨_, _, ht, hf, k⟩ => ?_
      have fw : ∀ i < 32, Bignum.X86_64.word t.mem I.B (8 * i) = Bignum.X86_64.word s.mem I.B (8 * i) :=
        fun i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
      exact ⟨I, c, rfl, ht, ha.congr fun i hi => fw i (by unfold VG.Proof.Rsa.X86_64.argSlot at hi; omega), k.2.2.trans hW, L, O,
        (fw _ (by decide)).trans hm⟩

theorem retMask_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.GS) (.block retMask) fun _ _ => True :=
  two_taint [.rdi] VG.Proof.Rsa.X86_64.pins_GS (by taint_decide)

/-- The stores and the exit. -/
theorem stores_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.GS) (seqs (storeA aX₂ sQi sPl Impl.Bignum.X86_64.Public.sMask ++
    (storeA aX₁ sDp sPl Impl.Bignum.X86_64.Public.sMask ++ (storeA aV sDq sQl Impl.Bignum.X86_64.Public.sMask ++
      ([.block retMask] : List (Prog isa)))))) (Two fun (_ : VG.Proof.Rsa.X86_64.CvP) (_ : State) => True) := by
  have k8 : ∀ {k l : Nat}, l < k → l ≤ 8 * VG.Proof.Rsa.X86_64.wk k := fun {k l} h => by unfold VG.Proof.Rsa.X86_64.wk; omega
  refine (VG.Proof.Rsa.X86_64.ct_app (by simp [storeA]) (by simp [storeA])
    (VG.Proof.Rsa.X86_64.storeA_ct (by decide) (by decide) (by decide) CvP.pQi CvP.pl (fun p s h => ?_) (by taint_decide))
    (VG.Proof.Rsa.X86_64.ct_app (by simp [storeA]) (by simp [storeA])
      (VG.Proof.Rsa.X86_64.storeA_ct (by decide) (by decide) (by decide) CvP.pDp CvP.pl (fun p s h => ?_) (by taint_decide))
      (VG.Proof.Rsa.X86_64.ct_app (by simp [storeA]) (by simp)
        (VG.Proof.Rsa.X86_64.storeA_ct (by decide) (by decide) (by decide) CvP.pDq CvP.ql (fun p s h => ?_) (by taint_decide))
        (VG.Proof.Rsa.X86_64.ct_one (Ψ := fun (_ : VG.Proof.Rsa.X86_64.CvP) (_ : State) => True)
          (retMask_ct.mono (fun _ _ h => h) fun _ _ _ => ⟨default, trivial, trivial⟩)))))
  all_goals
    obtain ⟨I, c, rfl, -, ha, -, L, O, -⟩ := h
    dsimp only [CvIn.pub]
  · exact ⟨ha.qi, ha.pl, O.qi, O.sqi, L.pl1, k8 L.pl2⟩
  · exact ⟨ha.dp, ha.pl, O.dp, O.sdp, L.pl1, k8 L.pl2⟩
  · exact ⟨ha.dq, ha.ql, O.dq, O.sdq, L.ql1, k8 L.ql2⟩

/-! ## `main` -/

/-- On entry to `main`. -/
def GM (p : VG.Proof.Rsa.X86_64.CvP) (s : State) : Prop := ∃ I : VG.Proof.Rsa.X86_64.CvIn, I.pub = p ∧ VG.Proof.Rsa.X86_64.CvPre I s

theorem pins_GM : Pins VG.Proof.Rsa.X86_64.GM [.rdi] := fun _ _ _ ⟨_, e₁, h₁⟩ ⟨_, e₂, h₂⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁.rdi, h₂.rdi]
  exact (congrArg CvP.B e₁).trans (congrArg CvP.B e₂).symm

theorem CvPre.outs {I : VG.Proof.Rsa.X86_64.CvIn} {s : State} (h : VG.Proof.Rsa.X86_64.CvPre I s) : VG.Proof.Rsa.X86_64.CvOuts I :=
  ⟨fun i hi => by rw [← h.wr]; exact h.oQi.wr i hi, fun i hi => by rw [← h.wr]; exact h.oDp.wr i hi,
    fun i hi => by rw [← h.wr]; exact h.oDq.wr i hi, h.oQi.sep, h.oDp.sep, h.oDq.sep, h.a1, h.a2, h.a3⟩

theorem head_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.GM) (.block head) (Two VG.Proof.Rsa.X86_64.GA) :=
  two_piece [.rdi] VG.Proof.Rsa.X86_64.pins_GM (by taint_decide) fun _ s ⟨I, e, h⟩ =>
    WP.mono (VG.Proof.Rsa.X86_64.cvHeadS_ok h) fun _ ⟨ht, hm⟩ => ⟨I, s.mem, true, e, ht, h.L, h.outs, hm⟩

/-- `main` leaks the same in two runs with the same public data. -/
theorem cvMain_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.GM) VG.Impl.Rsa.X86_64.Keys.CrtValues.main fun _ _ => True := by
  rw [VG.Proof.Rsa.X86_64.main_eq]
  exact (VG.Proof.Rsa.X86_64.ct_app (by simp) (by simp [loadA]) (VG.Proof.Rsa.X86_64.ct_one VG.Proof.Rsa.X86_64.head_ct)
    (VG.Proof.Rsa.X86_64.ct_app (by simp [loadA]) (by simp [pqCheck]) VG.Proof.Rsa.X86_64.loads_ct
    (VG.Proof.Rsa.X86_64.ct_app (by simp [pqCheck]) (by simp [invPart, invSetup]) VG.Proof.Rsa.X86_64.pqCheck_ct
    (VG.Proof.Rsa.X86_64.ct_app (by simp [invPart, invSetup]) (by simp [divisor]) VG.Proof.Rsa.X86_64.invPart_ct
    (VG.Proof.Rsa.X86_64.ct_app (by simp [divisor]) (by simp)
      (VG.Proof.Rsa.X86_64.ct_app (by simp [divisor]) (by simp) (VG.Proof.Rsa.X86_64.divisor_ct (by decide) (by decide) (by taint_decide))
        (VG.Proof.Rsa.X86_64.ct_one (VG.Proof.Rsa.X86_64.divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by taint_decide))))
    (VG.Proof.Rsa.X86_64.ct_app (by simp) (by simp [divisor])
      (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.zeroA_ct (by decide) (by taint_decide))
        (VG.Proof.Rsa.X86_64.ct_one (VG.Proof.Rsa.X86_64.copyA_ct (by decide) (by decide) (by decide) (by taint_decide))))
    (VG.Proof.Rsa.X86_64.ct_app (by simp [divisor]) (by simp [storeA])
      (VG.Proof.Rsa.X86_64.ct_app (by simp [divisor]) (by simp) (VG.Proof.Rsa.X86_64.divisor_ct (by decide) (by decide) (by taint_decide))
        (VG.Proof.Rsa.X86_64.ct_one (VG.Proof.Rsa.X86_64.divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by taint_decide))))
      (stores_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.gs) h) fun _ _ h => h)))))))).mono
    (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.CvCTCode`. -/
section

/-!
# `vg_rsa_crt_values` on x86-64: constant time but for `n`

`entry` and the modulus' check leak the same in runs that agree on the
public data (the pointers, the lengths and `n`), and so do `fail` and
`main` (`cvMain_ct`): `cvCode_ct`, and the contract's `ConstantTime`
(`cvCode_constantTime`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- A state the contract allows, with the public data `p`. -/
def CVRel (p : VG.Proof.Rsa.X86_64.CvP) (s : State) : Prop := cvContract.pre s ∧ (VG.Proof.Rsa.X86_64.cvIn s).pub = p

theorem cvEntry_split : VG.Impl.Rsa.X86_64.Keys.CrtValues.entry ++ ([.mov .rdx (.mem (VG.Impl.Bignum.X86_64.hdr Impl.Bignum.X86_64.Public.sN)),
    .mov .rcx (.mem (VG.Impl.Bignum.X86_64.hdr Impl.Bignum.X86_64.Public.sK))] : List Instr) =
    ([.mov .r11 (.mem { base := .rsp, disp := 72 })] : List Instr) ++
      ((entry.drop 1) ++ [.mov .rdx (.mem (VG.Impl.Bignum.X86_64.hdr Impl.Bignum.X86_64.Public.sN)),
        .mov .rcx (.mem (VG.Impl.Bignum.X86_64.hdr Impl.Bignum.X86_64.Public.sK))]) := rfl

/-- After `entry`'s first instruction. -/
def CV1 (p : VG.Proof.Rsa.X86_64.CvP) (t : State) : Prop :=
  ∃ s, VG.Proof.Rsa.X86_64.CVRel p s ∧ t.gpr .r11 = p.B ∧ t.gpr .rsp = p.sp ∧
    WP isa (.block ((entry.drop 1) ++ [.mov .rdx (.mem (VG.Impl.Bignum.X86_64.hdr Impl.Bignum.X86_64.Public.sN)),
      .mov .rcx (.mem (VG.Impl.Bignum.X86_64.hdr Impl.Bignum.X86_64.Public.sK))])) t (VG.Proof.Rsa.X86_64.CvHeadPost s)

/-- After `entry` and the reloads. -/
def CV2 (p : VG.Proof.Rsa.X86_64.CvP) (t : State) : Prop := ∃ s, VG.Proof.Rsa.X86_64.CVRel p s ∧ VG.Proof.Rsa.X86_64.CvHeadPost s t

/-- After the modulus' check. -/
def CV3 (p : VG.Proof.Rsa.X86_64.CvP) (t : State) : Prop :=
  ∃ s t₁, VG.Proof.Rsa.X86_64.CVRel p s ∧ VG.Proof.Rsa.X86_64.CvHeadPost s t₁ ∧ t.mem = t₁.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .rsi] t₁ t ∧
    t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k)

/-- Between the zeros of `fail`. -/
def GF (p : VG.Proof.Rsa.X86_64.CvP) (s : State) : Prop :=
  ∃ I : VG.Proof.Rsa.X86_64.CvIn, I.pub = p ∧ VG.Proof.Bignum.X86_64.Scr s I.B I.Z ∧ s.gpr .rdi = I.B ∧
    VG.Proof.Rsa.X86_64.CvArgs s.mem I.B I.k I.pl I.ql I.dl I.pDp I.pDq I.pQi I.pN I.pP I.pQ I.pD I.sv ∧ s.wr = I.W ∧ VG.Proof.Rsa.X86_64.CvLens I ∧
    VG.Proof.Rsa.X86_64.CvOuts I

theorem pins_GF : Pins VG.Proof.Rsa.X86_64.GF [.rdi] := fun _ _ _ ⟨_, e₁, _, h₁, _⟩ ⟨_, e₂, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁, h₂]
  exact (congrArg CvP.B e₁).trans (congrArg CvP.B e₂).symm

/-- The registers `zeroOut`'s loop needs pinned. -/
def zoVal (ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .rsi => ptr
  | .rcx => BitVec.ofNat 64 len
  | _ => 0

theorem zeroOut_ct {sPtr sLen : Nat} (hP : sPtr < 32) (hL : sLen < 32) (ptr : VG.Proof.Rsa.X86_64.CvP → Addr) (len : VG.Proof.Rsa.X86_64.CvP → Nat)
    (hA : ∀ p s, VG.Proof.Rsa.X86_64.GF p s → Bignum.X86_64.word s.mem p.B (8 * sPtr) = ptr p ∧
      Bignum.X86_64.word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∀ i < len p, InRegions p.W (ptr p + BitVec.ofNat 64 i) 1) ∧
      (∀ i < len p, p.Z ≤ VG.Proof.Bignum.X86_64.ofs p.B (ptr p + BitVec.ofNat 64 i)) ∧ 1 ≤ len p ∧ len p < 2 ^ 31)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rsi (.mem (VG.Impl.Bignum.X86_64.hdr sPtr)), .mov .rcx (.mem (VG.Impl.Bignum.X86_64.hdr sLen)),
      .mov32 .rax (.imm 0)]) hc).isSome = true) :
    RelCT isa (Two VG.Proof.Rsa.X86_64.GF) (zeroOut sPtr sLen) (Two VG.Proof.Rsa.X86_64.GF) :=
  VG.Proof.Rsa.X86_64.pin_ct [.rdi] [.rsi, .rcx] (fun p => VG.Proof.Rsa.X86_64.zoVal (ptr p) (len p)) VG.Proof.Rsa.X86_64.pins_GF ht
    (fun p s h => by
      obtain ⟨hp, hl, -⟩ := hA p s h
      obtain ⟨I, rfl, hs, hdi, -, -, L, -⟩ := h
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega
      have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off I.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
      refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = ptr I.pub ∧
        t.gpr .rcx = BitVec.ofNat 64 (len I.pub)) (by
        xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, hdrOff, hl' sPtr hP, hl' sLen hL]
        exact ⟨hp, hl⟩) rfl) fun t ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hl, hwr, hsep, hl1, hl2⟩ := hA p s h
      obtain ⟨I, rfl, hs, hdi, ha, hW, L, O⟩ := h
      dsimp only [CvIn.pub] at hp hl hwr hsep hl1 hl2 ⊢
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega
      refine WP.mono (VG.Proof.Rsa.X86_64.zeroOut_ok hs hdi h256 hP hL hp hl hl1 hl2 ⟨fun i hi => by rw [hW]; exact hwr i hi, hsep⟩)
        fun t ⟨_, hx, k⟩ => ?_
      have fw : ∀ i < 32, Bignum.X86_64.word t.mem I.B (8 * i) = Bignum.X86_64.word s.mem I.B (8 * i) :=
        fun i hi => (VG.Proof.Rsa.X86_64.frm_scr hsep hx).word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega))
          (by omega)
      exact ⟨I, rfl, hs.congr k.2.2, (k.gpr (by decide)).trans hdi, ha.congr fun i hi => fw i (by
        unfold VG.Proof.Rsa.X86_64.argSlot at hi; omega), k.2.2.trans hW, L, O⟩

theorem failExit_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.GF) (.block (([.mov32 .rax (.imm 0)] : List Instr) ++ Impl.Bignum.X86_64.Public.exit))
    fun _ _ => True :=
  two_taint [.rdi] VG.Proof.Rsa.X86_64.pins_GF (by taint_decide)

/-- `fail` leaks the same in two runs with the same public data. -/
theorem fail_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.GF) VG.Impl.Rsa.X86_64.Keys.CrtValues.fail fun _ _ => True := by
  unfold VG.Impl.Rsa.X86_64.Keys.CrtValues.fail
  refine (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.zeroOut_ct (by decide) (by decide) CvP.pDp CvP.pl (fun p s h => ?_) (by taint_decide))
    (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.zeroOut_ct (by decide) (by decide) CvP.pDq CvP.ql (fun p s h => ?_) (by taint_decide))
    (VG.Proof.Rsa.X86_64.ct_cons (by simp) (VG.Proof.Rsa.X86_64.zeroOut_ct (by decide) (by decide) CvP.pQi CvP.pl (fun p s h => ?_) (by taint_decide))
    (VG.Proof.Rsa.X86_64.ct_one (Ψ := fun (_ : VG.Proof.Rsa.X86_64.CvP) (_ : State) => True)
      (failExit_ct.mono (fun _ _ h => h) fun _ _ _ => ⟨default, trivial, trivial⟩))))).mono (fun _ _ h => h)
    fun _ _ _ => trivial
  all_goals
    obtain ⟨I, rfl, -, -, ha, -, L, O⟩ := h
    dsimp only [CvIn.pub]
    have := L.k2
  · exact ⟨ha.dp, ha.pl, O.dp, O.sdp, L.pl1, by have := L.pl2; omega⟩
  · exact ⟨ha.dq, ha.ql, O.dq, O.sdq, L.ql1, by have := L.ql2; omega⟩
  · exact ⟨ha.qi, ha.pl, O.qi, O.sqi, L.pl1, by have := L.pl2; omega⟩

/-- `vg_rsa_crt_values` leaks the same in runs that agree on the public
data. -/
theorem cvCode_ct : RelCT isa (Two VG.Proof.Rsa.X86_64.CVRel) CrtValues.code fun _ _ => True := by
  unfold CrtValues.code
  refine RelCT.seq (R := Two VG.Proof.Rsa.X86_64.CV3) (RelCT.block_append (RelCT.seq (R := Two VG.Proof.Rsa.X86_64.CV2) ?_ ?_)) ?_
  · rw [VG.Proof.Rsa.X86_64.cvEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := VG.Proof.Rsa.X86_64.CV1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (congrArg CvP.sp h₁.2).trans (congrArg CvP.sp h₂.2).symm) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := VG.Proof.Rsa.X86_64.cvCtx_of hs.1
    have hh : WP isa (.block (([.mov .r11 (.mem { base := .rsp, disp := 72 })] : List Instr) ++
        ((entry.drop 1) ++ [.mov .rdx (.mem (VG.Impl.Bignum.X86_64.hdr Impl.Bignum.X86_64.Public.sN)),
          .mov .rcx (.mem (VG.Impl.Bignum.X86_64.hdr Impl.Bignum.X86_64.Public.sK))]))) s (VG.Proof.Rsa.X86_64.CvHeadPost s) := by
      rw [← VG.Proof.Rsa.X86_64.cvEntry_split]; exact VG.Proof.Rsa.X86_64.cvHead_ok' c
    have e8 : s.gpr .rsp + BitVec.ofInt 64 72 = stackArgAddr s 8 := rfl
    have hB' : s.mem.readW (stackArgAddr s 8) 64 = stackArg s 8 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 8)
      (by xrun [State.ea, e8, c.ha 8 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans (congrArg CvP.B hs.2), (k.gpr (by decide)).trans (congrArg CvP.sp hs.2), hw⟩
  -- The modulus' check.
  · refine two_piece [.rdx, .rcx] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.rdx, h₂.rdx]
        exact (congrArg CvP.pN c₁.2).trans (congrArg CvP.pN c₂.2).symm
      · rw [h₁.rcx, h₂.rcx]
        exact congrArg (BitVec.ofNat 64) ((congrArg CvP.k c₁.2).trans (congrArg CvP.k c₂.2).symm))
      (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := VG.Proof.Rsa.X86_64.cvCtx_of hs.1
    have hnb := c.n.congrK h.inScr h.keep
    have hnl : (VG.Proof.Rsa.X86_64.cvIn s).nb.length = (stackArg s 1).toNat := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _
    refine WP.mono (invalid_ok h.rdx h.rcx c.L.k1 c.L.k2 hnl (fun i hi => hnb.rd i (by rw [hnl]; exact hi))
      (fun i hi => hnb.val i _)) fun t' ⟨hz, hm, k⟩ => ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, ← hs.2]
    rfl
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    simp only [VG.X86_64.eval, z₁, z₂]) ?_ ?_
  · exact fail_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ => by
      have hpre := VG.Proof.Rsa.X86_64.cvPre_of (VG.Proof.Rsa.X86_64.cvCtx_of hs.1) h hm k
      exact ⟨VG.Proof.Rsa.X86_64.cvIn s, hs.2, hpre.scr, hpre.rdi, hpre.args, hpre.wr, hpre.L, hpre.outs⟩) h) fun _ _ h => h
  · exact cvMain_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ =>
      ⟨VG.Proof.Rsa.X86_64.cvIn s, hs.2, VG.Proof.Rsa.X86_64.cvPre_of (VG.Proof.Rsa.X86_64.cvCtx_of hs.1) h hm k⟩) h) fun _ _ h => h

/-- `vg_rsa_crt_values` is constant time but for `n`. -/
theorem cvCode_constantTime : ConstantTime isa cvContract.pre cvContract.pub CrtValues.code := by
  refine RelCT.constantTime (cvCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨(VG.Proof.Rsa.X86_64.cvIn s₁).pub, ⟨h₁, rfl⟩, ⟨h₂, ?_⟩⟩)
    fun _ _ h => h)
  obtain ⟨hr, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, hn⟩ := hp
  have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
  have w₁ := h₁.2.2.1
  have w₂ := h₂.2.2.1
  simp only [CvIn.pub, VG.Proof.Rsa.X86_64.cvIn, CvP.mk.injEq]
  refine ⟨a8.symm, by rw [a9], by rw [a1], by rw [a3], by rw [a5], by rw [a7], r .rdi (by decide),
    r .rdx (by decide), r .r8 (by decide), a0.symm, a2.symm, a4.symm, a6.symm, hn.symm, ?_, r .rsp (by decide)⟩
  rw [w₁, w₂, r .rdi (by decide), r .rsi (by decide), r .rdx (by decide), r .rcx (by decide), r .r8 (by decide),
    r .r9 (by decide), a8, a9]

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.CvVerified`. -/
section

/-!
# `vg_rsa_crt_values` on x86-64: verified against the shared contract

`cvContract` states the shared contract on the registers and the stack
(`cv_implies`); with correctness (`cvCode_correct`) and constant time
(`cvCode_constantTime`), `CrtValues.code` is verified (`cv_verified`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64.Keys

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

/-- A state meeting `cvContract.pre`: a 512-bit modulus, one-byte factors
and exponent, and the stack arguments at `0x6008`. -/
def cvSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 0x1100 | .rcx => 1 | .r8 => 0x1200 | .r9 => 1
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x20 else if a = 0x6010 then 0x40 else if a = 0x6019 then 0x30
    else if a = 0x6020 then 1 else if a = 0x6029 then 0x31 else if a = 0x6030 then 1
    else if a = 0x6039 then 0x32 else if a = 0x6040 then 1 else if a = 0x6049 then 0x80
    else if a = 0x6051 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x6008, 80⟩]
  wr := [⟨0x1000, 1⟩, ⟨0x1100, 1⟩, ⟨0x1200, 1⟩, ⟨0x8000, 8192⟩]

theorem cv_implies : cvContract.Implies (Spec.Rsa.crtValuesContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, VG.Proof.Rsa.X86_64.cvContract, VG.Proof.Rsa.X86_64.stackArgs_ten, List.append_eq] at h
    sig_pre [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, VG.Proof.Rsa.X86_64.cvContract, VG.Proof.Rsa.X86_64.stackArgs_ten, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, VG.Proof.Rsa.X86_64.cvContract, VG.Proof.Rsa.X86_64.stackArgs_ten, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, VG.Proof.Rsa.X86_64.cvContract, VG.Proof.Rsa.X86_64.stackArgs_ten, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, VG.Proof.Rsa.X86_64.cvContract, VG.Proof.Rsa.X86_64.stackArgs_ten, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    refine ⟨?_, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, VG.Proof.Rsa.X86_64.cvContract, VG.Proof.Rsa.X86_64.stackArgs_ten, List.append_eq] [cvSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Rsa.X86_64.cvSatState

/-- `vg_rsa_crt_values`, given that its code never loads MXCSR (which the
registration file evaluates). -/
theorem cv_verified (hmx : CrtValues.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target CrtValues.code (Spec.Rsa.crtValuesContract abi) :=
  Verified.of_correct (VG.Proof.Rsa.X86_64.cvCode_correct hmx) VG.Proof.Rsa.X86_64.cvCode_constantTime VG.Proof.Rsa.X86_64.cv_implies

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpBase`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: the working space

The header slots the recovery changes besides the arrays (`RMut`: `-n⁻¹`,
the mask, the candidates' counters and masks, `t` and `sMo`), which keep the
working space (`Ws.congrR`); and the value of a number's low words
(`wv_mod`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- The header slots the recovery changes: `-n⁻¹` (7), the mask (22), the
candidate's number (25), the counters and masks (26, 30, 31), `t` (27) and
`sMo` (29). -/
def rSlot (i : Nat) : Bool :=
  i == 7 || i == 22 || i == 25 || i == 26 || i == 27 || i == 29 || i == 30 || i == 31

/-- The ranges the recovery's pieces may change: arrays, and the slots of
`rSlot`. -/
def RMut (r : Nat × Nat) : Prop := 8 * 32 ≤ r.1 ∨ ∃ i, VG.Proof.Rsa.X86_64.rSlot i = true ∧ r = (8 * i, 8)

theorem RMut.ofSlot (w j n : Nat) : VG.Proof.Rsa.X86_64.RMut (Bignum.X86_64.slot w j, n) :=
  Or.inl (by unfold Bignum.X86_64.slot hdrBytes; omega)

theorem RMut.hdr {i : Nat} (h : VG.Proof.Rsa.X86_64.rSlot i = true) : VG.Proof.Rsa.X86_64.RMut (8 * i, 8) := Or.inr ⟨i, h, rfl⟩

theorem RMut.of_mut {r : Nat × Nat} (h : VG.Proof.Rsa.X86_64.Mut r) : VG.Proof.Rsa.X86_64.RMut r := by
  rcases h with h | rfl | rfl
  · exact Or.inl h
  · exact RMut.hdr (by decide)
  · exact RMut.hdr (by decide)

/-- A slot of `rSlot` is not `w`'s, the stride's or a base's. -/
theorem rSlot_ne {i j : Nat} (h : VG.Proof.Rsa.X86_64.rSlot i = true) (hj : j ∈ [sW, sStride] ∨ (8 ≤ j ∧ j < 16)) :
    8 * j + 8 ≤ 8 * i ∨ 8 * i + 8 ≤ 8 * j := by
  simp only [VG.Proof.Rsa.X86_64.rSlot, Bool.or_eq_true, beq_iff_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false, sW, sStride, sFn] at hj
  omega

theorem Ws.congrR {s t : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {rs : List (Nat × Nat)}
    (hf : Frm B rs s.mem t.mem) (hm : ∀ r ∈ rs, VG.Proof.Rsa.X86_64.RMut r) {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t)
    (hr : .rdi ∉ regs) : VG.Proof.Rsa.X86_64.Ws t B Z w := by
  have hh : ∀ i, i ∈ [sW, sStride] ∨ (8 ≤ i ∧ i < 16) → VG.Proof.Bignum.X86_64.word t.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := by
    intro i hi
    have hi' : i < 16 ∨ i = 28 := by simp only [List.mem_cons, List.not_mem_nil, or_false, sW, sStride, sFn] at hi; omega
    exact hf.word_eq (fun r hr => by
      rcases hm r hr with h | ⟨j, hj, rfl⟩
      · omega
      · have := VG.Proof.Rsa.X86_64.rSlot_ne hj hi; dsimp only; omega)
      (by have := h.scr.nowrap; have := hdr_lt_slot w 16 (show 31 < 32 by decide); have := h.hZ; omega)
  exact ⟨h.scr.congr k.2.2, (k.gpr hr).trans h.rdi, (hh sW (.inl (by simp))).trans h.hw,
    (hh sStride (.inl (by simp))).trans h.hS, fun j hj => (hh (sArr j) (.inr (by unfold sArr; omega))).trans (h.harr j hj),
    h.hZ, h.w1, h.w2⟩

/-- The low `j` words of a number of `w ≥ j` words. -/
theorem wv_mod (m : Mem) (B : Addr) (e : Nat) {j w : Nat} (hj : j ≤ w) :
    wv m B e w % 2 ^ (64 * j) = wv m B e j := by
  have e1 := wv_add m B e j (w - j)
  rw [show j + (w - j) = w by omega] at e1
  rw [e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wv_lt _ _ _ _)]

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpProd`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: `M = d e`

`prod` zeroes `M`'s two arrays and adds `e_j d` at word `j` of `M`, by
`mulAddRow`, for each word `j` of `e` (`prod_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- `prodInit`: the bases, `e`'s words and the row counter. -/
theorem prodInit_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {el : Nat}
    (hel : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32) :
    WP isa (.block prodInit) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aE) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aM) ∧
      t.gpr .r15 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aD) ∧ t.gpr .r11 = BitVec.ofNat 64 ((el + 7) / 8) ∧
      t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.gpr .rdi = B ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .rbx, .r10, .r15, .r11, .r13] s t := by
  unfold prodInit
  rw [List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  have hdi₁ : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.rdi
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok aE (r := .rbx) (by decide) hdi₁ h9) fun t₂ ⟨hbx, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok aM (r := .r10) (by decide) ((k₂.gpr (by decide)).trans hdi₁)
    ((k₂.gpr (by decide)).trans h9)) fun t₃ ⟨h10, m₃, k₃⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok aD (r := .r15) (by decide) ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hdi₁))
    ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h9))) fun t₄ ⟨h15, m₄, k₄⟩ => ?_
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hdi₄ : t₄.gpr .rdi = B := (k14.gpr (by decide)).trans h.rdi
  have hs₄ := h.scr.congr k14.2.2
  have hl : InRegions (t₄.rd ++ t₄.wr) (VG.Proof.Bignum.X86_64.off B (8 * Impl.Bignum.X86_64.Public.sElen)) 8 :=
    hs₄.ld (by have := h.h256; simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega)
  refine WP.mono (WP.keep [.r11, .r13] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 ((el + 7) / 8) ∧
    t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = t₄.mem) (by
      xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi₄, hdrOff, hl, m₄, m₃, m₂, m₁, hel, shr3_w el hel']) rfl)
    fun t ⟨⟨h11, h13, m⟩, k₅⟩ => ⟨?_, ?_, ?_, ?_, h11, h13, (k₅.gpr (by decide)).trans hdi₄,
      by rw [m, m₄, m₃, m₂, m₁], (k14.trans k₅).mono (by simp)⟩
  · exact (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans
      ((k₂.gpr (by decide)).trans h12)))
  · exact (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hbx))
  · exact (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans h10)
  · exact (k₅.gpr (by decide)).trans h15

/-- `rowHead`: `e`'s word `j`, the accumulator's base at word `j` of `M`,
and `d`'s base. -/
theorem rowHead_ok {t : State} {B : Addr} {Z w j : Nat} (hs : VG.Proof.Bignum.X86_64.Scr t B Z) (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z)
    (hbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aE)) (h10 : t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aM))
    (h15 : t.gpr .r15 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aD)) (h13 : t.gpr .r13 = BitVec.ofNat 64 j) (hj : j < w) :
    WP isa (.block rowHead) t fun t' =>
      t'.gpr .rcx = VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aE + 8 * j) ∧ t'.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aM + 8 * j) ∧
      t'.gpr .r9 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aD) ∧ t'.mem = t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rcx, .r8, .r9] t t' := by
  have hn := hs.nowrap
  have sE := VG.Proof.Rsa.X86_64.slot_lt (w := w) (show aE < 16 by decide)
  unfold rowHead
  refine WP.mono (WP.keep [.rcx, .r8, .r9] (Q := fun t' => t'.gpr .rcx = VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aE + 8 * j) ∧
    t'.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aM + 8 * j) ∧ t'.gpr .r9 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aD) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, c, d, k⟩
  xrun [State.ea, ix, addr0 hbx h13, hs.ld (d := VG.Proof.Bignum.X86_64.slot w aE + 8 * j) (by omega), h10, h15]
  rw [h13, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, VG.Proof.Bignum.X86_64.off, BitVec.add_comm,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2
  omega

/-- A number below `P R` of the form `A + P (W + Q H)` with `R ≤ Q`: `H = 0`
and `W < R`. -/
theorem window_split {T A W H P Q R : Nat} (hT : T = A + P * (W + Q * H)) (hlt : T < P * R) (hRQ : R ≤ Q) :
    H = 0 ∧ W < R := by
  have h1 : P * (W + Q * H) < P * R := Nat.lt_of_le_of_lt (by rw [hT]; exact Nat.le_add_left _ _) hlt
  have h2 : W + Q * H < R := Nat.lt_of_mul_lt_mul_left h1
  refine ⟨?_, by omega⟩
  rcases Nat.eq_zero_or_pos H with h | h
  · exact h
  · have : Q ≤ Q * H := Nat.le_mul_of_pos_right _ h
    omega

theorem row_alg {A P W c D Ej Q : Nat} (hT : D * Ej = A + P * (W + Q * 0)) :
    A + P * (W + c * D + Q * 0) = D * (Ej + P * c) := by
  grind

/-- After `j` rows: `M = d (e mod 2^(64 j))`. -/
structure ProdInv (s₁ : State) (B : Addr) (Z w : Nat) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rbp, .r14, .rcx, .r8, .r9, .r13] s₁ t
  r13 : t.gpr .r13 = BitVec.ofNat 64 j
  out : VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w aM) (16 * (w + 2)) s₁.mem t.mem
  val : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) = wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w aD) w * wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w aE) j

/-- A row. -/
theorem prodStep_ok {s₁ t : State} {B : Addr} {Z w we j : Nat} (hI : VG.Proof.Rsa.X86_64.ProdInv s₁ B Z w j t) (hw : 2 ≤ w)
    (hw' : w < 2 ^ 24) (hZ : VG.Proof.Bignum.X86_64.slot w 16 ≤ Z) (hwe : we ≤ w) (hj : j < we)
    (h12 : s₁.gpr .r12 = BitVec.ofNat 64 w) (hbx : s₁.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aE))
    (h10 : s₁.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aM)) (h15 : s₁.gpr .r15 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aD))
    (h11 : s₁.gpr .r11 = BitVec.ofNat 64 we) :
    WP isa (.seq (.block rowHead) (.seq mulAddRow (.block rowNext))) t fun t' =>
      t'.zf = some (decide (j + 1 = we)) ∧ VG.Proof.Rsa.X86_64.ProdInv s₁ B Z w (j + 1) t' := by
  have hn := hI.scr.nowrap
  have sE := VG.Proof.Rsa.X86_64.slot_lt (w := w) (show aE < 16 by decide)
  have sD := VG.Proof.Rsa.X86_64.slot_lt (w := w) (show aD < 16 by decide)
  have sM := VG.Proof.Rsa.X86_64.slot_lt (w := w) (show aM + 1 < 16 by decide)
  have eM1 : VG.Proof.Bignum.X86_64.slot w (aM + 1) = VG.Proof.Bignum.X86_64.slot w aM + 8 * (w + 2) := by simp only [VG.Proof.Bignum.X86_64.slot, hdrBytes, aM]; omega
  have eDM : VG.Proof.Bignum.X86_64.slot w aD + 8 * (w + 2) = VG.Proof.Bignum.X86_64.slot w aM := by simp only [VG.Proof.Bignum.X86_64.slot, hdrBytes, aD, aM]; omega
  have eEM : VG.Proof.Bignum.X86_64.slot w aE + 8 * (w + 2) = VG.Proof.Bignum.X86_64.slot w aD := by simp only [VG.Proof.Bignum.X86_64.slot, hdrBytes, aE, aD]; omega
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.rowHead_ok hI.scr hZ ((hI.keep.gpr (by decide)).trans hbx)
    ((hI.keep.gpr (by decide)).trans h10) ((hI.keep.gpr (by decide)).trans h15) hI.r13 (by omega))
    fun t₁ ⟨hcx, h8, h9, m₁, k₁⟩ => ?_)
  have k01 := hI.keep.trans k₁
  have hs₁ := hI.scr.congr k₁.2.2
  -- `d` and `e`'s word `j`, as at the start.
  have hD : wv t₁.mem B (VG.Proof.Bignum.X86_64.slot w aD) w = wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w aD) w := by
    rw [m₁]; exact hI.out.wv (Or.inl (by omega)) (by omega)
  have hc : (t₁.gpr .rcx).toNat = (VG.Proof.Bignum.X86_64.word s₁.mem B (VG.Proof.Bignum.X86_64.slot w aE + 8 * j)).toNat := by
    rw [hcx, hI.out.word (Or.inl (by omega)) (by omega)]
  -- The accumulator's window, words `j` to `j + w + 1` of `M`.
  have hsplit : ∀ m : Mem, wv m B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) = wv m B (VG.Proof.Bignum.X86_64.slot w aM) j + 2 ^ (64 * j) *
      (wv m B (VG.Proof.Bignum.X86_64.slot w aM + 8 * j) (w + 2) + 2 ^ (64 * (w + 2)) *
        wv m B (VG.Proof.Bignum.X86_64.slot w aM + 8 * j + 8 * (w + 2)) (w + 2 - j)) := fun m => by
    have e1 := wv_add m B (VG.Proof.Bignum.X86_64.slot w aM) j (2 * (w + 2) - j)
    have e2 := wv_add m B (VG.Proof.Bignum.X86_64.slot w aM + 8 * j) (w + 2) (w + 2 - j)
    rw [show j + (2 * (w + 2) - j) = 2 * (w + 2) by omega] at e1
    rw [show w + 2 + (w + 2 - j) = 2 * (w + 2) - j by omega] at e2
    rw [e1, e2]
  have hT := hsplit t₁.mem
  rw [m₁, hI.val] at hT
  have hlt : wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w aD) w * wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w aE) j < 2 ^ (64 * j) * 2 ^ (64 * w) := by
    rw [Nat.mul_comm (2 ^ (64 * j))]
    exact Nat.mul_lt_mul'' (wv_lt _ _ _ _) (wv_lt _ _ _ _)
  obtain ⟨hH, hW⟩ := VG.Proof.Rsa.X86_64.window_split hT hlt (Nat.pow_le_pow_right (by decide) (by omega))
  have hbound : wv t₁.mem B (VG.Proof.Bignum.X86_64.slot w aM + 8 * j) (w + 2) + (t₁.gpr .rcx).toNat * wv t₁.mem B (VG.Proof.Bignum.X86_64.slot w aD) w <
      2 ^ (64 * (w + 2)) := by
    rw [hc, hD, m₁]
    have h1 : (VG.Proof.Bignum.X86_64.word s₁.mem B (VG.Proof.Bignum.X86_64.slot w aE + 8 * j)).toNat * wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w aD) w < 2 ^ 64 * 2 ^ (64 * w) :=
      Nat.mul_lt_mul'' (BitVec.isLt _) (wv_lt _ _ _ _)
    have h2 : 2 ^ (64 * (w + 2)) = 2 ^ (64 * w) * 2 ^ 128 := by rw [← Nat.pow_add]; congr 1
    have h3 : 2 ^ (64 * w) + 2 ^ 64 * 2 ^ (64 * w) ≤ 2 ^ (64 * w) * 2 ^ 128 := by
      rw [show 2 ^ (64 * w) + 2 ^ 64 * 2 ^ (64 * w) = 2 ^ (64 * w) * (1 + 2 ^ 64) by grind]
      exact Nat.mul_le_mul_left _ (by decide)
    omega
  refine WP.seq (WP.mono (mulAddRow_ok hs₁ h8 h9 ((k01.gpr (by decide)).trans h12) (by omega) (by omega)
    (by omega) (by omega) (Or.inr (by omega)) hbound) fun t₂ ⟨hv₂, o₂, k₂⟩ => ?_)
  have k02 := k01.trans k₂
  refine WP.mono (WP.keep [.r13] (Q := fun t' => t'.zf = some (decide (j + 1 = we)) ∧
      t'.gpr .r13 = BitVec.ofNat 64 (j + 1) ∧ t'.mem = t₂.mem) (by
    unfold rowNext
    xrun [(k₂.gpr (by decide) : t₂.gpr .r13 = _), (k₁.gpr (by decide) : t₁.gpr .r13 = _), hI.r13,
      (k02.gpr (by decide) : t₂.gpr .r11 = _), h11, ofNat_add_one,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show we < 2 ^ 64 by omega)]) rfl)
    fun t ⟨⟨hz, h13, mt⟩, k₃⟩ => ⟨hz, ⟨hs₁.congr (k₂.trans k₃).2.2, (k02.trans k₃).mono (by simp), h13,
      fun x hx => by
        rw [mt, o₂ x (by omega), m₁]; exact hI.out x hx, ?_⟩⟩
  -- The value.
  have hT₂ := hsplit t.mem
  have eA : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aM) j = wv t₁.mem B (VG.Proof.Bignum.X86_64.slot w aM) j := by
    rw [mt]; exact o₂.wv (Or.inl (by omega)) (by omega)
  have eH : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aM + 8 * j + 8 * (w + 2)) (w + 2 - j) =
      wv t₁.mem B (VG.Proof.Bignum.X86_64.slot w aM + 8 * j + 8 * (w + 2)) (w + 2 - j) := by
    rw [mt]; exact o₂.wv (Or.inr (by omega)) (by omega)
  have eW : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aM + 8 * j) (w + 2) = wv t₁.mem B (VG.Proof.Bignum.X86_64.slot w aM + 8 * j) (w + 2) +
      (t₁.gpr .rcx).toNat * wv t₁.mem B (VG.Proof.Bignum.X86_64.slot w aD) w := by rw [mt]; exact hv₂
  rw [eA, eH, eW, hc, hD, m₁, hH] at hT₂
  rw [hT₂, wv]
  rw [hH] at hT
  exact VG.Proof.Rsa.X86_64.row_alg hT

/-- `prod`: `M = d e` over `M`'s two arrays, for `e` of `⌈e_len / 8⌉` words. -/
theorem prod_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {el : Nat}
    (hel : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (he1 : 1 ≤ el)
    (he2 : el ≤ 8 * w) (hE : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aE) w < 2 ^ (64 * ((el + 7) / 8))) :
    WP isa (seqs prod) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) = wv s.mem B (VG.Proof.Bignum.X86_64.slot w aD) w * wv s.mem B (VG.Proof.Bignum.X86_64.slot w aE) w ∧
      VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w aM) (16 * (w + 2)) s.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .r8, .rax, .r14, .rbx, .r10, .r15, .r11, .r13, .rdx, .rbp, .rcx] s t := by
  have hn := h.scr.nowrap
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have sE := VG.Proof.Rsa.X86_64.slot_lt (w := w) (show aE < 16 by decide)
  have sD := VG.Proof.Rsa.X86_64.slot_lt (w := w) (show aD < 16 by decide)
  have sM := VG.Proof.Rsa.X86_64.slot_lt (w := w) (show aM + 1 < 16 by decide)
  have eM1 : VG.Proof.Bignum.X86_64.slot w (aM + 1) = VG.Proof.Bignum.X86_64.slot w aM + 8 * (w + 2) := by simp only [VG.Proof.Bignum.X86_64.slot, hdrBytes, aM]; omega
  have eDM : VG.Proof.Bignum.X86_64.slot w aD + 8 * (w + 2) = VG.Proof.Bignum.X86_64.slot w aM := by simp only [VG.Proof.Bignum.X86_64.slot, hdrBytes, aD, aM]; omega
  have eEM : VG.Proof.Bignum.X86_64.slot w aE + 8 * (w + 2) = VG.Proof.Bignum.X86_64.slot w aD := by simp only [VG.Proof.Bignum.X86_64.slot, hdrBytes, aE, aD]; omega
  unfold prod
  simp only [seqs]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.zeroA_ok h (j := aM) (by decide)) fun s₁ ⟨z₁, o₁, k₁⟩ => ?_)
  have h₁ := h.congr (Frm.of_outside o₁ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) k₁ (by decide)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.zeroA_ok h₁ (j := aM + 1) (by decide)) fun s₂ ⟨z₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.congr (Frm.of_outside o₂ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) k₂ (by decide)
  -- Memory but `M` as on entry.
  have o12 : VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w aM) (16 * (w + 2)) s.mem s₂.mem := fun x hx => by
    rw [o₂ x (by omega), o₁ x (by omega)]
  have hel₂ : VG.Proof.Bignum.X86_64.word s₂.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el := by
    rw [o12.word (Or.inl (by have := hdr_lt_slot w aM (show Impl.Bignum.X86_64.Public.sElen < 32 by decide); omega))
      (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega)]; exact hel
  have hz : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) = 0 := by
    rw [show 2 * (w + 2) = (w + 2) + (w + 2) by omega, wv_add, ← eM1, z₂,
      o₂.wv (Or.inl (by omega)) (by omega), z₁, Nat.mul_zero]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.prodInit_ok h₂ hel₂ (by omega)) fun s₃ ⟨h12, hbx, h10, h15, h11, h13, hdi, m₃, k₃⟩ => ?_)
  have hs₃ := h₂.scr.congr k₃.2.2
  refine wp_upto (a := 0) (N := (el + 7) / 8) (by omega) (VG.Proof.Rsa.X86_64.ProdInv s₃ B Z w)
    (fun j _ hj t hI => VG.Proof.Rsa.X86_64.prodStep_ok hI (by omega) (by omega) hZ (by omega) hj h12 hbx h10 h15 h11)
    (fun t hI => ?_) ⟨hs₃, Keep.refl _ _, h13, Outside.refl _ _ _ _, by rw [m₃, hz, wv, Nat.mul_zero]⟩
  have k03 := ((k₁.trans k₂).trans k₃).trans hI.keep
  have hDs : wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w aD) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w aD) w := by
    rw [m₃]; exact o12.wv (Or.inl (by omega)) (by omega)
  have hEs : wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w aE) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w aE) w := by
    rw [m₃]; exact o12.wv (Or.inl (by omega)) (by omega)
  refine ⟨?_, fun x hx => by rw [hI.out x hx, m₃]; exact o12 x hx, k03.mono (by simp)⟩
  rw [hI.val, hDs, VG.Proof.Rsa.X86_64.wv_low_of_lt (v := (el + 7) / 8) (w := w) (by omega) (by rw [hEs]; exact hE), hEs]

/-- `prod`'s loop, from `M = 0`. -/
theorem prodLoop_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {el : Nat}
    (hel : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (he1 : 1 ≤ el)
    (he2 : el ≤ 8 * w) (hE : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aE) w < 2 ^ (64 * ((el + 7) / 8)))
    (hz : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) = 0) :
    WP isa (.seq (.block prodInit) (.loop (.seq (.block rowHead) (.seq mulAddRow (.block rowNext))) .ne)) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) = wv s.mem B (VG.Proof.Bignum.X86_64.slot w aD) w * wv s.mem B (VG.Proof.Bignum.X86_64.slot w aE) w ∧
      VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w aM) (16 * (w + 2)) s.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .r8, .rax, .r14, .rbx, .r10, .r15, .r11, .r13, .rdx, .rbp, .rcx] s t := by
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.prodInit_ok h hel (by omega)) fun s₃ ⟨h12, hbx, h10, h15, h11, h13, hdi, m₃, k₃⟩ => ?_)
  have hs₃ := h.scr.congr k₃.2.2
  refine wp_upto (a := 0) (N := (el + 7) / 8) (by omega) (VG.Proof.Rsa.X86_64.ProdInv s₃ B Z w)
    (fun j _ hj t hI => VG.Proof.Rsa.X86_64.prodStep_ok hI (by omega) (by omega) hZ (by omega) hj h12 hbx h10 h15 h11)
    (fun t hI => ?_) ⟨hs₃, Keep.refl _ _, h13, Outside.refl _ _ _ _, by rw [m₃, hz, wv, Nat.mul_zero]⟩
  refine ⟨?_, fun x hx => by rw [hI.out x hx, m₃], (k₃.trans hI.keep).mono (by simp)⟩
  rw [hI.val, m₃, VG.Proof.Rsa.X86_64.wv_low_of_lt (v := (el + 7) / 8) (w := w) (by omega) hE]

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.RpSkip`. -/
section

/-!
# `vg_rsa_recover_primes` on x86-64: whether `d e - 1` is even and positive

`skipBlk` takes the mask of `M = d e` even and clears `M`'s low bit (`m =
M - 1` for an odd `M`); the loop of `orBody` tests `m = 0`, and `skipTest`
sets `ZF` to neither (`skip_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- A word's low bit, as a word. -/
theorem and_one (x : BitVec 64) : x &&& 1 = BitVec.ofNat 64 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show x.toNat % 2 < 2 ^ 64 by omega)]

/-- The mask of an even word, from its low bit. -/
theorem low_sub_one (x : BitVec 64) : (x &&& 1) - 1 = VG.Proof.Bignum.X86_64.mask (decide (x.toNat % 2 = 0)) := by
  rw [VG.Proof.Rsa.X86_64.and_one]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- A word minus its low bit. -/
theorem sub_low (x : BitVec 64) : (x - (x &&& 1)).toNat = x.toNat - x.toNat % 2 := by
  rw [VG.Proof.Rsa.X86_64.and_one, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

/-- `Bw = w + ⌈e_len / 8⌉` into `rax` (`bw`). -/
theorem bw_val (w el : Nat) (hel : el < 2 ^ 32) :
    (BitVec.ofNat 64 el + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 + BitVec.ofNat 64 w =
      BitVec.ofNat 64 (w + (el + 7) / 8) := by
  rw [shr3_w el hel, BitVec.ofNat_add_ofNat, Nat.add_comm]

/-- `skipBlk`. -/
theorem skipBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {el : Nat}
    (hel : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32) :
    WP isa (.block skipBlk) s fun t =>
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aM) ∧ t.gpr .rbp = 0 ∧ t.gpr .r12 = BitVec.ofNat 64 (w + (el + 7) / 8) ∧
      t.gpr .rdi = B ∧
      t.mem = (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aM)) (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aM) - (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aM) &&& 1))).writeW
        (VG.Proof.Bignum.X86_64.off B (8 * sC2)) (VG.Proof.Bignum.X86_64.mask (decide ((VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aM)).toNat % 2 = 0))) ∧
      VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .rbx, .rax, .rdx, .rcx, .rbp] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have sM := h.sl (j := aM) (by decide)
  have hM0 := hdr_lt_slot w aM (show sC2 < 32 by decide)
  unfold skipBlk
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok aM (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9)
    fun t₂ ⟨hbx, m₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := h.scr.congr k12.2.2
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans h.rdi
  have hl : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs₂.ld (by omega)
  have hW : VG.Proof.Bignum.X86_64.word t₂.mem B (8 * sW) = BitVec.ofNat 64 w := by rw [m₂, m₁]; exact h.hw
  have hE : VG.Proof.Bignum.X86_64.word t₂.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el := by rw [m₂, m₁]; exact hel
  refine WP.mono (WP.keep [.rax, .rdx, .rcx, .r12, .rbp] (Q := fun t => t.gpr .rbp = 0 ∧
    t.gpr .r12 = BitVec.ofNat 64 (w + (el + 7) / 8) ∧
    t.mem = (t₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aM)) (VG.Proof.Bignum.X86_64.word t₂.mem B (VG.Proof.Bignum.X86_64.slot w aM) - (VG.Proof.Bignum.X86_64.word t₂.mem B (VG.Proof.Bignum.X86_64.slot w aM) &&& 1))).writeW
        (VG.Proof.Bignum.X86_64.off B (8 * sC2)) (VG.Proof.Bignum.X86_64.mask (decide ((VG.Proof.Bignum.X86_64.word t₂.mem B (VG.Proof.Bignum.X86_64.slot w aM)).toNat % 2 = 0)))) (by
      xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, at0, hdi₂, hdrOff, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        hs₂.ld (d := VG.Proof.Bignum.X86_64.slot w aM) (by omega), hs₂.st (d := VG.Proof.Bignum.X86_64.slot w aM) (by omega), hl _ (show sW < 32 by decide),
        hl _ (show Impl.Bignum.X86_64.Public.sElen < 32 by decide), hW, hE, VG.Proof.Rsa.X86_64.bw_val w el hel',
        hs₂.st (d := 8 * sC2) (by omega)]
      rw [VG.Proof.Rsa.X86_64.low_sub_one]) rfl)
    fun t ⟨⟨hbp, h12, mt⟩, k₃⟩ => ⟨(k₃.gpr (by decide)).trans hbx, hbp, h12, (k₃.gpr (by decide)).trans hdi₂,
      by rw [mt, m₂, m₁], (k12.trans k₃).mono (by simp)⟩

/-- The loop of `orBody`: `rbp = 0` iff the `N` words at `rbx` are. -/
theorem orLoop_ok {s : State} {B : Addr} {Z N e : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hbx : s.gpr .rbx = VG.Proof.Bignum.X86_64.off B e)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 N) (hbp : s.gpr .rbp = 0) (hN1 : 1 ≤ N) (hN : N < 2 ^ 31)
    (he : e + 8 * N ≤ Z) :
    WP isa (wordLoop 0 orBody) s fun t =>
      (t.gpr .rbp = 0 ↔ wv s.mem B e N = 0) ∧ t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s t → t.cf = s.cf →
      OrInv s B Z (fun j => True ∧ ∀ i < j, VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * i) = 0) 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), hm, h14, by
      rw [(k.gpr (by decide) : t.gpr .rbp = s.gpr .rbp), hbp]
      exact ⟨fun _ => ⟨trivial, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, fun _ => rfl⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN _ h0
    (fun j _ hj t hI => orStep_ok hbx h12 (by omega) he hj hI)) fun t hI => ?_
  refine ⟨?_, hI.mem, hI.keep⟩
  rw [hI.val, wv_eq_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

/-- `skipTest`: `ZF` set iff `m = 0` or `M` is even. -/
theorem skipTest_ok {s : State} {B : Addr} {Z : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z)
    {z : Prop} [Decidable z] (hz : s.gpr .rbp = 0 ↔ z) {c : Bool} (hm : VG.Proof.Bignum.X86_64.word s.mem B (8 * sC2) = VG.Proof.Bignum.X86_64.mask c) :
    WP isa (.block skipTest) s fun t =>
      t.zf = some (decide (¬ z ∧ c = false)) ∧ t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rbp] s t := by
  have hn := hs.nowrap
  have e : decide (s.gpr .rbp = 0) = decide z := by
    by_cases hz' : z
    · rw [decide_eq_true hz', decide_eq_true (hz.mpr hz')]
    · rw [decide_eq_false hz', decide_eq_false (fun h => hz' (hz.mp h))]
  unfold skipTest
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.zf = some (decide (¬ z ∧ c = false)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩
  xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, hdrOff, hs.ld (d := 8 * sC2) (by simp only [sC2, sFn]; omega), hm, VG.Proof.Rsa.X86_64.decide_lt_one', e]
  rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide z))) = VG.Proof.Bignum.X86_64.mask (decide z) from rfl, BitVec.and_self]
  by_cases hz' : z <;> cases c <;> simp [hz'] <;> decide

/-- `M` with its low bit cleared: `M - M mod 2`. -/
theorem clearLow_wv (m : Mem) (B : Addr) {e n : Nat} (hn : 1 ≤ n) (hen : B.toNat + e + 8 * n ≤ 2 ^ 64) :
    wv (m.writeW (VG.Proof.Bignum.X86_64.off B e) (VG.Proof.Bignum.X86_64.word m B e - (VG.Proof.Bignum.X86_64.word m B e &&& 1))) B e n = wv m B e n - wv m B e n % 2 := by
  have o := VG.Proof.Bignum.X86_64.writeW_outside m B (VG.Proof.Bignum.X86_64.word m B e - (VG.Proof.Bignum.X86_64.word m B e &&& 1)) (d := e) (by omega)
  rw [VG.Proof.Rsa.X86_64.wv_low hn, VG.Proof.Rsa.X86_64.wv_low (m := m) hn, VG.Proof.Bignum.X86_64.word_writeW_self, VG.Proof.Rsa.X86_64.sub_low, o.wv (Or.inr (by omega)) (by omega)]
  have := (VG.Proof.Bignum.X86_64.word m B e).isLt
  omega

/-- The test of `skip`: `ZF` clear iff `M` is odd and above 1; then `M`'s
array holds `m = M - 1`. -/
theorem skip_ok {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.X86_64.Ws s B Z w) {el : Nat}
    (hel : VG.Proof.Bignum.X86_64.word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (he1 : 1 ≤ el)
    (he2 : el ≤ 8 * w)
    (hM : wv s.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) < 2 ^ (64 * (w + (el + 7) / 8))) :
    WP isa (seqs [.block skipBlk, wordLoop 0 orBody, .block skipTest]) s fun t =>
      t.zf = some (decide (wv s.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) % 2 = 1 ∧ 2 ≤ wv s.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)))) ∧
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) =
        wv s.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) - wv s.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) % 2 ∧
      Frm B [(VG.Proof.Bignum.X86_64.slot w aM, 8), (8 * sC2, 8)] s.mem t.mem ∧ t.gpr .rdi = B ∧
      VG.Proof.MlKem.X86_64.Keep [.r12, .r9, .rbx, .rax, .rdx, .rcx, .rbp, .r14] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have sM := VG.Proof.Rsa.X86_64.slot_lt (w := w) (show aM + 1 < 16 by decide)
  have hZ := h.hZ
  have eM1 : VG.Proof.Bignum.X86_64.slot w (aM + 1) = VG.Proof.Bignum.X86_64.slot w aM + 8 * (w + 2) := by simp only [VG.Proof.Bignum.X86_64.slot, hdrBytes, aM]; omega
  have hM0 := hdr_lt_slot w aM (show sC2 < 32 by decide)
  have hw1 := h.w1
  have hw2 := h.w2
  have sMM : VG.Proof.Bignum.X86_64.slot w aM + 16 * (w + 2) ≤ Z := by rw [eM1] at sM; omega
  simp only [seqs]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.skipBlk_ok h hel (by omega)) fun s₁ ⟨hbx, hbp, h12, hdi, m₁, k₁⟩ => ?_)
  have hs₁ := h.scr.congr k₁.2.2
  -- `m` in `M`'s arrays, and `M`'s parity in `sC2`.
  have o₂ := VG.Proof.Bignum.X86_64.writeW_outside (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aM)) (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aM) -
    (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aM) &&& 1))) B (VG.Proof.Bignum.X86_64.mask (decide ((VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aM)).toNat % 2 = 0))) (d := 8 * sC2)
    (by omega)
  have hm : wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) =
      wv s.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) - wv s.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) % 2 := by
    rw [m₁, o₂.wv (Or.inr (by omega)) (by omega), VG.Proof.Rsa.X86_64.clearLow_wv _ _ (by omega) (by omega)]
  have hpar : (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aM)).toNat % 2 = wv s.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) % 2 := by
    rw [VG.Proof.Rsa.X86_64.wv_low (show 1 ≤ 2 * (w + 2) by omega)]; omega
  have hc : VG.Proof.Bignum.X86_64.word s₁.mem B (8 * sC2) = VG.Proof.Bignum.X86_64.mask (decide (wv s.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) % 2 = 0)) := by
    rw [m₁, VG.Proof.Bignum.X86_64.word_writeW_self, hpar]
  -- `m = 0`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.orLoop_ok hs₁ hbx h12 hbp (by omega) (by have := h.w2; omega)
    (by omega)) fun s₂ ⟨hz, m₂, k₂⟩ => ?_)
  have hlt : wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) < 2 ^ (64 * (w + (el + 7) / 8)) := by rw [hm]; omega
  rw [VG.Proof.Rsa.X86_64.wv_low_of_lt (by omega) hlt, hm] at hz
  refine WP.mono (VG.Proof.Rsa.X86_64.skipTest_ok (hs₁.congr k₂.2.2) ((k₂.gpr (by decide)).trans hdi) h256 hz
    (c := decide (wv s.mem B (VG.Proof.Bignum.X86_64.slot w aM) (2 * (w + 2)) % 2 = 0)) (by rw [m₂]; exact hc)) fun t ⟨hzf, mt, k₃⟩ => ⟨?_, by rw [mt, m₂, hm], ?_,
      (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hdi), ((k₁.trans k₂).trans k₃).mono (by simp)⟩
  · rw [hzf]
    congr 1
    simp only [decide_eq_decide, decide_eq_false_iff_not]
    omega
  · intro x hx
    have a := hx (VG.Proof.Bignum.X86_64.slot w aM, 8) (by simp)
    have b := hx (8 * sC2, 8) (by simp)
    dsimp only at a b
    rw [mt, m₂, m₁, o₂ x b, VG.Proof.Bignum.X86_64.writeW_outside s.mem B _ (d := VG.Proof.Bignum.X86_64.slot w aM) (by omega) x a]

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.TTest`. -/
section

namespace VG.Proof.Rsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
example : RelCT isa (Two (fun (_ : Unit) (_ : State) => False)) (.seq (.block (base aU .r8 ++ [.mov .r11 (.reg .r12)] ++ List.replicate 6 (.alu .add .r11 (.reg .r11)) ++
    [.mov32 .r13 (.imm 0)])) (.seq zeroAccLoop (.loop (VG.Impl.Rsa.X86_64.Keys.divStep aU aV aP aT) .ne))) fun _ _ => True :=
  two_taint [.rdi, .r12, .r9] (fun _ _ _ h => h.elim) (by taint_decide)
example : RelCT isa (Two (fun (_ : Unit) (_ : State) => False)) (.seq (.block ([.mov .r11 (.reg .r12)] ++ List.replicate 7 (.alu .add .r11 (.reg .r11)) ++ [.mov32 .r13 (.imm 0)]))
   (.loop (VG.Impl.Rsa.X86_64.Keys.invStep aU aV aX₁ aX₂ aP aT) .ne)) fun _ _ => True :=
  two_taint [.rdi, .r12, .r9] (fun _ _ _ h => h.elim) (by taint_decide)
end VG.Proof.Rsa.X86_64

end
