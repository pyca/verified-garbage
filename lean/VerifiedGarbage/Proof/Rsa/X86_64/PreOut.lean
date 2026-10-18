module

public import VerifiedGarbage.Proof.Rsa.X86_64.PreSteps
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_precompute` on x86-64: the words to `pre`

`maskWords` copies `n` words from `rsi` to `rbx`, each and'ed with `rbp`
(`maskWords_ok`), and `failZ`'s loop writes `n` zeros to `rbx`
(`zeroWords_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.PrivPre
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- After `j` masked words from `S + eS` to `D + eD`. -/
structure MaskInv (s₀ : State) (S D : Addr) (eS eD : Nat) (mk : BitVec 64) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  done : ∀ i < j, Bignum.word t.mem D (eD + 8 * i) = Bignum.word s₀.mem S (eS + 8 * i) &&& mk
  frame : Outside D eD (8 * j) s₀.mem t.mem

theorem maskStep_ok {s₀ : State} {S D : Addr} {eS eD n : Nat} {mk : BitVec 64}
    (hsi : s₀.gpr .rsi = off S eS) (hbx : s₀.gpr .rbx = off D eD) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 n)
    (hbp : s₀.gpr .rbp = mk) (hn : n < 2 ^ 32) (hD : eD + 8 * n ≤ 2 ^ 64)
    (hrd : ∀ j < n, InRegions (s₀.rd ++ s₀.wr) (off S (eS + 8 * j)) 8)
    (hwr : ∀ j < n, InRegions s₀.wr (off D (eD + 8 * j)) 8)
    (hsep : ∀ j < n, ∀ b < 8, ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * n ≤ ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b))
    {j : Nat} (hj : j < n) {t : State} (hI : MaskInv s₀ S D eS eD mk j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rsi .r14)), .alu .and .rax (.reg .rbp), .store (ix .rbx .r14) .rax] :
        List Instr) ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = n)) ∧ MaskInv s₀ S D eS eD mk (j + 1) t' := by
  have tsi : t.gpr .rsi = off S eS := (hI.keep.gpr (by decide)).trans hsi
  have tbx : t.gpr .rbx = off D eD := (hI.keep.gpr (by decide)).trans hbx
  have tbp : t.gpr .rbp = mk := (hI.keep.gpr (by decide)).trans hbp
  have t12 : t.gpr .r12 = BitVec.ofNat 64 n := (hI.keep.gpr (by decide)).trans h12
  have hld : InRegions (t.rd ++ t.wr) (off S (eS + 8 * j)) 8 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd j hj
  have hst : InRegions t.wr (off D (eD + 8 * j)) 8 := by rw [hI.keep.2.2]; exact hwr j hj
  have hv : Bignum.word t.mem S (eS + 8 * j) = Bignum.word s₀.mem S (eS + 8 * j) :=
    Mem.readW_congr fun b hb => hI.frame _ (by have := hsep j hj b hb; omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off D (eD + 8 * j)) (Bignum.word s₀.mem S (eS + 8 * j) &&& mk)) ?_ rfl)
    fun t₁ ⟨hm, k₁⟩ => ?_
  · xrun [State.ea, ix, addr0 tsi hI.r14, addr0 tbx hI.r14, hld, hst, hv, tbp]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 n := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨((hI.keep.trans k₁).trans k').mono (by decide), h14, fun i hi => ?_, ?_⟩
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [(writeW_outside t.mem D _ (by omega)).word (by omega) (by omega)]; exact hI.done i hi
    · exact word_writeW_self _ _ _ _
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem D _ (by omega) x (by omega)]
    exact hI.frame x (by omega)

/-- `maskWords`: the `n` words at `S + eS`, and'ed with `rbp`, to `D + eD`,
which they do not overlap, changing only those. -/
theorem maskWords_ok {s : State} {S D : Addr} {eS eD n : Nat} {mk : BitVec 64}
    (hsi : s.gpr .rsi = off S eS) (hbx : s.gpr .rbx = off D eD) (h12 : s.gpr .r12 = BitVec.ofNat 64 n)
    (hbp : s.gpr .rbp = mk) (hn : 1 ≤ n) (hn' : n < 2 ^ 31) (hD : eD + 8 * n ≤ 2 ^ 64)
    (hrd : ∀ j < n, InRegions (s.rd ++ s.wr) (off S (eS + 8 * j)) 8)
    (hwr : ∀ j < n, InRegions s.wr (off D (eD + 8 * j)) 8)
    (hsep : ∀ j < n, ∀ b < 8, ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * n ≤ ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b)) :
    WP isa maskWords s fun t =>
      (∀ i < n, Bignum.word t.mem D (eD + 8 * i) = Bignum.word s.mem S (eS + 8 * i) &&& mk) ∧
      Outside D eD (8 * n) s.mem t.mem ∧ Keep [.rax, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      MaskInv s S D eS eD mk 0 t := fun t h14 hm k _ =>
    ⟨k.mono (by decide), h14, fun i hi => absurd hi (Nat.not_lt_zero _),
      by rw [hm]; exact Outside.refl _ _ _ _⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := n) (by omega) hn' (MaskInv s S D eS eD mk) h0
    (fun j _ hj t hI => maskStep_ok hsi hbx h12 hbp (by omega) hD hrd hwr hsep hj hI)) fun t hI => ?_
  exact ⟨hI.done, hI.frame, hI.keep⟩

/-- After `j` zeros to `D + eD`. -/
structure ZeroInv (s₀ : State) (D : Addr) (eD : Nat) (j : Nat) (t : State) : Prop where
  keep : Keep [.r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  done : ∀ i < j, Bignum.word t.mem D (eD + 8 * i) = 0
  frame : Outside D eD (8 * j) s₀.mem t.mem

/-- `failZ`'s loop: `n` zeros to `D + eD`, changing only those. -/
theorem zeroWords_ok {s : State} {D : Addr} {eD n : Nat}
    (hbx : s.gpr .rbx = off D eD) (h12 : s.gpr .r12 = BitVec.ofNat 64 n) (hax : s.gpr .rax = 0)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 31) (hD : eD + 8 * n ≤ 2 ^ 64)
    (hwr : ∀ j < n, InRegions s.wr (off D (eD + 8 * j)) 8) :
    WP isa (wordLoop 0 [.store (ix .rbx .r14) .rax]) s fun t =>
      (∀ i < n, Bignum.word t.mem D (eD + 8 * i) = 0) ∧ Outside D eD (8 * n) s.mem t.mem ∧ Keep [.r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      ZeroInv s D eD 0 t := fun t h14 hm k _ =>
    ⟨k, h14, fun i hi => absurd hi (Nat.not_lt_zero _), by rw [hm]; exact Outside.refl _ _ _ _⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := n) (by omega) hn' (ZeroInv s D eD) h0
    (fun j _ hj t hI => ?_)) fun t hI => ⟨hI.done, hI.frame, hI.keep⟩
  have tbx : t.gpr .rbx = off D eD := (hI.keep.gpr (by decide)).trans hbx
  have tax : t.gpr .rax = 0 := (hI.keep.gpr (by decide)).trans hax
  have t12 : t.gpr .r12 = BitVec.ofNat 64 n := (hI.keep.gpr (by decide)).trans h12
  have hst : InRegions t.wr (off D (eD + 8 * j)) 8 := by rw [hI.keep.2.2]; exact hwr j hj
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [] (Q := fun t₁ => t₁.mem = t.mem.writeW (off D (eD + 8 * j)) (0 : BitVec 64))
    (by xrun [State.ea, ix, addr0 tbx hI.r14, hst, tax]) rfl) fun t₁ ⟨hm, k₁⟩ => ?_
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 n := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨((hI.keep.trans k₁).trans k').mono (by decide), h14, fun i hi => ?_, ?_⟩
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [(writeW_outside t.mem D _ (by omega)).word (by omega) (by omega)]; exact hI.done i hi
    · exact word_writeW_self _ _ _ _
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem D _ (by omega) x (by omega)]
    exact hI.frame x (by omega)

end VG.Proof.Rsa.X86_64.Key
