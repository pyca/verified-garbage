module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightTriChain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMath

/-! # The row-wise triangle of an eight-limb square: a row

Row `j` (`1 ≤ j ≤ 7`) adds `a_j (a_0 + … + a_{j-1} 2^(64(j-1)))` to the
words `j … 2j - 2` held in the accumulators (`win`), leaving the words
`j … 2j`, and stores word `j`. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.SquareEight

/-- The `n` words from word `j` held in the accumulators. -/
def win (s : State) (j n : Nat) : Nat := regVal s (fun i => acc (j + i)) n

theorem acc_mem (k : Nat) : acc k ∈ accs := by
  have h : ∀ i < 8, accs[i]! ∈ accs := by decide
  exact h _ (Nat.mod_lt _ (by decide))

theorem acc_inj {k k' : Nat} (h : acc k = acc k') (h1 : k ≤ k') (h2 : k' < k + 8) : k = k' := by
  have hd : ∀ a < 8, ∀ b < 8, accs[a]! = accs[b]! → a = b := by decide
  have := hd _ (Nat.mod_lt k (by decide)) _ (Nat.mod_lt k' (by decide)) h
  omega

theorem acc_ne_tmp (k : Nat) : acc k ≠ tmp := fun h => by
  have := acc_mem k; rw [h] at this; exact absurd this (by decide)

theorem inp_not_work : ∀ i < 8, inp i ∉ work := by decide

theorem x7_not_work : Reg.x7 ∉ work := by decide
theorem x16_not_work : Reg.x16 ∉ work := by decide

theorem value_succ_left (r : Nat) (f : Nat → Nat) (n : Nat) :
    Square.value r f (n + 1) = f 0 + r * Square.value r (fun i => f (i + 1)) n := by
  induction n with
  | zero => simp [Square.value]
  | succ n ih =>
    rw [Square.value, ih, Square.value, Nat.pow_succ]
    grind

theorem halves_value (s : State) (x : Reg) (Y : Nat → Reg) (n : Nat) :
    halfVal s false x Y n + 2 ^ 64 * halfVal s true x Y n = (s.gpr x).toNat * regVal s Y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := half_value (s.gpr x) (s.gpr (Y n))
    simp only [halfVal, regVal, Square.value] at ih h ⊢
    grind

theorem carryWord_ok (s : State) (r : Reg) (h7 : s.gpr .x7 = 0) :
    WP isa (.block [.adc .x r .x7 .x7]) s fun t =>
      (t.gpr r = BitVec.ofNat 64 s.c.toNat ∧ t.mem = s.mem) ∧ Keep [r] s t := by
  refine WP.keep [r] ?_ (by simp [writesOnly, Code.allInstrs, dsts, dstOf, Option.toList]) rfl rfl
  brun [h7]
  simp

theorem addr_word8 (s : State) (n : Reg) {j : Nat} (hj : j < 4096) :
    addr s 8 n (8 * j) = some (s.gpr n + BitVec.ofNat 64 (8 * j)) := by
  simp only [addr]
  rw [ite_eq_left ⟨by omega, by omega⟩]

theorem storeWord_ok {s : State} {B : Addr} {Z e : Nat} (r : Reg) (j : Nat)
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e) (he : e + 8 * j + 8 ≤ Z) (hj : j < 4096) :
    WP isa (.block [st r .x16 (8 * j)]) s fun t =>
      (t.mem = s.mem.writeW (off B (e + 8 * j)) (s.gpr r)) ∧ Keep [] s t := by
  refine WP.keep [] ?_ rfl rfl rfl
  have ho : 8 * j % 8 = 0 ∧ 8 * j < 32768 := ⟨by omega, by omega⟩
  brun [h16, hs.st he, ho]

theorem regVal_ext {s t : State} {R R' : Nat → Reg} {n : Nat}
    (h : ∀ i < n, s.gpr (R i) = t.gpr (R' i)) : regVal s R n = regVal t R' n :=
  BlockedRedc.value_congr fun i hi => congrArg BitVec.toNat (h i hi)

theorem acc_inj' {a b : Nat} (h : acc a = acc b) (h1 : a < b + 8) (h2 : b < a + 8) : a = b := by
  rcases Nat.le_total a b with hab | hab
  · exact acc_inj h hab (by omega)
  · exact (acc_inj h.symm hab (by omega)).symm

theorem acc_ne_x7 (k : Nat) : acc k ≠ .x7 := fun h => by
  have := acc_mem k; rw [h] at this; exact absurd this (by decide)

theorem win_succ (s : State) (j n : Nat) :
    win s j (n + 1) = win s j n + (s.gpr (acc (j + n))).toNat * (2 ^ 64) ^ n := rfl

/-- A window splits into its first word and the window after it. -/
theorem win_split (s : State) (j n : Nat) :
    win s j (n + 1) = (s.gpr (acc j)).toNat + 2 ^ 64 * win s (j + 1) n := by
  unfold win regVal
  rw [value_succ_left]
  simp only [Nat.add_zero]
  congr 2
  exact BlockedRedc.value_congr fun i _ => by rw [show j + (i + 1) = j + 1 + i by omega]

private theorem row_arith {W L H Vb Vc bj winb winc cc aval P : Nat}
    (h1 : winb = W + L) (h2 : winb = bj + 2 ^ 64 * Vb) (h3 : Vc + P * cc = Vb + H)
    (h4 : winc = bj + 2 ^ 64 * Vc) (h5 : L + 2 ^ 64 * H = aval) (hb : W + aval < 2 ^ 64 * P)
    (hc : cc ≤ 1) : winc = W + aval := by
  rcases (by omega : cc = 0 ∨ cc = 1) with rfl | rfl
  · omega
  · omega

theorem triRow_ok {s : State} {B : Addr} {Z eT j : Nat} (hj1 : 1 ≤ j) (hj7 : j ≤ 7)
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 8 * j + 8 ≤ Z)
    (h7 : s.gpr .x7 = 0)
    (hb : win s j (j - 1) + (s.gpr (inp j)).toNat * regVal s inp j < 2 ^ (64 * (j + 1))) :
    WP isa (.block (row j)) s fun t =>
      (win t j (j + 1) = win s j (j - 1) + (s.gpr (inp j)).toNat * regVal s inp j ∧
        t.mem = s.mem.writeW (off B (eT + 8 * j)) (t.gpr (acc j))) ∧ Keep work s t := by
  unfold row low high
  rw [List.append_assoc, List.append_assoc]
  apply WP.block_append
  refine WP.mono (chain_ok false (inp j) inp (fun i => acc (j + i))
    (fun i => if i + 1 = j then .x7 else acc (j + i)) j s
    (fun i _ => acc_mem _) (inp_not_work j (by omega)) (fun k _ => inp_not_work k (by omega))
    (fun i _ k _ h => by have := acc_inj' h (by omega) (by omega); omega)
    (fun i hi => ⟨by split <;> [decide; exact acc_ne_tmp _], fun k hk => by
      split
      · exact acc_ne_x7 _
      · exact fun h => by have := acc_inj' h (by omega) (by omega); omega⟩))
    fun a ⟨⟨ha, hak, ham⟩, ka⟩ => ?_
  have h7a : a.gpr .x7 = 0 := (ka.gpr _ x7_not_work).trans h7
  apply WP.block_append
  refine WP.mono (carryWord_ok a (acc (2 * j)) h7a) fun b ⟨⟨hb2, hbm⟩, kb⟩ => ?_
  have kab := ka.trans kb
  have kabw : Keep work s b := kab.mono fun r hr => by
    rcases List.mem_append.mp hr with h | h
    · exact h
    · rw [List.mem_singleton.mp h]; exact List.mem_cons_of_mem _ (acc_mem _)
  -- the low halves, with the carry word
  have hlowS : regVal s (fun i => if i + 1 = j then .x7 else acc (j + i)) j = win s j (j - 1) := by
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    have e : regVal s (fun i => if i + 1 = n + 1 then .x7 else acc (n + 1 + i)) (n + 1) =
        regVal s (fun i => if i + 1 = n + 1 then .x7 else acc (n + 1 + i)) n +
          (s.gpr .x7).toNat * (2 ^ 64) ^ n := by
      simp only [regVal, Square.value, ↓reduceIte]
    rw [e, h7, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero,
      show n + 1 - 1 = n by omega]
    unfold win
    exact regVal_ext fun i hi => by simp only [show ¬ (i + 1 = n + 1) by omega, ↓reduceIte]
  have hj0 : j ≠ 0 := by omega
  have hcA : carryOf j a = a.c.toNat := by simp [carryOf, hj0]
  have hRb : regVal b (fun i => acc (j + i)) j = regVal a (fun i => acc (j + i)) j :=
    regVal_congr fun i hi => kb.gpr _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => by have := acc_inj' h (by omega) (by omega); omega)
  have hwinb : win b j (j + 1) = win s j (j - 1) + halfVal s false (inp j) inp j := by
    have e1 : win b j (j + 1) = regVal a (fun i => acc (j + i)) j + a.c.toNat * (2 ^ 64) ^ j := by
      rw [win_succ, show j + j = 2 * j by omega, hb2, show (BitVec.ofNat 64 a.c.toNat).toNat = a.c.toNat by
        cases a.c <;> rfl]
      unfold win
      rw [hRb]
    rw [e1, ← hlowS, ← ha, hcA, Nat.pow_mul, Nat.mul_comm (a.c.toNat)]
  -- the high halves
  apply WP.block_append
  refine WP.mono (chain_ok true (inp j) inp (fun i => acc (j + 1 + i)) (fun i => acc (j + 1 + i)) j b
    (fun i _ => acc_mem _) (inp_not_work j (by omega)) (fun k _ => inp_not_work k (by omega))
    (fun i _ k _ h => by have := acc_inj' h (by omega) (by omega); omega)
    (fun i hi => ⟨acc_ne_tmp _, fun k hk h => by have := acc_inj' h (by omega) (by omega); omega⟩))
    fun c ⟨⟨hc, hck, hcm⟩, kc⟩ => ?_
  have hcj : c.gpr (acc j) = b.gpr (acc j) :=
    hck _ (acc_ne_tmp _) fun i _ h => by have := acc_inj' h (by omega) (by omega); omega
  have hin : ∀ i < 8, b.gpr (inp i) = s.gpr (inp i) := fun i hi => kabw.gpr _ (inp_not_work i hi)
  have hhalf : halfVal b true (inp j) inp j = halfVal s true (inp j) inp j :=
    halfVal_congr (hin j (by omega)) fun i hi => hin i (by omega)
  have h16c : c.gpr .x16 = off B eT :=
    (kc.gpr _ x16_not_work).trans ((kabw.gpr _ x16_not_work).trans h16)
  refine WP.mono (storeWord_ok (c.gpr (acc j) |> fun _ => acc j) j (hs.congr (kc.wr.trans kabw.wr))
    h16c hT (by omega)) fun t ⟨htm, kt⟩ => ?_
  have hcc : c.c.toNat ≤ 1 := by cases c.c <;> decide
  have hcarry : carryOf j c = c.c.toNat := by simp [carryOf, hj0]
  have hwt : win t j (j + 1) = win c j (j + 1) := regVal_congr fun i _ => kt.gpr _ (by simp)
  refine ⟨⟨?_, ?_⟩, ((kabw.trans kc).trans kt).mono fun r hr => ?_⟩
  rotate_left 2
  · rcases List.mem_append.mp hr with h | h
    · rcases List.mem_append.mp h with h | h <;> exact h
    · exact absurd h List.not_mem_nil
  · rw [hwt]
    have h2 := win_split b j j
    have h4 := win_split c j j
    rw [hcj] at h4
    have h5 := halves_value s (inp j) inp j
    rw [hhalf, hcarry] at hc
    unfold win at h2 h4
    rw [show 2 ^ (64 * (j + 1)) = 2 ^ 64 * 2 ^ (64 * j) by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]] at hb
    exact row_arith hwinb (by unfold win at hwinb ⊢; exact h2) hc h4 h5 hb hcc
  · rw [htm, hcm, hbm, ham, kt.gpr _ (by simp)]

end VG.Proof.Bignum.AArch64.SquareEight
