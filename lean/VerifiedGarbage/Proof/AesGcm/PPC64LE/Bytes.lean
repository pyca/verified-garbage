module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE
public import VerifiedGarbage.Proof.Gather.PPC64LE.Copy
public import VerifiedGarbage.Proof.AesGcm.Bytes
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# AES-GCM on PPC64LE: bytes

Untrusted: everything here is checked by Lean. `xorBytes` XORs `n ≥ 1`
bytes at `S` into those at `D` (`xorBytes_wp`), as the gathering's
`copyBytes` copies them (`Proof/Gather/PPC64LE/Copy.lean`), and `minLen`
computes `min(16 - o, n)` (`minLen_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.WriteBytes VG.Proof.Gather.PPC64LE
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_lbz wp_stb wp_addi wp_subi wp_lsr wp_li wp_xor wp_sub
  wp_or)
open VG.Spec.Aes (bytesAt)

/-- `mov d, n` (`or d, n, n`). -/
theorem wp_mv {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n) → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.AesCbc.PPC64LE.mov d n :: is)) s Q :=
  wp_or fun s' u => k s' (by simpa only [BitVec.or_self] using u)

/-- `ldbrx`-style loads and stores (`lwbrx`, `stwbrx`, `stdbrx`). -/
theorem wp_lwbrx {is : List Instr} {s : State} {Q : State → Prop} {t a b : Reg} {ea : Addr}
    (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea) (hin : InRegions (s.rd ++ s.wr) ea 4)
    (k : ∀ s', Upd s s' t ((rev32 (s.mem.readW ea 32)).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.loadRev .w t a b :: is)) s Q := by
  refine VG.Proof.ChaCha20Poly1305.PPC64LE.WP.cons
    (s' := s.write t ((rev32 (s.mem.readW ea 32)).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_loadRev_w hn (by rw [hea]; exact hin), hea]

theorem wp_stwbrx {is : List Instr} {s : State} {Q : State → Prop} {t a b : Reg} {ea : Addr}
    (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea) (hout : InRegions s.wr ea 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW ea (rev32 ((s.gpr t).setWidth 32))) → WP isa (.block is) s' Q) :
    WP isa (.block (.storeRev .w t a b :: is)) s Q := by
  refine VG.Proof.ChaCha20Poly1305.PPC64LE.WP.cons
    (s' := { s with mem := s.mem.writeW ea (rev32 ((s.gpr t).setWidth 32)) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_storeRev_w hn (by rw [hea]; exact hout), hea]

theorem wp_stdbrx {is : List Instr} {s : State} {Q : State → Prop} {t a b : Reg} {ea : Addr}
    (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea) (hout : InRegions s.wr ea 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW ea (rev64 (s.gpr t))) → WP isa (.block is) s' Q) :
    WP isa (.block (.storeRev .d t a b :: is)) s Q := by
  refine VG.Proof.ChaCha20Poly1305.PPC64LE.WP.cons
    (s' := { s with mem := s.mem.writeW ea (rev64 (s.gpr t)) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_storeRev_d hn (by rw [hea]; exact hout), hea]

/-! ## XORing bytes -/

/-- What the XOR loop needs: `n ≥ 1` bytes at `S` to XOR into those at `D`, apart. -/
structure XorPre (s : State) (S D : Addr) (n : Nat) : Prop where
  r3 : s.gpr .r3 = S
  r9 : s.gpr .r9 = D
  r4 : s.gpr .r4 = BitVec.ofNat 64 n
  pos : 1 ≤ n
  lt : n < 2 ^ 64
  rd : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, n⟩] s.wr
  disj : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

/-- The bytes `d` XORed with `k`, byte by byte. -/
abbrev xorL (d k : List Byte) : List Byte := List.zipWith (· ^^^ ·) d k

theorem xor_byte (a b : Byte) : ((a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 : Byte) = b ^^^ a := by
  rw [BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le _ (by decide),
    BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.xor_comm]

theorem xorBytes_wp (s : State) {S D : Addr} {n : Nat} (h : XorPre s S D n) :
    WP isa xorBytes s fun s' =>
      s'.mem = writeBytes s.mem D (xorL (bytesAt s.mem D n) (bytesAt s.mem S n)) ∧
      s'.gpr .r9 = D + BitVec.ofNat 64 n ∧ Keeps s s' := by
  have hL := h.lt
  refine WP.loop (M := isa)
    (fun (w : Nat) (t : State) => ∃ i, w = n - i ∧ i < n ∧ t.gpr .r3 = S + BitVec.ofNat 64 i ∧
      t.gpr .r9 = D + BitVec.ofNat 64 i ∧ t.gpr .r4 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem D (xorL (bytesAt s.mem D i) (bytesAt s.mem S i)) ∧ Keeps s t) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.r3]; exact (BitVec.add_zero _).symm, by rw [h.r9]; exact (BitVec.add_zero _).symm,
      by rw [h.r4, Nat.sub_zero], by simp [bytesAt, writeBytes_nil], Keeps.refl s⟩
  rintro w t ⟨i, rfl, hi, r3, r9, r4, mem, kp⟩
  have hin : i + 1 ≤ n := by omega
  have hlen : (xorL (bytesAt s.mem D i) (bytesAt s.mem S i)).length = i := by
    simp [length_bytesAt]
  refine wp_lbz (a := S + BitVec.ofNat 64 i) (by decide) (by decide)
    (by rw [r3]; exact BitVec.add_zero _) (by rw [kp.rd, kp.wr]; exact in_off h.rd hin (by omega))
    fun t₁ u₁ => ?_
  refine wp_lbz (a := D + BitVec.ofNat 64 i) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), r9]; exact BitVec.add_zero _)
    (by rw [u₁.rd, u₁.wr, kp.rd, kp.wr]; exact in_off (VG.Covers.right h.wr) hin (by omega))
    fun t₂ u₂ => ?_
  refine wp_xor fun t₃ u₃ => ?_
  refine wp_stb (a := D + BitVec.ofNat 64 i) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), r9];
        exact BitVec.add_zero _)
    (by rw [u₃.wr, u₂.wr, u₁.wr, kp.wr]; exact in_off h.wr hin (by omega)) fun t₄ u₄ => ?_
  refine wp_addi (by decide) (by decide) fun t₅ u₅ => wp_addi (by decide) (by decide) fun t₆ u₆ =>
    wp_subi (by decide) (by decide) fun t₇ u₇ => WP.block_nil ?_
  have kp₇ : Keeps s t₇ := kp.trans ((kU u₁).trans ((kU u₂).trans ((kU u₃).trans ((kM u₄).trans
    ((kU u₅).trans ((kU u₆).trans (kU u₇)))))))
  -- The bytes read are what they were.
  have hS : t.mem (S + BitVec.ofNat 64 i) = s.mem (S + BitVec.ofNat 64 i) := by
    rw [mem]
    refine (writeBytes_frame s.mem D _ (R := ⟨D, i⟩) (by rw [hlen]; exact Region.contains_self _ _))
      _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact h.disj _ (Offset.contains_base S (show i + 1 ≤ n by omega) (by omega))
      (Region.sub_prefix (show i ≤ n by omega) _ hc)
  have hD : t.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := by
    rw [mem]
    refine (writeBytes_frame s.mem D _ (R := ⟨D, i⟩) (by rw [hlen]; exact Region.contains_self _ _))
      _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at hc
    rw [Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)] at hc
    omega
  have hmem : t₇.mem = writeBytes s.mem D (xorL (bytesAt s.mem D (i + 1)) (bytesAt s.mem S (i + 1))) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.other .r0 (by decide),
      u₁.gpr, u₂.mem, u₁.mem, xor_byte, hS, hD, mem, Proof.Cmac.Stream.bytesAt_append,
      Proof.Cmac.Stream.bytesAt_append, xorL, xorL, List.zipWith_append (by simp [length_bytesAt]),
      bytesAt_one, bytesAt_one, List.zipWith_cons_cons, List.zipWith_nil_left,
      writeBytes_snoc _ _ _ _ (by rw [hlen]; omega), hlen]
  have hstep (P : Addr) : P + BitVec.ofNat 64 i + BitVec.ofNat 64 1 = P + BitVec.ofNat 64 (i + 1) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have r3' : t₇.gpr .r3 = S + BitVec.ofNat 64 (i + 1) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), r3, hstep]
  have r9' : t₇.gpr .r9 = D + BitVec.ofNat 64 (i + 1) := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), r9, hstep]
  have r4' : t₇.gpr .r4 = BitVec.ofNat 64 (n - (i + 1)) := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), r4, ofNat_sub_one (by omega), Nat.sub_sub]
  have ev := eval_nonzero (r := .r4) (a := n - (i + 1)) r4' (by omega)
  by_cases he : i + 1 = n
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [r9', he], kp₇⟩
  · right
    exact ⟨by rw [ev]; simp; omega, n - (i + 1), by omega, i + 1, rfl, by omega, r3', r9', r4', hmem, kp₇⟩

/-! ## `min(16 - o, n)` -/

theorem ofNat_lsr4 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- The sign of `a - b`, for `a` and `b` below `2⁶³`. -/
theorem sub_sign {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = BitVec.ofNat 64 (if a < b then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := b) (by omega), Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  split <;> rename_i h
  · rw [Nat.mod_eq_of_lt (show 2 ^ 64 - b + a < 2 ^ 64 by omega),
      Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
  · rw [show 2 ^ 64 - b + a = (a - b) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
      Nat.div_eq_of_lt (by omega)]

theorem ofNat_sub_ofNat' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := a) ha, Nat.mod_eq_of_lt (a := a - b) (by omega)]
  omega

/-- `minLen`: `r4 = min(16 - o, n)` for `1 ≤ o ≤ 15` in `r20` and `n` in `r19`;
only `r4` and `r5` change. -/
theorem minLen_wp (s : State) {o n : Nat} (r20 : s.gpr .r20 = BitVec.ofNat 64 o)
    (r19 : s.gpr .r19 = BitVec.ofNat 64 n) (ho : 1 ≤ o ∧ o ≤ 15) (hn : n < 2 ^ 64) :
    WP isa minLen s fun s' => s'.gpr .r4 = BitVec.ofNat 64 (min (16 - o) n) ∧ s'.mem = s.mem ∧
      Keeps s s' := by
  unfold minLen
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_lsr (by decide) fun s₃ u₃ =>
    WP.block_nil ?_)
  have kp₃ : Keeps s s₃ := (kU u₁).trans ((kU u₂).trans (kU u₃))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have r4₃ : s₃.gpr .r4 = BitVec.ofNat 64 (16 - o) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), r20,
      ofNat_sub_ofNat' (by omega) (by decide)]
  have r19₃ : s₃.gpr .r19 = BitVec.ofNat 64 n := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), r19]
  have r5₃ : s₃.gpr .r5 = BitVec.ofNat 64 (n / 16) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r19, ofNat_lsr4 hn]
  refine WP.ite (decide (n / 16 = 0)) (eval_zero r5₃ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n < 16 := by have := of_decide_eq_true ht; omega
    refine WP.seq (wp_sub fun s₄ u₄ => wp_lsr (by decide) fun s₅ u₅ => WP.block_nil ?_)
    have kp₅ : Keeps s s₅ := kp₃.trans ((kU u₄).trans (kU u₅))
    have r5₅ : s₅.gpr .r5 = BitVec.ofNat 64 (if n < 16 - o then 1 else 0) := by
      rw [u₅.gpr, u₄.gpr, r19₃, r4₃, sub_sign (by omega) (by omega)]
    have r4₅ : s₅.gpr .r4 = BitVec.ofNat 64 (16 - o) := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), r4₃]
    have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, m₃]
    by_cases hlt : n < 16 - o
    · have r5' : s₅.gpr .r5 = BitVec.ofNat 64 1 := by rw [r5₅]; simp only [hlt, ↓reduceIte]
      refine WP.ite false (by rw [eval_zero r5' (by decide)]; rfl) (fun h => absurd h (by decide))
        (fun _ => ?_)
      refine wp_mv fun s₆ u₆ => WP.block_nil ⟨?_, by rw [u₆.mem, m₅], kp₅.trans (kU u₆)⟩
      rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), r19₃, Nat.min_eq_right (by omega)]
    · have r5' : s₅.gpr .r5 = BitVec.ofNat 64 0 := by rw [r5₅]; simp only [hlt, ↓reduceIte]
      refine WP.ite true (by rw [eval_zero r5' (by decide)]; rfl) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact WP.block_nil ⟨by rw [r4₅, Nat.min_eq_left (by omega)], m₅, kp₅⟩
  · have h0 : 16 ≤ n := by have := of_decide_eq_false hf; omega
    exact WP.block_nil ⟨by rw [r4₃, Nat.min_eq_left (by omega)], m₃, kp₃⟩

end VG.Proof.AesGcm.PPC64LE
