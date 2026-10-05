import VerifiedGarbage.Proof.Rsa.X86_64.PrivPd

/-!
# `vg_rsa_private_checked` on x86-64: the check and the release

After the calls, `out` (which `vg_rsa_public_precomputed_checked` wrote) is
compared with the input without branches (`cmpLoop_ok`), and `M` is
released to `out` under the mask of `r₁ = r₂ = r₃ = 1` and their equality,
and zeroed (`releaseLoop_ok`), whatever `M` and `out` hold (`tail_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.WriteBytes (writeW8_apply)

theorem ea_at10 (t : State) {b : Reg} {p : Addr} {j : Nat} (hb : t.gpr b = p)
    (hi : t.gpr .r10 = BitVec.ofNat 64 j) : t.ea (at10 b) = p + BitVec.ofNat 64 j := by
  simp only [State.ea, at10, hb, hi, BitVec.mul_one, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]

theorem ea_mByte (t : State) {S : Addr} {j : Nat} (hb : t.gpr .rsp = S) (hi : t.gpr .r10 = BitVec.ofNat 64 j) :
    t.ea mByte = off S oM + BitVec.ofNat 64 j := by
  simp only [State.ea, mByte, hb, hi, BitVec.mul_one, BitVec.ofInt_natCast, off]
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j)]

/-- `r₂ & r₁ & r₃ & 1`. -/
def gOf (r₂ r₁ r₃ : BitVec 64) : BitVec 64 := r₂ &&& r₁ &&& r₃ &&& 1

theorem gOf_cases (r₂ r₁ r₃ : BitVec 64) : gOf r₂ r₁ r₃ = 0 ∨ gOf r₂ r₁ r₃ = 1 := by
  unfold gOf
  generalize r₂ &&& r₁ &&& r₃ = x
  have h : (x &&& 1).toNat = x.toNat % 2 := by
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h0 | h1
  · exact .inl (BitVec.eq_of_toNat_eq (by rw [h, h0]; rfl))
  · exact .inr (BitVec.eq_of_toNat_eq (by rw [h, h1]; rfl))

/-- The comparison's registers. -/
theorem cmpArgs_ok {s t : State} (hp : PreF s) (he : Env s t) :
    WP isa (.block cmpArgs) t fun t' => t'.mem = t.mem ∧
      t'.gpr .r11 = gOf (t.gpr .rax) (word t.mem (fb s) oR1) (word t.mem (fb s) oR3) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = stackArg s 0 ∧ t'.gpr .rcx = s.gpr .rcx ∧
      t'.gpr .r10 = BitVec.ofNat 64 0 ∧ t'.gpr .rdx = 0 ∧ Keep [.rax, .r11, .rdi, .rsi, .rcx, .r10, .rdx] t t' := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.rax, .r11, .rdi, .rsi, .rcx, .r10, .rdx] (c := .block cmpArgs) (Q := fun t' =>
      t'.mem = t.mem ∧ t'.gpr .r11 = gOf (t.gpr .rax) (word t.mem (fb s) oR1) (word t.mem (fb s) oR3) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = stackArg s 0 ∧ t'.gpr .rcx = s.gpr .rcx ∧
      t'.gpr .r10 = BitVec.ofNat 64 0 ∧ t'.gpr .rdx = 0) (by
    xrun [cmpArgs, gOf, ea_sp, he.rsp, arg, hs.ld (d := oR1) (by decide), hs.ld (d := oR3) (by decide),
      hs.ld (d := oOut) (by decide), hs.ld (d := oK) (by decide), arg_in hp he (show 0 < 14 by decide),
      show fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 0) = stackArgAddr s 0 from (stackArgAddr_fb s 0).symm,
      he.sOut, he.sK, he.arg hp (show 0 < 14 by decide)]) rfl) fun t' ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, k⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, k⟩

theorem zext_xor_eq_zero (a b : Byte) : (BitVec.setWidth 64 a ^^^ BitVec.setWidth 64 b = 0) ↔ a = b := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    have := congrArg (BitVec.setWidth 8) h
    simpa using this
  · rintro rfl; rfl

/-- After `j` bytes of the comparison. -/
structure CmpInv (t₀ : State) (op ip : Addr) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r9, .r10, .rdx] t₀ t
  mem : t.mem = t₀.mem
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  rdx : t.gpr .rdx = 0 ↔ ∀ i < j, t₀.mem (op + BitVec.ofNat 64 i) = t₀.mem (ip + BitVec.ofNat 64 i)

/-- The comparison of the `k` bytes at `op` and `ip`: `rdx` is zero exactly
when they are equal. -/
theorem cmpLoop_ok {t : State} {op ip : Addr} {k : Nat} (hk1 : 1 ≤ k) (hk : k < 2 ^ 63)
    (hdi : t.gpr .rdi = op) (hsi : t.gpr .rsi = ip) (hcx : t.gpr .rcx = BitVec.ofNat 64 k)
    (h10 : t.gpr .r10 = BitVec.ofNat 64 0) (hdx : t.gpr .rdx = 0)
    (ho : ∀ i < k, InRegions (t.rd ++ t.wr) (op + BitVec.ofNat 64 i) 1)
    (hi : ∀ i < k, InRegions (t.rd ++ t.wr) (ip + BitVec.ofNat 64 i) 1) :
    WP isa cmpLoop t fun t' => CmpInv t op ip k t' := by
  refine wp_upto (a := 0) (N := k) (by omega) (CmpInv t op ip) ?_ (fun _ h => h)
    ⟨Keep.refl _ _, rfl, h10, ⟨fun _ _ h => absurd h (by omega), fun _ => hdx⟩⟩
  intro j _ hj u hI
  have hdi' : u.gpr .rdi = op := (hI.keep.gpr (by decide)).trans hdi
  have hsi' : u.gpr .rsi = ip := (hI.keep.gpr (by decide)).trans hsi
  have hcx' : u.gpr .rcx = BitVec.ofNat 64 k := (hI.keep.gpr (by decide)).trans hcx
  have hoj : InRegions (u.rd ++ u.wr) (op + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact ho j hj
  have hij : InRegions (u.rd ++ u.wr) (ip + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hi j hj
  refine WP.mono (WP.keep [.rax, .r9, .r10, .rdx] (Q := fun u' => u'.mem = u.mem ∧
      u'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ u'.zf = some (decide (j + 1 = k)) ∧
      u'.gpr .rdx = u.gpr .rdx ||| (BitVec.setWidth 64 (u.mem (op + BitVec.ofNat 64 j)) ^^^
        BitVec.setWidth 64 (u.mem (ip + BitVec.ofNat 64 j)))) (by
    xrun [cmpLoop, State.ea, at10, hdi', hsi', BitVec.mul_one, show BitVec.ofInt 64 0 = 0#64 from rfl,
      BitVec.add_zero, hoj, hij, hI.r10, hcx', ofNat_add_one,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show k < 2 ^ 64 by omega)]) rfl) fun u' ⟨⟨hm, h10', hz, hdx'⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hm.trans hI.mem, h10', ?_⟩
  rw [hdx', show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, ← show (0 : BitVec 64) = 0#64 from rfl,
    zext_xor_eq_zero, hI.rdx, hI.mem]
  constructor
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact h1 i hi
    · exact h2
  · intro h
    exact ⟨fun i hi => h i (by omega), h j (by omega)⟩

/-- The release mask and the result. -/
def relMask (g : BitVec 64) (eq : Bool) : BitVec 64 := if g = 1 ∧ eq = true then BitVec.allOnes 64 else 0
def result (g : BitVec 64) (eq : Bool) : BitVec 64 := if g = 1 then (if eq then 1 else 2) else 0

theorem masks_ok {t : State} {g : BitVec 64} {eq : Bool} (h11 : t.gpr .r11 = g) (hg : g = 0 ∨ g = 1)
    (hdx : t.gpr .rdx = 0 ↔ eq = true) :
    WP isa (.block masks) t fun t' => t'.mem = t.mem ∧ t'.gpr .r9 = relMask g eq ∧ t'.gpr .r11 = result g eq ∧
      t'.gpr .r10 = BitVec.ofNat 64 0 ∧ Keep [.rdx, .r9, .rax, .r8, .r11, .r10] t t' := by
  have hcf : decide ((t.gpr .rdx).toNat < BitVec.toNat (1 : BitVec 64)) = eq := by
    rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
    cases eq
    · have : t.gpr .rdx ≠ 0 := fun h => by simpa using hdx.mp h
      simp only [decide_eq_false_iff_not, Nat.lt_one_iff]
      intro h; exact this (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · simp only [decide_eq_true_eq, Nat.lt_one_iff, hdx.mpr rfl]; rfl
  refine WP.mono (WP.keep [.rdx, .r9, .rax, .r8, .r11, .r10] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .r9 = relMask g eq ∧ t'.gpr .r11 = result g eq ∧ t'.gpr .r10 = BitVec.ofNat 64 0) (by
    xrun [masks, h11, hcf]
    rcases hg with rfl | rfl <;> cases eq <;> decide) rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩

theorem low_and_mask (b : Byte) (g : BitVec 64) (eq : Bool) :
    (BitVec.setWidth 64 b &&& relMask g eq).setWidth 8 = if g = 1 ∧ eq = true then b else 0 := by
  unfold relMask
  split
  · rw [BitVec.and_allOnes]; simp
  · rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.and_zero]; rfl

/-- After `j` bytes of the release. -/
structure RelInv (t₀ : State) (op Mb : Addr) (g : BitVec 64) (eq : Bool) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r10] t₀ t
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  out : ∀ i < j, t.mem (op + BitVec.ofNat 64 i) = if g = 1 ∧ eq = true then t₀.mem (Mb + BitVec.ofNat 64 i) else 0
  m : ∀ i < j, t.mem (Mb + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ op + BitVec.ofNat 64 i) → (∀ i < j, x ≠ Mb + BitVec.ofNat 64 i) → t.mem x = t₀.mem x

/-- The release: `out := M & mask`, `M := 0`, byte by byte. -/
theorem releaseLoop_ok {t : State} {S op : Addr} {k : Nat} {g : BitVec 64} {eq : Bool} (hk1 : 1 ≤ k)
    (hk : k < 2 ^ 63) (hsp : t.gpr .rsp = S) (hdi : t.gpr .rdi = op) (h9 : t.gpr .r9 = relMask g eq)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 k) (h10 : t.gpr .r10 = BitVec.ofNat 64 0)
    (hwo : ∀ i < k, InRegions t.wr (op + BitVec.ofNat 64 i) 1)
    (hwm : ∀ i < k, InRegions t.wr (off S oM + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < k, ∀ i' < k, op + BitVec.ofNat 64 i ≠ off S oM + BitVec.ofNat 64 i') :
    WP isa releaseLoop t fun t' => RelInv t op (off S oM) g eq k t' := by
  refine wp_upto (a := 0) (N := k) (by omega) (RelInv t op (off S oM) g eq) ?_ (fun _ h => h)
    ⟨Keep.refl _ _, h10, fun _ h => absurd h (by omega), fun _ h => absurd h (by omega), fun _ _ _ => rfl⟩
  intro j _ hj u hI
  have hsp' : u.gpr .rsp = S := (hI.keep.gpr (by decide)).trans hsp
  have hdi' : u.gpr .rdi = op := (hI.keep.gpr (by decide)).trans hdi
  have h9' : u.gpr .r9 = relMask g eq := (hI.keep.gpr (by decide)).trans h9
  have hcx' : u.gpr .rcx = BitVec.ofNat 64 k := (hI.keep.gpr (by decide)).trans hcx
  have hoj : InRegions u.wr (op + BitVec.ofNat 64 j) 1 := by rw [hI.keep.2.2]; exact hwo j hj
  have hmj : InRegions u.wr (off S oM + BitVec.ofNat 64 j) 1 := by rw [hI.keep.2.2]; exact hwm j hj
  have hmj' : InRegions (u.rd ++ u.wr) (off S oM + BitVec.ofNat 64 j) 1 :=
    let ⟨r, hr, hc⟩ := hmj; ⟨r, List.mem_append_right _ hr, hc⟩
  have hb : u.mem (off S oM + BitVec.ofNat 64 j) = t.mem (off S oM + BitVec.ofNat 64 j) :=
    hI.frame _ (fun i hi h => hsep i (by omega) j hj h.symm) fun i hi h => out_ne (by omega) (by omega)
      (show j ≠ i by omega) h
  refine WP.mono (WP.keep [.rax, .r10] (Q := fun u' =>
      u'.mem = (u.mem.writeW (op + BitVec.ofNat 64 j)
        (if g = 1 ∧ eq = true then t.mem (off S oM + BitVec.ofNat 64 j) else 0)).writeW
          (off S oM + BitVec.ofNat 64 j) (0 : Byte) ∧
      u'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ u'.zf = some (decide (j + 1 = k))) (by
    xrun [releaseLoop, State.ea, at10, mByte, hsp', hdi', hI.r10, h9', hcx', BitVec.mul_one,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, BitVec.ofInt_natCast,
      show S + BitVec.ofNat 64 j + BitVec.ofNat 64 oM = off S oM + BitVec.ofNat 64 j by
        rw [off, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j)],
      hoj, hmj, hmj', hb, low_and_mask, ofNat_add_one,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show k < 2 ^ 64 by omega)]
    rfl) rfl) fun u' ⟨⟨hm, h10', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), h10', ?_, ?_, ?_⟩
  · intro i hi
    rw [hm, writeW8_apply, writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (hsep i (by omega) j hj)),
        ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) (show i ≠ j by omega)))]
      exact hI.out i hi
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (hsep i (by omega) i (by omega)))]; simp only [↓reduceIte]
  · intro i hi
    rw [hm, writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) (show i ≠ j by omega))),
        writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false fun h => hsep j hj i (by omega) h.symm)]
      exact hI.m i hi
    · simp only [↓reduceIte]
  · intro x hx hx'
    rw [hm, writeW8_apply, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx' j (by omega))),
      ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
    exact hI.frame x (fun i hi => hx i (by omega)) fun i hi => hx' i (by omega)

end VG.Proof.Rsa.X86_64
