import VerifiedGarbage.Proof.Rsa.X86_64.PrivPd
import VerifiedGarbage.Proof.Rsa.PrivCheck

/-!
# `vg_rsa_private_checked` on x86-64: the check and the release

After the calls, `out` (which `vg_rsa_public_precomputed_checked` wrote) is
compared with the input without branches (`cmpLoop_ok`), and `M` is
released to `out` under the mask of `r₁ = r₂ = r₃ = 1` and their equality,
and zeroed (`releaseLoop_ok`), whatever `M` and `out` hold (`tail_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.WriteBytes (writeW8_apply)

theorem ea_at10 (t : State) {b : Reg} {p : Addr} {j : Nat} (hb : t.gpr b = p)
    (hi : t.gpr .r10 = BitVec.ofNat 64 j) : t.ea (at10 b) = p + BitVec.ofNat 64 j := by
  simp only [State.ea, at10, hb, hi, BitVec.mul_one, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]

theorem ea_mByte (t : State) {S : Addr} {j : Nat} (hb : t.gpr .rsp = S) (hi : t.gpr .r10 = BitVec.ofNat 64 j) :
    t.ea mByte = off S oM + BitVec.ofNat 64 j := by
  simp only [State.ea, mByte, hb, hi, BitVec.mul_one, BitVec.ofInt_natCast, off]
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j)]

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

theorem contains_of_byte {r : Region} {p : Addr} {n : Nat} (h : r = ⟨p, n⟩) (hn : n ≤ 2 ^ 64) {i : Nat}
    (hi : i < n) : r.Contains (p + BitVec.ofNat 64 i) 1 := by
  subst h; exact Offset.contains_base _ (by omega) (by omega)

/-- The check and the release, after the calls, from `t`: whatever `M`,
`out` and the values returned hold. -/
theorem tail_ok {s t : State} (hp : PreF s) (he : Env s t) :
    WP isa (seqs PrivChecked.tail) t fun t' =>
      t'.gpr .rax = result (gOf (t.gpr .rax) (word t.mem (fb s) oR1) (word t.mem (fb s) oR3))
        (decide (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
          Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)) ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
        (if gOf (t.gpr .rax) (word t.mem (fb s) oR1) (word t.mem (fb s) oR3) = 1 ∧
            Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
              Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat
          then Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat
          else List.replicate (s.gpr .rcx).toNat 0) ∧
      Spec.Rsa.bytesAt t'.mem (off (fb s) oM) (s.gpr .rcx).toNat = List.replicate (s.gpr .rcx).toNat 0 ∧
      Env s t' := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hsi := hp.hsi
  have hil := hp.hil
  -- The input, unchanged.
  have hin : Spec.Rsa.bytesAt t.mem (stackArg s 0) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat :=
    bytes_of_frame he.mem (by rw [← hil]; exact hp.dKi) (by rw [← hil]; exact hp.dOi) (by rw [← hil]; exact hp.dis.symm)
      (by omega)
  have hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) ∈ t.wr := by
    rw [he.wr, hp.hwr, ← hsi]; simp
  have hinp : (⟨stackArg s 0, (s.gpr .rcx).toNat⟩ : Region) ∈ t.rd := by
    rw [he.rd, hp.hrd, ← hil]; simp
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have wO : (s.gpr .rcx).toNat ≤ 2 ^ 64 := by omega
  unfold PrivChecked.tail
  simp only [seqs]
  refine WP.seq (WP.mono (cmpArgs_ok hp he) fun t₁ ⟨hm₁, h11, hdi, hsi₁, hcx, h10, hdx, k₁⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (k := (s.gpr .rcx).toNat) (op := s.gpr .rdi) (ip := stackArg s 0) (by omega)
    (by omega) hdi hsi₁ (by rw [hcx]; exact (ofNat_toNat _).symm) h10 hdx
    (fun i hi => ⟨_, List.mem_append_right _ (by rw [k₁.2.2]; exact hout), contains_of_byte rfl wO hi⟩)
    (fun i hi => ⟨_, List.mem_append_left _ (by rw [k₁.2.1]; exact hinp), contains_of_byte rfl wO hi⟩))
    fun t₂ hI => ?_)
  have k12 := k₁.trans hI.keep
  have hrdx : t₂.gpr .rdx = 0 ↔ decide (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) = true := by
    rw [hI.rdx, decide_eq_true_iff, ← hin, bytesAt_eq_iff, hm₁]
  refine WP.seq (WP.mono (masks_ok (h11 ▸ (hI.keep.gpr (by decide))) (gOf_cases _ _ _) hrdx)
    fun t₃ ⟨hm₃, h9, h11', h10', k₃⟩ => ?_)
  have k13 := k12.trans k₃
  have hsep : ∀ i < (s.gpr .rcx).toNat, ∀ i' < (s.gpr .rcx).toNat,
      s.gpr .rdi + BitVec.ofNat 64 i ≠ off (fb s) oM + BitVec.ofNat 64 i' := fun i hi i' hi' h => by
    have hc := contains_of_byte (r := mR s) rfl wO hi'
    rw [← h] at hc
    exact (hp.dKo.sub_left (mR_sub hp)) _ hc
      (contains_of_byte (r := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩) rfl (by omega) (show i < (s.gpr .rsi).toNat by omega))
  refine WP.seq (WP.mono (releaseLoop_ok (k := (s.gpr .rcx).toNat) (S := fb s) (by omega) (by omega)
    ((k13.gpr (by decide)).trans he.rsp) (((hI.keep.trans k₃).gpr (by decide)).trans hdi) h9 ?_ h10'
    (fun i hi => ⟨_, by rw [k13.2.2]; exact hout, contains_of_byte rfl wO hi⟩)
    (fun i hi => ⟨_, by rw [k13.2.2]; exact hfr, by
      rw [off, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base _ (by unfold oM frameBytes; omega) (by unfold oM; omega)⟩)
    hsep) fun t₄ hR => ?_)
  · rw [((hI.keep.trans k₃).gpr (by decide)).trans hcx]; exact (ofNat_toNat _).symm
  have hm₃ : t₃.mem = t.mem := hm₃.trans (hI.mem.trans hm₁)
  have k14 := k13.trans hR.keep
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.gpr .rax = t₄.gpr .r11 ∧ t'.mem = t₄.mem) (by xrun) rfl)
    fun t' ⟨⟨hax, hm⟩, k'⟩ => ?_
  have k15 := k14.trans k'
  have hfr4 : Frame [outR s, mR s] t.mem t'.mem := fun x hx => by
    rw [hm, hR.frame x (fun i hi h => hx _ (List.mem_cons_self ..) (by
        rw [h]; exact contains_of_byte (r := outR s) rfl (by omega) (show i < (s.gpr .rsi).toNat by omega)))
      (fun i hi h => hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by
        rw [h]; exact contains_of_byte rfl wO hi)), hm₃]
  have hslot : ∀ {d : Nat}, 96 ≤ d → d + 8 ≤ oM → word t'.mem (fb s) d = word t.mem (fb s) d := fun hd hd' =>
    slot_keep hfr4 fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.dKo.sub_left (frame_sub s (by unfold oM frameBytes at *; omega))
      · exact Offset.disjoint _ (.inl hd') (by unfold oM at hd'; omega) (by unfold oM; omega)
  refine ⟨hax.trans ((hR.keep.gpr (by decide)).trans h11'), ?_, ?_, ⟨(k15.gpr (by decide)).trans he.rsp,
    k15.2.1.trans he.rd, k15.2.2.trans he.wr, frame_call he.mem hfr4 fun r hr => ?_,
    (hslot (by decide) (by decide)).trans he.sOut, (hslot (by decide) (by decide)).trans he.sN,
    (hslot (by decide) (by decide)).trans he.sK, (hslot (by decide) (by decide)).trans he.sE,
    (hslot (by decide) (by decide)).trans he.sEl⟩⟩
  · by_cases hc : gOf (t.gpr .rax) (word t.mem (fb s) oR1) (word t.mem (fb s) oR3) = 1 ∧
        Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
          Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat
    · have hc' : gOf (t.gpr .rax) (word t.mem (fb s) oR1) (word t.mem (fb s) oR3) = 1 ∧
          decide (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
            Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) = true := ⟨hc.1, decide_eq_true hc.2⟩
      simp only [hc, and_self, ↓reduceIte]
      simp only [Spec.Rsa.bytesAt, hm]
      exact List.map_congr_left fun i hi => by
        rw [hR.out i (List.mem_range.mp hi), hm₃]; simp only [hc', and_self, ↓reduceIte]
    · have hc' : ¬ (gOf (t.gpr .rax) (word t.mem (fb s) oR1) (word t.mem (fb s) oR3) = 1 ∧
          decide (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
            Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) = true) :=
        fun h => hc ⟨h.1, of_decide_eq_true h.2⟩
      simp only [hc, ↓reduceIte]
      simp only [Spec.Rsa.bytesAt, hm]
      refine List.ext_getElem (by simp) fun i h₁ _ => ?_
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
      rw [hR.out i (by simpa using h₁)]; simp only [hc', ↓reduceIte]
  · simp only [Spec.Rsa.bytesAt, hm]
    refine List.ext_getElem (by simp) fun i h₁ _ => ?_
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact hR.m i (by simpa using h₁)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inl (sub_refl _))
    · exact .inl (mR_sub hp)

end VG.Proof.Rsa.X86_64
