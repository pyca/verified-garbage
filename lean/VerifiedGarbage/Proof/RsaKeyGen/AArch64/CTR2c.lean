import VerifiedGarbage.Proof.Bignum.AArch64.CTR2

/-!
# A candidate on AArch64: constant time of `R² mod c`

`r2_ct` (`Proof/Bignum/AArch64/CTR2.lean`) relates runs with the same
modulus; a candidate `c` is secret, but its top bit is set, so `topBit`
runs 63 iterations and the doublings `w + 1` whatever `c` (`r2c_ct`). The
runs agree on the working space alone (`Ws`), `-c⁻¹` and `c` differing.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)

/-- The layout of the working space `L` with `-m⁻¹ = mi`. -/
abbrev lay (L : Ws) (mi : BitVec 64) : Lay := ⟨L.B, L.Z, L.w, mi⟩

/-- `Φ` fixes the registers `rs` to values of the public data. -/
theorem pins_of {α : Type} {Φ : α → State → Prop} (rs : List Reg) (f : α → Reg → BitVec 64)
    (h : ∀ a s, Φ a s → ∀ r ∈ rs, s.gpr r = f a r) : Pins Φ rs :=
  fun a _ _ h₁ h₂ r hr => (h a _ h₁ r hr).trans (h a _ h₂ r hr).symm

theorem pins_nil' {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

/-! ## The top bit -/

theorem top_div_two {T j : Nat} (hT : 2 ^ 63 ≤ T) (hT1 : T < 2 ^ 64) (hj : j < 63) :
    T / 2 ^ (j + 1) = 1 ↔ j + 1 = 63 := by
  constructor
  · intro h
    by_contra hne
    have h2 : 2 * 2 ^ (j + 1) ≤ T := by
      have : 2 ^ (j + 2) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.pow_succ] at this; omega
    have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos (j + 1))).mpr h2
    omega
  · intro h
    rw [h]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- One halving of `topBit`'s loop, from `T / 2^j` with `2^63 ≤ T`. -/
theorem topStep_ok {s : State} {T j : Nat} (hT : 2 ^ 63 ≤ T) (hT1 : T < 2 ^ 64) (hj : j < 63)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 (T / 2 ^ j)) :
    WP isa (.block [.lsr .x .x3 .x3 1, .add .x .x9 .x9 .x9, .subImm .x .x13 .x13 1, .subImm .x .x6 .x3 1]) s
      fun t => t.gpr .x3 = BitVec.ofNat 64 (T / 2 ^ (j + 1)) ∧
        isa.eval (.nonzero .x .x6) t = some (decide (j + 1 < 63)) := by
  have hTj : T / 2 ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hT1
  have hTj1 : 0 < T / 2 ^ (j + 1) := Nat.div_pos (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hT)
    (Nat.two_pow_pos _)
  have hlt : T / 2 ^ (j + 1) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hT1
  refine WP.mono (Q := fun (t : State) => t.gpr .x3 = BitVec.ofNat 64 (T / 2 ^ (j + 1)) ∧
      t.gpr .x6 = BitVec.ofNat 64 (T / 2 ^ (j + 1)) - BitVec.ofNat 64 1) (by
    brun [h3, shr1_ofNat _ hTj, div_pow_succ]) fun t ⟨h3', h6⟩ => ⟨h3', ?_⟩
  rw [eval_nonzero, h6]
  have e := ofNat_sub1_eq_zero hlt hTj1
  refine congrArg some ?_
  rw [bne, e]
  have k := top_div_two hT hT1 hj
  by_cases h : j + 1 = 63
  · rw [decide_eq_true (k.mpr h), decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false (fun e => h (k.mp e)), decide_eq_true (by omega)]; rfl

/-- `topBit` from `x3 = T` with `2^63 ≤ T`: its loop runs 63 iterations,
whatever `T`. -/
theorem topBit_ct {α : Type} {Φ : α → State → Prop}
    (hT : ∀ a s, Φ a s → ∃ T, 2 ^ 63 ≤ T ∧ T < 2 ^ 64 ∧ s.gpr .x3 = BitVec.ofNat 64 T) :
    RelCT isa (Two Φ) topBit fun _ _ => True := by
  unfold topBit
  refine RelCT.seq (two_piece (Ψ := fun _ s => ∃ T, 2 ^ 63 ≤ T ∧ T < 2 ^ 64 ∧
      s.gpr .x3 = BitVec.ofNat 64 (T / 2 ^ 0) ∧ isa.eval (.zero .x .x6) s = some false) [] (pins_nil' _)
      (by taint_decide) fun a s h => ?_) ?_
  · obtain ⟨T, hT0, hT1, h3⟩ := hT a s h
    refine WP.mono (Q := fun (t : State) => t.gpr .x3 = BitVec.ofNat 64 T ∧
        t.gpr .x6 = BitVec.ofNat 64 T - BitVec.ofNat 64 1) (by brun [h3]) fun t ⟨h3', h6⟩ =>
      ⟨T, hT0, hT1, by rw [h3', Nat.pow_zero, Nat.div_one], ?_⟩
    rw [eval_zero, h6, ofNat_sub1_eq_zero hT1 (by omega), decide_eq_false (by omega)]
  refine two_ite (fun _ _ _ h₁ h₂ => by
      obtain ⟨_, _, _, _, e₁⟩ := h₁
      obtain ⟨_, _, _, _, e₂⟩ := h₂
      rw [e₁, e₂])
    (RelCT.of_false fun _ _ ⟨_, ⟨⟨_, _, _, _, e⟩, et⟩, _, _⟩ => by rw [e] at et; cases et) ?_
  refine (two_loop (Φ := fun _ j s => ∃ T, 2 ^ 63 ≤ T ∧ T < 2 ^ 64 ∧ s.gpr .x3 = BitVec.ofNat 64 (T / 2 ^ j))
    (Ψ := fun _ _ => True) (fun _ => 63) (two_taint [] (pins_nil' _) (by taint_decide)) ?_).mono
    (fun _ _ ⟨a, ⟨⟨T, hT0, hT1, h3, _⟩, _⟩, ⟨⟨T', hT0', hT1', h3', _⟩, _⟩, hsp⟩ =>
      ⟨a, ⟨by decide, T, hT0, hT1, h3⟩, ⟨by decide, T', hT0', hT1', h3'⟩, hsp⟩) fun _ _ _ => trivial
  rintro a j s hj ⟨T, hT0, hT1, h3⟩
  exact WP.mono (topStep_ok hT0 hT1 hj h3) fun t ⟨h3', he⟩ => ⟨he, fun _ => ⟨T, hT0, hT1, h3'⟩, fun _ => trivial⟩


/-! ## Doublings and squarings, for any `-m⁻¹` -/

/-- `double` is constant time for any `-m⁻¹`. -/
theorem double_ctW {mo acc tmp o : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.x0]) (.block (dblHead mo acc tmp o)) hc).isSome = true) :
    RelCT isa (Two GoodW) (double mo acc tmp o) fun _ _ => True := by
  rw [double_eq]
  exact RelCT.seq (two_piece (Ψ := fun (L : Ws) t => DblHeadL mo acc tmp o (lay L 0) t) _ pins_goodW h
    fun L _ ⟨mi, hg, hZ⟩ => dblHead_ok (L := lay L mi) ⟨hg, hZ⟩ hmo hacc htmp ho)
    (two_map (fun L : Ws => lay L 0) (fun _ _ h => h) (dblTail_ct mo acc tmp o))

/-- The public data of `doubles`: the working space and the count. -/
structure DblW where
  L : Ws
  c : Nat

/-- After `j` doublings, for some `-m⁻¹`. -/
def DblsW (mo acc tmp o sl : Nat) (p : DblW) (j : Nat) (t : State) : Prop :=
  ∃ mi, DblsAt mo acc tmp o sl ⟨lay p.L mi, p.c⟩ j t

/-- `doubles` leaks the same in runs with the same working space and count. -/
theorem doubles_ctW {mo acc tmp o sl : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o) (d8 : o ≠ mo)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.x0]) (.block (dblHead mo acc tmp o)) hc).isSome = true)
    {hc' : VG.Taint.Hint VG.AArch64.Taint.T}
    (h' : (taint.check (Taint.ofRegs [.x0]) (.block [sth .x13 sl]) hc').isSome = true)
    {hc'' : VG.Taint.Hint VG.AArch64.Taint.T}
    (h'' : (taint.check (Taint.ofRegs [.x0]) (.block (dblCount sl)) hc'').isSome = true) :
    RelCT isa (Two fun (p : DblW) s => ∃ mi, GoodL (lay p.L mi) s ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31 ∧ 1 ≤ p.c ∧
      p.c < 2 ^ 31 ∧ s.gpr .x13 = BitVec.ofNat 64 p.c ∧
      wv s.mem p.L.B (slot p.L.w o) p.L.w < wv s.mem p.L.B (slot p.L.w mo) p.L.w)
      (doubles mo acc tmp o sl) fun _ _ => True := by
  rw [doubles_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.c ∧ DblsW mo acc tmp o sl p 0 s) [.x0]
    (pins_of _ (fun p _ => p.L.B) fun p s ⟨_, hg, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.1.x0) h' ?_) ?_
  · rintro p s ⟨mi, hg, hw, hw', hc1, hc', h13, hO⟩
    exact WP.mono (dblStart_ok (acc := acc) (tmp := tmp) hg.1.scr hg.1.x0 hg.1.hdr hg.2 hmo ho hsl hsl' h13 hO)
      fun t hI => ⟨by omega, mi, s, _, _, hI, hg.2, hw, hw', hc', Nat.lt_of_le_of_lt (Nat.zero_le _) hO⟩
  refine (two_loop (Φ := DblsW mo acc tmp o sl) (Ψ := fun _ _ => True) (fun p => p.c) ?_ ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  · refine RelCT.seq (two_post (Ψ := fun (q : DblW × Nat) s => GoodW q.1.L s)
      (two_map (·.1.L) (fun _ _ h => let ⟨mi, h'⟩ := h.2; ⟨mi, (dblsAt_good h')⟩) (double_ctW hmo hacc htmp ho h))
        ?_) (two_taint _ (pins_of [.x0] (fun q _ => q.1.L.B) fun q s ⟨_, hg, _⟩ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hg.x0) h'')
    rintro ⟨p, j⟩ s ⟨hj, mi, σ, O, N, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (double_ok hI.scr hI.x0 hI.hdr hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7
      (by rw [hI.ov, hI.nv]; exact Nat.mod_lt _ hN0)) fun t ⟨_, ha, k⟩ =>
        ⟨mi, ⟨hI.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hI.x0, ha.hdr hI.hdr⟩, hZ⟩
  · rintro p j s hj ⟨mi, σ, O, N, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (dblIter_ok hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7 d8 hsl hsl' hc' hN0 hj hI)
      fun t ⟨hI', hz⟩ => ⟨eval_count hj hz, fun _ => ⟨mi, σ, O, N, hI', hZ, hw, hw', hc', hN0⟩, fun _ => trivial⟩

/-- Squarings of `[aR2]`, for any `-m⁻¹`. -/
theorem sqs_ctW (M : Mont) (n : Nat) :
    RelCT isa (Two fun (L : Ws) s => ∃ mi, SqPre (lay L mi) s) (seqs (List.replicate (n + 1) (M.mm aR2 aR2 aR2)))
      fun _ _ => True := by
  have one : RelCT isa (Two fun (L : Ws) s => ∃ mi, SqPre (lay L mi) s) (M.mm aR2 aR2 aR2) fun _ _ => True :=
    two_map id (fun _ _ ⟨mi, h⟩ => ⟨mi, h.1⟩) (M.ct (.inl ⟨rfl, rfl, rfl⟩))
  induction n with
  | zero => exact one
  | succ n ih =>
    show RelCT isa _ (.seq (M.mm aR2 aR2 aR2) (seqs (List.replicate (n + 1) (M.mm aR2 aR2 aR2)))) _
    exact RelCT.seq (two_post (Ψ := fun (L : Ws) s => ∃ mi, SqPre (lay L mi) s) one
      fun _ _ ⟨mi, h⟩ => WP.mono (sq_pre M h) fun _ h' => ⟨mi, h'⟩) ih

/-! ## The pieces of `R² mod m` -/

theorem r2h_ok {p : R2Pub} {s : State} (h : R2Pre p s) : WP isa (.block [ldh .x12 sW, ldh .x8 (sArr aN)]) s (R2h p) := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
    h.1.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := h.1.2; omega)
  exact WP.mono (WP.keep [.x8, .x12] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 p.L.w ∧
      t.gpr .x8 = off p.L.B (slot p.L.w aN) ∧ t.mem = s.mem) (by
    brun [h.1.1.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aN < 32 by decide), hl sW (by decide),
      hl (sArr aN) (by decide), h.1.1.hdr.hw, h.1.1.hdr.harr aN (by decide)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h12, h8, hm⟩, k⟩ => ⟨h.keep hm k (by decide), h12, h8⟩

theorem r2a_ok {p : R2Pub} {s : State} (hh : R2h p s) :
    WP isa (.block [.subImm .x .x4 .x12 1, .lsl .x .x4 .x4 3, .add .x .x4 .x8 .x4, ld .x3 .x4]) s (R2a p) := by
  obtain ⟨h, h12, h8⟩ := hh
  obtain ⟨hT, -⟩ := h.top
  have hn := h.1.1.scr.nowrap
  have hw2 := h.2.1
  have := slot_le (w := p.L.w) (show aN < 8 by decide)
  have hw8 : (BitVec.ofNat 64 p.L.w - BitVec.ofNat 64 1) <<< 3 = BitVec.ofNat 64 (8 * (p.L.w - 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  exact WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 p.top ∧
      t.gpr .x12 = BitVec.ofNat 64 p.L.w ∧ t.mem = s.mem) (by
    brun [h12, h8, hw8, off_add,
      h.1.1.scr.ld (show slot p.L.w aN + 8 * (p.L.w - 1) + 8 ≤ p.L.Z by have := h.1.2; omega)]
    rw [← hT, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h3, h12', hm⟩, k⟩ => ⟨h.keep hm k (by decide), h3, h12'⟩

theorem r2b_ok {p : R2Pub} {s : State} (ha : R2a p s) : WP isa topBit s (R2b p) := by
  obtain ⟨h, h3, h12⟩ := ha
  obtain ⟨-, hT0, hT1, -⟩ := h.top
  exact WP.mono (topBit_ok h3 hT0 hT1) fun t ⟨⟨h9, h13, hm⟩, k⟩ =>
    ⟨h.keep hm k (by decide), h9, h13, (k.gpr .x12 (by decide)).trans h12⟩

theorem r2c_ok {p : R2Pub} {s : State} (hb : R2b p s) :
    WP isa (.block [sth .x13 sCnt, .subImm .x .x13 .x12 1]) s (R2c p) := by
  obtain ⟨⟨hg, hw, hw', hN, hinv, hodd, hlo⟩, h9, h13, h12⟩ := hb
  have hn := hg.1.scr.nowrap
  have hn' : p.L.B.toNat + slot p.L.w 8 ≤ 2 ^ 64 := by have := hg.2; omega
  have h0 := hdr_lt_slot p.L.w 0 (show sCnt < 32 by decide)
  have h0' := slot_le (w := p.L.w) (show 0 < 8 by decide)
  refine WP.mono (WP.keep [.x13] (Q := fun t => t.gpr .x13 = BitVec.ofNat 64 (p.L.w - 1) ∧
      t.mem = s.mem.writeW (off p.L.B (8 * sCnt)) (BitVec.ofNat 64 (64 - p.top.log2))) (by
    brun [hg.1.x0, hdr_enc (show sCnt < 32 by decide), hg.1.scr.st (d := 8 * sCnt) (by have := hg.2; omega),
      h13, h12, ofNat_sub_one' (show 1 ≤ p.L.w by omega) (by omega)]) (by decide) (by decide)
      (by decide +kernel)) fun t ⟨⟨h13', hm⟩, k⟩ => ?_
  exact ⟨⟨⟨⟨hg.1.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.1.x0,
    by rw [hm]; exact Hdr.store hg.1.hdr (by decide) (by decide) _⟩, hg.2⟩, hw, hw',
    by rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) hn']; exact hN,
    by rw [hm, hdrStore_word _ _ _ (by decide) (by decide) hn']; exact hinv, hodd, hlo⟩,
    (k.gpr .x12 (by decide)).trans h12, h13', (k.gpr .x9 (by decide)).trans h9, by rw [hm, word_writeW_self]⟩

theorem r2s_ok {p : R2Pub} {s : State} (h : R2c p s) :
    WP isa (.block [ldh .x8 (sArr aR2), movi .x7 0]) s fun t => R2c p t ∧ t.gpr .x8 = off p.L.B (slot p.L.w aR2) ∧
      t.gpr .x7 = 0 := by
  have hl : InRegions (s.rd ++ s.wr) (off p.L.B (8 * sArr aR2)) 8 :=
    h.1.1.1.scr.ld (by have := hdr_lt_slot p.L.w 8 (show sArr aR2 < 32 by decide); have := h.1.1.2; omega)
  refine WP.mono (WP.keep [.x7, .x8] (Q := fun t => t.gpr .x8 = off p.L.B (slot p.L.w aR2) ∧ t.gpr .x7 = 0 ∧
      t.mem = s.mem) (by
    brun [h.1.1.1.x0, hdr_enc (show sArr aR2 < 32 by decide), hl, h.1.1.1.hdr.harr aR2 (by decide)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h8, h7, hm⟩, k⟩ => ⟨?_, h8, h7⟩
  obtain ⟨hr, h12, h13, h9, hcnt⟩ := h
  exact ⟨hr.keep hm k (by decide), (k.gpr .x12 (by decide)).trans h12, (k.gpr .x13 (by decide)).trans h13,
    (k.gpr .x9 (by decide)).trans h9, hm ▸ hcnt⟩

theorem r2d_ok {p : R2Pub} {s : State} (h : R2c p s) : WP isa (setWord aR2) s (R2d p) := by
  obtain ⟨⟨hg, hw, hw', hN, hinv, hodd, hlo⟩, h12, h13, h9, hcnt⟩ := h
  obtain ⟨-, -, -, hL, -⟩ := r2top (s := s) hw hN hodd hlo
  have hn' : p.L.B.toNat + slot p.L.w 8 ≤ 2 ^ 64 := by have := hg.1.scr.nowrap; have := hg.2; omega
  refine WP.mono (setWord_ok hg.1.scr hg.1.x0 hg.1.hdr hg.2 h12 (by omega) (o := aR2) (by decide)
    (i := p.L.w - 1) (by omega) h13) fun t ⟨hv, ho, k⟩ => ?_
  have ha : Arrays p.L.B p.L.w [aR2] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (Nat.le_refl _)
  rw [h9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hL)] at hv
  exact ⟨⟨⟨⟨hg.1.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.1.x0, ha.hdr hg.1.hdr⟩, hg.2⟩, hw, hw',
    by rw [ha.wv_of_not_mem (by decide) (by decide) hn']; exact hN,
    by rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega)]; exact hinv, hodd, hlo⟩,
    by rw [ha.hslot (by decide)]; exact hcnt, hv⟩

theorem r2e_ok {p : R2Pub} {s : State} (h : R2d p s) :
    WP isa (.block [ldh .x13 sCnt, ldh .x12 sW, .add .x .x13 .x13 .x12]) s (R2e p) := by
  obtain ⟨hr, hcnt, hv⟩ := h
  have hg := hr.1
  have h0 := hdr_lt_slot p.L.w 0 (show 31 < 32 by decide)
  have h0' := slot_le (w := p.L.w) (show 0 < 8 by decide)
  have := hg.2
  exact WP.mono (WP.keep [.x12, .x13] (Q := fun t => t.gpr .x13 = BitVec.ofNat 64 p.cnt ∧ t.mem = s.mem) (by
    brun [hg.1.x0, hdr_enc (show sCnt < 32 by decide), hdr_enc (show sW < 32 by decide),
      hg.1.scr.ld (d := 8 * sCnt) (by unfold sCnt sFn; omega), hg.1.scr.ld (d := 8 * sW) (by unfold sW; omega),
      hcnt, hg.1.hdr.hw, ← BitVec.ofNat_add]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h13, hm⟩, k⟩ =>
      ⟨⟨hr.keep hm k (by decide), hm ▸ hcnt, hm ▸ hv⟩, h13⟩

theorem r2q_ok {p : R2Pub} {s : State} (h : R2e p s) :
    WP isa (doubles aN aAcc aTmp aR2 sCnt) s (SqPre p.L) := by
  obtain ⟨⟨⟨hg, hw, hw', hN, hinv, hodd, hlo⟩, -, hv⟩, h13⟩ := h
  obtain ⟨-, -, -, hL, hv0⟩ := r2top (s := s) hw hN hodd hlo
  have hn' : p.L.B.toNat + slot p.L.w 8 ≤ 2 ^ 64 := by have := hg.1.scr.nowrap; have := hg.2; omega
  refine WP.mono (doubles_ok hg.1.scr hg.1.x0 hg.1.hdr hg.2 hw (by omega) (mo := aN) (acc := aAcc)
    (tmp := aTmp) (o := aR2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (sl := sCnt) (by decide) (by decide)
    (c := p.cnt) (by unfold R2Pub.cnt; omega) (by unfold R2Pub.cnt; omega) h13 (by rw [hv, hN]; exact hv0))
    fun t ⟨hv', hf, hH, k⟩ => ?_
  have hf' : Frm p.L.B (r2Ranges p.L.w) s.mem t.mem := hf
  have hN0 : 0 < p.N := by omega
  refine ⟨⟨⟨hg.1.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.1.x0, hH⟩, hg.2⟩, hw, by omega,
    by rw [hf'.r2_word hn' (by decide) (by decide) (by decide) (by decide)]; exact hinv, ?_⟩
  rw [hv', hf'.r2_wv hn' (by decide) (by decide) (by decide) (by decide), hN]
  exact Nat.mod_lt _ hN0

/-! ## `R² mod c` for a candidate -/

/-- A predicate of `R2Pub` for some `-m⁻¹` and some `m` with its top bit set. -/
def Up (X : R2Pub → State → Prop) (L : Ws) (s : State) : Prop :=
  ∃ mi N, X ⟨lay L mi, N⟩ s ∧ 2 ^ (64 * L.w - 1) ≤ N

theorem up_post {X Y : R2Pub → State → Prop} {c : Prog isa} (h : ∀ p s, X p s → WP isa c s (Y p)) :
    ∀ L s, Up X L s → WP isa c s (Up Y L) :=
  fun _ _ ⟨mi, N, hx, hi⟩ => WP.mono (h _ _ hx) fun _ ht => ⟨mi, N, ht, hi⟩

/-- The top word of `m` with its top bit set. -/
theorem top63 {p : R2Pub} {s : State} (h : R2Pre p s) (hi : 2 ^ (64 * p.L.w - 1) ≤ p.N) :
    2 ^ 63 ≤ p.top ∧ p.top < 2 ^ 64 ∧ p.top.log2 = 63 := by
  obtain ⟨-, -, hT1, -⟩ := h.top
  have hw := h.2.1
  have e : 2 ^ 63 * 2 ^ (64 * (p.L.w - 1)) = 2 ^ (64 * p.L.w - 1) := by rw [← Nat.pow_add]; congr 1; omega
  have hT : 2 ^ 63 ≤ p.top := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by rw [e]; exact hi)
  exact ⟨hT, hT1, Nat.le_antisymm (Nat.lt_succ_iff.mp ((Nat.log2_lt (by omega)).mpr hT1))
    ((Nat.le_log2 (by omega)).mpr hT)⟩

theorem pins_up {X : R2Pub → State → Prop} (h : ∀ p s, X p s → R2Pre p s) : Pins (Up X) [.x0] :=
  pins_of _ (fun L _ => L.B) fun _ _ ⟨_, _, hx, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (h _ _ hx).1.1.x0

theorem setWordR2_ct : RelCT isa (Two (Up R2c)) (setWord aR2) fun _ _ => True := by
  rw [setWord_eq]
  exact RelCT.seq (two_piece (Ψ := Up fun p s => R2c p s ∧ s.gpr .x8 = off p.L.B (slot p.L.w aR2) ∧
      s.gpr .x7 = 0) _ (pins_up fun _ _ h => h.1) (by taint_decide) (up_post fun _ _ h => r2s_ok h))
    (two_taint [.x8, .x12, .x13, .x7] (pins_of _ (fun L r => match r with
        | .x8 => off L.B (slot L.w aR2) | .x12 => BitVec.ofNat 64 L.w | .x13 => BitVec.ofNat 64 (L.w - 1)
        | _ => 0) fun _ _ ⟨_, _, ⟨⟨_, h12, h13, _⟩, h8, h7⟩, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h8
      · exact h12
      · exact h13
      · exact h7) (by taint_decide))

/-- `R² mod c` leaks the same in runs that agree on the working space, for
moduli with their top bit set. -/
theorem r2c_ct (M : Mont) : RelCT isa (Two (Up R2Pre)) (seqs (r2Steps M.mm)) fun _ _ => True := by
  rw [r2Steps_eq]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (R := Two fun (L : Ws) s => ∃ mi, SqPre (lay L mi) s)
    ?_ (sqs_ctW M 5))
  refine RelCT.seq (RelCT.block_append (l₁ := ([ldh .x12 sW, ldh .x8 (sArr aN)] : List Instr))
    (l₂ := ([.subImm .x .x4 .x12 1, .lsl .x .x4 .x4 3, .add .x .x4 .x8 .x4, ld .x3 .x4] : List Instr))
    (RelCT.seq (two_piece (Ψ := Up R2h) _ (pins_up fun _ _ h => h) (by taint_decide)
        (up_post fun _ _ h => r2h_ok h))
      (two_piece (Ψ := Up R2a) [.x12, .x8] (pins_of _ (fun L r => match r with
          | .x12 => BitVec.ofNat 64 L.w | _ => off L.B (slot L.w aN)) fun _ _ ⟨_, _, ⟨_, h12, h8⟩, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h12
        · exact h8) (by taint_decide) (up_post fun _ _ h => r2a_ok h)))) ?_
  refine RelCT.seq (two_post (Ψ := Up R2b) (topBit_ct fun _ _ ⟨_, _, ⟨h, h3, _⟩, hi⟩ => by
    obtain ⟨hT, hT1, -⟩ := top63 h hi
    exact ⟨_, hT, hT1, h3⟩) (up_post fun _ _ h => r2b_ok h)) ?_
  refine RelCT.seq (two_piece (Ψ := Up R2c) _ (pins_up fun _ _ h => h.1) (by taint_decide)
    (up_post fun _ _ h => r2c_ok h)) ?_
  refine RelCT.seq (two_post (Ψ := Up R2d) setWordR2_ct (up_post fun _ _ h => r2d_ok h)) ?_
  refine RelCT.seq (two_piece (Ψ := Up R2e) _ (pins_up fun _ _ h => h.1) (by taint_decide)
    (up_post fun _ _ h => r2e_ok h)) ?_
  refine two_post (Ψ := fun L s => ∃ mi, SqPre (lay L mi) s) ((two_map (fun L : Ws => (⟨L, L.w + 1⟩ : DblW))
    (fun L s h => ?_) (doubles_ctW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide)
      (by taint_decide) (by taint_decide)))) fun L s ⟨mi, N, h, _⟩ => WP.mono (r2q_ok h) fun t h => ⟨mi, h⟩
  obtain ⟨mi, N, ⟨⟨⟨hg, hw, hw', hN, hinv, hodd, hlo⟩, -, hv⟩, h13⟩, hi⟩ := h
  obtain ⟨-, -, -, hL, hv0⟩ := r2top (s := s) hw hN hodd hlo
  obtain ⟨-, -, h63⟩ := top63 (p := ⟨lay L mi, N⟩) (s := s) ⟨hg, hw, hw', hN, hinv, hodd, hlo⟩ hi
  have hc : R2Pub.cnt ⟨lay L mi, N⟩ = L.w + 1 := by unfold R2Pub.cnt; rw [h63]; dsimp only; omega
  rw [hc] at h13
  have hw2 : 2 ≤ L.w := hw
  have hw30 : L.w < 2 ^ 30 := hw'
  exact ⟨mi, hg, hw2, show L.w < 2 ^ 31 by omega, show 1 ≤ L.w + 1 by omega, show L.w + 1 < 2 ^ 31 by omega, h13,
    by rw [hv, hN]; exact hv0⟩

end VG.Proof.RsaKeyGen.AArch64
